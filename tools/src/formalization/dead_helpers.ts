import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { PAPER_TMP_DIR } from "../paths.js";
import { maskLeanCommentsAndStrings } from "../graph/extractor.js";
import {
  isLeanModuleFile,
  isPublicDecl,
  LEAN_ATTRS_PREFIX_SRC,
  LEAN_DECL_MODIFIERS,
  publicSectionAt,
} from "../shared/lean_syntax.js";

/**
 * F4 dead-helper sweep — agent-authored declarations nothing in the run consumes.
 *
 * Every gate before F4 checks that proofs are CORRECT (build green, no sorry, axioms); nothing
 * checks that a declaration is USED. Helper lemmas are authored ahead of a planned proof route,
 * the route changes, and the abandoned helper still compiles — so it survives to F5 and gets a
 * docstring though no proof cites it
 * (observed live: `cellApproxPolynomial_coeff_envelope`, discrete-ATE Lemma 10). This
 * sweep reads the ground truth: the Lean sources at the done-point, when usage is final.
 *
 * A finding is a FLAG for the orchestrator, never an auto-delete: a follow-on run may consume an
 * earlier run's helpers (substrate reuse), so "unused by this run" is grounds for adjudication —
 * prune, or keep with a recorded reason.
 *
 * Scope guards against false positives: only public, attribute-free `theorem`/`lemma`/`def`s are
 * candidates (an `@[simp]`-style attribute or `instance` is consumed implicitly, with no textual
 * call site), and declarations realizing a graph node are exempt (results are products — they are
 * ALLOWED to have no consumer). Usage is a whole-identifier textual match over comment/string-
 * masked sources; same-name declarations in different namespaces merge, which can only
 * under-report (the safe direction).
 *
 * A declaration carrying a `-- @realizes <symbol>` tag in its own text is exempt: the F2.5 symbol
 * review consumes it (it realizes a symbol's space or meaning), with no call site in the proofs.
 *
 * Deliberate keeps: a decl whose preceding lines carry a `-- keep: <reason>` comment is exempt —
 * the justification lives in the source next to what it justifies, and the sweep stays quiet on
 * re-entry. An empty reason does not count.
 */

export interface DeadHelperFinding {
  decl: string;
  file: string;
  line: number;
}

interface DeclSite {
  name: string;
  file: string;
  line: number;
  attributed: boolean;
  kept: boolean;
}

/** Char indexes of `-- @realizes` tags in the RAW source. */
function realizesIndexes(raw: string): number[] {
  return [...raw.matchAll(/--\s*@realizes\b/g)].map((m) => m.index!);
}

/** Char indexes of `/-- … -/` docstrings carrying `@realizes`: the crosswalk reads the tag there
 *  (`crosswalk_semantics.ts`), so it binds to the declaration the docstring precedes. */
function docRealizesIndexes(raw: string): number[] {
  return [...raw.matchAll(/\/--[\s\S]*?-\//g)].filter((m) => /@realizes\b/.test(m[0])).map((m) => m.index!);
}

/** Char indexes of `-- keep: <reason>` markers in the RAW source (comments are masked everywhere
 *  else). Each marker exempts exactly the NEXT declaration that follows it — binding by adjacency
 *  in char order, so a marker never leaks onto later declarations and an intervening docstring or
 *  attribute block of any length cannot detach it (a fixed lookback window did both — audited
 *  2026-08-25). */
function keepMarkerIndexes(raw: string): number[] {
  return [...raw.matchAll(/^[ \t]*--\s*keep:\s*\S.*$/gm)].map((m) => m.index!);
}

// Name class covers Lean's real shapes: unicode letters (τ, ℓ-names) and dotted declarations.
// Dotted names are captured in full so they are never mistaken for their namespace prefix; they
// are then SKIPPED as candidates (call sites may use any qualified form, so a textual usage count
// is unreliable — under-reporting is the safe direction).
const DECL_RE =
  new RegExp(String.raw`^([ \t]*)(${LEAN_ATTRS_PREFIX_SRC})((?:(?:${LEAN_DECL_MODIFIERS})\s+)*)(theorem|lemma|def|instance|abbrev)\s+([\p{L}_][\p{L}\p{N}_?!']*(?:\.[\p{L}_][\p{L}\p{N}_?!']*)*)`, "gmu");

/** Public candidate + exempt declaration sites in one source. `masked` and `raw` are the same
 *  text with comments/strings blanked in `masked` (the mask is offset-preserving). */
export function scanDeclSites(masked: string, raw: string, file: string): DeclSite[] {
  const keeps = keepMarkerIndexes(raw);
  const realizes = realizesIndexes(raw);
  const docRealizes = docRealizesIndexes(raw);
  const starts = [...masked.matchAll(DECL_RE)].map((x) => x.index!);
  /** Whether a `@realizes` tag sits in the declaration starting at `at` (up to the next one). */
  const realizing = (at: number): boolean => {
    const next = starts.find((s) => s > at) ?? raw.length;
    return realizes.some((r) => r > at && r < next);
  };
  const moduleFile = isLeanModuleFile(raw);
  const out: DeclSite[] = [];
  let m: RegExpExecArray | null;
  let prevEnd = -1;
  DECL_RE.lastIndex = 0;
  while ((m = DECL_RE.exec(masked))) {
    const [, , attrs, mods, kind, name] = m;
    const declIndex = m.index;
    // A marker between the previous declaration and this one binds to this one.
    const kept = [...keeps, ...docRealizes].some((k) => k > prevEnd && k < declIndex);
    prevEnd = declIndex;
    if (!isPublicDecl(mods, { moduleFile, inPublicSection: publicSectionAt(masked, declIndex) })) continue;
    if (kind === "instance" || kind === "abbrev") continue; // consumed implicitly / inlined
    if (name.includes(".")) continue; // dotted decl: usage-count unreliable, skip (see DECL_RE note)
    const line = masked.slice(0, m.index).split("\n").length;
    out.push({ name, file, line, attributed: attrs.trim().length > 0, kept: kept || realizing(declIndex) });
  }
  return out;
}

export async function sweepDeadHelpers(
  leanDir: string,
  graphDeclNames: ReadonlySet<string>,
  opts?: {
    /** Extra root to scan for CONSUMERS (candidates still come only from `leanDir`). Runs share
     *  substrate across sibling run directories (a follow-on run consumes an earlier run's
     *  helpers from its own tree), so counting usage inside `leanDir` alone would flag
     *  cross-run-consumed helpers as dead. Default: `leanDir` only. */
    searchRoot?: string;
  },
): Promise<DeadHelperFinding[]> {
  if (!leanDir) return [];
  // Sources are read ONE FILE AT A TIME and dropped after use. The consumer corpus is the whole
  // package (every paper's sources: ~0.7 GB in 26k files on 2026-11-08), and holding it raw +
  // masked overflowed the runner's 4 GB heap right after every F4 review.
  async function* leanSources(root: string): AsyncGenerator<{ file: string; raw: string }> {
    // Disposable `tmp/` trees are pruned before descent rather than listed and then filtered (the
    // same files as `!isPaperTmpPath`): live they held 1.3M entries against 27k package entries.
    const rels: string[] = [];
    const walk = async (rel: string): Promise<void> => {
      for (const entry of await readdir(path.join(root, rel), { withFileTypes: true })) {
        const child = rel ? path.join(rel, entry.name) : entry.name;
        if (entry.isDirectory()) {
          if (entry.name !== PAPER_TMP_DIR) await walk(child);
        } else if (entry.name.endsWith(".lean")) rels.push(child);
      }
    };
    try {
      await walk("");
    } catch {
      return; // best-effort, like the sibling F3.5 scanners
    }
    rels.sort();
    for (const rel of rels) {
      let raw: string;
      try {
        raw = await readFile(path.join(root, rel), "utf8");
      } catch {
        continue; // file vanished between readdir and read
      }
      yield { file: rel.replaceAll(path.sep, "/"), raw };
    }
  }
  const searchRoot = opts?.searchRoot ? path.resolve(opts.searchRoot) : null;
  const leanAbs = path.resolve(leanDir);
  const usageRoots =
    searchRoot === null || searchRoot === leanAbs
      ? [leanDir]
      : leanAbs.startsWith(searchRoot + path.sep)
        ? [searchRoot] // parent root already covers leanDir
        : [searchRoot, leanDir];
  // Graph nodes may record fully qualified decl names; call sites use the short name.
  const exempt = new Set<string>();
  for (const d of graphDeclNames) {
    exempt.add(d);
    exempt.add(d.split(".").pop()!);
  }
  const sites: DeclSite[] = [];
  for await (const { file, raw } of leanSources(leanDir)) sites.push(...scanDeclSites(maskLeanCommentsAndStrings(raw), raw, file));
  const candidates = sites.filter((s) => !s.attributed && !s.kept && !exempt.has(s.name));
  if (candidates.length === 0) return [];

  /** Per candidate name: its whole-identifier matches and its definition sites over the corpus. */
  const counts = new Map<string, { wordRe: RegExp; defRe: RegExp; uses: number; defs: number }>();
  for (const { name } of candidates) {
    if (counts.has(name)) continue;
    const esc = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    counts.set(name, {
      wordRe: new RegExp(`(?<![\\p{L}\\p{N}_'])${esc}(?![\\p{L}\\p{N}_?!'])`, "gu"),
      // Every definition site of the same short name anywhere in the corpus contributes one match
      // that is not a use (the corpus may span sibling run dirs with their own re-declarations).
      defRe: new RegExp(`(?:theorem|lemma|def|instance|abbrev)\\s+${esc}(?![\\p{L}\\p{N}_?!'])`, "gu"),
      uses: 0,
      defs: 0,
    });
  }
  const matches = (src: string, re: RegExp): number => {
    re.lastIndex = 0;
    let n = 0;
    while (re.exec(src) !== null) n++;
    return n;
  };
  for (const root of usageRoots) {
    for await (const { raw } of leanSources(root)) {
      // Masking only blanks text, so a name absent from the raw source has no match in its masked
      // form: most files mention no candidate and are neither masked nor regex-scanned.
      const present = [...counts].filter(([name]) => raw.includes(name));
      if (present.length === 0) continue;
      const src = maskLeanCommentsAndStrings(raw);
      for (const [, c] of present) {
        c.uses += matches(src, c.wordRe);
        c.defs += matches(src, c.defRe);
      }
    }
  }

  const findings: DeadHelperFinding[] = [];
  for (const s of candidates) {
    const { uses, defs } = counts.get(s.name)!;
    if (uses - Math.max(defs, 1) <= 0) findings.push({ decl: s.name, file: s.file, line: s.line });
  }
  // One finding per name (same-name sites would all report or none).
  const seen = new Set<string>();
  return findings.filter((f) => (seen.has(f.decl) ? false : (seen.add(f.decl), true)));
}
