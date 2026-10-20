/**
 * INLINE CITATIONS — the published results a PROOF invokes by citation.
 *
 * A paper that restates an imported result as an environment of its own gets a `cited` leaf in the
 * core, compared with its source at V1.5. A result a proof merely invokes in running text ("where we
 * use [key, Proposition 3.1] in the last inequality") gets nothing: it is compared with no source,
 * and at the Lean stage the prover is left to prove another paper's theorem. This module finds those
 * places (`inlineCitationSites`) and words the V1 lint warning for each one no `cited` node covers
 * (`inlineCitationWarnings`).
 *
 * Detection only PROPOSES: a citation with a locator may also be a comparison, a borrowed method or
 * a result the paper proves itself. The V1 agent accounts for each site (`inlineCitationsBlock`) —
 * it registers it as a cited leaf made of the proof's own words (`ref_core.ts` `proof_citations`) or
 * dismisses it with a reason — and `lintInlineCitations` checks that accounting. A reference core
 * written before the accounting existed gets the warnings alone; so does, always, a site no cited
 * node can be made for (`accountableSites`).
 *
 * A SITE is a citation command inside the proof of an in-scope theorem-like environment that carries
 * a RESULT LOCATOR — Theorem / Thm. / Proposition / Prop. / Lemma / Lem. / Corollary / Cor. followed
 * by a number (`3.1`, `A.4`, `2`; several joined by commas or "and") — found
 *
 *  - in the command's optional argument (`\cite[Theorem 1.56]{key}`, `\citep[Prop.~3]{key}`), or
 *  - next to it in the same sentence: at most `WINDOW` characters before or after, with no sentence
 *    end, math, `\ref` or other citation in between ("Theorem 3.27 \citet{key}", "Theorems 11.2 and
 *    12.3 from \citet{key}", "\citet{key}, Theorem 2", `\citetext{\citealp{key}, Proposition 3.1}`).
 *    A locator between two citations goes to the nearer one (the one before it when equally near).
 *
 * A NAMED result counts as a locator too: "<Name>'s inequality / theorem / lemma / bound / identity"
 * right before the citation, in the same clause ("Freedman's inequality \cite{key}", "the
 * Azuma--Hoeffding inequality" does not: the name must be possessive), its locator that phrase.
 *
 * A citation without such a locator is not a site: "by standard theory \citep{key}" names no result
 * to compare. A locator written with a `\ref` is the paper's own result, not a site. TeX comments are
 * blanked first. A command citing several keys is ONE site naming them all (`keys`): which of the
 * works the locator belongs to is not decidable from the text.
 *
 * `unit` is the id of the proof unit holding the citation, `<env>/proof/<p>/<u>` — the cut of
 * `units.ts` (`regionUnits` over the proof's text, as `parseUnits` cuts it). Pure.
 */
import type { Core } from "../core/schema.js";
import { blankTexComments } from "../shared/tex_text.js";
import { regionUnits } from "./units.js";
import { texBalanceProblems } from "./tex_balance.js";
import type { EnvKind, EnvsJson, TexEnv } from "./types.js";

export interface InlineCitationSite {
  /** The environment (`envs.json` id) whose proof invokes the result. */
  env: string;
  /** The bibkey; several keys of one command joined by ", ". */
  key: string;
  keys: string[];
  /** The locator in full words: "Theorem 3.27", "Proposition 3.1". */
  locator: string;
  /** `<env>/proof/<p>/<u>`; `<env>/proof` when the citation sits in no unit. */
  unit: string;
  /** The citation with its locator and a few words around them, whitespace collapsed. */
  text: string;
}

/** The kinds whose proofs are read (`THEOREM_LIKE_KINDS` of the lint, which this module must not import). */
const PROVED_KINDS: ReadonlySet<EnvKind> = new Set<EnvKind>(["theorem", "lemma", "proposition", "corollary"]);

/** How far from its citation a locator may stand, in characters. */
const WINDOW = 48;

/** A citation command with its optional arguments and keys. `\citetext{…}` takes text, not keys: the
 * `\citealp` inside it is the citation. */
const CITE = /\\(?!citetext\b)(?:[Cc]ite[A-Za-z]*|(?:paren|text|auto|foot|full)cite)\*?\s*(?:\[([^\]]*)\]\s*)?(?:\[([^\]]*)\]\s*)?\{([^{}]*)\}/gu;

// a number: "3.1", "A.4", "B2", or a roman section "VIII.1" (a roman part needs its dot and a number after it)
const NUM = String.raw`(?:[IVXLC]+\.\d+(?:\.\d+)*|(?:[A-Z]\.?)?\d+(?:\.\d+)*)`;
const WORDS: ReadonlyArray<[RegExp, string]> = [
  [/^(?:theorem|thm)/iu, "Theorem"],
  [/^prop/iu, "Proposition"],
  [/^lem/iu, "Lemma"],
  [/^cor/iu, "Corollary"],
];
/** A locator: the word, then one number or a list of them. */
const LOCATOR = new RegExp(
  String.raw`\b(Theorems?|Thms?|Propositions?|Props?|Lemmas?|Lems?|Corollary|Corollaries|Cors?)\b\.?(?:\s|~|\\ )*(${NUM}(?:\s*(?:,\s*and\b|,|and\b|\\&)\s*${NUM})*)`,
  "giu",
);
/** A named result: "Freedman's inequality", "Bernstein's lemma", "Carath\\'eodory's theorem". */
const NAMED = /\b((?:[A-Z][A-Za-z\\'"]*)(?:(?:--|-|–)[A-Z][A-Za-z\\'"]*)*)['’]s\s+(inequality|theorem|lemma|bound|identity)\b/gu;
/** What may not stand between a citation and its locator. */
const BARRIER = /[.;!?](?:\s|$)|\n\s*\n|\$|\\\[|\\\(|\\begin\b|\\[A-Za-z]*ref\b|\\[A-Za-z]*cite/u;

/** The locators of one match of `LOCATOR`, or of every match in `text`: "Thm.~6.5, Cor.~6.7" ↦
 * ["Theorem 6.5", "Corollary 6.7"]; "Theorems 11.2 and 12.3" ↦ ["Theorem 11.2", "Theorem 12.3"]. */
function locatorsOf(m: RegExpMatchArray): string[] {
  const word = WORDS.find(([re]) => re.test(m[1]!))![1];
  return [...m[2]!.matchAll(new RegExp(NUM, "gu"))].map((n) => `${word} ${n[0]}`);
}
const namedOf = (m: RegExpMatchArray): string => `${m[1]}'s ${m[2]}`;
/** The locators of `text`: its numbered ones, else its named ones (a numbered locator wins: one result
 * named both ways is one site). */
export const locatorsIn = (text: string): string[] =>
  ((n) => (n.length > 0 ? n : [...text.matchAll(NAMED)].map(namedOf)))([...text.matchAll(LOCATOR)].flatMap(locatorsOf));

const PLURALS: Record<string, string> = { Theorem: "Theorems", Proposition: "Propositions", Lemma: "Lemmas", Corollary: "Corollaries" };
/** Several locators as one, the inverse of `locatorsIn`: ["Theorem 11.2", "Theorem 12.3"] ↦
 * "Theorems 11.2 and 12.3"; ["Theorem 6.5", "Corollary 6.7"] ↦ "Theorem 6.5 and Corollary 6.7". */
export function joinLocators(locators: readonly string[]): string {
  const groups: Array<{ word: string; nums: string[] }> = [];
  for (const l of locators) {
    const [word, num] = [l.slice(0, l.indexOf(" ")), l.slice(l.indexOf(" ") + 1)];
    if (groups.at(-1)?.word === word) groups.at(-1)!.nums.push(num);
    else groups.push({ word, nums: [num] });
  }
  return groups.map((g) => (g.nums.length === 1 ? `${g.word} ${g.nums[0]}` : `${PLURALS[g.word] ?? g.word} ${g.nums.slice(0, -1).join(", ")} and ${g.nums.at(-1)}`)).join(" and ");
}

/** `[from, to)` of `text` with up to `AROUND` characters of the same paragraph on each side, cut at
 * a word and marked with "…" where the paragraph goes on. */
const AROUND = 40;
function excerpt(text: string, from: number, to: number): string {
  const before = text.slice(Math.max(0, from - AROUND), from).replace(/^[\s\S]*\n\s*\n/u, "");
  const after = text.slice(to, to + AROUND).replace(/\n\s*\n[\s\S]*$/u, "");
  const head = before.length === AROUND && from > AROUND ? before.replace(/^\S*\s/u, "…") : before;
  const tail = after.length === AROUND && to + AROUND < text.length ? after.replace(/\s\S*$/u, "…") : after;
  return `${head}${text.slice(from, to)}${tail}`.replace(/\s+/gu, " ").trim();
}

/** A citation of `text` that carries a result locator: where it is, its keys, the locators, and
 * `[from, to)` spanning the citation and the locators next to it. */
interface LocatedCitation {
  start: number;
  keys: string[];
  locators: string[];
  from: number;
  to: number;
}

/** The citations of `text` (comments already blanked) that name a result, in order. */
function locatedCitations(text: string): LocatedCitation[] {
  const cites = [...text.matchAll(CITE)].map((m) => ({
    start: m.index!,
    end: m.index! + m[0].length,
    keys: m[3]!.split(",").map((k) => k.trim()).filter((k) => k.length > 0),
    // The post-note is the last optional argument (`\citep[see][Theorem 2]{key}`); a locator in
    // either is the paper's.
    inArg: locatorsIn(`${m[1] ?? ""} ${m[2] ?? ""}`),
    near: [] as Array<{ locators: string[]; start: number; end: number; named?: true }>,
  })).filter((c) => c.keys.length > 0);
  if (cites.length === 0) return [];
  // Each locator in the running text goes to the nearest citation it shares a clause with.
  for (const m of text.matchAll(LOCATOR)) {
    const start = m.index!;
    const end = start + m[0].length;
    if (cites.some((c) => c.start <= start && end <= c.end)) continue; // in an optional argument
    let best: { cite: (typeof cites)[number]; gap: number } | null = null;
    for (const c of cites) {
      if (c.inArg.length > 0) continue; // it carries its own
      const between = c.end <= start ? text.slice(c.end, start) : end <= c.start ? text.slice(end, c.start) : null;
      if (between === null || between.length > WINDOW || BARRIER.test(between)) continue;
      if (best === null || between.length < best.gap) best = { cite: c, gap: between.length };
    }
    best?.cite.near.push({ locators: locatorsOf(m), start, end });
  }
  // A named result goes to the citation right after it, in the same clause.
  for (const m of text.matchAll(NAMED)) {
    const start = m.index!;
    const end = start + m[0].length;
    if (cites.some((c) => c.start <= start && end <= c.end)) continue; // in an optional argument
    const c = cites.find((x) => x.start >= end);
    if (!c || c.inArg.length > 0) continue;
    const between = text.slice(end, c.start);
    if (between.length > WINDOW || BARRIER.test(between)) continue;
    c.near.push({ locators: [namedOf(m)], start, end, named: true });
  }
  return cites.flatMap((c) => {
    // The optional argument is where the paper put the locator; the text around the citation is
    // read only when it gives none.
    // a numbered locator wins over a named one: one result named both ways is one site
    const near = c.near.some((n) => !n.named) ? c.near.filter((n) => !n.named) : c.near;
    const locators = c.inArg.length > 0 ? c.inArg : near.flatMap((n) => n.locators);
    if (locators.length === 0) return [];
    return [{ start: c.start, keys: c.keys, locators: [...new Set(locators)], from: Math.min(c.start, ...near.map((n) => n.start)), to: Math.max(c.end, ...near.map((n) => n.end)) }];
  });
}

/** The published results a TeX text written outside the paper (a repair's proof) cites with a
 * locator, each once. */
export function citedResultsIn(tex: string): Array<{ keys: string[]; locator: string }> {
  const out = new Map<string, { keys: string[]; locator: string }>();
  for (const c of locatedCitations(blankTexComments(tex))) for (const locator of c.locators) out.set(`${c.keys.join(", ")}\u0000${locator}`, { keys: c.keys, locator });
  return [...out.values()];
}

/** The inline citation sites of every in-scope theorem-like environment's proof, in document order. */
export function inlineCitationSites(envs: Pick<EnvsJson, "envs">, scope: readonly string[]): InlineCitationSite[] {
  const scopeIds = new Set(scope);
  const sites: InlineCitationSite[] = [];
  for (const env of envs.envs) {
    if (!scopeIds.has(env.id) || !PROVED_KINDS.has(env.kind) || !env.proof) continue;
    const text = blankTexComments(env.proof);
    const cites = locatedCitations(text);
    if (cites.length === 0) continue;
    const units = regionUnits(env.proof);
    for (const c of cites) {
      const u = units.find((x) => x.start <= c.start && c.start < x.end);
      for (const locator of c.locators) {
        sites.push({
          env: env.id,
          key: c.keys.join(", "),
          keys: c.keys,
          locator,
          unit: u ? `${env.id}/proof/${u.p}/${u.u}` : `${env.id}/proof`,
          text: excerpt(text, c.from, c.to),
        });
      }
    }
  }
  return sites;
}

/** A result one proof invokes, whatever the number of places it cites it at: the unit of the
 * accounting. `id` names it in the reference core (`proof_citations[].site`). */
export interface CitationSite extends Omit<InlineCitationSite, "unit"> {
  id: string;
  units: string[];
}

export const siteId = (s: Pick<InlineCitationSite, "env" | "key" | "locator">): string => `${s.env} | ${s.key} | ${s.locator}`;

/** `inlineCitationSites` with the sites of one result in one proof merged, in document order. */
export function citationSites(envs: Pick<EnvsJson, "envs">, scope: readonly string[]): CitationSite[] {
  const out = new Map<string, CitationSite>();
  for (const { unit, ...site } of inlineCitationSites(envs, scope)) {
    const id = siteId(site);
    const had = out.get(id);
    if (!had) out.set(id, { ...site, id, units: [unit] });
    else if (!had.units.includes(unit)) had.units.push(unit);
  }
  return [...out.values()];
}

/**
 * Why a site is none the V1 agent can account for, or null when it is one. Its work is not in the
 * parsed bibliography: a cited node of that key fails the core gate, and the key is the runner's
 * copy. Or no passage that could register it is a whole TeX fragment: the citation sits inside a
 * group, a display or an environment that runs on past the units a leaf may take (an author's
 * note macro around the paragraph), and a node's text is never an unbalanced fragment.
 */
function unaccountable(envs: Pick<EnvsJson, "envs" | "bibliography">, site: CitationSite): string | null {
  if (!site.keys.some((k) => envs.bibliography.some((b) => b.key === k))) return `${site.key} is not in the parsed bibliography, so none can be made`;
  const proof = envs.envs.find((e) => e.id === site.env)?.proof ?? "";
  const units = regionUnits(proof);
  const held = units.map((u, i) => (site.units.includes(`${site.env}/proof/${u.p}/${u.u}`) ? i : -1)).filter((i) => i >= 0);
  const whole = held.some((at) => {
    for (let from = Math.max(0, at - MAX_CITATION_UNITS + 1); from <= at; from++) {
      for (let to = at; to < Math.min(units.length, from + MAX_CITATION_UNITS); to++) {
        if (texBalanceProblems(proof.slice(units[from]!.start, units[to]!.end)).length === 0) return true;
      }
    }
    return false;
  });
  return whole ? null : `no passage of at most ${MAX_CITATION_UNITS} units holding it is a whole TeX fragment, so none can be made`;
}

/** The sites the V1 agent accounts for (`unaccountable`); the others stay warnings (`lintInlineCitations`). */
export function accountableSites(envs: Pick<EnvsJson, "envs" | "bibliography">, scope: readonly string[]): CitationSite[] {
  return citationSites(envs, scope).filter((s) => unaccountable(envs, s) === null);
}

type Locator = TexEnv["lines"];
const locatorKey = (loc: Pick<Locator, "file" | "from" | "to">): string => `${loc.file}:${loc.from}-${loc.to}`;

/** The warning for a site no cited node registers; the line opens with the host's node id, as the
 * lint's other lines do (the V1.5 shard that grades the node is shown it). `why`: what keeps it one. */
function unregisteredLine(core: Pick<Core, "statements">, env: TexEnv, site: CitationSite, why = ""): string {
  const at = hostStatement(core, env) ?? core.statements.find((s) => s.tex_locator && locatorKey(s.tex_locator) === locatorKey(env.lines));
  return (
    `${at?.id ?? site.env}: the proof of ${site.env} invokes [${site.key}, ${site.locator}] (${site.units.join(", ")}): a published result used inside the proof, with no cited node of ` +
    `its own${why}. Not a defect of the node or of its wiring: grade the step as any use of a published result. paper: "${site.text}"`
  );
}

/**
 * One V1 lint warning per inline citation that nothing registers (`restated`); a result invoked at
 * several units of one proof is one line. Pure.
 */
export function inlineCitationWarnings(core: Pick<Core, "statements">, envs: Pick<EnvsJson, "envs">, scope: readonly string[]): string[] {
  const byId = new Map(envs.envs.map((e) => [e.id, e] as const));
  const lines: string[] = [];
  for (const site of citationSites(envs, scope)) {
    const env = byId.get(site.env)!;
    if (restated(core, env, hostStatement(core, env), site).length === 0) lines.push(unregisteredLine(core, env, site));
  }
  return lines;
}

/** The paper's own result printed at `env`. */
function hostStatement<C extends Pick<Core, "statements">>(core: C, env: TexEnv): C["statements"][number] | undefined {
  return core.statements.find((s) => s.status !== "cited" && s.tex_locator && locatorKey(s.tex_locator) === locatorKey(env.lines));
}

/** The cited leaves that register `site`: a cited statement of one of its works — of the site's
 * result, when its locator names one — at the host environment (its body or its proof) or among the
 * host's dependencies. */
function restated(core: Pick<Core, "statements">, env: TexEnv, host: Core["statements"][number] | undefined, site: Pick<CitationSite, "keys" | "locator">): Core["statements"] {
  const here = new Set([locatorKey(env.lines), ...(env.proofLines ? [locatorKey(env.proofLines)] : [])]);
  const names = (locator: string): boolean => ((l) => l.length === 0 || l.includes(site.locator))(locatorsIn(locator));
  return core.statements.filter(
    (s) =>
      s.status === "cited" && s.source && site.keys.includes(s.source.cite) && names(s.source.locator) &&
      ((s.tex_locator !== undefined && here.has(locatorKey(s.tex_locator))) || (host?.depends_on.includes(s.id) ?? false)),
  );
}

/** Why a site is not a use of the cited result (`dismissed_citations[].reason`). */
export const DISMISSAL_REASONS = {
  pointer: "a comparison or a pointer to the cited work",
  method: "a method or argument borrowed from the cited work, not its result",
  proved_here: "a result this paper proves itself",
  definition: "a definition or notation taken from the cited work",
} as const;
export interface DismissedCitation {
  site: string;
  reason: keyof typeof DISMISSAL_REASONS;
  note: string;
}

/** The most proof units an inline cited leaf may take: the citation and the step it gives, never the
 * rest of the argument. */
export const MAX_CITATION_UNITS = 3;

/** Where `text` sits in `proof` as a run of whole units: the ids of the run, or why it is none. */
function unitRun(envId: string, proof: string, text: string): string[] | string {
  const units = regionUnits(proof);
  let why = "is not a passage of that proof";
  for (let at = proof.indexOf(text); at >= 0; at = proof.indexOf(text, at + 1)) {
    const end = at + text.length;
    const run = units.filter((u) => u.start < end && at < u.end);
    if (run.length > 0 && proof.slice(run[0]!.start, at).trim() === "" && proof.slice(end, run.at(-1)!.end).trim() === "") return run.map((u) => `${envId}/proof/${u.p}/${u.u}`);
    why = "is not a run of whole units of that proof";
  }
  return why;
}

/**
 * Rule (i) of the V1 lint — the accounting of the inline citations. Every accountable site is covered
 * once: by one inline cited leaf (a statement with `cited_in`), by one dismissal, or by a cited leaf
 * the paper restates as an environment. An inline leaf is a run of at most `MAX_CITATION_UNITS`
 * consecutive whole units of its host's proof, verbatim, holding its site — its sites, when one
 * citation names several results; its source names their work and result(s); its host depends on it.
 * A site's units outside its leaf's run (the result is cited again elsewhere in the proof) are a
 * warning on the host. Each dismissal is also a warning, for the V1.5 referee to contest. A site no cited node can be
 * made for — its work is not in the parsed bibliography, or its proof is that of a cited leaf — is a
 * warning only. Pure.
 */
export function lintInlineCitations(
  core: Pick<Core, "statements">,
  envs: Pick<EnvsJson, "envs" | "bibliography">,
  scope: readonly string[],
  dismissed: readonly DismissedCitation[],
): { violations: string[]; warnings: string[] } {
  const violations: string[] = [];
  const warnings: string[] = [];
  const byId = new Map(envs.envs.map((e) => [e.id, e] as const));
  /** The cited leaf the paper states at `env` (its proof is then the cited work's, not this paper's). */
  const citedAt = (env: TexEnv): boolean => !hostStatement(core, env) && core.statements.some((s) => s.status === "cited" && s.cited_in === undefined && s.tex_locator && locatorKey(s.tex_locator) === locatorKey(env.lines));
  const sites: CitationSite[] = [];
  const exempt = new Set<string>();
  for (const site of citationSites(envs, scope)) {
    const env = byId.get(site.env)!;
    const none = unaccountable(envs, site);
    const why = none !== null ? ` (${none})` : citedAt(env) ? ` (${site.env} is itself a cited result)` : null;
    if (why === null) sites.push(site);
    else {
      exempt.add(site.id);
      if (restated(core, env, hostStatement(core, env), site).length === 0) warnings.push(unregisteredLine(core, env, site, why));
    }
  }
  const covering = new Map<string, string[]>(sites.map((s) => [s.id, []]));
  for (const n of core.statements) {
    if (n.cited_in === undefined) continue;
    const bad = (msg: string): void => void violations.push(`(i) ${n.id}: ${msg}`);
    const host = core.statements.find((s) => s.id === n.cited_in);
    const env = host?.tex_locator ? envs.envs.find((e) => locatorKey(e.lines) === locatorKey(host.tex_locator!)) : undefined;
    if (n.status !== "cited" || !n.source) bad("an inline citation is a `cited` node with its `source`");
    else if (!host || host.status === "cited" || !env || !env.proof || !env.proofLines) bad(`\`cited_in\` "${n.cited_in}" is not a result of this paper with a proof`);
    else {
      if (!n.tex_locator || locatorKey(n.tex_locator) !== locatorKey(env.proofLines)) bad(`its locator is not the proof of ${env.id}`);
      if (!host.depends_on.includes(n.id)) bad(`${host.id} must depend on it`);
      const run = unitRun(env.id, env.proof, n.statement);
      // One leaf may stand for the several results one citation names ("Theorems 11.2 and 12.3").
      const locators = ((l) => (l.length > 0 ? l : [n.source!.locator]))(locatorsIn(n.source.locator));
      if (typeof run === "string") bad(`its text ${run} (${env.id})`);
      else if (run.length > MAX_CITATION_UNITS) {
        bad(`it takes ${run.length} units (${run[0]} … ${run.at(-1)}); an inline citation takes at most ${MAX_CITATION_UNITS} — the unit holding the citation and the step the citation gives, not the argument around them`);
      }
      for (const locator of locators) {
        const site = sites.find((s) => s.env === env.id && s.keys.includes(n.source!.cite) && s.locator === locator);
        if (!site) {
          bad(`the proof of ${env.id} cites no [${n.source.cite}, ${locator}]`);
          continue;
        }
        covering.get(site.id)!.push(n.id);
        // (A citation the cut puts in no unit is at `<env>/proof`: any run of the proof may carry it.)
        if (typeof run !== "string" && site.units.some((u) => u !== `${env.id}/proof`) && !site.units.some((u) => run.includes(u))) bad(`its units (${run[0]} … ${run.at(-1)}) do not hold the citation, which is at ${site.units.join(", ")}`);
        // One result cited at several places of a proof is one site, and one leaf holds one of them.
        const outside = typeof run === "string" ? [] : site.units.filter((u) => u !== `${env.id}/proof` && !run.includes(u));
        if (outside.length > 0 && outside.length < site.units.length) {
          warnings.push(
            `${host.id}: the proof of ${env.id} cites [${n.source.cite}, ${locator}] also at ${outside.join(", ")}, outside the passage ${n.id} registers (${run[0]} … ${run.at(-1)}): ` +
              `a published result used there with no cited node covering that use. Not a defect of the node or of its wiring: grade the step as any use of a published result.`,
          );
        }
      }
    }
  }
  for (const d of dismissed) {
    const site = sites.find((s) => s.id === d.site);
    if (!site) {
      if (exempt.has(d.site)) continue; // nothing to account for: the site's warning stands
      violations.push(`(i) dismissed_citations: "${d.site}" is not a site of INLINE CITATIONS (${sites.map((s) => `"${s.id}"`).join(", ") || "the paper has none"})`);
      continue;
    }
    covering.get(site.id)!.push(`a dismissal (${d.reason})`);
    const env = byId.get(site.env)!;
    warnings.push(
      `${hostStatement(core, env)?.id ?? site.env}: the proof of ${site.env} cites [${site.key}, ${site.locator}] (${site.units.join(", ")}); the transcription reads the citation as ` +
        `${DISMISSAL_REASONS[d.reason]} and made no cited node for it${d.note.trim() ? ` (${d.note.trim()})` : ""}. paper: "${site.text}"`,
    );
  }
  for (const site of sites) {
    const by = covering.get(site.id)!;
    const env = byId.get(site.env)!;
    if (by.length > 1) violations.push(`(i) ${site.env}: the citation "${site.id}" is accounted for ${by.length} times (${by.join(", ")}) — once: one \`proof_citations\` entry or one dismissal`);
    else if (by.length === 0 && restated(core, env, hostStatement(core, env), site).length === 0) {
      violations.push(
        `(i) ${site.env}: its proof cites [${site.key}, ${site.locator}] at ${site.units.join(", ")} and the citation "${site.id}" is not accounted for — ` +
          `register it in \`proof_citations\` or dismiss it in \`dismissed_citations\`. paper: "${site.text}"`,
      );
    }
  }
  return { violations, warnings };
}

/** The most characters of a unit the block shows. */
const UNIT_SHOWN = 500;

/**
 * The INLINE CITATIONS block of the V1 prompt: each accountable site with its id, and the unit
 * holding the citation between its neighbours (`>` marks it). Empty when the paper has none.
 */
export function inlineCitationsBlock(envs: Pick<EnvsJson, "envs" | "bibliography">, scope: readonly string[]): string[] {
  const byId = new Map(envs.envs.map((e) => [e.id, e] as const));
  const out: string[] = [];
  for (const site of accountableSites(envs, scope)) {
    const proof = byId.get(site.env)!.proof!;
    const units = regionUnits(proof).map((u) => ({ id: `${site.env}/proof/${u.p}/${u.u}`, text: proof.slice(u.start, u.end).replace(/\s+/gu, " ").trim() }));
    const shown = new Set<number>();
    const at = new Set<number>();
    for (const id of site.units) {
      const k = units.findIndex((u) => u.id === id);
      if (k < 0) continue;
      at.add(k);
      for (const j of [k - 1, k, k + 1]) if (j >= 0 && j < units.length) shown.add(j);
    }
    out.push(`- site "${site.id}" — the proof of ${site.env} cites [${site.key}, ${site.locator}]`);
    for (const k of [...shown].sort((a, b) => a - b)) {
      const t = units[k]!.text;
      out.push(`  ${at.has(k) ? ">" : " "} ${units[k]!.id}: ${t.length > UNIT_SHOWN ? `${t.slice(0, UNIT_SHOWN)}…` : t}`);
    }
  }
  return out;
}

/**
 * One line per published result a REPAIR's written proof (its ops' TeX; its proof note when no op
 * rewrites the proof) cites with a locator while no inline cited leaf the repaired result still
 * depends on (one its repair `drops` is gone) registers it: the fixer may invoke a result the
 * paper's proof did not. For the V1.5 referee, with
 * the V1 lint warnings; the line opens with the repaired node. Pure.
 */
export function repairCitationWarnings<P extends { node: string; ops?: ReadonlyArray<{ tex?: string }> | null; proof_note?: string | null; drops?: readonly string[] | null }>(
  core: Pick<Core, "statements">,
  patches: readonly P[],
  rewritesProof: (p: P) => boolean,
): string[] {
  const out: string[] = [];
  for (const p of patches) {
    const deps = core.statements.find((s) => s.id === p.node)?.depends_on ?? [];
    const written = [...(p.ops ?? []).map((o) => o.tex ?? ""), ...(rewritesProof(p) ? [] : [p.proof_note ?? ""])].join("\n");
    for (const c of citedResultsIn(written)) {
      if (core.statements.some((s) => s.cited_in === p.node && deps.includes(s.id) && !p.drops?.includes(s.id) && s.source && c.keys.includes(s.source.cite) && locatorsIn(s.source.locator).includes(c.locator))) continue;
      // (nor is a result the paper states as a cited leaf — the node itself, or one it depends on)
      if (core.statements.some((s) => s.status === "cited" && !s.cited_in && (s.id === p.node || deps.includes(s.id)) && s.source && c.keys.includes(s.source.cite) && locatorsIn(s.source.locator).some((l) => locatorsIn(c.locator).includes(l)))) continue;
      out.push(
        `${p.node}: the repair of ${p.node} cites [${c.keys.join(", ")}, ${c.locator}] in the proof it writes: a published result used inside the repaired proof, with no cited node of ` +
          `its own. Not a defect of the node or of its wiring: grade the step as any use of a published result.`,
      );
    }
  }
  return out;
}
