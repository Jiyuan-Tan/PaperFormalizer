/**
 * The SOURCE of every result the paper cites rather than proves — what V1.5 checks the paper's
 * statement of it against. Fail-closed: a citation is the one place the referee would otherwise
 * take the paper's word, so an unchecked citation could carry a false "known result" into the
 * certified theorems.
 *
 * Never a source: the paper's own quote (V1 copies it into the cited node's
 * `verbatim_statement`, so checking against it would check the paper against itself).
 * Sources, in order:
 *   1. a file the user supplied at `discovery/cited_sources/<key>.txt` (or `.tex`) — reported
 *      as the user's attestation, never as "verified against the publication";
 *   2. the arXiv e-print named in the bibliography entry, fetched by the runner and cached at
 *      `discovery/cited_sources/<key>.arxiv.tex`;
 *   3. neither, and the user declared the cited work INACCESSIBLE at
 *      `discovery/cited_sources/<key>.unavailable` (what was tried, non-empty): the run continues
 *      with the citation taken as the paper prints it and NOT checked against the cited work —
 *      its verdict says so, every result resting on it is reported conditional on an unchecked
 *      citation, and a supplied source later re-opens it.
 * No source and no declaration → V1.5 checkpoints and asks the user to supply one.
 */
import { existsSync } from "node:fs";
import { mkdir, readFile, readdir, writeFile } from "node:fs/promises";
import path from "node:path";
import type { Core } from "../core/schema.js";
import { fetchArxivTex, type CitedMatchTarget, type FetchBytes } from "../formalization/citation_fetch.js";
import { locatorsIn } from "./inline_citations.js";
import { VERIFY_FILES, type EnvsJson } from "./types.js";

export const CITED_SOURCES_DIR = "discovery/cited_sources";

export interface CitedSource {
  nodeId: string;
  key: string;
  locator: string;
  mode: "supplied" | "fetched" | "unavailable";
  /** Provenance for the prompt and the report. */
  detail: string;
  /** The source text shown to the referee (an excerpt around the locator for long sources). */
  text: string;
}

export interface MissingSource {
  nodeId: string;
  key: string;
  locator: string;
  citation: string;
  /** Where the user should put the source. */
  file: string;
  why: string;
}

/** The suffix of the file declaring a cited work inaccessible. */
export const UNAVAILABLE_SUFFIX = ".unavailable";

/** Prefix of the verdict detail of a cited result whose source was declared unavailable. */
export const UNAVAILABLE_DETAIL_PREFIX = "[cited source unavailable — not checked against the cited work]";

/** A citation key as a file name. */
export function sourceFileKey(key: string): string {
  return key.replace(/[^A-Za-z0-9._-]/g, "_");
}

/** An arXiv identifier named in a bibliography entry, if any. */
export function arxivIdOf(text: string): string | null {
  const m =
    /arxiv(?:\.org\/(?:abs|pdf)\/|\s*[:=]?\s*\{?\s*)((?:\d{4}\.\d{4,5})|(?:[a-z-]+(?:\.[A-Z]{2})?\/\d{7}))/i.exec(text) ??
    /eprint\s*=\s*[{"]\s*((?:\d{4}\.\d{4,5})|(?:[a-z-]+\/\d{7}))/i.exec(text);
  return m ? m[1]! : null;
}

/** The raw bibliography entry for `key` in the source tree's .bib / .bbl files. */
async function rawBibEntry(sourceDir: string, key: string): Promise<string> {
  const out: string[] = [];
  const walk = async (dir: string): Promise<void> => {
    for (const e of await readdir(dir, { withFileTypes: true })) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) await walk(p);
      else if (/\.(bib|bbl)$/i.test(e.name)) {
        const t = await readFile(p, "utf8");
        const esc = key.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
        const bib = new RegExp(`@\\w+\\s*\\{\\s*${esc}\\s*,[\\s\\S]*?(?=\\n\\s*@|$)`).exec(t);
        const bbl = new RegExp(`\\\\bibitem(?:\\[[^\\]]*\\])?\\{${esc}\\}[\\s\\S]*?(?=\\\\bibitem|\\\\end\\{thebibliography\\}|$)`).exec(t);
        if (bib) out.push(bib[0]);
        if (bbl) out.push(bbl[0]);
      }
    }
  };
  if (existsSync(sourceDir)) await walk(sourceDir);
  return out.join("\n");
}

/** A window of a long source around the first mention of the locator (else its start): the locator
 * whole, then each result it names ("Theorem 11.2", "Theorem 12.3"), then its sectioned numbers
 * ("3.27" — a bare "2" locates nothing), then its words. */
export function excerptAround(text: string, locator: string, cap = 40000, byResult = false): string {
  if (text.length <= cap) return text;
  const words = locator.split(/[\s~.,;:()]+/).filter((w) => w.length > 2);
  // (`byResult`: the finer probes, for an inline leaf's source of record — the window of an ordinary
  // cited leaf is part of its verdict's basis and stays as it was cut)
  const numbers: string[] = byResult ? locator.match(/(?:[A-Z]\.)?\d+(?:\.\d+)+/g) ?? [] : [];
  const lower = text.toLowerCase();
  let at = -1;
  for (const probe of [locator, ...(byResult ? locatorsIn(locator) : []), ...numbers, ...words]) {
    // A number is matched whole: "3.27" is not found in "13.270".
    at = numbers.includes(probe) ? text.search(new RegExp(`(?<![\\d.])${probe.replace(/\./g, "\\.")}(?!\\.?\\d)`)) : lower.indexOf(probe.toLowerCase());
    if (at >= 0) break;
  }
  const start = Math.max(0, (at >= 0 ? at : 0) - cap / 4);
  return `${start > 0 ? "[… earlier source text omitted …]\n" : ""}${text.slice(start, start + cap)}\n[… later source text omitted …]`;
}

/**
 * The source of record of an inline cited leaf (`cited_in`) for the Lean stages: the file of the
 * cited work this run's referee was shown — never the leaf's own text, which is the paper's passage.
 * A supplied file is `attested`, the runner's arXiv cache `fetched`; no file (the work was declared
 * unavailable, or the run never resolved it) is `unverifiable`.
 */
export async function citedSourceOfRecord(runDir: string, key: string, locator: string): Promise<CitedMatchTarget> {
  const dir = path.join(runDir, CITED_SOURCES_DIR);
  const fileKey = sourceFileKey(key);
  for (const [ext, mode] of [[".txt", "attested"], [".tex", "attested"], [".arxiv.tex", "fetched"]] as const) {
    const file = path.join(dir, `${fileKey}${ext}`);
    if (!existsSync(file)) continue;
    const rel = path.posix.join(CITED_SOURCES_DIR, `${fileKey}${ext}`);
    return { text: excerptAround(await readFile(file, "utf8"), locator, 12000, true), mode, detail: `${mode === "attested" ? "source supplied" : "arXiv e-print cached"} at ${rel} @ ${locator}` };
  }
  return { text: "", mode: "unverifiable", detail: `no source of ${key} at ${CITED_SOURCES_DIR}/${fileKey}.txt` };
}

export async function resolveCitedSources(args: {
  runDir: string;
  core: Core;
  envs: EnvsJson | null;
  fetchBytes?: FetchBytes;
}): Promise<{ sources: CitedSource[]; missing: MissingSource[] }> {
  const { runDir, core } = args;
  const dir = path.join(runDir, CITED_SOURCES_DIR);
  const sources: CitedSource[] = [];
  const missing: MissingSource[] = [];
  for (const st of core.statements) {
    if (st.status !== "cited") continue;
    const key = st.source?.cite ?? "";
    const locator = st.source?.locator ?? "";
    const fileKey = sourceFileKey(key || st.id);
    const citation = args.envs?.bibliography.find((b) => b.key === key)?.text ?? "";
    const supplied = [".txt", ".tex"].map((ext) => path.join(dir, `${fileKey}${ext}`)).find((p) => existsSync(p));
    if (supplied) {
      sources.push({
        nodeId: st.id,
        key,
        locator,
        mode: "supplied",
        detail: `source supplied by the user at ${path.relative(runDir, supplied)}`,
        text: excerptAround(await readFile(supplied, "utf8"), locator),
      });
      continue;
    }
    const arxiv = arxivIdOf(`${citation}\n${await rawBibEntry(path.join(runDir, VERIFY_FILES.sourceDir), key)}`);
    if (arxiv) {
      const cache = path.join(dir, `${fileKey}.arxiv.tex`);
      let tex = existsSync(cache) ? await readFile(cache, "utf8") : await fetchArxivTex(arxiv, args.fetchBytes);
      if (tex && !existsSync(cache)) {
        await mkdir(dir, { recursive: true });
        await writeFile(cache, tex, "utf8");
      }
      if (tex) {
        sources.push({
          nodeId: st.id,
          key,
          locator,
          mode: "fetched",
          detail: `arXiv:${arxiv} e-print (fetched by the runner; the arXiv version may differ from the published one)`,
          text: excerptAround(tex, locator),
        });
        continue;
      }
    }
    const declared = path.join(dir, `${fileKey}${UNAVAILABLE_SUFFIX}`);
    const reason = existsSync(declared) ? (await readFile(declared, "utf8")).replace(/\s+/g, " ").trim() : null;
    if (reason) {
      sources.push({
        nodeId: st.id,
        key,
        locator,
        mode: "unavailable",
        detail: `NOT checked — the cited work was declared inaccessible at ${path.relative(runDir, declared)}: ${reason}`,
        text: `SOURCE UNAVAILABLE: ${reason}`,
      });
      continue;
    }
    missing.push({
      nodeId: st.id,
      key: key || "(no citation key)",
      locator,
      citation: citation || "(no bibliography entry)",
      file: path.posix.join(CITED_SOURCES_DIR, `${fileKey}.txt`),
      why:
        (arxiv ? `arXiv:${arxiv} could not be fetched` : "no arXiv identifier in its bibliography entry") +
        (reason === "" ? `; ${fileKey}${UNAVAILABLE_SUFFIX} is empty — say what was tried` : ""),
    });
  }
  return { sources, missing };
}

/**
 * A cited result whose source was declared unavailable is taken on the paper's word: the referee
 * cannot check the citation, so an `unclear` grade (or a clean one) becomes `ok` with the detail
 * saying it was not checked. A refutation the referee could still exhibit — the statement as the
 * paper prints it is false, with a witness — stands, as does a bookkeeping grade. Pure.
 */
export function settleUnavailableCited<V extends { id: string; correctness: string; detail: string; witness?: string | null }>(
  verdicts: readonly V[],
  sources: readonly CitedSource[],
): V[] {
  const unavailable = new Map(sources.filter((c) => c.mode === "unavailable").map((c) => [c.nodeId, c] as const));
  return verdicts.map((v) => {
    const c = unavailable.get(v.id);
    if (!c || (v.correctness !== "unclear" && v.correctness !== "ok") || v.detail.startsWith(UNAVAILABLE_DETAIL_PREFIX)) return v;
    return { ...v, correctness: "ok", witness: null, detail: `${UNAVAILABLE_DETAIL_PREFIX} (${c.detail.replace(/^NOT checked — /, "")}) ${v.detail}`.trim() };
  });
}
