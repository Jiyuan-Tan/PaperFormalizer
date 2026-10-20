// Best-effort resolver for the source text a `gate_class:"cited"` node is matched
// against at F2.5. Policy (user-confirmed): VERBATIM-FIRST — the cite: node's
// `verbatim_statement` is the reliable match target (mode "attested"); when absent
// and an `arxiv` handle is present we best-effort fetch the e-print tex (mode
// "fetched"); if neither yields text the node is "unverifiable". The fetch is injectable
// so the unit tests never touch the network.
import { gunzipSync } from "node:zlib";

import { blankTexComments } from "../shared/tex_text.js";
import type { Citation } from "./plan/schema.js";

/** Minimal source-of-record shape the F2.5/F4 cited review resolves. */
export type ResolvableCitation = Pick<Citation, "id" | "locator"> &
  Partial<Pick<Citation, "verbatim_statement" | "arxiv" | "doi" | "url">>;

export type CitedMatchMode = "attested" | "fetched" | "unverifiable";

export interface CitedMatchTarget {
  /** The exact statement text the Lean `def` must encode (empty when unverifiable). */
  text: string;
  /** Where `text` came from. */
  mode: CitedMatchMode;
  /** Human-readable provenance for logs / the prompt header. */
  detail: string;
}

/** Network seam — defaults to the global fetch; tests inject a stub. */
export type FetchBytes = (url: string) => Promise<Uint8Array | null>;

/** The fetch is awaited per cited node inside an F4 pass: a hung connection must not hold the
 *  whole convergence review. Past the deadline the source counts as unavailable. */
export const CITED_FETCH_TIMEOUT_MS = 60_000;

/** The global fetch with a deadline (null on any failure, the timeout included). */
export const fetchBytesWithTimeout = (timeoutMs: number): FetchBytes => async (url) => {
  try {
    const res = await fetch(url, { signal: AbortSignal.timeout(timeoutMs) });
    if (!res.ok) return null;
    return new Uint8Array(await res.arrayBuffer());
  } catch {
    return null;
  }
};

const defaultFetchBytes: FetchBytes = fetchBytesWithTimeout(CITED_FETCH_TIMEOUT_MS);

/** True when the bytes are a gzip stream (magic 0x1f 0x8b). */
function isGzip(b: Uint8Array): boolean {
  return b.length > 2 && b[0] === 0x1f && b[1] === 0x8b;
}

/** True when the buffer is a (ustar) tar archive: magic "ustar" at offset 257. */
function isTar(b: Uint8Array): boolean {
  if (b.length < 262) return false;
  return String.fromCharCode(b[257], b[258], b[259], b[260], b[261]) === "ustar";
}

/** Minimal ustar reader: concatenate the contents of every `.tex` member. */
function texFromTar(buf: Uint8Array): string {
  const dec = new TextDecoder("utf-8", { fatal: false });
  const files: Array<{ name: string; text: string }> = [];
  let off = 0;
  while (off + 512 <= buf.length) {
    const header = buf.subarray(off, off + 512);
    // Empty (all-zero) header block → end of archive.
    if (header.every((x) => x === 0)) break;
    const name = dec.decode(header.subarray(0, 100)).replace(/\0.*$/, "").trim();
    const sizeOctal = dec.decode(header.subarray(124, 136)).replace(/\0.*$/, "").trim();
    const size = parseInt(sizeOctal, 8) || 0;
    const dataStart = off + 512;
    if (name.endsWith(".tex")) {
      files.push({ name, text: dec.decode(buf.subarray(dataStart, dataStart + size)) });
    }
    // Advance past data, rounded up to the next 512-byte boundary.
    off = dataStart + Math.ceil(size / 512) * 512;
  }
  // ORDER MATTERS, because the consumer TRUNCATES. A multi-file arXiv bundle is emitted in
  // tar order, which is arbitrary (often alphabetical), and the F2.5/F4 reviewer is shown only
  // the leading slice of this string. Concatenating blindly therefore handed the referee a
  // symbol-macro fragment (`amssym.tex`) while the cited theorem sat megabytes further in
  // `paper/section3_theory.tex`, and the referee — correctly — reported it could not verify
  // a citation that was in fact accurate. A citation silently "unverifiable" for a packaging
  // reason is worse than a loud failure: the honest next move looks like editing our account
  // of a source we cannot read, which is how a citation gets laundered.
  //
  // So lead with the document root, then the files carrying sectioning/theorem content, and
  // put pure macro/style fragments last. Nothing is dropped — a bundle whose theorem lives
  // in an \input-ed file is still present — but the truncation window now opens on real text.
  const isRoot = (f: { text: string }) => /\\documentclass|\\begin\{document\}/.test(blankTexComments(f.text));
  // Include the near-universal `\newtheorem` ABBREVIATIONS (`thm`, `lem`, `prop`,
  // `cor`, `defn`, `assump`, `claim`, `rem`, `conj`): a sections/ file written
  // with `\begin{thm}` and no `\section` ranked as a macro fragment, sorted
  // last, and fell outside the referee's truncation window — grading an
  // accurate citation "unverifiable" for a packaging reason.
  const hasContent = (f: { text: string }) =>
    /\\(section|subsection|chapter)\b|\\begin\{(theorem|thms?|lemma|lem|proposition|prop|corollary|cor|definition|defn?|assumption|assump?|claim|remark|rem|conjecture|conj)\*?\}/i
      .test(f.text);
  const rank = (f: { text: string }): number => (isRoot(f) ? 0 : hasContent(f) ? 1 : 2);
  return files
    .map((f, i) => ({ f, i }))
    .sort((a, b) => rank(a.f) - rank(b.f) || a.i - b.i)
    .map(({ f }) => `${f.text}\n`)
    .join("");
}

/** Decode an arXiv e-print payload (gzip of either a tar or a single .tex) to tex. */
function decodeEprint(bytes: Uint8Array): string | null {
  let buf = bytes;
  if (isGzip(buf)) {
    try {
      buf = new Uint8Array(gunzipSync(buf));
    } catch {
      return null;
    }
  }
  if (isTar(buf)) {
    const tex = texFromTar(buf);
    return tex.trim() ? tex : null;
  }
  // Single uncompressed source file — accept only if it looks like TeX.
  const text = new TextDecoder("utf-8", { fatal: false }).decode(buf);
  return /\\(begin|documentclass|section|lemma|theorem)/.test(text) ? text : null;
}

/** Fetch an arXiv e-print and decode it to tex (null when unavailable). */
export async function fetchArxivTex(id: string, fetchBytes: FetchBytes = defaultFetchBytes): Promise<string | null> {
  const bytes = await fetchBytes(`https://arxiv.org/e-print/${id}`);
  return bytes ? decodeEprint(bytes) : null;
}

/**
 * Resolve the match target for one cited citation. Verbatim-first; arXiv fetch is
 * best-effort and only used when no verbatim statement is supplied.
 */
export async function resolveCitedTarget(
  c: ResolvableCitation,
  fetchBytes: FetchBytes = defaultFetchBytes,
): Promise<CitedMatchTarget> {
  const verbatim = c.verbatim_statement?.trim();
  if (verbatim) {
    return { text: verbatim, mode: "attested", detail: `attested verbatim statement @ ${c.locator}` };
  }
  if (c.arxiv) {
    const bytes = await fetchBytes(`https://arxiv.org/e-print/${c.arxiv}`);
    const tex = bytes ? decodeEprint(bytes) : null;
    if (tex) {
      return { text: tex, mode: "fetched", detail: `arXiv:${c.arxiv} e-print tex @ ${c.locator}` };
    }
  }
  if (!c.arxiv && (c.doi || c.url)) {
    return {
      text: "",
      mode: "unverifiable",
      // why: DOI/URL fetching is intentionally unsupported; require an attested target instead.
      detail: `citation ${c.id} has doi/url but no arXiv fetch; add verbatim_statement for ${c.locator}`,
    };
  }
  return {
    text: "",
    mode: "unverifiable",
    detail: `no verbatim statement and no fetchable source for ${c.id}`,
  };
}
