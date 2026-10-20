import { gzipSync } from "node:zlib";

import { describe, it, expect } from "vitest";

import { resolveCitedTarget, type FetchBytes } from "../../src/formalization/citation_fetch.js";
import type { Citation } from "../../src/formalization/plan/schema.js";

const base: Citation = {
  id: "cite:demo",
  title: "A Result",
  authors: "Author",
  year: 2020,
  locator: "Theorem 3.1",
};

const neverFetch: FetchBytes = async () => null;

/** Build a ustar archive holding each `[name, content]` member in order. */
function tar(...members: Array<[string, string]> | [string, string]): Uint8Array {
  const entries: Array<[string, string]> =
    typeof members[0] === "string"
      ? [members as [string, string]]
      : (members as Array<[string, string]>);
  const enc = new TextEncoder();
  const blocks: number[] = [];
  for (const [name, content] of entries) {
    const data = enc.encode(content);
    const header = new Uint8Array(512);
    header.set(enc.encode(name), 0);
    header.set(enc.encode("0000644\0"), 100); // mode
    header.set(enc.encode(data.length.toString(8).padStart(11, "0") + "\0"), 124); // size (octal)
    header.set(enc.encode("ustar\0"), 257); // magic
    const padded = new Uint8Array(Math.ceil(data.length / 512) * 512);
    padded.set(data);
    blocks.push(...header, ...padded);
  }
  return new Uint8Array([...blocks, ...new Uint8Array(1024)]); // two zero end blocks
}

describe("resolveCitedTarget", () => {
  it("is verbatim-first (attested) even when an arxiv handle exists", async () => {
    const c = { ...base, arxiv: "2207.11825", verbatim_statement: "R_n ≥ c · n^{-2α/(2α+1)}" };
    const r = await resolveCitedTarget(c, neverFetch);
    expect(r.mode).toBe("attested");
    expect(r.text).toContain("R_n");
  });

  it("leads a multi-file bundle with the document root, not an alphabetically-first macro file", async () => {
    // Regression (stat_doseresponse_minimax_elbow, 2026-07-29). A real 42.9 MB arXiv bundle
    // unpacked with `amssym.tex` first in tar order; every `.tex` was concatenated blindly
    // and the referee sees only the LEADING slice of the result, so it was handed a
    // symbol-macro fragment and honestly reported it could not verify a citation that was
    // in fact accurate. Ordering is load-bearing precisely because the consumer truncates.
    const archive = gzipSync(Buffer.from(tar(
      ["amssym.tex", `\\def\\Bbb{\\bf}\n${"% padding macro line\n".repeat(400)}`],
      ["paper/main.tex", "\\documentclass{article}\\begin{document}\\input{section3_theory}\\end{document}"],
      ["paper/section3_theory.tex", "\\section{Theory}\\begin{theorem}\\label{thm1} the cited result \\end{theorem}"],
    )));
    const fetchStub: FetchBytes = async (url) =>
      url.endsWith("/e-print/2210.06448") ? new Uint8Array(archive) : null;

    const r = await resolveCitedTarget({ ...base, arxiv: "2210.06448" }, fetchStub);

    expect(r.mode).toBe("fetched");
    // the window the referee actually reads must open on the document, not the macros
    expect(r.text.slice(0, 6000)).toContain("\\begin{document}");
    expect(r.text.slice(0, 6000)).toContain("the cited result");
    expect(r.text.indexOf("\\documentclass")).toBeLessThan(r.text.indexOf("\\def\\Bbb"));
    // nothing is dropped — the macro file is still present, just last
    expect(r.text).toContain("\\def\\Bbb");
  });

  it("is unverifiable when no verbatim statement and no fetchable source", async () => {
    const r = await resolveCitedTarget(base, neverFetch);
    expect(r.mode).toBe("unverifiable");
    expect(r.text).toBe("");
  });

});

describe("fetchBytesWithTimeout", () => {
  it("gives up on a hung connection after the deadline (the fetch is awaited inside an F4 pass)", async () => {
    const { fetchBytesWithTimeout, CITED_FETCH_TIMEOUT_MS } = await import("../../src/formalization/citation_fetch.js");
    expect(CITED_FETCH_TIMEOUT_MS).toBeGreaterThan(0);
    const realFetch = globalThis.fetch;
    let aborted = false;
    globalThis.fetch = ((_url: string, init?: { signal?: AbortSignal }) =>
      new Promise((_resolve, reject) => {
        init?.signal?.addEventListener("abort", () => { aborted = true; reject(init.signal!.reason); });
      })) as typeof fetch;
    try {
      expect(await fetchBytesWithTimeout(20)("https://arxiv.org/e-print/0000.00000")).toBeNull();
      expect(aborted).toBe(true);
    } finally {
      globalThis.fetch = realFetch;
    }
  });
});
