// Reuse whenever possible (owner, 2026-11-21): a segmenter edit never drops what its file holds, a node
// not located is handed to V1's agent (never a cold reading), and a revision read as far fewer results
// than its version is first taken for a failed parse.
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { changedMacros, lostNodeViolations, nodesUsingMacros, readSetupChangeAnswer, setupChangeNodes, setupExcerptCut } from "../../src/verify/reanchor.js";
import { paperIndex } from "../../src/verify/referee_slices.js";
import { segmentEntriesDropped, type Segments } from "../../src/verify/segments.js";
import { fewerResultsThanBefore, inPlaceRevisionRefusal } from "../../src/verify/stage_v1.js";
import { closeInPlaceFix, freezeVersion, startInPlaceFix } from "../../src/verify/revision.js";
import { hashSourceTree } from "../../src/verify/source_bundle.js";
import { createVerifyInitialState } from "../../src/state.js";
import { mkdir, mkdtemp, writeFile, readFile, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";

describe("a segmenter's edit of an existing file", () => {
  const file: Segments = {
    results: [
      { kind: "lemma", printed: "Lemma 4.2", lines: [10, 12] },
      { kind: "theorem", id: "thm-seg-1", lines: [20, 22] },
      { kind: "definition", lines: [30, 31] },
    ],
    bindings: [{ result: "lemma-3.1", proof_lines: [40, 44] }],
    extend: [{ env: "prop-2", lines: [50, 53] }],
  };
  it("keeps every entry: a file it empties (11-16) names them all", () => {
    expect(segmentEntriesDropped(file, { results: [], bindings: [], extend: [] })).toEqual([
      "result lemma Lemma 4.2", "result theorem thm-seg-1", "result definition at line 30", "the proof binding of lemma-3.1", "the extension of prop-2",
    ]);
  });
  it("matches each entry one to one by any of its head, id or start: a corrected kind or head is no drop, a duplicate dropped is", () => {
    const before: Segments = { results: [{ kind: "lemma", id: "l1", lines: [10, 12] }, { kind: "claim" as never, printed: "Claim", lines: [20, 21] }, { kind: "claim" as never, printed: "Claim", lines: [30, 31] }], bindings: [], extend: [] };
    const fixed: Segments = { results: [{ kind: "proposition", id: "l1", printed: "Proposition 2", lines: [10, 12] }, { kind: "claim" as never, printed: "Claim", lines: [20, 21] }, { kind: "claim" as never, printed: "Claim", lines: [30, 31] }], bindings: [], extend: [] };
    expect(segmentEntriesDropped(before, fixed)).toEqual([]);
    expect(segmentEntriesDropped(before, { ...fixed, results: fixed.results.slice(0, 2) })).toEqual(["result claim Claim"]);
  });
  it("may add entries and move their lines: nothing is dropped", () => {
    const after: Segments = {
      results: [{ kind: "lemma", printed: "Lemma 4.2", lines: [11, 13] }, { kind: "theorem", id: "thm-seg-1", lines: [21, 23] }, { kind: "definition", lines: [30, 31] }, { kind: "corollary", printed: "Corollary 5.2", lines: [60, 61] }],
      bindings: [...file.bindings, { result: "thm-2", proof_lines: [70, 72] }],
      extend: file.extend,
    };
    expect(segmentEntriesDropped(file, after)).toEqual([]);
  });
});

describe("a node not located in the revision", () => {
  const core = {
    statements: [{ id: "lem:aux", kind: "lemma", statement: "If $f$ is convex then $f$ is continuous on the interior.", depends_on: [] }],
    assumptions: [{ id: "ass:bounded", kind: "regularity", condition: "The outcome is bounded." }],
    definitions: [],
  } as unknown as Core;
  it("goes to V1's agent with what it read: re-point it keeping its id, or remove it", () => {
    const [a, b] = lostNodeViolations(core, ["lem:aux", "ass:bounded"]);
    expect(a).toBe('(reanchor) lem:aux was not located in the revised paper; it read: "If $f$ is convex then $f$ is continuous on the interior.". In discovery/core_refs.json, point it at its text in the revised paper, keeping the id lem:aux; if the revision removed it, remove the node and say so in your reply.');
    expect(b).toMatch(/^\(reanchor\) ass:bounded was not located in the revised paper; it read: "The outcome is bounded\."/);
    expect(lostNodeViolations(core, [])).toEqual([]);
  });
});

describe("a revision read as far fewer results than its version", () => {
  it("under half of two or more", () => {
    expect(fewerResultsThanBefore(17, 0)).toBe(true);
    expect(fewerResultsThanBefore(10, 4)).toBe(true);
    expect(fewerResultsThanBefore(10, 5)).toBe(false);
    expect(fewerResultsThanBefore(1, 0)).toBe(false);
    expect(fewerResultsThanBefore(5, 9)).toBe(false);
  });
});

describe("the setup-change check's answer", () => {
  const ids = new Set(["thm:a", "lem:b"]);
  it("is read strictly: all, or nodes of the core; anything else is no answer", () => {
    expect(readSetupChangeAnswer({ all: true, reason: "the standing assumption changed", affected: [] }, ids)).toEqual({ all: true });
    expect(readSetupChangeAnswer({ all: false, reason: "", affected: [{ id: "lem:b", reason: "x" }, { id: "lem:b", reason: "y" }] }, ids)).toEqual({ all: false, affected: ["lem:b"] });
    expect(readSetupChangeAnswer({ all: false, reason: "", affected: [] }, ids)).toEqual({ all: false, affected: [] });
    expect(readSetupChangeAnswer({ all: false, affected: [{ id: "thm:c" }] }, ids)).toBeNull();
    expect(readSetupChangeAnswer({ all: false }, ids)).toBeNull();
    expect(readSetupChangeAnswer(null, ids)).toBeNull();
  });
  it("reads every node of the core, one line each", () => {
    const core = { statements: [{ id: "thm:a", statement: "A holds." }], assumptions: [{ id: "ass:x", condition: "X is finite." }], definitions: [] } as unknown as Core;
    expect(setupChangeNodes(core)).toBe("ass:x: X is finite.\nthm:a: A holds.");
  });
});

describe("a source edited in place", () => {
  it("is frozen without its text by a --revise (it is not the version's), and is not re-pointed with nothing on file to re-point", async () => {
    const runDir = await mkdtemp(path.join(os.tmpdir(), "inplace-"));
    try {
      await mkdir(path.join(runDir, "source"), { recursive: true });
      await mkdir(path.join(runDir, "discovery"), { recursive: true });
      await writeFile(path.join(runDir, "source", "main.tex"), "as read", "utf8");
      const state = createVerifyInitialState("q", { phase: "done", source: { input: "/p/main.tex", main_file: "main.tex", sha256: await hashSourceTree(path.join(runDir, "source")) }, targets: null, core_sha256: null } as never);
      await writeFile(path.join(runDir, "source", "main.tex"), "edited in place", "utf8");
      expect(await inPlaceRevisionRefusal(runDir, state.verify!)).toMatch(/not on file/);
      const frozen = await freezeVersion({ runDir, state });
      expect(frozen).toMatchObject({ version: 1, source_edited_in_place: true });
      expect(existsSync(path.join(runDir, "versions", "v1", "source"))).toBe(false);
      expect(JSON.parse(await readFile(path.join(runDir, "versions", "v1", "version.json"), "utf8")).source_edited_in_place).toBe(true);
      // a frozen copy of another source in the way: refused
      await writeFile(path.join(runDir, "versions", "v1", "version.json"), JSON.stringify({ version: 1, source_sha256: "other" }), "utf8");
      for (const f of ["discovery/core_refs.json", "discovery/envs.json", "discovery/flat.tex", "discovery/flat.linemap.json", "discovery/core.transcribed.json"]) await writeFile(path.join(runDir, f), "{}", "utf8");
      expect(await inPlaceRevisionRefusal(runDir, state.verify!)).toMatch(/does not read/);
    } finally {
      await rm(runDir, { recursive: true, force: true });
    }
  });
});

describe("a setup change the check cannot be trusted with", () => {
  const px = (pre: string, body: string) => paperIndex(`\\documentclass{article}\n${pre}\n\\begin{document}\n${body}\n\\begin{theorem}\nT.\n\\end{theorem}\n\\end{document}`, null, null);
  it("names the macros redefined, added or removed — and the nodes whose text uses them, proofs included", () => {
    const a = px("\\newcommand{\\E}{\\mathbb{E}}\n\\newcommand{\\R}{\\mathbb{R}}\n\\def\\eps{\\varepsilon}", "Intro.");
    const b = px("\\newcommand{\\E}{\\mathbf{E}}\n\\newcommand{\\R}{\\mathbb{R}}\n\\newcommand{\\N}{\\mathbb{N}}", "Intro.");
    expect(changedMacros(a, b)).toEqual(["E", "N", "eps"]);
    expect(changedMacros(a, a)).toEqual([]);
    // two on one line, a body over several lines, \\gdef: each its own
    const c = px("\\newcommand{\\R}{\\mathbb R}\\newcommand{\\N}{\\mathbb N}\n\\newcommand{\\nrm}[1]{%\n  \\lVert #1 \\rVert}\n\\gdef\\eps{\\epsilon}", "Intro.");
    const d = px("\\newcommand{\\R}{\\mathbb R}\\newcommand{\\N}{\\mathbf N}\n\\newcommand{\\nrm}[1]{%\n  \\lvert #1 \\rvert}\n\\gdef\\eps{\\epsilon}", "Intro.");
    expect(changedMacros(c, d)).toEqual(["N", "nrm"]);
    const core = { statements: [{ id: "thm:a", statement: "$x\\in\\R$.", proof_tex: "Take $\\E X$." }, { id: "thm:b", statement: "$\\Eta$ only." }], assumptions: [], definitions: [] } as unknown as Core;
    expect(nodesUsingMacros(core, ["E"])).toEqual(["thm:a"]);
    expect(nodesUsingMacros(core, [])).toEqual([]);
  });
  it("is cut short past what a referee reads: a change there is not shown to it", () => {
    expect(setupExcerptCut(px("", "Intro."))).toBe(false);
    expect(setupExcerptCut(px("", "x ".repeat(20_000)))).toBe(true);
  });
});

describe("a fix in place", () => {
  it("is re-pointed from a snapshot, not a version: closed, the revision before it is back on record", async () => {
    const runDir = await mkdtemp(path.join(os.tmpdir(), "inplacefix-"));
    try {
      await mkdir(path.join(runDir, "discovery"), { recursive: true });
      await writeFile(path.join(runDir, "discovery", "envs.json"), "{}", "utf8");
      const state = createVerifyInitialState("q", { phase: "done", source: { input: "/p", main_file: "main.tex", sha256: "old" }, targets: null, core_sha256: null } as never);
      const earlier = { from_version: 1, started_at: "t", transcribed: true };
      state.verify!.version = 2;
      state.verify!.revision = earlier;
      expect(await startInPlaceFix({ runDir, state, save: async () => {} })).not.toBeNull();
      expect(state.verify!.revision).toMatchObject({ from_version: 2, in_place: { sha: "old", previous: earlier } });
      expect(existsSync(path.join(runDir, "versions", ".inplace", "discovery", "envs.json"))).toBe(true);
      expect(existsSync(path.join(runDir, "versions", ".inplace", "base", "state.json"))).toBe(true);
      // open: a second fix is not started over it
      expect(await startInPlaceFix({ runDir, state, save: async () => {} })).toBeNull();
      state.verify!.revision!.lines_before = { "thm:a": { file: "main.tex", from: 3, to: 4 } };
      expect(closeInPlaceFix(state.verify!)).toBe(true);
      expect(state.verify!.revision).toEqual(earlier);
      expect(state.verify!.version).toBe(2);
      // the source it replaced is kept (no plain entry reads it as a revision), and its scheme-5 lines
      expect(state.verify!.source.fixed_from).toEqual(["old"]);
      expect(state.verify!.fix_lines_before).toEqual({ "thm:a": { file: "main.tex", from: 3, to: 4 } });
      expect(closeInPlaceFix(state.verify!)).toBe(false);
    } finally {
      await rm(runDir, { recursive: true, force: true });
    }
  });
});
