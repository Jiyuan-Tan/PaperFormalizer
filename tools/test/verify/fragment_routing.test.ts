/**
 * Model-text defects of the annotated paper go back to their producers; only renderer defects are
 * the renderer checkpoint (user rule 2026-09-25: "fix the order and the classification").
 * Classification (`splitRenderDefects`), routing per producer
 * (`FragmentRouter`), continue-then-checkpoint, the fixer's scoped round, and the
 * `annotate` command's exit (unchanged).
 */
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import { annotateFailure } from "../../src/verify/annotate_cli.js";
import { FragmentRouter, type FragmentDefect } from "../../src/verify/fragment_routing.js";
import { PatchFileSchema } from "../../src/verify/patches.js";
import { contractBlock, splitRenderDefects, type FragmentProducer, type RenderDefect } from "../../src/verify/render_check.js";
import { VERIFY_FILES } from "../../src/verify/types.js";
import { restateAllPatches } from "../../src/verify/weakening.js";
import { withdrawnRepairBlock } from "../../src/verify/stage_v1.js";

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

const frag = (producer: FragmentProducer, text: string, node: string, ref?: string): FragmentDefect => ({
  node,
  block: producer === "symbol" ? "symbol reading" : "explanation",
  reason: `Missing $ inserted.; printed verbatim — the fragment: ${text}`,
  fragment: { kind: "note", text, producer, error: "Missing $ inserted.", ...(ref ? { ref } : {}) },
});

describe("classification: model text vs renderer", () => {
  it("a defect carrying its fragment is model text; a proof-step escape, a scan hit and a pdflatex error are the renderer's", () => {
    const defects: RenderDefect[] = [
      frag("symbol", "N=N_1+N_0 is the number of subjects", "symbol N", "N"),
      { node: "lem:a", block: "corrected step of the proof of lem:a", reason: "fragment escaped (math outside math)" },
      { node: null, block: "pdflatex (main.log)", reason: "./main.tex:1: Undefined control sequence." },
    ];
    const { renderer, fragments } = splitRenderDefects(defects);
    expect(fragments.map((d) => d.node)).toEqual(["symbol N"]);
    expect(renderer.map((d) => d.block)).toEqual(["corrected step of the proof of lem:a", "pdflatex (main.log)"]);
    expect(contractBlock(fragments)).toMatch(/^1 model-written fragment\(s\) still do not compile[\s\S]*the symbol referee \(1\):\n {4}symbol N — symbol reading: Missing \$ inserted\./u);
  });

  it("annotate (no model calls) still exits non-zero listing a failing fragment, the paper written", () => {
    const err = annotateFailure({ path: "/r/annotated/main.pdf", line: "/r/annotated/main.pdf (1 annotation(s))", result: null, error: null, render: [frag("symbol", "N is the size", "symbol N", "N")] });
    expect(err?.message).toMatch(/^render check: 1 block\(s\) could not be set as TeX —\n {4}symbol N — symbol reading: Missing \$ inserted\./u);
    expect(err?.message).toContain("The annotated paper (written anyway): /r/annotated/main.pdf");
  });
});

describe("FragmentRouter: routing per producer, continue then checkpoint", () => {
  const state = (over: Partial<NonNullable<StateJson["verify"]>> = {}, stage: StateJson["stage_completed"] = "V1"): StateJson => {
    const s = createVerifyInitialState("q", { phase: "v1", source: { input: "p.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: "c", v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
    Object.assign(s.verify!, over);
    s.stage_completed = stage;
    return s;
  };
  const router = (s: StateJson, over: { restate?: () => Promise<boolean>; answering?: boolean; runDir?: string } = {}) => {
    const calls = { restate: 0, reopened: [] as string[] };
    const r = new FragmentRouter({
      state: () => s,
      runDir: over.runDir ?? "/nonexistent",
      restate: async () => {
        calls.restate += 1;
        return over.restate ? over.restate() : false;
      },
      reopenAccepted: async (why) => {
        calls.reopened.push(why);
      },
      answering: over.answering ?? false,
    });
    return { r, calls };
  };

  it("symbol: the verdict is dropped; referee: the confirmation and the carry; the run continues into V1.5; after the pass, still failing → contract; fixer: its scoped round", async () => {
    const s = state({ confirmed_symbols: { N: "b1", r: "b2" }, confirmed: { "thm:a": "b", "thm:b": "b" }, level_pause: { carry: { "thm:a": "x" } } as never });
    const { r } = router(s);
    const fs = [frag("symbol", "N is the size", "symbol N", "N"), frag("referee", "Why: it fails at e_n", "thm:a")];
    const g1 = await r.gate(fs, "pass");
    expect(g1.verdict).toBe("continue");
    expect(s.verify!.confirmed_symbols).toEqual({ r: "b2" });
    expect(s.verify!.confirmed).toEqual({ "thm:b": "b" });
    expect(s.verify!.level_pause!.carry).toEqual({});
    // no pass yet: waiting, not stuck
    expect((await r.gate(fs, "pass")).verdict).toBe("continue");
    r.notePass("V1.5");
    const g2 = await r.gate(fs, "pass");
    expect(g2.verdict).toBe("contract");
    expect(g2.stuck.map((d) => d.node)).toEqual(["symbol N", "thm:a"]);
    // fixer: the scoped round is opened (never while the invocation answers a halt)
    const fixer = router(state(), { restate: async () => true });
    await fixer.r.gate([frag("fixer", "the theorem\u2019s claim", "thm:var-kurt")], "resume");
    expect(fixer.calls.restate).toBe(1);
    const answering = router(state(), { answering: true });
    await answering.r.gate([frag("fixer", "the theorem\u2019s claim", "thm:var-kurt")], "resume");
    expect(answering.calls.restate).toBe(0);
  });

  it("a V1.5 pass stopped at a pending receipt wrote the symbols again, not the nodes", async () => {
    const s = state();
    const { r } = router(s);
    const fs = [frag("symbol", "N is the size", "symbol N", "N"), frag("referee", "Why: it fails at e_n", "thm:a")];
    await r.gate(fs, "resume");
    r.notePass("V1.5", false);
    const g = await r.gate(fs, "pass");
    expect(g.stuck.map((d) => d.node)).toEqual(["symbol N"]);
  });

  it("a text no model re-writes is stuck at once", async () => {
    const { r } = router(state());
    const g = await r.gate([frag("other", "the owner\u2019s guidance", "thm:b")], "resume");
    expect(g.verdict).toBe("contract");
    expect(g.stuck).toHaveLength(1);
  });

  it("a failing referee or symbol fragment drops its cached verdict at once, even at a halt nothing runs before (no re-typeset keeps it)", async () => {
    const cap = { cap_reached: { counter: "patch_rounds", rounds: 3, cap: 3, origin: "V1.5", findings: [], proposed: [], at: "t" } as never };
    const s = state({ ...cap, confirmed_symbols: { N: "b1" }, confirmed: { "thm:a": "b" } });
    const { r, calls } = router(s);
    const g = await r.gate([frag("symbol", "N is the size", "symbol N", "N"), frag("referee", "Why: it fails at e_n", "thm:a")], "decision");
    expect(g.verdict).toBe("present");
    expect(g.pending).toHaveLength(2);
    expect(s.verify!.confirmed_symbols).toEqual({});
    expect(s.verify!.confirmed).toEqual({});
    expect(calls).toEqual({ restate: 0, reopened: [] });
  });

  it("an accepted core (no F stage yet) is re-opened for V1.5; after the F stages it is not, and a pass end then checkpoints", async () => {
    const s = state({ phase: "v1_5" }, "V1.5");
    const { r, calls } = router(s);
    expect((await r.gate([frag("symbol", "N is the size", "symbol N", "N")], "pass")).verdict).toBe("continue");
    expect(s.verify!.phase).toBe("v1");
    expect(s.stage_completed).toBe("V1");
    expect(calls.reopened).toHaveLength(1);
    const f = state({ phase: "formalization" }, "3");
    const rf = router(f);
    expect((await rf.r.gate([frag("symbol", "N is the size", "symbol N", "N")], "pass")).verdict).toBe("contract");
    expect(f.verify!.phase).toBe("formalization");
    // a refuted run's report phase before any F stage is re-opened too (the live CNS state)
    const v6 = state({ phase: "v6" }, "V1");
    expect((await router(v6).r.gate([frag("symbol", "N is the size", "symbol N", "N")], "resume")).verdict).toBe("continue");
    expect(v6.verify!.phase).toBe("v1");
  });

  it("at the weakened-repair halt the symbol pass is reachable (continue); a referee text alone is not (present, listed); a cap or rewind halt presents", async () => {
    const weak = { weakening_repair: { status: "pending", items: [] } as never };
    expect((await router(state(weak)).r.gate([frag("symbol", "N is the size", "symbol N", "N")], "weakening")).verdict).toBe("continue");
    const g = await router(state(weak)).r.gate([frag("referee", "Why: e_n", "thm:a")], "weakening");
    expect(g.verdict).toBe("present");
    expect(g.pending).toHaveLength(1);
    const cap = { cap_reached: { counter: "patch_rounds", rounds: 3, cap: 3, origin: "V1.5", findings: [], proposed: [], at: "t" } as never };
    expect((await router(state(cap)).r.gate([frag("symbol", "N is the size", "symbol N", "N")], "decision")).verdict).toBe("present");
  });
});

describe("a repair text that does not compile goes back to the fixer once", () => {
  const QID = "guard";
  const core = (): Core =>
    ({
      qid: QID,
      symbols: [],
      assumptions: [],
      definitions: [],
      statements: [
        { id: "lem:rate", kind: "lemma", statement: "the rate is \\(n^{-1/2}\\)", depends_on: [], status: "to-prove", proof_tex: "Bound the second display." },
        { id: "thm:main", kind: "theorem", statement: "the estimator is asymptotically normal", depends_on: ["lem:rate"], status: "to-prove" },
      ],
      target_estimand: "\\(\\tau\\)",
    }) as unknown as Core;
  const setup = async () => {
    const runDir = await mkdtemp(path.join(os.tmpdir(), "verify-guard-"));
    tmpDirs.push(runDir);
    await mkdir(path.join(runDir, "discovery"), { recursive: true });
    for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core()), "utf8");
    await writeFile(path.join(runDir, VERIFY_FILES.flatTex), "\\begin{lemma}the rate\\end{lemma}\n\\begin{proof}Bound the second display.\\end{proof}\n", "utf8");
    const state = createVerifyInitialState(QID, { phase: "v1_5", source: { input: "paper.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: "x", v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null });
    return { runDir, state };
  };

  it("restateAllPatches: a repair text the paper printed verbatim goes back to the fixer with the compiler's line, once", async () => {
    const { runDir, state } = await setup();
    const note = "Bound the lemma\u2019s second display by $C n^{-1/2}$.";
    const patch = { node: "lem:rate", corrected_statement: null, add_assumptions: [], remove_depends_on: [], proof_note: note };
    const file = PatchFileSchema.parse({ key_results: ["thm:main"], key_contribution: "c", patches: [patch], unfixable: [] });
    await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(file), "utf8");
    state.verify!.paper_errors = { "lem:rate": { detail: "d", witness: "w" } };
    // without the render's routing nothing is sent
    expect(await restateAllPatches(runDir, state, new Map())).toEqual([]);
    const compile = new Map([["lem:rate", [{ where: 'the proof note the paper prints for "lem:rate"', text: note, error: "a non-ASCII character U+2019 (\u2019)" }]]]);
    const lines = await restateAllPatches(runDir, state, compile);
    expect(lines[1]).toMatch(/the proof note the paper prints for "lem:rate" does not compile: a non-ASCII character U\+2019/u);
    expect(state.verify!.phase).toBe("init");
    const directive = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.findings[0].restatement.join(" ")).toContain("does not compile");
    // once per text and reason class
    state.verify!.phase = "v1_5";
    expect(await restateAllPatches(runDir, state, compile)).toEqual([]);
  });

  it("restateAllPatches: a suggestion sent back carries its repair as it stood (the new entry replaces it whole)", async () => {
    const { runDir, state } = await setup();
    const ops = [{ op: "replace", unit: "lem:rate/1/1", tex: "the rate, for bounded \\(\\hat p\\)" }];
    const file = PatchFileSchema.parse({
      key_results: ["thm:main"],
      key_contribution: "c",
      patches: [],
      unfixable: [{ node: "lem:rate", reason: "r", suggested_repair: { corrected_statement: "the rate, for bounded p", ops, proof_note: "p" } }],
    });
    await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(file), "utf8");
    state.verify!.paper_errors = { "lem:rate": { detail: "d", witness: "w" } };
    const compile = new Map([["lem:rate", [{ where: 'the statement the paper prints for "lem:rate"', text: "x", error: "Undefined control sequence" }]]]);
    await restateAllPatches(runDir, state, compile);
    const directive = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.findings[0].withdrawn_repair).toEqual({ corrected_statement: "the rate, for bounded p", ops });
  });
});

describe("withdrawnRepairBlock", () => {
  it("shows each op as its unit range and raw TeX, with the repair's drops and adds", () => {
    const block = withdrawnRepairBlock([
      { id: "thm:main", withdrawn_repair: { corrected_statement: "S", ops: [{ op: "replace", unit: "thm:main/1/1", to: "thm:main/1/2", tex: "Then $\\kappa<\\infty$." }], drops: ["ass:a"], adds: ["ass:b"] } },
      { id: "lem:rate" },
    ]);
    expect(block).toBe(["- thm:main", "  the statement it gave:", "    S", "  op: replace thm:main/1/1 … thm:main/1/2 by", "    Then $\\kappa<\\infty$.", "  drops: ass:a", "  adds: ass:b"].join("\n"));
  });
});
