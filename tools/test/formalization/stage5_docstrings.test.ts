import { describe, expect, it } from "vitest";
import { crosslinkDefect, docstringFingerprint, docstringLanes, lakeFailureSummary, moduleNamesFor, type UndocumentedDecl, LakeFailure, lakeReportsLeanError } from "../../src/formalization/stage5_docstrings.js";

describe("moduleNamesFor (F5 docstring coverage module derivation)", () => {
  it("maps run-dir .lean files to dotted module names, excluding non-Lean files and tmp/", () => {
    expect(
      moduleNamesFor("CausalSmith/Stat/X_Research", [
        "Basic.lean",
        "Helpers/Bound.lean",
        "notes.md",
        "tmp/Scratch.lean",
        "Helpers/tmp/Probe.lean",
      ]),
    ).toEqual([
      "CausalSmith.Stat.X_Research.Basic",
      "CausalSmith.Stat.X_Research.Helpers.Bound",
    ]);
  });
});

describe("crosslinkDefect (F5 hard gate on theorem docstring crosslinks)", () => {
  const source = `theorem t (x : ℝ) (hx : 0 ≤ x) (hb : x ≤ 1) : x ^ 2 ≤ x := proof`;
  it("accepts a fully crosslinked docstring; flags uncovered hypotheses, a missing goal link, and unknown names", () => {
    const doc = "If [x is nonnegative](hyp:hx) and [at most one](hyp:hb), then [x² ≤ x](goal).";
    expect(crosslinkDefect({ kind: "theorem", doc, source })).toBeNull();
    expect(
      crosslinkDefect({ kind: "theorem", doc: "If [x ≥ 0](hyp:hx), then [done](goal).", source }),
    ).toContain("hb");
    expect(
      crosslinkDefect({ kind: "theorem", doc: "If [a](hyp:hx) and [b](hyp:hb), done.", source }),
    ).toContain("(goal)");
    expect(
      crosslinkDefect({ kind: "theorem", doc: "If [a](hyp:hOld) and [b](hyp:hb), [c](goal).", source }),
    ).toContain("hOld");
  });
  it("requires the (goal) link even on hypothesis-free theorems", () => {
    expect(
      crosslinkDefect({ kind: "theorem", doc: "Plain NL.", source: "theorem s : 1 = 1 := rfl" }),
    ).toContain("(goal)");
    expect(
      crosslinkDefect({
        kind: "theorem",
        doc: "[One equals one](goal).",
        source: "theorem s : 1 = 1 := rfl",
      }),
    ).toBeNull();
  });
});

describe("crosslinkDefect: placeholder phrases and definitions (docstring contract)", () => {
  const source = `theorem t (x : ℝ) (hx : 0 ≤ x) (hb : x ≤ 1) : x ^ 2 ≤ x := proof`;
  it("rejects a fully linked docstring whose phrases translate nothing (a name→phrase table's output)", () => {
    const doc = "Given [the supplied x](hyp:x), [the stated condition](hyp:hx), [the stated condition](hyp:hb), [the stated t result](goal) holds.";
    const p = crosslinkDefect({ kind: "theorem", doc, source });
    expect(p).toContain("placeholder");
    expect(p).toContain('"the stated condition"');
    expect(p).toContain('"the supplied x"');
    expect(crosslinkDefect({ kind: "theorem", doc: "If [x is nonnegative](hyp:hx) and [at most one](hyp:hb), then [x² ≤ x](goal).", source })).toBeNull();
  });
  it("checks a definition: every explicit parameter and the object are linked; implicit binders are not required", () => {
    const def = "def groupMean {U G : Type*} (n : G → ℕ) (y : U → ℝ) (g : G) : ℝ := 0";
    expect(crosslinkDefect({ kind: "def", doc: "[The mean](goal) of [values](hyp:y) in [a group](hyp:g) over [its size](hyp:n).", source: def })).toBeNull();
    expect(crosslinkDefect({ kind: "def", doc: "[The mean](goal) of [values](hyp:y) in a group.", source: def })).toContain("n, g");
    expect(crosslinkDefect({ kind: "def", doc: "The mean of [values](hyp:y) in [a group](hyp:g) over [its size](hyp:n).", source: def })).toContain("(goal)");
    expect(crosslinkDefect({ kind: "def", doc: "For [the stated inputs](hyp:n,y,g), [the mean](goal).", source: def })).toContain("placeholder");
    // a structure or instance is not gated here
    expect(crosslinkDefect({ kind: "structure", doc: "Plain.", source: "structure S where x : ℕ" })).toBeNull();
  });
});

describe("docstringLanes (batched docstring calls)", () => {
  const decl = (file: string, line: number): UndocumentedDecl => ({ name: `${file}:${line}`, file, line, kind: "theorem" });
  it("packs whole files into calls of at most `size`, splits a larger file within one lane, and never puts a file in two lanes", () => {
    const undoc = [
      ...Array.from({ length: 3 }, (_, i) => decl("A.lean", i)),
      ...Array.from({ length: 3 }, (_, i) => decl("B.lean", i)),
      ...Array.from({ length: 9 }, (_, i) => decl("C.lean", 9 - i)),
      decl("D.lean", 1),
    ];
    const lanes = docstringLanes(undoc, 4);
    for (const lane of lanes) for (const call of lane) expect(call.length).toBeLessThanOrEqual(4);
    const laneOf = new Map<string, number>();
    lanes.forEach((lane, i) => lane.flat().forEach((e) => {
      expect(laneOf.get(e.file) ?? i).toBe(i);
      laneOf.set(e.file, i);
    }));
    expect(lanes.flat(2)).toHaveLength(undoc.length);
    const c = lanes.find((l) => l.flat().some((e) => e.file === "C.lean"))!;
    expect(c.map((call) => call.length)).toEqual([4, 4, 1]);
    expect(c.flat().map((e) => e.line)).toEqual([1, 2, 3, 4, 5, 6, 7, 8, 9]);
  });
  it("one call for a small module set", () => {
    expect(docstringLanes([decl("A.lean", 1), decl("B.lean", 2)])).toEqual([[[decl("A.lean", 1), decl("B.lean", 2)]]]);
  });
});

describe("docstringFingerprint (incremental docstring check)", () => {
  const a = [{ module: "P.A", text: "/-- [x](goal). -/\ntheorem a : True := trivial" }, { module: "P.B", text: "def b := 1" }];
  it("is order-independent and changes with any module's source", () => {
    expect(docstringFingerprint(a)).toBe(docstringFingerprint([...a].reverse()));
    expect(docstringFingerprint([{ ...a[0], text: a[0].text.replace("[x]", "[y]") }, a[1]])).not.toBe(docstringFingerprint(a));
    expect(docstringFingerprint([a[0]])).not.toBe(docstringFingerprint(a));
    // a module boundary moved between files is a change, not a coincidence of concatenation
    expect(docstringFingerprint([{ module: "M", text: "ab" }, { module: "N", text: "c" }]))
      .not.toBe(docstringFingerprint([{ module: "M", text: "a" }, { module: "N", text: "bc" }]));
  });
});

describe("lakeFailureSummary (F5 build-failure checkpoint text)", () => {
  it("surfaces Lean diagnostics from STDOUT and never the command line", () => {
    const stdout = "✖ [3/4] Building X\ninfo: stdout of lean\nerror: ./CausalSmith/Stat/X/Basic.lean:12:3: unknown identifier 'foo'\n";
    const msg = lakeFailureSummary({ stdout, stderr: "error: build failed\n", exitCode: 1 }, "/run/docstring_lake.log");
    expect(msg).toContain("Basic.lean:12:3: unknown identifier 'foo'");
    expect(msg).toContain("error: build failed");
    expect(msg).toContain("/run/docstring_lake.log");
    expect(msg).not.toContain("Command failed");
    expect(msg.length).toBeLessThan(300);
  });

  it("a lake stopped at the one-hour limit is marked [f5-time-limit], with the limit it hit", () => {
    const wall = lakeFailureSummary({ stdout: "✔ [3/90] Built X\n", stderr: "", exitCode: null, killedDueToTotalTimeout: true }, "/run/docstring_lake.log");
    expect(wall).toContain("[f5-time-limit] (killed: 60 min wall-clock)");
    const quiet = lakeFailureSummary({ stdout: "", stderr: "", exitCode: null, killedDueToInactivity: true }, "/run/docstring_lake.log");
    expect(quiet).toContain("[f5-time-limit] (killed: no output for 60 min)");
    expect(lakeFailureSummary({ stdout: "error: x.lean:1:1: bad\n", stderr: "", exitCode: 1 }, "/l")).not.toContain("[f5-time-limit]");
  });
});

describe("lakeReportsLeanError (a docstring defect vs a lake that did not finish)", () => {
  it("is true on a Lean diagnostic, false on a timeout kill or a lake failure with no diagnostic", () => {
    const lean = { stdout: "error: ./Papers/X/Basic.lean:12:3: unexpected token\n", stderr: "error: build failed\n" };
    expect(lakeReportsLeanError(lean)).toBe(true);
    expect(lakeReportsLeanError({ ...lean, killedDueToInactivity: true })).toBe(false);
    expect(lakeReportsLeanError({ stdout: "", stderr: "", killedDueToTotalTimeout: true })).toBe(false);
    expect(lakeReportsLeanError({ stdout: "", stderr: "lake: uncaught exception: no space left on device\n" })).toBe(false);
    expect(new LakeFailure("x", false).leanError).toBe(false);
  });
});

// The finding: one docstring call killed by the watchdog failed F5 while the other lanes kept writing.
describe("unlessKilled", () => {
  it("lets a killed call fall to the next pass and stops on any other failure", async () => {
    const { unlessKilled } = await import("../../src/formalization/stage5_docstrings.js");
    const { CodexRunError } = await import("../../src/shared/codex.js");
    expect(await unlessKilled("x", async () => undefined)).toBe(true);
    expect(await unlessKilled("x", async () => { throw new CodexRunError("codex killed: inactivity timeout (25m without output). stderr-tail=", "", ""); })).toBe(false);
    await expect(unlessKilled("x", async () => { throw new CodexRunError("codex exited 1. stderr-tail=429 Too Many Requests", "", ""); })).rejects.toThrow("codex exited 1");
    await expect(unlessKilled("x", async () => { throw new Error("boom"); })).rejects.toThrow("boom");
  });
});

// The finding: a failed lane let the other lanes keep dispatching after the stage had already failed.
describe("mapLimit after a failure", () => {
  it("starts no new item, lets the running ones settle, then throws the first failure", async () => {
    const { mapLimit } = await import("../../src/formalization/reviewer_verdicts.js");
    const started: number[] = [];
    let settled = 0;
    const run = mapLimit([0, 1, 2, 3, 4, 5], 2, async (x) => {
      started.push(x);
      if (x === 0) throw new Error("lane 0 failed");
      await new Promise((r) => setTimeout(r, 20));
      settled += 1;
      return x;
    });
    await expect(run).rejects.toThrow("lane 0 failed");
    expect(started).toEqual([0, 1]);
    expect(settled).toBe(1);
  });
});
