// Every halt message that points the orchestrator to a SKILL section names one the skill has, and
// every pointer of the skill into the user manual names a heading the manual has.
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import { checkpointGuidance, weakeningRepairGuidance } from "../src/checkpoint_playbook.js";

const TOOLS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const read = (p: string): string => readFileSync(path.resolve(TOOLS, p), "utf8");

describe("checkpoint playbook", () => {
  it("a weakened repair is the user's in every mode: recommend and wait, never rule", () => {
    for (const auto of [false, true]) {
      const g = weakeningRepairGuidance(auto);
      expect(g).toContain("orch.mjs recommend <slug> --toolkit <toolkit> repair <node> <accept|decline|redo>");
      expect(g).toMatch(/The USER decides each item on the paper's page/);
      expect(g).not.toMatch(/rule on it yourself on the owner's behalf|do not stop to ask/);
    }
    expect(weakeningRepairGuidance(true)).toContain("never rule on it yourself");
  });

  it("an F5 halt is a refusal: the reminder names the gate that refused, never 'F5 done'", () => {
    const of = (message: string, auto = false) => checkpointGuidance("5", "checkpoint", {}, auto, message)!;
    expect(of("F5 delivery audit REFUSED: cited-mismatch @ lem:a: x")).toMatch(/DELIVERY AUDIT REFUSED[\s\S]*--from-stage F2\.5/);
    expect(of("F5 delivery audit could not validate the artifacts: ENOENT")).toContain("could not read an artifact");
    expect(of("F5 docstring coverage: 3 declaration(s) still undocumented")).toContain("DOCSTRING GATE");
    // … and the gate's two other halts (their messages do not say "coverage")
    for (const m of ["F5 docstring pass could not be validated — lake did not finish", "F5 docstring pass broke the build; its edits were restored"]) expect(of(m)).toContain("DOCSTRING GATE");
    expect(of("F5 bank-soundness gate REFUSED: sorry in A.lean")).toContain("SOUNDNESS GATE");
    expect(of("F5 crosswalk consistency: 2 row(s) claim a verified Lean match")).toContain("CROSSWALK");
    expect(checkpointGuidance("5", "blocked", {}, false, "F5 cannot read the formalization note at x")).toContain("formalization note");
    for (const m of ["F5 docstring coverage: x", "anything else"]) for (const auto of [false, true]) expect(of(m, auto)).not.toContain("F5 done");
    expect(of("x", true)).toContain("F5 refused to complete");
  });

  it("an F1.5 review halt prints the exits that work, not the audit checkpoint's text or a plain resume", () => {
    const g = checkpointGuidance("1.5", "checkpoint", { general_review_halt: "Review boundary stage_1.5_to_1 halted: x" })!;
    expect(g).toMatch(/flags\.f1_revise_directive[\s\S]*--from-stage F1[\s\S]*--from-stage F2[\s\S]*--from-stage V1\.5/);
    expect(g).toContain("--clear-gate general_review_halt");
    expect(g).toContain("A plain resume is refused while the gate is set");
    expect(g).not.toContain("CONSOLIDATED CKPT 1");
    expect(checkpointGuidance("1.5", "checkpoint", {})).toContain("CONSOLIDATED CKPT 1");
  });

  it("the missing-architecture block and the proof-loop cap carry their exits in the reminder", () => {
    expect(checkpointGuidance("2", "blocked", { missing_architecture: true })).toMatch(/F2 MISSING ARCHITECTURE[\s\S]*flags\.missing_architecture_items/);
    // picked by the stage of the result: the loop's phases, and the guard that refuses F5 on an unresolved escalation
    for (const st of ["3", "3.5", "4"] as const) expect(checkpointGuidance(st, "checkpoint", {})).toContain("F2–F4: follow the checkpoint route");
    expect(checkpointGuidance("5", "checkpoint", {}, false, "PROOF-REVIEW ESCALATION UNRESOLVED [hint]: cannot enter F5")).toContain("F2–F4: follow the checkpoint route");
    expect(checkpointGuidance("2.5", "checkpoint", {})).not.toContain("fix-source/failed");
    // any other F2 halt: the scaffolder's own message carries no exit, the reminder does
    expect(checkpointGuidance("2", "blocked", {})).toMatch(/F2 DID NOT COMPLETE.*`--resume` scaffolds again.*flags\.f2_scaffold_directive.*--from-stage F1/);
    const cap = checkpointGuidance("2.5", "checkpoint", { proof_loop_cap_hit: "iteration budget" })!;
    expect(cap).toMatch(/PROOF-LOOP CAP[\s\S]*iteration budget[\s\S]*--clear-gate proof_loop_cap_hit/);
    expect(checkpointGuidance("2.5", "checkpoint", {})).toContain("F2–F4: follow the checkpoint route");
  });

  it("cites only SKILL sections that exist", () => {
    const skill = read("../.claude/skills/leansmith/SKILL.md");
    const headings = new Set([...skill.matchAll(/^## (.+)$/gm)].map((m) => m[1]!.trim()));
    // every runner text and the watcher's that points at a section, by either quoting style
    const sources = ["src/checkpoint_playbook.ts", "src/verify/pipeline.ts", "src/verify/stage_v1.ts", "src/verify/cross_stage_rewind.ts", "src/verify/caps.ts", "src/verify/weakening.ts", "scripts/orch.mjs"].map(read).join("\n");
    const cited = [...sources.matchAll(/SKILL (?:§'([^']+)'|\\?"([^"\\]+)\\?")/g)].map((m) => (m[1] ?? m[2])!);
    expect(cited.length).toBeGreaterThan(0);
    expect(cited.filter((c) => ![...headings].some((h) => h.startsWith(c)))).toEqual([]);
  });

  it("the skill points only at headings the user manual has, and stays within its size", () => {
    const skill = read("../.claude/skills/leansmith/SKILL.md");
    const manual = new Set([...read("../doc/USER_MANUAL.md").matchAll(/^#{2,3} (.+)$/gm)].map((m) => m[1]!.trim()));
    // "→ manual: "A", "B"": every quoted name (a pointer may wrap over a line break)
    const pointers = [...skill.replace(/\s+/g, " ").matchAll(/→ manual:((?: ?,? ?"[^"]+")+)/g)].flatMap((m) => [...m[1]!.matchAll(/"([^"]+)"/g)].map((q) => q[1]!));
    expect(pointers.length).toBeGreaterThan(0);
    expect(pointers.filter((h) => !manual.has(h))).toEqual([]);
    // the sections AGENTS.md names
    for (const h of ["Mechanics", "When the pipeline itself fails"]) expect(skill).toMatch(new RegExp(`^## ${h}`, "m"));
    expect(skill.split("\n").length).toBeLessThanOrEqual(370);
  });
});
