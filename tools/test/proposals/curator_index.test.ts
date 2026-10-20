import { mkdtempSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { MODELS } from "../../src/models.js";
import { candidateIndex, claudeAsker, curatorViolations, MAX_INDEX_PROPOSALS, unselectedItem, unshownItem, type CuratorItem, type ProposalCandidate } from "../../src/proposals/curator.js";
import { TOKEN_USAGE_LEDGER, type ModelTokenUsage } from "../../src/token_usage.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";
import type { ClaudeRunInput } from "../../src/workers/claude.js";

const cand = (name: string, over: Partial<ProposalCandidate> = {}): ProposalCandidate => ({
  candidate_id: `Papers.Foo.${name}`, source: { kind: "paper_decl", ref: `Papers.Foo.${name}` }, kind: "theorem",
  statement: "If [the variable is measurable](hyp:hY) then [its law is tight](goal). @node: lem:tight", context: { module: "Papers.Foo.Helpers.Tight" }, ...over,
});

describe("the curator's index of a paper with too many candidates to show in full", () => {
  it("lists every candidate once, under the Lean file that proves it, with what the scan knows", () => {
    const { prefix, text } = candidateIndex([
      cand("Tight.law_tight", { division_signal: "Foundations", helper_of: ["Papers.Foo.a", "Papers.Foo.b"], recurrence: [{ slug: "bar", name: "Papers.Bar.x", kind: "pattern" }, { slug: "baz", name: "Papers.Baz.y", kind: "similar", score: 9 }] as never }),
      cand("main_bound", { context: { module: "Papers.Foo.TMain" }, division_signal: "Tricks", paper_shaped: ["its own types"], dropped_hypotheses: ["h"], source: { kind: "paper_decl", ref: "Papers.Foo.main_bound", is_paper_result: true }, statement: "x".repeat(300) }),
    ]);
    expect(prefix).toBe("Papers.Foo.");
    expect(text).toContain("## Papers/Foo/Helpers/Tight.lean\n- Tight.law_tight [F; used by 2; recurs: bar] If the variable is measurable then its law is tight.");
    expect(text).toContain(`## Papers/Foo/TMain.lean\n- main_bound [T; paper-shaped; unused: h; stated in the paper] ${"x".repeat(110)}…`);
  });

  it("an index round's reply names only its proposals; the rest are set aside", () => {
    const cfg = { lib: "Toolkit", divisions: ["Foundations", "Tricks"], toolkitRoot: "/nonexistent" } as unknown as ToolkitConfig;
    const cs = [cand("a"), cand("b")];
    expect(curatorViolations([], cs, cfg)).toEqual(["candidate Papers.Foo.a was not judged.", "candidate Papers.Foo.b was not judged."]);
    expect(curatorViolations([], cs, cfg, undefined, undefined, { partial: true })).toEqual([]);
    expect(curatorViolations([unselectedItem("Papers.Foo.a")], cs, cfg, undefined, undefined, { partial: true })).toEqual([]);
    expect(curatorViolations([unselectedItem("Papers.Foo.zzz")], cs, cfg, undefined, undefined, { partial: true })).toEqual(["item Papers.Foo.zzz: not a candidate id."]);
  });

  it("an index round proposes at most the brief's number of entries: one more breaks the contract", () => {
    const cfg = { lib: "Toolkit", divisions: ["Foundations", "Tricks"], toolkitRoot: "/nonexistent" } as unknown as ToolkitConfig;
    const cs = Array.from({ length: MAX_INDEX_PROPOSALS + 1 }, (_, i) => cand(`c${i}`));
    const propose = (c: ProposalCandidate): CuratorItem => ({ ...unselectedItem(c.candidate_id), verdict: "propose" });
    const cap = (items: CuratorItem[]) => curatorViolations(items, cs, cfg, undefined, undefined, { partial: true }).filter((v) => v.includes("at most"));
    expect(cap(cs.slice(0, MAX_INDEX_PROPOSALS).map(propose))).toEqual([]);
    expect(cap(cs.map(propose))).toEqual([`${MAX_INDEX_PROPOSALS + 1} items proposed; an index round proposes at most ${MAX_INDEX_PROPOSALS} — keep the strongest.`]);
  });

  it("the index is capped in bytes: the highest-ranked candidates stay, the text says how many were cut, and a cut one is set aside as not shown", () => {
    const cs = [
      cand("plain_a"),
      cand("recurs", { recurrence: [{ slug: "bar", name: "Papers.Bar.x", kind: "identical" }] }),
      cand("plain_b"),
      cand("deferred", { deferred_before: [{ slug: "baz", proposal_id: "b-x" }] }),
    ];
    const whole = candidateIndex(cs);
    expect(whole.cut).toEqual([]);
    expect(whole.text).not.toContain("not shown");
    const capped = candidateIndex(cs, whole.text.length / 2);
    expect(capped.cut).toEqual(["Papers.Foo.plain_a", "Papers.Foo.plain_b"]);
    expect(capped.text).toContain("- recurs [recurs: bar]");
    expect(capped.text).toContain("- deferred [deferred before]");
    expect(capped.text).toContain("2 candidate(s) not shown: the index is capped at");
    expect(capped.prefix).toBe("Papers.Foo.");
    expect(unshownItem("Papers.Foo.plain_a").reuse_evidence).toMatch(/^not shown: the paper's index exceeded its size cap/);
  });
});

describe("the curator's Claude calls are recorded in the run's token ledger", () => {
  const usage: ModelTokenUsage = { input_tokens: 500, cached_input_tokens: 100, cache_creation_input_tokens: 0, output_tokens: 20, reasoning_output_tokens: 0, total_tokens: 620 };

  it("one record per call under its stage, provider claude, failures included — as the checker's codex calls are", async () => {
    const runDir = mkdtempSync(path.join(tmpdir(), "tc-curator-ledger-"));
    const cfg = { toolkitRoot: runDir } as unknown as ToolkitConfig;
    const seen: string[] = [];
    const ok = async (o: ClaudeRunInput) => { seen.push(o.prompt); o.onUsage?.(usage); return "{\"items\":[]}"; };
    expect(await claudeAsker(cfg, ok, { runDir, stage: "promotion B" }).ask("p", {})).toBe("{\"items\":[]}");
    await expect(claudeAsker(cfg, async () => { throw new Error("quota"); }, { runDir, stage: "garden" }).ask("q", {})).rejects.toThrow("quota");
    // no ledger given (the standalone `leansmith garden`): nothing is written
    await claudeAsker(cfg, ok).ask("r", {});
    const rows = readFileSync(path.join(runDir, TOKEN_USAGE_LEDGER), "utf8").trim().split("\n").map((l) => JSON.parse(l));
    expect(rows).toEqual([
      expect.objectContaining({ provider: "claude", model: MODELS.claudeMain, stage: "promotion B", success: true, usage }),
      expect.objectContaining({ provider: "claude", model: MODELS.claudeMain, stage: "garden", success: false, usage: null }),
    ]);
    expect(seen).toEqual(["p", "r"]);
  });
});
