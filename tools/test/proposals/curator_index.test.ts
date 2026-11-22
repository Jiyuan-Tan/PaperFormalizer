import { mkdtempSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { MODELS } from "../../src/models.js";
import { candidateIndex, claudeAsker, curatorViolations, MAX_INDEX_PROPOSALS, missingMustJudge, mustJudge, askJson, unjudgedItem, unselectedItem, unshownItem, type CuratorItem, type ProposalCandidate } from "../../src/proposals/curator.js";
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
    expect(cap(cs.map(propose))).toEqual([`${MAX_INDEX_PROPOSALS + 1} items proposed besides the must-judge ones; an index round proposes at most ${MAX_INDEX_PROPOSALS} of those — keep the strongest.`]);
  });

  it("the index is capped in bytes: the highest-ranked candidates stay, the text says how many were cut, and a cut one is set aside as not shown", () => {
    const cs = [
      cand("plain_a"),
      cand("recurs", { recurrence: [{ slug: "bar", name: "Papers.Bar.x", kind: "pattern" }] }),
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
    // no ledger given (the standalone `paperformalizer garden`): nothing is written
    await claudeAsker(cfg, ok).ask("r", {});
    const rows = readFileSync(path.join(runDir, TOKEN_USAGE_LEDGER), "utf8").trim().split("\n").map((l) => JSON.parse(l));
    expect(rows).toEqual([
      expect.objectContaining({ provider: "claude", model: MODELS.claudeMain, stage: "promotion B", success: true, usage }),
      expect.objectContaining({ provider: "claude", model: MODELS.claudeMain, stage: "garden", success: false, usage: null }),
    ]);
    expect(seen).toEqual(["p", "r"]);
  });
});

describe("must-judge candidates: an identical recurrence, or use by another paper's Lean", () => {
  const cfg = { lib: "Toolkit", divisions: ["Foundations", "Tricks"], toolkitRoot: "/nonexistent" } as unknown as ToolkitConfig;
  const identical = cand("same", { recurrence: [{ slug: "bar", name: "Papers.Bar.same", kind: "identical" }] });
  const imported = cand("api", { imported_by: ["Papers.Emp"] });
  const pattern = cand("shape", { recurrence: [{ slug: "bar", name: "Papers.Bar.shape", kind: "pattern" }] });

  it("are flagged, ranked first and never cut from the index, however small the cap", () => {
    expect(mustJudge(identical)).toBe(true);
    expect(mustJudge(imported)).toBe(true);
    expect(mustJudge(pattern)).toBe(false);
    const { text, cut } = candidateIndex([cand("plain"), pattern, identical, imported], 10);
    expect(cut).toEqual(["Papers.Foo.shape", "Papers.Foo.plain"]);
    expect(text).toContain("- same [must judge; recurs: bar]");
    expect(text).toContain("- api [must judge; imported by: Papers.Emp]");
  });

  it("each needs an item — propose, or skip with its reason — and none counts toward the cap", () => {
    const many = Array.from({ length: MAX_INDEX_PROPOSALS }, (_, i) => cand(`c${i}`));
    const cs = [...many, identical, imported];
    const propose = (c: ProposalCandidate): CuratorItem => ({ ...unselectedItem(c.candidate_id), verdict: "propose" });
    const skip = (c: ProposalCandidate): CuratorItem => ({ ...unselectedItem(c.candidate_id), reuse_evidence: "helper of Papers.Foo.c0, proposed" });
    const v = (items: CuratorItem[]) => curatorViolations(items, cs, cfg, undefined, undefined, { partial: true }).filter((x) => x.includes("must judge") || x.includes("at most"));
    expect(v(many.map(propose))).toEqual([]);
    expect(missingMustJudge(many.map(propose), cs)).toEqual([
      'candidate Papers.Foo.same is marked "must judge" and has no item: propose it, or skip it with the reason in reuse_evidence.',
      'candidate Papers.Foo.api is marked "must judge" and has no item: propose it, or skip it with the reason in reuse_evidence.',
    ]);
    expect(missingMustJudge([propose(identical), skip(imported)], cs)).toEqual([]);
    expect(v([...many.map(propose), propose(identical), skip(imported)])).toEqual([]);
    expect(v([...many.map(propose), propose(identical), propose(imported)])).toEqual([]);
    const over = [...many, cand("one_more"), identical, imported];
    expect(curatorViolations([...over.map(propose)], over, cfg, undefined, undefined, { partial: true }).filter((x) => x.includes("at most")))
      .toEqual([`${MAX_INDEX_PROPOSALS + 1} items proposed besides the must-judge ones; an index round proposes at most ${MAX_INDEX_PROPOSALS} of those — keep the strongest.`]);
  });
});

describe("a must-judge item the reply leaves out is asked for once more, then set aside — never a failed round", () => {
  it("askJson: a soft problem is asked about once and then accepted; a hard one still fails twice", async () => {
    const dir = mkdtempSync(path.join(tmpdir(), "tc-askjson-"));
    const cfg = { toolkitRoot: dir, runsDir: path.join(dir, "runs") } as unknown as ToolkitConfig;
    const prompts: string[] = [];
    const asker = { model: "m", ask: async (p: string) => { prompts.push(p); return "{\"items\":[]}"; } };
    const r = await askJson<{ items: unknown[] }>({ cfg, slug: "s", name: "curator", prompt: "P", schema: {}, asker, log: () => {}, violations: () => [], soft: () => ["candidate X is marked \"must judge\""] });
    expect(r).toEqual({ items: [] });
    expect(prompts).toHaveLength(2);
    expect(prompts[1]).toContain("candidate X is marked \"must judge\"");
    await expect(askJson({ cfg, slug: "s", name: "curator", prompt: "P", schema: {}, asker, log: () => {}, violations: () => ["bad"], soft: () => [] })).rejects.toThrow("broke the output contract twice");
    expect(unjudgedItem("Papers.Foo.x")).toMatchObject({ candidate_id: "Papers.Foo.x", verdict: "skip" });
    // a retry asked only for soft problems never loses the first reply to a broken second one
    let n = 0;
    const flaky = { model: "m", ask: async () => (++n === 1 ? "{\"items\":[1]}" : "{\"items\":[2]}") };
    const logs: string[] = [];
    const kept = await askJson<{ items: number[] }>({ cfg, slug: "s", name: "curator", prompt: "P", schema: {}, asker: flaky, log: (m) => logs.push(m),
      violations: (r) => (r.items[0] === 2 ? ["hard"] : []), soft: (r) => (r.items[0] === 1 ? ["soft"] : []) });
    expect(kept).toEqual({ items: [1] });
    expect(logs.at(-1)).toMatch(/keeping the first, whose only problems were soft/);
    // …nor to a second ask that fails outright
    let m = 0;
    const dying = { model: "m", ask: async () => { if (++m === 2) throw new Error("quota"); return "{\"items\":[1]}"; } };
    expect(await askJson<{ items: number[] }>({ cfg, slug: "s", name: "curator", prompt: "P", schema: {}, asker: dying, log: (x) => logs.push(x), violations: () => [], soft: () => ["soft"] })).toEqual({ items: [1] });
    await expect(askJson({ cfg, slug: "s", name: "curator", prompt: "P", schema: {}, asker: { model: "m", ask: async () => { throw new Error("quota"); } }, log: () => {}, violations: () => [] })).rejects.toThrow("quota");
  });
});
