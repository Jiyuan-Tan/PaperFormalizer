import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { fileHeadContains } from "../src/shared/codex.js";
import { TOKEN_USAGE_LEDGER, withTokenLedger, type ModelTokenUsage } from "../src/token_usage.js";

const usage: ModelTokenUsage = { input_tokens: 900, cached_input_tokens: 600, cache_creation_input_tokens: 0, output_tokens: 40, reasoning_output_tokens: 10, total_tokens: 940 };

describe("token ledger", () => {
  it("records each call of a wrapped runner under its stage, failures included, and passes usage on", async () => {
    const dir = mkdtempSync(path.join(tmpdir(), "tc-tokens-"));
    const seen: ModelTokenUsage[] = [];
    const ok = withTokenLedger(async (i: { model?: string; onUsage?: (u: ModelTokenUsage) => void }) => { i.onUsage?.(usage); return "out"; }, dir, "V1.5");
    expect(await ok({ model: "gpt-x", onUsage: (u) => seen.push(u) })).toBe("out");
    const bad = withTokenLedger(async (_i: { model?: string }) => { throw new Error("quota"); }, dir, "V1");
    await expect(bad({})).rejects.toThrow("quota");
    const rows = readFileSync(path.join(dir, TOKEN_USAGE_LEDGER), "utf8").trim().split("\n").map((l) => JSON.parse(l));
    expect(rows).toEqual([
      expect.objectContaining({ provider: "codex", model: "gpt-x", stage: "V1.5", success: true, usage }),
      expect.objectContaining({ model: "default", stage: "V1", success: false, usage: null }),
    ]);
    expect(seen).toEqual([usage]);
  });
  it("finds a session's marker however long the prompt before it (not just in the first 256KB)", async () => {
    const dir = mkdtempSync(path.join(tmpdir(), "tc-rollout-"));
    const file = path.join(dir, "rollout.jsonl");
    writeFileSync(file, `${"x".repeat(700 * 1024)}[leansmith-session-marker:abc]\n`);
    expect(await fileHeadContains(file, "leansmith-session-marker:abc", 256 * 1024)).toBe(false);
    expect(await fileHeadContains(file, "leansmith-session-marker:abc", 2 * 1024 * 1024)).toBe(true);
    // a marker cut across two read chunks is still found
    writeFileSync(file, `${"y".repeat(256 * 1024 - 10)}leansmith-session-marker:abc`);
    expect(await fileHeadContains(file, "leansmith-session-marker:abc", 1024 * 1024)).toBe(true);
  });
});

describe("token ledger — the login warm-up", () => {
  it("records the warm-up call made ahead of a call as a call of its own, under the caller's stage", async () => {
    const dir = mkdtempSync(path.join(tmpdir(), "tc-tokens-warm-"));
    type In = { model?: string; onUsage?: (u: ModelTokenUsage) => void; onAuthWarmUp?: (c: { model: string; duration_ms: number; success: boolean; usage: ModelTokenUsage | null }) => void };
    const run = withTokenLedger(async (i: In) => { i.onAuthWarmUp?.({ model: "gpt-mini", duration_ms: 7, success: true, usage }); i.onUsage?.(usage); return "out"; }, dir, "V1");
    await run({ model: "gpt-x" });
    const rows = readFileSync(path.join(dir, TOKEN_USAGE_LEDGER), "utf8").trim().split("\n").map((l) => JSON.parse(l));
    expect(rows.map((r) => [r.provider, r.stage, r.role ?? null, r.model, r.success])).toEqual([["codex", "V1", "auth warm-up", "gpt-mini", true], ["codex", "V1", null, "gpt-x", true]]);
    expect(rows[0].usage).toEqual(usage);
  });
});

describe("token ledger — attempts", () => {
  it("sums the usage of a transient retry's attempts instead of keeping the last one", async () => {
    const dir = mkdtempSync(path.join(tmpdir(), "tc-tokens-retry-"));
    const run = withTokenLedger(async (i: { model?: string; onUsage?: (u: ModelTokenUsage) => void }) => { i.onUsage?.(usage); i.onUsage?.(usage); return "out"; }, dir, "V1");
    await run({ model: "gpt-x" });
    const [row] = readFileSync(path.join(dir, TOKEN_USAGE_LEDGER), "utf8").trim().split("\n").map((l) => JSON.parse(l));
    expect(row.usage).toEqual({ ...usage, input_tokens: 1800, cached_input_tokens: 1200, output_tokens: 80, reasoning_output_tokens: 20, total_tokens: 1880 });
  });
});
