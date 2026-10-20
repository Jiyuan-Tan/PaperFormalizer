import { fileURLToPath } from "node:url";
/**
 * The shard prompt's size discipline (`referee_shard_prompts.ts`): byte caps on the paper slices,
 * dependency verdicts one line each and once, readings once with the nodes they bind, the symbol
 * entries of the shard's own nodes only, and a trimmed brief that fails loudly when its blocks move.
 */
import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { z } from "zod";
import type { Core } from "../../src/core/schema.js";
import type { DependencyVerdict } from "../../src/verify/referee_levels.js";
import {
  PROOF_EXCERPT_MAX,
  SETUP_HYPOTHESES_MAX,
  SETUP_SHARD_MAX,
  USED_TEXT_MAX,
  buildShardPrompt,
  capText,
  dependencyVerdictsSection,
  globalBriefOf,
  isMalformedReply,
  readingsSection,
  shardBriefOf,
  verdictLine,
  type ShardContext,
} from "../../src/verify/referee_shard_prompts.js";
import { paperIndex, setupExcerpt } from "../../src/verify/referee_slices.js";
import type { V15NodeVerdict } from "../../src/verify/types.js";

const PROMPTS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..", "src", "verify", "prompts", "V1.5");
const BASE = readFileSync(path.join(PROMPTS, "review.txt"), "utf8");
const SHARD = readFileSync(path.join(PROMPTS, "shard.txt"), "utf8");
const bytes = (t: string): number => Buffer.byteLength(t, "utf8");
const sectionOf = (p: string, header: string): string => {
  const at = p.indexOf(`=== ${header}`);
  expect(at).toBeGreaterThanOrEqual(0);
  const next = p.indexOf("\n=== ", at + 5);
  return p.slice(at, next < 0 ? undefined : next);
};

const sentences = (tag: string, n: number): string => Array.from({ length: n }, (_, i) => `The ${tag} sentence number ${i} says something about $\\Delta_{${i}}$.`).join(i2(tag));
const i2 = (tag: string): string => (tag === "proof" ? "\n" : " ");
const LONG_SETUP = sentences("setup", 800); // ~50 KB
const LONG_PROOF = sentences("proof", 800);
const FLAT = [
  "\\documentclass{article}",
  "\\newcommand{\\E}{\\mathbb{E}}",
  "\\begin{document}",
  LONG_SETUP,
  "\\begin{assumption}\\label{ass:h} The noise $\\Delta$ has mean zero.\\end{assumption}",
  "\\begin{theorem}\\label{thm:t} Under the assumption, $\\Delta$ is small.\\end{theorem}",
  "\\begin{proof}",
  LONG_PROOF,
  "\\end{proof}",
  "\\end{document}",
].join("\n");

function core(): Core {
  return {
    qid: "cap",
    symbols: [
      { name: "\\Delta", type: "noise" },
      { name: "\\sigma", type: "scale" },
    ],
    assumptions: [
      { id: "ass:h", kind: "moment", condition: "The noise $\\Delta$ has mean zero.", free_symbols: ["\\Delta"] },
      { id: "ass:pin-1", kind: "reading", condition: "$\\Delta$ is random.", bookkeeping: { added_by: "V1.5", reason: "pins reading of symbol \\Delta: the model section" } },
      { id: "ass:pin-2", kind: "reading", condition: "$\\sigma$ is fixed.", bookkeeping: { added_by: "V1.5", reason: "pins reading of symbol \\sigma: the model section" } },
    ],
    definitions: [],
    statements: [
      { id: "thm:t", kind: "theorem", statement: "Under the assumption, $\\Delta$ is small.", depends_on: ["ass:h", "ass:pin-1", "ass:pin-2"], proof_tex: LONG_PROOF, status: "to-prove", free_symbols: ["\\Delta"] },
      { id: "thm:u", kind: "theorem", statement: "Also $\\sigma > 0$.", depends_on: ["ass:h", "ass:pin-2"], status: "to-prove", free_symbols: ["\\sigma"] },
    ],
    target_estimand: "x",
    bibliography: [],
  } as unknown as Core;
}

function ctx(extra: string[] = [], deps?: (id: string) => DependencyVerdict[]): ShardContext {
  const px = paperIndex(FLAT, null, null);
  const c = core();
  return { core: c, px, setup: setupExcerpt(px), extraSections: () => extra, totalNodes: 5, scope: "scope", symbols: { binding: c, unresolved: [] }, ...(deps ? { dependencies: deps } : {}) };
}

const verdict = (id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "d", witness: null, bookkeeping_assumption: null, reading: null, ...over });

describe("byte caps", () => {
  it("capText cuts at a sentence boundary; a statement shard: setup ≤ 15 KB, each proof ≤ 12 KB; a hypotheses-only shard: setup ≤ 8 KB", () => {
    const t = sentences("proof", 400);
    const out = capText(t, 5_000);
    expect(bytes(out)).toBeLessThanOrEqual(5_000);
    expect(out).toMatch(/\.\n\[… \d+ lines omitted; read them in discovery\/flat\.tex …\]$/);
    expect(capText("short.", 5_000)).toBe("short.");
    const p = buildShardPrompt(ctx(), BASE, SHARD, ["thm:t"]);
    expect(bytes(sectionOf(p, "PAPER SETUP"))).toBeLessThanOrEqual(SETUP_SHARD_MAX + 100);
    const ex = sectionOf(p, "PAPER EXCERPTS FOR THE NODES YOU GRADE");
    const proof = ex.slice(ex.indexOf("Proof ("));
    expect(bytes(proof)).toBeLessThanOrEqual(PROOF_EXCERPT_MAX + 300);
    expect(proof).toMatch(/lines omitted; read them in discovery\/flat\.tex/);
    // The proof is shown once: the core does not repeat it.
    expect(sectionOf(p, "TYPED CORE")).not.toContain("proof sentence number 5 ");
    const h = buildShardPrompt(ctx(), BASE, SHARD, ["ass:h"]);
    expect(bytes(sectionOf(h, "PAPER SETUP"))).toBeLessThanOrEqual(SETUP_HYPOTHESES_MAX + 100);
    expect(sectionOf(h, "TYPED CORE")).toMatch(/^result: thm:t, thm:u$/m);
  });
});

describe("dependency verdicts", () => {
  it("one line per dependency, once however many nodes use it; texts clipped to 160 characters", () => {
    const long = "w".repeat(1_000);
    const deps = (id: string): DependencyVerdict[] =>
      id === "thm:t" || id === "thm:u" ? [{ id: "lem:x", kind: "lemma", verdict: verdict("lem:x", { correctness: "error", witness: long }), repair: null }, { id: "lem:y", kind: "lemma", verdict: verdict("lem:y"), repair: null }] : [];
    const s = dependencyVerdictsSection(ctx([], deps), ["thm:t", "thm:u"]).join("");
    const lines = s.split("\n").filter((l) => l.startsWith("- "));
    expect(lines).toHaveLength(2);
    expect(lines[0]).toMatch(/^- lem:x \(lemma\): ERROR — w{160} …; no confirmed repair — used by thm:t, thm:u$/);
    expect(lines[1]).toBe("- lem:y (lemma): ok — used by thm:t, thm:u");
    expect(s).not.toContain("w".repeat(161));
    // The rule on an errored dependency is stated once; the runner imposes it (no per-node directive).
    expect(s).not.toContain("→ grade");
    expect(s).toContain('the node\'s own correctness is `unclear` with detail "depends on <id>, graded error"');
  });
});

describe("readings", () => {
  it("each reading once, with the nodes it binds; a hypothesis is shown only its own; an open symbol only where a shown node uses it", () => {
    const c = core();
    const s = readingsSection(c, { binding: c, unresolved: [] }, ["thm:t"], ["ass:h"]).join("");
    expect(s).toContain("- ass:pin-1 (reading of symbol \\Delta): $\\Delta$ is random. — binds thm:t");
    const both = readingsSection(c, { binding: c, unresolved: [] }, ["thm:t", "thm:u"]).join("");
    expect(both.split("ass:pin-2 (reading").length).toBe(2);
    expect(both).toContain("— binds thm:t, thm:u");
    expect(readingsSection(c, { binding: c, unresolved: [] }, ["ass:h"]).join("")).not.toContain("ass:pin-2");
    const open = { name: "\\sigma", meaning: "ok", fix: null, ambiguity: "unresolvable", reading: null, redefined_at: null, detail: "scale or variance" } as const;
    expect(readingsSection(c, { binding: c, unresolved: [open] }, ["thm:u"]).join("")).toContain("- \\sigma: scale or variance");
    expect(readingsSection(c, { binding: c, unresolved: [open] }, ["ass:h"]).join("")).not.toContain("\\sigma: scale");
  });
});

describe("trimmed brief", () => {
  it("a brief whose blocks cannot be found is a prompt-contract bug: it throws, never falls back to the whole brief", () => {
    expect(() => shardBriefOf("a brief without the usual blocks", { statements: true, patches: false, cited: false })).toThrow(/review\.txt/);
    expect(() => globalBriefOf("a brief without the usual blocks", { patches: true })).toThrow(/review\.txt/);
  });

  it("the global pass's brief: the opening and FAITHFULNESS; PATCHES only with patches; never correctness, conventions or how-to", () => {
    const g = globalBriefOf(BASE, { patches: false });
    expect(g).toContain("FAITHFULNESS — ");
    expect(g).not.toContain("CORRECTNESS — ");
    expect(g).not.toContain("CONVENTIONS TO SETTLE.");
    expect(g).not.toContain("=== HOW TO CHECK CORRECTNESS");
    expect(g).not.toContain("PATCHES. ");
    expect(globalBriefOf(BASE, { patches: true })).toContain("PATCHES. ");
    expect(bytes(g)).toBeLessThan(bytes(BASE) / 2);
    // The brief has no scope block of its own: every call's own scope block says what it grades.
    expect(BASE).not.toContain("=== SCOPE AND ADDRESSING ===");
    expect(BASE).not.toContain("VERDICT OUTPUT");
  });
});

describe("symbol entries and used nodes in the compact core", () => {
  it("only the symbols the shard's OWN nodes use travel (not those of every node they use); a used node's text is cut at USED_TEXT_MAX", () => {
    const c = core();
    // thm:t uses thm:u (which mentions \sigma); a long hypothesis it uses is cut.
    c.statements.find((s) => s.id === "thm:t")!.depends_on.push("thm:u", "ass:long");
    c.assumptions.push({ id: "ass:long", kind: "moment", condition: `Long: ${"y".repeat(6_000)}`, free_symbols: [] } as never);
    const p = buildShardPrompt({ ...ctx(), core: c }, BASE, SHARD, ["thm:t"]);
    const core_ = sectionOf(p, "TYPED CORE");
    const symbols = core_.slice(core_.indexOf("Symbols the nodes you grade use"), core_.indexOf("The nodes you grade"));
    expect(symbols).toContain('"name":"\\\\Delta"');
    expect(symbols).not.toContain('"name":"\\\\sigma"');
    const used = core_.slice(core_.indexOf("What they use"), core_.indexOf("Every other node"));
    expect(used).toContain("- thm:u (theorem): Also $\\sigma > 0$.");
    expect(used).toContain(`${"y".repeat(USED_TEXT_MAX - 6)} …`);
    expect(used).not.toContain("y".repeat(USED_TEXT_MAX + 1));
    // A shard on thm:u sees \sigma.
    expect(sectionOf(buildShardPrompt(ctx(), BASE, SHARD, ["thm:u"]), "TYPED CORE")).toContain('"name":"\\\\sigma"');
  });
});

describe("the global pass's verdict lines", () => {
  it("no shard tag or basis; a carried verdict shows its grades, reading and condition, not its detail, witness or fix", () => {
    const fresh = verdictLine(verdict("thm:t", { correctness: "error", detail: "the detail", witness: "w", shards: ["L1-1"], basis: "b" } as never));
    expect(fresh).toContain('"detail":"the detail"');
    // a fresh verdict clean on every axis is shown by its grades, as a carried one
    expect(verdictLine(verdict("thm:t", { detail: "the detail" } as never))).not.toContain("the detail");
    expect(fresh).not.toContain("shards");
    expect(fresh).not.toContain('"basis"');
    const carried = verdictLine(verdict("thm:t", { graded: "carried", correctness: "bookkeeping", detail: "the detail", witness: "w", fix: { add_depends_on: ["ass:h"] }, bookkeeping_assumption: { condition: "$c$", reason: "r" }, reading: { reading: "$r$", evidence: "e" }, shards: ["L1-1"] } as never));
    expect(carried).toBe('{"id":"thm:t","faithfulness":"ok","ambiguity":"ok","correctness":"bookkeeping","bookkeeping_assumption":{"condition":"$c$","reason":"r"},"reading":{"reading":"$r$","evidence":"e"},"graded":"carried"}');
  });
});

describe("a malformed reply is a contract violation", () => {
  it("a schema failure or no JSON gives a violation line; any other error is the runner's", () => {
    const zerr = z.object({ nodes: z.array(z.string()) }).safeParse({ nodes: 1 });
    expect(zerr.success).toBe(false);
    if (zerr.success) return;
    expect(isMalformedReply(zerr.error)).toMatch(/does not fit the output schema: nodes: /);
    expect(isMalformedReply(Object.assign(new Error("no JSON object"), { code: "codex_malformed_output" }))).toMatch(/was not one JSON object: no JSON object/);
    expect(isMalformedReply(new Error("ECONNRESET"))).toBeNull();
  });
});
