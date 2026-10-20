import { describe, it, expect } from "vitest";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { SemanticTier, isEmbeddingsStale, loadSemanticTier } from "../src/formalization/semantic_tier.js";
import { indexSourceFromPath } from "../src/library/sources.js";

describe("SemanticTier", () => {
  it("ranks by cosine and applies the floor", () => {
    // 3 decls, 2-dim unit vectors
    const t = new SemanticTier(["A", "B", "C"], new Float32Array([1, 0, /*A*/ 0.8, 0.6, /*B*/ 0, 1 /*C*/]), 2);
    const r = t.topK(new Float32Array([1, 0]), { k: 3, floor: 0.5, exclude: new Set() });
    expect(r.map((x) => x.name)).toEqual(["A", "B"]); // C cos=0 < floor
    expect(r[0].sim).toBeCloseTo(1);
  });

  it("scores each decl by the max cosine across base and extra views", () => {
    // Query q=[1,0].  base: A cos1.0, B cos0.5.  extra: A cos0.0, B cos0.9.
    const base = new Float32Array([1, 0, 0.5, Math.sqrt(3) / 2]);
    const extra = new Float32Array([0, 1, 0.9, Math.sqrt(1 - 0.81)]);
    const t = new SemanticTier(["A", "B"], base, 2, [extra]);
    const hits = t.topK(new Float32Array([1, 0]), { k: 5, floor: -1, exclude: new Set() });
    expect(hits.find((h) => h.name === "B")!.sim).toBeCloseTo(0.9, 5); // extra view lifts B from 0.5
    expect(hits.find((h) => h.name === "A")!.sim).toBeCloseTo(1.0, 5); // base wins for A
  });

  it("an index with no embedding files has no semantic tier (silently)", () => {
    const dir = mkdtempSync(path.join(tmpdir(), "semtier-"));
    const idx = path.join(dir, "library_index.json");
    writeFileSync(idx, JSON.stringify({ commit: "c", entries: [{ name: "A" }] }));
    expect(loadSemanticTier(indexSourceFromPath(idx))).toBeNull();
  });

  it("isEmbeddingsStale: fresh when names+commit match, stale on drift", () => {
    expect(isEmbeddingsStale({ names: ["A", "B"], index_commit: "c1" }, { commit: "c1", names: ["A", "B"] })).toBe(false);
    expect(isEmbeddingsStale({ names: ["A", "B"], index_commit: "c1" }, { commit: "c2", names: ["A", "B"] })).toBe(true);
    expect(isEmbeddingsStale({ names: ["A"], index_commit: "c1" }, { commit: "c1", names: ["A", "B"] })).toBe(true);
  });
});
