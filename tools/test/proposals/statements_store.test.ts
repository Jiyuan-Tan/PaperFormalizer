import { existsSync, readdirSync, statSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { createRetrieval } from "../../src/formalization/reuse_retrieval.js";
import { indexSourceFromPath } from "../../src/library/sources.js";
import { withPromotionLock } from "../../src/shared/build_mutex.js";
import { toolkitTemplateDir } from "../../src/toolkit/lakefile.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";
import type { CandidateScan } from "../../src/proposals/candidate_scan.js";
import { deferredMatches } from "../../src/proposals/round_b.js";
import type { Recurrence } from "../../src/proposals/schema.js";
import {
  deferredMatchesIn, eachShard, findRecurrence, loadShard, loadStatementStore, normalizeType, recordDecisions, recordProposals, recordScan, statementPattern,
  statementShardDir, statementShardPath, statementStoreLockPath, statementStorePath, STATEMENT_STORE_LOCK_FILENAME, typeHash, updateStatementStore, type StatementEntry,
} from "../../src/proposals/statements.js";
import { mergePaper, splitStatementStore, streamStoreEntries } from "../../src/proposals/statements_split.js";

let root: string;
const cfgOf = (r: string) => ({ toolkitRoot: r, lockPath: path.join(r, ".toolkit-promote.lock"), runsDir: path.join(r, "runs") }) as unknown as ToolkitConfig;
const scanOf = (names: string[]) => ({
  declarations: names.map((name) => ({ name, module: "Papers.X", kind: "theorem", type: `∀ n : ℕ, ${name} n = n`, doc: "A doc." })),
}) as unknown as CandidateScan;
const filtered = (names: string[]) => ({ candidates: names.map((name) => ({ name })), movable: [], rejected: [] }) as never;

beforeEach(async () => { root = await mkdtemp(path.join(os.tmpdir(), "pf-statements-")); });
afterEach(async () => { await rm(root, { recursive: true, force: true }); });

describe("statement store: one shard per paper, its own lock", () => {
  it("the toolkit store is doc/statements/<slug>.json under its own lock, never the promotion lock; a dry run's lies under its run", () => {
    const cfg = cfgOf(root);
    // the store is still named by its single-file path; its shards are in the directory of that name
    expect(statementStorePath(cfg, "p", false)).toBe(path.join(root, "doc", "statements.json"));
    expect(statementShardDir(statementStorePath(cfg, "p", false))).toBe(path.join(root, "doc", "statements"));
    expect(statementShardPath(statementStorePath(cfg, "p", false), "p")).toBe(path.join(root, "doc", "statements", "p.json"));
    expect(statementStorePath(cfg, "p", true)).toBe(path.join(root, "runs", "p", "proposals", "dry_run", "statements.json"));
    expect(statementShardPath(statementStorePath(cfg, "p", true), "p")).toBe(path.join(root, "runs", "p", "proposals", "dry_run", "statements", "p.json"));
    expect(statementStoreLockPath(cfg, "p", false)).toBe(path.join(root, STATEMENT_STORE_LOCK_FILENAME));
    expect(statementStoreLockPath(cfg, "p", false)).not.toBe(cfg.lockPath);
    expect(statementStoreLockPath(cfg, "p", true)).toBe(`${statementStorePath(cfg, "p", true)}.lock`);
    expect(() => statementShardPath("/s", "../x")).toThrow(/not a paper slug/);
  });

  it("a toolkit made from the template ignores the store's lock, as it ignores the promotion lock (garden --verify refuses untracked files)", async () => {
    const ignored = (await readFile(path.join(toolkitTemplateDir(), ".gitignore"), "utf8")).split("\n");
    expect(ignored).toContain(".toolkit-promote.lock");
    expect(ignored).toContain(STATEMENT_STORE_LOCK_FILENAME);
  });

  it("recording a scan does not wait while another paper holds the promotion lock", async () => {
    const cfg = cfgOf(root);
    const store = statementStorePath(cfg, "a", false);
    let release!: () => void;
    const held = new Promise<void>((r) => { release = r; });
    let promotionActive!: () => void;
    const active = new Promise<void>((r) => { promotionActive = r; });
    const promotion = withPromotionLock(root, async () => { promotionActive(); await held; }, cfg.lockPath);
    await active;
    const t0 = Date.now();
    await recordScan(store, "a", scanOf(["Papers.X.a1"]), filtered(["Papers.X.a1"]), "2026-11-08T00:00:00Z", statementStoreLockPath(cfg, "a", false));
    await recordProposals(store, "a", [{ verdict: "propose", source: { ref: "Papers.X.a1" }, id: "b-a1" }] as never, statementStoreLockPath(cfg, "a", false));
    await recordDecisions(store, "a", new Map([["b-a1", "accept"]]) as never, statementStoreLockPath(cfg, "a", false));
    expect(Date.now() - t0).toBeLessThan(10_000);
    release();
    await promotion;
    const [e] = await loadShard(store, "a");
    expect(e).toMatchObject({ slug: "a", name: "Papers.X.a1", verdict: "candidate", proposal_id: "b-a1", decision: "accept" });
  });

  it("two papers recording at once both keep their entries, each in its shard", async () => {
    const cfg = cfgOf(root);
    const store = statementStorePath(cfg, "a", false);
    await Promise.all(["a", "b", "c", "d"].map((slug) =>
      recordScan(store, slug, scanOf([`Papers.X.${slug}1`, `Papers.X.${slug}2`]), filtered([`Papers.X.${slug}1`]), "2026-11-08T00:00:00Z", statementStoreLockPath(cfg, slug, false))));
    expect(readdirSync(statementShardDir(store)).sort()).toEqual(["a.json", "b.json", "c.json", "d.json"]);
    const names: string[] = [];
    for await (const s of eachShard(store)) {
      expect(s.entries.every((e) => e.slug === s.slug)).toBe(true);
      names.push(...s.entries.map((e) => e.name));
    }
    expect(names.sort()).toEqual(["a1", "a2", "b1", "b2", "c1", "c2", "d1", "d2"].map((n) => `Papers.X.${n}`));
  });

  it("a scan recorded, its proposals and its decisions touch its own shard alone", async () => {
    const cfg = cfgOf(root);
    const store = statementStorePath(cfg, "a", false);
    const lock = statementStoreLockPath(cfg, "a", false);
    await recordScan(store, "b", scanOf(["Papers.X.b1"]), filtered([]), "t0", lock);
    await recordScan(store, "c", scanOf(["Papers.X.c1"]), filtered([]), "t0", lock);
    // a single file an older process wrote beside the shards: never read or written either
    await writeFile(path.join(root, "doc", "statements.json"), '{"version":1,"entries":[]}');
    const stamp = (f: string) => { const s = statSync(f, { bigint: true }); return `${s.ino}:${s.mtimeNs}:${s.size}`; };
    const others = [statementShardPath(store, "b"), statementShardPath(store, "c"), path.join(root, "doc", "statements.json")];
    const before = others.map(stamp);
    await recordScan(store, "a", scanOf(["Papers.X.old"]), filtered([]), "t1", lock);
    await recordScan(store, "a", scanOf(["Papers.X.new"]), filtered(["Papers.X.new"]), "t2", lock);
    await recordProposals(store, "a", [{ verdict: "propose", source: { ref: "Papers.X.new" }, id: "b-new" }] as never, lock);
    await recordDecisions(store, "a", new Map([["b-new", "defer"]]) as never, lock);
    expect(others.map(stamp)).toEqual(before);
    expect(readdirSync(statementShardDir(store)).sort()).toEqual(["a.json", "b.json", "c.json"]);
    // a re-scan supersedes the paper's last; the proposal and decision stay with its declaration
    expect((await loadShard(store, "a")).map((e) => [e.name, e.recorded_at, e.proposal_id, e.decision])).toEqual([["Papers.X.new", "t2", "b-new", "defer"]]);
    await recordScan(store, "a", scanOf(["Papers.X.new"]), filtered(["Papers.X.new"]), "t3", lock);
    expect((await loadShard(store, "a"))[0]).toMatchObject({ recorded_at: "t3", proposal_id: "b-new", decision: "defer" });
  });
});

// ─── recurrence: the shards against one store, as before the split ──────────

/** `findRecurrence` as it was over the single-file store (the whole store in memory, a retrieval
 *  index of every other paper's entries): the reference the sharded store must agree with. */
async function unshardedRecurrence(entries: readonly StatementEntry[], slug: string, targets: ReadonlyArray<{ name: string; type: string; doc: string | null }>, workDir: string, papersLib = "Papers"): Promise<Map<string, Recurrence[]>> {
  const firstParagraph = (doc: string | null) => (doc ?? "").split(/\n\s*\n/)[0]!.replace(/\s+/g, " ").trim();
  const others = entries.filter((e) => e.slug !== slug);
  const out = new Map<string, Recurrence[]>(targets.map((t) => [t.name, []]));
  if (others.length === 0) return out;
  const key = (e: StatementEntry) => `${e.slug}::${e.name}`;
  const index = {
    commit: "statements", toolchain: "n/a", modules: {},
    entries: others.map((e) => ({ name: key(e), kind: e.kind, module: e.module, file: "", line: 0, statement: e.type_normalized, doc: e.doc_first_paragraph || null, refs: [], proofRefs: [], axioms: [], usesSorry: false })),
  };
  const idxFile = path.join(workDir, `statements_index.${Date.now()}.${Math.random().toString(36).slice(2)}.json`);
  await mkdir(workDir, { recursive: true });
  await writeFile(idxFile, JSON.stringify(index), "utf8");
  const retrieval = createRetrieval(indexSourceFromPath(idxFile, { library: "papers" }));
  const byKey = new Map(others.map((e) => [key(e), e] as const));
  for (const t of targets) {
    const hash = typeHash(normalizeType(t.type));
    const identical = others.filter((e) => e.type_sha256 === hash);
    const rec: Recurrence[] = identical.map((e) => ({ slug: e.slug, name: e.name, kind: "identical" as const }));
    const pattern = statementPattern(normalizeType(t.type), papersLib);
    const samePattern = pattern === null ? [] : others.filter((e) => !identical.includes(e) && statementPattern(e.type_normalized, papersLib) === pattern);
    rec.push(...samePattern.map((e) => ({ slug: e.slug, name: e.name, kind: "pattern" as const })));
    const leaf = t.name.split(".").pop() ?? t.name;
    const hits = retrieval.search({ mode: "concept", title: `${leaf.replace(/[_.]/g, " ")} ${firstParagraph(t.doc)}`, bodyTerms: [normalizeType(t.type)] }, { topK: 3 + identical.length + samePattern.length });
    for (const h of hits) {
      const e = byKey.get(h.name);
      if (!e || identical.includes(e) || samePattern.includes(e)) continue;
      if (rec.filter((r) => r.kind === "similar").length >= 3) break;
      rec.push({ slug: e.slug, name: e.name, kind: "similar", score: Math.round(h.score * 100) / 100 });
    }
    out.set(t.name, rec);
  }
  return out;
}

/** A fixture of five papers: identical statements, the same pattern over each paper's own
 *  definitions, lexical neighbours (more than three, with ties), a definition, an instance. */
function fixture(): Record<string, Array<{ name: string; kind: string; type: string; doc: string | null }>> {
  const mean = (p: string, D: string, f: string, g: string) => `∀ (${D.toLowerCase()} : Papers.${p}.${D}) (i j : Fin N), Causalean.FiniteDesign.E ${D.toLowerCase()} (Papers.${p}.${f} i) = Finset.card (Papers.${p}.${g} ${D.toLowerCase()}) / ↑N`;
  const paper = (p: string, D: string, f: string, g: string) => [
    { name: `Papers.${p}.ind_mean`, kind: "theorem", type: mean(p, D, f, g), doc: "The mean of the indicator under the design is the group's share." },
    { name: `Papers.${p}.sum_sq_le`, kind: "theorem", type: "∀ (s : Finset ℕ) (f : ℕ → ℝ), (∑ i ∈ s, f i) ^ 2 ≤ ↑s.card * ∑ i ∈ s, f i ^ 2", doc: "Cauchy–Schwarz for a finite sum of squares." },
    { name: `Papers.${p}.variance_nonneg`, kind: "theorem", type: `∀ (x : Papers.${p}.${D}), 0 ≤ Papers.${p}.var x`, doc: "The variance of the design estimator is nonnegative." },
    { name: `Papers.${p}.${D}`, kind: "def", type: "Type", doc: "The design of the experiment." },
    { name: `Papers.${p}.inst_design`, kind: "instance", type: `Inhabited (Papers.${p}.${D})`, doc: "A design exists; its mean and variance." },
  ];
  return {
    paper_a: paper("A", "Design", "ind", "grp"),
    paper_b: paper("B", "Plan", "onehot", "cohort"),
    paper_c: [...paper("C", "Scheme", "pick", "block"), { name: "Papers.C.mean_share", kind: "theorem", type: "∀ (n : ℕ), (n : ℝ) / n ≤ 1", doc: "The mean share of a group under the design is at most one." }],
    paper_d: [{ name: "Papers.D.sum_sq_le'", kind: "theorem", type: "∀ (t : Finset ℕ) (g : ℕ → ℝ), (∑ k ∈ t, g k) ^ 2 ≤ ↑t.card * ∑ k ∈ t, g k ^ 2", doc: "Sum of squares bound." }],
    paper_e: [{ name: "Papers.E.design_mean", kind: "theorem", type: "∀ (m : ℕ), m * 1 = m", doc: "The design mean of the indicator, its group and share." }],
  };
}

async function recordFixture(store: string, lock: string): Promise<StatementEntry[]> {
  const all: StatementEntry[] = [];
  let at = 0;
  for (const [slug, decls] of Object.entries(fixture())) {
    const scan = { declarations: decls.map((d) => ({ ...d, module: `Papers.${slug}` })) } as unknown as CandidateScan;
    const cands = decls.filter((d) => d.kind === "theorem").map((d) => d.name);
    all.push(...await recordScan(store, slug, scan, filtered(cands), `2026-11-1${at++}T00:00:00Z`, lock));
  }
  return all;
}

describe("recurrence over the shards", () => {
  it("finds the same identical, pattern and similar matches as over the single-file store of the same entries", async () => {
    const store = path.join(root, "doc", "statements.json");
    const all = await recordFixture(store, path.join(root, STATEMENT_STORE_LOCK_FILENAME));
    const kinds = new Set<string>();
    for (const [slug, decls] of Object.entries(fixture())) {
      const targets = decls.map((d) => ({ name: d.name, type: d.type, doc: d.doc }));
      const sharded = await findRecurrence(store, slug, targets);
      // the single file in its papers' order (the shards are read by slug): the same, in the same order
      const reference = await unshardedRecurrence(all, slug, targets, path.join(root, "work"));
      expect([...sharded.entries()]).toEqual([...reference.entries()]);
      // in any order of the single file, the same matches
      const shuffled = await unshardedRecurrence([...all].reverse(), slug, targets, path.join(root, "work"));
      const canon = (m: Map<string, Recurrence[]>) => [...m.entries()].map(([n, rs]) => [n, [...rs].sort((x, y) => `${x.kind}${x.slug}${x.name}`.localeCompare(`${y.kind}${y.slug}${y.name}`))]);
      expect(canon(sharded)).toEqual(canon(shuffled));
      for (const rs of sharded.values()) for (const r of rs) kinds.add(r.kind);
    }
    expect([...kinds].sort()).toEqual(["identical", "pattern", "similar"]);
  });

  it("finds nothing in an empty store, and never the paper's own entries", async () => {
    const store = path.join(root, "doc", "statements.json");
    const t = fixture().paper_a.map((d) => ({ name: d.name, type: d.type, doc: d.doc }));
    expect([...(await findRecurrence(store, "paper_a", t)).values()].flat()).toEqual([]);
    await recordFixture(store, path.join(root, STATEMENT_STORE_LOCK_FILENAME));
    const found = [...(await findRecurrence(store, "paper_a", t)).values()].flat();
    expect(found.length).toBeGreaterThan(0);
    expect(found.filter((r) => r.slug === "paper_a")).toEqual([]);
  });

  it("names the entries deferred in another paper that a candidate recurs with", async () => {
    const store = path.join(root, "doc", "statements.json");
    const lock = path.join(root, STATEMENT_STORE_LOCK_FILENAME);
    await recordFixture(store, lock);
    await recordProposals(store, "paper_b", [{ verdict: "propose", source: { ref: "Papers.B.ind_mean" }, id: "b-ind-mean" }, { verdict: "propose", source: { ref: "Papers.B.sum_sq_le" }, id: "b-sum-sq-le" }] as never, lock);
    await recordDecisions(store, "paper_b", new Map([["b-ind-mean", "defer"], ["b-sum-sq-le", "accept"]]) as never, lock);
    const recurrence = await findRecurrence(store, "paper_a", fixture().paper_a);
    const deferred = await deferredMatchesIn(store, recurrence);
    expect(deferred.get("Papers.A.ind_mean")).toEqual([{ slug: "paper_b", proposal_id: "b-ind-mean" }]);
    // as over the single file (every paper's entries at once, round B's `deferredMatches`)
    expect([...deferred.entries()]).toEqual([...deferredMatches(await loadStatementStore(store), recurrence).entries()]);
  });
});

// ─── compat 2026-11-11: remove after ≤2 days — the API and layout of before the shards ─────

describe("statement store: callers and layout of before the shards", () => {
  it("a store not split yet (its single file, no shard directory) is read and written as before", async () => {
    const cfg = cfgOf(root);
    const store = statementStorePath(cfg, "a", false);
    const lock = statementStoreLockPath(cfg, "a", false);
    await mkdir(path.dirname(store), { recursive: true });
    await writeFile(store, JSON.stringify({ version: 1, entries: [entryOf("z", "Papers.Z.z1"), entryOf("a", "Papers.X.gone")] }));
    await recordScan(store, "a", scanOf(["Papers.X.a1"]), filtered(["Papers.X.a1"]), "t1", lock);
    await recordProposals(store, "a", [{ verdict: "propose", source: { ref: "Papers.X.a1" }, id: "b-a1" }] as never, lock);
    expect(existsSync(statementShardDir(store))).toBe(false);
    const whole = JSON.parse(await readFile(store, "utf8")) as { entries: StatementEntry[] };
    expect(whole.entries.map((e) => [e.slug, e.name, e.proposal_id])).toEqual([["z", "Papers.Z.z1", null], ["a", "Papers.X.a1", "b-a1"]]);
    expect((await loadStatementStore(store)).entries).toHaveLength(2);
    // its other papers are searched
    const t = [{ name: "Papers.X.q", type: entryOf("z", "Papers.Z.z1").type_normalized, doc: null }];
    const z = { ...entryOf("z", "Papers.Z.z1"), type_sha256: typeHash(normalizeType(t[0]!.type)) };
    await writeFile(store, JSON.stringify({ version: 1, entries: [z] }));
    expect((await findRecurrence(store, "a", t)).get("Papers.X.q")?.[0]).toEqual({ slug: "z", name: "Papers.Z.z1", kind: "identical" });
  });

  it("the single file beside the shards (kept for, and written by, older processes) is ignored by every reader", async () => {
    const store = path.join(root, "doc", "statements.json");
    const lock = path.join(root, STATEMENT_STORE_LOCK_FILENAME);
    const all = await recordFixture(store, lock);
    await writeFile(store, JSON.stringify({ version: 1, entries: [entryOf("stale", "Papers.S.s1")] }));
    expect((await loadStatementStore(store)).entries).toEqual(all);
    const t = fixture().paper_a.map((d) => ({ name: d.name, type: d.type, doc: d.doc }));
    expect([...(await findRecurrence(store, "paper_a", t)).values()].flat().some((r) => r.slug === "stale")).toBe(false);
  });

  it("the old signatures: findRecurrence over a store in memory (with its work directory), updateStatementStore over the shards", async () => {
    const store = path.join(root, "doc", "statements.json");
    const lock = path.join(root, STATEMENT_STORE_LOCK_FILENAME);
    await recordFixture(store, lock);
    const t = fixture().paper_a.map((d) => ({ name: d.name, type: d.type, doc: d.doc }));
    const inMemory = await findRecurrence(await loadStatementStore(store), "paper_a", t, path.join(root, "work"), "Papers");
    expect([...inMemory.entries()]).toEqual([...(await findRecurrence(store, "paper_a", t)).entries()]);
    const seen = await updateStatementStore(store, lock, (s) => ({
      store: { ...s, entries: [...s.entries.filter((e) => e.slug !== "paper_e"), entryOf("paper_f", "Papers.F.f1")] },
      result: s.entries.length,
    }));
    expect(seen).toBe(allFixtureEntries());
    expect(readdirSync(statementShardDir(store)).sort()).toEqual(["paper_a.json", "paper_b.json", "paper_c.json", "paper_d.json", "paper_f.json"]);
    expect((await loadShard(store, "paper_f")).map((e) => e.name)).toEqual(["Papers.F.f1"]);
  });
});

const allFixtureEntries = () => Object.values(fixture()).flat().length;

// ─── the split ───────────────────────────────────────────────────────────────

const entryOf = (slug: string, name: string, extra: Partial<StatementEntry> = {}): StatementEntry => ({
  slug, name, module: `Papers.${slug}`, kind: "theorem", type_normalized: `∀ (x1 : ℕ), ${name} x1 = x1`, type_sha256: typeHash(name),
  doc_first_paragraph: "", verdict: "candidate", reasons: [], proposal_id: null, decision: null, recorded_at: "2026-11-01T00:00:00Z", ...extra,
});

describe("statements split", () => {
  it("copies the single file into one shard per paper, every entry round-tripping, and keeps the file in place", async () => {
    const doc = path.join(root, "doc");
    await mkdir(doc, { recursive: true });
    const tricky = '"quoted" {braces} [brackets] \\ back\\slash, ℕ ∀ ⦃x⦄ ✝ — and an emoji 🧮';
    const entries = [
      entryOf("a", "Papers.A.one", { doc_first_paragraph: tricky }),
      entryOf("b", "Papers.B.one", { reasons: ["uses sorry", "]}{["], extra_field: { nested: [1, { two: "}" }] } } as never),
      // a paper's entries need not be together in the file
      entryOf("a", "Papers.A.two", { proposal_id: "b-two", decision: "defer" }),
      // longer than a read of the file (1 MiB): an entry read across chunks, a multi-byte character on the cut
      entryOf("c", "Papers.C.big", { type_normalized: "ℕ".repeat(700_000) + "x" }),
      entryOf("b", "Papers.B.two", { verdict: "rejected" }),
    ];
    const text = JSON.stringify({ version: 1, entries }, null, 2);
    const legacy = path.join(doc, "statements.json");
    await writeFile(legacy, text);
    const store = legacy;
    const r = await splitStatementStore(legacy, path.join(root, STATEMENT_STORE_LOCK_FILENAME));
    expect(r).toMatchObject({ entries: 5, papers: 3, written: ["a", "b", "c"], unchanged: [], backup: null });
    // the single file stays, unchanged, for processes on older code
    expect(await readFile(legacy, "utf8")).toBe(text);
    expect(readdirSync(doc).sort()).toEqual(["statements", "statements.json"]);
    // each shard is what the store writes for the paper's entries (the file's, in its order), byte for byte
    for (const slug of ["a", "b", "c"]) {
      expect(await readFile(statementShardPath(store, slug), "utf8")).toBe(JSON.stringify({ version: 1, entries: entries.filter((e) => e.slug === slug) }, null, 2));
    }
    const back: StatementEntry[] = [];
    for await (const s of eachShard(store)) back.push(...s.entries);
    expect(back).toHaveLength(entries.length);
    expect(new Set(back.map((e) => JSON.stringify(e)))).toEqual(new Set(entries.map((e) => JSON.stringify(e))));
  });

  it("reads the file as a stream: entries one by one, the rest of the file returned", async () => {
    const file = path.join(root, "s.json");
    await writeFile(file, JSON.stringify({ version: 1, entries: [entryOf("a", "x"), entryOf("b", "y")] }));
    const it = streamStoreEntries(file);
    const got: unknown[] = [];
    let n = await it.next();
    for (; !n.done; n = await it.next()) got.push(n.value);
    expect(got).toEqual([entryOf("a", "x"), entryOf("b", "y")]);
    expect(n.value).toEqual({ version: 1, entries: [] });
  });

  it("installs nothing and keeps the file when it is truncated or an entry is invalid", async () => {
    const doc = path.join(root, "doc");
    await mkdir(doc, { recursive: true });
    const legacy = path.join(doc, "statements.json");
    const lock = path.join(root, STATEMENT_STORE_LOCK_FILENAME);
    const text = JSON.stringify({ version: 1, entries: [entryOf("a", "x"), entryOf("b", "y")] }, null, 2);
    await writeFile(legacy, text.slice(0, text.length - 40));
    await expect(splitStatementStore(legacy, lock)).rejects.toThrow(/truncated|JSON/);
    await writeFile(legacy, JSON.stringify({ version: 1, entries: [entryOf("a", "x"), { slug: "b" }] }));
    await expect(splitStatementStore(legacy, lock)).rejects.toThrow(/entry 2 is invalid/);
    expect(existsSync(statementShardDir(legacy))).toBe(false);
    expect(existsSync(legacy)).toBe(true);
  });

  it("run again, merges what a process on older code wrote to the file since, losing no proposal or decision either way; idempotent", async () => {
    const doc = path.join(root, "doc");
    const store = path.join(doc, "statements.json");
    const lock = path.join(root, STATEMENT_STORE_LOCK_FILENAME);
    const at = (d: string) => `2026-11-${d}T00:00:00Z`;
    // the single file as it was, and the first split
    const mono0 = [
      entryOf("a", "Papers.A.a1", { recorded_at: at("01") }),
      entryOf("b", "Papers.B.b1", { recorded_at: at("01"), proposal_id: "b-b1" }),
      entryOf("c", "Papers.C.c1", { recorded_at: at("01"), proposal_id: "b-c1" }),
      entryOf("d", "Papers.D.d1", { recorded_at: at("01"), proposal_id: "b-d1", decision: "defer" }),
    ];
    await mkdir(doc, { recursive: true });
    await writeFile(store, JSON.stringify({ version: 1, entries: mono0 }, null, 2));
    await splitStatementStore(store, lock);
    // this code since, in the shards: a re-scan of a; b's owner decides
    await recordScan(store, "a", scanOf(["Papers.A.a1", "Papers.A.a2"]), filtered(["Papers.A.a1"]), at("05"), lock);
    await recordProposals(store, "a", [{ verdict: "propose", source: { ref: "Papers.A.a1" }, id: "b-a1" }] as never, lock);
    await recordDecisions(store, "b", new Map([["b-b1", "accept"]]) as never, lock);
    // older code since, in the single file (whole): a proposal and a decision for c, a re-scan of d
    // (an older scan of a, which it never re-scanned, and e, a paper new to the store)
    const mono1 = [
      entryOf("a", "Papers.A.a1", { recorded_at: at("01") }),
      entryOf("b", "Papers.B.b1", { recorded_at: at("01"), proposal_id: "b-b1" }),
      entryOf("c", "Papers.C.c1", { recorded_at: at("01"), proposal_id: "b-c1", decision: "reject" }),
      entryOf("d", "Papers.D.d1", { recorded_at: at("07") }), // the re-scan keeps no proposal (older code read it so)
      entryOf("d", "Papers.D.d2", { recorded_at: at("07") }),
      entryOf("e", "Papers.E.e1", { recorded_at: at("07"), proposal_id: "b-e1" }),
    ];
    const monoText = JSON.stringify({ version: 1, entries: mono1 }, null, 2);
    await writeFile(store, monoText);
    const r = await splitStatementStore(store, lock);
    expect(r).toMatchObject({ written: ["c", "d", "e"], unchanged: ["a", "b"], backup: null });
    const pick = async (slug: string) => (await loadShard(store, slug)).map((e) => [e.name, e.recorded_at, e.proposal_id, e.decision]);
    // a: the shard's newer scan, its proposal kept
    expect(await pick("a")).toEqual([["Papers.A.a1", at("05"), "b-a1", null], ["Papers.A.a2", at("05"), null, null]]);
    // b: a tie keeps the shard's; its decision, made by this code, kept
    expect(await pick("b")).toEqual([["Papers.B.b1", at("01"), "b-b1", "accept"]]);
    // c: the decision older code recorded in the file merged in
    expect(await pick("c")).toEqual([["Papers.C.c1", at("01"), "b-c1", "reject"]]);
    // d: the file's newer scan, the shard's proposal and decision kept on it
    expect(await pick("d")).toEqual([["Papers.D.d1", at("07"), "b-d1", "defer"], ["Papers.D.d2", at("07"), null, null]]);
    expect(await pick("e")).toEqual([["Papers.E.e1", at("07"), "b-e1", null]]);
    // the file untouched; run again, nothing changes (no shard rewritten)
    expect(await readFile(store, "utf8")).toBe(monoText);
    const stamp = (slug: string) => statSync(statementShardPath(store, slug), { bigint: true }).mtimeNs;
    const before = ["a", "b", "c", "d", "e"].map(stamp);
    const again = await splitStatementStore(store, lock);
    expect(again).toMatchObject({ written: [], unchanged: ["a", "b", "c", "d", "e"], backup: null });
    expect(["a", "b", "c", "d", "e"].map(stamp)).toEqual(before);
    expect(existsSync(`${statementShardDir(store)}.split-tmp`)).toBe(false);
  });

  it("when two sides both set a proposal or decision and differ, the shard's wins", () => {
    const s = [entryOf("a", "x", { recorded_at: "t1", proposal_id: "b-new", decision: "accept" })];
    const m = [entryOf("a", "x", { recorded_at: "t2", proposal_id: "b-old", decision: "defer" })];
    expect(mergePaper(s, m)).toEqual([{ ...m[0], proposal_id: "b-new", decision: "accept" }]);
    expect(mergePaper(null, m)).toEqual(m);
  });

  it("--retire-monolith renames the file .bak after the merge; without it the file is never removed", async () => {
    const doc = path.join(root, "doc");
    const store = path.join(doc, "statements.json");
    const lock = path.join(root, STATEMENT_STORE_LOCK_FILENAME);
    await mkdir(doc, { recursive: true });
    const text = JSON.stringify({ version: 1, entries: [entryOf("a", "Papers.A.a1", { proposal_id: "b-a1" })] }, null, 2);
    await writeFile(store, text);
    await splitStatementStore(store, lock);
    await splitStatementStore(store, lock);
    expect(existsSync(store)).toBe(true);
    await writeFile(`${store}.bak`, "an earlier backup\n");
    const r = await splitStatementStore(store, lock, () => {}, { retire: true });
    expect(existsSync(store)).toBe(false);
    expect(r.backup).toMatch(/statements\.json\.bak-/);
    expect(await readFile(r.backup!, "utf8")).toBe(text);
    expect(await readFile(`${store}.bak`, "utf8")).toBe("an earlier backup\n");
    expect((await loadShard(store, "a"))[0]).toMatchObject({ proposal_id: "b-a1" });
  });
});
