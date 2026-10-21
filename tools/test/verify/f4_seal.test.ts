import { mkdir, mkdtemp, rm, symlink, writeFile } from "node:fs/promises";
import { DIRECTORY_LINK, FILE_SYMLINKS } from "../platform.js";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { parsePaperFormalizerCommand } from "../../bin/paperformalizer.js";
import { addNode, setLean, setNodeReview } from "../../src/graph/mutate.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import type { ConvergenceLedger, FormalizationGraph } from "../../src/graph/types.js";
import { parseReportArgs } from "../../src/verify/report_cli.js";
import { buildF4Seal, checkF4Seal, F4_REVIEWS_FILE, F4_SEAL_FILE, f4Reviews, runSealCli, sha256, withBundle } from "../../src/verify/f4_seal.js";

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

const pass = (h: string) => ({ codex: { verdict: "matched" as const, evidence_hash: h }, claude: { verdict: "matched" as const, evidence_hash: h } });

function graph(ledger: ConvergenceLedger): FormalizationGraph {
  let g = createEmptyGraph("q");
  g = addNode(g, { id: "thm:main", kind: "theorem", provenance: "from-note", nl_statement: "the main bound", tex_anchor: "" });
  g = addNode(g, { id: "lem:side", kind: "lemma", provenance: "from-note", nl_statement: "a side fact", tex_anchor: "" });
  g = setLean(g, "thm:main", "mainThm", "Main.lean");
  g = setLean(g, "lem:side", "sideLemma", "Main.lean");
  for (const id of ["thm:main", "lem:side"]) g = setNodeReview(g, id, "matched", "h");
  return { ...g, convergenceReview: ledger, symbolReview: { "sym:K": { verdict: "matched", hash: "k" }, "sym:U": { verdict: "untagged", hash: "u" } } };
}
const ALL = { "thm:main": pass("e1"), "lem:side": pass("e2"), "sym:K": pass("e3") };
const seal = (ledger: ConvergenceLedger) => buildF4Seal({ slug: "q", paperSha256: "abc", graph: graph(ledger) });

describe("the F4 seal", () => {
  it("holds when both reviewers passed every governed target, whatever the order of the records", () => {
    const s = seal(ALL);
    expect(checkF4Seal(s)).toEqual([]);
    expect(s.unreviewed).toEqual([]);
    expect(s.targets.map((t) => t.id)).toEqual(["lem:side", "sym:K", "thm:main"]);
    expect(seal({ "sym:K": pass("e3"), "lem:side": pass("e2"), "thm:main": pass("e1") }).code).toBe(s.code);
    // a reformatted or re-keyed file is the same seal
    const { code, ...rest } = s;
    expect(checkF4Seal(JSON.parse(JSON.stringify({ code, ...rest }, null, 4)))).toEqual([]);
  });

  it("changes its code with a verdict's evidence, the paper, or a state receipt", () => {
    const base = seal(ALL);
    expect(seal({ ...ALL, "thm:main": pass("e1x") }).code).not.toBe(base.code);
    const g = graph(ALL);
    expect(buildF4Seal({ slug: "q", paperSha256: "other", graph: g }).code).not.toBe(base.code);
    expect(buildF4Seal({ slug: "q", paperSha256: "abc", graph: g, delivery: [{ node_id: "lem:x", reviewer: "codex", verdict: "matched", evidence_hash: "d" }] }).code).not.toBe(base.code);
    const cited = buildF4Seal({ slug: "q", paperSha256: "abc", graph: g, cited: [{ node_id: "lem:c", reviewer: "claude", check_status: "cited-verified", cite_id: "c1", locator: "Thm 2", evidence_hash: "d" }] });
    expect(cited.code).not.toBe(base.code);
    expect(checkF4Seal(cited)).toEqual([]);
  });

  it("covers what F5 audits: a tagged symbol cluster, a node's own review status, and nothing the graph no longer holds", () => {
    const { "sym:K": _k, ...noSym } = ALL;
    expect(seal(noSym).unreviewed).toEqual(["sym:K"]);
    expect(seal({ ...ALL, "sym:K": { codex: { verdict: "drift", evidence_hash: "e3" }, claude: { verdict: "matched", evidence_hash: "e3" } } }).unreviewed).toEqual(["sym:K"]);
    const drifted = graph(ALL);
    const s = buildF4Seal({ slug: "q", paperSha256: "abc", graph: { ...drifted, nodes: drifted.nodes.map((n) => (n.id === "lem:side" ? { ...n, review: { ...n.review, status: "drift" as const } } : n)) } });
    expect(s.unreviewed).toEqual(["lem:side"]);
    expect(seal({ ...ALL, "thm:gone": pass("e9"), "sym:U": pass("e8") }).targets.map((t) => t.id)).toEqual(["lem:side", "sym:K", "thm:main"]);
  });

  it("names a governed target one reviewer did not pass, or the two passed on different statements", () => {
    const onePeer = seal({ ...ALL, "lem:side": { codex: { verdict: "matched", evidence_hash: "e2" } } });
    expect(onePeer.unreviewed).toEqual(["lem:side"]);
    expect(checkF4Seal(onePeer).join("\n")).toContain("lem:side");
    const split = seal({ ...ALL, "lem:side": { codex: { verdict: "matched", evidence_hash: "a" }, claude: { verdict: "matched", evidence_hash: "b" } } });
    expect(split.unreviewed).toEqual(["lem:side"]);
    expect(checkF4Seal(seal({})).join("\n")).toContain("no target");
  });

  it("refuses a seal edited after it was written, and a file that is no seal", () => {
    const s = seal({ ...ALL, "lem:side": { codex: { verdict: "drift", evidence_hash: "e2" }, claude: { verdict: "matched", evidence_hash: "e2" } } });
    const forged = { ...s, unreviewed: [] };
    expect(checkF4Seal(forged).join("\n")).toContain("changed after it was written");
    expect(checkF4Seal({ ...s, targets: [...s.targets, { id: "lem:side", ...pass("e2") }], unreviewed: [] }).join("\n")).toContain("changed after it was written");
    expect(checkF4Seal({ ...seal(ALL), signed_by: "a journal" })[0]).toContain("not an F4 seal");
    expect(checkF4Seal({ version: 1 })[0]).toContain("not an F4 seal");
  });

  it("travels with the F4 reviews: the convergence passes of the reviewer log, no path of the machine, under the code", async () => {
    const log = [
      "\n===== reviewer delta/codex :: high :: wave 1 =====\n--- codex stdout ---\ndelta answer\n",
      "\n===== reviewer convergence/dual :: high :: wave 2 =====\n--- codex stdout ---\nread /home/me/tk/Papers/X.lean and /home/me\n--- claude stdout ---\nmatched\n",
    ].join("");
    const reviews = f4Reviews(log, ["/home/me", "/home/me/tk"]);
    expect(reviews).toBe("===== reviewer convergence/dual :: high :: wave 2 =====\n--- codex stdout ---\nread <local>/Papers/X.lean and <local>\n--- claude stdout ---\nmatched\n");
    expect(f4Reviews("no reviewer call")).toBe("");
    // a listed path is blanked as a path, never as the start of a longer name
    expect(f4Reviews("===== reviewer convergence/dual =====\n/home/me/x /home/melissa/y /home/me-old /home/me.\n", ["/home/me"])).toContain("<local>/x /home/melissa/y /home/me-old /home/me.");
    const bare = seal(ALL);
    const none = new Map<string, string>();
    const s = withBundle(bare, { reviews, files: none });
    expect(s.code).not.toBe(bare.code);
    expect(checkF4Seal(s)).toEqual([]);
    expect(checkF4Seal(s, { reviews, files: none })).toEqual([]);
    expect(checkF4Seal(s, { reviews: `${reviews}drift`, files: none }).join("\n")).toContain("not the file the seal was written with");
    expect(checkF4Seal(s, { reviews: null, files: none }).join("\n")).toContain("is missing");
    expect(checkF4Seal(bare, { reviews: null, files: none })).toEqual([]);
    expect(checkF4Seal(bare, { reviews, files: none }).join("\n")).toContain("not named by the seal");
    const dir = await mkdtemp(join(tmpdir(), "f4seal-"));
    tmpDirs.push(dir);
    await writeFile(join(dir, F4_SEAL_FILE), JSON.stringify(s), "utf8");
    await expect(runSealCli([dir])).rejects.toThrow(/is missing/u);
    await writeFile(join(dir, F4_REVIEWS_FILE), reviews, "utf8");
    const out: string[] = [];
    await runSealCli([dir], { log: (m) => out.push(m) });
    expect(out.join("\n")).toContain(F4_REVIEWS_FILE);
  });

  it("names every file of lean/, corrected_paper/ and page/: a changed page snapshot is refused", async () => {
    const dir = await mkdtemp(join(tmpdir(), "f4seal-"));
    tmpDirs.push(dir);
    const texts = { "lean/Papers/X.lean": "theorem x : True := trivial", "corrected_paper/main.tex": "tex", "page/page.json": "{\"schema\":1}\n" };
    for (const [f, t] of Object.entries(texts)) {
      await mkdir(dirname(join(dir, f)), { recursive: true });
      await writeFile(join(dir, f), t, "utf8");
    }
    const s = withBundle(seal(ALL), { reviews: null, files: new Map(Object.entries(texts).map(([f, t]) => [f, sha256(t)])) });
    await writeFile(join(dir, F4_SEAL_FILE), JSON.stringify(s), "utf8");
    const out: string[] = [];
    await runSealCli([dir], { log: (m) => out.push(m) });
    expect(out.join("\n")).toContain("3 file(s) it names (corrected_paper/, lean/, page/)");
    await writeFile(join(dir, "page", "page.json"), "{\"schema\":1,\"verdict\":\"no_error_found\"}\n", "utf8");
    await expect(runSealCli([dir])).rejects.toThrow(/changed after the seal was written: page\/page\.json/u);
  });

  // (`paper/`: the corrected paper's folder in a bundle written before it was renamed — it still verifies)
  it("names every file of lean/ and paper/: one changed or gone is refused, one added (a build output) is not its concern", async () => {
    const files = new Map([["lean/Papers/X.lean", sha256("theorem x : True := trivial")], ["paper/main.tex", sha256("tex")]]);
    const s = withBundle(seal(ALL), { reviews: null, files });
    expect(s.files.map((f) => f.path)).toEqual(["lean/Papers/X.lean", "paper/main.tex"]);
    expect(s.code).not.toBe(withBundle(seal(ALL), { reviews: null, files: new Map([...files, ["paper/main.tex", sha256("other")]]) }).code);
    expect(checkF4Seal(s, { reviews: null, files: new Map([...files, ["lean/.lake/build/x.olean", "h"]]) })).toEqual([]);
    expect(checkF4Seal(s, { reviews: null, files: new Map([...files, ["lean/Papers/X.lean", sha256("theorem x : False := sorry")]]) }).join("\n")).toContain("changed after the seal was written: lean/Papers/X.lean");
    expect(checkF4Seal(s, { reviews: null, files: new Map([["paper/main.tex", sha256("tex")]]) }).join("\n")).toContain("missing from the bundle: lean/Papers/X.lean");
    // a seal never names a file outside its bundle
    expect(checkF4Seal({ ...s, files: [{ path: "lean/../../etc/passwd", sha256: "h" }] })[0]).toContain("not an F4 seal");
    for (const p of ["/etc/passwd", "lean/a\nb/../../../x", "lean/./x", "lean\\..\\x", "paper/", "other/x"]) expect(checkF4Seal({ ...s, files: [{ path: p, sha256: "h" }] })[0]).toContain("not an F4 seal");
    const dir = await mkdtemp(join(tmpdir(), "f4seal-"));
    tmpDirs.push(dir);
    await mkdir(join(dir, "lean", "Papers"), { recursive: true });
    await mkdir(join(dir, "paper"));
    await writeFile(join(dir, "lean", "Papers", "X.lean"), "theorem x : True := trivial", "utf8");
    await writeFile(join(dir, "paper", "main.tex"), "tex", "utf8");
    await writeFile(join(dir, F4_SEAL_FILE), JSON.stringify(s), "utf8");
    await runSealCli([dir], { log: () => {} });
    await writeFile(join(dir, "lean", "Papers", "X.lean"), "theorem x : False := sorry", "utf8");
    await expect(runSealCli([join(dir, F4_SEAL_FILE)])).rejects.toThrow(/changed after the seal was written/u);
    // a link in a submitted bundle is not followed, whatever it points to
    const outside = await mkdtemp(join(tmpdir(), "f4seal-out-"));
    tmpDirs.push(outside);
    await writeFile(join(outside, "X.lean"), "theorem x : True := trivial", "utf8");
    await rm(join(dir, "lean", "Papers", "X.lean"));
    if (FILE_SYMLINKS) {
      await symlink(join(outside, "X.lean"), join(dir, "lean", "Papers", "X.lean"));
      await expect(runSealCli([dir])).rejects.toThrow(/missing from the bundle: lean\/Papers\/X\.lean/u);
    }
    await rm(join(dir, "lean", "Papers"), { recursive: true });
    await symlink(outside, join(dir, "lean", "Papers"), DIRECTORY_LINK);
    await expect(runSealCli([dir])).rejects.toThrow(/missing from the bundle: lean\/Papers\/X\.lean/u);
  });

  it("carries the arXiv identifier the owner declared, under the code", () => {
    const g = graph(ALL);
    const s = buildF4Seal({ slug: "q", paperSha256: "abc", graph: g, arxiv: "2301.01234v2" });
    expect(s.arxiv).toBe("2301.01234v2");
    expect(s.code).not.toBe(seal(ALL).code);
    expect(checkF4Seal(s)).toEqual([]);
    expect(checkF4Seal({ ...s, arxiv: "2301.99999v1" }).join("\n")).toContain("changed after it was written");
    expect(checkF4Seal({ ...s, arxiv: "not an id" })[0]).toContain("not an F4 seal");
    expect(parseReportArgs(["demo", "--arxiv", "arXiv:math.ST/0601001"]).arxiv).toBe("math.ST/0601001");
    for (const id of ["0704.0001", "hep-th/9901001v3", "cond-mat.stat-mech/0601001"]) expect(parseReportArgs(["demo", "--arxiv", id]).arxiv).toBe(id);
    expect(() => parseReportArgs(["demo", "--arxiv", "nonsense"])).toThrow(/not an arXiv identifier/u);
  });

  it("is checked from a bundle directory by `paperformalizer seal`", async () => {
    expect(parsePaperFormalizerCommand(["seal", "x"]).mode).toBe("seal");
    const dir = await mkdtemp(join(tmpdir(), "f4seal-"));
    tmpDirs.push(dir);
    const s = seal(ALL);
    await writeFile(join(dir, F4_SEAL_FILE), JSON.stringify(s), "utf8");
    const out: string[] = [];
    await runSealCli([dir], { log: (m) => out.push(m) });
    expect(out.join("\n")).toContain(s.code);
    await writeFile(join(dir, F4_SEAL_FILE), JSON.stringify({ ...s, paper_sha256: "swapped" }), "utf8");
    await expect(runSealCli([join(dir, F4_SEAL_FILE)])).rejects.toThrow(/does not hold/u);
    await expect(runSealCli([join(dir, "absent")])).rejects.toThrow(/cannot read the seal/u);
    await expect(runSealCli([])).rejects.toThrow(/Usage/u);
  });
});
