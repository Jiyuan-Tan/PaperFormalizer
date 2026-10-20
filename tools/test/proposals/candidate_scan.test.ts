// Round-B candidate filter over fixture scans: axiom / sorry / private /
// other-paper rejection, the closure fixpoint, headline exclusion, definitions travelling with the
// theorems that need them, and the scan cache keyed by the paper's source hash.
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import {
  candidateScanPath,
  filterCandidates,
  obtainScan,
  paperObjects,
  reportHeadlineDecls,
  syntheticScan,
  type CandidateScan,
  type ScanConstRef,
  type ScanDecl,
} from "../../src/proposals/candidate_scan.js";
import { writeSkeleton } from "../toolkit/helpers.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

const P = "Papers.Foo";
const base = (name: string): ScanConstRef => ({ name, class: "base", module: "Mathlib.X" });
const paper = (leaf: string): ScanConstRef => ({ name: `${P}.${leaf}`, class: "paper", module: `${P}.Main` });
function decl(leaf: string, over: Partial<ScanDecl> = {}): ScanDecl {
  return {
    name: `${P}.${leaf}`, kind: "theorem", module: `${P}.Main`, file: "Papers/Foo/Main.lean", line: 1, end_line: 2,
    is_private: false, type: `type of ${leaf}`, doc: null, axioms: ["propext"], has_sorry: false,
    type_constants: [base("Nat")], body_constants: [base("Nat.add_comm")], ...over,
  };
}
function scan(decls: ScanDecl[]): CandidateScan {
  return { schema: 1, paper: P, toolkit_prefix: "Toolkit", papers_prefix: "Papers", modules: [`${P}.Main`], declarations: decls };
}
const reasonsOf = (r: ReturnType<typeof filterCandidates>, leaf: string) => r.rejected.find((x) => x.name === `${P}.${leaf}`)?.reasons ?? [];

describe("filterCandidates", () => {
  it("rejects sorry, non-standard axioms, private declarations and other papers' constants", () => {
    const r = filterCandidates(scan([
      decl("clean"),
      decl("holey", { axioms: ["sorryAx"], has_sorry: true }),
      decl("axiomatic", { axioms: ["propext", "Foo.myAxiom"] }),
      decl("hidden", { is_private: true }),
      decl("borrower", { body_constants: [{ name: "Papers.Bar.x", class: "other_paper", module: "Papers.Bar.Main" }] }),
      decl("staged", { type_constants: [{ name: "Toolkit.Staging.S.y", class: "toolkit_staging", module: "Toolkit.Staging.S.M" }] }),
      decl("toolkitUser", { body_constants: [{ name: "Toolkit.Tricks.T.z", class: "toolkit", module: "Toolkit.Tricks.T.M" }] }),
    ]), { results: new Map() });
    expect(r.candidates.map((c) => c.name).sort()).toEqual([`${P}.clean`, `${P}.toolkitUser`]);
    expect(reasonsOf(r, "holey")).toContain("uses sorry");
    expect(reasonsOf(r, "axiomatic").join()).toMatch(/Foo\.myAxiom/);
    expect(reasonsOf(r, "hidden").join()).toMatch(/private/);
    expect(reasonsOf(r, "borrower").join()).toMatch(/another paper/);
    expect(reasonsOf(r, "staged").join()).toMatch(/staging/);
  });

  it("computes the closure as a fixpoint: a chain falls when its last link is unfit", () => {
    const r = filterCandidates(scan([
      decl("a", { body_constants: [paper("b")] }),
      decl("b", { body_constants: [paper("c")] }),
      decl("c", { has_sorry: true, axioms: ["sorryAx"] }),
      decl("d", { body_constants: [paper("e")] }),
      decl("e"),
    ]), { results: new Map() });
    expect(r.candidates.map((c) => c.name).sort()).toEqual([`${P}.d`, `${P}.e`]);
    expect(reasonsOf(r, "b").join()).toMatch(/needs Papers\.Foo\.c/);
    expect(reasonsOf(r, "a").join()).toMatch(/needs Papers\.Foo\.b/);
    expect(r.candidates.find((c) => c.name === `${P}.d`)!.moves_with).toEqual([`${P}.e`]);
    expect(r.candidates.find((c) => c.name === `${P}.e`)!.used_by).toEqual([`${P}.d`]);
  });

  it("excludes the paper's results and everything that needs them", () => {
    const r = filterCandidates(scan([
      decl("main_thm"),
      decl("helper"),
      decl("uses_main", { body_constants: [paper("main_thm")] }),
    ]), { results: new Map([["Papers.Foo.main_thm", "thm:main"]]) });
    expect(r.candidates.map((c) => c.name)).toEqual([`${P}.helper`]);
    expect(reasonsOf(r, "main_thm").join()).toMatch(/result of the paper .*thm:main/);
    expect(reasonsOf(r, "uses_main").join()).toMatch(/needs Papers\.Foo\.main_thm/);
  });

  it("admits the paper's own lemmas and propositions, flagged; its theorems stay out", () => {
    const r = filterCandidates(scan([
      decl("main_thm", { body_constants: [paper("two_forms")] }),
      decl("two_forms"),
      decl("uses_lemma", { body_constants: [paper("two_forms")] }),
    ]), {
      results: new Map([["Papers.Foo.main_thm", "thm:main"]]),
      lemmas: new Map([["Papers.Foo.two_forms", { obj_id: "lem:twoforms", kind: "lemma" }]]),
    });
    expect(r.candidates.map((c) => c.name)).toEqual([`${P}.two_forms`, `${P}.uses_lemma`]);
    expect(r.candidates[0]!.paper_result).toEqual({ obj_id: "lem:twoforms", kind: "lemma" });
    expect(r.candidates[1]!.paper_result).toBeUndefined();
    // A helper needing the paper lemma moves it along; the owner sees which paper object that is.
    expect(r.candidates[1]!.moves_with).toEqual([`${P}.two_forms`]);
    expect(r.candidates[1]!.paper_objects).toEqual({ [`${P}.two_forms`]: "lem:twoforms" });
    expect(reasonsOf(r, "main_thm").join()).toMatch(/result of the paper .*thm:main/);
  });

  it("matches a namespace-relative crosswalk name", () => {
    const r = filterCandidates(scan([decl("main_thm")]), { results: new Map([["main_thm", "thm:main"]]) });
    expect(r.candidates).toEqual([]);
  });

  it("lets definitions travel with the theorems that need them, never alone", () => {
    const r = filterCandidates(scan([
      decl("dbl", { kind: "def", axioms: [] }),
      decl("dbl_eq", { type_constants: [base("Eq"), paper("dbl")] }),
      decl("lonely", { kind: "def", axioms: [] }),
      decl("paperDef", { kind: "structure", axioms: [] }),
      decl("aboutPaperDef", { type_constants: [paper("paperDef")] }),
    ]), { results: new Map(), definitions: new Map([["Papers.Foo.paperDef", "def:model"]]) });
    expect(r.candidates.map((c) => c.name).sort()).toEqual([`${P}.aboutPaperDef`, `${P}.dbl_eq`]);
    expect(r.candidates.find((c) => c.name === `${P}.dbl_eq`)!.moves_with).toEqual([`${P}.dbl`]);
    expect(r.candidates.find((c) => c.name === `${P}.aboutPaperDef`)!.paper_objects).toEqual({ [`${P}.paperDef`]: "def:model" });
    expect(r.movable).toEqual([`${P}.aboutPaperDef`, `${P}.dbl`, `${P}.dbl_eq`, `${P}.paperDef`]);
    expect(reasonsOf(r, "lonely").join()).toMatch(/definition no candidate theorem needs/);
  });

  it("refuses a statement that mentions a theorem of the paper", () => {
    const r = filterCandidates(scan([
      decl("lem"),
      decl("about_lem", { type_constants: [paper("lem")] }),
    ]), { results: new Map() });
    expect(r.candidates.map((c) => c.name)).toEqual([`${P}.lem`]);
    expect(reasonsOf(r, "about_lem").join()).toMatch(/mentions the theorem Papers\.Foo\.lem/);
  });

  it("syntheticScan turns every core statement into a clean theorem of the paper", () => {
    const s = syntheticScan({ statements: [{ id: "lem:a-b", statement: "x" }, { id: "thm:main", statement: "y" }] } as never, "Papers.Rb1");
    expect(s.synthetic).toBe(true);
    expect(filterCandidates(s, { results: new Map() }).candidates.map((c) => c.name)).toEqual(["Papers.Rb1.lem_a_b", "Papers.Rb1.thm_main"]);
  });
});

describe("paper objects and the scan cache", () => {
  it("splits crosswalk / report anchors into results and definitions; headlines are theorem rows", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "cands-"));
    tmp.push(root);
    const cfg = await writeSkeleton(root);
    await mkdir(path.join(root, "runs", "p", "formalization"), { recursive: true });
    await writeFile(path.join(root, "runs", "p", "formalization", "crosswalk_full.json"), JSON.stringify([
      { obj_id: "thm:main", kind: "theorem", lean: { decl: "Papers.P.main" } },
      { obj_id: "def:m", kind: "definition", lean: { decl: "Papers.P.Model" } },
      { obj_id: "ass:a", kind: "assumption", lean: null },
    ]));
    await writeFile(path.join(root, "runs", "p", "report.json"), JSON.stringify({ results: [
      { node_id: "lem:x", kind: "lemma", lean: { decl: "Papers.P.x" } },
      { node_id: "def:m", kind: "definition", lean: { decl: "Papers.P.Model" } },
    ] }));
    const o = await paperObjects(cfg, "p");
    // Theorems stay out of round B; the paper's lemmas / propositions are candidates.
    expect([...o.results.keys()]).toEqual(["Papers.P.main"]);
    expect([...o.lemmas]).toEqual([["Papers.P.x", { obj_id: "lem:x", kind: "lemma" }]]);
    expect([...o.definitions]).toEqual([["Papers.P.Model", "def:m"]]);
    expect(await reportHeadlineDecls(cfg, "p")).toEqual(["Papers.P.x"]);
    // A row already moved to the toolkit is neither a candidate anchor nor a headline.
    await writeFile(path.join(root, "runs", "p", "report.json"), JSON.stringify({ results: [
      { node_id: "lem:x", kind: "lemma", lean: { decl: "Toolkit.T.x" }, moved_to_toolkit: true },
    ] }));
    expect([...(await paperObjects(cfg, "p")).lemmas]).toEqual([]);
    expect(await reportHeadlineDecls(cfg, "p")).toEqual([]);
  });

  it("obtainScan reuses the scan while the paper's sources are unchanged and re-runs after an edit", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "cands-"));
    tmp.push(root);
    const cfg = await writeSkeleton(root);
    await mkdir(path.join(root, "Papers", "P"), { recursive: true });
    await writeFile(path.join(root, "Papers", "P.lean"), "module\npublic import Papers.P.Main\n");
    await writeFile(path.join(root, "Papers", "P", "Main.lean"), "module\n");
    const calls: string[][] = [];
    const exec = async (cmd: string, argv: string[]) => {
      calls.push([cmd, ...argv]);
      if (argv[0] === "exe") {
        const out = argv[argv.indexOf("--out") + 1]!;
        await mkdir(path.dirname(out), { recursive: true });
        await writeFile(out, JSON.stringify(scan([decl("x")])));
      }
      return { code: 0, stdout: "", stderr: "" };
    };
    const args = { toolkit: cfg, qid: "p", leanSubdir: "Papers/P", exec, log: () => undefined };
    await obtainScan(args);
    expect(calls.map((c) => c[1])).toEqual(["build", "exe"]);
    expect(calls[1]).toEqual(expect.arrayContaining(["--paper", "Papers.P", "--toolkit-prefix", "Toolkit", "--papers-prefix", "Papers", "--modules", "Papers.P"]));
    expect(JSON.parse(await readFile(candidateScanPath(cfg, "p"), "utf8")).source_sha256).toMatch(/^[0-9a-f]{64}$/);
    await obtainScan(args);
    expect(calls).toHaveLength(2);
    await writeFile(path.join(root, "Papers", "P", "Main.lean"), "module\n-- edited\n");
    await obtainScan(args);
    expect(calls).toHaveLength(4);
  });

  it("a failed build is an error naming the command", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "cands-"));
    tmp.push(root);
    const cfg = await writeSkeleton(root);
    await mkdir(path.join(root, "Papers", "P"), { recursive: true });
    await writeFile(path.join(root, "Papers", "P.lean"), "module\n");
    const exec = async () => ({ code: 1, stdout: "", stderr: "error: boom" });
    await expect(obtainScan({ toolkit: cfg, qid: "p", leanSubdir: "Papers/P", exec, log: () => undefined })).rejects.toThrow(/lake build Papers\.P candidate_scan.*failed[\s\S]*boom/);
  });
});
