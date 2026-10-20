import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { Catalog } from "../../src/toolkit/init.js";
import { writeBundle, type BundleArgs } from "../../src/verify/bundle.js";
import { blobHash, checkSelfContained, githubTree, leanHeader, planRequires, renderLakefile, toolkitRequires, type PublicTree } from "../../src/verify/bundle_lean.js";
import type { VerifyReportJson } from "../../src/verify/report.js";
import type { EnvsJson } from "../../src/verify/types.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

const REV = "1".repeat(40);
const CATALOG: Catalog = {
  lean_toolchain: "leanprover/lean4:v4.33.0",
  mathlib_rev: "a".repeat(40),
  domains: [],
  libraries: {
    Causalean: { summary: "causal", require: { git: "https://github.com/x/causal", rev: REV }, lib: "Causalean", provides: ["FoML"] },
    FoML: { summary: "learning", require: { path: "third_party/foml" }, lib: "FoML" },
    StatLean: { summary: "statistics", require: { path: "third_party/StatLean" }, lib: "StatLean" },
  },
};
const LAKEFILE = [
  'name = "tk"', "", "[leanOptions]", "relaxedAutoImplicit = false  # strict", "",
  "[[require]]", 'name = "Causalean"', 'path = "../base"', "",
  "[[lean_lib]]", 'name = "Toolkit"', "",
  "[[lean_lib]]", 'name = "Papers"', "requiresModuleSystem = true", "",
  "[[lean_exe]]", 'name = "paper_index"', 'root = "PaperIndex"', "",
].join("\n");

const git = (dir: string, ...args: string[]): string => {
  const r = spawnSync("git", ["-C", dir, "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false", ...args], { encoding: "utf8" });
  if (r.status !== 0) throw new Error(`git ${args.join(" ")}: ${r.stderr}`);
  return r.stdout.trim();
};

/** A toolkit beside the local checkout it requires Causalean from (`../base`) and a repository
 * root holding `third_party/`. The paper imports the toolkit, Causalean, FoML, StatLean, Mathlib. */
async function seed(paper = "module\npublic import Mathlib.Data.Real.Basic\npublic import Toolkit.A\npublic import Causalean.X\npublic import FoML.Z\npublic import StatLean.S\n\ntheorem rate : True := trivial\n"): Promise<{ root: string; base: string; args: BundleArgs }> {
  const top = await mkdtemp(path.join(os.tmpdir(), "bundle-lean-"));
  tmp.push(top);
  const w = async (rel: string, text: string): Promise<void> => {
    await mkdir(path.dirname(path.join(top, rel)), { recursive: true });
    await writeFile(path.join(top, rel), text, "utf8");
  };
  await w("tk/Papers/Demo/Basic.lean", paper);
  await w("tk/Papers/Demo.lean", "module\npublic import Papers.Demo.Basic\n");
  await w("tk/Toolkit.lean", "import Toolkit.A\nimport Toolkit.Unused\n");
  await w("tk/Toolkit/A.lean", "import Toolkit.B\n/- import Nowhere.At.All -/\ndef a := 1\n/-- a note\nimport json\n-/\ndef b := 2\n");
  await w("tk/Toolkit/B.lean", "-- leaf\n");
  await w("tk/Toolkit/Unused.lean", "import Causalean.Unreached\n");
  await w("tk/lean-toolchain", `${CATALOG.lean_toolchain}\n`);
  await w("tk/lakefile.toml", LAKEFILE);
  await w("tk/lake-manifest.json", JSON.stringify({ packages: [{ name: "mathlib", rev: CATALOG.mathlib_rev }, { name: "Causalean", dir: "../base" }] }));
  await w("base/lakefile.toml", 'name = "Causalean"\n[[require]]\nname = "FoML"\npath = "third_party/foml"\n');
  await w("base/Causalean/X.lean", "import Causalean.Y\n");
  await w("base/Causalean/Y.lean", "-- y\n");
  await w("base/Causalean/Unreached.lean", "-- not used by the paper\n");
  await w("base/third_party/foml/FoML/Z.lean", "-- z\n");
  await w("repo/third_party/StatLean/StatLean/S.lean", "import Mathlib.Order.Basic\nimport StatLean.T\n");
  await w("repo/third_party/StatLean/StatLean/T.lean", "-- t\n");
  await w("repo/third_party/StatLean/lakefile.toml", 'name = "StatLean"\n[[require]]\nname = "mathlib"\nscope = "leanprover-community"\n');
  await w("repo/third_party/StatLean/LICENSE", "Apache-2.0\n");
  await w("repo/third_party/StatLean/.lake/build/x.olean", "bin");
  await w("tk/runs/demo/source/main.tex", "\\documentclass{article}\n\\begin{document}\nHello.\n\\end{document}\n");
  const root = path.join(top, "tk");
  const core = { qid: "demo", symbols: [], assumptions: [], definitions: [], statements: [] } as unknown as Core;
  const report = { run: { early_stop: false }, results: [{ node_id: "thm:rate", label: "thm:rate", kind: "theorem", bucket: "verified", lean: { file: "Basic.lean", decl: "Papers.Demo.rate", line: 7 }, axioms: { axioms: ["propext"], clean: true }, change: null, bookkeeping: [], cited_hypotheses: [], assumed_substrate: [], added_premises: [], findings: [], statement: "The rate.", v1_5: null, inherits_refutation_from: [], crosswalk_verdict: "equivalent" }], run_level_findings: [] } as unknown as VerifyReportJson;
  const args: BundleArgs = {
    runDir: path.join(root, "runs", "demo"), toolkitRoot: root, slug: "demo_paper", mainFile: "main.tex", leanSubdir: "Papers/Demo",
    input: { envs: { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, envs: [], bibliography: [] } as unknown as EnvsJson, flatText: "", lineMap: [], refs: null, transcribed: core, core, patches: null, paperErrors: {}, findings: [], review: null },
    report, checkFragments: false, catalog: CATALOG, libraryRoot: path.join(top, "repo"),
    compile: async () => ({ status: "passed", tool: "pdflatex", pdf: "main.pdf", log_tail: "", reason: "" }),
  };
  return { root, base: path.join(top, "base"), args };
}

describe("bundle/lean is a standalone Lake project", () => {
  it("reads a Lean header only: an import in a comment or a docstring is not one", () => {
    expect(leanHeader("/- c /- nested -/ import No.Pe -/\nmodule\n-- import Nor.This\npublic import A.B\nmeta import C\nimport all «D».E\n/-- doc\nimport json\n-/\ndef x := 1\nimport Late\n")).toEqual({ module: true, imports: ["A.B", "C", "D.E"] });
    expect(leanHeader("import A\n")).toEqual({ module: false, imports: ["A"] });
  });

  it("requires each library in its public form: git from the catalogue, vendored when it has only a path, nothing a required one provides", () => {
    const toolkit = toolkitRequires(LAKEFILE);
    expect([...toolkit.values()]).toEqual([{ name: "Causalean", path: "../base" }]);
    const plan = (roots: string[]) => planRequires({ catalog: CATALOG, roots, toolkit, toolkitRoot: "/tk", libraryRoot: "/repo" }).map((r) => `${r.name}:${r.form}`);
    expect(plan(["Mathlib", "Causalean", "FoML", "StatLean", "Toolkit"])).toEqual(["Causalean:git", "StatLean:vendored", "mathlib:git"]);
    // FoML alone: the toolkit has it through Causalean, so that is what the bundle requires
    expect(plan(["FoML"])).toEqual(["Causalean:git", "mathlib:git"]);
    expect(plan([])).toEqual(["mathlib:git"]);
    // a toolkit that requires nothing providing it: FoML itself, vendored
    expect(planRequires({ catalog: CATALOG, roots: ["FoML"], toolkit: new Map(), toolkitRoot: "/tk", libraryRoot: "/repo" })[0]).toMatchObject({ name: "FoML", form: "vendored", path: "vendor/FoML", source: path.join("/repo", "third_party/foml") });
  });

  it("pins a library where the toolkit built on it: its manifest's commit, else its lakefile's rev; a path or another repository keeps the catalogue's", () => {
    const pin = (toolkit: Map<string, { name: string; path?: string; git?: string; rev?: string }>, manifest?: Map<string, string>) =>
      planRequires({ catalog: CATALOG, roots: ["Causalean"], toolkit, toolkitRoot: "/tk", libraryRoot: "/repo", ...(manifest ? { manifest } : {}) })[0]!;
    const git = (rev?: string, url = "https://github.com/x/causal.git") => new Map([["Causalean", { name: "Causalean", git: url, ...(rev ? { rev } : {}) }]]);
    expect(pin(git("main"), new Map([["Causalean", "b".repeat(40)]]))).toMatchObject({ rev: "b".repeat(40), catalogRev: REV });
    expect(pin(git("c".repeat(40)))).toMatchObject({ rev: "c".repeat(40), catalogRev: REV });
    expect(pin(git(undefined))).toMatchObject({ rev: REV });
    // a branch moves: only a commit is a pin
    expect(pin(git("main"))).toMatchObject({ rev: REV });
    expect(pin(git("c".repeat(40)))).toMatchObject({ fromToolkit: true });
    expect(pin(git(undefined))).not.toHaveProperty("fromToolkit");
    expect(pin(toolkitRequires(LAKEFILE), new Map([["Causalean", "b".repeat(40)]]))).toMatchObject({ rev: REV });
    expect(pin(git("d".repeat(40), "https://github.com/someone/fork"))).toMatchObject({ rev: REV });
  });

  it("keeps the pins one set: a library pinned from the toolkit brings the toolkit's Mathlib, else the catalogue's Mathlib", () => {
    const mathlibOf = (toolkit: Map<string, { name: string; path?: string; git?: string; rev?: string }>, manifest: Map<string, string>) =>
      planRequires({ catalog: CATALOG, roots: ["Causalean"], toolkit, toolkitRoot: "/tk", libraryRoot: "/repo", manifest }).find((r) => r.name === "mathlib")!.rev;
    const manifest = new Map([["Causalean", "b".repeat(40)], ["mathlib", "e".repeat(40)]]);
    expect(mathlibOf(new Map([["Causalean", { name: "Causalean", git: "https://github.com/x/causal" }]]), manifest)).toBe("e".repeat(40));
    expect(mathlibOf(toolkitRequires(LAKEFILE), manifest)).toBe("a".repeat(40));
  });

  it("writes a generated lakefile, the pin, root modules, Check.lean and the vendored library; records what it was built against", async () => {
    const { args, base } = await seed();
    const r = await writeBundle(args);
    const lean = path.join(args.runDir, "bundle", "lean");
    const read = (f: string): Promise<string> => readFile(path.join(lean, f), "utf8");
    expect(await read("lakefile.toml")).toBe([
      'name = "demo-paper"', 'defaultTargets = ["Papers", "Toolkit"]', "",
      "# Generated by LeanSmith: a standalone project. It requires the public base libraries",
      "# only; everything else it uses is in this directory. Mathlib stays the last require.", "",
      "[leanOptions]", "relaxedAutoImplicit = false", "",
      "# causal", "[[require]]", 'name = "Causalean"', 'git = "https://github.com/x/causal"', `rev = "${REV}"`, "",
      "# statistics", "[[require]]", 'name = "StatLean"', 'path = "vendor/StatLean"', "",
      "# the Lean mathematical library", "[[require]]", 'name = "mathlib"', 'git = "https://github.com/leanprover-community/mathlib4"', `rev = "${CATALOG.mathlib_rev}"`, "",
      "[[lean_lib]]", 'name = "Papers"', "requiresModuleSystem = true", "",
      "[[lean_lib]]", 'name = "Toolkit"', "",
    ].join("\n"));
    expect(await read("lean-toolchain")).toBe("leanprover/lean4:v4.33.0\n");
    expect(existsSync(path.join(lean, "lake-manifest.json"))).toBe(false);
    expect(await read("Check.lean")).toContain("import Papers\n");
    expect(await read("Check.lean")).toContain("#print axioms Papers.Demo.rate\n");
    // the toolkit: the transitive closure of what the paper imports, nothing else
    expect(r.bundle.lean!.toolkit_modules).toEqual(["Toolkit.A", "Toolkit.B"]);
    expect(await read("Toolkit.lean")).toBe("import Toolkit.A\nimport Toolkit.B\n");
    expect(existsSync(path.join(lean, "Toolkit", "Unused.lean"))).toBe(false);
    // vendored with its licence, without build products
    expect(await read("vendor/StatLean/LICENSE")).toBe("Apache-2.0\n");
    expect(existsSync(path.join(lean, "vendor", "StatLean", "StatLean", "T.lean"))).toBe(true);
    expect(existsSync(path.join(lean, "vendor", "StatLean", ".lake"))).toBe(false);
    expect(r.bundle.lean).toMatchObject({ manifest: false, check: "Check.lean", self_contained: { ok: true, problems: [] }, warnings: [] });
    // built against: the files of the local checkout the paper reaches (through the library it provides too), by content
    const b = r.bundle.lean!.base[0]!;
    expect(b).toMatchObject({ name: "Causalean", public_rev: REV, local_rev: null, status: "unverified" });
    expect(b.files).toEqual({ "Causalean/X.lean": blobHash(Buffer.from("import Causalean.Y\n")), "Causalean/Y.lean": blobHash(Buffer.from("-- y\n")), "third_party/foml/FoML/Z.lean": blobHash(Buffer.from("-- z\n")) });
    expect(b.files["Causalean/Y.lean"]).toBe(spawnSync("git", ["hash-object", path.join(base, "Causalean", "Y.lean")], { encoding: "utf8" }).stdout.trim());
    expect(JSON.parse(await read("built-against.json"))[0].files).toEqual(b.files);
    // not verified offline is a note, not a blocking item
    expect(r.bundle.lean!.notes[0]).toContain("was NOT verified (not possible offline): `leansmith report demo_paper --verify-public`");
    expect(r.todo).toEqual([]);
    const readme = await read("README.md");
    expect(readme).toContain("- Theorem labelled `thm:rate`: `Papers.Demo.rate` (`Papers/Demo/Basic.lean:7`)");
    expect(readme).toContain(`- \`Causalean\` (causal): \`https://github.com/x/causal\` at \`${REV}\`; it brings in \`FoML\``);
    expect(readme).toContain("- `StatLean` (statistics): no public repository carries the adapted copy this was built with, so it is included in `vendor/StatLean/`");
    expect(readme).toContain("Note: built against a local copy of Causalean: 3 file(s) of it are reached");
    expect(readme).not.toContain(os.tmpdir());
  });

  it("an import that resolves nowhere, a path out of the bundle and a machine path are blocking", async () => {
    const { args, root } = await seed(`module\npublic import Papers.Other.Thing\npublic import Elsewhere.Lib\npublic import Toolkit.A\n-- see ${"ROOT"}/notes\n`);
    const file = path.join(root, "Papers", "Demo", "Basic.lean");
    await writeFile(file, (await readFile(file, "utf8")).replace("ROOT", root), "utf8");
    const r = await writeBundle(args);
    const problems = r.bundle.lean!.self_contained.problems;
    expect(r.bundle.lean!.self_contained.ok).toBe(false);
    expect(problems).toEqual(expect.arrayContaining([
      "`Papers/Demo/Basic.lean` imports `Papers.Other.Thing`, which is neither a file of the bundle nor a module of a library it requires",
      "`Papers/Demo/Basic.lean` imports `Elsewhere.Lib`, which is neither a file of the bundle nor a module of a library it requires",
      `\`Papers/Demo/Basic.lean\` names a path of the machine it was built on (\`${root}\`)`,
    ]));
    expect(r.todo.filter((t) => t.group === "lean-contained")).toHaveLength(problems.length);
    expect(r.bundle.todo.blocking).toBe(problems.length);
    expect(await readFile(path.join(args.runDir, "bundle", "lean", "README.md"), "utf8")).toContain("NOT self-contained");
    expect(await readFile(path.join(args.runDir, "bundle", "corrected_paper", "TODO.md"), "utf8")).toContain("## The Lean directory is not self-contained");

    const dir = path.join(root, "probe");
    await mkdir(dir, { recursive: true });
    const requires = planRequires({ catalog: CATALOG, roots: ["StatLean"], toolkit: new Map(), toolkitRoot: root, libraryRoot: root });
    await writeFile(path.join(dir, "lakefile.toml"), `${renderLakefile({ name: "p", libs: ["Papers"], requires, toolkitLakefile: null })}\n[[require]]\nname = "x"\npath = "../../x"  # out\n[[require]]\nname = "y"\npath = "/abs/y"\n`, "utf8");
    expect(await checkSelfContained({ leanDir: dir, requires, forbidden: [] })).toEqual([
      "`lakefile.toml` refers to a path outside the bundle (`../../x`)",
      "`lakefile.toml` refers to a path outside the bundle (`/abs/y`)",
      "`vendor/StatLean` (StatLean) carries no licence or NOTICE file",
    ]);
  });

  it("compares the content built against with the public revision, never the commit hashes", async () => {
    const { args, base } = await seed();
    git(base, "init", "-q");
    git(base, "add", "-A");
    git(base, "commit", "-q", "-m", "local history");
    const head = git(base, "rev-parse", "HEAD");
    const same: Record<string, string> = { "Causalean/X.lean": blobHash(Buffer.from("import Causalean.Y\n")), "Causalean/Y.lean": blobHash(Buffer.from("-- y\n")), "third_party/foml/FoML/Z.lean": blobHash(Buffer.from("-- z\n")) };
    const tree = (files: Record<string, string>): PublicTree => async (url, rev) => (url === "https://github.com/x/causal" && rev === REV ? { files: new Map(Object.entries(files)), partial: false } : null);

    // another repository, another commit: offline nothing is claimed and nothing blocks
    let r = await writeBundle(args);
    expect(r.bundle.lean!.base[0]).toMatchObject({ local_rev: head, status: "unverified", uncommitted: 0 });
    expect(r.todo).toEqual([]);
    // the public revision read: same content is verified, whatever the hashes of the commits
    r = await writeBundle({ ...args, publicTree: tree(same) });
    expect(r.bundle.lean!.base[0]).toMatchObject({ status: "same", changed: [] });
    expect(r.bundle.lean!.notes).toEqual([]);
    expect(r.todo).toEqual([]);
    // a file the paper reaches differs there: named, to check — never blocking (the owner's ruling: a reminder, not a refusal)
    r = await writeBundle({ ...args, publicTree: tree({ ...same, "Causalean/Y.lean": "0".repeat(40) }) });
    expect(r.bundle.lean!.base[0]).toMatchObject({ status: "differs", changed: ["Causalean/Y.lean"] });
    expect(r.todo).toMatchObject([{ group: "lean-public" }]);
    expect(r.todo[0]!.text).toContain("1 of them differ from the public revision 111111111111 this bundle requires (Causalean/Y.lean)");
    expect(r.bundle.todo.blocking).toBe(0);
    expect(await readFile(path.join(args.runDir, "bundle", "lean", "README.md"), "utf8")).toContain("**Warning — this may not be what was built:**");
    // the public revision could not be read: said, not blocking
    r = await writeBundle({ ...args, publicTree: async () => null });
    expect(r.bundle.lean!.notes[0]).toContain("was NOT verified (the public revision could not be read)");
    expect(r.todo).toEqual([]);

    // the public revision is in the local repository: compared offline; an uncommitted change shows
    const catalog: Catalog = { ...CATALOG, libraries: { ...CATALOG.libraries, Causalean: { ...CATALOG.libraries.Causalean!, require: { git: "https://github.com/x/causal", rev: head } } } };
    r = await writeBundle({ ...args, catalog });
    expect(r.bundle.lean!.base[0]).toMatchObject({ status: "same", uncommitted: 0 });
    await writeFile(path.join(base, "Causalean", "Y.lean"), "-- y, edited\n", "utf8");
    await writeFile(path.join(base, "Causalean", "Unreached.lean"), "-- edited, but the paper does not reach it\n", "utf8");
    r = await writeBundle({ ...args, catalog });
    expect(r.bundle.lean!.base[0]).toMatchObject({ status: "differs", uncommitted: 1, changed: ["Causalean/Y.lean"] });
    expect(r.bundle.todo).toMatchObject({ total: 1, blocking: 0 });
  });

  it("reads a public revision from GitHub: one listing, or the subtrees the files are under when it is truncated", async () => {
    const asked: string[] = [];
    const api = "https://api.github.com/repos/x/causal/git/trees/";
    const trees: Record<string, { tree: Array<{ path: string; type: string; sha: string }>; truncated?: boolean }> = {
      [`${api}${REV}?recursive=1`]: { tree: [], truncated: true },
      [`${api}${REV}`]: { tree: [{ path: "Causalean", type: "tree", sha: "t1" }, { path: "docs", type: "tree", sha: "t2" }, { path: "lakefile.toml", type: "blob", sha: "b0" }] },
      [`${api}t1?recursive=1`]: { tree: [{ path: "X.lean", type: "blob", sha: "b1" }, { path: "Sub", type: "tree", sha: "t3" }, { path: "Sub/Y.lean", type: "blob", sha: "b2" }] },
    };
    const tree = githubTree(async (url) => { asked.push(url.slice(api.length)); return trees[url] ?? null; });
    expect(await tree("https://github.com/x/causal.git", REV, ["Causalean/X.lean", "Causalean/Sub/Y.lean"])).toEqual({ files: new Map([["Causalean/X.lean", "b1"], ["Causalean/Sub/Y.lean", "b2"], ["lakefile.toml", "b0"]]), partial: false });
    expect(asked).toEqual([`${REV}?recursive=1`, REV, "t1?recursive=1"]);
    expect(await tree("https://gitlab.com/x/causal", REV, [])).toBeNull();
    expect(await githubTree(async () => null)("https://github.com/x/causal", REV, [])).toBeNull();
  });

  it("a toolkit built on another toolchain or Mathlib than the pin is a blocking warning", async () => {
    const { args, root } = await seed();
    await writeFile(path.join(root, "lean-toolchain"), "leanprover/lean4:v4.30.0\n", "utf8");
    await writeFile(path.join(root, "lake-manifest.json"), JSON.stringify({ packages: [{ name: "mathlib", rev: "b".repeat(40) }] }), "utf8");
    const r = await writeBundle(args);
    expect(r.bundle.lean!.warnings).toEqual([
      "built with the toolchain `leanprover/lean4:v4.30.0`, which differs from the pinned `leanprover/lean4:v4.33.0` this bundle requires",
      "built against Mathlib at bbbbbbbbbbbb, which differs from the public rev aaaaaaaaaaaa this bundle requires",
    ]);
    expect(r.todo.map((t) => t.group)).toEqual(["lean-public", "lean-public"]);
  });
});
