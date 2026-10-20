import { existsSync, mkdtempSync, readFileSync, rmSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterAll, describe, expect, it } from "vitest";
import { parse as parseToml } from "smol-toml";
import { loadToolkitConfig } from "../../src/toolkit/config.js";
import { cacheFetches, catalogListing, initToolkit, lakefileRequires, librariesFor, loadCatalog, renderToolkitLakefile, repoRoot } from "../../src/toolkit/init.js";
import { assertToolkitLakefile } from "../../src/toolkit/lakefile.js";

const tmp = mkdtempSync(path.join(os.tmpdir(), "tc-init-"));
afterAll(() => rmSync(tmp, { recursive: true, force: true }));
const quiet = () => {};

describe("library catalog", () => {
  const c = loadCatalog();

  it("pins one toolchain and Mathlib, the template's own", () => {
    const tpl = path.join(repoRoot(), "templates", "toolkit");
    expect(readFileSync(path.join(tpl, "lean-toolchain"), "utf8").trim()).toBe(c.lean_toolchain);
    expect(readFileSync(path.join(tpl, "lakefile.toml"), "utf8")).toContain(`rev = "${c.mathlib_rev}"`);
  });

  it("every vendored library is on the catalog's pin", () => {
    for (const lib of Object.values(c.libraries)) {
      if (!("path" in lib.require) || lib.unavailable) continue;
      const dir = path.join(repoRoot(), lib.require.path);
      expect(readFileSync(path.join(dir, "lean-toolchain"), "utf8").trim()).toBe(c.lean_toolchain);
      const lakefile = ["lakefile.lean", "lakefile.toml"].map((f) => path.join(dir, f)).find((f) => existsSync(f))!;
      expect(readFileSync(lakefile, "utf8")).toContain(c.mathlib_rev);
    }
  });

  it("every library on offer is a module library: a toolkit's files are modules and can import nothing else", () => {
    for (const [name, lib] of Object.entries(c.libraries)) {
      if (!("path" in lib.require) || lib.unavailable) continue;
      const dir = path.join(repoRoot(), lib.require.path);
      const lakefile = ["lakefile.lean", "lakefile.toml"].map((f) => path.join(dir, f)).find((f) => existsSync(f))!;
      expect(readFileSync(lakefile, "utf8"), name).toMatch(/requiresModuleSystem\s*:?=\s*true/);
      expect(readFileSync(path.join(dir, `${lib.lib}.lean`), "utf8"), name).toMatch(/^module$/m);
    }
  });

  it("the statistics domain installs nothing a toolkit cannot import", () => {
    const sel = librariesFor(c, ["statistics"]);
    for (const l of sel.libs) expect(c.libraries[l]!.unavailable).toBeUndefined();
    expect(sel.libs).toEqual(["Causalean", "StatLean"]);
    expect(catalogListing(c)).not.toMatch(/not yet available/);
    expect(catalogListing(c)).toMatch(/statistics .* — Causalean, StatLean$/m);
  });

  it("a library that publishes its compiled files is fetched from its own package root before the build", () => {
    const tk = path.join(tmp, "tk");
    const f = cacheFetches(c, ["Causalean", "StatLean", "optlib"], tk);
    expect(f.map((x) => [x.name, x.argv])).toEqual([["Causalean", ["scripts/fetch_build_cache.sh"]], ["StatLean", ["port/build_cache.sh", "fetch"]]]);
    expect(f[0]!.cwd).toBe(path.join(tk, ".lake/packages/Causalean"));
    expect(existsSync(path.join(f[1]!.cwd, "port/build_cache.sh"))).toBe(true);
  });

  it("selects each library once, never one another selected library provides, never an unavailable one", () => {
    const sel = librariesFor(c, ["causal", "statistics", "learning", "optimization"]);
    // FoML and optlib come with Causalean; StatLean is installed only once the catalog offers it.
    const statLean = c.libraries.StatLean!.unavailable ? [] : ["StatLean"];
    expect(sel.libs).toEqual(["Causalean", ...statLean]);
    expect(sel.skipped.map((s) => s.name)).toEqual(statLean.length ? [] : ["StatLean"]);
    expect(librariesFor(c, ["optimization"]).libs).toEqual(["optlib"]);
    expect(librariesFor(c, ["general"]).libs).toEqual([]);
    expect(() => librariesFor(c, ["astrology"])).toThrow(/unknown domain/);
    // Libraries chosen by name join the domains' (each optional; none at all is Mathlib only).
    expect(librariesFor(c, [], ["optlib", "FoML"]).libs).toEqual(["optlib", "FoML"]);
    expect(librariesFor(c, ["causal"], ["optlib"]).libs).toEqual(["Causalean"]);
    expect(librariesFor(c, [], []).libs).toEqual([]);
    expect(() => librariesFor(c, [], ["Nonexistent"])).toThrow(/unknown library/);
  });
});

describe("theoremchecker init", () => {
  it.each(["\n", "\r\n"])("renders a %j template with the pinned revision and domain markers intact", (eol) => {
    const c = loadCatalog();
    const template = readFileSync(path.join(repoRoot(), "templates/toolkit/lakefile.toml"), "utf8")
      .replace(/\r\n/g, "\n").replace(/rev = "[0-9a-f]{40}"/, `rev = "${"0".repeat(40)}"`).replace(/\n/g, eol);
    const rendered = renderToolkitLakefile(template, c, ["Causalean"], path.join(tmp, "crlf"));
    const requires = parseToml(rendered).require as Array<{ name: string; rev?: string }>;
    expect(requires.map((r) => r.name)).toEqual(["Causalean", "mathlib"]);
    expect(requires.find((r) => r.name === "mathlib")!.rev).toBe(c.mathlib_rev);
    expect(rendered).not.toContain("\r");
  });

  it("escapes a vendored library path as valid TOML, including quotes and backslashes", () => {
    const c = loadCatalog();
    c.libraries.optlib!.require = { path: 'third_party/library "with" spaces' };
    const root = path.join(tmp, "owner\"s toolkit");
    const parsed = parseToml(lakefileRequires(c, ["optlib"], root));
    const entry = (parsed.require as Array<{ name: string; path: string }>)[0]!;
    expect(entry.name).toBe("optlib");
    expect(path.resolve(root, entry.path)).toBe(path.join(repoRoot(), 'third_party/library "with" spaces'));
  });

  it("writes a toolkit that passes the checks every verify runs: Causalean by git, Mathlib pinned last", () => {
    const dir = path.join(tmp, "causal");
    initToolkit({ dir, domains: ["causal"], owner: { name: "Ada" }, build: false, log: quiet });
    const lf = readFileSync(path.join(dir, "lakefile.toml"), "utf8");
    expect(lf).toMatch(/name = "Causalean"\ngit = "https:\/\/github.com\/Jiyuan-Tan\/CausalSmith"\nrev = "[0-9a-f]{40}"/);
    expect(lf.indexOf('name = "Causalean"')).toBeLessThan(lf.indexOf('name = "mathlib"'));
    expect(lf).toContain(`rev = "${loadCatalog().mathlib_rev}"`);
    expect(() => assertToolkitLakefile({ lib: "Toolkit", papersLib: "Papers", toolkitRoot: dir })).not.toThrow();
    const cfg = loadToolkitConfig({ explicit: dir });
    expect(cfg.baseLibraries.map((b) => b.name)).toEqual(["Mathlib", "Causalean"]);
    expect(cfg.baseLibraries[1]!.index).toBe(path.join(dir, ".lake/packages/Causalean/doc/library_index.json"));
    expect(existsSync(path.join(dir, ".git"))).toBe(true);
    expect(existsSync(path.join(dir, "theoremchecker.json.example"))).toBe(false);
  });

  it("requires a vendored library by its path in this repository, its index generated into the toolkit", () => {
    const dir = path.join(tmp, "opt");
    initToolkit({ dir, domains: ["optimization"], owner: { name: "Ada" }, build: false, log: quiet });
    const lf = readFileSync(path.join(dir, "lakefile.toml"), "utf8");
    const requires = parseToml(lf).require as Array<{ name: string; path?: string }>;
    expect(path.resolve(dir, requires.find((r) => r.name === "optlib")!.path!)).toBe(path.join(repoRoot(), "third_party/optlib"));
    const cfg = loadToolkitConfig({ explicit: dir });
    expect(cfg.baseLibraries[1]).toMatchObject({ name: "optlib", index: path.join(dir, "doc/base_index/optlib.json"), summary: expect.stringContaining("KKT") });
  });

  it("refuses a directory that is not empty", () => {
    expect(() => initToolkit({ dir: path.join(tmp, "causal"), domains: ["general"], owner: { name: "Ada" }, build: false, log: quiet })).toThrow(/not empty/);
  });
});
