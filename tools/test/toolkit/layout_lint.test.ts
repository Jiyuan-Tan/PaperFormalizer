import { describe, expect, it } from "vitest";
import {
  lintImportLayering, lintModuleHeader, lintModuleSize, lintRunTokens, lintToolkitLayout,
  type LayoutLintOptions,
} from "../../src/toolkit/layout_lint.js";
import { leanModule } from "./helpers.js";

const OPTS: LayoutLintOptions = { lib: "Toolkit", papersLib: "Papers", divisions: ["Foundations", "Tricks"] };
const imps = (...mods: string[]) => mods.map((module, line) => ({ module, line }));

describe("layering rule", () => {
  it.each([
    ["a toolkit module importing a paper module is rejected", "Toolkit.Tricks.Ineq.Basic", ["Papers.Lee.Main"], 1],
    ["Foundations importing Tricks is rejected", "Toolkit.Foundations.Prob.Tail", ["Toolkit.Tricks.Ineq.Basic"], 1],
    ["a paper importing its own modules and the toolkit is allowed", "Papers.A.Main", ["Papers.A.Aux", "Toolkit.Tricks.Ineq.Basic"], 0],
  ] as const)("%s", (_label, mod, imports, n) => {
    const f = lintImportLayering(mod, imps(...imports), OPTS);
    expect(f).toHaveLength(n);
    if (n > 0) expect(f.map((x) => x.rule)).toEqual(["layering"]);
  });
});

describe("size rule", () => {
  it("allows 600 lines and rejects 601", () => {
    expect(lintModuleSize("a.lean", `${"x\n".repeat(600)}`)).toEqual([]);
    const f = lintModuleSize("a.lean", `${"x\n".repeat(601)}`);
    expect(f).toHaveLength(1);
    expect(f[0].rule).toBe("size");
  });

  it("does not count import lines", () => {
    const imports = Array.from({ length: 60 }, (_, i) => `public import Mathlib.M${i}\n`).join("");
    expect(lintModuleSize("a.lean", `module\n${imports}${"x\n".repeat(599)}`)).toEqual([]);
    expect(lintModuleSize("a.lean", `module\n${imports}${"x\n".repeat(600)}`)).toHaveLength(1);
    // an import-like line inside a comment is content
    expect(lintModuleSize("a.lean", `module\n${imports}/-!\nimport Foo\n-/\n${"x\n".repeat(597)}`)).toHaveLength(1);
  });
});

describe("header rule", () => {
  const good = leanModule({ imports: ["Mathlib.A", "Toolkit.Foundations.B"], body: "theorem t : True := trivial" });
  const bad: Array<[string, string, RegExp]> = [
    ["missing module", good.replace(/^module\n/, ""), /first command must be `module`/],
    ["plain import", good.replace("public import Mathlib.A", "import Mathlib.A"), /must be `public import`/],
    ["unsorted", good.replace("public import Mathlib.A\npublic import Toolkit.Foundations.B", "public import Toolkit.Foundations.B\npublic import Mathlib.A"), /not sorted/],
    ["gap in block", good.replace("public import Mathlib.A\n", "public import Mathlib.A\n\n"), /contiguous/],
    ["no overview", good.replace(/\/-![\s\S]*?-\/\n/, ""), /missing the `\/-! -\/` module overview/],
    ["no section", good.replace("public section\n", ""), /exactly one blanket/],
    ["code before section", good.replace("public section", "open Nat\npublic section"), /code between the `\/-! -\/` overview/],
  ];
  it("accepts a well-formed module and a bare barrel, and rejects each header defect", () => {
    expect(lintModuleHeader("g.lean", good)).toEqual([]);
    expect(lintModuleHeader("b.lean", "module\n\n/-! Barrel. -/\n\npublic section\n")).toEqual([]);
    expect(lintModuleHeader("e.lean", leanModule({ body: "def d : Nat := 0", expose: true }))).toEqual([]);
    for (const [name, text, re] of bad) {
      const f = lintModuleHeader("x.lean", text);
      expect(f.map((x) => x.rule), name).toContain("header");
      expect(f.map((x) => x.message).join("\n"), name).toMatch(re);
    }
  });
});

describe("run-token rule", () => {
  it("checks module segments and declaration names", () => {
    const f = lintRunTokens("x.lean", "Toolkit.Tricks.Lee_Research.Main", [{ name: "Toolkit.Tricks.foo_Verify", line: 3 }]);
    expect(f.map((x) => x.message)).toEqual([
      expect.stringMatching(/module segment Lee_Research/),
      expect.stringMatching(/declaration Toolkit\.Tricks\.foo_Verify/),
    ]);
    expect(lintRunTokens("x.lean", "Toolkit.Tricks.Staging.Main", []).map((x) => x.message)).toEqual([
      expect.stringMatching(/module segment Staging is the reserved staging segment/),
    ]);
    expect(lintRunTokens("x.lean", "Toolkit.Tricks.Ineq.Basic", [{ name: "Toolkit.Tricks.Ineq.Staging.amgm", line: 4 }])
      .map((x) => x.message)).toEqual([expect.stringMatching(/declaration Toolkit\.Tricks\.Ineq\.Staging\.amgm/)]);
    expect(lintRunTokens("x.lean", "Toolkit.Tricks.Ineq.Basic", [{ name: "Toolkit.Tricks.Ineq.amgm", line: 3 }])).toEqual([]);
  });
});

describe("lintToolkitLayout", () => {
  it("applies all rules to toolkit modules, skips staging, and spares papers the size/name rules", () => {
    const findings = lintToolkitLayout([
      { path: "Toolkit/Staging/X/Main.lean", module: "Toolkit.Staging.X.Main", text: "garbage" },
      { path: "Papers/A/Main.lean", module: "Papers.A.Main", text: leanModule({ body: `theorem verify_x : True := trivial\n${"--\n".repeat(700)}` }) },
      { path: "Toolkit/Foundations/P/T.lean", module: "Toolkit.Foundations.P.T", text: leanModule({ imports: ["Toolkit.Tricks.Q"], body: "theorem t_Verify : True := trivial" }) },
    ], OPTS);
    expect(findings.map((f) => `${f.path}:${f.rule}`).sort()).toEqual([
      "Toolkit/Foundations/P/T.lean:layering",
      "Toolkit/Foundations/P/T.lean:namespace",
      "Toolkit/Foundations/P/T.lean:run-token",
    ]);
  });

  it("reports, as advisory, a declaration outside its module's topic namespace and an umbrella import", () => {
    const text = leanModule({
      imports: ["Mathlib.Tactic"],
      body: "namespace Toolkit.Foundations.P\n\ntheorem ok : True := trivial\n\nend Toolkit.Foundations.P\n\nnamespace IndepFun\n\ntheorem off : True := trivial\n\nend IndepFun",
    });
    const f = lintToolkitLayout([{ path: "Toolkit/Foundations/P/T.lean", module: "Toolkit.Foundations.P.T", text }], OPTS);
    expect(f.map((x) => [x.rule, x.advisory])).toEqual([["namespace", true], ["imports", true]]);
    expect(f[0]!.message).toContain("IndepFun.off");
    expect(f[0]!.message).not.toContain("Toolkit.Foundations.P.ok");
  });
});
