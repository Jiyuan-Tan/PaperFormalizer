import { mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { plannerCoreContextValue, readFormalizationCoreContext, restrictCoreContextValue } from "../../src/formalization/core_context.js";
import { formalizationView, parseTypedCore } from "../../src/core/core_io.js";

let tempDir: string | undefined;

afterEach(async () => {
  if (tempDir) await rm(tempDir, { recursive: true, force: true });
  tempDir = undefined;
});

describe("formalization structural core context", () => {
  it("retains declarations while omitting proof bodies and publication prose", async () => {
    tempDir = await mkdtemp(path.join(os.tmpdir(), "formalization-core-context-"));
    const fixture = JSON.parse(await import("node:fs/promises").then(({ readFile }) =>
      readFile(new URL("../fixtures/stat_ate_overlap_decay_core.json", import.meta.url), "utf8")));
    fixture.tldr = "PUBLICATION_PROSE_SENTINEL";
    fixture.statements[0].proof_tex = "PROOF_BODY_SENTINEL";
    fixture.statements[0].statement = "STATEMENT_SENTINEL";
    fixture.assumptions[0].condition = "CONDITION_SENTINEL";
    fixture.definitions[0].construction = "CONSTRUCTION_SENTINEL";
    fixture.statements[0].justification = "POSITIONING_SENTINEL_J";
    fixture.statements[0].gap = "POSITIONING_SENTINEL_G";
    fixture.statements[0].consumer = "POSITIONING_SENTINEL_C";
    fixture.bibliography = [{ key: "bib_sentinel", citation: "BIBLIOGRAPHY_SENTINEL" }];
    fixture.comparator_promise_table = [];
    const target = path.join(tempDir, "core.json");
    await writeFile(target, JSON.stringify(fixture), "utf8");

    const context = await readFormalizationCoreContext(target, "test");
    expect(context).not.toContain("PUBLICATION_PROSE_SENTINEL");
    expect(context).not.toContain("PROOF_BODY_SENTINEL");
    expect(context).toContain("STATEMENT_SENTINEL");
    expect(context).toContain("CONDITION_SENTINEL");
    expect(context).toContain("CONSTRUCTION_SENTINEL");
    // Positioning prose + bibliography are F1 material; F1.5/F2 never consume them.
    expect(context).not.toContain("POSITIONING_SENTINEL");
    expect(context).not.toContain("BIBLIOGRAPHY_SENTINEL");
    expect(context).not.toContain("comparator_promise_table");
    // Compact serialization: no indentation newlines.
    expect(context).not.toMatch(/\n {2}"/);
    // Dependency wiring survives.
    expect(context).toContain('"depends_on"');
  });
});

describe("the F1 planner's core view", () => {
  it("is the slim view plus the bibliography entries a node cites, and can be cut down to a set of nodes", async () => {
    const fixture = JSON.parse(await import("node:fs/promises").then(({ readFile }) =>
      readFile(new URL("../fixtures/stat_ate_overlap_decay_core.json", import.meta.url), "utf8")));
    fixture.statements[0].proof_tex = "PROOF_BODY_SENTINEL";
    fixture.statements[0].status = "cited";
    fixture.statements[0].source = { cite: "bk2022", locator: "Theorem 3" };
    fixture.bibliography = [{ key: "bk2022", citation: "CITED_ENTRY" }, { key: "other", citation: "UNCITED_ENTRY" }];
    const core = formalizationView(parseTypedCore(JSON.stringify(fixture), "test"));
    const view = JSON.stringify(plannerCoreContextValue(core));
    expect(view).toContain("CITED_ENTRY");
    expect(view).not.toContain("UNCITED_ENTRY");
    expect(view).not.toContain("PROOF_BODY_SENTINEL");
    const id = fixture.statements[0].id as string;
    const cut = restrictCoreContextValue(plannerCoreContextValue(core), new Set([id]));
    expect((cut.statements as { id: string }[]).map((s) => s.id)).toEqual([id]);
    expect(cut.assumptions).toEqual([]);
    expect(cut).not.toHaveProperty("symbols");
    expect(cut).not.toHaveProperty("bibliography");
  });
});
