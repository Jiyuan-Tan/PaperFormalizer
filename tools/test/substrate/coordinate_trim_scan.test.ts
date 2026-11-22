import { describe, expect, it } from "vitest";
import { trimCreatedImports, type CoordinateApplyDeps } from "../../src/substrate/coordinate.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";

// The import trim is optional: a scan output it cannot read (an older CandidateScan.lean's full
// rows, a truncated file) leaves the created modules' imports as written — it never throws, which
// would roll back a coordinate whose gate passed.
const cfg = { toolkitRoot: "/tk", lib: "Toolkit", papersLib: "Papers" } as unknown as ToolkitConfig;
const depsWith = (scan: string) => {
  const writes: string[] = [];
  const d = {
    exists: async (p: string) => p.endsWith("lakefile.toml") || p.endsWith("import_scan.json"),
    readFile: async (p: string) => (p.endsWith("lakefile.toml") ? '[[lean_exe]]\nname = "candidate_scan"\nroot = "CandidateScan"\n' : scan),
    run: async () => ({ code: 0, log: "" }),
  } as unknown as CoordinateApplyDeps;
  return { d, writes, write: async (abs: string) => { writes.push(abs); } };
};

describe("study coordinate: trimming a created module's imports", () => {
  it("an older full-row scan is not read as the compact one: not trimmed, nothing written, no throw", async () => {
    const { d, writes, write } = depsWith(JSON.stringify({ declarations: [{ name: "Toolkit.A.f", module: "Toolkit.A", type_constants: [], body_constants: [] }] }));
    const logs = await trimCreatedImports(cfg, "s__a", ["Toolkit.A"], write, d);
    expect(logs).toHaveLength(1);
    expect(logs[0]).toMatch(/^\[imports\] not trimmed: .* is not a compact --graph scan/);
    expect(writes).toEqual([]);
  });

  it("a truncated scan output: not trimmed, no throw", async () => {
    const { d, writes, write } = depsWith('{"declarations": [');
    const logs = await trimCreatedImports(cfg, "s__a", ["Toolkit.A"], write, d);
    expect(logs[0]).toMatch(/^\[imports\] not trimmed: unreadable scan output/);
    expect(writes).toEqual([]);
  });
});
