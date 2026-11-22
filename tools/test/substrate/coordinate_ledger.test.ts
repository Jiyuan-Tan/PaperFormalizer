// Round A's toolkit apply and the ledger: its declarations are appended under the ledger's lock and
// journaled by name; a failed gate's rollback removes exactly those, keeping what another paper
// recorded meanwhile.
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { applyManifest, realApplyDeps } from "../../src/substrate/coordinate.js";
import { appendLedgerDeclarations, loadLedger } from "../../src/toolkit/ledger.js";
import { leanModule, writeSkeleton } from "../toolkit/helpers.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

const other = { name: "Toolkit.Other.theirs", module: "Toolkit.Foundations.Other.Mod", division: "Foundations", origin: { kind: "proposal" as const, slug: "other-paper" }, date: "2026-11-08", decision: "accept", used_by: [] };

async function fixture() {
  const root = await mkdtemp(path.join(os.tmpdir(), "coord-ledger-"));
  tmp.push(root);
  const cfg = await writeSkeleton(root);
  const staging = path.join(root, "staging");
  await mkdir(staging, { recursive: true });
  await writeFile(path.join(staging, "c.lean"), leanModule({ imports: ["Mathlib.Tactic"], doc: "Conditioning", body: "/-- A fact. -/\ntheorem cond_fact : True := trivial" }));
  const args = {
    toolkit: cfg, toolsDir: "/tools", stagingDir: staging, leanFiles: [], slug: "s", modulePrefix: "Toolkit.Staging.S", indexStep: null,
    manifest: { ops: [{ kind: "create_file" as const, target: "Toolkit/Foundations/Probability/Conditioning.lean", from: "c.lean", newModule: "Toolkit.Foundations.Probability.Conditioning" }], notes: "" },
  };
  return { root, cfg, args };
}

const axiomsOk = async (cmd: string) => {
  const probe = /lake env lean '?([^'\s]+)'?/.exec(cmd)?.[1];
  if (probe) return { code: 0, log: [...(await readFile(probe, "utf8")).matchAll(/#print axioms (\S+)/g)].map((m) => `'${m[1]}' depends on axioms: [propext]`).join("\n") };
  return null;
};

describe("round A's apply and the ledger", () => {
  it("a failed gate's rollback removes the apply's declarations and keeps another paper's appended meanwhile", async () => {
    const { cfg, args } = await fixture();
    const run = async (cmd: string) => {
      if (cmd.startsWith("lake build")) {
        // another paper records a declaration while this gate builds
        await appendLedgerDeclarations(cfg.ledgerPath, [other]);
        return { code: 1, log: "error: build failed" };
      }
      return (await axiomsOk(cmd)) ?? { code: 0, log: "ok" };
    };
    const r = await applyManifest(args, { ...realApplyDeps, run });
    expect(r.ok).toBe(false);
    expect(r.log).toMatch(/rolled back/);
    expect((await loadLedger(cfg.ledgerPath)).declarations.map((d) => d.name)).toEqual(["Toolkit.Other.theirs"]);
  });
});
