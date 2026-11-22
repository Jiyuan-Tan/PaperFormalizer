import { renameSync, writeFileSync } from "node:fs";
import { mkdir, mkdtemp, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { appendDecisionRecords, appendLedgerDeclarations, loadLedger, parseLedger, removeLedgerDeclarations, saveLedger, updateLedger, type LedgerDeclaration } from "../../src/toolkit/ledger.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

async function ledgerFile(): Promise<string> {
  const dir = await mkdtemp(path.join(os.tmpdir(), "ledger-"));
  tmp.push(dir);
  const file = path.join(dir, "doc", "ledger.json");
  await mkdir(path.dirname(file), { recursive: true });
  await saveLedger(file, { version: 1, declarations: [], decisions: [] });
  return file;
}

const decl = (name: string, slug: string): LedgerDeclaration => ({
  name, module: "Toolkit.Tricks.Arith.Basic", division: "Tricks", origin: { kind: "proposal", slug }, date: "2026-11-08", decision: "accept", used_by: [slug],
});

describe("toolkit ledger", () => {
  it("preserves decisions and unknown fields through parse", () => {
    const l = parseLedger(JSON.stringify({ version: 1, declarations: [], decisions: [{ id: 1 }], note: "keep" }));
    expect(l.decisions).toEqual([{ id: 1 }]);
    expect((l as Record<string, unknown>).note).toBe("keep");
  });

  it("two papers appending at once lose neither's records (one lock for every read-modify-write)", async () => {
    const file = await ledgerFile();
    const key = (r: unknown) => (r as { id?: string }).id ?? null;
    await Promise.all([
      ...Array.from({ length: 5 }, (_, i) => appendDecisionRecords(file, [{ id: `a${i}` }], key)),
      ...Array.from({ length: 5 }, (_, i) => appendDecisionRecords(file, [{ id: `b${i}` }], key)),
      appendLedgerDeclarations(file, [decl("Toolkit.x", "pa")]),
      appendLedgerDeclarations(file, [decl("Toolkit.y", "pb")]),
    ]);
    const l = await loadLedger(file);
    expect((l.decisions as Array<{ id: string }>).map((r) => r.id).sort()).toEqual([...Array.from({ length: 5 }, (_, i) => `a${i}`), ...Array.from({ length: 5 }, (_, i) => `b${i}`)].sort());
    expect(l.declarations.map((d) => d.name).sort()).toEqual(["Toolkit.x", "Toolkit.y"]);
  }, 30_000);

  it("a write by a writer holding no lock, made during an update, is not lost: the update is applied again", async () => {
    const file = await ledgerFile();
    let calls = 0;
    await updateLedger(file, (l) => {
      calls += 1;
      // first pass: an old process (no lock) appends meanwhile
      if (calls === 1) {
        const text = JSON.stringify({ ...l, decisions: [...l.decisions, { id: "old-writer" }] }, null, 2);
        writeFileSync(`${file}.tmp`, text);
        renameSync(`${file}.tmp`, file);
      }
      return { ledger: { ...l, decisions: [...l.decisions, { id: "mine" }] }, result: null };
    });
    expect(calls).toBe(2);
    expect(((await loadLedger(file)).decisions as Array<{ id: string }>).map((r) => r.id)).toEqual(["old-writer", "mine"]);
  });

  it("an append reports, under the lock and before it writes, exactly what it adds", async () => {
    const file = await ledgerFile();
    await appendLedgerDeclarations(file, [decl("Toolkit.old", "pa")]);
    const seen: unknown[] = [];
    await appendLedgerDeclarations(file, [decl("Toolkit.old", "pa"), decl("Toolkit.new", "pa")], async (added) => {
      seen.push(added);
      // not yet written
      expect((await loadLedger(file)).declarations.map((d) => d.name)).toEqual(["Toolkit.old"]);
    });
    expect(seen).toEqual([[{ name: "Toolkit.new", slug: "pa" }]]);
  });

  it("an undo removes only the promotion's declarations: by name and the slug they were recorded from", async () => {
    const file = await ledgerFile();
    await appendLedgerDeclarations(file, [decl("Toolkit.mine", "pa"), decl("Toolkit.theirs", "pb")]);
    expect(await removeLedgerDeclarations(file, [{ name: "Toolkit.theirs", slug: "pa" }])).toBe(0);
    expect(await removeLedgerDeclarations(file, [{ name: "Toolkit.mine", slug: "pa" }])).toBe(1);
    expect((await loadLedger(file)).declarations.map((d) => d.name)).toEqual(["Toolkit.theirs"]);
  });
});
