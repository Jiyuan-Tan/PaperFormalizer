// Per-run record of the substrate gates the F4 convergence reviewers flag:
// `runs/<slug>/formalization/gates.json`. A `gated` row is an assumed-but-provable classical fact
// (owed even when the run escalates, so it is written before any early return); a `cited` row is
// a dependency matched against its source, written only once the cited match gate passes. The
// record is append-with-update: one row per (name, gate_class, cite_id, locator), the latest
// review's verdict winning. Registering a gate (`bin/gate.ts`) is a separate, explicit step.
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import type { SubstrateGate } from "../judgment.js";
import { formalizationDir } from "../paths.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";

export interface RunGateRow extends SubstrateGate {
  /** The stage whose review flagged it (`F4`). */
  stage: string;
  /** ISO timestamp of the latest review that reported it. */
  recorded_at: string;
}

export interface RunGatesFile {
  version: 1;
  gates: RunGateRow[];
}

/** `<toolkit>/runs/<slug>/formalization/gates.json`. */
export function runGatesPath(repoRoot: string, qid: string): string {
  return path.join(formalizationDir(repoRoot, qid), "formalization", "gates.json");
}

const rowKey = (g: SubstrateGate): string =>
  [g.name, g.gate_class ?? "gated", g.source?.cite_id ?? "", g.source?.locator ?? ""].join("\u0000");

/** Record `gates` for the run (update in place by key, append otherwise). Returns the file path. */
export async function appendRunGates(
  repoRoot: string,
  qid: string,
  gates: readonly SubstrateGate[],
  stage = "F4",
  now: Date = new Date(),
): Promise<string> {
  const file = runGatesPath(repoRoot, qid);
  const prior: RunGatesFile = existsSync(file)
    ? (JSON.parse(await readFile(file, "utf8")) as RunGatesFile)
    : { version: 1, gates: [] };
  const rows = new Map(prior.gates.map((g) => [rowKey(g), g] as const));
  for (const g of gates) rows.set(rowKey(g), { ...g, stage, recorded_at: now.toISOString() });
  await writeJsonAtomic(file, { version: 1, gates: [...rows.values()] } satisfies RunGatesFile);
  return file;
}
