/**
 * `discovery/v1_lint_warnings.json` — V1's NON-BLOCKING observations, read by V1.5 (which asks
 * the referee to settle each against the paper) and by V6 (which discloses them in the report).
 *
 * Two lists, from two different sources:
 *  - `warnings`: the transcription lint's unsettled observations about the CORE ("thm:x depends
 *    on ass:y which the environment never references"; "the proof of thm:x invokes [key, Theorem n]:
 *    a published result used inside the proof, with no cited node of its own", from `inline_citations.ts`);
 *  - `parser_warnings`: the tex parser's notes about the SOURCE ("file X included twice, folded
 *    once"; "a second proof of thm:y was discarded").
 *
 * Neither ever fails a V1 round — they are things a human (or the referee) must look at, and the
 * only way they reach one is by being carried forward, so this reader fails CLOSED on a
 * malformed file rather than reading it as "no warnings".
 */
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";

/** Relative to the run dir. Spelled out here, not imported from the V1 stage, so a reader does
 * not pull in the V1 agent machinery. */
export const V1_LINT_WARNINGS_FILE = "discovery/v1_lint_warnings.json";

export interface V1Warnings {
  /** Transcription-lint observations about the core. */
  lint: string[];
  /** Parser observations about the source tree. */
  parser: string[];
}

function stringList(value: unknown, field: string, file: string): string[] {
  if (value === undefined) return [];
  if (!Array.isArray(value) || value.some((item) => typeof item !== "string")) {
    throw new Error(`${V1_LINT_WARNINGS_FILE}: \`${field}\` must be an array of strings (${file}).`);
  }
  return value as string[];
}

/** Read the warnings V1 left, or two empty lists when it left no file. */
export async function readV1Warnings(runDir: string): Promise<V1Warnings> {
  const file = path.join(runDir, V1_LINT_WARNINGS_FILE);
  if (!existsSync(file)) return { lint: [], parser: [] };
  const raw = JSON.parse(await readFile(file, "utf8")) as Record<string, unknown>;
  return {
    lint: stringList(raw.warnings, "warnings", file),
    parser: stringList(raw.parser_warnings, "parser_warnings", file),
  };
}
