/**
 * sha256 of a file's BYTES — the verify mode's core-identity function.
 *
 * `state.verify.core_sha256` is the hash V1.5 stamped on the core it accepted, and the
 * verify-mode F-stage entry gate re-hashes `discovery/core.json` and refuses a
 * mismatch. Both sides must hash the same thing, so this hashes the file exactly as it
 * sits on disk — never a re-serialization of the parsed object, whose key order and
 * whitespace are a property of the serializer rather than of the accepted content.
 */
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import { writeJsonAtomic } from "../shared/json_atomic.js";

export async function sha256File(filePath: string): Promise<string> {
  return createHash("sha256").update(await readFile(filePath)).digest("hex");
}

/** Where the runner records the hash of the `core.json` it last wrote. */
const writtenHashPath = (corePath: string): string => `${corePath}.written.sha256`;

/** Write `core.json` (the runner's file) and record the hash of the bytes written, so a later
 * change to the file can be told from the runner's own writes (`coreEditedSinceWrite`). */
export async function writeCoreJson(corePath: string, core: unknown): Promise<void> {
  await writeJsonAtomic(corePath, core);
  await recordCoreWrite(corePath);
}

/** Record `core.json` as it sits as the runner's own (it wrote it, or found it equal to its build). */
export async function recordCoreWrite(corePath: string): Promise<void> {
  await writeFile(writtenHashPath(corePath), `${await sha256File(corePath)}\n`, "utf8");
}

/** Whether `core.json` changed since the runner last wrote it; null when no write was recorded
 * (a run from before the record). */
export async function coreEditedSinceWrite(corePath: string): Promise<boolean | null> {
  const rec = writtenHashPath(corePath);
  if (!existsSync(rec) || !existsSync(corePath)) return null;
  return (await readFile(rec, "utf8")).trim() !== (await sha256File(corePath));
}
