// Parse-once file reads for the UI server: a file is re-read only when its size or mtime changed,
// and a value derived from several files is recomputed only when one of them changed.
import { existsSync, statSync } from "node:fs";
import { readFile } from "node:fs/promises";

/** `<mtimeMs>:<size>` of a file, or "-" when absent. Cheap (one stat). */
export function signature(file: string): string {
  try {
    const s = statSync(file);
    return `${s.mtimeMs}:${s.size}`;
  } catch {
    return "-";
  }
}

const texts = new Map<string, { sig: string; text: string | null }>();

/** The file's text (null when absent), from memory while unchanged. */
export async function readCached(file: string): Promise<string | null> {
  const sig = signature(file);
  const hit = texts.get(file);
  if (hit && hit.sig === sig) return hit.text;
  const text = sig === "-" || !existsSync(file) ? null : await readFile(file, "utf8").catch(() => null);
  texts.set(file, { sig, text });
  return text;
}

const jsons = new Map<string, { sig: string; value: unknown }>();

/** The file parsed as JSON (null when absent or unparsable), from memory while unchanged. */
export async function readJsonCached<T = unknown>(file: string): Promise<T | null> {
  const sig = signature(file);
  const hit = jsons.get(file);
  if (hit && hit.sig === sig) return hit.value as T | null;
  const text = await readCached(file);
  let value: unknown = null;
  if (text !== null) {
    try { value = JSON.parse(text); } catch { value = null; }
  }
  jsons.set(file, { sig, value });
  return value as T | null;
}

const derived = new Map<string, { key: string; value: unknown }>();
const deriving = new Map<string, Promise<unknown>>();

/**
 * A value computed from `files`: recomputed only when one of their signatures changed (or `extra`
 * did). Returns the value and the key it was computed under (usable as an ETag). Two callers that
 * ask while it is being computed share the one computation.
 */
export async function derive<T>(name: string, files: string[], extra: string, compute: () => Promise<T>): Promise<{ value: T; key: string }> {
  const key = `${extra}|${files.map(signature).join("|")}`;
  const hit = derived.get(name);
  if (hit && hit.key === key) return { value: hit.value as T, key };
  const id = `${name}\n${key}`;
  let run = deriving.get(id) as Promise<T> | undefined;
  if (!run) {
    run = compute().then((value) => { derived.set(name, { key, value }); return value; }).finally(() => deriving.delete(id));
    deriving.set(id, run);
  }
  return { value: await run, key };
}

const tracked = new Map<string, { key: string; files: Map<string, string>; value: unknown }>();

/**
 * A value computed from files that are known only as it reads them (through `read`): recomputed
 * when `key` changed or one of the files it read did (a file it looked for and did not find
 * counts: it may appear).
 */
export async function deriveRead<T>(name: string, key: string, compute: (read: (file: string) => Promise<string | null>) => Promise<T>): Promise<T> {
  const hit = tracked.get(name);
  if (hit && hit.key === key && [...hit.files].every(([file, sig]) => signature(file) === sig)) return hit.value as T;
  const files = new Map<string, string>();
  const value = await compute((file) => { if (!files.has(file)) files.set(file, signature(file)); return readCached(file); });
  tracked.set(name, { key, files, value });
  return value;
}
