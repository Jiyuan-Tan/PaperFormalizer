// The store of a run's page conversation (runs/<slug>/orch_messages.json), written by the UI server
// and by orch.mjs alike: every change is read → modify → write under one cross-process lock, so no
// writer's entry is lost to another's. Plain Node, synchronous: a change is a few milliseconds.
import { randomBytes } from "node:crypto";
import { existsSync, mkdirSync, readFileSync, renameSync, rmdirSync, statSync, writeFileSync } from "node:fs";
import path from "node:path";

/** A lock older than this was left by a writer that died: it is taken over. */
const STALE_MS = 10_000;
const sleep = (ms) => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);

/** The messages on file ([] when there is none). A file that is not a JSON list throws, naming it:
 *  it is never read as empty, and so never overwritten. */
export function readMessages(file) {
  let text;
  try { text = readFileSync(file, "utf8"); } catch (e) { if (e.code === "ENOENT") return []; throw e; }
  let all;
  try { all = JSON.parse(text); } catch { all = null; }
  if (!Array.isArray(all)) throw new Error(`${file} is unreadable (not a JSON list): repair it or move it aside — nothing is written over it`);
  return all;
}

/** Where a conversation the owner cleared is kept (appended to; never read back onto the page). */
export const archiveOf = (file) => file.replace(/\.json$/, ".archive.json");
const writeList = (file, all) => {
  const tmp = `${file}.${process.pid}.${randomBytes(6).toString("hex")}.tmp`;
  writeFileSync(tmp, JSON.stringify(all, null, 2) + "\n");
  renameSync(tmp, file);
};
/** The id of the next message: past every one on file (`all`), archived, or named in `more` — an
 *  `m<n>` is never given twice. Called under the store's lock. */
export function nextMessageId(file, all, more = []) {
  const n = (id) => (/^m\d+$/.test(String(id)) ? Number(String(id).slice(1)) : 0);
  return `m${1 + Math.max(0, ...all.map((m) => n(m?.id)), ...readMessages(archiveOf(file)).map((m) => n(m?.id)), ...more.map(n))}`;
}
/** The conversation cleared: its entries moved to the archive, the store left an empty list. A
 *  message of the owner's not acted on yet stops it (`{ cleared: 0, pending }`) unless `force` —
 *  then it is archived as acted on (`handled`, `cleared`), and no watcher reports it again. */
export function clearMessages(file, force = false) {
  return updateMessages(file, (all) => {
    const open = all.filter((m) => m?.from === "user" && !m.handled);
    if (open.length && !force) return { cleared: 0, pending: open.length };
    if (!all.length) return { cleared: 0, pending: 0 };
    for (const m of open) Object.assign(m, { handled: true, cleared: true });
    writeList(archiveOf(file), [...readMessages(archiveOf(file)), ...all]);
    return { cleared: all.splice(0).length, pending: 0 };
  });
}

/** `change(all)` applied to the messages on file, under the store's lock; the list is then written
 *  whole (temp file, then rename) unless `change` returns false. Returns what `change` returned. */
export function updateMessages(file, change) {
  const lock = `${file}.lock`;
  mkdirSync(path.dirname(file), { recursive: true });
  for (let waited = 0; ; waited += 25) {
    try { mkdirSync(lock); break; } catch (e) {
      if (e.code !== "EEXIST") throw e;
      let age = 0;
      try { age = Date.now() - statSync(lock).mtimeMs; } catch { continue; }
      if (age > STALE_MS) { try { rmdirSync(lock); } catch { /* another took it over */ } continue; }
      if (waited > 3 * STALE_MS) throw new Error(`${file} is locked by another writer`);
      sleep(25);
    }
  }
  try {
    const all = readMessages(file);
    const out = change(all);
    if (out !== false && (all.length || existsSync(file))) writeList(file, all);
    return out;
  } finally { try { rmdirSync(lock); } catch { /* taken over as stale */ } }
}
