/**
 * One JSON line per hold of a toolkit lock (the Lake build lock, the promotion lock): who held it
 * (host, pid, run), for what, when it was asked for, got and released. Each process appends to a
 * file of its own (`<toolkit>/.lake/paperformalizer/lock-holds/<day>/<host>-<pid>.jsonl`): appends
 * from many NFS clients to one file are not atomic. `summarizeLockHolds` reads them back per day.
 */
import { appendFile, mkdir, readdir, readFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";

export interface LockHold {
  lock: "lake" | "promote";
  host: string;
  pid: number;
  slug?: string;
  what: string;
  asked: string;
  got: string;
  released: string;
  /** The Lake lock's mode (older records: exclusive). */
  mode?: "shared" | "exclusive";
  /** Why a shared request ran exclusive. */
  fallback?: string;
}

/** The run a process works for, when it works for one (the runner sets it; its workers inherit it). */
export const RUN_SLUG_ENV = "PAPERFORMALIZER_RUN_SLUG";

export const lockHoldsDir = (root: string) => path.join(root, ".lake", "paperformalizer", "lock-holds");

/** Append one hold (never throws: a record that cannot be written is not worth a stage). */
export async function recordLockHold(
  root: string,
  h: { lock: LockHold["lock"]; what: string; asked: Date; got: Date; released: Date; mode?: LockHold["mode"]; fallback?: string },
): Promise<void> {
  try {
    const slug = process.env[RUN_SLUG_ENV];
    const rec: LockHold = {
      lock: h.lock, host: os.hostname(), pid: process.pid, ...(slug ? { slug } : {}), what: h.what.slice(0, 300),
      asked: h.asked.toISOString(), got: h.got.toISOString(), released: h.released.toISOString(),
      ...(h.mode ? { mode: h.mode } : {}), ...(h.fallback ? { fallback: h.fallback.slice(0, 300) } : {}),
    };
    const dir = path.join(lockHoldsDir(root), rec.released.slice(0, 10));
    await mkdir(dir, { recursive: true });
    await appendFile(path.join(dir, `${os.hostname().replace(/[^A-Za-z0-9_-]+/g, "_")}-${process.pid}.jsonl`), `${JSON.stringify(rec)}\n`);
  } catch { /* best effort */ }
}

/** Every hold recorded under `root` on the days from `sinceDay` (YYYY-MM-DD) on. */
export async function readLockHolds(root: string, sinceDay = ""): Promise<LockHold[]> {
  return readDays<LockHold>(lockHoldsDir(root), sinceDay);
}

/** The JSON lines of every `<dir>/<day>/*.jsonl` from `sinceDay` on. */
async function readDays<T>(dir: string, sinceDay: string): Promise<T[]> {
  const out: T[] = [];
  const days = (await readdir(dir).catch(() => [] as string[])).filter((d) => /^\d{4}-\d\d-\d\d$/.test(d) && d >= sinceDay).sort();
  for (const day of days) {
    for (const f of await readdir(path.join(dir, day)).catch(() => [] as string[])) {
      if (!f.endsWith(".jsonl")) continue;
      for (const line of (await readFile(path.join(dir, day, f), "utf8").catch(() => "")).split("\n")) {
        try { if (line.trim()) out.push(JSON.parse(line) as T); } catch { /* a torn last line */ }
      }
    }
  }
  return out;
}

/** A commit that landed off its base, or was refused for a file of its read set (`commit.ts`, I1′;
 *  2026-11-11: counted by `scripts/lock_report.ts`, as the holds are kept). */
export interface CommitEvent {
  /** (2026-11-11, step 2) `additive`: a toolkit commit landed on a later generation without a rebase;
   *  `additive-miss`: one refused there (`why`). */
  event: "off-base" | "reads-miss" | "additive" | "additive-miss";
  id: string; base: number; gen: number; file?: string; why?: string;
  /** (additive, additive-miss) the commit's steps under the locks so far, ms each. */
  ms?: Record<string, number>;
  at: string; host: string; pid: number; slug?: string;
}
export const commitEventsDir = (root: string) => path.join(root, ".lake", "paperformalizer", "commit-events");

/** Append one commit event (never throws). */
export async function recordCommitEvent(root: string, e: Pick<CommitEvent, "event" | "id" | "base" | "gen" | "file" | "why" | "ms">): Promise<void> {
  try {
    const slug = process.env[RUN_SLUG_ENV];
    const rec: CommitEvent = { ...e, at: new Date().toISOString(), host: os.hostname(), pid: process.pid, ...(slug ? { slug } : {}) };
    const dir = path.join(commitEventsDir(root), rec.at.slice(0, 10));
    await mkdir(dir, { recursive: true });
    await appendFile(path.join(dir, `${os.hostname().replace(/[^A-Za-z0-9_-]+/g, "_")}-${process.pid}.jsonl`), `${JSON.stringify(rec)}\n`);
  } catch { /* best effort */ }
}

/** Every commit event recorded under `root` on the days from `sinceDay` on. */
export async function readCommitEvents(root: string, sinceDay = ""): Promise<CommitEvent[]> {
  return readDays<CommitEvent>(commitEventsDir(root), sinceDay);
}

/** Per day: commits landed off their base, and refused for a read-set file; (2026-11-11, step 2)
 *  additive commits landed on a later generation, and refused there. */
export function summarizeCommitEvents(events: readonly CommitEvent[]): { day: string; offBase: number; readsMiss: number; additive: number; additiveMiss: number }[] {
  const days = new Map<string, { day: string; offBase: number; readsMiss: number; additive: number; additiveMiss: number }>();
  for (const e of events) {
    const day = e.at.slice(0, 10);
    const d = days.get(day) ?? { day, offBase: 0, readsMiss: 0, additive: 0, additiveMiss: 0 };
    if (e.event === "off-base") d.offBase++;
    else if (e.event === "additive") d.additive++;
    else if (e.event === "additive-miss") d.additiveMiss++;
    else d.readsMiss++;
    days.set(day, d);
  }
  return [...days.values()].sort((a, b) => a.day.localeCompare(b.day));
}

export interface LockDaySummary {
  day: string;
  lock: string;
  holds: number;
  /** Minutes: waiting summed, its median, 90th percentile and maximum; holding summed and longest. */
  waitMin: { total: number; p50: number; p90: number; max: number };
  holdMin: { total: number; max: number };
  /** Share of the day the lock was held (by one hold or more). */
  heldShare: number;
  /** Holds by mode (the Lake lock: shared holds overlap; `fallbacks` asked for one and ran
   *  exclusive), and how many held it at once: at the most, and on average while it was held. */
  shared: number;
  exclusive: number;
  fallbacks: number;
  concurrent: { peak: number; mean: number };
  /** The callers that held it longest, with their summed minutes. */
  top: { what: string; holdMin: number; holds: number }[];
}

const mins = (ms: number) => Math.round(ms / 600) / 100;

/** How many of `hs` were held at once: at the most, and on average over the time any was; and
 *  that time. */
function overlap(hs: readonly LockHold[]): { peak: number; mean: number; busyMs: number } {
  // a hold that ends as another begins does not overlap it
  const events = hs.flatMap((h) => [[Date.parse(h.got), 1], [Date.parse(h.released), -1]] as const).sort((a, b) => a[0] - b[0] || a[1] - b[1]);
  let n = 0, peak = 0, last = 0, busy = 0, area = 0;
  for (const [t, d] of events) {
    if (n > 0) { busy += t - last; area += n * (t - last); }
    n += d;
    peak = Math.max(peak, n);
    last = t;
  }
  return { peak, mean: busy > 0 ? Math.round((area / busy) * 100) / 100 : 0, busyMs: busy };
}

/** Wait and hold per day (of the release) and lock. */
export function summarizeLockHolds(holds: readonly LockHold[]): LockDaySummary[] {
  const groups = new Map<string, LockHold[]>();
  for (const h of holds) {
    const k = `${h.released.slice(0, 10)}\0${h.lock}`;
    groups.set(k, [...(groups.get(k) ?? []), h]);
  }
  return [...groups.entries()].sort(([a], [b]) => a.localeCompare(b)).map(([k, hs]) => {
    const [day, lock] = k.split("\0") as [string, string];
    const waits = hs.map((h) => Date.parse(h.got) - Date.parse(h.asked)).sort((a, b) => a - b);
    const held = hs.map((h) => Date.parse(h.released) - Date.parse(h.got));
    const q = (p: number) => waits[Math.min(waits.length - 1, Math.floor(p * waits.length))] ?? 0;
    const byWhat = new Map<string, { what: string; holdMin: number; holds: number }>();
    hs.forEach((h, i) => {
      // the caller's label (`<caller>: <command>`), else the command's first words
      const what = h.what.includes(": ") ? h.what.slice(0, h.what.indexOf(": ")) : h.what.split(/\s+/).slice(0, 3).join(" ");
      const e = byWhat.get(what) ?? { what, holdMin: 0, holds: 0 };
      e.holdMin += held[i]! / 60_000;
      e.holds++;
      byWhat.set(what, e);
    });
    const sum = (xs: number[]) => xs.reduce((a, b) => a + b, 0);
    const o = overlap(hs);
    const shared = hs.filter((h) => h.mode === "shared").length;
    return {
      day, lock, holds: hs.length,
      waitMin: { total: mins(sum(waits)), p50: mins(q(0.5)), p90: mins(q(0.9)), max: mins(waits.at(-1) ?? 0) },
      holdMin: { total: mins(sum(held)), max: mins(Math.max(0, ...held)) },
      heldShare: Math.round((o.busyMs / 86_400_000) * 1000) / 1000,
      shared, exclusive: hs.length - shared, fallbacks: hs.filter((h) => h.fallback).length,
      concurrent: { peak: o.peak, mean: o.mean },
      top: [...byWhat.values()].map((e) => ({ ...e, holdMin: Math.round(e.holdMin * 100) / 100 })).sort((a, b) => b.holdMin - a.holdMin).slice(0, 5),
    };
  });
}

/** The summary as text, one block per day and lock. */
export function formatLockSummary(rows: readonly LockDaySummary[]): string {
  return rows.map((r) =>
    `${r.day} ${r.lock}: ${r.holds} hold(s)` +
    (r.shared > 0 || r.fallbacks > 0 ? ` (${r.shared} shared, ${r.exclusive} exclusive${r.fallbacks > 0 ? `; ${r.fallbacks} asked shared, ran exclusive` : ""})` : "") +
    `, held ${r.holdMin.total} min (${Math.round(r.heldShare * 100)}% of the day, longest ${r.holdMin.max}; ` +
    `at once: peak ${r.concurrent.peak}, mean ${r.concurrent.mean}); ` +
    `waited ${r.waitMin.total} min in all (median ${r.waitMin.p50}, p90 ${r.waitMin.p90}, max ${r.waitMin.max})\n` +
    r.top.map((t) => `    ${t.holdMin} min in ${t.holds} hold(s): ${t.what}`).join("\n"),
  ).join("\n");
}
