// `withPromotionLockUntil`: the promotion lock's wait, ended without the lock once `until` says so
// (a commit whose base moved meanwhile: `shared/commit.ts`) — the ticket withdrawn, the
// queue's order otherwise that of `withPromotionLock`.
import { mkdtemp, readdir, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { LAKE_LOCK_TIMING, promotionQueueDir, withPromotionLock, withPromotionLockUntil } from "../../src/shared/build_mutex.js";

const tmp: string[] = [];
const timing = { ...LAKE_LOCK_TIMING };
beforeEach(() => Object.assign(LAKE_LOCK_TIMING, { pollMs: 20, ticketRefreshMs: 50, ticketStaleMs: 5 * 60_000, firstLogMs: 100, progressMs: 200 }));
afterEach(async () => {
  Object.assign(LAKE_LOCK_TIMING, timing);
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

describe("withPromotionLockUntil", () => {
  it("runs under the lock as withPromotionLock does while `until` says no", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "promo-until-"));
    tmp.push(root);
    const lock = path.join(root, ".toolkit-promote.lock");
    expect(await withPromotionLockUntil(root, async () => 7, lock, undefined, async () => false)).toEqual({ value: 7 });
  });

  it("stops waiting once `until` says so — no lock, its ticket gone — and the next waiter keeps its turn", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "promo-until-"));
    tmp.push(root);
    const lock = path.join(root, ".toolkit-promote.lock");
    const order: string[] = [];
    let release!: () => void;
    const gate = new Promise<void>((r) => { release = r; });
    const holder = withPromotionLock(root, async () => { order.push("holder"); await gate; }, lock);
    await sleep(100);
    let done = false;
    const waiter = withPromotionLockUntil(root, async () => { order.push("waiter"); }, lock, undefined, async () => done);
    await sleep(100);
    const next = withPromotionLock(root, async () => { order.push("next"); }, lock);
    await sleep(100);
    expect(await readdir(promotionQueueDir(lock))).toHaveLength(2);
    done = true;
    expect(await waiter).toBeNull();
    expect(await readdir(promotionQueueDir(lock))).toHaveLength(1);
    release();
    await Promise.all([holder, next]);
    expect(order).toEqual(["holder", "next"]);
    expect(await readdir(promotionQueueDir(lock))).toEqual([]);
  });
});
