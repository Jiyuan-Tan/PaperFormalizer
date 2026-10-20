// A run's last share as recorded on this machine (`runs/<slug>/share.json`): apart from `share.ts`,
// which reads the bundle, so the run's page model reads the record without importing the bundle.
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";

/** `runs/<slug>/<this>`: the last share of the run; `papers/<slug>/<this>` in the registry: who shared it. */
export const SHARE_FILE = "share.json";

export type ShareStatus = "awaiting_upload" | "awaiting_sign_in" | "submitted" | "published" | "review" | "refused" | "expired";
const FINAL = new Set<ShareStatus>(["published", "review", "refused", "expired"]);
export const isFinal = (s: ShareStatus): boolean => FINAL.has(s);
export const STATUSES = new Set<string>(["awaiting_upload", "awaiting_sign_in", "submitted", "published", "review", "refused", "expired"]);

/** The last share of a run (`runs/<slug>/share.json`). `poll_token` reads its status at the
 *  service and stays on this machine (`shareView` leaves it out). */
export interface ShareRecord {
  slug: string;
  service: string;
  id: string;
  poll_token: string;
  claim_url: string;
  check_code: string;
  expires_at: string;
  started_at: string;
  status: ShareStatus;
  updated_at: string;
  /** The GitHub login that confirmed it, once the service names it. */
  login?: string;
  /** The paper's public page (published), the pull request the owner reviews (review), or what the registry refused. */
  url?: string;
  pr_url?: string;
  problems?: string[];
  /** Why an expired share ended, when not for want of a sign-in. */
  note?: string;
}
/** A share as the page shows it: the record less its token. */
export type ShareView = Omit<ShareRecord, "poll_token">;
export const shareRecordView = ({ poll_token: _t, ...v }: ShareRecord): ShareView => v;

/** The run's last share (`share.json`); null when there is none of this kind. */
export async function readShare(runDir: string): Promise<ShareRecord | null> {
  const r = await readFile(path.join(runDir, SHARE_FILE), "utf8").then((t) => JSON.parse(t) as ShareRecord, () => null);
  return r && typeof r.id === "string" && typeof r.poll_token === "string" && STATUSES.has(r.status) ? r : null;
}

/** Whether a finished run's bundle can be shared, read cheaply from `bundle/` (the share itself checks
 *  more: the seal holds, the layout is current); `reason` says why not, in a line the page shows. */
export interface Shareable { ok: boolean; reason?: string }
export async function shareableOf(runDir: string): Promise<Shareable> {
  const bundle = path.join(runDir, "bundle");
  const b = await readFile(path.join(bundle, "bundle.json"), "utf8").then((t) => JSON.parse(t) as { todo?: { blocking?: unknown } }, () => null);
  if (!b) return { ok: false, reason: "the run has no bundle yet" };
  if (!existsSync(path.join(bundle, "f4_seal.json"))) return { ok: false, reason: "its bundle has no seal: the paper's Lean was not reviewed to the end" };
  const n = typeof b.todo?.blocking === "number" ? b.todo.blocking : 0;
  return n > 0 ? { ok: false, reason: `${n} blocking item${n === 1 ? "" : "s"} in corrected_paper/TODO.md` } : { ok: true };
}
