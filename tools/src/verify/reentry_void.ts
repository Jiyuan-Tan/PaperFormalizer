/**
 * A fresh re-entry voids the pending owner receipts (2026-09-24).
 *
 * `--from-stage V1` / `--from-stage V1.5` (with or without `--fresh-review`) redoes the review. A
 * receipt still awaiting a ruling was derived from the verdicts that review replaces, so it must
 * neither block it nor be presented again:
 *
 *   weakening_repair (pending)            the receipt, and every pending suggestion in
 *                                         `patches.json` (an `unfixable` entry with a
 *                                         `suggested_repair` nobody ruled on). The entries leave
 *                                         the patch file, their ledger entries leave
 *                                         `paper_errors`: those nodes go back to the referee AS
 *                                         PRINTED, and an error that still holds is found again
 *                                         and goes to the fixer again (which re-derives any
 *                                         suggestion itself).
 *   cross_stage_rewind (pending/presented) the receipt; the F-runner flags that halted on it are
 *                                         lifted (the F stages restart at F1 on the new core).
 *   cap_reached                           the receipt; a V1.5 cap's patch directive (the round the
 *                                         cap held back) is set aside with it.
 *
 * Each is set aside under `runs/<slug>/proposals/voided/<stamp>/` (with the patch file as it stood,
 * kept as history), logged, and noted in `state.verify.voided_receipts`. Owner DECISIONS already
 * taken stay binding: declined suggestions, accepted weakening patches, owner readings
 * (`ass:pin-owner-<n>`), withdrawn findings and ruled-out rewinds are part of the patch file /
 * state and are never touched here.
 */
import { existsSync } from "node:fs";
import { copyFile, mkdir, readFile, rename } from "node:fs/promises";
import path from "node:path";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import type { StateJson } from "../types.js";
import { liftHaltFlags, receiptTargets, recordProofReviewRewind } from "./cross_stage_rewind.js";
import { isPendingSuggestion, isWithdrawn, readPatchFile, rebuildPatchedCore } from "./patches.js";
import { VERIFY_FILES, type VoidedReceipt } from "./types.js";

/** Where a re-entry's voided receipts are set aside. */
export function voidedDir(runDir: string, at: string): string {
  return path.join(runDir, "proposals", "voided", at.replace(/[:.]/g, "-"));
}

/**
 * Void every pending owner receipt of the run (see the module comment). Mutates `state.verify`,
 * rewrites `patches.json` when a pending suggestion leaves it; returns what was voided (empty when
 * nothing was pending — then nothing is written).
 */
export async function voidPendingReceipts(args: {
  runDir: string;
  state: StateJson;
  reason: string;
  log: (msg: string) => void;
  now?: () => Date;
}): Promise<VoidedReceipt[]> {
  const { runDir, state, reason, log } = args;
  const verify = state.verify!;
  // A still-pending proof-review escalation on a paper statement IS a receipt, only not yet written.
  recordProofReviewRewind(state);
  const patchFile = await readPatchFile(runDir);
  const pendingSuggestions = (patchFile?.unfixable ?? []).filter(isPendingSuggestion);
  const weak = verify.weakening_repair?.status === "pending" ? verify.weakening_repair : null;
  const rewind = verify.cross_stage_rewind?.status === "pending" ? verify.cross_stage_rewind : null;
  const cap = verify.cap_reached ?? null;
  if (!weak && pendingSuggestions.length === 0 && !rewind && !cap) return [];

  const at = (args.now ?? (() => new Date()))().toISOString();
  const dir = voidedDir(runDir, at);
  await mkdir(dir, { recursive: true });
  const rel = (f: string): string => path.relative(runDir, path.join(dir, f));
  const out: VoidedReceipt[] = [];
  const note = (r: Omit<VoidedReceipt, "reason" | "at">): void => {
    out.push({ ...r, reason, at });
    log(
      `voided pending ${r.kind} receipt (${r.items} item${r.items === 1 ? "" : "s"}${r.nodes.length ? `: ${r.nodes.join(", ")}` : ""}) — the review is redone; set aside at ${r.set_aside}` +
        (r.ledger_dropped?.length ? `; ${r.ledger_dropped.length} ledger entr${r.ledger_dropped.length === 1 ? "y" : "ies"} dropped (the referee grades those statements as printed)` : ""),
    );
  };

  if (patchFile && (weak || pendingSuggestions.length > 0 || cap)) {
    // The patch file as it stood: the fixer's earlier answers, kept as history.
    await copyFile(path.join(runDir, VERIFY_FILES.patches), path.join(dir, "patches.json"));
  }

  if (weak || pendingSuggestions.length > 0) {
    const nodes = [...new Set([...(weak?.items ?? []).map((i) => i.node), ...pendingSuggestions.map((u) => u.node)])];
    const ledger = { ...(verify.paper_errors ?? {}) };
    const dropped: Record<string, unknown> = {};
    for (const id of pendingSuggestions.map((u) => u.node)) {
      // A withdrawn finding is the owner's ruling: it stays (and needs no patch anyway).
      if (id in ledger && !isWithdrawn(ledger[id])) {
        dropped[id] = ledger[id];
        delete ledger[id];
      }
    }
    await writeJsonAtomic(path.join(dir, "weakening_repair.json"), { receipt: weak, suggestions: pendingSuggestions, ledger_entries: dropped });
    if (pendingSuggestions.length > 0) {
      const voided = new Set(pendingSuggestions);
      // (the consequential patches held for a voided suggestion go with it: `set_aside`)
      const voidedIds = new Set(pendingSuggestions.map((u) => u.node));
      const { set_aside, ...rest } = patchFile!;
      const held = (set_aside ?? []).filter((p) => !(p.consequence_of ?? []).some((o) => voidedIds.has(o)));
      await writeJsonAtomic(path.join(runDir, VERIFY_FILES.patches), { ...rest, unfixable: patchFile!.unfixable.filter((u) => !voided.has(u)), ...(held.length > 0 ? { set_aside: held } : {}) });
      // core.json follows the patch file (the next rebuild must not read the change as a hand edit).
      await rebuildPatchedCore(runDir, { detectHandEdits: false });
    }
    verify.paper_errors = ledger;
    verify.weakening_repair = null;
    note({ kind: "weakening_repair", nodes, items: weak?.items.length ?? pendingSuggestions.length, ledger_dropped: Object.keys(dropped), set_aside: rel("weakening_repair.json") });
  }

  if (rewind) {
    await writeJsonAtomic(path.join(dir, "cross_stage_rewind.json"), rewind);
    const targets = receiptTargets(rewind);
    delete verify.cross_stage_rewind;
    liftHaltFlags(state, rewind);
    note({
      kind: "cross_stage_rewind",
      nodes: [...new Set(targets.map((t) => t.node ?? t.obj_id).filter((x): x is string => !!x))],
      items: targets.length,
      set_aside: rel("cross_stage_rewind.json"),
    });
  }

  if (cap) {
    await writeJsonAtomic(path.join(dir, "cap_reached.json"), cap);
    if (cap.origin === "V1.5") {
      // The round the cap held back: its directive describes the review being replaced.
      const directive = path.join(runDir, VERIFY_FILES.v1ReviseDirective);
      if (existsSync(directive) && JSON.parse(await readFile(directive, "utf8"))?.mode === "patch") {
        await rename(directive, path.join(dir, "v1_revise_directive.json"));
      }
    }
    verify.cap_reached = null;
    note({ kind: "cap_reached", nodes: [...new Set(cap.findings.map((f) => f.id))], items: cap.findings.length, set_aside: rel("cap_reached.json") });
  }

  verify.voided_receipts = [...(verify.voided_receipts ?? []), ...out];
  return out;
}
