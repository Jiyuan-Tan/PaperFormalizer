// Statement invariance of a promotion: moving a result into the toolkit, or re-proving one as a
// corollary of its general form, must leave every declaration of the paper and of the toolkit
// STATING what it stated. Lean certifies it: `candidate_scan` reports a structural hash of each
// declaration's statement (a theorem's type; a definition's type and value; a structure's
// constructor types), read under the names the move gives (`--rename`); the hashes taken before
// the move must be the hashes after it. A proof may change; nothing a paper claims may. The F4
// receipts of the run are carried over on the strength of it (`carryReceipts`): the same two scans
// report the closure fingerprints the receipts are keyed on, before and after.
import { readFile } from "node:fs/promises";
import path from "node:path";
import { readTypedCore } from "../core/core_io.js";
import { clearedTargets, restampCleared } from "../formalization/convergence_evidence.js";
import { parseStatementFingerprints, type StatementFingerprints } from "../formalization/statement_fingerprints.js";
import { graphPath, loadGraph, saveGraph } from "../graph/store.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { VERIFY_FILES } from "../verify/types.js";
import { shq, type ApplyDeps } from "./gate.js";

export interface MovedName { from: string; to: string }

/** The scan of the toolkit and one paper that reports statement hashes, written to `out`. */
export function fingerprintScanCmd(cfg: Pick<ToolkitConfig, "lib" | "papersLib">, paperModule: string, out: string, rename: readonly MovedName[] = []): string {
  return [
    "lake exe candidate_scan -- --graph --fingerprints",
    `--toolkit-prefix ${shq(cfg.lib)} --papers-prefix ${shq(cfg.papersLib)}`,
    `--modules ${shq(`${cfg.lib},${paperModule}`)}`,
    ...(rename.length ? [`--rename ${shq(rename.map((m) => `${m.from}=${m.to}`).join(","))}`] : []),
    `--out ${shq(out.split(path.sep).join("/"))}`,
  ].join(" ");
}

/** Declaration → statement hash from a scan's JSON; null when the scan reports none (a toolkit
 *  whose `CandidateScan.lean` predates the hash). Pure. */
export function parseFingerprints(text: string): Map<string, string> | null {
  let decls: Array<{ name?: unknown; stmt_hash?: unknown }>;
  try {
    decls = (JSON.parse(text) as { declarations?: Array<{ name?: unknown; stmt_hash?: unknown }> }).declarations ?? [];
  } catch {
    return null;
  }
  const out = new Map<string, string>();
  for (const d of decls) if (typeof d.name === "string" && typeof d.stmt_hash === "string") out.set(d.name, d.stmt_hash);
  return out.size > 0 ? out : null;
}

/** `name` as the move leaves it: a moved declaration (or anything under it) takes its new name. */
export function nameAfterMove(name: string, moved: readonly MovedName[]): string {
  for (const m of moved) {
    if (name === m.from) return m.to;
    if (name.startsWith(`${m.from}.`)) return `${m.to}${name.slice(m.from.length)}`;
  }
  return name;
}

/**
 * Why the statements are not what they were, or null: every declaration scanned before must be
 * declared after (under its new name when it moved) with the same statement hash. `before` was
 * scanned with the move's `--rename`. A declaration that is new after the move is not judged. Pure.
 */
export function statementInvarianceFailure(before: ReadonlyMap<string, string>, after: ReadonlyMap<string, string>, moved: readonly MovedName[] = []): string | null {
  const gone: string[] = [];
  const changed: string[] = [];
  for (const [name, h] of before) {
    const now = nameAfterMove(name, moved);
    const a = after.get(now);
    if (a === undefined) gone.push(now);
    else if (a !== h) changed.push(now === name ? name : `${now} (was ${name})`);
  }
  if (gone.length === 0 && changed.length === 0) return null;
  const list = (xs: string[]) => `${xs.slice(0, 8).join(", ")}${xs.length > 8 ? `, … (${xs.length})` : ""}`;
  return [
    changed.length ? `no longer state${changed.length === 1 ? "s" : ""} what ${changed.length === 1 ? "it" : "they"} stated before: ${list(changed)}` : "",
    gone.length ? `no longer declared: ${list(gone)}` : "",
  ].filter(Boolean).join("; ");
}

/** Run the scan and read its hashes; null when it fails or reports none. */
export async function takeFingerprints(d: ApplyDeps, cfg: ToolkitConfig, paperModule: string, out: string, rename: readonly MovedName[] = []): Promise<Map<string, string> | null> {
  // the scan reads compiled modules: bring them (and the exe) up to date first
  const b = await d.run(`lake build ${shq(cfg.lib)} ${shq(paperModule)} candidate_scan`, cfg.toolkitRoot);
  if (b.code !== 0) return null;
  const r = await d.run(fingerprintScanCmd(cfg, paperModule, out, rename), cfg.toolkitRoot);
  if (r.code !== 0 || !(await d.exists(out))) return null;
  return parseFingerprints(await d.readFile(out));
}

/** The closure fingerprints a scan file reports for the run in `leanDir`; null when it has none. */
async function closuresIn(cfg: ToolkitConfig, leanDir: string, scanFile: string): Promise<StatementFingerprints | null> {
  const text = await readFile(scanFile, "utf8").catch(() => null);
  return text === null ? null : parseStatementFingerprints(text, path.relative(cfg.toolkitRoot, leanDir));
}

/**
 * The run's F4 receipts across a promotion step whose statements Lean has certified unchanged: the
 * targets both reviewers had passed on the Lean as it stood (`receiptsBefore`, read off the gate's
 * scan before the step) are passed on the Lean as it stands — the same statements under the names
 * and anchors the step left — so their receipts move to the evidence of the gate's scan after it
 * (`carryReceipts`). A run with no graph, no current receipt or no closure fingerprints has nothing
 * to carry: its targets are reviewed when it next enters F4.
 */
export async function receiptsBefore(cfg: ToolkitConfig, qid: string, leanDir: string, scanBefore: string): Promise<string[]> {
  const gp = graphPath(path.join(cfg.runsDir, qid));
  try {
    const core = await readTypedCore(path.join(cfg.runsDir, qid, VERIFY_FILES.coreJson)).catch(() => null);
    return await clearedTargets({ graph: await loadGraph(gp), leanDir, core, fingerprints: await closuresIn(cfg, leanDir, scanBefore) });
  } catch {
    return [];
  }
}

export async function carryReceipts(cfg: ToolkitConfig, qid: string, leanDir: string, before: readonly string[], scanAfter: string): Promise<number> {
  if (before.length === 0) return 0;
  const gp = graphPath(path.join(cfg.runsDir, qid));
  const core = await readTypedCore(path.join(cfg.runsDir, qid, VERIFY_FILES.coreJson)).catch(() => null);
  const r = await restampCleared({ graph: await loadGraph(gp), leanDir, core, ids: before, fingerprints: await closuresIn(cfg, leanDir, scanAfter) });
  if (r.restamped.length > 0) await saveGraph(gp, r.graph);
  return r.restamped.length;
}
