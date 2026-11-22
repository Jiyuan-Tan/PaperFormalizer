// An earlier version of a paper beside the run as it now stands (the page's `#/compare/<slug>/<n>`):
// one row per result of either version's core, matched by node id (a revision keeps the ids of what it
// re-points), with its statement in each and what each version's report concluded of it.
import path from "node:path";
import type { ToolkitConfig } from "../toolkit/config.js";
import type { RevisionRecord, VersionRecord } from "../verify/revision.js";
import { readJsonCached } from "./fscache.js";
import { frozenVersions, hasReport, runDir, versionSlug, type CoreFile } from "./run_model.js";

/** What a version's report concluded of one result: its bucket, and whether the paper's grade counts it
 *  among the major or the minor revisions. */
export interface Outcome { bucket: string; grade: "major" | "minor" | null }
/** One side of a version's row: the statement as that version's core holds it (TeX), and its outcome
 *  (null: the version has no report, or the report has no row for it). */
export interface CompareSide { statement: string; outcome: Outcome | null }
export interface CompareRow {
  id: string;
  kind: string;
  label: string | null;
  /** Its `\label` in the earlier version (a revision may rename it): what its old heading is found by. */
  labelBefore: string | null;
  /** As the paper numbers it ("Theorem 2.1"), when its page names it — the current version's paper,
   *  else (a result it no longer has) the earlier one's; filled by the server. */
  heading: string | null;
  /** As the earlier version's own paper numbers it, when it has the result. */
  headingBefore: string | null;
  change: "added" | "removed" | "unchanged" | "changed";
  /** In both versions, and its proof as the core holds it changed (whatever its statement did). */
  proofChanged: boolean;
  before: CompareSide | null;
  now: CompareSide | null;
}
/** A version as the compare view heads its column. */
export interface CompareVersion { n: number; frozenAt: string | null; report: boolean; verdict: string | null; grade: string | null }
/** The run's revision as it stands (`state.verify.revision`), in the counts the report gives. */
export interface CompareRevision { from: number; transcribed: boolean; cold: boolean; coldReason: string | null; same: number; changed: string[]; relocated: string[]; kept: string[]; adopted: string[]; setAside: string[] }
/** `unread`: the authors' revision is open and V1 has not read it yet — the run's core is still the
 *  version before's, so no row is given (each would read "unchanged"). */
/** `earlier`: every frozen version, newest first (the view's own picker). */
export interface CompareView { slug: string; before: CompareVersion; now: CompareVersion; earlier: Array<{ n: number; frozenAt: string | null; report: boolean }>; revision: CompareRevision | null; unread: boolean; rows: CompareRow[] }

type ReportFile = { verdict?: string; paper_grade?: { grade?: string; major?: Array<{ node?: string }>; minor?: Array<{ node?: string }> }; results?: Array<{ node_id: string; bucket: string }> };
type StatementRow = NonNullable<CoreFile["statements"]>[number] & { statement?: string };

/** The same statement, whatever its spacing. Pure. */
const squash = (t: string | undefined): string => String(t ?? "").replace(/\s+/g, " ").trim();

/** Each result's outcome in a report. Pure. */
export function outcomesOf(report: ReportFile | null): Map<string, Outcome> {
  const grade = new Map<string, "major" | "minor">();
  for (const m of report?.paper_grade?.minor ?? []) if (m?.node) grade.set(m.node, "minor");
  for (const m of report?.paper_grade?.major ?? []) if (m?.node) grade.set(m.node, "major");
  return new Map((report?.results ?? []).map((r) => [r.node_id, { bucket: r.bucket, grade: grade.get(r.node_id) ?? null }]));
}

/** The rows of the compare view: the results of the version as it now stands in its order, those only
 *  the earlier one had after them. Pure. */
export function compareRows(before: StatementRow[], now: StatementRow[], outBefore: Map<string, Outcome> | null, outNow: Map<string, Outcome> | null): CompareRow[] {
  const old = new Map(before.map((s) => [s.id, s]));
  const side = (s: StatementRow, out: Map<string, Outcome> | null): CompareSide => ({ statement: String(s.statement ?? ""), outcome: out?.get(s.id) ?? null });
  const rows: CompareRow[] = now.map((s) => {
    const b = old.get(s.id);
    return { id: s.id, kind: s.kind, label: s.tex_locator?.label ?? null, labelBefore: b?.tex_locator?.label ?? null, heading: null, headingBefore: null, change: !b ? "added" : squash(b.statement) === squash(s.statement) ? "unchanged" : "changed", proofChanged: Boolean(b) && squash(b!.proof_tex) !== squash(s.proof_tex), before: b ? side(b, outBefore) : null, now: side(s, outNow) };
  });
  const ids = new Set(now.map((s) => s.id));
  for (const b of before) if (!ids.has(b.id)) rows.push({ id: b.id, kind: b.kind, label: b.tex_locator?.label ?? null, labelBefore: b.tex_locator?.label ?? null, heading: null, headingBefore: null, change: "removed", proofChanged: false, before: side(b, outBefore), now: null });
  return rows;
}

/** Version `n` of run `slug` beside the run as it stands; null when `n` is no frozen version of it. */
export async function compareView(cfg: ToolkitConfig, slug: string, n: number): Promise<CompareView | null> {
  const { current, frozen } = await frozenVersions(cfg, slug);
  const f = frozen.find((x) => x.n === n);
  if (!f) return null;
  const dirNow = runDir(cfg, slug), dirBefore = runDir(cfg, versionSlug(slug, n));
  const side = async (dir: string, k: number, record: VersionRecord | null) => {
    const report = (await hasReport(dir)) ? await readJsonCached<ReportFile>(path.join(dir, "report.json")) : null;
    // the results as the page lists them (`runDetail`): the corrected core's, and those of the
    // transcription it dropped (one awaiting a ruling may be out of the corrected core)
    const core = await readJsonCached<{ statements?: StatementRow[] }>(path.join(dir, "discovery", "core.json"));
    const transcribed = await readJsonCached<{ statements?: StatementRow[] }>(path.join(dir, "discovery", "core.transcribed.json"));
    const statements = [...(core?.statements ?? [])];
    for (const t of transcribed?.statements ?? []) if (!statements.some((x) => x.id === t.id)) statements.push(t);
    const version: CompareVersion = { n: k, frozenAt: record?.frozen_at ?? null, report: report !== null, verdict: report?.verdict ?? null, grade: report?.paper_grade?.grade ?? null };
    return { version, statements, outcomes: report ? outcomesOf(report) : null };
  };
  const [b, a] = await Promise.all([side(dirBefore, n, f.record), side(dirNow, current, null)]);
  const rec = (await readJsonCached<{ verify?: { revision?: RevisionRecord } }>(path.join(dirNow, "state.json")))?.verify?.revision;
  // an open fix in place is no revision: the run's own transcription stands, and the revision on
  // record is the one before it
  const r = rec?.in_place ? rec.in_place.previous ?? undefined : rec;
  const revision: CompareRevision | null = r ? {
    from: r.from_version, transcribed: r.transcribed === true, cold: r.reanchor?.cold === true, coldReason: r.reanchor?.cold_reason ?? null,
    same: r.reanchor?.same ?? 0, changed: r.reanchor?.changed ?? [], relocated: r.reanchor?.broken ?? [],
    kept: r.patches?.kept ?? [], adopted: r.patches?.adopted ?? [], setAside: r.patches?.set_aside ?? [],
  } : null;
  const unread = Boolean(r) && r!.transcribed !== true;
  const earlier = await Promise.all([...frozen].reverse().map(async (x) => ({ n: x.n, frozenAt: x.record?.frozen_at ?? null, report: await hasReport(runDir(cfg, versionSlug(slug, x.n))) })));
  return { slug, before: b.version, now: a.version, earlier, revision, unread, rows: unread ? [] : compareRows(b.statements, a.statements, b.outcomes, a.outcomes) };
}
