/**
 * `verify <revised paper> --slug <s> --revise`: run an author's revision of a paper under the same
 * slug, as its next VERSION (owner, 2026-11-10).
 *
 * The version that stands is frozen under `runs/<slug>/versions/v<n>/` — its source, its V1/V1.5
 * records, the report, the annotated paper and the bundle (corrected paper, `lean/`, the page
 * snapshot `page/page.json`), the state — so the owner can read the two versions side by side. The
 * run then takes the revised source in place and re-enters V1 (`--from-stage V1`), where the
 * transcription is re-pointed at it (`reanchor.ts`) rather than redone: what the revision left
 * unchanged keeps its verdicts, its repairs, its plan entry and its Lean. The Lean itself is never
 * copied or moved: `Papers/<Slug>/` is the paper's, revised in place by the F stages.
 */
import { existsSync } from "node:fs";
import { copyFile, cp, mkdir, readFile, rename, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import type { Core } from "../core/schema.js";
import { nodeFields } from "./reanchor.js";
import type { StateJson } from "../types.js";
import type { PatchFile } from "./patches.js";
import type { PrepareSource, VerifyState } from "./types.js";
import { VERIFY_FILES } from "./types.js";
import { hashSourceTree } from "./source_bundle.js";

/** Where version `n` of a run is frozen. */
export const versionDir = (runDir: string, n: number): string => path.join(runDir, "versions", `v${n}`);

/** What a frozen version keeps (run-relative; absent ones are skipped): what was read, what was
 * found, what was delivered. Not the logs, raw replies or promotion batches: they are the run's. */
export const VERSION_FROZEN: readonly string[] = [
  VERIFY_FILES.sourceDir,
  "discovery",
  "formalization",
  "annotated",
  "bundle",
  VERIFY_FILES.reportJson,
  VERIFY_FILES.reportMd,
  "graph.json",
  "review_basis.json",
  "nl_links.json",
  // the Lean Proof in English (F5, `formalization/lean_proof_english.ts` `LEAN_PROOF_ENGLISH_ARTIFACT`)
  "lean_proof_english.json",
  "state.json",
];

/** One frozen version, as `state.verify.versions` records it and `versions/v<n>/version.json` holds. */
export interface VersionRecord {
  version: number;
  /** The input the version was read from, as given on the command line. */
  input: string;
  main_file: string;
  source_sha256: string;
  /** Where the version stood when it was frozen, and the core V1.5 had accepted. */
  stage_completed: string;
  phase: string;
  core_sha256?: string | null;
  frozen_at: string;
  /** The version's source was edited in place before the revision (`freezeVersion`): its text is not on file, only
   *  its transcription and the parse it was cut from. */
  source_edited_in_place?: true;
}

/** The revision in progress (`state.verify.revision`): what V1's re-pointing found, for the report. */
export interface RevisionRecord {
  /** The version it revises. */
  from_version: number;
  started_at: string;
  /** A FIX IN PLACE (`startInPlaceFix`): the source edited in `runs/<slug>/source/` — a template or
   *  markup fix, not the authors' revision — re-pointed without a new version, against the snapshot
   *  under `versions/.inplace/`; `sha`: the source it was cut from. Closed (`closeInPlaceFix`) when V1
   *  accepts it, the record before it (`previous`) back in its place. */
  in_place?: { sha: string; previous: RevisionRecord | null };
  reanchor?: {
    same: number;
    changed: string[];
    broken: string[];
    renamed: Record<string, string>;
    /** True when the revision was read afresh (`cold_reason` says why). */
    cold: boolean;
    cold_reason?: string;
  };
  patches?: { kept: string[]; adopted: string[]; set_aside: string[] };
  /** The owner's readings on a node the revision changed: still binding, to be confirmed by the
   *  attached agent against the new wording. */
  rulings_to_recheck?: Array<{ id: string; node: string }>;
  /** Set while the revised source waits to take `source/`'s place (`completeSourceSwap`). */
  source_swap_pending?: boolean;
  /** Set when V1 accepted a transcription of the revision (re-pointed, or read afresh): the revision's
   *  reading is closed. */
  transcribed?: boolean;
  /** The revised source V1 re-pointed the transcription at (or set aside for a cold reading), saved
   *  as soon as it did: a V1 cut short before it (a kill, a segmenter halt) re-points again from the
   *  revision's starting point; one halted after it (its agent's rounds) resumes on the re-pointed
   *  transcription. */
  reanchored_sha?: string;
  /** What the re-pointing left for V1's agent beyond the core's own checks (a changed setup): handed
   *  to every V1 entry until V1 accepts the revision. */
  pending_violations?: string[];
  /** The revised source at which V1 halted once because the revision reads as far fewer results than
   *  the version before (`fewerResultsThanBefore`): an entry on it again goes on. */
  fewer_results_seen?: string;
  /** TRANSITION (with `core_graph.ts` scheme 5): each node's `tex_locator` before the revision, while
   *  the verdict cache is under scheme 5, whose bases read it — so a verdict on a node the revision
   *  only moved is carried. */
  lines_before?: Record<string, unknown>;
}

export interface RevisionSummary {
  frozen: VersionRecord;
  versionDir: string;
  /** The version the run now is. */
  version: number;
}

/** The revised source, prepared beside the run and checked before anything of the run changes. */
export interface PreparedRevision {
  input: string;
  mainFile: string;
  sha256: string;
}

/** Where the revised source waits until the version is frozen (`completeSourceSwap`). */
const REVISED_SOURCE = ".revise_source";

/**
 * VALIDATE, THEN MUTATE: prepare the revised source beside the run (`.revise_source`) and refuse,
 * changing nothing of the run, when it is the source as it stands, or when `versions/v<n>/` holds a
 * copy of ANOTHER source than the run's (not a `--revise` cut short: someone's directory, or a source
 * edited in place since) — move it aside and run `--revise` again. A copy of this version's own source
 * is the freeze of a `--revise` cut short: `freezeVersion` keeps or replaces it.
 */
export async function prepareRevision(args: { runDir: string; state: StateJson; input: string; mainHint?: string | null; prepareSource: PrepareSource }): Promise<PreparedRevision> {
  const verify = args.state.verify as VerifyState;
  if (verify.revision?.in_place && revisionOpen(verify)) throw new Error("--revise is refused, nothing changed: a fix of the source in place is being re-pointed (V1 has not accepted it yet) — finish it with --resume, then send the revision.");
  const n = verify.version ?? 1;
  const dest = versionDir(args.runDir, n);
  // A revision not yet transcribed is replaced in place (`startRevision`): nothing is frozen again.
  if (!revisionOpen(verify) && existsSync(dest) && (await frozenRecord(args.runDir, n))?.source_sha256 !== verify.source.sha256) {
    throw new Error(`--revise is refused, nothing changed: ${dest} already exists and is not a copy of this run's version ${n} (another source). Move that directory aside and run --revise again.`);
  }
  const tmp = path.join(args.runDir, REVISED_SOURCE);
  await rm(tmp, { recursive: true, force: true });
  const prepared = await args.prepareSource({ input: args.input, sourceDir: tmp, mainHint: args.mainHint ?? verify.source.main_file });
  const standing = [await hashSourceTree(path.join(args.runDir, VERIFY_FILES.sourceDir)), ...(revisionOpen(verify) ? [] : [verify.source.sha256])];
  if (standing.includes(prepared.sha256)) {
    await rm(tmp, { recursive: true, force: true });
    throw new Error(`--revise is refused, nothing changed: ${args.input} is the source of version ${n} as it stands.`);
  }
  return { input: args.input, mainFile: prepared.mainFile, sha256: prepared.sha256 };
}

/**
 * Freeze the standing version: copied aside and renamed into `versions/v<n>/` whole, the state left
 * as it is. The FIRST change `--revise` makes — before the re-entry voids anything — so the frozen
 * version is the one delivered. Null for a revision still open (not yet transcribed): it is replaced
 * in place, the version before it staying the one frozen.
 */
export async function freezeVersion(args: { runDir: string; state: StateJson; now?: () => Date }): Promise<VersionRecord | null> {
  const verify = args.state.verify as VerifyState;
  if (revisionOpen(verify)) return null;
  const n = verify.version ?? 1;
  // Frozen already by a `--revise` killed before it recorded the revision: that copy was taken before
  // anything was voided — the version as delivered — and is kept while the run has not moved on since
  // (the same cursor, accepted core and report); a copy of an earlier state of it is replaced.
  const dest = versionDir(args.runDir, n);
  const already = await frozenRecord(args.runDir, n);
  if (already && already.source_sha256 === verify.source.sha256) {
    if (await sameRunAsFrozen(args.runDir, already, args.state)) return already;
    await rm(dest, { recursive: true, force: true });
  }
  const frozen: VersionRecord = {
    version: n,
    input: verify.source.input,
    main_file: verify.source.main_file,
    source_sha256: verify.source.sha256,
    stage_completed: args.state.stage_completed,
    phase: verify.phase,
    core_sha256: verify.core_sha256,
    frozen_at: (args.now ?? (() => new Date()))().toISOString(),
  };
  const partial = path.join(args.runDir, "versions", `.v${n}.partial`);
  await rm(partial, { recursive: true, force: true });
  await mkdir(partial, { recursive: true });
  // A source edited in place since it was read is not the version's text: frozen without it.
  const sourceDir = path.join(args.runDir, VERIFY_FILES.sourceDir);
  if (existsSync(sourceDir) && (await hashSourceTree(sourceDir)) !== verify.source.sha256) frozen.source_edited_in_place = true;
  for (const rel of VERSION_FROZEN) {
    if (rel === VERIFY_FILES.sourceDir && frozen.source_edited_in_place) continue;
    const from = path.join(args.runDir, rel);
    if (existsSync(from)) await cp(from, path.join(partial, rel), { recursive: true });
  }
  await writeFile(path.join(partial, "version.json"), `${JSON.stringify(frozen, null, 2)}\n`, "utf8");
  await rename(partial, versionDir(args.runDir, n));
  return frozen;
}

/**
 * The revision's STARTING POINT, under `versions/v<n>/base/`: the run as the `--revise` re-entry left
 * it, before V1 re-points anything — its state (the paper-error ledger, the verdict caches), its patch
 * file (the re-entry voided the pending suggestions in it) and the owner's open review items. Every
 * re-pointing starts from it — a V1 cut short, and a revision replaced before V1 read it — so what the
 * re-pointing prunes is never pruned twice, and what the re-entry voided never comes back.
 */
export const REVISION_BASE_FILES: readonly string[] = ["state.json", VERIFY_FILES.patches, "orch_decisions.json", "owner_objections.json"];
export const revisionBaseDir = (runDir: string, n: number): string => path.join(versionDir(runDir, n), "base");

async function writeRevisionBase(runDir: string, n: number, state: StateJson): Promise<void> {
  await writeBase(versionDir(runDir, n), runDir, state);
}

/** The starting point under `<into>/base/` (`REVISION_BASE_FILES`). */
async function writeBase(into: string, runDir: string, state: StateJson): Promise<void> {
  const dir = path.join(into, "base");
  await rm(dir, { recursive: true, force: true });
  await mkdir(path.join(dir, "discovery"), { recursive: true });
  await writeFile(path.join(dir, "state.json"), `${JSON.stringify(state, null, 2)}\n`, "utf8");
  for (const rel of REVISION_BASE_FILES.slice(1)) {
    const from = path.join(runDir, rel);
    if (existsSync(from)) await copyFile(from, path.join(dir, rel));
  }
}

/** The verify state of a revision's starting point (`writeRevisionBase`), or null when none is on file. */
export async function readRevisionBaseState(runDir: string, n: number): Promise<VerifyState | null> {
  const f = path.join(revisionBaseDir(runDir, n), "state.json");
  return existsSync(f) ? ((JSON.parse(await readFile(f, "utf8")) as StateJson).verify ?? null) : null;
}

/**
 * Record the revision (with the frozen version, `freezeVersion`; null: an open revision replaced)
 * and put the revised source in its place, in an order a crash anywhere leaves recoverable: the
 * state is saved (`save`, with whatever the caller set beside it — the V1 re-entry) with a pending
 * source swap before the source is touched; the swap (`completeSourceSwap`) is finished by the next
 * entry if it was cut short. `source.sha256` stays the version's, so V1 sees the change.
 */
export async function startRevision(args: { runDir: string; state: StateJson; prepared: PreparedRevision; frozen: VersionRecord | null; save: () => Promise<void> }): Promise<RevisionSummary> {
  const verify = args.state.verify as VerifyState;
  verify.source = { ...verify.source, input: args.prepared.input, main_file: args.prepared.mainFile };
  let frozen: VersionRecord;
  if (args.frozen) {
    frozen = args.frozen;
    verify.versions = [...(verify.versions ?? []), frozen];
    verify.version = frozen.version + 1;
    verify.revision = { from_version: frozen.version, started_at: frozen.frozen_at, source_swap_pending: true };
    delete verify.fix_lines_before;
    await writeRevisionBase(args.runDir, frozen.version, args.state);
  } else {
    // An open revision REPLACED (a halt, a kill, a corrected revision sent meanwhile): read again
    // against the same frozen version, from the start.
    const r = verify.revision!;
    frozen = verify.versions!.find((v) => v.version === r.from_version)!;
    verify.revision = { from_version: r.from_version, started_at: r.started_at, source_swap_pending: true };
  }
  await args.save();
  await completeSourceSwap(args.runDir, verify);
  await args.save();
  return { frozen, versionDir: versionDir(args.runDir, frozen.version), version: verify.version ?? frozen.version + 1 };
}

/** Where a fix in place keeps what it is re-pointed from: the parse the transcription was cut from
 * (`discovery/`) and the run as the re-entry left it (`base/`, as a revision's). Not a version. */
export const inPlaceDir = (runDir: string): string => path.join(runDir, "versions", ".inplace");

/**
 * A source EDITED IN PLACE (`runs/<slug>/source/` no longer hashes as recorded — an operator's
 * template or markup fix, not the authors' revision; owner, 2026-11-21): its transcription is
 * re-pointed at it like a revision's, keeping every node, verdict, repair and ruling it can, but no
 * version is made — the version number, the frozen versions and the report's "Changes from version n"
 * stay as they were. What it is re-pointed from is kept under `versions/.inplace/` until V1 accepts it
 * (`closeInPlaceFix`). A revised source a `--revise` cut short left beside the run is removed (it would
 * take the edited one's place). Null when a revision is open.
 */
export async function startInPlaceFix(args: { runDir: string; state: StateJson; save: () => Promise<void> }): Promise<{ dir: string } | null> {
  const verify = args.state.verify as VerifyState;
  if (revisionOpen(verify)) return null;
  const dir = inPlaceDir(args.runDir);
  await rm(dir, { recursive: true, force: true });
  await mkdir(dir, { recursive: true });
  await cp(path.join(args.runDir, "discovery"), path.join(dir, "discovery"), { recursive: true });
  await rm(path.join(args.runDir, REVISED_SOURCE), { recursive: true, force: true });
  const previous = verify.revision ?? null;
  verify.revision = { from_version: verify.version ?? 1, started_at: new Date().toISOString(), in_place: { sha: verify.source.sha256, previous } };
  await writeBase(dir, args.runDir, args.state);
  await args.save();
  return { dir };
}

/** A fix in place V1 accepted: the record before it back in its place; the source it replaced kept
 * (`source.fixed_from`) and its scheme-5 lines (`fix_lines_before`). Its snapshot stays on disk until
 * the next fix replaces it (nothing reads it once closed). True when there was one; the caller saves. */
export function closeInPlaceFix(verify: VerifyState): boolean {
  const r = verify.revision;
  const fix = r?.in_place;
  if (!r || !fix) return false;
  verify.source.fixed_from = [...new Set([...(verify.source.fixed_from ?? []), fix.sha])];
  if (r.lines_before) verify.fix_lines_before = r.lines_before;
  else delete verify.fix_lines_before;
  if (fix.previous) verify.revision = fix.previous;
  else delete verify.revision;
  return true;
}

/**
 * Finish a revision's source swap (`startRevision`) when one is pending — at its own end, or at the
 * next entry of the run after a crash cut it short: the revised source takes `source/`'s place and the
 * version's own source (frozen under `versions/v<n>/`) is removed. True when it did anything; the
 * caller saves the state.
 */
export async function completeSourceSwap(runDir: string, verify: VerifyState | undefined): Promise<boolean> {
  if (!verify?.revision?.source_swap_pending) return false;
  const src = path.join(runDir, VERIFY_FILES.sourceDir);
  const revised = path.join(runDir, REVISED_SOURCE);
  // (the version's own source is frozen: it is removed, and a swap cut short is done again)
  if (existsSync(revised)) {
    await rm(src, { recursive: true, force: true });
    await rename(revised, src);
  }
  delete verify.revision.source_swap_pending;
  return true;
}

/** Whether the run stands where its frozen version (`version.json`) left it: the same cursor and
 * phase, the same accepted core, the same report on disk. */
async function sameRunAsFrozen(runDir: string, frozen: VersionRecord, state: StateJson): Promise<boolean> {
  const bytes = async (p: string): Promise<string | null> => (existsSync(p) ? readFile(p, "utf8") : null);
  return (
    frozen.stage_completed === state.stage_completed &&
    frozen.phase === state.verify?.phase &&
    (frozen.core_sha256 ?? null) === (state.verify?.core_sha256 ?? null) &&
    (await bytes(path.join(versionDir(runDir, frozen.version), VERIFY_FILES.reportJson))) === (await bytes(path.join(runDir, VERIFY_FILES.reportJson)))
  );
}

/** The record of frozen version `n` (`version.json`), or null. */
async function frozenRecord(runDir: string, n: number): Promise<VersionRecord | null> {
  const f = path.join(versionDir(runDir, n), "version.json");
  return existsSync(f) ? (JSON.parse(await readFile(f, "utf8")) as VersionRecord) : null;
}

/** A revision recorded and not yet transcribed by V1. */
export function revisionOpen(verify: Pick<VerifyState, "revision"> | undefined): boolean {
  return !!verify?.revision && verify.revision.transcribed !== true;
}

/** The log line of a revision's start. */
export function revisionLine(s: RevisionSummary): string {
  return `--revise: version ${s.frozen.version} frozen under ${s.versionDir} (stage ${s.frozen.stage_completed}); the revised source is version ${s.version} — V1 re-points the transcription at it`;
}

/**
 * Whether the revised text of `node` is what the version's repair made of it: every text field the
 * repair changed now reads as repaired (the author took the correction). Pure.
 */
export function adoptsRepair(node: string, transcribedBefore: Core, patchedBefore: Core, transcribedNow: Core): boolean {
  const t = nodeFields(transcribedBefore, node);
  const p = nodeFields(patchedBefore, node);
  const n = nodeFields(transcribedNow, node);
  if (!t || !p || !n) return false;
  const moved = (Object.keys(t) as Array<keyof typeof t>).filter((k) => t[k] !== p[k]);
  return moved.length > 0 && moved.every((k) => n[k] === p[k]);
}

/** A unit id re-pointed at a renamed environment (`<env>/…`). */
const unitTo = (unit: string | null | undefined, renamed: Readonly<Record<string, string>>): string | null | undefined => {
  if (!unit) return unit;
  const at = unit.indexOf("/");
  const env = at < 0 ? unit : unit.slice(0, at);
  return renamed[env] ? `${renamed[env]}${at < 0 ? "" : unit.slice(at)}` : unit;
};

/** What an op replaces, in the paper before and after the revision (`units.ts` `textOfRun`). */
export interface UnitTexts {
  before: (unit: string, to?: string | null) => string | null;
  after: (unit: string, to?: string | null) => string | null;
}

/**
 * The version's patch file read against the revision (`reanchor.ts` result). A repair stands when
 * its node is unchanged AND every unit it replaces reads as before (units are numbered within their
 * region: a sentence added elsewhere in the environment renumbers them) — re-pointed at a renamed
 * environment. One whose node now reads as repaired is ADOPTED by the author and retired; every other
 * is set aside — V1.5 grades the node as now printed, and the fixer repairs it again if it still needs
 * it. The owner's readings all stand; `rulings_to_recheck` names those on a changed or lost node. A
 * typo fix stands as a repair does, and is dropped otherwise. Pure.
 */
export function reconcilePatches(
  file: PatchFile,
  r: { same: readonly string[]; changed: readonly string[]; broken: readonly string[]; renamed: Readonly<Record<string, string>> },
  cores: { transcribedBefore: Core; patchedBefore: Core; transcribedNow: Core },
  units: UnitTexts,
  /** `adopt: false` (a fix in place: an operator's edit, not the authors'): no repair is retired as
   *  adopted — one on a node the edit changed is set aside, for V1.5 to grade as now printed. */
  opts: { adopt?: boolean } = {},
): { file: PatchFile; kept: string[]; adopted: string[]; set_aside: string[]; rulings_to_recheck: Array<{ id: string; node: string }> } {
  const moved = new Set([...r.changed, ...r.broken]);
  const kept: string[] = [];
  const adopted: string[] = [];
  const setAside: string[] = [];
  type Ops = { ops?: Array<{ unit: string; to?: string | null }> };
  const reOps = <T extends Ops>(x: T): T =>
    x.ops ? { ...x, ops: x.ops.map((o) => ({ ...o, unit: unitTo(o.unit, r.renamed)!, ...(o.to !== undefined ? { to: unitTo(o.to, r.renamed) } : {}) })) } : x;
  /** Every unit the repair replaces reads as before, where it now is. */
  const unitsStand = (x: Ops): boolean =>
    (x.ops ?? []).every((o) => ((a) => a !== null && a === units.after(unitTo(o.unit, r.renamed)!, unitTo(o.to, r.renamed)))(units.before(o.unit, o.to)));
  const stands = (node: string, x: Ops): boolean => !moved.has(node) && unitsStand(x);
  const patches = (file.patches ?? []).flatMap((p) => {
    if (stands(p.node, p)) {
      kept.push(p.node);
      return [reOps(p)];
    }
    if (opts.adopt !== false && moved.has(p.node) && adoptsRepair(p.node, cores.transcribedBefore, cores.patchedBefore, cores.transcribedNow)) adopted.push(p.node);
    else setAside.push(p.node);
    return [];
  });
  const unfixable = (file.unfixable ?? []).flatMap((u) => {
    const body = (u.suggested_repair ?? {}) as Ops;
    if (stands(u.node, body)) return [u.suggested_repair ? { ...u, suggested_repair: reOps(body) as typeof u.suggested_repair } : u];
    setAside.push(u.node);
    return [];
  });
  // A consequential repair follows the repairs it is a consequence of: set aside with them.
  const gone = (p: { consequence_of?: readonly string[] | null }): boolean => (p.consequence_of ?? []).some((n) => setAside.includes(n) || adopted.includes(n));
  for (let changed = true; changed; ) {
    changed = false;
    for (const p of patches) if (kept.includes(p.node) && gone(p as { consequence_of?: string[] })) (kept.splice(kept.indexOf(p.node), 1), setAside.push(p.node), (changed = true));
  }
  const keptPatches = patches.filter((p) => kept.includes(p.node));
  // A consequence held for the owner's ruling on a suggestion follows its node and its cause.
  const held = file.set_aside?.flatMap((p) => (stands(p.node, p) && !gone(p as { consequence_of?: string[] }) ? [reOps(p)] : (setAside.push(p.node), [])));
  const rulings = (file.owner_readings ?? []).filter((o) => moved.has(o.node)).map((o) => ({ id: o.id, node: o.node }));
  // A typo fix stands like a repair (its node unchanged, every unit it replaces reading as before);
  // any other is dropped, not set aside: the referee reads the node as now printed and lists its typos.
  const typoFixes = file.typo_fixes?.flatMap((t) => (stands(t.node, t) ? [{ ...reOps(t), typos: t.typos.map((x) => ({ ...x, unit: unitTo(x.unit, r.renamed) ?? null })) }] : []));
  return { file: { ...file, patches: keptPatches, unfixable, ...(held !== undefined ? { set_aside: held } : {}), ...(typoFixes !== undefined ? { typo_fixes: typoFixes } : {}) }, kept, adopted, set_aside: [...new Set(setAside)], rulings_to_recheck: rulings };
}

/** The report's account of a revision (`report.json` `revision`, the "Changes from version" section). */
export interface ReportRevision {
  version: number;
  from_version: number;
  /** Where the version before is kept, run-relative. */
  previous: string;
  /** True when the revision was read afresh, and why. */
  cold: boolean;
  cold_reason?: string;
  /** False while V1 has not read the revision (the counts below are then empty). */
  transcribed: boolean;
  unchanged: number;
  changed: string[];
  repointed: string[];
  repairs_adopted: string[];
  repairs_set_aside: string[];
  rulings_to_recheck: Array<{ id: string; node: string }>;
  /** Results whose outcome moved, by node: the bucket before → now (new results: before null). */
  outcomes: Array<{ node: string; before: string | null; now: string }>;
}

/**
 * The report's revision record, from the run's `revision` and the report of the version before
 * (`versions/v<n>/report.json`); null on a run that was never revised. Pure.
 */
export function reportRevision(verify: Pick<VerifyState, "version" | "revision">, rows: ReadonlyArray<{ node_id: string; bucket: string }>, previousRows: ReadonlyArray<{ node_id: string; bucket: string }> | null): ReportRevision | null {
  const r = verify.revision;
  if (!r) return null;
  const before = new Map((previousRows ?? []).map((x) => [x.node_id, x.bucket] as const));
  return {
    version: verify.version ?? r.from_version + 1,
    from_version: r.from_version,
    previous: path.join("versions", `v${r.from_version}`),
    cold: r.reanchor?.cold === true,
    ...(r.reanchor?.cold_reason ? { cold_reason: r.reanchor.cold_reason } : {}),
    transcribed: r.transcribed === true,
    unchanged: r.reanchor?.same ?? 0,
    changed: r.reanchor?.changed ?? [],
    repointed: r.reanchor?.broken ?? [],
    repairs_adopted: r.patches?.adopted ?? [],
    repairs_set_aside: r.patches?.set_aside ?? [],
    rulings_to_recheck: r.rulings_to_recheck ?? [],
    outcomes: rows.filter((x) => before.get(x.node_id) !== x.bucket).map((x) => ({ node: x.node_id, before: before.get(x.node_id) ?? null, now: x.bucket })),
  };
}

/** The report's "Changes from version n" section (empty when the run was never revised). */
export function renderRevision(rev: ReportRevision | null | undefined): string[] {
  if (!rev) return [];
  const list = (xs: readonly string[]): string => xs.map((x) => `\`${x}\``).join(", ");
  const L = [`## Changes from version ${rev.from_version}`, ""];
  L.push(`This is version ${rev.version} of the paper. Version ${rev.from_version} — its report, annotated paper and bundle (with its Lean) — is kept under \`${rev.previous}/\`.`, "");
  if (!rev.transcribed) L.push("The revision has not been read yet: this report is of the run before it.", "");
  else if (rev.cold) L.push(`The revision was read afresh: ${rev.cold_reason ?? "it changed too much of the paper to carry its reading over"}.`, "");
  else {
    L.push(`- results, hypotheses and definitions the revision left as they were: ${rev.unchanged} (their checks carried over, but where what they rely on around them changed)`);
    if (rev.changed.length > 0) L.push(`- changed by the revision, checked again: ${list(rev.changed)}`);
    if (rev.repointed.length > 0) L.push(`- moved or rewritten so that they had to be located again: ${list(rev.repointed)}`);
  }
  if (rev.repairs_adopted.length > 0) L.push(`- corrections of version ${rev.from_version} the revision adopts: ${list(rev.repairs_adopted)}`);
  if (rev.repairs_set_aside.length > 0) L.push(`- corrections of version ${rev.from_version} on results the revision changed otherwise (checked again as now printed): ${list(rev.repairs_set_aside)}`);
  if (rev.rulings_to_recheck.length > 0) L.push(`- the owner's readings kept on results the revision changed — confirm each still says what is meant: ${rev.rulings_to_recheck.map((x) => `\`${x.id}\` (${x.node})`).join(", ")}`);
  if (rev.outcomes.length > 0) {
    L.push("", "| result | version " + rev.from_version + " | version " + rev.version + " |", "| --- | --- | --- |");
    for (const o of rev.outcomes) L.push(`| \`${o.node}\` | ${o.before ?? "(new)"} | ${o.now} |`);
  } else L.push(`- every result's outcome is as in version ${rev.from_version}`);
  L.push("");
  return L;
}
