// What the UI shows about verify runs, read from their records under `<toolkit>/runs/<slug>/`.
// Every read goes through fscache: a file is parsed again only when it changed.
import { closeSync, existsSync, mkdirSync, openSync, readdirSync, readFileSync, readSync, statSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import os from "node:os";
import path from "node:path";
import type { ToolkitConfig } from "../toolkit/config.js";
import { pendingDecisions } from "../verify/annotate_run.js";
import { isProofOp, isStatementOp, type PatchOp } from "../verify/ops.js";
import { isWithdrawn } from "../verify/patches.js";
import { gradesRepair } from "../verify/weakening.js";
import { splitKinds, type SplitKind } from "../verify/core_graph.js";
import type { LoosePatchFile, PendingDecisions } from "../verify/annotated_paper.js";
import type { V15NodeVerdict, VerifyState } from "../verify/types.js";
import { newTopics, parseChecklist, recommendationKeys, topicKey, type ChecklistDecision } from "../proposals/checklist.js";
import type { ProposalBatch } from "../proposals/schema.js";
import { declSource, displayWhole, flatLeanRows, partAlone } from "../formalization/nl_links.js";
import { leanStatementView, squash, viewRows } from "../formalization/lean_rows.js";
import { leanNameLeaf } from "../presentation/lean_decl_name.js";
import { applyLinks, eachRow, leanDefs, linksRefusal, type PageDef, type PageSegment, type PageView } from "./lean_view.js";
import { deriveRead, readCached, readJsonCached, signature } from "./fscache.js";
import { applyPidLine, heartbeatAgeMs, heartbeatLiveness, livenessOf } from "../shared/run_heartbeat.js";
import { readShare, shareableOf, shareRecordView, type Shareable, type ShareView } from "../verify/share_record.js";
import { frontMatter, labelAnchor, nodeAnchor, readPreamble, resolveDigitIfs, stripComments } from "./tex_html.js";

export const STAGES: ReadonlyArray<{ id: string; label: string }> = [
  { id: "V1", label: "Typed core" }, { id: "V1.5", label: "Referee" },
  { id: "1", label: "F1 Lean plan" }, { id: "1.5", label: "F1.5 Plan audit" },
  { id: "2", label: "F2 Lean scaffold" }, { id: "2.5", label: "F2.5 Faithfulness review" },
  { id: "3", label: "F3 Lean proofs" }, { id: "3.5", label: "F3.5 Mechanical review" },
  { id: "4", label: "F4 Final review" }, { id: "5", label: "F5 Docstrings" },
  { id: "V6", label: "Report" },
];

/**
 * "agent": halted, and the attached agent session decides (every halt is the agent's; it records each
 * ruling it makes for the owner's review). "needs-you": a promotion round, the agent's question, a
 * decision to review, or a halt with no agent attached. "superseded": a later run verifies the same
 * paper (same source hash); this one is history.
 */
export type RunStatus = "running" | "needs-you" | "agent" | "done" | "idle" | "superseded";

export interface RunEvent { at: string; stage: string; status: string; message: string; guidance?: string }

export interface RunSummary {
  slug: string;
  title: string;
  authors: string;
  stage: string;
  stageIndex: number;
  phase: string;
  live: boolean;
  status: RunStatus;
  headline: string;
  lastEvent: RunEvent | null;
  pending: { weakening: number; rewind: boolean; cap: boolean; promotion: "A" | "B" | null; checkpoint: boolean };
  /** The owner sent a suggested repair back: the proposal the paper still shows is discarded, its
   *  replacement being written. */
  redoing: boolean;
  /** Nothing is asked of the owner but a resume (a run that ended without a halt, a receipt still
   *  being confirmed, a round not prepared): the page offers it, or how to attach an agent. */
  toResume?: boolean;
  verdict: string | null;
  buckets: Record<string, number> | null;
  updatedAt: number;
  /** The later run of the same paper, when this one was redone. */
  supersededBy: string | null;
  /** The interactive agent session attached to the run (`tools/scripts/orch.mjs watch`), while it
   *  lives; `watching`: its watcher is armed now (what the owner writes reaches it within a tick);
   *  `starts`: it starts what the page asks itself (a batch job's orchestrator, `orch.mjs watch --starts`). */
  orch: { agent: string; since: string; watching: boolean; starts: boolean } | null;
  /** The run is in full auto (`verify --full-auto`): the owner's decisions take the agent's
   *  recommendations, listed in `reviews` once carried out. */
  fullAuto: boolean;
  /** What that agent asks the owner (answered on the page, or in the session). */
  requests: OrchRequest[];
  /** The agent's messages on the page the owner has not seen yet (`OrchMessage`). */
  unread: number;
  /** Rulings the agent made at halts, awaiting the owner's review. */
  reviews: OrchDecision[];
  /** The run's model calls and tokens so far (token_usage.jsonl), when it has any. */
  tokens: TokenTotals | null;
  /** The run's last share on the public site, less its token (`share.json`), when it was shared. */
  share: ShareView | null;
  /** A finished run: whether its bundle can be shared, and why not (`shareableOf`); null otherwise. */
  shareable: Shareable | null;
}

/** Sums of a run's token ledger; `uncounted`: calls whose usage could not be read. */
export interface TokenTotals { calls: number; uncounted: number; input: number; cached: number; output: number; total: number }

async function tokenTotals(dir: string): Promise<TokenTotals | null> {
  const text = await readCached(path.join(dir, "token_usage.jsonl"));
  if (!text) return null;
  const t: TokenTotals = { calls: 0, uncounted: 0, input: 0, cached: 0, output: 0, total: 0 };
  for (const line of text.split("\n")) {
    if (!line.trim()) continue;
    let u: { input_tokens?: number; cached_input_tokens?: number; output_tokens?: number; total_tokens?: number } | null;
    try { u = (JSON.parse(line) as { usage?: typeof u }).usage ?? null; } catch { continue; }
    t.calls++;
    if (!u) { t.uncounted++; continue; }
    t.input += u.input_tokens ?? 0; t.cached += u.cached_input_tokens ?? 0; t.output += u.output_tokens ?? 0;
    t.total += u.total_tokens ?? (u.input_tokens ?? 0) + (u.output_tokens ?? 0);
  }
  return t.calls ? t : null;
}

export interface OrchRequest { id: string; at: string; text: string }
/** A ruling the agent made at a halt (`orch.mjs decided`), and the owner's review of it. */
export interface OrchDecision { id: string; node: string; at: string; text: string; review?: { verdict: "approve" | "reject"; guidance?: string; at: string; handled?: boolean } }
export const DECISIONS_FILE = "orch_decisions.json";
/** What the owner asked the page to start (a resume, a ruling, the apply of a round) while the attached
 *  session starts runs itself: `{ argv, command, kind, round?, at }`; that session's watcher reports it,
 *  and the session starts it and removes the file. */
export const START_REQUEST_FILE = "start_request.json";
/** An issue the owner reports on a margin comment that asks no decision of them (a finding, a repair or
 *  a clarification they find wrong): optional. `comment`: the note's key (`PaperComment.key`). The
 *  agent's watcher wakes on one not `handled`, and the agent acts on it (`orch.mjs handled`). */
export interface OwnerObjection { id: string; comment: string; node: string | null; kind: string; excerpt: string; text: string; at: string; handled?: boolean }
export const OBJECTIONS_FILE = "owner_objections.json";
/** A file the owner attached to a message: data for the agent, kept under the run (`path`, from its directory). */
export interface MessageFile { name: string; bytes: number; sha256: string; path: string }
/** A message of the page's conversation between the owner and the agent: the owner's, written on the
 *  page (the agent's watcher wakes on one not `handled`; it changes nothing in the run by itself),
 *  or the agent's (`orch.mjs reply`). `re`: the message, or the request (`q<n>`), it answers;
 *  `seen`: the owner has read the agent's. */
export interface OrchMessage { id: string; from: "user" | "agent"; text: string; at: string; re?: string; files?: MessageFile[]; handled?: boolean; seen?: boolean }
export const MESSAGES_FILE = "orch_messages.json";
/** A message as the page draws it: the agent's `text` is TeX, the owner's `words` are plain text. */
export interface ThreadEntry { id: string; from: "user" | "agent"; at: string; re?: string; text?: string; words?: string; files?: Array<{ name: string; bytes: number }>; waiting?: true; unseen?: true }
/** (a store that is not a list shows no message: a send says why, `scripts/messages_store.mjs`) */
export const messagesOf = async (dir: string): Promise<OrchMessage[]> => { const all = await readJsonCached<OrchMessage[]>(path.join(dir, MESSAGES_FILE)).catch(() => null); return (Array.isArray(all) ? all : []).filter((m) => m && m.id && (m.from === "user" || m.from === "agent")); };

interface StateFile {
  stage_completed?: string;
  lean_subdir?: string;
  full_auto?: boolean;
  verify?: VerifyState & { phase?: string; source?: { input?: string; main_file?: string; sha256?: string } };
}

export const runsDir = (cfg: ToolkitConfig): string => path.join(cfg.toolkitRoot, "runs");
export const runDir = (cfg: ToolkitConfig, slug: string): string => path.join(runsDir(cfg), slug);

/** A run's slug is a directory name: letters, digits, `_`, `-`, `.` — never a path. */
export function validSlug(slug: string): boolean {
  return /^[A-Za-z0-9][A-Za-z0-9_.-]{0,120}$/.test(slug) && !slug.includes("..");
}

/** Verify runs: directories with a state.json holding a `verify` record (study and `_` runs left out). */
export function listRunSlugs(cfg: ToolkitConfig): string[] {
  const dir = runsDir(cfg);
  if (!existsSync(dir)) return [];
  return readdirSync(dir, { withFileTypes: true })
    .filter((d) => d.isDirectory() && !d.name.startsWith("_") && !d.name.startsWith("study_") && validSlug(d.name))
    .map((d) => d.name)
    .filter((s) => existsSync(path.join(dir, s, "state.json")))
    .sort();
}

/** The last `bytes` of a file (whole lines only). */
function tail(file: string, bytes = 65536): string {
  try {
    const size = statSync(file).size;
    const start = Math.max(0, size - bytes);
    const fd = openSync(file, "r");
    try {
      const buf = Buffer.alloc(size - start);
      readSync(fd, buf, 0, buf.length, start);
      const text = buf.toString("utf8");
      return start > 0 ? text.slice(text.indexOf("\n") + 1) : text;
    } finally {
      closeSync(fd);
    }
  } catch {
    return "";
  }
}

const eventCache = new Map<string, { sig: string; events: RunEvent[] }>();

/** The run's recent pipeline events (newest last), from the tail of pipeline.jsonl. */
export function recentEvents(cfg: ToolkitConfig, slug: string): RunEvent[] {
  const file = path.join(runDir(cfg, slug), "pipeline.jsonl");
  const sig = signature(file);
  const hit = eventCache.get(file);
  if (hit && hit.sig === sig) return hit.events;
  const events: RunEvent[] = [];
  for (const line of tail(file).split("\n")) {
    if (!line.trim()) continue;
    try {
      const e = JSON.parse(line) as { timestamp?: string; stage?: string; status?: string; message?: string; next_step_guidance?: string };
      events.push({ at: e.timestamp ?? "", stage: String(e.stage ?? ""), status: e.status ?? "", message: e.message ?? "", ...(e.next_step_guidance ? { guidance: e.next_step_guidance } : {}) });
    } catch {
      // a line being written
    }
  }
  eventCache.set(file, { sig, events });
  return events;
}

/** The apply of a promotion round: `live` while its process runs (`proposals/apply_<R>.pid`),
 *  `stopped` when it began (the decisions of the batch on file are recorded, or a move is half-way)
 *  and did not finish, else null. A decisions file older than the batch is an earlier round's
 *  (the run was rewound and the round proposed again): no apply of this one. */
export function applyOf(dir: string, round: "A" | "B"): "live" | "stopped" | null {
  // (the runner's rule: its pid on this machine, the file's freshness on another of the mount)
  if (heartbeatLiveness(path.join(dir, "proposals", `apply_${round}.pid`)).live) return "live";
  if (existsSync(path.join(dir, "proposals", "move_pending.json"))) return "stopped";
  return roundDecided(dir, round) ? "stopped" : null;
}

/** The fields of a proposals file that the round checks read, parsed once per change of the file:
 *  a batch can be tens of MB, and the watcher asks for every run every second. */
const proposalFields = new Map<string, { sig: string; value: Record<string, unknown> | null }>();
const proposalsJson = (dir: string, file: string): Record<string, unknown> | null => {
  const f = path.join(dir, "proposals", file);
  const sig = signature(f);
  const hit = proposalFields.get(f);
  if (hit && hit.sig === sig) return hit.value;
  let value: Record<string, unknown> | null = null;
  if (sig !== "-") {
    try {
      const j = JSON.parse(readFileSync(f, "utf8")) as Record<string, unknown> | null;
      if (j && typeof j === "object") value = { decided_at: j.decided_at, created: j.created, round: j.round, message: j.message, at: j.at };
    } catch {
      // being written (or removed under the read): not remembered, so the next pass reads it again
      return null;
    }
  }
  proposalFields.set(f, { sig, value });
  return value;
};

/** Whether the decisions on file are of the batch on file (`applyOf`). */
function roundDecided(dir: string, round: "A" | "B"): boolean {
  const decisions = proposalsJson(dir, `${round}.decisions.json`);
  if (!decisions) return false;
  return !(Date.parse(String(decisions.decided_at ?? "")) < Date.parse(String(proposalsJson(dir, `${round}.json`)?.created ?? "")));
}

/** Why the last apply of `round` ended without applying it (`proposals/apply_failed.json`, written
 *  by `propose --apply`): shown to the owner, whose decisions it usually concerns. Null once an
 *  apply completes, and for a failure older than the batch on file. */
function applyRefusal(dir: string, round: "A" | "B"): string | null {
  const f = proposalsJson(dir, "apply_failed.json");
  if (!f || (f.round != null && f.round !== round) || !f.message) return null;
  return Date.parse(String(f.at ?? "")) < Date.parse(String(proposalsJson(dir, `${round}.json`)?.created ?? "")) ? null : String(f.message);
}

/** Record that the UI started the apply of a promotion round as process `pid`: the page reads
 *  "applying" at once. The apply writes its own pid over it and removes the file when it ends. */
export function markApplying(cfg: ToolkitConfig, slug: string, round: "A" | "B", pid: number): void {
  const file = path.join(runDir(cfg, slug), "proposals", `apply_${round}.pid`);
  mkdirSync(path.dirname(file), { recursive: true });
  writeFileSync(file, applyPidLine(pid));
}

/**
 * The index in `STAGES` of the stage before the one in progress (-1: none). The run's PHASE says
 * which part it is in. Within the Lean stages the loop moves both ways (a review sends the scaffold
 * back, a core revision the plan) without the completed stage following: the latest event's stage is
 * the one in progress — done, when the event completes it — and the state's completed stage stands
 * only while the log ends outside them. A run sent back to V1 or V1.5 is there, whatever its log
 * still ends with.
 */
export function stageIndexOf(phase: string, completed: string, lastEventStage: string | null, lastEventStatus: string | null = null): number {
  const at = (id: string): number => STAGES.findIndex((s) => s.id === id);
  if (phase === "init") return -1;
  if (phase === "v1") return at("V1");
  if (phase === "v1_5") return at("V1.5");
  if (phase === "v6" || phase === "proposals_B") return at("5");
  if (phase === "done" || phase === "failed") return STAGES.length - 1;
  const lean = lastEventStage !== null && /^\d/.test(lastEventStage) ? at(lastEventStage) : -1;
  if (lean >= 0) return lastEventStatus === "completed" ? lean : lean - 1;
  return Math.max(at("V1.5"), at(completed));
}

/** Written by the UI when it starts a run: `<pid> <ISO time>`. A runner takes a while to come up
 *  and write its heartbeat; until then this is what says the run is on its way. */
export const STARTED_FILE = "logs/.ui.started";
const STARTING_MAX_MS = 10 * 60_000;

function alive(pid: number | undefined): boolean {
  if (pid === undefined || !Number.isFinite(pid) || pid <= 0) return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch (err) {
    // EPERM: alive but another user's process
    return (err as NodeJS.ErrnoException).code === "EPERM";
  }
}

/** Record that the UI started the run's runner as process `pid`. */
export function markStarted(cfg: ToolkitConfig, slug: string, pid: number): void {
  const file = path.join(runDir(cfg, slug), ...STARTED_FILE.split("/"));
  mkdirSync(path.dirname(file), { recursive: true });
  writeFileSync(file, `${pid} ${new Date().toISOString()}\n`);
}

/**
 * Whether the run's runner is alive — everything the UI shows of that is this. Its heartbeat decides
 * (`heartbeatLiveness`: the pid on this host, the file's freshness for a runner on another machine
 * of the mount, `elsewhere`, whose pid is not ours to signal) — or, `starting`, the UI launched it
 * within the last minutes and that process lives, the heartbeat still to come.
 */
export function runLive(cfg: ToolkitConfig, slug: string): { live: boolean; pid: number | null; elsewhere?: string; starting?: true; since?: string; left?: true } {
  const dir = runDir(cfg, slug);
  try {
    const hb = heartbeatLiveness(path.join(dir, "logs", ".run.active"));
    if (hb.live) return { live: true, pid: hb.pid, since: hb.since, ...(hb.elsewhere ? { elsewhere: hb.elsewhere } : {}) };
    const [pid, at] = (readCachedSync(path.join(dir, ...STARTED_FILE.split("/"))) ?? "").trim().split(/\s+/);
    if (Date.now() - Date.parse(at ?? "") < STARTING_MAX_MS && alive(Number(pid))) return { live: true, pid: Number(pid), starting: true };
    // `left`: a heartbeat on file whose owner is gone — a runner removes its own when it halts,
    // stops or finishes, so this one was killed or crashed, in whatever stage it was.
    return { live: false, pid: hb.pid, ...(hb.why !== "no-heartbeat" ? { left: true as const } : {}) };
  } catch {
    return { live: false, pid: null };
  }
}

/**
 * What decides a run's status and no file change announces: whether its runner, its agent session
 * and the apply of a promotion round live. The watcher pushes when this changes.
 */
export function runPulse(cfg: ToolkitConfig, slug: string): { key: string; atWork: boolean } {
  const dir = runDir(cfg, slug);
  const { live, starting, since } = runLive(cfg, slug);
  let orch: OrchFile | null = null;
  try { orch = JSON.parse(readCachedSync(path.join(dir, "orch.json")) ?? "null") as OrchFile | null; } catch { /* being written */ }
  const applies = [applyOf(dir, "A"), applyOf(dir, "B")];
  return { key: [live ? (starting ? "starting" : `live since ${since}`) : "", orchAlive(orch, path.join(dir, "orch.json")) ? (watcherArmed(orch!, path.join(dir, "orch.json")) ? "orch watching" : "orch") : "", ...applies].join("|"), atWork: live || applies.includes("live") };
}

/** A small file's text (null when absent), re-read only when its size or mtime changed: the
 *  watcher's pass reads these for every run every second. */
const syncTexts = new Map<string, { sig: string; text: string | null }>();
function readCachedSync(file: string): string | null {
  const sig = signature(file);
  const hit = syncTexts.get(file);
  if (hit && hit.sig === sig) return hit.text;
  let text: string | null = null;
  try {
    if (sig !== "-") text = readFileSync(file, "utf8");
  } catch {
    return null;
  }
  syncTexts.set(file, { sig, text });
  return text;
}

async function readState(cfg: ToolkitConfig, slug: string): Promise<StateFile | null> {
  return readJsonCached<StateFile>(path.join(runDir(cfg, slug), "state.json"));
}

async function readPatches(cfg: ToolkitConfig, slug: string): Promise<LoosePatchFile | null> {
  return readJsonCached<LoosePatchFile>(path.join(runDir(cfg, slug), "discovery", "patches.json"));
}

/** The paper's main TeX file name (state, else envs.json). */
async function mainFile(cfg: ToolkitConfig, slug: string, state: StateFile | null): Promise<string | null> {
  const m = state?.verify?.source?.main_file;
  if (m) return m;
  const envs = await readJsonCached<{ main_file?: string }>(path.join(runDir(cfg, slug), "discovery", "envs.json"));
  return envs?.main_file ?? null;
}

async function titleOf(cfg: ToolkitConfig, slug: string, state: StateFile | null): Promise<{ title: string; authors: string }> {
  const main = await mainFile(cfg, slug, state);
  // (the flattened paper when it is on file: a title set in a file the main one \input's is in it)
  const text =
    (await readCached(path.join(runDir(cfg, slug), "discovery", "flat.tex"))) ??
    (main ? await readCached(path.join(runDir(cfg, slug), "source", main)) : null);
  if (!text) return { title: slug, authors: "" };
  const plainText = stripComments(text);
  const fm = frontMatter(resolveDigitIfs(plainText, readPreamble(plainText).textMacros));
  const plain = (t: string) => t.replace(/\\(?:thanks|footnote)\s*\{(?:[^{}]|\{[^{}]*\})*\}/g, "").replace(/\\\\/g, " ")
    .replace(/\\&/g, "&").replace(/~/g, " ").replace(/\\[A-Za-z]+\*?/g, " ").replace(/[{}$]/g, "").replace(/\s+/g, " ").trim();
  return { title: plain(fm.title) || slug, authors: plain(fm.authors) };
}

/** The promotion round waiting on the owner (phase proposals_A / proposals_B), if any. */
function promotionRound(state: StateFile | null): "A" | "B" | null {
  const phase = state?.verify?.phase ?? "";
  return phase === "proposals_A" ? "A" : phase === "proposals_B" ? "B" : null;
}

/** The round whose batch on file is the one in front of the owner: the run's state holds a record of
 *  the round. Without one — a run sent back, then stopped before the round is proposed again — the
 *  batch on file is an earlier state's, shown as history, never as the round to decide. */
function roundProposed(state: StateFile | null): "A" | "B" | null {
  const round = promotionRound(state);
  return round && (round === "A" ? state?.verify?.promotion_a : state?.verify?.promotion) ? round : null;
}

/** The TeX `text` cut to `n` characters, never inside a formula: a `$…$` the cut would split is left out. Pure. */
export function texCut(text: string, n: number): string {
  if (text.length <= n) return text;
  const cut = text.slice(0, n), open = (cut.match(/(?<!\\)\$/g) ?? []).length % 2 === 1;
  return `${(open ? cut.slice(0, cut.lastIndexOf("$")) : cut).trimEnd()}…`;
}
function headlineOf(ev: RunEvent | null): string {
  if (!ev) return "";
  return ev.message.split("\n")[0]!.replace(/\s+/g, " ")
    .replace(/(?:\/[^\s/\],]+){2,}\/([^\s/\],]+)/g, "$1") // a path: its file name
    .slice(0, 200);
}

/** What a live run is doing, from its last event: "F3 proof filler — working" (no prompt sizes or paths). */
export function liveHeadline(ev: RunEvent | null): string {
  if (!ev) return "starting";
  const name = stageName(ev.stage);
  const m = headlineOf(ev)
    .replace(/:\s*prompt \d+ bytes from \[.*$/, " — working")
    .replace(/:\s*stdout \d+ bytes\s*$/, " — done")
    .replace(/batch\[([^\]]*)\]/, (_, l: string) => `${l.split(",").length} results`);
  return /^[FV]\d/.test(m) ? m : `${name} · ${m}`; // a message that names its stage keeps it alone
}

/** A process's start time (Linux; null elsewhere), so a reused PID is not taken for the session. */
function startedAt(pid: number): string | null {
  try { return readFileSync(`/proc/${pid}/stat`, "utf8").split(") ")[1]!.split(" ")[19] ?? null; } catch { return null; }
}

interface OrchFile { agent?: string; pid?: number; started?: string | null; host?: string | null; attached_at?: string; watcher?: number; starts?: boolean }
/** The watcher `orch.json` names is armed: its process on this machine; on another machine of the
 *  mount, the file it touches every minute is fresh. */
const WATCHER_STALE_MS = 3 * 60_000;
const watcherArmed = (o: OrchFile, file: string): boolean => Boolean(o.watcher) && (o.host && o.host !== os.hostname() ? Date.now() - mtime(file) < WATCHER_STALE_MS : alive(o.watcher));

/** Whether the session `orch.json` names lives, by the heartbeat's rule (`livenessOf`): on this
 *  machine its pid, started when the session did; on another machine of the mount, where a pid
 *  means nothing, the file's freshness — the armed watcher touches it every minute, and a session
 *  between two watches has the heartbeat's allowance for a file that records no beat. */
function orchAlive(o: OrchFile | null, file: string): boolean {
  if (!o?.pid) return false;
  const hb = { pid: o.pid, timestamp: o.attached_at ?? "", ownerToken: "", host: o.host ?? null, beatMs: null, start: o.started ?? null, mtimeMs: mtime(file), path: file };
  return livenessOf(hb, heartbeatAgeMs(file, hb.mtimeMs), { host: os.hostname(), alive, start: startedAt }).live;
}

/** The agent session attached to a run (orch.json, written by `orch.mjs watch`), when it still lives. */
export async function orchOf(cfg: ToolkitConfig, slug: string): Promise<{ agent: string; since: string; watching: boolean; starts: boolean } | null> {
  const file = path.join(runDir(cfg, slug), "orch.json");
  const o = await readJsonCached<OrchFile>(file);
  return o && orchAlive(o, file) ? { agent: o.agent ?? "agent", since: o.attached_at ?? "", watching: watcherArmed(o, file), starts: o.starts === true } : null;
}

const updatedOf = (cfg: ToolkitConfig, slug: string): number =>
  Math.max(mtime(path.join(runDir(cfg, slug), "pipeline.jsonl")), mtime(path.join(runDir(cfg, slug), "state.json")));

/** The most recently updated other run of the same paper (same source hash), when it is newer than this one. */
async function newerRunOf(cfg: ToolkitConfig, slug: string, sha: string | undefined, updatedAt: number): Promise<string | null> {
  if (!sha) return null;
  let best: { slug: string; at: number } | null = null;
  for (const other of listRunSlugs(cfg)) {
    if (other === slug || (await readState(cfg, other))?.verify?.source?.sha256 !== sha) continue;
    const at = updatedOf(cfg, other);
    if (at > updatedAt && (!best || at > best.at)) best = { slug: other, at };
  }
  return best?.slug ?? null;
}

/** The status of a log line a runner writes while a stage is at work (or as it dies): never the
 *  last line of a run that halted, stopped after a stage or finished. */
const ENDED_AT_WORK = /^(dispatch|dispatch-complete|failed|rewound)$/;

export async function runSummary(cfg: ToolkitConfig, slug: string): Promise<RunSummary> {
  const dir = runDir(cfg, slug);
  const state = await readState(cfg, slug);
  const { title, authors } = await titleOf(cfg, slug, state);
  const events = recentEvents(cfg, slug);
  const { live, starting, since, left } = runLive(cfg, slug);
  const stage = state?.stage_completed ?? "init";
  const phase = state?.verify?.phase ?? "";
  // A live runner that has logged nothing since it started is not where the log ends: a run sent
  // back to repair a statement is in V1 again, whatever stage its last halt was at.
  const fresh = events.at(-1) ?? null;
  const back = live && fresh !== null && since !== undefined && Date.parse(fresh.at) < Date.parse(since);
  const last = back ? null : fresh;
  const repairing = back && (phase === "init" || phase === "v1");
  // The Lean stages loop (scaffold → review → fill → review) without re-recording the completed stage,
  // so the last finished stage is the one before the last event's when that is further along.
  const stageIndex = repairing ? -1 : stageIndexOf(phase, stage, last?.stage ?? null, last?.status ?? null);
  const verify = state?.verify;
  const pd = verify ? pendingDecisions(verify, await readPatches(cfg, slug)) : null;
  // a round is in front of the owner once its checklist exists; before that the round is still to run
  const promotionPhase = promotionRound(state);
  const promotion = roundProposed(state) && existsSync(path.join(dir, "proposals", `${promotionPhase}.json`)) ? promotionPhase : null;
  // (`failed`: a run that ended in its report without Lean — a refutation at V1.5 — is done too)
  const done = stage === "V6" || phase === "done" || phase === "failed";
  // (a report on file from before the run was sent back describes another state of it)
  const report = reportCurrent(state) ? await readJsonCached<{ verdict?: string; paper_grade?: { grade?: string }; summary?: Record<string, number> }>(path.join(dir, "report.json")) : null;
  const halted = !live && last !== null && (last.status === "checkpoint" || last.status === "blocked");
  // A receipt the confirming V1.5 pass has not settled is not the owner's yet: the runner refuses a ruling on it.
  const rcp = renderCheckpointOf(verify);
  const confirming = pd?.confirming ? pd.weakening.length : 0;
  const pending = { weakening: confirming || rcp ? 0 : pd?.weakening.length ?? 0, rewind: Boolean(pd?.rewind), cap: Boolean(pd?.cap), promotion, checkpoint: halted };
  const updatedAt = updatedOf(cfg, slug);
  const supersededBy = live ? null : await newerRunOf(cfg, slug, verify?.source?.sha256, updatedAt);
  const orch = await orchOf(cfg, slug);
  const requests = ((await readJsonCached<OrchRequest[]>(path.join(dir, "orch_requests.json"))) ?? []).filter((r) => r && r.text);
  const reviews = ((await readJsonCached<OrchDecision[]>(path.join(dir, DECISIONS_FILE))) ?? []).filter((d) => d && d.text && !d.review);
  const unread = (await messagesOf(dir)).filter((m) => m.from === "agent" && !m.seen).length;
  const decision = pending.weakening ? `${pending.weakening} repair(s) would weaken a main result` : pending.cap ? "repairs did not settle within the cap" : pending.rewind ? "a Lean stage proposes a correction to the paper" : null;
  const halt = decision ?? (halted ? `halted at ${stageName(last!.stage)}: ${headlineOf(last)}` : null);
  // full auto: the owner's decisions are the attached agent's, carried out as it recommends
  const fullAuto = state?.full_auto === true;
  const delegated = fullAuto && orch !== null;
  let status: RunStatus = "idle";
  let headline = "";
  let toResume = false;
  // a superseded run is history — unless its agent still asks something or a ruling awaits review
  if (supersededBy && !requests.length && !reviews.length) { status = "superseded"; headline = `superseded by ${supersededBy}, a later run of the same paper`; }
  else if (requests.length && !live) { status = "needs-you"; headline = `the agent asks you: ${texCut(requests[0]!.text, 160)}`; }
  else if (live) { status = "running"; headline = starting ? "starting — taking up what you sent" : repairing ? "V1 · repairing the statements sent back" : back ? `${STAGES[stageIndex + 1]?.label ?? "working"} · working` : liveHeadline(last); }
  // the owner has decided the round and it is being applied (or stopped part-way: the agent's)
  else if (promotion && applyOf(dir, promotion) === "live") { status = "running"; headline = `applying promotion round ${promotion}: the accepted results are entering your toolkit`; }
  // (the state records the round applied: what is left is the resume that follows an apply — it died before its heartbeat)
  else if (promotion && (promotion === "A" ? verify?.promotion_a : verify?.promotion)?.status === "applied") { status = orch ? "agent" : "needs-you"; toResume = true; headline = `promotion round ${promotion} is applied — ${orch ? "the agent resumes the run" : "resume the run"}`; }
  else if (promotion && applyOf(dir, promotion) === "stopped") { status = orch ? "agent" : "needs-you"; headline = `promotion round ${promotion} is applied in part — ${orch ? "the agent settles the rest" : "no agent attached"}`; }
  // a render / contract checkpoint comes before every ruling: the agent's (a tool defect), nothing to decide
  else if (rcp) { status = orch ? "agent" : "needs-you"; toResume = true; headline = `${rcp.kind} checkpoint: ${rcp.blocks} block(s) of the annotated paper ${rcp.kind === "contract" ? "still do not compile after their model wrote them again" : "could not be set as TeX"} — a tool defect, ${orch ? "the agent settles it" : "no agent attached"}; no decision of yours is read until it is cleared`; }
  // a repair that weakens a main result is the owner's to decide, on the page
  else if (pending.weakening) { status = delegated ? "agent" : "needs-you"; headline = `${decision} — ${delegated ? "full auto: the agent decides each, for your review after" : "decide each (accept, decline, or redo with guidance)"}`; }
  else if (decision) { status = orch ? "agent" : "needs-you"; headline = `${decision} — ${orch ? "the agent decides" : "no agent attached"}`; }
  else if (confirming) { status = orch ? "agent" : "needs-you"; toResume = true; headline = `${confirming} suggested repair(s) of a main result are still being confirmed by the review — nothing to decide yet; ${orch ? "the agent resumes the run" : "resume the run"}`; }
  else if (promotion && applyRefusal(dir, promotion)) { status = "needs-you"; headline = `promotion round ${promotion} was not applied — ${applyRefusal(dir, promotion)!.split("\n")[0]!.slice(0, 200)}`; }
  else if (promotion) { status = delegated ? "agent" : "needs-you"; headline = `promotion round ${promotion}: ${delegated ? "full auto — the agent decides which results join your toolkit, for your review after" : "decide which results join your toolkit"}`; }
  else if (promotionPhase) { status = orch ? "agent" : "needs-you"; toResume = true; headline = `promotion round ${promotionPhase} is not prepared yet${halted ? ` (${headlineOf(last)})` : ""} — ${orch ? "the agent resumes the run" : "resume the run"}`; }
  else if (halt && !done) { status = orch ? "agent" : "needs-you"; headline = `${halt}${orch ? "" : " — no agent attached"}`; }
  else if (reviews.length) { status = "needs-you"; headline = `review ${reviews.length} decision(s) the agent made`; }
  else if (done) { status = "done"; headline = `${report?.verdict ? verdictWords(report.verdict) : "report written"}${report?.paper_grade?.grade ? ` · paper: ${gradeWords(report.paper_grade.grade)}` : ""}`; }
  // No runner, and it left its heartbeat behind (killed, in any stage) or its log ends on a stage
  // at work: it was killed or crashed — no halt, no finish. (A Lean-stage line under a run since
  // sent back to V1 or V1.5 is history, not where it ended: the phase says where it was.)
  else if (left || (last && ENDED_AT_WORK.test(last.status) && (!/^\d/.test(last.stage) || phase === "formalization"))) {
    const at = phase === "init" ? "V1" : phase === "v1" ? "V1.5" : last && (phase === "formalization" || !/^\d/.test(last.stage)) ? stageName(last.stage) : STAGES[stageIndex + 1]?.id ?? "the run";
    status = orch ? "agent" : "needs-you"; toResume = true;
    headline = `ended without a halt (crashed or killed) during ${at} — ${orch ? "the agent resumes the run" : "resume the run"}`;
  }
  else { status = "idle"; headline = last ? `stopped after ${stageName(last.stage)}` : "not started"; }
  return {
    slug, title, authors, stage, stageIndex, phase, live, status, headline, lastEvent: last, pending,
    redoing: redoingOf(verify),
    ...(toResume ? { toResume } : {}),
    verdict: report?.verdict ?? null,
    buckets: report?.summary ? Object.fromEntries(Object.entries(report.summary).filter(([, v]) => typeof v === "number" && v > 0)) : null,
    updatedAt, supersededBy, orch, fullAuto, requests, unread, reviews, tokens: await tokenTotals(dir),
    share: ((sh) => (sh ? shareRecordView(sh) : null))(await readShare(dir)),
    shareable: status === "done" ? await shareableOf(dir) : null,
  };
}

const mtime = (f: string): number => { try { return statSync(f).mtimeMs; } catch { return 0; } };

export function stageName(id: string): string {
  const s = STAGES.find((x) => x.id === id);
  return s ? (/^[0-9]/.test(id) ? s.label.split(" ")[0]! : `${id}`) : id === "init" ? "start" : id;
}

/** The paper's grade (`report.ts` `paperGrade`) in words. */
export function gradeWords(g: string): string {
  return ({ error_free: "error-free", minor: "minor issues", major: "major errors" } as Record<string, string>)[g] ?? g.replace(/_/g, " ");
}

export function verdictWords(v: string): string {
  return ({
    repaired: "errors found — all repaired",
    no_error_found: "no error found",
    errors_found: "errors found",
    not_determined: "not determined — results could not be checked as printed",
    refuted: "a result is refuted",
  } as Record<string, string>)[v] ?? v.replace(/_/g, " ");
}

// ── run detail ───────────────────────────────────────────────────────────────

export interface ResultView {
  id: string;
  kind: string;
  label: string | null;
  deps: string[];
  review: { faithfulness?: string; ambiguity?: string; correctness?: string; detail?: string; reading?: string | null } | null;
  paperError: { kind: string; detail: string; witness: string | null } | null;
  state: "error" | "minor" | "ok";
  needs: boolean;
  /** Where the repair on file changes the result: its statement, its proof only, or — an error with
   *  no repair on file — nowhere yet. Null for a result with no error. */
  repair: "statement" | "proof" | "none" | null;
  bucket: string | null;
  lean: { decl: string; file: string; line: number } | null;
  /** The Lean proof is closed: reported so, or (while the run is at work) its own proof and every
   *  lemma it uses hold no `sorry` in the run's graph. */
  proved: boolean;
  axioms: string[] | null;
  conditions: Array<{ id: string; condition: string; reason?: string }>;
  /** The rows of the statement as it now stands (the view's, or the flat cut), each with its links. */
  rows: Array<{ id: string; kind: string; names: string; lean: string; segments: string[]; unstated: boolean }> | null;
  /** The statement as nested rows and clause cards, its links on the rows; null when it does not
   *  structure — the page then draws `rows` flat. */
  leanView: PageView | null;
  /** The stored links are not shown (`linksRefusal`): written for an earlier version of this
   *  statement (`changed`), against it cut short (`truncated`), or by an earlier link step for a cut
   *  that is not its cut now (`recut`); `leansmith relink` writes them again. */
  linksStale?: "changed" | "truncated" | "recut";
  /** F5 asked this result's rows and no call answered them (`nl_links.json` `unanswered`). */
  linksUnanswered?: true;
  /** The report names a Lean declaration that its file no longer holds. */
  leanMissing?: true;
  /** The paper's phrases the rows are linked to; null when the result has no links, or stale ones. */
  segments: PageSegment[] | null;
  uncovered: string[];
  key: boolean;
  /** A corollary a repair split off this result: the paper does not print it; the page shows it in a
   *  block of its own right after that result (`tex_html.ts`, `\vsCorollary`). */
  splitFrom?: string;
  /** A published result the proof of this result invokes by citation (`cited_in`), and the citation. */
  citedIn?: string;
  /** The result is cited, not proved, and Lean states it as a proposition (its drawer shows that one): the proposition's name. */
  citedLean?: string;
  /** The cited work's own words, as the run holds them (`discovery/cited_sources/<key>.txt`: the statement copied
   *  from the source under a provenance header), or why they are not held (`<key>.unavailable`); null: neither. */
  citedSource?: { copy: string; cut?: true } | { unavailable: string } | null;
  cites?: string;
  /** With `splitFrom`: what the block is (`core_graph.ts` `splitKind`) — a corollary of that result, or
   *  a proposition its printed statement bundled in (`\vsSplitProposition`), which does not rest on it. */
  splitKind?: SplitKind;
  /** An UMBRELLA (`core_graph.ts` `UMBRELLA_STATEMENT`): the corrected result only says that the
   *  blocks split off it hold. It has no Lean declaration (`lean` null): `blocks` are its
   *  propositions, and it is `proved` exactly when all of them are. */
  umbrella?: true;
  blocks?: string[];
}

export interface RunDetail {
  summary: RunSummary;
  stages: Array<{ id: string; label: string; state: "done" | "current" | "todo" | "halt" }>;
  halt: RunEvent | null;
  pending: PendingDecisions | null;
  source: { input: string | null; main: string | null };
  results: ResultView[];
  /** The paper's own Prop-valued declarations the results' rows name (`refs`), each once. */
  leanDefs: Record<string, PageDef>;
  /** Where the page shows the core node each of those declarations formalizes (`PageDef.node`). */
  places: Record<string, NodePlace>;
  promotion: PromotionView | null;
  /** The suggested repairs that would weaken a main result, waiting on the owner. */
  repairs: RepairView[];
  /** The issues the owner reported on margin comments (optional: nothing waits on them). */
  objections: OwnerObjection[];
  /** The owner's and the agent's messages on the page, oldest first. */
  messages: ThreadEntry[];
  /** The run's last share on the site of shared papers (`share.json`, written by `leansmith share`), less its token. */
  share: ShareView | null;
}

/** One repair that weakens what the paper claims: the owner accepts it, declines it, or asks for another. */
export interface RepairView {
  node: string;
  printed: string;
  proposed: string;
  given_up: string;
  detail: string;
  witness: string | null;
  /** The printed statement is not wrong but undetermined (`PaperError.undetermined`): the card says so. */
  undetermined?: boolean;
  /** The corollaries the proposal splits off the statement: part of what the owner rules on. */
  corollaries?: Array<{ title?: string; statement: string }>;
  /** The owner's guidance of an earlier redo, when that again ended in a suggestion. */
  guidance: string | null;
  /** The orchestrating agent's recommendation (`orch.mjs recommend <slug> repair …`), when given;
   *  `guidance`: what it would tell the fixer, offered as the text of a redo. */
  recommendation: { kind: string; why: string; guidance?: string } | null;
}

export interface PromotionView {
  round: "A" | "B";
  waiting: boolean;
  applied: boolean;
  checklist: string;
  proposals: Array<{
    id: string; title: string; content: string; reference: string; path: string; division: string;
    target_module: string; proposed_name: string; reuse_evidence: string; relation_to_paper: string;
    lean_type: string; is_paper_result: boolean; checker: string;
    /** The orchestrating agent's recommendation (`orch.mjs recommend`), when it gave one. */
    recommendation: { kind: string; why: string } | null;
  }>;
  /** New topics the entries need: each is the owner's accept / decline, keyed `topic:<path>`. */
  topics: Array<{ key: string; path: string; scope: string; for: string[]; recommendation: { kind: string; why: string } | null }>;
  skipped: number;
  decisions: Record<string, ChecklistDecision>;
  error: string | null;
  /** Why the last apply of the round ended without applying it, when it did. */
  refusal: string | null;
}

interface CoreStatement { id: string; kind: string; depends_on?: string[]; tex_locator?: { label?: string }; split_from?: string; umbrella?: boolean; proof_tex?: string; cited_in?: string; source?: { cite?: string; locator?: string } }
interface CoreCondition { id: string; condition?: string; construction?: string; used_by?: string[]; tex_locator?: { file?: string; from?: number; to?: number; label?: string | null } }
export interface CoreFile { statements?: CoreStatement[]; assumptions?: CoreCondition[]; definitions?: CoreCondition[] }

/**
 * Where the page shows a core node: `anchor` — its passage in the paper (the labelled environment
 * holding it, else the anchor at its own first line), with the words the paper states it in (`says`)
 * for an assumption or definition; or `reading` — pinned on the core and printed nowhere: a note
 * beside a result, or one of a result's added conditions.
 */
export type NodePlace = { anchor: string; says?: string } | { reading: true };

export interface CoreWhere {
  places: Record<string, NodePlace>;
  /** The assumptions and definitions no labelled environment holds: the page anchors each at its text. */
  passages: Array<{ node: string; file: string; from: number; to: number; text: string }>;
  /** The pinned readings, each with the labels of the results it is pinned on. */
  readings: Array<{ node: string; text: string; labels: string[] }>;
}

/** A reading entered for the paper's owner (`patches.json` `owner_readings`), as the page edits it. */
export interface OwnerReadingEntry { id: string; node: string; kind: "reading" | "bookkeeping"; text: string; withdraws: number }

/**
 * The owner readings each margin note states: comment id → the entries on file it shows. `stated`
 * is the page's pinned reading → comment id (`RenderedPaper.readings`; a pin's node is its id), so a
 * sentence pinned on several results has one entry under each result's own note. Pure.
 */
export function ownerReadingsByComment(
  stated: Record<string, string>,
  comments: ReadonlyArray<{ id: string; kind: string }>,
  onFile: ReadonlyArray<{ id: string; node: string; reading: string; kind?: string; withdraws?: unknown[] }> | undefined,
): Record<string, OwnerReadingEntry[]> {
  const owner = new Set(comments.filter((c) => c.kind === "reading-owner").map((c) => c.id));
  const out: Record<string, OwnerReadingEntry[]> = {};
  for (const r of onFile ?? []) {
    const c = stated[r.id];
    if (c === undefined || !owner.has(c)) continue;
    (out[c] ??= []).push({ id: r.id, node: r.node, kind: r.kind === "bookkeeping" ? "bookkeeping" : "reading", text: r.reading, withdraws: r.withdraws?.length ?? 0 });
  }
  return out;
}

/** Every core node's place on the page, and what the paper's renderer needs to give it one. Pure. */
export function coreWhere(core: CoreFile | null): CoreWhere {
  const out: CoreWhere = { places: {}, passages: [], readings: [] };
  const labelOf = new Map((core?.statements ?? []).map((s) => [s.id, s.tex_locator?.label ?? null]));
  for (const [id, label] of labelOf) out.places[id] = { anchor: label ? labelAnchor(label) : nodeAnchor(id) };
  // a reading of a corollary a repair split off is stated where that corollary is shown: at its parent
  for (const s of core?.statements ?? []) if (s.split_from && labelOf.get(s.split_from)) labelOf.set(s.id, labelOf.get(s.split_from)!);
  // a published result a proof invokes by citation has no environment: it is shown at that proof's result
  for (const s of core?.statements ?? []) {
    const host = s.cited_in ? labelOf.get(s.cited_in) : null;
    if (!host) continue;
    labelOf.set(s.id, host);
    out.places[s.id] = { anchor: labelAnchor(host) };
  }
  for (const c of [...(core?.assumptions ?? []), ...(core?.definitions ?? [])]) {
    const text = (c.condition ?? c.construction ?? "").trim(), loc = c.tex_locator;
    if (!loc?.file || !loc.from) {
      out.places[c.id] = { reading: true };
      if (text) out.readings.push({ node: c.id, text, labels: (c.used_by ?? []).flatMap((u) => labelOf.get(u) ?? []) });
      continue;
    }
    out.places[c.id] = { anchor: loc.label ? labelAnchor(loc.label) : nodeAnchor(c.id), ...(text ? { says: text } : {}) };
    if (!loc.label && text) out.passages.push({ node: c.id, file: loc.file, from: loc.from, to: loc.to ?? loc.from, text });
  }
  return out;
}
/** A node of the referee's review (`V15NodeVerdict`, read loosely). `reading`: the reading the paper
 *  determines (`ambiguity: "pinned"`) with the referee's evidence for it — the page shows the reading. */
interface ReviewNode { id: string; faithfulness?: string; ambiguity?: string; correctness?: string; detail?: string; reading?: Partial<NonNullable<V15NodeVerdict["reading"]>> | string | null }
/** The text of a pinned reading, whichever way the review holds it. Pure. */
export const readingText = (r: ReviewNode["reading"]): string | null => (typeof r === "string" ? r : r?.reading) || null;
interface ReportResult {
  node_id: string; bucket: string; lean: { decl: string; file: string; line: number } | null;
  axioms?: { axioms?: string[] } | null; bookkeeping?: Array<{ id: string; condition: string; reason?: string }>;
  /** The hypotheses the proof stages added to the result's Lean statement (`report.ts` `added_premises`). */
  added_premises?: Array<{ label: string; statement: string; classification?: string }>;
  /** The gates the result still assumes (`report.ts` `assumed_substrate`). */
  assumed_substrate?: Array<{ id: string; description: string }>;
}
/** What a run's detail reads of its report (`report.json`). */
export interface RunReport { results?: ReportResult[] }

type ProofGraph = { nodes?: Array<{ id: string; kind: string; provenance?: string; proof?: { state?: string }; lean?: { decl_name?: string; file?: string }; gate?: { gate_class?: string } }>; edges?: Array<{ kind: string; from: string; to: string }> };

/** The names (qualified and leaf) of the Lean declarations that state a result the paper cites
 *  without proving: the run's cited gates. Pure. */
export function citedNames(graph: ProofGraph | null): Set<string> {
  const names = (graph?.nodes ?? []).filter((n) => n.gate?.gate_class === "cited").flatMap((n) => n.lean?.decl_name ?? []);
  return new Set(names.flatMap((n) => [n, leanNameLeaf(n)]));
}

const CITED_SOURCE_MAX = 20000;
async function citedSourceOf(dir: string, cite: string): Promise<ResultView["citedSource"]> {
  const base = path.join(dir, "discovery", "cited_sources", cite.replace(/[^\w.-]/g, "_"));
  const text = await readCached(`${base}.txt`);
  if (text?.trim()) return { copy: text.slice(0, CITED_SOURCE_MAX), ...(text.length > CITED_SOURCE_MAX ? { cut: true as const } : {}) };
  const none = await readCached(`${base}.unavailable`);
  return none?.trim() ? { unavailable: none.slice(0, 2000) } : null;
}

/** A paper node the report gives no Lean for and the graph does, proved: a published result the paper
 *  cites and the Lean stages proved (`line` 0: the graph keeps none). Pure. */
export function provedInGraph(graph: ProofGraph | null): Map<string, { file: string; decl: string; line: number }> {
  return new Map((graph?.nodes ?? []).filter((n) => n.kind !== "gate" && n.lean?.decl_name && n.lean.file && n.proof?.state === "complete").map((n) => [n.id, { file: n.lean!.file!, decl: n.lean!.decl_name!, line: 0 }]));
}

/** The results whose Lean proof is closed in the run's graph: the result's own proof and every
 *  result its proof uses, transitively, are complete. Pure. */
export function closedProofs(graph: ProofGraph | null): Set<string> {
  const proves = (k: string) => k === "theorem" || k === "lemma";
  const open = new Set((graph?.nodes ?? []).filter((n) => proves(n.kind) && n.proof?.state !== "complete").map((n) => n.id));
  const users = new Map<string, string[]>();
  for (const e of graph?.edges ?? []) if (e.kind === "proof-uses") users.set(e.to, [...(users.get(e.to) ?? []), e.from]);
  const todo = [...open];
  while (todo.length) for (const u of users.get(todo.pop()!) ?? []) if (!open.has(u)) { open.add(u); todo.push(u); }
  return new Set((graph?.nodes ?? []).filter((n) => proves(n.kind) && !open.has(n.id)).map((n) => n.id));
}

/** A result's Lean statement as its drawer draws it: its rows, its view, and whether the stored links are on them. */
interface LeanStatement { rows: ResultView["rows"]; leanView: PageView | null; linked: boolean; stale?: ResultView["linksStale"]; missing: boolean }
const NO_LEAN: LeanStatement = { rows: null, leanView: null, linked: false, missing: false };
type NlFile = { results?: Array<{ node: string; key?: string; unanswered?: true; segments: Array<{ id: string; text: string; display?: string }>; rows: NonNullable<ResultView["rows"]>; uncovered: string[] }> };

/** Stored segments as the page takes them. Pure. */
const pageSegments = (segments: NonNullable<NlFile["results"]>[number]["segments"]): PageSegment[] => segments.map((x) => ({
  id: x.id, text: x.text,
  ...(x.display ? { display: x.display, alone: { text: partAlone(x) } } : {}),
  ...(x.display === x.id ? { whole: { text: displayWhole(segments.filter((y) => y.display === x.id)) } } : {}),
}));

/**
 * The Lean statements of a run's reported results (`ids`: in the order the page lists them) and the
 * declarations they name. Cutting them is the costly part of a run's detail, so it is held while the
 * records it reads (report, links, graph) and every Lean file it read are unchanged. The views are
 * shared between answers: never changed after this.
 */
async function leanStatements(cfg: ToolkitConfig, dir: string, leanDir: string, ids: string[], given?: RunReport): Promise<{ of: Map<string, LeanStatement>; defs: Record<string, PageDef> }> {
  const records = ["report.json", "nl_links.json", "graph.json"].map((f) => path.join(dir, f));
  const held = given ? createHash("sha256").update(JSON.stringify(given.results ?? [])).digest("hex") : "";
  return deriveRead(`lean:${dir}`, [leanDir, held, ...records.map(signature), ...ids].join("|"), async (read) => {
    const [report, nl, graph] = await Promise.all([given ?? readJsonCached<RunReport>(records[0]!), readJsonCached<NlFile>(records[1]!), readJsonCached<ProofGraph>(records[2]!)]);
    const byReport = new Map((report?.results ?? []).map((r) => [r.node_id, r]));
    const byNl = new Map((nl?.results ?? []).map((r) => [r.node, r]));
    const cited = citedNames(graph);
    const named = leanDefs(cfg.toolkitRoot, leanDir, cited, read);
    const inGraph = provedInGraph(graph);
    const of = new Map<string, LeanStatement>();
    for (const id of ids) {
      const nlr = byNl.get(id);
      const rep = { lean: byReport.get(id)?.lean ?? inGraph.get(id) };
      if (!rep.lean) continue;
      // The Lean drawn is always the statement as it now stands; stored links are put on it only
      // when they are that statement's (`applyLinks`), and are otherwise not shown at all.
      let rows: ResultView["rows"] = null;
      let linked = false, stale: ResultView["linksStale"];
      const text = await read(path.join(leanDir, rep.lean.file));
      const src = text ? declSource(text, rep.lean.decl, rep.lean.line || undefined) : null;
      const leanView: PageView | null = src ? leanStatementView(src, cited) : null;
      if (leanView) {
        await named.annotate(leanView, rep.lean.file, rep.lean.decl, rep.lean.line || undefined);
        linked = Boolean(nlr) && applyLinks(leanView, nlr!.rows, nlr!.key);
        if (nlr && !linked) stale = linksRefusal(leanView, nlr.rows, nlr.key);
        const links = new Map<string, { segments: string[]; unstated: boolean }>();
        eachRow(leanView, (row) => { if (row.id) links.set(row.id, { segments: row.xl?.split(" ") ?? [], unstated: Boolean(row.unstated) }); });
        rows = viewRows(leanView).map((r) => ({ ...r, ...links.get(r.id)! }));
        delete leanView.statement;
        delete leanView.key;
      } else {
        const flat = src ? flatLeanRows(src) : null;
        linked = Boolean(nlr && flat) && flat!.length === nlr!.rows.length && flat!.every((r, k) => r.id === nlr!.rows[k].id && squash(r.lean) === squash(nlr!.rows[k].lean));
        rows = linked ? nlr!.rows : flat?.map((r) => ({ ...r, segments: [], unstated: false })) ?? null;
      }
      of.set(id, { rows, leanView, linked, stale, missing: !src });
    }
    // An assumption's or a definition's declaration takes its node's links when they are its own
    // (links for another version of it are not shown). A block may hold several: their phrases'
    // ids are told apart by the node.
    // the paper's assumptions and definitions are shown at their blocks, named by a result or not
    for (const n of graph?.nodes ?? []) if ((n.kind === "assumption" || n.kind === "definition") && n.provenance === "from-note" && n.lean?.decl_name && n.lean.file) await named.include(n.lean.file, n.lean.decl_name);
    for (const d of Object.values(named.defs)) {
      const nlr = d.node ? byNl.get(d.node) : undefined;
      if (!d.view) continue;
      const at = (id: string) => `${d.node}:${id}`;
      if (nlr && !nlr.unanswered && applyLinks(d.view, nlr.rows.map((r) => ({ ...r, segments: r.segments.map(at) })), nlr.key)) {
        d.segments = pageSegments(nlr.segments).map((x) => ({ ...x, id: at(x.id), ...(x.display ? { display: at(x.display) } : {}) }));
        d.uncovered = nlr.uncovered.map(at);
      }
      delete d.view.key;
    }
    return { of, defs: named.defs };
  });
}

/**
 * `lean: false` leaves the Lean statements out (`rows`, `leanView`, the links, `leanDefs`, `places`):
 * all that only a result's drawer shows of them, and the one costly part. `report`: the report to
 * read the results from in place of the file — V6's own, which it holds before it writes it.
 */
export async function runDetail(cfg: ToolkitConfig, slug: string, opts: { lean: boolean; report?: RunReport } = { lean: true }): Promise<RunDetail> {
  const dir = runDir(cfg, slug);
  const summary = await runSummary(cfg, slug);
  const state = await readState(cfg, slug);
  const verify = state?.verify;
  const patches = await readPatches(cfg, slug);
  const pending = verify ? pendingDecisions(verify, patches) : null;
  const events = recentEvents(cfg, slug);
  const last = events.at(-1) ?? null;
  const halt = !summary.live && last && (last.status === "checkpoint" || last.status === "blocked") ? last : null;

  const stages = STAGES.map((s, i) => ({
    id: s.id, label: s.label,
    state: (i <= summary.stageIndex ? "done" : i === summary.stageIndex + 1 ? (summary.live || summary.status === "running" ? "current" : summary.status === "needs-you" || summary.status === "agent" ? "halt" : "todo") : "todo") as "done" | "current" | "todo" | "halt",
  }));

  const core = await readJsonCached<CoreFile>(path.join(dir, "discovery", "core.json"));
  // The paper's results: the corrected core's, plus any the transcription holds that it dropped
  // (a result awaiting a ruling may be out of the corrected core).
  const transcribed = await readJsonCached<{ statements?: CoreStatement[] }>(path.join(dir, "discovery", "core.transcribed.json"));
  const statements = [...(core?.statements ?? [])];
  for (const s of transcribed?.statements ?? []) if (!statements.some((x) => x.id === s.id)) statements.push(s);
  const review = await readJsonCached<{ nodes?: ReviewNode[] }>(path.join(dir, "discovery", "v1_5_review.json"));
  const report = opts.report ?? (reportCurrent(state) ? await readJsonCached<RunReport>(path.join(dir, "report.json")) : null);
  const nl = await readJsonCached<NlFile>(path.join(dir, "nl_links.json"));
  const keys = new Set((patches as { key_results?: string[] } | null)?.key_results ?? []);
  const byReview = new Map((review?.nodes ?? []).map((n) => [n.id, n]));
  const byReport = new Map((report?.results ?? []).map((r) => [r.node_id, r]));
  const byNl = new Map((nl?.results ?? []).map((r) => [r.node, r]));
  const errors = (verify as { paper_errors?: Record<string, { detail: string; witness: string | null; kind?: string; undetermined?: boolean; owner_decision?: string }> } | undefined)?.paper_errors ?? {};
  // a result needs the owner when the agent's ruling on it awaits their review
  // … or when a repair that would weaken it waits for their decision
  // A suggestion is the owner's to rule on once the run has halted with it: while the runner lives
  // the referee is still grading it, and no ruling can be sent.
  const repairs = summary.live ? [] : await repairViews(dir, verify);
  const needs = new Set<string>([...summary.reviews.map((d) => d.node), ...repairs.map((r) => r.node)]);
  const ids = new Set(statements.map((s) => s.id));
  const kinds = splitKinds({ statements });
  const leanDir = state?.lean_subdir ? path.join(cfg.toolkitRoot, state.lean_subdir) : null;
  const graph = await readJsonCached<ProofGraph>(path.join(dir, "graph.json"));
  // What an earlier state of the run left is not this one's: the Lean statements are the current
  // report's (`reportCurrent`), and a proof counts as closed from the graph only while the graph is
  // the scaffold's of the core as it stands (`graphCurrent`).
  const stated = opts.lean && leanDir && report ? await leanStatements(cfg, dir, leanDir, statements.map((s) => s.id), opts.report) : null;
  const closed = report || !graphCurrent(state) ? new Set<string>() : closedProofs(graph);
  // a result the paper cites without proving: Lean states it as a proposition its users assume (a gate)
  const gates = new Map((graph?.nodes ?? []).filter((n) => n.kind === "gate" && n.lean?.decl_name).map((n) => [n.id, leanNameLeaf(n.lean!.decl_name!)]));
  // … or as a lemma the Lean proves: then it is a result like any other, with that declaration
  const citedProved = provedInGraph(graph);
  const results: ResultView[] = [];
  for (const s of statements) {
    const rv = byReview.get(s.id) ?? null;
    const rep = byReport.get(s.id) ?? null;
    // a finding the owner withdrew (`--reject-finding`) is no error of the paper: the statement stands, under their reading
    const pe = isWithdrawn(errors[s.id]) ? null : errors[s.id] ?? null;
    const isError = (pe && pe.kind !== "clarification") || rep?.bucket === "repaired" || rep?.bucket === "refuted";
    const isMinor = !isError && ((pe && pe.kind === "clarification") || rv?.ambiguity === "pinned");
    const nlr = byNl.get(s.id);
    const { rows, leanView, linked, stale, missing } = stated?.of.get(s.id) ?? NO_LEAN;
    results.push({
      id: s.id, kind: s.kind, label: s.tex_locator?.label ?? null,
      deps: (s.depends_on ?? []).filter((d) => ids.has(d)),
      review: rv ? { faithfulness: rv.faithfulness, ambiguity: rv.ambiguity, correctness: rv.correctness, detail: rv.detail, reading: readingText(rv.reading) } : null,
      paperError: pe ? { kind: pe.kind ?? (pe.undetermined && rep?.bucket !== "refuted" ? "undetermined" : "error"), detail: pe.detail, witness: pe.witness } : null,
      state: isError ? "error" : isMinor ? "minor" : "ok",
      needs: needs.has(s.id),
      repair: !isError ? null : repairPlace(patches?.patches?.find((p) => p.node === s.id)),
      bucket: rep?.bucket ?? null,
      lean: rep?.lean ?? (s.cited_in ? citedProved.get(s.id) : null) ?? null,
      proved: Boolean(rep?.lean) || closed.has(s.id) || Boolean(s.cited_in && citedProved.has(s.id)),
      axioms: rep?.axioms?.axioms ?? null,
      // every condition the report gives the result under: V1.5's side conditions, the hypotheses
      // the proof stages added to its Lean, the gates it still assumes — one list, as report.md's
      conditions: [
        ...(rep?.bookkeeping ?? []),
        ...(rep?.added_premises ?? []).map((p) => ({ id: p.label, condition: p.statement, reason: `added to the Lean statement${p.classification ? ` (${p.classification})` : ""}` })),
        ...(rep?.assumed_substrate ?? []).map((g) => ({ id: g.id, condition: g.description, reason: "assumed, not proved (the result is conditional on it)" })),
      ],
      rows,
      leanView,
      ...(nlr && rows && !linked ? { linksStale: stale ?? "changed" } : {}),
      ...(linked && nlr?.unanswered ? { linksUnanswered: true as const } : {}),
      ...(missing ? { leanMissing: true as const } : {}),
      segments: linked ? pageSegments(nlr!.segments) : null,
      uncovered: linked ? nlr!.uncovered : [],
      key: keys.has(s.id),
      ...(s.split_from ? { splitFrom: s.split_from, splitKind: kinds.get(s.id) ?? "corollary" } : {}),
      ...(!rep?.lean && gates.has(s.id) ? { citedLean: gates.get(s.id)! } : {}),
      ...(s.cited_in ? { citedIn: s.cited_in } : {}),
      ...(s.source?.cite ? { cites: `${s.source.cite}, ${s.source.locator ?? ""}`, ...(opts.lean ? { citedSource: await citedSourceOf(dir, s.source.cite) } : {}) } : {}),
      ...(s.umbrella ? { umbrella: true as const, blocks: statements.filter((x) => x.split_from === s.id).map((x) => x.id) } : {}),
    });
  }
  // An umbrella is established through its blocks: proved exactly when all of them are.
  for (const r of results) if (r.umbrella) r.proved = r.blocks!.length > 0 && r.blocks!.every((b) => results.find((x) => x.id === b)?.proved === true);
  const formalized = new Set(Object.values(stated?.defs ?? {}).flatMap((d) => d.node ?? []));
  return {
    summary, stages, halt, pending,
    source: { input: verify?.source?.input ?? null, main: await mainFile(cfg, slug, state) },
    results,
    leanDefs: stated?.defs ?? {},
    places: Object.fromEntries(Object.entries(coreWhere(core).places).filter(([id]) => formalized.has(id))),
    promotion: await promotionView(cfg, slug, state),
    repairs,
    objections: ((await readJsonCached<OwnerObjection[]>(path.join(dir, OBJECTIONS_FILE))) ?? []).filter((o) => o && o.comment && o.text),
    messages: (await messagesOf(dir)).map((m) => ({
      id: m.id, from: m.from, at: m.at, ...(m.re ? { re: m.re } : {}),
      ...(m.from === "agent" ? { text: String(m.text ?? ""), ...(m.seen ? {} : { unseen: true as const }) } : { words: String(m.text ?? ""), ...(m.handled ? {} : { waiting: true as const }) }),
      ...(m.files?.length ? { files: m.files.map((f) => ({ name: String(f.name), bytes: Number(f.bytes) || 0 })) } : {}),
    })),
    share: summary.share,
  };
}

/** What only a result's drawer shows of it: sent apart from the page's detail, which a run at work changes every few seconds. */
const DRAWER_KEYS = ["review", "paperError", "axioms", "conditions", "rows", "leanView", "linksStale", "linksUnanswered", "leanMissing", "segments", "uncovered", "citedSource"] as const;
type DrawerKey = (typeof DRAWER_KEYS)[number];
/** A run's detail as the page draws it before any drawer opens (`runDetail` with `lean: false`). Of a
 *  result's review it keeps the grade its badge shows. */
export type RunPage = Omit<RunDetail, "results" | "leanDefs" | "places"> & { results: Array<Omit<ResultView, DrawerKey> & { review: { correctness?: string } | null }> };
/** The rest of a run's detail: each result's drawer, the declarations the drawers open and their places. */
export interface RunDrawers { results: Record<string, Pick<ResultView, DrawerKey>>; leanDefs: RunDetail["leanDefs"]; places: RunDetail["places"] }

export function pageOf(d: RunDetail): RunPage {
  const { leanDefs: _defs, places: _places, ...page } = d;
  return { ...page, results: d.results.map((r) => ({ ...Object.fromEntries(Object.entries(r).filter(([k]) => !(DRAWER_KEYS as readonly string[]).includes(k))), review: r.review ? { correctness: r.review.correctness } : null }) as RunPage["results"][number]) };
}

export function drawersOf(d: RunDetail): RunDrawers {
  const pick = (r: ResultView) => Object.fromEntries(Object.entries(r).filter(([k]) => (DRAWER_KEYS as readonly string[]).includes(k))) as Pick<ResultView, DrawerKey>;
  return { results: Object.fromEntries(d.results.map((r) => [r.id, pick(r)])), leanDefs: d.leanDefs, places: d.places };
}

/** Where a patch changes its result (`ResultView.repair`). */
function repairPlace(patch: { ops?: PatchOp[]; corrected_statement?: string | null } | undefined): "statement" | "proof" | "none" {
  if (!patch) return "none";
  return patch.corrected_statement || (patch.ops ?? []).some(isStatementOp) ? "statement" : (patch.ops ?? []).some(isProofOp) ? "proof" : "none";
}

/** Whether a repair of the run's last receipt is being redone: the receipt closed as `redo`, or as
 *  `ruled` (the items ruled on differently) with a redo among its rulings. */
export function redoingOf(verify: unknown): boolean {
  const rec = (verify as { weakening_repair?: { status?: string; decisions?: Record<string, string> } } | undefined)?.weakening_repair;
  return rec?.status === "redo" || (rec?.status === "ruled" && Object.values(rec.decisions ?? {}).includes("redo"));
}

/** Whether `report.json` is the report of the run as it stands: written by V6 and not followed by a
 *  re-entry (a run sent back to V1, V1.5 or the Lean stages keeps the file of its earlier state). */
export function reportCurrent(state: { stage_completed?: string; verify?: { phase?: string } } | null | undefined): boolean {
  const phase = state?.verify?.phase ?? "";
  return state?.stage_completed === "V6" || phase === "done" || phase === "failed" || phase === "proposals_B";
}

/** Whether `graph.json` is the graph of the run as it stands: the scaffold stands (the cursor is at
 *  F2 or later). A run sent back before F2 — a new core, a re-plan, a re-scaffold — keeps the file
 *  of its earlier state until F2 writes it again. */
export function graphCurrent(state: { stage_completed?: string } | null | undefined): boolean {
  return ["2", "2.5", "3", "3.5", "4", "5"].includes(state?.stage_completed ?? "");
}

/** The render or contract checkpoint a run is halted at (`state.verify.render_checkpoint`): a tool
 *  or model-text defect of the annotated paper, the agent's to settle, answered before any ruling. */
export function renderCheckpointOf(verify: unknown): { kind: "render" | "contract"; blocks: number } | null {
  const rc = (verify as { render_checkpoint?: { kind?: string; defects?: unknown[] } | null } | undefined)?.render_checkpoint;
  return rc ? { kind: rc.kind === "contract" ? "contract" : "render", blocks: rc.defects?.length ?? 0 } : null;
}

/** The identity of a suggested repair, as `orch.mjs recommend` records it (`of`): its node and
 *  proposed statement. A redo, or a later round's suggestion on the node, is another repair. */
export const repairKey = (item: { node: string; proposed: string }): string => createHash("sha256").update(`${item.node}\n${item.proposed ?? ""}`).digest("hex").slice(0, 16);

/** The pending weakening repairs of a run, each with the agent's recommendation when it gave one. */
async function repairViews(dir: string, verify: StateFile["verify"] | undefined): Promise<RepairView[]> {
  const w = (verify as { weakening_repair?: { status?: string; unconfirmed?: boolean; items?: Array<{ node: string; printed: string; proposed: string; given_up: string; detail: string; witness: string | null; guidance?: string; corollaries?: Array<{ title?: string; statement: string }> }> } } | undefined)?.weakening_repair;
  // An unconfirmed receipt gets no decision card: the runner refuses every ruling on it. Nor does
  // any receipt behind a render or contract checkpoint, which the runner answers before it reads one.
  if (w?.status !== "pending" || w.unconfirmed || renderCheckpointOf(verify)) return [];
  const recs = await readJsonCached<Record<string, { kind?: string; why?: string; guidance?: string; of?: string }>>(path.join(dir, "repair_recommendations.json"));
  return (w.items ?? []).map((i) => ({
    // (a receipt written before `detail` was kept to the printed statement holds the repair's grade there)
    node: i.node, printed: i.printed, proposed: i.proposed, given_up: i.given_up, detail: gradesRepair(i.detail ?? "") ? "" : i.detail ?? "", witness: gradesRepair(i.detail ?? "") ? null : i.witness, guidance: i.guidance ?? null,
    ...((verify as { paper_errors?: Record<string, { undetermined?: boolean }> }).paper_errors?.[i.node]?.undetermined ? { undetermined: true } : {}),
    ...(i.corollaries?.length ? { corollaries: i.corollaries } : {}),
    // only the recommendation made on THIS proposal: one on an earlier repair of the node is not shown
    recommendation: recs?.[i.node]?.kind && recs[i.node]!.of === repairKey(i) ? { kind: String(recs[i.node]!.kind), why: String(recs[i.node]!.why ?? ""), ...(recs[i.node]!.guidance ? { guidance: String(recs[i.node]!.guidance) } : {}) } : null,
  }));
}

/** The checklist of a promotion round: `<toolkit>/doc/proposals/<slug>.<R>.md`. */
export const checklistPath = (cfg: ToolkitConfig, slug: string, round: "A" | "B"): string =>
  path.join(cfg.toolkitRoot, "doc", "proposals", `${slug}.${round}.md`);

async function promotionView(cfg: ToolkitConfig, slug: string, state: StateFile | null): Promise<PromotionView | null> {
  const dir = runDir(cfg, slug);
  const waitingRound = roundProposed(state);
  // the round in front of the owner, else the latest round on file (shown as applied)
  const round: "A" | "B" | null = waitingRound ?? (existsSync(path.join(dir, "proposals", "B.json")) ? "B" : existsSync(path.join(dir, "proposals", "A.json")) ? "A" : null);
  if (!round) return null;
  const batch = await readJsonCached<ProposalBatch>(path.join(dir, "proposals", `${round}.json`));
  if (!batch) return null;
  const md = checklistPath(cfg, slug, round);
  const text = await readCached(md);
  let decisions: Record<string, ChecklistDecision> = {};
  let error: string | null = null;
  if (text) {
    try { decisions = parseChecklist(text, batch); } catch (err) { error = err instanceof Error ? err.message : String(err); }
  }
  const proposed = batch.proposals.filter((p) => p.verdict === "propose");
  const recs = await readJsonCached<Record<string, { kind?: string; why?: string; of?: string }>>(path.join(dir, "proposals", `${round}.recommendations.json`));
  // a recommendation is shown beside the item it was written for only (`recommendationKeys`)
  const recKeys = recommendationKeys(batch);
  const recOf = (key: string): { kind: string; why: string } | null => (recs?.[key]?.kind && recs[key]!.of === recKeys.get(key) ? { kind: String(recs[key]!.kind), why: String(recs[key]!.why ?? "") } : null);
  type Loose = { relation_to_paper?: string; lean_type?: string; checker?: { agrees?: boolean; note?: string } | null; source: { is_paper_result?: boolean } };
  return {
    round, waiting: waitingRound === round,
    applied: roundDecided(dir, round),
    refusal: applyOf(dir, round) === "live" ? null : applyRefusal(dir, round),
    checklist: md,
    proposals: proposed.map((p) => {
      const l = p as unknown as Loose;
      return {
        id: p.id, title: p.title, content: p.content, reference: p.reference, path: (p as { path?: string }).path ?? "",
        division: p.division, target_module: p.target_module, proposed_name: p.proposed_name,
        reuse_evidence: p.reuse_evidence, relation_to_paper: l.relation_to_paper ?? "", lean_type: l.lean_type ?? "",
        is_paper_result: Boolean(l.source?.is_paper_result),
        checker: l.checker ? `${l.checker.agrees === false ? "disagrees" : "agrees"}${l.checker.note ? ` — ${l.checker.note}` : ""}` : "",
        recommendation: recOf(p.id),
      };
    }),
    topics: newTopics(batch).map((t) => { const key = topicKey(t.path); return { key, ...t, recommendation: recOf(key) }; }),
    skipped: batch.proposals.length - proposed.length,
    decisions, error,
  };
}
