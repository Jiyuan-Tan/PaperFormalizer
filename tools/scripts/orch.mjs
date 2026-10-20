#!/usr/bin/env node
// The orchestrating agent's link to one verify run (any agent: Claude Code, Codex, …). Plain Node,
// no build step:
//
//   node tools/scripts/orch.mjs watch <slug> --toolkit <path> [--timeout <s>] [--take] [--known <id,…>] [--starts]
//       Attach this session to the run (runs/<slug>/orch.json: the paper's page shows it), then block
//       until there is something to act on, print what and exit 0:
//         - with --starts (a session in a batch job that starts runs itself, `batch_orch.mjs`): the
//           owner asked the page to start the run (a resume, a ruling, the apply of a round) or to stop
//           it — the page wrote runs/<slug>/start_request.json and did nothing itself; do it, then
//           remove the file;
//         - the runner exited (a halt, a finish, a crash) — also a run the owner resumed on the page;
//         - a run that was waiting runs again (the owner's decisions sent on the page, or a resume by a
//           session): arm the watcher again to follow it;
//         - the apply of a promotion round the owner started ended without completing the round,
//           or was refused before it applied anything (its message is printed);
//         - the owner rejected a ruling of yours on the page (with guidance);
//         - the owner reported an issue with a comment of the page (a finding, a repair or a
//           clarification they find wrong; runs/<slug>/owner_objections.json);
//         - the run finished with blocking items in its bundle's TODO.md (once per bundle written);
//         - the owner wrote to you on the page — a message, or their reply to a request of yours,
//           with the files they attached (runs/<slug>/orch_messages.json) — whatever the run is
//           doing, and at once when one is on file as the watcher is armed: each is reported at
//           every arm until you `reply` to it or mark it `handled` (`--known`: messages, rejected
//           rulings and reported issues already reported, as `<id>@<time written>`, which alone return
//           nothing); it changes nothing in the run by itself.
//       A run that is not live waits for the owner (a resume or a review on the page). Exit 2 after
//       --timeout seconds with nothing to act on (for a harness that polls). Another live session
//       attached to the run: exit 3, unless --take. Armed right after a launch, it waits up to a
//       minute for the run to appear (runs/<slug>/state.json) before it exits 66.
//   node tools/scripts/orch.mjs decided <slug> --toolkit <path> <node> "<what you decided and why>"
//       Record a ruling you made at a halt, for the owner's review on the page; prints the id.
//   node tools/scripts/orch.mjs handled <slug> --toolkit <path> <id>
//       Mark a rejected ruling (d<n>), a reported issue (obj-<n>) or a message of the owner's (m<n>)
//       as acted on (after you followed the owner's guidance, or answered them).
//   node tools/scripts/orch.mjs ask <slug> --toolkit <path> [--owner-only] "<text>"
//       Ask the owner something on the paper's page (they reply there, or in this session); prints the id.
//       On a full-auto run (`verify --full-auto`) the owner delegated their rulings: a ruling is yours
//       (enter it, record it with `decided`), and only what they alone can give is asked, with
//       --owner-only (a cited source you cannot access, the workers' sandbox); else exit 65.
//   node tools/scripts/orch.mjs reply <slug> --toolkit <path> [<m<n>|q<n>>] "<text>"
//       Answer the owner on the page (TeX: math in `$…$`), under their message m<n> or in the
//       thread of your request q<n> — what it answers is then acted on (`handled`); with no id, a
//       message of your own. Prints the id. An id that names nothing exits 65.
//   The messages' store is written under a lock (messages_store.mjs); one that is not a JSON list is
//       never written over: the verb fails naming it, and the watcher returns saying so.
//   node tools/scripts/orch.mjs recommend <slug> --toolkit <path> <A|B> <proposal id> <kind> "<why, one line>"
//       Your recommendation on one entry of a promotion round, shown beside it on the paper's page
//       (kind: accept | accept_with_edits | generalize_first | defer | decline; a new topic the round
//       asks about by its key `topic:<path>`: accept | decline). The owner decides.
//   node tools/scripts/orch.mjs recommend <slug> --toolkit <path> repair <node> <accept|decline|redo> "<why>" [--guidance "<text>"]
//       Your recommendation on a suggested repair that would weaken a main result (the owner rules
//       on it on the page): accept it, decline it, or have the fixer repair it again — `--guidance`
//       is what you would tell the fixer, offered to the owner as the text of their redo.
//       A recommendation is on ONE proposal: it is bound to what the repair pending on <node>, or
//       the entry or new topic of the batch on file, proposes now (the page shows it beside that
//       proposal only; one on an earlier proposal is dropped when the file is next written — after
//       a redo, or a round written again, recommend again).
//   On a full-auto run the recommendation that completes the decision carries it out: the repairs by
//       `verify --resume` with the rulings recommended, a round by `propose --apply --recommended`,
//       started detached (output in runs/<slug>/logs/full_auto_<time>.log), and each repair (a round
//       as one entry) is listed for the owner's review as a ruling of yours; it prints what it started.
//   Exit codes: 0 done (watch: something to act on); 2 watch timed out with nothing to act on;
//       3 another live session holds the run; 64 usage; 65 nothing to act on by that name (no
//       repair pending on the node, no such batch entry, no such ruling, issue, message or request);
//       66 no such run under that toolkit (no runs/<slug>/state.json: a wrong slug or toolkit, or a
//       launch that was refused before it wrote one — read its log).
//   node tools/scripts/orch.mjs done <slug> --toolkit <path> [<id>]
//       Clear one request (or all); the owner's replies to it (to any, with no id) are then acted on.
//   node tools/scripts/orch.mjs detach <slug> --toolkit <path>
//       This session no longer follows the run: the page shows no agent attached.
//   node tools/scripts/orch.mjs --help
//       Print this text.
import { execFileSync, spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { closeSync, existsSync, mkdirSync, openSync, readdirSync, readFileSync, readlinkSync, realpathSync, renameSync, rmSync, statSync, utimesSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { nextMessageId, readMessages, updateMessages } from "./messages_store.mjs";

const [cmd, slug, ...rest] = process.argv.slice(2);
const opt = (name) => { const i = rest.indexOf(name); return i >= 0 ? rest.splice(i, 2)[1] : undefined; };
const flag = (name) => { const i = rest.indexOf(name); if (i >= 0) rest.splice(i, 1); return i >= 0; };
const usage = "usage: orch.mjs <watch|decided|handled|ask|reply|recommend|done|detach> <slug> --toolkit <path> …  (orch.mjs --help: what each does)";
if ([cmd, slug].some((a) => a === "--help" || a === "-h")) {
  // the verbs, as this file's header states them
  const header = readFileSync(fileURLToPath(import.meta.url), "utf8").split("\n").slice(1);
  console.log(header.slice(0, header.findIndex((l) => !l.startsWith("//"))).map((l) => l.replace(/^\/\/ ?/, "")).join("\n"));
  process.exit(0);
}
const toolkit = opt("--toolkit");
if (!cmd || !slug || !toolkit || !/^[A-Za-z0-9][A-Za-z0-9_.-]{0,120}$/.test(slug)) { console.error(usage); process.exit(64); }
const run = path.join(path.resolve(toolkit), "runs", slug);
// A watcher armed right after a launch: the runner seeds the run a few seconds in.
for (const until = Date.now() + (cmd === "watch" ? Number(process.env.THEOREMCHECKER_ORCH_APPEAR_MS ?? 60_000) : 0); !existsSync(path.join(run, "state.json")); ) {
  if (Date.now() >= until) { console.error(`no run ${slug} under ${toolkit}${cmd === "watch" ? " (waited for runs/<slug>/state.json: a wrong slug or toolkit, or the launch was refused — read its log)" : ""}`); process.exit(66); }
  await new Promise((r) => setTimeout(r, 500));
}
const ORCH = path.join(run, "orch.json");
const REQUESTS = path.join(run, "orch_requests.json");
/** What the owner asked the page to start while this session starts runs itself (`ui/run_model.ts` `START_REQUEST_FILE`). */
const START_REQUEST = path.join(run, "start_request.json");
const DECISIONS = path.join(run, "orch_decisions.json");
const OBJECTIONS = path.join(run, "owner_objections.json");
/** The page's conversation: `{ id: m<n>, from: "user" | "agent", text, at, re?, files?, handled?, seen? }`
 *  (`ui/run_model.ts` `OrchMessage`); `re`: the message, or the request q<n>, it answers. */
const MESSAGES = path.join(run, "orch_messages.json");
const num = (id) => Number(String(id).slice(1)) || 0;

const readJson = (f, dflt) => { try { return JSON.parse(readFileSync(f, "utf8")); } catch { return dflt; } };
/** Written whole (temp file, then rename): the page reads, and writes, the same files. */
const writeJson = (f, v) => { mkdirSync(path.dirname(f), { recursive: true }); const tmp = `${f}.${process.pid}.tmp`; writeFileSync(tmp, JSON.stringify(v, null, 2) + "\n"); renameSync(tmp, f); };
/** A text the page typesets as TeX must close its math: an odd count of `$` is a shell that ate a
 *  variable ("$X" in double quotes) or a lost delimiter, and the page would set the rest as one formula. */
const texOrExit = (what, text) => {
  if ((text.replace(/\\\$/g, "").match(/\$/g) ?? []).length % 2 === 1) {
    console.error(`${what}: the text has an unclosed $ (math is $…$; in a shell, pass the text in single quotes so that $X is not expanded): ${text.slice(0, 200)}`);
    process.exit(65);
  }
  // a reference the paper does not label is drawn "??" on the page: name each label as the paper writes it
  let flat = null;
  try { flat = readFileSync(path.join(run, "discovery", "flat.tex"), "utf8"); } catch { return; }
  const key = (l) => l.trim().replace(/\s+/g, " ");
  // the labels the page resolves: `\label{…}` (also `\label [t] {…}`), a paper macro wrapping `\label{#1}`,
  // the compiled `.aux` of the source or the annotated copy, and the annotator's own `vsSec<n>`
  const wrappers = [...flat.matchAll(/\\(?:re)?newcommand\*?\s*\{?\s*\\([A-Za-z]+)\s*\}?\s*\[1\]\s*\{[^{}]*\\label\s*\{#1\}/g)].map((m) => m[1]);
  const labelRe = new RegExp(String.raw`\\(?:label|${wrappers.join("|") || "label"})\s*(?:\[[^\]]*\])?\s*\{([^}]*)\}`, "g");
  const labels = new Set([...flat.matchAll(labelRe)].map((m) => key(m[1])));
  for (const dir of ["source", "annotated"]) {
    let names = [];
    try { names = readdirSync(path.join(run, dir)).filter((f) => f.endsWith(".aux")); } catch { continue; }
    for (const f of names) { try { for (const m of readFileSync(path.join(run, dir, f), "utf8").matchAll(/\\newlabel\{([^}]*)\}/g)) labels.add(key(m[1])); } catch { /* unreadable: skip */ } }
  }
  const unknown = [...text.matchAll(/\\(?:eq|c|C|auto)?ref\*?\{([^}]*)\}/g)].flatMap((m) => m[1].split(",").map(key)).filter((l) => l && !labels.has(l) && !/^vsSec\d+$/.test(l));
  if (unknown.length) {
    console.error(`${what}: the paper has no label ${unknown.map((l) => `"${l}"`).join(", ")} (the page would draw ??); use the label as \\label{…} writes it in the paper's TeX`);
    process.exit(65);
  }
};
const alive = (pid) => { try { process.kill(pid, 0); return true; } catch (e) { return e.code === "EPERM"; } };
/** A process's start time (Linux), so a reused PID is not taken for the session. */
const started = (pid) => { try { return readFileSync(`/proc/${pid}/stat`, "utf8").split(") ")[1].split(" ")[19]; } catch { return null; } };
/** A session on another machine of the shared mount: its pid means nothing here, so it lives while
 *  orch.json is fresh — an armed watcher touches it every minute, and a session between two watches
 *  has the heartbeat's allowance (the rule of `livenessOf`, src/shared/run_heartbeat.ts). */
const ELSEWHERE_STALE_MS = 30 * 60_000;
const sessionAlive = (o) => {
  if (!o?.pid) return false;
  if (o.host && o.host !== os.hostname()) { try { return Date.now() - statSync(ORCH).mtimeMs < ELSEWHERE_STALE_MS; } catch { return false; } }
  return alive(o.pid) && (o.started == null || started(o.pid) === o.started);
};

/**
 * The agent session this script runs under: the nearest ancestor that IS an agent harness — by its
 * program name (a `node` program by its script), never a shell whose command line merely mentions
 * one (a harness's tool shell sources files under `.claude/` and dies when its command returns).
 */
function session() {
  // a driver that is the session itself (`batch_orch.mjs`): it names itself
  const own = Number(process.env.THEOREMCHECKER_ORCH_SESSION_PID) || 0;
  if (own) return { agent: process.env.THEOREMCHECKER_ORCH_AGENT || "agent", pid: own, started: started(own), host: os.hostname() };
  let pid = process.ppid;
  for (let i = 0; i < 10 && pid > 1; i++) {
    let line = "";
    try { line = execFileSync("ps", ["-o", "ppid=,comm=,args=", "-p", String(pid)], { encoding: "utf8" }).trim(); } catch { break; }
    const m = /^(\d+)\s+(\S+)\s*(.*)$/.exec(line);
    if (!m) break;
    const prog = m[2] === "node" ? (m[3].split(/\s+/).find((a, k) => k > 0 && !a.startsWith("-")) ?? "") : m[2];
    const agent = /(^|\/)claude(-code)?(\.js|\.mjs)?$|@anthropic-ai\/claude-code/.test(prog) ? "Claude Code" : /(^|\/)codex(\.js)?$|@openai\/codex/.test(prog) ? "Codex" : null;
    if (agent) return { agent, pid, started: started(pid), host: os.hostname() };
    pid = Number(m[1]);
  }
  return { agent: "agent", pid: process.ppid, started: started(process.ppid), host: os.hostname() };
}

const real = (p) => { try { return realpathSync(p); } catch { return p; } };

/** The toolkit a process's `verify` runs on, as the CLI resolves it: `--toolkit`, else THEOREMCHECKER_TOOLKIT, else the nearest ancestor of its cwd holding theoremchecker.json. */
function toolkitOf(pid, argv) {
  let cwd;
  try { cwd = readlinkSync(`/proc/${pid}/cwd`); } catch { return null; }
  const k = argv.indexOf("--toolkit");
  let root = k >= 0 ? argv[k + 1] : undefined;
  if (!root) try { root = readFileSync(`/proc/${pid}/environ`, "utf8").split("\0").find((e) => e.startsWith("THEOREMCHECKER_TOOLKIT="))?.slice(23).trim() || undefined; } catch { /* not ours to read */ }
  if (root) return real(path.resolve(cwd, root));
  for (let d = cwd; ; d = path.dirname(d)) {
    if (existsSync(path.join(d, "theoremchecker.json"))) return real(d);
    if (path.dirname(d) === d) return null;
  }
}

/**
 * The run's runner is alive: its heartbeat's process, or (before it writes one) a `verify` process
 * for this slug ON THIS TOOLKIT — by its argv, so neither another toolkit's run of the same slug nor
 * a shell whose command line merely mentions one is taken for it. A heartbeat written on another
 * machine of the shared mount (`host=` token) is live while fresh — the runner refreshes it every
 * `beat=` seconds (5 min when it records none); its pid means nothing here.
 */
function runnerLive() {
  try {
    const hb = path.join(run, "logs", ".run.active");
    const fields = readFileSync(hb, "utf8").trim().split(/\s+/);
    const token = (key) => fields.find((f) => f.startsWith(`${key}=`))?.slice(key.length + 1);
    const host = token("host"), beat = Number(token("beat")), start = token("start");
    // (the rule of `heartbeatLiveness`, src/shared/run_heartbeat.ts: four missed beats and the mount's attribute cache)
    if (host && host !== os.hostname()) return Date.now() - statSync(hb).mtimeMs < (beat > 0 ? 4 * beat * 1000 + 30_000 : 30 * 60_000);
    const pid = Number(fields[0]);
    if (Number.isFinite(pid) && pid > 0 && alive(pid)) {
      let now = null;
      try { now = readFileSync(`/proc/${pid}/stat`, "utf8").split(") ").pop().split(" ")[19] ?? null; } catch { /* not Linux */ }
      if (!start || now === null || now === start) return true; // (else: the pid is another process's now)
    }
  } catch { /* no heartbeat yet */ }
  let pids;
  try { pids = readdirSync("/proc").filter((e) => /^\d+$/.test(e)); } catch {
    // no /proc (not Linux): the slug alone, by the command line
    try {
      const re = new RegExp(`theoremchecker\\.ts verify .*--slug ${slug.replace(/[.]/g, "\\.")}( |$)`);
      return execFileSync("ps", ["-eo", "args="], { encoding: "utf8" }).split("\n").some((l) => re.test(l));
    } catch { return false; }
  }
  const mine = real(path.resolve(toolkit));
  return pids.some((pid) => {
    let argv;
    try { argv = readFileSync(`/proc/${pid}/cmdline`, "utf8").split("\0"); } catch { return false; }
    const v = argv.findIndex((a, i) => /(^|\/)theoremchecker\.ts$/.test(a) && argv[i + 1] === "verify");
    const s = argv.indexOf("--slug", v);
    return v >= 0 && s > v && argv[s + 1] === slug && toolkitOf(pid, argv) === mine;
  });
}

/** What the run's state says it is halted on — the V-stage halts write no log line: each with whose
 *  it is. A render / contract checkpoint comes first: the runner answers it before it reads a ruling. */
function stateHalts() {
  const st = readJson(path.join(run, "state.json"), {});
  const v = st.verify ?? {};
  const out = [];
  // (a full-auto run: the owner delegated their decisions, and the last recommendation carries them out)
  const owners = (what) => st.full_auto === true ? `FULL AUTO, delegated to you: ${what}; the last recommendation carries them out` : `the USER's, on the page: ${what}, tell them, wait`;
  if (v.render_checkpoint) out.push(`a ${v.render_checkpoint.kind === "contract" ? "contract" : "render"} checkpoint (${(v.render_checkpoint.defects ?? []).length} block(s) of the annotated paper) — YOURS, a tool or model-text defect with no owner waiver; settle it first: no ruling is read while it stands (SKILL "Render checkpoint")`);
  const w = v.weakening_repair;
  if (w?.status === "pending") out.push(w.unconfirmed
    ? `suggested repair(s) of ${(w.items ?? []).map((i) => i.node).join(", ")} still being confirmed by V1.5 — resume plainly; nothing to decide yet`
    : `suggested repair(s) that weaken ${(w.items ?? []).map((i) => i.node).join(", ")} — ${owners("recommend on each (`orch.mjs recommend … repair`)")}`);
  if (v.cap_reached) out.push(`a patch cap (${v.cap_reached.counter}) — yours (SKILL "Patch caps")`);
  if (v.cross_stage_rewind?.status === "pending") out.push(v.cross_stage_rewind.presented
    ? `a proposed rewind from ${v.cross_stage_rewind.stage} — yours (SKILL "Rewinds are proposed")`
    : `a rewind from ${v.cross_stage_rewind.stage} not presented yet — resume plainly; nothing to rule on yet`);
  for (const [round, rec] of [["A", v.promotion_a], ["B", v.promotion]]) {
    if (rec?.status === "pending_user") out.push(`promotion round ${round} (results proposed for the toolkit) — ${owners(`recommend on each entry and new topic (\`orch.mjs recommend … ${round} <id> <kind>\`)`)}`);
  }
  return out;
}

/** The run's last events, first lines, without prompt sizes and paths. */
function lastEvents(n) {
  let lines = [];
  try { lines = readFileSync(path.join(run, "pipeline.jsonl"), "utf8").trim().split("\n").slice(-n); } catch { return []; }
  return lines.map((l) => { try { const e = JSON.parse(l); return `${e.stage} ${e.status}: ${String(e.message ?? "").split("\n")[0].slice(0, 240)}`; } catch { return ""; } }).filter(Boolean);
}

/** The round whose apply is at work (`proposals/apply_<R>.pid` names a live process), else null. */
function applyLive() {
  // (`<pid> host=<h> beat=<s>`: on another machine of the mount the file's freshness, as for the runner)
  return ["A", "B"].find((r) => {
    const file = path.join(run, "proposals", `apply_${r}.pid`);
    let fields;
    try { fields = readFileSync(file, "utf8").trim().split(/\s+/); } catch { return false; }
    const token = (key) => fields.find((f) => f.startsWith(`${key}=`))?.slice(key.length + 1);
    const host = token("host"), beat = Number(token("beat"));
    if (host && host !== os.hostname()) return Date.now() - statSync(file).mtimeMs < (beat > 0 ? 4 * beat * 1000 + 30_000 : 30 * 60_000);
    const pid = Number(fields[0]);
    return pid > 0 && alive(pid);
  }) ?? null;
}
/** The applies' own record: an apply writes its round's decisions first, a move it is half-way
 *  through, and — when it ends without applying the round — why (`apply_failed.json`). */
const applySig = () => ["A.decisions.json", "B.decisions.json", "move_pending.json", "apply_failed.json"].map((f) => { try { return statSync(path.join(run, "proposals", f)).mtimeMs; } catch { return 0; } }).join(":");
/** The round an apply left unfinished: decided since its batch was written, or a move half-way, and not recorded applied. */
function applyUnfinished(round) {
  const v = readJson(path.join(run, "state.json"), {}).verify ?? {};
  const open = (r) => (r === "A" ? v.promotion_a : v.promotion)?.status === "pending_user";
  // (`ui/run_model.ts` `roundDecided`: decisions on file, not older than the batch — no date counts as decided)
  const began = (r) => { const d = readJson(path.join(run, "proposals", `${r}.decisions.json`), null); return Boolean(d) && !(Date.parse(String(d.decided_at ?? "")) < Date.parse(String(readJson(path.join(run, "proposals", `${r}.json`), {})?.created ?? ""))); };
  return (round ? [round] : ["A", "B"]).find((r) => open(r) && (began(r) || existsSync(path.join(run, "proposals", "move_pending.json")))) ?? null;
}

/** The identity of a suggested repair (`ui/run_model.ts` `repairKey`): its node and proposed statement. */
const repairKey = (item) => createHash("sha256").update(`${item.node}\n${item.proposed ?? ""}`).digest("hex").slice(0, 16);
/** The identity of each item of a promotion batch, by decision key (`proposals/checklist.ts`
 *  `recommendationKeys`): an entry as the owner reads it, a new topic by its path and scope. */
const recommendationKeys = (batch) => {
  const h = (parts) => createHash("sha256").update(JSON.stringify(parts)).digest("hex").slice(0, 16);
  const out = new Map();
  for (const p of batch.proposals ?? []) out.set(p.id, h([p.id, p.content ?? "", p.proposed_name ?? "", p.target_module ?? "", p.path ?? "", p.division ?? ""]));
  const topics = new Map();
  for (const p of (batch.proposals ?? []).filter((x) => x.verdict === "propose" && x.new_topic)) if (!topics.has(p.new_topic.path)) topics.set(p.new_topic.path, p.new_topic.scope);
  for (const [t, scope] of topics) out.set(`topic:${t}`, h([t, scope ?? ""]));
  return out;
};

/**
 * A full-auto run (`verify --full-auto`; `state.full_auto`): the owner delegated their decisions. Once
 * every item of the decision waiting has a recommendation on it as it stands, the decision is carried
 * out as the page's "Accept all recommendations" would — the repairs by a resume with the rulings
 * recommended, a round by `propose --apply --recommended` — started detached here, and each repair (a
 * round as one entry) is listed for the owner's review (`orch_decisions.json`). Prints what it did.
 */
async function fullAutoApply(round) {
  const st = readJson(path.join(run, "state.json"), {});
  const v = st.verify ?? {};
  if (st.full_auto !== true) return;
  let argv, reviews;
  const dry = v.dry_run === true ? ["--dry-run"] : [];
  const tk = path.resolve(toolkit);
  if (round === "repair") {
    const pending = v.weakening_repair;
    if (pending?.status !== "pending" || pending.unconfirmed) return;
    const recs = readJson(path.join(run, "repair_recommendations.json"), {});
    // (an item already ruled on — a finding withdrawn by node — is no longer the receipt's to answer)
    const items = (pending.items ?? []).filter((i) => !pending.decisions?.[i.node]).map((i) => [i.node, recs[i.node]?.of === repairKey(i) ? recs[i.node] : null]);
    const open = items.filter(([, r]) => !r).map(([n]) => n);
    if (open.length) { console.log(`full auto: ${items.length - open.length} of ${items.length} repair(s) recommended; the last recommendation (${open.join(", ")}) resumes the run`); return; }
    const of = (k) => items.filter(([, r]) => r.kind === k);
    const accept = of("accept"), decline = of("decline"), redo = of("redo");
    argv = ["verify", "--toolkit", tk, "--slug", slug, "--resume", ...dry];
    if (accept.length) argv.push("--accept-repair", accept.map(([n]) => n).join(","));
    if (decline.length) argv.push("--decline-repair", `${decline.map(([n]) => n).join(",")}: ${decline.map(([n, r]) => decline.length > 1 ? `${n}: ${r.why}` : r.why).join("; ")}`);
    for (const [n, r] of redo) argv.push("--redo-repair", `${n}: ${r.guidance}`);
    reviews = items.map(([n, r]) => [n, `Full auto: ${r.kind === "redo" ? `redo, with the guidance "${r.guidance}"` : r.kind} the suggested repair, as recommended — ${r.why}`]);
  } else {
    const rec = round === "A" ? v.promotion_a : v.promotion;
    if (rec?.status !== "pending_user") return;
    const batch = readJson(path.join(run, "proposals", `${round}.json`), {});
    const keys = recommendationKeys(batch);
    const recs = readJson(path.join(run, "proposals", `${round}.recommendations.json`), {});
    const ids = [...(batch.proposals ?? []).filter((p) => p.verdict === "propose").map((p) => p.id), ...[...keys.keys()].filter((k) => k.startsWith("topic:"))];
    const open = ids.filter((k) => recs[k]?.of !== keys.get(k));
    if (open.length) { console.log(`full auto: ${ids.length - open.length} of ${ids.length} item(s) of round ${round} recommended; the last recommendation (${open.join(", ")}) applies the round`); return; }
    argv = ["propose", slug, "--round", round, "--apply", "--recommended", "--toolkit", tk, ...dry];
    const by = {};
    for (const k of ids) (by[recs[k].kind] ??= []).push(k);
    reviews = [[`round ${round}`, `Full auto: promotion round ${round} applied as recommended — ${Object.entries(by).map(([k, l]) => `${k.replace(/_/g, " ")}: ${l.join(", ")}`).join("; ")} (an entry the owner had decided keeps their decision)`]];
  }
  if (runnerLive() || applyLive()) { console.log(`full auto: every item is recommended, but the run is busy (a runner or an apply is at work): recommend again once it has stopped`); return; }
  // one start per decision: two recommendations completing it at once start it once
  const lock = path.join(run, "logs", ".full_auto.lock");
  mkdirSync(path.dirname(lock), { recursive: true });
  try { if (Date.now() - statSync(lock).mtimeMs > 10 * 60_000) rmSync(lock, { force: true }); } catch { /* none */ }
  try { closeSync(openSync(lock, "wx")); } catch { console.log("full auto: another recommendation is starting this decision already"); return; }
  const log = path.join(run, "logs", `full_auto_${new Date().toISOString().replace(/[:.]/g, "-")}.log`);
  let child;
  const fd = openSync(log, "a");
  try {
    const tools = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
    const tsx = createRequire(path.join(tools, "package.json")).resolve("tsx/cli");
    const cli = process.env.THEOREMCHECKER_ORCH_CLI ?? path.join(tools, "bin", "theoremchecker.ts");
    child = spawn(process.execPath, [tsx, cli, ...argv], { cwd: tools, detached: true, stdio: ["ignore", fd, fd], env: process.env });
  } finally { closeSync(fd); }
  // it counts as carried out once it is at work (or done): one refused at once is reported, not recorded
  let exited = null;
  child.on("exit", (code) => { exited = code ?? 1; });
  for (const until = Date.now() + Number(process.env.THEOREMCHECKER_FULL_AUTO_WAIT_MS ?? 60_000); exited === null && !runnerLive() && !applyLive() && Date.now() < until; ) await new Promise((r) => setTimeout(r, 300));
  child.unref();
  rmSync(lock, { force: true });
  if (exited !== null && exited !== 0) {
    console.error(`full auto: theoremchecker ${argv.join(" ")} failed (exit ${exited}) — nothing was carried out; read ${log}, settle what it says, and recommend again`);
    process.exit(1);
  }
  const all = readJson(DECISIONS, []);
  let n = Math.max(0, ...all.map((d) => num(d.id)));
  const ids = reviews.map(([node, text]) => { const id = `d${++n}`; all.push({ id, node, at: new Date().toISOString(), text }); return id; });
  writeJson(DECISIONS, all);
  console.log(`full auto: every item is recommended — started theoremchecker ${argv.join(" ")} (output: ${log}); listed for the owner's review as ${ids.join(", ")}`);
}

if (cmd === "watch") {
  const timeout = Number(opt("--timeout") ?? 0);
  const take = flag("--take");
  const starts = flag("--starts");
  // what the caller already reported and the owner has not yet answered (`orch_watch_loop.mjs`), each as
  // `<id>@<when the owner wrote it>` (an issue withdrawn and reported anew, or edited, is new): no return
  // for these alone — a further one returns with all of them. The keys a report names are written to
  // THEOREMCHECKER_ORCH_REPORTED when it is set.
  const known = new Set((opt("--known") ?? "").split(",").filter(Boolean));
  const keyOf = (x) => `${x.id}@${x.review?.at ?? x.at ?? ""}`;
  // armed by a loop (`orch_watch_loop.mjs`): once the loop is gone, nobody reads this watch — it ends
  // without handing anything over, so the next watch reports it
  const parent = Number(process.env.THEOREMCHECKER_ORCH_PARENT) || 0;
  const orphaned = () => parent > 0 && process.ppid !== parent;
  const me = session();
  const cur = readJson(ORCH, null);
  const sameSession = (o) => o?.pid === me.pid && (o.host ?? me.host) === me.host;
  if (cur && sessionAlive(cur) && !sameSession(cur) && !take) {
    console.error(`${slug} is attached to another live session (${cur.agent}, pid ${cur.pid}${cur.host && cur.host !== me.host ? ` on ${cur.host}` : ""}); --take to take it over`);
    process.exit(3);
  }
  // The run's log as this session last handed it over: a run that started and exited since — while
  // no watch was armed, or between two checks — moved the log, and is reported.
  const logSig = () => { try { const st = statSync(path.join(run, "pipeline.jsonl")); return `${st.mtimeMs}:${st.size}`; } catch { return "-"; } };
  const mine = sameSession(cur);
  const sig0 = (mine && cur.seen) || logSig();
  // The applies' record likewise: an apply has no heartbeat and writes no log line, so one that
  // began and ended since — failed part-way — shows only there.
  let apply0 = (mine && cur.seen_apply) || applySig();
  const attach = (seen, seenApply = apply0) => writeJson(ORCH, { ...me, attached_at: mine ? cur.attached_at : new Date().toISOString(), watcher: process.pid, seen, seen_apply: seenApply, ...(starts ? { starts: true } : {}) });
  // armed on a run at rest: it waits for the owner, whose resume on the page is news to this session;
  // taken before attaching, so a runner that starts once orch.json names this watcher is such news
  /** The page's list of formulas it could not draw, when it has entries: how many, the commonest error
   *  with one formula, and whether this list was already reported. */
  const mathFailures = () => {
    const file = path.join(run, "logs", "ui_math_failures.json"), toldFile = path.join(run, "logs", "ui_math_failures.told");
    let failures = [];
    try { failures = JSON.parse(readFileSync(file, "utf8")).failures ?? []; } catch { return null; }
    if (!failures.length) return null;
    const by = new Map();
    for (const f of failures) by.set(f.error ?? "?", [...(by.get(f.error ?? "?") ?? []), f]);
    const [err, of] = [...by.entries()].sort((a, b) => b[1].length - a[1].length)[0];
    const sig = createHash("sha256").update(failures.map((f) => f.tex).join("\u0000")).digest("hex");
    let told = "";
    try { told = readFileSync(toldFile, "utf8"); } catch { /* not told yet */ }
    return { n: failures.length, top: `${of.length} with "${err}", e.g. ${String(of[0].tex).replace(/\s+/g, " ").slice(0, 120)}`, sig, told, file, toldFile };
  };
  /** The page's list of what else it could not draw (unknown commands and environments, figure files not
   *  found, drawings left out, the TikZ compile's error, unresolved references), when it has entries: a
   *  one-line summary, and whether this list was already reported. */
  const renderProblems = () => {
    const file = path.join(run, "logs", "ui_render_problems.json"), toldFile = path.join(run, "logs", "ui_render_problems.told");
    let p;
    try { p = JSON.parse(readFileSync(file, "utf8")); } catch { return null; }
    const top = (o) => Object.entries(o ?? {}).sort((a, b) => b[1] - a[1]).slice(0, 6).map(([k, n]) => `\\${k} ×${n}`).join(", ");
    const parts = [
      Object.keys(p.unknownCommands ?? {}).length ? `commands it does not read (their arguments shown as text): ${top(p.unknownCommands)}` : "",
      Object.keys(p.unknownEnvironments ?? {}).length ? `environments it does not read: ${Object.keys(p.unknownEnvironments).join(", ")}` : "",
      p.missingFigures?.length ? `figure files not found: ${p.missingFigures.slice(0, 5).join(", ")}` : "",
      p.omittedDrawings ? `${p.omittedDrawings} drawing(s) left out` : "",
      p.tikz ? `the TikZ pictures were not typeset (${String(p.tikz).slice(0, 200)})` : "",
      p.unresolvedRefs?.length ? `${p.unresolvedRefs.length} reference(s) the page cannot resolve: ${p.unresolvedRefs.slice(0, 5).join(", ")}` : "",
      p.unnamedResults?.length ? `${p.unnamedResults.length} result(s) the page names by no environment (drawn by their kind or "?" on the proof map; often an anchor at the wrong line): ${p.unnamedResults.slice(0, 5).join(", ")}` : "",
    ].filter(Boolean);
    if (!parts.length) return null;
    const sig = createHash("sha256").update(JSON.stringify(p)).digest("hex");
    let told = "";
    try { told = readFileSync(toldFile, "utf8"); } catch { /* not told yet */ }
    return { summary: parts.join("; "), sig, told, file, toldFile };
  };
  /** A finished run's bundle with blocking items in its TODO.md (`bundle/bundle.json` todo.blocking):
   *  how many, and whether this bundle was already reported. */
  const blockingTodo = () => {
    const file = path.join(run, "bundle", "bundle.json"), toldFile = path.join(run, "logs", "bundle_todo.told");
    // only a finished run (run_model.ts `reportCurrent`: one rewound still has an older bundle), and
    // not at a halt of its own, which comes first (a promotion round waiting for the user does not)
    const st = readJson(path.join(run, "state.json"), {});
    const finished = st.stage_completed === "V6" || ["done", "failed", "proposals_B"].includes(st.verify?.phase ?? "");
    if (!finished || stateHalts().some((h) => !h.startsWith("promotion round"))) return null;
    let text = "";
    try { text = readFileSync(file, "utf8"); } catch { return null; }
    let n = 0;
    try { n = Number(JSON.parse(text).todo?.blocking) || 0; } catch { return null; }
    if (n <= 0) return null;
    let told = "";
    try { told = readFileSync(toldFile, "utf8"); } catch { /* not told yet */ }
    return { n, sig: createHash("sha256").update(text).digest("hex"), told, toldFile };
  };
  const atRest = !runnerLive();
  let sawLive = !atRest;
  let sawApply = null;
  attach(sig0);
  const t0 = Date.now();
  // `seen`: the run's log is handed over (a runner's exit); a rejected ruling hands over nothing else
  const report = (why, seen = true) => {
    if (orphaned()) process.exit(0);
    if (seen) attach(logSig(), applySig());
    console.log(`[orch] ${slug}: ${why}`);
    if (!runnerLive()) for (const l of stateHalts()) console.log(`  halted on: ${l}`);
    for (const l of lastEvents(8)) console.log(`  ${l}`);
    process.exit(0);
  };
  let beat = Date.now();
  const tick = () => {
    if (orphaned()) process.exit(0);
    // the beat a session on another machine is read by (`sessionAlive`)
    if (Date.now() - beat > 60_000) { beat = Date.now(); try { utimesSync(ORCH, new Date(), new Date()); } catch { /* replaced: the next attach writes it */ } }
    const rejected = readJson(DECISIONS, []).filter((d) => d.review?.verdict === "reject" && !d.review.handled);
    const objected = readJson(OBJECTIONS, []).filter((o) => o.text && !o.handled);
    // (looked at first, and from no other state of the run: live, halted or finished, a message is heard)
    let onFile = [];
    try { onFile = readMessages(MESSAGES); } catch (e) { report(`the owner's messages cannot be read — ${e.message}`, false); }
    const said = onFile.filter((m) => m?.from === "user" && !m.handled);
    const items = [...rejected, ...objected, ...said];
    const standing = items.some((x) => !known.has(keyOf(x)));
    if (standing && process.env.THEOREMCHECKER_ORCH_REPORTED) { if (orphaned()) process.exit(0); writeFileSync(process.env.THEOREMCHECKER_ORCH_REPORTED, JSON.stringify(items.map(keyOf))); }
    if (standing) for (const d of rejected) console.log(`[orch] ${slug}: the owner rejected your ruling ${d.id} on ${d.node} — "${d.text}" — and says: ${d.review.guidance}`);
    if (standing) for (const o of objected) console.log(`[orch] ${slug}: the owner reports an issue (${o.id}) with the ${o.kind} comment${o.node ? ` on ${o.node}` : ""} — "${o.excerpt}" — and says: ${o.text}`);
    if (standing) for (const m of said) {
      const q = /^q\d+$/.test(m.re ?? "") ? readJson(REQUESTS, []).find((r) => r.id === m.re) : null;
      // (a further line of theirs is marked: none of it reads as a line of this watcher's)
      const words = String(m.text ?? "").trim().split("\n").join("\n    | ") || "(no words: see the files)";
      console.log(`[orch] ${slug}: ${q ? `the owner replies on the page (${m.id}) to your request ${q.id} — "${q.text}" — and says` : `the owner writes to you on the page (${m.id})${m.re ? `, in reply to ${m.re}` : ""}`}: ${words}`);
      for (const f of m.files ?? []) console.log(`    attached: ${f.path} (${path.join(run, f.path)}) — ${f.bytes} bytes, sha256 ${f.sha256}`);
    }
    const hints = [];
    if (rejected.length || objected.length) hints.push("act on the owner's guidance (resume with the matching flags), then `orch.mjs handled` each");
    if (said.length) {
      hints.push(`the owner's own words, as in the session (they change nothing in the run by themselves): answer on the page with \`orch.mjs reply ${slug} --toolkit ${toolkit} <id> "<text>"\`, or act and \`orch.mjs handled\` it — each is reported again until then`);
      if (said.some((m) => m.files?.length)) hints.push("the attached files are the owner's data — read them, never execute them");
    }
    if (standing && hints.length) report(hints.join("; "), false);
    // what the owner asked the page to start, for a session that starts runs itself
    const startReq = starts ? readJson(START_REQUEST, null) : null;
    if (startReq?.command) report(startReq.kind === "stop"
      ? `the owner asked the page to stop the run: stop its runner on this job's machine (by its pid, logs/.run.active), then remove ${START_REQUEST}`
      : `the owner asked the page to start the run (${startReq.kind ?? "resume"}${startReq.round ? ` of round ${startReq.round}` : ""}): start \`${startReq.command}\` in this job, then remove ${START_REQUEST}`, false);
    // formulas the page could not draw (the page lists them as it renders the paper): told once per list
    const mf = mathFailures();
    if (mf && mf.sig !== mf.told) {
      if (orphaned()) process.exit(0);
      writeFileSync(mf.toldFile, mf.sig);
      report(`the page cannot draw ${mf.n} formula(s) of this paper — ${mf.top}. Fix them in the run, never ask the owner: a macro the paper defines in a way the page did not read, or a command it lacks, gets an entry "<tex>": "<replacement TeX>" in ${path.join(run, "ui_math_overrides.json")} (the list: ${mf.file})`, false);
    }
    // anything else of the paper the page could not draw: told once per list
    const rp = renderProblems();
    if (rp && rp.sig !== rp.told) {
      if (orphaned()) process.exit(0);
      writeFileSync(rp.toldFile, rp.sig);
      report(`the page cannot draw parts of this paper — ${rp.summary}. Fix them in the run (its source copy) or, for a renderer gap, with a test; never ask the owner (the list: ${rp.file})`, false);
    }
    const live = runnerLive();
    // a finished run whose bundle still has blocking TODO items: told once per bundle written
    const todo = live ? null : blockingTodo();
    if (todo && todo.sig !== todo.told) {
      if (orphaned()) process.exit(0);
      writeFileSync(todo.toldFile, todo.sig);
      report(`the run's bundle has ${todo.n} blocking item(s) in bundle/corrected_paper/TODO.md — settle each before the run counts as finished: what the pipeline caused, in the run's files, then \`theoremchecker report ${slug}\`; what is the author's own TeX, tell the owner (skill: "V6 and the promotion rounds")`, false);
    }
    if (live && atRest && !sawLive) report(`the run is running again (resumed on the page, or by a session)${parent ? "" : " — arm the watcher again to follow it"}`, false);
    if (live) sawLive = true;
    else if (sawLive || logSig() !== sig0) report("the runner exited — act on the halt or finish");
    // An apply that ended: completed, it resumes the run in its own process (a runner follows);
    // not completed, nothing follows it — the round is this session's to settle.
    const applying = applyLive();
    if (applying) sawApply = applying;
    else if (!live && (sawApply || applySig() !== apply0)) {
      const round = applyUnfinished(sawApply);
      // (a failure older than the batch on file is an earlier round's: `ui/run_model.ts` `applyRefusal`)
      const failedOnFile = readJson(path.join(run, "proposals", "apply_failed.json"), null);
      const batchOf = failedOnFile?.round ?? sawApply ?? "B";
      const failed = failedOnFile && !(Date.parse(failedOnFile.at ?? "") < Date.parse(readJson(path.join(run, "proposals", `${batchOf}.json`), {}).created ?? "")) ? failedOnFile : null;
      const said = failed?.message ? `\n  it said: ${String(failed.message).split("\n").join("\n  ")}` : "";
      if (round) report(`the apply of promotion round ${round} ended without completing it — read its output (the latest runs/${slug}/logs/ui_*.log, or your own log of it) and proposals/move_pending.json, settle what it names, then apply the round again (\`theoremchecker propose ${slug} --round ${round} --apply --toolkit ${toolkit}\`)${said}`);
      // refused before a decision was recorded: nothing entered the toolkit, the round still waits
      if (failed?.message) report(`the apply of promotion round ${failed.round ?? sawApply ?? ""} was refused and nothing was applied — the page shows the user why; when it is theirs to answer (an entry still undecided), tell them, else settle what it names and have the round applied again${said}`);
      sawApply = null;
      apply0 = applySig();
    }
    if (timeout && Date.now() - t0 > timeout * 1000) { console.log(`[orch] ${slug}: nothing to act on yet (${live ? "running" : "waiting for the owner"})`); process.exit(2); }
    setTimeout(tick, Number(process.env.THEOREMCHECKER_ORCH_TICK_MS) || (timeout ? Math.min(10_000, timeout * 1000) : 10_000));
  };
  tick();
} else if (cmd === "decided") {
  const [node, ...words] = rest;
  const text = words.join(" ").trim();
  if (!node || !text) { console.error("decided: <node> \"<what you decided and why>\""); process.exit(64); }
  texOrExit("decided", text);
  const all = readJson(DECISIONS, []);
  const id = `d${1 + Math.max(0, ...all.map((d) => Number(String(d.id).slice(1)) || 0))}`;
  all.push({ id, node, at: new Date().toISOString(), text });
  writeJson(DECISIONS, all);
  console.log(id);
} else if (cmd === "handled") {
  const issue = String(rest[0]).startsWith("obj-"), message = /^m\d+$/.test(rest[0] ?? "");
  if (message) {
    const found = updateMessages(MESSAGES, (all) => { const m = all.find((x) => x.id === rest[0] && x.from === "user"); if (m) m.handled = true; return Boolean(m); });
    if (!found) { console.error(`handled: no message of the owner's ${rest[0]}`); process.exit(65); }
    process.exit(0);
  }
  const all = readJson(issue ? OBJECTIONS : DECISIONS, []);
  const d = all.find((x) => x.id === rest[0]);
  if (issue ? !d : !d?.review) { console.error(`handled: no ${issue ? "reported issue" : "reviewed ruling"} ${rest[0] ?? ""}`); process.exit(65); }
  if (issue) d.handled = true; else d.review.handled = true;
  writeJson(issue ? OBJECTIONS : DECISIONS, all);
} else if (cmd === "ask") {
  const ownerOnly = flag("--owner-only");
  const text = rest.join(" ").trim();
  if (!text) { console.error("ask: the request text"); process.exit(64); }
  if (readJson(path.join(run, "state.json"), {}).full_auto === true && !ownerOnly) {
    console.error(`ask: ${slug} runs in full auto — the owner delegated their rulings, nobody is asked. Make this one yourself (re-derive it against the paper's tex), enter it with its lever, and record it for their review: \`orch.mjs decided ${slug} --toolkit ${toolkit} <node> "Full auto: <the ruling and why>"\`. Only what the owner alone can give (a cited source you cannot access, the workers' sandbox) is asked: \`ask --owner-only\`.`);
    process.exit(65);
  }
  texOrExit("ask", text);
  const reqs = readJson(REQUESTS, []);
  // (past the requests the page's conversation still names: a cleared one's id is not given again)
  const id = `q${1 + Math.max(0, ...reqs.map((r) => num(r.id)), ...readMessages(MESSAGES).map((m) => /^q\d+$/.test(m?.re ?? "") ? num(m.re) : 0))}`;
  reqs.push({ id, at: new Date().toISOString(), text });
  writeJson(REQUESTS, reqs);
  console.log(id);
} else if (cmd === "reply") {
  // a first word shaped like an id is one (never the text): it names a message or a request, or nothing is said
  const re = /^(m|q|obj)-?\d+$/i.test(rest[0] ?? "") ? rest.shift() : undefined;
  const text = rest.join(" ").trim();
  if (!text) { console.error("reply: [<m<n>|q<n>>] \"<text>\""); process.exit(64); }
  texOrExit("reply", text);
  const id = updateMessages(MESSAGES, (all) => {
    // what it answers: the owner's message, or everything they said on the request
    const answered = all.filter((m) => m.from === "user" && (m.id === re || (re?.startsWith("q") && m.re === re)));
    if (re && !answered.length && !(re.startsWith("q") && readJson(REQUESTS, []).some((r) => r.id === re))) return false;
    for (const m of answered) m.handled = true;
    const id = nextMessageId(MESSAGES, all);
    all.push({ id, from: "agent", text, at: new Date().toISOString(), ...(re ? { re } : {}) });
    return id;
  });
  if (!id) { console.error(`reply: no message of the owner's or request ${re}`); process.exit(65); }
  console.log(id);
} else if (cmd === "recommend") {
  const g = rest.indexOf("--guidance");
  const guidance = g >= 0 ? (rest.splice(g, 2)[1] ?? "").trim() : "";
  const [round, id, kind, ...why] = rest;
  const kinds = round === "repair" ? ["accept", "decline", "redo"] : String(id).startsWith("topic:") ? ["accept", "decline"] : ["accept", "accept_with_edits", "generalize_first", "defer", "decline"];
  if (!["A", "B", "repair"].includes(round) || !id || !kinds.includes(kind) || !why.join(" ").trim()) { console.error(`recommend: <A|B> <proposal id> <${kinds.join("|")}> "<why>"  |  <A|B> topic:<path> <accept|decline> "<why>"  |  repair <node> <accept|decline|redo> "<why>"`); process.exit(64); }
  if (round === "repair" && kind === "redo" && !guidance) { console.error(`recommend: a redo needs --guidance "<what you would tell the fixer>" (the page offers it to the user as the text of their redo)`); process.exit(64); }
  texOrExit("recommend", why.join(" "));
  texOrExit("recommend --guidance", guidance);
  const file = round === "repair" ? path.join(run, "repair_recommendations.json") : path.join(run, "proposals", `${round}.recommendations.json`);
  // A recommendation is on ONE proposal: the repair pending on the node now, an item of the batch
  // on file (`of`: the hash of what it proposes — the page shows it beside that proposal only).
  let of;
  let keys = null;
  if (round === "repair") {
    const pending = readJson(path.join(run, "state.json"), {}).verify?.weakening_repair;
    const item = pending?.status === "pending" ? (pending.items ?? []).find((i) => i.node === id) : null;
    if (!item) { console.error(`recommend: no suggested repair is pending on ${id} (pending: ${(pending?.status === "pending" ? pending.items ?? [] : []).map((i) => i.node).join(", ") || "none"})`); process.exit(65); }
    of = repairKey(item);
  } else {
    keys = recommendationKeys(readJson(path.join(run, "proposals", `${round}.json`), {}));
    if (!keys.has(id)) { console.error(`recommend: ${id} is no entry or new topic of the round-${round} batch on file (items: ${[...keys.keys()].join(", ") || "none"})`); process.exit(65); }
    of = keys.get(id);
  }
  // (recommendations on proposals that are no longer the ones on file are dropped as the file is written)
  const kept = round === "repair" ? Object.fromEntries(Object.entries(readJson(file, {})).filter(([n, r]) => { const it = (readJson(path.join(run, "state.json"), {}).verify?.weakening_repair?.items ?? []).find((i) => i.node === n); return it && r.of === repairKey(it); })) : Object.fromEntries(Object.entries(readJson(file, {})).filter(([k, r]) => r.of === keys.get(k)));
  writeJson(file, { ...kept, [id]: { kind, why: why.join(" ").trim(), ...(guidance ? { guidance } : {}), ...(of ? { of } : {}), at: new Date().toISOString() } });
  await fullAutoApply(round);
} else if (cmd === "done") {
  const id = rest[0];
  const reqs = readJson(REQUESTS, []).filter((r) => id && r.id !== id);
  if (reqs.length) writeJson(REQUESTS, reqs); else rmSync(REQUESTS, { force: true });
  // the owner's replies to the request cleared are acted on — to that one alone; with no id, to any
  updateMessages(MESSAGES, (all) => {
    const open = all.filter((m) => m.from === "user" && !m.handled && (id ? m.re === id : /^q\d+$/.test(m.re ?? "")));
    for (const m of open) m.handled = true;
    return open.length > 0;
  });
} else if (cmd === "detach") {
  const cur = readJson(ORCH, null);
  const me = session();
  const mine = cur && cur.pid === me.pid && (cur.host ?? me.host) === me.host;
  if (mine) rmSync(ORCH, { force: true });
  console.log(mine ? `detached from ${slug}` : `nothing to detach: this session is not attached to ${slug}`);
} else { console.error(usage); process.exit(64); }
