#!/usr/bin/env node
// Orchestrate verify runs with no interactive session (on a server, or inside a scheduler's batch job).
//
//   node tools/scripts/batch_orch.mjs --toolkit <path> [--queue <file>] [--runs <n>] [--hours <h>]
//       [--batch] [--grace-min <m>] [--brief <file>] [--sandbox <mode>] [--model <m>] [--effort <e>] [--max-agents <n>] [<slug>[=<source>[::<main>]] …]
//
// The driver is the session attached to each run it follows (`orch.mjs watch --starts`; the page shows
// it). For each run it keeps a watch armed and, at each event (a halt, a finish, a message of the owner, a
// list of what the page cannot draw …), gives the event to the run's Codex conversation (`codex exec`, then
// `codex exec resume`, started afresh every 15 events); the agent acts as the skill says (rules, resumes
// detached, answers the owner on the page) and ends its turn, so nothing spends tokens between events. An
// event whose agent call fails is given once more, to a fresh conversation. What the owner asks the page to
// start or stop (a resume, their rulings, the apply of a round) the page leaves in
// runs/<slug>/start_request.json: the driver checks it against the run and carries it out here, in this job.
// Runs to follow: the slugs given, then entries taken from --queue (one per line, `<slug>` or
// `<slug>=<source>[::<main file>]`, `#` comments; taken under a lock, so several jobs share one queue),
// keeping --runs of them (default 3) at work — a run waiting for the owner does not count; with --batch, the
// first --runs taken are seen through and no other is taken, and the job ends when they finish. A run with no
// state yet and a <source> is launched first. A run that finishes (phase done or failed) is left once nothing is
// left to it: no runner beats, its agent asks the owner nothing (a request open on the page — the agent is
// reminded once per job to clear one whose answers it acted on), every message of theirs is acted on, and a short
// watch after the agent's last turn finds nothing more (the blocking items of its bundle's TODO.md are told again
// to the agent of a job that attaches to it finished); until then it waits for the owner like a halted run, and is
// put back at the job's end. A run another live job holds is left to it (after 35 min, the time a dead job's
// record takes to lapse). When --hours is
// nearly spent (--grace-min before it, default 20), or the job is signalled, the driver stops its agents and
// the runners it reaches on this machine (SIGTERM: each stops its own workers), puts the unfinished runs
// back at the head of the queue, detaches and exits 75 — a job script may submit the next job on it;
// it exits 0 when nothing is left. A spent Codex account (an agent's error: its usage
// limit, a plan without the model, or three rate-limit errors within an hour) stops the job the same way
// but exits 76: no successor, and the reason is appended to <queue>.stopped. The agents and runs get this
// job's environment: CODEX_HOME is the account the job bills. --brief: a file of the owner's standing
// instructions, given to every agent. Logs: runs/<slug>/logs/batch_*, and this driver's own output.
import { spawn } from "node:child_process";
import { appendFileSync, closeSync, existsSync, mkdirSync, mkdtempSync, openSync, readFileSync, renameSync, rmSync, statSync, utimesSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { readMessages } from "./messages_store.mjs";

const args = process.argv.slice(2);
const opt = (name, dflt) => { const i = args.indexOf(name); return i >= 0 ? args.splice(i, 2)[1] : dflt; };
const toolkitArg = opt("--toolkit");
const hours = Number(opt("--hours", "0"));
const graceMin = Number(opt("--grace-min", "20"));
const briefFile = opt("--brief");
const maxAgents = Math.max(1, Number(opt("--max-agents", "2")) || 2);
const queueFile = opt("--queue");
const keep = Math.max(1, Number(opt("--runs", "3")) || 3);
// --batch: take --runs runs once and see them through, then end (the next job takes the next batch);
// without it, a finished run is replaced from the queue at once
const batchMode = args.includes("--batch") ? (args.splice(args.indexOf("--batch"), 1), true) : false;
// --full-auto: the runs this job starts are started in full auto (`verify --full-auto`): the owner's
// decisions take the agents' recommendations (a run started before keeps its own mode)
const fullAuto = args.includes("--full-auto") ? (args.splice(args.indexOf("--full-auto"), 1), true) : false;
const TOOLS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const REPO = path.dirname(TOOLS);
const localSandbox = (() => { try { return JSON.parse(readFileSync(path.join(TOOLS, "config", "local.json"), "utf8")).codexSandbox; } catch { return undefined; } })();
const sandbox = opt("--sandbox", localSandbox ?? "workspace-write");
// the orchestrating agent's model: the pipeline's own judging tier unless given (`src/models.ts`)
const model = opt("--model", process.env.THEOREMCHECKER_MODEL_CODEX_VERIFY || "gpt-6.1-sol");
const effort = opt("--effort", "high");
if (!toolkitArg || (args.length === 0 && !queueFile) || args.some((a) => a.startsWith("--"))) {
  console.error("usage: batch_orch.mjs --toolkit <path> [--queue <file>] [--runs <n>] [--batch] [--full-auto] [--hours <h>] [--grace-min <m>] [--brief <file>] [--sandbox <mode>] [--model <m>] [--effort <e>] [--max-agents <n>] [<slug>[=<source>[::<main>]] …]");
  process.exit(64);
}
const toolkit = path.resolve(toolkitArg);
const log = (line) => console.log(`[batch ${new Date().toISOString().slice(11, 19)}] ${line}`);
/** One entry, `<slug>` or `<slug>=<source>[::<main file>]`; null when it names no run. */
const entryOf = (line) => {
  const [slug, rest] = line.trim().split(/=(.*)/s);
  const [source, main] = (rest ?? "").split("::");
  return /^[A-Za-z0-9][A-Za-z0-9_.-]{0,120}$/.test(slug) ? { slug, source: source || null, main: main || null } : null;
};
const lineOf = (e) => (e.source ? `${e.slug}=${e.source}${e.main ? `::${e.main}` : ""}` : e.slug);
const given = args.map((a) => entryOf(a) ?? (console.error(`not a run: ${a}`), process.exit(64)));
let brief = "";
if (briefFile) { try { brief = readFileSync(briefFile, "utf8").trim(); } catch (e) { log(`--brief ${briefFile} not read (${e.code ?? e.message}): the agents get no standing instructions`); } }
const deadline = hours > 0 ? Date.now() + hours * 3_600_000 - graceMin * 60_000 : Infinity;
const ORCH = path.join(TOOLS, "scripts", "orch.mjs");
const CLI = path.join(TOOLS, "bin", "theoremchecker.ts");
const runDir = (slug) => path.join(toolkit, "runs", slug);
const stamp = () => new Date().toISOString().replace(/[:.]/g, "-");
const readJson = (f) => { try { return JSON.parse(readFileSync(f, "utf8")); } catch { return null; } };
const sleep = (ms) => new Promise((r) => setTimeout(r, Math.max(0, Math.min(ms, deadline - Date.now()))));
const phaseOf = (slug) => readJson(path.join(runDir(slug), "state.json"))?.verify?.phase ?? null;
const finished = (slug) => ["done", "failed"].includes(phaseOf(slug) ?? "");
/** The agent's requests open on the page (orch_requests.json: until `orch.mjs done` or the page's dismiss). */
const requestsOf = (slug) => { const r = readJson(path.join(runDir(slug), "orch_requests.json")); return Array.isArray(r) ? r.filter((q) => q?.text) : []; };
/** The page's conversation; null when the store cannot be read (`messages_store.mjs`: never read as empty). */
const messagesOf = (slug) => { try { return readMessages(path.join(runDir(slug), "orch_messages.json")); } catch { return null; } };
/** A run whose agent still asks the owner something, or whose owner wrote what nobody has acted on (a store that
 *  cannot be read may hold such words: the watch says so at each arm): the conversation is not over though the run
 *  may be finished, so it is still followed (as waiting for the owner) and put back at the job's end. */
const awaitsOwner = (slug) => { const said = messagesOf(slug); return requestsOf(slug).length > 0 || said === null || said.some((m) => m?.from === "user" && !m.handled); };
/** Open requests the owner answered, every answer acted on: settled, maybe, and not cleared — a request the agent
 *  forgot to `done` would keep a finished run followed, job after job. */
const answeredRequests = (slug) => {
  const said = messagesOf(slug) ?? [];
  return requestsOf(slug).filter((q) => { const re = said.filter((m) => m?.from === "user" && m.re === q.id); return re.length > 0 && re.every((m) => m.handled); }).map((q) => q.id);
};
/** Runs whose last watch in this job found nothing to act on (exit 2). */
const quiet = new Set();
/** Finished, no runner beats (a resume the agent started may not have moved the phase yet), nobody waits on
 *  anybody, and the last watch found nothing left to act on (a blocking item of the bundle's TODO.md, a message, a
 *  start request): the run is left, and not put back. */
const settled = (slug) => finished(slug) && !runnerHere(slug) && !awaitsOwner(slug) && quiet.has(slug);
/** The run's runner on this machine, by its heartbeat (`logs/.run.active`): its pid, when it beats here. */
const runnerHere = (slug) => {
  const hb = path.join(runDir(slug), "logs", ".run.active");
  try {
    const fields = readFileSync(hb, "utf8").trim().split(/\s+/);
    const tok = (k) => fields.find((f) => f.startsWith(`${k}=`))?.slice(k.length + 1);
    const beat = Number(tok("beat")) || 300;
    if (Date.now() - statSync(hb).mtimeMs > 4 * beat * 1000 + 30_000) return null;
    return { pid: Number(fields[0]), here: tok("host") === os.hostname() };
  } catch { return null; }
};

/** The runs this job took; those of them now waiting for the owner; the one Codex conversation each keeps. */
const followed = [];
const waitingOwner = new Set();
const active = new Map();
/** Runs not put back as the job ends (no run, or another live job holds it); runs given but not yet taken. */
const held = new Set();
const pending = [...given];
// every watch names this driver as the session (`orch.mjs` `session`); the agents and the runs get this job's
// own environment (CODEX_HOME, the account the job bills): a watch an agent arms anyway is another session's
const sessionEnv = { ...process.env, THEOREMCHECKER_ORCH_SESSION_PID: String(process.pid), THEOREMCHECKER_ORCH_AGENT: `batch job ${process.env.SLURM_JOB_ID ?? os.hostname()}`, THEOREMCHECKER_ORCH_PARENT: String(process.pid) };
let stopReason = null;

/** `theoremchecker <argv>` started detached in this job, its output in the run's logs. */
function startCli(slug, argv, what) {
  const file = path.join(runDir(slug), "logs", `batch_${what}_${stamp()}.log`);
  mkdirSync(path.dirname(file), { recursive: true });
  const fd = openSync(file, "a");
  try {
    const child = spawn(path.join(TOOLS, "node_modules", ".bin", "tsx"), [CLI, ...argv], { cwd: TOOLS, detached: true, stdio: ["ignore", fd, fd], env: process.env });
    child.on("error", (e) => log(`${slug}: ${what} could not start: ${e.message}`));
    child.unref();
    log(`${slug}: started ${what} (pid ${child.pid}) — log ${file}`);
  } finally { closeSync(fd); }
}

// ─── what the owner asked the page to start ──────────────────────────────────────
const RULING_FLAGS = new Set(["--accept-repair", "--decline-repair", "--redo-repair", "--edit-reading", "--remove-reading"]);
/** The request is one the page makes for this run (`ui/actions.ts` `buildArgv`): its own source, toolkit and
 *  slug, `--resume` and the owner's ruling flags, or the apply of a round. Nothing else is carried out. */
function validStart(slug, req) {
  if (req?.kind === "stop") return true;
  const a = req?.argv;
  if (!Array.isArray(a) || !a.every((x) => typeof x === "string")) return false;
  if (a[0] === "propose") return a.length === 7 && a[1] === slug && a[2] === "--round" && ["A", "B"].includes(a[3]) && a[4] === "--apply" && a[5] === "--toolkit" && path.resolve(a[6]) === toolkit;
  const source = readJson(path.join(runDir(slug), "state.json"))?.verify?.source?.input;
  if (a[0] !== "verify" || a[1] !== source || a[2] !== "--toolkit" || path.resolve(a[3] ?? "") !== toolkit || a[4] !== "--slug" || a[5] !== slug || a[6] !== "--resume") return false;
  for (let i = 7; i < a.length; i += 2) if (!RULING_FLAGS.has(a[i]) || a[i + 1] === undefined) return false;
  return true;
}
/** Carry out a request on file; whether there was one. */
function takeStartRequest(slug) {
  const file = path.join(runDir(slug), "start_request.json");
  if (!existsSync(file)) return false;
  const req = readJson(file);
  rmSync(file, { force: true });
  if (!validStart(slug, req)) { log(`${slug}: start request not taken (not one the page makes for this run): ${JSON.stringify(req).slice(0, 300)}`); return true; }
  const runner = runnerHere(slug);
  if (req.kind === "stop") {
    if (runner?.here && runner.pid > 0) { try { process.kill(runner.pid, "SIGTERM"); log(`${slug}: runner ${runner.pid} stopped, as the owner asked`); } catch { /* gone */ } }
    else log(`${slug}: stop asked, but no runner of it beats on this machine`);
    return true;
  }
  if (runner) { log(`${slug}: start request not taken: the run is running`); return true; }
  startCli(slug, req.argv, req.kind === "apply-promotion" ? `apply_${req.argv[3]}` : "resume");
  return true;
}

// ─── agents: one conversation per run, at most --max-agents at once ─────────────
const prompt = (slug, event) => [
  `You are the orchestrating agent of the TheoremChecker run \`${slug}\` (toolkit ${toolkit}), called by a driver script inside a batch job. Read ${path.join(REPO, "AGENTS.md")} and ${path.join(REPO, ".claude", "skills", "theoremchecker", "SKILL.md")} and follow them, with these differences of this mode:`,
  `- The driver watches the run and calls you once per event (below). Act on it as the skill says, then end your turn with one line saying what you did. Do not run \`orch.mjs watch\` or \`orch_watch_loop.mjs\`, do not wait for the run, and start no UI: the driver calls you again at the next event.`,
  `- Start a run detached, so that it outlives your turn — a resume (with your ruling's flags): \`cd ${TOOLS} && source scripts/node_env.sh && setsid nohup npx tsx bin/theoremchecker.ts verify ${readJson(path.join(runDir(slug), "state.json"))?.verify?.source?.input ?? "<the run's source: verify.source.input in its state.json>"} --toolkit ${toolkit} --slug ${slug} --resume [flags] > ${path.join(runDir(slug), "logs")}/batch_agent_<time>.log 2>&1 < /dev/null &\`; an apply: the same with \`propose ${slug} --round <A|B> --apply --toolkit ${toolkit}\`. A minute later check that it started (a resume: \`${path.join(runDir(slug), "logs", ".run.active")}\` is fresh; an apply: its log), and fix and relaunch it if not. The environment of this job (CODEX_HOME and the rest) is inherited.`,
  `- Act on this run only; stop a process only by its PID.`,
  `- Talk to the owner on the paper's page (\`orch.mjs reply | ask | recommend | decided | handled\`, as the skill says); nobody reads this session.`,
  ...(brief ? ["", "The owner's standing instructions:", brief] : []),
  "", "The event:", event,
].join("\n");
const CONVERSATION_EVENTS = 15;
const conversations = new Map(); // slug -> { id, events }
const queue = []; // { slug, event, attempt }
const agents = new Map(); // slug -> child
let agentsLive = 0;
const busy = (slug) => agents.has(slug) || queue.some((q) => q.slug === slug);
function enqueue(slug, event, attempt = 1) { queue.push({ slug, event, attempt }); pump(); }
function pump() {
  while (agentsLive < maxAgents && !stopReason && Date.now() < deadline) {
    const i = queue.findIndex((q) => !agents.has(q.slug));
    if (i < 0) return;
    const { slug, event, attempt } = queue.splice(i, 1)[0];
    const file = path.join(runDir(slug), "logs", `batch_agent_${stamp()}`);
    mkdirSync(path.dirname(file), { recursive: true });
    const fd = openSync(`${file}.jsonl`, "a");
    const conv = conversations.get(slug);
    const resume = Boolean(conv && conv.events < CONVERSATION_EVENTS);
    // (--json: the agent's own errors are events of their own, never read out of its transcript)
    const argv = resume
      ? ["exec", "resume", "--json", "--skip-git-repo-check", "-m", model, "-c", `model_reasoning_effort="${effort}"`, "-c", `sandbox_mode="${sandbox}"`, "-o", `${file}.last.txt`, conv.id, "-"]
      : ["exec", "--json", "-m", model, "-c", `model_reasoning_effort="${effort}"`, "--sandbox", sandbox, "-C", REPO, "--skip-git-repo-check", "-o", `${file}.last.txt`, "-"];
    const child = spawn("codex", argv, { cwd: REPO, stdio: ["pipe", fd, fd], env: process.env });
    closeSync(fd);
    agents.set(slug, child); agentsLive++;
    log(`${slug}: agent ${resume ? `resumed (conversation ${conv.id}, event ${conv.events + 1})` : "called"} (pid ${child.pid}) — log ${file}.jsonl`);
    child.stdin.on("error", () => { /* an agent that died before reading */ });
    child.stdin.end(resume ? `The next event of the run \`${slug}\` (same mode and instructions as before):\n${event}` : prompt(slug, event));
    const limit = setTimeout(() => { log(`${slug}: agent over 90 min — stopped`); stopChild(child); }, 90 * 60_000);
    let closed = false;
    const done = (code) => {
      if (closed) return; closed = true;
      clearTimeout(limit); agents.delete(slug); agentsLive--;
      const events = (() => { try { return readFileSync(`${file}.jsonl`, "utf8").split("\n").flatMap((l) => { try { return [JSON.parse(l)]; } catch { return []; } }); } catch { return []; } })();
      const id = events.find((e) => e.type === "thread.started")?.thread_id;
      const errors = events.flatMap((e) => (e.type === "error" ? [String(e.message ?? "")] : e.type === "turn.failed" ? [String(e.error?.message ?? "turn failed")] : []));
      const ok = code === 0 && !events.some((e) => e.type === "turn.failed");
      if (ok && resume) conv.events++;
      else if (ok && id) conversations.set(slug, { id, events: 1 });
      else conversations.delete(slug);
      log(`${slug}: agent ${ok ? "done" : `failed (exit ${code}${errors.length ? `: ${errors.at(-1).slice(0, 200)}` : ""})`}`);
      checkAccount(errors, `${slug}'s agent`);
      // a failed call is given once more, to a fresh conversation (the watch has handed the event over)
      if (!ok && attempt < 2 && !stopReason && Date.now() < deadline) queue.unshift({ slug, event, attempt: attempt + 1 });
      else if (!ok) log(`${slug}: the event was not acted on — ${event.split("\n")[0].slice(0, 200)}`);
      pump();
    };
    child.on("error", (e) => { log(`${slug}: agent could not start: ${e.message}`); done(-1); });
    child.on("close", (code) => done(code));
  }
}
/** SIGTERM, then SIGKILL half a minute later. */
function stopChild(c) { try { c.kill("SIGTERM"); } catch { /* gone */ } setTimeout(() => { try { c.kill("SIGKILL"); } catch { /* gone */ } }, 30_000).unref(); }

// ─── the account: a spent one stops the job, which submits no successor ─────────
// (the pipeline's own rule for a spent Codex account, `src/shared/codex.ts` `isTransientCodexFailure`)
const SPENT = /usage limit|session limit|quota (?:exceeded|exhausted)|exceeded your current quota|insufficient_quota|purchase more credits|not supported when using Codex with a ChatGPT account/i;
const RATE = /\b429\b|\brate[ -]limit/i;
const rateHits = [];
function checkAccount(errors, where) {
  for (const text of errors) {
    if (stopReason) return;
    if (SPENT.test(text)) stopReason = `the Codex account looks spent (${where}: ${text.slice(0, 200)})`;
    else if (RATE.test(text)) {
      rateHits.push(Date.now());
      while (rateHits.length && Date.now() - rateHits[0] > 3_600_000) rateHits.shift();
      if (rateHits.length >= 3) stopReason = `three rate-limit errors within an hour (last: ${where}: ${text.slice(0, 200)})`;
    }
  }
  if (stopReason) { log(`STOP: ${stopReason} — stopping the runs and submitting no further job`); halt(); }
}

// ─── watches ─────────────────────────────────────────────────────────────────────
const scratch = mkdtempSync(path.join(os.tmpdir(), "batch-orch-"));
const watches = new Set();
const watchOnce = (slug, known, timeout = 600) => new Promise((resolve) => {
  if (Date.now() >= deadline || stopReason) { resolve({ code: 2, out: "" }); return; }
  const child = spawn(process.execPath, [ORCH, "watch", slug, "--toolkit", toolkit, "--starts", "--timeout", String(timeout), ...(known.size ? ["--known", [...known].join(",")] : [])], {
    stdio: ["ignore", "pipe", "pipe"], env: { ...sessionEnv, THEOREMCHECKER_ORCH_REPORTED: path.join(scratch, `${slug}.json`) },
  });
  watches.add(child);
  let out = "";
  child.stdout.on("data", (d) => { out += d; });
  child.stderr.on("data", (d) => { out += d; });
  child.on("error", (e) => { watches.delete(child); resolve({ code: -1, out: `${out}\nthe watch could not start: ${e.message}` }); });
  child.on("close", (code) => { watches.delete(child); resolve({ code, out: out.trim() }); });
});
// while an agent works no watch is armed: the job's record of each run is kept fresh for the page
setInterval(() => {
  for (const slug of active.keys()) {
    const f = path.join(runDir(slug), "orch.json");
    if (readJson(f)?.pid === process.pid) { try { utimesSync(f, new Date(), new Date()); } catch { /* replaced */ } }
  }
}, 60_000).unref();

/** Follow one run until it is settled (finished, and nothing is left to it), the job's time is spent or the job
 *  stops; "held" when there is no run, or another live job holds it (that job puts it back) — such a run is not
 *  put back from here. */
async function follow({ slug, source, main }) {
  if (!existsSync(path.join(runDir(slug), "state.json"))) {
    if (!source) { log(`${slug}: no run and no source given — left`); return "held"; }
    startCli(slug, ["verify", source, "--toolkit", toolkit, "--slug", slug, ...(main ? ["--main", main] : []), ...(fullAuto ? ["--full-auto"] : [])], "start");
  } else {
    enqueue(slug, "The driver attached this job to the run (session start): act on the run as it stands — a halt already waiting is yours now; a run at rest that waits for nobody, resume it.");
  }
  // A finished run's blocking TODO items were told once (logs/bundle_todo.told), maybe to a session that is gone:
  // they are told again, to this job's agent — the record is dropped once this job's watch holds the run (not
  // before: a live session that holds it would be told twice), unless that watch has just told them anew.
  const toldFile = path.join(runDir(slug), "logs", "bundle_todo.told");
  let retell = null;
  if (finished(slug)) { try { retell = readFileSync(toldFile, "utf8"); } catch { /* never told */ } }
  const reminded = new Set(); // requests the agent was reminded to clear, in this job
  let known = new Set();
  let last = null;
  let heldSince = 0;
  while (Date.now() < deadline && !stopReason) {
    if (settled(slug)) {
      if (!busy(slug)) { log(`${slug}: finished, and nothing is left to act on — left`); break; }
      // its agent is still at it (the session start): what that turn does is looked at once it ends
      quiet.delete(slug);
      while (!stopReason && Date.now() < deadline && busy(slug)) await sleep(2_000);
      continue;
    }
    // A finished run kept only by a request whose answers were all acted on: once its agent's turn ends, it is
    // asked (once in this job) to clear it (`orch.mjs done`) or to leave it open on purpose — the run then waits
    // for the owner, job after job.
    if (finished(slug) && answeredRequests(slug).some((id) => !reminded.has(id))) {
      while (!stopReason && Date.now() < deadline && busy(slug)) await sleep(2_000);
      const forgotten = answeredRequests(slug).filter((id) => !reminded.has(id));
      if (forgotten.length && !stopReason && Date.now() < deadline) {
        for (const id of forgotten) reminded.add(id);
        quiet.delete(slug);
        log(`${slug}: finished, its request(s) ${forgotten.join(", ")} answered but open — the agent is asked to clear them`);
        enqueue(slug, `The run is finished, and your request(s) ${forgotten.join(", ")} to the owner are still open on the page though every reply of theirs to them was acted on. While a request is open, this job (and the next) stays attached to the run, waiting for the owner. If nothing more is wanted of them, clear each: \`node ${ORCH} done ${slug} --toolkit ${toolkit} <id>\`; if you still wait on their answer, leave it open and say so on the page.`);
        while (!stopReason && Date.now() < deadline && busy(slug)) await sleep(2_000);
      }
      continue;
    }
    const t0 = Date.now();
    // A finished run that waits for nobody gets a short look, not 10 min: the watch's first check reports what is
    // on file (a message, a start request, the blocking TODO items, what the page cannot draw), and the agent ended
    // its turn before it (a resume it started beats by then). One that waits for the owner is watched as any other.
    const look = finished(slug) && !awaitsOwner(slug) && !runnerHere(slug);
    const { code, out } = await watchOnce(slug, known, look ? 5 : 600);
    if (Date.now() >= deadline || stopReason) break;
    try { known = new Set(JSON.parse(readFileSync(path.join(scratch, `${slug}.json`), "utf8"))); rmSync(path.join(scratch, `${slug}.json`)); } catch { /* none named */ }
    if (code === 3) {
      // another live session holds it — or a job that died, whose record lapses within half an hour
      if (!heldSince) { heldSince = Date.now(); log(`${slug}: held by another session — waiting for its record to lapse`); }
      if (Date.now() - heldSince < 35 * 60_000) { await sleep(5 * 60_000); continue; }
      log(`${slug}: held by another live session — left to it`); return "held";
    }
    heldSince = 0;
    if (code === 64 || code === 66) { log(`${slug}: not followed any more — ${out.split("\n")[0]}`); return "held"; }
    // a run waiting for the owner needs no resources: it does not count among the runs at work
    if (code === 2 && /waiting for the owner/.test(out)) waitingOwner.add(slug); else waitingOwner.delete(slug);
    if (code === 2) quiet.add(slug); else quiet.delete(slug);
    // this job's watch holds the run now: the blocking items are told at the next watch (a look, not quiet)
    if (retell !== null) {
      try { if (readFileSync(toldFile, "utf8") === retell) rmSync(toldFile, { force: true }); } catch { /* gone */ }
      retell = null;
      quiet.delete(slug);
    }
    if (code !== 0) { if (code !== 2) { log(`${slug}: the watch exited ${code}: ${out.split("\n")[0]}`); await sleep(60_000); } continue; }
    // a request on file is carried out whatever the report was; a report of something else goes to the agent too
    takeStartRequest(slug);
    if (/^\[orch\] \S+: the owner asked the page to (?:start|stop) the run/.test(out)) continue;
    // a run that is running again needs nobody; the same report at once again waits a pause, not a spin
    if (/^\[orch\] \S+: the run is running again/.test(out)) continue;
    if (out === last && Date.now() - t0 < 5_000) { await sleep(60_000); continue; }
    last = out;
    log(`${slug}: ${out.split("\n")[0]}`);
    enqueue(slug, out);
    // the agent acts before the next watch reads the run
    while (!stopReason && Date.now() < deadline && busy(slug)) await sleep(2_000);
  }
  // A run already finished on entry still has its session-start call (and possibly a retry).
  // Drain it before normal shutdown, which stops outstanding agents.
  while (!stopReason && Date.now() < deadline && busy(slug)) await sleep(200);
}

// ─── the shared queue (several jobs take from one file) ─────────────────────────
const LOCK_STALE_MS = 5 * 60_000;
/** Run `fn` on the queue's lines under its lock: a directory beside it, with its holder's clock time in
 *  `owner`. A lock older than 5 min is a dead holder's: it is moved aside (one renamer wins), then taken. */
function withQueue(fn) {
  const lock = `${queueFile}.lock`;
  const t0 = Date.now();
  for (;;) {
    try { mkdirSync(lock); writeFileSync(path.join(lock, "owner"), `${os.hostname()} ${process.pid} ${Date.now()}`); break; } catch (e) {
      if (e.code !== "EEXIST") throw e;
      let at = 0;
      try { at = Number(readFileSync(path.join(lock, "owner"), "utf8").split(" ")[2]) || 0; } catch { /* being written, or just released */ }
      if (!at) { try { at = statSync(lock).mtimeMs; } catch { continue; } }
      if (Date.now() - at > LOCK_STALE_MS) { try { renameSync(lock, `${lock}.stale.${process.pid}.${Date.now()}`); } catch { /* another took it */ } continue; }
      if (Date.now() - t0 > 120_000) throw new Error(`the queue's lock ${lock} is held`);
      Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 100);
    }
  }
  try {
    let lines = [];
    try { lines = readFileSync(queueFile, "utf8").split("\n"); } catch { /* no queue yet */ }
    const out = fn(lines);
    const tmp = `${queueFile}.${process.pid}.tmp`;
    writeFileSync(tmp, out.lines.join("\n").replace(/\n*$/, "\n"));
    renameSync(tmp, queueFile);
    return out.value;
  } finally { rmSync(lock, { recursive: true, force: true }); }
}
const isEntry = (l) => l.trim() !== "" && !l.trim().startsWith("#");
/** The next entry of the queue, taken off it (a line that names no run is dropped, and said). */
const claim = () => withQueue((lines) => {
  for (let i = 0; i < lines.length; i++) {
    if (!isEntry(lines[i])) continue;
    const e = entryOf(lines[i]);
    const rest = lines.filter((_, k) => k !== i);
    if (e) return { lines: rest, value: e };
    log(`queue: not a run, dropped: ${lines[i]}`);
    lines = rest; i--;
  }
  return { lines, value: null };
});
/** Runs not settled, put back at the head of the queue for the next job (one already there is not repeated);
 *  when the queue cannot be written, into <queue>.orphans. */
function giveBack(entries) {
  if (!entries.length) return;
  try {
    withQueue((lines) => {
      const there = new Set(lines.filter(isEntry).map((l) => entryOf(l)?.slug));
      return { lines: [...entries.filter((e) => !there.has(e.slug)).map(lineOf), ...lines], value: null };
    });
  } catch (e) {
    appendFileSync(`${queueFile}.orphans`, entries.map(lineOf).join("\n") + "\n");
    log(`queue not written (${e.message}): the unfinished runs are in ${queueFile}.orphans`);
  }
}
const queueEmpty = () => { try { return !readFileSync(queueFile, "utf8").split("\n").some(isEntry); } catch { return true; } };

// ─── ending ──────────────────────────────────────────────────────────────────────
/** The job's time is spent or it is stopped: the watches end and the agents are stopped. */
function halt() { for (const c of watches) c.kill(); for (const c of agents.values()) stopChild(c); }
/** The runners of these runs on this machine, stopped (each stops its own workers). */
function stopRunners() {
  for (const { slug } of followed) {
    const r = runnerHere(slug);
    if (r?.here && r.pid > 0) { try { process.kill(r.pid, "SIGTERM"); log(`${slug}: runner ${r.pid} stopped (the job ends)`); } catch { /* gone */ } }
  }
}
/** Detach from every run followed (the page then shows no job attached). */
const detachAll = () => Promise.all(followed.map(({ slug }) => new Promise((r) => {
  const c = spawn(process.execPath, [ORCH, "detach", slug, "--toolkit", toolkit], { stdio: "ignore", env: sessionEnv });
  c.on("error", r); c.on("exit", r);
})));
let ending = false;
async function finish(why) {
  if (ending) return; ending = true;
  halt();
  for (let k = 0; k < 40 && agentsLive > 0; k++) await new Promise((r) => setTimeout(r, 1_000));
  if (why) { log(why); stopRunners(); }
  const back = [...followed.filter((e) => !settled(e.slug) && !held.has(e.slug)), ...pending].filter((e, i, a) => a.findIndex((x) => x.slug === e.slug) === i);
  if (queueFile) giveBack(back);
  for (const c of watches) c.kill();
  await detachAll();
  rmSync(scratch, { recursive: true, force: true });
  log(`done: ${followed.map((r) => `${r.slug} ${phaseOf(r.slug) ?? "?"}`).join(", ") || "nothing to follow"}${back.length ? `; left for the next job: ${back.map((e) => e.slug).join(", ")}` : ""}`);
  if (stopReason && queueFile) appendFileSync(`${queueFile}.stopped`, `${new Date().toISOString()} ${process.env.CODEX_HOME ?? ""}: ${stopReason}\n`);
  // 76: the account is spent — no successor; 75: work is left, in its runs or the queue (the job's script submits
  // the next job); 0: none
  process.exit(stopReason ? 76 : back.length || (queueFile && !queueEmpty()) ? 75 : 0);
}
for (const sig of ["SIGTERM", "SIGINT", "SIGHUP"]) process.on(sig, () => finish(`signalled (${sig}): stopping the runners`));

// ─── main ────────────────────────────────────────────────────────────────────────
const atWork = () => [...active.keys()].filter((s) => !waitingOwner.has(s)).length;
function fill() {
  while (Date.now() < deadline && !stopReason && atWork() < keep && !(batchMode && followed.length >= keep)) {
    let next = pending.shift() ?? null;
    if (!next && queueFile) { try { next = claim(); } catch (e) { log(`queue not read: ${e.message}`); return; } }
    if (!next) return;
    if (active.has(next.slug)) continue;
    const e = next;
    followed.push(e);
    log(`${e.slug}: followed`);
    active.set(e.slug, follow(e).then((how) => { if (how === "held") held.add(e.slug); active.delete(e.slug); }));
  }
}
if (Number.isFinite(deadline)) setTimeout(halt, Math.max(0, deadline - Date.now())).unref();
log(`on ${os.hostname()}${hours ? `, until ${new Date(deadline).toISOString()}` : ""}: ${keep} run(s) at work${queueFile ? `, taken from ${queueFile}` : ""}; agents: codex ${model} (${effort}, ${sandbox}), at most ${maxAgents} at once`);
fill();
// (the minute's timer is cleared when a run ends first: none is left to hold the process)
while (active.size) {
  let t;
  await Promise.race([...active.values(), new Promise((r) => { t = setTimeout(r, 60_000); })]);
  clearTimeout(t);
  fill();
}
await finish(stopReason ? `stopping the runners: ${stopReason}` : Date.now() >= deadline ? "the job's time is nearly spent: stopping the runners" : null);
