#!/usr/bin/env node
// One watcher over several runs that re-arms itself.
//
//   node tools/scripts/orch_watch_loop.mjs --toolkit <path> <slug> [<slug>…]
//
// For each run it keeps `orch.mjs watch <slug>` armed: every time a watch returns (a halt, a finish, a
// message of the owner, a list of what the page cannot draw…), its report is printed, each line prefixed
// with `[<slug>]`, and the watch is armed again at once. Run it as a streaming monitor (Claude Code:
// the Monitor tool; each printed report is one notification): the session can then miss no event by
// forgetting to re-arm. A message of the owner (a rejected ruling, a reported issue) is printed once:
// the next watches are told it is known (`--known`) and return only for something new. A run another
// live session holds (exit 3), or a slug with no run (exit 66), is reported once and left; any other
// exit is reported and the watch re-armed after a pause.
import { spawn } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const args = process.argv.slice(2);
const at = args.indexOf("--toolkit");
const toolkit = at >= 0 ? args.splice(at, 2)[1] : undefined;
if (!toolkit || args.length === 0) { console.error("usage: orch_watch_loop.mjs --toolkit <path> <slug> [<slug>…]"); process.exit(64); }
const orch = path.join(path.dirname(fileURLToPath(import.meta.url)), "orch.mjs");

// Stopped (a monitor's expiry, TaskStop), the loop stops its watches: one left behind would take a report the
// next watch then never prints. (Killed outright, the loop cannot: each watch then sees it is gone and ends
// without handing anything over — `PAPERFORMALIZER_ORCH_PARENT`.)
const live = new Set();
// where each watch names the owner's items it reported (`PAPERFORMALIZER_ORCH_REPORTED`)
const scratch = mkdtempSync(path.join(tmpdir(), "orch-loop-"));
const stopAll = () => { for (const c of live) c.kill(); rmSync(scratch, { recursive: true, force: true }); };
process.on("exit", stopAll);
for (const sig of ["SIGTERM", "SIGINT", "SIGHUP"]) process.on(sig, () => process.exit(0));
process.stdout.on("error", () => process.exit(0));

const watchOnce = (slug, known) => new Promise((resolve) => {
  const child = spawn(process.execPath, [orch, "watch", slug, "--toolkit", toolkit, ...(known.size ? ["--known", [...known].join(",")] : [])], {
    stdio: ["ignore", "pipe", "pipe"], env: { ...process.env, PAPERFORMALIZER_ORCH_PARENT: String(process.pid), PAPERFORMALIZER_ORCH_REPORTED: path.join(scratch, `${slug}.json`) },
  });
  live.add(child);
  let out = "";
  child.stdout.on("data", (d) => { out += d; });
  child.stderr.on("data", (d) => { out += d; });
  child.on("error", (e) => { live.delete(child); resolve({ code: -1, out: `${out}\n[loop] the watch could not start: ${e.message}` }); });
  child.on("close", (code) => { live.delete(child); resolve({ code, out }); });
});

const PAUSE_MS = Number(process.env.PAPERFORMALIZER_ORCH_LOOP_PAUSE_MS ?? 60_000);
const loop = async (slug) => {
  let known = new Set();
  let last = null;
  for (;;) {
    const t0 = Date.now();
    const { code, out } = await watchOnce(slug, known);
    const text = out.trim();
    // (the same report at once again — a file the watch cannot read — waits a pause, not a spin)
    if (text === last && Date.now() - t0 < 2000) { await new Promise((r) => setTimeout(r, PAUSE_MS)); continue; }
    last = text;
    if (text) console.log(text.split("\n").map((l) => `[${slug}] ${l}`).join("\n"));
    // the owner's items this report named (all that stand: answered or handled ones drop out)
    try { known = new Set(JSON.parse(readFileSync(path.join(scratch, `${slug}.json`), "utf8"))); rmSync(path.join(scratch, `${slug}.json`)); } catch { /* none named */ }
    if (code === 3 || code === 66 || code === 64) { console.log(`[${slug}] not watched any more (orch.mjs watch exited ${code})`); return; }
    if (code !== 0 && code !== 2) await new Promise((r) => setTimeout(r, PAUSE_MS));
  }
};

await Promise.all(args.map(loop));
