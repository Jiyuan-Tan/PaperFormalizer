// Owner actions from the UI (resume, stop, apply a promotion round, rule on the repairs that would
// weaken a main result, reword or remove a reading entered for the owner), as the CLI calls they
// stand for; every other ruling at a halt is the attached agent's, made at the CLI. `buildArgv` is
// pure (the page shows its result before anything runs); `launch` starts the call detached with this
// process's Node and tsx — no shell, so the same on Windows, macOS and Linux.
import { spawn } from "node:child_process";
import { closeSync, mkdirSync, openSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import { createRequire } from "node:module";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { parseChecklist, setDecisions, type ChecklistDecision } from "../proposals/checklist.js";
import type { ProposalBatch } from "../proposals/schema.js";

export const TOOLS_DIR = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..");

/** What the owner decided on the page. */
export type Action =
  | { kind: "resume" }
  | { kind: "stop" }
  | { kind: "apply-promotion"; round: "A" | "B" }
  /** The owner's ruling on the suggested repairs that weaken a main result: every item answered. */
  | { kind: "rule-repairs"; accept?: string[]; decline?: { nodes: string[]; reason: string }; redo?: Array<{ node: string; guidance: string }> }
  /** A reading entered for the owner (`patches.json` `owner_readings`, by id), reworded or removed. */
  | { kind: "edit-reading"; readings: Array<{ id: string; text: string }> }
  | { kind: "remove-reading"; ids: string[] };

/** The actions taken only under an attached agent session, which acts at the run's next halt:
 *  those that resume the run, and the apply of a promotion round — it resumes the run when it
 *  ends, and one that stops part-way is the agent's to settle. (A stop needs none.) */
export const needsAgent = (a: Action): boolean => a.kind !== "stop";

/** The CLI arguments of an action (after `theoremchecker`). Throws on an invalid action. Pure. */
export function buildArgv(a: Action, ctx: { toolkitRoot: string; slug: string; source: string | null }): string[] {
  const need = (cond: boolean, msg: string) => { if (!cond) throw new Error(msg); };
  const base = (src: string) => ["verify", src, "--toolkit", ctx.toolkitRoot, "--slug", ctx.slug];
  need(ctx.source !== null, "this run records no source to resume from");
  if (a.kind === "stop") return [...base(ctx.source!), "--stop"];
  if (a.kind === "apply-promotion") {
    need(a.round === "A" || a.round === "B", "a promotion round is A or B");
    return ["propose", ctx.slug, "--round", a.round, "--apply", "--toolkit", ctx.toolkitRoot];
  }
  if (a.kind === "rule-repairs") {
    const node = (n: string) => { need(/^[A-Za-z]+:[A-Za-z0-9._-]+$/.test(n), `not a node id: ${n}`); return n; };
    const accept = (a.accept ?? []).map(node);
    const decline = (a.decline?.nodes ?? []).map(node);
    const redo = a.redo ?? [];
    need(accept.length + decline.length + redo.length > 0, "no repair was ruled on");
    need(decline.length === 0 || Boolean(a.decline!.reason.trim()), "declining a repair needs a reason");
    const out = [...base(ctx.source!), "--resume"];
    if (accept.length) out.push("--accept-repair", accept.join(","));
    if (decline.length) out.push("--decline-repair", `${decline.join(",")}: ${a.decline!.reason.trim()}`);
    for (const r of redo) { need(Boolean(r.guidance.trim()), `say what the new repair of ${r.node} should do`); out.push("--redo-repair", `${node(r.node)}: ${r.guidance.trim()}`); }
    return out;
  }
  if (a.kind === "edit-reading" || a.kind === "remove-reading") {
    const reading = (id: string) => { need(/^ass:(pin|bk)-owner-[0-9]+$/.test(id), `not an owner reading's id: ${id}`); return id; };
    const out = [...base(ctx.source!), "--resume"];
    if (a.kind === "remove-reading") for (const id of a.ids ?? []) out.push("--remove-reading", reading(id));
    else for (const r of a.readings ?? []) { need(Boolean(r.text?.trim()), "the reading has no text (remove it instead)"); out.push("--edit-reading", `${reading(r.id)}: ${r.text.trim()}`); }
    need(out.length > base(ctx.source!).length + 1, "no reading was named");
    return out;
  }
  // the request's `kind` is the page's word: anything else must not pass for a plain resume
  need(a.kind === "resume", `not an action: ${String((a as { kind?: unknown }).kind)}`);
  return [...base(ctx.source!), "--resume"];
}

/** The argv as one display line (quoted where needed), for the page. Pure. */
export function displayCommand(argv: string[]): string {
  return ["theoremchecker", ...argv].map((a) => (/^[A-Za-z0-9_.,:/=@+\-]+$/.test(a) ? a : `"${a.replace(/(["\\$`])/g, "\\$1")}"`)).join(" ");
}

/** Start `theoremchecker <argv>` detached; its output goes to `log`. Returns the child's pid. */
export function launch(argv: string[], log: string): number {
  const require = createRequire(import.meta.url);
  const tsxCli = require.resolve("tsx/cli");
  mkdirSync(path.dirname(log), { recursive: true });
  const fd = openSync(log, "a");
  try {
    const child = spawn(process.execPath, [tsxCli, path.join(TOOLS_DIR, "bin", "theoremchecker.ts"), ...argv], {
      cwd: TOOLS_DIR, detached: true, stdio: ["ignore", fd, fd], windowsHide: true, env: process.env,
    });
    child.on("error", () => {}); // a failed start is in no log, but must not end the UI
    child.unref();
    return child.pid ?? -1;
  } finally {
    closeSync(fd);
  }
}

/**
 * Write decisions into a promotion checklist's ```decision blocks (other text untouched), then read
 * the result back with the pipeline's own parser — what this writes is what `propose --apply` reads.
 */
export async function writeChecklistDecisions(md: string, batch: ProposalBatch, decisions: Record<string, ChecklistDecision>): Promise<Record<string, ChecklistDecision>> {
  const text = await readFile(md, "utf8");
  const next = setDecisions(text, decisions);
  const parsed = parseChecklist(next, batch);
  await writeFile(md, next, "utf8");
  return parsed;
}

export { setDecisions };
