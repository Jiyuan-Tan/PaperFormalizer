// `paperformalizer demo`: one recorded run of a made-up paper, played back on the real page of a
// throwaway toolkit, step by step, with a tour beside it. No model call, no Lean, no account: the
// recorded states (`tools/data/demo/snapshots/`, written by `scripts/demo_capture.mjs build`) are laid
// over the toolkit one after the other, and this driver stands in for the attached agent — it takes
// what the owner sends from the page (their rulings, the apply of a round) as the cue for the next
// step, shows the run at work for a few seconds, then lays down the state that followed.
import { cpSync, existsSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { updateMessages } from "../../scripts/messages_store.mjs";
import type { Action } from "../ui/actions.js";
import type { OrchMessage } from "../ui/run_model.js";

export const DEMO_DATA_DIR = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..", "data", "demo");
export const TEMPLATE_TOOLKIT_DIR = path.resolve(DEMO_DATA_DIR, "..", "..", "..", "templates", "toolkit");

/** One step of the tour. */
export interface DemoStep {
  id: string;
  /** The recorded state laid down as the step begins (`snapshots/<name>`); none: the files stay. */
  snapshot?: string;
  /** The view the step is about; the tour offers to open it. */
  view: "toolkit" | "paper" | "library";
  title: string;
  /** What the tour says (HTML of a few short paragraphs). */
  body: string;
  /** A CSS selector of what the step points at on the page. */
  target?: string;
  /** How the step ends: the tour's Next button, or what the owner sends from the page. */
  advance?: "next" | "rule-repairs" | "apply-promotion";
  /** The run at work before this step's state is laid down: for how long, and its log lines. */
  running?: { seconds: number; events: Array<{ stage: string; message: string }> };
}
export interface DemoScript {
  /** The run's slug in the demo toolkit. */
  slug: string;
  /** The name the page shows for the stand-in agent. */
  agent: string;
  /** Its answer to a message of the owner's. */
  reply: string;
  steps: DemoStep[];
}

/** What the page's tour shows. */
export interface DemoView { step: number; total: number; slug: string; busy: boolean; current: DemoStep; expect: string | null }

/** The paths of the toolkit a recorded state covers (`demo_capture.mjs` `TREES`). */
const TREES = (slug: string) => [path.join("runs", slug), "Toolkit", "Toolkit.lean", "Papers", "Papers.lean", "doc"];
const TEXT = /\.(json|jsonl|md|tex|lean|txt|toml|bib|csv|html)$/;

/** Lay the recorded state `dir` over the toolkit: its files (the placeholders made this machine's), then its removals. */
export function applySnapshot(root: string, dir: string, paths: { toolkit: string; paper: string }): void {
  const files = path.join(dir, "files");
  const walk = (rel: string): string[] => readdirSync(path.join(files, rel), { withFileTypes: true }).flatMap((e) => (e.isDirectory() ? walk(path.join(rel, e.name)) : [path.join(rel, e.name)]));
  for (const rel of existsSync(files) ? walk("") : []) {
    const to = path.join(root, rel);
    mkdirSync(path.dirname(to), { recursive: true });
    // (inside JSON a path is written as a JSON string's text: a Windows path's backslashes escaped)
    const as = (p: string) => (/\.jsonl?$/.test(rel) ? JSON.stringify(p).slice(1, -1) : p);
    if (TEXT.test(rel)) writeFileSync(to, readFileSync(path.join(files, rel), "utf8").split("@@PAPER@@").join(as(paths.paper)).split("@@TOOLKIT@@").join(as(paths.toolkit)));
    else cpSync(path.join(files, rel), to);
  }
  let removed: string[] = [];
  try { removed = JSON.parse(readFileSync(path.join(dir, "removed.json"), "utf8")); } catch { /* none */ }
  for (const rel of removed) if (!path.isAbsolute(rel) && !rel.split(/[\\/]/).includes("..")) rmSync(path.join(root, rel), { force: true, recursive: true });
}

/** A process's start time (Linux), as `orch.mjs` records a session's. */
const startedOf = (pid: number): string | null => { try { return readFileSync(`/proc/${pid}/stat`, "utf8").split(") ")[1]!.split(" ")[19] ?? null; } catch { return null; } };
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

export class DemoDriver {
  private step = 0;
  private busy = false;
  /** Told when the step, or whether the run is at work, changes (the server pushes it to the page). */
  onChange: () => void = () => {};
  private readonly stateFile: string;

  constructor(
    private readonly root: string,
    private readonly script: DemoScript,
    private readonly data: string = DEMO_DATA_DIR,
    /** How long a step's `running` lasts, as a share of what the script says (tests: 0). */
    private readonly pace: number = 1,
  ) {
    this.stateFile = path.join(root, ".lake", "paperformalizer-demo.json");
    try { this.step = Math.min(Number(JSON.parse(readFileSync(this.stateFile, "utf8")).step) || 0, script.steps.length - 1); } catch { this.step = 0; }
  }

  private get run(): string { return path.join(this.root, "runs", this.script.slug); }
  private get paths() { return { toolkit: this.root, paper: path.join(this.data, "paper") }; }

  /** The toolkit as step `n` shows it, built afresh: the template, then every state up to the step's. */
  install(n = this.step): void {
    for (const t of TREES(this.script.slug)) rmSync(path.join(this.root, t), { recursive: true, force: true });
    cpSync(TEMPLATE_TOOLKIT_DIR, this.root, { recursive: true, filter: (src) => !/[\\/](runs|\.lake)([\\/]|$)/.test(src.slice(TEMPLATE_TOOLKIT_DIR.length)) });
    for (const s of this.script.steps.slice(0, n + 1)) if (s.snapshot) applySnapshot(this.root, path.join(this.data, "snapshots", s.snapshot), this.paths);
    this.step = n;
    this.save();
    this.attach();
  }

  /** The stand-in agent attached to the run, as `orch.mjs watch` records a session (this process). */
  attach(): void {
    if (!existsSync(this.run)) return;
    writeFileSync(path.join(this.run, "orch.json"), JSON.stringify({ agent: this.script.agent, pid: process.pid, started: startedOf(process.pid), host: os.hostname(), attached_at: new Date().toISOString(), watcher: process.pid }) + "\n");
  }

  view(): DemoView {
    const current = this.script.steps[this.step]!;
    return { step: this.step, total: this.script.steps.length, slug: this.script.slug, busy: this.busy, current, expect: current.advance && current.advance !== "next" ? current.advance : null };
  }

  /** The tour's Start over: the first step afresh, refused while the run is at work. */
  restart(): string | null {
    if (this.busy) return "the demo run is at work: wait for it to stop";
    this.install(0);
    return null;
  }

  /** The tour's Next: refused on a step that waits for the page, and on the last. */
  async next(): Promise<string | null> {
    const cur = this.script.steps[this.step]!;
    if (this.busy) return "the demo run is at work: wait for it to stop";
    if (cur.advance && cur.advance !== "next") return `this step waits for you on the page (${cur.advance === "rule-repairs" ? "send your decisions on the repairs" : "apply the promotion round"})`;
    if (this.step >= this.script.steps.length - 1) return "this is the last step";
    await this.go(this.step + 1);
    return null;
  }

  /** An action the page sends: the step's cue starts the next step; anything else is explained. */
  act(action: Action): string | null {
    const cur = this.script.steps[this.step]!;
    if (action.kind === "stop") return "in the demo the run stops by itself";
    if (this.busy) return "the demo run is at work: wait for it to stop";
    if (cur.advance !== action.kind) return `in the demo this step does not take that: ${cur.advance === "rule-repairs" ? "decide the repairs and send them" : cur.advance === "apply-promotion" ? "decide the round's entries and apply it" : "use the tour's Next button"}`;
    void this.go(this.step + 1);
    return null;
  }

  /** The owner wrote to the agent: the stand-in answers after a moment. */
  message(): void {
    setTimeout(() => {
      try {
        updateMessages(path.join(this.run, "orch_messages.json"), (all: OrchMessage[]) => {
          const open = all.filter((m) => m.from === "user" && !m.handled);
          if (!open.length) return false;
          for (const m of open) m.handled = true;
          all.push({ id: `m${1 + Math.max(0, ...all.map((m) => Number(String(m.id).slice(1)) || 0))}`, from: "agent", text: this.script.reply, at: new Date().toISOString(), re: open.at(-1)!.id });
          return true;
        });
      } catch { /* the demo goes on without an answer */ }
    }, 1500 * this.pace);
  }

  private async go(n: number): Promise<void> {
    const to = this.script.steps[n]!;
    this.busy = true;
    this.onChange();
    try {
      if (to.running) {
        const hb = path.join(this.run, "logs", ".run.active");
        mkdirSync(path.dirname(hb), { recursive: true });
        writeFileSync(hb, `${process.pid} host=${os.hostname()} beat=60\n`);
        const each = (to.running.seconds * 1000 * this.pace) / Math.max(1, to.running.events.length);
        for (const e of to.running.events) {
          writeFileSync(path.join(this.run, "pipeline.jsonl"), JSON.stringify({ timestamp: new Date().toISOString(), stage: e.stage, status: "dispatch", duration_ms: 0, message: e.message }) + "\n", { flag: "a" });
          await sleep(each);
        }
        rmSync(hb, { force: true });
      }
      if (to.snapshot) applySnapshot(this.root, path.join(this.data, "snapshots", to.snapshot), this.paths);
      this.step = n;
      this.save();
      this.attach();
    } finally {
      this.busy = false;
      this.onChange();
    }
  }

  private save(): void {
    this.onChange();
    mkdirSync(path.dirname(this.stateFile), { recursive: true });
    writeFileSync(this.stateFile, JSON.stringify({ step: this.step }) + "\n");
  }
}

export function loadDemoScript(data: string = DEMO_DATA_DIR): DemoScript {
  return JSON.parse(readFileSync(path.join(data, "demo.json"), "utf8")) as DemoScript;
}
