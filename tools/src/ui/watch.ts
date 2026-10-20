// Change detection for the UI: which views went stale. Polling stats a few files per run (state,
// pipeline log, report, review, patches, proposals, annotated paper) — cheap, and the only signal
// that works on every filesystem (file-watch events do not fire on NFS or some network drives).
// `fs.watch`, where the platform supports it, only wakes the poller early. What a run's status
// takes from no file at all — its runner alive or not (`runPulse`) — is looked at on every pass.
import { existsSync, readdirSync, watch, type FSWatcher } from "node:fs";
import path from "node:path";
import type { ToolkitConfig } from "../toolkit/config.js";
import { signature } from "./fscache.js";
import { checklistPath, listRunSlugs, runDir, runPulse } from "./run_model.js";

const RUN_FILES = [
  "state.json", "pipeline.jsonl", "report.json", "nl_links.json",
  "discovery/core.json", "discovery/v1_5_review.json", "discovery/patches.json",
  "proposals/A.json", "proposals/B.json", "repair_recommendations.json", "proposals/apply_A.pid", "proposals/apply_B.pid", "proposals/move_pending.json", "proposals/apply_failed.json", "proposals/A.recommendations.json", "proposals/B.recommendations.json", "proposals/A.decisions.json", "proposals/B.decisions.json", "orch.json", "orch_requests.json", "orch_messages.json", "orch_decisions.json", "owner_objections.json", "ui_math_overrides.json",
];

/** The files whose change makes a run's views stale. */
export function runFiles(cfg: ToolkitConfig, slug: string): string[] {
  const dir = runDir(cfg, slug);
  const files = RUN_FILES.map((f) => path.join(dir, ...f.split("/")));
  for (const sub of ["annotated", "source"]) {
    const d = path.join(dir, sub);
    if (existsSync(d)) {
      for (const f of readdirSync(d)) if (/\.(tex|aux|bbl)$/.test(f)) files.push(path.join(d, f));
    }
  }
  files.push(checklistPath(cfg, slug, "A"), checklistPath(cfg, slug, "B"));
  return files;
}

function libraryFiles(cfg: ToolkitConfig): string[] {
  const out: string[] = [];
  const walk = (d: string) => {
    if (!existsSync(d)) return;
    for (const e of readdirSync(d, { withFileTypes: true })) {
      const p = path.join(d, e.name);
      if (e.isDirectory()) { if (e.name !== "tmp") walk(p); } else if (e.name.endsWith(".lean")) out.push(p);
    }
  };
  for (const div of cfg.divisions) walk(path.join(cfg.toolkitRoot, cfg.lib, div));
  walk(path.join(cfg.toolkitRoot, cfg.papersLib));
  return out;
}

/**
 * Recursive `fs.watch` is native on Windows and macOS only: elsewhere Node emulates it with one
 * watcher per file, set up synchronously — thousands in a runs tree. There the runs directory, the
 * checklists and a few directories per run are watched instead.
 */
const NATIVE_RECURSIVE = process.platform === "win32" || process.platform === "darwin";
const RUN_WATCH_DIRS = ["", "discovery", "proposals", "annotated"];

export class ChangeWatcher {
  private sigs = new Map<string, string>();
  private timer: NodeJS.Timeout | null = null;
  private watchers = new Map<string, FSWatcher>();
  private tick = 0;
  /** Runs a watch event named since the last pass: scanned in the next one, live or not. */
  private dirty = new Set<string>();
  private soon = false;
  private stopped = false;

  constructor(private cfg: ToolkitConfig, private emit: (scope: string) => void) {}

  start(): void {
    this.scan(true);
    this.schedule(1000);
  }

  stop(): void {
    this.stopped = true;
    if (this.timer) clearTimeout(this.timer);
    for (const w of this.watchers.values()) w.close();
    this.watchers.clear();
  }

  private schedule(ms: number): void {
    if (this.timer) clearTimeout(this.timer);
    this.timer = setTimeout(() => {
      this.soon = false;
      try {
        this.scan(false);
      } catch {
        // a directory removed or rewritten under the pass (or a network-drive hiccup): the next pass sees it
      }
      if (!this.stopped) this.schedule(1000);
    }, ms);
  }

  /** An accelerator only: an event marks its run and brings the next pass forward. */
  private watch(dir: string, recursive: boolean, slugOf: (file: string) => string): void {
    if (this.stopped || this.watchers.has(dir) || !existsSync(dir)) return;
    try {
      const w = watch(dir, { recursive }, (_event, file) => {
        if (this.stopped) return;
        if (file) this.dirty.add(slugOf(String(file)));
        if (!this.soon) { this.soon = true; this.schedule(200); }
      });
      w.on("error", () => { w.close(); this.watchers.delete(dir); });
      this.watchers.set(dir, w);
    } catch {
      // not watchable here: polling alone
    }
  }

  /** (Re)arm the watchers: directories that appeared since are picked up, those of removed runs dropped. */
  private rewatch(slugs: string[]): void {
    const runs = this.cfg.runsDir;
    this.watch(runs, NATIVE_RECURSIVE, (f) => f.split(/[\\/]/)[0]!);
    this.watch(path.join(this.cfg.toolkitRoot, "doc", "proposals"), false, (f) => f.replace(/\.[AB]\.md$/, ""));
    if (NATIVE_RECURSIVE) return;
    const want = new Set(slugs.flatMap((s) => RUN_WATCH_DIRS.map((d) => path.join(runDir(this.cfg, s), d))));
    for (const [dir, w] of this.watchers) {
      if (dir.startsWith(runs + path.sep) && !want.has(dir)) { w.close(); this.watchers.delete(dir); }
    }
    for (const s of slugs) for (const d of RUN_WATCH_DIRS) this.watch(path.join(runDir(this.cfg, s), d), false, () => s);
  }

  /**
   * One pass. Every run's pulse — what no file change announces: a runner, an agent session or an
   * apply that died, a heartbeat gone stale — every second; the files of the runs at work and of
   * those a watch event named every second too, of the others every 5 s; the library every 10 s.
   */
  private scan(initial: boolean): void {
    this.tick++;
    const dirty = this.dirty;
    this.dirty = new Set();
    const slugs = listRunSlugs(this.cfg);
    const listSig = slugs.join(",");
    let toolkitChanged = this.update("runs-list", listSig, initial);
    if (initial || toolkitChanged || this.tick % 5 === 0) this.rewatch(slugs);
    for (const slug of slugs) {
      const { key, atWork } = runPulse(this.cfg, slug);
      const beat = this.update(`pulse:${slug}`, key, initial);
      if (!initial && !beat && !atWork && !dirty.has(slug) && this.tick % 5 !== 0 && this.sigs.has(`run:${slug}`)) continue;
      const sig = runFiles(this.cfg, slug).map(signature).join("|");
      if (this.update(`run:${slug}`, sig, initial) || beat) { this.emit(`run:${slug}`); toolkitChanged = true; }
    }
    if (toolkitChanged && !initial) this.emit("toolkit");
    if (initial || this.tick % 10 === 0) {
      const sig = libraryFiles(this.cfg).map((f) => `${f}:${signature(f)}`).join("|");
      if (this.update("library", sig, initial) && !initial) this.emit("library");
    }
  }

  private update(key: string, sig: string, initial: boolean): boolean {
    const prev = this.sigs.get(key);
    this.sigs.set(key, sig);
    return !initial && prev !== undefined && prev !== sig;
  }
}
