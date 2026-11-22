// A settled run's workspaces released (2026-11-10): removed on this machine unless in use, through
// a trash rename first; the sweep of a machine's `ws/` removes only marked, finished runs' — never the
// workspace being ensured, never a directory of no run.
import { spawn } from "node:child_process";
import { existsSync, readdirSync } from "node:fs";
import { chmod, mkdir, mkdtemp, readFile, rm, symlink, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { applyPidLine } from "../../src/shared/run_heartbeat.js";
import { commitJournalFile } from "../../src/shared/commit.js";
import { sourceSignature } from "../../src/shared/build_inputs.js";
import { createVerifyInitialState, saveState } from "../../src/state.js";
import { ownerOf, RELEASE_STEP, releasedMarker, releaseStudyPromo, releaseWorkspaces, sweepWorkspaces, workspacePath } from "../../src/shared/workspace.js";
import { runStudyCli } from "../../src/study_cli.js";
import { toolkitTemplateDir } from "../../src/toolkit/lakefile.js";
import { writeSkeleton } from "../toolkit/helpers.js";

let dir: string;
let root: string;
let local: string;
const lines: string[] = [];
const log = (l: string) => { lines.push(l); };
const put = async (file: string, text: string) => {
  await mkdir(path.dirname(file), { recursive: true });
  await writeFile(file, text);
};
const ws = (name: string) => path.join(local, "ws", name);
/** A workspace with a build output, a link out (never followed by the removal) and a generation's hard-linked file. */
const makeWs = async (name: string) => {
  await put(path.join(ws(name), "TC", "tk", ".lake", "build", "lib", "P.olean"), "o\n");
  await symlink(path.join(root, "runs"), path.join(ws(name), "TC", "tk", "runs"));
};
const run = async (slug: string, phase: string | null, marked = false) => {
  if (phase) await put(path.join(root, "runs", slug, "state.json"), JSON.stringify({ verify: { phase } }));
  if (marked) await put(releasedMarker(root, slug), JSON.stringify({ at: "2026-11-10T00:00:00Z", host: "h", phase }));
};
/** A promotion workspace's own directory (`<P>/.pf-promo/`). */
const priv = (name: string, file: string) => path.join(workspacePath(root, name, local), ".pf-promo", file);
const wsNames = () => readdirSync(path.join(local, "ws")).sort();
const until = async (cond: () => boolean) => { for (let k = 0; k < 100 && !cond(); k++) await new Promise((r) => setTimeout(r, 50)); };

beforeEach(async () => {
  dir = await mkdtemp(path.join(os.tmpdir(), "ws-release-"));
  root = path.join(dir, "tk");
  local = path.join(dir, "local");
  await put(path.join(local, "gens", "1", "keep"), "gen\n");
  await mkdir(path.join(local, "ws"), { recursive: true });
  lines.length = 0;
});
afterEach(async () => {
  RELEASE_STEP.at = async () => {};
  await chmod(dir, 0o755).catch(() => {});
  await rm(dir, { recursive: true, force: true });
});

describe("workspace release", () => {
  it("names each workspace's run: its own, its promotion's, its studies' promotions'", () => {
    expect(ownerOf("p1")).toBe("p1");
    expect(ownerOf("p1.promo")).toBe("p1");
    expect(ownerOf("study_p1__b-foo-bar.promo")).toBe("p1");
    expect(ownerOf("study_p_x__b-foo.promo")).toBe("p_x");
    expect(ownerOf(".trash-p1-12")).toBeNull();
  });

  it("removes the run's W and both kinds of promotion workspace, nothing else", async () => {
    await run("p1", "done");
    for (const n of ["p1", "p1.promo", "study_p1__b-x.promo", "p10", "p1x.promo", "study_p10__b-x.promo", "study_p1__b-x"]) await makeWs(n);
    const r = await releaseWorkspaces(root, "p1", log, { localRoot: local });
    expect(r.removed).toEqual(["p1", "p1.promo", "study_p1__b-x.promo"]);
    expect(wsNames()).toEqual(["p10", "p1x.promo", "study_p10__b-x.promo", "study_p1__b-x"]);
    // the links out were removed, never followed; the generation stays
    expect(existsSync(path.join(root, "runs", "p1", "state.json"))).toBe(true);
    expect(await readFile(path.join(local, "gens", "1", "keep"), "utf8")).toBe("gen\n");
    expect(lines.join("\n")).toContain("p1: released ws/p1, ws/p1.promo, ws/study_p1__b-x.promo");
  });

  it("keeps them while anything uses them: the runner, an apply, a journal, the toolkit's commit", async () => {
    const proposals = path.join(root, "runs", "p1", "proposals");
    const cases: Array<[string, () => Promise<unknown>, () => Promise<unknown>]> = [
      ["its runner is live", () => put(path.join(root, "runs", "p1", "logs", ".run.active"), `${process.pid} 2026-11-10T00:00:00Z tok host=${os.hostname()} beat=15\n`),
        () => rm(path.join(root, "runs", "p1", "logs", ".run.active"))],
      ["an apply is live (apply_B.pid", () => put(path.join(proposals, "apply_B.pid"), applyPidLine(process.pid)), () => rm(path.join(proposals, "apply_B.pid"))],
      ["move_journal.json", () => put(path.join(proposals, "move_journal.json"), "{}"), () => rm(path.join(proposals, "move_journal.json"))],
      ["move_batch_journal.json", () => put(path.join(proposals, "move_batch_journal.json"), "{}"), () => rm(path.join(proposals, "move_batch_journal.json"))],
      ["study_p1__b-x/coordinate_journal.json", () => put(path.join(root, "runs", "study_p1__b-x", "coordinate_journal.json"), "{}"),
        () => rm(path.join(root, "runs", "study_p1__b-x", "coordinate_journal.json"))],
      ["toolkit commit c1 on file was prepared in ws/p1.promo", async () => {
        await put(path.join(dir, "C", "manifest.json"), JSON.stringify({ ws: path.join(ws("p1.promo"), "TC", "tk") }));
        await put(commitJournalFile(root), JSON.stringify({ id: "c1", dir: path.join(dir, "C") }));
      }, () => rm(commitJournalFile(root))],
      ["study study_p1__b-x is live", () => put(path.join(root, "runs", "study_p1__b-x", "logs", ".run.active"), `${process.pid} 2026-11-10T00:00:00Z tok host=${os.hostname()} beat=15\n`),
        () => rm(path.join(root, "runs", "study_p1__b-x", "logs", ".run.active"))],
      ["…/.pf-promo/coordinate_journal.json", () => put(priv("study_p1__b-x.promo", "coordinate_journal.json"), "{}"), () => rm(priv("study_p1__b-x.promo", "coordinate_journal.json"))],
      ["…/.pf-promo/move_batch_journal.json", () => put(priv("p1.promo", "move_batch_journal.json"), "{}"), () => rm(priv("p1.promo", "move_batch_journal.json"))],
      ["whose workspace cannot be read", () => put(commitJournalFile(root), JSON.stringify({ id: "c2", dir: path.join(dir, "gone") })), () => rm(commitJournalFile(root))],
    ];
    await run("p1", "done");
    for (const n of ["p1", "p1.promo", "study_p1__b-x.promo"]) await makeWs(n);
    // a dead apply's pid file, and a commit journal of another workspace, keep nothing
    await put(path.join(proposals, "apply_A.pid"), "999999999 host=" + os.hostname() + " beat=60\n");
    for (const [why, on, off] of cases) {
      await on();
      const r = await releaseWorkspaces(root, "p1", log, { localRoot: local });
      expect(r.removed, why).toEqual([]);
      expect(r.kept, why).toContain(why);
      expect(wsNames(), why).toEqual(["p1", "p1.promo", "study_p1__b-x.promo"]);
      await off();
    }
    await put(path.join(dir, "C", "manifest.json"), JSON.stringify({ ws: path.join(ws("p2.promo"), "TC", "tk") }));
    await put(commitJournalFile(root), JSON.stringify({ id: "c3", dir: path.join(dir, "C") }));
    expect((await releaseWorkspaces(root, "p1", log, { localRoot: local })).removed).toEqual(["p1", "p1.promo", "study_p1__b-x.promo"]);
    expect(wsNames()).toEqual([]);
  });

  it("looks again once renamed: a runner or a journal that came between the look and the rename puts them back", async () => {
    await run("p1", "done");
    for (const n of ["p1", "p1.promo"]) await makeWs(n);
    const hb = path.join(root, "runs", "p1", "logs", ".run.active");
    RELEASE_STEP.at = () => put(hb, `${process.pid} 2026-11-10T00:00:00Z tok host=${os.hostname()} beat=15\n`);
    const r = await releaseWorkspaces(root, "p1", log, { localRoot: local });
    expect(r.removed).toEqual([]);
    expect(r.kept).toContain("its runner is live");
    expect(r.kept).toContain("put back");
    expect(wsNames()).toEqual(["p1", "p1.promo"]);
    await rm(hb);
    // a promotion's journal written just before the rename is found where the workspace went
    await run("p2", "done", true);
    await makeWs("p2.promo");
    RELEASE_STEP.at = () => put(priv("p2.promo", "move_batch_journal.json"), "{}");
    expect(await sweepWorkspaces(root, local, "other", log)).toEqual([]);
    expect(wsNames()).toEqual(["p1", "p1.promo", "p2.promo"]);
    expect(lines.join("\n")).toContain("p2: released, but its workspaces are kept — a journal is on file (ws/p2.promo/…/.pf-promo/move_batch_journal.json) — seen once renamed: put back");
  });

  it("keeps a promotion workspace whose own lock is held (.pf-promo.flock), also once renamed; a free or missing lock keeps nothing", async () => {
    const holders: Array<ReturnType<typeof spawn>> = [];
    /** `file`'s flock held by another process until `let go`. */
    const hold = (file: string) => new Promise<void>((resolve) => {
      const c = spawn("flock", ["-o", file, "-c", "echo held; exec sleep 60"], { stdio: ["ignore", "pipe", "ignore"] });
      holders.push(c);
      c.stdout!.on("data", () => resolve());
    });
    const letGo = () => Promise.all(holders.splice(0).map((c) => new Promise((r) => { c.on("exit", r); c.kill("SIGKILL"); })));
    try {
      await run("p1", "done");
      for (const n of ["p1", "p1.promo", "study_p1__b-x.promo"]) await makeWs(n);
      for (const n of ["p1.promo", "study_p1__b-x.promo"]) {
        await hold(path.join(ws(n), ".pf-promo.flock"));
        const r = await releaseWorkspaces(root, "p1", log, { localRoot: local });
        expect(r.removed, n).toEqual([]);
        expect(r.kept, n).toBe(`ws/${n} is in use (its .pf-promo.flock is held)`);
        expect(wsNames(), n).toEqual(["p1", "p1.promo", "study_p1__b-x.promo"]);
        await letGo();
      }
      // taken just before the rename: it moved with the directory, and is seen held at the trash's path
      RELEASE_STEP.at = () => hold(path.join(ws("p1.promo"), ".pf-promo.flock"));
      const r = await releaseWorkspaces(root, "p1", log, { localRoot: local });
      expect(r.kept).toBe("ws/p1.promo is in use (its .pf-promo.flock is held) — seen once renamed: put back");
      expect(wsNames()).toEqual(["p1", "p1.promo", "study_p1__b-x.promo"]);
      await letGo();
      RELEASE_STEP.at = async () => {};
      // free (p1.promo's, let go) or missing (the study's: never made): released
      expect(existsSync(path.join(ws("study_p1__b-x.promo"), ".pf-promo.flock"))).toBe(true);
      await rm(path.join(ws("study_p1__b-x.promo"), ".pf-promo.flock"));
      const free = await releaseWorkspaces(root, "p1", log, { localRoot: local });
      expect(free.removed).toEqual(["p1", "p1.promo", "study_p1__b-x.promo"]);
      expect(wsNames()).toEqual([]);
    } finally {
      await letGo();
    }
  });

  it("releases a study's promotion workspace alone at its step's end, unless in use; its own heartbeat is no use", async () => {
    // (2026-11-11) 31 idle ones held 77 GB on one machine until their paper's run was released
    const study = "study_p1__b-x";
    const hb = (pid: number) => `${pid} 2026-11-10T00:00:00Z tok host=${os.hostname()} beat=15\n`;
    const holders: Array<ReturnType<typeof spawn>> = [];
    try {
      await run("p1", "v1_5");
      for (const n of ["p1", "p1.promo", `${study}.promo`, "study_p1__b-y.promo"]) await makeWs(n);
      // the paper's runner live, and an apply of it: not this workspace's users
      await put(path.join(root, "runs", "p1", "logs", ".run.active"), hb(process.ppid));
      await put(path.join(root, "runs", "p1", "proposals", "move_journal.json"), "{}");
      const cases: Array<[string, () => Promise<unknown>, () => Promise<unknown>]> = [
        [`study ${study} is live (pid ${process.ppid})`, () => put(path.join(root, "runs", study, "logs", ".run.active"), hb(process.ppid)), () => rm(path.join(root, "runs", study, "logs", ".run.active"))],
        [`a journal is on file (runs/${study}/coordinate_journal.json)`, () => put(path.join(root, "runs", study, "coordinate_journal.json"), "{}"), () => rm(path.join(root, "runs", study, "coordinate_journal.json"))],
        ["…/.pf-promo/coordinate_journal.json", () => put(priv(`${study}.promo`, "coordinate_journal.json"), "{}"), () => rm(priv(`${study}.promo`, "coordinate_journal.json"))],
        [`ws/${study}.promo is in use (its .pf-promo.flock is held)`, () => new Promise<void>((resolve) => {
          const c = spawn("flock", ["-o", path.join(ws(`${study}.promo`), ".pf-promo.flock"), "-c", "echo held; exec sleep 60"], { stdio: ["ignore", "pipe", "ignore"] });
          holders.push(c);
          c.stdout!.on("data", () => resolve());
        }), () => Promise.all(holders.splice(0).map((c) => new Promise((r) => { c.on("exit", r); c.kill("SIGKILL"); })))],
        [`toolkit commit c1 on file was prepared in ws/${study}.promo`, async () => {
          await put(path.join(dir, "C", "manifest.json"), JSON.stringify({ ws: path.join(ws(`${study}.promo`), "TC", "tk") }));
          await put(commitJournalFile(root), JSON.stringify({ id: "c1", dir: path.join(dir, "C") }));
        }, () => rm(commitJournalFile(root))],
      ];
      for (const [why, on, off] of cases) {
        await on();
        const r = await releaseStudyPromo(root, study, log, { localRoot: local });
        expect(r.removed, why).toEqual([]);
        expect(r.kept, why).toContain(why);
        expect(wsNames(), why).toEqual(["p1", "p1.promo", `${study}.promo`, "study_p1__b-y.promo"]);
        await off();
      }
      // the study's heartbeat held by this process (its step ending) keeps nothing
      await put(path.join(root, "runs", study, "logs", ".run.active"), hb(process.pid));
      expect((await releaseStudyPromo(root, study, log, { localRoot: local })).removed).toEqual([`${study}.promo`]);
      expect(wsNames()).toEqual(["p1", "p1.promo", "study_p1__b-y.promo"]);
      expect(lines.join("\n")).toContain(`${study}: its step ended — released ws/${study}.promo`);
      // gone already, or no local root: nothing
      expect(await releaseStudyPromo(root, study, log, { localRoot: local })).toEqual({ removed: [] });
    } finally {
      await Promise.all(holders.map((c) => new Promise((r) => { c.on("exit", r); c.kill("SIGKILL"); })));
    }
  });

  it("removes the released run's paper tmp/ in the shared tree (no signature reads it), never while the run is in use", async () => {
    // (2026-11-11) agents' scratch builds: 17 GB in 222 papers
    await saveState(root, "p1", createVerifyInitialState("p1", {
      phase: "done", source: { input: "/p.tex", main_file: "main.tex", sha256: "x" }, targets: null, core_sha256: null,
      v1_rounds: 0, v1_5_rounds: 0, findings: [], report_path: null,
    }));
    const paper = path.join(root, "Papers", "P1");
    await put(path.join(paper, "Main.lean"), "theorem t : True := trivial\n");
    await put(path.join(root, "Toolkit", "A.lean"), "-- A\n");
    for (const f of ["Main.lean", "probe/Check.lean", ".lake/build/ir/Main.setup.json"]) await put(path.join(paper, "tmp", f), `${f}\n`);
    const sig = () => sourceSignature({ toolkitRoot: root, toolkitLibDir: path.join(root, "Toolkit") }, paper);
    const before = await sig();
    const hb = path.join(root, "runs", "p1", "logs", ".run.active");
    await put(hb, `${process.pid} 2026-11-10T00:00:00Z tok host=${os.hostname()} beat=15\n`);
    expect((await releaseWorkspaces(root, "p1", log, { localRoot: local })).tmp).toBeUndefined();
    expect(existsSync(path.join(paper, "tmp", "Main.lean"))).toBe(true);
    expect(lines.join("\n")).toContain("p1: its paper's tmp/ kept — its runner is live");
    await rm(hb);
    // no workspace on this machine: its tmp/ goes all the same; the paper's own files stay
    const r = await releaseWorkspaces(root, "p1", log, { localRoot: local });
    expect(r).toEqual({ removed: [], tmp: path.join(paper, "tmp") });
    expect(existsSync(path.join(paper, "tmp"))).toBe(false);
    expect(existsSync(path.join(paper, "Main.lean"))).toBe(true);
    // renamed away first, never beside the paper (its walks skip `tmp` alone), and the trash removed
    expect(readdirSync(paper).sort()).toEqual(["Main.lean"]);
    expect(readdirSync(path.join(root, ".lake", "paperformalizer", "trash"))).toEqual([]);
    expect(await sig()).toBe(before);
    expect(lines.join("\n")).toContain("p1: removed its paper's scratch Papers/P1/tmp");
    // none: nothing said
    expect((await releaseWorkspaces(root, "p1", log, { localRoot: local })).tmp).toBeUndefined();
  });

  it("a study run on its own takes the runner's heartbeat (runs/study_<slug>/logs/.run.active)", async () => {
    await writeSkeleton(root);
    await writeFile(path.join(root, "lakefile.toml"), await readFile(path.join(toolkitTemplateDir(), "lakefile.toml"), "utf8"));
    await put(path.join(root, "runs", "study_p1__b-x", "logs", ".run.active"), `${process.pid} 2026-11-10T00:00:00Z tok host=${os.hostname()} beat=15\n`);
    await expect(runStudyCli(["p1__b-x", "--toolkit", root, "--dry-run"])).rejects.toThrow(/another paperformalizer run is active on qid study_p1__b-x/);
  });

  it("renames a workspace into the trash before removing it: one the removal cannot finish is never seen as a workspace", async () => {
    if (process.getuid?.() === 0) return; // (root removes a read-only directory's entries)
    await run("p1", "done");
    await makeWs("p1");
    const stuck = path.join(ws("p1"), "TC", "tk", ".lake", "build", "lib");
    await chmod(stuck, 0o555);
    const r = await releaseWorkspaces(root, "p1", log, { localRoot: local });
    expect(r.removed).toEqual(["p1"]);
    expect(wsNames()).toEqual([`.trash-p1-${process.pid}`]);
    expect(lines.join("\n")).toContain("the next sweep removes it");
    // the next sweep removes the trash
    await chmod(path.join(local, "ws", `.trash-p1-${process.pid}`, "TC", "tk", ".lake", "build", "lib"), 0o755);
    await sweepWorkspaces(root, local, "other", log);
    await until(() => wsNames().length === 0);
    expect(wsNames()).toEqual([]);
  });

  it("sweeps only marked, finished runs' workspaces, never the one being ensured, never a directory of no run", async () => {
    await run("done1", "done", true);
    await run("failed1", "failed", true);
    await run("again", "v1_5", true); // marked, then resumed elsewhere: not finished any more
    await run("unmarked", "done");
    await run("busy", "done", true);
    await put(path.join(root, "runs", "busy", "proposals", "move_journal.json"), "{}");
    await run("me", "done", true);
    for (const n of ["done1", "done1.promo", "study_done1__b-x.promo", "failed1", "again", "unmarked", "busy", "me", "pilot0", "study_ghost__b-x.promo", "library-check", "_garden"]) await makeWs(n);
    await mkdir(path.join(local, "ws", ".trash-old-1"), { recursive: true });
    const swept = await sweepWorkspaces(root, local, "me", log);
    expect(swept.sort()).toEqual(["done1", "done1.promo", "failed1", "study_done1__b-x.promo"]);
    await until(() => !wsNames().some((n) => n.startsWith(".trash-")));
    expect(wsNames()).toEqual(["_garden", "again", "busy", "library-check", "me", "pilot0", "study_ghost__b-x.promo", "unmarked"]);
    const said = lines.join("\n");
    // (2026-11-11) the operator's own workspaces are of no run: kept, and not said
    expect(said).toContain("no run state for ws/pilot0, ws/study_ghost__b-x.promo (");
    expect(said).not.toMatch(/ws\/library-check|ws\/_garden/);
    expect(said).toContain("busy: released, but its workspaces are kept — a journal is on file");
  });
});
