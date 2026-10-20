import { afterEach, describe, expect, it } from "vitest";
import { execa, type ResultPromise } from "execa";
import { spawn } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import {
  haltIfStopping,
  liveChildren,
  processStartId,
  registerChild,
  resetChildRegistryForTest,
  setChildrenFile,
  clearChildrenFile,
  setStoppingForTest,
  stopRecordedRun,
  type ChildrenFile,
} from "../../src/shared/child_registry.js";
import { mapLimit } from "../../src/formalization/reviewer_verdicts.js";
import { spawnWithInactivityTimeout } from "../../src/workers/spawn.js";
import { parseVerifyArgsForTest } from "../../src/verify/cli.js";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const HARNESS = path.join(HERE, "..", "fixtures", "child_registry_harness.mts");
const posix = process.platform !== "win32";
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

/** Alive and not a zombie. */
function alive(pid: number): boolean {
  try {
    process.kill(pid, 0);
  } catch {
    return false;
  }
  try {
    const stat = readFileSync(`/proc/${pid}/stat`, "utf8");
    return stat.slice(stat.lastIndexOf(")") + 2)[0] !== "Z";
  } catch {
    return !existsSync("/proc/self/stat");
  }
}
async function until(pred: () => boolean, ms: number): Promise<boolean> {
  const end = Date.now() + ms;
  while (Date.now() < end) {
    if (pred()) return true;
    await sleep(50);
  }
  return pred();
}

const dirs: string[] = [];
const strays: number[] = [];
function tmp(): string {
  const d = mkdtempSync(path.join(os.tmpdir(), "child_registry_"));
  dirs.push(d);
  return d;
}
afterEach(() => {
  resetChildRegistryForTest();
  for (const pid of strays.splice(0)) {
    try {
      process.kill(pid, "SIGKILL");
    } catch {
      /* gone */
    }
  }
  for (const d of dirs.splice(0)) rmSync(d, { recursive: true, force: true });
});

function startHarness(mode: string, dir: string): ResultPromise {
  return execa(process.execPath, ["--import", "tsx/esm", HARNESS, mode, dir], { cwd: path.join(HERE, "..", ".."), reject: false });
}
async function grandchildren(dir: string, n: number): Promise<number[]> {
  const file = path.join(dir, "grandchild.pid");
  const read = () => (existsSync(file) ? readFileSync(file, "utf8").trim().split("\n").filter(Boolean).map(Number) : []);
  expect(await until(() => read().length >= n, 30_000)).toBe(true);
  const pids = read();
  strays.push(...pids);
  return pids;
}

describe("child registry", () => {
  it("adds and removes children, persisting children.json while alive", () => {
    const file = path.join(tmp(), "logs", "children.json");
    setChildrenFile(file);
    const unregister = registerChild(process.pid, { kind: "codex", tag: "m1", groupLeader: false, cmd: "bash -lc codex" });
    expect(liveChildren().map((c) => [c.pid, c.kind, c.tag])).toEqual([[process.pid, "codex", "m1"]]);
    const rec = JSON.parse(readFileSync(file, "utf8")) as ChildrenFile;
    expect(rec.children).toHaveLength(1);
    expect(rec.children[0]).toMatchObject({ pid: process.pid, kind: "codex", tag: "m1", startId: processStartId(process.pid) });
    expect(rec.runner.pid).toBe(process.pid);
    unregister();
    unregister();
    expect(liveChildren()).toEqual([]);
    expect((JSON.parse(readFileSync(file, "utf8")) as ChildrenFile).children).toEqual([]);
    clearChildrenFile();
    expect(existsSync(file)).toBe(false);
  });

  it("starts no new child once stopping (mapLimit slot and spawn both park)", async () => {
    setStoppingForTest(true);
    let started = 0;
    const settled = await Promise.race([
      mapLimit([1, 2, 3], 2, async () => {
        started += 1;
      }).then(() => "done"),
      spawnWithInactivityTimeout("true", [], { inactivityTimeoutMs: 1_000 }).then(() => "spawned"),
      sleep(300).then(() => "parked"),
    ]);
    expect(settled).toBe("parked");
    expect(started).toBe(0);
    expect(liveChildren()).toEqual([]);
    setStoppingForTest(false);
    await haltIfStopping();
  });

  it.skipIf(!posix)("SIGTERM kills the detached child's whole group, logs, clears children.json, exits 143", async () => {
    const dir = tmp();
    const h = startHarness("group", dir);
    const [gc] = await grandchildren(dir, 1);
    expect(alive(gc)).toBe(true);
    // the worker writes its pid file the moment it runs; the registry records it a tick later
    const readRec = () => JSON.parse(readFileSync(path.join(dir, "children.json"), "utf8")) as ChildrenFile;
    expect(await until(() => readRec().children.length > 0, 3_000)).toBe(true);
    expect(readRec().children.map((c) => [c.kind, c.groupLeader])).toEqual([["fake-codex", true]]);
    h.kill("SIGTERM");
    const r = await h;
    expect(r.exitCode).toBe(143);
    expect(await until(() => !alive(gc), 3_000)).toBe(true);
    expect(readFileSync(path.join(dir, "log.txt"), "utf8")).toContain("SIGTERM: stopped 1 child process(es)");
    expect(existsSync(path.join(dir, "children.json"))).toBe(false);
  }, 60_000);

  it.skipIf(!posix)("--stop cleans up after a SIGKILLed runner from children.json", async () => {
    const dir = tmp();
    const h = startHarness("group", dir);
    const [gc] = await grandchildren(dir, 1);
    h.kill("SIGKILL");
    await h;
    // No handler ran: the worker survives and the record is still there.
    expect(alive(gc)).toBe(true);
    expect(existsSync(path.join(dir, "children.json"))).toBe(true);
    const lines: string[] = [];
    const out = await stopRecordedRun(path.join(dir, "children.json"), { graceMs: 1_000, log: (l) => lines.push(l) });
    expect(out.refused).toEqual([]);
    expect(out.stopped).toBeGreaterThanOrEqual(1);
    expect(await until(() => !alive(gc), 3_000)).toBe(true);
    expect(existsSync(path.join(dir, "children.json"))).toBe(false);
  }, 60_000);
});

describe("verify --stop", () => {
  function record(dir: string, child: { pid: number; startId: string | null }): string {
    const file = path.join(dir, "children.json");
    const body: ChildrenFile = {
      runner: { pid: 0x3ffffffe, startId: null, cmd: "node leansmith.ts verify" },
      runTag: "",
      children: [{ ...child, kind: "codex", tag: "m", started: new Date().toISOString(), groupLeader: true, cmd: "sleep 300" }],
    };
    writeFileSync(file, JSON.stringify(body));
    return file;
  }
  function detachedSleep(): number {
    const c = spawn("sleep", ["300"], { detached: true, stdio: "ignore" });
    c.unref();
    strays.push(c.pid!);
    return c.pid!;
  }

  it.skipIf(!posix)("refuses a pid whose start time no longer matches", async () => {
    const dir = tmp();
    const pid = detachedSleep();
    const file = record(dir, { pid, startId: "some-boot:1" });
    const out = await stopRecordedRun(file, { graceMs: 500, log: () => {} });
    expect(out.stopped).toBe(0);
    expect(out.refused).toHaveLength(1);
    expect(out.refused[0]).toMatch(/start time differs/);
    await sleep(200);
    expect(alive(pid)).toBe(true);
  });

  it.skipIf(!posix)("leaves a run recorded on another machine of the mount alone, file included", async () => {
    const dir = tmp();
    const pid = detachedSleep();
    const file = record(dir, { pid, startId: null });
    const body = JSON.parse(readFileSync(file, "utf8")) as ChildrenFile;
    body.runner.host = "elsewhere";
    writeFileSync(file, JSON.stringify(body));
    const lines: string[] = [];
    const out = await stopRecordedRun(file, { graceMs: 500, log: (l) => lines.push(l) });
    expect(out.stopped).toBe(0);
    expect(out.refused[0]).toMatch(/recorded on elsewhere/);
    expect(lines.join("\n")).toContain("stop the run there");
    expect(existsSync(file)).toBe(true);
    expect(alive(pid)).toBe(true);
  });

  it.skipIf(!posix)("stops a live runner — the recorded pid, by its start time", async () => {
    const dir = tmp();
    const pid = detachedSleep();
    const file = path.join(dir, "children.json");
    const body: ChildrenFile = { runner: { pid, startId: processStartId(pid), cmd: "sleep 300" }, runTag: "", children: [] };
    writeFileSync(file, JSON.stringify(body));
    const out = await stopRecordedRun(file, { graceMs: 500, log: () => {} });
    expect(out).toEqual({ stopped: 1, refused: [] });
    expect(alive(pid)).toBe(false);
    expect(existsSync(file)).toBe(false);
  });

  it("parses --stop alone and refuses it with run flags", () => {
    expect(parseVerifyArgsForTest(["paper.tex", "--stop", "--slug", "s"]).stop).toBe(true);
    // the slug names the run: no paper is needed
    expect(parseVerifyArgsForTest(["--stop", "--slug", "s", "--toolkit", "tk"])).toMatchObject({ stop: true, slug: "s", input: "", toolkit: "tk" });
    expect(() => parseVerifyArgsForTest(["--stop"])).toThrow(/--stop needs the run: --slug <s>, or the paper/);
    expect(() => parseVerifyArgsForTest(["--slug", "s"])).toThrow(/Missing <paper\.tex\|dir\|archive>/);
    expect(parseVerifyArgsForTest(["paper.tex"]).stop).toBe(false);
    expect(() => parseVerifyArgsForTest(["paper.tex", "--stop", "--resume"])).toThrow(/--stop combines only with --toolkit and --slug/);
  });
});
