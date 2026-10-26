// `paperformalizer ui`: start the local UI for a toolkit and print its link.
import { randomBytes } from "node:crypto";
import { spawn } from "node:child_process";
import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import path from "node:path";
import { loadToolkitConfig, type ToolkitConfig } from "../toolkit/config.js";
import { startUiServer, type UiServer } from "./server.js";

export const UI_USAGE =
  "Usage: paperformalizer ui [--toolkit <path>] [--port N] [--open] [--new]\n" +
  "  the local web UI: your toolkit, its library, and each paper's run (live; decisions run the CLI).\n" +
  "  Listens on 127.0.0.1 only; open the printed link (it carries this session's key). One UI per\n" +
  "  toolkit: when one is already running this prints its link and exits (--new starts another).\n" +
  "  --open opens the page in your browser, unless a tab already shows it.";

/** Where the running UI of a toolkit records itself (`.lake/` is ignored by every Lean project's git). */
export const uiStateFile = (cfg: ToolkitConfig): string => path.join(cfg.toolkitRoot, ".lake", "paperformalizer-ui.json");

/**
 * The toolkit's UI token, kept across restarts (readable by the owner only): the link the owner has
 * open, and the tab behind it, go on working when the UI is started again.
 */
export function uiToken(cfg: ToolkitConfig): string {
  const file = path.join(cfg.toolkitRoot, ".lake", "paperformalizer-ui.token");
  try {
    const t = readFileSync(file, "utf8").trim();
    if (/^[A-Za-z0-9_-]{20,}$/.test(t)) return t;
  } catch {
    // none yet
  }
  const t = randomBytes(18).toString("base64url");
  mkdirSync(path.dirname(file), { recursive: true });
  writeFileSync(file, `${t}\n`, { mode: 0o600 });
  return t;
}

/** Record `ui` as this toolkit's running UI (readable by the owner only). */
export function writeUiState(cfg: ToolkitConfig, ui: UiServer): void {
  const file = uiStateFile(cfg);
  mkdirSync(path.dirname(file), { recursive: true });
  writeFileSync(file, JSON.stringify({ pid: process.pid, port: Number(new URL(ui.url).port), url: ui.url, started: new Date().toISOString() }) + "\n", { mode: 0o600 });
}

/** Remove the record if it is this process's. */
export function clearUiState(cfg: ToolkitConfig): void {
  try {
    const st = JSON.parse(readFileSync(uiStateFile(cfg), "utf8")) as { pid?: number };
    if (st.pid === process.pid) rmSync(uiStateFile(cfg), { force: true });
  } catch {
    // no record
  }
}

/** The link of this toolkit's UI when one is running and answering, else null. */
export async function runningUi(cfg: ToolkitConfig): Promise<string | null> {
  let st: { pid?: number; port?: number; url?: string };
  try { st = JSON.parse(readFileSync(uiStateFile(cfg), "utf8")); } catch { return null; }
  if (!st.pid || !st.port || !st.url) return null;
  try { process.kill(st.pid, 0); } catch (err) { if ((err as NodeJS.ErrnoException).code !== "EPERM") return null; }
  try {
    const r = await fetch(`http://127.0.0.1:${st.port}/api/toolkit`, { signal: AbortSignal.timeout(2000) });
    const body = await r.text();
    return r.status === 403 && body.includes("paperformalizer ui") ? st.url : null;
  } catch {
    return null;
  }
}

/** The first of `cmds` found on the PATH of `env`, else null. */
function onPath(cmds: string[], env: NodeJS.ProcessEnv): string | null {
  const dirs = (env.PATH ?? "").split(path.delimiter).filter(Boolean);
  for (const c of cmds) for (const d of dirs) if (existsSync(path.join(d, c))) return c;
  return null;
}

/**
 * Open `url` in the default browser: `start` (Windows), `open` (macOS), `xdg-open` (others; `wslview`
 * on WSL without one). False when there is nothing to open it with — a Linux machine with no display
 * (a server reached over SSH) or no launcher: the link must then be opened by hand, on the user's
 * own computer.
 */
export function openBrowser(url: string, env: NodeJS.ProcessEnv = process.env, platform: NodeJS.Platform = process.platform): boolean {
  let cmd: string, args: string[];
  if (platform === "win32") [cmd, args] = ["cmd", ["/c", "start", "", url]];
  else if (platform === "darwin") [cmd, args] = ["open", [url]];
  else {
    if (!env.DISPLAY && !env.WAYLAND_DISPLAY && !env.WSL_DISTRO_NAME) return false;
    const found = onPath(["xdg-open", "wslview"], env);
    if (!found) return false;
    [cmd, args] = [found, [url]];
  }
  try {
    const child = spawn(cmd, args, { detached: true, stdio: "ignore", windowsHide: true });
    child.on("error", () => {});
    child.unref();
    return true;
  } catch {
    return false;
  }
}

/**
 * How many browser tabs hold the UI at `url` open; null when it cannot say (an older UI without the
 * count). The key is the link's own, so the query never touches the toolkit's key file.
 */
export async function pageViewers(url: string): Promise<number | null> {
  const u = new URL(url), port = u.port;
  try {
    const r = await fetch(`http://127.0.0.1:${port}/api/presence`, { headers: { Cookie: `tc_token_${port}=${u.searchParams.get("token") ?? ""}` }, signal: AbortSignal.timeout(2000) });
    if (!r.ok) return null;
    const v = (await r.json()) as { viewers?: unknown };
    return typeof v.viewers === "number" ? v.viewers : null;
  } catch {
    return null;
  }
}

/**
 * `--open`: open the page unless a tab already shows it, and say which — the orchestrating agent
 * reads these lines to tell the user where the page is.
 */
export function openUnlessShown(url: string, viewers: number | null, tag = "ui"): void {
  if (viewers) { console.log(`[${tag}] the page is already open in ${viewers} browser tab(s)`); return; }
  console.log(openBrowser(url)
    ? `[${tag}] opening the page in your browser`
    : `[${tag}] could not open a browser on this machine (no display, or no browser launcher): open the link above in a browser (from another computer, forward the port first)`);
}

/** How long a just-started UI waits for a tab left open from before (a browser restoring its tabs) to reconnect. */
export const REOPEN_GRACE_MS = 3000;

/** `--open` on a UI just started: a tab from before may come back on its own, so look first. */
export function openWhenStarted(ui: UiServer, tag = "ui", graceMs = REOPEN_GRACE_MS): void {
  setTimeout(() => openUnlessShown(ui.url, ui.viewers(), tag), graceMs).unref();
}

export async function runUiCli(argv: string[]): Promise<void> {
  const value = (flag: string): string | null => {
    const i = argv.indexOf(flag);
    if (i < 0) return null;
    const v = argv[i + 1];
    if (!v || v.startsWith("--")) throw new Error(`${flag} needs a value\n${UI_USAGE}`);
    return v;
  };
  const cfg = loadToolkitConfig({ explicit: value("--toolkit") });
  const port = Number(value("--port") ?? 7341);
  if (!Number.isInteger(port) || port < 0 || port > 65535) throw new Error(`--port must be 0–65535\n${UI_USAGE}`);
  if (!argv.includes("--new")) {
    const url = await runningUi(cfg);
    if (url) {
      console.log(`[ui] already running for ${cfg.toolkitRoot}`);
      console.log(`[ui] open: ${url}`);
      if (argv.includes("--open")) openUnlessShown(url, await pageViewers(url));
      return;
    }
  }
  let ui;
  try {
    ui = await startUiServer(cfg, { port, token: uiToken(cfg) });
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "EADDRINUSE") {
      ui = await startUiServer(cfg, { port: 0, token: uiToken(cfg) });
      console.log(`[ui] port ${port} is in use; using ${new URL(ui.url).port}`);
    } else throw err;
  }
  writeUiState(cfg, ui);
  console.log(`[ui] toolkit ${cfg.toolkitRoot}`);
  console.log(`[ui] open: ${ui.url}`);
  console.log("[ui] Ctrl+C stops the UI (runs it started keep going).");
  if (argv.includes("--open")) openWhenStarted(ui);
  await new Promise<void>((resolve) => {
    const stop = () => { clearUiState(cfg); void ui!.close().then(resolve); };
    process.once("SIGINT", stop);
    process.once("SIGTERM", stop);
  });
}
