// `paperformalizer ui`: start the local UI for a toolkit and print its link.
import { randomBytes } from "node:crypto";
import { spawn } from "node:child_process";
import { mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import path from "node:path";
import { loadToolkitConfig, type ToolkitConfig } from "../toolkit/config.js";
import { startUiServer, type UiServer } from "./server.js";

export const UI_USAGE =
  "Usage: paperformalizer ui [--toolkit <path>] [--port N] [--open] [--new]\n" +
  "  the local web UI: your toolkit, its library, and each paper's run (live; decisions run the CLI).\n" +
  "  Listens on 127.0.0.1 only; open the printed link (it carries this session's key). One UI per\n" +
  "  toolkit: when one is already running this prints its link and exits (--new starts another).";

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

/** Open `url` in the default browser: `start` (Windows), `open` (macOS), `xdg-open` (others). */
export function openBrowser(url: string): void {
  const [cmd, args] =
    process.platform === "win32" ? ["cmd", ["/c", "start", "", url]] :
    process.platform === "darwin" ? ["open", [url]] : ["xdg-open", [url]];
  try {
    const child = spawn(cmd as string, args as string[], { detached: true, stdio: "ignore", windowsHide: true });
    child.on("error", () => {});
    child.unref();
  } catch {
    // no browser launcher: the printed link is enough
  }
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
      if (argv.includes("--open")) openBrowser(url);
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
  if (argv.includes("--open")) openBrowser(ui.url);
  await new Promise<void>((resolve) => {
    const stop = () => { clearUiState(cfg); void ui!.close().then(resolve); };
    process.once("SIGINT", stop);
    process.once("SIGTERM", stop);
  });
}
