// `paperformalizer demo`: the guided tour of a run for a first-time user (`DemoDriver`) on the real page,
// in a toolkit of its own; nothing it does reaches the user's toolkit, a model or Lean.
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { loadToolkitConfig } from "../toolkit/config.js";
import { openBrowser, uiToken } from "../ui/cli.js";
import { startUiServer } from "../ui/server.js";
import { DemoDriver, loadDemoScript, TEMPLATE_TOOLKIT_DIR } from "./driver.js";

export const DEMO_USAGE =
  "Usage: paperformalizer demo [--dir <path>] [--port N] [--open] [--restart]\n" +
  "  a guided tour of one run, on the real page: a made-up paper goes through every stage, and you make the\n" +
  "  decisions a run asks of you (a repair that weakens a main result, the two promotion rounds). The run is\n" +
  "  recorded: no model call, no Lean, no account, nothing written to your toolkit. Its own toolkit is --dir\n" +
  "  (default ~/.paperformalizer/demo); it goes on where you left it, --restart begins again. Ctrl+C stops it.";

export async function runDemoCli(argv: string[]): Promise<void> {
  const value = (flag: string): string | null => {
    const i = argv.indexOf(flag);
    if (i < 0) return null;
    const v = argv[i + 1];
    if (!v || v.startsWith("--")) throw new Error(`${flag} needs a value\n${DEMO_USAGE}`);
    return v;
  };
  const dir = path.resolve(value("--dir") ?? path.join(os.homedir(), ".paperformalizer", "demo"));
  const port = Number(value("--port") ?? 7342);
  if (!Number.isInteger(port) || port < 0 || port > 65535) throw new Error(`--port must be 0–65535\n${DEMO_USAGE}`);
  const config = path.join(dir, "paperformalizer.json");
  // the demo rewrites its toolkit's Lean trees and doc/: only an empty folder, or one it made (its marker)
  const made = existsSync(path.join(dir, ".lake", "paperformalizer-demo.json"));
  if (existsSync(dir) && !made && readdirSync(dir).length) throw new Error(`${dir} is not empty and is no demo toolkit (a toolkit of yours would be overwritten): give an empty or new --dir`);
  const fresh = !made || argv.includes("--restart");
  mkdirSync(dir, { recursive: true });
  if (fresh) {
    const cfg = JSON.parse(readFileSync(path.join(TEMPLATE_TOOLKIT_DIR, "paperformalizer.json.example"), "utf8"));
    writeFileSync(config, JSON.stringify({ ...cfg, owner: { name: "You (demo)", email: "demo@example.org" } }, null, 2) + "\n");
  }
  const driver = new DemoDriver(dir, loadDemoScript());
  driver.install(fresh ? 0 : undefined);
  const cfg = loadToolkitConfig({ explicit: dir });
  let ui;
  try {
    ui = await startUiServer(cfg, { port, token: uiToken(cfg), demo: driver });
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code !== "EADDRINUSE") throw err;
    ui = await startUiServer(cfg, { port: 0, token: uiToken(cfg), demo: driver });
  }
  console.log(`[demo] the demo toolkit is ${dir}`);
  console.log(`[demo] open: ${ui.url}`);
  console.log("[demo] Ctrl+C stops the demo; `paperformalizer demo` again goes on where you left it (--restart begins again).");
  if (argv.includes("--open")) openBrowser(ui.url);
  await new Promise<void>((resolve) => {
    const stop = () => void ui!.close().then(resolve);
    process.once("SIGINT", stop);
    process.once("SIGTERM", stop);
  });
}
