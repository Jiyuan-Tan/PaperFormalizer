// The deterministic gate every toolkit promotion passes, and the journal of what one wrote. A move
// never self-certifies: after its edits,
//     lake build <lib> → #print axioms (moved declarations) → lint_module_headers →
//     lint_toolkit_layout → toolkit index
// runs in order. A round-B move that fails it is left as written for the orchestrator (`move.ts`).
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { readFile, rmdir, unlink } from "node:fs/promises";
import path from "node:path";
import { bashBinary } from "../local_config.js";
import { withLakeBuildLock } from "../shared/build_mutex.js";
import { writeTextAtomic } from "../shared/json_atomic.js";
import { divisionBarrelPath, type ToolkitConfig } from "../toolkit/config.js";
import { parseLakefileLean, parseLakefileToml } from "../toolkit/lakefile.js";
import { parseAxiomReport } from "../verify/lean_evidence.js";
import { spawnWithInactivityTimeout } from "../workers/spawn.js";

export interface GateStep {
  label: string;
  cmd: string;
  cwd: string;
  /** Output check for a step whose exit code is not the whole verdict: a failure reason, or null. */
  check?: (log: string) => string | null;
}

export function shq(s: string): string {
  return /^[A-Za-z0-9_./:@=+-]+$/.test(s) ? s : `'${s.replace(/'/g, `'\\''`)}'`;
}

/** The toolkit-index step when the toolkit's lakefile declares a `toolkit_index` exe, else null. */
export async function detectToolkitIndexStep(
  cfg: ToolkitConfig,
  d: Pick<ApplyDeps, "exists" | "readFile">,
): Promise<GateStep | null> {
  const toml = path.join(cfg.toolkitRoot, "lakefile.toml");
  const lean = path.join(cfg.toolkitRoot, "lakefile.lean");
  let exes = new Set<string>();
  if (await d.exists(toml)) exes = parseLakefileToml(await d.readFile(toml)).exes;
  else if (await d.exists(lean)) exes = parseLakefileLean(await d.readFile(lean)).exes;
  return exes.has("toolkit_index") ? { label: "toolkit index", cmd: "lake exe toolkit_index", cwd: cfg.toolkitRoot } : null;
}

/** `#print axioms` probe over the moved declarations: imports every touched module, then one
 *  `#print axioms` line per declaration. Run by `lake env lean` (never lean-lsp: stale oleans). */
export function axiomsProbeText(modules: readonly string[], decls: readonly string[]): string {
  return [...new Set(modules)].sort().map((m) => `import ${m}`).join("\n") + "\n\n" +
    [...new Set(decls)].sort().map((d) => `#print axioms ${d}`).join("\n") + "\n";
}

/** Why a `#print axioms` output fails the gate (a declaration with no line, or an axiom beyond
 *  propext / Classical.choice / Quot.sound), or null when every declaration is clean. */
export function axiomsProbeFailure(log: string, decls: readonly string[]): string | null {
  const report = parseAxiomReport(log, [...new Set(decls)].sort());
  const bad = Object.entries(report).flatMap(([name, r]) =>
    r.error ? [`${name}: ${r.error}`] : r.clean ? [] : [`${name} depends on ${r.axioms.join(", ")}`]);
  return bad.length === 0 ? null : `moved declarations are not axiom-clean:\n  ${bad.join("\n  ")}`;
}

/** The toolkit gate, in order; the index step when available, the axioms step when given. */
export function toolkitGateChain(
  cfg: ToolkitConfig,
  toolsDir: string,
  indexStep: GateStep | null,
  axiomsStep: GateStep | null = null,
): GateStep[] {
  const headerPaths = [
    path.join(cfg.toolkitRoot, `${cfg.lib}.lean`),
    ...cfg.divisions.flatMap((div) => [divisionBarrelPath(cfg, div), path.join(cfg.toolkitLibDir, div)]),
  ];
  return [
    { label: "lake build", cmd: `lake build ${cfg.lib}`, cwd: cfg.toolkitRoot },
    ...(axiomsStep ? [axiomsStep] : []),
    {
      label: "module headers",
      cmd: `npx tsx bin/lint_module_headers.ts --strict --paths ${headerPaths.map(shq).join(" ")}`,
      cwd: toolsDir,
    },
    {
      label: "toolkit layout",
      cmd: `npx tsx bin/lint_toolkit_layout.ts --toolkit ${shq(cfg.toolkitRoot)} --scope toolkit`,
      cwd: toolsDir,
    },
    ...(indexStep ? [indexStep] : []),
  ];
}

/** File IO and commands of a promotion (tests replace `run`). */
export interface ApplyDeps {
  /** `timedOut`: the command was watchdog-killed rather than exiting — not proof it failed. */
  run: (cmd: string, cwd: string) => Promise<{ code: number; log: string; timedOut?: boolean }>;
  readFile: (p: string) => Promise<string>;
  writeFile: (p: string, text: string) => Promise<void>;
  removeFile: (p: string) => Promise<void>;
  removeDir?: (p: string) => Promise<void>;
  exists: (p: string) => Promise<boolean>;
}

export const realApplyDeps: ApplyDeps = {
  run: async (cmd, cwd) => {
    const exec = async () => {
      const env = { ...process.env };
      // Nested tsx subcommands open an IPC pipe under TMPDIR and collide on a per-run TMPDIR.
      delete env.TMPDIR;
      const maxTotalMs = Number(process.env.PAPERFORMALIZER_VERIFY_MAX_MS ?? 60 * 60 * 1000);
      const r = await spawnWithInactivityTimeout(bashBinary(), ["-c", cmd], {
        cwd, env, inactivityTimeoutMs: 30 * 60 * 1000, maxTotalMs,
      });
      const log = [r.stdout, r.stderr].filter(Boolean).join("\n");
      const timedOut = r.killedDueToInactivity || r.killedDueToLiveness != null || r.killedDueToTotalTimeout === true;
      return { code: (r.exitCode ?? 1) !== 0 ? 1 : 0, log, timedOut };
    };
    // Only Lake commands contend for the build directory.
    return cmd.startsWith("lake ") ? withLakeBuildLock(cwd, exec) : exec();
  },
  readFile: (p) => readFile(p, "utf8"),
  writeFile: (p, text) => writeTextAtomic(p, text),
  removeFile: async (p) => { await unlink(p).catch(() => {}); },
  removeDir: async (p) => { await rmdir(p).catch(() => {}); },
  exists: async (p) => existsSync(p),
};

export interface TargetPlacement { division: string; topic: string; module: string }

/** A toolkit target is a Lean module inside a topic directory of a configured division:
 *  `<lib>/<Division>/<Topic>/…/<File>.lean`. */
export function classifyTarget(target: string, cfg: Pick<ToolkitConfig, "lib" | "divisions">): TargetPlacement {
  const normalized = target.replace(/\\/g, "/");
  if (!normalized.endsWith(".lean")) throw new Error(`target must be a Lean module (.lean): ${target}`);
  const parts = normalized.slice(0, -".lean".length).split("/");
  if (parts[0] !== cfg.lib || !cfg.divisions.includes(parts[1] ?? "") || parts.length < 4) {
    throw new Error(
      `target must be ${cfg.lib}/<Division>/<Topic>/<File>.lean with Division one of ${cfg.divisions.join(", ")}: ${target}`,
    );
  }
  for (const seg of parts) {
    if (!/^[A-Za-z_][A-Za-z0-9_']*$/.test(seg)) throw new Error(`target segment is not a Lean identifier: ${seg} in ${target}`);
  }
  return { division: parts[1]!, topic: parts[2]!, module: parts.join(".") };
}

/** One entry per file a promotion wrote: its original bytes (null = did not exist) and the sha256
 *  of every state written to it; `generated` = a gate artifact (the index) of unknown content. */
export interface PromotionJournal {
  version: 1;
  slug: string;
  entries: Array<{ path: string; orig: string | null; after_sha: string[]; generated?: boolean }>;
  /** Directories the promotion created, deepest first. */
  created_dirs: string[];
}

export function sha256(text: string): string {
  return createHash("sha256").update(text, "utf8").digest("hex");
}
