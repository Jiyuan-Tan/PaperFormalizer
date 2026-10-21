// The `coordinate` phase: integrate a reviewed study module into the owner's toolkit.
//
// On reviewer PASS, a Claude COORDINATOR agent decides how the proven staging module enters
// the toolkit: which division it belongs to (by the division admission tests), which topic
// module it lands in (an existing module first), what existing declarations it should reuse,
// and how it is documented (per-declaration docstrings, a `/-! -/` overview for a new module).
//
// The intelligence is the coordinator's; SAFETY is deterministic TS. The coordinator emits a small
// MANIFEST (never free-form edits); this module applies it under snapshot / verify / rollback.
// Edits to EXISTING Lean files are INSERT-ONLY (asserted by byte preservation). A created
// module is wired into its division barrel, and every promoted declaration is recorded in the
// toolkit ledger. The coordinator never self-certifies: the gate chain
//     lake build <lib> → #print axioms (promoted declarations) → lint_module_headers →
//     lint_toolkit_layout → toolkit index
// runs deterministically and rolls everything back on any failure. Before any write, every
// op's Lean content is scanned for `sorry` / `admit` / `axiom` (outside comments and strings).
import { mkdir, readFile, unlink, rmdir, rm, readdir } from "node:fs/promises";
import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import path from "node:path";
import { withLakeBuildLock } from "../shared/build_mutex.js";
import { spawnWithInactivityTimeout } from "../workers/spawn.js";
import { bashBinary } from "../local_config.js";
import { MODELS } from "../models.js";
import { claudeRoleModel } from "../claude_roles.js";
import { runClaude as realRunClaude, writeLeanLspMcpConfig, type ClaudeRunInput } from "../workers/claude.js";
import { expectStringJsonOutput, persistCodexRaw } from "../shared/codex_json.js";
import { writeTextAtomic } from "../shared/json_atomic.js";
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import { isLeanModuleFile } from "../shared/lean_syntax.js";
import { insertImportSorted } from "../toolkit/barrels.js";
import {
  divisionBarrelPath, TOOLKIT_STAGING_SEGMENT, paperFormalizerToolsDir, type ToolkitConfig,
} from "../toolkit/config.js";
import { appendDeclarations, emptyLedger, parseLedger, serializeLedger, type LedgerDeclaration } from "../toolkit/ledger.js";
import { formatLayoutFinding, lintImportLayering, lintModuleHeader, runTokenIn } from "../toolkit/layout_lint.js";
import { declaredNames, forbiddenLeanTokens, leanImports } from "../toolkit/lean_source.js";
import { renamespace, topicNamespace, trimmedImportSets, usedModules, withImportBlock } from "../toolkit/namespaces.js";
import { rewriteReferences } from "../proposals/move.js";
import { parseAxiomReport } from "../verify/lean_evidence.js";
import { parseLakefileLean, parseLakefileToml } from "../toolkit/lakefile.js";
import { studyRunId, substrateRunDir } from "./paths.js";
import { logAgentCall } from "./log.js";
import { buildCoordinatorPrompt, toolkitPromptContext } from "./prompts.js";
import { effectiveTaxonomy, taxonomyPromptText } from "../toolkit/taxonomy.js";
import { parseCoordinationManifest, type CoordinationManifest, type StudyProvenance } from "./types.js";

// --- The coordinator agent (Claude → manifest) --------------------------------

export interface CoordinatorArgs {
  toolkit: ToolkitConfig;
  toolsDir: string;
  runDir: string;
  round: number;
  slug: string;
  requirement: string;
  leanDir: string;
  modulePrefix: string;
  leanFiles: string[];
  /** Directory where the coordinator WRITES file bodies / insert patches; the
   *  manifest references them by `from`. Keeps large content out of the JSON. */
  stagingDir: string;
  /** Failing integration-gate log from the previous coordinate attempt, fed back
   *  so the coordinator can fix placement / imports / a dedup that broke the build. */
  lastFailureLog: string | null;
}
/** The coordinator is a claude role (the scaffolder, fillers and reviewer run on codex). */
export interface CoordinatorDeps {
  runClaude: (o: ClaudeRunInput) => Promise<string>;
}

export async function runCoordinator(
  args: CoordinatorArgs,
  deps: CoordinatorDeps = { runClaude: realRunClaude },
): Promise<CoordinationManifest> {
  const topicTree = taxonomyPromptText(await effectiveTaxonomy(args.toolkit));
  const prompt = buildCoordinatorPrompt({ ...args, toolkit: toolkitPromptContext(args.toolkit, args.toolsDir), topicTree });
  // why: retries must not see staged bodies from an earlier coordinate attempt.
  await rm(args.stagingDir, { recursive: true, force: true });
  await mkdir(args.stagingDir, { recursive: true });
  const t0 = Date.now();
  let stdout = "";
  let parsed: CoordinationManifest | undefined;
  let parseError: string | undefined;
  try {
    // cwd = the toolkit root: the coordinator sees the staging module and the toolkit it
    // integrates into, and lean-lsp targets the toolkit's Lake project.
    stdout = await deps.runClaude({
      prompt, model: MODELS.claudeMain, cwd: args.toolkit.toolkitRoot,
      mcpConfigPath: writeLeanLspMcpConfig(args.toolkit.toolkitRoot),
      allowedTools: [
        "Read", "Write", "Edit", "Grep", "Glob",
        "mcp__lean-lsp__lean_leansearch", "mcp__lean-lsp__lean_loogle", "mcp__lean-lsp__lean_local_search",
        "mcp__lean-lsp__lean_hover_info", "mcp__lean-lsp__lean_file_outline",
      ],
    });
    // Persist raw stdout BEFORE parsing, so a parse failure leaves a forensic trail.
    await persistCodexRaw(args.runDir, "coordinator", stdout);
    parsed = parseCoordinationManifest(expectStringJsonOutput(stdout));
    await assertManifestFromFilesExist(args.stagingDir, parsed);
    return parsed;
  } catch (err) {
    parseError = err instanceof Error ? err.message : String(err);
    throw err;
  } finally {
    await logAgentCall(args.runDir, {
      agent: "coordinator", round: args.round, callId: "main", model: claudeRoleModel(MODELS.claudeMain),
      prompt, promptBytes: Buffer.byteLength(prompt), rawOutput: stdout,
      parsed, parseError, ok: parseError === undefined, durationMs: Date.now() - t0,
    });
  }
}

// --- Gate chain -----------------------------------------------------------------

export interface GateStep {
  label: string;
  cmd: string;
  cwd: string;
  /** Output check for a step whose exit code is not the whole verdict: a failure reason, or null. */
  check?: (log: string) => string | null;
}

function shq(s: string): string {
  return /^[A-Za-z0-9_./:@=+-]+$/.test(s) ? s : `'${s.replace(/'/g, `'\\''`)}'`;
}

/** The toolkit-index step, when the toolkit's lakefile declares a `toolkit_index` exe (read from
 *  the lakefile — `lakefile.toml` first, else `lakefile.lean` — via `toolkit/lakefile.ts`); else
 *  null. A live study never reaches the null case: `assertToolkitLakefile` refuses a toolkit
 *  without the exe at the start of the run. */
export async function detectToolkitIndexStep(
  cfg: ToolkitConfig,
  d: Pick<CoordinateApplyDeps, "exists" | "readFile">,
): Promise<GateStep | null> {
  const toml = path.join(cfg.toolkitRoot, "lakefile.toml");
  const lean = path.join(cfg.toolkitRoot, "lakefile.lean");
  let exes = new Set<string>();
  if (await d.exists(toml)) exes = parseLakefileToml(await d.readFile(toml)).exes;
  else if (await d.exists(lean)) exes = parseLakefileLean(await d.readFile(lean)).exes;
  return exes.has("toolkit_index") ? { label: "toolkit index", cmd: "lake exe toolkit_index", cwd: cfg.toolkitRoot } : null;
}

/** `#print axioms` probe over the promoted declarations: imports every touched module, then one
 *  `#print axioms` line per declaration. Run by `lake env lean` (never lean-lsp: stale oleans). */
export function axiomsProbeText(modules: readonly string[], decls: readonly string[]): string {
  return [...new Set(modules)].sort().map((m) => `import ${m}`).join("\n") + "\n\n" +
    [...new Set(decls)].sort().map((d) => `#print axioms ${d}`).join("\n") + "\n";
}

/** Why a `#print axioms` probe output fails the gate (a declaration with no line, or an axiom
 *  beyond propext / Classical.choice / Quot.sound), or null when every declaration is clean. */
export function axiomsProbeFailure(log: string, decls: readonly string[]): string | null {
  const report = parseAxiomReport(log, [...new Set(decls)].sort());
  const bad = Object.entries(report).flatMap(([name, r]) =>
    r.error ? [`${name}: ${r.error}`] : r.clean ? [] : [`${name} depends on ${r.axioms.join(", ")}`]);
  return bad.length === 0 ? null : `promoted declarations are not axiom-clean:\n  ${bad.join("\n  ")}`;
}

/** The `#print axioms` gate step over a probe file written by `applyManifest`. */
export function axiomsGateStep(cfg: ToolkitConfig, probePath: string, decls: readonly string[]): GateStep {
  return {
    label: "print axioms",
    cmd: `lake env lean ${shq(probePath.split(path.sep).join("/"))}`,
    cwd: cfg.toolkitRoot,
    check: (log) => axiomsProbeFailure(log, decls),
  };
}

/** Where `applyManifest` writes the axioms probe: the study's run record (never the toolkit). */
export function axiomsProbePath(cfg: ToolkitConfig, slug: string): string {
  return path.join(substrateRunDir(cfg.toolkitRoot, slug), "promotion_axioms.lean");
}

/** The deterministic integration gate, in order. The index step is present only when available;
 *  the axioms step whenever the promotion declares anything. */
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

export const INDEX_STEP_SKIPPED =
  "[toolkit index] skipped: the toolkit lakefile defines no `toolkit_index` exe (see templates/toolkit/lakefile.toml)";

// --- Deterministic manifest apply (snapshot / verify / rollback) ---------------

export interface CoordinateApplyDeps {
  /** `timedOut` is set when the command was watchdog-killed (inactivity/liveness)
   *  rather than exiting on its own. A kill is NOT proof the step failed, so the
   *  caller escalates instead of rolling back proven work. */
  run: (cmd: string, cwd: string) => Promise<{ code: number; log: string; timedOut?: boolean }>;
  readFile: (p: string) => Promise<string>;
  writeFile: (p: string, text: string) => Promise<void>;
  removeFile: (p: string) => Promise<void>;
  removeDir?: (p: string) => Promise<void>;
  exists: (p: string) => Promise<boolean>;
}

export const realApplyDeps: CoordinateApplyDeps = {
  run: async (cmd, cwd) => {
    const exec = async () => {
      const env = { ...process.env };
      // Nested tsx subcommands open an IPC pipe under TMPDIR and collide on a per-run TMPDIR.
      delete env.TMPDIR;
      // Inactivity bounds a SILENT hang; the wall-clock backstop bounds a step that spins
      // while emitting output. `PAPERFORMALIZER_VERIFY_MAX_MS=0` disables the backstop. Both kinds
      // surface as `timedOut` → escalate (preserve).
      const maxTotalMs = Number(process.env.PAPERFORMALIZER_VERIFY_MAX_MS ?? 60 * 60 * 1000);
      const r = await spawnWithInactivityTimeout(bashBinary(), ["-c", cmd], {
        cwd, env, inactivityTimeoutMs: 30 * 60 * 1000, maxTotalMs,
      });
      const log = [r.stdout, r.stderr].filter(Boolean).join("\n");
      const timedOut =
        r.killedDueToInactivity || r.killedDueToLiveness != null || r.killedDueToTotalTimeout === true;
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

/** Resolve `rel` against `root`, refusing any path that escapes it. */
function resolveInside(root: string, rel: string): string {
  const abs = path.resolve(root, rel);
  const back = path.relative(root, abs);
  if (back === "" || back.startsWith("..") || path.isAbsolute(back)) {
    throw new Error(`manifest op path escapes its root: ${rel}`);
  }
  return abs;
}

async function listStagedFiles(root: string, dir = root): Promise<Set<string>> {
  const out = new Set<string>();
  const entries = await readdir(dir, { withFileTypes: true }).catch(() => []);
  for (const entry of entries) {
    const abs = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      for (const nested of await listStagedFiles(root, abs)) out.add(nested);
    } else if (entry.isFile()) {
      out.add(path.relative(root, abs));
    }
  }
  return out;
}

async function assertManifestFromFilesExist(stagingDir: string, manifest: CoordinationManifest): Promise<void> {
  const staged = await listStagedFiles(stagingDir);
  for (const op of manifest.ops) {
    const abs = resolveInside(stagingDir, op.from);
    const rel = path.relative(stagingDir, abs);
    // why: the staging dir was cleared for this attempt, so membership proves this round wrote it.
    if (!staged.has(rel)) throw new Error(`manifest references unstaged from file: ${op.from}`);
  }
}

/** The import lines of a merge whose content is import lines only (`import M` / `public import M`,
 * blank lines aside), else null. */
export function importOnlyLines(content: string): string[] | null {
  const lines = content.split(/\r?\n/).map((l) => l.trim()).filter((l) => l !== "");
  return lines.length > 0 && lines.every((l) => /^(?:public\s+)?import\s+[\w.«»']+$/.test(l)) ? lines : null;
}

/**
 * Insert `insert` into `orig` after the first line containing `anchor` (empty
 * anchor → append at end of file). Returns the merged text plus the exact
 * inserted segment and its offset, so the caller can assert byte-preservation.
 */
export function applyInsertOnly(
  orig: string,
  anchor: string,
  insert: string,
): { merged: string; at: number; segment: string } {
  const block = insert.endsWith("\n") ? insert : `${insert}\n`;
  if (anchor.trim() === "") {
    const lead = orig.length === 0 || orig.endsWith("\n") ? "\n" : "\n\n";
    const segment = `${lead}${block}`;
    return { merged: orig + segment, at: orig.length, segment };
  }
  const lines = orig.split("\n");
  const idx = lines.findIndex((l) => l.includes(anchor));
  if (idx < 0) throw new Error(`merge_lean anchor not found: ${JSON.stringify(anchor)}`);
  // Char offset of the start of line idx+1 (i.e. just after line idx's newline).
  let at = 0;
  for (let i = 0; i <= idx; i++) at += lines[i].length + 1;
  if (at > orig.length) at = orig.length; // last line had no trailing newline
  const segment = `${block}\n`;
  const merged = orig.slice(0, at) + segment + orig.slice(at);
  return { merged, at, segment };
}

/** A merge must leave every pre-existing byte intact: removing the inserted
 *  segment at its offset must reproduce the original exactly. */
function assertInsertOnly(orig: string, merged: string, at: number, segment: string): void {
  const without = merged.slice(0, at) + merged.slice(at + segment.length);
  if (without !== orig) {
    throw new Error("insert-only invariant violated: a merge would change existing bytes");
  }
}

export interface TargetPlacement { division: string; topic: string; module: string }

/**
 * Map a manifest target to its division and topic. A toolkit target is a Lean module inside a
 * topic directory of a configured division: `<lib>/<Division>/<Topic>/…/<File>.lean`.
 */
export function classifyTarget(target: string, cfg: Pick<ToolkitConfig, "lib" | "divisions">): TargetPlacement {
  const normalized = target.replace(/\\/g, "/");
  if (!normalized.endsWith(".lean")) {
    throw new Error(`manifest target must be a Lean module (.lean): ${target}`);
  }
  const parts = normalized.slice(0, -".lean".length).split("/");
  if (parts[0] !== cfg.lib || !cfg.divisions.includes(parts[1] ?? "") || parts.length < 4) {
    throw new Error(
      `manifest target must be ${cfg.lib}/<Division>/<Topic>/<File>.lean with Division one of ` +
        `${cfg.divisions.join(", ")}: ${target}`,
    );
  }
  for (const seg of parts) {
    if (!/^[A-Za-z_][A-Za-z0-9_']*$/.test(seg)) throw new Error(`manifest target segment is not a Lean identifier: ${seg} in ${target}`);
  }
  return { division: parts[1], topic: parts[2], module: parts.join(".") };
}

/** Reject target segments carrying a run token (see `runTokenIn`) before the first mutation. */
function assertNoRunNamedTarget(target: string): void {
  for (const seg of target.replace(/\\/g, "/").replace(/\.lean$/, "").split("/")) {
    const why = runTokenIn(seg);
    if (why) throw new Error(`manifest target segment ${seg} ${why}: ${target}`);
  }
}

/** Import and reference checks on staged Lean content (create body or merge patch). */
async function assertContentAllowed(
  content: string,
  target: string,
  placement: TargetPlacement,
  cfg: ToolkitConfig,
  createdModules: ReadonlySet<string>,
  d: CoordinateApplyDeps,
): Promise<void> {
  const staging = `${cfg.lib}.${TOOLKIT_STAGING_SEGMENT}`;
  if (new RegExp(`\\b${staging.replace(/\./g, "\\.")}\\b`).test(maskLeanCommentsAndStrings(content))) {
    throw new Error(`final Lean content still references study staging (${staging}.*): ${target}`);
  }
  const imports = leanImports(content);
  const layering = lintImportLayering(placement.module, imports, {
    lib: cfg.lib, papersLib: cfg.papersLib, divisions: cfg.divisions,
  }, target);
  if (layering.length > 0) {
    throw new Error(`disallowed import in ${target}:\n  ${layering.map(formatLayoutFinding).join("\n  ")}`);
  }
  for (const imp of imports) {
    const root = imp.module.split(".")[0];
    let file: string | null = null;
    if (root === cfg.lib) file = path.join(cfg.toolkitRoot, ...imp.module.split(".")) + ".lean";
    const base = cfg.baseLibraries.find((b) => b.name === root && b.kind === "path" && b.path);
    if (base?.path) file = path.join(base.path, ...imp.module.split(".")) + ".lean";
    if (!file || createdModules.has(imp.module) || (await d.exists(file))) continue;
    const leaf = imp.module.slice(imp.module.lastIndexOf(".") + 1);
    const candidates = [...createdModules].filter((m) => m.endsWith(`.${leaf}`));
    const hint = candidates.length === 1 ? `; did you mean ${candidates[0]}?` : "";
    throw new Error(`unresolved import in ${target}: ${imp.module}${hint}`);
  }
}

function isoDate(now: Date): string {
  return now.toISOString().slice(0, 10);
}

export interface ApplyManifestArgs {
  toolkit: ToolkitConfig;
  /** PaperFormalizer `tools/` directory (the lint bins run from here). */
  toolsDir: string;
  /** Root the manifest's `from` paths resolve against (where the coordinator staged the bodies). */
  stagingDir: string;
  leanFiles: string[];
  manifest: CoordinationManifest;
  slug: string;
  modulePrefix: string;
  /** Clock for ledger dates (tests). */
  now?: Date;
  /** Index step override; `undefined` = detect from the toolkit lakefile. */
  indexStep?: GateStep | null;
  /** Ledger provenance when the study builds an accepted proposal (else `{kind: "study"}`). */
  provenance?: StudyProvenance;
}

export async function applyManifest(
  args: ApplyManifestArgs,
  d: CoordinateApplyDeps = realApplyDeps,
): Promise<{ ok: boolean; log: string; timedOut?: boolean }> {
  const { toolkit: cfg, stagingDir, leanFiles, manifest, slug } = args;
  const root = cfg.toolkitRoot;
  const logs: string[] = [];
  // abs path → original content (null = file did not exist, so rollback deletes).
  const snapshots = new Map<string, string | null>();
  // Write-ahead journal of every toolkit write (`coordinate_journal.json` in the run record): a
  // crash mid-apply or mid-gate leaves it behind, and the next attempt restores the toolkit from
  // it (`recoverInterruptedApply`) before re-applying, so a merge is never applied twice.
  const journalFile = coordinateJournalPath(cfg, slug);
  const journal: CoordinateJournal = { version: 1, slug, entries: [], created_dirs: [] };
  const persistJournal = () => d.writeFile(journalFile, `${JSON.stringify(journal, null, 2)}\n`);
  const snap = async (abs: string, afterSha: string | null = null) => {
    if (!snapshots.has(abs)) {
      snapshots.set(abs, (await d.exists(abs)) ? await d.readFile(abs) : null);
      journal.entries.push({ path: abs, orig: snapshots.get(abs)!, after_sha: [] });
    }
    const entry = journal.entries.find((e) => e.path === abs)!;
    if (afterSha === null) entry.generated = true;
    else if (!entry.after_sha.includes(afterSha)) entry.after_sha.push(afterSha);
    await persistJournal();
  };
  /** Journal the intent, then write: the journal always knows every byte state this apply produced. */
  const write = async (abs: string, text: string) => {
    await snap(abs, sha256(text));
    await d.writeFile(abs, text);
  };
  /** Record the directories a write under `dir` will create (deepest first), so a rollback
   *  removes them again. */
  const noteCreatedDirs = async (dir: string) => {
    const created: string[] = [];
    for (let cur = dir; cur.startsWith(`${root}${path.sep}`) && !(await d.exists(cur)); cur = path.dirname(cur)) created.push(cur);
    for (const c of created) if (!journal.created_dirs.includes(c)) journal.created_dirs.push(c);
  };
  const rollback = async () => {
    for (const [abs, orig] of snapshots) {
      if (orig === null) await d.removeFile(abs);
      else await d.writeFile(abs, orig);
    }
    for (const dir of journal.created_dirs) await d.removeDir?.(dir);
  };
  const finish = async <T>(result: T): Promise<T> => {
    await d.removeFile(journalFile);
    return result;
  };
  try {
    // Validate every op before any write, so a bad later op cannot transiently mutate the tree.
    const placements = manifest.ops.map((op) => {
      if (op.kind === "write_file") {
        throw new Error(`write_file is not a toolkit op (the ledger is written by the system): ${op.target}`);
      }
      resolveInside(root, op.target);
      assertNoRunNamedTarget(op.target);
      return classifyTarget(op.target, cfg);
    });
    const createdModules = new Set<string>();
    manifest.ops.forEach((op, i) => { if (op.kind === "create_file") createdModules.add(placements[i].module); });
    // Proof holes and new axioms refuse the whole manifest before the first write.
    const contents: string[] = [];
    for (const [i, op] of manifest.ops.entries()) {
      const content = await d.readFile(resolveInside(stagingDir, op.from));
      const holes = forbiddenLeanTokens(content);
      if (holes.length > 0) {
        throw new Error(
          `manifest op ${i + 1} (${op.kind} ${op.target}) contains ` +
            holes.map((h) => `\`${h.token}\` at line ${h.line + 1}`).join(", ") +
            `; the toolkit admits only proved, axiom-clean content — manifest refused, nothing written`,
        );
      }
      contents.push(content);
    }

    // Toolkit convention: a created module declares everything in its topic namespace; the other
    // ops' references follow the renames.
    const renames = new Map<string, string>();
    for (const [i, op] of manifest.ops.entries()) {
      if (op.kind !== "create_file") continue;
      const imported = leanImports(contents[i]!).map((x) => topicNamespace(x.module)).filter((x): x is string => !!x);
      const r = renamespace(contents[i]!, placements[i]!.module, (ns) => imported.includes(ns));
      if (r.renames.size === 0) continue;
      contents[i] = r.text;
      for (const [a, b] of r.renames) renames.set(a, b);
      logs.push(`[namespace] ${op.target}: ${[...r.renames].map(([a, b]) => `${a} → ${b}`).join(", ")}`);
    }
    if (renames.size) for (const i of contents.keys()) contents[i] = rewriteReferences(contents[i]!, renames).text;

    const ledgerEntries: LedgerDeclaration[] = [];
    const date = isoDate(args.now ?? new Date());
    const prov = args.provenance;
    const leaf = (n: string) => n.slice(n.lastIndexOf(".") + 1);
    const record = (placement: TargetPlacement, text: string, range?: { from: number; to: number }) => {
      for (const decl of declaredNames(text, range)) {
        if (decl.isPrivate) continue;
        ledgerEntries.push({
          name: decl.name, module: placement.module, division: placement.division,
          origin: prov ? { ...prov.origin, run_id: studyRunId(slug) } : { kind: "study", slug, run_id: studyRunId(slug) },
          date, decision: prov?.decision ?? "accepted-by-study",
          ...(prov ? { nearest_existing: prov.nearest_existing } : {}),
          used_by: [],
        });
      }
    };
    // An accepted proposal's main result is the main node; what the study added beside it, its auxiliaries.
    const tierEntries = (entries: LedgerDeclaration[]): LedgerDeclaration[] => {
      const main = prov?.main ? entries.find((e) => leaf(e.name) === leaf(prov.main!)) : undefined;
      if (!main) return entries;
      return entries.map((e) => (e === main
        ? { ...e, tier: "main", ...(prov!.title ? { title: prov!.title } : {}) }
        : { ...e, tier: "aux", owners: [main.name] }));
    };
    const newModules: TargetPlacement[] = [];
    const touchedDivisions = new Set<string>();

    for (const [i, op] of manifest.ops.entries()) {
      const placement = placements[i];
      const abs = resolveInside(root, op.target);
      const content = contents[i];
      await assertContentAllowed(content, op.target, placement, cfg, createdModules, d);
      touchedDivisions.add(placement.division);
      if (op.kind === "create_file") {
        if (op.newModule !== placement.module) {
          throw new Error(`create_file newModule must match target (${placement.module}): ${op.newModule ?? "(missing)"}`);
        }
        const header = lintModuleHeader(op.target, content);
        if (header.length > 0) {
          throw new Error(`new module ${op.target} breaks the header contract:\n  ${header.map(formatLayoutFinding).join("\n  ")}`);
        }
        if (await d.exists(abs)) {
          // Recovery after an interrupted verification pass: accept only an exact byte match.
          if ((await d.readFile(abs)) !== content) {
            throw new Error(`create_file target already exists with different content (use merge_lean): ${op.target}`);
          }
        } else {
          await noteCreatedDirs(path.dirname(abs));
          await write(abs, content);
        }
        newModules.push(placement);
        record(placement, content);
      } else if (op.kind === "merge_lean") {
        if (!(await d.exists(abs))) throw new Error(`merge_lean target does not exist: ${op.target}`);
        const orig = await d.readFile(abs);
        const importLines = importOnlyLines(content);
        if (importLines) {
          // Imports are placed by the runner, sorted into the module's import block: an anchor
          // puts them at a line, and the header lint then refuses the block.
          await write(abs, importLines.reduce((text, line) => insertImportSorted(text, line), orig));
        } else {
          const { merged, at, segment } = applyInsertOnly(orig, op.anchor, content);
          assertInsertOnly(orig, merged, at, segment);
          await write(abs, merged);
          record(placement, merged, { from: at, to: at + segment.length });
        }
      }
    }

    // Wire each created module into its division barrel.
    for (const placement of newModules) {
      const barrel = divisionBarrelPath(cfg, placement.division);
      if (!(await d.exists(barrel))) throw new Error(`division barrel missing: ${path.relative(root, barrel)}`);
      const text = await d.readFile(barrel);
      if (!isLeanModuleFile(text)) throw new Error(`division barrel is not a module-system file: ${path.relative(root, barrel)}`);
      await write(barrel, insertImportSorted(text, `public import ${placement.module}`));
    }

    // Provenance: append one ledger record per promoted public declaration.
    const ledgerText = (await d.exists(cfg.ledgerPath)) ? await d.readFile(cfg.ledgerPath) : null;
    const { ledger, added, skipped } = appendDeclarations(
      ledgerText === null ? emptyLedger() : parseLedger(ledgerText, cfg.ledgerPath), tierEntries(ledgerEntries));
    if (added.length > 0) await write(cfg.ledgerPath, serializeLedger(ledger));
    logs.push(
      `[ledger] ${added.length} declaration(s) recorded` +
        (skipped.length > 0 ? `, ${skipped.length} already present` : "") +
        (added.length > 0 ? `: ${added.map((e) => e.name).join(", ")}` : ""),
    );

    // Integration gate — any failure rolls back; a watchdog kill preserves and escalates.
    const indexStep = args.indexStep !== undefined ? args.indexStep : await detectToolkitIndexStep(cfg, d);
    if (!indexStep) logs.push(INDEX_STEP_SKIPPED);
    else await snap(cfg.indexPath, null); // the index exe rewrites this generated artifact
    // `#print axioms` over every promoted public declaration (the probe lives in the run record).
    const promotedDecls = ledgerEntries.map((e) => e.name);
    const touchedModules = placements.map((p) => p.module);
    let axiomsStep: GateStep | null = null;
    if (promotedDecls.length > 0) {
      const probe = axiomsProbePath(cfg, slug);
      await d.writeFile(probe, axiomsProbeText(touchedModules, promotedDecls));
      axiomsStep = axiomsGateStep(cfg, probe, promotedDecls);
    }
    for (const step of toolkitGateChain(cfg, args.toolsDir, indexStep, axiomsStep)) {
      const r = await d.run(step.cmd, step.cwd);
      logs.push(`$ (${step.cwd}) ${step.cmd}\n${r.log}`);
      if (r.timedOut) {
        // A kill is not a compile error, and the files are already in the toolkit: rolling back
        // would destroy proven work and a mid-build rollback is itself unsafe. Preserve and
        // escalate; the promotion is UNVERIFIED until a human re-runs the gate.
        // The human who verifies the promotion owns it now: no automatic recovery may undo it.
        return finish({
          ok: false, timedOut: true,
          log: `${logs.join("\n\n")}\n\n[coordinate] gate step '${step.label}' was watchdog-killed (unverified); files left in place for human verification (NOT rolled back).`,
        });
      }
      const why = r.code !== 0 ? null : step.check?.(r.log) ?? null;
      if (r.code !== 0 || why) {
        await rollback();
        return finish({
          ok: false,
          log: `${logs.join("\n\n")}\n\n[coordinate] gate step '${step.label}' failed${why ? `: ${why}` : ""}; rolled back.`,
        });
      }
    }
    // Each created module imports what it uses: its header trimmed to the modules of its
    // declarations' constants, kept only when the toolkit still builds.
    const created = newModules.map((pl) => pl.module);
    if (created.length > 0) logs.push(...(await trimCreatedImports(cfg, slug, created, write, d)));
    // Success — delete the staging sources and the now-empty staging dirs (best-effort).
    for (const f of leanFiles) await d.removeFile(f);
    if (d.removeDir) {
      const dirs = Array.from(new Set(leanFiles.map((f) => path.dirname(f))));
      for (const dir of dirs) {
        await d.removeDir(dir);
        await d.removeDir(path.dirname(dir));
      }
    }
    return finish({
      ok: true,
      log: `${logs.join("\n\n")}\n\n[coordinate] applied ${manifest.ops.length} op(s) in division(s) ${[...touchedDivisions].join(", ")}.` +
        (manifest.notes ? `\nnotes: ${manifest.notes}` : ""),
    });
  } catch (err) {
    await rollback();
    const msg = err instanceof Error ? err.message : String(err);
    return finish({ ok: false, log: `${logs.join("\n\n")}\n\n[coordinate] apply error: ${msg}` });
  }
}

/** Trim the headers of the modules a study created (`namespaces.ts`): a `--graph` scan of them
 *  gives the modules their declarations use; each smaller header is tried with `lake build <lib>`
 *  and kept only when it builds (the next variant adds the common tactics; else the original stays).
 *  Skipped when the toolkit has no `candidate_scan` exe. */
async function trimCreatedImports(
  cfg: ToolkitConfig,
  slug: string,
  modules: readonly string[],
  write: (abs: string, text: string) => Promise<void>,
  d: CoordinateApplyDeps,
): Promise<string[]> {
  const toml = path.join(cfg.toolkitRoot, "lakefile.toml");
  const lean = path.join(cfg.toolkitRoot, "lakefile.lean");
  const exes = (await d.exists(toml)) ? parseLakefileToml(await d.readFile(toml)).exes
    : (await d.exists(lean)) ? parseLakefileLean(await d.readFile(lean)).exes : new Set<string>();
  if (!exes.has("candidate_scan")) return ["[imports] not trimmed: the toolkit lakefile declares no candidate_scan exe"];
  const out = path.join(substrateRunDir(cfg.toolkitRoot, slug), "import_scan.json");
  const scanCmd = `lake exe candidate_scan -- --graph --toolkit-prefix ${cfg.lib} --papers-prefix ${cfg.papersLib} --modules ${modules.join(",")} --out ${shq(out)}`;
  const r = await d.run(scanCmd, cfg.toolkitRoot);
  if (r.code !== 0 || !(await d.exists(out))) return [`[imports] not trimmed: the scan failed\n${r.log.split("\n").slice(-5).join("\n")}`];
  const decls = (JSON.parse(await d.readFile(out)) as { declarations?: Parameters<typeof usedModules>[0] }).declarations ?? [];
  const logs: string[] = [];
  for (const module of modules) {
    const abs = `${path.join(cfg.toolkitRoot, ...module.split("."))}.lean`;
    const original = await d.readFile(abs);
    let kept = false;
    for (const set of trimmedImportSets(original, usedModules(decls, module, { lib: cfg.lib, papersLib: cfg.papersLib }))) {
      await write(abs, withImportBlock(original, set));
      const b = await d.run(`lake build ${cfg.lib}`, cfg.toolkitRoot);
      if (b.code === 0 && !b.timedOut) {
        logs.push(`[imports] ${module}: header trimmed to ${set.length} import(s)`);
        kept = true;
        break;
      }
      await write(abs, original);
      if (b.timedOut) break;
    }
    if (!kept) logs.push(`[imports] ${module}: its trimmed header does not build; the original header is kept`);
  }
  return logs;
}

// --- Crash recovery (write-ahead journal) ---------------------------------------

export interface CoordinateJournal {
  version: 1;
  slug: string;
  /** One entry per toolkit file the apply wrote: its original bytes (null = did not exist) and
   *  the sha256 of every state the apply wrote to it; `generated` = a gate artifact (the index)
   *  whose content the apply does not know in advance. */
  entries: Array<{ path: string; orig: string | null; after_sha: string[]; generated?: boolean }>;
  /** Directories the apply created, deepest first. */
  created_dirs: string[];
}

function sha256(text: string): string {
  return createHash("sha256").update(text, "utf8").digest("hex");
}

/** `runs/study_<slug>/coordinate_journal.json`: present only while an apply is in flight, or
 *  after a crash interrupted one. */
export function coordinateJournalPath(cfg: ToolkitConfig, slug: string): string {
  return path.join(substrateRunDir(cfg.toolkitRoot, slug), "coordinate_journal.json");
}

/**
 * Undo an apply a crash interrupted (mid-write or mid-gate): restore every journaled toolkit file
 * to its original bytes and remove the directories the apply created, then drop the journal.
 * Returns null when there is nothing to recover. A file whose current bytes are neither its
 * original nor a state the apply wrote was changed by someone else: nothing is touched and
 * `conflict` names it, for a human to resolve.
 */
export async function recoverInterruptedApply(
  cfg: ToolkitConfig,
  slug: string,
  d: CoordinateApplyDeps = realApplyDeps,
): Promise<{ ok: boolean; log: string; conflict?: string[] } | null> {
  return recoverInterruptedApplyAt(cfg, coordinateJournalPath(cfg, slug), d);
}

/** `recoverInterruptedApply` for a journal at any path. */
export async function recoverInterruptedApplyAt(
  cfg: ToolkitConfig,
  file: string,
  d: CoordinateApplyDeps = realApplyDeps,
): Promise<{ ok: boolean; log: string; conflict?: string[] } | null> {
  if (!(await d.exists(file))) return null;
  const journal = JSON.parse(await d.readFile(file)) as CoordinateJournal;
  const plan: Array<{ path: string; orig: string | null }> = [];
  const conflict: string[] = [];
  for (const e of journal.entries) {
    const current = (await d.exists(e.path)) ? await d.readFile(e.path) : null;
    if (current === e.orig) continue;
    if (e.generated || (current !== null && e.after_sha.includes(sha256(current)))) plan.push(e);
    else conflict.push(path.relative(cfg.toolkitRoot, e.path));
  }
  if (conflict.length > 0) {
    return {
      ok: false, conflict,
      log: `[coordinate] an interrupted promotion left ${file}, but ${conflict.join(", ")} changed since it ` +
        "was written; nothing was restored. Resolve the files by hand (the journal holds their original " +
        "bytes), then delete the journal and resume.",
    };
  }
  for (const e of plan) {
    if (e.orig === null) await d.removeFile(e.path);
    else await d.writeFile(e.path, e.orig);
  }
  for (const dir of journal.created_dirs) await d.removeDir?.(dir);
  await d.removeFile(file);
  return {
    ok: true,
    log: `[coordinate] recovered an interrupted promotion: restored ${plan.length} toolkit file(s) ` +
      `(${plan.map((e) => path.relative(cfg.toolkitRoot, e.path)).join(", ") || "none changed"}) before re-applying.`,
  };
}

// --- Orchestrator (one coordinate attempt: agent → apply) ----------------------

export interface CoordinateArgs {
  toolkit: ToolkitConfig;
  /** Defaults to this package's `tools/` directory. */
  toolsDir?: string;
  slug: string;
  leanDir: string;
  requirement: string;
  modulePrefix: string;
  runDir: string;
  leanFiles: string[];
  round: number;
  lastFailureLog: string | null;
  provenance?: StudyProvenance;
}
export interface CoordinateDeps {
  runCoordinator: typeof runCoordinator;
  apply: typeof applyManifest;
  applyDeps?: CoordinateApplyDeps;
}

const realCoordinateDeps: CoordinateDeps = { runCoordinator, apply: applyManifest };

function coordinateStagingDir(runDir: string, round: number): string {
  return path.join(runDir, "coordinate_staging", `round_${round}`);
}

/**
 * One coordinate attempt: ask the coordinator for a manifest, then apply it
 * deterministically. Returns `{ ok, log }`; the pipeline owns the bounded retry
 * (feeding a failure log back on `ok === false`).
 */
export async function coordinate(
  args: CoordinateArgs,
  deps: CoordinateDeps = realCoordinateDeps,
): Promise<{ ok: boolean; log: string; timedOut?: boolean; conflict?: boolean }> {
  const toolsDir = args.toolsDir ?? paperFormalizerToolsDir();
  const stagingDir = coordinateStagingDir(args.runDir, args.round);
  // A crash mid-apply / mid-gate left its journal: restore the toolkit first, so re-applying a
  // fresh manifest can never merge the same content twice.
  const recovered = await recoverInterruptedApply(args.toolkit, args.slug, deps.applyDeps ?? realApplyDeps);
  if (recovered && !recovered.ok) return { ok: false, conflict: true, log: recovered.log };
  let manifest: CoordinationManifest;
  try {
    manifest = await deps.runCoordinator({
      toolkit: args.toolkit, toolsDir, runDir: args.runDir, round: args.round, slug: args.slug,
      requirement: args.requirement, leanDir: args.leanDir, modulePrefix: args.modulePrefix,
      leanFiles: args.leanFiles, stagingDir, lastFailureLog: args.lastFailureLog,
    });
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    // A parse/agent failure is retryable: the pipeline feeds this back so the coordinator re-emits.
    return { ok: false, log: `${recovered ? `${recovered.log}\n\n` : ""}[coordinate] coordinator agent/parse failed: ${msg}` };
  }
  const res = await deps.apply(
    {
      toolkit: args.toolkit, toolsDir, stagingDir, leanFiles: args.leanFiles, manifest,
      slug: args.slug, modulePrefix: args.modulePrefix,
      ...(args.provenance ? { provenance: args.provenance } : {}),
    },
    deps.applyDeps ?? realApplyDeps,
  );
  return recovered ? { ...res, log: `${recovered.log}\n\n${res.log}` } : res;
}

/** Dry-run stand-in for `coordinate`: describe what a real attempt would do, touching nothing. */
export async function describeCoordinatePlan(args: CoordinateArgs): Promise<string> {
  const toolsDir = args.toolsDir ?? paperFormalizerToolsDir();
  const cfg = args.toolkit;
  const indexStep = await detectToolkitIndexStep(cfg, realApplyDeps);
  const axiomsStep = axiomsGateStep(cfg, axiomsProbePath(cfg, args.slug), []);
  const chain = toolkitGateChain(cfg, toolsDir, indexStep, axiomsStep);
  return [
    `[dry-run] would coordinate ${args.leanFiles.length} staged file(s) from ${args.leanDir} into ${cfg.toolkitRoot}`,
    `[dry-run] coordinator stages bodies under ${coordinateStagingDir(args.runDir, args.round)}`,
    `[dry-run] targets: ${cfg.lib}/<${cfg.divisions.join("|")}>/<Topic>/<File>.lean; new modules wired into the division barrel; ledger ${cfg.ledgerPath}`,
    ...(args.provenance
      ? [`[dry-run] ledger origin: proposal ${args.provenance.origin.slug} round ${args.provenance.origin.round} ${args.provenance.origin.proposal_id} (${args.provenance.decision})`]
      : []),
    `[dry-run] gate chain (${cfg.toolkitRoot}, lock ${cfg.lockPath}):`,
    ...chain.map((s, i) => `  ${i + 1}. [${s.label}] (${s.cwd}) ${s.cmd}`),
    ...(indexStep ? [] : [`  ${INDEX_STEP_SKIPPED}`]),
  ].join("\n");
}
