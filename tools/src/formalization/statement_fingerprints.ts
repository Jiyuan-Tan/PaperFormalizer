// What Lean ELABORATED, as the F4 review cache reads it: `candidate_scan --fingerprints` reports,
// for every declaration of the toolkit package a run's modules can see, a `closure_hash` — the hash
// of what the declaration states together with every package declaration its statement reaches
// (a theorem by its type, a definition by its type and value, a structure by its constructor and
// field names; library constants by name). It moves exactly when one of those statements does:
// not with a proof, a comment, a docstring, an `open`, a `variable`, a `set_option`, an import, or
// a declaration the statement does not reach. See `closureFingerprint` in the toolkit's
// `CandidateScan.lean`.
import { existsSync } from "node:fs";
import { mkdir, readFile, readdir } from "node:fs/promises";
import path from "node:path";
import { isPaperTmpPath } from "../paths.js";
import { withLakeBuildLock } from "../shared/build_mutex.js";
import { toolkitConfigFileIn, toolkitConfigFromJson, type ToolkitConfig } from "../toolkit/config.js";
import { readLakefileTargets } from "../toolkit/lakefile.js";

export interface DeclFingerprint {
  /** User-facing declared name, namespaces included. */
  name: string;
  /** Source file, relative to the toolkit root. */
  file: string;
  hash: string;
}

export interface StatementFingerprints {
  /** Last name segment → every scanned declaration carrying it. */
  byShort: Map<string, DeclFingerprint[]>;
  byFile: Map<string, DeclFingerprint[]>;
  /** The run's Lean dir relative to the toolkit root, `/`-separated: graph anchors and symbol
   *  members name their files relative to it. */
  leanSubdir: string;
  /** The run's modules (dotted names) the scan's build covered — green when the scan exists. */
  modules: string[];
}

const lastSegment = (name: string): string => name.split(".").filter(Boolean).pop() ?? "";

/** The closure fingerprints of a scan's JSON; null when it reports none (unreadable, or a toolkit
 *  whose `CandidateScan.lean` predates `closure_hash`). Pure. */
export function parseStatementFingerprints(text: string, leanSubdir: string): StatementFingerprints | null {
  let decls: Array<{ name?: unknown; file?: unknown; closure_hash?: unknown }>;
  try {
    decls = (JSON.parse(text) as { declarations?: typeof decls }).declarations ?? [];
  } catch {
    return null;
  }
  const byShort = new Map<string, DeclFingerprint[]>();
  const byFile = new Map<string, DeclFingerprint[]>();
  const push = (m: Map<string, DeclFingerprint[]>, k: string, d: DeclFingerprint) => { if (!m.has(k)) m.set(k, []); m.get(k)!.push(d); };
  for (const d of decls) {
    if (typeof d.name !== "string" || typeof d.file !== "string" || typeof d.closure_hash !== "string") continue;
    const fp = { name: d.name, file: d.file, hash: d.closure_hash };
    push(byShort, lastSegment(fp.name), fp);
    push(byFile, fp.file, fp);
  }
  return byShort.size > 0 ? { byShort, byFile, leanSubdir: leanSubdir.split(/[\\/]+/).filter(Boolean).join("/"), modules: [] } : null;
}

/** `file` of the run's Lean dir as the scan names it. */
const scanFile = (fp: StatementFingerprints, file: string): string => `${fp.leanSubdir}/${file.replace(/\\/g, "/")}`;

/** The scanned declarations an anchor names: the declared name, or either a namespace-qualified
 *  form of the other; in `file` (relative to the run's Lean dir) when the anchor has one. */
export function resolveFingerprints(fp: StatementFingerprints, declName: string, file: string | null): DeclFingerprint[] {
  const inFile = file ? scanFile(fp, file) : null;
  return (fp.byShort.get(lastSegment(declName)) ?? []).filter((c) =>
    (c.name === declName || declName.endsWith(`.${c.name}`) || c.name.endsWith(`.${declName}`)) && (!inFile || c.file === inFile));
}

/** Every scanned declaration of `file` (relative to the run's Lean dir). */
export function fingerprintsInFile(fp: StatementFingerprints, file: string): DeclFingerprint[] {
  return fp.byFile.get(scanFile(fp, file)) ?? [];
}

/** The rows a target's evidence hashes, order-canonical and deduplicated. */
export function fingerprintRows(decls: readonly DeclFingerprint[]): [string, string, string][] {
  const rows = decls.map((d) => JSON.stringify([d.file, d.name, d.hash]));
  return [...new Set(rows)].sort().map((r) => JSON.parse(r) as [string, string, string]);
}

/** `killed`: the process was stopped for inactivity or at the wall-clock cap, not by its own exit. */
export type FingerprintExec = (args: string[], cwd: string) => Promise<{ code: number | null; output: string; killed?: boolean }>;

async function lakeExec(args: string[], cwd: string): Promise<{ code: number | null; output: string; killed?: boolean }> {
  const { spawnWithInactivityTimeout } = await import("../workers/spawn.js");
  const r = await spawnWithInactivityTimeout("lake", args, { cwd, env: process.env, inactivityTimeoutMs: 30 * 60_000, maxTotalMs: 60 * 60_000 });
  return { code: r.exitCode, output: `${r.stdout}\n${r.stderr}`, killed: r.killedDueToInactivity || r.killedDueToTotalTimeout };
}

/**
 * The closure fingerprints of the run in `leanDir`, taken from a fresh build of its modules under
 * the toolkit's lake lock (a no-op on the green tree F4 and F5 hold). Null — with the reason
 * logged — whenever they cannot be had: no `candidate_scan` exe, a red build, a failed scan, a
 * scan with no `closure_hash`. A caller reads null as "no target is current", never as a pass.
 * A build stopped by its timeout (a stalled lake, not a red tree) is retried once before that:
 * without the retry one stall turned every target of the F5 audit into a finding.
 */
export async function takeStatementFingerprints(toolkitRoot: string, leanDir: string, exec: FingerprintExec = lakeExec): Promise<StatementFingerprints | null> {
  const none = (why: string): null => {
    console.warn(`[f4] statement fingerprints unavailable — every target is reviewed: ${why}`);
    return null;
  };
  const leanSubdir = path.relative(toolkitRoot, leanDir).split(path.sep).join("/");
  if (!leanSubdir || leanSubdir.startsWith("..") || !existsSync(leanDir)) return none(`${leanDir} is not a Lean dir of ${toolkitRoot}`);
  if (!readLakefileTargets(toolkitRoot).exes.has("candidate_scan")) return none(`the toolkit lakefile declares no \`candidate_scan\` exe (copy it and CandidateScan.lean from the toolkit template)`);
  let cfg: ToolkitConfig;
  try {
    // the library names only: nothing here reads the base libraries the full loader validates
    cfg = toolkitConfigFromJson(toolkitRoot, JSON.parse(await readFile(toolkitConfigFileIn(toolkitRoot) ?? "", "utf8")));
  } catch (err) {
    return none(err instanceof Error ? err.message : String(err));
  }
  const modules = (await readdir(leanDir, { recursive: true })).map(String)
    .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f))
    .map((f) => `${leanSubdir}/${f.replace(/\\/g, "/")}`.replace(/\.lean$/, "").split("/").join("."))
    .sort();
  if (modules.length === 0) return none(`no Lean modules under ${leanDir}`);
  const out = path.join(toolkitRoot, ".lake", "build", "leansmith", `fingerprints_${leanSubdir.replace(/[^A-Za-z0-9_.-]+/g, "_")}.json`);
  const tail = (s: string) => s.split("\n").filter((l) => l.trim()).slice(-8).join("\n");
  try {
    await mkdir(path.dirname(out), { recursive: true });
    const failure = await withLakeBuildLock(toolkitRoot, async () => {
      let build = await exec(["build", ...modules, "candidate_scan"], toolkitRoot);
      if (build.killed) {
        console.warn("[f4] `lake build` for the statement fingerprints was stopped by its timeout — retrying once");
        build = await exec(["build", ...modules, "candidate_scan"], toolkitRoot);
      }
      if (build.code !== 0) return `\`lake build\` of the run's modules and candidate_scan ${build.killed ? "timed out" : "failed"}:\n${tail(build.output)}`;
      const scan = await exec([
        "exe", "candidate_scan", "--", "--graph", "--fingerprints", "--toolkit-prefix", cfg.lib,
        "--papers-prefix", cfg.papersLib, "--modules", modules.join(","), "--out", out,
      ], toolkitRoot);
      return scan.code === 0 ? null : `candidate_scan failed:\n${tail(scan.output)}`;
    });
    if (failure) return none(failure);
    const fp = parseStatementFingerprints(await readFile(out, "utf8"), leanSubdir);
    return fp ? { ...fp, modules } : none(`${out} reports no closure_hash (update the toolkit's CandidateScan.lean from the template)`);
  } catch (err) {
    return none(err instanceof Error ? err.message : String(err));
  }
}
