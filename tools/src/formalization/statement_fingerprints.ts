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
import { greenBuildCurrent, recordGreenBuild, recordScan, scanCurrent, sourceSignature } from "../shared/build_inputs.js";
import { LAKE_NO_BUILD_EXIT, WOULD_BUILD, withLakeBuildLock, withScannerHold } from "../shared/build_mutex.js";
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

/** Where `after` differs from `before` on the run's own declarations (those in `before`'s Lean
 *  dir and its root module; a closure fingerprint moves with every statement it rests on, the toolkit's included,
 *  while a declaration another run adds or promotes meanwhile is not this run's): a fingerprint
 *  moved, a declaration gone, one new (`name (file)` each). Empty when every statement is as it
 *  was. Pure. */
export function statementChanges(before: StatementFingerprints, after: StatementFingerprints): string[] {
  const own = (file: string) => file.startsWith(`${before.leanSubdir}/`) || file === `${before.leanSubdir}.lean`;
  // By file and name: a private declaration's user name can repeat across files, and a name-only
  // map keeps the last row (scan order reads as a change; a change in an earlier row is hidden).
  const key = (d: { file: string; name: string }) => `${d.file}\u0000${d.name}`;
  const flat = (fp: StatementFingerprints) => new Map([...fp.byFile.entries()].filter(([f]) => own(f)).flatMap(([, ds]) => ds).map((d) => [key(d), d] as const));
  const [b, a] = [flat(before), flat(after)];
  const out: string[] = [];
  for (const [k, d] of b) {
    const now = a.get(k);
    if (!now) out.push(`${d.name} (${d.file}) is gone`);
    else if (now.hash !== d.hash) out.push(`${d.name} (${d.file}) states something else`);
  }
  for (const [k, d] of a) if (!b.has(k)) out.push(`${d.name} (${d.file}) is new`);
  return out;
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
 * the toolkit's lake lock (a no-op on the green tree F4 and F5 hold). Every input provably unchanged
 * (`shared/build_inputs.ts`) since the last scan: that scan's output, without the lock; since a
 * green build of these modules (the compile gate's): the scan alone. Null — with the reason
 * logged — whenever they cannot be had: no `candidate_scan` exe, a red build, a failed scan, a
 * scan with no `closure_hash`. A caller reads null as "no target is current", never as a pass.
 * A build stopped by its timeout (a stalled lake, not a red tree) is retried once before that:
 * without the retry one stall turned every target of the F5 audit into a finding.
 */
export async function takeStatementFingerprints(
  toolkitRoot: string,
  leanDir: string,
  exec: FingerprintExec = lakeExec,
  /** The log's tag, and what the caller does without them. */
  log: { tag: string; without: string } = { tag: "f4", without: "every target is reviewed" },
): Promise<StatementFingerprints | null> {
  const none = (why: string): null => {
    console.warn(`[${log.tag}] statement fingerprints unavailable — ${log.without}: ${why}`);
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
  const out = path.join(toolkitRoot, ".lake", "build", "paperformalizer", `fingerprints_${leanSubdir.replace(/[^A-Za-z0-9_.-]+/g, "_")}.json`);
  const tail = (s: string) => s.split("\n").filter((l) => l.trim()).slice(-8).join("\n");
  try {
    await mkdir(path.dirname(out), { recursive: true });
    // A scan is a function of the sources: one taken of them as they stand still holds.
    if (await scanCurrent(out, modules, await sourceSignature(cfg, leanDir))) {
      const fp = parseStatementFingerprints(await readFile(out, "utf8"), leanSubdir);
      if (fp) {
        console.warn(`[${log.tag}] statement fingerprints: every input unchanged since the last scan — reusing it`);
        return { ...fp, modules };
      }
    }
    // The Lake turns, under the lock: nothing builds the toolkit meanwhile, so sources unchanged
    // since a green build of these modules mean the oleans the scan reads are that build's. Under a
    // shared hold of the paper (`withScannerHold`: the toolkit clean, the exe up to date) only its
    // modules are built and the exe runs `--no-build`; else exclusive, the exe built too.
    const turns = async (shared: boolean): Promise<string | null | typeof WOULD_BUILD> => {
      const sig = await sourceSignature(cfg, leanDir);
      await recordScan(out, null);
      const scan = () => exec([...(shared ? ["--no-build"] : []),
        "exe", "candidate_scan", "--", "--graph", "--fingerprints", "--toolkit-prefix", cfg.lib,
        "--papers-prefix", cfg.papersLib, "--modules", modules.join(","), "--out", out,
      ], toolkitRoot);
      const targets = shared ? modules : [...modules, "candidate_scan"];
      if (await greenBuildCurrent(toolkitRoot, leanDir, modules, sig)) {
        const first = await scan();
        if (shared && first.code === LAKE_NO_BUILD_EXIT) return WOULD_BUILD;
        if (first.code === 0) { await recordScan(out, { sig, modules }); return null; }
        console.warn(`[${log.tag}] candidate_scan failed on the tree built green before — building it again:\n${tail(first.output)}`);
      }
      let build = await exec(["build", ...targets], toolkitRoot);
      if (build.killed) {
        console.warn(`[${log.tag}] \`lake build\` for the statement fingerprints was stopped by its timeout — retrying once`);
        build = await exec(["build", ...targets], toolkitRoot);
      }
      if (build.code !== 0) return `\`lake build\` of the run's modules and candidate_scan ${build.killed ? "timed out" : "failed"}:\n${tail(build.output)}`;
      await recordGreenBuild(toolkitRoot, leanDir, modules, sig);
      const r = await scan();
      if (shared && r.code === LAKE_NO_BUILD_EXIT) return WOULD_BUILD;
      if (r.code !== 0) return `candidate_scan failed:\n${tail(r.output)}`;
      await recordScan(out, { sig, modules });
      return null;
    };
    const what = `${log.tag} fingerprints: lake build ${modules.length} module(s) + candidate_scan`;
    const failure = await withScannerHold<string | null>(toolkitRoot, [leanSubdir.split("/").join(".")], what, {
      exeFresh: async () => (await exec(["build", "--no-build", "candidate_scan"], toolkitRoot)).code === 0,
      shared: () => turns(true),
      exclusive: () => withLakeBuildLock(toolkitRoot, async () => (await turns(false)) as string | null, what),
    });
    if (failure) return none(failure);
    const fp = parseStatementFingerprints(await readFile(out, "utf8"), leanSubdir);
    return fp ? { ...fp, modules } : none(`${out} reports no closure_hash (update the toolkit's CandidateScan.lean from the template)`);
  } catch (err) {
    return none(err instanceof Error ? err.message : String(err));
  }
}
