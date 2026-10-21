// Round-B candidates: which proved declarations of a paper module could move into the toolkit.
// Mechanical, no model.
//
// The facts come from the toolkit's `candidate_scan` exe (`templates/toolkit/CandidateScan.lean`):
// per declaration of the paper, its axioms, whether it uses `sorry`, and every constant its type
// and body mention, classified base / toolkit / paper / other-paper. The rules applied here:
//
//   - intrinsic: axioms ⊆ {propext, Classical.choice, Quot.sound} (so no `sorry`); not `private`
//     (not reachable from another module); no constant from another paper or from toolkit staging;
//     not one of the paper's main results (a declaration the crosswalk or the V6 report maps a
//     paper THEOREM or corollary to). The paper's own lemmas and propositions are candidates like
//     the helpers the F stages added, flagged `paper_result` so the owner sees which they are;
//   - closure (fixpoint): every paper constant a candidate mentions is itself a candidate, so the
//     declaration and everything it needs move together; a candidate's TYPE may mention a paper
//     constant only when that constant is a definition moving with it (the statement is over base,
//     toolkit, and definitions that travel with it);
//   - definitions travel, never alone: a definition-like declaration (def, instance, structure,
//     class, inductive, opaque) stays a candidate only when a candidate theorem needs it.
//
// Proposals are made for candidate THEOREMS; each carries its closure (`moves_with`), the paper
// declarations that move with it.
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { mkdir, readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { z } from "zod";
import type { Core } from "../core/schema.js";
import { crosswalkFullJsonPath, leanModulePrefix, leanTheoremDir, PAPER_TMP_DIR, paperBarrelPath } from "../paths.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { CLEAN_AXIOMS, type LeanExec } from "../verify/lean_evidence.js";
import { VERIFY_FILES } from "../verify/types.js";

export const SCAN_CLASSES = ["base", "toolkit", "toolkit_staging", "paper", "other_paper", "unknown"] as const;

const constRefSchema = z.object({ name: z.string(), class: z.enum(SCAN_CLASSES), module: z.string() });
export type ScanConstRef = z.infer<typeof constRefSchema>;

export const scanDeclSchema = z.object({
  name: z.string().min(1),
  kind: z.string().min(1),
  module: z.string(),
  file: z.string(),
  line: z.number().int(),
  name_line: z.number().int().optional(),
  end_line: z.number().int(),
  is_private: z.boolean(),
  type: z.string(),
  /** A structural hash of what the declaration states (`CandidateScan.lean` `stmtFingerprint`). */
  stmt_hash: z.string().optional(),
  doc: z.string().nullable(),
  axioms: z.array(z.string()),
  has_sorry: z.boolean(),
  type_constants: z.array(constRefSchema),
  body_constants: z.array(constRefSchema),
});
export type ScanDecl = z.infer<typeof scanDeclSchema>;

export const candidateScanSchema = z.object({
  schema: z.literal(1),
  paper: z.string().min(1),
  toolkit_prefix: z.string(),
  papers_prefix: z.string(),
  toolchain: z.string().optional(),
  /** A `--graph` scan: every toolkit and paper declaration (`toolkit_graph.ts`). */
  graph: z.boolean().optional(),
  modules: z.array(z.string()),
  declarations: z.array(scanDeclSchema),
  /** Set by the dry-run stand-in (`syntheticScan`); never by the exe. */
  synthetic: z.boolean().optional(),
  /** sha256 over the paper's Lean sources when the scan ran (`paperSourceHash`), added by the TS
   *  runner so a later step reuses the scan only while the sources are unchanged. */
  source_sha256: z.string().optional(),
});
export type CandidateScan = z.infer<typeof candidateScanSchema>;

/** Declaration kinds that travel with the theorems that need them (never proposed alone). */
export const DEFINITION_KINDS: ReadonlySet<string> = new Set(["def", "instance", "structure", "class", "inductive", "opaque", "abbrev"]);

export interface CandidateEntry {
  name: string;
  kind: string;
  module: string;
  file: string;
  line: number;
  end_line: number;
  type: string;
  doc: string | null;
  /** Paper declarations that move with it (its closure, itself excluded), dependencies first. */
  moves_with: string[];
  /** Candidate theorems whose closure contains it. */
  used_by: string[];
  /** Closure members the crosswalk maps to one of the paper's own definitions / assumptions /
   *  lemmas (`decl → paper object`): they move too, which the owner should see. */
  paper_objects: Record<string, string>;
  /** Set when the candidate is one of the paper's own stated lemmas / propositions. */
  paper_result?: { obj_id: string; kind: string };
}

export interface CandidatesFile {
  schema: 1;
  slug: string;
  paper: string;
  scan_path: string;
  synthetic: boolean;
  /** Candidate theorems — the proposal candidates of round B. */
  candidates: CandidateEntry[];
  /** Every declaration that may move (candidate theorems and the definitions travelling with them). */
  movable: string[];
  rejected: Array<{ name: string; kind: string; reasons: string[] }>;
}

/** A paper statement a declaration is anchored to (crosswalk / V6 report). */
export interface PaperStatementRef { obj_id: string; kind: string }

export interface FilterOptions {
  /** Declarations the crosswalk / V6 report map a paper THEOREM or corollary to (excluded). */
  results: ReadonlyMap<string, string>;
  /** Declarations they map a paper lemma / proposition to: candidates, flagged `paper_result`. */
  lemmas?: ReadonlyMap<string, PaperStatementRef>;
  /** Declarations the crosswalk maps a paper definition / assumption to: never proposed on their
   *  own (as any definition), they travel with a candidate that needs them. */
  definitions?: ReadonlyMap<string, string>;
}

const STATEMENT_OBJ_RE = /^(thm|lem|prop|cor|conj):/;

function describePaperObject(obj: string): string {
  if (/^ass:pin/.test(obj)) return `reading pin ${obj}`;
  if (obj.startsWith("ass:")) return `assumption ${obj}`;
  if (obj.startsWith("def:")) return `definition ${obj}`;
  if (/^S\d/.test(obj)) return `setting ${obj}`;
  return obj;
}

/**
 * What ties a candidate's Lean to the paper, in words (empty = it can move as is): a definition in
 * its closure (the paper's own types and constructions would travel into the toolkit with it), or
 * a closure member realizing one of the paper's definitions, assumptions, reading pins or settings.
 * A paper lemma it uses is no tie (it is a result and moves as one). Such a candidate enters the
 * toolkit only in general form (`generalize`), never as is.
 */
export function paperShapedReasons(c: Pick<CandidateEntry, "moves_with" | "paper_objects">, scan: Pick<CandidateScan, "declarations">): string[] {
  const kindOf = new Map(scan.declarations.map((d) => [d.name, d.kind] as const));
  const leaf = (n: string) => n.slice(n.lastIndexOf(".") + 1);
  const out: string[] = [];
  for (const n of c.moves_with) {
    const obj = c.paper_objects[n];
    if (obj && STATEMENT_OBJ_RE.test(obj)) continue;
    if (obj) out.push(`\`${leaf(n)}\` is the paper's ${describePaperObject(obj)}`);
    else if (DEFINITION_KINDS.has(kindOf.get(n) ?? "")) out.push(`\`${leaf(n)}\` is a definition made for this paper`);
  }
  return out;
}

/** Whether scan name `name` is the crosswalk's `decl` (exact, or `decl` is a namespace-relative
 *  suffix of it). */
function nameMatches(name: string, decl: string): boolean {
  return name === decl || name.endsWith(`.${decl}`);
}

/** Apply the round-B rules to a scan. Pure. */
export function filterCandidates(scan: CandidateScan, opts: FilterOptions): Omit<CandidatesFile, "slug" | "scan_path" | "synthetic"> {
  const byName = new Map(scan.declarations.map((d) => [d.name, d] as const));
  const reasons = new Map<string, string[]>(scan.declarations.map((d) => [d.name, []]));
  const reject = (n: string, why: string) => reasons.get(n)!.push(why);
  const paperRefs = (d: ScanDecl, which: "type" | "body" | "all") =>
    [...(which !== "body" ? d.type_constants : []), ...(which !== "type" ? d.body_constants : [])]
      .filter((c) => c.class === "paper" && c.name !== d.name).map((c) => c.name);

  // Intrinsic rules.
  for (const d of scan.declarations) {
    if (d.has_sorry) reject(d.name, "uses sorry");
    const extra = d.axioms.filter((a) => !CLEAN_AXIOMS.has(a) && a !== "sorryAx");
    if (extra.length) reject(d.name, `depends on axiom(s) ${extra.join(", ")}`);
    if (d.is_private) reject(d.name, "private (not reachable from another module)");
    for (const c of [...d.type_constants, ...d.body_constants]) {
      if (c.class === "other_paper") reject(d.name, `uses ${c.name} from another paper (${c.module})`);
      else if (c.class === "toolkit_staging") reject(d.name, `uses toolkit staging ${c.name}`);
      else if (c.class === "unknown") reject(d.name, `uses ${c.name}, whose module is unknown`);
    }
    for (const [decl, obj] of opts.results) {
      if (nameMatches(d.name, decl)) reject(d.name, `a result of the paper (the crosswalk maps ${obj} to it)`);
    }
  }
  const inSet = new Set(scan.declarations.filter((d) => reasons.get(d.name)!.length === 0).map((d) => d.name));

  // Closure fixpoint.
  for (let changed = true; changed;) {
    changed = false;
    for (const n of [...inSet]) {
      const d = byName.get(n)!;
      const missing = paperRefs(d, "all").filter((r) => !inSet.has(r));
      const typeNonDef = paperRefs(d, "type").filter((r) => inSet.has(r) && !DEFINITION_KINDS.has(byName.get(r)?.kind ?? ""));
      if (missing.length || typeNonDef.length) {
        inSet.delete(n);
        changed = true;
        for (const r of missing) reject(n, `needs ${r}, which cannot move${byName.has(r) ? "" : " (not a scanned declaration)"}`);
        for (const r of typeNonDef) reject(n, `its statement mentions the theorem ${r}`);
      }
    }
  }

  // Closures of candidate theorems; definitions not needed by any stay behind.
  const closureOf = (root: string): string[] => {
    const seen = new Set<string>([root]);
    const order: string[] = [];
    const visit = (n: string) => {
      for (const r of paperRefs(byName.get(n)!, "all")) {
        if (seen.has(r) || !inSet.has(r)) continue;
        seen.add(r);
        visit(r);
        order.push(r);
      }
    };
    visit(root);
    return order;
  };
  const roots = [...inSet].filter((n) => !DEFINITION_KINDS.has(byName.get(n)!.kind)).sort();
  const closures = new Map(roots.map((r) => [r, closureOf(r)] as const));
  const needed = new Set<string>([...roots, ...[...closures.values()].flat()]);
  for (const n of [...inSet]) {
    if (!needed.has(n)) {
      inSet.delete(n);
      reject(n, "a definition no candidate theorem needs (definitions move only with the theorems that use them)");
    }
  }
  const usedBy = (n: string) => roots.filter((r) => r !== n && closures.get(r)!.includes(n));
  const paperResult = (n: string): PaperStatementRef | undefined => {
    for (const [decl, ref] of opts.lemmas ?? []) if (nameMatches(n, decl)) return ref;
    return undefined;
  };
  const paperObject = (n: string): string | undefined => {
    for (const [decl, obj] of opts.definitions ?? []) if (nameMatches(n, decl)) return obj;
    return paperResult(n)?.obj_id;
  };
  const candidates: CandidateEntry[] = roots.map((r) => {
    const d = byName.get(r)!;
    const objs = Object.fromEntries(closures.get(r)!.flatMap((n) => (paperObject(n) ? [[n, paperObject(n)!]] : [])));
    const own = paperResult(r);
    return {
      name: d.name, kind: d.kind, module: d.module, file: d.file, line: d.line, end_line: d.end_line,
      type: d.type, doc: d.doc, moves_with: closures.get(r)!, used_by: usedBy(r), paper_objects: objs,
      ...(own ? { paper_result: own } : {}),
    };
  });
  return {
    schema: 1,
    paper: scan.paper,
    candidates,
    movable: [...inSet].sort(),
    rejected: scan.declarations.filter((d) => !inSet.has(d.name)).map((d) => ({ name: d.name, kind: d.kind, reasons: reasons.get(d.name)! })),
  };
}

// ─── paper results (excluded) ──────────────────────────────────────────────

interface CrosswalkLike { obj_id: string; kind?: string; lean?: { decl?: string } | null; moved_to_toolkit?: boolean }
interface ReportLike { results?: Array<{ node_id?: string; kind?: string; lean?: { decl?: string } | null; moved_to_toolkit?: boolean }> }

const STATEMENT_KINDS = new Set(["theorem", "lemma", "proposition", "corollary"]);
/** Statement kinds round B may move (the paper's theorems and corollaries stay in the paper). */
const MOVABLE_RESULT_KINDS = new Set(["lemma", "proposition"]);

/**
 * The paper's own objects, from the F5 crosswalk and the V6 report. `results`: declarations a
 * paper THEOREM or corollary is anchored to — excluded from round B (the paper's deliverable).
 * `lemmas`: declarations a paper lemma or proposition is anchored to — round-B candidates like the
 * helpers, flagged. `definitions`: declarations a paper definition or assumption is anchored to —
 * like any definition they are never proposed alone and move only with a candidate that needs
 * them (listed under `paper_objects`). Rows already moved to the toolkit are skipped.
 */
export async function paperObjects(cfg: ToolkitConfig, qid: string): Promise<{ results: Map<string, string>; lemmas: Map<string, PaperStatementRef>; definitions: Map<string, string> }> {
  const statements = new Map<string, PaperStatementRef[]>();
  const definitions = new Map<string, string>();
  const add = (decl: string, obj: string, kind: string) => {
    if (STATEMENT_KINDS.has(kind)) statements.set(decl, [...(statements.get(decl) ?? []), { obj_id: obj, kind }]);
    else definitions.set(decl, obj);
  };
  const cw = crosswalkFullJsonPath(cfg.toolkitRoot, qid);
  if (existsSync(cw)) {
    for (const e of JSON.parse(await readFile(cw, "utf8")) as CrosswalkLike[]) {
      if (e.lean?.decl && !e.moved_to_toolkit) add(e.lean.decl, e.obj_id, e.kind ?? "theorem");
    }
  }
  const rp = path.join(cfg.runsDir, qid, VERIFY_FILES.reportJson);
  if (existsSync(rp)) {
    for (const r of ((JSON.parse(await readFile(rp, "utf8")) as ReportLike).results ?? [])) {
      if (r.lean?.decl && !r.moved_to_toolkit) add(r.lean.decl, r.node_id ?? "a result", r.kind ?? "theorem");
    }
  }
  const results = new Map<string, string>();
  const lemmas = new Map<string, PaperStatementRef>();
  for (const [decl, refs] of statements) {
    // Movable only when every anchor calls it a lemma / proposition.
    if (refs.every((r) => MOVABLE_RESULT_KINDS.has(r.kind))) lemmas.set(decl, refs[0]!);
    else results.set(decl, refs.find((r) => !MOVABLE_RESULT_KINDS.has(r.kind))!.obj_id);
    definitions.delete(decl);
  }
  return { results, lemmas, definitions };
}

/** Declarations the V6 report anchors a paper result to (the headline set whose `#print axioms`
 *  a round-B move must leave unchanged); rows already moved to the toolkit are not headlines. */
export async function reportHeadlineDecls(cfg: ToolkitConfig, qid: string): Promise<string[]> {
  const rp = path.join(cfg.runsDir, qid, VERIFY_FILES.reportJson);
  if (!existsSync(rp)) return [];
  const rows = ((JSON.parse(await readFile(rp, "utf8")) as ReportLike).results ?? [])
    .filter((r) => STATEMENT_KINDS.has(r.kind ?? "theorem") && !r.moved_to_toolkit);
  return [...new Set(rows.map((r) => r.lean?.decl).filter((d): d is string => !!d))].sort();
}

// ─── running the exe ───────────────────────────────────────────────────────

export function candidateScanPath(cfg: ToolkitConfig, qid: string): string {
  return path.join(cfg.runsDir, qid, "formalization", "candidate_scan.json");
}
export function candidatesPath(cfg: ToolkitConfig, qid: string): string {
  return path.join(cfg.runsDir, qid, "formalization", "candidates.json");
}

/** Dotted module name of the run barrel (`Papers.<Pascal>`). */
export function paperModulePrefix(leanSubdir: string): string {
  return leanModulePrefix(leanSubdir);
}

async function defaultExec(cmd: string, args: string[], opts: { cwd: string }) {
  const { spawnWithInactivityTimeout } = await import("../workers/spawn.js");
  const r = await spawnWithInactivityTimeout(cmd, args, { cwd: opts.cwd, env: process.env, inactivityTimeoutMs: 30 * 60_000, maxTotalMs: 60 * 60_000 });
  return { code: r.exitCode ?? 1, stdout: r.stdout, stderr: r.stderr };
}

/** The toolkit lakefile must declare the `candidate_scan` exe (the template's `CandidateScan.lean`). */
async function assertCandidateScanExe(cfg: ToolkitConfig): Promise<void> {
  const { readLakefileTargets, toolkitTemplateDir } = await import("../toolkit/lakefile.js");
  if (readLakefileTargets(cfg.toolkitRoot).exes.has("candidate_scan")) return;
  throw new Error(
    `the toolkit lakefile declares no \`candidate_scan\` exe, which the promotion round and the toolkit graph run. ` +
      `Copy its \`[[lean_exe]]\` entry from ${path.join(toolkitTemplateDir(), "lakefile.toml")} and ` +
      `${path.join(toolkitTemplateDir(), "CandidateScan.lean")} (with PaperFormalizerIndexCore.lean) into ${cfg.toolkitRoot}, then resume.`,
  );
}

/** Where the `--graph` scan is written: machine-local build output, never committed. */
export function graphScanPath(cfg: ToolkitConfig): string {
  return path.join(cfg.toolkitRoot, ".lake", "build", "paperformalizer", "graph_scan.json");
}

/** Build the toolkit and papers libraries and the exe, then scan every toolkit and paper
 *  declaration (`candidate_scan --graph`), under the toolkit's lake-build lock. */
export async function runGraphScan(args: { toolkit: ToolkitConfig; exec?: LeanExec; log: (m: string) => void }): Promise<CandidateScan> {
  const { toolkit: cfg } = args;
  await assertCandidateScanExe(cfg);
  const exec = args.exec ?? defaultExec;
  const { withLakeBuildLock } = await import("../shared/build_mutex.js");
  const out = graphScanPath(cfg);
  await mkdir(path.dirname(out), { recursive: true });
  const tail = (s: string) => s.split("\n").filter((l) => l.trim()).slice(-30).join("\n");
  const libs = [cfg.lib, ...(existsSync(path.join(cfg.toolkitRoot, `${cfg.papersLib}.lean`)) ? [cfg.papersLib] : [])];
  const build = await withLakeBuildLock(cfg.toolkitRoot, () => exec("lake", ["build", ...libs, "candidate_scan"], { cwd: cfg.toolkitRoot }));
  if (build.code !== 0) throw new Error(`toolkit graph: \`lake build ${libs.join(" ")} candidate_scan\` failed:\n${tail(`${build.stdout}\n${build.stderr}`)}`);
  const scanArgs = ["exe", "candidate_scan", "--", "--graph", "--toolkit-prefix", cfg.lib, "--papers-prefix", cfg.papersLib, "--modules", libs.join(","), "--out", out];
  args.log(`toolkit graph: lake ${scanArgs.join(" ")}`);
  const r = await withLakeBuildLock(cfg.toolkitRoot, () => exec("lake", scanArgs, { cwd: cfg.toolkitRoot }));
  if (r.code !== 0 || !existsSync(out)) throw new Error(`toolkit graph: \`lake ${scanArgs.join(" ")}\` failed:\n${tail(`${r.stdout}\n${r.stderr}`)}`);
  const parsed = candidateScanSchema.safeParse(JSON.parse(await readFile(out, "utf8")));
  if (!parsed.success) throw new Error(`toolkit graph: ${out} does not match the scan schema: ${parsed.error.message}`);
  return parsed.data;
}

/**
 * Build the paper and the exe, then run `lake exe candidate_scan` from the toolkit root, both
 * under the toolkit's lake-build lock. Throws on a failed build or scan (the paper must build for
 * anything to be harvested).
 */
export async function runCandidateScan(args: {
  toolkit: ToolkitConfig;
  qid: string;
  leanSubdir: string;
  exec?: LeanExec;
  log: (m: string) => void;
}): Promise<CandidateScan> {
  const { toolkit: cfg, qid } = args;
  if (!args.exec) await assertCandidateScanExe(cfg);
  const exec = args.exec ?? defaultExec;
  const { withLakeBuildLock } = await import("../shared/build_mutex.js");
  const prefix = paperModulePrefix(args.leanSubdir);
  if (!existsSync(paperBarrelPath(cfg.toolkitRoot, args.leanSubdir))) {
    throw new Error(`candidate scan: the run barrel ${paperBarrelPath(cfg.toolkitRoot, args.leanSubdir)} does not exist; F5 writes it.`);
  }
  const out = candidateScanPath(cfg, qid);
  await mkdir(path.dirname(out), { recursive: true });
  const tail = (s: string) => s.split("\n").filter((l) => l.trim()).slice(-30).join("\n");
  const build = await withLakeBuildLock(cfg.toolkitRoot, () => exec("lake", ["build", prefix, "candidate_scan"], { cwd: cfg.toolkitRoot }));
  if (build.code !== 0) throw new Error(`candidate scan: \`lake build ${prefix} candidate_scan\` failed:\n${tail(`${build.stdout}\n${build.stderr}`)}`);
  const scanArgs = ["exe", "candidate_scan", "--", "--paper", prefix, "--toolkit-prefix", cfg.lib, "--papers-prefix", cfg.papersLib, "--modules", prefix, "--out", out];
  args.log(`candidate scan: lake ${scanArgs.join(" ")}`);
  const r = await withLakeBuildLock(cfg.toolkitRoot, () => exec("lake", scanArgs, { cwd: cfg.toolkitRoot }));
  if (r.code !== 0 || !existsSync(out)) throw new Error(`candidate scan: \`lake ${scanArgs.join(" ")}\` failed:\n${tail(`${r.stdout}\n${r.stderr}`)}`);
  const parsed = candidateScanSchema.safeParse(JSON.parse(await readFile(out, "utf8")));
  if (!parsed.success) throw new Error(`candidate scan: ${out} does not match the scan schema: ${parsed.error.message}`);
  return parsed.data;
}

/** sha256 over the paper's Lean sources (every `.lean` under its directory except the disposable
 *  `tmp/`, plus the run barrel), path-tagged and in sorted order. */
export async function paperSourceHash(repoRoot: string, leanSubdir: string): Promise<string> {
  const dir = leanTheoremDir(repoRoot, leanSubdir);
  const files: string[] = [];
  const walk = async (d: string): Promise<void> => {
    for (const e of await readdir(d, { withFileTypes: true }).catch(() => [])) {
      const abs = path.join(d, e.name);
      if (e.isDirectory()) { if (!(d === dir && e.name === PAPER_TMP_DIR)) await walk(abs); }
      else if (e.isFile() && e.name.endsWith(".lean")) files.push(abs);
    }
  };
  await walk(dir);
  const barrel = paperBarrelPath(repoRoot, leanSubdir);
  if (existsSync(barrel)) files.push(barrel);
  const h = createHash("sha256");
  for (const f of files.sort()) h.update(`${path.relative(repoRoot, f)}\0${await readFile(f, "utf8")}\0`);
  return h.digest("hex");
}

/**
 * The paper's scan: the one on disk when it was taken from the current sources (same
 * `paperSourceHash`), else a fresh `runCandidateScan`, recorded with the hash. Round B and the
 * reuse measurement at F5 completion share it; a move changes the sources, so the next caller
 * re-scans.
 */
export async function obtainScan(args: Parameters<typeof runCandidateScan>[0]): Promise<CandidateScan> {
  const { toolkit: cfg, qid } = args;
  const hash = await paperSourceHash(cfg.toolkitRoot, args.leanSubdir);
  const file = candidateScanPath(cfg, qid);
  if (existsSync(file)) {
    const prior = candidateScanSchema.safeParse(JSON.parse(await readFile(file, "utf8")));
    if (prior.success && prior.data.source_sha256 === hash && !prior.data.synthetic) {
      args.log(`candidate scan: reusing ${file} (paper sources unchanged)`);
      return prior.data;
    }
  }
  const scan = { ...(await runCandidateScan(args)), source_sha256: hash };
  await writeJsonAtomic(file, scan);
  return scan;
}

/** Dry-run stand-in for the exe: every core statement as a clean theorem of the paper module,
 *  named `<Papers.Pascal>.<statement id with non-identifier runs as _>`, mentioning only base. */
export function syntheticScan(core: Core, prefix: string): CandidateScan {
  return {
    schema: 1, paper: prefix, toolkit_prefix: "Toolkit", papers_prefix: prefix.split(".")[0]!, modules: [prefix], synthetic: true,
    declarations: core.statements.map((s, i) => ({
      name: `${prefix}.${s.id.replace(/[^A-Za-z0-9_]+/g, "_")}`,
      kind: "theorem", module: `${prefix}.Main`, file: `${prefix.split(".").join("/")}/Main.lean`,
      line: 10 * (i + 1), end_line: 10 * (i + 1) + 2, is_private: false,
      type: s.statement.replace(/\s+/g, " ").slice(0, 400), doc: null, axioms: [], has_sorry: false,
      type_constants: [], body_constants: [],
    })),
  };
}

/** Write `runs/<slug>/formalization/candidates.json`. */
export async function writeCandidates(cfg: ToolkitConfig, qid: string, scan: CandidateScan, objects: FilterOptions): Promise<CandidatesFile> {
  const file: CandidatesFile = {
    ...filterCandidates(scan, objects),
    slug: qid,
    scan_path: candidateScanPath(cfg, qid),
    synthetic: scan.synthetic === true,
  };
  await mkdir(path.dirname(candidatesPath(cfg, qid)), { recursive: true });
  await writeJsonAtomic(candidatesPath(cfg, qid), file);
  return file;
}
