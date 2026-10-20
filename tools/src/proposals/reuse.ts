// Reuse measurement at F5 completion (live runs only): which toolkit declarations the paper's
// finished Lean actually uses, and how many of the paper's proof obligations touch the toolkit.
//
// The facts come from the same `candidate_scan` exe round B uses (its constants classified base /
// toolkit / paper): a toolkit constant in any paper declaration's type or body is a use; an
// obligation (a paper statement the F5 crosswalk anchors) touches the toolkit when its declaration,
// or a paper declaration in its dependency closure, uses one. Written to
// `runs/<slug>/formalization/reuse.json`; the ledger's `declarations[].used_by` gains the slug for
// every used toolkit declaration it records (idempotent). V6 prints the one-line summary.
import { existsSync } from "node:fs";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { crosswalkFullJsonPath, leanTheoremDir, PAPER_TMP_DIR, paperBarrelPath } from "../paths.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { leanImports } from "../toolkit/lean_source.js";
import { loadLedger, saveLedger } from "../toolkit/ledger.js";
import type { LeanExec } from "../verify/lean_evidence.js";
import { obtainScan, type CandidateScan, type ScanDecl } from "./candidate_scan.js";

export interface ReuseReport {
  slug: string;
  measured_at: string;
  /** Toolkit declarations some paper declaration mentions (type or body), sorted. */
  toolkit_decls_used: string[];
  /** `<lib>.*` modules the paper's files import. */
  toolkit_imports: string[];
  /** Distinct base-library constants the paper mentions. */
  base_decls_used_count: number;
  /** Paper statements (theorem / lemma / proposition) the crosswalk anchors to a declaration. */
  paper_obligations: number;
  /** Of those, how many use a toolkit declaration directly or through their paper closure. */
  obligations_touching_toolkit: number;
  obligations: Array<{ obj_id: string; decl: string; toolkit: string[] }>;
  /** Set when the measurement could not run (the report then says so). */
  error?: string;
}

interface CrosswalkLike { obj_id: string; kind?: string; lean?: { decl?: string } | null }
const OBLIGATION_KINDS = new Set(["theorem", "lemma", "proposition"]);

export function reuseJsonPath(cfg: ToolkitConfig, qid: string): string {
  return path.join(cfg.runsDir, qid, "formalization", "reuse.json");
}

/** Pure: the reuse facts of a scan against the crosswalk. */
export function computeReuse(scan: CandidateScan, crosswalk: readonly CrosswalkLike[], toolkitImports: readonly string[]): Omit<ReuseReport, "slug" | "measured_at"> {
  const byName = new Map(scan.declarations.map((d) => [d.name, d] as const));
  const refs = (d: ScanDecl) => [...d.type_constants, ...d.body_constants];
  const used = new Set<string>();
  const base = new Set<string>();
  for (const d of scan.declarations) {
    for (const c of refs(d)) {
      if (c.class === "toolkit") used.add(c.name);
      else if (c.class === "base") base.add(c.name);
    }
  }
  const touching = (root: ScanDecl): string[] => {
    const seen = new Set<string>([root.name]);
    const out = new Set<string>();
    const stack = [root];
    while (stack.length) {
      const d = stack.pop()!;
      for (const c of refs(d)) {
        if (c.class === "toolkit") out.add(c.name);
        else if (c.class === "paper" && !seen.has(c.name) && byName.has(c.name)) {
          seen.add(c.name);
          stack.push(byName.get(c.name)!);
        }
      }
    }
    return [...out].sort();
  };
  const find = (decl: string) => byName.get(decl) ?? scan.declarations.find((d) => d.name.endsWith(`.${decl}`));
  const obligations = crosswalk
    .filter((e) => e.lean?.decl && OBLIGATION_KINDS.has(e.kind ?? ""))
    .map((e) => {
      const d = find(e.lean!.decl!);
      return { obj_id: e.obj_id, decl: e.lean!.decl!, toolkit: d ? touching(d) : [] };
    });
  return {
    toolkit_decls_used: [...used].sort(),
    toolkit_imports: [...new Set(toolkitImports)].sort(),
    base_decls_used_count: base.size,
    paper_obligations: obligations.length,
    obligations_touching_toolkit: obligations.filter((o) => o.toolkit.length > 0).length,
    obligations,
  };
}

/** `<lib>.*` imports of the paper's Lean files (run barrel included, `tmp/` excluded). */
export async function paperToolkitImports(cfg: ToolkitConfig, leanSubdir: string): Promise<string[]> {
  const dir = leanTheoremDir(cfg.toolkitRoot, leanSubdir);
  const files: string[] = [paperBarrelPath(cfg.toolkitRoot, leanSubdir)];
  const walk = async (d: string): Promise<void> => {
    for (const e of await readdir(d, { withFileTypes: true }).catch(() => [])) {
      const abs = path.join(d, e.name);
      if (e.isDirectory()) { if (!(d === dir && e.name === PAPER_TMP_DIR)) await walk(abs); }
      else if (e.name.endsWith(".lean")) files.push(abs);
    }
  };
  await walk(dir);
  const out = new Set<string>();
  for (const f of files) {
    if (!existsSync(f)) continue;
    for (const imp of leanImports(await readFile(f, "utf8"))) if (imp.module === cfg.lib || imp.module.startsWith(`${cfg.lib}.`)) out.add(imp.module);
  }
  return [...out];
}

/**
 * Measure a live run's toolkit reuse (scan → `reuse.json`, ledger `used_by`). Never throws: a
 * failed measurement is written as `{error}` and logged, so the report says it was not measured.
 */
export async function measureReuse(args: {
  toolkit: ToolkitConfig;
  qid: string;
  leanSubdir: string;
  log: (m: string) => void;
  now?: () => Date;
  exec?: LeanExec;
  /** Injectable scan (tests). */
  scan?: () => Promise<CandidateScan>;
}): Promise<ReuseReport> {
  const { toolkit: cfg, qid, log } = args;
  const measuredAt = (args.now ?? (() => new Date()))().toISOString();
  const out = reuseJsonPath(cfg, qid);
  try {
    const scan = args.scan ? await args.scan() : await obtainScan({ toolkit: cfg, qid, leanSubdir: args.leanSubdir, log, ...(args.exec ? { exec: args.exec } : {}) });
    const cw = crosswalkFullJsonPath(cfg.toolkitRoot, qid);
    const crosswalk = existsSync(cw) ? (JSON.parse(await readFile(cw, "utf8")) as CrosswalkLike[]) : [];
    const report: ReuseReport = { slug: qid, measured_at: measuredAt, ...computeReuse(scan, crosswalk, await paperToolkitImports(cfg, args.leanSubdir)) };
    await writeJsonAtomic(out, report);
    const ledger = await loadLedger(cfg.ledgerPath);
    const used = new Set(report.toolkit_decls_used);
    let changed = 0;
    for (const d of ledger.declarations) {
      if (used.has(d.name) && !d.used_by.includes(qid)) {
        d.used_by = [...d.used_by, qid];
        changed += 1;
      }
    }
    if (changed > 0) await saveLedger(cfg.ledgerPath, ledger);
    log(`toolkit reuse: ${reuseSummaryLine(report)} → ${out}${changed ? `; ledger used_by updated for ${changed} declaration(s)` : ""}`);
    return report;
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    const report: ReuseReport = {
      slug: qid, measured_at: measuredAt, toolkit_decls_used: [], toolkit_imports: [], base_decls_used_count: 0,
      paper_obligations: 0, obligations_touching_toolkit: 0, obligations: [], error: msg,
    };
    await writeJsonAtomic(out, report);
    log(`WARNING toolkit reuse not measured: ${msg}`);
    return report;
  }
}

/** The one-line summary V6 prints. */
export function reuseSummaryLine(r: ReuseReport): string {
  if (r.error) return `not measured (${r.error.split("\n")[0]})`;
  return `${r.toolkit_decls_used.length} toolkit declaration(s) used; ${r.obligations_touching_toolkit} of ${r.paper_obligations} ` +
    `paper obligation(s) touch the toolkit; ${r.base_decls_used_count} base constant(s) mentioned`;
}
