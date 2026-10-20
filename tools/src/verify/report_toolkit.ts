// The report's "Toolkit" section: the one-line reuse summary (`formalization/reuse.json`, measured
// when the promotion round scans the paper) and the list of what the round moved into the toolkit.
// Written by the promotion round and again by `propose --apply`; the section sits between
// markers in `report.md` (replaced in place, appended when absent) and under `toolkit` in
// `report.json`, so re-writing it never touches the rest of the report.
import { existsSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import type { RoundBMove } from "../proposals/schema.js";
import type { ReuseReport } from "../proposals/reuse.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { loadLedger } from "../toolkit/ledger.js";
import { VERIFY_FILES } from "./types.js";

const START = "<!-- toolkit:start -->";
const END = "<!-- toolkit:end -->";

/** `runs/<slug>/formalization/reuse.json`, or null. */
export async function loadRunReuse(runDir: string): Promise<ReuseReport | null> {
  const p = path.join(runDir, "formalization", "reuse.json");
  return existsSync(p) ? (JSON.parse(await readFile(p, "utf8")) as ReuseReport) : null;
}

/** The toolkit's MAIN results the paper used: a used main declaration counts itself, a used helper
 *  counts the main result owning it (the ledger's tiers). */
export async function mainResultsUsed(cfg: Pick<ToolkitConfig, "ledgerPath">, reuse: ReuseReport | null): Promise<string[]> {
  if (!reuse || reuse.error || reuse.toolkit_decls_used.length === 0) return [];
  const ledger = await loadLedger(cfg.ledgerPath);
  const byName = new Map(ledger.declarations.map((d) => [d.name, d as { name: string; tier?: string; owners?: string[] }] as const));
  const out = new Set<string>();
  for (const n of reuse.toolkit_decls_used) {
    const d = byName.get(n);
    if (d?.tier === "aux" && d.owners?.length) d.owners.forEach((o) => out.add(o));
    else out.add(n);
  }
  return [...out].sort();
}

export function toolkitSummaryLine(reuse: ReuseReport | null, main?: readonly string[]): string {
  if (!reuse) return "toolkit reuse: not measured (dry run, or the promotion round has not scanned this paper)";
  if (reuse.error) return `toolkit reuse: not measured (${reuse.error.split("\n")[0]})`;
  return `toolkit reuse: ${main ? `${main.length} toolkit result(s) used (` : ""}${reuse.toolkit_decls_used.length} declaration(s)${main ? ")" : " used"}; ` +
    `${reuse.obligations_touching_toolkit} of ${reuse.paper_obligations} paper obligation(s) touch the toolkit`;
}

export function renderToolkitSection(reuse: ReuseReport | null, moves: readonly RoundBMove[] | undefined, main?: readonly string[]): string {
  const L = [START, "## Toolkit", "", `- ${toolkitSummaryLine(reuse, main)}`];
  if (reuse && !reuse.error && reuse.toolkit_decls_used.length) {
    L.push(`- used: ${reuse.toolkit_decls_used.map((d) => `\`${d}\``).join(", ")}`);
  }
  if (moves && moves.length) {
    L.push("", "Moved into the toolkit by the promotion round:", "");
    for (const m of moves) {
      const what = m.decls.map((d) => (d.from === d.to ? `\`${d.to}\`` : `\`${d.from}\` → \`${d.to}\``)).join(", ");
      L.push(`- ${m.proposal_id} (${m.decision}): ${what} in \`${m.module}\``);
    }
  }
  L.push(END);
  return L.join("\n");
}

/** Replace (or append) the section in `report.md` and set `toolkit` in `report.json`. A run with
 *  no report yet is left alone. */
export async function writeReportToolkitSection(runDir: string, reuse: ReuseReport | null, moves: readonly RoundBMove[] | undefined, main?: readonly string[]): Promise<void> {
  const md = path.join(runDir, VERIFY_FILES.reportMd);
  if (existsSync(md)) {
    const text = await readFile(md, "utf8");
    const section = renderToolkitSection(reuse, moves, main);
    const s = text.indexOf(START);
    const e = text.indexOf(END);
    const next = s >= 0 && e > s ? `${text.slice(0, s)}${section}${text.slice(e + END.length)}` : `${text.replace(/\n*$/, "")}\n\n${section}\n`;
    if (next !== text) await writeFile(md, next, "utf8");
  }
  const js = path.join(runDir, VERIFY_FILES.reportJson);
  if (existsSync(js)) {
    const obj = JSON.parse(await readFile(js, "utf8")) as Record<string, unknown>;
    obj.toolkit = {
      summary: toolkitSummaryLine(reuse, main),
      reuse: reuse ?? null,
      ...(main ? { main_results_used: main } : {}),
      moves: moves ?? [],
    };
    await writeJsonAtomic(js, obj);
  }
}
