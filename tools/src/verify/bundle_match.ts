/**
 * The bundle's `MATCH.md` — each result of the corrected paper beside its Lean declaration.
 *
 * PURE, and no model call: everything is read from what the F stages left — the report's rows (the
 * declaration, its status and axioms), `nl_links.json` (which phrase of the statement each Lean binder
 * and conclusion clause states) and the `-- @node:` tags of the Lean source (which declaration
 * realizes which condition or reading of the paper). A corollary or proposition a repair split off a result follows
 * that result, a result like any other. Results are named as the paper names them; the
 * run's identifiers are in the table at the end.
 */
import type { Core } from "../core/schema.js";
import { declSource, legacyMatch, segmentShown, type NlSegment } from "../formalization/nl_links.js";
import { binderChip, completeView, forallHeaderChip, leanScopes, leanStatementView } from "../formalization/lean_rows.js";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { splitCount } from "./core_graph.js";
import { axiomWords, citedDisclosure, formalStatus, umbrellaWords } from "./report_plain.js";
import type { ReportRow, VerifyReportJson } from "./report.js";

/** One result of `nl_links.json`. */
export interface NlLinksResult {
  obj_id: string;
  node: string;
  decl: string;
  /** The statement the links were written for (`StatementView.key`); absent on links of the flat cut. */
  key?: string;
  segments: NlSegment[];
  rows: Array<{ id: string; kind: string; names: string; lean: string; segments: string[]; unstated: boolean; coarse?: boolean }>;
  uncovered?: string[];
}

/** A result's Lean statement as it stands in the bundle: the key links are written under, and its text. */
export interface CurrentStatement { key: string; statement: string }

/**
 * The statements the links of `links` belong to now, read from the bundle's Lean (`leanRoot`: its
 * `lean/` directory, `leanDir` the paper's directory inside it): node → the statement, null when its
 * declaration is not found or does not structure. What `renderMatch` checks stored links against.
 */
export async function currentStatements(report: VerifyReportJson, leanRoot: string, leanDir: string): Promise<Map<string, CurrentStatement | null>> {
  const lean = leanScopes({ toolkitRoot: leanRoot, leanDir, read: (abs) => readFile(abs, "utf8").catch(() => null) });
  const out = new Map<string, CurrentStatement | null>();
  for (const r of report.results) {
    if (!r.lean) continue;
    const text = await readFile(path.join(leanDir, r.lean.file), "utf8").catch(() => null);
    const src = text ? declSource(text, r.lean.decl, r.lean.line) : null;
    const view = src ? leanStatementView(src) : null;
    if (view) await completeView(view, r.lean.file, r.lean.decl, lean, new Set(), r.lean.line);
    out.set(r.node_id, view ? { key: view.key, statement: view.statement } : null);
  }
  return out;
}

/** A declaration carrying a `-- @node: <id>` tag. */
export interface NodeTag { decl: string; file: string; line: number }

const DECL_RE = /^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|nonrec|partial|unsafe|scoped|local)\s+)*(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\s+([^\s:({[]+)/u;

/** The `-- @node:` tags of one Lean file: node id → the declaration the tag sits on. Pure. */
export function nodeTags(file: string, text: string): Map<string, NodeTag> {
  const out = new Map<string, NodeTag>();
  const lines = text.split("\n");
  lines.forEach((l, i) => {
    const m = /^--\s*@node:\s*([A-Za-z0-9_:.-]+)\s*$/u.exec(l);
    if (!m || out.has(m[1]!)) return;
    for (let j = i + 1; j < Math.min(lines.length, i + 60); j += 1) {
      if (/^--\s*@node:/u.test(lines[j]!)) return;
      const d = DECL_RE.exec(lines[j]!);
      if (d) {
        out.set(m[1]!, { decl: d[1]!, file, line: j + 1 });
        return;
      }
    }
  });
  return out;
}

const one = (t: string): string => t.replace(/\s+/gu, " ").trim();
const cell = (t: string): string => one(t).replace(/\|/gu, "\\|") || "—";
const code = (t: string): string => `\`${one(t).replace(/`/gu, "ˋ")}\``;

export interface MatchInput {
  report: VerifyReportJson;
  /** `nl_links.json` `results`, or null when the run wrote none. */
  links: NlLinksResult[] | null;
  /** Node id → tagged declaration, over the paper's Lean files. */
  tags: ReadonlyMap<string, NodeTag>;
  /** The corrected core: the conditions each result uses. */
  core: Core;
  /** The paper's Lean directory inside the bundle (`lean/Papers/<Name>`). */
  leanDir: string;
  /** The statements as they stand (`currentStatements`): a result's stored links are printed only when
   *  written for its statement now. Without it they are printed as stored. */
  current?: ReadonlyMap<string, CurrentStatement | null>;
}

/** Whether `link` was written for the statement `now`: under its key, or (links of the flat cut) row for row. */
const linksHold = (link: NlLinksResult, now: CurrentStatement | null): boolean =>
  now !== null && (link.key !== undefined ? link.key === now.key : legacyMatch({ statement: now.statement }, link.rows) === "same");

/** What a row no phrase of the paper states is: an `object` Lean declares (a binder of one, an
 *  instance, a `∀ x` header, a `let`), a `condition` it assumes, or a `conclusion` it draws. */
function unstatedKind(w: NlLinksResult["rows"][number]): "object" | "condition" | "conclusion" {
  if (w.kind === "conclusion") return "conclusion";
  if (w.kind === "instance" || /^let[I]?\s|^haveI\s/.test(w.lean)) return "object";
  const chip = w.kind === "binder" ? binderChip(w.names, w.lean) : w.lean.startsWith("∀") ? forallHeaderChip(w.lean) : "hyp";
  return chip === "decl" ? "object" : "condition";
}

/** A result's corrected statement (the printed one when it stands). */
const statementOf = (r: ReportRow): string => r.change?.corrected ?? r.statement;

export function renderMatch(a: MatchInput): string {
  const { report } = a;
  const names = report.names ?? {};
  const name = (r: ReportRow): string => names[r.node_id] ?? r.node_id;
  const at = (file: string, line: number): string => `\`${a.leanDir}/${file}:${line}\``;
  const linkOf = new Map((a.links ?? []).map((l) => [l.node, l] as const));
  const condText = new Map<string, string>([
    ...a.core.assumptions.map((x) => [x.id, x.condition] as const),
    ...a.core.definitions.map((x) => [x.id, (x as { construction?: string; statement?: string }).construction ?? (x as { statement?: string }).statement ?? ""] as const),
  ]);
  const defIds = new Set(a.core.definitions.map((x) => x.id));
  const L: string[] = [`# The corrected paper and its Lean formalization — ${report.run.qid}`, ""];
  L.push(
    "For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, " +
      "and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked \"corrected\"; " +
      "the report says what changed and why.",
    "",
  );
  if (report.run.early_stop) L.push("The run stopped before the Lean formalization: no result has a Lean declaration.", "");
  for (const r of report.results) {
    const st = formalStatus(r, report.run.early_stop);
    L.push(`## ${name(r)}`, "");
    const how = r.split_from
      ? r.split_kind === "proposition"
        ? ` (a proposition the correction of ${names[r.split_from] ?? "its result"} states apart: the original paper states it inside that result)`
        : ` (a corollary the correction of ${names[r.split_from] ?? "its result"} splits off; the original paper does not state it)`
      : r.change?.corrected ? " (corrected)" : r.change?.descoped ? " (as printed; not part of the corrected paper's formal development)" : "";
    const umbrella = r.umbrella ? umbrellaWords(r, report.results, names) : null;
    L.push(`**Statement${how}.** ${one(umbrella?.sentence ?? statementOf(r))}`, "");
    const split = report.results.filter((x) => x.split_from === r.node_id);
    if (umbrella) L.push(`The original paper states these conclusions in one statement; the correction states each as a proposition of its own, set out after it: ${split.map((x) => names[x.node_id] ?? x.node_id).join(", ")}. This result is established exactly when all of them are.`, "");
    else if (split.length > 0) L.push(`The correction states this result with ${splitCount(split.map((x) => x.split_kind ?? "corollary"))}, set out after it.`, "");
    L.push(`**Lean.** ${r.lean ? `${code(r.lean.decl)} — ${at(r.lean.file, r.lean.line)}` : umbrella ? `no declaration of its own: established as ${umbrella.range} (${split.map((x) => (x.lean ? code(x.lean.decl) : "no declaration")).join(", ")})` : "no declaration"}`, "");
    L.push(`**Status.** ${st.words}.${r.lean || (umbrella && r.axioms) ? ` **Axioms${umbrella ? " (of its propositions together)" : ""}.** ${axiomWords(r.axioms)}.` : ""}`, "");
    const link = linkOf.get(r.node_id);
    const stale = Boolean(link && r.lean && a.current?.has(r.node_id) && !linksHold(link, a.current.get(r.node_id)!));
    if (link && r.lean && stale) L.push("The phrase-by-phrase correspondence on file was written for another version of this Lean statement, so it is not shown (`leansmith relink` writes it again).", "");
    else if (link && r.lean) {
      // a row with no text (links written when a hypothesis's bare name was a row) states nothing
      const rows = link.rows.filter((w) => w.lean.trim() !== "");
      L.push("**Statement correspondence.**", "", "| The paper says | Lean states |", "| --- | --- |");
      for (const s of link.segments) {
        const on = rows.filter((w) => w.segments.includes(s.id));
        L.push(`| ${cell(segmentShown(s.text))} | ${on.length > 0 ? on.map((w) => `${w.coarse ? "≈ " : ""}${w.kind === "conclusion" ? "then " : ""}${code(w.names ? `${w.names} : ${w.lean}` : w.lean)}`).join("<br>") : "— (no Lean counterpart recorded)"} |`);
      }
      L.push("");
      if (rows.some((w) => w.coarse && w.segments.length > 0)) L.push("A row marked ≈ was given these phrases with many rows of its result at once, not on its own.", "");
      // what no phrase states, said for what it is: an object declared, a condition added, a claim added
      const unstated = (what: ReturnType<typeof unstatedKind>) => rows.filter((w) => w.unstated && unstatedKind(w) === what).map((w) => code(w.names ? `${w.names} : ${w.lean}` : w.lean)).join(", ");
      if (unstated("object")) L.push(`Lean also declares what the paper leaves implicit (the objects and their types): ${unstated("object")}.`, "");
      if (unstated("condition")) L.push(`Lean assumes conditions that the paper's text does not state: ${unstated("condition")}.`, "");
      if (unstated("conclusion")) L.push(`Lean concludes what the paper's text does not state: ${unstated("conclusion")}.`, "");
    } else if (r.lean) L.push("No phrase-by-phrase correspondence was recorded for this result.", "");
    const realized: string[] = [];
    const seen = new Set<string>();
    const add = (id: string, text: string, what: string): void => {
      if (seen.has(id) || !text.trim()) return;
      seen.add(id);
      const t = a.tags.get(id);
      realized.push(`- ${what}: ${one(text)} → ${t ? `${code(t.decl)} (${at(t.file, t.line)})` : "no declaration is tagged with it"}`);
    };
    for (const b of r.bookkeeping) add(b.id, b.condition, b.reason.startsWith("pins reading") ? "reading" : "side condition");
    // (what report.md lists for the result under "Added conditions" and its assumed gates: a hypothesis
    // of its own Lean statement, carried by no declaration of its own)
    for (const p of r.added_premises) if (!seen.has(p.label) && p.statement.trim()) { seen.add(p.label); realized.push(`- hypothesis added to the Lean statement${p.classification ? ` (${p.classification})` : ""}: ${one(p.statement)}`); }
    for (const g of r.assumed_substrate) if (!seen.has(g.id) && g.description.trim()) { seen.add(g.id); realized.push(`- assumed, not proved (the result is conditional on it): ${one(g.description)}`); }
    for (const d of a.core.statements.find((s) => s.id === r.node_id)?.depends_on ?? []) if (condText.has(d)) add(d, condText.get(d)!, defIds.has(d) ? "definition of the paper" : "condition of the paper");
    if (realized.length > 0 && r.lean) L.push("**Conditions and readings, and the Lean definitions that carry them.**", "", ...realized, "");
    // The published results it uses directly (itself, when the paper only cites it): what Lean assumes for each.
    const uses = a.core.statements.find((s) => s.id === r.node_id)?.depends_on ?? [];
    for (const c of r.cited_hypotheses) {
      const shown = c.id === r.node_id || uses.includes(c.id) ? citedDisclosure(c, "", (file, line) => (line ? at(file, line) : `\`${a.leanDir}/${file}\``)) : [];
      if (shown.length > 0) L.push(`**Taken from the literature: ${one(c.cite)}${c.locator ? `, ${one(c.locator)}` : ""}.**`, "", ...shown);
    }
  }
  L.push("## Identifiers", "", "| Result | run id | paper label | source | Lean declaration |", "| --- | --- | --- | --- | --- |");
  for (const r of report.results) L.push(`| ${name(r)} | \`${r.node_id}\` | ${r.label ? code(r.label) : "—"} | \`${r.locator}\` | ${r.lean ? code(r.lean.decl) : r.umbrella ? `— (${umbrellaWords(r, report.results, names).range})` : "—"} |`);
  return `${L.join("\n")}\n`;
}
