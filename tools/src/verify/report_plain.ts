/**
 * V6 — the report's plain-language part, and the words the bundle's companions share with it.
 *
 * PURE, from the report's JSON alone: what was wrong and what was done (one entry per finding: the
 * printed claim, why it is wrong, the counterexample, the correction or the suggested repair and the
 * owner's decision, the corollaries and propositions the correction splits off, what it gives up, the formal check),
 * the results that could not be checked as printed (not determined: nothing shown false) and the
 * clarifications, both kept apart from the errors, and what was proved in Lean and what was not. Written
 * to accompany a submission or a response letter: results are named as the paper names them
 * (`resultNames`), never by a node id, a stage or a bucket — those stay in the technical appendix
 * (`report.ts`).
 */
import { splitCount, umbrellaRange, umbrellaSentence } from "./core_graph.js";
import { laid } from "./corrected_tex.js";
import type { DeclAxioms } from "./lean_evidence.js";
import type { ReportCitedHypothesis, ReportRow, VerifyReportJson } from "./report.js";
import type { VerifyFinding } from "./types.js";

const KIND_WORD: Record<string, string> = { theorem: "Theorem", lemma: "Lemma", proposition: "Proposition", corollary: "Corollary", definition: "Definition", assumption: "Assumption" };

/** The number of a result numbered by hand: its environment is unnumbered and its note is only a number,
 *  `\begin{corollary*}[(3.2)]` → "3.2". */
export function handNumber(note: string | null | undefined): string | null {
  return /^\(?\s*((?:[A-Z]?\d+|[A-Z])(?:\.\d+)*[a-z]?)\s*\)?$/u.exec((note ?? "").trim())?.[1] ?? null;
}

/**
 * Each result as the paper names it: "Theorem 2" when its label has a number (`numberOf`: the compiled
 * paper's `.aux`; a result in an unnumbered environment by its hand number, `unnumbered` saying which), else by
 * its title, its own label, or where it is printed. A block a repair split
 * off a result is numbered under it, by its kind (`split_kind`) — "Corollary 2.1", "Proposition 2.2":
 * one running number per result across both kinds — never as one of the paper's own numbers
 * ("Corollary 1 of …" when the result has no number).
 */
export function resultNames(rows: readonly ReportRow[], numberOf: (label: string) => string | undefined, unnumbered: (r: ReportRow) => boolean = () => false): Record<string, string> {
  const out: Record<string, string> = {};
  for (const r of rows.filter((x) => !x.split_from)) {
    const word = KIND_WORD[r.kind] ?? "Result";
    // the .aux numbers a label in an unnumbered environment by the enclosing counter: its hand number wins
    const n = (unnumbered(r) ? handNumber(r.title) : null) ?? (r.label ? numberOf(r.label) : undefined);
    const at = /^(.*):(\d+)-\d+$/u.exec(r.locator);
    out[r.node_id] = n ? `${word} ${n}` : r.title ? `${word} (${r.title.replace(/\s+/gu, " ").trim()})` : r.label ? `${word} labelled \`${r.label}\`` : `${word} at ${at ? `${at[1]}, line ${at[2]}` : r.locator}`;
    const split = rows.filter((x) => x.split_from === r.node_id);
    split.forEach((c, k) => {
      const word = c.split_kind === "proposition" ? "Proposition" : "Corollary";
      out[c.node_id] = n ? `${word} ${n}.${k + 1}` : `${word} ${k + 1} of ${out[r.node_id]}`;
    });
  }
  return out;
}

/** An umbrella row's blocks named together ("Propositions 5.2.1–5.2.6"; "its propositions" when
 * they have no numbers), and the sentence it is stated as (`core_graph.ts` `umbrellaSentence`). */
export function umbrellaWords(r: ReportRow, rows: readonly ReportRow[], names: Readonly<Record<string, string>>): { range: string; sentence: string } {
  const blocks = rows.filter((x) => x.split_from === r.node_id).map((x) => names[x.node_id] ?? "");
  return { range: umbrellaRange(blocks) ?? "its propositions", sentence: umbrellaSentence(blocks) };
}

const STANDARD_AXIOMS = new Set(["propext", "Classical.choice", "Quot.sound"]);

/** A declaration's axioms, in words. */
export function axiomWords(a: DeclAxioms | null): string {
  if (!a) return "not audited";
  if (a.error) return `not audited (${a.error})`;
  if (a.axioms.length === 0) return "none";
  const extra = a.axioms.filter((x) => !STANDARD_AXIOMS.has(x));
  return extra.length === 0 ? `the standard ones only (${a.axioms.join(", ")})` : `NOT standard: ${extra.map((x) => `\`${x}\``).join(", ")}`;
}

export type FormalStatus = "proved" | "cited" | "not certified" | "not formalized";

/** What Lean establishes about one result, in words (`status`: the word MATCH.md tabulates). */
export function formalStatus(r: ReportRow, earlyStop: boolean): { status: FormalStatus; words: string } {
  if (r.change?.descoped) return { status: "not formalized", words: "not formalized: it was left out of the corrected paper's formal development" };
  if (r.bucket === "refuted") return { status: "not formalized", words: "not formalized: it is false as printed and has no adopted repair" };
  if (r.bucket === "not_determined") return { status: "not formalized", words: "not formalized: it could not be checked as printed and has no adopted reading or repair (this is not a claim that the result is wrong)" };
  if (r.bucket === "not_checked" || earlyStop) return { status: "not formalized", words: "not formalized: the run stopped before the Lean formalization" };
  if (r.bucket === "unresolved") return { status: "not certified", words: `not certified: the Lean formalization of ${r.umbrella ? "one of its propositions" : "it"} did not close (this is not a claim that the result is wrong)` };
  if (r.cited_hypotheses.some((c) => c.id === r.node_id)) return { status: "cited", words: "taken from the literature as cited; not proved here" };
  const given = [
    r.cited_hypotheses.length > 0 ? `${r.cited_hypotheses.length} cited result(s)` : "",
    r.assumed_substrate.length > 0 ? `${r.assumed_substrate.length} standard fact(s) left assumed` : "",
  ].filter(Boolean);
  const under = r.bookkeeping.length + r.added_premises.length;
  return {
    status: "proved",
    words:
      (r.umbrella ? "established through its propositions, each proved in Lean (it has no Lean declaration of its own)" : `proved in Lean${r.change?.corrected ? " (the corrected statement)" : ""}`) +
      (given.length > 0 ? `, given ${given.join(" and ")}` : "") +
      (under > 0 ? `, under ${under} condition(s) made explicit` : ""),
  };
}

/** One line of a text of the run: the annotated paper's layout macros written out. */
const one = (t: string): string => laid(t).replace(/\s+/gu, " ").trim();
const clip = (t: string, n: number, more: string): string => (one(t).length > n ? `${one(t).slice(0, n).replace(/\s+\S*$/u, "")} … (${more})` : one(t));
const refuted = (fs: readonly VerifyFinding[]): VerifyFinding[] => fs.filter((f) => f.kind === "refuted");
/** What left a statement not determined (`VerifyFinding.undetermined`): nothing shown false. */
const undetermined = (fs: readonly VerifyFinding[]): VerifyFinding[] => fs.filter((f) => f.kind === "unresolved" && f.undetermined === true);
/** A statement the paper left undetermined, made precise by a confirmed repair (`report.ts` `isMadePrecise`). */
const madePrecise = (fs: readonly VerifyFinding[]): VerifyFinding | undefined => fs.find((f) => f.kind === "note" && f.undetermined === true && f.patch?.confirmed === true);
const declWords = (r: ReportRow): string => (r.lean ? ` — \`${r.lean.decl}\` (\`${r.lean.file}:${r.lean.line}\`); axioms: ${axiomWords(r.axioms)}` : "");

/** What a repair gives up and who settled it, or null. */
function givesUp(fs: readonly VerifyFinding[]): string | null {
  const p = fs.map((f) => f.patch).find((x) => x?.narrowed);
  if (!p?.narrowed) return null;
  return `${one(p.narrowed)} ${p.narrowed_by === "runner" ? "(An intermediate result: its strongest true version was adopted.)" : "(The paper's owner accepted the weaker statement.)"}`;
}

/** What a result rests on that is itself open, each named for what it is: found wrong, or not determined. */
function restsOn(r: ReportRow, name: (id: string) => string): string | null {
  const open = new Set(r.rests_on_undetermined ?? []);
  const wrong = r.inherits_refutation_from.filter((id) => !open.has(id)).map(name);
  const parts = [
    wrong.length > 0 ? `${wrong.join(", ")}, ${r.bucket === "not_determined" ? "" : "also "}found wrong as printed` : "",
    open.size > 0 ? `${[...open].map(name).join(", ")}, which ${r.bucket === "not_determined" ? "also " : ""}could not be checked as printed` : "",
  ].filter(Boolean);
  return parts.length > 0 ? `- **Rests on.** ${parts.join("; ")}.` : null;
}

/** The entry of a result that could not be checked as printed (`not_determined`): never worded as wrong. */
function undeterminedEntry(json: VerifyReportJson, r: ReportRow, name: (id: string) => string): string[] {
  const fs = undetermined(r.findings);
  const out = r.change?.descoped || fs.some((f) => f.descoped);
  const L = [`### ${name(r.node_id)} — could not be checked as printed${out ? "; left out of the corrected paper's formal development" : ""}`, ""];
  L.push(`- **As printed.** ${one(r.statement)}`);
  const ex = json.explanations?.[r.node_id];
  // (a finding with a witness is a repair that was tried and refuted: listed apart, below)
  L.push(`- **What is not determined.** ${ex && ex.what_is_wrong.some((t) => t.trim()) ? ex.what_is_wrong.filter((t) => t.trim()).map(one).join(" ") : fs.filter((f) => !f.witness).map((f) => one(f.detail)).join(" ")}`);
  const rests = restsOn(r, name);
  if (rests) L.push(rests);
  const rejected = fs.find((f) => f.patch && !f.patch.confirmed);
  if (rejected?.patch?.corrected_statement) L.push(`- **A repair was tried and rejected by the confirming check.** ${one(rejected.patch.corrected_statement)}`);
  for (const f of fs.filter((x) => x.witness)) L.push(`- **Why the repair tried was rejected.** ${one(f.detail)} Counterexample to the reading tried (not to the printed statement): ${one(f.witness!)}`);
  const sug = fs.find((f) => f.suggested_repair);
  if (sug) {
    L.push(`- **Suggested repair (not applied).** ${one(sug.suggested_repair!)}`);
    L.push(`- **Owner's decision.** ${sug.suggestion_declined !== undefined ? `Declined: ${one(sug.suggestion_declined) || "no reason recorded"}` : "None recorded: the suggestion weakens the result, so it was not applied."}`);
  } else L.push("- **Correction.** None: the paper does not determine a reading, and no repair that keeps the point of the result was found.");
  L.push(`- **Formal check.** ${formalStatus(r, json.run.early_stop).words}${declWords(r)}.`, "");
  return L;
}

/** The entry of one finding on a result. */
function resultEntry(json: VerifyReportJson, r: ReportRow, name: (id: string) => string): string[] {
  const fs = refuted(r.findings);
  const repaired = fs.every((f) => f.patch?.confirmed === true);
  const c = r.change;
  const gu = givesUp(fs);
  const umbrella = r.umbrella ? umbrellaWords(r, json.results, json.names ?? {}) : null;
  const corrected = umbrella?.sentence ?? c?.corrected ?? fs.map((f) => (f.patch?.confirmed ? f.patch.corrected_statement : null)).find(Boolean) ?? null;
  const outcome = !repaired
    ? c?.descoped || fs.some((f) => f.descoped) ? "not repaired; left out of the corrected paper's formal development" : "not repaired"
    : umbrella ? `established as ${umbrella.range}${gu ? "; together they claim less than the printed statement" : ""}` : corrected ? (gu ? "corrected; the corrected statement is weaker" : "corrected") : "statement unchanged; proof corrected";
  const L = [`### ${name(r.node_id)} — ${outcome}`, ""];
  L.push(`- **As printed.** ${one(r.statement)}`);
  const ex = json.explanations?.[r.node_id];
  const wrong = ex && ex.what_is_wrong.some((t) => t.trim()) ? ex.what_is_wrong.filter((t) => t.trim()).map(one).join(" ") : fs.map((f) => one(f.detail)).join(" ");
  L.push(`- **What is wrong.** ${wrong}`);
  const witness = (ex?.why.trim() ? ex.why : fs.map((f) => f.witness).find(Boolean)) ?? null;
  if (witness) L.push(`- **Counterexample.** ${one(witness)}`);
  const rests = restsOn(r, name);
  if (rests) L.push(rests);
  if (repaired) {
    L.push(`- **Correction.** ${corrected ? one(corrected) : "The statement stands as printed; its proof is corrected."}`);
    const proof = umbrella ? null : fs.map((f) => f.patch?.proof_note).find(Boolean) ?? c?.proof_change?.replace(/^the printed proof, revised step by step\]\s*/u, "") ?? null;
    if (proof) L.push(`- **Proof.** ${clip(proof, 700, "the corrected paper gives it in full")}`);
    const split = json.results.filter((x) => x.split_from === r.node_id);
    if (umbrella) {
      L.push(`- **Split.** The printed statement mixes several conclusions, each under its own conditions; the correction states every one as a proposition of its own (${umbrella.range}). The result is established exactly when all of them are. Nothing moved to one of them counts as given up.`);
      for (const c of split) L.push(`  - **${name(c.node_id)}.** ${one(c.statement)} Formal check: ${formalStatus(c, json.run.early_stop).words}${declWords(c)}.`);
    } else if (split.length > 0) {
      const kinds = split.map((x) => x.split_kind ?? "corollary");
      const props = kinds.filter((x) => x === "proposition").length;
      L.push(
        `- **Split.** The correction states this result as the statement above and ${splitCount(kinds)}, each a result of its own` +
          `${props === 0 ? "" : props === kinds.length ? ` (${props === 1 ? "a separate claim" : "separate claims"} the printed statement bundled in, not ${props === 1 ? "a consequence" : "consequences"} of the statement above)` : " (a corollary follows from the statement above; a proposition is a separate claim the printed statement bundled in)"}. ` +
          "Nothing moved to one of them counts as given up.",
      );
      for (const c of split) L.push(`  - **${name(c.node_id)}.** ${one(c.statement)} Formal check: ${formalStatus(c, json.run.early_stop).words}${declWords(c)}.`);
    }
    if (gu) L.push(`- **What the correction gives up.** ${gu}`);
    if ((c?.dropped_dependencies.length ?? 0) > 0) L.push(`- **Conditions.** The corrected statement states the conditions it uses itself; it no longer refers to ${c!.dropped_dependencies.length} condition(s) of the paper it used as printed.`);
  } else {
    const rejected = fs.find((f) => f.patch && !f.patch.confirmed);
    if (rejected?.patch?.corrected_statement) L.push(`- **A repair was tried and rejected by the confirming check.** ${one(rejected.patch.corrected_statement)}`);
    const sug = fs.find((f) => f.suggested_repair);
    if (sug) {
      L.push(`- **Suggested repair (not applied).** ${one(sug.suggested_repair!)}`);
      L.push(`- **Owner's decision.** ${sug.suggestion_declined !== undefined ? `Declined: ${one(sug.suggestion_declined) || "no reason recorded"}` : "None recorded: the suggestion weakens the result, so it was not applied."}`);
    } else L.push("- **Correction.** None: no repair that keeps the point of the result was found.");
  }
  L.push(`- **Formal check.** ${formalStatus(r, json.run.early_stop).words}${declWords(r)}${r.umbrella && r.axioms ? `; axioms of its propositions together: ${axiomWords(r.axioms)}` : ""}.`, "");
  return L;
}

/**
 * What a cited result stands for in the formalization, as markdown lines under `indent`: the Lean
 * declaration assumed for it with its source text, and — for a result a proof invokes by citation —
 * the passage of that proof. Empty when the report holds neither. `at`: how a file and line are written.
 */
export function citedDisclosure(c: ReportCitedHypothesis, indent = "", at = (file: string, line: number | null): string => `\`${file}${line ? `:${line}` : ""}\``): string[] {
  const L: string[] = [];
  if (c.lean) {
    L.push(`What Lean assumes for it: \`${c.lean.decl}\` (${at(c.lean.file, c.lean.line)})`, "");
    if (c.lean.statement) L.push("```lean", ...c.lean.statement.split("\n"), "```", "");
    else L.push("(the declaration was not found in that file)", "");
  }
  if (c.passage) L.push("The passage of the proof:", "", ...c.passage.split("\n").map((l) => `> ${l}`), "");
  return L.map((l) => (l ? `${indent}${l}` : l));
}

/** The report's plain-language sections (see the module doc). */
export function renderPlainSections(json: VerifyReportJson): string[] {
  const names = json.names ?? {};
  const name = (id: string): string => names[id] ?? "a condition or definition of the paper";
  const rows = json.results;
  const wrong = rows.filter((r) => refuted(r.findings).length > 0);
  const repairedRows = wrong.filter((r) => refuted(r.findings).every((f) => f.patch?.confirmed === true));
  const conditions = refuted(json.run_level_findings);
  // Not determined: could not be checked as printed, nothing shown false — counted and listed apart.
  const open = rows.filter((r) => r.bucket === "not_determined");
  const openConditions = undetermined(json.run_level_findings);
  // Made precise: the paper left the statement undetermined and a confirmed repair states the reading adopted.
  const precise = rows.filter((r) => !wrong.includes(r) && !open.includes(r) && madePrecise(r.findings));
  const followed = rows.filter((r) => !wrong.includes(r) && !open.includes(r) && !precise.includes(r) && r.change?.corrected);
  const status = rows.map((r) => formalStatus(r, json.run.early_stop).status);
  const count = (s: FormalStatus): number => status.filter((x) => x === s).length;
  const split = rows.filter((r) => r.split_from).length;
  const L: string[] = [];

  L.push(
    `${rows.length - split} result(s) of the paper were examined${split > 0 ? `, and ${splitCount(rows.filter((r) => r.split_from).map((r) => r.split_kind ?? "corollary"))} a correction split off them` : ""}. ` +
      (wrong.length === 0
        ? "None was found wrong as printed. "
        : `${wrong.length} ${wrong.length === 1 ? "was" : "were"} found wrong as printed: ${repairedRows.length} corrected` +
          `${repairedRows.filter((r) => givesUp(refuted(r.findings))).length > 0 ? ` (${repairedRows.filter((r) => givesUp(refuted(r.findings))).length} by a weaker statement)` : ""}, ${wrong.length - repairedRows.length} not repaired. `) +
      (precise.length > 0 ? `${precise.length} ${precise.length === 1 ? "was" : "were"} made precise: the printed statement did not determine what is claimed, and the reading adopted was confirmed (not an error). ` : "") +
      (open.length > 0 ? `${open.length} could not be checked as printed: ${open.length === 1 ? "it does" : "they do"} not say enough to determine what is claimed (not shown false). ` : "") +
      (json.run.early_stop
        ? "The run stopped before the Lean formalization."
        : `In Lean: ${count("proved")} proved, ${count("cited")} taken from the literature as cited, ${count("not certified")} not certified, ${count("not formalized")} not formalized.`),
    "",
  );

  L.push("## What was wrong and what was done", "");
  if (wrong.length + conditions.length + followed.length === 0) L.push("No error was found in the results examined.", "");
  for (const r of wrong) L.push(...resultEntry(json, r, name));
  if (conditions.length > 0) {
    L.push("### Conditions and definitions restated", "");
    L.push("Conditions or definitions the paper states too loosely for the results that use them; the corrected results now state what they use.", "");
    for (const f of conditions) {
      const ex = json.explanations?.[f.node];
      const what = ex?.claim.trim() ? one(ex.claim) : one(f.detail);
      const why = ex && ex.what_is_wrong.some((t) => t.trim()) ? ` ${ex.what_is_wrong.filter((t) => t.trim()).map(one).join(" ")}` : "";
      const fix = f.patch?.confirmed
        ? f.patch.corrected_statement ? ` Corrected text: ${one(f.patch.corrected_statement)}` : ex?.fix.trim() ? ` ${one(ex.fix)}` : " The results using it are restated."
        : " Not repaired.";
      L.push(`- ${what}${why}${fix}`);
    }
    L.push("");
  }
  if (followed.length > 0) {
    L.push("### Restated to follow a correction above", "");
    L.push("No error of their own: these results use a corrected result and are restated accordingly.", "");
    for (const r of followed) L.push(`- **${name(r.node_id)}.** ${one(r.change!.corrected!)}`);
    L.push("");
  }

  const preciseConditions = json.run_level_findings.filter((f) => madePrecise([f]));
  if (precise.length + preciseConditions.length > 0) {
    L.push("## Statements made precise (not errors)", "");
    L.push("Nothing in this section was shown false. As printed, each statement did not determine what is claimed; it now states the reading adopted, which an independent referee pass confirmed.", "");
    for (const r of precise) {
      const f = madePrecise(r.findings)!;
      const corrected = r.change?.corrected ?? f.patch?.corrected_statement ?? null;
      L.push(`### ${name(r.node_id)} — made precise`, "");
      L.push(`- **As printed.** ${one(r.statement)}`);
      L.push(`- **What was not determined.** ${one(f.detail.replace(/^made precise — [^:]*:\s*/u, ""))}`);
      L.push(`- **As it reads now.** ${corrected ? one(corrected) : "The statement stands as printed; the reading adopted is stated with it."}`);
      const gu = givesUp([f]);
      if (gu) L.push(`- **What the reading adopted gives up.** ${gu}`);
      L.push(`- **Formal check.** ${formalStatus(r, json.run.early_stop).words}${declWords(r)}.`, "");
    }
    if (preciseConditions.length > 0) {
      L.push("### Conditions and definitions made precise", "");
      for (const f of preciseConditions) L.push(`- ${one(f.detail.replace(/^made precise — [^:]*:\s*/u, ""))}${f.patch?.corrected_statement ? ` Now: ${one(f.patch.corrected_statement)}` : ""}`);
      L.push("");
    }
  }

  if (open.length + openConditions.length > 0) {
    L.push("## What could not be checked as printed", "");
    L.push("Nothing in this section was shown false. Each item does not say enough to be checked — the paper does not determine what is claimed — and no reading or repair was adopted.", "");
    for (const r of open) L.push(...undeterminedEntry(json, r, name));
    if (openConditions.length > 0) {
      L.push("### Conditions and definitions left undetermined", "");
      for (const f of openConditions) {
        const ex = json.explanations?.[f.node];
        L.push(`- ${ex && ex.what_is_wrong.some((t) => t.trim()) ? ex.what_is_wrong.filter((t) => t.trim()).map(one).join(" ") : one(f.detail)}`);
      }
      L.push("");
    }
  }

  // Not errors: readings, side conditions, proofs written out, findings the owner withdrew.
  const seen = new Set<string>();
  const readings: string[] = [];
  const sides: string[] = [];
  for (const r of rows) {
    for (const b of r.bookkeeping) {
      if (seen.has(b.id)) continue;
      seen.add(b.id);
      (b.reason.startsWith("pins reading") ? readings : sides).push(`- **${name(r.node_id)}.** ${one(b.condition)}`);
    }
  }
  const written = rows.filter((r) => !wrong.includes(r) && !precise.includes(r) && r.change && !r.change.corrected && r.change.proof_change);
  const withdrawn = json.withdrawn_findings ?? [];
  const symbols = json.symbol_readings ?? [];
  L.push("## Clarifications (not errors)", "");
  if (readings.length + sides.length + written.length + withdrawn.length + symbols.length === 0) L.push("None.", "");
  else {
    L.push("Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.", "");
    if (readings.length > 0) L.push("**How a statement is read.**", "", ...readings, "");
    if (sides.length > 0) L.push("**Side conditions the proofs use without stating them.**", "", ...sides, "");
    if (symbols.length > 0) L.push("**Notation.**", "", ...symbols.map((s) => `- $${s.symbol}$: ${one(s.reading)}`), "");
    if (written.length > 0) L.push("**Proofs completed** (a step of the printed argument could not be checked as it stands, so it was completed; no error was found).", "", ...written.map((r) => `- ${name(r.node_id)}`), "");
    if (withdrawn.length > 0) {
      L.push("**Objections raised during the review and withdrawn.** The paper's owner showed that each misreads the paper; the printed statement stands under the reading given.", "");
      for (const w of withdrawn) L.push(`- **${name(w.node)}.** ${one(w.reason)}`);
      L.push("");
    }
  }

  L.push("## What was proved in Lean, and what was not", "");
  if (json.run.early_stop) L.push("Nothing: the run stopped before the Lean formalization.", "");
  else {
    L.push("A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.", "");
    L.push("| Result | Formal status | Lean declaration | Axioms |", "| --- | --- | --- | --- |");
    for (const r of rows) {
      L.push(`| ${name(r.node_id)} | ${formalStatus(r, false).words} | ${r.lean ? `\`${r.lean.decl}\` (\`${r.lean.file}:${r.lean.line}\`)` : "—"} | ${r.lean ? axiomWords(r.axioms) : "—"} |`);
    }
    L.push("");
    const cited = new Map(rows.flatMap((r) => r.cited_hypotheses).map((c) => [c.id, c] as const));
    if (cited.size > 0) {
      L.push("**Taken from the literature, not proved here.**", "");
      for (const c of cited.values()) {
        L.push(`- ${one(c.cite)}${c.locator ? `, ${one(c.locator)}` : ""} — ${c.source_check ? `checked against ${one(c.source_check)}` : c.unchecked_reason ? one(c.unchecked_reason) : "not checked against its source"}`);
        // What the citation stands for in the proofs above: disclosed, since Lean takes it as given.
        const shown = citedDisclosure(c, "  ");
        if (shown.length > 0) L.push("", ...shown.slice(0, -1));
      }
      L.push("");
    }
    const gates = new Map(rows.flatMap((r) => r.assumed_substrate).map((g) => [g.id, g] as const));
    if (gates.size > 0) L.push("**Standard facts left assumed** (classical results not yet in the library; not gaps of the paper).", "", ...[...gates.values()].map((g) => `- ${one(g.description)}`), "");
    const premises = new Map(rows.flatMap((r) => r.added_premises).map((p) => [p.label, p] as const));
    if (premises.size > 0) L.push("**Conditions made explicit during the formalization.**", "", ...[...premises.values()].map((p) => `- ${one(p.statement)}`), "");
    if (json.lean_build) {
      L.push(`The Lean development ${json.lean_build.ok ? "builds" : "does NOT build"}; ${(json.sorry_scan ?? []).length === 0 ? "it contains no `sorry`, `admit` or added axiom" : `the source scan reports ${(json.sorry_scan ?? []).length} issue(s) (technical appendix)`}.`, "");
    }
  }

  const b = json.bundle;
  if (b) {
    L.push("## The corrected paper", "");
    if (b.error) L.push(`The corrected paper could not be written: ${b.error}`, "");
    else {
      L.push(
        `\`${b.dir}/${b.paper.dir ?? "paper"}/\` holds the paper as it reads after the corrections, as plain source in the author's own class and layout` +
          (b.paper.pdf ? `, compiled to \`${b.dir}/${b.paper.dir ?? "paper"}/${b.paper.pdf}\`${b.paper.pages ? ` (${b.paper.pages} pages)` : ""}` : b.paper.compile.status === "failed" ? `; compiling it FAILED (${b.paper.compile.reason})` : `; not compiled (${b.paper.compile.reason})`) +
          `. \`${b.dir}/MATCH.md\` sets each result beside its Lean declaration${b.lean ? `; \`${b.dir}/lean/\` holds the Lean code` : ""}.`,
        "",
        b.todo.total === 0
          ? "The mechanical checks leave nothing open."
          : `**${b.todo.total} item(s) remain before the paper is ready to submit** (${b.todo.blocking} blocking), each with its place in the source: \`${b.dir}/${b.paper.dir ?? "paper"}/TODO.md\`. ` +
            "What is checked is the paper's results; the prose around them is the authors', as printed.",
        "",
      );
    }
  }
  return L;
}
