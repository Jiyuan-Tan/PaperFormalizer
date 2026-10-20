// The promotion checklist the owner edits: `<toolkit>/doc/proposals/<slug>.<round>.md` (a dry run's
// lives under `runs/<slug>/proposals/dry_run/` instead).
//
// One section per main result, written like a textbook entry for a reader who does not read Lean
// — title, reference, the statement in words, why it is reusable, the evidence in words — then a
// secondary "Lean details" block (names, module, the Lean statement, what moves with it), then a
// fenced `decision` block the owner edits. The batch JSON (`runs/<slug>/proposals/<round>.json`) stays
// the authoritative copy of each proposal; parsing reads nothing but the decision blocks.
// Rendering and parsing are deterministic and round-trip.
//
// Decision block grammar (inside ```decision … ```):
//
//     decision: pending | accept | accept_with_edits | generalize_first | decline | defer
//                                  (generalize_first: round B only)
//     note: <text>                 optional, any decision; recorded in the ledger
//     edits:                       accept_with_edits only, followed by one or more
//     <field>: <value>             field ∈ division, target_module, proposed_name, title,
//                                  reference, content
//
// A line that starts with none of these keys continues the previous `note` or edit field (up to
// four leading spaces are stripped). A malformed block is an error naming the proposal id.
//
// A topic an entry needs that the toolkit's tree lacks is its own section (`## topic · <path>`) with
// a decision block of `accept` or `decline`, keyed `topic:<path>`.
import { createHash } from "node:crypto";
import {
  countsAsRecurrence,
  DECISION_KINDS,
  EDITABLE_FIELDS,
  decisionSchema,
  type Decision,
  type EditableField,
  type Proposal,
  type ProposalBatch,
} from "./schema.js";

/** A parsed decision line: a decision, or `pending` (not decided yet). */
export type ChecklistDecision = Decision | { kind: "pending" };

const FENCE_OPEN = "```decision";
const FENCE_CLOSE = "```";

function indentBlock(text: string, indent: string): string {
  return text.split("\n").map((l) => (l.length > 0 ? `${indent}${l}` : l)).join("\n");
}

/** The lines of a decision block for `d`. */
export function serializeDecision(d: ChecklistDecision): string[] {
  const lines = [`decision: ${d.kind}`];
  if (d.kind !== "pending" && d.note) lines.push(...keyValueLines("note", d.note));
  if (d.kind === "accept_with_edits") {
    lines.push("edits:");
    for (const field of EDITABLE_FIELDS) {
      const v = d.edits[field];
      if (v !== undefined) lines.push(...keyValueLines(field, v));
    }
  }
  return lines;
}

function keyValueLines(key: string, value: string): string[] {
  const [first, ...rest] = value.split("\n");
  return [`${key}: ${first}`, ...rest.map((l) => `  ${l}`)];
}

/** Decisions a paper's own stated result allows: it moves verbatim, or its general form is built
 *  and it stays in the paper as a corollary. */
export const PAPER_RESULT_DECISIONS: readonly string[] = ["accept", "accept_with_edits", "generalize_first", "decline", "defer"];

/** What ties the Lean to the paper, in words (the per-declaration list is in the Lean details). */
function paperSettingWords(shaped: readonly string[]): string {
  const kinds: string[] = [];
  const add = (k: string) => { if (!kinds.includes(k)) kinds.push(k); };
  for (const s of shaped) {
    if (/reading pin/.test(s)) add("a reading of its wording the referee pinned");
    else if (/assumption/.test(s)) add("its assumptions");
    else if (/setting /.test(s)) add("its setting");
    else add("objects defined for this paper");
  }
  return kinds.length <= 1 ? (kinds[0] ?? "") : `${kinds.slice(0, -1).join(", ")} and ${kinds[kinds.length - 1]}`;
}

/** Whether an accepted entry is built in general form (round B). */
function generalizes(p: Proposal): boolean {
  return p.path === "generalize" || (p.paper_shaped?.length ?? 0) > 0 || (p.dropped_hypotheses?.length ?? 0) > 0;
}

/** How the entry enters the toolkit if accepted, in words. */
function pathText(p: Proposal): string[] {
  if (p.round === "A") {
    return ["**If accepted.** It is built in your toolkit from scratch (stated as above, proved and reviewed); the paper then uses it instead of assuming it."];
  }
  if (generalizes(p)) {
    const why = p.paper_shaped?.length ? ` Its Lean is stated over the paper's own setting — ${paperSettingWords(p.paper_shaped)} — so it cannot move as is.` : "";
    const dropped = p.dropped_hypotheses?.length
      ? ` The general form drops the hypothesis${p.dropped_hypotheses.length === 1 ? "" : "es"} ${p.dropped_hypotheses.map((h) => `\`${h}\``).join(", ")}, which the paper's proof never uses.`
      : "";
    return [`**If accepted.** Built in general form — the statement above — in your toolkit; the paper's result stays in the paper as a corollary of it.${why}${dropped}`];
  }
  return ["**If accepted.** Moves as is into your toolkit, with the helper lemmas proving it; the paper then uses it from there. (`generalize_first` builds a general form instead.)"];
}

/** Where else the owner's papers state it, in words: identical statements and the pattern or
 *  similar matches the curator confirmed count; the rest are shown as possibly related. */
function recurrenceText(p: Proposal): string {
  const r = p.recurrence ?? [];
  const counted = r.filter(countsAsRecurrence);
  const maybe = [...new Set(r.filter((x) => !countsAsRecurrence(x)).map((x) => x.slug))];
  const deferred = (p.deferred_before ?? []).map((x) => `${x.slug} (${x.proposal_id})`);
  const papers = [...new Set(counted.map((x) => x.slug))];
  const head = papers.length === 0
    ? "first time — no other paper of yours states it"
    : `now in ${papers.length + 1} of your papers: this one and ${papers.join(", ")}` +
      (counted.some((x) => x.kind !== "identical") ? " (the same result under different notation, confirmed by the curator)" : "");
  return head +
    (deferred.length ? `; you deferred it before in ${deferred.join(", ")} — it returns with this evidence` : "") +
    (maybe.length ? `; possibly related in ${maybe.join(", ")}` : "");
}

/** Where it goes, in one line: division › topic, and the bar it meets. */
function goesToText(p: Proposal): string {
  const topic = p.target_module.replace(/\.lean$/, "").split("/").slice(2, -1).join(" › ");
  const signal = p.division_signal && p.division_signal !== p.division
    ? ` (The dependency graph reads it as ${p.division_signal}-shaped: ${p.division_signal === "Tricks" ? "it leans on a domain library or the toolkit" : "it leans on Mathlib alone"}.)`
    : "";
  return `**Goes to.** ${p.division} › ${topic}${p.new_topic ? " (a new topic, decided below)" : ""} — ${p.division_reason ?? "(no reason given)"}${signal}`;
}

/** The curator's advice for a technique seen for the first time. */
function firstSightingText(p: Proposal): string[] {
  if (p.division !== "Tricks" || p.qualifies_by !== "judgement" || (p.recurrence ?? []).some(countsAsRecurrence)) return [];
  return ["**First sighting.** A technique seen in one paper only; deferring it keeps it on record, and it returns when another of your papers proves the same pattern.", ""];
}

function nearestText(p: Proposal): string[] {
  return p.nearest_existing.length === 0
    ? ["  - nothing close was found"]
    : p.nearest_existing.map((n) => `  - ${n.why_not_same} (${n.library}: ${n.name})`);
}

function checkText(p: Proposal): string {
  if (!p.checker) return "not run";
  const mismatch = p.round === "A"
    ? "The statement above is not what the cited work states."
    : generalizes(p)
      ? "The general statement above does not hold, or the paper's result does not follow from it."
      : "The statement above does not say exactly what the Lean proves.";
  const words = p.checker.content_matches === false
    ? ` **${mismatch}**`
    : p.checker.agrees ? "" : " (The statement itself is confirmed; the disagreement is about its wording or placement.)";
  return `${p.checker.agrees ? "agrees" : "**disagrees**"} — ${p.checker.note}${words}`;
}

function renderProposal(p: Proposal, decision: ChecklistDecision): string {
  const own = !p.source.is_paper_result
    ? []
    : generalizes(p)
      ? [`*One of the paper's own results (${p.source.paper_env ?? "?"}): its general form would be built in your toolkit and the paper's result re-proved from it — accept, decline or defer.*`, ""]
      : [`*One of the paper's own results (${p.source.paper_env ?? "?"}): it moves verbatim — accept, decline or defer.*`, ""];
  const moves = p.moves_with ?? [];
  return [
    `## ${p.id} · ${p.title}`,
    "",
    goesToText(p),
    "",
    ...own,
    ...firstSightingText(p),
    `**Reference.** ${p.reference}`,
    "",
    "**Content.**",
    "",
    indentBlock(p.content, "> "),
    "",
    ...(p.relation_to_paper ? [`**In the paper.** ${p.relation_to_paper}`, ""] : []),
    `**Why it is reusable.** ${p.reuse_evidence}`,
    "",
    `**In your other papers.** ${recurrenceText(p)}.`,
    "",
    "**Closest existing results.**",
    ...nearestText(p),
    "",
    ...(p.graph_note ? [`**Where it attaches.** ${p.graph_note}`, ""] : []),
    ...pathText(p),
    "",
    `**Independent check.** ${checkText(p)}`,
    "",
    "<details><summary>Lean details</summary>",
    "",
    `- Name in the toolkit: \`${p.proposed_name}\` in \`${p.target_module}\` (${p.division})` +
      (p.new_module_overview ? ` — a new module: ${p.new_module_overview}` : ""),
    p.round === "A"
      ? `- Cited by the paper as \`${p.source.ref}\`${p.source.citation ? ` (${p.source.citation})` : ""}; assumed until built`
      : `- Proved in the paper as \`${p.source.ref}\``,
    ...(p.lean_type ? [`- Lean statement${p.round === "B" && pathText(p)[0]!.includes("general form") ? " (the paper's instance)" : ""}:`, "", "  ```lean", indentBlock(p.lean_type, "  "), "  ```", ""] : []),
    ...(p.round === "B" ? [`- Moves with it (the helper lemmas proving it and the definitions it needs): ${moves.length ? moves.map((n) => `\`${n}\``).join(", ") : "nothing else"}`] : []),
    ...(p.paper_shaped?.length ? [`- What ties it to the paper: ${p.paper_shaped.join("; ")}`] : []),
    "",
    "</details>",
    "",
    FENCE_OPEN,
    ...serializeDecision(decision),
    FENCE_CLOSE,
    "",
  ].join("\n");
}

export interface RenderChecklistOptions {
  toolkitRoot: string;
  /** Decisions to show instead of `pending` (a re-render keeps the owner's edits). */
  decisions?: Readonly<Record<string, ChecklistDecision>>;
  /** A dry run's checklist: the apply command it shows carries `--dry-run`. */
  dryRun?: boolean;
  /** The toolkit's health on its main view, in words (`toolkit_graph.ts` `healthSummary`). */
  health?: string;
  /** The gardening list the round wrote, when the toolkit's health had findings. */
  garden?: string;
}

/** The new topics the proposed entries need, once each (the owner decides each before anything
 *  moves into it). */
export function newTopics(batch: ProposalBatch): Array<{ path: string; scope: string; for: string[] }> {
  const out = new Map<string, { path: string; scope: string; for: string[] }>();
  for (const p of batch.proposals.filter((x) => x.verdict === "propose" && x.new_topic)) {
    const t = out.get(p.new_topic!.path) ?? { path: p.new_topic!.path, scope: p.new_topic!.scope, for: [] };
    t.for.push(p.id);
    out.set(t.path, t);
  }
  return [...out.values()].sort((a, b) => a.path.localeCompare(b.path));
}

/** Whose a promotion round is, as its stop message says it (rounds A and B). */
export const ROUND_IS_THE_OWNERS = "the owner decides each on the paper's page (the orchestrating agent recommends on each first, with orch.mjs recommend, and waits)";
/** The same round on a full-auto run (`verify --full-auto`): the owner delegated it. */
export const ROUND_IS_DELEGATED = "FULL AUTO, the owner delegated the round: recommend on every entry and new topic (orch.mjs recommend); the last recommendation applies the round as recommended (propose --apply --recommended), listed for the owner's review";

/** The decision key of a new topic. */
export const topicKey = (topicPath: string): string => `topic:${topicPath}`;

/**
 * What a recommendation on an item of a round is ON, by decision key: the entry as the owner reads
 * it (its statement, name, place and path) or the new topic (its path and scope), hashed. A
 * recommendation carries the key of the item it was written for (`of`; `scripts/orch.mjs` computes
 * the same), so one written for an earlier batch's entry of the same id is not shown on this one.
 */
export function recommendationKeys(batch: ProposalBatch): Map<string, string> {
  const h = (parts: unknown[]): string => createHash("sha256").update(JSON.stringify(parts)).digest("hex").slice(0, 16);
  const out = new Map<string, string>();
  for (const p of batch.proposals) out.set(p.id, h([p.id, p.content ?? "", p.proposed_name ?? "", p.target_module ?? "", (p as { path?: string }).path ?? "", p.division ?? ""]));
  for (const t of newTopics(batch)) out.set(topicKey(t.path), h([t.path, t.scope ?? ""]));
  return out;
}

/** Render a batch's main results as the owner's checklist (what is not offered is listed briefly). */
export function renderChecklist(batch: ProposalBatch, opts: RenderChecklistOptions): string {
  const proposed = batch.proposals.filter((p) => p.verdict === "propose");
  const skipped = batch.proposals.filter((p) => p.verdict === "skip");
  const duplicates = skipped.filter((p) => p.duplicate_of);
  const other = skipped.filter((p) => !p.part_of && !p.duplicate_of);
  const local = (ref: string) => ref.slice(ref.lastIndexOf(".") + 1);
  const decide = batch.round === "A"
    ? [
      `Created ${batch.created}. The paper relies on ${proposed.length} cited result(s) it does not prove that could join your toolkit.`,
      "Unbuilt, each stays an assumption of the paper. Decide each by editing the `decision:` line in its",
      "`decision` block:",
      "",
      "- `accept` — build it in your toolkit (proved and reviewed before the paper's proofs); the paper then",
      "  uses it instead of assuming it. Building a deep result takes a while.",
      "- `accept_with_edits` — the same, with your changes: add an `edits:` line, then one `<field>: <value>`",
      `  line per change (fields: ${EDITABLE_FIELDS.join(", ")}; indented lines continue a value).`,
      "- `decline` — it stays a cited assumption of the paper.",
      "- `defer` — not now; it stays an assumption and may be proposed again.",
    ]
    : [
      `Created ${batch.created}. The paper's formalization proved ${proposed.length} result(s) that could join your toolkit.`,
      "Each is one main result; \"If accepted\" says how it enters the toolkit. Decide each by editing the",
      "`decision:` line in its `decision` block:",
      "",
      "- `accept` — bring it into your toolkit as the entry says; the paper then uses it from there.",
      "- `accept_with_edits` — the same, with your changes: add an `edits:` line, then one `<field>: <value>`",
      `  line per change (fields: ${EDITABLE_FIELDS.join(", ")}; indented lines continue a value).`,
      "  What the result proves is not edited; on one of the paper's own results `content` cannot change.",
      "- `generalize_first` — build a general form of it in your toolkit; the paper's result becomes its corollary.",
      "- `decline` — keep it inside the paper.",
      "- `defer` — not now; it stays in the paper and may be proposed again.",
    ];
  const head = [
    `# ${batch.round === "A" ? "Cited results" : "Results"} from ${batch.slug} proposed for your toolkit`,
    "",
    ...decide,
    "- Any decision may carry a `note: <text>` line; it is kept in the ledger.",
    "",
    "Then run:",
    "",
    `    leansmith propose ${batch.slug} --round ${batch.round} --apply --toolkit ${opts.toolkitRoot}${opts.dryRun ? " --dry-run" : ""}`,
    "",
    ...(opts.health ? ["## Your toolkit now", "", opts.health, ""] : []),
    ...(opts.garden ? [`Gardening suggestions for the toolkit as it stands are in \`${opts.garden}\` (the orchestrator decides and carries them out).`, ""] : []),
  ];
  const topics = newTopics(batch).map((t) => [
    `## topic · ${t.path}`,
    "",
    `A new topic for your toolkit: **${t.path.split("/").join(" › ")}** — ${t.scope}. Needed by ${t.for.join(", ")}.`,
    "`accept` adds it to the topic tree (`doc/taxonomy.json`); `decline` keeps the tree as it is — then",
    "choose an existing topic for those entries with `accept_with_edits` (`target_module`).",
    "",
    FENCE_OPEN,
    ...serializeDecision(opts.decisions?.[topicKey(t.path)] ?? { kind: "pending" }),
    FENCE_CLOSE,
    "",
  ].join("\n"));
  const body = [...topics, ...proposed.map((p) => renderProposal(p, opts.decisions?.[p.id] ?? { kind: "pending" }))];
  const tail = [
    ...(duplicates.length ? [
      "## Already available (declined automatically)",
      "",
      ...duplicates.map((p) => `- \`${local(p.source.ref)}\` is already stated by \`${p.duplicate_of}\`; the paper could use that instead.`),
      "",
    ] : []),
    ...(other.length ? [
      "## Not proposed",
      "",
      ...other.map((p) => `- \`${local(p.source.ref)}\`: ${p.reuse_evidence || "(no reason given)"}`),
      "",
    ] : []),
  ];
  return [...head, ...body, ...tail].join("\n");
}

const SECTION_RE = /^## ([ab]-[a-z0-9]+(?:-[a-z0-9]+)*) · /;
const TOPIC_SECTION_RE = /^## topic · (\S+)\s*$/;
const KEY_RE = /^([a-z_]+):(?:\s(.*))?$/;

function blockError(id: string, msg: string): Error {
  return new Error(`proposal ${id}: ${msg}`);
}

/** Parse one decision block's lines (between the fences). */
export function parseDecisionBlock(id: string, lines: readonly string[]): ChecklistDecision {
  const content = lines.map((l) => l.replace(/\s+$/, ""));
  const firstIdx = content.findIndex((l) => l.trim() !== "");
  if (firstIdx === -1) throw blockError(id, "empty decision block (expected `decision: <kind>`)");
  const first = content[firstIdx]!.trim().match(KEY_RE);
  const allowed = ["pending", ...DECISION_KINDS];
  if (!first || first[1] !== "decision" || !allowed.includes((first[2] ?? "").trim())) {
    throw blockError(id, `malformed decision line "${content[firstIdx]!.trim()}" (expected \`decision: ${allowed.join(" | ")}\`)`);
  }
  const kind = (first[2] ?? "").trim();
  let noteText: string | undefined;
  let inEdits = false;
  const edits: Partial<Record<EditableField, string>> = {};
  let current: { key: "note" } | { key: EditableField } | null = null;
  const append = (text: string) => {
    if (!current) throw blockError(id, `unexpected line "${text.trim()}" (not a \`key: value\` line)`);
    if (current.key === "note") noteText = `${noteText ?? ""}\n${text}`;
    else edits[current.key] = `${edits[current.key] ?? ""}\n${text}`;
  };
  for (const raw of content.slice(firstIdx + 1)) {
    const m = raw.match(KEY_RE);
    const key = m?.[1];
    if (m && key === "note") {
      noteText = (m[2] ?? "").trim();
      current = { key: "note" };
    } else if (m && key === "edits" && (m[2] ?? "").trim() === "") {
      if (kind !== "accept_with_edits") throw blockError(id, `an \`edits:\` block needs \`decision: accept_with_edits\`, not ${kind}`);
      inEdits = true;
      current = null;
    } else if (m && (EDITABLE_FIELDS as readonly string[]).includes(key!)) {
      if (!inEdits) throw blockError(id, `field \`${key}\` must follow an \`edits:\` line`);
      edits[key as EditableField] = (m[2] ?? "").trim();
      current = { key: key as EditableField };
    } else if (m && key === "decision") {
      throw blockError(id, "more than one `decision:` line");
    } else if (raw.trim() === "") {
      append("");
    } else {
      append(raw.replace(/^ {1,4}/, ""));
    }
  }
  const tidy = (s: string | undefined) => (s === undefined ? undefined : s.replace(/\n+$/, "").trim() === "" ? undefined : s.replace(/\n+$/, ""));
  noteText = tidy(noteText);
  for (const f of EDITABLE_FIELDS) {
    if (edits[f] !== undefined) {
      const v = tidy(edits[f]);
      if (v === undefined) throw blockError(id, `edit field \`${f}\` is empty`);
      edits[f] = v;
    }
  }
  if (kind === "pending") {
    if (inEdits) throw blockError(id, "an undecided (`pending`) item carries edits");
    return { kind: "pending" };
  }
  if (kind === "accept_with_edits" && Object.keys(edits).length === 0) {
    throw blockError(id, "`accept_with_edits` needs an `edits:` line followed by at least one `<field>: <value>` line");
  }
  const candidate = kind === "accept_with_edits"
    ? { kind, edits, ...(noteText ? { note: noteText } : {}) }
    : { kind, ...(noteText ? { note: noteText } : {}) };
  const parsed = decisionSchema.safeParse(candidate);
  if (!parsed.success) throw blockError(id, parsed.error.issues.map((i) => i.message).join("; "));
  return parsed.data;
}

/**
 * Read the owner's decisions back from a checklist. Every proposed item of `batch` must have
 * exactly one section with one decision block; a section for an unknown id is an error.
 */
export function parseChecklist(text: string, batch: ProposalBatch): Record<string, ChecklistDecision> {
  const proposed = new Set(batch.proposals.filter((p) => p.verdict === "propose").map((p) => p.id));
  const topics = new Set(newTopics(batch).map((t) => topicKey(t.path)));
  const lines = text.split(/\r?\n/);
  const out: Record<string, ChecklistDecision> = {};
  for (let i = 0; i < lines.length; i += 1) {
    const tm = lines[i]!.match(TOPIC_SECTION_RE);
    if (tm) {
      const key = topicKey(tm[1]!);
      if (!topics.has(key)) throw blockError(key, "the checklist has a section for a topic no entry of this batch needs");
      let j = i + 1;
      while (j < lines.length && !/^## /.test(lines[j]!) && lines[j]!.trim() !== FENCE_OPEN) j += 1;
      if (j >= lines.length || lines[j]!.trim() !== FENCE_OPEN) throw blockError(key, "no ```decision block in its section");
      let end = j + 1;
      while (end < lines.length && lines[end]!.trim() !== FENCE_CLOSE) end += 1;
      if (end >= lines.length) throw blockError(key, "unterminated ```decision block");
      const d = parseDecisionBlock(key, lines.slice(j + 1, end));
      if (!["pending", "accept", "decline"].includes(d.kind)) throw blockError(key, `a new topic is accepted or declined (not ${d.kind})`);
      out[key] = d;
      i = end;
      continue;
    }
    const m = lines[i]!.match(SECTION_RE);
    if (!m) continue;
    const id = m[1]!;
    if (!proposed.has(id)) throw blockError(id, `the checklist has a section for ${id}, which is not a proposed item of this batch`);
    if (id in out) throw blockError(id, "the checklist has two sections for this id");
    let j = i + 1;
    while (j < lines.length && !SECTION_RE.test(lines[j]!) && !/^## /.test(lines[j]!) && lines[j]!.trim() !== FENCE_OPEN) j += 1;
    if (j >= lines.length || lines[j]!.trim() !== FENCE_OPEN) throw blockError(id, "no ```decision block in its section");
    const start = j + 1;
    let end = start;
    while (end < lines.length && lines[end]!.trim() !== FENCE_CLOSE) end += 1;
    if (end >= lines.length) throw blockError(id, "unterminated ```decision block");
    out[id] = parseDecisionBlock(id, lines.slice(start, end));
    const item = batch.proposals.find((p) => p.id === id)!;
    if (item.source.is_paper_result && !PAPER_RESULT_DECISIONS.includes(out[id]!.kind) && out[id]!.kind !== "pending") {
      throw blockError(id, `one of the paper's stated results (${item.source.paper_env ?? item.source.ref}) keeps its statement; decide ${PAPER_RESULT_DECISIONS.join(", ")} (not ${out[id]!.kind})`);
    }
    const dk = out[id]!;
    if (item.source.is_paper_result && dk.kind === "accept_with_edits" && dk.edits.content !== undefined) {
      throw blockError(id, `one of the paper's stated results (${item.source.paper_env ?? item.source.ref}) keeps what it proves; \`accept_with_edits\` may change its placement and presentation (division, target_module, proposed_name, title, reference), not content`);
    }
    if (batch.round === "A" && out[id]!.kind === "generalize_first") {
      throw blockError(id, "a cited result is always built in general form; decide accept, accept_with_edits, decline or defer");
    }
    i = end;
  }
  for (const id of [...proposed, ...topics]) if (!(id in out)) throw blockError(id, "missing from the checklist (its section or decision block was deleted)");
  return out;
}

/** The checklist text with each listed section's decision block replaced (other text untouched). Pure. */
export function setDecisions(text: string, decisions: Record<string, ChecklistDecision>): string {
  const lines = text.split(/\r?\n/);
  const eol = text.includes("\r\n") ? "\r\n" : "\n";
  for (const [id, d] of Object.entries(decisions)) {
    const head = lines.findIndex((l) => l.startsWith(`## ${id} · `) || l.trim() === `## topic · ${id.replace(/^topic:/, "")}`);
    if (head < 0) throw new Error(`the checklist has no section for ${id}`);
    let j = head + 1;
    while (j < lines.length && lines[j]!.trim() !== FENCE_OPEN && !/^## /.test(lines[j]!)) j++;
    if (j >= lines.length || lines[j]!.trim() !== FENCE_OPEN) throw new Error(`no decision block in the section of ${id}`);
    let end = j + 1;
    while (end < lines.length && lines[end]!.trim() !== FENCE_CLOSE) end++;
    lines.splice(j + 1, end - (j + 1), ...serializeDecision(d));
  }
  return lines.join(eol);
}

/** A recommendation on an item of a round, as `orch.mjs recommend` writes it (`<round>.recommendations.json`). */
export interface ItemRecommendation { kind?: string; why?: string; of?: string }

/**
 * What the agent's recommendations enter on the items of a round still pending, as the page's
 * "Accept all recommendations" enters them (`propose --apply --recommended`, the apply of a full-auto
 * run): only a recommendation written for the item as it stands (`recommendationKeys`), its reason
 * kept as the decision's note. `missing`: the pending items it gives no decision for. Pure.
 */
export function recommendedDecisions(
  batch: ProposalBatch,
  decided: Readonly<Record<string, ChecklistDecision>>,
  recs: Readonly<Record<string, ItemRecommendation>>,
): { decisions: Record<string, ChecklistDecision>; missing: string[] } {
  const keys = recommendationKeys(batch);
  const decisions: Record<string, ChecklistDecision> = {};
  const missing: string[] = [];
  for (const id of pendingIds(decided, batch)) {
    const r = recs[id];
    const kind = r?.of === keys.get(id) ? r?.kind : undefined;
    const note = r?.why?.trim() ? `as the agent recommended: ${r.why.trim()}` : undefined;
    const entry = batch.proposals.find((p) => p.id === id);
    const ok = entry ? (DECISION_KINDS as readonly string[]).includes(kind ?? "") : kind === "accept" || kind === "decline";
    if (!ok) { missing.push(id); continue; }
    decisions[id] = kind === "accept_with_edits"
      ? { kind, edits: { target_module: entry!.target_module }, ...(note ? { note } : {}) }
      : ({ kind, ...(note ? { note } : {}) } as ChecklistDecision);
  }
  return { decisions, missing };
}

/** Ids still `pending` (new topics first, then entries in batch order). */
export function pendingIds(decisions: Readonly<Record<string, ChecklistDecision>>, batch: ProposalBatch): string[] {
  return [
    ...newTopics(batch).map((t) => topicKey(t.path)).filter((k) => decisions[k]?.kind === "pending"),
    ...batch.proposals.filter((p) => p.verdict === "propose" && decisions[p.id]?.kind === "pending").map((p) => p.id),
  ];
}
