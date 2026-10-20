// The curator: ONE schema-constrained Claude call that judges every candidate of a round — `propose`
// a MAIN result (written for a reader who does not read Lean: title, reference, the statement in
// words; with a division and topic and the bar it meets, a path into the toolkit and the nearest
// existing declaration) or `skip` (a helper that enters with a main result, or nothing worth a
// toolkit entry). The round's brief (`prompts/round_a.txt` / `round_b.txt`) says what the candidates
// are. Its input is grounded and kept small: a likely main result carries its Lean statement and the
// top search hits over every indexed base library and the toolkit; a helper (a candidate another
// candidate's proof uses) is one line under its owner. The toolkit's existing modules, its topic
// tree and the ledger's decision history are attached, so "declined before" and "seen in N papers"
// are evidence. The runner checks the reply's structure (judgment is the curator's, structure is the
// lint's) and asks once more on a contract violation.
import { docstringContract } from "../shared/docstring_contract.js";
import { existsSync } from "node:fs";
import { mkdir, readdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { createRetrieval } from "../formalization/reuse_retrieval.js";
import { indexSourcesFromToolkit } from "../library/sources.js";
import { MODELS } from "../models.js";
import { claudeRoleModel, claudeRoles } from "../claude_roles.js";
import type { runCodex as RunCodex } from "../shared/codex.js";
import { expectStringJsonOutput, persistCodexRaw } from "../shared/codex_json.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { addTokenUsage, appendTokenUsageRecord, markTokenUsageIncomplete, type ModelTokenUsage } from "../token_usage.js";
import { runTokenIn } from "../toolkit/layout_lint.js";
import { loadLedger } from "../toolkit/ledger.js";
import { effectiveTaxonomy, newTopicProblem, taxonomyPromptText, topicOfModulePath, type Taxonomy } from "../toolkit/taxonomy.js";
import type { ClaudeRunInput } from "../workers/claude.js";
import {
  assignProposalIds,
  proposalDecisionRecordSchema,
  proposalsRunDir,
  QUALIFIES_BY,
  type NearestExisting,
  type NewTopic,
  type Proposal,
  type ProposalRound,
  type ProposalSource,
  type Recurrence,
} from "./schema.js";

/** A candidate as the curator sees it. Round-specific extraction fills it. */
export interface ProposalCandidate {
  /** The declaration's fully-qualified name. */
  candidate_id: string;
  source: ProposalSource;
  /** Statement kind (lemma, theorem, …) or declaration kind. */
  kind: string;
  /** The statement as the paper (or the Lean declaration) gives it. */
  statement: string;
  /** Facts shown to the curator verbatim (the Lean type, docstring, closure, …). */
  context: Record<string, unknown>;
  /** Words the lexical search uses for the title (default: derived from `candidate_id`). */
  search_words?: string;
  /** What the stable proposal id is derived from (default: `source.ref`). */
  id_ref?: string;
  /** Paper declarations that move with this one. Copied onto the proposal. */
  moves_with?: string[];
  /** The Lean statement as proved. Copied onto the proposal. */
  lean_type?: string;
  /** The same statement in other papers (`doc/statements.json`; round A: the same cited theorem).
   *  Copied onto the proposal, with the curator's confirmations. */
  recurrence?: Recurrence[];
  /** Round B: what ties the Lean to the paper (`paperShapedReasons`); set, the entry is built in
   *  general form. Copied onto the proposal. */
  paper_shaped?: string[];
  /** Round A: the cited work's own text of the result. Copied onto the proposal. */
  source_text?: string;
  /** What the statement leans on (Mathlib alone → Foundations-shaped; a domain library or the
   *  toolkit → Tricks-shaped). Copied onto the proposal. */
  division_signal?: "Foundations" | "Tricks";
  /** Hypotheses the paper's proof never uses: the entry is built in general form without them. */
  dropped_hypotheses?: string[];
  /** The same entry deferred before in another paper. Copied onto the proposal. */
  deferred_before?: Array<{ slug: string; proposal_id: string }>;
  /** Candidates whose proof uses this one: set, it is shown to the curator as one helper line. */
  helper_of?: string[];
}

export interface SearchHit { name: string; library: string; module: string; statement: string; doc: string }

export interface GroundedCandidate extends ProposalCandidate { search_hits: SearchHit[] }

export interface CuratorArgs {
  toolkit: ToolkitConfig;
  slug: string;
  /** Default `B`. */
  round?: ProposalRound;
  candidates: readonly ProposalCandidate[];
  dryRun: boolean;
  /** The curator runs on Claude (`MODELS.claudeMain`); default: the claude CLI worker. */
  runClaude?: (o: ClaudeRunInput) => Promise<string>;
  log: (msg: string) => void;
  /** The topic tree (default: the toolkit's, else the template's). */
  taxonomy?: Taxonomy;
}

const PROMPT_DIR = path.join(path.dirname(fileURLToPath(import.meta.url)), "prompts");
const HITS_PER_LIBRARY = 2;
const MAX_HITS = 4;
const HIT_TEXT = 140;
const MAX_MODULES = 200;
const MAX_HISTORY = 200;
const HISTORY_TEXT = 140;
/** An index round proposes at most this many entries (`round_b.txt` says so; the lint enforces it). */
export const MAX_INDEX_PROPOSALS = 30;

/** Top lexical hits per candidate over every indexed source (base libraries + toolkit). */
export function groundCandidates(cfg: ToolkitConfig, candidates: readonly ProposalCandidate[]): GroundedCandidate[] {
  const r = createRetrieval(indexSourcesFromToolkit(cfg));
  return candidates.map((c) => {
    if (c.helper_of?.length) return { ...c, search_hits: [] };
    const words = (c.search_words ?? c.candidate_id.split(":")[1] ?? c.candidate_id).replace(/[-_.]/g, " ");
    const hits = r.libraries.flatMap((lib) =>
      r.search({ mode: "concept", title: `${words} ${c.kind}`, label: c.candidate_id, bodyTerms: [c.statement] }, { library: lib.name, topK: HITS_PER_LIBRARY })
        .map((h) => ({
          name: h.name,
          library: h.library,
          module: h.module,
          statement: h.statement.replace(/\s+/g, " ").slice(0, HIT_TEXT),
          doc: h.docFirstPara.slice(0, HIT_TEXT),
        })));
    return { ...c, search_hits: hits.slice(0, MAX_HITS) };
  });
}

/** The candidates as the prompt shows them: a likely main result in full; a candidate another
 *  candidate's proof uses (`helper_of`) compact — its Lean statement and the candidates using it,
 *  no search hits or docstring — since it usually enters only with its owner (yet may be a main
 *  result when its users are not). */
export function promptCandidates(grounded: readonly GroundedCandidate[]): unknown[] {
  return grounded.map((c) => {
    // `context` already carries the Lean statement, what ties it to the paper and the unused hypotheses.
    const { search_words: _w, id_ref: _i, moves_with: _m, lean_type: _l, paper_shaped: _p, dropped_hypotheses: _d, ...all } = c;
    const shaped = Array.isArray(c.context.paper_shaped) ? (c.context.paper_shaped as string[]) : null;
    const rest = {
      ...all,
      ...(shaped && shaped.length > 3 ? { context: { ...c.context, paper_shaped: [...shaped.slice(0, 3), `(+${shaped.length - 3} more of the same kind)`] } } : {}),
      search_hits: c.search_hits.map((h) => ({ name: h.name, library: h.library, statement: h.statement.slice(0, 120) })),
    };
    if (!c.helper_of?.length) return rest;
    const { docstring: _doc, ...context } = c.context;
    const { search_hits: _h, ...lean } = rest;
    return { ...lean, context, statement: c.statement.slice(0, 200) };
  });
}

/** Existing toolkit modules (staging excluded): relative path and the overview's first line. */
export async function listToolkitModules(cfg: ToolkitConfig): Promise<Array<{ path: string; overview: string }>> {
  const out: Array<{ path: string; overview: string }> = [];
  const walk = async (dir: string): Promise<void> => {
    const entries = await readdir(dir, { withFileTypes: true }).catch(() => []);
    for (const e of entries.sort((a, b) => a.name.localeCompare(b.name))) {
      const abs = path.join(dir, e.name);
      if (e.isDirectory()) {
        if (abs !== cfg.stagingDir) await walk(abs);
      } else if (e.isFile() && e.name.endsWith(".lean") && out.length < MAX_MODULES) {
        const text = await readFile(abs, "utf8").catch(() => "");
        const doc = text.match(/\/-!([\s\S]*?)-\//)?.[1] ?? "";
        const first = doc.split("\n").map((l) => l.replace(/^#+\s*/, "").trim()).find((l) => l !== "") ?? "";
        out.push({ path: path.relative(cfg.toolkitRoot, abs).split(path.sep).join("/"), overview: first });
      }
    }
  };
  await walk(cfg.toolkitLibDir);
  return out;
}

/** The owner's earlier proposal decisions (dry-run records excluded), compacted for the prompt. */
export async function decisionHistory(cfg: ToolkitConfig): Promise<string[]> {
  const ledger = await loadLedger(cfg.ledgerPath);
  return ledger.decisions
    .map((d) => proposalDecisionRecordSchema.safeParse(d))
    .filter((r) => r.success && !r.data.dry_run)
    .map((r) => {
      const d = r.data!;
      const statement = String(d.proposal.content ?? d.proposal.general_statement ?? "").replace(/\s+/g, " ").slice(0, HISTORY_TEXT);
      return `- ${d.decision.kind}${d.promoted ? " (in the toolkit)" : ""}: ${d.proposal.proposed_name} [${d.slug}] ${statement}${d.decision.note ? ` — note: ${d.decision.note.replace(/\s+/g, " ").slice(0, HISTORY_TEXT)}` : ""}`;
    })
    .slice(-MAX_HISTORY);
}

// ─── reply contract ────────────────────────────────────────────────────────

/** One curator item, as the reply schema constrains it. */
export interface CuratorItem {
  candidate_id: string;
  verdict: "propose" | "skip";
  title: string;
  reference: string;
  content: string;
  /** How the paper's own result relates to `content`, or "". */
  relation_to_paper: string;
  division: string;
  /** One line: why this division and topic — the bar the entry meets. */
  division_reason: string;
  qualifies_by: (typeof QUALIFIES_BY)[number];
  target_module: string;
  new_module_overview: string | null;
  /** A topic the target needs that the tree lacks, or null. */
  new_topic: NewTopic | null;
  proposed_name: string;
  nearest_existing: NearestExisting[];
  reuse_evidence: string;
  path: "move" | "generalize";
  /** `<slug>::<name>` of each pattern / similar recurrence the curator confirms is the same result. */
  recurrence_confirmed: string[];
}

const STR = { type: "string" } as const;
export const CURATOR_REPLY: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: ["items"],
  properties: {
    items: {
      type: "array",
      items: {
        type: "object",
        additionalProperties: false,
        required: ["candidate_id", "verdict", "title", "reference", "content", "relation_to_paper", "division", "division_reason", "qualifies_by",
          "target_module", "new_module_overview", "new_topic", "proposed_name", "nearest_existing", "reuse_evidence", "path",
          "recurrence_confirmed"],
        properties: {
          candidate_id: STR,
          verdict: { type: "string", enum: ["propose", "skip"] },
          title: STR,
          reference: STR,
          content: STR,
          relation_to_paper: STR,
          division: STR,
          division_reason: STR,
          qualifies_by: { type: "string", enum: [...QUALIFIES_BY] },
          target_module: STR,
          new_module_overview: { type: ["string", "null"] },
          new_topic: {
            anyOf: [
              { type: "null" },
              { type: "object", additionalProperties: false, required: ["path", "scope"], properties: { path: STR, scope: STR } },
            ],
          },
          proposed_name: STR,
          nearest_existing: {
            type: "array",
            items: {
              type: "object",
              additionalProperties: false,
              required: ["name", "library", "why_not_same"],
              properties: { name: STR, library: STR, why_not_same: STR },
            },
          },
          reuse_evidence: STR,
          path: { type: "string", enum: ["move", "generalize"] },
          recurrence_confirmed: { type: "array", items: STR },
        },
      },
    },
  },
};

const LEAN_NAME_RE = /^[A-Za-z_][A-Za-z0-9_'!?]*(\.[A-Za-z_][A-Za-z0-9_'!?]*)*$/;

/** Every declaration the indexes the toolkit names know (base libraries and the toolkit): name → kind. */
export async function indexNameTable(cfg: ToolkitConfig): Promise<Map<string, string>> {
  const out = new Map<string, string>();
  for (const src of indexSourcesFromToolkit(cfg)) {
    const idx = JSON.parse(await readFile(src.indexPath, "utf8")) as { entries?: Array<{ name?: string; kind?: string }> };
    for (const e of idx.entries ?? []) if (e.name) out.set(e.name, e.kind ?? "");
  }
  return out;
}

const TYPE_KINDS = new Set(["structure", "class", "inductive", "def", "abbrev", "opaque"]);

/**
 * What is wrong with `name` as a toolkit declaration name (empty = nothing): it is already declared
 * in a base library or the toolkit; or it is `X.foo` where `X` is not a declaration but names a type
 * declared inside a namespace (`IndepFun.foo` for `ProbabilityTheory.IndepFun`) — a result about a
 * type lives in that type's full namespace, so dot notation works (`ProbabilityTheory.IndepFun.foo`).
 */
export function nameProblems(name: string, table: ReadonlyMap<string, string>): string[] {
  const out: string[] = [];
  if (table.has(name)) out.push(`\`${name}\` is already declared in a base library or the toolkit`);
  const dot = name.lastIndexOf(".");
  if (dot > 0) {
    const head = name.slice(0, dot);
    if (!table.has(head)) {
      const full = [...table].filter(([n, k]) => TYPE_KINDS.has(k) && n.endsWith(`.${head}`)).map(([n]) => n);
      if (full.length === 1) out.push(`\`${head}\` is \`${full[0]}\`: name it \`${full[0]}${name.slice(dot)}\` (a result about a type lives in the type's namespace)`);
    }
  }
  return out;
}
/** TeX in a text the owner reads (`$…$`, `\command`): the checklist states mathematics in Unicode. */
export const TEX_RE = /\$|\\[A-Za-z]+/;

/** Structural problems of a curator reply (empty = acceptable). `names`: the declarations the
 *  indexes know (`indexNameTable`), for the naming checks; `taxonomy`: the topic tree. */
export function curatorViolations(
  items: readonly CuratorItem[],
  candidates: readonly ProposalCandidate[],
  cfg: ToolkitConfig,
  names?: ReadonlyMap<string, string>,
  taxonomy?: Taxonomy,
  opts: { /** An index round: a candidate the reply does not name is set aside. */ partial?: boolean } = {},
): string[] {
  const v: string[] = [];
  const ids = new Set(candidates.map((c) => c.candidate_id));
  const byId = new Map(candidates.map((c) => [c.candidate_id, c] as const));
  const seen = new Set<string>();
  const topics = new Set((taxonomy?.topics ?? []).map((t) => t.path));
  for (const it of items) {
    const at = `item ${it.candidate_id}`;
    if (!ids.has(it.candidate_id)) v.push(`${at}: not a candidate id.`);
    if (seen.has(it.candidate_id)) v.push(`${at}: judged twice.`);
    seen.add(it.candidate_id);
    const recKeys = new Set((byId.get(it.candidate_id)?.recurrence ?? []).filter((r) => r.kind !== "identical").map((r) => `${r.slug}::${r.name}`));
    for (const k of it.recurrence_confirmed ?? []) if (!recKeys.has(k)) v.push(`${at}: recurrence_confirmed names "${k}", which is not one of its pattern / similar matches.`);
    if (it.verdict === "skip") {
      if (it.reuse_evidence.trim() === "") v.push(`${at}: a skip states its reason in reuse_evidence.`);
      continue;
    }
    if (!cfg.divisions.includes(it.division)) v.push(`${at}: division "${it.division}" is not one of ${cfg.divisions.join(", ")}.`);
    const mod = it.target_module;
    const segs = mod.replace(/\.lean$/, "").split("/");
    if (!mod.endsWith(".lean") || segs.length < 4 || segs[0] !== cfg.lib || segs[1] !== it.division || segs.some((s) => !/^[A-Z][A-Za-z0-9]*$/.test(s))) {
      v.push(`${at}: target_module "${mod}" must be ${cfg.lib}/${it.division}/<topic path>/<File>.lean (UpperCamelCase segments).`);
    } else {
      if (!existsSync(path.join(cfg.toolkitRoot, mod)) && !(it.new_module_overview ?? "").trim()) {
        v.push(`${at}: target_module ${mod} does not exist yet, so new_module_overview is required.`);
      }
      const topic = topicOfModulePath(mod, cfg);
      if (taxonomy && topic !== null && !topics.has(topic)) {
        if (!it.new_topic || it.new_topic.path !== topic) {
          v.push(`${at}: "${topic}" is not a topic of the tree — choose a listed topic, or set new_topic {path: "${topic}", scope} for the owner to decide.`);
        } else {
          const why = newTopicProblem(it.new_topic.path, taxonomy);
          if (why) v.push(`${at}: ${why}.`);
          if (!it.new_topic.scope.trim()) v.push(`${at}: new_topic needs a one-line scope.`);
        }
      } else if (it.new_topic) {
        v.push(`${at}: new_topic is set but target_module already sits under a topic of the tree; set it to null.`);
      }
    }
    if (segs.some((s) => runTokenIn(s) !== null)) v.push(`${at}: target_module contains a run token.`);
    if (!LEAN_NAME_RE.test(it.proposed_name)) v.push(`${at}: proposed_name "${it.proposed_name}" is not a Lean identifier.`);
    else {
      const tok = it.proposed_name.split(".").map((c) => runTokenIn(c)).find((t) => t !== null);
      if (tok) v.push(`${at}: proposed_name ${tok}.`);
      if (names) for (const n of nameProblems(it.proposed_name, names)) v.push(`${at}: proposed_name — ${n}.`);
    }
    for (const key of ["title", "reference", "content", "reuse_evidence", "division_reason"] as const) {
      if (it[key].trim() === "") v.push(`${at}: ${key} is empty.`);
      else if (TEX_RE.test(it[key])) v.push(`${at}: ${key} contains TeX — write the mathematics in Unicode (∑, ≤, ∈, x², …), no $ or backslash commands.`);
    }
    if (it.nearest_existing.length === 0) v.push(`${at}: name the nearest existing declaration and why it differs.`);
  }
  if (!opts.partial) {
    for (const id of ids) if (!seen.has(id)) v.push(`candidate ${id} was not judged.`);
  } else {
    const proposed = items.filter((it) => it.verdict === "propose").length;
    if (proposed > MAX_INDEX_PROPOSALS) v.push(`${proposed} items proposed; an index round proposes at most ${MAX_INDEX_PROPOSALS} — keep the strongest.`);
  }
  return v;
}

/** The item of a candidate an index round's curator did not select. */
export function unselectedItem(candidate_id: string): CuratorItem {
  return {
    candidate_id, verdict: "skip", title: "", reference: "", content: "", relation_to_paper: "", division: "", division_reason: "",
    qualifies_by: QUALIFIES_BY[0], target_module: "", new_module_overview: null, new_topic: null, proposed_name: "", nearest_existing: [],
    reuse_evidence: "not selected: the curator chose the paper's main reusable results from its index", path: "move", recurrence_confirmed: [],
  };
}

/** The item of a candidate the index's size cap left out (the curator never saw it). */
export function unshownItem(candidate_id: string): CuratorItem {
  return { ...unselectedItem(candidate_id), reuse_evidence: "not shown: the paper's index exceeded its size cap and this candidate ranked below the ones shown" };
}

// ─── dispatch ──────────────────────────────────────────────────────────────

/** Resolve and record a prompt; in dry-run, say so the way the other dry-run agents do. */
export async function recordPrompt(cfg: ToolkitConfig, slug: string, name: string, prompt: string, dryRun: boolean, log: (m: string) => void, model: string = MODELS.codexKernel): Promise<string> {
  const dir = dryRun ? path.join(proposalsRunDir(cfg, slug), "dry_run_prompts") : path.join(proposalsRunDir(cfg, slug), "prompts");
  await mkdir(dir, { recursive: true });
  const file = path.join(dir, `${name}.txt`);
  await writeFile(file, prompt, "utf8");
  const bytes = Buffer.byteLength(prompt);
  if (dryRun) console.log(`[dry-run] ${name}: prompt resolved (${bytes} bytes) → ${file}`);
  else log(`${name}: dispatching ${model}, prompt ${bytes} bytes → ${file}`);
  return file;
}

export async function readProposalPrompt(name: "curator.txt" | "checker.txt" | "round_a.txt" | "round_b.txt" | "gardener.txt"): Promise<string> {
  const p = path.join(PROMPT_DIR, name);
  const text = await readFile(p, "utf8");
  if (text.trim() === "") throw new Error(`proposal prompt ${p} is empty`);
  // The curator writes `content`, which opens the built entry's docstring: it states the contract.
  return name === "curator.txt" ? `${text.trimEnd()}\n\n${docstringContract()}\n` : text;
}

export function section(title: string, body: string): string {
  return `=== ${title} ===\n${body}\n=== END ${title} ===`;
}

/** One schema-constrained model call: prompt + schema → the reply text (a JSON object). */
export interface JsonAsker {
  model: string;
  ask: (prompt: string, schema: Record<string, unknown>) => Promise<string>;
}

/** Codex (`MODELS.codexKernel`, high effort, read-only, no tools beyond reading). */
export function codexAsker(cfg: ToolkitConfig, runCodex: typeof RunCodex): JsonAsker {
  return {
    model: `${MODELS.codexKernel} (high)`,
    ask: async (prompt, schema) => (await runCodex({
      prompt, cwd: cfg.toolkitRoot, model: MODELS.codexKernel, reasoningEffort: "high",
      leanLsp: false, sandboxMode: "read-only", outputSchema: schema,
    })).stdout,
  };
}

/** Where a Claude call's token record goes: the run's ledger (`token_usage.jsonl`) under `stage`. */
export interface TokenLedger { runDir: string; stage: string }

/**
 * A Claude runner that writes one ledger record per call — the record `withTokenLedger`
 * (`token_usage.ts`) writes for a Codex call, under the runner and model the role really ran on
 * (`claude_roles.ts`). Telemetry is best-effort: it never changes the call's outcome.
 */
export function withClaudeTokenLedger(run: (o: ClaudeRunInput) => Promise<string>, ledger: TokenLedger): (o: ClaudeRunInput) => Promise<string> {
  return async (input) => {
    const started = Date.now();
    let usage: ModelTokenUsage | null = null;
    const record = (success: boolean) =>
      appendTokenUsageRecord(ledger.runDir, {
        timestamp: new Date().toISOString(), provider: claudeRoles().runner, model: claudeRoleModel(input.model), stage: ledger.stage,
        duration_ms: Date.now() - started, success, usage,
      }).catch((err) => markTokenUsageIncomplete(ledger.runDir, String(err)).catch(() => {}));
    try {
      // Summed: on codex the runner reports each transient-retry attempt, and each was paid for.
      const out = await run({ ...input, onUsage: (u) => { usage = addTokenUsage(usage, u); input.onUsage?.(u); } });
      await record(true);
      return out;
    } catch (err) {
      await record(false);
      throw err;
    }
  };
}

/** Claude (`MODELS.claudeMain`) with the JSON schema, read-only tools, no subagents or web; each
 *  call recorded in `ledger` when one is given. Run by codex when the claude roles are (`claude_roles.ts`). */
export function claudeAsker(cfg: ToolkitConfig, runClaude?: (o: ClaudeRunInput) => Promise<string>, ledger?: TokenLedger): JsonAsker {
  return {
    model: claudeRoleModel(MODELS.claudeMain),
    ask: async (prompt, schema) => {
      const worker = runClaude ?? (await import("../workers/claude.js")).runClaude;
      const run = ledger ? withClaudeTokenLedger(worker, ledger) : worker;
      return run({
        prompt, model: MODELS.claudeMain, cwd: cfg.toolkitRoot, jsonSchema: schema,
        allowedTools: ["Read", "Grep", "Glob"], allowSubagents: false, webSearch: false, leanLsp: false,
      });
    },
  };
}

/** One schema-constrained call with one contract retry. */
export async function askJson<T>(args: {
  cfg: ToolkitConfig; slug: string; name: string; prompt: string; schema: Record<string, unknown>;
  asker: JsonAsker; log: (m: string) => void; violations: (reply: T) => string[];
}): Promise<T> {
  const runDir = proposalsRunDir(args.cfg, args.slug);
  let prompt = args.prompt;
  for (let attempt = 1; attempt <= 2; attempt += 1) {
    await recordPrompt(args.cfg, args.slug, attempt === 1 ? args.name : `${args.name}.retry`, prompt, false, args.log, args.asker.model);
    const stdout = await args.asker.ask(prompt, args.schema);
    await persistCodexRaw(runDir, `${args.name}_${attempt}`, stdout);
    const reply = expectStringJsonOutput(stdout) as T;
    const v = args.violations(reply);
    if (v.length === 0) return reply;
    args.log(`${args.name}: reply broke the contract (${v.length}): ${v.join(" ")}`);
    if (attempt === 2) throw new Error(`${args.name} broke the output contract twice: ${v.join(" ")}`);
    prompt = [args.prompt, section("CONTRACT VIOLATIONS IN YOUR PREVIOUS REPLY", `Fix every point and emit the full corrected JSON:\n${v.map((x) => `- ${x}`).join("\n")}`)].join("\n\n");
  }
  throw new Error("unreachable");
}

function snake(s: string): string {
  return s.replace(/[^A-Za-z0-9]+/g, "_").replace(/^_+|_+$/g, "").toLowerCase() || "item";
}
function pascal(s: string): string {
  return s.split(/[^A-Za-z0-9]+/).filter(Boolean).map((p) => p[0]!.toUpperCase() + p.slice(1)).join("") || "Item";
}

/** Dry-run curator: every candidate proposed into the first division with a stub entry, under the
 *  first topic of the tree. */
export function syntheticCuratorItems(cfg: ToolkitConfig, grounded: readonly GroundedCandidate[], taxonomy?: Taxonomy): CuratorItem[] {
  const division = cfg.divisions[0]!;
  const topic = taxonomy?.topics[0]?.path ?? "DryRun";
  return grounded.map((c) => {
    const words = c.search_words ?? c.candidate_id;
    const hit = c.search_hits[0];
    return {
      candidate_id: c.candidate_id,
      verdict: "propose",
      title: `[dry-run] ${words}`,
      reference: "[dry-run] no curator was called",
      content: `[dry-run] ${c.statement.split("\n")[0]}`,
      relation_to_paper: "",
      division,
      division_reason: "[dry-run] first division",
      qualifies_by: "judgement",
      target_module: `${cfg.lib}/${division}/${topic}/${pascal(words)}.lean`,
      new_module_overview: "[dry-run] stub module",
      new_topic: null,
      proposed_name: snake(words),
      nearest_existing: [hit
        ? { name: hit.name, library: hit.library, why_not_same: "[dry-run] top search hit, not judged" }
        : { name: "(none found)", library: "-", why_not_same: "[dry-run] the search returned nothing" }],
      reuse_evidence: "[dry-run] synthetic proposal; no curator was called.",
      path: c.paper_shaped?.length || c.dropped_hypotheses?.length || c.source.kind === "cited" ? "generalize" : "move",
      recurrence_confirmed: [],
    };
  });
}

/** The curator prompt (exported to measure its size). */
export async function curatorPrompt(args: {
  toolkit: ToolkitConfig; slug: string; round: ProposalRound; grounded: readonly GroundedCandidate[];
  taxonomy: Taxonomy;
  /** Round B: show the candidates as an index (`candidateIndex`); the curator returns only what it proposes. */
  index?: boolean;
}): Promise<string> {
  const cfg = args.toolkit;
  const [modules, history, rules, brief] = await Promise.all([
    listToolkitModules(cfg), decisionHistory(cfg), readProposalPrompt("curator.txt"),
    readProposalPrompt(args.round === "A" ? "round_a.txt" : "round_b.txt"),
  ]);
  const index = args.index ? candidateIndex(args.grounded) : null;
  return [
    rules,
    section("THIS ROUND", brief.trim().replaceAll("{{PREFIX}}", () => index?.prefix ?? "").replaceAll("{{MAX_PROPOSALS}}", () => String(MAX_INDEX_PROPOSALS))),
    section("TOOLKIT", JSON.stringify({
      lib: cfg.lib, divisions: cfg.divisions,
      base_libraries: cfg.baseLibraries.map((b) => (b.summary ? `${b.name}: ${b.summary}` : b.name)),
    }, null, 2)),
    section("TOPIC TREE (doc/taxonomy.json)", taxonomyPromptText(args.taxonomy)),
    section("EXISTING TOOLKIT MODULES", modules.length ? modules.map((m) => `- ${m.path}: ${m.overview}`).join("\n") : "(none yet)"),
    section("OWNER DECISION HISTORY (ledger)", history.length ? history.join("\n") : "(no earlier decisions)"),
    index
      ? section(`CANDIDATE INDEX (paper ${args.slug}; ${args.grounded.length} candidates${index.cut.length ? `, ${index.cut.length} not shown` : ""}, by Lean file)`, index.text)
      : section(`CANDIDATES (paper ${args.slug}; one JSON object per line)`, promptCandidates(args.grounded).map((c) => JSON.stringify(c)).join("\n")),
  ].join("\n\n");
}

/** Characters of a statement an index line shows. */
const INDEX_STATEMENT = 110;
/** Bytes of index the curator is shown at most: beyond it the lowest-ranked candidates are cut. */
export const INDEX_BYTES = 120_000;

/** How much the scan says for a candidate: recurrence in other papers first, then an earlier
 *  deferral, then how many proofs use it. A cap on the index keeps the highest. */
function indexRank(c: ProposalCandidate): number {
  const papers = new Set((c.recurrence ?? []).filter((r) => r.kind !== "similar").map((r) => r.slug)).size;
  return papers * 100 + (c.deferred_before?.length ? 50 : 0) + Math.min(c.helper_of?.length ?? 0, 49);
}

/** The longest dotted prefix every name shares (`Papers.Foo.`), or "". */
function commonPrefix(names: readonly string[]): string {
  if (names.length === 0) return "";
  const parts = names[0]!.split(".").slice(0, -1);
  let n = parts.length;
  for (const name of names) {
    const q = name.split(".");
    let k = 0;
    while (k < n && k < q.length - 1 && q[k] === parts[k]) k += 1;
    n = k;
  }
  return n === 0 ? "" : `${parts.slice(0, n).join(".")}.`;
}

/**
 * Round B's candidates as an INDEX: grouped
 * by the Lean file that proves them, one line each — the name (without `prefix`), what the scan
 * knows (Foundations/Tricks-shaped, how many candidates' proofs use it, the other papers it recurs
 * in, whether its Lean is tied to the paper or carries unused hypotheses) and the start of its
 * statement. The curator reads the Lean of the ones it considers. Within `cap` bytes: past it the
 * lowest-ranked candidates (`indexRank`) are left out, `cut` names them and the text says how many.
 * Pure.
 */
export function candidateIndex(candidates: readonly ProposalCandidate[], cap = INDEX_BYTES): { prefix: string; text: string; cut: string[] } {
  const prefix = commonPrefix(candidates.map((c) => c.candidate_id));
  const byFile = new Map<string, string[]>();
  const cut: string[] = [];
  let used = 0;
  // ranked best first for the cap; the lines keep candidate order within each file
  const ranked = candidates.map((c, i) => ({ c, i })).sort((a, b) => indexRank(b.c) - indexRank(a.c) || a.i - b.i);
  const kept = new Set<number>();
  for (const { c, i } of ranked) {
    const line = indexLine(c, prefix);
    if (used + line.length > cap) { cut.push(c.candidate_id); continue; }
    used += line.length;
    kept.add(i);
  }
  for (const [i, c] of candidates.entries()) {
    if (!kept.has(i)) continue;
    const module = typeof c.context.module === "string" ? c.context.module : "";
    const file = module ? `${module.replace(/\./g, "/")}.lean` : "(module unknown)";
    byFile.set(file, [...(byFile.get(file) ?? []), indexLine(c, prefix)]);
  }
  const tail = cut.length ? [`${cut.length} candidate(s) not shown: the index is capped at ${cap} bytes, and the ones shown rank highest by recurrence, earlier deferral and use.`] : [];
  return { prefix, text: [...[...byFile].map(([file, lines]) => `## ${file}\n${lines.join("\n")}`), ...tail].join("\n\n"), cut };
}

/** One index line of a candidate. */
function indexLine(c: ProposalCandidate, prefix: string): string {
  // a lexically `similar` statement is no evidence of recurrence (most declarations have one)
  const papers = [...new Set((c.recurrence ?? []).filter((r) => r.kind !== "similar").map((r) => r.slug))];
  const flags = [
    c.division_signal === "Tricks" ? "T" : c.division_signal === "Foundations" ? "F" : "",
    c.helper_of?.length ? `used by ${c.helper_of.length}` : "",
    papers.length ? `recurs: ${papers.join(", ")}` : "",
    c.deferred_before?.length ? "deferred before" : "",
    c.paper_shaped?.length ? "paper-shaped" : "",
    c.dropped_hypotheses?.length ? `unused: ${c.dropped_hypotheses.join(", ")}` : "",
    c.source.is_paper_result ? "stated in the paper" : "",
  ].filter(Boolean).join("; ");
  // the statement is a docstring's first paragraph: without its binder links and node tag
  const statement = c.statement.replace(/\[([^\]]*)\]\((?:hyp:[^)]*|goal)\)/g, "$1").replace(/\s*@node:.*$/s, "").replace(/\s+/g, " ").trim();
  return `- ${c.candidate_id.slice(prefix.length)} [${flags}] ${statement.length > INDEX_STATEMENT ? `${statement.slice(0, INDEX_STATEMENT)}…` : statement}`;
}

/** Run the curator over the candidates. Returns one proposal per candidate, in candidate order,
 *  ids `<round>-<slug of the source>` (`assignProposalIds`). */
export async function runCurator(args: CuratorArgs): Promise<Proposal[]> {
  const { toolkit: cfg, slug } = args;
  const round = args.round ?? "B";
  const taxonomy = args.taxonomy ?? (await effectiveTaxonomy(cfg));
  // Round B is curated from an index of the paper's declarations: the curator reads the Lean it
  // considers (and searches the libraries itself) and returns only what it proposes; the rest are
  // set aside. Round A's few cited results are shown in full, each with its search hits.
  const indexed = round === "B";
  const grounded = indexed ? args.candidates.map((c) => ({ ...c, search_hits: [] })) : groundCandidates(cfg, args.candidates);
  const name = round === "A" ? "curator_a" : "curator";
  const prompt = await curatorPrompt({ toolkit: cfg, slug, round, grounded, taxonomy, ...(indexed ? { index: true } : {}) });
  let items: CuratorItem[];
  if (args.dryRun) {
    await recordPrompt(cfg, slug, name, prompt, true, args.log, claudeRoleModel(MODELS.claudeMain));
    items = syntheticCuratorItems(cfg, grounded, taxonomy);
  } else {
    const names = await indexNameTable(cfg);
    const prefix = indexed ? candidateIndex(grounded).prefix : "";
    // an index line shows a name without the paper's prefix: read a reply's id either way
    const known = new Set(args.candidates.map((c) => c.candidate_id));
    const full = (r: { items: CuratorItem[] }): CuratorItem[] => (r.items ?? []).map((it) => (!known.has(it.candidate_id) && known.has(prefix + it.candidate_id) ? { ...it, candidate_id: prefix + it.candidate_id } : it));
    // the call is recorded in the run's token ledger as the checker's codex call is (`withTokenLedger`)
    const ledger = { runDir: path.join(cfg.runsDir, slug), stage: round === "A" ? "promotion A" : "promotion B" };
    const reply = await askJson<{ items: CuratorItem[] }>({
      cfg, slug, name, prompt, schema: CURATOR_REPLY, asker: claudeAsker(cfg, args.runClaude, ledger), log: args.log,
      violations: (r) => curatorViolations(full(r), args.candidates, cfg, names, taxonomy, { partial: indexed }),
    });
    items = full(reply);
  }
  if (indexed) {
    const named = new Set(items.map((it) => it.candidate_id));
    const cut = new Set(candidateIndex(grounded).cut);
    if (cut.size) args.log(`${name}: ${cut.size} candidate(s) not shown to the curator (index capped at ${INDEX_BYTES} bytes)`);
    items = [...items, ...args.candidates.filter((c) => !named.has(c.candidate_id)).map((c) => (cut.has(c.candidate_id) ? unshownItem(c.candidate_id) : unselectedItem(c.candidate_id)))];
  }
  const byId = new Map(items.map((it) => [it.candidate_id, it] as const));
  const ids = assignProposalIds(args.candidates.map((c) => c.id_ref ?? c.source.ref), round);
  return args.candidates.map((c, i): Proposal => {
    const it = byId.get(c.candidate_id)!;
    const propose = it.verdict === "propose";
    // A cited result is always built; a paper-shaped result, or one carrying hypotheses its proof
    // never uses, never moves as is.
    const path_ = round === "A" || (c.paper_shaped?.length ?? 0) > 0 || (c.dropped_hypotheses?.length ?? 0) > 0 ? "generalize" : it.path;
    const confirmed = new Set(it.recurrence_confirmed ?? []);
    const recurrence = c.recurrence?.map((r) => (r.kind === "identical" ? r : { ...r, confirmed: confirmed.has(`${r.slug}::${r.name}`) }));
    return {
      id: ids[i]!,
      round,
      source: c.source,
      verdict: it.verdict,
      title: propose ? it.title : "",
      reference: propose ? it.reference : "",
      content: propose ? it.content : "",
      ...(propose && it.relation_to_paper?.trim() ? { relation_to_paper: it.relation_to_paper.trim() } : {}),
      division: propose ? it.division : "",
      target_module: propose ? it.target_module : "",
      new_module_overview: propose && !existsSync(path.join(cfg.toolkitRoot, it.target_module)) ? (it.new_module_overview ?? null) : null,
      proposed_name: propose ? it.proposed_name : "",
      nearest_existing: propose ? it.nearest_existing : [],
      reuse_evidence: it.reuse_evidence,
      ...(propose ? { division_reason: it.division_reason, qualifies_by: it.qualifies_by } : {}),
      ...(propose && it.new_topic ? { new_topic: it.new_topic } : {}),
      ...(c.division_signal ? { division_signal: c.division_signal } : {}),
      ...(c.dropped_hypotheses?.length ? { dropped_hypotheses: c.dropped_hypotheses } : {}),
      ...(c.deferred_before?.length ? { deferred_before: c.deferred_before } : {}),
      ...(c.moves_with ? { moves_with: c.moves_with } : {}),
      ...(c.lean_type ? { lean_type: c.lean_type } : {}),
      ...(recurrence ? { recurrence } : {}),
      ...(propose ? { path: path_ } : {}),
      ...(c.paper_shaped?.length ? { paper_shaped: c.paper_shaped } : {}),
      ...(c.source_text ? { source_text: c.source_text } : {}),
    };
  });
}
