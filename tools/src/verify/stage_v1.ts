/**
 * V1 — extract a typed core from the paper.
 *
 * Three steps, in order:
 *
 *   1. MECHANICAL. `buildEnvsJson` parses the source into `discovery/envs.json` +
 *      `discovery/flat.tex`; the SCOPE (which environments the core must cover) is computed
 *      from `--targets` by following `\ref` edges, or is every core-bearing environment
 *      when no target was given, and is written to `discovery/v1_scope.json`.
 *   2. ONE AGENT. A single codex call on the mechanical tier writes `discovery/core_refs.json`
 *      (the runner materializes `discovery/core.json` from it) and replies with a status JSON. It never proves anything: every statement
 *      it writes is `to-prove`.
 *   3. GATE LOOP. The core must pass `runStructuralGate` (well-formed) AND
 *      `lintTranscription` (faithful to the source, node by node, through `tex_locator`),
 *      run in phase `v1` — so the V1 agent cannot mint a `bookkeeping` assumption, which is
 *      V1.5's to add. Violations go back to the agent, at most three rounds, then the stage
 *      checkpoints for the operator. The lint's non-blocking WARNINGS — with one per published
 *      result a proof invokes by citation that no `cited` node registers (`inline_citations.ts`) —
 *      are written to `discovery/v1_lint_warnings.json` for the V1.5 referee to settle against
 *      the paper.
 *
 * When V1.5 sends the run back with `discovery/v1_revise_directive.json`, V1 starts from
 * the EXISTING core, hands the agent the must-fix findings, and deletes the directive once
 * a round passes.
 *
 * REWINDS REVISE, THEY NEVER REBUILD (user decision 2026-09-23). Every entry — the first, a
 * revise round, `--from-stage V1`, an F-stage rewind — picks its path with `v1EntryMode`: while
 * the source tree hashes as it did and `discovery/core_refs.json` exists, V1 materializes the
 * core from the reference core + the patch file, applies the directive's structured fixes itself,
 * and calls the agent only for what is left (scoped to those findings); a cold extraction happens
 * only when the source changed or there is no reference core.
 */
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { mkdir, readFile, rename, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { z } from "zod";
import { MODEL_PLAN } from "../constants.js";
import { runStructuralGate } from "../core/gate.js";
import { orderSymbolsByRefs } from "../core/symbol_order.js";
import { parseTypedCore } from "../core/core_io.js";
import { normalizeRawModelJson } from "../core/latex_serialization.js";
import { RefCoreSchema, accountsForCitations, anchorMatches, materializeRefCore, numberedSentences, type RefCore } from "./ref_core.js";
import type { Core } from "../core/schema.js";
import { expectStringJsonOutput, parseJsonWithEscapeRepair } from "../shared/codex_json.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { saveState } from "../state.js";
import { buildEnvsJson, recordedNoteMacros, writeEnvsArtifacts, type FlatTex } from "./tex_envs.js";
import { SegmentsSchema, V1_SEGMENTS_FILE, applySegments, flatRangeOf, numberedFlat, segmentationGaps, truncationGaps } from "./segments.js";
import { DriftFixSchema, applyDriftFixes, assertFixKeepsRefCoreValid, hasDriftFix } from "./directive_edits.js";
import { openFindingKind, recordVerifyFinding } from "./findings.js";
import { earlierFindingsBlock, readFixerHistory, withFindings, writeFixerHistory } from "./fixer_history.js";
import { NOTE_FIELDS_TEXT, nodeIdMentions, noteProblems, paperLabels, type PaperLabels } from "./owner_text.js";
import { consequenceViolations, findingNodes, isConsequential, setAsideSuggestionConsequences } from "./consequential.js";
import { hashSourceTree } from "./source_bundle.js";
import { statementBody, statementClosure } from "./core_graph.js";
import { carryOrphanedRecords } from "./orphan_records.js";
import { appendPipelineLog } from "../log.js";
import {
  PATCH_REPLY_JSON_SCHEMA,
  PatchFileSchema,
  materializeReply,
  applyPatchFile,
  applySuggestions,
  blockedUnfixable,
  findingPatch,
  isPendingSuggestion,
  isWithdrawn,
  normalizeTextlessEntries,
  openErrorIds,
  overlapViolations,
  onSplitParent,
  readPatchFile,
  readTranscribedCore,
  rebuildPatchedCore,
  snapshotTranscribedCore,
  validatePatchFile,
  type PatchFile,
} from "./patches.js";
import { convertWeakeningPatches, mainTheoremIds, pinOwnerEntries, settleSuggestions } from "./weakening.js";
import { MODELS } from "../models.js";
import { repairTextProblems, restatementProblems, resultEnvNames } from "./restatement.js";
import { patchFileTexFields, texFieldViolations } from "./tex_fragment_check.js";
import { PatchOpSchema, isProofOp, materializeRepair, nodePassage, noteUnitIds, supersededNodes, unitsBlock, type PassageSources, type PatchOp } from "./ops.js";
import { PaperUnits, flatLineStart, loadUnits } from "./units.js";
import { inlineCitationWarnings, inlineCitationsBlock, lintInlineCitations, type DismissedCitation } from "./inline_citations.js";
import {
  envBalanceProblems,
  isAlgorithmEnv,
  isCoreBearingEnv,
  lintTranscription,
  norm,
  sentenceSpans,
  STATEMENT_KIND_OF_ENV,
  THEOREM_LIKE_KINDS,
} from "./transcription_lint.js";
import {
  VERIFY_FILES,
  type EnvsJson,
  type TexEnv,
  type VerifyStage,
  type VerifyStageArgs,
  type VerifyStageResult,
} from "./types.js";
import { sha256File, writeCoreJson } from "./core_hash.js";

/** `discovery/v1_scope.json` — which environments the core must cover, and why. */
export const V1_SCOPE_FILE = VERIFY_FILES.v1Scope;

/**
 * `discovery/v1_lint_warnings.json` — `{ warnings: string[] }`, the transcription lint's
 * NON-BLOCKING observations. V1 writes it on every successful round (an empty array when
 * there is nothing to say); V1.5 reads it if present and settles each entry against the
 * paper. Nothing here ever fails a V1 round.
 */
import { V1_LINT_WARNINGS_FILE } from "./lint_warnings.js";
export { V1_LINT_WARNINGS_FILE };
/** The REFERENCE core the agent writes (see `ref_core.ts`); the runner materializes it into
 * `discovery/core.json`. */
export const V1_REFS_FILE = VERIFY_FILES.coreRefs;

/** The extraction prompt, next to this module. */
const PROMPT_FILE = path.join(
  path.dirname(fileURLToPath(import.meta.url)),
  "prompts",
  "V1",
  "extract_core.txt",
);

/** The segmentation prompt (the fallback when the parser reports gaps; see `segments.ts`). */
const SEGMENT_PROMPT_FILE = path.join(path.dirname(fileURLToPath(import.meta.url)), "prompts", "V1", "segment.txt");

/** The fixer prompt (V1 patch mode; see `patches.ts`). */
const PATCH_PROMPT_FILE = path.join(path.dirname(fileURLToPath(import.meta.url)), "prompts", "V1", "patch.txt");
/** Fixer rounds per patch invocation: one to write the file, one to fix its violations. */
export const MAX_PATCH_AGENT_ROUNDS = 2;
/** One more, when the violations fell between the two: a reply that answered most of what it was
 * sent and tripped on the rest (a third of the checkpoints read "not clean after 2 rounds" with one
 * or two violations left of many) is finished rather than handed to the orchestrator. */
export const MAX_PATCH_AGENT_ROUNDS_CONVERGING = MAX_PATCH_AGENT_ROUNDS + 1;

/** Whether fixer round `round` runs. `sent`: the number of violations the fixer was sent at each
 * round so far, this round's last (0 for a first round). Past `MAX_PATCH_AGENT_ROUNDS`, only the
 * converging round: fewer violations sent now than last time. Pure. */
export function fixerRoundAllowed(round: number, sent: readonly number[]): boolean {
  if (round <= MAX_PATCH_AGENT_ROUNDS) return true;
  if (round > MAX_PATCH_AGENT_ROUNDS_CONVERGING || sent.length < 2) return false;
  const [before, now] = [sent[sent.length - 2]!, sent[sent.length - 1]!];
  return now > 0 && now < before;
}

/** Agent rounds per V1 invocation before handing the core to the operator. */
export const MAX_V1_ROUNDS = 3;
/** Segmentation rounds: one to write the file, one to fix its violations. */
export const MAX_SEGMENT_ROUNDS = 2;

const ReplySchema = z.object({
  status: z.enum(["completed", "failed"]),
  message: z.string().nullish(),
});

/**
 * A worker's final message says it could not reach the run's files: its sandbox did not start, or
 * a read or a write was denied. That is the machine's, not the paper's — no retry can change it.
 */
export function workerAccessFailure(reply: string): boolean {
  return (
    /\b(sandbox|bwrap|bubblewrap)\b|permission denied|operation not permitted|read-only file ?system/i.test(reply) ||
    /\b(cannot|can't|can not|could not|couldn't|unable to|not able to|no way to)\s+(access|read|open|write|create|list|inspect)\b[^.\n]*\b(files?|file ?system|director(?:y|ies)|workspace|source|output|disk)\b/i.test(reply)
  );
}

/** The halt of a worker that could not reach the run's files (`workerAccessFailure`). */
function environmentCheckpoint(worker: string, reply: string): VerifyStageResult {
  let said = reply.trim();
  try {
    said = String((JSON.parse(said) as { message?: unknown }).message ?? said);
  } catch {
    /* not the status JSON: the text itself */
  }
  return {
    status: "checkpoint",
    message:
      `ENVIRONMENT checkpoint: the ${worker} (a model worker) could not read or write the run's files — it said: ` +
      `${said.split("\n")[0]!.slice(0, 300)}. This is the machine, not the paper: run \`leansmith doctor\` and settle what it ` +
      `reports (the workers' sandbox). Do not retry, and do not change the paper or --targets`,
  };
}

/** `codex exec --output-schema`: the reply is valid by construction, so no repair tier. */
const REPLY_OUTPUT_SCHEMA: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: ["status", "message"],
  properties: {
    status: { type: "string", enum: ["completed", "failed"] },
    message: { type: "string" },
  },
};

const ReviseDirectiveSchema = z.object({
  /** `transcribe`: drift for the transcriber (the default); `patch`: errors for the fixer. */
  mode: z.enum(["transcribe", "patch"]).default("transcribe"),
  round: z.number(),
  findings: z.array(
    z.object({
      id: z.string(),
      axis: z.string(),
      detail: z.string(),
      fix: DriftFixSchema.nullable().optional(),
      witness: z.string().nullable().optional(),
      /** Set on a finding an F-stage rewind wrote (`cross_stage_rewind.ts`): the F stage whose
       * reviewer found it. A `clarify` finding from an F stage is a clarification of the paper's
       * statement (ledger kind `clarification`); a V1.5 `clarify` asks for a proof step written out. */
      from_stage: z.string().optional(),
      /** The readings the referee pinned for the statement, which a clarifying patch writes into it. */
      folds: z.array(z.object({ node: z.string(), reading: z.string() })).optional(),
      /** An F-stage finding whose fixer rejection the referee overruled: it must be patched. */
      overruled: z.boolean().optional(),
      /** The referee found this node's repair holds but WEAKENS the paper's claim: the runner turns
       * the patch into a suggestion for the owner (`weakening.ts`); the fixer never sees it. */
      weakens_contribution: z.boolean().optional(),
      /** `--redo-repair "<node>: <guidance>"`: the paper's owner discarded this node's suggested
       * (weakened) repair and asks the fixer again, under this guidance (binding; `OWNER GUIDANCE`). */
      owner_guidance: z.string().optional(),
      /** The runner sent this node's repair back once (a patch on file or a pending suggested repair,
       * `restateAllPatches`): a text of it does not compile; these are the problems (`RESTATEMENT`
       * block). Not the owner's. */
      restatement: z.array(z.string()).optional(),
      /** A suggested repair the runner sent back (the referee did not confirm it, or a text of it does not
       * compile), as it stood: the new entry replaces it whole (`YOUR SUGGESTED REPAIR` block). */
      withdrawn_repair: z
        .object({
          corrected_statement: z.string().nullable(),
          ops: z.array(PatchOpSchema).optional(),
          drops: z.array(z.string()).optional(),
          adds: z.array(z.string()).optional(),
          readings: z.array(z.string()).optional(),
          supersedes: z.array(z.string()).optional(),
        })
        .optional(),
    }),
  ),
});
type ReviseDirective = z.infer<typeof ReviseDirectiveSchema>;

/** How V1 enters: `revise` the existing transcription, or extract it `cold`. */
export interface V1EntryMode {
  mode: "revise" | "cold";
  /** For the log: why this path. */
  why: string;
  /** The source tree's hash now. */
  sourceSha: string;
}

/**
 * The V1 entry rule. `revise` when the source tree hashes as recorded at seeding AND a reference
 * core exists (`core_refs.json`; a dry run, which writes no reference core, uses its
 * `core.transcribed.json`): the transcription is still a transcription of this paper, so it is
 * materialized, never re-extracted. `cold` when the source changed or nothing was transcribed.
 */
export async function v1EntryMode(runDir: string, recordedSha: string, dryRun: boolean): Promise<V1EntryMode> {
  const sourceSha = await hashSourceTree(path.join(runDir, VERIFY_FILES.sourceDir));
  const short = (h: string): string => h.slice(0, 12);
  if (sourceSha !== recordedSha) {
    return { mode: "cold", sourceSha, why: `the source changed (sha ${short(recordedSha)} → ${short(sourceSha)})` };
  }
  if (existsSync(path.join(runDir, V1_REFS_FILE))) {
    return { mode: "revise", sourceSha, why: `source unchanged (sha ${short(sourceSha)}) and ${V1_REFS_FILE} present` };
  }
  if (dryRun && existsSync(path.join(runDir, VERIFY_FILES.coreTranscribed))) {
    return { mode: "revise", sourceSha, why: `dry run: source unchanged (sha ${short(sourceSha)}) and ${VERIFY_FILES.coreTranscribed} present` };
  }
  return { mode: "cold", sourceSha, why: `no ${V1_REFS_FILE} to revise` };
}

/** Environments the core must cover, in document order.
 *
 * With no `--targets`, that is every core-bearing environment in the paper. With targets,
 * it is the `\ref` closure of the targets (refs are label strings, so only labelled
 * environments can be reached), restricted to the core-bearing ones. Throws when a target
 * names no environment — a silently empty scope would produce an empty core. */
export function computeScope(envs: EnvsJson, targets: readonly string[] | null): string[] {
  if (targets === null) return envs.envs.filter(isCoreBearingEnv).map((e) => e.id);

  const byHandle = new Map<string, TexEnv>();
  for (const env of envs.envs) {
    byHandle.set(env.id, env);
    if (env.label) byHandle.set(env.label, env);
  }
  const unknown = targets.filter((t) => !byHandle.has(t));
  if (unknown.length > 0) {
    throw new Error(
      `V1: --targets ${unknown.join(", ")} match no environment in the paper. ` +
        `Known ids/labels: ${[...byHandle.keys()].join(", ")}`,
    );
  }
  const byLabel = new Map(
    envs.envs.filter((e) => e.label !== null).map((e) => [e.label as string, e] as const),
  );
  const reached = new Set<string>();
  const stack = targets.map((t) => (byHandle.get(t) as TexEnv).id);
  while (stack.length > 0) {
    const id = stack.pop() as string;
    if (reached.has(id)) continue;
    reached.add(id);
    const env = byHandle.get(id);
    for (const ref of env?.refs ?? []) {
      const target = byLabel.get(ref);
      if (target) stack.push(target.id);
    }
  }
  return envs.envs.filter((e) => reached.has(e.id) && isCoreBearingEnv(e)).map((e) => e.id);
}

/** `thm:`/`lem:`/`prop:`/`ass:`/`def:` id body: `[a-z0-9-]+`, derived from the env handle
 * with any `label:`-style prefix dropped. `used` keeps ids unique. */
function slugFor(env: TexEnv, used: Set<string>): string {
  const tail = (env.label ?? env.id).split(":").pop() ?? env.id;
  const base =
    tail
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, "-")
      .replace(/^-+|-+$/g, "") || "env";
  let slug = base;
  for (let n = 2; used.has(slug); n += 1) slug = `${base}-${n}`;
  used.add(slug);
  return slug;
}


/**
 * The core the DRY RUN writes: one node per in-scope environment, transcribed verbatim, no
 * symbols, a placeholder estimand. It is deliberately run through the same gate + lint as
 * an agent core — the dry run is what proves the mechanical half of V1 without spending a
 * model call, so it must satisfy every transcription rule itself:
 *
 *   • an assumption environment becomes ONE node PER SENTENCE, not one node for its first
 *     sentence. One sentence per node keeps each condition atomic (G2), and taking every
 *     sentence is what covers the environment's text (rule (b)'s coverage floor);
 *   • a statement `depends_on` every node transcribed from every environment its own
 *     environment `\ref`s (rule (g), forward direction). Ids are therefore assigned in a
 *     first pass, so a forward reference resolves.
 */
export function minimalCore(qid: string, envs: EnvsJson, scope: readonly string[]): unknown {
  const byId = new Map(envs.envs.map((e) => [e.id, e] as const));
  const byLabel = new Map(
    envs.envs.filter((e) => e.label !== null).map((e) => [e.label as string, e] as const),
  );
  const used = new Set<string>();
  // Pass 1: the node ids each in-scope environment yields, keyed by env id.
  const idsOfEnv = new Map<string, string[]>();
  for (const id of scope) {
    const env = byId.get(id);
    if (!env) continue;
    if (THEOREM_LIKE_KINDS.has(env.kind)) {
      const kind = STATEMENT_KIND_OF_ENV[env.kind as keyof typeof STATEMENT_KIND_OF_ENV];
      const prefix = kind === "lemma" ? "lem" : kind === "proposition" ? "prop" : "thm";
      idsOfEnv.set(id, [`${prefix}:${slugFor(env, used)}`]);
    } else if (env.kind === "assumption") {
      idsOfEnv.set(
        id,
        sentenceSpans(norm(env.body)).map(() => `ass:${slugFor(env, used)}`),
      );
    } else if (env.kind === "definition" || isAlgorithmEnv(env)) {
      idsOfEnv.set(id, [`def:${slugFor(env, used)}`]);
    }
    // A `cited` other-env has no mechanical transcription (it needs a bibkey + locator the
    // parser cannot infer), so the dry run leaves it out; rules (a)–(c) do not cover it.
  }

  // Pass 2: the nodes themselves.
  const statements: unknown[] = [];
  const assumptions: unknown[] = [];
  const definitions: unknown[] = [];
  for (const id of scope) {
    const env = byId.get(id);
    const ids = env ? idsOfEnv.get(id) : undefined;
    if (!env || !ids) continue;
    if (THEOREM_LIKE_KINDS.has(env.kind)) {
      const kind = STATEMENT_KIND_OF_ENV[env.kind as keyof typeof STATEMENT_KIND_OF_ENV];
      const depends_on = [
        ...new Set(
          env.refs.flatMap((ref) => {
            const target = byLabel.get(ref);
            if (!target || target.id === env.id) return [];
            return idsOfEnv.get(target.id) ?? [];
          }),
        ),
      ];
      statements.push({
        id: ids[0],
        kind,
        statement: env.body,
        status: "to-prove",
        depends_on,
        tex_locator: env.lines,
        ...(env.proof !== null ? { proof_tex: env.proof } : {}),
      });
    } else if (env.kind === "assumption") {
      const body = norm(env.body);
      sentenceSpans(body).forEach((span, i) => {
        assumptions.push({
          id: ids[i],
          condition: body.slice(span.start, span.end).trim(),
          novel: { flag: true, justification: "dry run: mechanical transcription, unreviewed" },
          tex_locator: env.lines,
        });
      });
    } else if (env.kind === "definition" || isAlgorithmEnv(env)) {
      definitions.push({
        id: ids[0],
        name: env.title ?? env.id,
        construction: norm(env.body),
        tex_locator: env.lines,
      });
    }
  }
  return {
    qid,
    symbols: [],
    sampling_model: { "dry run": "No setting was transcribed (dry run: the runner wrote this core without the agent)." },
    assumptions,
    definitions,
    statements,
    target_estimand: "dry-run",
    bibliography: [],
  };
}

/** Materialize `discovery/core_refs.json` into `discovery/core.json`. Returns the
 * violations the agent must fix (file unreadable, schema, anchors that do not cut); on
 * success the core is written and the list is empty. */
export async function materializeRefs(
  refsPath: string,
  corePath: string,
  envs: EnvsJson,
  flat: FlatTex,
): Promise<string[]> {
  let raw: unknown;
  try {
    // The reference core is MODEL-typed JSON: its symbol names carry TeX (`$\varepsilon$`),
    // whose backslashes are not JSON escapes. The raw normalizer exists for exactly this.
    raw = JSON.parse(normalizeRawModelJson(await readFile(refsPath, "utf8")));
  } catch (err) {
    return [`(refs) ${refsPath} is not valid JSON: ${err instanceof Error ? err.message : String(err)}`];
  }
  const parsed = RefCoreSchema.safeParse(raw);
  if (!parsed.success) {
    return parsed.error.issues.map((i) => `(refs) ${i.path.join(".") || "(root)"}: ${i.message}`);
  }
  const { core, violations } = materializeRefCore(parsed.data, envs, flat.text);
  if (violations.length > 0) return violations;
  await writeCoreJson(corePath, core);
  return [];
}

/** The inline-citation warnings, never a reason for a round to fail: a detector fault yields none. */
function inlineCitations(...a: Parameters<typeof inlineCitationWarnings>): string[] {
  try {
    return inlineCitationWarnings(...a);
  } catch {
    return [];
  }
}

/**
 * How a V1 round treats the paper's inline citations: `{ dismissed, leaves }` when the reference core
 * must account for each (`strict`: the run extracted its core under the accounting,
 * `verify.citation_accounting`; or the reference core already accounts), null when it was written
 * before the accounting existed — its sites are then warnings, and the run is not made to change. No
 * reference core (a core written directly): null. `leaves`: the ids of its `proof_citations`.
 */
async function citationAccounting(refsPath: string, strict: boolean): Promise<{ dismissed: DismissedCitation[]; leaves: string[] } | null> {
  if (!existsSync(refsPath)) return null;
  let ref: RefCore;
  try {
    ref = RefCoreSchema.parse(JSON.parse(normalizeRawModelJson(await readFile(refsPath, "utf8"))));
  } catch {
    return null; // an unreadable reference core is `materializeRefs`'s to report
  }
  return strict || accountsForCitations(ref) ? { dismissed: ref.dismissed_citations ?? [], leaves: (ref.proof_citations ?? []).map((c) => c.id) } : null;
}


/** Read + canonicalize the core the agent left on disk, then check it.
 *
 * The symbol table is put in defined-before-use order here (`orderSymbolsByRefs`: the identity on
 * a table already in order), so the order the agent — or a hand edit of the reference core — lists
 * the symbols in is free.
 *
 * The bibliography is overwritten from the paper's own entries BEFORE the gate runs: G6
 * resolves `standard.cite` / `source.cite` against it, and the paper — not the agent — is
 * the authority on which keys exist. */
async function validateRound(
  corePath: string,
  envs: EnvsJson,
  scope: readonly string[],
  flat: FlatTex,
  accounting: { dismissed: DismissedCitation[] } | null = null,
): Promise<{ core: Core | null; violations: string[]; warnings: string[] }> {
  if (!existsSync(corePath)) {
    return { core: null, violations: [`(schema) no core was written at ${corePath}`], warnings: [] };
  }
  let core: Core;
  try {
    core = parseTypedCore(await readFile(corePath, "utf8"), `V1 core ${corePath}`);
  } catch (err) {
    const reason = err instanceof Error ? err.message : String(err);
    return {
      core: null,
      violations: [`(schema) ${corePath} is not a valid core: ${reason}`],
      warnings: [],
    };
  }
  core.bibliography = envs.bibliography.map((b) => ({ key: b.key, citation: b.text }));
  core.symbols = orderSymbolsByRefs(core.symbols);
  await writeCoreJson(corePath, core);
  const gate = runStructuralGate(core, { allowBookkeeping: true, verbatim: true });
  // Phase `v1`: a `bookkeeping` assumption here is the V1 agent minting one, not V1.5
  // supplying it. Only `violations` block; `warnings` go to the referee.
  const lint = lintTranscription(core, envs, scope, { phase: "v1", flatText: flat.text });
  // The results a proof invokes by citation (`inline_citations.ts`): accounted for one by one, each
  // dismissal a warning the referee may contest; on a reference core older than the accounting, a
  // warning per result with no `cited` node.
  const inline = accounting ? lintInlineCitations(core, envs, scope, accounting.dismissed) : { violations: [], warnings: inlineCitations(core, envs, scope) };
  return {
    core,
    violations: [
      ...gate.violations.map((v) => `(${v.code}) ${v.where}: ${v.message}`),
      ...lint.violations,
      ...inline.violations,
    ],
    warnings: [...lint.warnings, ...inline.warnings, ...(gate.notes ?? []).map((v) => `(${v.code}) ${v.where}: ${v.message}`)],
  };
}

/** Fill in the source lines of every `prose` locator: the lint has verified the node's text
 * is a verbatim (whitespace-insensitive) slice of the flattened paper, so locate that slice
 * in `flat.text` and map its lines back to the original file through the line map. Returns
 * how many locators were resolved. Exported for tests. */
export function resolveProseLocators(core: Core, flat: FlatTex): number {
  const lineStarts: number[] = [0];
  for (let i = 0; i < flat.text.length; i += 1) if (flat.text[i] === "\n") lineStarts.push(i + 1);
  const lineOf = (offset: number): number => {
    let lo = 0;
    let hi = lineStarts.length - 1;
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1;
      if (lineStarts[mid]! <= offset) lo = mid;
      else hi = mid - 1;
    }
    return lo; // 0-based flat line
  };
  let resolved = 0;
  const nodes: Array<{ text: string; loc: { file: string; from: number; to: number; env: string } }> = [
    ...core.assumptions.filter((a) => a.tex_locator?.env === "prose").map((a) => ({ text: a.condition, loc: a.tex_locator! })),
    ...core.definitions.filter((d) => d.tex_locator?.env === "prose").map((d) => ({ text: d.construction, loc: d.tex_locator! })),
  ];
  for (const { text, loc } of nodes) {
    const tokens = text.trim().split(/\s+/).filter((t) => t.length > 0);
    if (tokens.length === 0) continue;
    const re = new RegExp(tokens.map((t) => t.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join("\\s*"));
    const m = re.exec(flat.text);
    if (!m) continue; // the lint guarantees a match; leave the placeholder rather than guess
    const startLine = lineOf(m.index);
    const endLine = lineOf(m.index + m[0].length - 1);
    const start = flat.lineMap[startLine];
    const end = flat.lineMap[endLine];
    if (!start) continue;
    loc.file = start.file;
    loc.from = start.line;
    loc.to = end && end.file === start.file ? end.line : start.line;
    resolved += 1;
  }
  return resolved;
}

/** `discovery/v1_lint_warnings.json` — the V1.5 referee's non-blocking to-check list
 * (`warnings`, from the transcription lint) plus the tex parser's structural notes
 * (`parser_warnings`: a file folded once although included twice, a discarded second
 * proof, …). V6 prints both; V1.5 is told to confirm each. */
async function writeLintWarnings(
  runDir: string,
  warnings: readonly string[],
  parserWarnings: readonly string[],
): Promise<void> {
  await writeJsonAtomic(path.join(runDir, V1_LINT_WARNINGS_FILE), {
    warnings: [...warnings],
    parser_warnings: [...parserWarnings],
  });
}

function counts(core: Core): string {
  const cited = core.statements.filter((s) => s.status === "cited").length;
  return (
    `${core.statements.length - cited} statements, ${core.assumptions.length} assumptions, ` +
    `${core.definitions.length} definitions, ${cited} cited leaves, ${core.symbols.length} symbols`
  );
}

function buildPrompt(args: {
  base: string;
  qid: string;
  corePath: string;
  refsPath: string;
  envs: EnvsJson;
  scope: readonly string[];
  directive: ReviseDirective | null;
  violations: readonly string[];
  /** Whether the round accounts for the inline citations (`citationAccounting`). */
  citations: boolean;
  /** The ids of the reference core's `proof_citations`. */
  inlineLeaves: readonly string[];
}): string {
  const scopeIds = new Set(args.scope);
  // Each SCOPE entry carries its body as numbered sentences (not again as `body`) so a hypothesis can be
  // named by sentence number instead of copied; the paper itself is discovery/flat.tex in the agent's cwd,
  // where the proof of each environment is read (its locator `proofLines` stays; the proof's text — the
  // bulk of every environment — is not inlined: a proof slice is rare and its anchors are read there).
  const inScope = args.envs.envs
    .filter((e) => scopeIds.has(e.id))
    .map(({ body, proof: _p, ...e }) => ({ ...e, sentences: numberedSentences(body) }));
  const sites = args.citations ? inlineCitationsBlock(args.envs, args.scope) : [];
  const context = args.envs.envs.filter((e) => e.kind === "remark" || e.kind === "example").map(({ proof: _p, proofLines: _l, refs: _r, ...e }) => e);
  const blocks = [
    args.base.trimEnd(),
    "",
    "=== SCOPE — transcribe exactly these environments ===",
    JSON.stringify(inScope, null, 2),
    "",
    "=== CONTEXT — remarks and examples (notation only; never transcribe these into nodes) ===",
    JSON.stringify(context, null, 2),
    "",
    "=== BIBLIOGRAPHY — the only citable keys ===",
    args.envs.bibliography.map((b) => b.key).join(", "),
    "",
    ...(sites.length > 0 ? ["=== INLINE CITATIONS — account for each ===", ...sites, ""] : []),
    `FULL PAPER: ${VERIFY_FILES.flatTex} (the flattened source, in your working directory; read its setup / notation sections, each environment's proof, and search prose anchors in it)`,
    "",
    `QID: ${args.qid}`,
    `REFS_FILE: ${args.refsPath}`,
    `CORE_FILE: ${args.corePath}`,
  ];
  if (args.directive) {
    // Only a drift is about the account of a citation (an error on a leaf is its host's, `errorsOnHosts`).
    const onLeaves = [...new Set(args.directive.findings.filter((f) => f.axis === "faithfulness").map((f) => f.id).filter((id) => args.inlineLeaves.includes(id)))];
    blocks.push(
      "",
      `=== REVISE DIRECTIVE (round ${args.directive.round}) — every finding is must-fix ===`,
      "The reference core at REFS_FILE already exists. EDIT IT IN PLACE: fix these findings and leave",
      "every other node as it is. A finding about drift means the node does not say what its",
      "environment says — re-transcribe it, never argue with the referee.",
      ...(onLeaves.length > 0
        ? [
            `${onLeaves.join(", ")}: a \`proof_citations\` entry has no text to re-transcribe. A faithfulness finding on it is about your account of the citation: move its site to`,
            "`dismissed_citations` when the proof does not rely on the cited result, or change `units` when they leave out the citation or the step it gives (at most 3 consecutive units).",
          ]
        : []),
      JSON.stringify(args.directive.findings, null, 2),
    );
  }
  if (args.violations.length > 0) {
    blocks.push(
      "",
      "=== VIOLATIONS (must fix, edit REFS_FILE in place) ===",
      ...args.violations.map((v) => `- ${v}`),
    );
  }
  return blocks.join("\n");
}

/** The line-numbered source without the lines of `elided` ranges (1-based, inclusive): each run
 * stands as one marker naming what it is, so the numbering the segmenter points with is unchanged.
 * Pure. */
export function numberedFlatWithout(flat: FlatTex, elided: ReadonlyArray<{ range: [number, number]; what: string }>): string {
  const lines = numberedFlat(flat).split("\n");
  const out: string[] = [];
  const at = new Map(elided.map((e) => [e.range[0], e] as const));
  for (let i = 1; i <= lines.length; i += 1) {
    const e = at.get(i);
    if (e && e.range[1] >= i) {
      out.push(`     | [lines ${e.range[0]}–${e.range[1]}: ${e.what}; read them in ${VERIFY_FILES.flatTex}]`);
      i = e.range[1];
    } else out.push(lines[i - 1]!);
  }
  return out.join("\n");
}

function segmentPrompt(base: string, segPath: string, envs: EnvsJson, flat: FlatTex, gaps: readonly string[], violations: readonly string[]): string {
  const theoremLike = envs.envs.filter((e) => THEOREM_LIKE_KINDS.has(e.kind) || e.kind === "assumption" || e.kind === "definition");
  const parsed = theoremLike.map((e) => {
    const r = flatRangeOf(e.lines, flat);
    const p = e.proofLines ? flatRangeOf(e.proofLines, flat) : null;
    return `- ${e.id} (${e.kind}${e.title ? `, "${e.title}"` : ""}) lines ${r ? `${r[0]}–${r[1]}` : "?"}${p ? `; proof lines ${p[0]}–${p[1]}` : "; no proof attached"}`;
  });
  // A proof the parser already attached is no gap: its lines are elided (named by the PARSED block).
  const attached = theoremLike.flatMap((e) => {
    const p = e.proofLines ? flatRangeOf(e.proofLines, flat) : null;
    return p ? [{ range: p, what: `the proof of ${e.id}, already attached` }] : [];
  });
  const blocks = [
    base,
    "",
    `SEGMENTS_FILE: ${segPath}`,
    "",
    "=== GAPS (the parser's own report) ===",
    ...gaps.map((g) => `- ${g}`),
    "",
    "=== PARSED (already extracted; never re-declare) ===",
    ...parsed,
    "",
    `=== SOURCE (flat, line-numbered; a proof already attached is elided, its lines named; the whole file is ${VERIFY_FILES.flatTex} in your working directory) ===`,
    numberedFlatWithout(flat, attached),
  ];
  if (violations.length > 0) blocks.push("", "=== VIOLATIONS (must fix, edit SEGMENTS_FILE in place) ===", ...violations.map((v) => `- ${v}`));
  return blocks.join("\n");
}

/**
 * The segmentation fallback (see `segments.ts`). `applyExistingSegments` re-applies a
 * `segments.json` already on disk without an agent call (deterministic, so `--resume` never
 * pays twice). `runSegmenter` asks the agent to fill `gaps` — writing the file, or editing it
 * in place when it exists — with one revise round on violations; a file still not clean after
 * that is set aside (renamed) and the run continues on the parser's output. A segmenter that
 * wrote no file and says it could not reach the run's files is not asked again: `halt`. Both work
 * from the PARSED environments: the file is cumulative and is always applied to the parser's output.
 */
async function applySegmentsFile(
  segPath: string,
  parsedEnvs: EnvsJson,
  flat: FlatTex,
): Promise<{ envs: EnvsJson; violations: string[]; notes: string[] }> {
  const seg = SegmentsSchema.safeParse(JSON.parse(await readFile(segPath, "utf8")));
  if (!seg.success) {
    return { envs: parsedEnvs, violations: seg.error.issues.map((i) => `(segment) ${i.path.join(".")}: ${i.message}`), notes: [] };
  }
  return applySegments(seg.data, parsedEnvs, flat);
}

async function applyExistingSegments(
  args: VerifyStageArgs,
  parsedEnvs: EnvsJson,
  flat: FlatTex,
): Promise<{ envs: EnvsJson; notes: string[]; applied: boolean }> {
  const segPath = path.join(args.runDir, V1_SEGMENTS_FILE);
  if (!existsSync(segPath)) return { envs: parsedEnvs, notes: [], applied: false };
  const r = await applySegmentsFile(segPath, parsedEnvs, flat);
  if (r.violations.length === 0) {
    args.log(`segments: re-applied ${V1_SEGMENTS_FILE} (${r.notes.length} change(s))`);
    return { envs: r.envs, notes: r.notes, applied: true };
  }
  args.log(`segments: ${V1_SEGMENTS_FILE} on disk no longer applies (${r.violations[0]}); it will be rewritten`);
  return { envs: parsedEnvs, notes: [], applied: false };
}

async function runSegmenter(
  args: VerifyStageArgs,
  parsedEnvs: EnvsJson,
  currentEnvs: EnvsJson,
  flat: FlatTex,
  gaps: readonly string[],
): Promise<{ envs: EnvsJson; notes: string[]; changed: boolean; halt?: VerifyStageResult }> {
  const { runDir, log } = args;
  const segPath = path.join(runDir, V1_SEGMENTS_FILE);
  log(`segments: ${gaps.length} gap(s) — asking the segmenter${existsSync(segPath) ? " (editing the existing file)" : ""}`);
  const base = await readFile(SEGMENT_PROMPT_FILE, "utf8");
  await mkdir(path.join(runDir, "logs"), { recursive: true });
  let violations: string[] = [];
  const stamp = Date.now().toString(36);
  for (let round = 1; round <= MAX_SEGMENT_ROUNDS; round += 1) {
    const prompt = segmentPrompt(base, segPath, currentEnvs, flat, gaps, violations);
    const out = await args.deps.runCodex({
      prompt,
      cwd: runDir,
      sandboxMode: "workspace-write",
      model: MODEL_PLAN.mechanicalTier.model,
      reasoningEffort: MODEL_PLAN.mechanicalTier.effort,
      leanLsp: false,
      webSearch: false,
      outputSchema: REPLY_OUTPUT_SCHEMA,
    });
    await writeFile(
      path.join(runDir, "logs", `v1_segment_${stamp}_round${round}.json`),
      JSON.stringify({ prompt_bytes: Buffer.byteLength(prompt), prompt, stdout: out.stdout }, null, 2),
      "utf8",
    );
    if (!existsSync(segPath)) {
      violations = [`(segment) no file was written at ${V1_SEGMENTS_FILE}`];
      log(`segments round ${round}: ${violations[0]}`);
      if (workerAccessFailure(out.stdout)) {
        log(`segments round ${round}: the segmenter could not reach the run's files — not asked again`);
        return { envs: currentEnvs, notes: [], changed: false, halt: environmentCheckpoint("segmenter", out.stdout) };
      }
      continue;
    }
    const r = await applySegmentsFile(segPath, parsedEnvs, flat);
    if (r.violations.length === 0) {
      log(`segments round ${round}: accepted — ${r.notes.length} change(s)`);
      for (const n of r.notes) log(n);
      return { envs: r.envs, notes: r.notes, changed: true };
    }
    violations = r.violations;
    log(`segments round ${round}: ${violations.length} violation(s) — ${violations[0]}`);
  }
  if (existsSync(segPath)) {
    const aside = `${segPath}.rejected`;
    await rm(aside, { force: true });
    await writeFile(aside, await readFile(segPath, "utf8"), "utf8");
    await rm(segPath, { force: true });
  }
  log(`segments: not clean after ${MAX_SEGMENT_ROUNDS} rounds; set aside, continuing on the parser's output`);
  return { envs: currentEnvs, notes: [`segment: the segmenter's file was rejected (${violations[0]}); the gaps above stand`], changed: false };
}

export const runStageV1: VerifyStage = async (args: VerifyStageArgs): Promise<VerifyStageResult> => {
  const { runDir, state, log } = args;
  const verify = state.verify;
  if (!verify) throw new Error("V1: state has no `verify` block — this is not a verify run.");

  // 0. PATCH mode: V1.5 found errors on a faithful core; the transcription is not touched.
  {
    const directivePath = path.join(runDir, VERIFY_FILES.v1ReviseDirective);
    const d = existsSync(directivePath) ? ReviseDirectiveSchema.parse(JSON.parse(await readFile(directivePath, "utf8"))) : null;
    // `last_drift` is the drift the last V1.5 pass handed to a revise round, so that the pass
    // after it can tell drift the agent could not fix from drift that is still moving. An entry
    // that consumes no revise directive (a patch round, a re-entry, a cold extraction) was told
    // nothing: the record is void, or the next pass calls undelivered drift "repeated".
    if (!d || d.mode === "patch") delete verify.last_drift;
    if (d?.mode === "patch") return runPatchMode(args, d);
  }

  // Revise or rebuild: the path, and why, are logged on every entry.
  const entry = await v1EntryMode(runDir, verify.source.sha256, args.dryRun);
  log(`entry: ${entry.mode === "revise" ? "revise the existing transcription" : "cold extraction"} — ${entry.why}`);
  // The transcription is rebuilt from the reference core: a hand edit of it would be lost (a dry run
  // revises the transcription itself; a changed source starts over).
  const transcribedPath = path.join(runDir, VERIFY_FILES.coreTranscribed);
  if (!args.dryRun && entry.sourceSha === verify.source.sha256 && verify.transcribed_written_sha256 && existsSync(transcribedPath) && (await sha256File(transcribedPath)) !== verify.transcribed_written_sha256) {
    return {
      status: "checkpoint",
      message: `${VERIFY_FILES.coreTranscribed} was edited by hand since V1 wrote it; V1 rebuilds it from ${V1_REFS_FILE}, so the edit would be lost. Undo the edit there (V1 reads the file it wrote to carry records across renamed nodes), make the fix in ${V1_REFS_FILE}, then --resume.`,
    };
  }
  if (entry.sourceSha !== verify.source.sha256) {
    // The paper changed: what was transcribed, and every verdict given on it, describe another
    // text. The old reference core and any pending transcription directive are set aside.
    verify.source.sha256 = entry.sourceSha;
    verify.confirmed = {};
    const refsFile = path.join(runDir, V1_REFS_FILE);
    if (existsSync(refsFile)) await rename(refsFile, `${refsFile}.prev`);
    const pending = path.join(runDir, VERIFY_FILES.v1ReviseDirective);
    if (existsSync(pending)) await rm(pending, { force: true });
    // the directive never reached an agent: the drift it carried was not "handed to a revise round"
    delete verify.last_drift;
    log(`source changed: ${V1_REFS_FILE} set aside (.prev), carried V1.5 verdicts and any pending directive dropped`);
  }

  // 1. Mechanical extraction + scope.
  const sourceDir = path.join(runDir, VERIFY_FILES.sourceDir);
  // The authors' note macros are read away when a paper is read for the first time (a cold extraction);
  // a transcription on file is revised against the text it was cut from, read as its `envs.json` records.
  const noteMacros = entry.mode === "revise" ? await recordedNoteMacros(runDir) : process.env.LEANSMITH_NOTE_MACROS !== "off";
  const parsed = await buildEnvsJson(sourceDir, verify.source.main_file, noteMacros, runDir);
  const { flat } = parsed;
  if (entry.mode === "cold" && noteMacros === false) log("parser: authors' note macros are read as written (LEANSMITH_NOTE_MACROS=off)");
  for (const m of flat.notes?.log ?? []) log(`parser: ${m}`);
  for (const w of parsed.warnings) log(`parser: ${w}`);
  const scopeOf = (e: EnvsJson): { scope: string[]; theoremLike: string[] } => {
    const scope = computeScope(e, verify.targets);
    const byId = new Map(e.envs.map((x) => [x.id, x] as const));
    return { scope, theoremLike: scope.filter((id) => THEOREM_LIKE_KINDS.has(byId.get(id)?.kind ?? "other")) };
  };
  // 1b. Segmentation fallback: the parser's gaps, filled by an agent that points at lines.
  let envs = parsed.envs;
  let segmentNotes: string[] = [];
  {
    const existing = await applyExistingSegments(args, parsed.envs, flat);
    envs = existing.envs;
    segmentNotes = existing.notes;
    // A revise entry keeps the segmentation the reference core was written against.
    if (!existing.applied && !args.dryRun && entry.mode === "cold") {
      const gaps = segmentationGaps(parsed.warnings, envs, scopeOf(envs).theoremLike);
      if (gaps.length > 0) {
        const r = await runSegmenter(args, parsed.envs, envs, flat, gaps);
        if (r.halt) return r.halt;
        envs = r.envs;
        segmentNotes = r.notes;
      }
    }
  }
  // An algorithm the units leave uncut (markup the cutter does not know) is repaired as before: say so.
  const uncut = (e: EnvsJson): string[] => PaperUnits.parse(flat.text, e, flatLineStart(flat.text, flat.lineMap)).file.warnings ?? [];
  let parserWarnings = [...parsed.warnings, ...segmentNotes, ...uncut(envs)];
  await writeEnvsArtifacts(runDir, envs, flat);
  let { scope, theoremLike } = scopeOf(envs);
  if (theoremLike.length === 0) {
    throw new Error(
      `V1: the extraction scope holds no theorem-like environment (scope: ${scope.join(", ") || "empty"}). ` +
        `The paper's ${envs.envs.length} environments yielded nothing to verify — check --targets and --main.`,
    );
  }
  await writeJsonAtomic(path.join(runDir, V1_SCOPE_FILE), {
    targets: verify.targets,
    envs: scope,
    theorem_like: theoremLike,
  });
  log(
    `parsed ${envs.envs.length} environments from ${envs.files.length} file(s); ` +
      `scope = ${scope.length} (${theoremLike.length} theorem-like)`,
  );
  // 1c. Every statement and proof the parser hands on is whole TeX. One cut inside math (a proof
  // ended at a QED mark set inside its last display) is a parser defect no agent round can fix —
  // `proof_tex` must equal the parsed proof verbatim — so the transcription is refused here.
  {
    const cut = envBalanceProblems(envs, scope);
    if (cut.length > 0) {
      for (const c of cut) log(`unbalanced parse: ${c}`);
      return {
        status: "checkpoint",
        message:
          `V1 refused the transcription: ${cut.length} parsed statement/proof text(s) are not balanced TeX (cut inside math, ` +
          `a display or an environment):\n` +
          cut.map((c) => `  - ${c}`).join("\n") +
          `\nThis is a parser gap, not a transcription defect: re-cut these texts in discovery/segments.json, or make the smallest neutral edit in a COPY of the source and run it from V1 (leansmith SKILL §'When the pipeline itself fails').`,
      };
    }
  }

  const corePath = path.join(runDir, VERIFY_FILES.coreJson);

  // 2. Dry run: the mechanical core, through the same gate + lint. A revise entry keeps the
  // transcription and only rebuilds core.json from it and the patch file.
  if (args.dryRun && entry.mode === "revise") {
    await rebuildPatchedCore(runDir, { detectHandEdits: false });
    const core = parseTypedCore(await readFile(corePath, "utf8"), `V1 core ${corePath}`);
    log(`materialized ${VERIFY_FILES.coreJson} from ${VERIFY_FILES.coreTranscribed} + ${VERIFY_FILES.patches} — no extraction, no agent`);
    return { status: "completed", message: `dry run: transcription kept, core materialized (no agent): ${counts(core)}` };
  }
  if (args.dryRun) {
    await mkdir(path.dirname(corePath), { recursive: true });
    await writeCoreJson(corePath, minimalCore(args.qid, envs, scope));
    const { core, violations, warnings } = await validateRound(corePath, envs, scope, flat);
    if (!core || violations.length > 0) {
      throw new Error(
        `V1 dry run: the mechanically transcribed core did not pass its own gate — this is a V1 bug.\n` +
          violations.map((v) => `  - ${v}`).join("\n"),
      );
    }
    await writeLintWarnings(runDir, warnings, parserWarnings);
    const stale = await snapshotTranscribedCore(runDir, verify);
    if (stale) log(`WARNING: ${stale}`);
    verify.v1_rounds += 1;
    return { status: "completed", message: `dry run: ${counts(core)}` };
  }

  // 3. Agent rounds.
  const directivePath = path.join(runDir, VERIFY_FILES.v1ReviseDirective);
  let directive: ReviseDirective | null = null;
  if (existsSync(directivePath)) {
    directive = ReviseDirectiveSchema.parse(JSON.parse(await readFile(directivePath, "utf8")));
    log(`revise round ${directive.round}: ${directive.findings.length} must-fix finding(s)`);
  }
  const base = await readFile(PROMPT_FILE, "utf8");
  const refsPath = path.join(runDir, V1_REFS_FILE);
  await mkdir(path.join(runDir, "logs"), { recursive: true });

  let violations: string[] = [];
  const truncationTried = new Set<string>();
  /** Referee fixes the runner applied this invocation; re-applied after every agent round,
   * because the agent rewrites REFS_FILE and has dropped them. */
  const appliedFixes: Array<{ id: string; fix: NonNullable<ReviseDirective["findings"][number]["fix"]>; detail: string }> = [];

  // 3a. MECHANICAL revise. The referee states a drift fix as data whenever it is an edit of
  // the core's structure; the runner applies those to the reference core itself. Only the
  // findings without a fix (or whose fix could not be applied) go to the agent — and when
  // none are left, the round needs no agent at all: materialize, check, accept. A re-entry with
  // no directive is the same path with nothing to apply.
  if (entry.mode === "revise") {
    const reentry = directive === null;
    let d: ReviseDirective = directive ?? { mode: "transcribe", round: 0, findings: [] };
    const tag = reentry ? "re-entry" : `revise round ${d.round}`;
    const withFix = d.findings.filter((f) => f.axis === "faithfulness" && hasDriftFix(f.fix));
    if (withFix.length > 0) {
      let rawRefs: Parameters<typeof applyDriftFixes>[0] | null = null;
      try {
        rawRefs = JSON.parse(normalizeRawModelJson(await readFile(refsPath, "utf8")));
      } catch {
        rawRefs = null;
      }
      if (rawRefs) {
        const base = rawRefs;
        const fixesOf = (keep: (id: string) => boolean) => withFix.filter((f) => keep(f.id)).map((f) => ({ id: f.id, fix: f.fix! }));
        // A fix whose edit does not materialize (an anchor that does not cut, an environment that is
        // not the paper's) is not applied: the runner never hands the agent a violation it made.
        const refViolations = (refs: unknown): Set<string> => {
          const p = RefCoreSchema.safeParse(refs);
          return new Set(p.success ? materializeRefCore(p.data, envs, flat.text).violations : []);
        };
        const before = refViolations(base);
        let out = applyDriftFixes(base, fixesOf(() => true));
        const broken = out.applied.flatMap((id) => {
          const added = [...refViolations(applyDriftFixes(base, fixesOf((x) => x === id)).refs)].filter((v) => !before.has(v));
          return added.length > 0 ? [{ id, reason: `the edit does not fit the paper: ${added.join(" ")}` }] : [];
        });
        if (broken.length > 0) {
          const brokenIds = new Set(broken.map((b) => b.id));
          const rest = applyDriftFixes(base, fixesOf((x) => !brokenIds.has(x)));
          out = { ...rest, rejected: [...rest.rejected, ...broken] };
        }
        for (const n of out.notes) log(n);
        for (const r of out.rejected) log(`referee fix rejected — ${r.id}: ${r.reason}`);
        // Never write a core the fixes made invalid (duplicate ids, dangling wiring): the agent
        // cannot repair a violation the runner re-creates after every one of its rounds.
        assertFixKeepsRefCoreValid(rawRefs, out.refs, `V1 ${tag}`);
        appliedFixes.push(...withFix.filter((f) => out.applied.includes(f.id)).map((f) => ({ id: f.id, fix: f.fix!, detail: f.detail })));
        await writeFile(refsPath, JSON.stringify(out.refs, null, 2), "utf8");
        parserWarnings = [...parserWarnings, ...out.notes];
        const applied = new Set(out.applied);
        // A fix the runner could not apply reaches the agent as prose: the finding, why the fix failed.
        const why = new Map(out.rejected.map((r) => [r.id, r.reason] as const));
        d = {
          ...d,
          findings: d.findings
            // Only the finding whose fix was applied is answered; another finding on the node still goes.
            // (… and one whose fix also carries prose for the transcriber — the setting, an edit the
            // runner could not merge — is answered in its structural part only: the rest goes to the agent.)
            .filter((f) => !(f.axis === "faithfulness" && hasDriftFix(f.fix) && applied.has(f.id) && !f.fix.setting && !f.fix.also))
            .map((f) => (f.axis === "faithfulness" && hasDriftFix(f.fix) && applied.has(f.id) ? { ...f, detail: `${f.detail}\n(The runner applied the referee's structural fix; what is left for you is the part stated in words above.)`, fix: null } : f))
            .map((f) => (f.axis === "faithfulness" && hasDriftFix(f.fix) && why.has(f.id) ? { ...f, detail: `${f.detail}\n(The referee's structural fix could not be applied — ${why.get(f.id)} — make the change yourself.)`, fix: null } : f)),
        };
        log(`${tag}: ${out.applied.length} fix(es) applied by the runner, ${out.rejected.length} rejected, ${d.findings.length} finding(s) left for the agent`);
      }
    }
    if (d.findings.length === 0) {
      const refViolations = await materializeRefs(refsPath, corePath, envs, flat);
      if (refViolations.length === 0) {
        const checked = await validateRound(corePath, envs, scope, flat, await citationAccounting(refsPath, verify.citation_accounting === true));
        if (checked.core && checked.violations.length === 0) {
          if (resolveProseLocators(checked.core, flat) > 0) await writeCoreJson(corePath, checked.core);
          await rm(directivePath, { force: true });
          await writeLintWarnings(runDir, checked.warnings, parserWarnings);
          for (const l of await carryOrphanedRecords(runDir, checked.core, verify, await readPatchFile(runDir))) log(l);
          const stale = await snapshotTranscribedCore(runDir, verify);
          if (stale) log(`WARNING: ${stale}`);
          if (reentry) {
            log(`${tag}: materialized ${VERIFY_FILES.coreJson} from ${V1_REFS_FILE} + ${VERIFY_FILES.patches} — no extraction, no agent (${counts(checked.core)})`);
            return { status: "completed", message: `core materialized from the existing transcription (no agent): ${counts(checked.core)}` };
          }
          log(`${tag}: every finding was fixed mechanically — core accepted without an agent round (${counts(checked.core)})`);
          return { status: "completed", message: `core revised mechanically (no agent round): ${counts(checked.core)}` };
        }
        violations = checked.violations;
      } else {
        violations = refViolations;
      }
      log(`${tag}: ${reentry ? "the materialized core" : "mechanical fixes applied but the core"} is not clean (${violations[0]}); handing the violations to the agent`);
      directive = null;
    } else {
      directive = d;
    }
  }

  // A core extracted cold accounts for its citations, and so does every later entry of the run (a
  // halt mid-extraction, a revise round): recorded in the state, so no reference core can drop it. A
  // revise of a reference core older than the accounting leaves its citations as they are.
  // Saved before the first agent call: a process killed mid-round resumes under the accounting.
  if (entry.mode === "cold" && verify.citation_accounting !== true) {
    verify.citation_accounting = true;
    if (!args.dryRun) await saveState(args.repoRoot, args.qid, args.state);
  }
  const strict = verify.citation_accounting === true;
  for (let round = 1; round <= MAX_V1_ROUNDS; round += 1) {
    const accounting = await citationAccounting(refsPath, strict);
    const prompt = buildPrompt({
      citations: strict || accounting !== null,
      inlineLeaves: accounting?.leaves ?? [],
      base,
      qid: args.qid,
      corePath,
      refsPath,
      envs,
      scope,
      directive,
      violations,
    });
    log(
      `round ${round}/${MAX_V1_ROUNDS}: prompt ${PROMPT_FILE} + blocks, ${Buffer.byteLength(prompt)} bytes, ` +
        `${violations.length} violation(s) to fix`,
    );
    const out = await args.deps.runCodex({
      prompt,
      cwd: runDir,
      // The agent writes ONE file, `discovery/core_refs.json`, inside its own cwd — the
      // narrowest sandbox that permits that is `workspace-write`. (`productionWrite` is a
      // dispatcher-level cwd switch and is inert for a direct `runCodex` call with an
      // explicit cwd, so it is not set.)
      sandboxMode: "workspace-write",
      model: MODEL_PLAN.mechanicalTier.model,
      reasoningEffort: MODEL_PLAN.mechanicalTier.effort,
      leanLsp: false,
      webSearch: false,
      outputSchema: REPLY_OUTPUT_SCHEMA,
    });
    await writeFile(
      path.join(runDir, "logs", `v1_round${round}.json`),
      JSON.stringify({ prompt_bytes: Buffer.byteLength(prompt), prompt, stdout: out.stdout }, null, 2),
      "utf8",
    );

    let reply: z.infer<typeof ReplySchema> | null = null;
    try {
      reply = ReplySchema.parse(expectStringJsonOutput(out.stdout));
    } catch (err) {
      const reason = err instanceof Error ? err.message : String(err);
      violations = [`(reply) the status JSON did not parse: ${reason}`];
      log(`round ${round}: unparseable reply — ${reason}`);
      continue;
    }
    if (reply.status === "failed") {
      const why = reply.message ?? "(no message)";
      log(`round ${round}: the builder refused — ${why}`);
      if (workerAccessFailure(why)) return environmentCheckpoint("V1 builder", why);
      return {
        status: "checkpoint",
        message:
          `V1 could not transcribe this paper: ${why}. Inspect discovery/envs.json and ` +
          `discovery/v1_scope.json, fix the source or --targets, then re-enter with --from-stage V1.`,
      };
    }

    // "completed" with nothing written, and a reply that says it could not: the same halt.
    if (!existsSync(refsPath) && !existsSync(corePath) && workerAccessFailure(reply.message ?? "")) {
      log(`round ${round}: the builder wrote nothing — ${reply.message}`);
      return environmentCheckpoint("V1 builder", reply.message ?? "");
    }

    // The agent writes the REFERENCE core; the runner copies the text. (A core.json written
    // directly — the dry run, an older artifact — is still accepted.)
    // A referee fix that no longer applies to the agent's transcription goes to the agent, once, with
    // its finding: the next pass's referee checks the change.
    let notReapplied: string[] = [];
    if (existsSync(refsPath) && appliedFixes.length > 0) {
      let raw: Parameters<typeof applyDriftFixes>[0] | null = null;
      try {
        raw = JSON.parse(normalizeRawModelJson(await readFile(refsPath, "utf8")));
      } catch {
        raw = null; // unparseable refs are reported by materializeRefs below
      }
      if (raw && Array.isArray(raw.statements) && Array.isArray(raw.assumptions) && Array.isArray(raw.definitions)) {
        const again = applyDriftFixes(raw, appliedFixes, { reapply: true });
        for (const r of again.rejected) log(`round ${round}: referee fix not re-applied — ${r.id}: ${r.reason}`);
        notReapplied = again.rejected.map((r) => `(fix) the referee's structural fix for "${r.id}" no longer applies to your transcription (${r.reason}) — make the change it asked for yourself: ${appliedFixes.find((f) => f.id === r.id)?.detail ?? r.id}`);
        const dropped = new Set(again.rejected.map((r) => r.id));
        appliedFixes.splice(0, appliedFixes.length, ...appliedFixes.filter((f) => !dropped.has(f.id)));
        assertFixKeepsRefCoreValid(raw, again.refs, `V1 round ${round} (re-applying referee fixes)`);
        if (JSON.stringify(again.refs) !== JSON.stringify(raw)) {
          await writeFile(refsPath, JSON.stringify(again.refs, null, 2), "utf8");
          log(`round ${round}: re-applied ${again.applied.length} referee fix(es) the agent had dropped`);
        }
      }
    }
    if (existsSync(refsPath)) {
      let refViolations = [...notReapplied, ...(await materializeRefs(refsPath, corePath, envs, flat))];
      if (refViolations.length > 0 && !args.dryRun) {
        // An anchor that lands just PAST its environment's end says the parser ended the
        // statement early. Hand those environments to the segmenter (once each) and retry.
        let refs: { statements?: Array<{ id: string; env?: string }>; assumptions?: Array<{ id: string; source?: { env?: string } }>; definitions?: Array<{ id: string; source?: { env?: string } }> } = {};
        try {
          refs = JSON.parse(normalizeRawModelJson(await readFile(refsPath, "utf8")));
        } catch {
          refs = {}; // unparseable refs: already a (refs) violation below; nothing to extend
        }
        const envOfNode = (id: string): string | undefined =>
          refs.statements?.find((n) => n.id === id)?.env ??
          refs.assumptions?.find((n) => n.id === id)?.source?.env ??
          refs.definitions?.find((n) => n.id === id)?.source?.env;
        const gaps = truncationGaps(refViolations, envOfNode, envs, flat, anchorMatches).filter((g) => !truncationTried.has(g.split(" ")[0]!));
        if (gaps.length > 0) {
          for (const g of gaps) truncationTried.add(g.split(" ")[0]!);
          log(`round ${round}: ${gaps.length} environment(s) look truncated — ${gaps[0]}`);
          const r = await runSegmenter(args, parsed.envs, envs, flat, gaps);
          if (r.halt) return r.halt;
          if (r.changed) {
            envs = r.envs;
            parserWarnings = [...parsed.warnings, ...r.notes, ...uncut(envs)];
            await writeEnvsArtifacts(runDir, envs, flat);
            ({ scope, theoremLike } = scopeOf(envs));
            refViolations = [...notReapplied, ...(await materializeRefs(refsPath, corePath, envs, flat))];
          }
        }
      }
      if (refViolations.length > 0) {
        violations = refViolations;
        log(`round ${round}: ${violations.length} reference violation(s) — ${violations[0]}`);
        continue;
      }
    }
    const checked = await validateRound(corePath, envs, scope, flat, await citationAccounting(refsPath, strict));
    if (checked.core && checked.violations.length === 0) {
      if (resolveProseLocators(checked.core, flat) > 0) await writeCoreJson(corePath, checked.core);
      verify.v1_rounds += round;
      if (directive) await rm(directivePath, { force: true });
      await writeLintWarnings(runDir, checked.warnings, parserWarnings);
      if (entry.mode === "revise") for (const l of await carryOrphanedRecords(runDir, checked.core, verify, await readPatchFile(runDir))) log(l);
      const stale = await snapshotTranscribedCore(runDir, verify);
      if (stale) log(`WARNING: ${stale}`);
      log(
        `round ${round}: core accepted — ${counts(checked.core)}` +
          (checked.warnings.length > 0 ? `; ${checked.warnings.length} lint warning(s) for V1.5` : ""),
      );
      return {
        status: "completed",
        message: `core extracted in ${round} round(s): ${counts(checked.core)}`,
      };
    }
    violations = checked.violations;
    log(`round ${round}: ${violations.length} violation(s) — ${violations[0]}`);
  }

  verify.v1_rounds += MAX_V1_ROUNDS;
  return {
    status: "checkpoint",
    message:
      `V1 could not produce a clean core in ${MAX_V1_ROUNDS} rounds. Remaining violations:\n` +
      violations.map((v) => `  - ${v}`).join("\n"),
  };
};

/**
 * The paper's units the fixer addresses its ops to (`ops.ts` `unitsBlock`): for each node it may repair,
 * its statement's units and its environment's proof units, each with its id; and the passage sources the
 * reply's ops are resolved against (`core_refs.json`, `envs.json`, the parse of `flat.tex`).
 */
export async function paperUnits(runDir: string, transcribed: Core, nodes: readonly string[]): Promise<{ block: string; src: PassageSources }> {
  // A run without `flat.tex` / `envs.json` has no units: no op resolves on it.
  const envsFile = path.join(runDir, VERIFY_FILES.envsJson);
  const units = (await loadUnits(runDir)) ?? PaperUnits.parse("", { main_file: "", files: [], newtheorem: {}, envs: [], bibliography: [] } as unknown as EnvsJson);
  let refs: RefCore | null = null;
  const refsFile = path.join(runDir, "discovery", "core_refs.json");
  if (existsSync(refsFile)) {
    const parsed = RefCoreSchema.safeParse(JSON.parse(await readFile(refsFile, "utf8")));
    if (parsed.success) refs = parsed.data;
  }
  const envs = existsSync(envsFile) ? (JSON.parse(await readFile(envsFile, "utf8")) as EnvsJson) : ({ envs: [] } as unknown as EnvsJson);
  const src: PassageSources = { units, refs, statements: transcribed.statements, envs };
  return { block: unitsBlock(src, nodes), src };
}

/** A statement's printed text, compact (whitespace collapsed, at most `max` characters). */
function compactStatement(text: string, max = 600): string {
  const t = statementBody(text).replace(/\s+/g, " ").trim();
  return t.length > max ? `${t.slice(0, max - 1)}…` : t;
}

/**
 * The SERVES block of the fixer's prompt (user decision 2026-09-24: a lemma is repaired with the main
 * theorems in mind): for each node to repair, every OTHER main theorem (`mainTheoremIds`) that rests
 * on it transitively (a main theorem no other main theorem uses gets none) (the node is in the theorem's `depends_on`
 * closure, or — an assumption / definition — a statement of that closure uses it), with the theorem's
 * printed statement, compact; the run's `key_contribution` heads the block. "" when no node serves one.
 */
export function servesBlock(core: Core, file: { key_results: readonly string[]; key_contribution?: string } | null, nodes: readonly string[]): string {
  const mains = [...mainTheoremIds(core, file)].filter((id) => core.statements.some((s) => s.id === id));
  const closures = new Map(mains.map((t) => [t, statementClosure(core, [t])] as const));
  const byId = new Map(core.statements.map((s) => [s.id, s] as const));
  const serves = (node: string, t: string): boolean => {
    if (node === t) return false;
    const c = closures.get(t)!;
    return c.has(node) || [...c].some((id) => byId.get(id)?.depends_on.includes(node));
  };
  const lines: string[] = [];
  for (const node of [...new Set(nodes)]) {
    if (node === "run") continue;
    const users = mains.filter((t) => serves(node, t));
    if (users.length === 0) continue;
    lines.push(`${node} — SERVES (main results):`, ...users.map((t) => `  - ${t}: ${compactStatement(byId.get(t)!.statement)}`));
  }
  if (lines.length === 0) return "";
  const kc = file?.key_contribution?.trim();
  return [`Key contribution: ${kc ? kc : "(not yet stated — you state it in \`key_contribution\`)"}`, ...lines].join("\n");
}

/** The suggested repairs sent back to the fixer (`withdrawn_repair`), each op as its unit range and raw TeX. Pure. */
export function withdrawnRepairBlock(findings: ReadonlyArray<{ id: string; withdrawn_repair?: { corrected_statement: string | null; ops?: PatchOp[]; drops?: string[]; adds?: string[]; corollaries?: ReadonlyArray<{ title?: string; statement: string; follows: string; adds?: string[] }>; umbrella?: boolean } }>): string {
  return findings
    .filter((f) => f.withdrawn_repair)
    .map((f) => {
      const w = f.withdrawn_repair!;
      return [
        `- ${f.id}`,
        ...(w.umbrella ? ["  umbrella: true (the result only said that the blocks below hold)"] : w.corrected_statement ? [`  the statement it gave:`, indent(w.corrected_statement)] : []),
        ...(w.ops ?? []).map((o) => `  op: replace ${o.unit}${o.to ? ` … ${o.to}` : ""} by\n${indent(o.tex)}`),
        ...(w.drops?.length ? [`  drops: ${w.drops.join(", ")}`] : []),
        ...(w.adds?.length ? [`  adds: ${w.adds.join(", ")}`] : []),
        ...(w.corollaries ?? []).map((c) => `  corollary${c.title ? ` (${c.title})` : ""}${c.adds?.length ? ` [adds: ${c.adds.join(", ")}]` : ""}:\n${indent(c.statement)}\n  follows:\n${indent(c.follows)}`),
      ].join("\n");
    })
    .join("\n");
}

const indent = (t: string): string => t.split("\n").map((l) => `    ${l}`).join("\n");

/** The OWNER GUIDANCE block: the owner's binding guidance for each node it asked the fixer to redo. */
export function ownerGuidanceBlock(findings: ReadonlyArray<{ id: string; owner_guidance?: string }>): string {
  return findings.filter((f) => f.owner_guidance?.trim()).map((f) => `- ${f.id}: ${f.owner_guidance!.trim()}`).join("\n");
}

/** The fields of a core node a patch round reads: its id, kind and text, its wiring and hypotheses,
 * a cited leaf's source, a split block's parent, an umbrella's mark. Not its locator, symbol list,
 * provenance tag, environment or user list (`core.transcribed.json` has them). */
const FIXER_NODE_FIELDS = new Set(["id", "kind", "name", "statement", "condition", "construction", "depends_on", "hypotheses", "status", "source", "inputs", "by_member_properties", "split_from", "umbrella"]);

/**
 * The part of the typed core a patch round needs, compact (one node per line): the nodes to repair and
 * every node they rest on (their `depends_on` closure), each with the fields the fixer reads
 * (`FIXER_NODE_FIELDS`: no printed proof — the PAPER UNITS block shows it — no locator or symbol list),
 * the symbols those nodes use, and the statements using them directly in one line each (a
 * hypothesis added to a result must reach its users). The whole core is `discovery/core.transcribed.json`.
 * Pure.
 */
export function coreExcerpt(core: Core, ids: readonly string[]): string {
  const byId = new Map<string, { id: string; depends_on?: string[] }>([...core.statements, ...core.assumptions, ...core.definitions].map((n) => [n.id, n as never] as const));
  const keep = new Set<string>();
  const visit = (id: string): void => {
    if (keep.has(id) || !byId.has(id)) return;
    keep.add(id);
    for (const d of byId.get(id)!.depends_on ?? []) visit(d);
  };
  for (const id of ids) visit(id);
  // The results using them directly, in one line each (their full entries are in the file).
  const users = core.statements.filter((st) => !keep.has(st.id) && st.depends_on.some((d) => ids.includes(d)));
  const pick = <T extends { id: string }>(xs: readonly T[]): T[] => xs.filter((x) => keep.has(x.id));
  const fields = (n: object): Record<string, unknown> => Object.fromEntries(Object.entries(n).filter(([k, v]) => FIXER_NODE_FIELDS.has(k) && v !== undefined && v !== null));
  const nodes = [...pick(core.assumptions), ...pick(core.definitions), ...pick(core.statements)] as Array<{ free_symbols?: string[] }>;
  const used = new Set(nodes.flatMap((n) => n.free_symbols ?? []));
  const symbols = core.symbols.filter((sy) => used.has(sy.name));
  const line = (x: unknown): string => JSON.stringify(x);
  const clip = (t: string): string => {
    const c = statementBody(t).replace(/\s+/gu, " ").trim();
    return c.length > 240 ? `${c.slice(0, 239)}…` : c;
  };
  return [
    `qid: ${core.qid}; target estimand: ${core.target_estimand}`,
    "symbols:",
    ...symbols.map(line),
    "assumptions and definitions:",
    ...[...pick(core.assumptions), ...pick(core.definitions)].map((n) => line(fields(n))),
    "statements:",
    ...pick(core.statements).map((n) => line(fields(n))),
    ...(users.length > 0 ? ["results using them (id, depends_on, statement opening):", ...users.map((st) => line({ id: st.id, depends_on: st.depends_on, statement: clip(st.statement) }))] : []),
  ].join("\n");
}

/** A carried entry of the patch file, in one line (the whole entry is in `discovery/patches.json`). */
function carriedLine(e: { node: string; corrected_statement?: string | null; ops?: PatchOp[]; corollaries?: readonly unknown[]; suggested_repair?: unknown }, what: string): string {
  const ops = e.ops ?? [];
  const parts = [
    e.corrected_statement ? "statement corrected" : "",
    ops.length ? `${ops.length} op(s)` : "",
    e.corollaries?.length ? `${e.corollaries.length} corollar${e.corollaries.length === 1 ? "y" : "ies"} split off` : "",
    e.suggested_repair ? "a suggested repair awaiting the owner" : "",
  ].filter(Boolean);
  return `- ${what} ${e.node}: ${parts.join("; ") || "no change to the text"}`;
}

/** Bytes of a previous reply under which it is re-sent whole when no violation names an entry of
 * it (`previousReplyExcerpt`); a larger one is shown by its named entries only. */
export const PREVIOUS_REPLY_WHOLE_MAX = 16_000;

/** The fixer's previous reply with only the entries the violations name (and `key_results` /
 * `key_contribution`). The whole reply only when NO violation names an entry and the reply is small
 * (`PREVIOUS_REPLY_WHOLE_MAX`): a violation naming no entry re-sends nothing on its own — it is read
 * in the VIOLATIONS block, and the entries it concerns are the ones the other violations name (or,
 * past the cap, none: the fixer is told the rest stands). Pure. */
export function previousReplyExcerpt(previous: unknown, violations: readonly string[]): unknown {
  // A reply that did not parse is shown as text, cut at the cap: the fixer answers afresh anyway.
  if (typeof previous === "string" && Buffer.byteLength(previous, "utf8") > PREVIOUS_REPLY_WHOLE_MAX) {
    return `${previous.slice(0, PREVIOUS_REPLY_WHOLE_MAX)}\n[… ${Buffer.byteLength(previous, "utf8") - PREVIOUS_REPLY_WHOLE_MAX} bytes omitted: the reply did not parse; answer afresh …]`;
  }
  if (!previous || typeof previous !== "object" || Array.isArray(previous)) return previous;
  const entries = replyEntries(previous);
  const mentions = (v: string, names: readonly string[]): boolean => names.some((n) => (n.startsWith("key_") ? v.includes(n) : v.includes(`"${n}"`)));
  const named = new Set([...entries].filter(([, e]) => violations.some((v) => mentions(v, e.names))).map(([k]) => k));
  if (named.size === 0 && Buffer.byteLength(JSON.stringify(previous), "utf8") <= PREVIOUS_REPLY_WHOLE_MAX) return previous;
  const r = previous as Record<string, unknown>;
  const keep = (list: string) => (Array.isArray(r[list]) ? (r[list] as Array<{ node?: unknown }>).filter((e) => named.has(`${list} "${String(e?.node)}"`)) : []);
  return { key_results: r.key_results, key_contribution: r.key_contribution, patches: keep("patches"), unfixable: keep("unfixable"), rejected: keep("rejected") };
}

/** A round-2 reply completed with every entry of the previous reply it leaves out (the fixer was shown,
 * and returns, only the entries its violations name). Pure. */
export function mergePreviousReply(previous: unknown, reply: unknown): unknown {
  if (!previous || typeof previous !== "object" || !reply || typeof reply !== "object" || Array.isArray(reply)) return reply;
  const p = previous as Record<string, unknown>;
  const r = { ...(reply as Record<string, unknown>) };
  for (const k of ["key_results", "key_contribution"]) if (!(k in r) && k in p) r[k] = p[k];
  // A node the reply answers in any list (a patch, an unfixable entry, a rejection) is answered.
  const lists = ["patches", "unfixable", "rejected"];
  const answered = new Set(lists.flatMap((l) => (Array.isArray(r[l]) ? (r[l] as Array<{ node?: unknown }>).map((e) => e?.node) : [])));
  for (const list of lists) {
    const mine = Array.isArray(r[list]) ? (r[list] as Array<{ node?: unknown }>) : [];
    const theirs = Array.isArray(p[list]) ? (p[list] as Array<{ node?: unknown }>) : [];
    r[list] = [...mine, ...theirs.filter((e) => !answered.has(e?.node))];
  }
  return r;
}

function patchPrompt(args: {
  base: string;
  core: Core;
  directive: ReviseDirective;
  existing: PatchFile | null;
  violations: readonly string[];
  units?: string;
  serves?: string;
  /** From round 2 on: the fixer's previous reply (the parsed JSON, or the raw text when it did not
   * parse). It replaces the on-disk PATCHES FILE block: the fixer revises only what the violations name. */
  previousReply?: unknown;
  /** The earlier findings on the nodes to repair (`fixer_history.ts`). */
  earlier?: string;
}): string {
  const guidance = ownerGuidanceBlock(args.directive.findings);
  const withdrawn = withdrawnRepairBlock(args.directive.findings);
  const restate = args.directive.findings.filter((f) => f.restatement?.length).map((f) => `- ${f.id}: ${f.restatement!.join("; ")}`).join("\n");
  const demanded = new Set(args.directive.findings.map((f) => f.id).filter((id) => id !== "run"));
  const blocks = [
    args.base.trimEnd(),
    "",
    "=== TYPED CORE (the nodes to repair, what they rest on and the results using them, as transcribed before any patch; the whole core is discovery/core.transcribed.json and the paper discovery/flat.tex — your working directory is the run directory) ===",
    coreExcerpt(args.core, [...demanded]),
    "",
    ...(args.units ? ["=== PAPER UNITS (the statement and proof units of the results to repair: address every op to these ids; any other result's units are in discovery/units.json, ids with offsets into discovery/flat.tex) ===", args.units, ""] : []),
    `=== FINDINGS (patch round ${args.directive.round}) — every node named here must be patched or declared unfixable ===`,
    JSON.stringify(args.directive.findings.map(({ fix: _fix, owner_guidance: _g, restatement: _r, withdrawn_repair: _w, ...f }) => f), null, 2),
    ...(args.earlier
      ? ["", "=== EARLIER FINDINGS (what earlier rounds sent back on these nodes: unless a current finding or an owner reading says otherwise, your repair must still meet each and never reintroduce one) ===", args.earlier]
      : []),
    ...(args.serves ? ["", "=== SERVES (the main results each node to repair supports; the brief's SERVES rule applies) ===", args.serves] : []),
    ...(guidance
      ? ["", "=== OWNER GUIDANCE (binding: the paper's owner discarded the suggested repair of these nodes and asks for a repair along these lines; follow it, or answer the node `unfixable` with `reason` saying why the guidance cannot be realised) ===", guidance]
      : []),
    ...(withdrawn
      ? ["", "=== YOUR SUGGESTED REPAIR, SENT BACK (as it stood; your new entry for the node replaces it whole — ops apply to the printed text, so keep every op, drop and add that still holds, or those units return to the printed text) ===", withdrawn]
      : []),
    ...(restate
      ? ["", "=== RESTATEMENT (the repair on file for these nodes breaks the contract — the brief's DROP-IN REPLACEMENT rule, or a text the author reads does not compile or read; answer each node again: the same repair with every problem listed fixed) ===", restate]
      : []),
  ];
  if (args.previousReply !== undefined) {
    const shown = previousReplyExcerpt(args.previousReply, args.violations);
    blocks.push(
      "",
      "=== YOUR PREVIOUS REPLY (the entries the violations below name, with key_results and key_contribution: revise them and return them; the runner keeps every other entry of that reply as it was) ===",
      typeof shown === "string" ? shown : JSON.stringify(shown, null, 2),
    );
  }
  if (args.existing) {
    // The file in the reply's shape: the runner's fields (re-stamped from the findings) and the texts it
    // derives from the ops (the corrected statement, an amended proof, what a suggestion gives up) are not
    // shown.
    const replyShape = <T extends { ops?: PatchOp[]; proof_note?: string }>({ corrected_statement: _c, ...b }: T & { corrected_statement?: unknown }): Omit<T, "corrected_statement"> =>
      (b.ops ?? []).some(isProofOp) ? { ...b, proof_note: null as never } : b;
    const { owner_readings: ownerReadings } = args.existing;
    if (args.previousReply === undefined) {
      // In full: the entries of the nodes the findings name; the others (carried as they stand) one line each.
      const full = {
        key_results: args.existing.key_results,
        key_contribution: args.existing.key_contribution,
        patches: args.existing.patches.filter((p) => demanded.has(p.node)).map(({ accepted_weakening: _a, given_up: _g, given_up_by: _gb, narrowed_by: _n, supersedes: _s, ...p }) => replyShape(p)),
        unfixable: args.existing.unfixable.filter((u) => demanded.has(u.node)).map(({ suggested_by: _s, declined: _d, consequence_of: _c, consequence_reason: _cr, ...u }) => ({ ...u, suggested_repair: u.suggested_repair ? (({ given_up: _gu, given_up_by: _gub, supersedes: _su, ...sr }) => replyShape(sr))(u.suggested_repair) : null })),
      };
      const carried = [
        ...args.existing.patches.filter((p) => !demanded.has(p.node)).map((p) => carriedLine(p, "patch")),
        ...args.existing.unfixable.filter((u) => !demanded.has(u.node)).map((u) => carriedLine(u, "unfixable")),
      ];
      blocks.push(
        "",
        "=== PATCHES FILE (your previous patch; the entries of the nodes the FINDINGS name in full; every other entry stands as it is — leave it out, or return it only to revise it; its full text is in discovery/patches.json) ===",
        JSON.stringify(full, null, 2),
        ...(carried.length > 0 ? ["", "Carried entries (stand as they are):", ...carried] : []),
      );
    }
    if (ownerReadings?.length) {
      blocks.push(
        "",
        "=== OWNER READINGS (binding: the paper's owner withdrew a finding under each; the runner keeps them — do not return them, and never patch a node on the finding its reading answers) ===",
        ...ownerReadings.map((r) => `- ${r.id} on ${r.node}: ${r.reading}`),
      );
    }
  }
  if (args.violations.length > 0) {
    blocks.push("", "=== VIOLATIONS IN YOUR PREVIOUS REPLY (must fix) ===", ...args.violations.map((v) => `- ${v}`));
  }
  return blocks.join("\n");
}

/** A reply's entries keyed for the drift check: `patch <node>`, `unfixable <node>`, `rejected
 * <node>`, and the top-level `key_results` / `key_contribution`; each with the ids it is named by. */
function replyEntries(reply: unknown): Map<string, { names: string[]; value: unknown }> {
  const out = new Map<string, { names: string[]; value: unknown }>();
  if (!reply || typeof reply !== "object" || Array.isArray(reply)) return out;
  const r = reply as Record<string, unknown>;
  for (const k of ["key_results", "key_contribution"]) if (k in r) out.set(k, { names: [k], value: r[k] });
  for (const list of ["patches", "unfixable", "rejected"]) {
    const arr = r[list];
    if (!Array.isArray(arr)) continue;
    for (const e of arr) {
      const node = e && typeof e === "object" ? (e as { node?: unknown }).node : undefined;
      if (typeof node !== "string") continue;
      out.set(`${list} "${node}"`, { names: [node], value: e });
    }
  }
  return out;
}

/** JSON with sorted keys, absent/undefined fields dropped, and whitespace runs in strings collapsed. */
function canonicalJson(v: unknown): string {
  if (typeof v === "string") return JSON.stringify(v.replace(/\s+/g, " ").trim());
  if (Array.isArray(v)) return `[${v.map(canonicalJson).join(",")}]`;
  if (v && typeof v === "object") {
    const o = v as Record<string, unknown>;
    // null, an empty list and an absent field all mean "none" in a reply
    return `{${Object.keys(o).filter((k) => o[k] !== undefined && o[k] !== null && !(Array.isArray(o[k]) && (o[k] as unknown[]).length === 0)).sort().map((k) => `${JSON.stringify(k)}:${canonicalJson(o[k])}`).join(",")}}`;
  }
  return JSON.stringify(v ?? null);
}

/**
 * From round 2 on the fixer revises only the entries the violations name and copies every other
 * entry of its previous reply verbatim. An entry is named when a violation quotes its node, or
 * mentions `key_results` / `key_contribution`. A violation that
 * names no entry opens the whole file (nothing is checked); so does a previous reply that did not
 * parse. Every other entry changed, added or dropped (up to whitespace) is a drift violation.
 */
export function replyDriftViolations(previous: unknown, violations: readonly string[], reply: unknown, free: ReadonlySet<string> = new Set()): string[] {
  const before = replyEntries(previous);
  if (before.size === 0) return [];
  const after = replyEntries(reply);
  const mentions = (v: string, names: readonly string[]): boolean => names.some((n) => (n.startsWith("key_") ? v.includes(n) : v.includes(`"${n}"`)));
  const all = new Map([...before, ...after]);
  if (!violations.every((v) => [...all.values()].some((e) => mentions(v, e.names)))) return [];
  // (an entry the runner set aside — `free` — the fixer may keep, drop or change)
  const named = (e: { names: string[] } | undefined): boolean => e !== undefined && (violations.some((v) => mentions(v, e.names)) || e.names.some((n) => free.has(n)));
  const out: string[] = [];
  for (const key of all.keys()) {
    const b = before.get(key);
    const a = after.get(key);
    if (named(b) || named(a)) continue;
    if (!b) out.push(`(drift) ${key} is new, but no violation named it — return your previous reply with only the named entries revised.`);
    else if (!a) out.push(`(drift) ${key} was dropped, but no violation named it — copy it from your previous reply verbatim.`);
    else if (canonicalJson(a.value) !== canonicalJson(b.value)) out.push(`(drift) ${key} changed, but no violation named it — copy it from your previous reply verbatim.`);
  }
  return out;
}

/**
 * The fixer's `owner_explanation` on every entry it wrote (an entry the owner already settled is
 * carried as it was): a note meeting the field contract (`noteProblems`: the paper's `labels` and
 * `\ref{…}` arguments are the paper's own references, not node ids; each defect's step among the node's
 * units, `unitsOf`) — except on a consequential patch of a node with no finding (`hasFinding`), which
 * carries none. Pipeline vocabulary is left to the backstop filter (`ownerFacing`), since words like
 * "edge" or "node" are legitimate in a graph paper.
 */
export function ownerExplanationViolations(file: PatchFile, prior: PatchFile | null, labels?: PaperLabels, hasFinding?: (node: string) => boolean, unitsOf?: (node: string) => ReadonlySet<string>): string[] {
  const settled = new Set((prior?.unfixable ?? []).filter((u) => u.suggested_repair).map((u) => u.node));
  // A consequential patch on a node with no finding explains itself in its `reason` (`consequential.ts`).
  const consequence = (p: PatchFile["patches"][number]): boolean => hasFinding !== undefined && isConsequential(p) && !hasFinding(p.node);
  const entries = [...file.patches.filter((p) => !consequence(p)).map((p) => ({ node: p.node, text: p.owner_explanation, what: "patch" })), ...file.unfixable.filter((u) => !settled.has(u.node)).map((u) => ({ node: u.node, text: u.owner_explanation, what: "unfixable entry" }))];
  const out: string[] = [];
  for (const e of entries) {
    if (e.text === undefined || e.text === null || e.text === "") {
      out.push(`the ${e.what} for "${e.node}" has no \`owner_explanation\` — the note {claim, defects, why, fix, gives_up} for the paper's author.`);
      continue;
    }
    for (const p of noteProblems(e.text, { labels, units: unitsOf?.(e.node) ?? null })) out.push(`the \`owner_explanation\` for "${e.node}" ${p} — the author reads it next to the paper.`);
  }
  return out;
}

/**
 * Proof steps name no pipeline id (user rule 2026-09-25: a pipeline id reached the author in a blue
 * step): every proof op's TeX and — for a node the paper prints no proof of — `proof_note` of the
 * patches and suggested repairs in `file`, checked with the node-id
 * rule (`nodeIdMentions`: the paper's `labels` and reference-macro arguments are the paper's own). One
 * violation per step naming the node. `printsProof`: whether the paper prints a proof of a node. Pure.
 */
export function proofStepIdViolations(file: Pick<PatchFile, "patches" | "unfixable">, printsProof: (node: string) => boolean, labels?: PaperLabels): string[] {
  const out: string[] = [];
  type Body = { ops?: PatchOp[]; proof_note?: string | null; corollaries?: ReadonlyArray<{ statement: string; follows: string }> | null };
  const check = (node: string, b: Body, what: string): void => {
    // A corollary the repair splits off is the author's to read too: its statement and its proof.
    const steps = [...(b.ops ?? []).flatMap((op) => (isProofOp(op) ? [op.tex] : [])), ...(!printsProof(node) && b.proof_note ? [b.proof_note] : []), ...(b.corollaries ?? []).flatMap((c) => [c.statement, c.follows])];
    const ids = [...new Set(steps.flatMap((t) => nodeIdMentions(t, labels)))];
    if (ids.length > 0) {
      out.push(
        `a proof step of the ${what} for "${node}" names ${ids.join(", ")} — refer to a hypothesis by its content in the paper's words ` +
          `and to a result as the paper does, never by id: the author reads the step.`,
      );
    }
  };
  for (const p of file.patches) check(p.node, p, "patch");
  for (const u of file.unfixable) if (u.suggested_repair) check(u.node, u.suggested_repair, "suggested repair");
  return out;
}

/**
 * Why a corrected statement of the reply is not a drop-in replacement for the printed one
 * (`restatement.ts`), one violation per problem naming the node: every patch's corrected statement
 * (an accepted weakening returned in its accepted wording excepted) and every suggested repair not
 * already pending with the owner. Pure.
 */
export function restatementViolations(core: Core, file: PatchFile, prior: PatchFile | null): string[] {
  const settled = new Set((prior?.unfixable ?? []).filter((u) => u.suggested_repair).map((u) => u.node));
  const printed = (id: string): string | null => core.statements.find((s) => s.id === id)?.statement ?? null;
  const entries = [
    ...file.patches
      .filter((p) => !(p.accepted_weakening && prior?.patches.some((q) => q.node === p.node && q.corrected_statement === p.corrected_statement)))
      // An umbrella's sentence is the pipeline's: its blocks carry the printed statement's content.
      .filter((p) => !p.umbrella)
      .map((p) => ({ node: p.node, text: p.corrected_statement, what: "patch", ops: p.ops })),
    ...file.unfixable.filter((u) => !settled.has(u.node) && !u.suggested_repair?.umbrella).map((u) => ({ node: u.node, text: u.suggested_repair?.corrected_statement ?? null, what: "suggested repair", ops: u.suggested_repair?.ops })),
  ];
  const out: string[] = [];
  for (const e of entries) {
    const o = printed(e.node);
    if (!e.text?.trim() || !o) continue;
    for (const p of restatementProblems(o, e.text, { ops: e.ops })) out.push(`(restatement) the ${e.what} for "${e.node}": its corrected_statement ${p}. It replaces the printed statement word for word, so it must read as complete without it.`);
  }
  return out;
}

/**
 * The texts of every repair of the reply the author reads (`repairTextProblems`): the TeX of each
 * corrected statement, op and proof note (C6), none stating a result in an environment of its own
 * (`newtheorem`: the paper's theorem environments); and the fixer's explanation — a `gives_up` a proof-only repair
 * contradicts (C4), a `why` that is no concrete failing instance (C2). Every patch and every
 * suggested repair not already pending with the owner; one violation per problem naming the node.
 * Pure.
 */
export function repairTextViolations(core: Core, file: PatchFile, prior: PatchFile | null, newtheorem: EnvsJson["newtheorem"] = {}): string[] {
  const settled = new Set((prior?.unfixable ?? []).filter((u) => u.suggested_repair).map((u) => u.node));
  const all = [...core.statements, ...core.assumptions, ...core.definitions] as Array<{ id: string; tex_locator?: { label?: string | null } | null }>;
  const labelOf = (id: string): string | null => all.find((n) => n.id === id)?.tex_locator?.label ?? null;
  const resultEnvs = resultEnvNames(newtheorem);
  const ctx = (node: string): { printed: string; proof: string; labelOf: typeof labelOf; resultEnvs: Set<string> } => {
    const st = core.statements.find((x) => x.id === node);
    // An assumption's or a definition's repair copies its own printed text, as a statement's does.
    const own = core.assumptions.find((x) => x.id === node)?.condition ?? core.definitions.find((x) => x.id === node)?.construction;
    return { printed: st?.statement ?? own ?? "", proof: st?.proof_tex ?? "", labelOf, resultEnvs };
  };
  const out: string[] = [];
  // An accepted weakening returned in its accepted wording is the owner's text.
  const accepted = (p: PatchFile["patches"][number]): boolean => !!p.accepted_weakening && !!prior?.patches.some((q) => q.node === p.node && q.corrected_statement === p.corrected_statement);
  for (const p of file.patches) {
    if (accepted(p)) continue;
    for (const x of repairTextProblems(p, p.owner_explanation, ctx(p.node))) out.push(`the patch for "${p.node}": ${x}.`);
  }
  for (const u of file.unfixable) {
    if (settled.has(u.node) || !u.suggested_repair) continue;
    for (const x of repairTextProblems(u.suggested_repair, u.owner_explanation, ctx(u.node))) out.push(`the suggested repair for "${u.node}": ${x}.`);
  }
  return out;
}

/**
 * The entries of the previous patch file the runner CARRIES into this round: every patch and
 * `unfixable` entry for a node the round's findings do not name. They were checked when written and
 * stand as they are (a fresh V1.5 pass grades the patched core either way); the fixer is not asked
 * to return them, and a reply that leaves one out keeps it (`carryPriorEntries`). Pure.
 */
export function carriedEntries(prior: PatchFile | null, directive: ReviseDirective): Pick<PatchFile, "patches" | "unfixable"> {
  const named = new Set(directive.findings.map((f) => f.id));
  return {
    patches: (prior?.patches ?? []).filter((p) => !named.has(p.node)),
    unfixable: (prior?.unfixable ?? []).filter((u) => !named.has(u.node)),
  };
}

/** The reply with every carried entry it does not answer (no patch, `unfixable` or `rejected` entry
 * on the node) added back as it was; `carried` lists the nodes added. Pure. */
export function carryPriorEntries(file: PatchFile, carried: Pick<PatchFile, "patches" | "unfixable">): { file: PatchFile; carried: string[] } {
  const answered = new Set([...file.patches.map((p) => p.node), ...file.unfixable.map((u) => u.node), ...(file.rejected ?? []).map((r) => r.node)]);
  const patches = carried.patches.filter((p) => !answered.has(p.node));
  const unfixable = carried.unfixable.filter((u) => !answered.has(u.node));
  return {
    file: { ...file, patches: [...file.patches, ...patches], unfixable: [...file.unfixable, ...unfixable] },
    carried: [...patches.map((p) => p.node), ...unfixable.map((u) => u.node)],
  };
}

/** `file` without the entries on `nodes`: the fixer's own entries, for the checks on what it wrote. Pure. */
function withoutNodes(file: PatchFile, nodes: ReadonlySet<string>): PatchFile {
  return { ...file, patches: file.patches.filter((p) => !nodes.has(p.node)), unfixable: file.unfixable.filter((u) => !nodes.has(u.node)) };
}

/**
 * V1 patch mode in a DRY RUN. No V1.5 dry run reports an error, so a patch directive here comes
 * from a (simulated) F-stage rewind. No fixer is called: a stand-in replacement per node named — its
 * last printed unit with a dry-run remark appended (a `clarify` finding: its pinned readings), else a
 * proof note — goes through the same checks, and `core.json` is rebuilt from it.
 */
async function dryRunPatchMode(
  args: VerifyStageArgs,
  directive: ReviseDirective,
  transcribed: Core,
  required: readonly string[],
): Promise<VerifyStageResult> {
  const { runDir, log } = args;
  const existing = await readPatchFile(runDir);
  const byNode = new Map(directive.findings.map((f) => [f.id, f] as const));
  const paper = await paperUnits(runDir, transcribed, required);
  const patches = [...(existing?.patches ?? []).filter((p) => !byNode.has(p.node))];
  for (const id of required) {
    if (patches.some((p) => p.node === id) || (existing?.unfixable ?? []).some((u) => u.node === id)) continue;
    const f = byNode.get(id);
    const passage = nodePassage(paper.src, id);
    const last = passage?.units.at(-1);
    const remark = f?.axis === "clarify" ? `(dry run --- the reading written in: ${(f.folds ?? []).map((x) => x.reading).join("; ") || "none pinned"})` : "(dry run --- corrected)";
    const ops: PatchOp[] = last ? [{ op: "replace", unit: last.id, tex: `${paper.src.units.contentOf(last).trim()} ${remark}` }] : [];
    patches.push({
      node: id,
      ops,
      corrected_statement: passage ? materializeRepair(ops, { units: paper.src.units, passage }, id).corrected_statement : null,
      ...(passage ? { supersedes: supersededNodes(paper.src, id, ops) } : {}),
      proof_note: "dry run: no fixer was called; the paper's proof is unchanged.",
    });
  }
  let file: PatchFile = {
    key_results: existing?.key_results.length ? existing.key_results : transcribed.statements.filter((st) => st.kind === "theorem").map((st) => st.id),
    key_contribution: existing?.key_contribution || "dry run: no fixer was called.",
    patches,
    unfixable: existing?.unfixable ?? [],
    ...(existing?.owner_readings?.length ? { owner_readings: existing.owner_readings } : {}),
  };
  const violations = validatePatchFile(transcribed, file, required);
  if (violations.length > 0) {
    throw new Error(`V1 dry-run patch mode: the stand-in patch file fails its own checks — this is a V1 bug.\n${violations.map((v) => `  - ${v}`).join("\n")}`);
  }
  await writeJsonAtomic(path.join(runDir, VERIFY_FILES.patches), file);
  await rebuildPatchedCore(runDir, { detectHandEdits: false });
  await rm(path.join(runDir, VERIFY_FILES.v1ReviseDirective), { force: true });
  args.state.verify!.core_sha256 = null;
  log(`dry run: patch round ${directive.round} revised without an agent — stand-in patch(es) on ${required.join(", ")}; ${VERIFY_FILES.coreJson} rebuilt from ${VERIFY_FILES.coreTranscribed} + ${VERIFY_FILES.patches}`);
  return { status: "completed", message: `dry run: patched ${required.join(", ")} (no agent)` };
}

/**
 * V1 PATCH MODE. The fixer (solving tier) returns the whole patch file; the runner fills the
 * runner-owned fields, checks it mechanically against the TRANSCRIBED core (coverage, ids,
 * wiring, closure) and through the structural gate, writes `discovery/patches.json`, and
 * rebuilds `core.json`. An unfixable node on a key result's path stops the run here (the
 * paper's contribution cannot be kept); everything else goes to a fresh V1.5 pass.
 */
/** The patch file carrying suggestions that weaken a claim, settled by the owner-scope rule
 * (`weakening.ts`): suggestions on intermediate results are applied as patches the runner narrowed;
 * suggestions on main theorems are recorded in the owner's receipt and the run halts (every mode) —
 * `core.json` is rebuilt once the owner answers. With no main theorem pending, the narrowed core
 * goes to a fresh V1.5 pass. */
async function haltForOwner(args: VerifyStageArgs, transcribed: Core, file: PatchFile, directivePath: string): Promise<VerifyStageResult> {
  const settled = settleSuggestions(args.state, transcribed, file, args.log);
  await writeJsonAtomic(path.join(args.runDir, VERIFY_FILES.patches), settled.file);
  await rm(directivePath, { force: true });
  args.state.verify!.core_sha256 = null;
  const rec = settled.receipt;
  if (rec) {
    return {
      status: "checkpoint",
      message: `no repair keeps ${rec.items.map((i) => i.node).join(", ")} at full strength; the suggested (weakened) repair(s) of these main theorem(s) await the owner (--accept-repair / --decline-repair).`,
    };
  }
  const { descoped } = await rebuildPatchedCore(args.runDir, { detectHandEdits: false });
  return {
    status: "completed",
    message:
      `narrowed ${settled.narrowed.map((n) => n.node).join(", ")} (intermediate results) to their strongest true version` +
      `${descoped.size > 0 ? `; descoped ${[...descoped.keys()].join(", ")}` : ""} — handing the patched core to a fresh V1.5 pass`,
  };
}

async function runPatchMode(args: VerifyStageArgs, directiveIn: ReviseDirective): Promise<VerifyStageResult> {
  let directive = directiveIn;
  const { runDir, log, state } = args;
  // A patch file in an older format is converted first, never patched in it.
  try {
    await readPatchFile(runDir);
  } catch (err) {
    return { status: "checkpoint", message: `V1 patch mode: ${err instanceof Error ? err.message : String(err)}` };
  }
  const verify = state.verify!;
  const directivePath = path.join(runDir, VERIFY_FILES.v1ReviseDirective);
  const transcribed = await readTranscribedCore(runDir);
  const flatFile = path.join(runDir, VERIFY_FILES.flatTex);
  const flat = existsSync(flatFile) ? await readFile(flatFile, "utf8") : "";
  const envsFile = path.join(runDir, VERIFY_FILES.envsJson);
  const envsJson = existsSync(envsFile) ? (JSON.parse(await readFile(envsFile, "utf8")) as EnvsJson) : null;
  const existing = await readPatchFile(runDir);
  // A finding on a corollary a repair split off (a referee's, an F-stage reviewer's) is answered on
  // the repaired result: the fixer returns that entry, corollaries included.
  directive = { ...directive, findings: onSplitParent(directive.findings, existing) };
  // The note's fields are described once (`owner_text.ts` `NOTE_FIELDS_TEXT`), where its schema is shown.
  const base = (await readFile(PATCH_PROMPT_FILE, "utf8")).replace("{{NOTE_FIELDS}}", () => NOTE_FIELDS_TEXT.replace(/^/gmu, "    "));
  // Every node named now, AND every node an earlier round already patched or gave up on: a
  // revised file may not silently drop an earlier repair (its error would vanish from the report).
  // An earlier entry the findings do not name is CARRIED (`carriedEntries`): kept as it stands
  // unless the reply revises it, so it is not demanded again.
  const everyNode = [
    ...new Set([
      ...directive.findings.map((f) => f.id).filter((id) => id !== "run"),
      ...openErrorIds(verify.paper_errors),
      ...(existing?.patches ?? []).map((p) => p.node),
      ...(existing?.unfixable ?? []).map((u) => u.node),
    ]),
  ];
  // What the PAPER got wrong: the referee's correctness and ambiguity findings. An objection to a
  // patch ("patch rejected") or to the key-result list is about the repair, not the paper.
  // The ledger (`state.verify.paper_errors`): every earlier entry stays — the FIRST error found
  // on a node is the record — and this round's findings on the paper join it. Persisted with the
  // state even when the fixer checkpoints.
  // First entry per node wins — across rounds, and within this round (a node graded both an error
  // and an ambiguity keeps the witnessed error, which the directive lists first).
  // An F-stage `clarify` finding (the statement admits several readings) joins as a
  // CLARIFICATION: the fixer states the intended reading beside the statement (`readings`), and the report does
  // not count it as an error of the paper. An error found on the node replaces a clarification.
  // An F-stage finding the fixer may REJECT (it says the paper grants what the finding says is
  // missing) joins the ledger only once the fixer patches it: a rejected one waits for the next
  // V1.5 pass's ruling (`state.verify.fixer_rejections`).
  const rejectable = (f: ReviseDirective["findings"][number]): boolean => f.from_stage !== undefined && f.overruled !== true && f.id !== "run";
  const addToLedger = (ledger: NonNullable<typeof verify.paper_errors>, f: ReviseDirective["findings"][number]): void => {
    const isError = f.axis === "correctness" || f.axis === "ambiguity";
    const isClarification = f.axis === "clarify" && f.from_stage !== undefined;
    // An entry the owner withdrew yields only to an error on another axis (its correctness finding
    // is overruled before it reaches a directive).
    // A witnessed error also replaces an ambiguity on record: the node is then refuted, not undetermined.
    const replaceable = !(f.id in ledger) || ledger[f.id]!.kind === "clarification" || (ledger[f.id]!.undetermined === true && f.axis === "correctness") || (isWithdrawn(ledger[f.id]) && f.axis !== "correctness");
    if (isError && replaceable) {
      // An ambiguity the paper leaves open shows nothing false: the entry says so (`undetermined`).
      // (the entry replaced keeps what was ruled on its repair; a withdrawal of the ambiguity it was does not carry over)
      const had = ledger[f.id]?.undetermined && !isWithdrawn(ledger[f.id]) ? ledger[f.id]! : undefined;
      ledger[f.id] = {
        detail: f.detail,
        witness: f.witness ?? null,
        ...(f.axis === "ambiguity" && !f.witness ? { undetermined: true } : {}),
        ...(had?.owner_decision ? { owner_decision: had.owner_decision } : {}),
        ...(had?.decision_reason ? { decision_reason: had.decision_reason } : {}),
        ...(had?.guidance ? { guidance: had.guidance } : {}),
        ...(had?.weakens_contribution ? { weakens_contribution: true } : {}),
        ...(had?.suggested_repair ? { suggested_repair: had.suggested_repair } : {}),
      };
    } else if (isClarification && !(f.id in ledger)) {
      ledger[f.id] = { detail: f.detail, witness: null, kind: "clarification" };
    }
  };
  const ledger = { ...(verify.paper_errors ?? {}) };
  for (const f of directive.findings) if (!rejectable(f)) addToLedger(ledger, f);
  verify.paper_errors = ledger;
  const errors = verify.paper_errors;
  // A repair the referee found WEAKENS the claim becomes a suggestion for the owner, never another
  // fixer attempt: every finding on it waits for the pass that grades the suggestion, and the fixer
  // answers only the rest of the round.
  // A repair whose text does not compile (`restatement`) is the fixer's to write again first: it is
  // answered with the weakening finding, never locked into a suggestion carrying that text.
  const restated = new Set(directive.findings.filter((f) => f.restatement?.length).map((f) => f.id));
  const weakening = directive.findings.filter((f) => f.weakens_contribution === true && existing?.patches.some((p) => p.node === f.id) && !restated.has(f.id));
  let prior = existing;
  if (weakening.length > 0) {
    prior = convertWeakeningPatches(existing!, weakening);
    const converted = new Set(weakening.map((f) => f.id));
    directive = { ...directive, findings: directive.findings.filter((f) => !converted.has(f.id)) };
    log(`${weakening.length} repair(s) weaken the claim (${weakening.map((f) => f.id).join(", ")}) — turned into suggestions (applied on intermediate results, the owner's on main theorems)`);
    if (directive.findings.length === 0) return haltForOwner(args, transcribed, prior, directivePath);
  }
  // A suggestion awaiting the owner stands whatever a reply says (`pinOwnerEntries`): a finding on it
  // waits for the pass that grades it, never for a fixer answer that would be discarded.
  const awaiting = new Set((prior?.unfixable ?? []).filter(isPendingSuggestion).map((u) => u.node));
  const onAwaiting = directive.findings.filter((f) => awaiting.has(f.id));
  if (onAwaiting.length > 0) {
    directive = { ...directive, findings: directive.findings.filter((f) => !awaiting.has(f.id)) };
    log(`${[...new Set(onAwaiting.map((f) => f.id))].join(", ")}: a suggestion awaits the owner — its finding(s) wait for the pass that grades it, not the fixer`);
    if (directive.findings.length === 0) return haltForOwner(args, transcribed, prior!, directivePath);
  }
  const carried = carriedEntries(prior, directive);
  const carriedIds = new Set([...carried.patches.map((p) => p.node), ...carried.unfixable.map((u) => u.node)]);
  const required = everyNode.filter((id) => !carriedIds.has(id));
  const restating = directive.findings.filter((f) => f.restatement?.length).map((f) => f.id);
  log(
    `patch round ${directive.round}: ${required.length} node(s) to repair (${required.join(", ") || "none"})` +
      (restating.length > 0 ? `; ${restating.length} restated (${restating.join(", ")})` : "") +
      (carriedIds.size > 0 ? `; ${carriedIds.size} earlier entr${carriedIds.size === 1 ? "y" : "ies"} carried as they stand (${[...carriedIds].join(", ")})` : ""),
  );
  if (args.dryRun) {
    // No fixer, so nothing is rejected: every F-stage finding is patched (by the stand-in) and joins the ledger.
    for (const f of directive.findings) if (rejectable(f)) addToLedger(verify.paper_errors, f);
    const out = await dryRunPatchMode(args, directive, transcribed, required);
    const file = await readPatchFile(args.runDir);
    return file?.unfixable.some(isPendingSuggestion) ? haltForOwner(args, transcribed, file, directivePath) : out;
  }
  await mkdir(path.join(runDir, "logs"), { recursive: true });

  let violations: string[] = [];
  const stamp = Date.now().toString(36);
  // A reply the runner failed on last time (same directive): validated first, no fixer call, and
  // not counted as a fixer round.
  const directiveSha = createHash("sha256").update(await readFile(directivePath)).digest("hex");
  const pendingPath = path.join(runDir, VERIFY_FILES.v1PendingReply);
  let replay: string | null = null;
  if (existsSync(pendingPath)) {
    const pending = z.object({ directive_sha256: z.string(), stdout: z.string() }).safeParse(parseJsonWithEscapeRepair(await readFile(pendingPath, "utf8")));
    if (pending.success && pending.data.directive_sha256 === directiveSha) replay = pending.data.stdout;
    else log(`${VERIFY_FILES.v1PendingReply} was saved for another directive — ignored`);
    await rm(pendingPath, { force: true });
  }
  /** A runner exception while validating a reply is the runner's bug: never a violation the fixer
   * answers, never a spent round. The reply is kept for the next entry; the run stops here. */
  const runnerError = async (err: unknown, stdout: string, where: string): Promise<VerifyStageResult> => {
    const stack = err instanceof Error ? (err.stack ?? err.message) : String(err);
    await writeJsonAtomic(pendingPath, { directive_sha256: directiveSha, stdout });
    log(`runner error while validating the fixer's reply (${where}) — not the fixer's fault, no round counted:\n${stack}`);
    return {
      status: "checkpoint",
      message:
        `V1 patch mode: runner error while validating the fixer's reply (${where}): ${err instanceof Error ? err.message : String(err)}. ` +
        `The reply is saved in ${VERIFY_FILES.v1PendingReply}; fix the runner, then --resume (the directive is kept, and the saved reply is validated before any new fixer call).`,
    };
  };
  // The units of the results to repair; every other unit is in discovery/units.json (ids and offsets into
  // flat.tex), and every op resolves on the whole paper.
  const paper = await paperUnits(runDir, transcribed, directive.findings.map((f) => f.id).filter((id) => id !== "run"));
  const printsProof = (node: string): boolean => !!transcribed.statements.find((st) => st.id === node)?.proof_tex?.trim();
  const serves = servesBlock(transcribed, prior, directive.findings.map((f) => f.id));
  const history = await readFixerHistory(runDir);
  const earlier = earlierFindingsBlock(history, directive.findings, new Set((prior?.owner_readings ?? []).map((r) => r.node)));
  await writeFixerHistory(runDir, withFindings(history, directive.round, directive.findings));
  /** The fixer's last reply (parsed, or raw text) and the violations it was sent back with: every
   * round after a validated reply (the saved reply of round 0 included) shows it in place of the on-disk file, and the new reply may change only
   * the entries those violations name (`replyDriftViolations`). */
  let previousReply: unknown;
  /** The violations the fixer was sent at each round (`fixerRoundAllowed`). */
  const sent: number[] = [];
  let rounds = 0;
  /** The patches the last validated reply set aside (`setAsideSuggestionConsequences`): the next
   * reply may keep or drop them, neither is drift. */
  let asideIds = new Set<string>();
  for (let round = replay === null ? 1 : 0; ; round += 1) {
    if (round > 0) sent.push(violations.length);
    if (!fixerRoundAllowed(round, sent)) break;
    rounds = round;
    const cap = round > MAX_PATCH_AGENT_ROUNDS ? MAX_PATCH_AGENT_ROUNDS_CONVERGING : MAX_PATCH_AGENT_ROUNDS;
    const shownReply = previousReply;
    const shownViolations = violations;
    let stdout: string;
    if (round === 0) {
      stdout = replay!;
      log(`fixer round 0: validating the saved reply in ${VERIFY_FILES.v1PendingReply} (no fixer call)`);
    } else {
      const prompt = patchPrompt({ base, core: transcribed, directive, existing: prior, violations, units: paper.block, serves, previousReply: shownReply, earlier });
      log(
        `fixer round ${round}/${cap}: ${PATCH_PROMPT_FILE} + blocks, ${Buffer.byteLength(prompt)} bytes, ` +
          `${required.length} node(s) demanded, ${carriedIds.size} carried (${MODELS.codexVerify}, high)` +
          (round > MAX_PATCH_AGENT_ROUNDS ? ` — one more round: the violations fell from ${sent[sent.length - 2]} to ${sent[sent.length - 1]}` : ""),
      );
      const t0 = Date.now();
      const out = await args.deps.runCodex({
        prompt,
        cwd: runDir,
        // The fixer returns the patch file as its reply; it writes nothing.
        sandboxMode: "read-only",
        model: MODELS.codexVerify,
        reasoningEffort: "high",
        leanLsp: false,
        webSearch: false,
        outputSchema: PATCH_REPLY_JSON_SCHEMA,
      });
      await writeFile(
        path.join(runDir, "logs", `v1_patch_${stamp}_round${round}.json`),
        JSON.stringify({ prompt_bytes: Buffer.byteLength(prompt), prompt, stdout: out.stdout }, null, 2),
        "utf8",
      );
      await appendPipelineLog(args, {
        stage: "V1",
        status: "fixer_round",
        duration_ms: Date.now() - t0,
        message: `fixer round ${round}/${cap} (patch round ${directive.round}): 1 call, ${Buffer.byteLength(prompt)} prompt bytes, ${required.length} node(s) demanded, ${carriedIds.size} carried${violations.length ? `, ${violations.length} violation(s) answered` : ""}`,
      });
      stdout = out.stdout;
    }
    // The fixer's faults (not JSON, fails the schema) are violations it answers; an exception in
    // the runner's own checks is `runnerError`.
    let raw: unknown;
    try {
      raw = expectStringJsonOutput(stdout);
    } catch (err) {
      // Only malformed output is the fixer's; an exception in the parser's own repair is the runner's.
      if ((err as { code?: string }).code !== "codex_malformed_output") return runnerError(err, stdout, "parse");
      previousReply = stdout;
      violations = [`(reply) the patch file did not parse: ${err instanceof Error ? err.message : String(err)}`];
      log(`fixer round ${round}: ${violations[0]}`);
      continue;
    }
    if (shownReply !== undefined) {
      // Shown only the entries its violations name, the fixer returns those: the rest stand as they were.
      raw = mergePreviousReply(shownReply, raw);
      const drift = replyDriftViolations(shownReply, shownViolations, raw, asideIds);
      if (drift.length > 0) {
        // The baseline stays the reply the fixer was asked to revise; its violations still stand.
        violations = [...shownViolations, ...drift];
        log(`fixer round ${round}: ${drift.length} drift violation(s) — ${drift[0]}`);
        continue;
      }
    }
    previousReply = raw;
    // What a runner error saves: this round's reply merged with the one it revised (`mergePreviousReply`),
    // so the replay on the next entry has every entry the fixer gave.
    const mergedReply = (): string => (typeof previousReply === "string" ? previousReply : JSON.stringify(previousReply));
    // The entry of a hypothesis with no printed text of its own is bookkeeping, set here.
    const textless = normalizeTextlessEntries(raw, (node) => [...transcribed.assumptions, ...transcribed.definitions].some((n) => n.id === node) && nodePassage(paper.src, node) === null);
    if (textless.nodes.length > 0) log(`fixer round ${round}: ${textless.nodes.join(", ")} (no printed text of its own): a patch with no ops, its results restated instead`);
    raw = textless.raw;
    let derived: ReturnType<typeof materializeReply>;
    try {
      // The repair is ops on the paper's units: the corrected statement and the amended proof are
      // derived from them (`ops.ts`).
      const proofGiven = (node: string): boolean => printsProof(node) || !transcribed.statements.some((st) => st.id === node);
      derived = materializeReply(raw, (node) => ({ units: paper.src.units, passage: nodePassage(paper.src, node) }), proofGiven, (node, ops) => supersededNodes(paper.src, node, ops));
    } catch (err) {
      return runnerError(err, mergedReply(), "ops");
    }
    if (derived.violations.length > 0) {
      violations = derived.violations.map((v) => `(ops) ${v}`);
      log(`fixer round ${round}: ${violations.length} violation(s) — ${violations[0]}`);
      continue;
    }
    const parsed = PatchFileSchema.safeParse(derived.raw);
    if (!parsed.success) {
      violations = [`(reply) the patch file did not parse: ${parsed.error.message}`];
      log(`fixer round ${round}: ${violations[0]}`);
      continue;
    }
    let file: PatchFile = parsed.data;
    let rejected: NonNullable<PatchFile["rejected"]> = [];
    let rejectedIds = new Set<string>();
    try {
      // What the reply leaves out of the carried entries stands as it was; what the owner settled
      // (or has yet to settle) stands whatever the reply says.
      const merged = carryPriorEntries(file, carried);
      if (merged.carried.length > 0) log(`fixer round ${round}: ${merged.carried.length} carried entr${merged.carried.length === 1 ? "y" : "ies"} kept as they stand`);
      // The checks judge what the fixer wrote: a carried entry, and one the owner settled (or has yet
      // to), are not its text this round.
      const pinned = new Set((prior?.unfixable ?? []).filter((u) => u.suggested_repair).map((u) => u.node));
      const kept = new Set([...merged.carried, ...pinned]);
      file = pinOwnerEntries(merged.file, prior, new Set(directive.findings.filter((f) => f.restatement?.length).map((f) => f.id)));
      // A patch that follows a suggested repair: of an intermediate result, the suggestion is applied
      // in this same call (`narrowIntermediates`), so it follows a repair; of a main theorem, it awaits
      // the owner's ruling, not a round — set aside (the fixer's own entries; a carried one stands).
      const pending = [...file.unfixable, ...(prior?.unfixable ?? [])].filter(isPendingSuggestion).map((u) => u.node);
      const mains = mainTheoremIds(transcribed, file);
      const aside = setAsideSuggestionConsequences(withoutNodes(file, kept), new Set(pending.filter((n) => mains.has(n))));
      asideIds = new Set(aside.setAside.map((s) => s.node));
      // Held in the file (`set_aside`) with those held before, less any the fixer now patches outright.
      const held = [...(prior?.set_aside ?? []).filter((p) => !asideIds.has(p.node) && !file.patches.some((x) => x.node === p.node)), ...file.patches.filter((p) => asideIds.has(p.node))];
      file = { ...file, patches: file.patches.filter((p) => !asideIds.has(p.node)), ...(held.length > 0 ? { set_aside: held } : {}) };
      if (asideIds.size > 0) {
        log(`fixer round ${round}: ${asideIds.size} consequential patch(es) set aside, each following only a suggested repair of a main theorem the owner has not ruled on — ${aside.setAside.map((s) => `${s.node} (after ${s.follows.join(", ")})`).join("; ")}; held in ${VERIFY_FILES.patches} (set_aside), applied with the suggestion the owner accepts`);
      }
      /** The file with the intermediate suggestions as the repairs they become. */
      const asApplied = applySuggestions(file, new Set(pending.filter((n) => !mains.has(n))));
      // Rejections: only of an F-stage finding the directive names (not overruled), and never of a
      // node the file also patches or gives up on. A rejected node is answered, so coverage skips it.
      rejected = file.rejected ?? [];
      const rejectionViolations: string[] = [];
      for (const r of rejected) {
        const f = directive.findings.find((x) => x.id === r.node && rejectable(x));
        if (!f) rejectionViolations.push(`\`rejected\` names "${r.node}", which is not an F-stage finding of this round you may reject (a finding without \`from_stage\`, or one marked \`overruled\`, must be patched).`);
        if (file.patches.some((p) => p.node === r.node) || file.unfixable.some((u) => u.node === r.node)) {
          rejectionViolations.push(`"${r.node}" is both rejected and patched / declared unfixable — give one answer.`);
        }
        if ((existing?.patches ?? []).some((p) => p.node === r.node) || r.node in errors) {
          rejectionViolations.push(`"${r.node}" already carries a repair or a recorded error; it cannot be rejected.`);
        }
      }
      rejectedIds = new Set(rejected.map((r) => r.node));
      // A patch on a node with no finding of its own follows another repair (`consequential.ts`).
      const withFinding = findingNodes({ findings: directive.findings, ledger: errors, prior });
      const hasFinding = (node: string): boolean => withFinding.has(node);
      const statementIds = new Set(transcribed.statements.map((st) => st.id));
      violations = [
        ...rejectionViolations,
        ...validatePatchFile(transcribed, file, required.filter((id) => !rejectedIds.has(id) && !asideIds.has(id))),
        ...overlapViolations(file, (node) => ({ units: paper.src.units, passage: nodePassage(paper.src, node) }), pinned),
        // The wording checks judge what the fixer wrote this round, not a carried entry.
        ...ownerExplanationViolations(withoutNodes(file, kept), prior, paperLabels(flat), hasFinding, (node) => noteUnitIds(paper.src, node)),
        ...proofStepIdViolations(withoutNodes(file, kept), printsProof, paperLabels(flat)),
        ...consequenceViolations(withoutNodes(file, kept), hasFinding, {
          statements: statementIds,
          printsProof,
          labels: paperLabels(flat),
          all: asApplied,
        }),
        ...restatementViolations(transcribed, withoutNodes(file, kept), prior),
        ...repairTextViolations(transcribed, withoutNodes(file, kept), prior, envsJson?.newtheorem),
        // Every TeX field the fixer wrote must compile against the paper's preamble (P1: compile at source).
        ...(await texFieldViolations(patchFileTexFields(withoutNodes(file, kept), (op) => paper.src.units.textOfRun(op.unit, op.to)), { runDir, mainFile: verify.source.main_file, log })),
      ];
      // (two checks read the same note: a violation is told once)
      violations = [...new Set(violations)];
      // An unfixable node on a key result's path ends the run whatever else the file says: the
      // paper's key contribution cannot be kept, so no patched core is built.
      if (violations.length === 0) {
        const blocked = blockedUnfixable(transcribed, file);
        if (blocked.length > 0) {
          // The key contribution cannot be kept: every error in the ledger is the paper's
          // refutation (not only this round's findings — a round-two stop must report round one's).
          for (const [node, e] of Object.entries(errors)) {
            if (isWithdrawn(e)) continue;
            const p = file.patches.find((x) => x.node === node);
            const u = file.unfixable.find((x) => x.node === node);
            recordVerifyFinding(state, {
              node,
              stage: "V1.5",
              // A clarification that could not be written is an unsettled reading, not a refutation;
              // nor is a statement the paper leaves undetermined.
              ...openFindingKind(e),
              detail: u ? `${e.detail} — cannot be repaired: ${u.reason}` : e.detail,
              witness: e.witness,
              ...(p ? { patch: findingPatch(p, false) } : {}),
            });
          }
          // Kept for the record under another name: re-applying it would descope a key result.
          await writeJsonAtomic(path.join(runDir, "discovery", "patches.blocked.json"), file);
          await rm(directivePath, { force: true });
          log(`unfixable on a key result's path: ${blocked.join(", ")} — the run stops`);
          return {
            status: "failed",
            message: `${blocked.join(", ")} cannot be repaired without losing the paper's key contribution (key results: ${file.key_results.join(", ")}).`,
          };
        }
      }
      if (violations.length === 0) {
        const gate = runStructuralGate(applyPatchFile(transcribed, file).core, { allowBookkeeping: true, verbatim: true });
        violations = gate.violations.map((v) => `(gate ${v.code}) ${v.where}: ${v.message}`);
      }
    } catch (err) {
      return runnerError(err, mergedReply(), "patch-file checks");
    }
    if (violations.length > 0) {
      log(`fixer round ${round}: ${violations.length} violation(s) — ${violations[0]}`);
      continue;
    }

    // The F-stage findings the fixer patched join the ledger; the ones it rejected wait for the
    // next V1.5 pass to rule on them. `rejected` is never persisted in the patch file.
    const nextLedger = { ...(verify.paper_errors ?? {}) };
    for (const f of directive.findings) if (rejectable(f) && !rejectedIds.has(f.id)) addToLedger(nextLedger, f);
    verify.paper_errors = nextLedger;
    // A rejection still awaiting its ruling (a V1.5 pass that paused before its global pass) stays.
    const awaiting = (verify.fixer_rejections ?? []).filter((r) => !directive.findings.some((f) => f.id === r.node));
    verify.fixer_rejections = [...awaiting, ...rejected.map((r) => {
      const f = directive.findings.find((x) => x.id === r.node)!;
      return {
        node: r.node,
        axis: f.axis === "clarify" ? ("clarify" as const) : ("correctness" as const),
        from_stage: f.from_stage!,
        finding: f.detail,
        witness: f.witness ?? null,
        reason: r.reason,
        where_the_paper_grants_it: r.where_the_paper_grants_it,
      };
    })];
    if (rejected.length > 0) log(`the fixer rejects ${rejected.length} F-stage finding(s) (${[...rejectedIds].join(", ")}): the next V1.5 pass rules on them`);
    const { rejected: _rejected, ...persisted } = file;
    file = persisted;
    // No repair keeps some result at full strength: the owner rules on the suggestion first.
    if (file.unfixable.some(isPendingSuggestion)) {
      log(`the fixer found no repair that keeps ${file.unfixable.filter(isPendingSuggestion).map((u) => u.node).join(", ")} at full strength — the strongest true version is applied to intermediate results, main theorems go to the owner`);
      return haltForOwner(args, transcribed, file, directivePath);
    }
    await writeJsonAtomic(path.join(runDir, VERIFY_FILES.patches), file);
    const { descoped } = await rebuildPatchedCore(runDir, { detectHandEdits: false });
    await rm(directivePath, { force: true });
    verify.core_sha256 = null; // a patched core must be accepted by a fresh V1.5 pass
    log(
      `patch round ${directive.round}: ${file.patches.length} patch(es), ${file.unfixable.length} unfixable, ` +
        `${descoped.size} result(s) descoped — handing the patched core to a fresh V1.5 pass`,
    );
    return {
      status: "completed",
      message:
        `patched ${file.patches.map((p) => p.node).join(", ") || "nothing"}${descoped.size > 0 ? `; descoped ${[...descoped.keys()].join(", ")}` : ""}` +
        (rejected.length > 0 ? `; rejected ${[...rejectedIds].join(", ")} (for V1.5 to rule on)` : ""),
    };
  }
  // The last reply is kept: a --resume (after a runner fix) validates it before any new fixer call.
  if (previousReply !== undefined) await writeJsonAtomic(pendingPath, { directive_sha256: directiveSha, stdout: typeof previousReply === "string" ? previousReply : JSON.stringify(previousReply) });
  return {
    status: "checkpoint",
    message:
      `V1 patch mode: the fixer's patch file was not clean after ${rounds} rounds. Remaining violations:\n` +
      violations.map((v) => `  - ${v}`).join("\n") +
      `\nWrite ${VERIFY_FILES.patches} by hand, delete ${VERIFY_FILES.v1ReviseDirective}, then --from-stage V1.5 — or, when a violation is the runner's error, fix the runner and --resume (the last reply, saved in ${VERIFY_FILES.v1PendingReply}, is validated before any new fixer call).`,
  };
}
