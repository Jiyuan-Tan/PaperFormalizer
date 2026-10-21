/**
 * A corrected statement is a DROP-IN REPLACEMENT for the printed one (user rule 2026-09-25). Whether it
 * reads as one — restating rather than summarizing, not pointing at its surroundings, stating every
 * hypothesis its repair adds — is the referee's judgement (the rule is in the fixer and referee
 * prompts), never a runner text heuristic (user decision 2026-09-26: only exact checks block).
 *
 * What the runner checks here is exact: coverage is STRUCTURAL (the corrected statement is the printed
 * one with the repair's ops applied, `ops.ts`), so only a statement unit an op DELETES is a drop
 * (`droppedUnitProblems`); and the texts a repair writes are TeX that compiles and is well formed
 * (`repairTextProblems`).
 */
import { isProofOp, opTex, revisesProof, type PatchOp } from "./ops.js";
import { givesUpProblems, isStructuredExplanation, noteProblems, texMathProblems, type NoteContext } from "./owner_text.js";
import { BUILTIN_ENVS } from "./tex_envs.js";
import type { EnvKind } from "./types.js";

const RESULT_KINDS: ReadonlySet<EnvKind> = new Set<EnvKind>(["theorem", "lemma", "proposition", "corollary"]);

/** The environments a result is stated in: the standard names and the paper's own (`envs.json`
 * `newtheorem`), a starred one under its plain name. Pure. */
export function resultEnvNames(newtheorem: Readonly<Record<string, EnvKind>> = {}): Set<string> {
  const declared = Object.entries({ ...BUILTIN_ENVS, ...newtheorem }).filter(([, kind]) => RESULT_KINDS.has(kind)).map(([name]) => name.replace(/\*$/u, ""));
  return new Set([...declared, "claim", "fact", "conjecture"]);
}

/** Why `tex` is no text of a repair: it opens a result environment (`names`) the printed text it
 * replaces (`reference`) does not — a result of its own, which a repair states in `corollaries`. Pure. */
function resultEnvProblems(tex: string, field: string, names: ReadonlySet<string>, reference: string): string[] {
  const opened = (t: string): string[] => [...t.matchAll(/\\begin\s*\{\s*([^{}]*?)\*?\s*\}/gu)].map((m) => m[1]!).filter((n) => names.has(n));
  const printed = new Set(opened(reference));
  const own = [...new Set(opened(tex))].filter((n) => !printed.has(n));
  return own.length > 0
    ? [`states a result in an environment of its own in \`${field}\` (${own.map((n) => `\\begin{${n}}`).join(", ")}) — a repair's text is the sentences of the statement or proof it replaces, never a theorem-like environment: return a result that stands apart as an entry of \`corollaries\``]
    : [];
}

/**
 * What a repair's ops drop from the printed statement (empty = nothing). Coverage is structural: a unit
 * no op names stands as printed, and a unit an op replaces is an explicit change the referee judges;
 * only a statement unit replaced by blank TeX is gone. Pure.
 */
export function droppedUnitProblems(ops: readonly PatchOp[]): string[] {
  const runs = ops.flatMap((op) => (!op.tex.trim() && !isProofOp(op) ? [op.to && op.to !== op.unit ? `${op.unit} … ${op.to}` : op.unit] : []));
  return runs.length > 0
    ? [`deletes the printed statement's unit${runs.length > 1 ? "s" : ""} ${runs.join(", ")} — it replaces the printed statement, so it keeps every condition and conclusion the original states: give a unit whose content changes or moves as a \`replace\` (a run \`unit\` … \`to\` when content moves between units), never a deletion`]
    : [];
}

/** Why `corrected` is not a drop-in replacement for `original` (empty = it is), by exact checks only:
 * the statement units its ops delete (`droppedUnitProblems`). Pure. */
export function restatementProblems(_original: string, _corrected: string, opts: { ops?: readonly PatchOp[] } = {}): string[] {
  return droppedUnitProblems(opts.ops ?? []);
}

/** The texts of a repair the author reads (a patch, or a suggested repair's body). */
export interface RepairBody {
  corrected_statement?: string | null;
  /** The repair's operations on the paper's units (`ops.ts`). */
  ops?: ReadonlyArray<PatchOp>;
  proof_note?: string | null;
  /** The side conditions it states beside the statement. */
  conditions?: readonly string[] | null;
  /** The corollaries it splits off the result. */
  corollaries?: ReadonlyArray<{ statement: string; follows: string }> | null;
}

/**
 * Why the texts of a repair break the contract (empty = they do not), each problem naming its field:
 * the TeX of the corrected statement, each op's TeX and the proof note (`texMathProblems`); a result
 * environment the corrected statement, an op or a corollary's statement opens (`resultEnvProblems`;
 * `resultEnvs`: default the standard names); and the `explanation`: the note's exact contract
 * (`noteProblems`) and a `gives_up` a proof-only repair contradicts (`givesUpProblems`). Pure.
 */
export function repairTextProblems(body: RepairBody, explanation: unknown, ctx: { printed: string; proof: string; labelOf: (id: string) => string | null; note?: NoteContext; resultEnvs?: ReadonlySet<string> }): string[] {
  const out: string[] = [];
  const both = `${ctx.printed}\n${ctx.proof}`;
  const envs = ctx.resultEnvs ?? resultEnvNames();
  const inOps: string[] = [];
  if (body.corrected_statement?.trim()) out.push(...texMathProblems(body.corrected_statement, "corrected_statement", { reference: ctx.printed }));
  (body.ops ?? []).forEach((op, k) => {
    const tex = opTex(op);
    if (!tex) return;
    const reference = isProofOp(op) ? both : ctx.printed;
    out.push(...texMathProblems(tex, `ops[${k}] (${op.op})`, { reference }));
    inOps.push(...resultEnvProblems(tex, `ops[${k}] (${op.op})`, envs, reference));
  });
  // A corrected statement derived from the ops repeats theirs: named once, on the op.
  out.push(...(inOps.length > 0 ? inOps : resultEnvProblems(body.corrected_statement ?? "", "corrected_statement", envs, ctx.printed)));
  // With proof ops, the proof note is the printed proof as they amend it (`materializeReply`).
  const amended = revisesProof(body);
  if (body.proof_note?.trim()) out.push(...texMathProblems(body.proof_note, amended ? "amended proof (the printed proof with your proof ops applied: each op keeps math delimiters balanced)" : "proof_note", { reference: both }));
  (body.conditions ?? []).forEach((c, k) => out.push(...texMathProblems(c, `conditions[${k}]`, { reference: ctx.printed })));
  (body.corollaries ?? []).forEach((c, k) => {
    out.push(...texMathProblems(c.statement, `corollaries[${k}].statement`, { reference: ctx.printed }), ...texMathProblems(c.follows, `corollaries[${k}].follows`, { reference: both }));
    // The runner sets a corollary's heading: its `statement` is the text under it.
    out.push(...resultEnvProblems(c.statement, `corollaries[${k}].statement`, envs, ""));
  });
  if (explanation !== null && explanation !== undefined && explanation !== "") {
    out.push(...noteProblems(explanation, ctx.note).map((p) => `its owner_explanation ${p}`));
    if (isStructuredExplanation(explanation)) out.push(...givesUpProblems(explanation, body).map((p) => `its owner_explanation ${p}`));
  }
  return out;
}
