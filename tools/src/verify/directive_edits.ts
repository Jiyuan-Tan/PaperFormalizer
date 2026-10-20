/**
 * Mechanical drift fixes — the runner applies what the referee can state as an edit.
 *
 * Every wave-4 hand-patch was a drift finding whose correction is a small, unambiguous edit
 * of the reference core: add or drop a dependency, wire an assumption or definition into a result
 * or out of it, extend a slice to the next sentence, add a premise the paper states in one sentence. The V1 agent, told to make such an edit, often did not.
 * So the referee states the edit as data (`fix` on a `drift` node) and the runner applies it
 * to `discovery/core_refs.json` itself before any agent round. Findings without a `fix`, and
 * fixes the runner cannot apply (unknown ids, anchors that do not cut — reported by the
 * materializer afterwards), still go to the agent as prose.
 *
 * The edits touch only STRUCTURE (slices, wiring); the text keeps coming from the source through
 * the materializer, so the verbatim contract is untouched.
 */
import { z } from "zod";

const Ids = z.array(z.string().min(1));
/** An optional prose edit. The strict reply schema (below) types it `string | null` and cannot say
 * "non-empty": an empty string is the same answer as null — no edit — and is read as one. */
const NullableProse = z.string().nullable().optional().transform((v) => (v != null && v.trim() === "" ? null : v));

export const DriftFixSchema = z.object({
  /** node ids the statement must also depend on (assumption ids join `hypotheses` too) */
  add_depends_on: Ids.nullable().optional(),
  /** node ids the statement must not depend on */
  remove_depends_on: Ids.nullable().optional(),
  /** on an assumption or definition: the statements that must use it / must not use it */
  wire_into: Ids.nullable().optional(),
  unwire_from: Ids.nullable().optional(),
  /** for an assumption/definition whose slice ends too early: the new `to` anchor */
  extend_to: NullableProse,
  /** the node's setting, as the core's `sampling_model` should state it (what is random, what is
   * fixed, the law): a transcription defect, so it goes to V1 even on a repaired node. Prose for the
   * transcriber, never applied by the runner. */
  setting: NullableProse,
  /** Runner-written, never asked of a referee: an edit of a second fix on the node that could not be
   * merged with the first (two different `extend_to` phrases, two new assumptions) — prose for the
   * transcriber, like `setting`. */
  also: z.string().min(1).nullable().optional(),
  /** a premise the paper states that no node carries: a new assumption node, wired in */
  new_assumption: z
    .object({
      id: z.string().regex(/^ass:[a-z0-9-]+$/),
      /** environment id holding the sentence; null/absent = running text */
      env: z.string().min(1).nullable().optional(),
      from: z.string().min(1),
      to: z.string().min(1),
      wire_into: Ids,
    })
    .nullable()
    .optional(),
});
export type DriftFix = z.infer<typeof DriftFixSchema>;

/** Strict JSON Schema for `fix` (codex `--output-schema`: every property required, nullable). */
export const DRIFT_FIX_JSON_SCHEMA: Record<string, unknown> = {
  anyOf: [
    {
      type: "object",
      additionalProperties: false,
      required: ["add_depends_on", "remove_depends_on", "wire_into", "unwire_from", "extend_to", "new_assumption", "setting"],
      properties: {
        setting: { type: ["string", "null"] },
        add_depends_on: { type: ["array", "null"], items: { type: "string" } },
        remove_depends_on: { type: ["array", "null"], items: { type: "string" } },
        wire_into: { type: ["array", "null"], items: { type: "string" } },
        unwire_from: { type: ["array", "null"], items: { type: "string" } },
        extend_to: { type: ["string", "null"] },
        new_assumption: {
          anyOf: [
            {
              type: "object",
              additionalProperties: false,
              required: ["id", "env", "from", "to", "wire_into"],
              properties: {
                id: { type: "string" },
                env: { type: ["string", "null"] },
                from: { type: "string" },
                to: { type: "string" },
                wire_into: { type: "array", items: { type: "string" } },
              },
            },
            { type: "null" },
          ],
        },
      },
    },
    { type: "null" },
  ],
};

/** The parts of a reference core these edits touch (the rest is carried through untouched). */
interface RefNodeLike {
  id: string;
  depends_on?: string[];
  hypotheses?: string[];
  source?: { env?: string; prose?: boolean; slice?: { from: string; to: string }; sentences?: [number, number] };
  [k: string]: unknown;
}
interface RefCoreLike {
  statements: RefNodeLike[];
  assumptions: RefNodeLike[];
  definitions: RefNodeLike[];
  [k: string]: unknown;
}

export interface DriftFixOutcome {
  refs: RefCoreLike;
  /** finding ids whose fix was applied in full */
  applied: string[];
  /** finding ids whose fix could not be applied, with the reason */
  rejected: Array<{ id: string; reason: string }>;
  /** one line per change, for the log and the referee's warning list */
  notes: string[];
}

/** Does `fix` carry any edit at all? (A referee may emit the object with every field null.) */
export function hasDriftFix(fix: DriftFix | null | undefined): fix is DriftFix {
  if (!fix) return false;
  return Boolean(
    fix.add_depends_on?.length || fix.remove_depends_on?.length || fix.wire_into?.length || fix.unwire_from?.length || fix.extend_to || fix.new_assumption,
  );
}

/** Every node id of a reference core, with its multiplicity. */
function idCounts(refs: RefCoreLike): Map<string, number> {
  const m = new Map<string, number>();
  for (const n of [...(refs.statements ?? []), ...(refs.assumptions ?? []), ...(refs.definitions ?? [])]) m.set(n.id, (m.get(n.id) ?? 0) + 1);
  return m;
}

/**
 * The structural invariant of a reference core that every runner edit must keep: no id names
 * two records, and every `depends_on` / `hypotheses` entry names a node of the core.
 */
export function refCoreViolations(refs: RefCoreLike): string[] {
  const counts = idCounts(refs);
  const out: string[] = [];
  for (const [id, n] of counts) if (n > 1) out.push(`duplicate node id ${id} (${n} records)`);
  for (const s of [...(refs.statements ?? []), ...(refs.assumptions ?? []), ...(refs.definitions ?? [])]) {
    for (const d of s.depends_on ?? []) if (!counts.has(d)) out.push(`${s.id}: depends_on names no node: ${d}`);
    for (const h of s.hypotheses ?? []) if (!counts.has(h)) out.push(`${s.id}: hypotheses names no node: ${h}`);
  }
  return out;
}

/** The invariant violations `after` has that `before` did not (a violation already on file is
 * not the edit's doing, and is left to the materializer's gate and the agent). */
export function newRefCoreViolations(before: RefCoreLike, after: RefCoreLike): string[] {
  const had = new Set(refCoreViolations(before));
  return [...new Set(refCoreViolations(after))].filter((v) => !had.has(v));
}

/** Throw at the fix site when a runner-applied edit broke the core's invariant (the per-finding
 * check in `applyDriftFixes` refuses such an edit; this is the guard around the whole write). */
export function assertFixKeepsRefCoreValid(before: RefCoreLike, after: RefCoreLike, where: string): void {
  const introduced = newRefCoreViolations(before, after);
  if (introduced.length > 0) {
    throw new Error(`${where}: a runner-applied referee fix would write an invalid reference core — not written:\n` + introduced.map((v) => `  - ${v}`).join("\n"));
  }
}

/**
 * Apply the referee's mechanical fixes to a reference core. Pure: returns a new core. A
 * finding is `applied` only when every edit in its fix went through; otherwise it is
 * `rejected` with the first reason and the core is left as it was for that finding.
 */
export function applyDriftFixes(
  refsIn: RefCoreLike,
  findings: ReadonlyArray<{ id: string; fix: DriftFix }>,
  /** `reapply`: the call re-applies fixes after an agent round: a wiring fix already in place
   * is kept as applied, not rejected. */
  opts: { reapply?: boolean } = {},
): DriftFixOutcome {
  let refs: RefCoreLike = structuredClone(refsIn);
  const applied: string[] = [];
  const rejected: Array<{ id: string; reason: string }> = [];
  const notes: string[] = [];

  for (const f of findings) {
    const work = structuredClone(refs);
    const allIds = new Set([...work.statements, ...work.assumptions, ...work.definitions].map((n) => n.id));
    const isAss = (id: string): boolean => work.assumptions.some((a) => a.id === id);
    const statement = work.statements.find((n) => n.id === f.id);
    const adNode = work.assumptions.find((n) => n.id === f.id) ?? work.definitions.find((n) => n.id === f.id);
    const fail = (reason: string): void => {
      rejected.push({ id: f.id, reason });
    };
    const local: string[] = [];
    try {
      const fx = f.fix;
      if (fx.new_assumption) {
        const na = fx.new_assumption;
        // an id that already exists is the same fix re-issued (the referee repeats itself when
        // the agent's round dropped the wiring): keep the node, restore the wiring
        if (allIds.has(na.id) && !work.assumptions.some((a) => a.id === na.id)) throw new Error(`new_assumption id ${na.id} names a non-assumption node`);
        for (const w of na.wire_into) if (!work.statements.some((s) => s.id === w)) throw new Error(`wire_into names no statement: ${w}`);
        // An environment named by the id of the node it holds is that node's environment.
        const holder = na.env ? [...work.statements, ...work.assumptions, ...work.definitions].find((n) => n.id === na.env) : undefined;
        const env = (holder && ((holder as { env?: string }).env ?? holder.source?.env)) || na.env;
        if (!work.assumptions.some((a) => a.id === na.id)) work.assumptions.push({
          id: na.id,
          kind: "premise",
          source: env ? { env, slice: { from: na.from, to: na.to } } : { prose: true, slice: { from: na.from, to: na.to } },
          free_symbols: [],
          novel: { flag: true, justification: "a premise the paper states that no node carried (referee fix)" },
        });
        for (const w of na.wire_into) {
          const s = work.statements.find((x) => x.id === w)!;
          s.depends_on = [...new Set([...(s.depends_on ?? []), na.id])];
          s.hypotheses = [...new Set([...(s.hypotheses ?? []), na.id])];
        }
        local.push(`${f.id}: added ${na.id} (${env ? `slice of ${env}` : "prose"}) and wired it into ${na.wire_into.join(", ")}`);
      }
      if (fx.add_depends_on?.length || fx.remove_depends_on?.length) {
        // Only a statement has dependencies: the edges an assumption or definition's cross-reference
        // asks for are added to each statement using it (directly, or through a class definition that
        // carves it). Nothing is removed there: a user may cite the node itself.
        if (!statement && fx.remove_depends_on?.length) throw new Error(`${f.id} is not a statement node: it has no dependencies to remove`);
        // The edge to an inline cited leaf is the materializer's (`proof_citations`): dropped here, it
        // would come back with the next materialization and the finding would count as answered.
        const inline = (fx.remove_depends_on ?? []).filter((d) => ((work.proof_citations as Array<{ id?: string }> | undefined) ?? []).some((c) => c.id === d));
        if (inline.length > 0) throw new Error(`${inline.join(", ")} is a \`proof_citations\` entry, whose edge is not an edit: when the proof does not rely on the cited result, move its site to \`dismissed_citations\``);
        // Only hypotheses carry over to the users: a fix on a hypothesis naming a RESULT could mean
        // either direction (the users need that result, or that result needs this hypothesis).
        const results = statement ? [] : (fx.add_depends_on ?? []).filter((d) => work.statements.some((x) => x.id === d));
        if (results.length > 0) throw new Error(`${f.id} is not a statement node, and the fix names results (${results.join(", ")}): which result depends on which is for the transcriber`);
        const carvedBy = new Set(work.definitions.filter((d) => ((d as { by_member_properties?: string[] }).by_member_properties ?? []).includes(f.id)).map((d) => d.id));
        const targets = statement ? [statement] : work.statements.filter((s) => (s.depends_on ?? []).some((d) => d === f.id || carvedBy.has(d)));
        if (targets.length === 0) throw new Error(`${f.id} is not a statement node, and no statement uses it`);
        // Nothing to add is no edit: the finding goes to the agent with why.
        if (!statement && targets.every((t) => (fx.add_depends_on ?? []).every((d) => d === t.id || (t.depends_on ?? []).includes(d)))) {
          // Re-applied after an agent round, a fix already in place is kept, not failed.
          if (opts.reapply) local.push(`${f.id}: already in place`);
          else throw new Error(`every statement using ${f.id} (${targets.map((t) => t.id).join(", ")}) already depends on ${(fx.add_depends_on ?? []).join(", ")} — nothing to add`);
        }
        // An edge closing a cycle (the dependency already reaches the statement) is left out.
        const reaches = (from: string, to: string): boolean => {
          const seen = new Set<string>();
          const stack = [from];
          while (stack.length > 0) {
            const id = stack.pop()!;
            if (id === to) return true;
            if (seen.has(id)) continue;
            seen.add(id);
            stack.push(...(work.statements.find((s) => s.id === id)?.depends_on ?? []));
          }
          return false;
        };
        for (const t of targets) {
          for (const d of fx.add_depends_on ?? []) {
            if (!statement && reaches(d, t.id)) continue;
            if (!allIds.has(d) && !work.assumptions.some((a) => a.id === d)) throw new Error(`add_depends_on names no node: ${d}`);
            if (d === t.id) {
              if (statement) throw new Error(`a node cannot depend on itself`);
              continue; // a user of the node named in the fix: it does not depend on itself
            }
            t.depends_on = [...new Set([...(t.depends_on ?? []), d])];
            // a printed hypothesis of the statement only where the node itself is one
            if (isAss(d) && (statement || (t.hypotheses ?? []).includes(f.id))) t.hypotheses = [...new Set([...(t.hypotheses ?? []), d])];
          }
          for (const d of fx.remove_depends_on ?? []) {
            t.depends_on = (t.depends_on ?? []).filter((x) => x !== d);
            t.hypotheses = (t.hypotheses ?? []).filter((x) => x !== d);
          }
        }
        const change = `depends_on ${fx.add_depends_on?.length ? `+ ${fx.add_depends_on.join(", ")}` : ""}${fx.remove_depends_on?.length ? ` − ${fx.remove_depends_on.join(", ")}` : ""}`.trim();
        local.push(statement ? `${f.id}: ${change}` : `${f.id} (used by ${targets.map((t) => t.id).join(", ")}): ${change} on each`);
      }
      if (fx.wire_into?.length || fx.unwire_from?.length) {
        // The edges between this assumption or definition and the results using it.
        if (!adNode) throw new Error(`${f.id} is not an assumption/definition node: a result's own dependencies are add_depends_on / remove_depends_on`);
        for (const w of [...(fx.wire_into ?? []), ...(fx.unwire_from ?? [])]) if (!work.statements.some((s) => s.id === w)) throw new Error(`wire_into / unwire_from names no statement: ${w}`);
        const uses = (w: string): boolean => (work.statements.find((x) => x.id === w)!.depends_on ?? []).includes(f.id);
        // Nothing to change is no edit: the finding goes to the agent with why.
        if ((fx.wire_into ?? []).every(uses) && !(fx.unwire_from ?? []).some(uses)) {
          if (opts.reapply) local.push(`${f.id}: already in place`);
          else throw new Error(`the wiring of ${f.id} already is as the fix states — nothing to change`);
        }
        for (const w of fx.wire_into ?? []) {
          const s = work.statements.find((x) => x.id === w)!;
          s.depends_on = [...new Set([...(s.depends_on ?? []), f.id])];
          if (isAss(f.id)) s.hypotheses = [...new Set([...(s.hypotheses ?? []), f.id])];
        }
        for (const w of fx.unwire_from ?? []) {
          const s = work.statements.find((x) => x.id === w)!;
          s.depends_on = (s.depends_on ?? []).filter((x) => x !== f.id);
          s.hypotheses = (s.hypotheses ?? []).filter((x) => x !== f.id);
        }
        local.push(`${f.id}:${fx.wire_into?.length ? ` wired into ${fx.wire_into.join(", ")}` : ""}${fx.unwire_from?.length ? ` unwired from ${fx.unwire_from.join(", ")}` : ""}`);
      }
      if (fx.extend_to) {
        if (!adNode) throw new Error(`${f.id} is not an assumption/definition node`);
        if (!adNode.source?.slice) throw new Error(`${f.id} has no anchor slice to extend (its source is a whole environment or sentences)`);
        adNode.source.slice = { ...adNode.source.slice, to: fx.extend_to };
        local.push(`${f.id}: slice extended to "${fx.extend_to.slice(0, 50)}"`);
      }
      if (local.length === 0) throw new Error("the fix carries no edit");
      // A fix may never leave the core worse-formed than it found it: every consumer keys
      // nodes by id, and the agent cannot repair a violation the runner re-creates each round.
      const introduced = newRefCoreViolations(refs, work);
      if (introduced.length > 0) throw new Error(`refused — the edit would leave an invalid core: ${introduced.join("; ")}`);
      refs = work;
      applied.push(f.id);
      notes.push(...local.map((l) => `referee fix applied — ${l}`));
    } catch (err) {
      fail(err instanceof Error ? err.message : String(err));
    }
  }
  return { refs, applied, rejected, notes };
}
