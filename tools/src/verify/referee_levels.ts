/**
 * DEPENDENCY ORDER of the sharded V1.5 referee (`referee_shards.ts`): the leaves are graded first and
 * the root last, and each result is judged under the final grades of the results it uses.
 *
 *   • LEVELS (`refereeLevels`). Over the nodes to grade (a carried verdict counts as graded):
 *     level 0 = the definitions and assumptions; level 1 = the statements that rest on no statement
 *     still to grade; level k = the statements resting only on statements below k. A statement RESTS
 *     on one still to grade when it uses it directly or through carried results (`gradedBelow`): a
 *     verdict graded below may re-open the carried verdicts between them (`referee_shards.ts`, the
 *     chain), and those are graded before what uses them. A dependency cycle (the structural gate
 *     forbids one) is logged and its members share one level (the strongly connected components are
 *     levelled, not the nodes).
 *   • DEPENDENCY VERDICTS (`dependencyVerdicts`). A node graded at level k is shown, for every
 *     statement it depends on, that statement's final verdict — carried, or settled at a lower level.
 *   • THE RULE ON AN ERRORED DEPENDENCY (`settleOnErroredDependencies`). A result using a statement
 *     graded `error` with no confirmed repair is not reproduced: its correctness is `unclear`, with
 *     the detail "depends on <id>, graded error" (a grade of its own that is `unclear` or `error`
 *     stands). The referee is told the same; the runner enforces it. Since fix as you go
 *     (`stage_v1_5.ts`) a repairable error pauses the grading before any level above it, so this rule
 *     is the fallback for an error nobody repairs (withdrawn, declined, unfixable).
 */
import type { Core } from "../core/schema.js";
import type { V15NodeVerdict } from "./types.js";

export interface RefereeLevels {
  /** `levels[k]` = the nodes graded at level k, in the order they were given (empty levels kept). */
  levels: string[][];
  /** Dependency cycles among the statements to grade, each one level. Empty on a well-formed core. */
  cycles: string[][];
}

/**
 * Per statement to grade (`grade`), the statements to grade it RESTS on: those it reaches through
 * `depends_on` — directly, or through statements not to grade (carried) — stopping at the first one
 * to grade on each path (what lies below that one is its own). A result is a statement (`thm:` /
 * `lem:` / `prop:` / … — any node of `core.statements`).
 */
export function gradedBelow(core: Core, grade: ReadonlySet<string>): Map<string, string[]> {
  const stmts = new Map(core.statements.map((s) => [s.id, s] as const));
  const out = new Map<string, string[]>();
  for (const s of core.statements) {
    if (!grade.has(s.id)) continue;
    const found = new Set<string>();
    const seen = new Set<string>([s.id]);
    const stack = [...s.depends_on];
    while (stack.length > 0) {
      const d = stack.pop()!;
      // A statement that uses itself is a cycle of one (reported as such).
      if (d === s.id && s.depends_on.includes(d)) found.add(d);
      if (seen.has(d) || !stmts.has(d)) continue;
      seen.add(d);
      if (grade.has(d)) found.add(d);
      else stack.push(...stmts.get(d)!.depends_on);
    }
    out.set(s.id, [...found]);
  }
  return out;
}

/** The levels the nodes to grade are graded in (see the module comment). */
export function refereeLevels(core: Core, toGrade: readonly string[]): RefereeLevels {
  const grade = new Set(toGrade);
  const deps = gradedBelow(core, grade);
  // Tarjan's strongly connected components over the statements to grade.
  const index = new Map<string, number>();
  const low = new Map<string, number>();
  const onStack = new Set<string>();
  const stack: string[] = [];
  const comp = new Map<string, number>();
  const comps: string[][] = [];
  let next = 0;
  const visit = (v: string): void => {
    index.set(v, next);
    low.set(v, next);
    next += 1;
    stack.push(v);
    onStack.add(v);
    for (const w of deps.get(v) ?? []) {
      if (!index.has(w)) {
        visit(w);
        low.set(v, Math.min(low.get(v)!, low.get(w)!));
      } else if (onStack.has(w)) low.set(v, Math.min(low.get(v)!, index.get(w)!));
    }
    if (low.get(v) === index.get(v)) {
      const c: string[] = [];
      let w: string;
      do {
        w = stack.pop()!;
        onStack.delete(w);
        comp.set(w, comps.length);
        c.push(w);
      } while (w !== v);
      comps.push(c);
    }
  };
  for (const v of deps.keys()) if (!index.has(v)) visit(v);
  // Tarjan emits a component after every component it depends on: level them in emission order.
  const compLevel: number[] = [];
  comps.forEach((c, i) => {
    let lv = 1;
    for (const v of c) for (const d of deps.get(v)!) if (comp.get(d) !== i) lv = Math.max(lv, compLevel[comp.get(d)!]! + 1);
    compLevel[i] = lv;
  });
  const cycles = comps.filter((c) => c.length > 1 || deps.get(c[0]!)!.includes(c[0]!)).map((c) => toGrade.filter((id) => c.includes(id)));
  const levelOf = (id: string): number => (deps.has(id) ? compLevel[comp.get(id)!]! : 0);
  const top = Math.max(0, ...toGrade.map(levelOf));
  const levels: string[][] = Array.from({ length: toGrade.length > 0 ? top + 1 : 0 }, () => []);
  for (const id of toGrade) levels[levelOf(id)]!.push(id);
  return { levels, cycles };
}

/** A statement's final verdict as the results using it are shown it. */
export interface DependencyVerdict {
  id: string;
  kind: string;
  verdict: V15NodeVerdict;
  /** A repair of the node on file (the node's text in the core is its corrected form) and what the
   * printed statement got wrong (`state.verify.paper_errors`). Confirmed only when the verdict does
   * not refute it (`repairConfirmed`). */
  repair: { corrected: string; printedError: string | null } | null;
}

/** A refuting `error`: not a grade on a repair's minimality or on whether it weakens the claim. */
export const refutes = (v: V15NodeVerdict): boolean => v.correctness === "error" && v.minimality !== true && v.weakens_contribution !== true;

/** The repair on file is confirmed: the current grade of the corrected form is clean, or an `error`
 * only on its minimality / weakening (the corrected form holds). */
export function repairConfirmed(d: DependencyVerdict): boolean {
  if (!d.repair) return false;
  const v = d.verdict;
  return v.correctness === "ok" || v.correctness === "bookkeeping" || (v.correctness === "error" && !refutes(v));
}

/** For a node, the final verdicts of the statements it depends on that are known (`final`), in
 * `depends_on` order. `repairOf` gives a repair on file, if any. */
export function dependencyVerdicts(
  core: Core,
  id: string,
  final: ReadonlyMap<string, V15NodeVerdict>,
  repairOf: (id: string) => DependencyVerdict["repair"] = () => null,
): DependencyVerdict[] {
  const byId = new Map(core.statements.map((s) => [s.id, s] as const));
  const node = [...core.statements, ...core.assumptions, ...core.definitions].find((n) => n.id === id) as { depends_on?: string[] } | undefined;
  const out: DependencyVerdict[] = [];
  for (const d of new Set(node?.depends_on ?? [])) {
    const st = byId.get(d);
    const v = final.get(d);
    if (!st || !v || d === id) continue;
    out.push({ id: d, kind: String(st.kind ?? "statement"), verdict: v, repair: repairOf(d) });
  }
  return out;
}

/** The dependencies that stop a node's own correctness: graded `error` (refuting), no confirmed repair. */
export function erroredDependencies(deps: readonly DependencyVerdict[]): string[] {
  return deps.filter((d) => refutes(d.verdict) && !repairConfirmed(d)).map((d) => d.id);
}

/**
 * The rule on an errored dependency, enforced by the runner: a node graded `ok` or `bookkeeping`
 * that uses a statement graded `error` (no confirmed repair) becomes `unclear` with the detail
 * "depends on <id>, graded error". A grade of its own that is `unclear` or `error` stands (an
 * `unclear` gains the note). Returns the node unchanged when no dependency is errored.
 */
export function settleOnErroredDependencies(n: V15NodeVerdict, deps: readonly DependencyVerdict[]): { verdict: V15NodeVerdict; on: string[] } {
  const on = erroredDependencies(deps);
  if (on.length === 0 || n.correctness === "error") return { verdict: n, on: n.correctness === "error" ? [] : on };
  const note = on.map((d) => `depends on ${d}, graded error`).join("; ");
  if (n.detail.includes(note)) return { verdict: n, on: [] };
  return {
    verdict: { ...n, correctness: "unclear", bookkeeping_assumption: null, detail: `${note}. ${n.detail}`.trim() },
    on,
  };
}
