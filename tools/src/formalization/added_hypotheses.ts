// Hypotheses added to a paper statement's Lean signature since the reviewer last passed it.
//
// Why: the frozen-statement guard compares paper text only, and a binder the proof filler (or a
// re-scaffold) adds to a paper theorem/lemma reached the reviewer only as part of the whole
// statement — caught when the filler disclosed it AND the reviewer noticed it. The runner now
// records each paper result's binders when it passes review (`passed_binders` on the node), diffs
// the current binders against them at the next review, and names every new one in the target block
// next to what the filler disclosed for that result, so no added hypothesis is judged by omission.

import type { FormalizationGraph, GraphNode } from "../graph/types.js";
import { statementBinders } from "./unused_hypothesis_lint.js";

/** A paper (`from-note`) theorem or lemma — the statements whose binders are tracked. */
export function tracksBinders(n: Pick<GraphNode, "kind" | "provenance">): boolean {
  return n.provenance === "from-note" && (n.kind === "theorem" || n.kind === "lemma");
}

/** The binders of `declText` absent from the node's last passed signature; `[]` with no record
 *  (a first review judges the whole statement anyway). */
export function addedBinders(n: Pick<GraphNode, "passed_binders">, declText: string): string[] {
  if (!n.passed_binders) return [];
  const before = new Set(n.passed_binders);
  return statementBinders(declText).filter((b) => !before.has(b));
}

/** The assumptions an agent disclosed for `nodeId` (agent-introduced, wired from it). */
export function disclosedAssumptions(graph: FormalizationGraph, nodeId: string): GraphNode[] {
  const wired = new Set(graph.edges.filter((e) => e.from === nodeId && (e.kind === "proof-uses" || e.kind === "statement-uses")).map((e) => e.to));
  return graph.nodes.filter((n) => wired.has(n.id) && n.kind === "assumption" && n.provenance === "agent-introduced");
}

/** The reviewer's block naming each added binder; "" when none was added. */
export function addedHypothesesBlock(added: string[], disclosed: GraphNode[]): string {
  if (added.length === 0) return "";
  return [
    "",
    "HYPOTHESES ADDED SINCE THIS STATEMENT LAST PASSED REVIEW (a mechanical diff of its Lean binders):",
    ...added.map((b) => `  • ${b}`),
    disclosed.length
      ? "Disclosed for this result by the agent that edited it:\n" +
        disclosed.map((d) => `  • ${d.id} (${d.assumption?.classification ?? "unclassified"}): ${d.nl.statement}`).join("\n")
      : "None of them was disclosed.",
    "Judge each added binder by the rule on an extra hypothesis and name it in your note; one the paper does not state or entail is `drift`, disclosed or not.",
  ].join("\n");
}

/** Record the current binders of every tracked node the reviewer just passed (`matched`). */
export function recordPassedBinders(graph: FormalizationGraph, declTextById: ReadonlyMap<string, string>): FormalizationGraph {
  return {
    ...graph,
    nodes: graph.nodes.map((n) =>
      tracksBinders(n) && n.review.status === "matched" && declTextById.has(n.id)
        ? { ...n, passed_binders: statementBinders(declTextById.get(n.id)!) }
        : n,
    ),
  };
}
