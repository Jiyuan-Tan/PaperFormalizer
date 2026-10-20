// The deterministic plan gate as F1 and F1.5 run it on the plan on disk (hygiene included) — with the library
// index ∪ the toolkit ledger ∪ the toolkit's scanned declarations as the known decls — memoized
// on the plan and the core: F1's self-check and F1.5's pre-lint run it back to back on the same
// two files, and the toolkit declaration scan behind `knownDeclsForContext` is the slow part.

import type { Core } from "../../core/schema.js";
import type { ToolkitConfig } from "../../toolkit/config.js";
import { knownDeclsForContext } from "../known_decls.js";
import { runPlanGate, type PlanGateResult } from "./plan_gate.js";

let last: { root: string; plan: string; core: string; result: PlanGateResult } | null = null;

/** The gate's verdict on `planObj` (the parsed plan at `planPath`) against `core` (parsed from
 *  `coreText`), reused when both are what the previous call saw. */
export function planGateOnDisk(
  ctx: { repoRoot: string; toolkit?: ToolkitConfig },
  input: { planObj: unknown; coreText: string; core: Core },
): PlanGateResult {
  const plan = JSON.stringify(input.planObj);
  if (last && last.root === ctx.repoRoot && last.plan === plan && last.core === input.coreText) return last.result;
  const knownDecls = knownDeclsForContext(ctx);
  if (!knownDecls) {
    console.warn(
      "[leansmith] no library index loaded — the P5 reuse-existence check is SKIPPED this pass; hallucinated reuse decls will surface only at compile.",
    );
  }
  const result = runPlanGate(input.planObj, input.core, { knownDecls: knownDecls?.names, ownedDeclPrefixes: knownDecls?.ownedPrefixes, hygiene: true });
  last = { root: ctx.repoRoot, plan, core: input.coreText, result };
  return result;
}
