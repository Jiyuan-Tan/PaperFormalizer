/**
 * Model-text defects of a render go back to their producers (user rule 2026-09-25: "simple and
 * robust — fix the order and the classification").
 *
 * A model-written fragment of the annotated paper that fails its compile check (`render_check.ts`
 * `splitRenderDefects`: a render defect carrying `fragment`) is the MODEL's to write again, never the
 * renderer's. On every render the verify runner hands the failing fragments to `FragmentRouter.gate`,
 * which invalidates each at its producer and says whether the run goes on:
 *
 * - the symbol referee's reading / table fix, and the V1.5 referee's text (a reading, a bookkeeping
 *   condition): the symbol loses its cached verdict (`confirmed_symbols`), or the node
 *   its confirmation (and a paused pass's carry), and the next pass grades it afresh, the compiler's
 *   line in its prompt (`referee_symbols.ts`; `stage_v1_5.ts` `storedTexFeedback`);
 * - the fixer's text (a repair's statement, proof or note): the scoped fixer round (`weakening.ts`
 *   `restateAllPatches`) — opened here unless the invocation answers a halt, whose own flow runs it;
 * - a text no model of the run writes (the owner's words, the transcription's symbol name, an F-stage
 *   reviewer's reason): no pass is left to ask, so it is stuck at once.
 *
 * A symbol / referee fragment on a core accepted past V1.5 re-opens it (phase `v1`; the proposal
 * rounds voided by the caller), unless an owner or orchestrator decision is pending, or the F stages
 * already ran (a re-formalization is not bought for a TeX slip: it is a contract checkpoint).
 *
 * The verdict, per invocation: a fragment routed earlier whose producer has run a pass since and
 * still fails is STUCK → the contract checkpoint (distinct from the renderer checkpoint: the model
 * could not write it within its retries; the orchestrator reads the listed texts). Otherwise the run
 * CONTINUES into the producers' passes — at a resume always (its loop reaches them before the next
 * render), at a V1.5 pass end when every pending producer can run (else the contract checkpoint), at
 * the weakened-repair halt when one can (the symbol pass runs before the receipt checkpoint; the
 * fixer's round withdraws the receipt). At a patch-cap or rewind halt nothing can run before the
 * orchestrator answers: the halt is PRESENTED, the fragments listed (routed; the pass the answer opens
 * writes them again).
 */
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { STAGE_ORDER } from "../constants.js";
import type { StateJson } from "../types.js";
import { PRODUCER_LABEL, type FailedFragment, type FragmentProducer, type RenderDefect } from "./render_check.js";
import { VERIFY_FILES } from "./types.js";
import { DISPLAY_TOO_WIDE } from "./annotate_tex.js";

/** A render defect that is a model fragment failing its compile check. */
export type FragmentDefect = RenderDefect & { fragment: FailedFragment };

/** Where a render is checked: at the resume's re-render (`resume`), at a V1.5 pass end that the run
 * continues from (`pass`), at the weakened-repair halt (`weakening`), at another halt (`decision`: a
 * patch cap, a proposed rewind, a V1.5 checkpoint). */
export type RenderSite = "resume" | "pass" | "weakening" | "decision";

/** The producers a later pass of this run writes again. */
type Rerun = Extract<FragmentProducer, "symbol" | "referee" | "fixer">;
const RERUN: ReadonlySet<FragmentProducer> = new Set<FragmentProducer>(["symbol", "referee", "fixer"]);

export interface FragmentGate {
  /** `continue`: nothing is presented, the run goes on into the producers' passes; `present`: the
   * halt is presented with `pending` listed; `contract`: the contract checkpoint on `stuck`. */
  verdict: "continue" | "present" | "contract";
  stuck: FragmentDefect[];
  /** Routed (now or earlier in this invocation) and waiting for their producer's pass. */
  pending: FragmentDefect[];
  lines: string[];
}

export interface FragmentRouterContext {
  state: () => StateJson;
  runDir: string;
  /** The scoped fixer round (`restateAll`) with the repair texts that do not compile, by node: true
   * when it opened one. */
  restate: (when: string, compile: ReadonlyMap<string, ReadonlyArray<{ where: string; text: string; error: string }>>) => Promise<boolean>;
  /** A core accepted past V1.5 is re-opened (the caller takes the paper out of the papers barrel). */
  reopenAccepted: (reason: string) => Promise<void>;
  /** The invocation answers a halt: its own flow runs the fixer round, never a render. */
  answering: boolean;
}

/** The key a fragment is routed under: its producer, how it is set, its text. */
export const fragmentKey = (f: FailedFragment): string => `${f.producer}\u0000${f.kind}\u0000${f.text}`;

const ACCEPTED = new Set(["v1_5", "formalization"]);
/** The cursor is before F1: the F stages never ran on this core. */
const preF = (stage: string): boolean => STAGE_ORDER.indexOf(stage as (typeof STAGE_ORDER)[number]) < STAGE_ORDER.indexOf("1");

/** One invocation's routing of failing model fragments (see the module doc). */
export class FragmentRouter {
  private readonly passes: Record<Rerun, number> = { symbol: 0, referee: 0, fixer: 0 };
  private readonly routedAt = new Map<string, { at: number; producer: Rerun; defect: FragmentDefect }>();

  constructor(private readonly ctx: FragmentRouterContext) {}

  /** A stage ran: V1 answers the fixer's texts; V1.5 grades the symbol table, and the nodes unless it
   * stopped at a pending receipt (`gradedNodes`). */
  notePass(stage: "V1" | "V1.5", gradedNodes = true): void {
    if (stage === "V1") this.passes.fixer += 1;
    else {
      this.passes.symbol += 1;
      if (gradedNodes) this.passes.referee += 1;
    }
  }

  async gate(fragments: readonly FragmentDefect[], site: RenderSite): Promise<FragmentGate> {
    const stuck: FragmentDefect[] = [];
    const fresh: FragmentDefect[] = [];
    const waiting: FragmentDefect[] = [];
    for (const d of fragments) {
      const p = d.fragment.producer;
      // A too-wide display prints shrunk and is only reported: its producer's own check asks for rows
      // when it writes the text, so one here was written before that check (routing it would re-open
      // the review on every resume).
      if (d.fragment.error.startsWith(DISPLAY_TOO_WIDE)) continue;
      if (!RERUN.has(p)) {
        stuck.push(d);
        continue;
      }
      const r = this.routedAt.get(fragmentKey(d.fragment));
      if (r === undefined) fresh.push(d);
      else if (this.passes[r.producer] > r.at) stuck.push(d);
      else waiting.push(d);
    }
    const lines = this.route(fresh);
    // Routed earlier and not yet written again, though this render does not show it (a core rebuilt
    // without the symbol table's readings until V1.5 runs): still pending.
    const shown = new Set(fragments.map((d) => fragmentKey(d.fragment)));
    const unseen = [...this.routedAt].filter(([k, r]) => !shown.has(k) && this.passes[r.producer] === r.at).map(([, r]) => r.defect);
    const pending = [...fresh, ...waiting, ...unseen];
    if (stuck.length > 0) return { verdict: "contract", stuck, pending, lines };
    // At a halt the orchestrator answers, nothing is re-opened or opened: the answer's flow runs the pass.
    if (pending.length === 0 || site === "decision") return { verdict: "present", stuck, pending, lines };
    const reach = await this.reachable(pending, lines);
    const all = pending.every((d) => reach.has(d.fragment.producer));
    const some = pending.some((d) => reach.has(d.fragment.producer));
    switch (site) {
      case "resume":
        return { verdict: "continue", stuck, pending, lines };
      case "pass":
        return all ? { verdict: "continue", stuck, pending, lines } : { verdict: "contract", stuck: pending.filter((d) => !reach.has(d.fragment.producer)), pending, lines };
      case "weakening":
        return { verdict: some ? "continue" : "present", stuck, pending, lines };
    }
  }

  /** Invalidate each fresh fragment at its producer; log lines. */
  private route(fresh: readonly FragmentDefect[]): string[] {
    const verify = this.ctx.state().verify!;
    const by = new Map<Rerun, Set<string>>();
    for (const d of fresh) {
      const p = d.fragment.producer as Rerun;
      this.routedAt.set(fragmentKey(d.fragment), { at: this.passes[p], producer: p, defect: d });
      const target = p === "fixer" ? (d.node ?? "?") : (d.fragment.ref ?? d.node ?? "?");
      (by.get(p) ?? by.set(p, new Set()).get(p)!).add(target);
      if (p === "symbol" && verify.confirmed_symbols) delete verify.confirmed_symbols[target];
      if (p === "referee") {
        if (verify.confirmed) delete verify.confirmed[target];
        if (verify.level_pause?.carry) delete verify.level_pause.carry[target];
      }
    }
    return [...by].map(([p, ts]) => `${fresh.filter((d) => d.fragment.producer === p).length} fragment(s) of ${PRODUCER_LABEL[p]} do not compile — routed back (${[...ts].join(", ")})`);
  }

  /** The producers whose pass the run reaches from here, after re-opening an accepted core and
   * opening the fixer round where that is allowed. */
  private async reachable(pending: readonly FragmentDefect[], lines: string[]): Promise<Set<FragmentProducer>> {
    const state = this.ctx.state();
    const verify = state.verify!;
    const cap = !!verify.cap_reached;
    const rewind = verify.cross_stage_rewind?.status === "pending";
    // A receipt its confirming V1.5 pass has not settled leaves the node grading reachable.
    const weak = verify.weakening_repair?.status === "pending" && !verify.weakening_repair.unconfirmed;
    const need = new Set(pending.map((d) => d.fragment.producer));
    if ((need.has("symbol") || need.has("referee")) && !cap && !rewind && !weak) {
      if ((ACCEPTED.has(verify.phase) || verify.phase === "v6") && preF(state.stage_completed)) {
        verify.core_sha256 = null;
        verify.phase = "v1";
        state.stage_completed = "V1";
        lines.push("the core is re-opened for a V1.5 pass: model texts on file do not compile");
        await this.ctx.reopenAccepted("model texts on file do not compile: the next V1.5 pass writes them again");
      }
    }
    if (need.has("fixer") && !this.ctx.answering && !cap && !rewind) {
      const compile = new Map<string, Array<{ where: string; text: string; error: string }>>();
      for (const d of pending) {
        if (d.fragment.producer !== "fixer" || !d.node) continue;
        (compile.get(d.node) ?? compile.set(d.node, []).get(d.node)!).push({ where: `the ${d.block} the paper prints for "${d.node}"`, text: d.fragment.text, error: d.fragment.error });
      }
      if (await this.ctx.restate("render check", compile)) lines.push("the fixer's texts that do not compile go back to it in a scoped round");
    }
    const v15 = !cap && !rewind && (verify.phase === "init" || verify.phase === "v1");
    const out = new Set<FragmentProducer>();
    if (v15) out.add("symbol");
    if (v15 && !weak) out.add("referee");
    // Only a patch directive runs the fixer (a revise directive runs the transcriber).
    const directive = path.join(this.ctx.runDir, VERIFY_FILES.v1ReviseDirective);
    if (verify.phase === "init" && existsSync(directive) && (JSON.parse(readFileSync(directive, "utf8")) as { mode?: string }).mode === "patch") out.add("fixer");
    return out;
  }
}
