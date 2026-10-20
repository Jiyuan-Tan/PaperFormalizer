// The checker: a SECOND, independent schema-constrained codex call over the proposed items only.
// It re-judges what the curator decided — whether the entry's words say what they must (exactly
// what the Lean proves for a `move`, a general form of it for a `generalize`, what the cited work
// states for a cited result), whether the result already exists, and whether its division and
// home are right. A
// duplicate is declined automatically (the entry becomes a `skip` naming the existing declaration);
// any other disagreement is recorded on the proposal (`checker`) and shown to the owner.
import type { runCodex as RunCodex } from "../shared/codex.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { effectiveTaxonomy, taxonomyPromptText } from "../toolkit/taxonomy.js";
import { askJson, codexAsker, groundCandidates, listToolkitModules, readProposalPrompt, recordPrompt, section, type ProposalCandidate } from "./curator.js";
import type { Proposal, ProposalRound } from "./schema.js";

export interface CheckerReview { proposal_id: string; agrees: boolean; content_matches: boolean; duplicate_of: string | null; note: string }

export const CHECKER_REPLY: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: ["reviews"],
  properties: {
    reviews: {
      type: "array",
      items: {
        type: "object",
        additionalProperties: false,
        required: ["proposal_id", "agrees", "content_matches", "duplicate_of", "note"],
        properties: {
          proposal_id: { type: "string" },
          agrees: { type: "boolean" },
          content_matches: { type: "boolean" },
          duplicate_of: { type: ["string", "null"] },
          note: { type: "string" },
        },
      },
    },
  },
};

export function checkerViolations(reviews: readonly CheckerReview[], proposed: readonly Proposal[]): string[] {
  const ids = new Set(proposed.map((p) => p.id));
  const seen = new Set<string>();
  const v: string[] = [];
  for (const r of reviews) {
    if (!ids.has(r.proposal_id)) v.push(`review ${r.proposal_id}: not a proposed id.`);
    if (seen.has(r.proposal_id)) v.push(`review ${r.proposal_id}: given twice.`);
    if (r.note.trim() === "") v.push(`review ${r.proposal_id}: the note is empty.`);
    seen.add(r.proposal_id);
  }
  for (const id of ids) if (!seen.has(id)) v.push(`proposal ${id} was not reviewed.`);
  return v;
}

/**
 * Re-judge the proposed items of a batch; returns the batch with `checker` set on every proposed
 * item. `candidates` are the round's candidates, re-searched so the checker sees the same
 * grounding without the curator's verdicts.
 */
export async function runChecker(args: {
  toolkit: ToolkitConfig;
  slug: string;
  proposals: readonly Proposal[];
  candidates: readonly ProposalCandidate[];
  dryRun: boolean;
  runCodex: typeof RunCodex;
  log: (msg: string) => void;
  /** Default `B`. */
  round?: ProposalRound;
}): Promise<Proposal[]> {
  const proposed = args.proposals.filter((p) => p.verdict === "propose");
  if (proposed.length === 0) return [...args.proposals];
  const refs = new Set(proposed.map((p) => p.source.ref));
  const grounded = groundCandidates(args.toolkit, args.candidates.filter((c) => refs.has(c.candidate_id)));
  const hitsByRef = new Map(grounded.map((g) => [g.candidate_id, g.search_hits] as const));
  const [modules, rules, taxonomy] = await Promise.all([listToolkitModules(args.toolkit), readProposalPrompt("checker.txt"), effectiveTaxonomy(args.toolkit)]);
  const prompt = [
    rules,
    section("TOOLKIT", JSON.stringify({ lib: args.toolkit.lib, divisions: args.toolkit.divisions }, null, 2)),
    section("TOPIC TREE (doc/taxonomy.json)", taxonomyPromptText(taxonomy)),
    section("EXISTING TOOLKIT MODULES", modules.length ? modules.map((m) => `- ${m.path}: ${m.overview}`).join("\n") : "(none yet)"),
    section(`PROPOSALS (paper ${args.slug})`, JSON.stringify(proposed.map((p) => {
      const { moves_with, recurrence: _r, ...rest } = p;
      return { ...rest, ...(moves_with?.length ? { moves_with_count: moves_with.length } : {}), search_hits: hitsByRef.get(p.source.ref) ?? [] };
    }), null, 1)),
  ].join("\n\n");
  const name = args.round === "A" ? "checker_a" : "checker";
  let reviews: CheckerReview[];
  if (args.dryRun) {
    await recordPrompt(args.toolkit, args.slug, name, prompt, true, args.log);
    reviews = proposed.map((p) => ({ proposal_id: p.id, agrees: true, content_matches: true, duplicate_of: null, note: "[dry-run] no checker was called." }));
  } else {
    const reply = await askJson<{ reviews: CheckerReview[] }>({
      cfg: args.toolkit, slug: args.slug, name, prompt, schema: CHECKER_REPLY, asker: codexAsker(args.toolkit, args.runCodex), log: args.log,
      violations: (r) => checkerViolations(r.reviews ?? [], proposed),
    });
    reviews = reply.reviews;
  }
  const byId = new Map(reviews.map((r) => [r.proposal_id, r] as const));
  return args.proposals.map((p) => {
    const r = byId.get(p.id);
    if (!r) return p;
    const checker = { agrees: r.agrees, note: r.note, content_matches: r.content_matches, duplicate_of: r.duplicate_of };
    // Already available: declined automatically; the owner sees which declaration states it.
    if (r.duplicate_of) {
      return { ...p, verdict: "skip" as const, checker, duplicate_of: r.duplicate_of, reuse_evidence: `already available as ${r.duplicate_of}: ${r.note}` };
    }
    return { ...p, checker };
  });
}
