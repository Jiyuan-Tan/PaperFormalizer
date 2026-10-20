/**
 * Consequential edits (user decision 2026-09-25): a patch on a node the referee found NO error in.
 *
 * When a repair adds a hypothesis to a result L, a result S that uses L may need its own proof revised
 * so that it uses the new hypothesis. S then carries a patch, but the paper's author has no defect of S to read: the defect is L's. Such a
 * patch is CONSEQUENTIAL. It declares `consequence_of` — the nodes whose repairs it follows — and a
 * one-sentence `reason` (what the step now uses) instead of the defect-shaped `owner_explanation`
 * (Claim / What is wrong / Counterexample), which it must not carry: a counterexample cannot be
 * written for a result nobody showed to fail. It restates the result or revises its proof. The annotated paper renders
 * its units red/blue as for any repair and one line, "Changed to follow the repair of <L>:
 * <reason>" (`annotated_paper.ts`). A definition or assumption S uses may follow a repair of S the
 * same way, when the error of S lives in its formula (an estimator missing its scaling): it
 * replaces its own units, or has no ops when it has none (the restated S carries the formula).
 *
 * The contract (`consequenceViolations`, run on every fixer reply by `stage_v1.ts`): a patch on a node
 * without a finding (`findingNodes`) must declare `consequence_of` and must not carry an
 * `owner_explanation`; a patch on a node with one must not declare it.
 */
import { revisesProof } from "./ops.js";
import { hasExplanation, nodeIdMentions, sentences, texMathProblems, type PaperLabels } from "./owner_text.js";
import { openErrorIds, type PaperErrors, type PatchFile } from "./patches.js";

/** Does this patch follow another repair (`consequence_of` non-empty)? */
export function isConsequential(p: { consequence_of?: readonly string[] | null } | null | undefined): boolean {
  return (p?.consequence_of?.length ?? 0) > 0;
}

/**
 * The nodes of a patch round that carry a finding of their own: every node the directive names (a
 * `consequence` finding, and a `patch rejected` objection to a consequential patch on file, excepted —
 * those are about following another repair, not the paper), every open error of the ledger, and every node an earlier patch answered (a patch on file
 * that is not consequential, or an `unfixable` entry: it was written against a finding). Pure.
 */
export function findingNodes(args: {
  findings: ReadonlyArray<{ id: string; axis: string }>;
  ledger: PaperErrors | undefined;
  prior: Pick<PatchFile, "patches" | "unfixable"> | null;
}): Set<string> {
  const priorPatch = new Map((args.prior?.patches ?? []).map((p) => [p.node, p] as const));
  const out = new Set<string>(openErrorIds(args.ledger));
  for (const f of args.findings) {
    if (f.id === "run") continue;
    if (f.axis === "consequence" || (f.axis === "patch rejected" && isConsequential(priorPatch.get(f.id)))) continue;
    out.add(f.id);
  }
  for (const p of args.prior?.patches ?? []) if (!isConsequential(p)) out.add(p.node);
  for (const u of args.prior?.unfixable ?? []) out.add(u.node);
  return out;
}

/** The repairs answering a finding that a consequential patch's chain of `consequence_of` starts from. */
function rootRepairs(node: string, patches: ReadonlyArray<{ node: string; consequence_of?: string[] | null }>, hasFinding: (id: string) => boolean): string[] {
  const out = new Set<string>();
  const seen = new Set<string>();
  const stack = [node];
  while (stack.length > 0) {
    const id = stack.pop()!;
    if (seen.has(id)) continue;
    seen.add(id);
    const p = patches.find((x) => x.node === id);
    if (p?.consequence_of?.length) stack.push(...p.consequence_of);
    else if (p && id !== node && hasFinding(id)) out.add(id);
  }
  return [...out];
}

/**
 * The consequential patches that follow only a SUGGESTED repair of a MAIN theorem — an `unfixable`
 * entry with a `suggested_repair` the owner has not ruled on (`pendingSuggestions`), which is no
 * repair of the file — set aside: the file without them, and each with what it followed. The fixer
 * writes them when a round shows it a weakening it may only suggest (the definitions a weakened
 * theorem's statement now needs), and the contract has no place for them until the owner accepts
 * the suggestion: refused, the file was never clean (two papers, 2026-10-13). Once the owner
 * accepts, the confirming pass grades those nodes against the accepted statement and its
 * `consequence` findings ask for them again. A suggestion on an intermediate result is not set
 * aside: the runner applies it in the same call (`narrowIntermediates`), so a patch following it
 * follows a repair — the caller passes main-theorem suggestions only. A patch that also follows an
 * applied repair stays (its violation names the suggestion); one that follows a set-aside patch is
 * set aside with it. Pure.
 */
export function setAsideSuggestionConsequences<F extends Pick<PatchFile, "patches">>(file: F, pendingSuggestions: ReadonlySet<string>): { file: F; setAside: Array<{ node: string; follows: string[] }> } {
  const patched = new Set(file.patches.map((p) => p.node));
  const gone = new Set<string>();
  const follows = (p: F["patches"][number]): string[] => (p.consequence_of ?? []).filter((o) => (pendingSuggestions.has(o) && !patched.has(o)) || gone.has(o));
  const setAside: Array<{ node: string; follows: string[] }> = [];
  for (let grew = true; grew; ) {
    grew = false;
    for (const p of file.patches) {
      if (gone.has(p.node) || !isConsequential(p) || follows(p).length !== p.consequence_of!.length) continue;
      gone.add(p.node);
      setAside.push({ node: p.node, follows: follows(p) });
      grew = true;
    }
  }
  if (setAside.length === 0) return { file, setAside };
  return { file: { ...file, patches: file.patches.filter((p) => !gone.has(p.node)) }, setAside };
}

/** The violation for a patch on a node without a finding that explains itself as a defect. */
const NOT_A_DEFECT = "this node has no finding — give consequence_of and a one-sentence reason, not a defect note";

/**
 * Why the patches of `file` break the consequential-edit contract (see the module doc), one violation
 * per problem, each quoting the node (and the nodes it names) so a revise round may change them.
 * `statements`: the core's statement ids; `printsProof`: whether the paper prints a proof of a node. Pure.
 */
export function consequenceViolations(
  file: Pick<PatchFile, "patches">,
  hasFinding: (node: string) => boolean,
  opts: { statements: ReadonlySet<string>; printsProof: (node: string) => boolean; labels?: PaperLabels; all?: Pick<PatchFile, "patches"> },
): string[] {
  const all = opts.all ?? file;
  const out: string[] = [];
  for (const p of file.patches) {
    const owners = p.consequence_of ?? [];
    const q = `"${p.node}"`;
    if (hasFinding(p.node)) {
      if (owners.length > 0) out.push(`the patch for ${q} declares \`consequence_of\`, but ${q} has a finding of its own — answer that finding: set \`consequence_of\` and \`reason\` to null and give the \`owner_explanation\`.`);
      else if (p.reason) out.push(`the patch for ${q} gives a \`reason\`, which only a patch on a node with no finding carries (with \`consequence_of\`) — set it to null; the \`owner_explanation\` explains the repair.`);
      continue;
    }
    if (owners.length === 0) {
      out.push(`the patch for ${q}: ${NOT_A_DEFECT} (\`consequence_of\`: the ids of the repaired results whose repairs this proof follows).`);
      if (hasExplanation(p.owner_explanation)) out.push(`the patch for ${q} carries an \`owner_explanation\`: ${NOT_A_DEFECT} — set \`owner_explanation\` to null.`);
      continue;
    }
    if (hasExplanation(p.owner_explanation)) out.push(`the patch for ${q} carries an \`owner_explanation\`: ${NOT_A_DEFECT} — set \`owner_explanation\` to null.`);
    const named = owners.map((o) => `"${o}"`).join(", ");
    for (const o of owners) {
      const op = all.patches.find((x) => x.node === o);
      if (o === p.node || !op || isConsequential(op) || !hasFinding(o)) {
        // A consequence of a consequence names the repairs its chain starts from.
        const roots = op && isConsequential(op) ? rootRepairs(o, all.patches, hasFinding) : [];
        const list = roots.map((r) => `"${r}"`).join(", ");
        out.push(
          roots.length === 0
            ? `the patch for ${q} names "${o}" in \`consequence_of\`, which is not a repair of this file answering a finding — name the results whose repairs this proof follows.`
            : roots.every((r) => owners.includes(r))
              ? `the patch for ${q} names "${o}" in \`consequence_of\`, whose own patch only follows other repairs (${list}), already named: remove "${o}" from \`consequence_of\`.`
              : `the patch for ${q} names "${o}" in \`consequence_of\`, whose own patch only follows other repairs: replace "${o}" by ${list} in \`consequence_of\`.`,
        );
      }
    }
    const reason = (p.reason ?? "").trim();
    if (!reason) out.push(`the patch for ${q} declares \`consequence_of\` but gives no \`reason\` — one sentence, in the paper's terms, on what the corrected step now uses.`);
    else {
      const n = sentences(reason).length;
      if (n !== 1) out.push(`the \`reason\` of the patch for ${q} has ${n} sentences — give one sentence on what the corrected step now uses.`);
      const ids = nodeIdMentions(reason, opts.labels);
      if (ids.length > 0) out.push(`the \`reason\` of the patch for ${q} names node ids (${ids.join(", ")}) — refer to results as the paper does; the author reads it.`);
      for (const t of texMathProblems(reason, "reason")) out.push(`the \`reason\` of the patch for ${q} ${t}.`);
    }
    if (!opts.statements.has(p.node)) continue;
    if (p.corrected_statement === null && opts.printsProof(p.node) && !revisesProof(p)) {
      out.push(`the patch for ${q} follows another repair (\`consequence_of\`: ${named}) but changes nothing — restate it with the hypothesis that repair adds, or give the proof ops that make it use it.`);
    }
  }
  return out;
}
