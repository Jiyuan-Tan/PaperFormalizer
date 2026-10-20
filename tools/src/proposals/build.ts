// Building an accepted proposal with the study pipeline: a round-A entry (a result the paper
// cites) and a round-B entry on the `generalize` path (a general form of what the paper proved over
// its own setting). The proposal becomes a study requirement (`runs/study_<paper>__<id>/
// requirement.md`); the study scaffolds, proves, reviews and coordinates it into the toolkit under
// its own gate (build, `#print axioms`, header and layout lints, toolkit index) and records it in
// the ledger as the proposal's main result. For a round-B entry the paper's result is then re-proved
// as a corollary of the general one (`reproveAsCorollary`): its statement stays, the build must
// pass, and the paper file is restored otherwise.
import { existsSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { statementText } from "../formalization/crosswalk_parse.js";
import { lintUnusedHypotheses } from "../formalization/unused_hypothesis_lint.js";
import { hasRealSorry } from "../graph/extractor.js";
import { MODELS } from "../models.js";
import type { runCodex as RunCodex } from "../shared/codex.js";
import { withLakeBuildLock } from "../shared/build_mutex.js";
import { requirementPath, studyRunId } from "../substrate/paths.js";
import type { runSubstratePipeline as RunStudy } from "../substrate/pipeline.js";
import { studyExit } from "../substrate/state.js";
import { substrateStateExists } from "../substrate/state.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { declarationSpans, forbiddenLeanTokens } from "../toolkit/lean_source.js";
import { loadLedger } from "../toolkit/ledger.js";
import { spawnWithInactivityTimeout } from "../workers/spawn.js";
import { indexNameTable, nameProblems } from "./curator.js";
import { proposalStudySlug, proposalsRunDir, type Decision, type Proposal } from "./schema.js";

const PROMPT_DIR = path.join(path.dirname(fileURLToPath(import.meta.url)), "prompts");

/** The paper's own Lean statement of a round-B entry, which the general form must specialize to. */
export interface PaperInstance {
  decl: string;
  lean_type: string;
}

/** The study requirement (`requirement.md`) that builds one accepted proposal. */
export function renderProposalRequirement(p: Proposal, paperSlug: string, instance?: PaperInstance): string {
  const blocks = p.nearest_existing.map((n) => `- \`${n.name}\` (${n.library}): ${n.why_not_same}`);
  const shaped = p.paper_shaped ?? [];
  return [
    `# Substrate requirement: ${p.proposed_name}`,
    "",
    "## Goal",
    `Build "${p.title}" as a general result of the ${p.division} division of the toolkit.`,
    "",
    "## Provides (API contract)",
    `- \`${p.proposed_name}\` — the main declaration, placed in \`${p.target_module}\`${p.new_module_overview ? ` (a new module: ${p.new_module_overview})` : " (an existing module)"}. Its docstring opens with the statement below in plain words.`,
    "- Any definition the statement needs, in the same module, with supporting lemmas as the proof requires.",
    "",
    "## Statement / milestones",
    p.content,
    ...(p.source_text ? ["", "The cited work states it as follows (excerpt):", "", "```", p.source_text.trim(), "```"] : []),
    ...(instance ? [
      "",
      `The paper's formalization proves a special case of it as \`${instance.decl}\`; the general statement must specialize to this one directly (the paper's result is re-proved as its corollary afterwards):`,
      "",
      "```lean",
      instance.lean_type.trim(),
      "```",
    ] : []),
    "",
    "## Standard reference",
    p.reference,
    "",
    "## Intended reuse",
    `Proposed from paper ${paperSlug} (round-${p.round} proposal ${p.id}); the paper ${p.round === "A" ? "uses it instead of assuming it" : "re-proves its result as a corollary of it"}. ${p.reuse_evidence}`,
    "",
    "## May assume / must derive",
    "Assume exactly the hypotheses the statement lists — none that the proof does not use; derive everything else from the base libraries and the toolkit. No new axioms, no sorry." +
      (p.dropped_hypotheses?.length ? ` The paper's version also assumes ${p.dropped_hypotheses.map((h) => `\`${h}\``).join(", ")}, which its proof never uses: leave them out.` : ""),
    "",
    "## Non-goals (optional)",
    `Nothing specific to paper ${paperSlug}: no paper notation, types, readings or special cases in the toolkit declaration.` +
      (shaped.length ? ` In particular none of: ${shaped.join("; ")}.` : ""),
    "",
    "## Known building blocks (optional)",
    ...(blocks.length ? blocks : ["- (none named)"]),
    "",
  ].join("\n");
}

export interface BuiltProposal {
  studyRun: string;
  /** Toolkit declarations the study recorded for this proposal. */
  promoted: string[];
  /** The main result's toolkit declaration, when the study recorded one. */
  main?: { name: string; module: string };
  /** Hypotheses of the built main result its proof never uses (the lint's definite findings). */
  unused_hypotheses?: string[];
}

/** Whether `name` is in the toolkit because THIS proposal's own study put it there (a study that
 *  halted, was continued and finished before the apply was re-run): then the name is not taken by
 *  something else. Pure. */
export function builtByOwnStudy(
  declarations: ReadonlyArray<{ name: string; origin: { kind: string; slug: string } }>,
  qid: string,
  p: Pick<Proposal, "id" | "round">,
  name: string,
): boolean {
  return declarations.some((e) => {
    const o = e.origin as Record<string, unknown>;
    return e.name === name && e.origin.kind === "proposal" && e.origin.slug === qid && o.round === p.round && o.proposal_id === p.id;
  });
}

/** Build one accepted proposal through the study pipeline. Throws, saying how to continue, when the
 *  study stops short of `done`. */
export async function buildProposal(args: {
  toolkit: ToolkitConfig;
  qid: string;
  p: Proposal;
  decision: Decision;
  dryRun: boolean;
  runStudy: typeof RunStudy;
  log: (msg: string) => void;
  instance?: PaperInstance;
}): Promise<BuiltProposal> {
  const { toolkit: cfg, qid, p, log } = args;
  if (!args.dryRun && !builtByOwnStudy((await loadLedger(cfg.ledgerPath)).declarations, qid, p, p.proposed_name)) {
    const problems = nameProblems(p.proposed_name, await indexNameTable(cfg));
    if (problems.length) throw new Error(`${p.id}: ${problems.join("; ")} — decide accept_with_edits with a proposed_name that fixes it, then re-run`);
  }
  const studySlug = proposalStudySlug(qid, p.id);
  const req = renderProposalRequirement(p, qid, args.instance);
  const reqFile = requirementPath(cfg.toolkitRoot, studySlug);
  const resume = await substrateStateExists(cfg.toolkitRoot, studySlug);
  if (resume && existsSync(reqFile) && (await readFile(reqFile, "utf8")) !== req) {
    log(`${p.id}: study ${studyRunId(studySlug)} exists with a different requirement; keeping the one on disk`);
  } else if (!resume) {
    await mkdir(path.dirname(reqFile), { recursive: true });
    await writeFile(reqFile, req, "utf8");
  }
  log(`${p.id}: building \`${p.proposed_name}\` via study ${studyRunId(studySlug)}${resume ? " (resume)" : ""}`);
  const label = args.decision.kind === "accept_with_edits" ? "accepted-with-edits" : args.decision.kind === "generalize_first" ? "generalize-first" : "accepted";
  const study = await args.runStudy({
    toolkit: cfg, slug: studySlug, resume, dryRun: args.dryRun,
    provenance: {
      origin: { kind: "proposal", slug: qid, round: p.round, proposal_id: p.id },
      decision: label,
      nearest_existing: p.nearest_existing.map((n) => n.name),
      main: p.proposed_name,
      ...(p.title ? { title: p.title } : {}),
    },
  });
  if (study.phase !== "done") {
    throw new Error(
      `${p.id}: study ${studyRunId(studySlug)} stopped in phase ${study.phase}${study.terminalMessage ? ` (${study.terminalMessage})` : ""}. ` +
        `${studyExit(study, studySlug, cfg.toolkitRoot)} Then re-run ` +
        `\`leansmith propose ${qid} --round ${p.round} --apply\`, or change this item's decision to decline/defer. Items already built stay built.`,
    );
  }
  const ledger = await loadLedger(cfg.ledgerPath);
  const mine = ledger.declarations.filter((e) => {
    const o = e.origin as Record<string, unknown>;
    return e.origin.kind === "proposal" && e.origin.slug === qid && o.round === p.round && o.proposal_id === p.id;
  });
  const leaf = (n: string) => n.slice(n.lastIndexOf(".") + 1);
  const main = mine.find((e) => (e as Record<string, unknown>).tier === "main") ?? mine.find((e) => leaf(e.name) === leaf(p.proposed_name));
  // The built statement carries no hypothesis its proof never uses (reported, for the gardener).
  let unused: string[] = [];
  if (main && !args.dryRun) {
    const file = path.join(cfg.toolkitRoot, ...main.module.split(".")) + ".lean";
    if (existsSync(file)) {
      unused = lintUnusedHypotheses(await readFile(file, "utf8")).findings
        .filter((f) => f.severity === "definite" && leaf(f.theoremName) === leaf(main.name)).map((f) => f.hypothesisName);
      if (unused.length) log(`${p.id}: WARNING the built \`${main.name}\` still assumes ${unused.join(", ")}, which its proof never uses`);
    }
  }
  return {
    studyRun: studyRunId(studySlug), promoted: mine.map((e) => e.name),
    ...(main ? { main: { name: main.name, module: main.module } } : {}),
    ...(unused.length ? { unused_hypotheses: unused } : {}),
  };
}

/** The toolkit index's statement of `name` (what the corollary agent instantiates). */
async function indexedStatement(cfg: ToolkitConfig, name: string): Promise<string> {
  if (!existsSync(cfg.indexPath)) return "(not in the toolkit index; read it in its module)";
  const idx = JSON.parse(await readFile(cfg.indexPath, "utf8")) as { entries?: Array<{ name?: string; statement?: string }> };
  return idx.entries?.find((e) => e.name === name)?.statement ?? "(not in the toolkit index; read it in its module)";
}

/** The statement (everything before `:=`) of `decl` in `text`, or null when it is not declared there. */
function statementOf(text: string, decl: string): string | null {
  const leaf = decl.slice(decl.lastIndexOf(".") + 1);
  const span = declarationSpans(text).find((s) => s.name === decl || s.name.endsWith(`.${leaf}`) || s.written === leaf);
  return span ? statementText(text.slice(span.from, span.to)).replace(/\s+/g, " ").trim() : null;
}

/** The paper module of a file under the toolkit root (`Papers/Foo/Bar.lean` → `Papers.Foo.Bar`). */
function moduleOfFile(cfg: ToolkitConfig, file: string): string {
  return path.relative(cfg.toolkitRoot, file).replace(/\.lean$/, "").split(path.sep).join(".");
}

export interface CorollaryDeps {
  runCodex: typeof RunCodex;
  /** `lake build <module>` in the toolkit: exit code and output. */
  build: (cfg: ToolkitConfig, module: string) => Promise<{ ok: boolean; log: string }>;
}

async function lakeBuild(cfg: ToolkitConfig, module: string): Promise<{ ok: boolean; log: string }> {
  return withLakeBuildLock(cfg.toolkitRoot, async () => {
    const r = await spawnWithInactivityTimeout("lake", ["build", module], { cwd: cfg.toolkitRoot, env: process.env, inactivityTimeoutMs: 20 * 60 * 1000 });
    return { ok: r.exitCode === 0, log: [r.stdout, r.stderr].filter(Boolean).join("\n") };
  });
}

/** The reason of a reply's closing `COROLLARY: not possible — <reason>` line ("" when it gave none). */
export function corollaryReason(stdout: string): string {
  // (the prompt shows the line in backticks: a reply may keep them)
  const m = [...stdout.matchAll(/^\s*`?COROLLARY:\s*not possible\s*[—–-]\s*(.+?)`?\s*$/gm)].at(-1);
  return m ? m[1]!.trim().slice(0, 400) : "";
}

/**
 * Re-prove the paper's `decl` (in `file`) as a corollary of the toolkit's `general`: one codex agent
 * edits the file; the runner then requires the statement unchanged, no `sorry`/`admit`/`axiom` in the
 * file, and the paper module building. Anything else restores the file. Returns whether it held.
 */
export async function reproveAsCorollary(args: {
  toolkit: ToolkitConfig;
  qid: string;
  proposalId: string;
  decl: string;
  file: string;
  general: { name: string; module: string };
  log: (msg: string) => void;
  deps?: Partial<CorollaryDeps>;
  /** Once the file builds: why the re-proof cannot stay (a statement of the paper or the toolkit
   *  changed — `invariance.ts`), or null. */
  verify?: () => Promise<string | null>;
}): Promise<{ ok: boolean; why: string }> {
  const { toolkit: cfg, decl, file, general, log } = args;
  const runCodex = args.deps?.runCodex ?? (await import("../shared/codex.js")).runCodex;
  const build = args.deps?.build ?? lakeBuild;
  const before = await readFile(file, "utf8");
  const stmt = statementOf(before, decl);
  if (stmt === null) return { ok: false, why: `\`${decl}\` is not declared in ${file}` };
  const module = moduleOfFile(cfg, file);
  const tpl = await readFile(path.join(PROMPT_DIR, "corollary.txt"), "utf8");
  const prompt = tpl
    .split("{{PAPER_DECL}}").join(decl)
    .split("{{PAPER_FILE}}").join(path.relative(cfg.toolkitRoot, file))
    .split("{{PAPER_MODULE}}").join(module)
    .split("{{GENERAL_DECL}}").join(general.name)
    .split("{{GENERAL_MODULE}}").join(general.module)
    .split("{{GENERAL_STATEMENT}}").join(await indexedStatement(cfg, general.name));
  const dir = path.join(proposalsRunDir(cfg, args.qid), "prompts");
  await mkdir(dir, { recursive: true });
  await writeFile(path.join(dir, `corollary_${args.proposalId}.txt`), prompt, "utf8");
  log(`${args.proposalId}: re-proving \`${decl}\` as a corollary of \`${general.name}\` (${MODELS.codexKernel})`);
  const restore = async (why: string) => {
    await writeFile(file, before, "utf8");
    log(`${args.proposalId}: corollary not kept (${why}); ${path.relative(cfg.toolkitRoot, file)} restored — the paper keeps its own proof`);
    return { ok: false, why };
  };
  // The agent's own closing line (`COROLLARY: not possible — <reason>`), for the log when it kept the file.
  let said = "";
  try {
    const res = await runCodex({ prompt, model: MODELS.codexKernel, reasoningEffort: "high", cwd: cfg.toolkitRoot, leanProjectPath: cfg.leanProjectPath });
    await writeFile(path.join(dir, `corollary_${args.proposalId}.out.txt`), res.stdout, "utf8");
    said = corollaryReason(res.stdout);
  } catch (err) {
    return restore(`the agent failed: ${err instanceof Error ? err.message : String(err)}`);
  }
  const after = await readFile(file, "utf8");
  if (after === before) return restore(`the agent changed nothing${said ? `: ${said}` : ""}`);
  if (statementOf(after, decl) !== stmt) return restore("the statement changed");
  if (hasRealSorry(after) && !hasRealSorry(before)) return restore("a `sorry` appeared");
  const holes = forbiddenLeanTokens(after).length - forbiddenLeanTokens(before).length;
  if (holes > 0) return restore("a `sorry`/`admit`/`axiom` appeared");
  const b = await build(cfg, module);
  if (!b.ok) return restore(`\`lake build ${module}\` failed: ${b.log.split("\n").filter((l) => /error/.test(l)).slice(0, 3).join(" | ")}`);
  const changed = args.verify ? await args.verify() : null;
  if (changed) return restore(changed);
  log(`${args.proposalId}: \`${decl}\` is now a corollary of \`${general.name}\`; ${module} builds`);
  return { ok: true, why: "" };
}
