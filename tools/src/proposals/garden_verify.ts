// `leansmith garden --verify <checklist>`: the mechanical check after the orchestrator has
// carried out the accepted gardening items BY HAND (editing the Lean, lean-lsp + builds).
// Nothing here edits Lean. The toolkit must have been committed before the edits: the check is the
// working tree against `HEAD`, and an unfixable failure is reverted with git by the orchestrator.
//
// It checks: only the toolkit library, the papers, their barrels and `doc/` changed; the toolkit and
// the papers build; `#print axioms` of every toolkit declaration and every paper theorem/lemma of a
// changed paper file is standard (propext, Classical.choice, Quot.sound); no sorry/admit/axiom in
// the toolkit or a changed paper file; every paper theorem/lemma STATEMENT is unchanged (references
// to toolkit declarations the edits renamed are followed); the module-header and layout lints; the
// toolkit index is regenerated; the toolkit graph's health is not worse than at `HEAD` (regressions
// reported). Every step's full log is kept under `runs/_garden/verify/<stamp>/`. When everything
// holds, the ledger records the decisions (`garden_decision`, one per item: re-running updates it),
// and every renamed (`renamed_from`) or moved declaration.
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { statementText } from "../formalization/crosswalk_parse.js";
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import { leanSmithToolsDir, type ToolkitConfig } from "../toolkit/config.js";
import { declarationSpans, forbiddenLeanTokens, identifierTokens } from "../toolkit/lean_source.js";
import { loadLedger, serializeLedger } from "../toolkit/ledger.js";
import { parseGardenChecklist, type GardenBatch } from "./garden.js";
import { axiomsProbeFailure, axiomsProbeText, detectToolkitIndexStep, realApplyDeps, shq, toolkitGateChain, type GateStep } from "./gate.js";
import { rewriteReferences } from "./move.js";
import { healthRegressions, refreshToolkitGraph, toolkitHealth, type ToolkitGraph } from "./toolkit_graph.js";

export interface VerifyDeps {
  /** A shell command (lake, the lints): exit code and its full output. */
  run: (cmd: string, cwd: string) => Promise<{ code: number; log: string; timedOut?: boolean }>;
  /** `git <args>` in the toolkit: exit code and stdout. */
  git: (args: string[], cwd: string) => { code: number; stdout: string };
}

export const realVerifyDeps: VerifyDeps = {
  run: realApplyDeps.run,
  git: (args, cwd) => {
    const r = spawnSync("git", args, { cwd, encoding: "utf8", maxBuffer: 256 * 1024 * 1024 });
    return { code: r.status ?? 1, stdout: r.stdout ?? "" };
  },
};

export interface VerifyGardenResult {
  ok: boolean;
  /** What failed, each naming its log when a command failed. */
  problems: string[];
  /** What the edits made worse in the toolkit graph (main view): reported, not a failure. */
  regressions: string[];
  /** Toolkit declarations whose name changed (old → new), and whose module changed (name → module). */
  renames: Map<string, string>;
  moved: Map<string, string>;
  baseline: string;
  logDir: string;
  recorded: number;
}

const THEOREM_KINDS = new Set(["theorem", "lemma"]);

/** A declaration's statement, comments dropped and whitespace collapsed. */
function statementOf(spanText: string): string {
  const masked = maskLeanCommentsAndStrings(spanText);
  const header = masked.search(/^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma)\b/m);
  return statementText(masked.slice(Math.max(0, header))).replace(/\s+/g, " ").trim();
}

/** Toolkit declarations (full name → { module, kind, shape }) of a set of module texts; `shape` is
 *  the statement with every identifier cut to its last segment (stable under a namespace change). */
function toolkitDecls(texts: ReadonlyMap<string, string>): Map<string, { module: string; kind: string; shape: string }> {
  const out = new Map<string, { module: string; kind: string; shape: string }>();
  for (const [module, text] of texts) {
    for (const s of declarationSpans(text)) {
      const body = text.slice(s.from, s.to);
      let shape = maskLeanCommentsAndStrings(statementText(body.slice(s.nameTo - s.from)));
      for (const t of identifierTokens(shape).reverse()) shape = shape.slice(0, t.from) + t.text.slice(t.text.lastIndexOf(".") + 1) + shape.slice(t.to);
      out.set(s.name, { module, kind: s.kind, shape: shape.replace(/\s+/g, " ").trim() });
    }
  }
  return out;
}

/** Old name → new name: a declaration gone from `before` and one new in `after` with the same leaf,
 *  kind and statement shape (the only match). */
export function detectRenames(
  before: ReadonlyMap<string, { kind: string; shape: string }>,
  after: ReadonlyMap<string, { kind: string; shape: string }>,
): Map<string, string> {
  const out = new Map<string, string>();
  const leaf = (n: string) => n.slice(n.lastIndexOf(".") + 1);
  const added = [...after.keys()].filter((n) => !before.has(n));
  for (const [old, b] of before) {
    if (after.has(old)) continue;
    const hits = added.filter((n) => leaf(n) === leaf(old) && after.get(n)!.kind === b.kind && after.get(n)!.shape === b.shape);
    if (hits.length === 1) out.set(old, hits[0]!);
  }
  return out;
}

/**
 * The paper theorem/lemma statements an edit changed: `before` (the file at `HEAD`, renamed
 * references followed) against `after`, declaration by declaration. A declaration gone is a change.
 */
export function changedStatements(before: string, after: string, renames: ReadonlyMap<string, string>): Array<{ name: string; before: string; after: string | null }> {
  const old = rewriteReferences(before, renames).text;
  const now = new Map(declarationSpans(after).filter((s) => THEOREM_KINDS.has(s.kind)).map((s) => [s.name, statementOf(after.slice(s.from, s.to))] as const));
  const out: Array<{ name: string; before: string; after: string | null }> = [];
  for (const s of declarationSpans(old).filter((x) => THEOREM_KINDS.has(x.kind))) {
    const a = statementOf(old.slice(s.from, s.to));
    const b = now.get(s.name) ?? null;
    if (b !== a) out.push({ name: s.name, before: a, after: b });
  }
  return out;
}

export async function verifyGarden(args: {
  toolkit: ToolkitConfig;
  md: string;
  log: (m: string) => void;
  /** The accepted items the orchestrator carried out (default: every accepted item). */
  items?: readonly string[];
  now?: () => Date;
  deps?: VerifyDeps;
  toolsDir?: string;
  indexStep?: GateStep | null;
  /** The toolkit graph after the edits (default: re-derived from the Lean; null skips the health check). */
  graphAfter?: () => Promise<ToolkitGraph | null>;
}): Promise<VerifyGardenResult> {
  const cfg = args.toolkit;
  const d = args.deps ?? realVerifyDeps;
  const root = cfg.toolkitRoot;
  const json = args.md.replace(/\.md$/, ".json");
  if (!existsSync(json)) throw new Error(`no gardening batch beside ${args.md} (${json})`);
  const batch = JSON.parse(await readFile(json, "utf8")) as GardenBatch;
  const decisions = parseGardenChecklist(await readFile(args.md, "utf8"), batch);
  const pending = Object.entries(decisions).filter(([, x]) => x.kind === "pending").map(([k]) => k);
  if (pending.length) throw new Error(`refusing --verify: ${pending.length} item(s) still pending (${pending.join(", ")}) in ${args.md}`);
  const accepted = batch.items.filter((it) => decisions[it.finding_id]?.kind === "accept" && it.action !== "keep").map((it) => it.finding_id);
  const carried = args.items ? [...args.items] : accepted;
  const notAccepted = carried.filter((id) => !accepted.includes(id));
  if (notAccepted.length) throw new Error(`refusing --verify: ${notAccepted.join(", ")} not accepted on the checklist — never apply an item not accepted`);

  // The baseline: the committed toolkit. Only the library, the papers, their barrels, doc/ and run
  // records may differ from it.
  const head = d.git(["rev-parse", "HEAD"], root);
  if (head.code !== 0) throw new Error(`${root} is not a git repository with a commit: commit the toolkit before gardening, so a failed edit can be reverted`);
  const baseline = head.stdout.trim();
  const status = d.git(["status", "--porcelain=v1", "-uall"], root).stdout.split("\n").filter(Boolean).map((l) => l.slice(3).replace(/^.* -> /, ""));
  const allowed = (p: string) => [`${cfg.lib}/`, `${cfg.papersLib}/`, "doc/", "runs/"].some((x) => p.startsWith(x)) || p === `${cfg.lib}.lean` || p === `${cfg.papersLib}.lean`;
  const problems: string[] = [];
  for (const p of status.filter((x) => !allowed(x))) problems.push(`${p} changed since ${baseline.slice(0, 7)} and is not part of the toolkit's Lean — commit or revert it, then verify again`);
  const lean = status.filter((p) => p.endsWith(".lean") && (p.startsWith(`${cfg.lib}/`) || p.startsWith(`${cfg.papersLib}/`) || p === `${cfg.lib}.lean` || p === `${cfg.papersLib}.lean`));
  if (lean.length === 0) throw new Error(`nothing in the toolkit's Lean changed since ${baseline.slice(0, 7)}: carry out the accepted items first (${carried.join(", ")})`);

  const stamp = (args.now ?? (() => new Date()))().toISOString();
  const logDir = path.join(cfg.runsDir, "_garden", "verify", stamp.replace(/[:.]/g, "-"));
  await mkdir(logDir, { recursive: true });

  // Toolkit module texts at HEAD and now; the declarations renamed or moved.
  const listAt = (rev: string | null) => {
    if (rev) return d.git(["ls-tree", "-r", "--name-only", rev, "--", `${cfg.lib}/`], root).stdout.split("\n").filter((f) => f.endsWith(".lean"));
    return d.git(["ls-files", "--cached", "--others", "--exclude-standard", "--", `${cfg.lib}/`], root).stdout.split("\n").filter((f) => f.endsWith(".lean") && existsSync(path.join(root, f)));
  };
  const moduleOf = (rel: string) => rel.replace(/\.lean$/, "").split("/").join(".");
  const inDivision = (rel: string) => cfg.divisions.includes(rel.split("/")[1] ?? "") && !rel.split("/").includes("Staging");
  const textsBefore = new Map(listAt(baseline).filter(inDivision).map((f) => [moduleOf(f), d.git(["show", `${baseline}:${f}`], root).stdout] as const));
  const textsAfter = new Map<string, string>();
  for (const f of listAt(null).filter(inDivision)) textsAfter.set(moduleOf(f), await readFile(path.join(root, f), "utf8"));
  const before = toolkitDecls(textsBefore);
  const after = toolkitDecls(textsAfter);
  const renames = detectRenames(before, after);
  const moved = new Map<string, string>();
  for (const [name, a] of after) {
    const old = [...renames].find(([, n]) => n === name)?.[0] ?? name;
    const b = before.get(old);
    if (b && b.module !== a.module) moved.set(name, a.module);
  }
  for (const [old, b] of before) {
    if (!after.has(old) && !renames.has(old)) problems.push(`${old} (${b.module}) is gone from the toolkit and was not found under another name — a gardening edit never drops a result unless an accepted item retires or removes it`);
  }

  // No sorry/admit/axiom in the toolkit or a changed paper file.
  const changedPapers = lean.filter((p) => p.startsWith(`${cfg.papersLib}/`));
  for (const [module, text] of textsAfter) {
    for (const t of forbiddenLeanTokens(text)) problems.push(`${module}:${t.line + 1}: ${t.token}`);
  }
  for (const p of changedPapers) {
    if (!existsSync(path.join(root, p))) continue;
    for (const t of forbiddenLeanTokens(await readFile(path.join(root, p), "utf8"))) problems.push(`${p}:${t.line + 1}: ${t.token}`);
  }

  // Paper theorem/lemma statements: unchanged (only proofs and imports may change).
  const paperDecls: string[] = [];
  for (const p of changedPapers) {
    const old = d.git(["show", `${baseline}:${p}`], root);
    const nowText = existsSync(path.join(root, p)) ? await readFile(path.join(root, p), "utf8") : "";
    for (const s of declarationSpans(nowText)) if (THEOREM_KINDS.has(s.kind)) paperDecls.push(s.name);
    if (old.code !== 0) continue;
    for (const c of changedStatements(old.stdout, nowText, renames)) {
      problems.push(c.after === null
        ? `${p}: ${c.name} is gone — a gardening edit never removes a paper's result`
        : `${p}: the statement of ${c.name} changed — only proofs and imports of a paper may change\n    before: ${c.before}\n    after:  ${c.after}`);
    }
  }

  // The commands: toolkit build, papers build, axioms, lints, index — each log kept in full.
  const toolsDir = args.toolsDir ?? leanSmithToolsDir();
  const indexStep = args.indexStep !== undefined ? args.indexStep : await detectToolkitIndexStep(cfg, realApplyDeps);
  const axiomDecls = [...after.keys(), ...paperDecls];
  const probe = path.join(logDir, "axioms.lean");
  await writeFile(probe, axiomsProbeText([cfg.lib, ...changedPapers.map(moduleOf)], axiomDecls), "utf8");
  const axiomsStep: GateStep = { label: "axioms", cmd: `lake env lean ${shq(probe)}`, cwd: root };
  const chain = toolkitGateChain(cfg, toolsDir, indexStep, axiomsStep);
  chain.splice(1, 0, { label: "lake build papers", cmd: `lake build ${cfg.papersLib}`, cwd: root });
  let built = true;
  for (const [i, step] of chain.entries()) {
    const r = await d.run(step.cmd, step.cwd);
    const logFile = path.join(logDir, `${String(i + 1).padStart(2, "0")}-${step.label.replace(/\W+/g, "_")}.log`);
    await writeFile(logFile, `$ (${step.cwd}) ${step.cmd}\n${r.log}`, "utf8");
    const axiomsBad = step.label === "axioms" && r.code === 0 ? axiomsProbeFailure(r.log, axiomDecls) : null;
    if (r.code !== 0 || r.timedOut || axiomsBad) {
      problems.push(`${step.label} failed${axiomsBad ? `: ${axiomsBad}` : ""} — full log: ${logFile}`);
      if (step.label.startsWith("lake build")) { built = false; break; }
    }
  }

  // The toolkit graph's health against HEAD (main view): regressions are reported, not failures.
  let regressions: string[] = [];
  if (built) {
    const graphAt = d.git(["show", `${baseline}:doc/toolkit_graph.json`], root);
    let beforeGraph: ToolkitGraph | null = null;
    if (graphAt.code === 0) {
      const committedGraph = graphAt.stdout; // the committed file, not model output
      try {
        beforeGraph = JSON.parse(committedGraph) as ToolkitGraph;
      } catch {
        args.log(`the committed doc/toolkit_graph.json is unreadable; the health comparison is skipped`);
      }
    }
    const afterGraph = await (args.graphAfter ?? (() => refreshToolkitGraph({ toolkit: cfg, log: args.log })))().catch(() => null);
    if (beforeGraph && afterGraph) {
      const touched = [...new Set([...renames.values(), ...moved.keys()])];
      regressions = healthRegressions(toolkitHealth(beforeGraph), toolkitHealth(afterGraph), touched);
    }
  }

  const ok = problems.length === 0;
  let recorded = 0;
  if (ok) {
    const ledger = await loadLedger(cfg.ledgerPath);
    const decidedAt = stamp;
    const decls = (ledger.declarations as Array<Record<string, unknown>>).map((x) => {
      const name = String(x.name);
      const renamed = renames.get(name);
      const nowName = renamed ?? name;
      const mod = moved.get(nowName);
      const owners = Array.isArray(x.owners) ? { owners: (x.owners as string[]).map((o) => renames.get(o) ?? o) } : {};
      return {
        ...x, name: nowName, ...owners,
        ...(renamed ? { renamed_from: name } : {}),
        ...(mod ? { module: mod, division: mod.split(".")[1] } : {}),
      };
    });
    const records = batch.items.map((it) => ({
      kind: "garden_decision", garden: batch.created, item: it.finding_id, action: it.action, decision: decisions[it.finding_id],
      title: it.title, decided_at: decidedAt,
      ...(carried.includes(it.finding_id) ? { applied: true, verified_at: decidedAt, baseline } : { applied: false }),
    }));
    const kept = (ledger.decisions as Array<Record<string, unknown>>).filter((x) =>
      !(x.kind === "garden_decision" && x.garden === batch.created && records.some((r) => r.item === x.item)));
    const changes = renames.size || moved.size
      ? [{ kind: "garden_verified", garden: batch.created, at: decidedAt, baseline, renamed: Object.fromEntries(renames), moved: Object.fromEntries(moved) }]
      : [];
    await writeFile(cfg.ledgerPath, serializeLedger({ ...ledger, declarations: decls as typeof ledger.declarations, decisions: [...kept, ...records, ...changes] }), "utf8");
    recorded = records.length;
  }
  return { ok, problems, regressions, renames, moved, baseline, logDir, recorded };
}
