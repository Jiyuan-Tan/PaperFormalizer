/**
 * Test helper: the canned model replies of tests written before `owner_explanation` (2026-09-24)
 * gain one wherever the contract requires it and the reply leaves the field out — an `error` node
 * of a referee reply, every patch and unfixable entry of a fixer reply — and a
 * refuting error node gains `witness_regime: "in_scope"` and a `witness_instance`. A reply that sets
 * a field (even to null or "") is left as it is, so a contract test can still omit it.
 */
import type { OwnerExplanation } from "../../src/verify/owner_text.js";

export const CANNED_EXPLANATION: OwnerExplanation = {
  claim: "The statement claims more than the argument gives.",
  // A note names its failing step by a unit (`<node>/1/1`: the statement unit `writeToyPaper` gives a
  // node; `withOwnerExplanations` sets the node's own).
  defects: [{ kind: "out_of_domain", step_unit: "thm:x/1/1", uses: "a property of the model", assumed_on: "a special case", applied_at: "the general case", detail: null }],
  why: { objects: ["$X$ uniform on $[0,1]$", "$f(x)=x^{-1/2}$"], consequence: "$E\\{f(X)^2\\}=\\infty$ while the statement bounds it by $4$" },
  fix: "The fix states what does hold.",
  gives_up: null,
};

/** The canned note, its step `unit` (default the node's statement unit, `writeToyPaper`). */
export const cannedExplanation = (node: string, unit = `${node}/1/1`): OwnerExplanation => ({ ...structuredClone(CANNED_EXPLANATION), defects: [{ ...CANNED_EXPLANATION.defects[0]!, step_unit: unit }] });

export const CANNED_INSTANCE = "the paper's own model, with the constants of the witness";

export function withOwnerExplanations<T>(reply: T): T {
  if (!reply || typeof reply !== "object") return reply;
  const r = withOps(structuredClone(reply)) as Record<string, unknown>;
  const fill = (x: Record<string, unknown>): void => {
    const node = typeof x.node === "string" ? x.node : typeof x.id === "string" ? x.id : "thm:x";
    // A repair's note names the step its first replacing op changes (a step it names is one its ops change).
    const ops = [...(Array.isArray(x.ops) ? x.ops : []), ...(Array.isArray((x.suggested_repair as { ops?: unknown } | undefined)?.ops) ? ((x.suggested_repair as { ops: unknown[] }).ops) : [])] as Array<{ op?: string; unit?: string }>;
    const unit = ops.find((o) => o.op === "replace" && typeof o.unit === "string")?.unit;
    if (!("owner_explanation" in x)) {
      const note = cannedExplanation(node, unit);
      // A suggestion's `given_up` is derived from its note's `gives_up` (2026-09-26): the canned note of
      // a reply written with `given_up` on the suggestion says it.
      const gu = (x.suggested_repair as { given_up?: unknown } | null | undefined)?.given_up;
      if (typeof gu === "string" && gu.trim()) note.gives_up = gu;
      x.owner_explanation = note;
    }
  };
  // Replies written before `witness_regime` (2026-09-24): a refuting error's witness is in scope.
  const regime = (x: Record<string, unknown>): void => {
    if (x.minimality === true || x.weakens_contribution === true) return;
    if (!("witness_regime" in x)) x.witness_regime = "in_scope";
    if (!("witness_instance" in x)) x.witness_instance = CANNED_INSTANCE;
  };
  const errorNode = (n: Record<string, unknown>): void => {
    fill(n);
    regime(n);
  };
  // Replies written before the referee authored the explanations (2026-09-24): a clean grade may
  // confirm a repair, which owes an explanation and a clarity grade of the fixer's.
  const cleanNode = (n: Record<string, unknown>): void => {
    fill(n);
    if (!("explanation_clarity" in n)) n.explanation_clarity = { grade: "ok", reason: "canned: the fixer's explanation locates the step" };
  };
  const visit = (n: Record<string, unknown>): void => {
    if (n?.correctness === "error") errorNode(n);
    else if (n?.correctness === "ok" || n?.correctness === "bookkeeping") cleanNode(n);
  };
  if (Array.isArray(r.nodes)) for (const n of r.nodes as Array<Record<string, unknown>>) visit(n);
  const node = r.node as Record<string, unknown> | undefined;
  if (node && typeof node === "object") visit(node);
  if (Array.isArray(r.patches) && Array.isArray(r.unfixable)) {
    for (const p of r.patches as Array<Record<string, unknown>>) fill(p);
    for (const u of r.unfixable as Array<Record<string, unknown>>) fill(u);
  }
  return r as T;
}

/**
 * Fixer replies written before operation patches (2026-09-25): a patch's or suggested repair's
 * `corrected_statement` becomes one `replace` of its statement's single unit (`<node>/1/1`, the unit
 * `writeToyPaper` gives it); a suggestion's `given_up` goes to its note (`withOwnerExplanations`); a
 * reply that sets non-empty `ops` is left as it is. The texts stay (a file on disk holds them, derived;
 * a reply's are derived again), sentence-anchored proof edits go.
 */
export function withOps(reply: unknown): unknown {
  if (!reply || typeof reply !== "object") return reply;
  const r = structuredClone(reply) as Record<string, unknown>;
  const toOps = (x: Record<string, unknown>, node: string): void => {
    if (!Array.isArray(x.ops) || x.ops.length === 0) {
      const ops: unknown[] = [];
      if (typeof x.corrected_statement === "string" && x.corrected_statement.trim()) ops.push({ op: "replace", unit: `${node}/1/1`, to: null, tex: x.corrected_statement });
      x.ops = ops;
    }
    delete x.proof_edits;
    delete x.insert_after;
  };
  if (Array.isArray(r.patches) && Array.isArray(r.unfixable)) {
    for (const p of r.patches as Array<Record<string, unknown>>) if (typeof p.node === "string") toOps(p, p.node);
    for (const u of r.unfixable as Array<Record<string, unknown>>) {
      if (typeof u.node === "string" && u.suggested_repair && typeof u.suggested_repair === "object") toOps(u.suggested_repair as Record<string, unknown>, u.node);
    }
  }
  return r;
}

/**
 * A toy paper for a core's statements, so the fixer's ops have units to address: each statement is an
 * environment labelled with its id whose body is its statement (without V1's `[Hypotheses: …]`), written
 * as `flat.tex` (before any flat text the test wrote), `envs.json`, `flat.linemap.json` and a reference
 * core naming each statement's environment. A one-sentence statement is one unit, `<id>/1/1`.
 */
export async function writeToyPaper(runDir: string, core: { qid?: string; statements: Array<{ id: string; kind: string; statement: string; proof_tex?: string | null }> }): Promise<void> {
  const { writeFile, mkdir } = await import("node:fs/promises");
  const path = await import("node:path");
  const lines: string[] = [];
  const envs: unknown[] = [];
  for (const s of core.statements) {
    const env = ["theorem", "lemma", "proposition", "corollary"].includes(s.kind) ? s.kind : "proposition";
    const body = `\\label{${s.id}}\n${s.statement.replace(/\s*\[Hypotheses:[^\]]*\]\s*$/u, "")}\n`;
    const from = lines.length + 1;
    lines.push(`\\begin{${env}}`, ...body.replace(/\n$/u, "").split("\n"), `\\end{${env}}`);
    const to = lines.length;
    let proof: string | null = null;
    let proofLines: unknown = null;
    if (s.proof_tex?.trim()) {
      proof = `\n${s.proof_tex.trim()}\n`;
      const pf = lines.length + 1;
      lines.push("\\begin{proof}", ...s.proof_tex.trim().split("\n"), "\\end{proof}");
      proofLines = { file: "main.tex", from: pf, to: lines.length, env: "proof", label: null };
    }
    lines.push("");
    envs.push({ id: s.id, kind: env, envName: env, label: s.id, title: null, body, proof, proofLines, section: "Results", lines: { file: "main.tex", from, to, env, label: s.id }, refs: [] });
  }
  // A flat text the test wrote before stays, after the toy environments (a canned note may quote it).
  const { existsSync } = await import("node:fs");
  const { readFile } = await import("node:fs/promises");
  const flatFile = path.join(runDir, "discovery", "flat.tex");
  const before = existsSync(flatFile) ? await readFile(flatFile, "utf8") : "";
  for (const l of before.replace(/\n$/u, "").split("\n")) if (before) lines.push(l);
  const flat = `${lines.join("\n")}\n`;
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  await writeFile(path.join(runDir, "discovery", "flat.tex"), flat, "utf8");
  await writeFile(path.join(runDir, "discovery", "flat.linemap.json"), JSON.stringify({ lineMap: lines.map((_, i) => ({ file: "main.tex", line: i + 1 })) }), "utf8");
  await writeFile(path.join(runDir, "discovery", "envs.json"), JSON.stringify({ main_file: "main.tex", files: ["main.tex"], newtheorem: {}, envs, bibliography: [] }), "utf8");
  const refs = {
    qid: core.qid ?? "toy",
    target_estimand: "\\(\\tau\\)",
    statements: core.statements.filter((s) => /^(thm|lem|prop):[a-z0-9-]+$/u.test(s.id)).map((s) => ({ id: s.id, kind: ["theorem", "lemma", "proposition"].includes(s.kind) ? s.kind : "proposition", env: s.id, status: "to-prove" })),
  };
  await writeFile(path.join(runDir, "discovery", "core_refs.json"), JSON.stringify(refs), "utf8");
}
