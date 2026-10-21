#!/usr/bin/env node
// Writes the states `paperformalizer demo` plays back (`tools/data/demo/snapshots/`): a dry run of the
// demo paper (no model call, no Lean), its halts written in by hand — the referee's finding on Theorem 3
// with the weakened repair the fixer suggests, Schur's inequality as a cited result for round A, the
// rounds' entries in plain words, the agent's recommendations, the finished report and the toolkit's
// new Lean — each state copied as the page reads it (`demo_capture.mjs copy`) and kept as layered
// snapshots (`demo_capture.mjs build`). Run it again when the run records change shape:
//
//   node tools/scripts/demo_author.mjs [--work <scratch dir>]
//
// then `npx vitest run test/ui/demo.test.ts`. The tour itself is tools/data/demo/demo.json.
import { spawnSync } from "node:child_process";
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const TOOLS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const DATA = path.join(TOOLS, "data", "demo");
const PAPER = path.join(DATA, "paper");
const TEMPLATE = path.join(TOOLS, "..", "templates", "toolkit");
const w = process.argv.indexOf("--work");
const work = w >= 0 ? path.resolve(process.argv[w + 1]) : mkdtempSync(path.join(os.tmpdir(), "tc-demo-author-"));
const tk = path.join(work, "tk"), raw = path.join(work, "raw"), run = path.join(tk, "runs", "demo");
const SLUG = "demo";

const sh = (args, what) => {
  const r = spawnSync(process.execPath, args, { cwd: TOOLS, encoding: "utf8" });
  if (r.status !== 0) { console.error(`${what} failed:\n${r.stdout}\n${r.stderr}`); process.exit(1); }
  return r.stdout;
};
const tsx = path.join(TOOLS, "node_modules", "tsx", "dist", "cli.mjs");
const cli = (...a) => sh([tsx, path.join(TOOLS, "bin", "paperformalizer.ts"), ...a], `paperformalizer ${a.join(" ")}`);
const orch = (...a) => sh([path.join(TOOLS, "scripts", "orch.mjs"), ...a], `orch.mjs ${a[0]}`);
const verify = (...a) => cli("verify", PAPER, "--toolkit", tk, "--slug", SLUG, "--dry-run", ...a);
const json = (f, edit) => { const v = JSON.parse(readFileSync(f, "utf8")); edit(v); writeFileSync(f, JSON.stringify(v, null, 2) + "\n"); };
let n = 0;
const copy = (label) => sh([path.join(TOOLS, "scripts", "demo_capture.mjs"), "copy", "--toolkit", tk, "--slug", SLUG, "--to", path.join(raw, `${String(++n).padStart(3, "0")}-${label}`)], "copy");

rmSync(work, { recursive: true, force: true });
mkdirSync(work, { recursive: true });
cpSync(TEMPLATE, tk, { recursive: true });
cpSync(path.join(tk, "paperformalizer.json.example"), path.join(tk, "paperformalizer.json"));

// start: the paper transcribed; Schur's inequality marked as the result it cites (round A offers it)
verify("--stop-after", "V1");
for (const f of ["core.json", "core.transcribed.json"]) json(path.join(run, "discovery", f), (c) => {
  const s = c.statements.find((x) => x.id === "lem:schur");
  s.status = "cited"; s.source = { cite: "hlp", locator: "Theorem 1" };
});
copy("start");

// review: the referee's finding on Theorem 3, the fixer's weakened repair, the agent's recommendation
verify("--resume", "--stop-after", "V1.5");
const detail = "False for negative numbers: for $a=b=-1$ the left side is $-1$ while the right side is $\\sqrt{1}=1$. The proof takes $\\sqrt{a}$ and $\\sqrt{b}$, which are real numbers only when $a,b\\ge 0$.";
const witness = "$a=b=-1$: $\\frac{a+b}{2}=-1<1=\\sqrt{ab}$.";
const printed = "For all real numbers $a$ and $b$, \\[ \\frac{a + b}{2} \\ge \\sqrt{ab} . \\]";
const proposed = "For all real numbers $a, b \\ge 0$, \\[ \\frac{a + b}{2} \\ge \\sqrt{ab} . \\]";
const proof = "Apply Lemma~\\ref{lem:sq} to $x = \\sqrt{a}$ and $y = \\sqrt{b}$, real numbers since $a, b \\ge 0$: then $x^2 = a$, $y^2 = b$ and $xy = \\sqrt{ab}$, so $a + b \\ge 2\\sqrt{ab}$.";
const givenUp = "The inequality is no longer claimed when $a$ or $b$ is negative.";
const at = "2026-10-17T12:00:00.000Z";
json(path.join(run, "discovery", "v1_5_review.json"), (r) => {
  r.verdict = "FAIL"; r.summary = "One error: Theorem 3 fails for negative numbers.";
  Object.assign(r.nodes.find((x) => x.id === "thm:amgm"), { correctness: "error", detail, witness, weakens_contribution: true });
});
json(path.join(run, "state.json"), (s) => {
  s.stage_completed = "V1";
  s.verify.findings = [{ node: "thm:amgm", stage: "V1.5", kind: "refuted", detail, witness, suggested_repair: proposed, at }];
  s.verify.paper_errors = { "thm:amgm": { detail, witness, kind: "error", weakens_contribution: true, suggested_repair: proposed } };
  s.verify.weakening_repair = { status: "pending", items: [{ node: "thm:amgm", printed, proposed, given_up: givenUp, detail, witness, source: "fixer" }], at };
});
writeFileSync(path.join(run, "discovery", "patches.json"), JSON.stringify({
  key_results: ["thm:amgm", "thm:cubic"], key_contribution: "the two-variable AM-GM inequality, and a cubic inequality from Schur's inequality", patches: [],
  unfixable: [{ node: "thm:amgm", reason: "any repair weakens the contribution: the inequality fails for negative numbers; only the nonnegative case holds", suggested_repair: { corrected_statement: proposed, proof_note: proof, given_up: givenUp }, suggested_by: "fixer" }],
}, null, 2) + "\n");
cli("annotate", SLUG, "--toolkit", tk);
orch("recommend", SLUG, "--toolkit", tk, "repair", "thm:amgm", "accept", "The printed inequality is false for negative numbers ($a=b=-1$), and the proof only works for $a,b\\ge 0$. Adding $a,b\\ge 0$ gives the standard AM-GM inequality, which is what the paper evidently means.");
copy("review");

// round A: the repair accepted; Schur's inequality offered, in plain words, with the recommendation
verify("--resume", "--accept-repair");
json(path.join(run, "proposals", "A.json"), (b) => {
  Object.assign(b.proposals[0], {
    title: "Schur's inequality (exponent 1)", reference: "Hardy, Littlewood and P\\'olya, \\emph{Inequalities}, Theorem 1",
    content: "For all real numbers $a, b, c \\ge 0$, $a(a-b)(a-c) + b(b-a)(b-c) + c(c-a)(c-b) \\ge 0$.",
    division: "Foundations", target_module: "Toolkit/Foundations/Algebra/Schur.lean", new_module_overview: "Classical polynomial inequalities for nonnegative reals.",
    proposed_name: "schur_inequality", nearest_existing: [{ name: "(none found)", library: "Mathlib", why_not_same: "Mathlib has no Schur inequality for real numbers." }],
    reuse_evidence: "A standard inequality, cited by many papers on polynomial inequalities; not in Mathlib.", division_reason: "An elementary inequality on real numbers.",
    checker: { agrees: true, note: "The statement is the classical Schur inequality with exponent 1.", content_matches: true, duplicate_of: null },
  });
});
rmSync(path.join(run, "proposals", "dry_run", `${SLUG}.A.md`), { force: true });
cli("propose", SLUG, "--round", "A", "--toolkit", tk, "--dry-run");
orch("recommend", SLUG, "--toolkit", tk, "A", "a-lem-schur", "accept", "Schur's inequality is a standard tool that Mathlib lacks; building it once lets this paper and later ones use it instead of assuming it.");
copy("roundA");

// round B: round A applied (Schur's inequality in the toolkit); the paper's results offered
cli("propose", SLUG, "--round", "A", "--apply", "--recommended", "--toolkit", tk, "--dry-run");
const lean = (withCubic) => `import Mathlib

/-!
# Schur's inequality

Classical polynomial inequalities for nonnegative reals.
-/

namespace Toolkit.Foundations.Algebra

/-- **Schur's inequality** (exponent 1). For all real numbers \`a, b, c ≥ 0\`,
\`a(a-b)(a-c) + b(b-a)(b-c) + c(c-a)(c-b) ≥ 0\`.
Hardy, Littlewood and Pólya, *Inequalities*, Theorem 1. -/
theorem schur_inequality {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac <;>
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc,
      mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hbc), mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hac),
      mul_nonneg (sub_nonneg.2 hbc) (sub_nonneg.2 hac)]
${withCubic ? `
/-- A cubic inequality from Schur's inequality. For all real numbers \`a, b, c ≥ 0\`,
\`(a+b+c)^3 + 9abc ≥ 4(a+b+c)(ab+bc+ca)\`. -/
theorem cubic_ge_of_schur {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    4 * (a + b + c) * (a * b + b * c + c * a) ≤ (a + b + c) ^ 3 + 9 * a * b * c := by
  nlinarith [schur_inequality ha hb hc]
` : ""}
end Toolkit.Foundations.Algebra
`;
const leanFile = path.join(tk, "Toolkit", "Foundations", "Algebra", "Schur.lean");
mkdirSync(path.dirname(leanFile), { recursive: true });
writeFileSync(leanFile, lean(false));
json(path.join(run, "proposals", "B.json"), (b) => {
  const P = Object.fromEntries(b.proposals.map((p) => [p.id, p]));
  const checker = { agrees: true, note: "The statement matches the paper's result.", content_matches: true, duplicate_of: null };
  Object.assign(P["b-lem-schur"], { verdict: "skip", duplicate_of: "Toolkit.Foundations.Algebra.schur_inequality", title: "Schur's inequality", reuse_evidence: "Built into your toolkit in round A." });
  Object.assign(P["b-lem-sq"], { verdict: "skip", duplicate_of: "two_mul_le_add_sq", title: "$x^2+y^2 \\ge 2xy$", reuse_evidence: "Mathlib has it: two_mul_le_add_sq." });
  Object.assign(P["b-thm-amgm"], {
    title: "AM-GM for two nonnegative reals", reference: "Theorem 3 of the paper (as corrected)", content: "For all real numbers $a, b \\ge 0$, $\\frac{a+b}{2} \\ge \\sqrt{ab}$.",
    target_module: "Toolkit/Foundations/Algebra/MeanInequalities.lean", new_module_overview: "Inequalities between means of nonnegative reals.", proposed_name: "add_div_two_ge_sqrt_mul",
    nearest_existing: [{ name: "Real.geom_mean_le_arith_mean2_weighted", library: "Mathlib", why_not_same: "The weighted AM-GM inequality; with weights 1/2 it gives this one." }],
    reuse_evidence: "Close to Mathlib's weighted AM-GM.", division_reason: "An elementary inequality on real numbers.", checker,
  });
  Object.assign(P["b-thm-cubic"], {
    title: "A cubic inequality from Schur's inequality", reference: "Theorem 4 of the paper", content: "For all real numbers $a, b, c \\ge 0$, $(a+b+c)^3 + 9abc \\ge 4(a+b+c)(ab+bc+ca)$.",
    target_module: "Toolkit/Foundations/Algebra/Schur.lean", new_module_overview: "", proposed_name: "cubic_ge_of_schur",
    nearest_existing: [{ name: "(none found)", library: "Mathlib", why_not_same: "Not in Mathlib or your toolkit." }],
    reuse_evidence: "A known consequence of Schur's inequality, used in olympiad-style estimates.", division_reason: "Beside Schur's inequality, which it follows from.", checker,
  });
});
rmSync(path.join(run, "proposals", "dry_run", `${SLUG}.B.md`), { force: true });
cli("propose", SLUG, "--round", "B", "--toolkit", tk, "--dry-run");
orch("recommend", SLUG, "--toolkit", tk, "B", "b-thm-cubic", "accept", "New to your toolkit and a natural companion of Schur's inequality, which round A added.");
orch("recommend", SLUG, "--toolkit", tk, "B", "b-thm-amgm", "decline", "Mathlib already proves the weighted AM-GM inequality, which gives this one with weights $1/2$; a second copy adds nothing.");
copy("roundB");

// done: round B applied; the repair confirmed and the report as a full run would write it
cli("propose", SLUG, "--round", "B", "--apply", "--recommended", "--toolkit", tk, "--dry-run");
writeFileSync(leanFile, lean(true));
json(path.join(run, "state.json"), (s) => {
  s.verify.phase = "done";
  s.verify.findings.find((f) => f.node === "thm:amgm").patch = { corrected_statement: proposed, proof_note: proof, confirmed: true, narrowed: givenUp };
});
json(path.join(run, "report.json"), (r) => {
  r.verdict = "repaired";
  r.summary = Object.fromEntries(Object.keys(r.summary).map((k) => [k, 0]));
  Object.assign(r.summary, { verified: 3, repaired: 1 });
  r.paper_grade = { grade: "major", major: [{ node: "thm:amgm", what: "weakened: the inequality is no longer claimed when $a$ or $b$ is negative" }], minor: [] };
});
copy("done");

sh([path.join(TOOLS, "scripts", "demo_capture.mjs"), "build", "--raw", raw, "--toolkit", tk, "--paper", PAPER, "--steps", "start=001,review=002,roundA=003,roundB=004,done=005", "--out", path.join(DATA, "snapshots")], "build");
console.log(`[demo_author] snapshots written to ${path.join(DATA, "snapshots")} (work: ${work})`);
