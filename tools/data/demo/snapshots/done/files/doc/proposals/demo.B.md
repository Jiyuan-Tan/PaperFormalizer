# Results from demo proposed for your toolkit

Created 2026-10-17T18:38:23.699Z. The paper's formalization proved 2 result(s) that could join your toolkit.
Each is one main result; "If accepted" says how it enters the toolkit. Decide each by editing the
`decision:` line in its `decision` block:

- `accept` — bring it into your toolkit as the entry says; the paper then uses it from there.
- `accept_with_edits` — the same, with your changes: add an `edits:` line, then one `<field>: <value>`
  line per change (fields: division, target_module, proposed_name, title, reference, content; indented lines continue a value).
  What the result proves is not edited; on one of the paper's own results `content` cannot change.
- `generalize_first` — build a general form of it in your toolkit; the paper's result becomes its corollary.
- `decline` — keep it inside the paper.
- `defer` — not now; it stays in the paper and may be proposed again.
- Any decision may carry a `note: <text>` line; it is kept in the ledger.

Then run:

    theoremchecker propose demo --round B --apply --toolkit @@TOOLKIT@@ --dry-run

## b-thm-amgm · AM-GM for two nonnegative reals

**Goes to.** Foundations › Algebra — An elementary inequality on real numbers.

**Reference.** Theorem 3 of the paper (as corrected)

**Content.**

> For all real numbers $a, b \ge 0$, $\frac{a+b}{2} \ge \sqrt{ab}$.

**Why it is reusable.** Close to Mathlib's weighted AM-GM.

**In your other papers.** first time — no other paper of yours states it.

**Closest existing results.**
  - The weighted AM-GM inequality; with weights 1/2 it gives this one. (Mathlib: Real.geom_mean_le_arith_mean2_weighted)

**If accepted.** Moves as is into your toolkit, with the helper lemmas proving it; the paper then uses it from there. (`generalize_first` builds a general form instead.)

**Independent check.** agrees — The statement matches the paper's result.

<details><summary>Lean details</summary>

- Name in the toolkit: `add_div_two_ge_sqrt_mul` in `Toolkit/Foundations/Algebra/MeanInequalities.lean` (Foundations) — a new module: Inequalities between means of nonnegative reals.
- Proved in the paper as `Papers.Demo.thm_amgm`
- Lean statement (the paper's instance):

  ```lean
  For all real numbers $a, b \ge 0$, \[ \frac{a + b}{2} \ge \sqrt{ab} . \]
  ```

- Moves with it (the helper lemmas proving it and the definitions it needs): nothing else

</details>

```decision
decision: decline
note: as the agent recommended: Mathlib already proves the weighted AM-GM inequality, which gives this one with weights $1/2$; a second copy adds nothing.
```

## b-thm-cubic · A cubic inequality from Schur's inequality

**Goes to.** Foundations › Algebra — Beside Schur's inequality, which it follows from.

**Reference.** Theorem 4 of the paper

**Content.**

> For all real numbers $a, b, c \ge 0$, $(a+b+c)^3 + 9abc \ge 4(a+b+c)(ab+bc+ca)$.

**Why it is reusable.** A known consequence of Schur's inequality, used in olympiad-style estimates.

**In your other papers.** first time — no other paper of yours states it.

**Closest existing results.**
  - Not in Mathlib or your toolkit. (Mathlib: (none found))

**If accepted.** Moves as is into your toolkit, with the helper lemmas proving it; the paper then uses it from there. (`generalize_first` builds a general form instead.)

**Independent check.** agrees — The statement matches the paper's result.

<details><summary>Lean details</summary>

- Name in the toolkit: `cubic_ge_of_schur` in `Toolkit/Foundations/Algebra/Schur.lean` (Foundations)
- Proved in the paper as `Papers.Demo.thm_cubic`
- Lean statement (the paper's instance):

  ```lean
  \label{thm:cubic} For all real numbers $a, b, c \ge 0$, \[ (a + b + c)^3 + 9abc \ge 4(a + b + c)(ab + bc + ca) . \]
  ```

- Moves with it (the helper lemmas proving it and the definitions it needs): nothing else

</details>

```decision
decision: accept
note: as the agent recommended: New to your toolkit and a natural companion of Schur's inequality, which round A added.
```

## Already available (declined automatically)

- `lem_schur` is already stated by `Toolkit.Foundations.Algebra.schur_inequality`; the paper could use that instead.
- `lem_sq` is already stated by `two_mul_le_add_sq`; the paper could use that instead.
