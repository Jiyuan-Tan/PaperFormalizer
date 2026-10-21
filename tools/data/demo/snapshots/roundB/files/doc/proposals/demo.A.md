# Cited results from demo proposed for your toolkit

Created 2026-10-17T18:38:17.330Z. The paper relies on 1 cited result(s) it does not prove that could join your toolkit.
Unbuilt, each stays an assumption of the paper. Decide each by editing the `decision:` line in its
`decision` block:

- `accept` — build it in your toolkit (proved and reviewed before the paper's proofs); the paper then
  uses it instead of assuming it. Building a deep result takes a while.
- `accept_with_edits` — the same, with your changes: add an `edits:` line, then one `<field>: <value>`
  line per change (fields: division, target_module, proposed_name, title, reference, content; indented lines continue a value).
- `decline` — it stays a cited assumption of the paper.
- `defer` — not now; it stays an assumption and may be proposed again.
- Any decision may carry a `note: <text>` line; it is kept in the ledger.

Then run:

    paperformalizer propose demo --round A --apply --toolkit @@TOOLKIT@@ --dry-run

## a-lem-schur · Schur's inequality (exponent 1)

**Goes to.** Foundations › Algebra — An elementary inequality on real numbers.

**Reference.** Hardy, Littlewood and P\'olya, \emph{Inequalities}, Theorem 1

**Content.**

> For all real numbers $a, b, c \ge 0$, $a(a-b)(a-c) + b(b-a)(b-c) + c(c-a)(c-b) \ge 0$.

**Why it is reusable.** A standard inequality, cited by many papers on polynomial inequalities; not in Mathlib.

**In your other papers.** first time — no other paper of yours states it.

**Closest existing results.**
  - Mathlib has no Schur inequality for real numbers. (Mathlib: (none found))

**If accepted.** It is built in your toolkit from scratch (stated as above, proved and reviewed); the paper then uses it instead of assuming it.

**Independent check.** agrees — The statement is the classical Schur inequality with exponent 1.

<details><summary>Lean details</summary>

- Name in the toolkit: `schur_inequality` in `Toolkit/Foundations/Algebra/Schur.lean` (Foundations) — a new module: Classical polynomial inequalities for nonnegative reals.
- Cited by the paper as `lem:schur` (G.~H. Hardy, J.~E. Littlewood and G.~P\'olya, \emph{Inequalities}, 2nd ed., Cambridge University Press, 1952., Theorem 1); assumed until built

</details>

```decision
decision: accept
note: as the agent recommended: Schur's inequality is a standard tool that Mathlib lacks; building it once lets this paper and later ones use it instead of assuming it.
```
