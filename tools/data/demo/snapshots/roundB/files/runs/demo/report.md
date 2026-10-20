# Correctness report — demo

**Verdict: ERRORS FOUND**

**Paper: MAJOR ERRORS — a main result or the contribution is affected**

Major:

- Theorem 3: weakened: The inequality is no longer claimed when $a$ or $b$ is negative.; false as printed, no repair holds

4 result(s) of the paper were examined. 1 was found wrong as printed: 0 corrected, 1 not repaired. In Lean: 0 proved, 0 taken from the literature as cited, 3 not certified, 1 not formalized.

## What was wrong and what was done

### Theorem 3 — not repaired

- **As printed.** \label{thm:amgm} For all real numbers $a$ and $b$, \[ \frac{a + b}{2} \ge \sqrt{ab} . \]
- **What is wrong.** False for negative numbers: for $a=b=-1$ the left side is $-1$ while the right side is $\sqrt{1}=1$. The proof takes $\sqrt{a}$ and $\sqrt{b}$, which are real numbers only when $a,b\ge 0$.
- **Counterexample.** $a=b=-1$: $\frac{a+b}{2}=-1<1=\sqrt{ab}$.
- **Suggested repair (not applied).** For all real numbers $a, b \ge 0$, \[ \frac{a + b}{2} \ge \sqrt{ab} . \]
- **Owner's decision.** None recorded: the suggestion weakens the result, so it was not applied.
- **Formal check.** not formalized: it is false as printed and has no adopted repair.

## Clarifications (not errors)

None.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Lemma 1 | not certified: the Lean formalization of it did not close (this is not a claim that the result is wrong) | — | — |
| Lemma 2 | not certified: the Lean formalization of it did not close (this is not a claim that the result is wrong) | — | — |
| Theorem 3 | not formalized: it is false as printed and has no adopted repair | — | — |
| Theorem 4 | not certified: the Lean formalization of it did not close (this is not a claim that the result is wrong) | — | — |

**Taken from the literature, not proved here.**

- hlp, Theorem 1 — not checked against its source

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (2 pages). `bundle/MATCH.md` sets each result beside its Lean declaration.

**1 item(s) remain before the paper is ready to submit** (1 blocking), each with its place in the source: `bundle/corrected_paper/TODO.md`. What is checked is the paper's results; the prose around them is the authors', as printed.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `943d23dc47c7585bada40a17d1f9f182973b8074b343002c8aa72696acf9a8b8`)
- stage completed: `5`
- results in scope: 4

| bucket | count |
| --- | --- |
| verified | 0 |
| verified_with_bookkeeping | 0 |
| conditional | 0 |
| repaired | 0 |
| unresolved | 3 |
| not_checked | 0 |
| not_determined | 0 |
| refuted | 1 |

> This is a conditional report. A `verified` result is verified only up to the cited results it assumes, the substrate gates left assumed, and the conditions added during formalization — all listed in full below. `unresolved` means the formalization did not close; it is NOT a claim that the result is wrong. A `refuted` row is a result shown false by a positive witness with no confirmed repair; a `repaired` row was false as printed, and an independent referee confirmed its minimal repair. A `not_determined` row could not be checked as printed: the paper does not say enough to determine the claim, and no reading or repair was adopted; it is NOT a claim that the result is wrong.

## Results

### 1. Schur's inequality {\cite[Theorem~1]{hlp}} `lem:schur`

| field | value |
| --- | --- |
| bucket | `unresolved` |
| source | `main.tex:22-27` (`lemma`, label `lem:schur`) |
| statement | \label{lem:schur} For all real numbers $a, b, c \ge 0$, \[ a(a-b)(a-c) + b(b-a)(b-c) + c(c-a)(c-b) \ge 0 . \] |
| Lean | no declaration anchored |
| crosswalk verdict | — |
| axioms | — |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | `lem:schur` (hlp, Theorem 1) |
| assumed substrate gates | — |
| findings | — |

### 2. `lem:sq`

| field | value |
| --- | --- |
| bucket | `unresolved` |
| source | `main.tex:29-31` (`lemma`, label `lem:sq`) |
| statement | \label{lem:sq} For all real numbers $x$ and $y$, $x^2 + y^2 \ge 2xy$. |
| Lean | no declaration anchored |
| crosswalk verdict | — |
| axioms | — |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. `thm:amgm`

| field | value |
| --- | --- |
| bucket | `refuted` |
| source | `main.tex:39-44` (`theorem`, label `thm:amgm`) |
| statement | \label{thm:amgm} For all real numbers $a$ and $b$, \[ \frac{a + b}{2} \ge \sqrt{ab} . \] |
| Lean | no declaration anchored |
| crosswalk verdict | — |
| axioms | — |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | [refuted, V1.5] False for negative numbers: for $a=b=-1$ the left side is $-1$ while the right side is $\sqrt{1}=1$. The proof takes $\sqrt{a}$ and $\sqrt{b}$, which are real numbers only when $a,b\ge 0$. witness: $a=b=-1$: $\frac{a+b}{2}=-1<1=\sqrt{ab}$. suggested repair (not applied): For all real numbers $a, b \ge 0$, \[ \frac{a + b}{2} \ge \sqrt{ab} . \] |

### 4. `thm:cubic`

| field | value |
| --- | --- |
| bucket | `unresolved` |
| source | `main.tex:51-56` (`theorem`, label `thm:cubic`) |
| statement | \label{thm:cubic} For all real numbers $a, b, c \ge 0$, \[ (a + b + c)^3 + 9abc \ge 4(a + b + c)(ab + bc + ca) . \] |
| Lean | no declaration anchored |
| crosswalk verdict | — |
| axioms | — |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | `lem:schur` (hlp, Theorem 1) |
| assumed substrate gates | — |
| findings | — |

## Errors by root cause

1 independent error(s) — 0 repaired by a minimal patch, 1 not repaired, 0 unfixable and left out of Lean; 0 result(s) inherit one.

### Not repaired

No confirmed repair: the result as printed is false and was not formalized.

- **`thm:amgm`** (`main.tex:39-44`): False for negative numbers: for $a=b=-1$ the left side is $-1$ while the right side is $\sqrt{1}=1$. The proof takes $\sqrt{a}$ and $\sqrt{b}$, which are real numbers only when $a,b\ge 0$.
  - witness: $a=b=-1$: $\frac{a+b}{2}=-1<1=\sqrt{ab}$.
  - suggested repair (not applied): For all real numbers $a, b \ge 0$, \[ \frac{a + b}{2} \ge \sqrt{ab} . \]

## Corrected version

1 of 4 result(s) differ from the version you provided — 1 repaired, 0 with the proof written out in full (no error), 0 only with a side condition or reading made explicit; the others are as printed. The Lean formalization is of the corrected version.

### `thm:amgm` (`main.tex:39-44`)

- as printed: \label{thm:amgm} For all real numbers $a$ and $b$, \[ \frac{a + b}{2} \ge \sqrt{ab} . \]
- corrected: For all real numbers $a, b \ge 0$, \[ \frac{a + b}{2} \ge \sqrt{ab} . \]
- proof change: Apply Lemma~\ref{lem:sq} to $x = \sqrt{a}$ and $y = \sqrt{b}$, real numbers since $a, b \ge 0$: then $x^2 = a$, $y^2 = b$ and $xy = \sqrt{ab}$, so $a + b \ge 2\sqrt{ab}$.
- why: False for negative numbers: for $a=b=-1$ the left side is $-1$ while the right side is $\sqrt{1}=1$. The proof takes $\sqrt{a}$ and $\sqrt{b}$, which are real numbers only when $a,b\ge 0$.

## Added conditions

None: no condition was added to the paper's own hypotheses.

## Conditions assumed

### Cited results

| id | used by | citation | locator | checked against |
| --- | --- | --- | --- | --- |
| `lem:schur` | `lem:schur` | hlp | Theorem 1 | NOT checked against its source |
| `lem:schur` | `thm:cubic` | hlp | Theorem 1 | NOT checked against its source |

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- `lem:schur` (unresolved, `main.tex:22-27`): no Lean declaration was anchored to it
- `lem:sq` (unresolved, `main.tex:29-31`): no Lean declaration was anchored to it
- `thm:amgm` (refuted, `main.tex:39-44`): [refuted, V1.5] False for negative numbers: for $a=b=-1$ the left side is $-1$ while the right side is $\sqrt{1}=1$. The proof takes $\sqrt{a}$ and $\sqrt{b}$, which are real numbers only when $a,b\ge 0$. witness: $a=b=-1$: $\frac{a+b}{2}=-1<1=\sqrt{ab}$. suggested repair (not applied): For all real numbers $a, b \ge 0$, \[ \frac{a + b}{2} \ge \sqrt{ab} . \]
- `thm:cubic` (unresolved, `main.tex:51-56`): no Lean declaration was anchored to it

## Lean evidence

Not collected: not collected: --dry-run

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (4 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | absent: dry run (the F stages wrote nothing) |
| `graph.json` | absent: dry run (the F stages wrote nothing) |
| Lean evidence | not collected: --dry-run |

## Annotated paper

Annotated paper: `annotated/main.tex` (1 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
