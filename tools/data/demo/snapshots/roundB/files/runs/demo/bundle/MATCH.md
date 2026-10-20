# The corrected paper and its Lean formalization — demo

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Lemma 1

**Statement.** \label{lem:schur} For all real numbers $a, b, c \ge 0$, \[ a(a-b)(a-c) + b(b-a)(b-c) + c(c-a)(c-b) \ge 0 . \]

**Lean.** no declaration

**Status.** not certified: the Lean formalization of it did not close (this is not a claim that the result is wrong).

## Lemma 2

**Statement.** \label{lem:sq} For all real numbers $x$ and $y$, $x^2 + y^2 \ge 2xy$.

**Lean.** no declaration

**Status.** not certified: the Lean formalization of it did not close (this is not a claim that the result is wrong).

## Theorem 3

**Statement (corrected).** For all real numbers $a, b \ge 0$, \[ \frac{a + b}{2} \ge \sqrt{ab} . \]

**Lean.** no declaration

**Status.** not formalized: it is false as printed and has no adopted repair.

## Theorem 4

**Statement.** \label{thm:cubic} For all real numbers $a, b, c \ge 0$, \[ (a + b + c)^3 + 9abc \ge 4(a + b + c)(ab + bc + ca) . \]

**Lean.** no declaration

**Status.** not certified: the Lean formalization of it did not close (this is not a claim that the result is wrong).

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Lemma 1 | `lem:schur` | `lem:schur` | `main.tex:22-27` | — |
| Lemma 2 | `lem:sq` | `lem:sq` | `main.tex:29-31` | — |
| Theorem 3 | `thm:amgm` | `thm:amgm` | `main.tex:39-44` | — |
| Theorem 4 | `thm:cubic` | `thm:cubic` | `main.tex:51-56` | — |
