module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Empirical process `G_n f = √n · (P_n f − P f)`

For a real-valued function $f : \Omega \to \mathbb{R}$ and an i.i.d. sample
$X_1, \dots, X_n$ drawn from a distribution $P$, the **empirical process** is
the centred, $\sqrt{n}$-scaled empirical measure
$$
\mathbb{G}_n f \;=\; \sqrt{n}\,\bigl(\mathbb{P}_n f - P f\bigr),
\qquad
\mathbb{P}_n f = \frac{1}{n}\sum_{i=1}^n f(X_i),
\quad P f = \int f \, dP .
$$
Indexed over a function class $\mathcal{F}$, $\{\mathbb{G}_n f : f \in \mathcal{F}\}$
is the object whose limiting behaviour the Glivenko–Cantelli (uniform law of
large numbers) and Donsker (uniform central limit) theorems characterise.

This file provides the definition together with its degenerate-`n` value and
the two linearity-in-`f` properties (additivity and scalar homogeneity).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 19 (Empirical Processes), §19.1 (introduction of the empirical process
$\mathbb{G}_n = \sqrt{n}(\mathbb{P}_n - P)$).

**Proof formalization notes.**
Operationally we use the empirical-average shorthand `empiricalAvg` in place of
$\int f \, d\mathbb{P}_n$; the two agree on measurable functions, so
`empiricalProcess P n X f` is `Real.sqrt n * (empiricalAvg f n X - ∫ x, f x ∂P)`.

* Edge case $n = 0$: `empiricalAvg f 0 X = 0` and `Real.sqrt 0 = 0`, so
  `empiricalProcess P 0 X f = 0`. Recorded as the simp lemma
  `empiricalProcess_zero`.
* Additivity `empiricalProcess_add` requires `Integrable f P` and
  `Integrable g P` so that the population term splits via `integral_add`; the
  empirical term splits unconditionally via `empiricalAvg_add`.
* Scalar homogeneity `empiricalProcess_smul` is unconditional, using
  `empiricalAvg_smul` and `integral_const_mul`.

**Bibliographic comments.** The empirical process $\mathbb{G}_n$ as a centred,
$\sqrt n$-scaled measure is foundational/folklore with no single seminal source;
its definition is the natural normalization making the classical limit theorems
non-degenerate. The two theorems it underpins do have canonical origins:
V. Glivenko, "Sulla determinazione empirica delle leggi di probabilità",
*Giornale dell'Istituto Italiano degli Attuari* **4** (1933), 92–99, and
F. P. Cantelli, "Sulla determinazione empirica delle leggi di probabilità",
*ibid.* **4** (1933), 421–424 (uniform law of large numbers); and
M. D. Donsker, "Justification and extension of Doob's heuristic approach to the
Kolmogorov–Smirnov theorems", *Annals of Mathematical Statistics* **23** (1952),
277–281 (the functional/uniform central limit theorem for $\mathbb{G}_n$). The
abstract function-class formulation used here follows van der Vaart §19.1.

Main definition: `empiricalProcess`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **empirical process** `G_n f = √n · (P_n f − P f)`, where `P_n`
is the empirical measure of a sample `X : Fin n → Ω` and `P` is the
underlying distribution.

Operationally we use the empirical-average shorthand `empiricalAvg`
in place of `∫ f dP_n`; the two agree on measurable functions.

Edge: for `n = 0`, `empiricalAvg f 0 X = 0` and `Real.sqrt 0 = 0`, so
`empiricalProcess P 0 X f = -0 * ∫ f dP = 0`. Stated explicitly via
`empiricalProcess_zero`.

vdV §19.1: the centred, `√n`-scaled empirical measure indexed by `f`. -/
noncomputable def empiricalProcess
    (P : Measure Ω) (n : ℕ) (X : Fin n → Ω) (f : Ω → ℝ) : ℝ :=
  Real.sqrt n * (empiricalAvg f n X - ∫ x, f x ∂P)

@[simp] lemma empiricalProcess_zero (P : Measure Ω) (X : Fin 0 → Ω) (f : Ω → ℝ) :
    empiricalProcess P 0 X f = 0 := by
  simp [empiricalProcess]

lemma empiricalProcess_add (P : Measure Ω) (n : ℕ) (X : Fin n → Ω)
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P) :
    empiricalProcess P n X (fun x => f x + g x) =
      empiricalProcess P n X f + empiricalProcess P n X g := by
  unfold empiricalProcess
  rw [empiricalAvg_add, integral_add hf hg]
  ring

lemma empiricalProcess_smul (P : Measure Ω) (n : ℕ) (X : Fin n → Ω)
    (c : ℝ) (f : Ω → ℝ) :
    empiricalProcess P n X (fun x => c * f x) = c * empiricalProcess P n X f := by
  unfold empiricalProcess
  rw [empiricalAvg_smul, integral_const_mul]
  ring

lemma empiricalProcess_sub (P : Measure Ω) (n : ℕ) (X : Fin n → Ω)
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P) :
    empiricalProcess P n X (fun x => f x - g x) =
      empiricalProcess P n X f - empiricalProcess P n X g := by
  have havg : empiricalAvg (fun x => f x - g x) n X
      = empiricalAvg f n X - empiricalAvg g n X := by
    have : (fun x => f x - g x) = (fun x => f x + (-1 : ℝ) * g x) := by
      funext x; ring
    rw [this, empiricalAvg_add, empiricalAvg_smul]; ring
  unfold empiricalProcess
  rw [havg, integral_sub hf hg]
  ring

end AsymptoticStatistics.EmpiricalProcess
