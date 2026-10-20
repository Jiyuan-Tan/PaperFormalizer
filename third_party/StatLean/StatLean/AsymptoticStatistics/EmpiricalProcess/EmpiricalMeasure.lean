module
public import StatLean.AsymptoticStatistics.ForMathlib.EmpiricalAverage
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section

/-!
# Empirical measure of a finite sample

Given a sample $X_1, \dots, X_n$ taking values in a measurable space $\Omega$, the
**empirical measure** is the discrete probability measure that places mass $1/n$ at
each observation,
$$\mathbb{P}_n \;=\; \frac{1}{n} \sum_{i=1}^{n} \delta_{X_i},$$
where $\delta_x$ is the Dirac point mass at $x$. It is the natural (unbiased) estimator
of an underlying distribution $P$: for any integrable $f$ the empirical average
$$\mathbb{P}_n f \;=\; \int f \, d\mathbb{P}_n \;=\; \frac{1}{n}\sum_{i=1}^{n} f(X_i)$$
estimates $P f = \int f \, dP$. When $n \ge 1$, $\mathbb{P}_n$ is a probability measure
(total mass $1$). All higher-level empirical-process objects (the centred empirical
process $\mathbb{G}_n$, the Glivenko–Cantelli predicate, the Donsker predicate) are
stated in terms of integrals against this measure or, equivalently, against the
real-valued empirical-average shorthand `empiricalAvg`.

Main declarations: `empiricalMeasure`, `empiricalAvg`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998. Chapter 19
(Empirical Processes), §19.1. (The empirical measure $\mathbb{P}_n$ and the notation
$\mathbb{P}_n f$ for $\frac1n\sum_i f(X_i)$ are introduced there as the basic objects of
the chapter.)

**Proof formalization notes.** The Lean definition `empiricalMeasure n X` is
$(n : \mathbb{R}_{\ge 0}^{\infty})^{-1} \cdot \sum_i \mathrm{dirac}(X_i)$, a scalar
multiple of a finite sum of Dirac measures. Edge behaviour: for $n = 0$ the index set
`Fin 0` is empty, the sum is the zero measure, and the prefactor
$(0 : \mathbb{R}_{\ge 0}^{\infty})^{-1} = \infty$ collapses against the zero measure to
leave the zero measure; the `IsProbabilityMeasure` instance is therefore stated under the
`[NeZero n]` hypothesis. The probability-measure proof evaluates total mass via
`Measure.smul_apply` / `Measure.coe_finset_sum`, uses
`Measure.dirac_apply_of_mem` to get each $\delta_{X_i}(\Omega) = 1$, sums to $n$, and
closes with `ENNReal.inv_mul_cancel`. The real shorthand `empiricalAvg f n X` is
$(n : \mathbb{R})^{-1} \cdot \sum_i f(X_i)$; here Lean's convention
$(0 : \mathbb{R})^{-1} = 0$ makes the $n = 0$ case evaluate to $0$. The accompanying
lemmas record that `empiricalAvg` is linear in $f$ (additivity `empiricalAvg_add`,
scalar homogeneity `empiricalAvg_smul`) and vanishes on the zero function.

**Bibliographic comments.** The empirical measure is folklore foundational
material with no single seminal originating paper. Its scalar-CDF special case, the
empirical distribution function $F_n(t) = \frac1n\#\{i : X_i \le t\}$, traces to the
uniform-convergence results of V. Glivenko, "Sulla determinazione empirica delle leggi di
probabilità," *Giornale dell'Istituto Italiano degli Attuari* 4 (1933), 92–99, and
F. P. Cantelli, "Sulla determinazione empirica delle leggi di probabilità," same volume,
421–424. The general empirical-measure-on-an-abstract-space viewpoint used here is the
modern synthesis presented in van der Vaart (1998, Chapter 19) and in A. W. van der Vaart
and J. A. Wellner, *Weak Convergence and Empirical Processes*, Springer, 1996.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **empirical measure** of a sample `X : Fin n → Ω`:

`empiricalMeasure n X = (1/n) · Σᵢ Measure.dirac (X i)`.

Edge: for `n = 0`, the indexing `Fin 0` is empty and the sum is the
zero measure; the scaling `(0 : ℝ≥0∞)⁻¹ = ∞` collapses against `0`
to leave the zero measure. The `IsProbabilityMeasure` instance is
therefore stated under `[NeZero n]`.

vdV §19.1: the natural unbiased estimator of an
underlying distribution `P`. -/
noncomputable def empiricalMeasure (n : ℕ) (X : Fin n → Ω) : Measure Ω :=
  ((n : ℝ≥0∞))⁻¹ • ∑ i, Measure.dirac (X i)

@[simp] lemma empiricalMeasure_zero (X : Fin 0 → Ω) :
    empiricalMeasure 0 X = 0 := by
  unfold empiricalMeasure
  simp

/-- The empirical measure is a probability measure for `n ≥ 1`. -/
instance instIsProbabilityMeasure_empiricalMeasure
    (n : ℕ) [NeZero n] (X : Fin n → Ω) : IsProbabilityMeasure (empiricalMeasure n X) := by
  refine ⟨?_⟩
  unfold empiricalMeasure
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
  have hsum : (∑ i : Fin n, (Measure.dirac (X i) : Measure Ω) Set.univ)
      = (n : ℝ≥0∞) := by
    have hi : ∀ i : Fin n, (Measure.dirac (X i) : Measure Ω) Set.univ = 1 :=
      fun i => Measure.dirac_apply_of_mem (Set.mem_univ _)
    simp [hi]
  rw [hsum, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (NeZero.ne n)) (natCast_ne_top n)

end AsymptoticStatistics.EmpiricalProcess
