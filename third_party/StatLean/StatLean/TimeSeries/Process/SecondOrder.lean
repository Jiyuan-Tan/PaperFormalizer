module
public import StatLean.TimeSeries.Process.Defs
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Weakly stationary processes — second-order structure (FY §2.1.1, §2.2.1)

Consequences of `IsStationary`: integrability of the marginals, the anchor-freeness of
the autocovariance (`Cov(X_s, X_t)` depends only on `s − t`), and the identification of
`acvf X μ 0` with the common variance.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.1
(Definition 2.1) and §2.2.1 (p. 39, the unnumbered display `Cov(X_{t+k}, X_t) =
Cov(X_k, X_0)`). (`FY §2.1.1, §2.2.1`.)

**Proof formalization notes.** `cov_eq_acvf` is the `cov_shift` field applied at the
anchor `t` with lag `s − t`, plus the group identity `t + (s − t) = s`. Integrability is
`MemLp` monotonicity of exponents on a probability space.

**Bibliographic comments.** Classical second-order (Khinchin) theory; see Doob (1953),
ch. X.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℤ → Ω → ℝ}

/-- Marginals of a weakly stationary process are integrable (on a probability space). -/
theorem IsStationary.integrable [IsProbabilityMeasure μ] (h : IsStationary X μ)
    (t : ℤ) : Integrable (X t) μ :=
  memLp_one_iff_integrable.mp ((h.memLp t).mono_exponent one_le_two)

/-- Anchor-freeness (FY §2.2.1): for a weakly stationary process,
`Cov(X_s, X_t) = γ(s − t)`. -/
theorem IsStationary.cov_eq_acvf (h : IsStationary X μ) (s t : ℤ) :
    cov[X s, X t; μ] = acvf X μ (s - t) := by
  have ht : t + (s - t) = s := by ring
  have := h.cov_shift t (s - t)
  rw [ht] at this
  exact this

/-- The lag-`0` autocovariance is the (time-constant) variance. -/
theorem IsStationary.acvf_zero_eq_variance (h : IsStationary X μ) (t : ℤ) :
    acvf X μ 0 = variance (X t) μ := by
  have h1 := h.cov_eq_acvf t t
  rw [sub_self] at h1
  rw [← h1, covariance_self (h.memLp t).aestronglyMeasurable.aemeasurable]

/-- `γ(0) ≥ 0`. -/
theorem IsStationary.acvf_zero_nonneg (h : IsStationary X μ) :
    0 ≤ acvf X μ 0 := by
  rw [h.acvf_zero_eq_variance 0]
  exact variance_nonneg _ _

end StatLean.TimeSeries
