module
public import StatLean.PointEstimation.ExponentialFamily.Basic
public import Mathlib.Probability.Moments.Tilted
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Moment and cumulant generating functions of the natural statistic

For an exponential family in canonical form the moment generating function of the natural
statistic is a ratio of normalizing constants, and the cumulant generating function is a
difference of log-partition values:
$$ E_\eta\bigl[e^{\langle u, T\rangle}\bigr] \;=\; e^{A(\eta+u) - A(\eta)}, $$
valid whenever both `η` and `η + u` lie in the natural parameter set. Differentiating the
identity `∫ exp(⟨η,T⟩ − A(η)) dν = 1` at an interior natural parameter gives the mean and the
variance of the natural statistic as the first and second derivatives of the log-partition
function.

* `ExpFamily.natSet_eq_integrableExpSet`, `ExpFamily.logPartition_eq_cgf`,
  `ExpFamily.P_eq_tilted_mul` — the one-dimensional bridge to Mathlib's `mgf`/`cgf` API;
* `ExpFamily.integral_exp_inner_P` — the moment/cumulant generating function identity;
* `ExpFamily.integral_stat_P` — the mean of the natural statistic is `A'(η)`;
* `ExpFamily.variance_stat_P` — the variance of the natural statistic is `A''(η)`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.5
(Exponential Families), Theorem 5.10 (moment and cumulant generating functions of the natural
statistic). (`TPE2 §1.5 Thm 5.10`.)

**Proof formalization notes.**
* `integral_exp_inner_P` is `MeasureTheory.integral_exp_tilted` (which computes
  `∫ exp(g) ∂(μ.tilted f) = (∫ exp(f+g) ∂μ) / ∫ exp f ∂μ`) plus additivity of the inner
  product in its first argument and `Real.exp_log` on the two normalizers.
* The nondegeneracy hypothesis `E.base ≠ 0` in `integral_exp_inner_P` is **not** cosmetic: for
  the zero reference measure the left-hand side is `0` while the right-hand side is
  `exp(0 − 0) = 1`, since both log-partition values degenerate to `log 0 = 0`.
* The one-dimensional moment identities are the exponential-family reading of Mathlib's
  `ProbabilityTheory.integral_tilted_mul_self` (`(μ.tilted (t * X ·))[X] = deriv (cgf X μ) t`)
  and `ProbabilityTheory.variance_tilted_mul`
  (`Var[X; μ.tilted (t * X ·)] = iteratedDeriv 2 (cgf X μ) t`), which in turn rest on
  `ProbabilityTheory.deriv_cgf` and `ProbabilityTheory.iteratedDeriv_two_cgf`. Neither
  Mathlib lemma carries a nondegeneracy hypothesis — both sides vanish for the zero measure —
  so neither do ours.
* The three bridge lemmas exist to close the syntactic gap: our natural parameter set,
  log-partition and member are phrased with `⟪η, T x⟫_ℝ`, which for `V = ℝ` reduces to
  `T x * η` (`RCLike.inner_apply`), while Mathlib's `integrableExpSet`, `cgf` and
  `Measure.tilted` are phrased with `η * T x`. The gap is exactly one `mul_comm`.
* The multivariate analogues of the moment identities — the gradient and Hessian of the
  log-partition function — are obtained by composing `integral_exp_inner_P` with the
  differentiation results of `ExponentialFamily.Smoothness`; they are not restated here.

**Bibliographic comments.** The identification of the derivatives of the log-partition
function with the cumulants of the natural statistic is classical, going back to R. A. Fisher
("Two new properties of mathematical likelihood," *Proc. R. Soc. Lond. A* **144** (1934),
285–307); the modern convex-analytic account is due to O. Barndorff-Nielsen (*Information
and Exponential Families in Statistical Theory*, Wiley, 1978, Ch. 7–9) and L. D. Brown
(*Fundamentals of Statistical Exponential Families*, IMS Lecture Notes 9, 1986, Ch. 2).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

namespace ExpFamily

/-- On `ℝ` the inner product is multiplication (with our `⟪η, ·⟫` matching Mathlib's `η · ·`). -/
private theorem inner_real_eq (η t : ℝ) : ⟪η, t⟫_ℝ = η * t := by
  rw [← real_inner_comm]; rfl

section RealBridge

/-- For a real natural statistic the natural parameter set is Mathlib's `integrableExpSet`. -/
theorem natSet_eq_integrableExpSet (E : ExpFamily 𝓧 ℝ) :
    E.natSet = integrableExpSet E.stat E.base := by
  ext η
  simp only [ExpFamily.natSet, integrableExpSet, Set.mem_setOf_eq]
  exact integrable_congr (Filter.Eventually.of_forall fun x => by simp only [inner_real_eq])

/-- For a real natural statistic the log-partition function is Mathlib's cumulant generating
function of the statistic under the reference measure. -/
theorem logPartition_eq_cgf (E : ExpFamily 𝓧 ℝ) : E.logPartition = cgf E.stat E.base := by
  funext η
  simp only [ExpFamily.logPartition, cgf, mgf]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [inner_real_eq])

/-- For a real natural statistic the member is Mathlib's exponential tilt by `η · T`. -/
theorem P_eq_tilted_mul (E : ExpFamily 𝓧 ℝ) (η : ℝ) :
    E.P η = E.base.tilted fun x => η * E.stat x := by
  rw [show E.P η = E.base.tilted (fun x => ⟪η, E.stat x⟫_ℝ) from rfl]
  exact tilted_congr (Filter.Eventually.of_forall fun x => inner_real_eq η (E.stat x))

end RealBridge

section GeneratingFunctions

variable [OpensMeasurableSpace V]

/-- **Moment generating function of the natural statistic.** For `η` and `η + u` in the
natural parameter set,
`E_η[exp⟨u, T⟩] = exp(A(η + u) − A(η))`; equivalently the cumulant generating function of `T`
under `P_η` is `u ↦ A(η + u) − A(η)`. -/
theorem integral_exp_inner_P (E : ExpFamily 𝓧 V) {η u : V}
    -- USER-INPUT: nondegenerate reference measure; the identity is false for `E.base = 0`,
    -- where the left-hand side is `0` and the right-hand side is `1`
    (hbase : E.base ≠ 0)
    -- USER-INPUT: the base point lies where the family is defined
    (hη : η ∈ E.natSet)
    -- USER-INPUT: the shifted point lies where the family is defined; this is exactly the
    -- classical requirement that the generating function exist near the origin
    (hηu : η + u ∈ E.natSet) :
    ∫ x, Real.exp ⟪u, E.stat x⟫_ℝ ∂(E.P η)
      = Real.exp (E.logPartition (η + u) - E.logPartition η) := by
  haveI : NeZero E.base := ⟨hbase⟩
  have hηu_pos : 0 < ∫ x, Real.exp ⟪η + u, E.stat x⟫_ℝ ∂E.base := integral_exp_pos hηu
  have hη_pos : 0 < ∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base := integral_exp_pos hη
  rw [show E.P η = E.base.tilted (fun x => ⟪η, E.stat x⟫_ℝ) from rfl, integral_exp_tilted]
  have hnum : ∫ x, Real.exp (((fun x => ⟪η, E.stat x⟫_ℝ) + fun x => ⟪u, E.stat x⟫_ℝ) x) ∂E.base
      = ∫ x, Real.exp ⟪η + u, E.stat x⟫_ℝ ∂E.base :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Pi.add_apply, inner_add_left])
  rw [hnum, Real.exp_sub]
  simp only [ExpFamily.logPartition]
  rw [Real.exp_log hηu_pos, Real.exp_log hη_pos]

end GeneratingFunctions

section Moments

/-- **Mean of the natural statistic**: at an interior natural parameter the expectation of `T`
under `P_η` is the derivative of the log-partition function. -/
theorem integral_stat_P (E : ExpFamily 𝓧 ℝ) {η : ℝ}
    -- USER-INPUT: interior natural parameter; interiority is what licenses differentiation
    -- under the integral sign and is the classical hypothesis of the moment formulas
    (hη : η ∈ interior E.natSet) :
    ∫ x, E.stat x ∂(E.P η) = deriv E.logPartition η := by
  have hmem : η ∈ interior (integrableExpSet E.stat E.base) := by
    rw [← natSet_eq_integrableExpSet]; exact hη
  rw [P_eq_tilted_mul, integral_tilted_mul_self hmem, logPartition_eq_cgf]

/-- **Variance of the natural statistic**: at an interior natural parameter the variance of
`T` under `P_η` is the second derivative of the log-partition function. -/
theorem variance_stat_P (E : ExpFamily 𝓧 ℝ) {η : ℝ}
    -- USER-INPUT: interior natural parameter; see `integral_stat_P`
    (hη : η ∈ interior E.natSet) :
    variance E.stat (E.P η) = iteratedDeriv 2 E.logPartition η := by
  have hmem : η ∈ interior (integrableExpSet E.stat E.base) := by
    rw [← natSet_eq_integrableExpSet]; exact hη
  rw [P_eq_tilted_mul, variance_tilted_mul hmem, logPartition_eq_cgf]

end Moments

end ExpFamily

end StatLean.PointEstimation
