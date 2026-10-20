module
public import StatLean.PointEstimation.UMVU.Defs

@[expose] public section

/-!
# Unbiased estimation: the affine structure of the unbiased class, and uniqueness of UMVU

Two structural facts underlying the whole theory of minimum-variance unbiased estimation.

* `isUnbiased_iff_sub_unbiasedZero` — once one unbiased estimator `δ₀` of `g` is available,
  the unbiased estimators of `g` are exactly the differences `δ₀ - U` with `U` an unbiased
  estimator of zero. Estimating `g` well is therefore the same problem as approximating `δ₀`
  from the linear space of unbiased estimators of zero, which is what makes the covariance
  criterion (and its projection reading) possible.
* `isUMVU_unique` — a uniformly minimum variance unbiased estimator is unique up to almost
  everywhere equality under every member of the model. This is why one speaks of *the* UMVU
  estimator.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.1 (UMVU
Estimators), Lemma 1.4 (the unbiased estimators of `g` are `δ₀` minus the unbiased estimators
of zero) and the uniqueness of the UMVU estimator. (`TPE2 §2.1 Lem 1.4`.)

**Proof formalization notes.**
* The equivalence is stated in the "difference" form `IsUnbiasedZero P (δ₀ - δ)` rather than
  as an existential `∃ U, δ = δ₀ - U`: the two are trivially interchangeable (take
  `U := δ₀ - δ`), and the difference form is the one every downstream argument uses. The set
  form of the classical statement follows immediately and is not stated separately.
* Integrability of `δ₀` and of `δ` under every member is required in both directions: means
  split additively only for integrable functions, and unbiasedness as defined is an equation
  between Bochner integrals, whose junk value `0` for non-integrable functions would
  otherwise make the equivalence false rather than merely unprovable.
* Uniqueness is proved parameter by parameter and needs only local minimality at that
  parameter: given two UMVU estimators, their variances agree, the average
  `(δ₁ + δ₂)/2` is again unbiased and square-integrable, and comparing its variance with the
  common value forces equality in the Cauchy–Schwarz bound for `cov(δ₁, δ₂)`, hence an affine
  relation between the centered estimators; equal variances and equal means then give
  `δ₁ = δ₂` almost everywhere. The degenerate case of zero variance is the statement that both
  are almost everywhere constant, equal to `g θ`.
* No measurability hypothesis appears: `MemEstL2` already carries almost-everywhere strong
  measurability under each member through `MemLp`.

**Bibliographic comments.** The systematic theory of minimum-variance unbiased estimation is
due to C. R. Rao ("Information and the accuracy attainable in the estimation of statistical
parameters," *Bull. Calcutta Math. Soc.* **37** (1945), 81–91; "Sufficient statistics and
minimum variance estimates," *Proc. Camb. Phil. Soc.* **45** (1949), 213–218), D. Blackwell
("Conditional expectation and unbiased sequential estimation," *Ann. Math. Statist.* **18**
(1947), 105–110) and E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and
unbiased estimation," *Sankhyā* **10** (1950), 305–340). The reading of the unbiased class as
an affine subspace, with the minimum-variance element obtained by projecting onto the space of
unbiased estimators of zero, is developed by R. R. Bahadur ("On unbiased estimates of
uniformly minimum variance," *Sankhyā* **18** (1957), 211–224).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **The unbiased class is `δ₀` minus the unbiased estimators of zero.** Given one unbiased
estimator `δ₀` of `g`, an integrable `δ` is unbiased for `g` exactly when `δ₀ - δ` is an
unbiased estimator of zero. -/
theorem isUnbiased_iff_sub_unbiasedZero (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (g : Θ → ℝ) {δ₀ δ : 𝓧 → ℝ}
    -- USER-INPUT: a reference unbiased estimator of the estimand; the classical starting point
    (hδ₀ : IsUnbiased P g δ₀)
    -- LEAN-ONLY: integrability of the reference estimator under every member, so that means
    -- split additively (Bochner integrals return junk `0` otherwise)
    (hδ₀i : ∀ θ, Integrable δ₀ (P θ))
    -- LEAN-ONLY: integrability of the candidate estimator, same reason
    (hδi : ∀ θ, Integrable δ (P θ)) :
    IsUnbiased P g δ ↔ IsUnbiasedZero P (fun x => δ₀ x - δ x) := by
  constructor
  · intro hδu θ
    rw [integral_sub (hδ₀i θ) (hδi θ), hδ₀ θ, hδu θ, sub_self]
  · intro hz θ
    have h := hz θ
    rw [integral_sub (hδ₀i θ) (hδi θ), hδ₀ θ] at h
    linarith

/-- **Uniqueness of the UMVU estimator.** Two uniformly minimum variance unbiased estimators
of the same estimand agree almost everywhere under every member of the model. -/
theorem isUMVU_unique (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)] (g : Θ → ℝ)
    {δ₁ δ₂ : 𝓧 → ℝ}
    -- USER-INPUT: the first UMVU estimator
    (h₁ : IsUMVU P g δ₁)
    -- USER-INPUT: the second UMVU estimator of the same estimand
    (h₂ : IsUMVU P g δ₂) (θ : Θ) :
    δ₁ =ᵐ[P θ] δ₂ := by
  obtain ⟨h1u, h1L2, h1min⟩ := h₁
  obtain ⟨h2u, h2L2, h2min⟩ := h₂
  have int1 : ∀ θ', Integrable δ₁ (P θ') := fun θ' => (h1L2 θ').integrable one_le_two
  have int2 : ∀ θ', Integrable δ₂ (P θ') := fun θ' => (h2L2 θ').integrable one_le_two
  -- the average `η = (δ₁ + δ₂)/2` is again an unbiased square-integrable competitor
  have hηu : IsUnbiased P g (fun x => 2⁻¹ * (δ₁ x + δ₂ x)) := by
    intro θ'
    rw [integral_const_mul, integral_add (int1 θ') (int2 θ'), h1u θ', h2u θ']
    ring
  have hηL2 : MemEstL2 P (fun x => 2⁻¹ * (δ₁ x + δ₂ x)) := fun θ' =>
    ((h1L2 θ').add (h2L2 θ')).const_mul 2⁻¹
  -- both variances are equal by mutual minimality
  have hv : variance δ₁ (P θ) = variance δ₂ (P θ) :=
    le_antisymm (h1min δ₂ h2u h2L2 θ) (h2min δ₁ h1u h1L2 θ)
  -- minimality of `δ₁` bounds the covariance from below
  have hmin_η : variance δ₁ (P θ) ≤ variance (fun x => 2⁻¹ * (δ₁ x + δ₂ x)) (P θ) :=
    h1min _ hηu hηL2 θ
  rw [variance_const_mul, variance_fun_add (h1L2 θ) (h2L2 θ)] at hmin_η
  -- the difference has zero variance and zero mean, hence vanishes a.e.
  have hsub : variance (fun ω => δ₁ ω - δ₂ ω) (P θ)
      = variance δ₁ (P θ) - 2 * covariance δ₁ δ₂ (P θ) + variance δ₂ (P θ) :=
    variance_fun_sub (h1L2 θ) (h2L2 θ)
  have hDvar : variance (fun ω => δ₁ ω - δ₂ ω) (P θ) = 0 := by
    have hnn := variance_nonneg (fun ω => δ₁ ω - δ₂ ω) (P θ)
    rw [hsub] at hnn ⊢
    nlinarith [hnn, hmin_η, hv]
  have hint : ∫ x, (δ₁ x - δ₂ x) ∂ P θ = 0 := by
    rw [integral_sub (int1 θ) (int2 θ), h1u θ, h2u θ, sub_self]
  have hae := ae_eq_integral_of_variance_eq_zero ((h1L2 θ).sub (h2L2 θ)) hDvar
  filter_upwards [hae] with ω hω
  simp only [Pi.sub_apply] at hω
  rw [hint] at hω
  linarith

end StatLean.PointEstimation
