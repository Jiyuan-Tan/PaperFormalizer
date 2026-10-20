module
public import StatLean.StatisticalModels.Longitudinal.Defs
public import StatLean.AsymptoticStatistics.ForMathlib.CondExpL2
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

/-!
# GEE unbiasedness — the estimating function is centered at the truth

**Headline (L1).** Under the marginal mean model, the GEE estimating function has mean zero:
$$\mathbb E_Q\big[D^\top V^{-1}\,(y - \mu(\beta_0))\big] = 0,$$
coordinate by coordinate. The mechanism: each coordinate of the score is a finite sum of
`(weight entry) · (residual)` terms; the weight entry is a function of the covariates only
(constitutive: `D` and `V` depend on the visit data), and the residual has vanishing
conditional mean given the covariates — so each term is an inner product of a
covariate-measurable factor against a conditionally centered factor.

Two routes, both stated:

* `gee_unbiased` — the **L² pairing route** (primary): with `MemLp 2` USER-INPUT moment
  hypotheses, each term is `⟪W, y − μ⟫_{L²(Q)} = ⟪W, condExpL2 (y − μ)⟫ = 0` via the
  self-adjointness of `condExpL2` against covariate-measurable elements. This avoids the
  bounded-factor limitation of `condExp` pull-out.
* `gee_unbiased_of_bounded` — the corollary whose hypotheses match the books' phrasing
  (bounded weights, integrable responses), via `condExp` pull-out for bounded factors.

**Reference.** `LZ86 §2` (the remark below Eq. (6): the equations are unbiased under the
mean model alone, whatever the working covariance); FLW Ch. 13 (verify §); McCulloch–Searle–
Neuhaus, *Generalized, Linear, and Mixed Models*, 2nd ed., Ch. 9 (verify §) (`MSN Ch. 9`).

**Proof formalization notes.** Coordinatewise: `geeScore … k = ∑ j, W k j · resid j`;
linearity of the integral reduces to one visit. The measurability hypotheses on the mean
function and the weight entries are LEAN-ONLY (the books implicitly assume everything
measurable); the `MemLp 2` moment hypotheses are USER-INPUT (LZ86 assume finite second
moments throughout). *Book vs Lean:* no correctness of `V` and no independence across visits
is assumed — exactly LZ86's point.

**Bibliographic comments.** Unbiasedness of estimating functions as the defining property is
`God60`; the GEE instance is Liang–Zeger (1986). The observation that only the conditional
mean model matters (robustness to working-covariance misspecification) is the celebrated
LZ86 Theorem 1 hypothesis structure.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace StatLean.StatisticalModels.Longitudinal

variable {p m q : ℕ} {Θβ : Type*}

/-- The covariate σ-algebra is a sub-σ-algebra of the record σ-algebra (LEAN-ONLY
structural fact used by every conditioning step). -/
theorem covariateSigma_le (p m : ℕ) :
    covariateSigma p m ≤ (inferInstance : MeasurableSpace (LongitudinalRecord p m)) := by
  rintro s ⟨t, ht, rfl⟩
  exact ⟨{u | (u.1, u.2.1) ∈ t},
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) ht, rfl⟩

/-- The record-to-triple map is measurable for the record σ-algebra (LEAN-ONLY plumbing). -/
private theorem measurable_record_triple :
    Measurable fun r : LongitudinalRecord p m => (r.times, r.x, r.y) :=
  Measurable.of_comap_le le_rfl

/-- Record accessors are measurable (LEAN-ONLY plumbing). -/
theorem measurable_record_y (j : Fin m) :
    Measurable fun r : LongitudinalRecord p m => r.y j :=
  ((measurable_pi_apply j).comp ((WithLp.measurable_ofLp 2 _).comp
    (measurable_snd.comp measurable_snd))).comp measurable_record_triple

/-- Covariate functionals are `covariateSigma`-measurable (LEAN-ONLY plumbing): any
measurable function of `(times, x)` is measurable for the covariate σ-algebra. -/
theorem covariateSigma_measurable_comp
    -- LEAN-ONLY: measurability of the covariate functional; plumbing
    {g : (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin p)) → ℝ} (hg : Measurable g) :
    Measurable[covariateSigma p m] fun r : LongitudinalRecord p m => g (r.times, r.x) :=
  hg.comp (Measurable.of_comap_le le_rfl)

/-- Orthogonality: a `m`-measurable factor integrates to zero against a conditionally
centered one. The pull-out property plus `integral_condExp` (LEAN-ONLY packaging of the
step shared by both routes). -/
private theorem integral_mul_eq_zero_of_condExp_eq_zero {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {μ : Measure Ω} [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : StronglyMeasurable[m] f) (hg : Integrable g μ) (hfg : Integrable (f * g) μ)
    (hg0 : μ[g | m] =ᵐ[μ] 0) :
    ∫ ω, f ω * g ω ∂μ = 0 := by
  have key : μ[f * g|m] =ᵐ[μ] 0 := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hf hfg hg, hg0] with ω h h'
    rw [h]
    simp [h']
  have h0 : ∫ ω, (f * g) ω ∂μ = ∫ ω, (μ[f * g|m]) ω ∂μ :=
    (integral_condExp (μ := μ) (f := f * g) hm).symm
  have h3 : ∫ ω, (μ[f * g|m]) ω ∂μ = 0 := by rw [integral_congr_ae key]; simp
  simpa using h0.trans h3

/-- The residual of the marginal mean model is conditionally centered given the covariates
(LEAN-ONLY packaging: the mean-model hypothesis in the form both routes consume). -/
private theorem condExp_geeResidual_eq_zero (Q : Measure (LongitudinalRecord p m))
    [IsFiniteMeasure Q] (S : GEESpec p m q Θβ) (β₀ : Θβ)
    (hmean : IsMarginalMeanModel Q S.μfun β₀)
    (hY : ∀ j, Integrable (fun r : LongitudinalRecord p m => r.y j) Q)
    (hμ : ∀ j, Integrable (fun r : LongitudinalRecord p m =>
      S.μfun β₀ (r.times j, r.x j)) Q) (j : Fin m) :
    Q[fun r => S.geeResidual β₀ r j|covariateSigma p m] =ᵐ[Q] 0 := by
  have h1 : Q[fun r => S.geeResidual β₀ r j|covariateSigma p m]
      =ᵐ[Q] Q[fun r : LongitudinalRecord p m => r.y j|covariateSigma p m]
        - Q[fun r : LongitudinalRecord p m =>
            S.μfun β₀ (r.times j, r.x j)|covariateSigma p m] :=
    condExp_sub (hY j) (hμ j) _
  have h2 : Q[fun r : LongitudinalRecord p m =>
        S.μfun β₀ (r.times j, r.x j)|covariateSigma p m]
      =ᵐ[Q] Q[fun r : LongitudinalRecord p m => r.y j|covariateSigma p m] :=
    (condExp_congr_ae (hmean j).symm).trans
      (condExp_condExp_of_le le_rfl (covariateSigma_le p m))
  filter_upwards [h1, h2] with r e1 e2
  simp [e1, e2]

/-- **L1, GEE unbiasedness (L² route)** (`LZ86 §2`, remark below Eq. (6)): under the marginal
mean model, every coordinate of the GEE estimating function integrates to zero — whatever the
working covariance. -/
theorem gee_unbiased (Q : Measure (LongitudinalRecord p m)) [IsProbabilityMeasure Q]
    (S : GEESpec p m q Θβ) (β₀ : Θβ)
    -- USER-INPUT: the marginal mean model holds at β₀; LZ86 §2 Eq. (2)
    (hmean : IsMarginalMeanModel Q S.μfun β₀)
    -- USER-INPUT: square-integrable responses and fitted values; LZ86 §2
    (hY : ∀ j, MemLp (fun r => r.y j) 2 Q)
    (hμ : ∀ j, MemLp (fun r : LongitudinalRecord p m =>
      S.μfun β₀ (r.times j, r.x j)) 2 Q)
    -- USER-INPUT: square-integrable weight entries; LZ86 §2
    (hW : ∀ k j, MemLp (fun r : LongitudinalRecord p m =>
      S.geeWeight β₀ r.times r.x k j) 2 Q)
    -- LEAN-ONLY: measurability of the weight entries as covariate functionals
    (hWmeas : ∀ k j, Measurable fun tx : (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin p)) =>
      S.geeWeight β₀ tx.1 tx.2 k j)
    (k : Fin q) :
    ∫ r, S.geeScore β₀ r k ∂Q = 0 := by
  have hm := covariateSigma_le p m
  have hres : ∀ j, MemLp (fun r : LongitudinalRecord p m => S.geeResidual β₀ r j) 2 Q :=
    fun j => (hY j).sub (hμ j)
  have hint : ∀ j : Fin m, Integrable (fun r : LongitudinalRecord p m =>
      S.geeWeight β₀ r.times r.x k j * S.geeResidual β₀ r j) Q :=
    fun j => (hW k j).integrable_mul (hres j)
  have hterm : ∀ j : Fin m,
      ∫ r, S.geeWeight β₀ r.times r.x k j * S.geeResidual β₀ r j ∂Q = 0 := fun j =>
    integral_mul_eq_zero_of_condExp_eq_zero hm
      (covariateSigma_measurable_comp (hWmeas k j)).stronglyMeasurable
      ((hres j).integrable one_le_two) (hint j)
      (condExp_geeResidual_eq_zero Q S β₀ hmean (fun j => (hY j).integrable one_le_two)
        (fun j => (hμ j).integrable one_le_two) j)
  have hsum : ∀ r : LongitudinalRecord p m, S.geeScore β₀ r k
      = ∑ j, S.geeWeight β₀ r.times r.x k j * S.geeResidual β₀ r j := fun _ => rfl
  calc ∫ r, S.geeScore β₀ r k ∂Q
      = ∫ r, ∑ j, S.geeWeight β₀ r.times r.x k j * S.geeResidual β₀ r j ∂Q := by
        simp_rw [hsum]
    _ = ∑ j, ∫ r, S.geeWeight β₀ r.times r.x k j * S.geeResidual β₀ r j ∂Q :=
        integral_finset_sum _ fun j _ => hint j
    _ = 0 := by simp [hterm]

/-- **L1', the bounded-weights corollary** (hypotheses in the books' phrasing: bounded
weights, integrable data), via `condExp` pull-out for bounded factors. -/
theorem gee_unbiased_of_bounded (Q : Measure (LongitudinalRecord p m))
    [IsProbabilityMeasure Q] (S : GEESpec p m q Θβ) (β₀ : Θβ)
    -- USER-INPUT: the marginal mean model holds at β₀; LZ86 §2 Eq. (2)
    (hmean : IsMarginalMeanModel Q S.μfun β₀)
    -- USER-INPUT: integrable responses and fitted values; FLW Ch. 13
    (hY : ∀ j, Integrable (fun r => r.y j) Q)
    (hμ : ∀ j, Integrable (fun r : LongitudinalRecord p m =>
      S.μfun β₀ (r.times j, r.x j)) Q)
    -- USER-INPUT: uniformly bounded weight entries; FLW Ch. 13
    {C : ℝ} (hC : ∀ k j r, |S.geeWeight β₀ (LongitudinalRecord.times r)
      (LongitudinalRecord.x r) k j| ≤ C)
    -- LEAN-ONLY: measurability of the weight entries as covariate functionals
    (hWmeas : ∀ k j, Measurable fun tx : (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin p)) =>
      S.geeWeight β₀ tx.1 tx.2 k j)
    (k : Fin q) :
    ∫ r, S.geeScore β₀ r k ∂Q = 0 := by
  have hm := covariateSigma_le p m
  have hWsm : ∀ j : Fin m, StronglyMeasurable[covariateSigma p m]
      fun r : LongitudinalRecord p m => S.geeWeight β₀ r.times r.x k j :=
    fun j => (covariateSigma_measurable_comp (hWmeas k j)).stronglyMeasurable
  have hbd : ∀ j : Fin m, ∀ᵐ r ∂Q, ‖S.geeWeight β₀ r.times r.x k j‖ ≤ C := fun j =>
    Filter.Eventually.of_forall fun r => (Real.norm_eq_abs _).le.trans (hC k j r)
  have hres : ∀ j, Integrable (fun r : LongitudinalRecord p m =>
      S.geeResidual β₀ r j) Q := fun j => (hY j).sub (hμ j)
  have hint : ∀ j : Fin m, Integrable (fun r : LongitudinalRecord p m =>
      S.geeWeight β₀ r.times r.x k j * S.geeResidual β₀ r j) Q := fun j =>
    (hres j).bdd_mul (((hWsm j).mono hm).aestronglyMeasurable) (hbd j)
  have hterm : ∀ j : Fin m,
      ∫ r, S.geeWeight β₀ r.times r.x k j * S.geeResidual β₀ r j ∂Q = 0 := fun j =>
    integral_mul_eq_zero_of_condExp_eq_zero hm (hWsm j) (hres j) (hint j)
      (condExp_geeResidual_eq_zero Q S β₀ hmean hY hμ j)
  have hsum : ∀ r : LongitudinalRecord p m, S.geeScore β₀ r k
      = ∑ j, S.geeWeight β₀ r.times r.x k j * S.geeResidual β₀ r j := fun _ => rfl
  calc ∫ r, S.geeScore β₀ r k ∂Q
      = ∫ r, ∑ j, S.geeWeight β₀ r.times r.x k j * S.geeResidual β₀ r j ∂Q := by
        simp_rw [hsum]
    _ = ∑ j, ∫ r, S.geeWeight β₀ r.times r.x k j * S.geeResidual β₀ r j ∂Q :=
        integral_finset_sum _ fun j _ => hint j
    _ = 0 := by simp [hterm]

end StatLean.StatisticalModels.Longitudinal
