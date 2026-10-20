module
public import StatLean.PointEstimation.Equivariance.LocationMRE
public import StatLean.PointEstimation.Equivariance.Pitman
public import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance

public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-!
# Location equivariance — the normal example and a least-favourable property

Two results about the normal location family.

* `isLocMRE_mean_gaussian` — for independent normal observations with a common unknown
  mean and known variance, the sample mean is the minimum risk equivariant estimator
  under squared error.
* `risk_le_gaussian_of_unitVariance` — among all location families built from an
  independent sample of unit-variance observations, the minimum risk equivariant risk is
  **largest** for the normal: it is at most `1/n`, with equality in the normal case
  (`locRisk_isLocMRE_gaussian_eq`). In this sense the normal distribution is least
  favourable for equivariant location estimation.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.1 (First
Examples), Theorem 1.17 (the characterization of the normal mean as MRE) and Corollary 1.14
(the one-observation bounded-loss case). (`TPE2 §3.1 Thm 1.17, Cor 1.14`.)

**Proof formalization notes.**
* The least-favourable statement is proved exactly as classically, by a one-line
  comparison and *not* by a characterization theorem: the sample mean is equivariant and
  measurable and has risk `1/n` for **every** member of the class (that is just the
  variance of a mean of independent unit-variance observations), so a minimum risk
  equivariant estimator, being at least as good, has risk at most `1/n`; and in the
  normal case the sample mean is itself the minimum risk equivariant estimator, so the
  bound is attained.
* We deliberately do **not** state the converse. That for `n ≥ 3` the normal is the *only*
  member of the class attaining `1/n` is a characterization result of Kagan, Linnik and
  Rao, quoted rather than proved in the classical development; formalizing it is out of
  scope here and nothing downstream uses it.
* The sampling structure is supplied as an equation `locationBase f = Measure.pi …`
  rather than by writing out a joint density: the theorems only ever use the law, and
  this keeps the product structure available as a rewrite.
* No integrability hypotheses accompany the moment conditions: a Bochner integral of a
  non-integrable function is `0`, so `∫ t², dP₁ = 1` already forces square-integrability,
  and integrability of `t` then follows on a probability space.
* The risk `1/n` is expressed in `ℝ≥0∞` through `ENNReal.ofReal`, matching `locRisk`.

**Bibliographic comments.** Equivariant estimation of a location parameter is due to
E. J. G. Pitman, "The estimation of the location and scale parameters of a continuous
population of any given form," *Biometrika* **30** (1939), 391–421; the admissibility of
his estimator is C. Stein, "The admissibility of Pitman's estimator of a single location
parameter," *Ann. Math. Statist.* **30** (1959), 970–979. The characterization of the
normal law by the linearity of the relevant conditional expectation — the converse
alluded to above and not formalized here — is due to A. M. Kagan, Yu. V. Linnik and
C. R. Rao, *Characterization Problems in Mathematical Statistics*, Wiley, 1973.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.PointEstimation

section LocationExamples

variable {m : ℕ}

/-- The sample mean is measurable. -/
private lemma measurable_sampleMean :
    Measurable (fun x : Fin (m + 1) → ℝ => (∑ i, x i) / ((m : ℝ) + 1)) := by
  fun_prop

/-- The sample mean is location equivariant: `Xbar(x + a𝟙) = Xbar(x) + a`. -/
private lemma isLocEquivariant_sampleMean :
    IsLocEquivariant (fun x : Fin (m + 1) → ℝ => (∑ i, x i) / ((m : ℝ) + 1)) := by
  intro a x
  show (∑ i, (x + a • (1 : Fin (m + 1) → ℝ)) i) / ((m : ℝ) + 1)
    = (∑ i, x i) / ((m : ℝ) + 1) + a
  have hsum : (∑ i, (x + a • (1 : Fin (m + 1) → ℝ)) i) = (∑ i, x i) + ((m : ℝ) + 1) * a := by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; ring
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [hsum]
  field_simp

/-! ### The explicit product-Gaussian density and its Pitman estimator

We transfer `isLocMRE_mean_gaussian` to the explicit joint density
`gaussDensity v x = ∏ i, gaussianPDFReal 0 v (x i)`, whose `locationBase` is the product
Gaussian, and for which the Pitman estimator is the sample mean by completing the square. -/

/-- The explicit product-Gaussian density on `Fin (m + 1) → ℝ`. -/
private noncomputable def gaussDensity (v : ℝ≥0) (x : Fin (m + 1) → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 v (x i)

private lemma gaussDensity_nonneg {v : ℝ≥0} (x : Fin (m + 1) → ℝ) : 0 ≤ gaussDensity v x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _

private lemma measurable_gaussDensity (v : ℝ≥0) :
    Measurable (gaussDensity (m := m) v) := by
  unfold gaussDensity
  exact Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 v).comp
    (measurable_pi_apply i)

/-- **STEP A.** The `locationBase` of the explicit product-Gaussian density is the product
Gaussian measure. -/
private lemma locationBase_gaussDensity {v : ℝ≥0} (hv : v ≠ 0) :
    locationBase (gaussDensity (m := m) v)
      = Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 v := by
  haveI : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]; infer_instance
  have h_each : (fun _ : Fin (m + 1) => gaussianReal 0 v)
      = fun _ : Fin (m + 1) => (volume : Measure ℝ).withDensity (gaussianPDF 0 v) := by
    funext _; exact gaussianReal_of_var_ne_zero 0 hv
  rw [h_each, ← MeasureTheory.pi_withDensity_prod (fun _ : Fin (m + 1) => measurable_gaussianPDF 0 v)]
  show (volume : Measure (Fin (m + 1) → ℝ)).withDensity (fun x => ENNReal.ofReal (gaussDensity v x))
    = (volume : Measure (Fin (m + 1) → ℝ)).withDensity (fun x => ∏ i, gaussianPDF 0 v (x i))
  refine withDensity_congr_ae (ae_of_all _ fun x => ?_)
  simp only [gaussDensity]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _]
  rfl

/-- The variance of the sample mean, as an `ℝ≥0`: `v / (m + 1)`. -/
private noncomputable def meanVar (v : ℝ≥0) : ℝ≥0 := v / ((m : ℝ≥0) + 1)

private lemma meanVar_ne_zero {v : ℝ≥0} (hv : v ≠ 0) : meanVar (m := m) v ≠ 0 := by
  rw [meanVar, ne_eq, div_eq_zero_iff]
  push_neg
  exact ⟨hv, by positivity⟩

private lemma coe_meanVar (v : ℝ≥0) : (meanVar (m := m) v : ℝ) = (v : ℝ) / ((m : ℝ) + 1) := by
  rw [meanVar, NNReal.coe_div]
  push_cast
  ring

/-- **STEP B core.** Completing the square: the product of `m + 1` centred Gaussian slices
`x i − u` equals a `u`-independent positive constant times the density of
`𝒩(Xbar, v/(m+1))` evaluated at `u`, where `Xbar = (∑ x i)/(m+1)`. -/
private lemma prod_gaussianPDFReal_sub_eq {v : ℝ≥0} (hv : v ≠ 0) (x : Fin (m + 1) → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      (∏ i, gaussianPDFReal 0 v (x i - u))
        = C * gaussianPDFReal ((∑ i, x i) / ((m : ℝ) + 1)) (meanVar (m := m) v) u := by
  set N : ℝ := (m : ℝ) + 1 with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; positivity
  set S : ℝ := ∑ i, x i with hSdef
  set Xbar : ℝ := S / N with hXbardef
  set vr : ℝ := (v : ℝ) with hvr
  have hvrpos : 0 < vr := by rw [hvr]; positivity
  set Q : ℝ := (∑ i, (x i) ^ 2) - N * Xbar ^ 2 with hQdef
  -- the product of the normalising constants times exp of the residual `Q`
  set C : ℝ := (Real.sqrt (2 * Real.pi * vr))⁻¹ ^ (m + 1)
      * Real.sqrt (2 * Real.pi * (meanVar (m := m) v : ℝ)) * Real.exp (-Q / (2 * vr)) with hCdef
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * vr) :=
    Real.sqrt_pos.mpr (by positivity)
  have hsqrt_mv : 0 < Real.sqrt (2 * Real.pi * (meanVar (m := m) v : ℝ)) :=
    Real.sqrt_pos.mpr (by
      have : (0 : ℝ) < (meanVar (m := m) v : ℝ) := by
        rw [coe_meanVar]; positivity
      positivity)
  refine ⟨C, by rw [hCdef]; positivity, fun u => ?_⟩
  -- sum-of-squares expansion
  have hsumsq : ∑ i, (x i - u) ^ 2 = N * (u - Xbar) ^ 2 + Q := by
    have hexpand : ∑ i, (x i - u) ^ 2 = (∑ i, (x i) ^ 2) - 2 * u * S + N * u ^ 2 := by
      have h1 : ∑ i, (x i - u) ^ 2 = ∑ i, ((x i) ^ 2 - 2 * u * x i + u ^ 2) :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← hSdef, hNdef]
      push_cast; ring
    rw [hexpand, hQdef, hXbardef]
    have hNne : N ≠ 0 := hNpos.ne'
    field_simp
    ring
  -- rewrite the product as a single exp
  have hprod : (∏ i, gaussianPDFReal 0 v (x i - u))
      = (Real.sqrt (2 * Real.pi * vr))⁻¹ ^ (m + 1)
        * Real.exp (-(∑ i, (x i - u) ^ 2) / (2 * vr)) := by
    simp only [gaussianPDFReal, sub_zero, hvr]
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
    congr 1
    · rw [Finset.card_univ, Fintype.card_fin]
    · rw [← Finset.sum_div, Finset.sum_neg_distrib, neg_div]
  rw [hprod, hsumsq]
  -- the target density
  have hmv : (meanVar (m := m) v : ℝ) = vr / N := by rw [coe_meanVar, hvr, hNdef]
  simp only [gaussianPDFReal]
  rw [hCdef, hmv]
  rw [neg_add, add_div, Real.exp_add]
  have h2v : (2 : ℝ) * (vr / N) = (2 * vr) / N := by ring
  rw [h2v]
  have hne : (2 * vr) ≠ 0 := by positivity
  have hNne : N ≠ 0 := hNpos.ne'
  -- match the exponentials on the `(u - Xbar)²` term
  have hexp_eq : -(N * (u - Xbar) ^ 2) / (2 * vr)
      = -(u - Xbar) ^ 2 / ((2 * vr) / N) := by
    rw [div_div_eq_mul_div]; ring
  rw [hexp_eq]
  have hsq : Real.sqrt (Real.pi * vr * N⁻¹ * 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

/-- The `gaussDensity` slice through `x` in direction `𝟙`, shifted by `u`, is the plain
product of centred Gaussian coordinate densities. -/
private lemma gaussDensity_sub_smul (v : ℝ≥0) (x : Fin (m + 1) → ℝ) (u : ℝ) :
    gaussDensity v (x - u • (1 : Fin (m + 1) → ℝ))
      = ∏ i, gaussianPDFReal 0 v (x i - u) := by
  unfold gaussDensity
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]

/-- The Gaussian first moment against Lebesgue measure: `∫ gaussianPDFReal μ v x · x = μ`. -/
private lemma integral_id_mul_gaussianPDFReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, gaussianPDFReal μ v x * x ∂(volume : Measure ℝ) = μ := by
  have h := integral_id_gaussianReal (μ := μ) (v := v)
  rw [gaussianReal_of_var_ne_zero μ hv,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF μ v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top) (fun x => x)] at h
  simpa only [toReal_gaussianPDF, smul_eq_mul] using h

/-- Integrability of the Gaussian first-moment integrand against Lebesgue measure. -/
private lemma integrable_gaussianPDFReal_mul_id (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => gaussianPDFReal μ v x * x) (volume : Measure ℝ) := by
  have hint : Integrable (fun x : ℝ => x) (gaussianReal μ v) :=
    (memLp_id_gaussianReal (μ := μ) (v := v) 1).integrable le_rfl
  rw [gaussianReal_of_var_ne_zero μ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF μ v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hint
  simpa only [id_eq, toReal_gaussianPDF, smul_eq_mul] using hint

/-- **STEP B.** The Pitman estimator of the explicit product-Gaussian density is the sample
mean, by completing the square (`prod_gaussianPDFReal_sub_eq`). -/
private lemma pitmanEstimator_gaussDensity {v : ℝ≥0} (hv : v ≠ 0) (x : Fin (m + 1) → ℝ) :
    pitmanEstimator (gaussDensity (m := m) v) x = (∑ i, x i) / ((m : ℝ) + 1) := by
  obtain ⟨C, hCpos, hC⟩ := prod_gaussianPDFReal_sub_eq hv x
  set Xbar : ℝ := (∑ i, x i) / ((m : ℝ) + 1) with hXbar
  have hfun : ∀ u, gaussDensity v (x - u • (1 : Fin (m + 1) → ℝ))
      = C * gaussianPDFReal Xbar (meanVar (m := m) v) u :=
    fun u => by rw [gaussDensity_sub_smul]; exact hC u
  unfold pitmanEstimator
  have hden : (∫ u : ℝ, gaussDensity v (x - u • (1 : Fin (m + 1) → ℝ))) = C := by
    simp_rw [hfun]
    rw [integral_const_mul, integral_gaussianPDFReal_eq_one Xbar (meanVar_ne_zero hv), mul_one]
  have hnum : (∫ u : ℝ, u * gaussDensity v (x - u • (1 : Fin (m + 1) → ℝ))) = C * Xbar := by
    simp_rw [hfun]
    rw [show (fun u => u * (C * gaussianPDFReal Xbar (meanVar (m := m) v) u))
          = fun u => C * (gaussianPDFReal Xbar (meanVar (m := m) v) u * u) from by
        funext u; ring,
      integral_const_mul, integral_id_mul_gaussianPDFReal Xbar (meanVar_ne_zero hv)]
  rw [hnum, hden, mul_comm C Xbar, mul_div_assoc, div_self hCpos.ne', mul_one]

/-- `IsLocMRE` depends on the density only through its `locationBase`, since both the risk
and the equivariant class do. -/
private lemma isLocMRE_congr_locationBase {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (h : locationBase f = locationBase g) {ρ : ℝ → ℝ} {δ : (Fin n → ℝ) → ℝ} :
    IsLocMRE f ρ δ ↔ IsLocMRE g ρ δ := by
  unfold IsLocMRE locRisk; rw [h]

/-- **The sample mean is the minimum risk equivariant estimator in the normal location
family** under squared error, for any known variance. -/
theorem isLocMRE_mean_gaussian (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    {v : ℝ≥0}
    -- USER-INPUT: the variance is known and nondegenerate
    (hv : v ≠ 0)
    -- USER-INPUT: the base member is an independent normal sample with mean `0`
    (hf : locationBase f = Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 v) :
    IsLocMRE f (fun t : ℝ => t ^ 2) (fun x => (∑ i, x i) / ((m : ℝ) + 1)) := by
  -- `IsLocMRE f ρ δ` depends on `f` only through `locationBase f`; transfer to the explicit
  -- product-Gaussian density, whose Pitman estimator is the sample mean by completing the
  -- square (STEP A/B above). The Kagan–Linnik–Rao converse is out of scope (see docstring).
  have hbase : locationBase f = locationBase (gaussDensity (m := m) v) :=
    hf.trans (locationBase_gaussDensity hv).symm
  rw [isLocMRE_congr_locationBase hbase]
  haveI : IsProbabilityMeasure (locationBase (gaussDensity (m := m) v)) := by
    rw [locationBase_gaussDensity hv]; infer_instance
  -- The three slice side conditions and the finite reference risk.
  have hslice : ∀ x : Fin (m + 1) → ℝ,
      (fun u : ℝ => gaussDensity v (x - u • (1 : Fin (m + 1) → ℝ)))
        = fun u => (Classical.choose (prod_gaussianPDFReal_sub_eq hv x))
            * gaussianPDFReal ((∑ i, x i) / ((m : ℝ) + 1)) (meanVar (m := m) v) u := by
    intro x
    funext u
    rw [gaussDensity_sub_smul]
    exact (Classical.choose_spec (prod_gaussianPDFReal_sub_eq hv x)).2 u
  have hden : ∀ x, Integrable
      fun u : ℝ => gaussDensity v (x - u • (1 : Fin (m + 1) → ℝ)) := by
    intro x; rw [hslice x]; exact (integrable_gaussianPDFReal _ _).const_mul _
  have hnum : ∀ x, Integrable
      fun u : ℝ => u * gaussDensity v (x - u • (1 : Fin (m + 1) → ℝ)) := by
    intro x
    have hpt : (fun u : ℝ => u * gaussDensity v (x - u • (1 : Fin (m + 1) → ℝ)))
        = fun u => (Classical.choose (prod_gaussianPDFReal_sub_eq hv x))
            * (gaussianPDFReal ((∑ i, x i) / ((m : ℝ) + 1)) (meanVar (m := m) v) u * u) := by
      funext u; rw [show gaussDensity v (x - u • (1 : Fin (m + 1) → ℝ))
        = _ from congrFun (hslice x) u]; ring
    rw [hpt]
    exact ((integrable_gaussianPDFReal_mul_id _ (meanVar_ne_zero hv)).const_mul _)
  have hden0 : ∀ x, (∫ u : ℝ, gaussDensity v (x - u • (1 : Fin (m + 1) → ℝ))) ≠ 0 := by
    intro x
    rw [hslice x, integral_const_mul,
      integral_gaussianPDFReal_eq_one _ (meanVar_ne_zero hv), mul_one]
    exact (Classical.choose_spec (prod_gaussianPDFReal_sub_eq hv x)).1.ne'
  have hfin : locRisk (gaussDensity (m := m) v) (fun t : ℝ => t ^ 2)
      (fun x => x (Fin.last m)) ≠ ∞ := by
    unfold locRisk
    rw [locationBase_gaussDensity hv]
    have hmp : MeasurePreserving (fun x : Fin (m + 1) → ℝ => x (Fin.last m))
        (Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 v) (gaussianReal 0 v) :=
      measurePreserving_eval (fun _ : Fin (m + 1) => gaussianReal 0 v) (Fin.last m)
    rw [hmp.lintegral_comp (by fun_prop : Measurable
      fun t : ℝ => ENNReal.ofReal (t ^ 2))]
    have hI2 : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 v) :=
      (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := v) 2).integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hI2 (ae_of_all _ fun t => sq_nonneg t)]
    exact ENNReal.ofReal_ne_top
  -- The Pitman estimator equals the sample mean, so its MRE property is the claim.
  have hpit := pitmanEstimator_isLocMRE (gaussDensity (m := m) v)
    (measurable_gaussDensity v) gaussDensity_nonneg hnum hden hden0 hfin
  have hpe : pitmanEstimator (gaussDensity (m := m) v)
      = fun x => (∑ i, x i) / ((m : ℝ) + 1) := by
    funext x; exact pitmanEstimator_gaussDensity hv x
  rwa [hpe] at hpit

/-- The risk of the sample mean in an independent unit-variance location family is
`1/n`, whatever the shape of the underlying distribution. This is the observation that
drives the least-favourable property of the normal law. -/
theorem locRisk_mean_eq_inv (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    (P₁ : Measure ℝ) [IsProbabilityMeasure P₁]
    -- USER-INPUT: the base member is an independent sample from `P₁`
    (hf : locationBase f = Measure.pi fun _ : Fin (m + 1) => P₁)
    -- USER-INPUT: the coordinates are centred with unit variance
    (hmean : ∫ t, t ∂P₁ = 0) (hvar : ∫ t, t ^ 2 ∂P₁ = 1) :
    locRisk f (fun t : ℝ => t ^ 2) (fun x => (∑ i, x i) / ((m : ℝ) + 1))
      = ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
  set N : ℝ := (m : ℝ) + 1 with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; positivity
  -- Square-integrability of the coordinate law from the second-moment hypothesis.
  have hsq_int : Integrable (fun t : ℝ => t ^ 2) P₁ := by
    by_contra h; rw [integral_undef h] at hvar; exact one_ne_zero hvar.symm
  have hL2 : MemLp (fun t : ℝ => t) 2 P₁ :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq_int
  -- Each coordinate is square-integrable under the product law.
  have hL2i : ∀ i : Fin (m + 1),
      MemLp (fun x : Fin (m + 1) → ℝ => x i) 2 (Measure.pi fun _ => P₁) := by
    intro i
    have := hL2.comp_measurePreserving (measurePreserving_eval (fun _ => P₁) i)
    simpa [Function.comp] using! this
  have hint_i : ∀ i, Integrable (fun x : Fin (m + 1) → ℝ => x i)
      (Measure.pi fun _ => P₁) := fun i => (hL2i i).integrable one_le_two
  have hint_ij : ∀ i j, Integrable (fun x : Fin (m + 1) → ℝ => x i * x j)
      (Measure.pi fun _ => P₁) := fun i j => (hL2i i).integrable_mul (hL2i j)
  -- Coordinate first and second moments; cross moments vanish by independence.
  have hEi : ∀ i, ∫ x : Fin (m + 1) → ℝ, x i ∂(Measure.pi fun _ => P₁) = 0 := by
    intro i; rw [integral_eval]; exact hmean
  have hindep : iIndepFun (fun i (x : Fin (m + 1) → ℝ) => x i) (Measure.pi fun _ => P₁) :=
    iIndepFun_pi fun _ => aemeasurable_id
  have hc : ∀ i j, ∫ x : Fin (m + 1) → ℝ, x i * x j ∂(Measure.pi fun _ => P₁)
      = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have heq : (fun x : Fin (m + 1) → ℝ => x i * x i)
          = fun x => (fun t : ℝ => t ^ 2) (x i) := by funext x; ring
      have hev := integral_comp_eval (μ := fun _ : Fin (m + 1) => P₁) (i := i)
        (f := fun t : ℝ => t ^ 2) (by fun_prop)
      rw [if_pos rfl, heq, hev]; exact hvar
    · rw [if_neg hij]
      have hpair := (hindep.indepFun hij).integral_fun_mul_eq_mul_integral
        (measurable_pi_apply i).aestronglyMeasurable
        (measurable_pi_apply j).aestronglyMeasurable
      rw [hpair, hEi i, hEi j, mul_zero]
  -- Second moment of the total: `∫ (∑ Xᵢ)² = m + 1`.
  have hSmemLp : MemLp (fun x : Fin (m + 1) → ℝ => ∑ i, x i) 2 (Measure.pi fun _ => P₁) :=
    memLp_finset_sum _ fun i _ => hL2i i
  have hSsq_int : Integrable (fun x : Fin (m + 1) → ℝ => (∑ i, x i) ^ 2)
      (Measure.pi fun _ => P₁) := by
    have := hSmemLp.integrable_mul hSmemLp
    simpa [Pi.mul_apply, pow_two] using! this
  have hSsq : ∫ x : Fin (m + 1) → ℝ, (∑ i, x i) ^ 2 ∂(Measure.pi fun _ => P₁) = N := by
    have hexpand : (fun x : Fin (m + 1) → ℝ => (∑ i, x i) ^ 2)
        = fun x => ∑ i, ∑ j, x i * x j := by
      funext x; rw [pow_two, Fintype.sum_mul_sum]
    rw [hexpand, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint_ij i j]
    have hinner : ∀ i, ∫ x : Fin (m + 1) → ℝ, ∑ j, x i * x j ∂(Measure.pi fun _ => P₁) = 1 := by
      intro i
      rw [integral_finset_sum _ fun j _ => hint_ij i j]
      simp [hc i]
    simp only [hinner]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hNdef]
    push_cast; ring
  -- Assemble: `∫ Xbar² = (1/N²) · N = 1/N`.
  have hmean_sq_int : Integrable (fun x : Fin (m + 1) → ℝ => ((∑ i, x i) / N) ^ 2)
      (Measure.pi fun _ => P₁) := by
    have : (fun x : Fin (m + 1) → ℝ => ((∑ i, x i) / N) ^ 2)
        = fun x => (N ^ 2)⁻¹ * (∑ i, x i) ^ 2 := by
      funext x; rw [div_pow]; ring
    rw [this]; exact hSsq_int.const_mul _
  have hmeanRisk : ∫ x : Fin (m + 1) → ℝ, ((∑ i, x i) / N) ^ 2 ∂(Measure.pi fun _ => P₁)
      = 1 / N := by
    have hrw : (fun x : Fin (m + 1) → ℝ => ((∑ i, x i) / N) ^ 2)
        = fun x => (N ^ 2)⁻¹ * (∑ i, x i) ^ 2 := by funext x; rw [div_pow]; ring
    have hN0 : N ≠ 0 := hNpos.ne'
    rw [hrw, integral_const_mul, hSsq, pow_two, mul_inv, mul_assoc,
        inv_mul_cancel₀ hN0, mul_one, one_div]
  -- The `ℝ≥0∞`-risk is the `ENNReal.ofReal` of this Bochner integral.
  unfold locRisk
  rw [hf, ← ofReal_integral_eq_lintegral_ofReal hmean_sq_int
        (ae_of_all _ fun x => sq_nonneg _), hmeanRisk]

/-- **The normal law is least favourable for equivariant location estimation.** Over the
class of location families generated by an independent sample of centred unit-variance
observations, the risk of a minimum risk equivariant estimator is at most `1/n` — the
value it takes in the normal case (`locRisk_isLocMRE_gaussian_eq`). The minimum risk
equivariant risk is therefore maximized at the normal law.

The classical development notes, but does not prove, that for `n ≥ 3` the normal is the
only member of the class attaining `1/n`; that converse is not formalized. -/
theorem risk_le_gaussian_of_unitVariance (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    (P₁ : Measure ℝ) [IsProbabilityMeasure P₁]
    -- USER-INPUT: the base member is an independent sample from `P₁`
    (hf : locationBase f = Measure.pi fun _ : Fin (m + 1) => P₁)
    -- USER-INPUT: the coordinates are centred with unit variance
    (hmean : ∫ t, t ∂P₁ = 0) (hvar : ∫ t, t ^ 2 ∂P₁ = 1)
    {δ : (Fin (m + 1) → ℝ) → ℝ}
    -- USER-INPUT: `δ` is minimum risk equivariant under squared error
    (hMRE : IsLocMRE f (fun t : ℝ => t ^ 2) δ) :
    locRisk f (fun t : ℝ => t ^ 2) δ ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
  -- The sample mean is a measurable equivariant competitor with risk `1/(m+1)`
  -- (`locRisk_mean_eq_inv`); the minimum risk equivariant `δ` does at least as well.
  have hcomp := hMRE.2.2 (fun x => (∑ i, x i) / ((m : ℝ) + 1))
    measurable_sampleMean isLocEquivariant_sampleMean
  rwa [locRisk_mean_eq_inv f P₁ hf hmean hvar] at hcomp

/-- The bound of `risk_le_gaussian_of_unitVariance` is attained at the standard normal
law, where the sample mean is itself minimum risk equivariant. -/
theorem locRisk_isLocMRE_gaussian_eq (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    -- USER-INPUT: the base member is a standard normal independent sample
    (hf : locationBase f = Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1)
    {δ : (Fin (m + 1) → ℝ) → ℝ}
    -- USER-INPUT: `δ` is minimum risk equivariant under squared error
    (hMRE : IsLocMRE f (fun t : ℝ => t ^ 2) δ) :
    locRisk f (fun t : ℝ => t ^ 2) δ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
  -- At the standard normal the sample mean is itself minimum risk equivariant
  -- (`isLocMRE_mean_gaussian`); two minimum risk equivariant estimators have equal risk,
  -- and that common value is `1/(m+1)` (`locRisk_mean_eq_inv`).
  have hXbar := isLocMRE_mean_gaussian f (v := 1) one_ne_zero hf
  have hle1 : locRisk f (fun t : ℝ => t ^ 2) δ
      ≤ locRisk f (fun t : ℝ => t ^ 2) (fun x => (∑ i, x i) / ((m : ℝ) + 1)) :=
    hMRE.2.2 _ hXbar.1 hXbar.2.1
  have hle2 : locRisk f (fun t : ℝ => t ^ 2) (fun x => (∑ i, x i) / ((m : ℝ) + 1))
      ≤ locRisk f (fun t : ℝ => t ^ 2) δ :=
    hXbar.2.2 _ hMRE.1 hMRE.2.1
  have hmean : ∫ t, t ∂(ProbabilityTheory.gaussianReal 0 1) = 0 :=
    ProbabilityTheory.integral_id_gaussianReal
  have hvar : ∫ t, t ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 := by
    have hV := ProbabilityTheory.variance_id_gaussianReal (μ := 0) (v := 1)
    rw [ProbabilityTheory.variance_eq_integral aemeasurable_id] at hV
    simpa [ProbabilityTheory.integral_id_gaussianReal] using hV
  rw [le_antisymm hle1 hle2, locRisk_mean_eq_inv f _ hf hmean hvar]

end LocationExamples

end StatLean.PointEstimation
