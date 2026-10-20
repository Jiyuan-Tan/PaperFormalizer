module
public import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Likelihood comparison for finite products of densities

This file packages the measure-theoretic finite-product likelihood comparison for
two nonnegative real densities with respect to a common dominating measure.  It
does not assume common support: the two one-sided zero-density masses are tracked
explicitly in the comparison bound.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.FiniteProductLikelihood

variable {X : Type*} [MeasurableSpace X]

/-- The `N`-fold product law induced by the real density `p` with respect to `mu`.
Negative values are truncated to zero by `ENNReal.ofReal`; theorem hypotheses below
require nonnegativity when this is used as the law represented by `p`.
-/
noncomputable def productMeasureOfDensity (mu : Measure X) (p : X -> ℝ) (N : ℕ) :
    Measure (Fin N -> X) :=
  Measure.pi fun _ => mu.withDensity (ENNReal.ofReal ∘ p)

/-- The log-likelihood ratio of the `N`-fold `q`-law against the `N`-fold `p`-law.
For `N = 0` this is the empty sum `0`; at a zero density, Lean's totalized division
and `Real.log` conventions apply.
-/
noncomputable def logLikelihood (p q : X -> ℝ) (N : ℕ) (x : Fin N -> X) : ℝ :=
  ∑ i, Real.log (q (x i) / p (x i))

/-- The one-coordinate region on which both densities are strictly positive.
Its complement retains both zero-density faces; no common-support convention is
built into the definition.
-/
def commonPositiveSet (p q : X -> ℝ) : Set X :=
  {x | 0 < p x ∧ 0 < q x}

/-- A nonnegative measurable density of integral one induces a probability measure,
and so does every finite product of that measure, including the empty product.
-/
theorem productMeasureOfDensity_isProbabilityMeasure
    -- the common dominating measure.
    (mu : Measure X)
    -- the supplied real density.
    (p : X -> ℝ)
    -- the finite product size.
    (N : ℕ)
    -- measurability of the supplied density.
    (hpm : Measurable p)
    -- pointwise nonnegativity of the supplied density.
    (hp0 : ∀ x, 0 ≤ p x)
    -- integrability of the supplied density.
    (hpi : Integrable p mu)
    -- unit mass, making the supplied density a probability density.
    (hp1 : ∫ x, p x ∂(mu) = 1) :
    IsProbabilityMeasure (productMeasureOfDensity mu p N) := by
  have hpE : Measurable (ENNReal.ofReal ∘ p) := hpm.ennreal_ofReal
  letI : IsProbabilityMeasure (mu.withDensity (ENNReal.ofReal ∘ p)) := by
    refine ⟨?_⟩
    rw [← lintegral_one,
      lintegral_withDensity_eq_lintegral_mul _ hpE measurable_const]
    simp only [Pi.mul_apply, mul_one, Function.comp_apply]
    change (∫⁻ x, ENNReal.ofReal (p x) ∂mu) = 1
    rw [← ofReal_integral_eq_lintegral_ofReal hpi
      (Filter.Eventually.of_forall hp0), hp1, ENNReal.ofReal_one]
  change IsProbabilityMeasure (Measure.pi fun _ : Fin N =>
    mu.withDensity (ENNReal.ofReal ∘ p))
  infer_instance

private noncomputable def expLogFactor (p q : X → ℝ) (x : X) : ℝ :=
  p x * Real.exp (Real.log (q x / p x))

omit [MeasurableSpace X] in
private lemma expLogFactor_nonneg (p q : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (x : X) :
    0 ≤ expLogFactor p q x :=
  mul_nonneg (hp0 x) (Real.exp_pos _).le

private lemma expLogFactor_meas (p q : X → ℝ) (hpm : Measurable p) (hqm : Measurable q) :
    Measurable (expLogFactor p q) :=
  hpm.mul ((hqm.div hpm).log.exp)

omit [MeasurableSpace X] in
private lemma expLogFactor_apply (p q : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hq0 : ∀ x, 0 ≤ q x) (x : X) :
    expLogFactor p q x = if p x = 0 then 0 else if q x = 0 then p x else q x := by
  unfold expLogFactor
  by_cases hpz : p x = 0
  · simp [hpz]
  · rw [if_neg hpz]
    by_cases hqz : q x = 0
    · simp [hqz, Real.log_zero, Real.exp_zero]
    · rw [if_neg hqz, Real.exp_log (div_pos (lt_of_le_of_ne (hq0 x) (Ne.symm hqz))
        (lt_of_le_of_ne (hp0 x) (Ne.symm hpz)))]
      field_simp

omit [MeasurableSpace X] in
private lemma expLogFactor_le (p q : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hq0 : ∀ x, 0 ≤ q x) (x : X) : expLogFactor p q x ≤ p x + q x := by
  rw [expLogFactor_apply p q hp0 hq0]
  by_cases hpz : p x = 0
  · rw [if_pos hpz]
    exact add_nonneg (hp0 x) (hq0 x)
  · rw [if_neg hpz]
    by_cases hqz : q x = 0
    · rw [if_pos hqz]
      exact le_add_of_nonneg_right (hq0 x)
    · rw [if_neg hqz]
      exact le_add_of_nonneg_left (hp0 x)

private lemma expLogFactor_integrable (p q : X → ℝ) (mu : Measure X)
    (hpm : Measurable p) (hqm : Measurable q) (hp0 : ∀ x, 0 ≤ p x)
    (hq0 : ∀ x, 0 ≤ q x) (hpi : Integrable p mu) (hqi : Integrable q mu) :
    Integrable (expLogFactor p q) mu := by
  refine Integrable.mono' (hpi.add hqi) (expLogFactor_meas p q hpm hqm).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (expLogFactor_nonneg p q hp0 x)]
  exact expLogFactor_le p q hp0 hq0 x

private lemma expLogFactor_integral_eq (p q : X → ℝ) (mu : Measure X)
    (hpm : Measurable p) (hqm : Measurable q) (hp0 : ∀ x, 0 ≤ p x)
    (hq0 : ∀ x, 0 ≤ q x) (hpi : Integrable p mu) (hqi : Integrable q mu)
    (hq1 : ∫ x, q x ∂mu = 1) :
    ∫ x, expLogFactor p q x ∂mu =
      1 - ∫ x in {x | p x = 0}, q x ∂mu + ∫ x in {x | q x = 0}, p x ∂mu := by
  let P0 : Set X := {x | p x = 0}
  let Q0 : Set X := {x | q x = 0}
  have hP0 : MeasurableSet P0 := hpm (measurableSet_singleton 0)
  have hQ0 : MeasurableSet Q0 := hqm (measurableSet_singleton 0)
  have hgint := expLogFactor_integrable p q mu hpm hqm hp0 hq0 hpi hqi
  have hp_ind : Integrable (Q0.indicator p) mu := hpi.indicator hQ0
  have hq_ind : Integrable (P0.indicator q) mu := hqi.indicator hP0
  have hdiff : (fun x => expLogFactor p q x - q x) =
      fun x => Q0.indicator p x - P0.indicator q x := by
    funext x
    rw [expLogFactor_apply p q hp0 hq0, Set.indicator_apply, Set.indicator_apply]
    simp only [P0, Q0, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  have key : (∫ x, expLogFactor p q x ∂mu) - ∫ x, q x ∂mu =
      (∫ x, Q0.indicator p x ∂mu) - ∫ x, P0.indicator q x ∂mu := by
    rw [← integral_sub hgint hqi, hdiff, integral_sub hp_ind hq_ind]
  rw [integral_indicator hQ0, integral_indicator hP0, hq1] at key
  simp only [P0, Q0] at key
  linarith

private lemma expLogLikelihood_lintegral_eq (mu : Measure X) (p q : X → ℝ) (N : ℕ)
    (hpm : Measurable p) (hqm : Measurable q) (hp0 : ∀ x, 0 ≤ p x)
    (hq0 : ∀ x, 0 ≤ q x) (hpi : Integrable p mu) (hqi : Integrable q mu)
    (hp1 : ∫ x, p x ∂mu = 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (logLikelihood p q N x))
        ∂(productMeasureOfDensity mu p N) =
      ENNReal.ofReal (∫ x, expLogFactor p q x ∂mu) ^ N := by
  let e : X → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (Real.log (q x / p x)))
  have he : Measurable e := ((hqm.div hpm).log.exp).ennreal_ofReal
  have hpE : Measurable (ENNReal.ofReal ∘ p) := hpm.ennreal_ofReal
  letI : IsProbabilityMeasure (mu.withDensity (ENNReal.ofReal ∘ p)) := by
    refine ⟨?_⟩
    rw [← lintegral_one, lintegral_withDensity_eq_lintegral_mul _ hpE measurable_const]
    simp only [Pi.mul_apply, mul_one, Function.comp_apply]
    change (∫⁻ x, ENNReal.ofReal (p x) ∂mu) = 1
    rw [← ofReal_integral_eq_lintegral_ofReal hpi
      (Filter.Eventually.of_forall hp0), hp1, ENNReal.ofReal_one]
  have hfun : (fun x : Fin N → X => ENNReal.ofReal (Real.exp (logLikelihood p q N x))) =
      fun x => ∏ i, e (x i) := by
    funext x
    unfold logLikelihood
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  rw [hfun]
  unfold productMeasureOfDensity
  rw [lintegral_fin_nat_prod_eq_prod (fun _ => he)]
  have hfactor : ∀ _i : Fin N, ∫⁻ x, e x ∂(mu.withDensity (ENNReal.ofReal ∘ p)) =
      ENNReal.ofReal (∫ x, expLogFactor p q x ∂mu) := by
    intro _i
    rw [lintegral_withDensity_eq_lintegral_mul _ hpE he,
      ofReal_integral_eq_lintegral_ofReal
        (expLogFactor_integrable p q mu hpm hqm hp0 hq0 hpi hqi)
        (Filter.Eventually.of_forall (expLogFactor_nonneg p q hp0))]
    refine lintegral_congr (fun x => ?_)
    change ENNReal.ofReal (p x) * ENNReal.ofReal
        (Real.exp (Real.log (q x / p x))) = ENNReal.ofReal (expLogFactor p q x)
    rw [← ENNReal.ofReal_mul (hp0 x)]
    rfl
  rw [Finset.prod_congr rfl (fun i _ => hfactor i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The exponential finite-product log-likelihood is integrable under the `p`-law.
Its mass is `c ^ N`, where `c = 1 - D + E`, `D` is the `q`-mass on `{p = 0}`,
and `E` is the `p`-mass on `{q = 0}`.  The `E` term records the edge behavior of
Lean's totalized `Real.log 0 = 0`.
-/
theorem exp_logLikelihood_integrable_and_integral_eq
    -- the common dominating measure.
    (mu : Measure X) (p q : X -> ℝ) (N : ℕ)
    -- measurability of the two supplied densities.
    (hpm : Measurable p) (hqm : Measurable q)
    -- pointwise nonnegativity of the two supplied densities.
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    -- integrability of the two supplied densities.
    (hpi : Integrable p mu) (hqi : Integrable q mu)
    -- both supplied densities have unit mass.
    (hp1 : ∫ x, p x ∂(mu) = 1) (hq1 : ∫ x, q x ∂(mu) = 1) :
    let D := ∫ x in {x | p x = 0}, q x ∂(mu)
    let E := ∫ x in {x | q x = 0}, p x ∂(mu)
    let c := 1 - D + E
    Integrable (fun x => Real.exp (logLikelihood p q N x))
        (productMeasureOfDensity mu p N) ∧
      ∫ x, Real.exp (logLikelihood p q N x) ∂(productMeasureOfDensity mu p N) = c ^ N := by
  dsimp only
  have hc : 0 ≤ 1 - (∫ x in {x | p x = 0}, q x ∂mu) +
      ∫ x in {x | q x = 0}, p x ∂mu := by
    rw [← expLogFactor_integral_eq p q mu hpm hqm hp0 hq0 hpi hqi hq1]
    exact integral_nonneg (expLogFactor_nonneg p q hp0)
  have hexp : Measurable (fun x : Fin N → X => Real.exp (logLikelihood p q N x)) :=
    Real.continuous_exp.measurable.comp <| Finset.measurable_sum _ fun i _ =>
      ((hqm.comp (measurable_pi_apply i)).div (hpm.comp (measurable_pi_apply i))).log
  constructor
  · refine ⟨hexp.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)),
      expLogLikelihood_lintegral_eq mu p q N hpm hqm hp0 hq0 hpi hqi hp1,
      expLogFactor_integral_eq p q mu hpm hqm hp0 hq0 hpi hqi hq1]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))
        hexp.aestronglyMeasurable,
      expLogLikelihood_lintegral_eq mu p q N hpm hqm hp0 hq0 hpi hqi hp1,
      expLogFactor_integral_eq p q mu hpm hqm hp0 hq0 hpi hqi hq1,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hc]

/-- On the product rectangle where both densities are positive, restriction of the
alternative product law agrees with tilting the base product law by the exponential
log-likelihood.  Outside this rectangle no absolute-continuity claim is made.
-/
theorem positiveRectangle_restrict_eq
    -- the common dominating measure and the two supplied densities.
    (mu : Measure X) (p q : X -> ℝ) (N : ℕ)
    -- measurability of the two supplied densities.
    (hpm : Measurable p) (hqm : Measurable q)
    -- pointwise nonnegativity of the two supplied densities.
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    -- integrability makes the two one-coordinate laws finite.
    (hpi : Integrable p mu) (hqi : Integrable q mu) :
    (productMeasureOfDensity mu q N).restrict
        (Set.univ.pi fun _ : Fin N => commonPositiveSet p q) =
      ((productMeasureOfDensity mu p N).withDensity
        (fun x => ENNReal.ofReal (Real.exp (logLikelihood p q N x)))).restrict
          (Set.univ.pi fun _ : Fin N => commonPositiveSet p q) := by
  let e : X → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (Real.log (q x / p x)))
  have he : Measurable e := ((hqm.div hpm).log.exp).ennreal_ofReal
  have hpE : Measurable (ENNReal.ofReal ∘ p) := hpm.ennreal_ofReal
  have hG : MeasurableSet (commonPositiveSet p q) := by
    exact (measurableSet_lt measurable_const hpm).inter
      (measurableSet_lt measurable_const hqm)
  letI : IsFiniteMeasure (mu.withDensity (ENNReal.ofReal ∘ p)) :=
    isFiniteMeasure_withDensity_ofReal hpi.hasFiniteIntegral
  letI : IsFiniteMeasure (mu.withDensity (ENNReal.ofReal ∘ q)) :=
    isFiniteMeasure_withDensity_ofReal hqi.hasFiniteIntegral
  have htilt :
      (mu.withDensity (ENNReal.ofReal ∘ p)).withDensity e =
        mu.withDensity (fun x => ENNReal.ofReal (expLogFactor p q x)) := by
    rw [← withDensity_mul _ hpE he]
    refine withDensity_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    change ENNReal.ofReal (p x) * ENNReal.ofReal
        (Real.exp (Real.log (q x / p x))) = ENNReal.ofReal (expLogFactor p q x)
    rw [← ENNReal.ofReal_mul (hp0 x)]
    rfl
  have hfactor :
      (mu.withDensity (ENNReal.ofReal ∘ q)).restrict (commonPositiveSet p q) =
        ((mu.withDensity (ENNReal.ofReal ∘ p)).withDensity e).restrict
          (commonPositiveSet p q) := by
    rw [htilt, restrict_withDensity hG, restrict_withDensity hG]
    refine withDensity_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' hG]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    change ENNReal.ofReal (q x) = ENNReal.ofReal (expLogFactor p q x)
    rw [expLogFactor_apply p q hp0 hq0]
    obtain ⟨hp, hq⟩ := hx
    rw [if_neg (ne_of_gt hp), if_neg (ne_of_gt hq)]
  haveI : IsFiniteMeasure ((mu.withDensity (ENNReal.ofReal ∘ p)).withDensity e) := by
    rw [htilt]
    exact isFiniteMeasure_withDensity_ofReal
      (expLogFactor_integrable p q mu hpm hqm hp0 hq0 hpi hqi).hasFiniteIntegral
  have hfun : (fun x : Fin N → X =>
      ENNReal.ofReal (Real.exp (logLikelihood p q N x))) =
      fun x => ∏ i, e (x i) := by
    funext x
    unfold logLikelihood
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  rw [hfun]
  unfold productMeasureOfDensity
  rw [pi_withDensity_prod (fun _ : Fin N => he), Measure.restrict_pi_pi,
    Measure.restrict_pi_pi]
  exact congrArg (fun nu => Measure.pi (fun _ : Fin N => nu)) hfactor

/-- The alternative product mass outside the common-positive rectangle is at most
`N` times the one-coordinate missing-support mass `D`.
-/
theorem alternative_positiveRectangle_compl_le
    -- the common dominating measure and the two supplied densities.
    (mu : Measure X) (p q : X -> ℝ) (N : ℕ)
    -- measurability of the two supplied densities.
    (hpm : Measurable p) (hqm : Measurable q)
    -- pointwise nonnegativity of the two supplied densities.
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    -- integrability of the alternative density.
    (hqi : Integrable q mu)
    -- unit mass of the alternative density.
    (hq1 : ∫ x, q x ∂(mu) = 1) :
    let D := ∫ x in {x | p x = 0}, q x ∂(mu)
    productMeasureOfDensity mu q N
        ((Set.univ.pi fun _ : Fin N => commonPositiveSet p q)ᶜ) ≤
      (N : ℝ≥0∞) * ENNReal.ofReal D := by
  dsimp only
  cases N with
  | zero =>
      have hrect : (Set.univ.pi fun _ : Fin 0 => commonPositiveSet p q) = Set.univ := by
        ext x
        simp
      rw [hrect]
      simp
  | succ N =>
      have hqE : Measurable (ENNReal.ofReal ∘ q) := hqm.ennreal_ofReal
      have hG : MeasurableSet (commonPositiveSet p q) := by
        exact (measurableSet_lt measurable_const hpm).inter
          (measurableSet_lt measurable_const hqm)
      have hP0 : MeasurableSet {x | p x = 0} := hpm (measurableSet_singleton 0)
      letI : IsProbabilityMeasure (mu.withDensity (ENNReal.ofReal ∘ q)) := by
        refine ⟨?_⟩
        rw [← lintegral_one,
          lintegral_withDensity_eq_lintegral_mul _ hqE measurable_const]
        simp only [Pi.mul_apply, mul_one, Function.comp_apply]
        change (∫⁻ x, ENNReal.ofReal (q x) ∂mu) = 1
        rw [← ofReal_integral_eq_lintegral_ofReal hqi
          (Filter.Eventually.of_forall hq0), hq1, ENNReal.ofReal_one]
      have hfactor : (mu.withDensity (ENNReal.ofReal ∘ q))
          (commonPositiveSet p q)ᶜ ≤
          ENNReal.ofReal (∫ x in {x | p x = 0}, q x ∂mu) := by
        have hle : (mu.withDensity (ENNReal.ofReal ∘ q))
            (commonPositiveSet p q)ᶜ ≤
            (mu.withDensity (ENNReal.ofReal ∘ q)) {x | p x = 0} := by
          rw [withDensity_apply _ hG.compl, withDensity_apply _ hP0,
            ← lintegral_indicator hG.compl, ← lintegral_indicator hP0]
          refine lintegral_mono (fun x => ?_)
          by_cases hx : x ∈ (commonPositiveSet p q)ᶜ
          · rw [Set.indicator_of_mem hx]
            change ENNReal.ofReal (q x) ≤
              {x | p x = 0}.indicator (ENNReal.ofReal ∘ q) x
            by_cases hpz : p x = 0
            · rw [Set.indicator_of_mem
                (show x ∈ {x | p x = 0} from hpz)]
              rfl
            · have hp : 0 < p x := lt_of_le_of_ne (hp0 x) (Ne.symm hpz)
              rw [Set.mem_compl_iff, commonPositiveSet, Set.mem_setOf_eq, not_and] at hx
              have hqz : q x = 0 := le_antisymm (not_lt.mp (hx hp)) (hq0 x)
              rw [hqz, ENNReal.ofReal_zero]
              exact zero_le
          · rw [Set.indicator_of_notMem hx]
            exact zero_le
        refine hle.trans_eq ?_
        rw [withDensity_apply _ hP0]
        change (∫⁻ x in {x | p x = 0}, ENNReal.ofReal (q x) ∂mu) = _
        rw [← ofReal_integral_eq_lintegral_ofReal hqi.restrict
          (ae_restrict_of_ae (Filter.Eventually.of_forall hq0))]
      have hsubset :
          (Set.univ.pi fun _ : Fin (N + 1) => commonPositiveSet p q)ᶜ ⊆
            ⋃ i : Fin (N + 1), Function.eval i ⁻¹' (commonPositiveSet p q)ᶜ := by
        intro x hx
        rw [Set.mem_compl_iff, Set.mem_univ_pi] at hx
        push Not at hx
        obtain ⟨i, hi⟩ := hx
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      calc
        productMeasureOfDensity mu q (N + 1)
            (Set.univ.pi fun _ : Fin (N + 1) => commonPositiveSet p q)ᶜ
            ≤ productMeasureOfDensity mu q (N + 1)
                (⋃ i : Fin (N + 1), Function.eval i ⁻¹' (commonPositiveSet p q)ᶜ) :=
          measure_mono hsubset
        _ ≤ ∑ i : Fin (N + 1), productMeasureOfDensity mu q (N + 1)
              (Function.eval i ⁻¹' (commonPositiveSet p q)ᶜ) :=
          measure_iUnion_fintype_le _ _
        _ = ∑ _i : Fin (N + 1), (mu.withDensity (ENNReal.ofReal ∘ q))
              (commonPositiveSet p q)ᶜ := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact (MeasureTheory.measurePreserving_eval
            (μ := fun _ : Fin (N + 1) => mu.withDensity (ENNReal.ofReal ∘ q)) i).measure_preimage
              hG.compl.nullMeasurableSet
        _ = (N.succ : ℝ≥0∞) * (mu.withDensity (ENNReal.ofReal ∘ q))
              (commonPositiveSet p q)ᶜ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (N.succ : ℝ≥0∞) *
              ENNReal.ofReal (∫ x in {x | p x = 0}, q x ∂mu) := by
          gcongr

/-- Eventwise finite-product comparison between the alternative law and exponential
integration under the base law.  The real error is the support-mismatch contribution
`2 * N * D` plus the normalization defect `|c ^ N - 1|`.
-/
theorem finiteProduct_expLog_comparison
    -- the common dominating measure.
    (mu : Measure X) (p q : X -> ℝ) (N : ℕ)
    -- measurability of the two supplied densities.
    (hpm : Measurable p) (hqm : Measurable q)
    -- pointwise nonnegativity of the two supplied densities.
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    -- integrability of the two supplied densities.
    (hpi : Integrable p mu) (hqi : Integrable q mu)
    -- both supplied densities have unit mass.
    (hp1 : ∫ x, p x ∂(mu) = 1) (hq1 : ∫ x, q x ∂(mu) = 1) :
    let D := ∫ x in {x | p x = 0}, q x ∂(mu)
    let E := ∫ x in {x | q x = 0}, p x ∂(mu)
    let c := 1 - D + E
    Integrable (fun x => Real.exp (logLikelihood p q N x))
        (productMeasureOfDensity mu p N) ∧
      (∫ x, Real.exp (logLikelihood p q N x) ∂(productMeasureOfDensity mu p N) = c ^ N) ∧
      ∀ A : Set (Fin N -> X), MeasurableSet A ->
        |(productMeasureOfDensity mu q N).real A -
            ∫ x in A, Real.exp (logLikelihood p q N x)
              ∂(productMeasureOfDensity mu p N)| ≤
          2 * (N : ℝ) * D + |c ^ N - 1| := by
  dsimp only
  let f : (Fin N → X) → ℝ := fun x => Real.exp (logLikelihood p q N x)
  let P := productMeasureOfDensity mu p N
  let Q := productMeasureOfDensity mu q N
  let G := Set.univ.pi fun _ : Fin N => commonPositiveSet p q
  let T := P.withDensity (ENNReal.ofReal ∘ f)
  have hmass := exp_logLikelihood_integrable_and_integral_eq
    mu p q N hpm hqm hp0 hq0 hpi hqi hp1 hq1
  have hfint : Integrable f P := by simpa only [f, P] using hmass.1
  have hfmeas : Measurable f := by
    exact Real.continuous_exp.measurable.comp <| Finset.measurable_sum _ fun i _ =>
      ((hqm.comp (measurable_pi_apply i)).div (hpm.comp (measurable_pi_apply i))).log
  have hf0 : ∀ x, 0 ≤ f x := fun x => (Real.exp_pos _).le
  have hG : MeasurableSet G := by
    exact MeasurableSet.univ_pi fun _ =>
      (measurableSet_lt measurable_const hpm).inter
        (measurableSet_lt measurable_const hqm)
  have hPprob : IsProbabilityMeasure P := by
    simpa only [P] using productMeasureOfDensity_isProbabilityMeasure mu p N hpm hp0 hpi hp1
  have hQprob : IsProbabilityMeasure Q := by
    simpa only [Q] using productMeasureOfDensity_isProbabilityMeasure mu q N hqm hq0 hqi hq1
  letI : IsProbabilityMeasure P := hPprob
  letI : IsProbabilityMeasure Q := hQprob
  have hTfinite : IsFiniteMeasure T := by
    simpa only [T, Function.comp_apply] using!
      isFiniteMeasure_withDensity_ofReal hfint.hasFiniteIntegral
  letI : IsFiniteMeasure T := hTfinite
  have hrestrict : Q.restrict G = T.restrict G := by
    simpa only [Q, T, P, G, f, Function.comp_apply] using!
      positiveRectangle_restrict_eq mu p q N hpm hqm hp0 hq0 hpi hqi
  have hTuniv : T.real Set.univ =
      (1 - (∫ x in {x | p x = 0}, q x ∂mu) +
        ∫ x in {x | q x = 0}, p x ∂mu) ^ N := by
    calc
      T.real Set.univ = ∫ _x, (1 : ℝ) ∂T := by simp
      _ = ∫ x, f x ∂P := by
        simp only [T, P]
        simpa only [Function.comp_apply, ENNReal.toReal_ofReal (hf0 _), smul_eq_mul,
          mul_one] using!
          (integral_withDensity_eq_integral_toReal_smul hfmeas.ennreal_ofReal
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
            (fun _ => (1 : ℝ)))
      _ = _ := by simpa only [f, P] using hmass.2
  refine ⟨hfint, hmass.2, ?_⟩
  intro A hA
  have hAGeq : Q.real (A ∩ G) = T.real (A ∩ G) := by
    have := congrArg (fun nu : Measure (Fin N → X) => nu.real A) hrestrict
    simpa only [measureReal_restrict_apply hA] using this
  have hQsplit : Q.real (A ∩ G) + Q.real (A \ G) = Q.real A :=
    measureReal_inter_add_diff hG
  have hTsplit : T.real (A ∩ G) + T.real (A \ G) = T.real A :=
    measureReal_inter_add_diff hG
  have hQcomp : Q.real Gᶜ ≤
      (N : ℝ) * (∫ x in {x | p x = 0}, q x ∂mu) := by
    have h := alternative_positiveRectangle_compl_le
      mu p q N hpm hqm hp0 hq0 hqi hq1
    change Q Gᶜ ≤ (N : ℝ≥0∞) * ENNReal.ofReal
      (∫ x in {x | p x = 0}, q x ∂mu) at h
    rw [← ENNReal.toReal_le_toReal (measure_ne_top Q Gᶜ)
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal] at h
    · exact h
    · exact integral_nonneg_of_ae
        (ae_restrict_of_ae (Filter.Eventually.of_forall hq0))
  have hQdiff : Q.real (A \ G) ≤ Q.real Gᶜ :=
    measureReal_mono (Set.diff_subset_compl A G)
  have hTdiff : T.real (A \ G) ≤ T.real Gᶜ :=
    measureReal_mono (Set.diff_subset_compl A G)
  have hQG : Q.real G + Q.real Gᶜ = 1 := by
    simpa only [probReal_univ] using measureReal_add_measureReal_compl hG (μ := Q)
  have hTcomp : T.real Gᶜ ≤ Q.real Gᶜ + |T.real Set.univ - 1| := by
    have hGeq : Q.real G = T.real G := by
      have := congrArg (fun nu : Measure (Fin N → X) => nu.real Set.univ) hrestrict
      simpa only [measureReal_restrict_apply_univ] using this
    have hTG : T.real G + T.real Gᶜ = T.real Set.univ :=
      measureReal_add_measureReal_compl hG
    rw [← hGeq] at hTG
    have habs : T.real Set.univ - 1 ≤ |T.real Set.univ - 1| := le_abs_self _
    linarith
  have hsetIntegral : ∫ x in A, f x ∂P = T.real A := by
    calc
      ∫ x in A, f x ∂P = ∫ _x in A, (1 : ℝ) ∂T := by
        simp only [T]
        symm
        calc
          ∫ _x in A, (1 : ℝ) ∂P.withDensity (ENNReal.ofReal ∘ f) =
              ∫ x in A, (ENNReal.ofReal (f x)).toReal • (1 : ℝ) ∂P := by
            simpa only [Function.comp_apply] using!
              (setIntegral_withDensity_eq_setIntegral_toReal_smul
                hfmeas.ennreal_ofReal
                (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
                (fun _ => (1 : ℝ)) hA)
          _ = ∫ x in A, f x ∂P := by
            simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul, mul_one]
      _ = T.real A := by simp
  rw [show (∫ x in A, Real.exp (logLikelihood p q N x) ∂P) = T.real A by
    simpa only [f] using hsetIntegral]
  rw [← hQsplit, ← hTsplit, hAGeq]
  have hnonnegQ : 0 ≤ Q.real (A \ G) := measureReal_nonneg
  have hnonnegT : 0 ≤ T.real (A \ G) := measureReal_nonneg
  calc
    |(T.real (A ∩ G) + Q.real (A \ G)) -
        (T.real (A ∩ G) + T.real (A \ G))| =
        |Q.real (A \ G) - T.real (A \ G)| := by ring_nf
    _ ≤ Q.real (A \ G) + T.real (A \ G) := by
      rw [abs_le]
      constructor <;> linarith
    _ ≤ 2 * ((N : ℝ) * ∫ x in {x | p x = 0}, q x ∂mu) +
        |T.real Set.univ - 1| := by linarith
    _ = 2 * (N : ℝ) * (∫ x in {x | p x = 0}, q x ∂mu) +
        |(1 - (∫ x in {x | p x = 0}, q x ∂mu) +
          ∫ x in {x | q x = 0}, p x ∂mu) ^ N - 1| := by rw [hTuniv]; ring

/-- If `m n -> infinity` and `m n * a n -> 0`, then the corresponding natural
powers `(1 + a n) ^ m n` tend to one.  No sign condition is imposed on `a`.
-/
theorem tendsto_one_add_pow_nat_zero_of_scaled_tendsto
    -- the natural exponent sequence.
    (m : ℕ -> ℕ)
    -- the real perturbation sequence.
    (a : ℕ -> ℝ)
    -- divergence of the exponent sequence.
    (hm : Tendsto m atTop atTop)
    -- the scaled perturbations vanish.
    (ha : Tendsto (fun n => (m n : ℝ) * a n) atTop (nhds 0)) :
    Tendsto (fun n => (1 + a n) ^ m n) atTop (nhds 1) := by
  have hmR : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hmpos : ∀ᶠ n in atTop, 0 < m n :=
    hm (eventually_ge_atTop 1)
  have ha0 : Tendsto a atTop (nhds 0) := by
    have hinv : Tendsto (fun n => ((m n : ℝ)⁻¹)) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hmR
    have hprod := ha.mul hinv
    simp only [zero_mul] at hprod
    apply hprod.congr'
    filter_upwards [hmpos] with n hn
    field_simp [Nat.ne_of_gt hn]
  have ha0C : Tendsto (fun n => (a n : ℂ)) atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp ha0
  have hma0C : Tendsto (fun n => (((m n : ℝ) * a n : ℝ) : ℂ)) atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp ha
  have herr : Tendsto (fun n => (m n : ℂ) *
      (Complex.log (1 + (a n : ℂ)) - (a n : ℂ))) atTop (nhds 0) := by
    apply ((Asymptotics.isBigO_refl (fun n => (m n : ℂ)) atTop).mul
      (Complex.log_sub_self_isBigO.comp_tendsto ha0C)).trans_tendsto
    have hmul := hma0C.mul ha0C
    simp only [mul_zero] at hmul
    apply hmul.congr'
    filter_upwards [] with n
    simp only [Function.comp_apply]
    push_cast
    ring
  have hlogC : Tendsto (fun n => (m n : ℂ) * Complex.log (1 + (a n : ℂ)))
      atTop (nhds 0) := by
    have hsum := hma0C.add herr
    simp only [add_zero] at hsum
    apply hsum.congr'
    filter_upwards [] with n
    push_cast
    ring_nf
  have hbase : ∀ᶠ n in atTop, 0 < 1 + a n := by
    filter_upwards [ha0.eventually (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num))] with n hn
    linarith [hn.1]
  have hlog : Tendsto (fun n => (m n : ℝ) * Real.log (1 + a n))
      atTop (nhds 0) := by
    rw [← tendsto_ofReal_iff]
    apply hlogC.congr'
    filter_upwards [hbase] with n hn
    rw [Complex.ofReal_mul, Complex.ofReal_log hn.le, Complex.ofReal_add,
      Complex.ofReal_one]
    norm_cast
  have hexp := (Real.continuous_exp.tendsto 0).comp hlog
  simpa only [Real.exp_zero] using hexp.congr' (by
    filter_upwards [hbase] with n hn
    change Real.exp ((m n : ℝ) * Real.log (1 + a n)) = (1 + a n) ^ m n
    rw [Real.exp_nat_mul, Real.exp_log hn])

end AsymptoticStatistics.FiniteProductLikelihood
