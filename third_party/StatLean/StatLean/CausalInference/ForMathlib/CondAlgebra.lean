module
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Conditioning on a discrete random variable — the algebra of covariate cells

Theorem-agnostic toolkit for conditioning on the level sets of a map `X : Ω → 𝒳` with `𝒳`
a finite type: the law of total expectation over the cells, the two-arm split inside a
cell, and the factorization of an expectation under independence. Everything is phrased
with `ProbabilityTheory.cond` (`μ[|s]`), so a "conditional expectation given `X = x`" is
an ordinary Bochner integral.

Main results:

* `integral_eq_sum_cell` — `∫ f dμ = ∑ₓ μ(X = x) · ∫ f d(μ[|X = x])`.
* `integral_cell_eq_arm_split` — inside a cell, `∫ f d(μ[|X = x])` splits over `{Z = 1}`
  and `{Z = 0}` with weights `e(x)` and `1 - e(x)`.
* `integral_cond_indepFun_mul_ind` — under independence of `y` and `Z` in a cell,
  `∫ 1{Z = z}·y = P(Z = z)·∫ y`.

**Reference.** Standard measure-theoretic bookkeeping; no textbook result is being
formalized here. The statistical use is P. Ding, *A First Course in Causal Inference*,
arXiv:2305.18793v2, 2023, §10.3.1 eq. (10.8), where identification formulas are written
as finite sums over the values of a discrete covariate. (`Ding §10.3.1`.)

**Proof formalization notes.**

* `ProbabilityTheory.cond μ s = (μ s)⁻¹ • μ.restrict s`, so `∫ f d(μ[|s])` equals
  `(μ s).toReal⁻¹ • ∫ x in s, f x ∂μ`; that identity (`integral_cond_eq_setIntegral`) is
  the bridge every other lemma in this file uses.
* Null cells: `cond` scales by `(μ s)⁻¹ = ∞`, but the `toReal` route makes the value `0`;
  the decomposition lemmas are stated so that null cells contribute `0` on both sides, so
  no positivity hypotheses are needed for the *sums*. Positivity is required only where a
  single cell's conditional expectation is claimed to equal something.
* The cells `X ⁻¹' {x}` for `x : 𝒳` are pairwise disjoint with union `univ`, so the
  decomposition is `MeasureTheory.integral_fintype`-style over a finite partition.

**Bibliographic comments.** None: this is infrastructure, not a book result.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳]
  {μ : Measure Ω}

/-- Integration against a conditional measure is the set integral rescaled by the mass of
the conditioning event. -/
theorem integral_cond_eq_setIntegral (s : Set Ω) (f : Ω → ℝ) :
    ∫ ω, f ω ∂(μ[|s]) = (μ s).toReal⁻¹ * ∫ ω in s, f ω ∂μ := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]

/-- The mass of a conditioning event times its conditional integral is the set integral
— the form used to reassemble a decomposition, valid even when the event is null. -/
theorem measureReal_mul_integral_cond {s : Set Ω} (hs : μ s ≠ ⊤) (f : Ω → ℝ) :
    (μ s).toReal * ∫ ω, f ω ∂(μ[|s]) = ∫ ω in s, f ω ∂μ := by
  rw [integral_cond_eq_setIntegral, ← mul_assoc]
  rcases eq_or_ne (μ s) 0 with h | h
  · rw [Measure.restrict_eq_zero.2 h, integral_zero_measure, h]
    simp
  · rw [mul_inv_cancel₀ (by simp [ENNReal.toReal_eq_zero_iff, h, hs]), one_mul]

/-- **Law of total expectation over a discrete covariate**: an integral is the
cell-probability-weighted sum of the within-cell conditional integrals. -/
theorem integral_eq_sum_cell [Fintype 𝒳] [MeasurableSingletonClass 𝒳]
    [IsFiniteMeasure μ] {X : Ω → 𝒳}
    -- USER-INPUT: the covariate is a random variable; user-supplied data
    (hX : Measurable X) {f : Ω → ℝ}
    -- USER-INPUT: integrability of the integrand; needed for the additivity of the integral
    (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ = ∑ x : 𝒳, (μ (X ⁻¹' {x})).toReal * ∫ ω, f ω ∂(μ[|X ⁻¹' {x}]) := by
  have hmeas : ∀ x : 𝒳, MeasurableSet (X ⁻¹' {x}) := fun x => hX (measurableSet_singleton x)
  have hdisj : Pairwise (Function.onFun Disjoint fun x : 𝒳 => X ⁻¹' {x}) := by
    intro a b hab
    simp only [Function.onFun, Set.disjoint_left, Set.mem_preimage, Set.mem_singleton_iff]
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have hcover : (⋃ x : 𝒳, X ⁻¹' {x}) = Set.univ := by
    ext ω; simp
  calc ∫ ω, f ω ∂μ = ∫ ω in Set.univ, f ω ∂μ := setIntegral_univ.symm
    _ = ∫ ω in ⋃ x : 𝒳, X ⁻¹' {x}, f ω ∂μ := by rw [hcover]
    _ = ∑ x : 𝒳, ∫ ω in X ⁻¹' {x}, f ω ∂μ :=
        integral_iUnion_fintype hmeas hdisj fun _ => hf.integrableOn
    _ = ∑ x : 𝒳, (μ (X ⁻¹' {x})).toReal * ∫ ω, f ω ∂(μ[|X ⁻¹' {x}]) :=
        Finset.sum_congr rfl fun x _ =>
          (measureReal_mul_integral_cond (measure_ne_top μ _) f).symm

/-- Auxiliary: a conditional measure of a finite measure takes no infinite value. -/
private lemma cond_apply_ne_top [IsFiniteMeasure μ] {c : Set Ω} (hc : MeasurableSet c)
    (t : Set Ω) : (μ[|c]) t ≠ ⊤ := by
  rcases eq_or_ne (μ c) 0 with h | h
  · simp [cond_eq_zero_of_meas_eq_zero h]
  · rw [cond_apply hc]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h) (measure_ne_top _ _)

/-- Auxiliary: integrability transfers to any conditional measure of a finite measure. -/
private lemma integrable_cond [IsFiniteMeasure μ] {c : Set Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) : Integrable f (μ[|c]) := by
  rcases eq_or_ne (μ c) 0 with h | h
  · simp [cond_eq_zero_of_meas_eq_zero h]
  · exact (hf.integrableOn (s := c)).smul_measure (by simp [h])

/-- **Two-arm split inside a cell**: conditioning further on the treatment splits a
within-cell conditional integral into the propensity-weighted average of the two arm
conditional integrals. -/
theorem integral_cond_cell_eq_arm_split [MeasurableSingletonClass 𝒳] [IsFiniteMeasure μ]
    {X : Ω → 𝒳} {Z : Ω → Bool}
    -- USER-INPUT: covariate and treatment are random variables; user-supplied data
    (hX : Measurable X) (hZ : Measurable Z) {f : Ω → ℝ}
    -- USER-INPUT: integrability of the integrand
    (hf : Integrable f μ) (x : 𝒳) :
    ∫ ω, f ω ∂(μ[|X ⁻¹' {x}])
      = ((μ[|X ⁻¹' {x}]) {ω | Z ω = true}).toReal
            * ∫ ω, f ω ∂(μ[|{ω | Z ω = true} ∩ X ⁻¹' {x}])
        + ((μ[|X ⁻¹' {x}]) {ω | Z ω = false}).toReal
            * ∫ ω, f ω ∂(μ[|{ω | Z ω = false} ∩ X ⁻¹' {x}]) := by
  have hc : MeasurableSet (X ⁻¹' {x}) := hX (measurableSet_singleton x)
  have ht : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  have hcompl : {ω | Z ω = true}ᶜ = {ω | Z ω = false} := by
    ext ω; simp
  have key : ∀ t : Set Ω, MeasurableSet t →
      ((μ[|X ⁻¹' {x}]) t).toReal * ∫ ω, f ω ∂(μ[|t ∩ X ⁻¹' {x}])
        = ∫ ω in t, f ω ∂(μ[|X ⁻¹' {x}]) := by
    intro t htm
    rw [Set.inter_comm t (X ⁻¹' {x}), ← cond_cond_eq_cond_inter' hc htm (measure_ne_top μ _)]
    exact measureReal_mul_integral_cond (cond_apply_ne_top hc t) f
  rw [key _ ht, key {ω | Z ω = false} (hZ (measurableSet_singleton false)), ← hcompl,
    integral_add_compl ht (integrable_cond hf)]

/-- The two arm probabilities inside a cell sum to one on a cell of positive mass. -/
theorem cond_treated_add_cond_control [MeasurableSingletonClass 𝒳] [IsFiniteMeasure μ]
    {X : Ω → 𝒳} {Z : Ω → Bool} (hX : Measurable X) (hZ : Measurable Z) {x : 𝒳}
    -- USER-INPUT: a cell of positive probability; on a null cell both sides are `0`
    (hpos : μ (X ⁻¹' {x}) ≠ 0) :
    ((μ[|X ⁻¹' {x}]) {ω | Z ω = true}).toReal
        + ((μ[|X ⁻¹' {x}]) {ω | Z ω = false}).toReal = 1 := by
  haveI : IsProbabilityMeasure (μ[|X ⁻¹' {x}]) := cond_isProbabilityMeasure hpos
  have ht : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  have hcompl : {ω | Z ω = false} = {ω | Z ω = true}ᶜ := by
    ext ω; simp
  rw [hcompl, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    measure_add_measure_compl ht]
  simp

/-- **Factorization under independence**: if `y` and `Z` are independent under a measure,
the expectation of `y` restricted to an arm factors into the arm probability times the
unrestricted expectation of `y`. This is the workhorse turning unconfoundedness into
identification. -/
theorem integral_ind_mul_of_indepFun {ν : Measure Ω} [IsProbabilityMeasure ν]
    {y : Ω → ℝ} {Z : Ω → Bool}
    -- USER-INPUT: independence of the potential outcome and the treatment (unconfoundedness)
    (hindep : IndepFun y Z ν)
    -- USER-INPUT: the potential outcome is integrable
    (hy : Integrable y ν)
    -- USER-INPUT: measurability of the two variables
    (hym : Measurable y) (hZ : Measurable Z) (z : Bool) :
    ∫ ω, (if Z ω = z then (1 : ℝ) else 0) * y ω ∂ν
      = (ν {ω | Z ω = z}).toReal * ∫ ω, y ω ∂ν := by
  have hs : MeasurableSet {ω | Z ω = z} := hZ (measurableSet_singleton z)
  have hgm : Measurable (fun b : Bool => if b = z then (1 : ℝ) else 0) := by
    measurability
  have hmul := hindep.integral_fun_comp_mul_comp (f := id)
    (g := fun b : Bool => if b = z then (1 : ℝ) else 0) hym.aemeasurable hZ.aemeasurable
    aestronglyMeasurable_id hgm.aestronglyMeasurable
  simp only [id] at hmul
  have hind : (fun ω => if Z ω = z then (1 : ℝ) else 0)
      = Set.indicator {ω | Z ω = z} 1 := by
    funext ω
    by_cases h : Z ω = z <;> simp [Set.indicator, h]
  calc ∫ ω, (if Z ω = z then (1 : ℝ) else 0) * y ω ∂ν
      = ∫ ω, y ω * (if Z ω = z then (1 : ℝ) else 0) ∂ν := by
        simp_rw [mul_comm]
    _ = (∫ ω, y ω ∂ν) * ∫ ω, (if Z ω = z then (1 : ℝ) else 0) ∂ν := hmul
    _ = (ν {ω | Z ω = z}).toReal * ∫ ω, y ω ∂ν := by
        rw [hind, integral_indicator_one hs, measureReal_def, mul_comm]

/-- Consequence of the previous lemma in conditional form: under independence, the
conditional expectation of `y` given an arm equals its unconditional expectation. -/
theorem integral_cond_arm_eq_of_indepFun {ν : Measure Ω} [IsProbabilityMeasure ν]
    {y : Ω → ℝ} {Z : Ω → Bool} (hindep : IndepFun y Z ν) (hy : Integrable y ν)
    (hym : Measurable y) (hZ : Measurable Z) {z : Bool}
    -- USER-INPUT: the arm has positive probability; on a null arm the left side is `0`
    (hpos : ν {ω | Z ω = z} ≠ 0) :
    ∫ ω, y ω ∂(ν[|{ω | Z ω = z}]) = ∫ ω, y ω ∂ν := by
  have hs : MeasurableSet {ω | Z ω = z} := hZ (measurableSet_singleton z)
  have hset : ∫ ω in {ω | Z ω = z}, y ω ∂ν
      = ∫ ω, (if Z ω = z then (1 : ℝ) else 0) * y ω ∂ν := by
    rw [← integral_indicator hs]
    congr 1
    funext ω
    by_cases h : Z ω = z <;> simp [Set.indicator, h]
  rw [integral_cond_eq_setIntegral, hset, integral_ind_mul_of_indepFun hindep hy hym hZ z,
    ← mul_assoc, inv_mul_cancel₀ (by simp [ENNReal.toReal_eq_zero_iff, hpos,
      measure_ne_top ν _]), one_mul]

end StatLean.CausalInference
