module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# Gaussian exponential-square moments and weighted sums

Two Gaussian facts feeding the sup-norm risk analysis of linear smoothers:

* `lintegral_exp_mul_sq_gaussianReal_le` — for `X ~ N(0, v)` and `4av ≤ 1`:
  `E[exp(a·X²)] ≤ √2` (the classical `α₀ = 1/(4σ²)` exponential-square moment bound).
* `hasLaw_sum_mul_gaussianReal` — a linear combination `∑ cᵢ·ξᵢ` of independent `N(0, v)`
  variables is `N(0, (∑ cᵢ²)·v)`.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.6.2 (Gaussian exponential-square moment bricks
for Lemma 1.6 and Corollary 1.3).

**Proof formalization notes.** The exponential-square moment is the explicit Gaussian integral
`E exp(aX²) = (1 − 2av)^{-1/2}`, computed from the density (`gaussianPDFReal`) and
`integral_gaussian`-family lemmas; at `4av ≤ 1` the value is at most `√2`, and for `a ≤ 0` the
integrand is bounded by `1`. The `v = 0` case is the Dirac mass, where the integral is `1`.
The weighted-sum law is induction on the index set via
`ProbabilityTheory.gaussianReal_conv_gaussianReal` (convolution of Gaussians), the map lemma
`gaussianReal_map_const_mul` for the scalar factors, and independence of the partial sum from
the next coordinate (`iIndepFun.indepFun_finset_sum_of_notMem`-style); zero coefficients
degrade gracefully since `N(0,0) = δ₀`.

**Bibliographic comments.** Classical Gaussian computations; the exponential-square moment in
this normalized form is folklore (see e.g. relevant chapters of textbooks on Gaussian
processes).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- **Exponential-square moment of a centered Gaussian**: for `X ~ N(0, v)` and `4·a·v ≤ 1`,
`E[exp(a·X²)] ≤ √2`. (For `a ≤ 0` the bound is trivial; at `a = 1/(4v)` the exact value is
`(1 − 1/2)^{-1/2} = √2`.) -/
theorem lintegral_exp_mul_sq_gaussianReal_le (v : ℝ≥0) {a : ℝ}
    -- USER-INPUT: the exponent scale satisfies `4·a·v ≤ 1`; classical range of the Gaussian
    -- exponential-square moment
    (ha : a * (4 * (v : ℝ)) ≤ 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (a * x ^ 2)) ∂(gaussianReal 0 v)
      ≤ ENNReal.ofReal (Real.sqrt 2) := by
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, lintegral_dirac]
    rw [show a * (0 : ℝ) ^ 2 = 0 by ring, Real.exp_zero, ENNReal.ofReal_one]
    exact ENNReal.one_le_ofReal.mpr hsqrt2
  have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hv
  by_cases ha0 : a ≤ 0
  · calc ∫⁻ x, ENNReal.ofReal (Real.exp (a * x ^ 2)) ∂(gaussianReal 0 v)
        ≤ ∫⁻ _, 1 ∂(gaussianReal 0 v) := by
          refine lintegral_mono (fun x => ?_)
          exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg ha0 (sq_nonneg x)))
      _ = 1 := by rw [lintegral_one, measure_univ]
      _ ≤ ENNReal.ofReal (Real.sqrt 2) := ENNReal.one_le_ofReal.mpr hsqrt2
  replace ha0 : 0 < a := not_le.mp ha0
  -- Main case: `0 < a` and `v ≠ 0`. Set the reduced exponent scale `c = 1/(2v) − a > 0`.
  set c : ℝ := 1 / (2 * (v : ℝ)) - a with hcdef
  have hπ0 : (Real.pi) ≠ 0 := ne_of_gt Real.pi_pos
  have hv0 : (v : ℝ) ≠ 0 := ne_of_gt hvpos
  have h2vc : 2 * (v : ℝ) * c = 1 - 2 * a * (v : ℝ) := by rw [hcdef]; field_simp
  have hcpos : (0 : ℝ) < c := by
    by_contra h
    replace h : c ≤ 0 := not_lt.mp h
    have hle : 2 * (v : ℝ) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    rw [h2vc] at hle
    nlinarith [ha]
  have hc0 : c ≠ 0 := ne_of_gt hcpos
  have hmeas_g : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x ^ 2))) := by fun_prop
  rw [gaussianReal_of_var_ne_zero 0 hv,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 v) hmeas_g]
  -- Merge the two exponentials into a single centered Gaussian kernel `exp(−c x²)`.
  have hint_eq : ∀ x : ℝ,
      (gaussianPDF 0 v * fun x => ENNReal.ofReal (Real.exp (a * x ^ 2))) x
        = ENNReal.ofReal ((√(2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-c * x ^ 2)) := by
    intro x
    simp only [Pi.mul_apply, gaussianPDF]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x)]
    congr 1
    rw [gaussianPDFReal, mul_assoc, ← Real.exp_add]
    congr 2
    rw [sub_zero, hcdef]
    ring
  rw [lintegral_congr hint_eq,
    ← ofReal_integral_eq_lintegral_ofReal
      ((integrable_exp_neg_mul_sq hcpos).const_mul _)
      (Filter.Eventually.of_forall (fun x => by positivity))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul, integral_gaussian]
  -- Reduce to `1/(2vc) ≤ 2`, i.e. `4·a·v ≤ 1`.
  have hAB : (2 * Real.pi * (v : ℝ))⁻¹ * (Real.pi / c) = 1 / (2 * (v : ℝ) * c) := by
    field_simp
  rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [hAB, div_le_iff₀ (mul_pos (by positivity) hcpos)]
  nlinarith [ha, h2vc]

/-- **Weighted sums of independent centered Gaussians are Gaussian**:
if `ξ 0, …, ξ (n−1)` are independent with common law `N(0, v)`, then
`∑ i, c i · ξ i` has law `N(0, (∑ i, c i²)·v)`. -/
theorem hasLaw_sum_mul_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {ξ : Fin n → Ω → ℝ} {v : ℝ≥0} (c : Fin n → ℝ)
    -- LEAN-ONLY: measurability of the coordinates; standard regularity
    (hmeas : ∀ i, Measurable (ξ i))
    -- USER-INPUT: mutual independence of the noise coordinates; classical Gaussian-sum input
    (hindep : iIndepFun ξ P)
    -- USER-INPUT: each coordinate is centered Gaussian with variance `v`
    (hlaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 v) P) :
    HasLaw (fun ω => ∑ i, c i * ξ i ω)
      (gaussianReal 0 ((∑ i, (c i) ^ 2 : ℝ).toNNReal * v)) P := by
  classical
  -- The rescaled coordinates `Y i = c i · ξ i`.
  set Y : Fin n → Ω → ℝ := fun i ω => c i * ξ i ω with hY
  have hYmeas : ∀ i, Measurable (Y i) := fun i => (hmeas i).const_mul (c i)
  have hYindep : iIndepFun Y P :=
    hindep.comp (fun i x => c i * x) (fun i => measurable_id.const_mul (c i))
  have hYlaw : ∀ i, HasLaw (Y i) (gaussianReal 0 (((c i) ^ 2).toNNReal * v)) P := by
    intro i
    have hmap : HasLaw (fun x : ℝ => c i * x)
        (gaussianReal 0 (((c i) ^ 2).toNNReal * v)) (gaussianReal 0 v) := by
      refine ⟨(measurable_id.const_mul (c i)).aemeasurable, ?_⟩
      rw [gaussianReal_map_const_mul]
      congr 1
      · ring
      · congr 1
        exact NNReal.eq (by simp [Real.coe_toNNReal _ (sq_nonneg _)])
    exact hmap.comp (hlaw i)
  -- Prove the `Finset`-indexed version by induction, then specialise to `univ`.
  suffices H : ∀ s : Finset (Fin n),
      HasLaw (fun ω => ∑ i ∈ s, Y i ω)
        (gaussianReal 0 ((∑ i ∈ s, (c i) ^ 2 : ℝ).toNNReal * v)) P by
    simpa only [hY] using H Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Real.toNNReal_zero, zero_mul, gaussianReal_zero_var]
    refine ⟨aemeasurable_const, ?_⟩
    rw [Measure.map_const]
    simp
  | insert i s hi ih =>
    have hsumeq : (∑ j ∈ s, Y j) = fun ω => ∑ j ∈ s, Y j ω := by
      funext ω; rw [Finset.sum_apply]
    have hstep : IndepFun (Y i) (fun ω => ∑ j ∈ s, Y j ω) P := by
      rw [← hsumeq]; exact (hYindep.indepFun_finset_sum_of_notMem hYmeas hi).symm
    have hsum : HasLaw (fun ω => Y i ω + ∑ j ∈ s, Y j ω)
        ((gaussianReal 0 (((c i) ^ 2).toNNReal * v)) ∗
          gaussianReal 0 ((∑ j ∈ s, (c j) ^ 2 : ℝ).toNNReal * v)) P :=
      hstep.hasLaw_fun_add (hYlaw i) ih
    rw [gaussianReal_conv_gaussianReal] at hsum
    simp only [add_zero] at hsum
    have hfun : (fun ω => ∑ j ∈ insert i s, Y j ω)
        = (fun ω => Y i ω + ∑ j ∈ s, Y j ω) := funext (fun ω => Finset.sum_insert hi)
    have hvar : ((∑ j ∈ insert i s, (c j) ^ 2 : ℝ).toNNReal * v)
        = ((c i) ^ 2).toNNReal * v + (∑ j ∈ s, (c j) ^ 2 : ℝ).toNNReal * v := by
      rw [Finset.sum_insert hi, Real.toNNReal_add (sq_nonneg _)
        (Finset.sum_nonneg (fun j _ => sq_nonneg _)), add_mul]
    rw [hfun, hvar]
    exact hsum

end StatLean.NonparametricStatistics
