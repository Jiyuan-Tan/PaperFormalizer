module
public import StatLean.ConcentrationInequalities.SubGaussian.Defs
public import StatLean.ConcentrationInequalities.Orlicz.Basic
public import StatLean.ConcentrationInequalities.Orlicz.Generators
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Layercake

@[expose] public section

/-!
# From Gaussian tails to the ψ₂ norm (B3)

The layer-cake engine: Gaussian-type tails
$\mathbb{P}(|X| \ge t) \le 2e^{-t^2/K_1^2}$ imply the ψ₂ condition at scale
$K = \sqrt{3}\,K_1$, i.e.
$$ \|X\|_{\psi_2} \le \sqrt{3}\, K_1, $$
assembled into the reverse bridge **B3**: a Mathlib `HasSubgaussianMGF X σ2 μ`
(in particular the project carrier `IsSubGaussian`) gives
$\|X\|_{\psi_2} \le \sqrt{6\,\sigma^2}$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.6.1 ((i)⇒(iii)) and the (iv)⇒(i)
composition; Proposition 2.6.6.

**Proof formalization notes.** Constants (all frozen as `NNReal.sqrt`
numerals): `K₃ = √3·K₁` for (i)⇒(iii), and `C' = √6` for B3 (formula:
Mathlib tails give `K₁ = √(2σ2)`, then `√3·√(2σ2) = √(6σ2)`). **Documented
deviation from the book route:** (i)⇒(iii) is proved *directly* by the
weighted layer cake (`MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`
with the FTC identity `exp(u²/K²) − 1 = ∫₀ᵘ (2t/K²)e^{t²/K²} dt` and the
improper integral `∫_{(0,∞)} t·e^{−ct²} dt = 1/(2c)` via
`integral_Ioi_of_hasDerivAt_of_tendsto`), avoiding the book's (i)⇒(ii)⇒(iii)
chain and its `Γ(x) ≤ 3x^x` brick, which is absent from Mathlib. B3 takes
no measurability hypothesis beyond the frozen signature:
`HasSubgaussianMGF.aemeasurable` supplies it; tails come from
`HasSubgaussianMGF.measure_ge_le` on `X` and `−X` (via `.neg`). Named-sorry
fallback of this work item: `integral_Ioi_self_mul_exp_neg_mul_sq` (isolated
improper-integral computation); the layer-cake assembly and B3 close modulo
it.

**Bibliographic comments.** The layer-cake (distribution-integral) identity
is classical (see Lieb–Loss, *Analysis*, 2nd ed., §1.13); the tails-to-Orlicz
direction of the equivalence traces to Buldygin–Kozachenko (1980).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Antiderivative brick for the Gaussian moment: the map
`s ↦ −(2c)⁻¹·e^{−c s²}` has derivative `t·e^{−c t²}`. -/
private lemma hasDerivAt_gaussianAntideriv {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => -(2 * c)⁻¹ * Real.exp (-c * s ^ 2))
      (t * Real.exp (-c * t ^ 2)) t := by
  have h2c : (2 : ℝ) * c ≠ 0 := mul_ne_zero two_ne_zero hc
  have h1 : HasDerivAt (fun s : ℝ => -c * s ^ 2) (-c * (2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul (-c)
  have h2 := (h1.exp).const_mul (-(2 * c)⁻¹)
  convert! h2 using 1
  field_simp

/-- Improper integral `∫_{(0,∞)} t·exp(−c·t²) dt = 1/(2c)` (antiderivative
`−e^{−ct²}/(2c)` + `integral_Ioi_of_hasDerivAt_of_tendsto`); designated
named-sorry fallback of the tail-to-norm work item. -/
lemma integral_Ioi_self_mul_exp_neg_mul_sq {c : ℝ}
    -- LEAN-ONLY: positive decay rate; integral diverges for c ≤ 0
    (hc : 0 < c) :
    ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-c * t ^ 2) = 1 / (2 * c) := by
  have htend : Filter.Tendsto (fun s : ℝ => -(2 * c)⁻¹ * Real.exp (-c * s ^ 2))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : ℝ => -c * s ^ 2) Filter.atTop Filter.atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by linarith) (Filter.tendsto_pow_atTop two_ne_zero)
    have h2 : Filter.Tendsto (fun s : ℝ => Real.exp (-c * s ^ 2)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul (-(2 * c)⁻¹)
  have key := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0 : ℝ))
    (g := fun s : ℝ => -(2 * c)⁻¹ * Real.exp (-c * s ^ 2))
    (fun x _ => hasDerivAt_gaussianAntideriv hc.ne' x)
    (fun x hx => mul_nonneg (le_of_lt (Set.mem_Ioi.mp hx)) (Real.exp_pos _).le)
    htend
  rw [key]
  simp [one_div]

/-- FTC identity `∫₀ᵘ (2t/K²)·exp(t²/K²) dt = ψ₂(u/K)` feeding the weighted
layer cake `lintegral_comp_eq_lintegral_meas_le_mul`. -/
lemma intervalIntegral_psiTwo_deriv {K : ℝ}
    -- LEAN-ONLY: positive scale; division by K² in the integrand
    (hK : 0 < K)
    {u : ℝ}
    -- LEAN-ONLY: nonnegative upper limit; ψ₂ is evaluated at |X|/K ≥ 0
    (hu : 0 ≤ u) :
    ∫ t in (0 : ℝ)..u, 2 * t / K ^ 2 * Real.exp (t ^ 2 / K ^ 2)
      = psiTwo (u / K) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) u,
      HasDerivAt (fun s => Real.exp (s ^ 2 / K ^ 2))
        (2 * t / K ^ 2 * Real.exp (t ^ 2 / K ^ 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / K ^ 2) (2 * t / K ^ 2) t := by
      simpa using (hasDerivAt_pow 2 t).div_const (K ^ 2)
    have h2 := h1.exp
    rw [mul_comm (2 * t / K ^ 2) (Real.exp (t ^ 2 / K ^ 2))]
    exact h2
  have hII : IntervalIntegrable
      (fun t => 2 * t / K ^ 2 * Real.exp (t ^ 2 / K ^ 2)) volume 0 u :=
    Continuous.intervalIntegrable (by fun_prop) 0 u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hII, psiTwo_apply, div_pow]
  simp

/-- Layer-cake core (HDP Prop 2.6.1 (i)⇒(iii), `K₃ = √3·K₁`; direct route,
see module docstring): Gaussian tails at scale `K₁` verify the Luxemburg
condition at any scale `K ≥ √3·K₁`. -/
theorem lintegral_psiTwo_le_one_of_tail_le {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; layer-cake regularity
    (hX : AEMeasurable X μ)
    {K₁ : ℝ≥0}
    -- USER-INPUT: positive tail scale; HDP Prop 2.6.1(i)
    (hK₁ : 0 < K₁)
    {K : ℝ≥0}
    -- LEAN-ONLY: target scale dominates √3·K₁; the provable constant, stated
    -- with slack so downstream numerals stay NNReal.sqrt expressions
    (hK : Real.sqrt 3 * (K₁ : ℝ) ≤ (K : ℝ))
    -- USER-INPUT: Gaussian-type two-sided tails at scale K₁; HDP Prop 2.6.1(i)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2))) :
    ∫⁻ ω, ENNReal.ofReal (psiTwo (|X ω| / (K : ℝ))) ∂μ ≤ 1 := by
  -- positivity of the scales
  have hK₁R : (0 : ℝ) < (K₁ : ℝ) := by exact_mod_cast hK₁
  have hsqrt3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hKR : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le (mul_pos hsqrt3 hK₁R) hK
  have hK1sq : (0 : ℝ) < (K₁ : ℝ) ^ 2 := pow_pos hK₁R 2
  have hKsq : (0 : ℝ) < (K : ℝ) ^ 2 := pow_pos hKR 2
  have hK1ne : (K₁ : ℝ) ^ 2 ≠ 0 := hK1sq.ne'
  have hKne : (K : ℝ) ^ 2 ≠ 0 := hKsq.ne'
  -- 3·K₁² ≤ K²
  have key : 3 * (K₁ : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 := by
    have h0 : 0 ≤ Real.sqrt 3 * (K₁ : ℝ) := by positivity
    have hmul := mul_self_le_mul_self h0 hK
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    nlinarith [hmul, h3]
  have hK1K : (K₁ : ℝ) < (K : ℝ) := by
    have h31 : (1 : ℝ) < Real.sqrt 3 := by
      nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    nlinarith [h31, hK, hK₁R]
  have hsqlt : (K₁ : ℝ) ^ 2 < (K : ℝ) ^ 2 := by nlinarith [hK1K, hK₁R, hKR]
  -- decay rate
  set c : ℝ := 1 / (K₁ : ℝ) ^ 2 - 1 / (K : ℝ) ^ 2 with hc_def
  have hc : 0 < c := by
    rw [hc_def]; exact sub_pos.mpr (one_div_lt_one_div_of_lt hK1sq hsqlt)
  -- pointwise algebra: the integrand collapses to (4/K²)·t·e^{−c t²}
  have hFeq : ∀ t : ℝ,
      2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2)
          * (2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2))
        = 4 / (K : ℝ) ^ 2 * (t * Real.exp (-c * t ^ 2)) := by
    intro t
    have hexp : Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2) * Real.exp (t ^ 2 / (K : ℝ) ^ 2)
        = Real.exp (-c * t ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      rw [hc_def]; field_simp; ring
    calc 2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2)
            * (2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2))
        = 4 / (K : ℝ) ^ 2 * t
            * (Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2) * Real.exp (t ^ 2 / (K : ℝ) ^ 2)) := by ring
      _ = 4 / (K : ℝ) ^ 2 * t * Real.exp (-c * t ^ 2) := by rw [hexp]
      _ = 4 / (K : ℝ) ^ 2 * (t * Real.exp (-c * t ^ 2)) := by ring
  -- integrability of the reduced integrand on (0,∞)
  have htend : Filter.Tendsto (fun s : ℝ => -(2 * c)⁻¹ * Real.exp (-c * s ^ 2))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : ℝ => -c * s ^ 2) Filter.atTop Filter.atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by linarith) (Filter.tendsto_pow_atTop two_ne_zero)
    have h2 : Filter.Tendsto (fun s : ℝ => Real.exp (-c * s ^ 2)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul (-(2 * c)⁻¹)
  have hbase : IntegrableOn (fun t => t * Real.exp (-c * t ^ 2)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' (a := (0 : ℝ))
      (g := fun s : ℝ => -(2 * c)⁻¹ * Real.exp (-c * s ^ 2))
      (fun x _ => hasDerivAt_gaussianAntideriv hc.ne' x)
      (fun x hx => mul_nonneg (le_of_lt (Set.mem_Ioi.mp hx)) (Real.exp_pos _).le)
      htend
  have hFint : IntegrableOn
      (fun t => 2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2)
        * (2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2))) (Set.Ioi (0 : ℝ)) := by
    refine (hbase.const_mul (4 / (K : ℝ) ^ 2)).congr ?_
    filter_upwards with t
    exact (hFeq t).symm
  have hFnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun t => 2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2)
        * (2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h0t : (0 : ℝ) ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
    exact mul_nonneg (by positivity)
      (mul_nonneg (div_nonneg (by linarith) (sq_nonneg _)) (Real.exp_pos _).le)
  -- value of the real integral is ≤ 1 (equality at K = √3·K₁)
  have hFval_le : (∫ t in Set.Ioi (0 : ℝ),
      2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2)
        * (2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2))) ≤ 1 := by
    have hval : (∫ t in Set.Ioi (0 : ℝ),
        2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2)
          * (2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2)))
        = 4 / (K : ℝ) ^ 2 * (1 / (2 * c)) := by
      simp_rw [hFeq]
      rw [integral_const_mul, integral_Ioi_self_mul_exp_neg_mul_sq hc]
    rw [hval, div_mul_div_comm, mul_one,
      div_le_one (mul_pos hKsq (by linarith : (0 : ℝ) < 2 * c))]
    rw [hc_def]
    have hrw : (K : ℝ) ^ 2 * (2 * (1 / (K₁ : ℝ) ^ 2 - 1 / (K : ℝ) ^ 2))
        = 2 * ((K : ℝ) ^ 2 / (K₁ : ℝ) ^ 2) - 2 := by field_simp
    rw [hrw]
    have h3le : (3 : ℝ) ≤ (K : ℝ) ^ 2 / (K₁ : ℝ) ^ 2 := by
      rw [le_div_iff₀ hK1sq]; linarith [key]
    linarith
  -- layer-cake hypotheses
  have f_nn : 0 ≤ᵐ[μ] fun ω => |X ω| := ae_of_all μ fun ω => abs_nonneg _
  have f_mble : AEMeasurable (fun ω => |X ω|) μ := hX.abs
  have g_intble : ∀ t > (0 : ℝ), IntervalIntegrable
      (fun s => 2 * s / (K : ℝ) ^ 2 * Real.exp (s ^ 2 / (K : ℝ) ^ 2)) volume 0 t :=
    fun t _ => Continuous.intervalIntegrable (by fun_prop) 0 t
  have g_nn : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      0 ≤ 2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h0t : (0 : ℝ) ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
    exact mul_nonneg (div_nonneg (by linarith) (sq_nonneg _)) (Real.exp_pos _).le
  have hlc := MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn
  calc ∫⁻ ω, ENNReal.ofReal (psiTwo (|X ω| / (K : ℝ))) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..|X ω|,
          2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2)) ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [intervalIntegral_psiTwo_deriv hKR (abs_nonneg (X ω))]
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | t ≤ |X ω|}
          * ENNReal.ofReal (2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2)) := hlc
    _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2))
          * ENNReal.ofReal (2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_le_mul_left (htail t (le_of_lt (Set.mem_Ioi.mp ht))) _
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2)
            * (2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2))) := by
        refine lintegral_congr fun t => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ),
          2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2)
            * (2 * t / (K : ℝ) ^ 2 * Real.exp (t ^ 2 / (K : ℝ) ^ 2))) :=
        (ofReal_integral_eq_lintegral_ofReal hFint hFnn).symm
    _ ≤ 1 := by rw [ENNReal.ofReal_le_one]; exact hFval_le

/-- HDP Prop 2.6.1 (i)⇒(iii) packaged for the norm:
`‖X‖_{ψ₂} ≤ √3·K₁` from Gaussian tails at scale `K₁`. -/
theorem subGaussianNorm_le_of_tail_le {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; layer-cake regularity
    (hX : AEMeasurable X μ)
    {K₁ : ℝ≥0}
    -- USER-INPUT: positive tail scale; HDP Prop 2.6.1(i)
    (hK₁ : 0 < K₁)
    -- USER-INPUT: Gaussian-type two-sided tails at scale K₁; HDP Prop 2.6.1(i)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2))) :
    subGaussianNorm X μ ≤ (NNReal.sqrt 3 * K₁ : ℝ≥0∞) := by
  have hK0 : (0 : ℝ≥0) < NNReal.sqrt 3 * K₁ :=
    mul_pos (NNReal.sqrt_pos.mpr (by norm_num)) hK₁
  have hcoe : ((NNReal.sqrt 3 * K₁ : ℝ≥0) : ℝ) = Real.sqrt 3 * (K₁ : ℝ) := by
    rw [NNReal.coe_mul, Real.coe_sqrt]; norm_num
  have hmem : (NNReal.sqrt 3 * K₁) ∈ orliczSet psiTwo X μ :=
    ⟨hK0, lintegral_psiTwo_le_one_of_tail_le hX hK₁ (le_of_eq hcoe.symm) htail⟩
  calc subGaussianNorm X μ = orliczNorm psiTwo X μ := subGaussianNorm_def X μ
    _ ≤ ((NNReal.sqrt 3 * K₁ : ℝ≥0) : ℝ≥0∞) := orliczNorm_le_of_mem hmem
    _ = (NNReal.sqrt 3 * K₁ : ℝ≥0∞) := by rw [ENNReal.coe_mul]

/-- B3 raw form (frozen constant `C' = √6`; formula `√6 = √3·√2` from
Mathlib tails `K₁ = √(2σ2)` composed with `K₃ = √3·K₁`): the Mathlib MGF
predicate bounds the ψ₂ norm. Measurability and tails are supplied by the
predicate itself (`.aemeasurable`, `.measure_ge_le` + `.neg`). -/
theorem subGaussianNorm_le_of_hasSubgaussianMGF {X : Ω → ℝ} {μ : Measure Ω}
    {σ2 : ℝ≥0}
    -- USER-INPUT: sub-Gaussian MGF bound with variance proxy σ2; HDP Prop 2.6.1(iv)
    (h : ProbabilityTheory.HasSubgaussianMGF X σ2 μ) :
    subGaussianNorm X μ ≤ (NNReal.sqrt (6 * σ2) : ℝ≥0∞) := by
  by_cases hσ : σ2 = 0
  · -- degenerate proxy: X = 0 a.e., so the ψ₂ norm is 0
    have hae : X =ᵐ[μ] 0 := by
      rw [hσ] at h; exact h.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hae' : X =ᵐ[μ] fun _ : Ω => (0 : ℝ) := hae
    have hz : orliczNorm psiTwo (fun _ : Ω => (0 : ℝ)) μ = 0 :=
      orliczNorm_zero psiTwo_zero.le μ
    calc subGaussianNorm X μ = orliczNorm psiTwo X μ := subGaussianNorm_def X μ
      _ = orliczNorm psiTwo (fun _ => (0 : ℝ)) μ := orliczNorm_congr_ae hae'
      _ = 0 := hz
      _ ≤ (NNReal.sqrt (6 * σ2) : ℝ≥0∞) := zero_le
  · -- nondegenerate: Chernoff tails at K₁ = √(2σ2) feed the layer-cake core
    have hσpos : (0 : ℝ≥0) < σ2 := lt_of_le_of_ne (zero_le) (Ne.symm hσ)
    have hfin : IsFiniteMeasure μ := by
      have hi := h.integrable_exp_mul 0
      simp only [zero_mul, Real.exp_zero] at hi
      exact (integrable_const_iff.mp hi).resolve_left one_ne_zero
    have hK₁ : (0 : ℝ≥0) < NNReal.sqrt (2 * σ2) :=
      NNReal.sqrt_pos.mpr (mul_pos two_pos hσpos)
    have hexp2 : ((NNReal.sqrt (2 * σ2) : ℝ)) ^ 2 = 2 * (σ2 : ℝ) := by
      rw [← NNReal.coe_pow, NNReal.sq_sqrt]; push_cast; ring
    have htail : ∀ t : ℝ, 0 ≤ t →
        μ {ω | t ≤ |X ω|}
          ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (NNReal.sqrt (2 * σ2) : ℝ) ^ 2)) := by
      intro t ht
      have hXt : μ {ω | t ≤ X ω}
          ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (σ2 : ℝ)))) := by
        have hb := h.measure_ge_le ht
        calc μ {ω | t ≤ X ω}
            = ENNReal.ofReal ((μ {ω | t ≤ X ω}).toReal) :=
              (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
          _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (σ2 : ℝ)))) :=
              ENNReal.ofReal_le_ofReal hb
      have hnXt : μ {ω | t ≤ -X ω}
          ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (σ2 : ℝ)))) := by
        have hb := (h.neg).measure_ge_le ht
        calc μ {ω | t ≤ -X ω}
            = ENNReal.ofReal ((μ {ω | t ≤ -X ω}).toReal) :=
              (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
          _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (σ2 : ℝ)))) :=
              ENNReal.ofReal_le_ofReal hb
      have hsub : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
        intro ω hω
        have hω' : t ≤ |X ω| := hω
        rcases le_abs.mp hω' with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
      calc μ {ω | t ≤ |X ω|}
          ≤ μ ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) := measure_mono hsub
        _ ≤ μ {ω | t ≤ X ω} + μ {ω | t ≤ -X ω} := measure_union_le _ _
        _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (σ2 : ℝ))))
              + ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (σ2 : ℝ)))) := add_le_add hXt hnXt
        _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (NNReal.sqrt (2 * σ2) : ℝ) ^ 2)) := by
            rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
            congr 1
            rw [hexp2]; ring
    have hbound := subGaussianNorm_le_of_tail_le h.aemeasurable hK₁ htail
    have hcoe : (NNReal.sqrt 3 * NNReal.sqrt (2 * σ2) : ℝ≥0) = NNReal.sqrt (6 * σ2) := by
      rw [← NNReal.sqrt_mul]; congr 1; ring
    rw [← ENNReal.coe_mul, hcoe] at hbound
    exact hbound

/-- B3 project-carrier (centered) form: an `IsSubGaussian` variable has
centered ψ₂ norm at most `√(6σ2)` (chaining's increments consume the raw
form; this is the general-mean corollary). -/
theorem subGaussianNorm_centered_le_of_isSubGaussian {X : Ω → ℝ} {μ : Measure Ω}
    {σ2 : ℝ≥0}
    -- USER-INPUT: X sub-Gaussian with variance proxy σ2; HDP Prop 2.6.6 / Def 2.6.4
    (h : IsSubGaussian X σ2 μ) :
    subGaussianNorm (fun ω => X ω - ∫ x, X x ∂μ) μ
      ≤ (NNReal.sqrt (6 * σ2) : ℝ≥0∞) :=
  subGaussianNorm_le_of_hasSubgaussianMGF (isSubGaussian_iff.mp h)

/-- **B3** (contract form; HDP Proposition 2.6.1 (iv)⇒(iii) with frozen
constant `C' = √6`): a mean-zero `IsSubGaussian` variable has
`‖X‖_{ψ₂} ≤ √(6σ2)`. -/
theorem subGaussianNorm_le_of_isSubGaussian
    -- LEAN-ONLY: probability measure; per the frozen B3 bridge signature
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; per the frozen B3 bridge signature
    (hX : AEMeasurable X μ)
    {σ2 : ℝ≥0}
    -- USER-INPUT: X sub-Gaussian with variance proxy σ2; HDP Prop 2.6.6 / Def 2.6.4
    (h : IsSubGaussian X σ2 μ)
    -- USER-INPUT: mean zero (centered = raw); HDP §2.6 mean-zero convention
    (hmean : ∫ x, X x ∂μ = 0) :
    subGaussianNorm X μ ≤ (NNReal.sqrt (6 * σ2) : ℝ≥0∞) :=
  subGaussianNorm_le_of_hasSubgaussianMGF
    (by simpa only [hmean, sub_zero] using isSubGaussian_iff.mp h)

end StatLean.ConcentrationInequalities
