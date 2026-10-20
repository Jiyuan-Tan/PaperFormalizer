module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# A scale-free square-root logarithm integral

This file isolates the real-analysis estimate used when a polynomial entropy
bound depends only on the relative scale `δ / ε`. The resulting integral is
linear in `δ`, with a constant independent of `δ`.
-/

open scoped ENNReal

namespace AsymptoticStatistics.ForMathlib

/-- The scale-free ratio integral `∫₀^δ √(δ/ε) dε = 2δ`. -/
private lemma lintegral_sqrt_ratio {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ ε in Set.Ioc (0 : ℝ) δ, ENNReal.ofReal (Real.sqrt (δ / ε)) ∂MeasureTheory.volume
      = ENNReal.ofReal (2 * δ) := by
  have hfun : Set.EqOn (fun ε : ℝ => Real.sqrt (δ / ε))
      (fun ε => Real.sqrt δ * ε ^ (-(1 / 2) : ℝ)) (Set.Ioc 0 δ) := by
    intro ε hε
    have hε0 : 0 < ε := hε.1
    change Real.sqrt (δ / ε) = Real.sqrt δ * ε ^ (-(1 / 2) : ℝ)
    rw [Real.rpow_neg hε0.le, ← Real.sqrt_eq_rpow, Real.sqrt_div hδ.le, div_eq_mul_inv]
  have hint_pow : MeasureTheory.IntegrableOn (fun ε : ℝ => ε ^ (-(1 / 2) : ℝ))
      (Set.Ioc 0 δ) MeasureTheory.volume :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).1
  have hbase : MeasureTheory.IntegrableOn
      (fun ε : ℝ => Real.sqrt δ * ε ^ (-(1 / 2) : ℝ))
      (Set.Ioc 0 δ) MeasureTheory.volume := hint_pow.const_mul (Real.sqrt δ)
  have hint : MeasureTheory.IntegrableOn (fun ε : ℝ => Real.sqrt (δ / ε))
      (Set.Ioc 0 δ) MeasureTheory.volume := hbase.congr_fun hfun.symm measurableSet_Ioc
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 δ)]
      (fun ε => Real.sqrt (δ / ε)) :=
    Filter.Eventually.of_forall (fun ε => Real.sqrt_nonneg _)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hfun,
    MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le hδ.le,
    integral_rpow (Or.inl (by norm_num))]
  have h0 : (0 : ℝ) ^ (-(1 / 2) + 1 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  have hd : δ ^ (-(1 / 2) + 1 : ℝ) = Real.sqrt δ := by
    rw [show (-(1 / 2) + 1 : ℝ) = 1 / (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  rw [h0, hd, sub_zero, show (-(1 / 2) + 1 : ℝ) = 1 / 2 by norm_num,
    show Real.sqrt δ * (Real.sqrt δ / (1 / 2)) = 2 * (Real.sqrt δ * Real.sqrt δ) from by
      ring,
    Real.mul_self_sqrt hδ.le]

/-- A polynomial entropy weight at relative scale has a scale-free integral bound.

For `C > 0` and `p : ℕ`, there is a positive constant `Cp`, independent of
`δ`, such that

` ∫₀^δ √(log(1 + (Cδ/ε)^p)) dε ≤ Cp · δ `

for every `δ > 0`. This is the analytic estimate behind the cancellation of
the localization radius in finite-dimensional relative entropy integrals. -/
theorem sqrt_log_pow_ratio_lintegral_le (C : ℝ) (hC : 0 < C) (p : ℕ) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ δ : ℝ, 0 < δ →
      ∫⁻ ε in Set.Ioc (0 : ℝ) δ,
          ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * δ / ε) ^ p))) ∂MeasureTheory.volume
        ≤ ENNReal.ofReal (Cp * δ) := by
  set A : ℝ := Real.log 2 + p * |Real.log C| + p with hAdef
  have hA_pos : 0 < A := by
    have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : 0 ≤ (p : ℝ) * |Real.log C| := by positivity
    rw [hAdef]
    positivity
  set B : ℝ := Real.sqrt A with hBdef
  have hB_pos : 0 < B := Real.sqrt_pos.mpr hA_pos
  have hB_nn : 0 ≤ B := hB_pos.le
  refine ⟨2 * B, by positivity, fun δ hδ => ?_⟩
  have hpoint : ∀ ε ∈ Set.Ioc (0 : ℝ) δ,
      Real.sqrt (Real.log (1 + (C * δ / ε) ^ p)) ≤ B * Real.sqrt (δ / ε) := by
    intro ε hε
    obtain ⟨hε0, hεδ⟩ := hε
    set y : ℝ := δ / ε with hy
    have hy1 : 1 ≤ y := by
      rw [hy, le_div_iff₀ hε0]
      linarith
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    have hCδε : C * δ / ε = C * y := by rw [hy]; ring
    rw [hCδε]
    have hlogy_nn : 0 ≤ Real.log y := Real.log_nonneg hy1
    have hlogy_le : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
    have hlog_le : Real.log (1 + (C * y) ^ p) ≤ A * y := by
      have hl2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hl2 : Real.log 2 ≤ Real.log 2 * y := by nlinarith [hl2_pos, hy1]
      by_cases hge : 1 ≤ (C * y) ^ p
      · have hCyp_pos : 0 < (C * y) ^ p := by positivity
        have ha : (0 : ℝ) ≤ (p : ℝ) * |Real.log C| :=
          mul_nonneg (Nat.cast_nonneg p) (abs_nonneg _)
        have hpc : (p : ℝ) * |Real.log C| ≤ (p : ℝ) * |Real.log C| * y := by
          nlinarith [ha, hy1]
        have hply : (p : ℝ) * Real.log y ≤ (p : ℝ) * y :=
          mul_le_mul_of_nonneg_left hlogy_le (Nat.cast_nonneg p)
        calc Real.log (1 + (C * y) ^ p)
            ≤ Real.log (2 * (C * y) ^ p) := Real.log_le_log (by positivity) (by linarith)
          _ = Real.log 2 + p * Real.log (C * y) := by
              rw [Real.log_mul two_ne_zero hCyp_pos.ne', Real.log_pow]
          _ = Real.log 2 + p * (Real.log C + Real.log y) := by
              rw [Real.log_mul hC.ne' hy0.ne']
          _ ≤ Real.log 2 + p * (|Real.log C| + Real.log y) := by
              gcongr
              exact le_abs_self _
          _ = Real.log 2 + p * |Real.log C| + p * Real.log y := by ring
          _ ≤ Real.log 2 * y + p * |Real.log C| * y + p * y := by linarith
          _ = A * y := by rw [hAdef]; ring
      · have hlt : (C * y) ^ p < 1 := not_le.mp hge
        have hCyp_nn : (0 : ℝ) ≤ (C * y) ^ p := by positivity
        calc Real.log (1 + (C * y) ^ p)
            ≤ Real.log 2 := Real.log_le_log (by positivity) (by linarith)
          _ ≤ Real.log 2 * y := hl2
          _ ≤ A * y := by
              rw [hAdef]
              nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) * |Real.log C|) hy0.le,
                mul_nonneg (Nat.cast_nonneg p) hy0.le]
    calc Real.sqrt (Real.log (1 + (C * y) ^ p))
        ≤ Real.sqrt (A * y) := Real.sqrt_le_sqrt hlog_le
      _ = Real.sqrt A * Real.sqrt y := Real.sqrt_mul hA_pos.le y
      _ = B * Real.sqrt y := by rw [hBdef]
  calc ∫⁻ ε in Set.Ioc (0 : ℝ) δ,
        ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * δ / ε) ^ p))) ∂MeasureTheory.volume
      ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) δ,
          ENNReal.ofReal (B * Real.sqrt (δ / ε)) ∂MeasureTheory.volume :=
        MeasureTheory.setLIntegral_mono_ae' measurableSet_Ioc
          (Filter.Eventually.of_forall fun ε hε => ENNReal.ofReal_le_ofReal (hpoint ε hε))
    _ = ∫⁻ ε in Set.Ioc (0 : ℝ) δ,
          ENNReal.ofReal B * ENNReal.ofReal (Real.sqrt (δ / ε)) ∂MeasureTheory.volume :=
        MeasureTheory.lintegral_congr fun ε => ENNReal.ofReal_mul hB_nn
    _ = ENNReal.ofReal B * ∫⁻ ε in Set.Ioc (0 : ℝ) δ,
          ENNReal.ofReal (Real.sqrt (δ / ε)) ∂MeasureTheory.volume :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal B * ENNReal.ofReal (2 * δ) := by rw [lintegral_sqrt_ratio hδ]
    _ = ENNReal.ofReal (2 * B * δ) := by
        rw [← ENNReal.ofReal_mul hB_nn]
        congr 1
        ring

end AsymptoticStatistics.ForMathlib
