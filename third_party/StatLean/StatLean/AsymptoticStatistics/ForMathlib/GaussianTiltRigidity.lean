module
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.TangentCone.Real

@[expose] public section

/-! # Rigidity from nonnegative Gaussian tilts -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics.ForMathlib.GaussianTiltRigidity

/-- A half-line of exact Gaussian exponential tilts determines the covariance,
including the degenerate `v=0` case.

Proof idea: establish right differentiability at zero of tilted first
moments, justify it by Gaussian exponential integrability, and split `v=0`.

Joint witness: any centered PSD bivariate Gaussian; PSD forces `c=0` when
`v=0`. -/
theorem covariance_eq_of_nonneg_gaussian_tilts
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (v s : ℝ≥0) (c : ℝ)
    (h_snd : π.map Prod.snd = gaussianReal 0 v)
    (h_tilts : ∀ a : ℝ, 0 ≤ a →
      (π.withDensity (fun q => ENNReal.ofReal
        (Real.exp (a * q.2 - (a ^ 2 / 2) * (v : ℝ))))).map Prod.fst =
        gaussianReal (a * c) s) :
    Integrable (fun q : ℝ × ℝ => q.1 * q.2) π ∧
      ∫ q : ℝ × ℝ, q.1 * q.2 ∂π = c := by
  have h_fst : π.map Prod.fst = gaussianReal 0 s := by
    simpa using h_tilts 0 le_rfl
  have hX_map : MemLp id 2 (π.map Prod.fst) := by
    rw [h_fst]
    exact ProbabilityTheory.memLp_id_gaussianReal 2
  have hY_map : MemLp id 2 (π.map Prod.snd) := by
    rw [h_snd]
    exact ProbabilityTheory.memLp_id_gaussianReal 2
  have hX : MemLp (fun q : ℝ × ℝ => q.1) 2 π := by
    simpa [Function.comp_def] using
      hX_map.comp_of_map measurable_fst.aemeasurable
  have hY : MemLp (fun q : ℝ × ℝ => q.2) 2 π := by
    simpa [Function.comp_def] using
      hY_map.comp_of_map measurable_snd.aemeasurable
  have hXY : Integrable (fun q : ℝ × ℝ => q.1 * q.2) π := by
    simpa only [Pi.mul_apply] using! hX.integrable_mul hY
  have h_exp_snd (t : ℝ) :
      Integrable (fun q : ℝ × ℝ => Real.exp (t * q.2)) π := by
    have h_map : Integrable (fun y : ℝ => Real.exp (t * y)) (π.map Prod.snd) := by
      rw [h_snd]
      exact ProbabilityTheory.integrable_exp_mul_gaussianReal t
    simpa [Function.comp_def] using
      h_map.comp_aemeasurable measurable_snd.aemeasurable
  let B : ℝ × ℝ → ℝ := fun q =>
    (|q.2| + (v : ℝ)) * Real.exp |q.2|
  have h_pow_two : Integrable
      (fun q : ℝ × ℝ => |q.2| ^ 2 *
        Real.exp (0 * q.2 + 2 * |q.2|)) π := by
    apply ProbabilityTheory.integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
      (X := fun q : ℝ × ℝ => q.2) (v := 0) (t := 3)
    · simpa using h_exp_snd 3
    · simpa using h_exp_snd (-3)
    · norm_num
    · norm_num
  have h_pow_zero : Integrable
      (fun q : ℝ × ℝ => |q.2| ^ 0 *
        Real.exp (0 * q.2 + 2 * |q.2|)) π := by
    apply ProbabilityTheory.integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
      (X := fun q : ℝ × ℝ => q.2) (v := 0) (t := 3)
    · simpa using h_exp_snd 3
    · simpa using h_exp_snd (-3)
    · norm_num
    · norm_num
  have h_B_sq : Integrable (fun q => B q ^ 2) π := by
    have h_majorant : Integrable (fun q : ℝ × ℝ =>
        2 * |q.2| ^ 2 * Real.exp (2 * |q.2|) +
          (2 * (v : ℝ) ^ 2) * Real.exp (2 * |q.2|)) π := by
      have h_two : Integrable
          (fun q : ℝ × ℝ => 2 *
            (|q.2| ^ 2 * Real.exp (0 * q.2 + 2 * |q.2|))) π :=
        h_pow_two.const_mul 2
      have h_zero : Integrable
          (fun q : ℝ × ℝ => (2 * (v : ℝ) ^ 2) *
            (|q.2| ^ 0 * Real.exp (0 * q.2 + 2 * |q.2|))) π :=
        h_pow_zero.const_mul (2 * (v : ℝ) ^ 2)
      simpa [mul_assoc] using! h_two.add h_zero
    refine h_majorant.mono' (by fun_prop) (Filter.Eventually.of_forall (fun q => ?_))
    rw [Real.norm_eq_abs, abs_sq]
    dsimp only [B]
    have hv : (0 : ℝ) ≤ (v : ℝ) := NNReal.coe_nonneg v
    have hsum : (|q.2| + (v : ℝ)) ^ 2 ≤
        2 * |q.2| ^ 2 + 2 * (v : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (|q.2| - (v : ℝ))]
    have hexp : (Real.exp |q.2|) ^ 2 = Real.exp (2 * |q.2|) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, hexp]
    calc
      (|q.2| + (v : ℝ)) ^ 2 * Real.exp (2 * |q.2|)
          ≤ (2 * |q.2| ^ 2 + 2 * (v : ℝ) ^ 2) *
              Real.exp (2 * |q.2|) :=
            mul_le_mul_of_nonneg_right hsum (Real.exp_nonneg _)
      _ = 2 * |q.2| ^ 2 * Real.exp (2 * |q.2|) +
            2 * (v : ℝ) ^ 2 * Real.exp (2 * |q.2|) := by ring
  have hB : MemLp B 2 π :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 h_B_sq
  have h_bound : Integrable (fun q : ℝ × ℝ => |q.1| * B q) π := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using! hX.norm.integrable_mul hB
  let F : ℝ → (ℝ × ℝ) → ℝ := fun a q =>
    q.1 * Real.exp (a * q.2 - (a ^ 2 / 2) * (v : ℝ))
  let F' : ℝ → (ℝ × ℝ) → ℝ := fun a q =>
    q.1 * (q.2 - a * (v : ℝ)) *
      Real.exp (a * q.2 - (a ^ 2 / 2) * (v : ℝ))
  have hF_meas : ∀ᶠ a in 𝓝 (0 : ℝ), AEStronglyMeasurable (F a) π :=
    Filter.Eventually.of_forall (fun _ => by fun_prop)
  have hF_int : Integrable (F 0) π := by
    simpa [F] using hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hF'_meas : AEStronglyMeasurable (F' 0) π := by fun_prop
  have hF'_bound : ∀ᵐ q ∂π, ∀ a ∈ Metric.ball (0 : ℝ) 1,
      ‖F' a q‖ ≤ |q.1| * B q := by
    refine Filter.Eventually.of_forall (fun q a ha => ?_)
    have ha_abs : |a| < 1 := by
      simpa [Real.dist_eq] using ha
    have hv : (0 : ℝ) ≤ (v : ℝ) := NNReal.coe_nonneg v
    have hlin : |q.2 - a * (v : ℝ)| ≤ |q.2| + (v : ℝ) := by
      calc
        |q.2 - a * (v : ℝ)| ≤ |q.2| + |a * (v : ℝ)| := abs_sub _ _
        _ = |q.2| + |a| * (v : ℝ) := by rw [abs_mul, abs_of_nonneg hv]
        _ ≤ |q.2| + (v : ℝ) := by
          simpa using add_le_add_right
            (mul_le_mul_of_nonneg_right ha_abs.le hv) |q.2|
    have hexponent :
        a * q.2 - (a ^ 2 / 2) * (v : ℝ) ≤ |q.2| := by
      calc
        a * q.2 - (a ^ 2 / 2) * (v : ℝ) ≤ a * q.2 := by
          exact sub_le_self _ (mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) hv)
        _ ≤ |a * q.2| := le_abs_self _
        _ = |a| * |q.2| := abs_mul _ _
        _ ≤ 1 * |q.2| :=
          mul_le_mul_of_nonneg_right ha_abs.le (abs_nonneg _)
        _ = |q.2| := one_mul _
    change
      |q.1 * (q.2 - a * (v : ℝ)) *
          Real.exp (a * q.2 - (a ^ 2 / 2) * (v : ℝ))| ≤
        |q.1| * ((|q.2| + (v : ℝ)) * Real.exp |q.2|)
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      |q.1| * |q.2 - a * (v : ℝ)| *
          Real.exp (a * q.2 - a ^ 2 / 2 * (v : ℝ))
          ≤ |q.1| * (|q.2| + (v : ℝ)) *
              Real.exp (a * q.2 - a ^ 2 / 2 * (v : ℝ)) := by
            gcongr
      _ ≤ |q.1| * (|q.2| + (v : ℝ)) * Real.exp |q.2| := by
            gcongr
      _ = |q.1| * ((|q.2| + (v : ℝ)) * Real.exp |q.2|) := by ring
  have hF'_diff : ∀ᵐ q ∂π, ∀ a ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (F · q) (F' a q) a := by
    refine Filter.Eventually.of_forall (fun q a _ => ?_)
    dsimp only [F, F']
    have harg : HasDerivAt
        (fun x : ℝ => x * q.2 - (x ^ 2 / 2) * (v : ℝ))
        (q.2 - a * (v : ℝ)) a := by
      convert! ((hasDerivAt_id a).mul_const q.2).sub
        ((((hasDerivAt_id a).pow 2).div_const 2).mul_const (v : ℝ)) using 1
      all_goals simp only [id_eq]
      all_goals ring
    convert! (hasDerivAt_const a q.1).mul harg.exp using 1
    all_goals ring
  obtain ⟨_, hF_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := π) (𝕜 := ℝ) (E := ℝ) (s := Metric.ball (0 : ℝ) 1)
      (x₀ := 0) (F := F) (F' := F') (bound := fun q => |q.1| * B q)
      (Metric.ball_mem_nhds _ zero_lt_one) hF_meas hF_int hF'_meas
      hF'_bound h_bound hF'_diff
  have h_integral_deriv : HasDerivAt
      (fun a => ∫ q, F a q ∂π) (∫ q, q.1 * q.2 ∂π) 0 := by
    simpa [F'] using hF_deriv
  have h_integral_eq (a : ℝ) (ha : 0 ≤ a) :
      (∫ q, F a q ∂π) = a * c := by
    let w : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal
      (Real.exp (a * q.2 - (a ^ 2 / 2) * (v : ℝ)))
    have hw_meas : Measurable w := by fun_prop
    have hw_top : ∀ᵐ q ∂π, w q < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    calc
      (∫ q, F a q ∂π) = ∫ q, q.1 ∂π.withDensity w := by
        rw [integral_withDensity_eq_integral_toReal_smul hw_meas hw_top]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
        dsimp only [F, w]
        rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
        ring
      _ = ∫ x, x ∂(π.withDensity w).map Prod.fst := by
        rw [integral_map (by fun_prop) (by fun_prop)]
      _ = ∫ x, x ∂gaussianReal (a * c) s := by
        rw [show (π.withDensity w).map Prod.fst = gaussianReal (a * c) s by
          simpa [w] using h_tilts a ha]
      _ = a * c := ProbabilityTheory.integral_id_gaussianReal
  have h_linear : HasDerivWithinAt (fun a : ℝ => a * c) c (Set.Ici 0) 0 := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const c).hasDerivWithinAt
  have h_integral_linear : HasDerivWithinAt
      (fun a => ∫ q, F a q ∂π) c (Set.Ici 0) 0 :=
    h_linear.congr_of_mem (fun a ha => h_integral_eq a ha) Set.self_mem_Ici
  refine ⟨hXY, ?_⟩
  exact (uniqueDiffWithinAt_Ici 0).eq_deriv (Set.Ici 0)
    h_integral_deriv.hasDerivWithinAt h_integral_linear

end AsymptoticStatistics.ForMathlib.GaussianTiltRigidity
