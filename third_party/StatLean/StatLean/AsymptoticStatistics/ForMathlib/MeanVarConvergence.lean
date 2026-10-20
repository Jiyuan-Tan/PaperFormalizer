module
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-!
Convergence in probability from mean + variance control.

Standalone probability lemma used in Step 4 of Theorem 7.2: if `E[Y_n] → c` and
`Var[Y_n] → 0`, then `Y_n → c` in probability.

Theorem-agnostic; lives outside any chapter directory.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics

/-- If `E[Y_n] → c` and `Var[Y_n] → 0`, then `Y_n → c` in probability. -/
theorem tendstoInMeasure_of_tendsto_mean_of_tendsto_variance
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {Y : ℕ → Ω → ℝ} {c : ℝ}
    (hmem : ∀ n, MemLp (Y n) 2 P)
    (h_mean : Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop (𝓝 c))
    (h_var : Tendsto (fun n => variance (Y n) P) atTop (𝓝 0)) :
    TendstoInMeasure P Y atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hε_eq : ε = δ + δ := by simp [hδdef]
  -- Eventually the bias `|E[Y n] − c|` is strictly below `δ`.
  have h_bias : ∀ᶠ n in atTop, |(∫ ω, Y n ω ∂P) - c| < δ := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h_mean) δ hδ
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rwa [Real.dist_eq] at this
  -- Pointwise: `|Y n ω − c| ≥ ε ⇒ |Y n ω − E[Y n]| ≥ δ` (whenever bias `< δ`).
  have h_subset :
      ∀ᶠ n in atTop,
        P {ω | ε ≤ ‖Y n ω - c‖} ≤ P {ω | δ ≤ |Y n ω - ∫ a, Y n a ∂P|} := by
    filter_upwards [h_bias] with n hbias
    refine measure_mono ?_
    intro ω hω
    rw [Set.mem_setOf_eq, Real.norm_eq_abs] at hω
    rw [Set.mem_setOf_eq]
    have hsplit : Y n ω - c = (Y n ω - ∫ a, Y n a ∂P) + ((∫ a, Y n a ∂P) - c) := by ring
    have htri : |Y n ω - c| ≤ |Y n ω - ∫ a, Y n a ∂P| + |(∫ a, Y n a ∂P) - c| := by
      rw [hsplit]; exact abs_add_le _ _
    linarith
  -- Chebyshev controls the inner deviation set by `Var[Y n] / δ²`.
  have h_cheby :
      ∀ᶠ n in atTop,
        P {ω | ε ≤ ‖Y n ω - c‖} ≤ ENNReal.ofReal (variance (Y n) P / δ ^ 2) := by
    filter_upwards [h_subset] with n hn
    exact hn.trans (meas_ge_le_variance_div_sq (hmem n) hδ)
  -- The Chebyshev bound tends to `0`.
  have h_bound :
      Tendsto (fun n => ENNReal.ofReal (variance (Y n) P / δ ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => variance (Y n) P / δ ^ 2) atTop (𝓝 (0 / δ ^ 2)) :=
      h_var.div_const _
    rw [zero_div] at h1
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    simpa using! h2
  -- Squeeze.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_bound
    (Eventually.of_forall (fun _ => zero_le)) h_cheby

/-- A constant sequence trivially converges in probability to its value. -/
lemma tendstoInMeasure_const
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} (c : ℝ) :
    TendstoInMeasure P (fun _ : ℕ => fun _ : Ω => c) atTop (fun _ : Ω => c) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have h_empty : {ω : Ω | ε ≤ ‖(c : ℝ) - c‖} = ∅ := by
    ext ω
    simp [show ¬ (ε ≤ 0) from not_le.mpr hε]
  simp_rw [h_empty, measure_empty]
  exact tendsto_const_nhds

/-- Scaling a real-valued `TendstoInMeasure` sequence by a constant preserves the limit. -/
lemma tendstoInMeasure_const_mul
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} {a : ℝ} (c : ℝ)
    (hY : TendstoInMeasure P Y atTop (fun _ => a)) :
    TendstoInMeasure P (fun n ω => c * Y n ω) atTop (fun _ => c * a) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_mul]
    exact tendstoInMeasure_const 0
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have h_abs_c_pos : 0 < |c| := abs_pos.mpr hc
  have h_ratio_pos : 0 < ε / |c| := div_pos hε h_abs_c_pos
  have h_bd := tendstoInMeasure_iff_norm.mp hY (ε / |c|) h_ratio_pos
  have h_eq : ∀ n : ℕ,
      {ω | ε ≤ ‖c * Y n ω - c * a‖}
        = {ω | ε / |c| ≤ ‖Y n ω - a‖} := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
    rw [show c * Y n ω - c * a = c * (Y n ω - a) from by ring, abs_mul]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [div_le_iff₀ h_abs_c_pos]; linarith
    · calc ε = (ε / |c|) * |c| := by rw [div_mul_cancel₀ _ (ne_of_gt h_abs_c_pos)]
        _ ≤ |Y n ω - a| * |c| := mul_le_mul_of_nonneg_right h h_abs_c_pos.le
        _ = |c| * |Y n ω - a| := by ring
  simp_rw [h_eq]
  exact h_bd

/-- Convergence in probability of real-valued sequences is preserved under addition. -/
lemma tendstoInMeasure_add
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Y Z : ℕ → Ω → ℝ} {a b : ℝ}
    (hY : TendstoInMeasure P Y atTop (fun _ => a))
    (hZ : TendstoInMeasure P Z atTop (fun _ => b)) :
    TendstoInMeasure P (fun n ω => Y n ω + Z n ω) atTop (fun _ => a + b) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  set δ : ℝ := ε / 2 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hε_le : ε ≤ δ + δ := by rw [hδ_def]; linarith
  have hY_bd := tendstoInMeasure_iff_norm.mp hY δ hδ_pos
  have hZ_bd := tendstoInMeasure_iff_norm.mp hZ δ hδ_pos
  have h_sub : ∀ n : ℕ,
      P {ω | ε ≤ ‖(Y n ω + Z n ω) - (a + b)‖}
        ≤ P {ω | δ ≤ ‖Y n ω - a‖} + P {ω | δ ≤ ‖Z n ω - b‖} := by
    intro n
    have h_inclusion :
        {ω | ε ≤ ‖(Y n ω + Z n ω) - (a + b)‖}
          ⊆ {ω | δ ≤ ‖Y n ω - a‖} ∪ {ω | δ ≤ ‖Z n ω - b‖} := by
      intro ω hω
      rw [Set.mem_setOf_eq, Real.norm_eq_abs] at hω
      by_contra h
      rw [Set.mem_union, not_or] at h
      obtain ⟨hY', hZ'⟩ := h
      rw [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at hY'
      rw [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at hZ'
      have hdecomp : (Y n ω + Z n ω) - (a + b) = (Y n ω - a) + (Z n ω - b) := by ring
      have htri : |(Y n ω + Z n ω) - (a + b)| ≤ |Y n ω - a| + |Z n ω - b| := by
        rw [hdecomp]; exact abs_add_le _ _
      linarith
    exact (measure_mono h_inclusion).trans (measure_union_le _ _)
  have h_sum_tendsto : Filter.Tendsto
      (fun n => P {ω | δ ≤ ‖Y n ω - a‖} + P {ω | δ ≤ ‖Z n ω - b‖})
      Filter.atTop (𝓝 0) := by
    have := hY_bd.add hZ_bd
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_sum_tendsto
    (Filter.Eventually.of_forall fun _ => zero_le)
    (Filter.Eventually.of_forall h_sub)

end AsymptoticStatistics
