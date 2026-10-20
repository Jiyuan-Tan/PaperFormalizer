module
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-!
# Algebraic operations preserving `TendstoInMeasure ... 0`

Mathlib's `TendstoInMeasure` API (`Mathlib.MeasureTheory.Function.ConvergenceInMeasure`)
provides `congr_left`, `congr_right`, `mono`, `comp`, but no direct algebraic
operations (`add`, `neg`, `sub`, `const_mul`) for the case where the limit is
the zero function. We package those here for real-valued sequences.

Headline declarations: `TendstoInMeasure.neg_zero`, `TendstoInMeasure.const_mul_zero`,
`TendstoInMeasure.add_zero`, `TendstoInMeasure.sub_zero`.

The declarations below provide this zero-limit algebra for real-valued sequences.
-/

namespace MeasureTheory

open scoped ENNReal

variable {α ι : Type*} {m : MeasurableSpace α} {μ : Measure α} {l : Filter ι}

/-- `-f →_P 0` from `f →_P 0`.
Proof: `convert` on `edist (-f n ω) 0 = edist (f n ω) 0` via `enorm_neg`. -/
theorem TendstoInMeasure.neg_zero {f : ι → α → ℝ}
    (hf : TendstoInMeasure μ f l (fun _ => (0 : ℝ))) :
    TendstoInMeasure μ (fun n => -f n) l (fun _ => (0 : ℝ)) := by
  intro ε hε
  convert hf ε hε using 1
  ext n
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, edist_zero_right, Pi.neg_apply, enorm_neg]

/-- `c · f →_P 0` from `f →_P 0`.
Proof: case-split c=0 (trivial: set is empty), c≠0 (scale ε by 1/‖c‖ₑ
via `enorm_mul` for ℝ + `ENNReal.le_div_iff_mul_le`). -/
theorem TendstoInMeasure.const_mul_zero (c : ℝ) {f : ι → α → ℝ}
    (hf : TendstoInMeasure μ f l (fun _ => (0 : ℝ))) :
    TendstoInMeasure μ (fun n ω => c * f n ω) l (fun _ => (0 : ℝ)) := by
  by_cases hc : c = 0
  · subst hc
    intro ε hε
    have h_empty : ∀ n, {ω : α | ε ≤ edist ((0 : ℝ) * f n ω) (0 : ℝ)} = ∅ := by
      intro n
      ext ω
      simp only [zero_mul, edist_self, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
                 not_le]
      exact hε
    simp_rw [h_empty, measure_empty]
    exact tendsto_const_nhds
  · intro ε hε
    have h_c_pos : (0 : ℝ) < |c| := abs_pos.mpr hc
    set k : ℝ≥0∞ := ENNReal.ofReal |c| with hk_def
    have hk_ne : k ≠ 0 := by
      simp only [hk_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact h_c_pos
    have hk_top : k ≠ ∞ := ENNReal.ofReal_ne_top
    have hε_div : (0 : ℝ≥0∞) < ε / k := ENNReal.div_pos hε.ne' hk_top
    have hf' := hf (ε / k) hε_div
    have h_set_eq : ∀ n,
        {ω | ε ≤ edist (c * f n ω) (0 : ℝ)}
          = {ω | ε / k ≤ edist (f n ω) (0 : ℝ)} := by
      intro n
      ext ω
      simp only [Set.mem_setOf_eq, edist_zero_right]
      have h_enorm : ‖c * f n ω‖ₑ = k * ‖f n ω‖ₑ := by
        rw [enorm_mul, hk_def, ← Real.enorm_eq_ofReal_abs]
      rw [h_enorm, ENNReal.div_le_iff' hk_ne hk_top]
    simp_rw [h_set_eq]
    exact hf'

/-- `f + g →_P 0` from each →_P 0.
Proof: union bound, `{|f+g|≥ε} ⊆ {|f|≥ε/2} ∪ {|g|≥ε/2}` via triangle ineq,
then `measure_union_le` + Tendsto.add on the ε/2-events. -/
theorem TendstoInMeasure.add_zero {f g : ι → α → ℝ}
    (hf : TendstoInMeasure μ f l (fun _ => (0 : ℝ)))
    (hg : TendstoInMeasure μ g l (fun _ => (0 : ℝ))) :
    TendstoInMeasure μ (fun n ω => f n ω + g n ω) l (fun _ => (0 : ℝ)) := by
  intro ε hε
  have hε_half : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hf' := hf (ε / 2) hε_half
  have hg' := hg (ε / 2) hε_half
  have h_sub : ∀ n,
      {ω | ε ≤ edist (f n ω + g n ω) (0 : ℝ)}
        ⊆ {ω | ε / 2 ≤ edist (f n ω) (0 : ℝ)} ∪
          {ω | ε / 2 ≤ edist (g n ω) (0 : ℝ)} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq, edist_zero_right] at hω
    by_contra h_neg
    rw [Set.mem_union, not_or] at h_neg
    obtain ⟨h1, h2⟩ := h_neg
    simp only [Set.mem_setOf_eq, edist_zero_right, not_le] at h1 h2
    have h_sum : ‖f n ω‖ₑ + ‖g n ω‖ₑ < ε := by
      calc ‖f n ω‖ₑ + ‖g n ω‖ₑ
          < ε / 2 + ε / 2 := ENNReal.add_lt_add h1 h2
        _ = ε := ENNReal.add_halves _
    exact absurd hω (not_le.mpr ((enorm_add_le _ _).trans_lt h_sum))
  have h_sum_tendsto : Filter.Tendsto
      (fun n => μ {ω | ε / 2 ≤ edist (f n ω) (0 : ℝ)} +
                μ {ω | ε / 2 ≤ edist (g n ω) (0 : ℝ)}) l (nhds 0) := by
    have := hf'.add hg'
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    h_sum_tendsto (.of_forall fun _ => zero_le) (.of_forall fun n => ?_)
  exact (measure_mono (h_sub n)).trans (measure_union_le _ _)

/-- `f - g →_P 0` from each →_P 0. Composed from `add_zero` + `neg_zero`. -/
theorem TendstoInMeasure.sub_zero {f g : ι → α → ℝ}
    (hf : TendstoInMeasure μ f l (fun _ => (0 : ℝ)))
    (hg : TendstoInMeasure μ g l (fun _ => (0 : ℝ))) :
    TendstoInMeasure μ (fun n ω => f n ω - g n ω) l (fun _ => (0 : ℝ)) := by
  have h_negg : TendstoInMeasure μ (fun n => -g n) l (fun _ => (0 : ℝ)) := hg.neg_zero
  have h_sum := hf.add_zero h_negg
  refine h_sum.congr_left ?_
  intro n
  filter_upwards with ω
  simp [sub_eq_add_neg]

end MeasureTheory
