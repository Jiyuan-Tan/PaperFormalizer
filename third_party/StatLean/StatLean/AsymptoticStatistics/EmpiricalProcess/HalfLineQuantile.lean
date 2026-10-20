module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.HalfLineIndicators

@[expose] public section

/-!
# Atom-safe CDF quantiles and grids

Generalized inverse CDF points and the finite monotone grids underlying the
half-line bracketing argument in vdV Theorem 19.1 and Example 19.6.

All statements allow arbitrary atoms. Open gaps carry the small-mass bounds;
each quantile jump is isolated as a singleton rather than absorbed into a
closed-right bracket.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

/-- Generalized CDF inverse `inf {x | u ≤ F(x)}`.

Edge behavior: this raw `sInf` definition is total. The textbook quantile
specification is asserted only for `0 < u < 1`, where the defining set is
nonempty and bounded below. -/
noncomputable def cdfQuantile (P : Measure ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | u ≤ cdf P x}

private lemma cdf_leftLim_eq_real_Iio (P : Measure ℝ) [IsProbabilityMeasure P]
    (x : ℝ) :
    Function.leftLim (cdf P) x = P.real (Iio x) := by
  have hnonneg : 0 ≤ Function.leftLim (cdf P) x :=
    (cdf_nonneg P (x - 1)).trans ((monotone_cdf P).le_leftLim (sub_lt_self x one_pos))
  have hmeasure : P (Iio x) = ENNReal.ofReal (Function.leftLim (cdf P) x) := by
    calc
      P (Iio x) = (cdf P).measure (Iio x) := by rw [measure_cdf P]
      _ = _ := by rw [(cdf P).measure_Iio (tendsto_cdf_atBot P), sub_zero]
  rw [measureReal_def, hmeasure, ENNReal.toReal_ofReal hnonneg]

/-- Generalized-inverse specification, valid without CDF continuity:
`u ≤ F(q(u))` and `F(q(u)-) ≤ u`. The left limit is represented exactly by
`P.real (Iio q(u))`, so atoms at the quantile are not discarded. -/
theorem cdfQuantile_spec (P : Measure ℝ) [IsProbabilityMeasure P]
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    u ≤ cdf P (cdfQuantile P u) ∧
      P.real (Iio (cdfQuantile P u)) ≤ u := by
  let S : Set ℝ := {x | u ≤ cdf P x}
  have hS_nonempty : S.Nonempty := by
    have h_event : ∀ᶠ x in atTop, u < cdf P x :=
      (tendsto_cdf_atTop P).eventually (Ioi_mem_nhds hu1)
    obtain ⟨x, hx⟩ := h_event.exists
    exact ⟨x, hx.le⟩
  have hS_bdd : BddBelow S := by
    have h_event : ∀ᶠ x in atBot, cdf P x < u :=
      (tendsto_cdf_atBot P).eventually (Iio_mem_nhds hu0)
    obtain ⟨a, ha⟩ := eventually_atBot.mp h_event
    refine ⟨a, ?_⟩
    intro x hx
    by_contra hax
    have hxa : x ≤ a := le_of_not_ge hax
    exact (not_lt_of_ge hx) ((monotone_cdf P hxa).trans_lt (ha a le_rfl))
  change u ≤ cdf P (sInf S) ∧ P.real (Iio (sInf S)) ≤ u
  constructor
  · rw [← (cdf P).iInf_Ioi_eq (sInf S)]
    refine le_ciInf fun (r : Ioi (sInf S)) ↦ ?_
    obtain ⟨x, hxS, hxr⟩ := (csInf_lt_iff hS_bdd hS_nonempty).mp r.2
    exact hxS.trans (monotone_cdf P hxr.le)
  · rw [← cdf_leftLim_eq_real_Iio P]
    apply le_of_tendsto ((monotone_cdf P).tendsto_leftLim (sInf S))
    filter_upwards [self_mem_nhdsWithin] with x hx
    by_contra hxu
    have hxS : x ∈ S := le_of_not_ge hxu
    exact (not_lt_of_ge (csInf_le hS_bdd hxS)) hx

/-- Two generalized quantiles enclose an open gap of mass at most the
difference of their levels. Endpoint atoms are deliberately excluded. -/
theorem cdfQuantile_openGap_measure_le (P : Measure ℝ) [IsProbabilityMeasure P]
    {u v : ℝ} (hu0 : 0 < u) (huv : u < v) (hv1 : v < 1) :
    P (Ioo (cdfQuantile P u) (cdfQuantile P v)) ≤ ENNReal.ofReal (v - u) := by
  have hu := cdfQuantile_spec P hu0 (huv.trans hv1)
  have hv := cdfQuantile_spec P (hu0.trans huv) hv1
  calc
    P (Ioo (cdfQuantile P u) (cdfQuantile P v)) =
        (cdf P).measure (Ioo (cdfQuantile P u) (cdfQuantile P v)) := by
          rw [measure_cdf P]
    _ = ENNReal.ofReal
        (Function.leftLim (cdf P) (cdfQuantile P v) - cdf P (cdfQuantile P u)) :=
      (cdf P).measure_Ioo
    _ ≤ ENNReal.ofReal (v - u) := ENNReal.ofReal_le_ofReal
      (sub_le_sub (by rw [cdf_leftLim_eq_real_Iio P]; exact hv.2) hu.1)

/-- The discrepancy between open- and closed-right half-line endpoints at a
quantile is exactly its singleton. This is the atom-isolation step. -/
theorem halfLine_quantile_jump_support (P : Measure ℝ) (u : ℝ) :
    {x | openHalfLineIndicator (cdfQuantile P u) x ≠
      halfLineIndicator (cdfQuantile P u) x} = {cdfQuantile P u} := by
  ext x
  by_cases hx : x = cdfQuantile P u
  · subst x
    simp [openHalfLineIndicator, halfLineIndicator]
  · rcases lt_or_gt_of_ne hx with hlt | hgt
    · simp [openHalfLineIndicator, halfLineIndicator, hlt, hlt.le, hx]
    · simp [openHalfLineIndicator, halfLineIndicator, not_lt_of_ge hgt.le,
        not_le_of_gt hgt, hx]

private lemma cdfQuantile_mono_of_le (P : Measure ℝ) [IsProbabilityMeasure P]
    {u v : ℝ} (hu0 : 0 < u) (huv : u ≤ v) (hv1 : v < 1) :
    cdfQuantile P u ≤ cdfQuantile P v := by
  rcases huv.eq_or_lt with rfl | huv'
  · exact le_rfl
  · by_contra hq
    have hqu := cdfQuantile_spec P hu0 (huv'.trans hv1)
    have hqv := cdfQuantile_spec P (hu0.trans huv') hv1
    have hbetween : cdf P (cdfQuantile P v) ≤
        P.real (Iio (cdfQuantile P u)) := by
      rw [cdf_eq_real]
      exact measureReal_mono (Iic_subset_Iio.mpr (lt_of_not_ge hq))
    exact (not_le_of_gt huv') (hqv.1.trans (hbetween.trans hqu.2))

/-- Atom-safe finite monotone CDF grid. For `n+1` quantile points, both tails
and every open gap have mass at most `1/(n+2)`. Repeated grid points are
allowed and are necessary for large atoms. -/
theorem exists_halfLine_atomSafeGrid (P : Measure ℝ) [IsProbabilityMeasure P]
    (n : ℕ) :
    ∃ q : Fin (n + 1) → ℝ,
      Monotone q ∧
      P (Iio (q 0)) ≤ ENNReal.ofReal (1 / (n + 2 : ℝ)) ∧
      (∀ j : Fin n,
        P (Ioo (q j.castSucc) (q j.succ)) ≤ ENNReal.ofReal (1 / (n + 2 : ℝ))) ∧
      P (Ioi (q (Fin.last n))) ≤ ENNReal.ofReal (1 / (n + 2 : ℝ)) := by
  let level : Fin (n + 1) → ℝ := fun i ↦ ((i.val + 1 : ℕ) : ℝ) / (n + 2 : ℝ)
  let q : Fin (n + 1) → ℝ := fun i ↦ cdfQuantile P (level i)
  have hd : 0 < (n + 2 : ℝ) := by positivity
  have hlevel_pos (i : Fin (n + 1)) : 0 < level i := by
    dsimp [level]
    positivity
  have hlevel_lt_one (i : Fin (n + 1)) : level i < 1 := by
    rw [div_lt_one hd]
    exact_mod_cast (show i.val + 1 < n + 2 by omega)
  have hlevel_mono : Monotone level := by
    intro i j hij
    change ((i.val + 1 : ℕ) : ℝ) / (n + 2 : ℝ) ≤
      ((j.val + 1 : ℕ) : ℝ) / (n + 2 : ℝ)
    apply div_le_div_of_nonneg_right _ hd.le
    have hij' : i.val ≤ j.val := hij
    exact_mod_cast Nat.add_le_add_right hij' 1
  have hlevel_succ (j : Fin n) : level j.castSucc < level j.succ := by
    change ((j.val + 1 : ℕ) : ℝ) / (n + 2 : ℝ) <
      ((j.val + 2 : ℕ) : ℝ) / (n + 2 : ℝ)
    rw [div_lt_div_iff_of_pos_right hd]
    exact_mod_cast Nat.lt_succ_self (j.val + 1)
  have hlevel_diff (j : Fin n) : level j.succ - level j.castSucc =
      1 / (n + 2 : ℝ) := by
    change ((j.val + 2 : ℕ) : ℝ) / (n + 2 : ℝ) -
      ((j.val + 1 : ℕ) : ℝ) / (n + 2 : ℝ) = 1 / (n + 2 : ℝ)
    field_simp [ne_of_gt hd]
    norm_num [Nat.cast_add]
  have hlevel_last : 1 - level (Fin.last n) = 1 / (n + 2 : ℝ) := by
    change 1 - ((n + 1 : ℕ) : ℝ) / (n + 2 : ℝ) = 1 / (n + 2 : ℝ)
    field_simp [ne_of_gt hd]
    norm_num [Nat.cast_add]
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact cdfQuantile_mono_of_le P (hlevel_pos i) (hlevel_mono hij) (hlevel_lt_one j)
  · rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [q, level] using (cdfQuantile_spec P (hlevel_pos 0) (hlevel_lt_one 0)).2)
  · intro j
    simpa [q, hlevel_diff j] using
      cdfQuantile_openGap_measure_le P (hlevel_pos j.castSucc) (hlevel_succ j)
        (hlevel_lt_one j.succ)
  · calc
      P (Ioi (q (Fin.last n))) = ENNReal.ofReal
          (1 - cdf P (q (Fin.last n))) := by
        calc
          P (Ioi (q (Fin.last n))) = (cdf P).measure (Ioi (q (Fin.last n))) := by
            rw [measure_cdf P]
          _ = _ := (cdf P).measure_Ioi (tendsto_cdf_atTop P) _
      _ ≤ ENNReal.ofReal (1 / (n + 2 : ℝ)) := ENNReal.ofReal_le_ofReal <| calc
        1 - cdf P (q (Fin.last n)) ≤ 1 - level (Fin.last n) :=
          sub_le_sub_left (cdfQuantile_spec P (hlevel_pos _) (hlevel_lt_one _)).1 1
        _ = 1 / (n + 2 : ℝ) := hlevel_last

end AsymptoticStatistics.EmpiricalProcess
