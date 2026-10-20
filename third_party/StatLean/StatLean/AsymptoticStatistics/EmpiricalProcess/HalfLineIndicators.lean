module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.PointwiseDense
public import Mathlib.Probability.CDF

@[expose] public section

/-!
# Half-line indicator class

The measurable class `x ↦ 1{x ≤ t}` from van der Vaart §19.1 and Example 19.6,
together with its elementary `L²(P)` and CDF identities and the countable
right-rational pointwise-dense skeleton used by empirical-process suprema.

The approximating rationals approach each threshold from the right. Approaching
from the left gives the wrong value at the threshold itself.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

/-- The half-line indicator `1_{(-∞,t]}` (vdV §19.1, p.265).

Edge behavior: the endpoint is included, so `halfLineIndicator t t = 1`.
This closed-right convention is essential for the empirical CDF. -/
noncomputable def halfLineIndicator (t : ℝ) : ℝ → ℝ :=
  Set.Iic t |>.indicator 1

/-- The class of all closed half-line indicators from vdV Example 19.6.

Edge behavior: every real threshold occurs; no formal `±∞` endpoint is added.
The limiting zero and one functions are therefore not separate class members. -/
def halfLineIndicatorClass : Set (ℝ → ℝ) := Set.range halfLineIndicator

/-- The open half-line indicator `1_{(-∞,t)}` used as an atom-safe bracket endpoint.

Edge behavior: it is zero at `t`; its difference from `halfLineIndicator t`
is supported exactly on the singleton `{t}`. -/
noncomputable def openHalfLineIndicator (t : ℝ) : ℝ → ℝ :=
  Set.Iio t |>.indicator 1

/-- Canonical threshold index in `halfLineIndicatorClass`. -/
noncomputable def halfLineIndex (t : ℝ) : ↑halfLineIndicatorClass :=
  ⟨halfLineIndicator t, ⟨t, rfl⟩⟩

/-- The threshold parametrization is a bijection onto the half-line class. -/
noncomputable def halfLineIndexEquiv : ℝ ≃ ↑halfLineIndicatorClass :=
  Equiv.ofBijective halfLineIndex ⟨by
    intro s t hst
    apply le_antisymm
    · by_contra h
      have hvalue := congrFun (congrArg Subtype.val hst) s
      simp [halfLineIndex, halfLineIndicator, not_le.mp h] at hvalue
    · by_contra h
      have hvalue := congrFun (congrArg Subtype.val hst) t
      simp [halfLineIndex, halfLineIndicator, not_le.mp h] at hvalue
  , by
    rintro ⟨f, t, rfl⟩
    exact ⟨t, rfl⟩⟩

lemma measurable_halfLineIndicator (t : ℝ) :
    Measurable (halfLineIndicator t) := by
  exact (measurable_indicator_const_iff (1 : ℝ)).2 measurableSet_Iic

lemma measurable_openHalfLineIndicator (t : ℝ) :
    Measurable (openHalfLineIndicator t) := by
  exact (measurable_indicator_const_iff (1 : ℝ)).2 measurableSet_Iio

lemma halfLineIndicator_memLp (P : Measure ℝ) [IsProbabilityMeasure P]
    (t : ℝ) (p : ℝ≥0∞) : MemLp (halfLineIndicator t) p P := by
  exact memLp_indicator_const p measurableSet_Iic 1 (Or.inr (measure_ne_top P _))

lemma openHalfLineIndicator_memLp (P : Measure ℝ) [IsProbabilityMeasure P]
    (t : ℝ) (p : ℝ≥0∞) : MemLp (openHalfLineIndicator t) p P := by
  exact memLp_indicator_const p measurableSet_Iio 1 (Or.inr (measure_ne_top P _))

/-- Population integral of a half-line indicator is the CDF coordinate. -/
lemma integral_halfLineIndicator (P : Measure ℝ) [IsProbabilityMeasure P]
    (t : ℝ) :
    ∫ x, halfLineIndicator t x ∂P = cdf P t := by
  rw [halfLineIndicator, integral_indicator_one measurableSet_Iic, cdf_eq_real]

/-- Products of half-line indicators intersect at the smaller threshold. -/
lemma halfLineIndicator_mul (s t x : ℝ) :
    halfLineIndicator s x * halfLineIndicator t x =
      halfLineIndicator (min s t) x := by
  by_cases hxs : x ≤ s <;> by_cases hxt : x ≤ t <;>
    simp [halfLineIndicator, hxs, hxt]

/-- Integral form of the half-line intersection identity. -/
lemma integral_halfLineIndicator_mul (P : Measure ℝ) [IsProbabilityMeasure P]
    (s t : ℝ) :
    ∫ x, halfLineIndicator s x * halfLineIndicator t x ∂P = cdf P (min s t) := by
  simp_rw [halfLineIndicator_mul]
  exact integral_halfLineIndicator P (min s t)

/-- Right-rational approximation makes the half-line class pointwise dense in
the sense needed for empirical-process suprema. The common envelope is `1`.
No continuity or nonatomicity assumption on `P` is used. -/
theorem halfLine_empProcPointwiseDense (P : Measure ℝ) [IsProbabilityMeasure P] :
    EmpProcPointwiseDense halfLineIndicatorClass P := by
  refine ⟨Set.range (fun q : ℚ => halfLineIndicator (q : ℝ)), ?_,
    Set.countable_range _, ?_, ?_⟩
  · rintro f ⟨q, rfl⟩
    exact ⟨q, rfl⟩
  · intro f hf
    rcases hf with ⟨t, rfl⟩
    obtain ⟨q, -, htq, hq⟩ := Real.exists_seq_rat_strictAnti_tendsto t
    refine ⟨fun n => halfLineIndicator (q n : ℝ), fun n => ⟨q n, rfl⟩, ?_⟩
    intro x
    by_cases hxt : x ≤ t
    · have heq : (fun n => halfLineIndicator (q n : ℝ) x) = fun _ => (1 : ℝ) := by
        funext n
        simp [halfLineIndicator, hxt.trans (le_of_lt (htq n))]
      rw [heq]
      simp [halfLineIndicator, hxt]
    · refine (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [hq.eventually_lt_const (lt_of_not_ge hxt)] with n hn
      simp [halfLineIndicator, hxt, not_le_of_gt hn]
  · refine ⟨fun _ => (1 : ℝ), integrable_const 1, ?_⟩
    rintro g ⟨t, rfl⟩ x
    by_cases hxt : x ≤ t <;> simp [halfLineIndicator, hxt]

end AsymptoticStatistics.EmpiricalProcess
