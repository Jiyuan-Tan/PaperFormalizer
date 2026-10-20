module
public import StatLean.AsymptoticStatistics.ForMathlib.ChoquetCapacity.Analytic
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Measure.NullMeasurable

@[expose] public section

/-!
# Universal measurability of analytic sets

This file derives compact inner approximation for analytic subsets of Polish spaces
from the general Choquet-capacity theorem, then assembles the finite-measure result into
the s-finite public API used by measurable selection.

## Main declarations

* `MeasureTheory.AnalyticSet.exists_isCompact_measure_diff_lt`
* `MeasureTheory.AnalyticSet.statLean_nullMeasurableSet`

The dependency chain is `ChoquetCapacity.Basic` → `ChoquetCapacity.Analytic` →
this file → `MeasurableSelection`.
-/

namespace MeasureTheory

open Set Filter Topology
open scoped ENNReal

/-- An analytic set under a finite Borel measure admits a compact inner approximation
whose missing mass is smaller than any positive tolerance.

The Polish/Borel and finite-measure assumptions state the theorem's
mathematical scope. -/
theorem AnalyticSet.exists_isCompact_measure_diff_lt
    {β : Type*} [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β]
    {A : Set β} (hA : AnalyticSet A)
    (m : Measure β) [IsFiniteMeasure m]
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set β, IsCompact K ∧ K ⊆ A ∧ m (A \ K) < ε := by
  have hcap := hA.cap_eq_iSup_isCompact (measure_isChoquetCapacity m)
  rcases eq_or_ne (m A) 0 with hA0 | hA0
  · refine ⟨∅, isCompact_empty, Set.empty_subset A, ?_⟩
    simpa [hA0]
  · have hsub : m A - ε < m A :=
      ENNReal.sub_lt_self (measure_ne_top m A) hA0 hε.ne'
    have hltSup : m A - ε <
        ⨆ (K : Set β), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ A), m K := by
      calc
        m A - ε < m A := hsub
        _ = ⨆ (K : Set β), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ A), m K := hcap
    obtain ⟨K, hK⟩ := lt_iSup_iff.mp hltSup
    obtain ⟨hKc, hK⟩ := lt_iSup_iff.mp hK
    obtain ⟨hKA, hK⟩ := lt_iSup_iff.mp hK
    refine ⟨K, hKc, hKA, ?_⟩
    apply measure_diff_lt_of_lt_add hKc.nullMeasurableSet hKA (measure_ne_top m K)
    exact ENNReal.lt_add_of_sub_lt_right (Or.inl (measure_ne_top m A)) hK

/-- Inner approximation for analytic sets under a finite Borel measure.

Its signature is the finite-measure form consumed by the s-finite theorem.
The assumptions state the Polish/Borel finite-measure scope. -/
private theorem analyticSet_innerApprox_of_isFiniteMeasure
    {β : Type*} [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β]
    {A : Set β} (hA : AnalyticSet A)
    (m : Measure β) [IsFiniteMeasure m] :
    ∃ B : Set β, B ⊆ A ∧ MeasurableSet B ∧ m (A \ B) = 0 := by
  classical
  let ε : ℕ → ℝ≥0∞ := fun n => (((n : ℕ) + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hε_pos : ∀ n : ℕ, 0 < ε n := by
    intro n
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
  have hcomp : ∀ n : ℕ, ∃ K : Set β,
      K ⊆ A ∧ MeasurableSet K ∧ m (A \ K) ≤ ε n := by
    intro n
    obtain ⟨K, hKc, hKA, hKlt⟩ :=
      hA.exists_isCompact_measure_diff_lt m (hε_pos n)
    exact ⟨K, hKA, hKc.measurableSet, le_of_lt hKlt⟩
  choose K hKA hKmeas hKlt using hcomp
  refine ⟨⋃ n, K n, ?_, MeasurableSet.iUnion hKmeas, ?_⟩
  · intro x hx
    rcases mem_iUnion.mp hx with ⟨n, hxn⟩
    exact hKA n hxn
  · have hbd : ∀ n : ℕ, m (A \ ⋃ i, K i) ≤ ε n := by
      intro n
      have hsubn : A \ ⋃ i, K i ⊆ A \ K n := by
        intro x hx
        refine ⟨hx.1, fun hxK => hx.2 ?_⟩
        exact mem_iUnion.mpr ⟨n, hxK⟩
      exact (measure_mono hsubn).trans (hKlt n)
    have htend : Tendsto ε atTop (𝓝 0) := by
      exact (Filter.tendsto_add_atTop_iff_nat 1).mpr
        ENNReal.tendsto_inv_nat_nhds_zero
    have hle0 : m (A \ ⋃ i, K i) ≤ 0 :=
      ge_of_tendsto htend (Filter.Eventually.of_forall hbd)
    exact le_antisymm hle0 (zero_le)

/-- In a Polish space, every analytic set is null-measurable for every s-finite Borel
measure.

This is the form required by the measurable-selection module.
The Polish/Borel and s-finite assumptions state the theorem's scope. -/
theorem AnalyticSet.statLean_nullMeasurableSet
    {β : Type*} [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β]
    {A : Set β} (hA : AnalyticSet A)
    (m : Measure β) [SFinite m] :
    NullMeasurableSet A m := by
  classical
  have hcomp : ∀ i : ℕ, ∃ B : Set β,
      B ⊆ A ∧ MeasurableSet B ∧ (sfiniteSeq m i) (A \ B) = 0 := by
    intro i
    haveI : IsFiniteMeasure (sfiniteSeq m i) := isFiniteMeasure_sfiniteSeq i
    exact analyticSet_innerApprox_of_isFiniteMeasure hA (sfiniteSeq m i)
  choose B hBA hBmeas hμ using hcomp
  set Buniv : Set β := ⋃ i, B i with hBuniv_def
  have hBuniv_sub : Buniv ⊆ A := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨i, hxi⟩
    exact hBA i hxi
  have hBuniv_meas : MeasurableSet Buniv := MeasurableSet.iUnion hBmeas
  have hμi : ∀ i, (sfiniteSeq m i) (A \ Buniv) = 0 := by
    intro i
    have hsubi : A \ Buniv ⊆ A \ B i := by
      intro x hx
      refine ⟨hx.1, fun hxBi => hx.2 ?_⟩
      exact mem_iUnion.mpr ⟨i, hxBi⟩
    exact measure_mono_null hsubi (hμ i)
  have hsum : m = Measure.sum (sfiniteSeq m) := (sum_sfiniteSeq m).symm
  have hμmeas : m (A \ Buniv) = 0 := by
    have hzero : Measure.sum (sfiniteSeq m) (A \ Buniv) = 0 :=
      Measure.sum_apply_eq_zero.mpr hμi
    simpa [hsum] using hzero
  refine ⟨Buniv, hBuniv_meas, ?_⟩
  rw [ae_eq_set]
  refine ⟨hμmeas, ?_⟩
  have : Buniv \ A = ∅ := by
    ext x
    simp only [mem_diff, mem_empty_iff_false, iff_false, not_and, not_not]
    intro hxB
    exact hBuniv_sub hxB
  rw [this]
  simp

end MeasureTheory
