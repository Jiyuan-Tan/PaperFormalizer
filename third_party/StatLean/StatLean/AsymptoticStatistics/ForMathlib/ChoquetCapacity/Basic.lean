module
/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file
LICENSES/formal-learning-theory-kernel-Apache-2.0.txt.
Authors: Dhruv Gupta

This file adapts and splits the basic-capacity portion of
FLT_Proofs/PureMath/ChoquetCapacity.lean at commit
b1b9d16a552e3e09bfbb8151fe6aa14c805d7979.
-/
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-!
# Choquet capacities: basic definitions

This file defines the abstract Choquet-capacity interface and the finite-measure
instance used by the analytic-set capacitability theorem.

The declarations are adapted from Dhruv Gupta's *Formal Learning Theory Kernel*,
pinned at commit `b1b9d16a552e3e09bfbb8151fe6aa14c805d7979` (Apache-2.0).

## Main declarations

* `MeasureTheory.compactCap`
* `MeasureTheory.compactCap_mono`
* `MeasureTheory.IsChoquetCapacity`
* `MeasureTheory.measure_isChoquetCapacity`
* `MeasureTheory.MeasurableSet.compactCap_eq`
-/

open MeasureTheory Set Filter Topology

/-- Compact capacity of `s` relative to `μ`: the supremum of `μ K` over compact
subsets `K ⊆ s`.

The topology and measurable space are ambient structure. Edge behavior: the
empty family has supremum
zero, so `compactCap μ ∅ = 0`. -/
noncomputable def MeasureTheory.compactCap
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (s : Set α) : ENNReal := by
  exact sSup {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K}

/-- Compact capacity is monotone in its set argument.

The ambient instances encode the topological measurable space. -/
theorem MeasureTheory.compactCap_mono
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s t : Set α} (hst : s ⊆ t) :
    MeasureTheory.compactCap μ s ≤ MeasureTheory.compactCap μ t := by
  apply sSup_le_sSup
  rintro r ⟨K, hKc, hKs, rfl⟩
  exact ⟨K, hKc, hKs.trans hst, rfl⟩

/-- The three constitutive axioms of a Choquet capacity: monotonicity,
continuity from below along increasing sequences, and continuity from above along
decreasing sequences of closed sets.

The functional `cap` is explicit data; the topology is ambient structure.
-/
structure MeasureTheory.IsChoquetCapacity
    {α : Type*} [TopologicalSpace α]
    (cap : Set α → ENNReal) : Prop where
  /-- Constitutive (Choquet, *Theory of capacities*, 1954): capacities are monotone. -/
  mono : ∀ {s t : Set α}, s ⊆ t → cap s ≤ cap t
  /-- Constitutive (Choquet, *Theory of capacities*, 1954): capacities are continuous
  from below on increasing sequences. -/
  iUnion_nat : ∀ (f : ℕ → Set α), Monotone f →
    cap (⋃ n, f n) = ⨆ n, cap (f n)
  /-- Constitutive (Choquet, *Theory of capacities*, 1954): capacities are continuous
  from above on decreasing sequences of closed sets. -/
  iInter_closed : ∀ (f : ℕ → Set α), Antitone f →
    (∀ n, IsClosed (f n)) →
    cap (⋂ n, f n) = ⨅ n, cap (f n)

/-- Every finite Borel measure on a Polish space is a Choquet capacity.

Finiteness and the Polish/Borel instances state the mathematical scope of this
general theorem. -/
theorem MeasureTheory.measure_isChoquetCapacity
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ] :
    MeasureTheory.IsChoquetCapacity (fun s : Set α => μ s) := by
  constructor
  · intro s t hst
    exact measure_mono hst
  · intro f hf
    exact hf.measure_iUnion
  · intro f hf hclosed
    exact hf.measure_iInter
      (fun n => (hclosed n).measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top μ (f 0)⟩

/-- On Borel-measurable sets, compact capacity equals the measure.

Finite measure and Polish/Borel structure are the theorem's mathematical scope.
-/
theorem MeasureTheory.MeasurableSet.compactCap_eq
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s) :
    MeasureTheory.compactCap μ s = μ s := by
  apply le_antisymm
  · apply sSup_le
    rintro r ⟨K, _, hKs, rfl⟩
    exact measure_mono hKs
  · change μ s ≤ MeasureTheory.compactCap μ s
    unfold MeasureTheory.compactCap
    have hbdd : BddAbove {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K} :=
      ⟨μ Set.univ, fun _ ⟨_, _, hLs, hr⟩ =>
        hr ▸ measure_mono (hLs.trans (Set.subset_univ _))⟩
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hε_ne : (ε : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hε.ne'
    obtain ⟨K, hKs, hKc, hlt⟩ := hs.exists_isCompact_lt_add (measure_ne_top μ s) hε_ne
    calc
      μ s ≤ μ K + ε := le_of_lt hlt
      _ ≤ sSup {r | ∃ K, IsCompact K ∧ K ⊆ s ∧ r = μ K} + ε := by
        gcongr
        exact le_csSup hbdd ⟨K, hKc, hKs, rfl⟩
