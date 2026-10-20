module
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

@[expose] public section

/-!
# Measurable diagonals over a countable parameter range

This file proves measurability of a family of measurable sections evaluated
along a measurable parameter map with countable range.
-/

/-- Evaluating measurable sections along a measurable parameter map remains
measurable when the parameter map has countable range and singleton parameter
sets are measurable. -/
theorem measurable_diag_of_countable_range
    {α τ β : Type*}
    -- the measurable structures on the source and parameter spaces.
    [MeasurableSpace α] [MeasurableSpace τ]
    -- singleton measurability makes the countably many parameter fibers measurable.
    [MeasurableSingletonClass τ]
    -- the measurable structure on the target space.
    [MeasurableSpace β]
    -- the supplied parameter map and family of sections.
    (p : α → τ) (f : α → τ → β)
    -- measurability of the supplied parameter map.
    (hp : Measurable p)
    -- countability of the attained parameter values.
    (hrange : (Set.range p).Countable)
    -- measurability of every supplied fixed-parameter section.
    (hf : ∀ t, Measurable (fun x => f x t)) :
    Measurable (fun x => f x (p x)) := by
  intro s hs
  letI : Countable (Set.range p) := hrange.to_subtype
  have hpreimage : (fun x => f x (p x)) ⁻¹' s =
      ⋃ t : Set.range p, (p ⁻¹' ({t.1} : Set τ)) ∩ ((fun x => f x t.1) ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.2 ⟨⟨p x, Set.mem_range_self x⟩, rfl, hx⟩
    · intro hx
      obtain ⟨t, hpt, hft⟩ := Set.mem_iUnion.1 hx
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hpt
      change f x (p x) ∈ s
      change f x t.1 ∈ s at hft
      rw [hpt]
      exact hft
  rw [hpreimage]
  exact MeasurableSet.iUnion fun t =>
    (hp (measurableSet_singleton t.1)).inter (hf t.1 hs)
