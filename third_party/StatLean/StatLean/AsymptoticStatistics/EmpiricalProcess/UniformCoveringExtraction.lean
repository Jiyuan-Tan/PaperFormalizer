module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCovering

@[expose] public section

/-!
# Minimal normalized finite-discrete covers

This file extracts an achieving finite cover from the extended-natural
infimum defining the normalized finite-discrete covering number.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open scoped ENNReal NNReal

variable {Ω : Type*}

/-- A finite normalized covering number with nonzero envelope seminorm is
achieved by an ambient-center finite cover. -/
theorem exists_minimal_normalizedL2Cover
    (Q : FiniteDiscreteProbability Ω) (F : Set (Ω → ℝ))
    (Φ : Ω → ℝ) (ε : ℝ)
    (hΦ : Q.l2Seminorm Φ ≠ 0)
    (hN : normalizedL2CoveringNumber Q F Φ ε ≠ ⊤) :
    ∃ S : Finset (Ω → ℝ),
      (∀ f ∈ F, ∃ g ∈ S,
        Q.distL2 f g < ε * Q.l2Seminorm Φ) ∧
      (S.card : ℕ∞) = normalizedL2CoveringNumber Q F Φ ε := by
  classical
  let Covers : Finset (Ω → ℝ) → Prop := fun S =>
    ∀ f ∈ F, ∃ g ∈ S, Q.distL2 f g < ε * Q.l2Seminorm Φ
  obtain ⟨S, hS⟩ := ENat.exists_eq_iInf
    (fun S : Finset (Ω → ℝ) => ⨅ (_ : Covers S), (S.card : ℕ∞))
  have hN_eq : normalizedL2CoveringNumber Q F Φ ε =
      ⨅ S : Finset (Ω → ℝ), ⨅ (_ : Covers S), (S.card : ℕ∞) := by
    simp [normalizedL2CoveringNumber, hΦ, Covers]
  have hCovers : Covers S := by
    by_contra h
    have htop : (⨅ (_ : Covers S), (S.card : ℕ∞)) = ⊤ := by
      simp [h]
    apply hN
    rw [hN_eq, ← hS, htop]
  refine ⟨S, hCovers, ?_⟩
  rw [hN_eq, ← hS]
  simp [hCovers]

/-- A finite normalized cover inherits the uniform covering-number bound. -/
theorem exists_normalizedL2Cover_card_le_uniform
    (Q : FiniteDiscreteProbability Ω) (F : Set (Ω → ℝ))
    (Φ : Ω → ℝ) (ε : ℝ)
    (hΦ : Q.l2Seminorm Φ ≠ 0)
    (hU : uniformL2CoveringNumber F Φ ε ≠ ⊤) :
    ∃ S : Finset (Ω → ℝ),
      (∀ f ∈ F, ∃ g ∈ S,
        Q.distL2 f g < ε * Q.l2Seminorm Φ) ∧
      (S.card : ℕ∞) ≤ uniformL2CoveringNumber F Φ ε := by
  have hN : normalizedL2CoveringNumber Q F Φ ε ≠ ⊤ := by
    intro htop
    apply hU
    exact top_unique (by
      simpa [htop] using normalizedL2CoveringNumber_le_uniform Q F Φ ε)
  obtain ⟨S, hcover, hcard⟩ :=
    exists_minimal_normalizedL2Cover Q F Φ ε hΦ hN
  refine ⟨S, hcover, ?_⟩
  calc
    (S.card : ℕ∞) = normalizedL2CoveringNumber Q F Φ ε := hcard
    _ ≤ uniformL2CoveringNumber F Φ ε :=
      normalizedL2CoveringNumber_le_uniform Q F Φ ε

end AsymptoticStatistics.EmpiricalProcess
