module
public import StatLean.StatisticalLearning.FiniteClass.UniformConvergence
public import StatLean.StatisticalLearning.Core.ERM

@[expose] public section

/-!
# Finite classes are agnostic PAC learnable

SSBD Corollary 4.6, second half: a finite class with `[0,1]`-valued loss is
agnostically PAC learnable by any ERM selector with sample complexity
`m(ε,δ) ≤ ⌈2 log(2|𝓗|/δ)/ε²⌉` (the `ε ↦ ε/2` substitution into the
uniform-convergence half, exact book constant).

**Reference.** SSBD §4.2, Corollary 4.6. Transcriptions:
`notes/statistical_learning/book_statements/ch2-5.md`.

**Formalization notes.** Chains `finiteClass_hasUniformConvergenceWith`
through `isAgnosticPACLearnerWith_of_hasUniformConvergenceWith`
(SSBD Corollary 4.4); the only work is the ceiling arithmetic
`⌈log(2N/δ)/(2(ε/2)²)⌉ = ⌈2 log(2N/δ)/ε²⌉`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z H : Type*} [MeasurableSpace Z] {ℓ : H → Z → ℝ}

/-- **SSBD Corollary 4.6, agnostic-PAC half**: a finite class with
`[0,1]`-valued loss is agnostically PAC learnable using any ERM selector, with
`m(ε,δ) = ⌈2 log(2|𝓗|/δ)/ε²⌉` (exact book constant). -/
theorem finiteClass_isAgnosticPACLearnerWith (𝓗 : Finset H)
    {A : ∀ m : ℕ, Sample Z m → H}
    -- USER-INPUT: nonempty class; SSBD §4.2 (implicit — else vacuous)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: loss range in `[0,1]` on the class; SSBD Cor. 4.6
    (hrange : ∀ h ∈ 𝓗, ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: measurability of each loss; SSBD Remark 3.1
    (hmeas : ∀ h ∈ 𝓗, Measurable (ℓ h))
    -- USER-INPUT: `A` is an ERM selector; SSBD §2.3 (`ERM_𝓗` is data)
    (hA : ∀ (m : ℕ) (s : Sample Z m), IsERM (↑𝓗 : Set H) ℓ s (A m s))
    -- USER-INPUT: nonnegative loss off the class as well (so risks are
    -- bounded below); SSBD §3.2.1 (`ℓ : 𝓗 × Z → ℝ₊`)
    (hpos : ∀ h z, 0 ≤ ℓ h z) :
    IsAgnosticPACLearnerWith (↑𝓗 : Set H) ℓ A
      (fun ε δ => ⌈2 * Real.log (2 * 𝓗.card / δ) / ε ^ 2⌉₊) := by
  -- the `ε ↦ ε/2` substitution of SSBD Corollary 4.4 into the uniform
  -- convergence half of Corollary 4.6
  have hUC := finiteClass_hasUniformConvergenceWith 𝓗 h𝓗 hrange hmeas
  have hPAC := isAgnosticPACLearnerWith_of_hasUniformConvergenceWith hUC hA hpos
  -- `m^{UC}(ε/2, δ) = ⌈log(2N/δ)/(2(ε/2)²)⌉ = ⌈2 log(2N/δ)/ε²⌉` (the exact
  -- book constant); the identity also holds at the junk point `ε = 0`
  have key : ∀ ε L : ℝ, L / (2 * (ε / 2) ^ 2) = 2 * L / ε ^ 2 := by
    intro ε L
    rcases eq_or_ne ε 0 with rfl | hne
    · norm_num
    · field_simp
  intro D hD ε δ hε hδ hδ1 n hn
  refine hPAC D hD ε δ hε hδ hδ1 n ?_
  show ⌈Real.log (2 * 𝓗.card / δ) / (2 * (ε / 2) ^ 2)⌉₊ ≤ n
  rwa [key]

end StatLean.StatisticalLearning
