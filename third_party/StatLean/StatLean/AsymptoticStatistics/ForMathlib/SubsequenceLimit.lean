module
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Topology.Defs.Filter

@[expose] public section

/-!
Subsequence limit uniqueness: if every subsequence of `x` has a sub-subsequence
converging to `x_lim`, then the full sequence converges to `x_lim`.

This is the "Urysohn-type" lemma used in van der Vaart Theorem 7.10 (§7.3) Step 8 to promote a
subsequence weak limit (extracted via Prohorov) to a full-sequence weak limit.

Pure topology, theorem-agnostic; it is a thin wrapper around Mathlib's
`Filter.tendsto_of_subseq_tendsto`, specialised to strictly monotone subsequences
(which is the form produced by Prohorov-style extractions).
-/

open Filter Topology

namespace AsymptoticStatistics
namespace SubsequenceLimit

/-- **Urysohn subsequence principle (StrictMono form).** If every strictly monotone
subsequence of `x : ℕ → X` admits a further strictly monotone sub-subsequence whose
composite converges to `x_lim`, then the full sequence `x` converges to `x_lim`.

Proof: reduce to `Filter.tendsto_of_subseq_tendsto` by extracting a strictly monotone
sub-sequence from any `ns : ℕ → ℕ` tending to `atTop`
(via `Filter.strictMono_subseq_of_tendsto_atTop`), then apply the hypothesis to it. -/
theorem tendsto_of_subseq_tendsto
    {X : Type*} [TopologicalSpace X]
    (x : ℕ → X) (x_lim : X)
    (h : ∀ (φ : ℕ → ℕ), StrictMono φ →
        ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧ Tendsto (fun k => x (φ (ψ k))) atTop (𝓝 x_lim)) :
    Tendsto x atTop (𝓝 x_lim) := by
  refine Filter.tendsto_of_subseq_tendsto ?_
  intro ns hns
  obtain ⟨θ, _hθ_mono, hns_θ_mono⟩ := Filter.strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨ψ, _hψ_mono, hψ_conv⟩ := h (ns ∘ θ) hns_θ_mono
  exact ⟨θ ∘ ψ, hψ_conv⟩

end SubsequenceLimit
end AsymptoticStatistics
