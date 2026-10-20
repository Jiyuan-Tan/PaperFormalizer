module
public import StatLean.StatisticalModels.Identifiability.Transfer
public import StatLean.PointEstimation.Sufficiency.Defs

@[expose] public section

/-!
# Adapter: sufficiency is exactly lossless coarsening

The flagship identifiability adapter: reducing data to a **sufficient** statistic loses no
identification power. Against `StatLean.PointEstimation.Sufficiency` (imported, never
redefined):

* `pushforward_eq_statLaw` — the calculus' `pushforward` is PointEstimation's `statLaw`
  (definitional);
* `identifiable_pushforward_iff_of_hasSufficientKernel` — for `T` with a sufficient kernel,
  `Identifiable (pushforward P T) ↔ Identifiable P`: the backward direction is the generic
  destroy-direction; the forward direction reconstructs each `P θ` from the law of `T` through
  the θ-free kernel (marginalizing the graph disintegration), so distinct laws of `T` are
  forced;
* `identifiesTarget_pushforward_iff_of_hasSufficientKernel` — the target version.

Together with `Identifiability.Transfer` this completes the picture: coarsening can only
destroy identification, and sufficiency is precisely the case in which it destroys none.

**Reference.** TPE2 §1.6 (sufficiency via θ-free conditional distributions); the
reconstruction-from-the-statistic reading: P. R. Halmos and L. J. Savage, *Ann. Math.
Statist.* **20** (1949), 225–241.

**Proof formalization notes.** The forward direction takes `Measure.snd` of the graph identity
`(P θ).map (fun x => (T x, x)) = statLaw P T θ ⊗ₘ Q` (the reconstruction move documented in
`PointEstimation.Sufficiency.BayesianBridge`): equal statistic laws then force equal
reconstructions, i.e. equal models. Markov-ness of `Q` and probability of the members enter
through `Measure.snd_compProd`.

**Bibliographic comments.** Sufficiency as the coarsening that preserves all statistical
content is Fisher's original reading ("On the mathematical foundations of theoretical
statistics," *Phil. Trans. R. Soc. A* **222** (1922), 309–368); the kernel form is
Halmos–Savage.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

open StatLean.PointEstimation

variable {Θ : Type*} {𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- The calculus' pushforward model is PointEstimation's law-of-the-statistic
(definitional). -/
theorem pushforward_eq_statLaw (P : Θ → Measure 𝓧) (T : 𝓧 → S) :
    pushforward P T = statLaw P T := rfl

-- **Batch-0 finding: the two `iff`s below are FALSE as frozen** (no `Measurable T`).
-- `HasSufficientKernel P T` is *vacuously* satisfiable by a statistic that is nowhere
-- a.e.-measurable: then `(P θ).map (fun x => (T x, x)) = 0` and `statLaw P T θ = 0`
-- (`Measure.map_of_not_aemeasurable`), so the graph identity reads `0 = 0 ⊗ₘ Q = 0`
-- (`Measure.compProd_zero_left`) for *any* Markov `Q`. Concretely: `𝓧 = S = ℝ`,
-- `Θ = Bool`, `P` two distinct probability laws equivalent to Lebesgue on `[0,1]`,
-- `T = Set.indicator V 1` for a non-Lebesgue-measurable `V ⊆ [0,1]`, and
-- `Q = Kernel.const S (P false)`.
-- Then `HasSufficientKernel P T` holds, `Identifiable P` holds, but
-- `pushforward P T = fun _ => 0` is constant, so `Identifiable (pushforward P T)` fails —
-- the `iff` is `False ↔ True`. (Both halves of this were machine-checked.)
-- The `←`/destroy direction is the generic transfer theorem and is proved below; the `→`
-- direction is exactly the `Measure.snd` reconstruction, which needs
-- `AEMeasurable (fun x => (T x, x)) (P θ)` for `Measure.map_map`. Adding
-- `(hT : Measurable T)` to both signatures repairs them and closes both proofs.

/-- **Reconstruction from the statistic**: marginalizing the graph disintegration recovers
each model member from the law of `T` through the θ-free kernel, `P θ = Q ∘ₘ statLaw P T θ`.
Taking `Measure.snd` of the graph identity: on the left `Prod.snd ∘ (T, id) = id`
(`Measure.map_map`, whence the measurability of `T`), on the right `Measure.snd_compProd`. -/
private theorem eq_comp_statLaw_of_graph {P : Θ → Measure 𝓧} {T : 𝓧 → S} {Q : Kernel S 𝓧}
    [IsMarkovKernel Q] [∀ θ, IsProbabilityMeasure (P θ)] (hTm : Measurable T)
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = statLaw P T θ ⊗ₘ Q) (θ : Θ) :
    P θ = Q ∘ₘ statLaw P T θ := by
  have hst : IsProbabilityMeasure (statLaw P T θ) := by
    rw [statLaw]; exact Measure.isProbabilityMeasure_map hTm.aemeasurable
  have hgm : Measurable fun x => (T x, x) := by fun_prop
  have h := congrArg Measure.snd (hgraph θ)
  rw [Measure.snd, Measure.snd, Measure.map_map measurable_snd hgm] at h
  simp only [Function.comp_def, Measure.map_id'] at h
  rw [h, ← Measure.snd, Measure.snd_compProd]

/-- **Sufficiency is lossless coarsening**: for a statistic with a sufficient kernel, the
reduced model is identifiable iff the full model is (TPE2 §1.6; Halmos–Savage 1949). -/
theorem identifiable_pushforward_iff_of_hasSufficientKernel {P : Θ → Measure 𝓧} {T : 𝓧 → S}
    -- USER-INPUT: T admits a θ-free sufficient kernel (regular-conditional sufficiency);
    -- TPE2 §1.6
    (hT : HasSufficientKernel P T)
    -- LEAN-ONLY: measurability of the statistic — without it `Measure.map T` junk-values
    -- and `HasSufficientKernel` holds vacuously, making the iff false
    (hTm : Measurable T)
    -- USER-INPUT: probability family; TPE2 §1.1
    [∀ θ, IsProbabilityMeasure (P θ)] :
    Identifiable (pushforward P T) ↔ Identifiable P := by
  refine ⟨identifiable_of_pushforward T, fun hP θ₁ θ₂ hEq => ?_⟩
  obtain ⟨Q, _, hgraph⟩ := hT
  have hst : statLaw P T θ₁ = statLaw P T θ₂ := hEq
  exact hP (by rw [eq_comp_statLaw_of_graph hTm hgraph θ₁,
    eq_comp_statLaw_of_graph hTm hgraph θ₂, hst])

/-- Target version: sufficiency preserves target identifiability in both directions. -/
theorem identifiesTarget_pushforward_iff_of_hasSufficientKernel {Γ : Type*}
    {P : Θ → Measure 𝓧} {T : 𝓧 → S} {ψ : Θ → Γ}
    -- USER-INPUT: sufficiency of T; TPE2 §1.6
    (hT : HasSufficientKernel P T)
    -- LEAN-ONLY: measurability of the statistic (see identifiable_pushforward_iff)
    (hTm : Measurable T)
    -- USER-INPUT: probability family; TPE2 §1.1
    [∀ θ, IsProbabilityMeasure (P θ)] :
    IdentifiesTarget (pushforward P T) ψ ↔ IdentifiesTarget P ψ := by
  refine ⟨identifiesTarget_of_pushforward T, fun hP θ₁ θ₂ hEq => ?_⟩
  obtain ⟨Q, _, hgraph⟩ := hT
  have hst : statLaw P T θ₁ = statLaw P T θ₂ := hEq
  exact hP (by rw [eq_comp_statLaw_of_graph hTm hgraph θ₁,
    eq_comp_statLaw_of_graph hTm hgraph θ₂, hst])

end StatLean.StatisticalModels
