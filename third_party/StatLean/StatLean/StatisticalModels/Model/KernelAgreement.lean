module
public import StatLean.StatisticalModels.Model.Defs
public import StatLean.StatisticalModels.Calculus.Defs
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-!
# Agreement of the model calculus with Mathlib's kernel algebra

Across the bridge `toKernel` / `⇑κ` of `Model.Defs`, the model-calculus operations of
`Calculus.Defs` are exactly Mathlib's kernel operations:

* `isMarkovKernel_toKernel_iff` — Markov ↔ pointwise probability;
* `observe_coe` — `observe ⇑K κ = ⇑(κ ∘ₖ K)` (observation is kernel composition);
* `pushforward_coe` — `pushforward ⇑K T = ⇑(K.map T)` (pushforward is kernel map);
* `condProd_coe_const` — the regression joint of a kernel model with a θ-free response
  kernel is Mathlib's kernel `compProd` with `prodMkLeft`-lifting;
* `measurable_observe`, `measurable_pushforward` — the operations preserve measurable
  parameterization (so bare families built by the calculus can re-enter kernel land).

Consequently every kernel-side result of the library (Mathlib's decision theory, the Bayesian
area, Minimaxity) transports to models built by the calculus, and conversely.

**Reference.** The kernel presentation of statistical models: L. Le Cam, *Asymptotic Methods
in Statistical Decision Theory*, Springer, 1986, Ch. 1 (verify §); TPE2 §1.1.

**Proof formalization notes.** All proofs are `funext`/`Kernel.ext` plus the defining `apply`
lemmas (`Kernel.comp_apply`, `Kernel.map_apply`, `Kernel.compProd_apply`). Measurability of
`observe P κ` for measurable `P` is free by rewriting through `observe_coe` at
`toKernel P hP` — no bespoke measurability inductions. The exact `⊗ₖ`/`prodMkLeft`
spelling of `condProd_coe_const` is pinned here.

**Bibliographic comments.** That parameterized families and transition kernels are the same
object (given measurability) is folklore of the kernel formulation of statistics; see
N. N. Chentsov, *Statistical Decision Rules and Optimal Inference* (Nauka, 1972) for the
early categorical treatment.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

variable {Θ : Type*} [MeasurableSpace Θ] {𝓧 𝓨 : Type*}
  [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/-- The bundled family is a Markov kernel iff every member is a probability measure. -/
-- LEAN-ONLY: measurability in θ of the family; kernel-side plumbing
theorem isMarkovKernel_toKernel_iff (P : Θ → Measure 𝓧) (hP : Measurable P) :
    IsMarkovKernel (toKernel P hP) ↔ ∀ θ, IsProbabilityMeasure (P θ) :=
  ⟨fun h θ => h.isProbabilityMeasure θ, fun h => ⟨h⟩⟩

/-- **Observation is kernel composition**: on kernel models, `observe` is `∘ₖ`. -/
theorem observe_coe (K : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) :
    observe ⇑K κ = ⇑(κ ∘ₖ K) := by
  funext θ
  exact (Kernel.comp_apply κ K θ).symm

/-- **Pushforward is kernel map**: on kernel models, `pushforward` is `Kernel.map`. -/
theorem pushforward_coe (K : Kernel Θ 𝓧) {T : 𝓧 → 𝓨}
    -- LEAN-ONLY: measurability of the statistic (Kernel.map_apply needs it)
    (hT : Measurable T) :
    pushforward ⇑K T = ⇑(K.map T) := by
  funext θ
  exact (Kernel.map_apply K hT θ).symm

/-- The regression joint with a θ-free response kernel is Mathlib's kernel `compProd`
against the `prodMkLeft` lift. Named Batch-0 spelling-verification item. -/
theorem condProd_coe_const (K : Kernel Θ 𝓧) (η : Kernel 𝓧 𝓨)
    [IsSFiniteKernel K] [IsSFiniteKernel η] :
    condProd ⇑K (fun _ => η) = ⇑(K ⊗ₖ Kernel.prodMkLeft Θ η) := by
  funext θ
  ext s hs
  rw [Kernel.compProd_apply hs]
  simp only [Kernel.prodMkLeft_apply]
  exact Measure.compProd_apply hs

/-- `observe` preserves measurable parameterization. -/
-- LEAN-ONLY: measurability in θ of the family; kernel-side plumbing
theorem measurable_observe {P : Θ → Measure 𝓧} (hP : Measurable P) (κ : Kernel 𝓧 𝓨) :
    Measurable (observe P κ) := by
  have h : observe P κ = ⇑(κ ∘ₖ toKernel P hP) := observe_coe (toKernel P hP) κ
  rw [h]
  exact Kernel.measurable _

/-- `pushforward` preserves measurable parameterization. -/
-- LEAN-ONLY: measurability in θ of the family; kernel-side plumbing
theorem measurable_pushforward {P : Θ → Measure 𝓧} (hP : Measurable P) {T : 𝓧 → 𝓨}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) :
    Measurable (pushforward P T) := by
  have h : pushforward P T = ⇑((toKernel P hP).map T) := pushforward_coe (toKernel P hP) hT
  rw [h]
  exact Kernel.measurable _

end StatLean.StatisticalModels
