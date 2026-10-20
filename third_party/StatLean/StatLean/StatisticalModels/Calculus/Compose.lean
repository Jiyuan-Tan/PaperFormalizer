module
public import StatLean.StatisticalModels.Calculus.Defs

@[expose] public section

/-!
# Algebra of the model calculus — composition laws and probability preservation

The functoriality laws making `Calculus.Defs` a calculus rather than a list of definitions:
composing observations is observation by the composed kernel; deterministic observation is
pushforward; pushforward is functorial; observation commutes with latent marginalization; and
every operation preserves "the model is a family of *probability* measures" (the instances).

Main statements:

* `observe_observe` — $\kappa\text{-then-}\eta$ observation is observation by `η ∘ₖ κ`
  (composition of coarsening mechanisms, Heitjan–Rubin §2);
* `observe_deterministic` — observation through `Kernel.deterministic T hT` is `pushforward T`
  (deterministic coarsening = transformation);
* `pushforward_pushforward`, `pushforward_id`, `observe_id` — functoriality;
* `observe_mix`, `observe_eq_mix_const`, `mix_deterministic` — interaction of observation and
  latent marginalization;
* `observe_reparam`, `pushforward_reparam` — the calculus commutes with reparameterization
  `P ∘ g` (definitionally);
* `IsProbabilityMeasure` instances for `observe`, `mix`, `condProd`, `iid`, `indepProd`,
  `iidSeq`, and the theorem `isProbabilityMeasure_pushforward`.

**Reference.** Composition of observation channels: L. Le Cam, "Sufficiency and approximate
sufficiency," *Ann. Math. Statist.* **35** (1964), 1419–1455 (transitions compose); coarsening
mechanisms: D. F. Heitjan and D. B. Rubin, "Ignorability and coarse data," *Ann. Statist.*
**19** (1991), §2.

**Proof formalization notes.** Every law is `funext θ` plus one Mathlib brick:
`Measure.comp_assoc` (hypothesis-free) for `observe_observe`, `Kernel.deterministic_comp_eq_map`
for `observe_deterministic`, `Measure.map_map` for `pushforward_pushforward`. The reparam laws
are definitional (`rfl`). Instances follow the `mixPrior` pattern of
`StatLean.Bayesian.Hierarchical.Defs` (`unfold` + `infer_instance` against Mathlib's instances
for `∘ₘ`, `⊗ₘ`, `Measure.pi`, `Measure.infinitePi`).

**Bibliographic comments.** That statistical "experiments" with transition channels form a
category is the starting point of Le Cam's theory of experiments (Le Cam, *Asymptotic Methods
in Statistical Decision Theory*, Springer, 1986, Ch. 1–3); the model calculus here is the
measure-level shadow of that categorical structure.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

variable {Θ Φ : Type*} {𝓧 𝓨 𝓩 : Type*}
  [MeasurableSpace 𝓧] [MeasurableSpace 𝓨] [MeasurableSpace 𝓩]

/-! ## Probability preservation -/

instance isProbabilityMeasure_observe (P : Θ → Measure 𝓧) (κ : Kernel 𝓧 𝓨)
    [∀ θ, IsProbabilityMeasure (P θ)] [IsMarkovKernel κ] (θ : Θ) :
    IsProbabilityMeasure (observe P κ θ) := by
  unfold observe; infer_instance

instance isProbabilityMeasure_mix (P : Θ → Measure 𝓧) (K : Θ → Kernel 𝓧 𝓨)
    [∀ θ, IsProbabilityMeasure (P θ)] [∀ θ, IsMarkovKernel (K θ)] (θ : Θ) :
    IsProbabilityMeasure (mix P K θ) := by
  unfold mix; infer_instance

instance isProbabilityMeasure_condProd (P : Θ → Measure 𝓧) (K : Θ → Kernel 𝓧 𝓨)
    [∀ θ, IsProbabilityMeasure (P θ)] [∀ θ, IsMarkovKernel (K θ)] (θ : Θ) :
    IsProbabilityMeasure (condProd P K θ) := by
  unfold condProd; infer_instance

instance isProbabilityMeasure_iid (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (n : ℕ) (θ : Θ) : IsProbabilityMeasure (iid P n θ) := by
  unfold iid; infer_instance

instance isProbabilityMeasure_indepProd {ι : Type*} [Fintype ι] (P : ι → Θ → Measure 𝓧)
    [∀ i θ, IsProbabilityMeasure (P i θ)] (θ : Θ) :
    IsProbabilityMeasure (indepProd P θ) := by
  unfold indepProd; infer_instance

instance isProbabilityMeasure_iidSeq (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (θ : Θ) : IsProbabilityMeasure (iidSeq P θ) := by
  unfold iidSeq; infer_instance

/-- Pushforward preserves probability (a theorem, not an instance: it needs measurability
of the statistic). -/
theorem isProbabilityMeasure_pushforward (P : Θ → Measure 𝓧) {T : 𝓧 → 𝓨}
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- LEAN-ONLY: measurability of the statistic; standard regularity
    (hT : Measurable T) (θ : Θ) :
    IsProbabilityMeasure (pushforward P T θ) := by
  unfold pushforward
  exact Measure.isProbabilityMeasure_map hT.aemeasurable

/-! ## Composition laws -/

/-- **Observations compose** (Heitjan–Rubin §2): coarsening by `κ` then by `η` is coarsening
by the composed mechanism `η ∘ₖ κ`. -/
theorem observe_observe (P : Θ → Measure 𝓧) (κ : Kernel 𝓧 𝓨) (η : Kernel 𝓨 𝓩) :
    observe (observe P κ) η = observe P (η ∘ₖ κ) := by
  funext θ
  exact Measure.comp_assoc

/-- **Deterministic observation is pushforward**: coarsening through the deterministic kernel
of a measurable map `T` is the model for the statistic `T`. -/
theorem observe_deterministic (P : Θ → Measure 𝓧) {T : 𝓧 → 𝓨}
    -- LEAN-ONLY: measurability of the coarsening map; standard regularity
    (hT : Measurable T) :
    observe P (Kernel.deterministic T hT) = pushforward P T := by
  funext θ
  exact Measure.deterministic_comp_eq_map hT

/-- Observing through the identity mechanism returns the model. -/
theorem observe_id (P : Θ → Measure 𝓧) :
    observe P (Kernel.deterministic id measurable_id) = P := by
  rw [observe_deterministic P measurable_id]
  funext θ
  exact Measure.map_id

/-- Functoriality of `pushforward`. -/
theorem pushforward_pushforward (P : Θ → Measure 𝓧) {T : 𝓧 → 𝓨} {S : 𝓨 → 𝓩}
    -- LEAN-ONLY: measurability of the two statistics; standard regularity
    (hT : Measurable T) (hS : Measurable S) :
    pushforward (pushforward P T) S = pushforward P (S ∘ T) := by
  funext θ
  exact Measure.map_map hS hT

@[simp]
theorem pushforward_id (P : Θ → Measure 𝓧) : pushforward P id = P := by
  funext θ
  exact Measure.map_id

/-- Observation after latent marginalization is latent marginalization with the composed
conditional kernels. -/
theorem observe_mix (P : Θ → Measure 𝓧) (K : Θ → Kernel 𝓧 𝓨) (η : Kernel 𝓨 𝓩) :
    observe (mix P K) η = mix P (fun θ => η ∘ₖ K θ) := by
  funext θ
  exact Measure.comp_assoc

/-- θ-free observation is the constant case of latent marginalization (definitional). -/
theorem observe_eq_mix_const (P : Θ → Measure 𝓧) (κ : Kernel 𝓧 𝓨) :
    observe P κ = mix P (fun _ => κ) := rfl

/-- Latent marginalization through deterministic kernels is θ-wise pushforward. -/
theorem mix_deterministic (P : Θ → Measure 𝓧) {T : Θ → 𝓧 → 𝓨}
    -- LEAN-ONLY: measurability of each map; standard regularity
    (hT : ∀ θ, Measurable (T θ)) :
    mix P (fun θ => Kernel.deterministic (T θ) (hT θ)) = fun θ => (P θ).map (T θ) := by
  funext θ
  exact Measure.deterministic_comp_eq_map (hT θ)

/-- The calculus commutes with reparameterization (definitional): observing a reparameterized
model is the reparameterized observed model. -/
theorem observe_reparam (P : Θ → Measure 𝓧) (κ : Kernel 𝓧 𝓨) (g : Φ → Θ) :
    observe (P ∘ g) κ = (observe P κ) ∘ g := rfl

/-- `pushforward` commutes with reparameterization (definitional). -/
theorem pushforward_reparam (P : Θ → Measure 𝓧) (T : 𝓧 → 𝓨) (g : Φ → Θ) :
    pushforward (P ∘ g) T = (pushforward P T) ∘ g := rfl

end StatLean.StatisticalModels
