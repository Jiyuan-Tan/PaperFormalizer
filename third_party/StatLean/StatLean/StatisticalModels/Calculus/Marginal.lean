module
public import StatLean.StatisticalModels.Calculus.Compose

@[expose] public section

/-!
# Marginals of composite models

How the replication and conditioning operations of the model calculus project back onto their
ingredients:

* `pushforward_condProd_fst` — the covariate marginal of the regression joint law is the
  covariate model;
* `pushforward_condProd_snd` — **the hinge between regression and latent-variable models**: the
  response marginal of the regression joint law is exactly the latent marginalization `mix P K`;
* `condProd_const` — a covariate-free response kernel gives the independent product;
* `pushforward_iid_eval`, `pushforward_iidSeq_eval` — single-coordinate marginals of iid
  replication recover the base model;
* `iid_pushforward` — replication commutes with per-coordinate transformation;
* `pushforward_iidSeq_window` — finite windows of the infinite iid sequence are the `n`-fold
  iid model;
* `iid_indepProd` — iid replication is the constant case of independent replication.

**Reference.** Joint, marginal and conditional model construction: A. C. Davison, *Statistical
Models*, Cambridge University Press, 2003, Chapter 6 (Stochastic Models) (verify §); the product
experiment: L. Le Cam, *Asymptotic Methods in Statistical Decision Theory*, Springer, 1986,
Ch. 3 (verify §).

**Proof formalization notes.** Each lemma is `funext θ` plus one Mathlib brick:
`Measure.fst_compProd` / `Measure.snd_compProd` for the regression marginals,
`Measure.compProd_const` for the product case, `Measure.pi_map_eval` /
`Measure.infinitePi_map_eval` for coordinate marginals (the probability hypothesis makes the
spectator factors have total mass one), `Measure.pi_map_pi` for `iid_pushforward`. Statements
are phrased through the area's `pushforward` so downstream identifiability transfer applies
verbatim.

**Bibliographic comments.** The observation that the second marginal of a disintegrated joint
law is the mixture of the conditional over the marginal is the measure-theoretic form of the
law of total probability; in the statistical-model reading it identifies regression models
observed without covariates with latent-variable (mixture) models — see B. G. Lindsay, *Mixture
Models* (IMS, 1995), §1 (verify §).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

variable {Θ : Type*} {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/-- The covariate (first) marginal of the regression joint law is the covariate model. -/
theorem pushforward_condProd_fst (P : Θ → Measure 𝓧) (K : Θ → Kernel 𝓧 𝓨)
    -- LEAN-ONLY: s-finiteness of the covariate law (satisfied by probability models);
    -- Markov response kernels are USER-INPUT: the model supplies genuine conditional laws
    [∀ θ, SFinite (P θ)] [∀ θ, IsMarkovKernel (K θ)] :
    pushforward (condProd P K) Prod.fst = P := by
  funext θ
  exact Measure.fst_compProd (P θ) (K θ)

/-- **Regression ↔ latent marginalization**: the response (second) marginal of the regression
joint law is the latent marginalization `mix P K`. This is the hinge identifying mixture /
mixed-effects models with regression models whose covariate is unobserved. -/
theorem pushforward_condProd_snd (P : Θ → Measure 𝓧) (K : Θ → Kernel 𝓧 𝓨)
    -- LEAN-ONLY: s-finiteness of the covariate law (satisfied by probability models)
    [∀ θ, SFinite (P θ)] [∀ θ, IsSFiniteKernel (K θ)] :
    pushforward (condProd P K) Prod.snd = mix P K := by
  funext θ
  exact Measure.snd_compProd (P θ) (K θ)

/-- A covariate-free (constant) response kernel makes the regression joint the independent
product of the two models. -/
theorem condProd_const (P : Θ → Measure 𝓧) (Q : Θ → Measure 𝓨)
    [∀ θ, SFinite (P θ)] [∀ θ, SFinite (Q θ)] :
    condProd P (fun θ => Kernel.const 𝓧 (Q θ)) = fun θ => (P θ).prod (Q θ) := by
  funext θ
  exact Measure.compProd_const

/-- Single-coordinate marginal of the `n`-fold iid model recovers the base model. -/
theorem pushforward_iid_eval (P : Θ → Measure 𝓧)
    -- USER-INPUT: the family consists of probability measures (the spectator coordinates
    -- must carry total mass one); TPE2 §1.1
    [∀ θ, IsProbabilityMeasure (P θ)] {n : ℕ} (i : Fin n) :
    pushforward (iid P n) (Function.eval i) = P := by
  funext θ
  exact (measurePreserving_eval (fun _ : Fin n => P θ) i).map_eq

-- **Batch-0 finding: the probability hypothesis is not decorative.** Mathlib's `Measure.pi`
-- API is σ-finite throughout (`Measure.pi_pi`, `Measure.pi_eq` and `Measure.pi_map_pi` all
-- demand `SigmaFinite`), and `SFinite μ` does not supply `SigmaFinite (μ.map T)`; at the
-- s-finite level only the inequality `≤` is free (the preimage of a `𝓨`-box is a `𝓧`-box of
-- the same price, so every `𝓨`-cover converts, but not conversely). Probability members make
-- `(P θ).map T` a probability measure, which discharges `Measure.pi_map_pi`'s side condition.

/-- Replication commutes with per-coordinate transformation: the iid model of the pushforward
is the coordinatewise pushforward of the iid model. -/
theorem iid_pushforward (P : Θ → Measure 𝓧) {T : 𝓧 → 𝓨}
    -- LEAN-ONLY: measurability of the statistic; probability members (the pin's
    -- `Measure.pi_map_pi` is stated for probability factors)
    (hT : Measurable T) [∀ θ, IsProbabilityMeasure (P θ)] (n : ℕ) :
    iid (pushforward P T) n = pushforward (iid P n) (fun x => T ∘ x) := by
  funext θ
  have : IsProbabilityMeasure ((P θ).map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  exact (Measure.pi_map_pi (fun _ : Fin n => hT.aemeasurable)).symm

/-- Single-coordinate marginal of the infinite iid sequence model recovers the base model. -/
theorem pushforward_iidSeq_eval (P : Θ → Measure 𝓧)
    -- USER-INPUT: probability family; TPE2 §1.1
    [∀ θ, IsProbabilityMeasure (P θ)] (i : ℕ) :
    pushforward (iidSeq P) (Function.eval i) = P := by
  funext θ
  exact Measure.infinitePi_map_eval (fun _ : ℕ => P θ) i

/-- Finite windows of the infinite iid sequence model are the `n`-fold iid model. -/
theorem pushforward_iidSeq_window (P : Θ → Measure 𝓧)
    -- USER-INPUT: probability family; TPE2 §1.1
    [∀ θ, IsProbabilityMeasure (P θ)] (n : ℕ) :
    pushforward (iidSeq P) (fun x (i : Fin n) => x i) = iid P n := by
  classical
  funext θ
  simp only [pushforward, iidSeq, iid]
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : (fun (x : ℕ → 𝓧) (i : Fin n) => x i) ⁻¹' Set.univ.pi s
      = Set.pi ↑(Finset.range n) fun j => if h : j < n then s ⟨j, h⟩ else Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Finset.coe_range,
      Set.mem_Iio]
    refine ⟨fun h j hj => by rw [dif_pos hj]; exact h ⟨j, hj⟩, fun h i => ?_⟩
    have := h i.1 i.2
    rwa [dif_pos i.2, Fin.eta] at this
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs), hpre,
    Measure.infinitePi_pi _ (fun j _ => by split_ifs with h; exacts [hs _, .univ]),
    ← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_congr rfl fun i _ => by rw [dif_pos i.2, Fin.eta]

/-- iid replication is the constant case of independent replication (definitional). -/
theorem iid_indepProd (P : Θ → Measure 𝓧) (n : ℕ) :
    iid P n = indepProd (fun _ : Fin n => P) := rfl

end StatLean.StatisticalModels
