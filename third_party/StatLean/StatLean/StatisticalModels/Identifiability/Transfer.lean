module
public import StatLean.StatisticalModels.Identifiability.Defs
public import StatLean.StatisticalModels.Calculus.Marginal
public import StatLean.StatisticalModels.Constraint.Defs

@[expose] public section

/-!
# Identifiability transfer under the model calculus

How identifiability (of the model, and of a target) moves along each operation of the model
calculus. The precise directions matter and are part of the statement:

* engine: `identifiesTarget_of_comp` — any θ-wise post-processing of the laws can only make
  identification *harder*; identification of the processed model transfers back;
* reparameterization `P ∘ g`: forward (`identifiesTarget_comp`; `Identifiable` needs `g`
  injective). The converse is false (a submodel can be identifiable when the model is not);
* `pushforward` / `observe`: **coarsening destroys, never creates** — identification from
  coarsened data implies identification from full data (`identifiesTarget_of_pushforward`,
  `identifiesTarget_of_observe`, and the `Identifiable` corollaries);
* `iid` / `iidSeq`: replication is **lossless** — an iff (`identifiable_iid_iff`, …);
* semiparametric section (`Θ = Ψ × Η`): identified targets restrict to nuisance sections;
* constraint models: `SeparatesTarget` on singleton fibers is exactly `IdentifiesTarget`, and
  separation transfers back from observed constraint models.

**Non-theorem (documented):** `mix` (θ-dependent latent marginalization) admits no general
transfer in either direction — mixture identifiability is genuinely model-specific
(H. Teicher, "Identifiability of mixtures," *Ann. Math. Statist.* **32** (1961), 244–248).

**Reference.** TPE2 §1.5 (identifiability and functions of the parameter); sufficiency as
lossless coarsening is `Adapters.Sufficiency`.

**Proof formalization notes.** The engine lemma is `congrArg`-level; destroy-directions are its
instances at `F = (·.map T)` and `F = (κ ∘ₘ ·)`. The iid iff recovers the marginal via
`Calculus.Marginal.pushforward_iid_eval` (needs `n ≠ 0` — for `n = 0` all parameters give the
same one-point law, so the forward direction genuinely fails; the hypothesis is USER-INPUT,
not plumbing).

**Bibliographic comments.** Koopmans–Reiersøl 1950 (identification); Teicher 1961 (mixtures);
C. F. Manski, *Partial Identification of Probability Distributions* (Springer, 2003) for the
identified-set reading of `SeparatesTarget`.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

open PointEstimation

variable {Θ Φ Γ : Type*} {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/-! ## The engine and the law functional -/

/-- **Engine lemma**: θ-wise post-processing by any `F : Measure 𝓧 → Measure 𝓨` can only make
identification harder; a target identified after processing was identified before. -/
theorem identifiesTarget_of_comp {P : Θ → Measure 𝓧} {ψ : Θ → Γ}
    -- LEAN-ONLY: identifiability certificate being transferred; antecedent, no scope change
    (F : Measure 𝓧 → Measure 𝓨) (h : IdentifiesTarget (fun θ => F (P θ)) ψ) :
    IdentifiesTarget P ψ :=
  fun _ _ hEq => h (congrArg F hEq)

/-- The law functional represents the estimand on the model range. -/
theorem lawFunctional_comp {P : Θ → Measure 𝓧} {ψ : Θ → Γ} [Nonempty Γ]
    -- LEAN-ONLY: identifiability certificate being transferred; antecedent, no scope change
    (h : IdentifiesTarget P ψ) (θ : Θ) :
    lawFunctional P ψ (P θ) = ψ θ :=
  Function.FactorsThrough.extend_apply h _ θ

/-- Conversely, any representation of the estimand as a functional of the law certifies
target identifiability. -/
theorem identifiesTarget_of_rep {P : Θ → Measure 𝓧} {ψ : Θ → Γ} (Ψ : Measure 𝓧 → Γ)
    -- LEAN-ONLY: law-functional representation of the estimand; antecedent, no scope change
    (h : ∀ θ, Ψ (P θ) = ψ θ) : IdentifiesTarget P ψ :=
  fun θ₁ θ₂ hEq => by rw [← h θ₁, ← h θ₂, hEq]

/-- Model identifiability is target identifiability of the identity estimand. -/
theorem identifiable_iff_identifiesTarget_id {P : Θ → Measure 𝓧} :
    Identifiable P ↔ IdentifiesTarget P id := Iff.rfl

/-! ## Reparameterization and restriction (forward only) -/

/-- Identified targets pull back along any reparameterization. The converse is false: a
submodel can identify a target the full model does not. -/
theorem identifiesTarget_comp {P : Θ → Measure 𝓧} {ψ : Θ → Γ} (g : Φ → Θ)
    -- LEAN-ONLY: identifiability certificate being transferred; antecedent, no scope change
    (h : IdentifiesTarget P ψ) : IdentifiesTarget (P ∘ g) (ψ ∘ g) :=
  fun _ _ hEq => h hEq

/-- Identifiability pulls back along injective reparameterizations (in particular along
`Subtype.val`, i.e. restriction to a submodel). -/
theorem identifiable_comp_of_injective {P : Θ → Measure 𝓧} {g : Φ → Θ}
    -- LEAN-ONLY: injectivity of the reparameterization + identifiability certificate being
    -- transferred; antecedents, no scope change
    (hg : Function.Injective g) (h : Identifiable P) : Identifiable (P ∘ g) :=
  fun _ _ hEq => hg (h hEq)

/-- **Semiparametric section**: a target identified on `Θ = Ψ × Η` stays identified on every
nuisance section `η ↦ P (ψ₀, η)` (instance of `identifiesTarget_comp` at `g = (ψ₀, ·)`). -/
theorem identifiesTarget_section {Ψ' Η : Type*} {P : Ψ' × Η → Measure 𝓧} {ψ : Ψ' × Η → Γ}
    -- LEAN-ONLY: identifiability certificate being transferred; antecedent, no scope change
    (h : IdentifiesTarget P ψ) (ψ₀ : Ψ') :
    IdentifiesTarget (fun η => P (ψ₀, η)) (fun η => ψ (ψ₀, η)) :=
  fun _ _ hEq => h hEq

/-! ## Coarsening destroys, never creates -/

/-- A target identified from the law of a statistic was identified from the full data. -/
theorem identifiesTarget_of_pushforward {P : Θ → Measure 𝓧} {ψ : Θ → Γ} (T : 𝓧 → 𝓨)
    -- LEAN-ONLY: identifiability certificate being transferred; antecedent, no scope change
    (h : IdentifiesTarget (pushforward P T) ψ) : IdentifiesTarget P ψ :=
  identifiesTarget_of_comp (fun Q => Q.map T) h

/-- A target identified from data observed through a mechanism `κ` was identified from the
full data. -/
theorem identifiesTarget_of_observe {P : Θ → Measure 𝓧} {ψ : Θ → Γ} (κ : Kernel 𝓧 𝓨)
    -- LEAN-ONLY: identifiability certificate being transferred; antecedent, no scope change
    (h : IdentifiesTarget (observe P κ) ψ) : IdentifiesTarget P ψ :=
  identifiesTarget_of_comp (fun Q => κ ∘ₘ Q) h

/-- Identifiability from the coarsened model implies identifiability from the full model. -/
theorem identifiable_of_pushforward {P : Θ → Measure 𝓧} (T : 𝓧 → 𝓨)
    -- LEAN-ONLY: identifiability certificate being transferred; antecedent, no scope change
    (h : Identifiable (pushforward P T)) : Identifiable P :=
  identifiesTarget_of_comp (fun Q => Q.map T) h

/-- Identifiability from the observed model implies identifiability from the full model. -/
theorem identifiable_of_observe {P : Θ → Measure 𝓧} (κ : Kernel 𝓧 𝓨)
    -- LEAN-ONLY: identifiability certificate being transferred; antecedent, no scope change
    (h : Identifiable (observe P κ)) : Identifiable P :=
  identifiesTarget_of_comp (fun Q => κ ∘ₘ Q) h

/-! ## Replication is lossless -/

/-- **iid replication preserves identifiability — an iff.** -/
theorem identifiable_iid_iff {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)] {n : ℕ}
    -- USER-INPUT: at least one observation; for n = 0 every parameter yields the same
    -- one-point law and the forward direction is false; TPE2 §1.1
    (hn : n ≠ 0) :
    Identifiable (iid P n) ↔ Identifiable P := by
  refine ⟨identifiesTarget_of_comp (fun Q => Measure.pi fun _ : Fin n => Q), fun h θ₁ θ₂ hEq => ?_⟩
  have key := congrFun (pushforward_iid_eval P (⟨0, Nat.pos_of_ne_zero hn⟩ : Fin n))
  exact h ((key θ₁).symm.trans (by rw [pushforward, hEq]; exact key θ₂))

/-- Target version of `identifiable_iid_iff`. -/
theorem identifiesTarget_iid_iff {P : Θ → Measure 𝓧} {ψ : Θ → Γ}
    [∀ θ, IsProbabilityMeasure (P θ)] {n : ℕ}
    -- USER-INPUT: at least one observation; TPE2 §1.1
    (hn : n ≠ 0) :
    IdentifiesTarget (iid P n) ψ ↔ IdentifiesTarget P ψ := by
  refine ⟨identifiesTarget_of_comp (fun Q => Measure.pi fun _ : Fin n => Q), fun h θ₁ θ₂ hEq => ?_⟩
  have key := congrFun (pushforward_iid_eval P (⟨0, Nat.pos_of_ne_zero hn⟩ : Fin n))
  exact h ((key θ₁).symm.trans (by rw [pushforward, hEq]; exact key θ₂))

/-- The infinite-sequence model preserves identifiability — an iff. -/
theorem identifiable_iidSeq_iff {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)] :
    Identifiable (iidSeq P) ↔ Identifiable P := by
  refine ⟨identifiesTarget_of_comp (fun Q => Measure.infinitePi fun _ : ℕ => Q),
    fun h θ₁ θ₂ hEq => ?_⟩
  have key := congrFun (pushforward_iidSeq_eval P 0)
  exact h ((key θ₁).symm.trans (by rw [pushforward, hEq]; exact key θ₂))

/-! ## Constraint models -/

/-- Fully specified models embed: separation on singleton fibers is exactly target
identifiability. -/
theorem separatesTarget_singletonFibers {P : Θ → Measure 𝓧} {ψ : Θ → Γ} :
    SeparatesTarget (singletonFibers P) ψ ↔ IdentifiesTarget P ψ := by
  constructor
  · exact fun h _ _ hEq => h ⟨_, rfl, hEq⟩
  · rintro h θ₁ θ₂ ⟨Q, hQ₁, hQ₂⟩
    exact h (hQ₁.symm.trans hQ₂)

/-- Singleton fibers are feasible. -/
theorem fibersNonempty_singletonFibers (P : Θ → Measure 𝓧) :
    FibersNonempty (singletonFibers P) :=
  fun θ => ⟨P θ, rfl⟩

/-- Separation transfers back from the observed constraint model (image fibers under a
θ-free observation mechanism). -/
theorem separatesTarget_of_observe {C : Θ → Set (Measure 𝓧)} {ψ : Θ → Γ} (κ : Kernel 𝓧 𝓨)
    -- LEAN-ONLY: separation certificate being transferred; antecedent, no scope change
    (h : SeparatesTarget (fun θ => (fun Q => κ ∘ₘ Q) '' C θ) ψ) :
    SeparatesTarget C ψ := by
  rintro θ₁ θ₂ ⟨Q, hQ₁, hQ₂⟩
  exact h ⟨κ ∘ₘ Q, ⟨Q, hQ₁, rfl⟩, ⟨Q, hQ₂, rfl⟩⟩

end StatLean.StatisticalModels
