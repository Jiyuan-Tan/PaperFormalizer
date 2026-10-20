module
public import StatLean.Bayesian.ForMathlib.IIDKernel
public import Mathlib.Probability.Kernel.Posterior

@[expose] public section

/-!
# Exchangeability and conditional independence

The easy, useful direction of de Finetti: a **conditionally i.i.d.** sample — drawn i.i.d. from
`f(·|θ)` with `θ` itself random — has an **exchangeable** marginal law, and its posterior depends on
the data only through their (permutation-invariant) empirical content. The full de Finetti
representation theorem is postponed (recorded in `roadmap.md`, Batch 4).

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §5.2
(exchangeability and hierarchical models), p. 104.

**Proof formalization notes.** `IsExchangeable` is invariance of the law under coordinate
permutations. `iidKernel_map_perm` is permutation invariance of `Measure.pi` of identical factors
(`Measure.pi` is symmetric under `MeasurableEquiv.piCongrLeft`/coordinate relabelling);
`conditionallyIID_implies_exchangeable` pushes it through the mixing `∘ₘ π` (map commutes with
bind); `posterior_exchangeable_of_exchangeable_hierarchy` transports it to the posterior via the
posterior's uniqueness under the permuted joint.

**Bibliographic comments.** Exchangeability and the representation of an exchangeable sequence as a
mixture of i.i.d. sequences are due to B. de Finetti ("Funzione caratteristica di un fenomeno
aleatorio," *Atti Accad. Naz. Lincei* 4 (1931), 251–299; "La prévision," *Ann. Inst. H. Poincaré*
7 (1937), 1–68); the general (Polish-space) form is E. Hewitt and L. J. Savage (*Trans. Amer. Math.
Soc.* 80 (1955), 470–501). The conditionally-i.i.d. direction formalized here is the "if" half and
the foundation of the Bayesian reading of hierarchical models.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- A law on `Fin n → α` is **exchangeable** if it is invariant under permuting the coordinates
(Gelman §5.2). -/
def IsExchangeable {n : ℕ} {α : Type*} [MeasurableSpace α] (μ : Measure (Fin n → α)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), μ.map (fun x i => x (σ i)) = μ

/-- **Conditional group joint is permutation-invariant** (3B.1): the i.i.d. product law is
symmetric under coordinate permutations. -/
theorem iidKernel_map_perm (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (n : ℕ) (θ : Θ)
    (σ : Equiv.Perm (Fin n)) :
    (iidKernel κ n θ).map (fun x i => x (σ i)) = iidKernel κ n θ := by
  rw [iidKernel_apply]
  have hmeas : Measurable (fun (x : Fin n → 𝓧) i => x (σ i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (σ i))
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun (x : Fin n → 𝓧) i => x (σ i)) ⁻¹' Set.univ.pi s
      = Set.univ.pi (fun i => s (σ.symm i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h i => by have := h (σ.symm i); rwa [σ.apply_symm_apply] at this,
      fun h i => by have := h (σ i); rwa [σ.symm_apply_apply] at this⟩
  rw [hpre, Measure.pi_pi]
  exact Equiv.prod_comp σ.symm (fun i => κ θ (s i))

/-- **Conditionally i.i.d. ⇒ exchangeable** (3B.2): mixing an i.i.d. product over a prior gives an
exchangeable marginal (de Finetti, the easy direction). -/
theorem conditionallyIID_implies_exchangeable (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (n : ℕ)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    IsExchangeable (iidKernel κ n ∘ₘ π) := by
  intro σ
  have hmeas : Measurable (fun (x : Fin n → 𝓧) i => x (σ i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (σ i))
  ext s hs
  rw [Measure.map_apply hmeas hs,
      Measure.bind_apply hs (iidKernel κ n).measurable.aemeasurable,
      Measure.bind_apply (hmeas hs) (iidKernel κ n).measurable.aemeasurable]
  refine lintegral_congr fun θ => ?_
  rw [← Measure.map_apply hmeas hs, iidKernel_map_perm κ n θ σ]

/-- **Posterior is exchangeable** (3B.3): under the conditionally-i.i.d. hierarchy the posterior at
a permuted sample agrees with the posterior at the original sample, for marginal-a.e. data. -/
theorem posterior_exchangeable_of_exchangeable_hierarchy (κ : Kernel Θ 𝓧) [IsMarkovKernel κ]
    (n : ℕ) (π : Measure Θ) [IsProbabilityMeasure π] [StandardBorelSpace Θ] [Nonempty Θ]
    (σ : Equiv.Perm (Fin n)) :
    ∀ᵐ x ∂(iidKernel κ n ∘ₘ π),
      ((iidKernel κ n) † π) (fun i => x (σ i)) = ((iidKernel κ n) † π) x := by
  set κ' := iidKernel κ n with hκ'def
  -- the coordinate permutation as a measurable equivalence on the data space
  let e : (Fin n → 𝓧) ≃ᵐ (Fin n → 𝓧) :=
    { toEquiv :=
        { toFun := fun x i => x (σ i)
          invFun := fun x i => x (σ.symm i)
          left_inv := fun x => funext fun i => by simp only [σ.apply_symm_apply]
          right_inv := fun x => funext fun i => by simp only [σ.symm_apply_apply] }
      measurable_toFun := measurable_pi_lambda _ (fun i => measurable_pi_apply (σ i))
      measurable_invFun := measurable_pi_lambda _ (fun i => measurable_pi_apply (σ.symm i)) }
  have he_map : (κ' ∘ₘ π).map (⇑e) = κ' ∘ₘ π :=
    conditionallyIID_implies_exchangeable κ n π σ
  -- `κ'` is invariant under permuting coordinates (both σ and σ.symm)
  have hκ'e : Kernel.map κ' (⇑e.symm) = κ' := by
    ext θ : 1
    rw [Kernel.map_apply _ e.symm.measurable]
    exact iidKernel_map_perm κ n θ σ.symm
  -- the candidate posterior at permuted data
  let η : Kernel (Fin n → 𝓧) Θ := Kernel.comap (κ'†π) (⇑e) e.measurable
  haveI : IsMarkovKernel η := Kernel.IsMarkovKernel.comap (κ'†π) e.measurable
  -- key: the permuted joint equals the original joint, so `η` is a posterior
  have hstar : (κ' ∘ₘ π) ⊗ₘ η
      = ((κ' ∘ₘ π) ⊗ₘ (κ'†π)).map (Prod.map (⇑e.symm) id) := by
    ext A hA
    rw [Measure.compProd_apply hA,
        Measure.map_apply (e.symm.measurable.prodMap measurable_id) hA]
    have hB : MeasurableSet ((Prod.map (⇑e.symm) id) ⁻¹' A) :=
      (e.symm.measurable.prodMap measurable_id) hA
    rw [Measure.compProd_apply hB]
    -- change of variables x ↦ e x, using invariance of the marginal
    have hFmeas : Measurable fun x =>
        (κ'†π) x (Prod.mk x ⁻¹' ((Prod.map (⇑e.symm) id) ⁻¹' A)) :=
      Kernel.measurable_kernel_prodMk_left hB
    conv_rhs => rw [← he_map]
    rw [lintegral_map hFmeas e.measurable]
    refine lintegral_congr fun x => ?_
    rw [Kernel.comap_apply]
    congr 1
    ext θ
    simp only [Set.mem_preimage, Prod.map_apply, id_eq, e.symm_apply_apply]
  have h : (κ' ∘ₘ π) ⊗ₘ η = (π ⊗ₘ κ').map Prod.swap := by
    rw [hstar, compProd_posterior_eq_map_swap, Measure.map_map
        (e.symm.measurable.prodMap measurable_id) measurable_swap]
    have hcomp : ((Prod.map (⇑e.symm) id) ∘ Prod.swap
        : Θ × (Fin n → 𝓧) → (Fin n → 𝓧) × Θ)
        = Prod.swap ∘ (Prod.map id (⇑e.symm)) := by
      funext p; obtain ⟨θ, x⟩ := p; rfl
    rw [hcomp, ← Measure.map_map measurable_swap (measurable_id.prodMap e.symm.measurable),
        ← Measure.compProd_map e.symm.measurable, hκ'e]
  have hae := ae_eq_posterior_of_compProd_eq (μ := π) (κ := κ') h
  filter_upwards [hae] with x hx
  show η x = (κ'†π) x
  exact hx

end StatLean.Bayesian
