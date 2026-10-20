module
public import StatLean.Bayesian.DoobConsistency.Defs
public import StatLean.Bayesian.DoobConsistency.Basic
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

/-!
# The posterior martingale and Lévy's upward theorem

The martingale half of the proof of Doob's consistency theorem: on the joint space
`Ω = (ℕ → 𝓧) × Θ`, the posterior probabilities `Π(A | X₁..Xₙ)` form a bounded martingale
for the observation filtration, and converge almost surely to the indicator `1_A(Θ̄)` once
the parameter is (a.e.) a measurable function of the data sequence.

* `iSup_comap_data_eq_pi` — the observation σ-algebras generate the product σ-algebra of
  the data sequence: `⨆ n, comap (restrict to first n) = pi`;
* `iSup_doobSigma_eq_comap_fst` — on the joint space, `⨆ n, doobSigma n = comap fst`;
* `doobJoint_map_data_param` — the joint law of `(X₁..Xₙ, Θ̄)` is the swapped
  `π ⊗ₘ iidKernel K n`;
* `condDistrib_doobData_eq_posterior` — the regular conditional distribution of `Θ̄` given
  `X₁..Xₙ` **is** the posterior kernel `(iidKernel K n)†π` (equality of kernels: both are
  `condKernel` of the same measure);
* `posterior_ae_tendsto_indicator` — Lévy's upward convergence of the posterior masses to
  `1_A(Θ̄)`, given a measurable a.e.-retraction of the parameter from the data (display
  the parameter-recovery identity, supplied by `Accessible.lean`).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.4, proof of
Theorem 10.10, pp. 149–150 (the martingale display and (10.11)).

**Proof formalization notes.** Lévy upward is `MeasureTheory.Integrable.tendsto_ae_condExp`
(real-valued, ℕ-filtration); the bridge from the kernel posterior to the conditional
expectation is `ProbabilityTheory.condDistrib_ae_eq_condExp` plus
`condDistrib_doobData_eq_posterior`. The `Filtration` structure over `doobSigma` is
assembled at the point of use from `doobSigma_mono` / `doobSigma_le`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- **The observation σ-algebras generate the sequence σ-algebra**:
`⨆ n, comap (ω ↦ (ω ∘ Fin.val : Fin n → 𝓧)) = MeasurableSpace.pi` on `ℕ → 𝓧`. -/
theorem iSup_comap_data_eq_pi :
    ⨆ n : ℕ, MeasurableSpace.comap
        (fun (ω : ℕ → 𝓧) => (fun i : Fin n => ω i.val)) inferInstance
      = (inferInstance : MeasurableSpace (ℕ → 𝓧)) := by
  have hmeas : ∀ n : ℕ, Measurable (fun (ω : ℕ → 𝓧) => (fun i : Fin n => ω i.val)) :=
    fun n => measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  refine le_antisymm (iSup_le fun n => (hmeas n).comap_le) ?_
  change (⨆ a : ℕ, MeasurableSpace.comap (fun b : ℕ → 𝓧 => b a) m𝓧) ≤ _
  refine iSup_le fun a => ?_
  have hfac : (fun b : ℕ → 𝓧 => b a)
      = (fun x : Fin (a + 1) → 𝓧 => x ⟨a, Nat.lt_succ_self a⟩)
        ∘ (fun ω : ℕ → 𝓧 => fun i : Fin (a + 1) => ω i.val) := rfl
  rw [hfac, ← MeasurableSpace.comap_comp]
  refine le_iSup_of_le (a + 1) ?_
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-- On the joint space, the observation filtration generates exactly the data σ-algebra:
`⨆ n, doobSigma n = comap Prod.fst`. -/
theorem iSup_doobSigma_eq_comap_fst :
    ⨆ n : ℕ, doobSigma (Θ := Θ) (𝓧 := 𝓧) n
      = MeasurableSpace.comap (Prod.fst : (ℕ → 𝓧) × Θ → ℕ → 𝓧) inferInstance := by
  have hfac : ∀ n : ℕ, doobSigma (Θ := Θ) (𝓧 := 𝓧) n
      = MeasurableSpace.comap (Prod.fst : (ℕ → 𝓧) × Θ → ℕ → 𝓧)
          (MeasurableSpace.comap (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) inferInstance) := by
    intro n
    rw [MeasurableSpace.comap_comp]
    rfl
  simp_rw [hfac]
  rw [← MeasurableSpace.comap_iSup, iSup_comap_data_eq_pi]

/-- **The joint law of `(X₁..Xₙ, Θ̄)`** under `doobJoint` is the swapped finite joint
`(π ⊗ₘ iidKernel K n).map Prod.swap`. -/
theorem doobJoint_map_data_param (K : Kernel Θ 𝓧) [IsMarkovKernel K] (π : Measure Θ)
    [IsFiniteMeasure π] (n : ℕ) :
    (doobJoint K π).map (fun ω => (doobData n ω, ω.2))
      = (π ⊗ₘ iidKernel K n).map Prod.swap := by
  have hr : Measurable (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have key : π ⊗ₘ iidKernel K n
      = (π ⊗ₘ iidSeqKernel K).map
          (Prod.map id (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val)) := by
    rw [← iidSeqKernel_map_restrict K n, Measure.compProd_map hr]
  rw [key, doobJoint,
    Measure.map_map ((measurable_doobData n).prodMk measurable_snd) measurable_swap,
    Measure.map_map measurable_swap (measurable_id.prodMap hr)]
  rfl

/-- **The conditional distribution of the parameter given the first `n` observations is the
posterior kernel** — an equality of kernels (both sides are `Measure.condKernel` of the
same measure, by `doobJoint_map_data_param`). -/
theorem condDistrib_doobData_eq_posterior [StandardBorelSpace Θ] [Nonempty Θ]
    (K : Kernel Θ 𝓧) [IsMarkovKernel K] (π : Measure Θ) [IsProbabilityMeasure π] (n : ℕ) :
    condDistrib (Prod.snd : (ℕ → 𝓧) × Θ → Θ) (doobData n) (doobJoint K π)
      = (iidKernel K n)†π := by
  rw [condDistrib, posterior]
  congr 1
  exact doobJoint_map_data_param K π n

/-- **Lévy upward convergence of the posterior masses** (vdV p. 149, the martingale
display): given a measurable a.e.-retraction of the parameter from the data sequence
(the parameter-recovery identity), for every measurable `A ⊆ Θ` the posterior masses converge
`doobJoint`-a.s. to the indicator `1_A(Θ̄)`. -/
theorem posterior_ae_tendsto_indicator [StandardBorelSpace Θ] [Nonempty Θ]
    (K : Kernel Θ 𝓧) [IsMarkovKernel K] (π : Measure Θ) [IsProbabilityMeasure π]
    -- LEAN-ONLY: the parameter-recovery identity — the parameter is a.e. a measurable function of
    -- the
    -- data; supplied by `exists_measurable_retraction` (vdV p. 149)
    (hrec : ∃ g : (ℕ → 𝓧) → Θ, Measurable g ∧
      ∀ᵐ ω ∂(doobJoint K π), g ω.1 = ω.2)
    {A : Set Θ}
    -- LEAN-ONLY: measurable parameter set (regularity)
    (hA : MeasurableSet A) :
    ∀ᵐ ω ∂(doobJoint K π),
      Tendsto (fun n => (((iidKernel K n)†π) (doobData n ω) A).toReal) atTop
        (𝓝 (A.indicator (fun _ => (1 : ℝ)) ω.2)) := by
  classical
  obtain ⟨r, hrmeas, hr⟩ := hrec
  -- the `Prod.fst`-measurable modification of the indicator of the parameter
  let G : ((ℕ → 𝓧) × Θ) → ℝ := fun ω => A.indicator (fun _ => (1 : ℝ)) (r ω.1)
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace ((ℕ → 𝓧) × Θ)) :=
    { seq := doobSigma, mono' := fun _ _ h => doobSigma_mono h, le' := doobSigma_le }
  have hGg : ∀ᵐ ω ∂(doobJoint K π), G ω = A.indicator (fun _ => (1 : ℝ)) ω.2 := by
    filter_upwards [hr] with ω hω
    simp only [G, hω]
  have hGint : Integrable G (doobJoint K π) := by
    have hGeq : G = ((fun ω : (ℕ → 𝓧) × Θ => r ω.1) ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      simp only [G, Set.indicator_apply, Set.mem_preimage]
    rw [hGeq]
    exact (integrable_const _).indicator (hA.preimage (hrmeas.comp measurable_fst))
  have hGsm : StronglyMeasurable[⨆ n, ℱ n] G := by
    have hsup : (⨆ n, (ℱ : ℕ → MeasurableSpace ((ℕ → 𝓧) × Θ)) n)
        = MeasurableSpace.comap (Prod.fst : (ℕ → 𝓧) × Θ → ℕ → 𝓧) inferInstance :=
      iSup_doobSigma_eq_comap_fst
    rw [hsup]
    exact (((measurable_const.indicator hA).comp hrmeas).comp
      (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  -- Lévy's upward theorem for the bounded, `⨆ ℱ`-measurable limit
  have hlevy := hGint.tendsto_ae_condExp (ℱ := ℱ) hGsm
  have hind : Set.indicator ((Prod.snd : (ℕ → 𝓧) × Θ → Θ) ⁻¹' A) (fun _ => (1 : ℝ))
      =ᵐ[doobJoint K π] G := by
    filter_upwards [hGg] with ω hω
    rw [hω]
    simp [Set.indicator_apply]
  -- the posterior masses are versions of the conditional expectations
  have hpost : ∀ n : ℕ,
      (fun ω : (ℕ → 𝓧) × Θ => (((iidKernel K n)†π) (doobData n ω) A).toReal)
        =ᵐ[doobJoint K π] (doobJoint K π)[G | ℱ n] := by
    intro n
    have h1 := condDistrib_ae_eq_condExp (μ := doobJoint K π)
      (Y := (Prod.snd : (ℕ → 𝓧) × Θ → Θ)) (X := doobData n)
      (measurable_doobData n) measurable_snd hA
    rw [condDistrib_doobData_eq_posterior K π n] at h1
    simp only [measureReal_def] at h1
    exact h1.trans (condExp_congr_ae hind)
  filter_upwards [hlevy, hGg, (ae_all_iff (ι := ℕ)).2 hpost] with ω h1 h2 h3
  have hfun : (fun n : ℕ => (((iidKernel K n)†π) (doobData n ω) A).toReal)
      = fun n : ℕ => ((doobJoint K π)[G | ℱ n]) ω := funext h3
  rw [← h2, hfun]
  exact h1

end StatLean.Bayesian
