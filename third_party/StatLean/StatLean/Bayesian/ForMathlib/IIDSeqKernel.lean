module
public import StatLean.Bayesian.ForMathlib.IIDKernel
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Constructions.Cylinders

@[expose] public section

/-!
# The infinite iid product kernel `θ ↦ (κ θ)^{⊗ ℕ}`

For a Markov kernel `κ : Kernel Θ 𝓧`, the **infinite iid kernel** sends a parameter `θ` to the
countable product `Measure.infinitePi (fun _ : ℕ => κ θ)` on `ℕ → 𝓧` — the law of an infinite
iid sample from the model `κ θ`. The pinned Mathlib has `Measure.infinitePi` but no
kernel-valued version; this file supplies it:

* `measurable_pi_fintype_const_kernel` — the finite-product measurability of
  `IIDKernel.lean`, generalized from `Fin n` to an arbitrary `Fintype` index (needed for the
  cylinder step below);
* `measurable_infinitePi_const_kernel` — measurability of `θ ↦ (κ θ)^{⊗ ℕ}`, by π-system
  induction over `measurableCylinders` (`Measure.measurable_of_measurable_coe` +
  `MeasurableSpace.induction_on_inter` with `generateFrom_measurableCylinders`; the basic
  case is `Measure.infinitePi_cylinder` plus the finite-product lemma);
* `iidSeqKernel` — the kernel, with its Markov instance;
* `iidSeqKernel_map_restrict` — restriction to the first `n` coordinates recovers
  `iidKernel κ n` (via `AsymptoticStatistics.pi_const_eq_infinitePi_map`).

This is the sampling model of Doob's consistency theorem (Doob's consistency theorem).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10 (Bayes
Procedures), §10.4 (Consistency), p. 149 (the joint construction of
`(X₁, X₂, …, Θ̄)`).

**Proof formalization notes.** Candidate for upstreaming to Mathlib
(`ProbabilityTheory.Kernel.infinitePi`). The complement step of the cylinder induction uses
that `infinitePi` of probability measures is a probability measure.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- The map `θ ↦ (κ θ)^{⊗ ι'}` is measurable for any `Fintype` index — the
`measurable_pi_const_kernel` argument of `IIDKernel.lean`, index-generalized. -/
theorem measurable_pi_fintype_const_kernel {ι' : Type*} [Fintype ι']
    (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] :
    Measurable fun θ => Measure.pi fun _ : ι' => κ θ := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  induction s, hs using MeasurableSpace.induction_on_inter with
  | h_eq => exact generateFrom_pi.symm
  | h_inter => exact isPiSystem_pi
  | empty => simp only [measure_empty]; exact measurable_const
  | basic t ht =>
      obtain ⟨u, hu, rfl⟩ := ht
      simp_rw [Measure.pi_pi]
      exact Finset.measurable_prod _ fun i _ => κ.measurable_coe (hu i (Set.mem_univ i))
  | compl t htm iht =>
      simp_rw [measure_compl htm (measure_ne_top _ _), measure_univ]
      exact iht.const_sub 1
  | iUnion g hgd hgm ihg =>
      simp_rw [measure_iUnion hgd hgm]
      exact Measurable.ennreal_tsum ihg

/-- The map `θ ↦ (κ θ)^{⊗ ℕ}` (countable iid product) is measurable, by π-system induction
over the measurable cylinders. -/
theorem measurable_infinitePi_const_kernel (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] :
    Measurable fun θ => Measure.infinitePi fun _ : ℕ => κ θ := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  induction s, hs using MeasurableSpace.induction_on_inter with
  | h_eq => exact generateFrom_measurableCylinders.symm
  | h_inter => exact isPiSystem_measurableCylinders
  | empty => simp only [measure_empty]; exact measurable_const
  | basic t ht =>
      obtain ⟨u, S, hS, rfl⟩ := (mem_measurableCylinders t).mp ht
      have hcyl : ∀ θ : Θ, (Measure.infinitePi fun _ : ℕ => κ θ) (cylinder u S)
          = (Measure.pi fun _ : u => κ θ) S := fun θ =>
        Measure.infinitePi_cylinder (fun _ : ℕ => κ θ) hS
      simp_rw [hcyl]
      exact (Measure.measurable_coe hS).comp (measurable_pi_fintype_const_kernel κ)
  | compl t htm iht =>
      simp_rw [measure_compl htm (measure_ne_top _ _), measure_univ]
      exact iht.const_sub 1
  | iUnion g hgd hgm ihg =>
      simp_rw [measure_iUnion hgd hgm]
      exact Measurable.ennreal_tsum ihg

/-- The **infinite iid product kernel** `θ ↦ (κ θ)^{⊗ ℕ}` on `ℕ → 𝓧`: the law of an infinite
iid sample from the model `κ θ` (the sampling model of Doob's consistency theorem). -/
noncomputable def iidSeqKernel (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] : Kernel Θ (ℕ → 𝓧) :=
  ⟨fun θ => Measure.infinitePi fun _ : ℕ => κ θ, measurable_infinitePi_const_kernel κ⟩

@[simp]
theorem iidSeqKernel_apply (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (θ : Θ) :
    iidSeqKernel κ θ = Measure.infinitePi fun _ : ℕ => κ θ := rfl

instance (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] : IsMarkovKernel (iidSeqKernel κ) :=
  ⟨fun θ => by rw [iidSeqKernel_apply]; infer_instance⟩

/-- **Restriction to the first `n` coordinates recovers the finite iid kernel**:
`(iidSeqKernel κ).map (ω ↦ (ω ∘ Fin.val)) = iidKernel κ n`. Pointwise in `θ` this is
`AsymptoticStatistics.pi_const_eq_infinitePi_map`. -/
theorem iidSeqKernel_map_restrict (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (n : ℕ) :
    Kernel.map (iidSeqKernel κ) (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val)
      = iidKernel κ n := by
  have hmeas : Measurable (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  ext θ s hs
  rw [Kernel.map_apply _ hmeas, iidSeqKernel_apply, iidKernel_apply,
    ← AsymptoticStatistics.pi_const_eq_infinitePi_map (κ θ) n]

end StatLean.Bayesian
