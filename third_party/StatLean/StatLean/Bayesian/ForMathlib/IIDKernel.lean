module
public import StatLean.Bayesian.ForMathlib.PiWithDensity
public import Mathlib.Probability.Kernel.Basic

@[expose] public section

/-!
# The iid product kernel `θ ↦ (κ θ)^{⊗ n}`

For a Markov kernel `κ : Kernel Θ 𝓧` and `n : ℕ`, the **iid kernel** sends a parameter `θ` to the
`n`-fold product of `κ θ` on `Fin n → 𝓧` — the law of an iid sample `x₁, …, xₙ` from the model
`f(·|θ)`. The key facts are measurability of `θ ↦ (κ θ)^{⊗ n}` (so the kernel exists), the Markov
property, and the **product-density representation**: if `κ θ = ν.withDensity (p θ)` then
$$\mathrm{iidKernel}\ \kappa\ n\ \theta = \nu^{\otimes n}.\mathrm{withDensity}
  \Big(x \mapsto \prod_i p(\theta, x_i)\Big).$$

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §1.3, p. 6
(iid sampling model).

**Proof formalization notes.** The pinned Mathlib has no `Kernel.pi`; we package `Measure.pi`
directly. Measurability of the coe (`measurable_pi_const_kernel`) is by π-system induction on
boxes (`Measure.measurable_of_measurable_coe`, `Measure.pi_pi`, `Finset.measurable_prod` of
`Kernel.measurable_coe`); the Markov instance is `Measure.pi` of probability measures; the density
representation is `pi_withDensity` from `ForMathlib.PiWithDensity`. Restricted to
`[IsMarkovKernel κ]` (all Bayesian uses are Markov; it keeps the complement step of the induction
finite). Candidate for upstreaming.

**Bibliographic comments.** The iid product experiment is the basic object of sampling theory
since J. Bernoulli's *Ars Conjectandi* (1713); its kernel-parametrized form (a measurable family
of product measures) is the measure-theoretic folklore underlying Ionescu-Tulcea's and
Kolmogorov's constructions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- The map `θ ↦ (κ θ)^{⊗ n}` is measurable (π-system induction on boxes). -/
theorem measurable_pi_const_kernel (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (n : ℕ) :
    Measurable fun θ => Measure.pi fun _ : Fin n => κ θ := by
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

/-- The **iid product kernel** `θ ↦ (κ θ)^{⊗ n}` on `Fin n → 𝓧`: the law of an iid sample of
size `n` from the model `κ θ` (Gelman §1.3). -/
noncomputable def iidKernel (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (n : ℕ) :
    Kernel Θ (Fin n → 𝓧) :=
  ⟨fun θ => Measure.pi fun _ : Fin n => κ θ, measurable_pi_const_kernel κ n⟩

@[simp]
theorem iidKernel_apply (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (n : ℕ) (θ : Θ) :
    iidKernel κ n θ = Measure.pi fun _ : Fin n => κ θ := rfl

instance (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (n : ℕ) : IsMarkovKernel (iidKernel κ n) :=
  ⟨fun θ => by rw [iidKernel_apply]; infer_instance⟩

/-- Product form on measurable boxes:
`iidKernel κ n θ (univ.pi s) = ∏ i, κ θ (s i)`. -/
theorem iidKernel_apply_pi (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (n : ℕ) (θ : Θ)
    -- LEAN-ONLY: box sides are events (regularity)
    {s : Fin n → Set 𝓧} (hs : ∀ i, MeasurableSet (s i)) :
    iidKernel κ n θ (Set.univ.pi s) = ∏ i, κ θ (s i) := by
  rw [iidKernel_apply, Measure.pi_pi]

/-- **Product-density representation of the iid kernel**: a dominated model has iid samples
dominated by the product measure, with the product likelihood as density (Gelman §1.3,
`∏ᵢ f(xᵢ|θ)`). -/
theorem iidKernel_withDensity {κ : Kernel Θ 𝓧} [IsMarkovKernel κ] {ν : Measure 𝓧} [SigmaFinite ν]
    {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model, K(θ, ·) = p(θ, ·) ν; Gelman §1.3
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) (n : ℕ) (θ : Θ) :
    iidKernel κ n θ
      = (Measure.pi fun _ : Fin n => ν).withDensity fun x => ∏ i, p θ (x i) := by
  have hpθ : Measurable (p θ) := hp.comp (measurable_const.prodMk measurable_id)
  haveI : SigmaFinite (ν.withDensity (p θ)) := by rw [← hκ θ]; infer_instance
  rw [iidKernel_apply]
  simp_rw [hκ θ]
  exact pi_withDensity ν (fun _ => hpθ)

/-- Joint measurability of the product likelihood `(θ, x) ↦ ∏ i, p θ (x i)`. -/
theorem measurable_uncurry_prod_likelihood {p : Θ → 𝓧 → ℝ≥0∞} {n : ℕ}
    -- LEAN-ONLY: joint measurability of the one-observation density (regularity)
    (hp : Measurable (Function.uncurry p)) :
    Measurable (Function.uncurry fun (θ : Θ) (x : Fin n → 𝓧) => ∏ i, p θ (x i)) := by
  change Measurable fun z : Θ × (Fin n → 𝓧) => ∏ i, p z.1 (z.2 i)
  exact Finset.measurable_prod _ fun i _ =>
    hp.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

end StatLean.Bayesian
