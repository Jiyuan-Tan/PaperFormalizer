module
public import StatLean.Bayesian.ForMathlib.PiWithDensity
public import Mathlib.Probability.Kernel.Basic

@[expose] public section

/-!
# The diagonal product kernel `θ ↦ ⊗ⱼ κ(θⱼ)`

For a Markov kernel `κ : Kernel α β` and `J : ℕ`, the **diagonal product kernel** sends a vector
`θ : Fin J → α` to the product measure `⊗ⱼ κ(θ_j)` on `Fin J → β` — the law of `J` independent
observations, the `j`-th drawn from `κ(θ_j)`. Unlike `iidKernel` (which applies the *same*
parameter to every coordinate), each coordinate here uses its own parameter `θ_j`. This is the
data kernel of the hierarchical normal model (`Y_j ∣ θ_j ∼ N(θ_j, σ²)` independently).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §10.2.5 (hierarchical extensions for the normal model), p. 470
(the per-coordinate sampling model of the one-way normal hierarchy).

**Proof formalization notes.** The pinned Mathlib has no `Kernel.pi`; we package `Measure.pi`
directly, exactly as `StatLean.Bayesian.iidKernel` does. Measurability of the coe is the same
π-system induction on boxes (`Measure.measurable_of_measurable_coe`, `Measure.pi_pi`,
`Finset.measurable_prod`), differing from the iid case only in the box step: each factor
`θ ↦ κ (θ j) (u j)` is `κ.measurable_coe` precomposed with the coordinate projection
`measurable_pi_apply j`. Restricted to `[IsMarkovKernel κ]` (all uses are Markov; keeps the
complement step finite). Candidate for upstreaming as the finite homogeneous-index `Kernel.pi`.

**Bibliographic comments.** The diagonal product of a measurable kernel family is the sampling
model behind the one-way random-effects (variance-components) analysis of C. Eisenhart ("The
assumptions underlying the analysis of variance," *Biometrics* 3 (1947), 1–21) and the compound
decision problems of H. Robbins (1951, 1956); it is the likelihood layer of the James–Stein /
empirical-Bayes normal-means problem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]

/-- The map `θ ↦ ⊗ⱼ κ(θⱼ)` is measurable (π-system induction on boxes; box step uses the
coordinate projection `measurable_pi_apply`). -/
theorem measurable_diagKernel_coe (κ : Kernel α β) [IsMarkovKernel κ] (J : ℕ) :
    Measurable fun θ : Fin J → α => Measure.pi fun j => κ (θ j) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  induction s, hs using MeasurableSpace.induction_on_inter with
  | h_eq => exact generateFrom_pi.symm
  | h_inter => exact isPiSystem_pi
  | empty => simp only [measure_empty]; exact measurable_const
  | basic t ht =>
      obtain ⟨u, hu, rfl⟩ := ht
      simp_rw [Measure.pi_pi]
      exact Finset.measurable_prod _ fun i _ =>
        (κ.measurable_coe (hu i (Set.mem_univ i))).comp (measurable_pi_apply i)
  | compl t htm iht =>
      simp_rw [measure_compl htm (measure_ne_top _ _), measure_univ]
      exact iht.const_sub 1
  | iUnion g hgd hgm ihg =>
      simp_rw [measure_iUnion hgd hgm]
      exact Measurable.ennreal_tsum ihg

/-- The **diagonal product kernel** `θ ↦ ⊗ⱼ κ(θⱼ)` on `Fin J → β`: `J` independent observations,
the `j`-th from `κ(θ_j)` (Robert §10.2.5). -/
noncomputable def diagKernel (κ : Kernel α β) [IsMarkovKernel κ] (J : ℕ) :
    Kernel (Fin J → α) (Fin J → β) :=
  ⟨fun θ => Measure.pi fun j => κ (θ j), measurable_diagKernel_coe κ J⟩

@[simp]
theorem diagKernel_apply (κ : Kernel α β) [IsMarkovKernel κ] (J : ℕ) (θ : Fin J → α) :
    diagKernel κ J θ = Measure.pi fun j => κ (θ j) := rfl

instance (κ : Kernel α β) [IsMarkovKernel κ] (J : ℕ) : IsMarkovKernel (diagKernel κ J) :=
  ⟨fun θ => by rw [diagKernel_apply]; infer_instance⟩

/-- Product form on measurable boxes: `diagKernel κ J θ (univ.pi s) = ∏ j, κ (θ j) (s j)`. -/
theorem diagKernel_apply_pi (κ : Kernel α β) [IsMarkovKernel κ] (J : ℕ) (θ : Fin J → α)
    {s : Fin J → Set β} (hs : ∀ j, MeasurableSet (s j)) :
    diagKernel κ J θ (Set.univ.pi s) = ∏ j, κ (θ j) (s j) := by
  rw [diagKernel_apply, Measure.pi_pi]

end StatLean.Bayesian
