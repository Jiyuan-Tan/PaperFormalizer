module
public import StatLean.Bayesian.Decision.BayesEstimator

@[expose] public section

/-!
# The posterior mode (MAP) is the Bayes estimator under 0–1 loss (Robert §2.5.3 / §4.1.2)

On a finite parameter space, under the 0–1 loss `ℓ(θ, a) = 𝟙[θ ≠ a]`, the posterior mode (MAP
estimator) is a Bayes estimator. The mechanism is that the posterior 0–1 risk of action `a` is
`1 − π({a} | x)`, so minimizing it means maximizing the posterior mass.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §2.5.3, eq. (2.5.5)
and Proposition 2.5.7 (0–1 loss picks the most probable hypothesis), p. 81; §4.1.2 (MAP estimator
= posterior mode), p. 166.

**Proof formalization notes.** `lintegral_zeroOneLoss_eq` gives `∫ 𝟙[θ ≠ a] dρ = 1 − ρ{a}` (via
`lintegral_indicator` and `prob_compl_eq_one_sub`); since `1 − ·` is antitone
(`tsub_le_tsub_left`), an a.e. posterior-mass maximizer minimizes posterior 0–1 risk, and
`isBayesEstimator_of_ae_argmin` (our Robert Thm 2.3.2) finishes. Existence uses the choice-free
`fintypeArgmax`, whose measurable-selection lemma `measurable_fintypeArgmax` comes from
`measurable_to_countable'` and the finite Boolean combination of comparison sets (via
`fintypeArgmax_eq_iff`). Parameter space carries `[Fintype Θ] [Nonempty Θ]
[DiscreteMeasurableSpace Θ]`, so `StandardBorelSpace Θ` is automatic.

**Bibliographic comments.** The 0–1 loss is the decision-theoretic formulation of hypothesis
selection, tied to the testing theory of J. Neyman and E. S. Pearson ("On the problem of the most
efficient tests of statistical hypotheses," *Philosophical Transactions of the Royal Society A*
231 (1933), 289–337). That the Bayes rule under 0–1 loss is the *maximum a posteriori* (MAP)
estimator — the posterior mode — is standard; the MAP estimator is also read as penalized maximum
likelihood, and H. Rue ("New loss functions in Bayesian imaging," *J. Amer. Statist. Assoc.* 90
(1995), 900–908) critiques its oversmoothing in high-dimensional image models.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-! ### `fintypeArgmax` API -/

/-- Every value is `≤` the value at the argmax. -/
theorem le_fintypeArgmax [Fintype Θ] [Nonempty Θ] (g : Θ → ℝ≥0∞) (b : Θ) :
    g b ≤ g (fintypeArgmax g) := by
  classical
  have hmem := Finset.min'_mem
    ((Finset.univ.filter fun a => ∀ b, g b ≤ g a).image (Fintype.equivFin Θ))
    (by
      obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
      exact ⟨_, Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ a, fun b => ha b (Finset.mem_univ b)⟩)⟩)
  obtain ⟨a₀, ha₀mem, ha₀eq⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_filter] at ha₀mem
  have hfa : fintypeArgmax g = a₀ := by
    unfold fintypeArgmax
    rw [← ha₀eq, Equiv.symm_apply_apply]
  rw [hfa]
  exact ha₀mem.2 b

/-- Characterization of the argmax: it is a maximizer, and least (in the canonical enumeration)
among maximizers. -/
theorem fintypeArgmax_eq_iff [Fintype Θ] [Nonempty Θ] (g : Θ → ℝ≥0∞) (a : Θ) :
    fintypeArgmax g = a ↔
      (∀ b, g b ≤ g a) ∧ ∀ a', (∀ b, g b ≤ g a') → Fintype.equivFin Θ a ≤ Fintype.equivFin Θ a' := by
  classical
  have hSne : ((Finset.univ.filter fun a => ∀ b, g b ≤ g a).image
      (Fintype.equivFin Θ)).Nonempty := by
    obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
    exact ⟨_, Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ c, fun b => hc b (Finset.mem_univ b)⟩)⟩
  set S := (Finset.univ.filter fun a => ∀ b, g b ≤ g a).image (Fintype.equivFin Θ) with hS
  have hmem_iff : ∀ c, Fintype.equivFin Θ c ∈ S ↔ ∀ b, g b ≤ g c := by
    intro c
    rw [hS, Finset.mem_image]
    refine ⟨?_, fun hc => ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩, rfl⟩⟩
    rintro ⟨d, hd, hde⟩
    rw [Finset.mem_filter] at hd
    have hdc : d = c := (Fintype.equivFin Θ).injective hde
    rw [← hdc]; exact hd.2
  have hfa : Fintype.equivFin Θ (fintypeArgmax g) = S.min' hSne := by
    unfold fintypeArgmax
    rw [Equiv.apply_symm_apply]
  rw [← (Fintype.equivFin Θ).injective.eq_iff, hfa]
  constructor
  · intro hmin
    refine ⟨?_, ?_⟩
    · have haS : Fintype.equivFin Θ a ∈ S := by rw [← hmin]; exact S.min'_mem hSne
      exact (hmem_iff a).mp haS
    · intro a' ha'
      have ha'S : Fintype.equivFin Θ a' ∈ S := (hmem_iff a').mpr ha'
      calc Fintype.equivFin Θ a = S.min' hSne := hmin.symm
        _ ≤ Fintype.equivFin Θ a' := S.min'_le _ ha'S
  · rintro ⟨hmax, hleast⟩
    have haS : Fintype.equivFin Θ a ∈ S := (hmem_iff a).mpr hmax
    have hle1 : S.min' hSne ≤ Fintype.equivFin Θ a := S.min'_le _ haS
    have hec₀ : Fintype.equivFin Θ ((Fintype.equivFin Θ).symm (S.min' hSne)) = S.min' hSne := by
      rw [Equiv.apply_symm_apply]
    have hc₀S : Fintype.equivFin Θ ((Fintype.equivFin Θ).symm (S.min' hSne)) ∈ S := by
      rw [hec₀]; exact S.min'_mem hSne
    have hc₀max : ∀ b, g b ≤ g ((Fintype.equivFin Θ).symm (S.min' hSne)) :=
      (hmem_iff _).mp hc₀S
    have hle2 : Fintype.equivFin Θ a ≤ S.min' hSne := by
      rw [← hec₀]; exact hleast _ hc₀max
    exact le_antisymm hle1 hle2

/-- Measurable selection: an argmax over finitely many measurable `ℝ≥0∞` coordinates is
measurable. -/
theorem measurable_fintypeArgmax [Fintype Θ] [Nonempty Θ] [DiscreteMeasurableSpace Θ]
    {g : 𝓧 → Θ → ℝ≥0∞}
    -- LEAN-ONLY: each coordinate is measurable (regularity)
    (hg : ∀ a, Measurable fun x => g x a) :
    Measurable fun x => fintypeArgmax (g x) := by
  classical
  apply measurable_to_countable'
  intro a
  have hset : (fun x => fintypeArgmax (g x)) ⁻¹' {a}
      = (⋂ b, {x | g x b ≤ g x a}) ∩
        (⋂ a', {x | (∀ b, g x b ≤ g x a') →
          Fintype.equivFin Θ a ≤ Fintype.equivFin Θ a'}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq]
    rw [fintypeArgmax_eq_iff]
  rw [hset]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter fun b => measurableSet_le (hg b) (hg a)
  · refine MeasurableSet.iInter fun a' => ?_
    by_cases h : Fintype.equivFin Θ a ≤ Fintype.equivFin Θ a'
    · have hset' : {x | (∀ b, g x b ≤ g x a') →
          Fintype.equivFin Θ a ≤ Fintype.equivFin Θ a'} = Set.univ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact fun _ => h
      rw [hset']; exact MeasurableSet.univ
    · have hset' : {x | (∀ b, g x b ≤ g x a') →
          Fintype.equivFin Θ a ≤ Fintype.equivFin Θ a'} = (⋂ b, {x | g x b ≤ g x a'})ᶜ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iInter]
        exact ⟨fun himp hall => h (himp hall), fun hnot hall => absurd hall hnot⟩
      rw [hset']
      exact (MeasurableSet.iInter fun b => measurableSet_le (hg b) (hg a')).compl

/-! ### Posterior 0–1 risk and the MAP estimator -/

/-- The 0–1 loss is jointly measurable on a countable parameter space. -/
theorem measurable_uncurry_zeroOneLoss [Countable Θ] [MeasurableSingletonClass Θ] :
    Measurable (Function.uncurry (zeroOneLoss (α := Θ))) := by
  classical
  have h : Function.uncurry (zeroOneLoss (α := Θ))
      = fun p : Θ × Θ => if p.1 = p.2 then (0 : ℝ≥0∞) else 1 := by
    funext p; rfl
  rw [h]
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd)
    measurable_const measurable_const

/-- Posterior 0–1 risk is one minus the posterior mass: `∫ 𝟙[θ ≠ a] dρ = 1 − ρ{a}`
(Robert §2.5.3, the mechanism of Proposition 2.5.7). -/
theorem lintegral_zeroOneLoss_eq [MeasurableSingletonClass Θ]
    (ρ : Measure Θ) [IsProbabilityMeasure ρ] (a : Θ) :
    ∫⁻ θ, zeroOneLoss θ a ∂ρ = 1 - ρ {a} := by
  classical
  have hfun : (fun θ => zeroOneLoss θ a)
      = Set.indicator ({a}ᶜ : Set Θ) (fun _ => (1 : ℝ≥0∞)) := by
    funext θ
    rw [Set.indicator_apply]
    simp only [zeroOneLoss, Set.mem_compl_iff, Set.mem_singleton_iff]
    by_cases h : θ = a <;> simp [h]
  rw [hfun, lintegral_indicator (measurableSet_singleton a).compl, lintegral_const, one_mul,
    Measure.restrict_apply_univ, prob_compl_eq_one_sub (measurableSet_singleton a)]

/-- The posterior mode is measurable. -/
theorem measurable_posteriorMode [Fintype Θ] [Nonempty Θ] [DiscreteMeasurableSpace Θ]
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    Measurable (posteriorMode P π) := by
  unfold posteriorMode
  exact measurable_fintypeArgmax
    (fun a => Kernel.measurable_coe (P†π) (measurableSet_singleton a))

/-- Any measurable a.e.-maximizer of the posterior mass is a Bayes estimator under 0–1 loss
(the criterion behind Robert Proposition 2.5.7). -/
theorem isBayesEstimator_of_ae_argmax_posterior [Fintype Θ] [Nonempty Θ]
    [DiscreteMeasurableSpace Θ]
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π]
    -- LEAN-ONLY: the estimator is measurable
    {δ : 𝓧 → Θ} (hδ : Measurable δ)
    -- USER-INPUT: `δ(x)` maximizes the posterior mass for predictive-a.e. `x`; Robert Prop. 2.5.7
    (hmax : ∀ᵐ x ∂(P ∘ₘ π), ∀ b, (P†π) x {b} ≤ (P†π) x {δ x}) :
    IsBayesEstimator zeroOneLoss P (Kernel.deterministic δ hδ) π := by
  refine isBayesEstimator_of_ae_argmin zeroOneLoss measurable_uncurry_zeroOneLoss P π hδ ?_
  filter_upwards [hmax] with x hx
  intro y
  rw [lintegral_zeroOneLoss_eq ((P†π) x) (δ x), lintegral_zeroOneLoss_eq ((P†π) x) y]
  exact tsub_le_tsub_left (hx y) 1

/-- **The posterior mode (MAP) is a Bayes estimator under 0–1 loss** on a finite parameter space
(Robert Proposition 2.5.7 / §4.1.2). -/
theorem posteriorMode_isBayesEstimator_zeroOneLoss [Fintype Θ] [Nonempty Θ]
    [DiscreteMeasurableSpace Θ]
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    IsBayesEstimator zeroOneLoss P
      (Kernel.deterministic (posteriorMode P π) (measurable_posteriorMode P π)) π := by
  refine isBayesEstimator_of_ae_argmax_posterior P π (measurable_posteriorMode P π)
    (ae_of_all _ fun x b => ?_)
  exact le_fintypeArgmax (fun a => (P†π) x {a}) b

end StatLean.Bayesian
