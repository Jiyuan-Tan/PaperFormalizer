module
public import StatLean.PointEstimation.Sufficiency.Defs
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-!
# Sufficiency — first consequences of the regular-conditional (kernel) form

This file develops the elementary API of `HasSufficientKernel`, the graph/compProd carrier
of sufficiency fixed in `Sufficiency.Defs`:

* `isProbabilityMeasure_statLaw` — the law of the statistic is a probability measure;
* `isSufficient_of_hasSufficientKernel` — the kernel form implies the per-event form, the
  determination of `P_θ(A ∣ T = t)` being `t ↦ Q t A`;
* `statLaw_snd` — second-marginal (reconstruction) recovery: composing the kernel with the
  law of the statistic returns the original member, `Q ∘ₘ (statLaw P T θ) = P θ`;
* `hasSufficientKernel_fiber` — the kernel is carried by the fibers of `T`:
  `Q t {x | T x = t} = 1` for almost every `t`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.6
(Sufficient Statistics), first consequences of the conditional-distribution definition of
sufficiency. (`TPE2 §1.6`.)

**Proof formalization notes.**
* `statLaw_snd` is stated in the shape dictated by Mathlib's composition API: the relevant
  lemma is `MeasureTheory.Measure.snd_compProd : (μ ⊗ₘ κ).snd = κ ∘ₘ μ`, whose right-hand
  side puts the kernel on the *left* of `∘ₘ`. We therefore state reconstruction as
  `Q ∘ₘ (statLaw P T θ) = P θ` rather than in a `bind`/`∫⁻`-unfolded form; the left side of
  `snd_compProd` is supplied by pushing the graph identity through `Measure.snd`, using
  `snd ∘ (fun x => (T x, x)) = id`.
* `isSufficient_of_hasSufficientKernel` evaluates the graph identity on measurable
  rectangles `B ×ˢ A`: the left side is `P θ (T ⁻¹' B ∩ A)` and the right side is
  `∫⁻ t in B, Q t A ∂(statLaw P T θ)`, which the change of variables for `Measure.map`
  turns into `∫⁻ x in T ⁻¹' B, Q (T x) A ∂(P θ)`. Measurability of `t ↦ Q t A` is
  `Kernel.measurable_coe`, and `Q t A ≤ 1` is the Markov property.
* `hasSufficientKernel_fiber` needs the diagonal `{(t, x) | T x = t} ⊆ S × 𝓧` to be
  measurable; `[StandardBorelSpace S]` supplies `MeasurableSingletonClass S` and countable
  generation, which is what makes that set measurable (via `measurableSet_eq_fun`). The
  fiber statement is the reason the area's carrier is the *graph* compProd form rather than
  the weaker reconstruction identity: reconstruction alone does not pin `Q` to the fibers.

**Bibliographic comments.** Sufficiency and the reconstruction interpretation are due to
R. A. Fisher ("On the mathematical foundations of theoretical statistics," *Phil. Trans. R.
Soc. A* **222** (1922), 309–368). The measure-theoretic treatment of sufficiency for
dominated families, including the passage between per-event determinations and regular
conditional distributions, is due to P. R. Halmos and L. J. Savage ("Application of the
Radon–Nikodym theorem to the theory of sufficient statistics," *Ann. Math. Statist.* **20**
(1949), 225–241); the general decision-theoretic formulation, in which a sufficient
statistic is exactly one admitting a θ-free reconstruction kernel, is due to R. R. Bahadur
("Sufficiency and statistical decision functions," *Ann. Math. Statist.* **25** (1954),
423–462).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- The law of a statistic under a probability member is a probability measure. -/
theorem isProbabilityMeasure_statLaw (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic; needed for `Measure.map` to be the law
    (hT : Measurable T) (θ : Θ) :
    IsProbabilityMeasure (statLaw P T θ) := by
  unfold statLaw
  exact Measure.isProbabilityMeasure_map hT.aemeasurable

/-- **Reconstruction from the statistic.** If the joint law of `(T(X), X)` disintegrates as
`(law of T) ⊗ₘ Q`, then feeding the law of `T` through `Q` returns the law of `X`:
`Q ∘ₘ (statLaw P T θ) = P θ`. This is the "regenerate the data from `T` with a θ-free random
mechanism" statement, and it is the second-marginal shadow of the graph identity. -/
theorem statLaw_snd (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; classical sufficiency input
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q) (θ : Θ) :
    Q ∘ₘ (statLaw P T θ) = P θ := by
  haveI := isProbabilityMeasure_statLaw P hT θ
  have h := congrArg Measure.snd (hgraph θ)
  rw [Measure.snd_compProd, Measure.snd_map_prodMk hT, Measure.map_id'] at h
  exact h.symm

/-- **Kernel form implies the per-event form.** A θ-free Markov disintegration of the graph
law provides, for every measurable `A`, the θ-free determination `t ↦ Q t A` of the
conditional probability `P_θ(A ∣ T = t)`. -/
theorem isSufficient_of_hasSufficientKernel (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T)
    -- USER-INPUT: `T` admits a θ-free reconstruction kernel; the regular-conditional form
    -- of sufficiency
    (h : HasSufficientKernel P T) :
    IsSufficient P T := by
  obtain ⟨Q, hQ, hgraph⟩ := h
  haveI := hQ
  refine fun A hA => ⟨fun t => Q t A, Q.measurable_coe hA, fun t => prob_le_one, ?_⟩
  intro θ B hB
  haveI := isProbabilityMeasure_statLaw P hT θ
  have e := congrArg (· (B ×ˢ A)) (hgraph θ)
  simp only [statLaw] at e
  rw [Measure.map_apply (hT.prodMk measurable_id') (hB.prod hA),
    Measure.compProd_apply_prod hB hA,
    setLIntegral_map hB (Q.measurable_coe hA) hT] at e
  rw [← e]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
  tauto

/-- **The sufficiency kernel is carried by the fibers of `T`.** For almost every value `t` of
the statistic, the reconstruction kernel puts all its mass on `{x | T x = t}`: the regenerated
observation is consistent with the reported value of the statistic. -/
theorem hasSufficientKernel_fiber [StandardBorelSpace S] (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; classical sufficiency input
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q) (θ : Θ) :
    ∀ᵐ t ∂(statLaw P T θ), Q t {x | T x = t} = 1 := by
  haveI := isProbabilityMeasure_statLaw P hT θ
  letI := upgradeStandardBorel S
  have hG : MeasurableSet {p : S × 𝓧 | T p.2 = p.1} :=
    measurableSet_eq_fun (hT.comp measurable_snd) measurable_fst
  have hone : ∫⁻ t, Q t {x | T x = t} ∂(statLaw P T θ) = 1 := by
    have h1 : (statLaw P T θ ⊗ₘ Q) {p : S × 𝓧 | T p.2 = p.1} = 1 := by
      rw [← hgraph θ, Measure.map_apply (hT.prodMk measurable_id') hG]
      have hpre : (fun x => (T x, x)) ⁻¹' {p : S × 𝓧 | T p.2 = p.1} = Set.univ := by
        ext x; simp
      rw [hpre, measure_univ]
    rw [Measure.compProd_apply hG] at h1
    exact h1
  have hle : (fun t => Q t {x | T x = t}) ≤ᵐ[statLaw P T θ] fun _ => 1 :=
    Filter.Eventually.of_forall fun t => prob_le_one
  exact ae_eq_of_ae_le_of_lintegral_le hle (by rw [hone]; exact ENNReal.one_ne_top)
    aemeasurable_const
    (le_of_eq (by rw [lintegral_const, measure_univ, mul_one, hone]))

end StatLean.PointEstimation
