module
public import StatLean.PointEstimation.Sufficiency.Basic
public import StatLean.Bayesian.Sufficiency.Defs

@[expose] public section

/-!
# Bridging the two carriers of sufficiency

Sufficiency is formalized twice in this library, with different carriers suited to different
uses: a bare family of measures `P : Θ → Measure 𝓧` indexed by an unstructured parameter set,
and a Markov kernel `K : Θ ⇝ 𝓧` (a *statistical experiment*), which is what Bayesian arguments
need in order to build joint laws with a prior. This file records that the kernel-form
notions agree:

* `bayesian_isSufficient_of_hasSufficientKernel` — a θ-free disintegration of the graph law
  of `(T, id)` under every member of an experiment gives the reconstruction factorization
  `K = Q ∘ₖ K_T` of the Bayesian carrier;
* `isFactorizedDensity_of_isFactorizedLikelihood` — the pointwise Fisher–Neyman factorization
  of a likelihood implies the almost-everywhere factorization of the densities.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.6
(Sufficient Statistics), the equivalence of the conditional-distribution and factorization
carriers of sufficiency. (`TPE2 §1.6`.)

**Proof formalization notes.**
* **Import direction.** This is a bridge file and is the one place where the point-estimation
  area reaches into another area's concept layer. It imports the Bayesian *definitions* only,
  and nothing in the Bayesian area imports it back; the direction of the statements is
  "point-estimation hypothesis ⟹ Bayesian conclusion", so no other file in this area needs
  to depend on it.
* The first bridge is the second-marginal identity: taking `Measure.snd` of the graph
  identity turns `(K θ).map (T, id) = ((K θ).map T) ⊗ₘ Q` into `K θ = Q ∘ₘ ((K θ).map T)`
  (`statLaw_snd`), and `(K θ).map T` is exactly the statistic-induced experiment `K_T` of the
  Bayesian carrier evaluated at `θ`; kernel extensionality finishes. So the graph form is
  strictly stronger, as intended: it also pins the kernel to the fibers of `T`, which the
  bare reconstruction identity does not.
* The second bridge is a weakening, from a pointwise equation to a `μ`-a.e. one, and holds
  for an arbitrary reference measure `μ` with no measurability side conditions. The converse
  is false without further hypotheses, and is not stated.
* No claim is made in the reverse direction (Bayesian sufficiency ⟹ the graph form): that
  implication needs a regular-conditional construction and is exactly the content of
  `Sufficiency.RegularConditional`.

**Bibliographic comments.** The reconstruction formulation of sufficiency — a statistic is
sufficient when the data can be regenerated from it by a parameter-free random mechanism — is
due to R. A. Fisher ("On the mathematical foundations of theoretical statistics," *Phil.
Trans. R. Soc. A* **222** (1922), 309–368) and was made precise, in the kernel form used
here, by R. R. Bahadur ("Sufficiency and statistical decision functions," *Ann. Math.
Statist.* **25** (1954), 423–462). The factorization criterion is due to J. Neyman ("Sur un
teorema concernente le cosiddette statistiche sufficienti," *Giorn. Ist. Ital. Attuari* **6**
(1935), 320–334) with the measure-theoretic version of P. R. Halmos and L. J. Savage
("Application of the Radon–Nikodym theorem to the theory of sufficient statistics," *Ann.
Math. Statist.* **20** (1949), 225–241).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- **From the graph form to the Bayesian reconstruction form.** If the experiment `K` admits
a θ-free Markov kernel disintegrating the graph law of `(T, id)` under every parameter value,
then `K` factors through the statistic-induced experiment as `K = Q ∘ₖ K_T`. -/
theorem bayesian_isSufficient_of_hasSufficientKernel (K : Kernel Θ 𝓧) [IsMarkovKernel K]
    {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic; part of the Bayesian carrier's data
    (hT : Measurable T)
    -- USER-INPUT: `T` is sufficient in the regular-conditional (graph) sense
    (h : HasSufficientKernel (⇑K) T) :
    _root_.StatLean.Bayesian.IsSufficient K hT := by
  obtain ⟨Q, hQ, hgraph⟩ := h
  haveI := hQ
  haveI : ∀ θ, IsProbabilityMeasure ((⇑K) θ) := fun θ => inferInstance
  refine ⟨Q, hQ, ?_⟩
  ext θ
  have hsk : StatLean.Bayesian.statKernel K hT θ = statLaw (⇑K) T θ := by
    unfold StatLean.Bayesian.statKernel
    rw [Kernel.deterministic_comp_eq_map hT, Kernel.map_apply K hT]
    rfl
  rw [Kernel.comp_apply, hsk, statLaw_snd (⇑K) hT hgraph θ]

/-- **From a pointwise factorized likelihood to factorized densities.** A pointwise
Fisher–Neyman factorization `p(θ, x) = g(θ, T x) · h(x)` implies the almost-everywhere
factorization used by the point-estimation carrier, for any reference measure. -/
theorem isFactorizedDensity_of_isFactorizedLikelihood (p : Θ → 𝓧 → ℝ≥0∞) (μ : Measure 𝓧)
    (T : 𝓧 → S) (g : Θ → S → ℝ≥0∞) (h : 𝓧 → ℝ≥0∞)
    -- USER-INPUT: the pointwise Fisher–Neyman factorization of the likelihood
    (hfac : _root_.StatLean.Bayesian.IsFactorizedLikelihood p T g h) :
    IsFactorizedDensity p μ T g h := by
  intro θ
  exact ae_of_all μ fun x => hfac θ x

end StatLean.PointEstimation
