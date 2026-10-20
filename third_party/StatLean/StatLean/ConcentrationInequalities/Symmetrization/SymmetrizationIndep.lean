module
public import StatLean.ConcentrationInequalities.Symmetrization.Symmetrization
public import StatLean.ConcentrationInequalities.ForMathlib.IndepTransport

@[expose] public section

/-!
# Symmetrization with random signs on the sample space (book-faithful form)

The book states Lemma 6.3.2 with Rademacher signs $\varepsilon_i$ that are
random variables on the same probability space, independent of the data
(footnote 7):
$$ \tfrac12\, \mathbb{E}\Bigl\|\sum_i \varepsilon_i X_i\Bigr\|
   \;\le\; \mathbb{E}\Bigl\|\sum_i X_i\Bigr\|
   \;\le\; 2\, \mathbb{E}\Bigl\|\sum_i \varepsilon_i X_i\Bigr\|. $$
This file derives that abstract-$\Omega$ form from the mixed product-space
form of `Symmetrization.lean` by joint-law transport. Joint independence of
$(X, \varepsilon)$ is encoded as **two-block** independence: `iIndepFun ε μ` +
per-index Rademacher marginals + vector-vs-vector `IndepFun` between the data
vector and the sign vector — equivalent to the book's footnote-7 hypothesis
(all that is used is the joint-law factorization) and free of heterogeneous
`Sum`-indexed family ergonomics.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.3, Lemma 6.3.2 and footnote 7.

**Proof formalization notes.** The marginal-law hypothesis is stated as the
pushforward identity `μ.map (ε i) = radLaw` (Mathlib's `HasLaw` is absent at
our pin). `map_signs_eq_signVec` upgrades per-index marginals + independence
to the joint identity `μ.map (fun ω i => ε i ω) = signVec N`; the two public
corollaries then follow from `symmetrization_upper`/`lower` via
`integral_indepFun_eq_integral_prod` (`ForMathlib/IndepTransport`).
Constants `2`, `2` exactly as the book. Named-sorry fallback of this work
item: `symmetrization_lower_of_indepFun` (upper corollary +
`map_signs_eq_signVec` proven).

**Bibliographic comments.** See `Symmetrization.lean`; the observation that
the auxiliary signs may live on any enlargement of the probability space is
classical (Ledoux–Talagrand, *Probability in Banach Spaces*, 1991, §6.1).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Independent per-coordinate Rademacher variables on `Ω` have joint law
`signVec N` (HDP §6.3). -/
-- LEAN-ONLY: joint law of an iid Rademacher vector; transport plumbing.
theorem map_signs_eq_signVec {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    {ε : Fin N → Ω → ℝ}
    -- LEAN-ONLY: measurability of the signs
    (hε_meas : ∀ i, Measurable (ε i))
    -- USER-INPUT: independent signs; HDP §6.3 Lemma 6.3.2
    (hε_indep : iIndepFun ε μ)
    -- USER-INPUT: Rademacher marginals; HDP §6.3
    (hε_law : ∀ i, μ.map (ε i) = radLaw) :
    μ.map (fun ω i => ε i ω) = signVec N := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hε_meas i).aemeasurable)).mp hε_indep]
  unfold signVec
  congr 1
  funext i
  exact hε_law i

/-- **Symmetrization, upper bound, book statement** (HDP §6.3, Lemma 6.3.2):
`E‖∑ Xᵢ‖ ≤ 2 E‖∑ εᵢXᵢ‖` for independent mean-zero data and independent
Rademacher signs living on the same sample space, signs independent of the
data (footnote 7). -/
theorem symmetrization_upper_of_indepFun {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {N : ℕ}
    {X : Fin N → Ω → E} {ε : Fin N → Ω → ℝ}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability (book's E‖Xᵢ‖ < ∞); HDP §6.3 Lemma 6.3.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.3 Lemma 6.3.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent data; HDP §6.3 Lemma 6.3.2
    (hX_indep : iIndepFun X μ)
    -- LEAN-ONLY: measurability of the signs
    (hε_meas : ∀ i, Measurable (ε i))
    -- USER-INPUT: independent signs; HDP §6.3 Lemma 6.3.2
    (hε_indep : iIndepFun ε μ)
    -- USER-INPUT: Rademacher marginals; HDP §6.3
    (hε_law : ∀ i, μ.map (ε i) = radLaw)
    -- USER-INPUT: signs independent of the data; HDP §6.3.2 footnote 7
    (hXε : IndepFun (fun ω i => X i ω) (fun ω i => ε i ω) μ) :
    ∫ ω, ‖∑ i, X i ω‖ ∂μ ≤ 2 * ∫ ω, ‖∑ i, ε i ω • X i ω‖ ∂μ := by
  have hG : AEStronglyMeasurable
      (fun q : (Fin N → E) × (Fin N → ℝ) => ‖∑ i, q.2 i • q.1 i‖)
      ((μ.map (fun ω i => X i ω)).prod (signVec N)) := by
    have hm : Measurable (fun q : (Fin N → E) × (Fin N → ℝ) => ∑ i, q.2 i • q.1 i) := by
      apply Finset.measurable_sum
      intro i _
      exact ((measurable_pi_apply i).comp measurable_snd).smul
        ((measurable_pi_apply i).comp measurable_fst)
    exact hm.aestronglyMeasurable.norm
  have htransport : ∫ ω, ‖∑ i, ε i ω • X i ω‖ ∂μ
      = ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (signVec N)) :=
    integral_indepFun_eq_integral_prod
      (A := fun ω i => X i ω) (B := fun ω i => ε i ω)
      (measurable_pi_lambda _ hX_meas) (measurable_pi_lambda _ hε_meas)
      hXε (map_signs_eq_signVec hε_meas hε_indep hε_law)
      (G := fun q : (Fin N → E) × (Fin N → ℝ) => ‖∑ i, q.2 i • q.1 i‖) hG
  calc ∫ ω, ‖∑ i, X i ω‖ ∂μ
      ≤ 2 * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (signVec N)) :=
        symmetrization_upper hX_meas hX_int hX_mean hX_indep
    _ = 2 * ∫ ω, ‖∑ i, ε i ω • X i ω‖ ∂μ := by rw [htransport]

/-- **Symmetrization, lower bound, book statement** (HDP §6.3, Lemma 6.3.2):
`E‖∑ εᵢXᵢ‖ ≤ 2 E‖∑ Xᵢ‖`. Named-sorry debt candidate of this work item. -/
theorem symmetrization_lower_of_indepFun {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {N : ℕ}
    {X : Fin N → Ω → E} {ε : Fin N → Ω → ℝ}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability; HDP §6.3 Lemma 6.3.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.3 Lemma 6.3.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent data; HDP §6.3 Lemma 6.3.2
    (hX_indep : iIndepFun X μ)
    -- LEAN-ONLY: measurability of the signs
    (hε_meas : ∀ i, Measurable (ε i))
    -- USER-INPUT: independent signs; HDP §6.3 Lemma 6.3.2
    (hε_indep : iIndepFun ε μ)
    -- USER-INPUT: Rademacher marginals; HDP §6.3
    (hε_law : ∀ i, μ.map (ε i) = radLaw)
    -- USER-INPUT: signs independent of the data; HDP §6.3.2 footnote 7
    (hXε : IndepFun (fun ω i => X i ω) (fun ω i => ε i ω) μ) :
    ∫ ω, ‖∑ i, ε i ω • X i ω‖ ∂μ ≤ 2 * ∫ ω, ‖∑ i, X i ω‖ ∂μ := by
  have hG : AEStronglyMeasurable
      (fun q : (Fin N → E) × (Fin N → ℝ) => ‖∑ i, q.2 i • q.1 i‖)
      ((μ.map (fun ω i => X i ω)).prod (signVec N)) := by
    have hm : Measurable (fun q : (Fin N → E) × (Fin N → ℝ) => ∑ i, q.2 i • q.1 i) := by
      apply Finset.measurable_sum
      intro i _
      exact ((measurable_pi_apply i).comp measurable_snd).smul
        ((measurable_pi_apply i).comp measurable_fst)
    exact hm.aestronglyMeasurable.norm
  have htransport : ∫ ω, ‖∑ i, ε i ω • X i ω‖ ∂μ
      = ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (signVec N)) :=
    integral_indepFun_eq_integral_prod
      (A := fun ω i => X i ω) (B := fun ω i => ε i ω)
      (measurable_pi_lambda _ hX_meas) (measurable_pi_lambda _ hε_meas)
      hXε (map_signs_eq_signVec hε_meas hε_indep hε_law)
      (G := fun q : (Fin N → E) × (Fin N → ℝ) => ‖∑ i, q.2 i • q.1 i‖) hG
  calc ∫ ω, ‖∑ i, ε i ω • X i ω‖ ∂μ
      = ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (signVec N)) := htransport
    _ ≤ 2 * ∫ ω, ‖∑ i, X i ω‖ ∂μ :=
        symmetrization_lower hX_meas hX_int hX_mean hX_indep

end StatLean.ConcentrationInequalities
