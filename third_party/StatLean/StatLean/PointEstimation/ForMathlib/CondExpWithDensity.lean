module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# Conditional expectation and determinations of `P(A ∣ T)` under a `T`-measurable tilt

Three bricks relating a statistic `T : 𝓧 → S`, the σ-algebra `MeasurableSpace.comap T` it
generates, and reweighting of the underlying measure by a density that is measurable with
respect to that σ-algebra:

* `map_restrict_eq_withDensity_map` — a θ-free determination `κA` of `P(A ∣ T = ·)` is
  literally a density of the pushed-forward restricted measure: `(μ.restrict A).map T` equals
  `(μ.map T).withDensity κA`. This is the identification that turns the per-event definition
  of sufficiency into a Radon–Nikodym statement on the sample space of the statistic.
* `setLIntegral_comp_withDensity_comap_eq` — **the same** `κA` remains a determination after
  the base measure is tilted by a `T`-measurable density. This is what makes sufficiency a
  property of the *family*: the members of a dominated family differ from one another by
  exactly such tilts once the densities factor through `T`.
* `condExp_withDensity_comap_ae_eq` — the vector-valued counterpart: conditional expectation
  given `σ(T)` is unchanged by a `T`-measurable tilt.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.6
(Sufficient Statistics), supporting material for the factorization criterion: conditional
expectations and determinations of `P(A ∣ T)` under a `T`-measurable tilt. (`TPE2 §1.6`.)

**Proof formalization notes.**
* **Densities are taken in composed form `g ∘ T`.** Every `MeasurableSpace.comap T`-measurable
  function into `ℝ≥0∞` is of this form (the factorization lemma for comap-measurable
  functions), so nothing is lost, while the statements stay first-order and the proofs avoid
  a factorization step in every application. Callers holding an abstract comap-measurable
  density factor it once, at the call site.
* **Route for `map_restrict_eq_withDensity_map`.** Both sides are measures on `S`; test them
  on a measurable `B`. The left side is `μ (A ∩ T ⁻¹' B)` by `Measure.map_apply` and
  `Measure.restrict_apply`, the right side is `∫⁻ x in T ⁻¹' B, κA (T x) ∂μ` by
  `setLIntegral_map` (`withDensity` against a pushforward). The defining property of a
  determination says these agree, and `Measure.ext` closes. No σ-finiteness is needed.
* **Route for `setLIntegral_comp_withDensity_comap_eq`.** Verify first for `g` an indicator
  `Set.indicator B' 1`, where both sides reduce to the defining property at `B ∩ B'`; extend
  by linearity to simple functions and by monotone convergence
  (`lintegral_iSup` / `SimpleFunc.lintegral_eq_lintegral`) to general measurable `g`. No
  finiteness assumption on `g` is required because the whole argument lives in `ℝ≥0∞`.
* **Route for `condExp_withDensity_comap_ae_eq`.** `condExp m μ f` is `m`-measurable and, for
  `m`-measurable `h ≥ 0` with the relevant products integrable, satisfies
  `∫ x in E, condExp m μ f · h ∂μ = ∫ x in E, f · h ∂μ` for `m`-measurable `E`
  ("pulling out what is known"). Taking `h = g ∘ T` and `E = T ⁻¹' B` exhibits `condExp m μ f`
  as a version of the conditional expectation under `μ.withDensity (g ∘ T)`; a.e.-uniqueness
  of conditional expectation gives the conclusion.
* **Regularity carried deliberately.** Two `SigmaFinite (·.trim hT.comap_le)` instances (one
  per measure) are the standing side conditions of Mathlib's `condExp` — without them
  `condExp` is junk-valued `0` and the statement, while still true, would be vacuous.
  A.e.-finiteness of the density `g ∘ T` is likewise genuine regularity, not laundering: the
  conclusion is false for a density that is `∞` on a set of positive measure. Integrability
  of `f` is assumed against **both** measures because neither implies the other and `condExp`
  degenerates to `0` when it fails.

**Bibliographic comments.** Conditional expectation with respect to a σ-algebra, and the
identification of conditional probabilities with Radon–Nikodym derivatives, are due to
A. N. Kolmogorov (*Grundbegriffe der Wahrscheinlichkeitsrechnung*, Springer, 1933, Ch. V);
the systematic development used here, including the "pulling out what is known" identity, is
J. L. Doob's (*Stochastic Processes*, Wiley, 1953, Ch. I).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {𝓧 S : Type*} [MeasurableSpace 𝓧] [mS : MeasurableSpace S]

/-- A θ-free determination `κA` of `P(A ∣ T = ·)` is a density of the pushforward under `T` of
the measure restricted to `A`. -/
theorem map_restrict_eq_withDensity_map
    -- USER-INPUT: the statistic; genuine external data
    {T : 𝓧 → S} (hT : Measurable T)
    -- USER-INPUT: the event whose conditional probability is represented
    {A : Set 𝓧} (hA : MeasurableSet A)
    -- USER-INPUT: the base measure; free choice
    {μ : Measure 𝓧}
    -- USER-INPUT: the candidate determination and its measurability
    {κA : S → ℝ≥0∞} (hκA : Measurable κA)
    -- USER-INPUT: the defining property of a determination of `P(A ∣ T = ·)`
    (hdet : ∀ ⦃B : Set S⦄, MeasurableSet B →
      ∫⁻ x in T ⁻¹' B, κA (T x) ∂μ = μ (A ∩ T ⁻¹' B)) :
    (μ.restrict A).map T = (μ.map T).withDensity κA := by
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply hT hB, Measure.restrict_apply (hT hB),
      withDensity_apply κA hB, setLIntegral_map hB hκA hT, hdet hB, Set.inter_comm]

/-- A determination of `P(A ∣ T = ·)` for `μ` is still a determination after `μ` is tilted by
a density that factors through `T`. -/
theorem setLIntegral_comp_withDensity_comap_eq
    -- USER-INPUT: the statistic; genuine external data
    {T : 𝓧 → S} (hT : Measurable T)
    -- USER-INPUT: the event whose conditional probability is represented
    {A : Set 𝓧} (hA : MeasurableSet A)
    -- USER-INPUT: the base measure; free choice
    {μ : Measure 𝓧}
    -- USER-INPUT: the candidate determination and its measurability
    {κA : S → ℝ≥0∞} (hκA : Measurable κA)
    -- USER-INPUT: the defining property of a determination under the base measure `μ`
    (hdet : ∀ ⦃B : Set S⦄, MeasurableSet B →
      ∫⁻ x in T ⁻¹' B, κA (T x) ∂μ = μ (A ∩ T ⁻¹' B))
    -- USER-INPUT: the tilting density, given in composed form; see the notes above
    {g : S → ℝ≥0∞} (hg : Measurable g)
    -- USER-INPUT: the test cylinder
    ⦃B : Set S⦄ (hB : MeasurableSet B) :
    ∫⁻ x in T ⁻¹' B, κA (T x) ∂(μ.withDensity fun x => g (T x))
      = (μ.withDensity fun x => g (T x)) (A ∩ T ⁻¹' B) := by
  have hgT : Measurable fun x => g (T x) := hg.comp hT
  have hκAT : Measurable fun x => κA (T x) := hκA.comp hT
  have hmap := map_restrict_eq_withDensity_map hT hA hκA hdet
  have key : ∫⁻ x in T ⁻¹' B, g (T x) * κA (T x) ∂μ
      = ∫⁻ x in A ∩ T ⁻¹' B, g (T x) ∂μ := by
    have h : ∫⁻ y in B, g y ∂((μ.restrict A).map T)
        = ∫⁻ y in B, g y ∂((μ.map T).withDensity κA) := by rw [hmap]
    rw [setLIntegral_map hB hg hT, Measure.restrict_restrict (hT hB), Set.inter_comm,
        restrict_withDensity hB, lintegral_withDensity_eq_lintegral_mul _ hκA hg] at h
    simp only [Pi.mul_apply] at h
    rw [setLIntegral_map hB (hκA.fun_mul hg) hT] at h
    rw [h]
    refine lintegral_congr fun x => ?_
    rw [mul_comm]
  rw [withDensity_apply _ (hA.inter (hT hB)), ← key, restrict_withDensity (hT hB),
      lintegral_withDensity_eq_lintegral_mul _ hgT hκAT]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]

/-- Conditional expectation given `σ(T)` is invariant under a tilt by a `T`-measurable
density. -/
theorem condExp_withDensity_comap_ae_eq
    -- USER-INPUT: the statistic; genuine external data
    {T : 𝓧 → S} (hT : Measurable T)
    -- USER-INPUT: the base measure; free choice
    {μ : Measure 𝓧}
    -- USER-INPUT: the tilting density, given in composed form; see the notes above
    {g : S → ℝ≥0∞} (hg : Measurable g)
    -- USER-INPUT: the tilting density is a.e. finite; genuine regularity (false without it)
    (hg_ne_top : ∀ᵐ x ∂μ, g (T x) ≠ ⊤)
    -- USER-INPUT: the integrand
    {f : 𝓧 → ℝ}
    -- USER-INPUT: integrability under the base measure; else `condExp` is junk-valued `0`
    (hf : Integrable f μ)
    -- USER-INPUT: integrability under the tilted measure; neither implies the other
    (hf' : Integrable f (μ.withDensity fun x => g (T x)))
    -- LEAN-ONLY: Mathlib's `condExp` is junk-valued `0` without σ-finiteness of the trim;
    -- carried for the base measure. No scope change: it holds in every application.
    [SigmaFinite (μ.trim hT.comap_le)]
    -- LEAN-ONLY: the same for the tilted measure. No scope change, same reason.
    [SigmaFinite ((μ.withDensity fun x => g (T x)).trim hT.comap_le)] :
    condExp (MeasurableSpace.comap T mS) (μ.withDensity fun x => g (T x)) f
      =ᵐ[(μ.withDensity fun x => g (T x))] condExp (MeasurableSpace.comap T mS) μ f := by
  have hd_meas : Measurable fun x => g (T x) := hg.comp hT
  have hd_lt : ∀ᵐ x ∂μ, g (T x) < ∞ := by
    filter_upwards [hg_ne_top] with x hx using lt_top_iff_ne_top.mpr hx
  -- the density, in composed form, is `σ(T)`-measurable
  have hw_sm : StronglyMeasurable[MeasurableSpace.comap T mS]
      (fun x => (g (T x)).toReal) :=
    (hg.ennreal_toReal.comp (comap_measurable T)).stronglyMeasurable
  -- `w * f` is `μ`-integrable because `f` is integrable against the tilt
  have hwf : Integrable (fun x => (g (T x)).toReal * f x) μ := by
    simpa [smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul' hd_meas hd_lt).mp hf'
  -- pull the `σ(T)`-measurable density out of the conditional expectation
  have hpull := condExp_mul_of_stronglyMeasurable_left hw_sm hwf hf
  have hwc : Integrable
      (fun x => (g (T x)).toReal * (μ[f | MeasurableSpace.comap T mS]) x) μ :=
    integrable_condExp.congr hpull
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap T mS]
      (μ[f | MeasurableSpace.comap T mS]) (μ.withDensity fun x => g (T x)) :=
    StronglyMeasurable.aestronglyMeasurable stronglyMeasurable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq (g := μ[f | MeasurableSpace.comap T mS])
    hT.comap_le hf' ?_ ?_ hgm).symm
  · -- integrability of the candidate on finite-measure `σ(T)`-sets
    intro s hs _
    change Integrable (μ[f | MeasurableSpace.comap T mS])
      ((μ.withDensity fun x => g (T x)).restrict s)
    rw [restrict_withDensity (hT.comap_le s hs),
        integrable_withDensity_iff_integrable_smul' hd_meas (ae_restrict_of_ae hd_lt)]
    simpa [smul_eq_mul] using! hwc.integrableOn
  · -- the set-integral identity, via pull-out and `setIntegral_condExp`
    intro s hs _
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hd_meas
          (ae_restrict_of_ae hd_lt) _ (hT.comap_le s hs),
        setIntegral_withDensity_eq_setIntegral_toReal_smul hd_meas
          (ae_restrict_of_ae hd_lt) _ (hT.comap_le s hs)]
    simp only [smul_eq_mul]
    rw [← setIntegral_condExp hT.comap_le hwf hs]
    refine setIntegral_congr_ae (hT.comap_le s hs) ?_
    filter_upwards [hpull] with x hx _
    exact hx.symm

end StatLean.PointEstimation
