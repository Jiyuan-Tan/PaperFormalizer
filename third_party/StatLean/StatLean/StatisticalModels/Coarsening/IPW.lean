module
public import StatLean.StatisticalModels.Coarsening.Basic
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-!
# Inverse-probability weighting — the Horvitz–Thompson identity under MAR

**Headline (C3).** Under a MAR mechanism with uniform positivity, the inverse-propensity-
weighted observed outcome has the full-data mean:
$$\mathbb E_{\text{obs}}\Big[\frac{R\,Y}{\pi(X)}\Big] = \mathbb E_Q[Y].$$
This is exactly the identification statement that the semiparametric example
`AsymptoticStatistics.Examples.MARMean` *assumes* of its estimand `marMean_Ψ` ("supplied
separately by the caller") — supplied here at the model level; the agreement lemma with
`marMean_Ψ` lands in `Coarsening.Ignorability` (batch C-B2) after the observed-carrier
transport.

**Reference.** D. G. Horvitz and D. J. Thompson, "A generalization of sampling without
replacement from a finite universe," *J. Amer. Statist. Assoc.* **47** (1952), 663–685
(the inverse-inclusion-probability estimator) (`HT52`); J. M. Robins, A. Rotnitzky, and
L. P. Zhao, "Estimation of regression coefficients when some regressors are not always
observed," *J. Amer. Statist. Assoc.* **89** (1994), 846–866, §2 (IPW under MAR); van der
Vaart, *Asymptotic Statistics*, CUP 1998, §25.5.3, Example 25.43 (`vdV §25.5.3`).

**Proof formalization notes.** Pushforward unfolding (`integral_map` along `missingObserve`
— the integrand composed with the coarsening map depends only on the full datum), then
`MeasureTheory.integral_compProd` over `Q ⊗ₘ ρ'` and the two-point Bool integral: the inner
integral is `π(x)·(y/π(x)) + 0 = y` under positivity. Integrability side conditions come from
`‖R·Y/π(X)‖ ≤ ‖Y‖/δ`.

**Bibliographic comments.** The IPW identity is the measure-theoretic core of
Horvitz–Thompson (1952) survey estimation, imported to missing-data problems by
Robins–Rotnitzky–Zhao (1994); positivity/overlap as an explicit hypothesis is emphasized
throughout the modern causal-inference literature (Rosenbaum–Rubin 1983).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.StatisticalModels.Coarsening

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The IPW integrand on the observed carrier: `(x, r, ry) ↦ r · ry / π(x)`. -/
noncomputable def ipwIntegrand (ρ' : Kernel 𝓧 Bool) (o : 𝓧 × Bool × ℝ) : ℝ :=
  ind o.2.1 * o.2.2 / propensity ρ' o.1

/-- The IPW integrand is bounded by the outcome over the overlap constant along the
coarsening map (the integrability workhorse). -/
theorem abs_ipwIntegrand_comp_le (ρ' : Kernel 𝓧 Bool) {δ : ℝ}
    -- USER-INPUT: uniform positivity (overlap), δ > 0; Rosenbaum–Rubin 1983
    (hδ : 0 < δ) (hpos : HasPositivity ρ' δ) (p : 𝓧 × ℝ × Bool) :
    |ipwIntegrand ρ' (missingObserve p)| ≤ |p.2.1| / δ := by
  have hπ : 0 < propensity ρ' p.1 := lt_of_lt_of_le hδ (hpos p.1)
  cases hr : p.2.2 with
  | false =>
      have h0 : ipwIntegrand ρ' (missingObserve p) = 0 := by
        change ind p.2.2 * (if p.2.2 then p.2.1 else 0) / propensity ρ' p.1 = 0
        rw [hr]; simp [ind]
      rw [h0, abs_zero]
      exact div_nonneg (abs_nonneg _) hδ.le
  | true =>
      simp only [ipwIntegrand, missingObserve, ind, hr, if_true, one_mul, abs_div,
        abs_of_pos hπ]
      gcongr
      exact hpos p.1

/-- The propensity is a measurable function of the covariate. -/
private theorem measurable_propensity (ρ' : Kernel 𝓧 Bool) : Measurable (propensity ρ') :=
  (Kernel.measurable_coe ρ' (measurableSet_singleton true)).ennreal_toReal

/-- The IPW integrand is measurable on the observed carrier. -/
private theorem measurable_ipwIntegrand (ρ' : Kernel 𝓧 Bool) :
    Measurable (ipwIntegrand ρ') :=
  (((measurable_of_countable ind).comp measurable_snd.fst).mul measurable_snd.snd).div
    ((measurable_propensity ρ').comp measurable_fst)

/-- The full-data reassociation `((x, y), r) ↦ (x, y, r)` is measurable. -/
private theorem measurable_fullAssoc :
    Measurable fun q : (𝓧 × ℝ) × Bool => (q.1.1, q.1.2, q.2) :=
  measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)

/-- **C3, the Horvitz–Thompson identity under MAR** (`HT52`; Robins–Rotnitzky–Zhao 1994 §2;
`vdV §25.5.3` Example 25.43): under a MAR mechanism with uniform positivity, the
inverse-propensity-weighted observed outcome recovers the full-data outcome mean. -/
theorem ipw_identity (Q : Measure (𝓧 × ℝ)) [IsProbabilityMeasure Q]
    (ρ' : Kernel 𝓧 Bool) [IsMarkovKernel ρ'] {δ : ℝ}
    -- USER-INPUT: uniform positivity (overlap), δ > 0; Rosenbaum–Rubin 1983
    (hδ : 0 < δ) (hpos : HasPositivity ρ' δ)
    -- USER-INPUT: integrable outcome; HT52
    (hY : Integrable (fun p : 𝓧 × ℝ => p.2) Q) :
    ∫ o, ipwIntegrand ρ' o ∂(observedLaw Q (ρ'.comap Prod.fst measurable_fst))
      = ∫ p, p.2 ∂Q := by
  have hπ : ∀ x, propensity ρ' x ≠ 0 := fun x => ne_of_gt (lt_of_lt_of_le hδ (hpos x))
  have hcomp : Measurable fun q : (𝓧 × ℝ) × Bool => missingObserve (q.1.1, q.1.2, q.2) :=
    measurable_missingObserve.comp measurable_fullAssoc
  -- the observed law is a single pushforward of `Q ⊗ₘ ρ'`
  have hmapeq : observedLaw Q (ρ'.comap Prod.fst measurable_fst)
      = (Q ⊗ₘ ρ'.comap Prod.fst measurable_fst).map
        fun q : (𝓧 × ℝ) × Bool => missingObserve (q.1.1, q.1.2, q.2) := by
    rw [observedLaw, fullLaw, Measure.map_map measurable_missingObserve measurable_fullAssoc]
    rfl
  rw [hmapeq, integral_map hcomp.aemeasurable (measurable_ipwIntegrand ρ').aestronglyMeasurable]
  -- integrability from the `|y|/δ` envelope
  have hdom : Integrable
      (fun q : (𝓧 × ℝ) × Bool => |q.1.2| / δ) (Q ⊗ₘ ρ'.comap Prod.fst measurable_fst) := by
    have h1 : Integrable (fun p : 𝓧 × ℝ => |p.2| / δ) Q := hY.abs.div_const δ
    have hfst : (Q ⊗ₘ ρ'.comap Prod.fst measurable_fst).map Prod.fst = Q :=
      Measure.fst_compProd Q _
    exact (integrable_map_measure (by rw [hfst]; exact h1.aestronglyMeasurable)
      measurable_fst.aemeasurable).mp (by rw [hfst]; exact h1)
  have hint : Integrable (fun q : (𝓧 × ℝ) × Bool =>
      ipwIntegrand ρ' (missingObserve (q.1.1, q.1.2, q.2)))
      (Q ⊗ₘ ρ'.comap Prod.fst measurable_fst) := by
    refine hdom.mono' ((measurable_ipwIntegrand ρ').comp hcomp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    simpa using abs_ipwIntegrand_comp_le ρ' hδ hpos (q.1.1, q.1.2, q.2)
  rw [Measure.integral_compProd hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have hne : propensity ρ' p.1 ≠ 0 := hπ p.1
  change ∫ b, ipwIntegrand ρ' (missingObserve ((p, b).1.1, (p, b).1.2, (p, b).2))
      ∂(ρ' p.1) = p.2
  rw [integral_bool]
  change propensity ρ' p.1 * (1 * p.2 / propensity ρ' p.1)
      + (ρ' p.1 {false}).toReal * (0 * 0 / propensity ρ' p.1) = p.2
  field_simp
  ring

end StatLean.StatisticalModels.Coarsening
