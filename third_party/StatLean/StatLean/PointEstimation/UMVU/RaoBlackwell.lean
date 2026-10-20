module
public import StatLean.PointEstimation.UMVU.Defs
public import StatLean.PointEstimation.Sufficiency.Defs
public import StatLean.PointEstimation.Model.Defs
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Rao–Blackwellization: averaging an estimator over the fibers of a sufficient statistic

Given a sufficient statistic `T` with θ-free reconstruction kernel `Q : S ⇝ 𝓧`, any estimator
`δ` can be replaced by its average over the reconstruction fibers,
$$ \eta(t) \;=\; \int \delta(x)\, dQ_t(x), $$
an estimator that reads the data only through `T`. Averaging preserves unbiasedness and can
only decrease the risk, for every loss that is convex in the decision:

* `rbEstimator` — the fiberwise average displayed above;
* `isUnbiased_rbEstimator` — unbiasedness is preserved;
* `risk_rbEstimator_le` — the risk decreases, for every nonnegative convex loss;
* `variance_rbEstimator_le` — the squared-error case.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.7 (Convex
Loss Functions), Theorem 1.7.8 (Rao–Blackwell: conditioning on a sufficient statistic does not
increase the risk for any convex loss). (`TPE2 §1.7 Thm 1.7.8`.)

**Proof formalization notes.**
* **Plain Jensen, not conditional Jensen.** Because the reconstruction kernel is available as
  data, the inequality is proved *pointwise in `t`* by ordinary Jensen's inequality
  (`ConvexOn.map_integral_le`) applied to the probability measure `Q t`, and only then
  integrated against the law of the statistic. No conditional-expectation machinery, no
  conditional Jensen, and no filtration bookkeeping is involved. This is the main reason the
  area's sufficiency carrier is a kernel rather than a σ-field.
* **Fiber integrability is derived, not assumed.** The hypotheses ask only for integrability
  under the members `P θ`. That `δ` (respectively `ρ θ ∘ δ`, respectively `δ²`) is integrable
  against `Q t` for almost every `t` follows from the reconstruction identity
  `Q ∘ₘ (statLaw P T θ) = P θ` together with the fact that an iterated `∫⁻` is finite only if
  its inner integral is finite almost everywhere. Assuming the fiber conditions instead would
  be hypothesis laundering: they are forced by the setup, not free inputs.
* `rbEstimator` is defined by a Bochner integral, hence returns the junk value `0` on fibers
  where `δ` fails to be integrable. Under the hypotheses of the theorems below this happens
  only on a null set of values of the statistic, so the junk never propagates.
* Risks are `ℝ≥0∞`-valued and losses enter through `ENNReal.ofReal`, matching `Model.Defs`.
  The convex loss is required nonnegative, so that `ENNReal.ofReal` loses no information, and
  continuous, which for a convex function on all of `ℝ` is automatic; the hypothesis is kept
  explicit only to avoid importing the convex-continuity machinery, and may be dropped once
  it is available.
* The finite-risk hypothesis `hρi` is a genuine restriction only in appearance: if the risk of
  `δ` is infinite the inequality is trivially true, so the statement could be strengthened by
  case analysis. It is kept because the Jensen step consumes exactly this integrability.

**Bibliographic comments.** The theorem is due to C. R. Rao ("Information and the accuracy
attainable in the estimation of statistical parameters," *Bull. Calcutta Math. Soc.* **37**
(1945), 81–91) and D. Blackwell ("Conditional expectation and unbiased sequential
estimation," *Ann. Math. Statist.* **18** (1947), 105–110); its extension from squared error
to arbitrary convex losses, via Jensen's inequality, is standard and appears in E. L. Lehmann
and H. Scheffé ("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10**
(1950), 305–340). The formulation in terms of a reconstruction kernel rather than a
conditional expectation follows R. R. Bahadur ("Sufficiency and statistical decision
functions," *Ann. Math. Statist.* **25** (1954), 423–462).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- The **Rao–Blackwellized estimator**: the average of `δ` over the reconstruction fiber at
`s`, `η(s) = ∫ δ dQ_s`. Formalizes conditioning an estimator on a sufficient statistic, with
the θ-free reconstruction kernel `Q` supplying the conditional distribution.

Edge behavior: the Bochner integral returns `0` at any `s` where `δ` is not `Q s`-integrable;
under the hypotheses of the theorems in this file, this occurs only on a null set of values of
the statistic. -/
noncomputable def rbEstimator (Q : Kernel S 𝓧) (δ : 𝓧 → ℝ) : S → ℝ :=
  fun s => ∫ x, δ x ∂(Q s)

/-- **Reconstruction identity for the mean.** Averaging over the fibers and then over the law
of the statistic recovers the mean under `P θ`. This is the disintegration `Q ∘ₘ statLaw = P`
read on the integral of `δ`, and it underlies both unbiasedness and the risk bound. -/
private lemma rbEstimator_integral_eq (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {T : 𝓧 → S} (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q) {δ : 𝓧 → ℝ}
    (hδm : Measurable δ) (hδi : ∀ θ, Integrable δ (P θ)) (θ : Θ) :
    ∫ x, rbEstimator Q δ (T x) ∂ P θ = ∫ x, δ x ∂ P θ := by
  haveI : IsProbabilityMeasure (statLaw P T θ) := (P θ).isProbabilityMeasure_map hT.aemeasurable
  have hgm : Measurable (fun x : 𝓧 => (T x, x)) := hT.prodMk measurable_id
  have hδsnd : Measurable (fun z : S × 𝓧 => δ z.2) := hδm.comp measurable_snd
  have hrb : StronglyMeasurable (rbEstimator Q δ) :=
    hδm.stronglyMeasurable.integral_kernel (κ := Q)
  have hInt : Integrable (fun z : S × 𝓧 => δ z.2) (statLaw P T θ ⊗ₘ Q) := by
    rw [← hgraph θ, integrable_map_measure hδsnd.aestronglyMeasurable hgm.aemeasurable]
    exact hδi θ
  calc ∫ x, rbEstimator Q δ (T x) ∂ P θ
      = ∫ t, rbEstimator Q δ t ∂ (statLaw P T θ) :=
        (integral_map hT.aemeasurable hrb.aestronglyMeasurable).symm
    _ = ∫ z, δ z.2 ∂ (statLaw P T θ ⊗ₘ Q) := (Measure.integral_compProd hInt).symm
    _ = ∫ z, δ z.2 ∂ ((P θ).map (fun x => (T x, x))) := by rw [hgraph θ]
    _ = ∫ x, δ x ∂ P θ := integral_map hgm.aemeasurable hδsnd.aestronglyMeasurable

/-- **Fiberwise Jensen transfer.** For a nonnegative convex continuous loss `φ`, the risk of the
Rao–Blackwellized estimator is bounded by that of `δ`, at the level of `ℝ≥0∞` lower integrals.
Fiber integrability is derived from the reconstruction identity, not assumed. -/
private lemma rbEstimator_lintegral_ofReal_le (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S} (hT : Measurable T) {Q : Kernel S 𝓧}
    [IsMarkovKernel Q] (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    {δ : 𝓧 → ℝ} (hδm : Measurable δ) (hδi : ∀ θ, Integrable δ (P θ)) {φ : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ φ) (hcont : Continuous φ) (hnn : ∀ y, 0 ≤ φ y) (θ : Θ)
    (hφi : Integrable (fun x => φ (δ x)) (P θ)) :
    ∫⁻ x, ENNReal.ofReal (φ (rbEstimator Q δ (T x))) ∂ P θ
      ≤ ∫⁻ x, ENNReal.ofReal (φ (δ x)) ∂ P θ := by
  haveI : IsProbabilityMeasure (statLaw P T θ) := (P θ).isProbabilityMeasure_map hT.aemeasurable
  have hgm : Measurable (fun x : 𝓧 => (T x, x)) := hT.prodMk measurable_id
  have hδsnd : Measurable (fun z : S × 𝓧 => δ z.2) := hδm.comp measurable_snd
  have hφδ : Measurable (fun z : S × 𝓧 => φ (δ z.2)) := hcont.measurable.comp hδsnd
  have hrb : StronglyMeasurable (rbEstimator Q δ) :=
    hδm.stronglyMeasurable.integral_kernel (κ := Q)
  -- integrability of `δ ∘ snd` and `φ ∘ δ ∘ snd` over the graph law
  have hδsndInt : Integrable (fun z : S × 𝓧 => δ z.2) (statLaw P T θ ⊗ₘ Q) := by
    rw [← hgraph θ, integrable_map_measure hδsnd.aestronglyMeasurable hgm.aemeasurable]
    exact hδi θ
  have hφInt : Integrable (fun z : S × 𝓧 => φ (δ z.2)) (statLaw P T θ ⊗ₘ Q) := by
    rw [← hgraph θ, integrable_map_measure hφδ.aestronglyMeasurable hgm.aemeasurable]
    exact hφi
  have haeδ : ∀ᵐ t ∂ statLaw P T θ, Integrable (fun x => δ x) (Q t) :=
    ((Measure.integrable_compProd_iff hδsndInt.aestronglyMeasurable).mp hδsndInt).1
  have haeφ : ∀ᵐ t ∂ statLaw P T θ, Integrable (fun x => φ (δ x)) (Q t) :=
    ((Measure.integrable_compProd_iff hφInt.aestronglyMeasurable).mp hφInt).1
  -- rewrite both sides as integrals over the law of the statistic
  have hlhs : ∫⁻ x, ENNReal.ofReal (φ (rbEstimator Q δ (T x))) ∂ P θ
      = ∫⁻ t, ENNReal.ofReal (φ (rbEstimator Q δ t)) ∂ (statLaw P T θ) :=
    (lintegral_map ((hcont.measurable.comp hrb.measurable).ennreal_ofReal) hT (μ := P θ)).symm
  have hrhs : ∫⁻ x, ENNReal.ofReal (φ (δ x)) ∂ P θ
      = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (φ (δ x)) ∂ Q t ∂ (statLaw P T θ) := by
    have e : ∫⁻ z, ENNReal.ofReal (φ (δ z.2)) ∂ ((P θ).map (fun x => (T x, x)))
        = ∫⁻ x, ENNReal.ofReal (φ (δ x)) ∂ P θ :=
      lintegral_map hφδ.ennreal_ofReal hgm
    rw [← e, hgraph θ]
    exact Measure.lintegral_compProd hφδ.ennreal_ofReal
  rw [hlhs, hrhs]
  refine lintegral_mono_ae ?_
  filter_upwards [haeδ, haeφ] with t htδ htφ
  calc ENNReal.ofReal (φ (rbEstimator Q δ t))
      ≤ ENNReal.ofReal (∫ x, φ (δ x) ∂ Q t) :=
        ENNReal.ofReal_le_ofReal (hconv.map_integral_le hcont.continuousOn isClosed_univ
          (Filter.Eventually.of_forall fun _ => Set.mem_univ _) htδ htφ)
    _ = ∫⁻ x, ENNReal.ofReal (φ (δ x)) ∂ Q t :=
        ofReal_integral_eq_lintegral_ofReal htφ (Filter.Eventually.of_forall fun x => hnn (δ x))

/-- **Rao–Blackwellization preserves unbiasedness.** Averaging an unbiased estimator over the
fibers of a sufficient statistic yields an unbiased estimator of the same estimand which
depends on the data only through the statistic. -/
theorem isUnbiased_rbEstimator (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (g : Θ → ℝ) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; classical sufficiency input
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the estimator
    (hδm : Measurable δ)
    -- LEAN-ONLY: integrability under every member; fiber integrability is derived from it
    (hδi : ∀ θ, Integrable δ (P θ))
    -- USER-INPUT: the estimator is unbiased for the estimand
    (hδu : IsUnbiased P g δ) :
    IsUnbiased P g (fun x => rbEstimator Q δ (T x)) := by
  intro θ
  rw [rbEstimator_integral_eq P hT hgraph hδm hδi θ]
  exact hδu θ

/-- **Rao–Blackwellization does not increase the risk**, for any loss that is convex and
nonnegative in the decision argument. -/
theorem risk_rbEstimator_le (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; classical sufficiency input
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the estimator
    (hδm : Measurable δ)
    -- LEAN-ONLY: integrability under every member; fiber integrability is derived from it
    (hδi : ∀ θ, Integrable δ (P θ)) (ρ : Θ → ℝ → ℝ)
    -- USER-INPUT: the loss is convex in the decision argument; the classical hypothesis
    (hconv : ∀ θ, ConvexOn ℝ Set.univ (ρ θ))
    -- LEAN-ONLY: continuity of the loss, automatic for a convex function on all of `ℝ`
    (hcont : ∀ θ, Continuous (ρ θ))
    -- USER-INPUT: the loss is nonnegative, so that `ENNReal.ofReal` loses nothing
    (hnn : ∀ θ y, 0 ≤ ρ θ y)
    -- USER-INPUT: the risk of `δ` is finite (otherwise the inequality is trivial)
    (hρi : ∀ θ, Integrable (fun x => ρ θ (δ x)) (P θ)) (θ : Θ) :
    risk P (fun θ' d => ENNReal.ofReal (ρ θ' d)) (fun x => rbEstimator Q δ (T x)) θ ≤
      risk P (fun θ' d => ENNReal.ofReal (ρ θ' d)) δ θ :=
  rbEstimator_lintegral_ofReal_le P hT hgraph hδm hδi (hconv θ) (hcont θ) (hnn θ) θ (hρi θ)

/-- **Rao–Blackwellization does not increase the variance** — the squared-error case. -/
theorem variance_rbEstimator_le (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; classical sufficiency input
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the estimator
    (hδm : Measurable δ)
    -- USER-INPUT: the estimator lies in the estimator class `Δ`
    (hδ2 : MemEstL2 P δ) (θ : Θ) :
    variance (fun x => rbEstimator Q δ (T x)) (P θ) ≤ variance δ (P θ) := by
  have hδi : ∀ θ', Integrable δ (P θ') := fun θ' => (hδ2 θ').integrable one_le_two
  set m := ∫ x, δ x ∂ P θ with hm
  -- the centered squared-error loss is convex, continuous, nonnegative
  have hconv : ConvexOn ℝ Set.univ (fun y => (y - m) ^ 2) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have hb1 : b = 1 - a := by linarith
    subst hb1
    simp only [smul_eq_mul]
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]
  have hcont : Continuous (fun y => (y - m) ^ 2) := by fun_prop
  have hnn : ∀ y, 0 ≤ (y - m) ^ 2 := fun y => sq_nonneg _
  have hφi : Integrable (fun x => (δ x - m) ^ 2) (P θ) :=
    ((hδ2 θ).sub (memLp_const m)).integrable_sq
  -- the `ℝ≥0∞` Jensen bound instantiated at the centered square
  have hle := rbEstimator_lintegral_ofReal_le P hT hgraph hδm hδi hconv hcont hnn θ hφi
  -- both variances are the centered squared-error integrals (means coincide)
  have hmean : ∫ x, rbEstimator Q δ (T x) ∂ P θ = m :=
    (rbEstimator_integral_eq P hT hgraph hδm hδi θ).trans hm.symm
  have hrbT : Measurable (fun x => rbEstimator Q δ (T x)) :=
    (hδm.stronglyMeasurable.integral_kernel (κ := Q)).measurable.comp hT
  have hRHSint : ∫ x, (δ x - m) ^ 2 ∂ P θ = variance δ (P θ) := by
    rw [variance_eq_integral (hδ2 θ).aemeasurable, ← hm]
  have hLHSint : variance (fun x => rbEstimator Q δ (T x)) (P θ)
      = ∫ x, (rbEstimator Q δ (T x) - m) ^ 2 ∂ P θ := by
    rw [variance_eq_integral hrbT.aemeasurable, hmean]
  -- finiteness of the reference risk, then transport of the `ℝ≥0∞` inequality to `ℝ`
  have hnnae : (0 : 𝓧 → ℝ) ≤ᵐ[P θ] fun x => (δ x - m) ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  have hRne : ∫⁻ x, ENNReal.ofReal ((δ x - m) ^ 2) ∂ P θ ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hφi hnnae]
    exact ENNReal.ofReal_ne_top
  have hInt_lhs : Integrable (fun x => (rbEstimator Q δ (T x) - m) ^ 2) (P θ) :=
    ⟨((hrbT.sub_const m).pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)).mpr
        (lt_of_le_of_lt hle (lt_of_le_of_ne le_top hRne))⟩
  have hvarrb : variance (fun x => rbEstimator Q δ (T x)) (P θ)
      = (∫⁻ x, ENNReal.ofReal ((rbEstimator Q δ (T x) - m) ^ 2) ∂ P θ).toReal := by
    rw [hLHSint, ← ofReal_integral_eq_lintegral_ofReal hInt_lhs
      (Filter.Eventually.of_forall fun x => sq_nonneg _),
      ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg _)]
  have hvarδ : variance δ (P θ)
      = (∫⁻ x, ENNReal.ofReal ((δ x - m) ^ 2) ∂ P θ).toReal := by
    rw [← hRHSint, ← ofReal_integral_eq_lintegral_ofReal hφi
      (Filter.Eventually.of_forall fun x => sq_nonneg _),
      ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg _)]
  rw [hvarrb, hvarδ]
  exact ENNReal.toReal_mono hRne hle

end StatLean.PointEstimation
