module
public import StatLean.PointEstimation.UMVU.RaoBlackwell
public import StatLean.PointEstimation.UMVU.Basic
public import StatLean.PointEstimation.UMVU.CovarianceCriterion
public import StatLean.PointEstimation.Sufficiency.Basic
public import StatLean.PointEstimation.Completeness.Defs
public import StatLean.PointEstimation.Completeness.ExpFamily
public import StatLean.PointEstimation.ExponentialFamily.Defs
public import StatLean.PointEstimation.ExponentialFamily.Basic
public import StatLean.PointEstimation.Sufficiency.Factorization
public import StatLean.PointEstimation.Sufficiency.RegularConditional
public import Mathlib.Probability.CondVar

@[expose] public section

/-!
# The Lehmann–Scheffé theorem

Rao–Blackwellization improves any estimator by averaging it over the fibers of a sufficient
statistic, but leaves open which function of the statistic to use. Completeness settles this:
a complete sufficient statistic admits *at most one* unbiased function, so all
Rao–Blackwellized estimators of the same estimand coincide, and the common value is
simultaneously optimal — not only for squared error, but for every convex loss.

* `unique_unbiased_function_of_complete` — at most one unbiased function of a complete
  statistic;
* `isUMVU_of_complete_sufficient` — the Rao–Blackwellization of any unbiased square-integrable
  estimator along a complete sufficient statistic is UMVU;
* `risk_le_of_complete_sufficient` — the same estimator minimizes the risk among all unbiased
  estimators, for every nonnegative convex loss;
* `isUMVU_of_fullRank_expFamily` — the specialization to a full-rank exponential family, whose
  natural statistic is complete and sufficient;
* `variance_condExp_le` and `condExp_comap_eq_rbEstimator` — the `condExp` form of the
  Rao–Blackwell step, which needs integrability where the kernel form needs measurability.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.1 (UMVU
Estimators), Lemma 1.10 (uniqueness of the unbiased function of a complete sufficient
statistic), Theorem 1.11 (Lehmann–Scheffé: minimum risk for every convex loss) and Corollary
1.12 (the full-rank exponential-family specialization). (`TPE2 §2.1 Lem 1.10, Thm 1.11, Cor
1.12`.)

**Proof formalization notes.**
* `unique_unbiased_function_of_complete` uses **only completeness**, not sufficiency: the
  difference of two unbiased functions of `T` integrates to zero under every law of `T`, and
  completeness concludes. The classical statement bundles sufficiency because it is stated for
  a complete sufficient statistic and because sufficiency is what makes unbiased functions of
  `T` *exist*; dropping it here strengthens the lemma and is recorded as a deliberate
  deviation.
* Optimality is proved by transport, not by a fresh variational argument: given a competitor
  `δ'`, its Rao–Blackwellization is an unbiased function of `T`, hence almost everywhere equal
  to the given one by the uniqueness lemma, and the Rao–Blackwell inequality applied to `δ'`
  finishes. The two theorems therefore have the same shape, with variance replaced by the
  `ℝ≥0∞`-valued convex risk.
* The risk statement fixes one unbiased integrable `δ` to build the estimator and quantifies
  over competitors `δ'` separately, rather than asserting a minimum over an unnamed class:
  this keeps the statement first-order and makes clear that the *same* estimator dominates
  every competitor.
* Integrability of the Rao–Blackwellized estimator under the laws of the statistic is derived
  from the corresponding property of `δ` through the reconstruction identity, not assumed
  (see the notes in `UMVU.RaoBlackwell`).
* Rao–Blackwellization appears here in two forms. The kernel form `rbEstimator Q δ`, which is
  what the Lehmann–Scheffé uniqueness step needs (its completeness test function must be
  globally measurable), and the `condExp` form, which needs only integrability. They agree
  (`condExp_comap_eq_rbEstimator`), and the variance half of Rao–Blackwell holds for the
  `condExp` form with no measurability input at all (`variance_condExp_le`, the law of total
  variance).
* The `IsUMVU` minimality clause quantifies over competitors carrying only `MemEstL2`, i.e. a
  *per-parameter* a.e. measurable version, whereas the completeness test function of the
  uniqueness step must be globally measurable. The two classes are reconciled by domination:
  `isUMVU_of_complete_sufficient` carries a σ-finite dominating measure (an added hypothesis,
  documented there and discharged for free by its only consumer), and the equivalent countable
  mixture of `exists_equivalent_countable_mixture` turns a per-parameter version into one that
  serves at *every* parameter. The measurable-competitor case is isolated in the private lemma
  `variance_rbEstimator_le_of_complete`, which the general case reduces to.
* `isUMVU_of_fullRank_expFamily` combines the completeness of the natural statistic of a
  full-rank exponential family with the two theorems above. It is phrased as the *existence*
  of a measurable function of the natural statistic which is UMVU, since the function itself
  is only determined almost everywhere. The full-rank condition is imposed on a parameter set
  that the family is required to cover. Its signature deviates from the printed statement —
  the natural statistic is `EuclideanSpace ℝ (Fin s)`-valued and the reference measure is
  σ-finite; both deviations are documented at the theorem.

**Bibliographic comments.** The theorem is due to E. L. Lehmann and H. Scheffé
("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10** (1950), 305–340;
**15** (1955), 219–236), building on the conditioning theorem of C. R. Rao ("Information and
the accuracy attainable in the estimation of statistical parameters," *Bull. Calcutta Math.
Soc.* **37** (1945), 81–91) and D. Blackwell ("Conditional expectation and unbiased sequential
estimation," *Ann. Math. Statist.* **18** (1947), 105–110). That the existence of a complete
sufficient statistic is, under mild conditions, also *necessary* for every estimable function
to admit a uniformly minimum variance unbiased estimator is due to R. R. Bahadur ("On unbiased
estimates of uniformly minimum variance," *Sankhyā* **18** (1957), 211–224). The completeness
of the natural statistic of a full-rank exponential family is established in Lehmann and
Scheffé (1955, ibid.).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

/-- Integrability of the Rao–Blackwellized estimator on the scale of the statistic, derived
from integrability under the members through the reconstruction identity. -/
private lemma integrable_rbEstimator_statLaw (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S} (hT : Measurable T) {Q : Kernel S 𝓧}
    [IsMarkovKernel Q] (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    {δ : 𝓧 → ℝ} (hδm : Measurable δ) (hδi : ∀ θ, Integrable δ (P θ)) (θ : Θ) :
    Integrable (rbEstimator Q δ) (statLaw P T θ) := by
  haveI : IsProbabilityMeasure (statLaw P T θ) := isProbabilityMeasure_statLaw P hT θ
  have hgm : Measurable (fun x : 𝓧 => (T x, x)) := hT.prodMk measurable_id
  have hδsnd : Measurable (fun z : S × 𝓧 => δ z.2) := hδm.comp measurable_snd
  have hrb : StronglyMeasurable (rbEstimator Q δ) :=
    hδm.stronglyMeasurable.integral_kernel (κ := Q)
  have hδsndInt : Integrable (fun z : S × 𝓧 => δ z.2) (statLaw P T θ ⊗ₘ Q) := by
    rw [← hgraph θ, integrable_map_measure hδsnd.aestronglyMeasurable hgm.aemeasurable]
    exact hδi θ
  have hnormInt : Integrable (fun t => ∫ x, ‖δ x‖ ∂ Q t) (statLaw P T θ) :=
    ((Measure.integrable_compProd_iff hδsndInt.aestronglyMeasurable).mp hδsndInt).2
  refine Integrable.mono' hnormInt hrb.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  exact norm_integral_le_integral_norm _

/-- Square-integrability of the Rao–Blackwellized estimator on the scale of the statistic,
via the fiberwise `L²` Jensen bound `(∫ δ dQ_t)² ≤ ∫ δ² dQ_t`. -/
private lemma memLp_two_rbEstimator_statLaw (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S} (hT : Measurable T) {Q : Kernel S 𝓧}
    [IsMarkovKernel Q] (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    {δ : 𝓧 → ℝ} (hδm : Measurable δ) (hδ2 : MemEstL2 P δ) (θ : Θ) :
    MemLp (rbEstimator Q δ) 2 (statLaw P T θ) := by
  haveI : IsProbabilityMeasure (statLaw P T θ) := isProbabilityMeasure_statLaw P hT θ
  have hgm : Measurable (fun x : 𝓧 => (T x, x)) := hT.prodMk measurable_id
  have hδsnd : Measurable (fun z : S × 𝓧 => δ z.2) := hδm.comp measurable_snd
  have hsqm : Measurable (fun z : S × 𝓧 => (δ z.2) ^ 2) := hδsnd.pow_const 2
  have hrb : StronglyMeasurable (rbEstimator Q δ) :=
    hδm.stronglyMeasurable.integral_kernel (κ := Q)
  have hδi : ∀ θ', Integrable δ (P θ') := fun θ' => (hδ2 θ').integrable one_le_two
  have hδsndInt : Integrable (fun z : S × 𝓧 => δ z.2) (statLaw P T θ ⊗ₘ Q) := by
    rw [← hgraph θ, integrable_map_measure hδsnd.aestronglyMeasurable hgm.aemeasurable]
    exact hδi θ
  have hsqInt : Integrable (fun z : S × 𝓧 => (δ z.2) ^ 2) (statLaw P T θ ⊗ₘ Q) := by
    rw [← hgraph θ, integrable_map_measure hsqm.aestronglyMeasurable hgm.aemeasurable]
    exact (hδ2 θ).integrable_sq
  have haeδ : ∀ᵐ t ∂ statLaw P T θ, Integrable δ (Q t) :=
    ((Measure.integrable_compProd_iff hδsndInt.aestronglyMeasurable).mp hδsndInt).1
  have haesq : ∀ᵐ t ∂ statLaw P T θ, Integrable (fun x => (δ x) ^ 2) (Q t) :=
    ((Measure.integrable_compProd_iff hsqInt.aestronglyMeasurable).mp hsqInt).1
  have hinnerInt : Integrable (fun t => ∫ x, (δ x) ^ 2 ∂ Q t) (statLaw P T θ) := by
    have h2 := ((Measure.integrable_compProd_iff hsqInt.aestronglyMeasurable).mp hsqInt).2
    refine h2.congr (Filter.Eventually.of_forall fun t =>
      integral_congr_ae (Filter.Eventually.of_forall fun x => Real.norm_of_nonneg (sq_nonneg _)))
  have hconv : ConvexOn ℝ Set.univ (fun y : ℝ => y ^ 2) := Even.convexOn_pow even_two
  have hcont : Continuous (fun y : ℝ => y ^ 2) := by fun_prop
  have hbound : ∀ᵐ t ∂ statLaw P T θ, (rbEstimator Q δ t) ^ 2 ≤ ∫ x, (δ x) ^ 2 ∂ Q t := by
    filter_upwards [haeδ, haesq] with t htδ htsq
    have hj := hconv.map_integral_le hcont.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) htδ htsq
    simpa [rbEstimator] using hj
  have hrbsqInt : Integrable (fun t => (rbEstimator Q δ t) ^ 2) (statLaw P T θ) := by
    refine Integrable.mono' hinnerInt ((hrb.measurable.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [hbound] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact ht
  exact (memLp_two_iff_integrable_sq hrb.aestronglyMeasurable).mpr hrbsqInt

/-!
### The `condExp` Rao–Blackwell layer

The kernel form of Rao–Blackwellization, `rbEstimator Q δ = fun s => ∫ δ dQ_s`, needs a
genuine measurable `δ` in order to be a measurable function of `s` at all. The conditional
expectation `(P θ)[δ | σ(T)]` needs only *integrability* under the single measure `P θ`. The
two agree (`condExp_comap_eq_rbEstimator`), and the variance-reduction half of Rao–Blackwell
holds for the conditional expectation with no measurability input whatsoever
(`variance_condExp_le`, the law of total variance).
-/

section CondExpVariance

-- a fresh carrier with an explicitly *named* ambient σ-algebra, so that the coarser σ-algebra
-- `m` cannot shadow it in the statement below
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-- **Conditioning does not increase the variance.** The law of total variance, in the form
used by Rao–Blackwell. In contrast with the kernel form `variance_rbEstimator_le`, no
measurable representative of the estimator is required: square-integrability under the single
measure `μ` suffices. -/
theorem variance_condExp_le (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    -- LEAN-ONLY: the conditioning σ-algebra is coarser than the ambient one; `μ` is declared
    -- before `m` so that `m` cannot be picked up as the σ-algebra carrying `μ`
    (hm : m ≤ m₀) {δ : Ω → ℝ}
    -- USER-INPUT: the estimator is square-integrable; only an a.e. version is needed
    (hδ : MemLp δ 2 μ) :
    variance (μ[δ|m]) μ ≤ variance δ μ := by
  have htot := integral_condVar_add_variance_condExp (μ := μ) (X := δ) hm hδ
  have hnn : 0 ≤ ∫ x, condVar m δ μ x ∂μ := by
    refine integral_nonneg_of_ae (condExp_nonneg ?_)
    filter_upwards with x
    simpa using sq_nonneg (δ x - (μ[δ|m]) x)
  linarith [htot]

end CondExpVariance

/-- **Rao–Blackwellization is a conditional expectation.** Under the θ-free disintegration of
the graph law, the kernel average `s ↦ ∫ δ dQ_s`, read along `T`, is a version of the
conditional expectation of `δ` given the σ-algebra generated by the statistic. -/
theorem condExp_comap_eq_rbEstimator (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; sufficiency of the statistic
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the estimator, needed to form the kernel average
    (hδm : Measurable δ)
    -- LEAN-ONLY: integrability under every member
    (hδi : ∀ θ, Integrable δ (P θ)) (θ : Θ) :
    (P θ)[δ|MeasurableSpace.comap T inferInstance] =ᵐ[P θ] fun x => rbEstimator Q δ (T x) := by
  haveI : IsProbabilityMeasure (statLaw P T θ) := isProbabilityMeasure_statLaw P hT θ
  have hm : MeasurableSpace.comap T inferInstance ≤ (inferInstance : MeasurableSpace 𝓧) :=
    hT.comap_le
  haveI : IsFiniteMeasure ((P θ).trim hm) := isFiniteMeasure_trim hm
  have hgm : Measurable (fun x : 𝓧 => (T x, x)) := hT.prodMk measurable_id
  have hδsnd : Measurable (fun z : S × 𝓧 => δ z.2) := hδm.comp measurable_snd
  have hrb : StronglyMeasurable (rbEstimator Q δ) :=
    hδm.stronglyMeasurable.integral_kernel (κ := Q)
  have hδsndInt : Integrable (fun z : S × 𝓧 => δ z.2) (statLaw P T θ ⊗ₘ Q) := by
    rw [← hgraph θ, integrable_map_measure hδsnd.aestronglyMeasurable hgm.aemeasurable]
    exact hδi θ
  -- `T` is measurable for the σ-algebra it generates, so the kernel average is `σ(T)`-measurable
  have hTcomap : Measurable[MeasurableSpace.comap T inferInstance] T :=
    Measurable.of_comap_le le_rfl
  have hrbT : StronglyMeasurable[MeasurableSpace.comap T inferInstance]
      (fun x => rbEstimator Q δ (T x)) := hrb.comp_measurable hTcomap
  have hrbInt : Integrable (fun x => rbEstimator Q δ (T x)) (P θ) := by
    have hstat := integrable_rbEstimator_statLaw P hT hgraph hδm hδi θ
    rw [statLaw] at hstat
    exact (integrable_map_measure hrb.aestronglyMeasurable hT.aemeasurable).mp hstat
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hδi θ)
    (fun s _ _ => hrbInt.integrableOn) (fun s hs _ => ?_) hrbT.aestronglyMeasurable).symm
  obtain ⟨B, hB, rfl⟩ := hs
  -- the real-valued indicator of `B`, used to turn the set integrals into plain ones
  set w : S → ℝ := B.indicator (fun _ => (1 : ℝ)) with hwdef
  have hwm : Measurable w := measurable_const.indicator hB
  have hwbdd : ∀ t, ‖w t‖ ≤ 1 := by
    intro t
    by_cases ht : t ∈ B <;> simp [hwdef, ht]
  have hpull : ∀ f : 𝓧 → ℝ, ∫ x in T ⁻¹' B, f x ∂ P θ = ∫ x, w (T x) * f x ∂ P θ := by
    intro f
    rw [← integral_indicator (hB.preimage hT)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : T x ∈ B <;>
      simp [hwdef, hx, Set.mem_preimage]
  -- the left-hand side is a set integral against the law of the statistic
  have hL : ∫ x in T ⁻¹' B, rbEstimator Q δ (T x) ∂ P θ
      = ∫ t, w t * rbEstimator Q δ t ∂ statLaw P T θ := by
    rw [hpull]
    have := integral_map (φ := T) (μ := P θ) hT.aemeasurable
      (f := fun t => w t * rbEstimator Q δ t)
      ((hwm.stronglyMeasurable.mul hrb).aestronglyMeasurable)
    rw [statLaw, this]
  -- the right-hand side is the same, computed through the graph disintegration
  have hprodm : Measurable (fun z : S × 𝓧 => w z.1 * δ z.2) := (hwm.comp measurable_fst).mul hδsnd
  have hprodInt : Integrable (fun z : S × 𝓧 => w z.1 * δ z.2) (statLaw P T θ ⊗ₘ Q) :=
    hδsndInt.bdd_mul (c := 1) (hwm.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hwbdd z.1)
  have hR : ∫ x in T ⁻¹' B, δ x ∂ P θ = ∫ t, w t * rbEstimator Q δ t ∂ statLaw P T θ := by
    rw [hpull]
    have h1 : ∫ x, w (T x) * δ x ∂ P θ
        = ∫ z, w z.1 * δ z.2 ∂ ((P θ).map (fun x => (T x, x))) :=
      (integral_map hgm.aemeasurable hprodm.aestronglyMeasurable).symm
    rw [h1, hgraph θ, Measure.integral_compProd hprodInt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [rbEstimator]
    exact integral_const_mul (w t) δ
  rw [hL, hR]

/-- **At most one unbiased function of a complete statistic.** If two measurable functions of
a complete statistic are both unbiased for the same estimand, they agree almost everywhere
under every law of the statistic.

Only completeness is used; the classical statement additionally assumes sufficiency, which is
what guarantees that such functions exist but is not needed for uniqueness. -/
theorem unique_unbiased_function_of_complete (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (g : Θ → ℝ) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic; needed for the change of variables
    (hT : Measurable T)
    -- USER-INPUT: completeness of the statistic; the classical hypothesis
    (hcomp : IsCompleteStat P T) {η₁ η₂ : S → ℝ}
    -- LEAN-ONLY: measurability of the two candidate functions
    (hη₁ : Measurable η₁) (hη₂ : Measurable η₂)
    -- LEAN-ONLY: integrability under the laws of the statistic, so that means subtract
    (hi₁ : ∀ θ, Integrable η₁ (statLaw P T θ)) (hi₂ : ∀ θ, Integrable η₂ (statLaw P T θ))
    -- USER-INPUT: both are unbiased for the same estimand
    (hu₁ : IsUnbiased P g fun x => η₁ (T x)) (hu₂ : IsUnbiased P g fun x => η₂ (T x))
    (θ : Θ) :
    η₁ =ᵐ[statLaw P T θ] η₂ := by
  -- the difference of the two functions has identically zero mean under the laws of `T`
  have hz : ∀ θ', ∫ s, (η₁ s - η₂ s) ∂(statLaw P T θ') = 0 := by
    intro θ'
    rw [integral_sub (hi₁ θ') (hi₂ θ')]
    have e1 : ∫ s, η₁ s ∂(statLaw P T θ') = g θ' := by
      rw [statLaw, integral_map hT.aemeasurable hη₁.aestronglyMeasurable]; exact hu₁ θ'
    have e2 : ∫ s, η₂ s ∂(statLaw P T θ') = g θ' := by
      rw [statLaw, integral_map hT.aemeasurable hη₂.aestronglyMeasurable]; exact hu₂ θ'
    rw [e1, e2, sub_self]
  have hfz := hcomp (fun s => η₁ s - η₂ s) (hη₁.sub hη₂)
    (fun θ' => (hi₁ θ').sub (hi₂ θ')) hz θ
  filter_upwards [hfz] with s hs
  simp only [Pi.zero_apply] at hs
  exact sub_eq_zero.mp hs

/-- Lehmann–Scheffé minimality for an **arbitrary** square-integrable unbiased competitor.

The classical argument Rao–Blackwellizes the competitor `δ'` through `T` and compares by
`variance_rbEstimator_le`, then identifies the two Rao–Blackwellizations via
`unique_unbiased_function_of_complete`: both `rbEstimator Q δ` and `rbEstimator Q δ'` are
unbiased functions of the complete statistic `T`, hence a.e. equal, so the variance of the
former equals that of `rbEstimator Q δ' ∘ T`, which does not exceed `var δ'`.

**Added hypothesis (private lemma, pre-authorized).** `hδ'm : Measurable δ'`. Both the kernel
average `t ↦ ∫ δ' dQ_t = rbEstimator Q δ'` and the completeness test function require `δ'` to
carry a genuine (global) measurable representative. The `IsUMVU` minimality quantifies over
competitors holding only `MemEstL2 P δ'`, i.e. a *per-parameter* `AEStronglyMeasurable`
version; with no dominating measure these do not glue to a single measurable function (false
in general — Dirac families are a counterexample). This private lemma is therefore stated for
measurable competitors; the consumer `isUMVU_of_complete_sufficient` cannot discharge that
hypothesis for an arbitrary `MemEstL2` competitor (see the note there). -/
private lemma variance_rbEstimator_le_of_complete (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (g : Θ → ℝ) {T : 𝓧 → S} (hT : Measurable T)
    {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    (hcomp : IsCompleteStat P T) {δ : 𝓧 → ℝ} (hδm : Measurable δ) (hδu : IsUnbiased P g δ)
    (hδ2 : MemEstL2 P δ) {δ' : 𝓧 → ℝ} (hδ'm : Measurable δ') (hδ'u : IsUnbiased P g δ')
    (hδ'2 : MemEstL2 P δ') (θ : Θ) :
    variance (fun x => rbEstimator Q δ (T x)) (P θ) ≤ variance δ' (P θ) := by
  have hδi : ∀ θ', Integrable δ (P θ') := fun θ' => (hδ2 θ').integrable one_le_two
  have hδ'i : ∀ θ', Integrable δ' (P θ') := fun θ' => (hδ'2 θ').integrable one_le_two
  have hrbδm : Measurable (rbEstimator Q δ) :=
    (hδm.stronglyMeasurable.integral_kernel (κ := Q)).measurable
  have hrbδ'm : Measurable (rbEstimator Q δ') :=
    (hδ'm.stronglyMeasurable.integral_kernel (κ := Q)).measurable
  -- both Rao–Blackwellizations are unbiased functions of the complete `T`, hence a.e. equal
  have huniq : rbEstimator Q δ =ᵐ[statLaw P T θ] rbEstimator Q δ' :=
    unique_unbiased_function_of_complete P g hT hcomp hrbδm hrbδ'm
      (fun θ' => integrable_rbEstimator_statLaw P hT hgraph hδm hδi θ')
      (fun θ' => integrable_rbEstimator_statLaw P hT hgraph hδ'm hδ'i θ')
      (isUnbiased_rbEstimator P g hT hgraph hδm hδi hδu)
      (isUnbiased_rbEstimator P g hT hgraph hδ'm hδ'i hδ'u) θ
  have hEq : (fun x => rbEstimator Q δ (T x)) =ᵐ[P θ] fun x => rbEstimator Q δ' (T x) :=
    ae_eq_comp hT.aemeasurable huniq
  rw [variance_congr hEq]
  -- Rao–Blackwellization of the competitor does not increase its variance
  exact variance_rbEstimator_le P hT hgraph hδ'm hδ'2 θ

/-- **Lehmann–Scheffé, variance form.** Averaging any unbiased square-integrable estimator
over the fibers of a *complete* sufficient statistic produces the uniformly minimum variance
unbiased estimator of the estimand.

**Added hypothesis (authorized signature amendment): the family is dominated.** `μ` σ-finite
with `∀ θ, P θ ≪ μ` — the standing hypothesis of the whole dominated theory of sufficiency
(and the setting of the source: completeness and sufficiency are developed there for
dominated families), already carried by the only consumer of this theorem,
`isUMVU_of_fullRank_expFamily`, where it is discharged by `E.base`.

*What it buys, and why some such hypothesis is needed.* The minimality clause of `IsUMVU`
quantifies over competitors `δ'` holding only `MemEstL2 P δ'`, i.e. a *per-parameter*
`AEStronglyMeasurable` version, whereas `IsCompleteStat` tests globally measurable functions,
and Rao–Blackwellization `rbEstimator Q δ'` needs a genuine measurable representative to be a
legitimate test function. Domination bridges exactly that gap: `exists_equivalent_countable_mixture`
produces a countable mixture `ν` of members with `P θ ≪ ν` for *every* `θ`, the competitor is
`AEStronglyMeasurable` for `ν` because it is so for each mixed member
(`AEStronglyMeasurable.sum_measure`), and its `ν`-measurable version is then a version of it
simultaneously under every member — so it is unbiased and square-integrable throughout, and
the classical argument (`variance_rbEstimator_le_of_complete`) applies verbatim. Without a
dominating measure the per-parameter versions need not glue (Dirac-type families), which is
the obstruction recorded in earlier drafts of this file. -/
theorem isUMVU_of_complete_sufficient (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (g : Θ → ℝ) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T)
    -- USER-INPUT (AMENDMENT): the model is dominated by the σ-finite measure `μ`; the
    -- standing hypothesis of the dominated theory, used only to glue the per-parameter a.e.
    -- versions of a competitor into one measurable representative
    (μ : Measure 𝓧) [SigmaFinite μ] (hdom : ∀ θ, P θ ≪ μ) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; sufficiency of the statistic
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    -- USER-INPUT: completeness of the statistic; the classical hypothesis
    (hcomp : IsCompleteStat P T) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the estimator
    (hδm : Measurable δ)
    -- USER-INPUT: the estimand is estimable, witnessed by the unbiased estimator `δ`
    (hδu : IsUnbiased P g δ)
    -- USER-INPUT: the witness lies in the estimator class `Δ`
    (hδ2 : MemEstL2 P δ) :
    IsUMVU P g (fun x => rbEstimator Q δ (T x)) := by
  refine ⟨isUnbiased_rbEstimator P g hT hgraph hδm
      (fun θ' => (hδ2 θ').integrable one_le_two) hδu, ?_, ?_⟩
  · -- square-integrability of the Rao–Blackwellized estimator, transported to the data scale
    intro θ
    have hstat := memLp_two_rbEstimator_statLaw P hT hgraph hδm hδ2 θ
    exact (memLp_map_measure_iff hstat.aestronglyMeasurable hT.aemeasurable).mp hstat
  · -- minimality against every square-integrable unbiased competitor
    intro δ' hδ'u hδ'2 θ
    haveI : Nonempty Θ := ⟨θ⟩
    -- an equivalent countable mixture of members of the family: it dominates *every* member,
    -- so a version of the competitor under the mixture is a version under every member
    obtain ⟨θs, c, ν, hνdef, -, -, hdomν, -⟩ := exists_equivalent_countable_mixture P μ hdom
    have hae : AEStronglyMeasurable δ' ν := by
      rw [hνdef]
      exact AEStronglyMeasurable.sum_measure
        fun i => ((hδ'2 (θs i)).aestronglyMeasurable).smul_measure (c i)
    -- the glued measurable representative, and its a.e. agreement with `δ'` at every parameter
    have hdm : Measurable (hae.mk δ') := hae.stronglyMeasurable_mk.measurable
    have hdae : ∀ θ', δ' =ᵐ[P θ'] hae.mk δ' :=
      fun θ' => hae.ae_eq_mk.filter_mono (hdomν θ').ae_le
    have hdu : IsUnbiased P g (hae.mk δ') :=
      fun θ' => (integral_congr_ae (hdae θ')).symm.trans (hδ'u θ')
    have hd2 : MemEstL2 P (hae.mk δ') := fun θ' => (hδ'2 θ').ae_eq (hdae θ')
    rw [variance_congr (hdae θ)]
    exact variance_rbEstimator_le_of_complete P g hT hgraph hcomp hδm hδu hδ2 hdm hdu hd2 θ


/-- **Lehmann–Scheffé, convex-loss form.** The estimator of `isUMVU_of_complete_sufficient`
minimizes the risk among *all* unbiased estimators, simultaneously for every loss that is
convex and nonnegative in the decision argument — its optimality is not tied to squared
error. -/
theorem risk_le_of_complete_sufficient (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (g : Θ → ℝ) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; sufficiency of the statistic
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    -- USER-INPUT: completeness of the statistic; the classical hypothesis
    (hcomp : IsCompleteStat P T) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the estimator used to build the optimal one
    (hδm : Measurable δ)
    -- LEAN-ONLY: integrability under every member; fiber integrability is derived from it
    (hδi : ∀ θ, Integrable δ (P θ))
    -- USER-INPUT: the estimand is estimable, witnessed by the unbiased estimator `δ`
    (hδu : IsUnbiased P g δ) (ρ : Θ → ℝ → ℝ)
    -- USER-INPUT: the loss is convex in the decision argument; the classical hypothesis
    (hconv : ∀ θ, ConvexOn ℝ Set.univ (ρ θ))
    -- LEAN-ONLY: continuity of the loss, automatic for a convex function on all of `ℝ`
    (hcont : ∀ θ, Continuous (ρ θ))
    -- USER-INPUT: the loss is nonnegative, so that `ENNReal.ofReal` loses nothing
    (hnn : ∀ θ y, 0 ≤ ρ θ y) {δ' : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the competitor
    (hδ'm : Measurable δ')
    -- LEAN-ONLY: integrability of the competitor under every member
    (hδ'i : ∀ θ, Integrable δ' (P θ))
    -- USER-INPUT: the competitor is unbiased for the same estimand
    (hδ'u : IsUnbiased P g δ')
    -- USER-INPUT: the competitor has finite risk (otherwise the inequality is trivial)
    (hρi : ∀ θ, Integrable (fun x => ρ θ (δ' x)) (P θ)) (θ : Θ) :
    risk P (fun θ' d => ENNReal.ofReal (ρ θ' d)) (fun x => rbEstimator Q δ (T x)) θ ≤
      risk P (fun θ' d => ENNReal.ofReal (ρ θ' d)) δ' θ := by
  have hrbδm : Measurable (rbEstimator Q δ) :=
    (hδm.stronglyMeasurable.integral_kernel (κ := Q)).measurable
  have hrbδ'm : Measurable (rbEstimator Q δ') :=
    (hδ'm.stronglyMeasurable.integral_kernel (κ := Q)).measurable
  -- the two Rao–Blackwellizations are unbiased functions of `T`, hence a.e. equal
  have huniq : rbEstimator Q δ =ᵐ[statLaw P T θ] rbEstimator Q δ' :=
    unique_unbiased_function_of_complete P g hT hcomp hrbδm hrbδ'm
      (fun θ' => integrable_rbEstimator_statLaw P hT hgraph hδm hδi θ')
      (fun θ' => integrable_rbEstimator_statLaw P hT hgraph hδ'm hδ'i θ')
      (isUnbiased_rbEstimator P g hT hgraph hδm hδi hδu)
      (isUnbiased_rbEstimator P g hT hgraph hδ'm hδ'i hδ'u) θ
  have hEq : (fun x => rbEstimator Q δ (T x)) =ᵐ[P θ] fun x => rbEstimator Q δ' (T x) :=
    ae_eq_comp hT.aemeasurable huniq
  have hriskeq : risk P (fun θ' d => ENNReal.ofReal (ρ θ' d))
        (fun x => rbEstimator Q δ (T x)) θ
      = risk P (fun θ' d => ENNReal.ofReal (ρ θ' d)) (fun x => rbEstimator Q δ' (T x)) θ := by
    simp only [risk, crossRisk]
    refine lintegral_congr_ae ?_
    filter_upwards [hEq] with x hx
    rw [hx]
  rw [hriskeq]
  exact risk_rbEstimator_le P hT hgraph hδ'm hδ'i ρ hconv hcont hnn hρi θ

/-- **Full-rank exponential families.** For a family that is a canonical exponential family of
full rank, every estimable function admits a uniformly minimum variance unbiased estimator,
and it is a function of the natural statistic.

**Deviation from the printed statement (authorized signature amendment).** The natural
statistic is specialized from an abstract real inner-product space `V` to
`EuclideanSpace ℝ (Fin s)`, and one instance on the reference measure is added,
`[SigmaFinite E.base]`. Both are forced:

* the only completeness theorem for the natural statistic,
  `isCompleteStat_of_interior_nonempty`, is `EuclideanSpace ℝ (Fin s)`-valued, because the
  Laplace/MGF-uniqueness brick it consumes (`ae_eq_zero_of_integral_exp_inner_eq_zero`) is a
  finite-dimensional fact; there is no completeness statement for an abstract `V`;
* `[SigmaFinite E.base]` is what turns the Fisher–Neyman factorization of the densities into
  sufficiency (`isSufficient_of_isFactorizedDensity`) and then into the θ-free reconstruction
  kernel (`hasSufficientKernel_of_isSufficient_dominated`).

Nothing else is added. In particular neither `E.base ≠ 0` nor membership of the parameters in
the natural parameter set is assumed: both are *derived* from
`[∀ θ, IsProbabilityMeasure (P θ)]`, since off the natural parameter set — and for a zero
reference measure — every member of the family is the zero measure. -/
theorem isUMVU_of_fullRank_expFamily {s : ℕ} (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    -- LEAN-ONLY (amendment): σ-finiteness of the reference measure, consumed by the
    -- factorization ⇒ sufficiency ⇒ reconstruction-kernel chain
    [SigmaFinite E.base] (Ξ : Set (EuclideanSpace ℝ (Fin s))) (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- LEAN-ONLY: the sufficiency kernel of the natural statistic is produced by
    -- `Sufficiency.RegularConditional`, which needs a standard Borel sample space; an
    -- exponential family supplies no explicit reconstruction kernel without such structure.
    -- Standard throughout this literature: every sufficiency theorem in the area carries it.
    [StandardBorelSpace 𝓧] [Nonempty 𝓧] (ηmap : Θ → EuclideanSpace ℝ (Fin s))
    -- USER-INPUT: the family is a reparametrization of the canonical exponential family `E`
    (hrepr : IsCanonicalRepr P E ηmap)
    -- USER-INPUT: the parametrization covers the full-rank parameter set
    (hcover : Ξ ⊆ Set.range ηmap)
    -- USER-INPUT: full rank — nonempty interior of the parameter set plus an affinely
    -- independent natural statistic
    (hFR : E.FullRank Ξ) (g : Θ → ℝ) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the witness estimator
    (hδm : Measurable δ)
    -- USER-INPUT: the estimand is estimable, witnessed by the unbiased estimator `δ`
    (hδu : IsUnbiased P g δ)
    -- USER-INPUT: the witness lies in the estimator class `Δ`
    (hδ2 : MemEstL2 P δ) :
    ∃ η : EuclideanSpace ℝ (Fin s) → ℝ, Measurable η ∧
      IsUMVU P g (fun x => η (E.stat x)) := by
  obtain ⟨hΞnat, hint, -⟩ := hFR
  -- every parameter lands in the natural parameter set: outside it the member would be `0`
  have hnat : ∀ θ, ηmap θ ∈ E.natSet := by
    intro θ
    by_contra hθ
    have h0 : P θ = 0 := by rw [hrepr θ]; exact E.P_eq_zero_of_notMem hθ
    have huniv : (P θ) Set.univ = 1 := measure_univ
    rw [h0] at huniv
    simp at huniv
  -- the densities over the reference measure, and their Fisher–Neyman factorization
  set p : Θ → 𝓧 → ℝ≥0∞ := fun θ x =>
    ENNReal.ofReal (Real.exp (⟪ηmap θ, E.stat x⟫_ℝ - E.logPartition (ηmap θ))) with hpdef
  have hpm : ∀ θ, Measurable (p θ) := fun θ =>
    (((continuous_const.inner continuous_id).measurable.comp E.stat_meas).sub
      measurable_const).exp.ennreal_ofReal
  have hP : ∀ θ, P θ = E.base.withDensity (p θ) := fun θ => by
    rw [hrepr θ]; exact E.P_eq_withDensity (hnat θ)
  have hsuf : IsSufficient P E.stat :=
    isSufficient_of_isFactorizedDensity P E.base p hpm hP E.stat_meas
      (g := fun θ t => ENNReal.ofReal (Real.exp (⟪ηmap θ, t⟫_ℝ - E.logPartition (ηmap θ))))
      (h := fun _ => 1)
      (fun θ => (((continuous_const.inner continuous_id).measurable).sub
        measurable_const).exp.ennreal_ofReal)
      measurable_const
      (fun θ => Filter.Eventually.of_forall fun x => (mul_one _).symm)
  have hdomE : ∀ θ, P θ ≪ E.base :=
    fun θ => (hP θ) ▸ withDensity_absolutelyContinuous E.base (p θ)
  -- the θ-free reconstruction kernel, from sufficiency and domination by `E.base`
  obtain ⟨Q, hQm, hgraph⟩ :=
    hasSufficientKernel_of_isSufficient_dominated P E.stat_meas E.base hdomE hsuf
  haveI := hQm
  -- completeness of the natural statistic, transported from the `Ξ`-indexed subfamily
  have hcomp : IsCompleteStat P E.stat := by
    have hcompΞ := isCompleteStat_of_interior_nonempty E Ξ hΞnat hint
    obtain ⟨ξ₀, hξ₀int⟩ := hint
    have hξ₀ : ξ₀ ∈ Ξ := interior_subset hξ₀int
    -- a parameter of the model realizing each point of `Ξ`
    choose θsel hθsel using fun ξ : ↥Ξ => hcover ξ.2
    have hQeq : ∀ ξ : ↥Ξ, (E.P (ξ : EuclideanSpace ℝ (Fin s))).map E.stat
        = (P (θsel ξ)).map E.stat := fun ξ => by rw [hrepr (θsel ξ), hθsel ξ]
    intro f hfm hfi hf0 θ
    have hfiΞ : ∀ ξ : ↥Ξ, Integrable f ((E.P (ξ : EuclideanSpace ℝ (Fin s))).map E.stat) := by
      intro ξ; rw [hQeq ξ]; exact hfi (θsel ξ)
    have hf0Ξ : ∀ ξ : ↥Ξ,
        ∫ t, f t ∂((E.P (ξ : EuclideanSpace ℝ (Fin s))).map E.stat) = 0 := by
      intro ξ; rw [hQeq ξ]; exact hf0 (θsel ξ)
    have hzero : f =ᵐ[(E.P ξ₀).map E.stat] 0 := hcompΞ f hfm hfiΞ hf0Ξ ⟨ξ₀, hξ₀⟩
    -- every member is mutually absolutely continuous with the reference measure, so the
    -- conclusion at the single parameter `ξ₀` propagates to the whole model
    have h1 : P θ ≪ E.base := by
      rw [hrepr θ]; exact tilted_absolutelyContinuous E.base _
    have h2 : E.base ≪ E.P ξ₀ := absolutelyContinuous_tilted (hΞnat hξ₀)
    exact hzero.filter_mono ((h1.trans h2).map E.stat_meas).ae_le
  exact ⟨rbEstimator Q δ, (hδm.stronglyMeasurable.integral_kernel (κ := Q)).measurable,
    isUMVU_of_complete_sufficient P g E.stat_meas E.base hdomE hgraph hcomp hδm hδu hδ2⟩

end StatLean.PointEstimation
