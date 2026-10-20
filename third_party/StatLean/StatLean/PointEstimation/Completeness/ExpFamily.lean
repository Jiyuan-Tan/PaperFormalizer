module
public import StatLean.PointEstimation.Completeness.Defs
public import StatLean.PointEstimation.ExponentialFamily.Defs
public import StatLean.PointEstimation.ForMathlib.MGFUniqueness
public import StatLean.PointEstimation.ForMathlib.MGFUniquenessPi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Probability.Notation

@[expose] public section

/-!
# Completeness of the natural statistic of an exponential family

The natural statistic of a canonical exponential family is complete as soon as the parameter
set has nonempty interior. Suppose `f` is integrable with `E_η[f(T)] = 0` for every `η` in the
parameter set. On the statistic's scale this reads
$$ \int f(t)\,e^{\langle \eta, t\rangle}\,d\nu_T(t) \;=\; 0, $$
so the two finite measures obtained by weighting `ν_T` with the positive and the negative part
of `f` have the same Laplace transform on a set with nonempty interior. Uniqueness of Laplace
transforms on an open set forces the two measures to coincide, i.e. `f = 0` almost
everywhere.

* `isCompleteStat_of_interior_nonempty` — the multivariate statement;
* `isCompleteStat_of_interior_nonempty_real` — its one-dimensional specialization.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.6
(Sufficient Statistics), Theorem 6.22 (in an exponential family of full rank the natural
statistic is complete). (`TPE2 §1.6 Thm 6.22`.)

**Proof formalization notes.**
* Only **nonempty interior** of the parameter set is assumed, not the full rank condition.
  Affine independence of the natural statistic — the other half of `ExpFamily.FullRank` — is
  what minimality of `T` needs; completeness does not use it, and assuming it would weaken the
  theorem for no gain. `ExpFamily.FullRank.2.1` supplies the interior hypothesis directly for
  callers holding the classical full-rank condition.
* No nondegeneracy hypothesis on the reference measure is needed: if `E.base = 0` then every
  member and hence every law of the statistic is the zero measure, and the conclusion
  `f =ᵐ[0] 0` is vacuously true.
* The intended route is the Laplace/moment-generating-function uniqueness bricks being
  developed in the area's `ForMathlib` layer —
  `ext_of_integral_exp_eqOn` and `ae_eq_zero_of_integral_exp_smul_eq_zero` in the
  one-dimensional case, `ext_of_integral_exp_inner_eqOn` and
  `ae_eq_zero_of_integral_exp_inner_eq_zero` in the multivariate case.
* The conclusion is stated as `IsCompleteFamily` applied to the laws of the natural statistic;
  this unfolds definitionally to `IsCompleteStat (fun θ : Ξ' => E.P θ) E.stat`, so either
  spelling may be used by consumers.
* The multivariate statement is given on `EuclideanSpace ℝ (Fin s)` rather than for an
  abstract inner-product space: the Laplace-uniqueness argument is a statement about finitely
  many real parameters, and the concrete space is what carries the required measurable-space
  and Borel instances.

**Bibliographic comments.** Completeness of the natural statistic of a full-rank exponential
family is due to E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and unbiased
estimation," *Sankhyā* **10** (1950), 305–340; **15** (1955), 219–236). Modern treatments,
including the Laplace-transform argument used here, are in O. Barndorff-Nielsen (*Information
and Exponential Families in Statistical Theory*, Wiley, 1978, Lemma 8.2) and L. D. Brown
(*Fundamentals of Statistical Exponential Families*, IMS Lecture Notes 9, 1986, Thm 2.12).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- A measure carrying an integrable strictly-positive exponential is σ-finite: the level sets
`{t | 1/(n+1) ≤ e^{⟪η, t⟫}}` are of finite measure (Markov) and cover the space. -/
private lemma sigmaFinite_of_integrable_exp {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V]
    {ν : Measure V} {η : V}
    (hg : Integrable (fun t => Real.exp ⟪η, t⟫_ℝ) ν) : SigmaFinite ν := by
  refine Measure.sigmaFinite_of_countable
    (Set.countable_range
      (fun n : ℕ => {t : V | 1 / ((n : ℝ) + 1) ≤ Real.exp ⟪η, t⟫_ℝ})) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    exact hg.measure_ge_lt_top (by positivity)
  · refine Set.eq_univ_of_forall fun t => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (Real.exp_pos ⟪η, t⟫_ℝ)
    exact Set.mem_sUnion.2 ⟨_, ⟨n, rfl⟩, le_of_lt hn⟩

/-- Generic completeness reduction: the family of laws of the natural statistic is complete
whenever the inner-product-form signed Laplace corollary `hsigned` holds on the ambient
space `V`. Both headline theorems below supply `hsigned` from the corresponding `ForMathlib`
uniqueness brick. -/
private lemma isCompleteFamily_of_signed {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (E : ExpFamily 𝓧 V) (Ξ' : Set V) (hΞ : Ξ' ⊆ E.natSet) (hint : (interior Ξ').Nonempty)
    (hsigned : ∀ {ν : Measure V}, SigmaFinite ν → ∀ {f : V → ℝ}, Measurable f →
      (∀ t ∈ Ξ', Integrable (fun x => f x * Real.exp ⟪t, x⟫_ℝ) ν) →
      (∀ t ∈ Ξ', ∫ x, f x * Real.exp ⟪t, x⟫_ℝ ∂ν = 0) → f =ᵐ[ν] 0) :
    IsCompleteFamily fun θ : Ξ' => (E.P (θ : V)).map E.stat := by
  intro f hf_meas hf_int hf_zero θ
  rcases eq_zero_or_neZero E.base with hbase0 | hbaseNe
  · have hh : E.P (θ : V) = 0 := by
      unfold ExpFamily.P; rw [hbase0]; exact tilted_zero_measure _
    change f =ᵐ[(E.P (θ : V)).map E.stat] 0
    rw [hh, Measure.map_zero]
    change ∀ᶠ x in ae (0 : Measure V), f x = (0 : V → ℝ) x
    rw [ae_zero]; exact Filter.eventually_bot
  · set ν : Measure V := E.base.map E.stat with hνdef
    obtain ⟨η₀, hη₀⟩ := hint
    have hη₀int : Integrable (fun x => Real.exp ⟪η₀, E.stat x⟫_ℝ) E.base := hΞ (interior_subset hη₀)
    have hexpν : Integrable (fun y => Real.exp ⟪η₀, y⟫_ℝ) ν := by
      rw [hνdef, integrable_map_measure (by fun_prop) E.stat_meas.aemeasurable]
      exact hη₀int
    haveI : SigmaFinite ν := sigmaFinite_of_integrable_exp hexpν
    -- integrability of the weighted transforms on `Ξ'`
    have hInt : ∀ t ∈ Ξ', Integrable (fun y => f y * Real.exp ⟪t, y⟫_ℝ) ν := by
      intro t ht
      have htnat : Integrable (fun x => Real.exp ⟪t, E.stat x⟫_ℝ) E.base := hΞ ht
      have hPeq : E.P t = E.base.tilted (fun x => ⟪t, E.stat x⟫_ℝ) := rfl
      have h1 : Integrable (fun x => f (E.stat x)) (E.P t) :=
        (integrable_map_measure hf_meas.aestronglyMeasurable E.stat_meas.aemeasurable).mp
          (hf_int ⟨t, ht⟩)
      rw [hPeq, integrable_tilted_iff htnat] at h1
      rw [hνdef, integrable_map_measure (by fun_prop) E.stat_meas.aemeasurable]
      change Integrable (fun x => f (E.stat x) * Real.exp ⟪t, E.stat x⟫_ℝ) E.base
      exact h1.congr (Filter.Eventually.of_forall fun x => by simp [smul_eq_mul, mul_comm])
    -- vanishing of the weighted transforms on `Ξ'`
    have hZero : ∀ t ∈ Ξ', ∫ y, f y * Real.exp ⟪t, y⟫_ℝ ∂ν = 0 := by
      intro t ht
      have htnat : Integrable (fun x => Real.exp ⟪t, E.stat x⟫_ℝ) E.base := hΞ ht
      have hPeq : E.P t = E.base.tilted (fun x => ⟪t, E.stat x⟫_ℝ) := rfl
      have hZt : (0 : ℝ) < ∫ x, Real.exp ⟪t, E.stat x⟫_ℝ ∂E.base := integral_exp_pos htnat
      have hZtne : (∫ x, Real.exp ⟪t, E.stat x⟫_ℝ ∂E.base) ≠ 0 := hZt.ne'
      have h0 : ∫ y, f y ∂((E.P t).map E.stat) = 0 := hf_zero ⟨t, ht⟩
      have hbridge : ∫ x, f (E.stat x) * Real.exp ⟪t, E.stat x⟫_ℝ ∂E.base
          = (∫ x, Real.exp ⟪t, E.stat x⟫_ℝ ∂E.base) * ∫ y, f y ∂((E.P t).map E.stat) := by
        rw [integral_map E.stat_meas.aemeasurable hf_meas.aestronglyMeasurable, hPeq,
            integral_tilted, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [smul_eq_mul]; field_simp
      have hI0 : ∫ x, f (E.stat x) * Real.exp ⟪t, E.stat x⟫_ℝ ∂E.base = 0 := by
        rw [hbridge, h0, mul_zero]
      rw [hνdef,
        integral_map E.stat_meas.aemeasurable
          (hf_meas.fun_mul (by fun_prop)).aestronglyMeasurable]
      exact hI0
    have hfν : f =ᵐ[ν] 0 := hsigned ‹SigmaFinite ν› hf_meas hInt hZero
    have habs : (E.P (θ : V)).map E.stat ≪ ν := by
      rw [hνdef]; exact (tilted_absolutelyContinuous E.base _).map E.stat_meas
    exact hfν.filter_mono habs.ae_le

/-- **Completeness of the natural statistic**: for a canonical exponential family on
`EuclideanSpace ℝ (Fin s)` whose parameter set has nonempty interior, the family of laws of
the natural statistic is complete. -/
theorem isCompleteStat_of_interior_nonempty {s : ℕ}
    (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s))) (Ξ' : Set (EuclideanSpace ℝ (Fin s)))
    -- USER-INPUT: the parameter set lies in the natural parameter set, so every member is a
    -- genuine probability measure of the family
    (hΞ : Ξ' ⊆ E.natSet)
    -- USER-INPUT: the parameter set has nonempty interior; the classical rank condition, and
    -- exactly the openness that Laplace-transform uniqueness requires
    (hint : (interior Ξ').Nonempty) :
    IsCompleteFamily fun θ : Ξ' => (E.P (θ : EuclideanSpace ℝ (Fin s))).map E.stat := by
  refine isCompleteFamily_of_signed E Ξ' hΞ hint ?_
  intro ν hν f hf hIntν hZeroν
  haveI := hν
  exact ae_eq_zero_of_integral_exp_inner_eq_zero hf hint hIntν hZeroν

/-- One-dimensional specialization of `isCompleteStat_of_interior_nonempty`: a real natural
statistic is complete whenever the parameter set has nonempty interior in the line. -/
theorem isCompleteStat_of_interior_nonempty_real (E : ExpFamily 𝓧 ℝ) (Ξ' : Set ℝ)
    -- USER-INPUT: the parameter set lies in the natural parameter set
    (hΞ : Ξ' ⊆ E.natSet)
    -- USER-INPUT: the parameter set has nonempty interior; classically, it contains an
    -- interval of positive length
    (hint : (interior Ξ').Nonempty) :
    IsCompleteFamily fun θ : Ξ' => (E.P (θ : ℝ)).map E.stat := by
  have hmul : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := fun a b =>
    (RCLike.inner_apply a b).trans (by simp [mul_comm])
  refine isCompleteFamily_of_signed E Ξ' hΞ hint ?_
  intro ν hν f hf hIntν hZeroν
  haveI := hν
  refine ae_eq_zero_of_integral_exp_smul_eq_zero hf hint ?_ ?_
  · intro t ht
    have := hIntν t ht
    simpa only [hmul] using this
  · intro t ht
    have := hZeroν t ht
    simpa only [hmul] using this

end StatLean.PointEstimation
