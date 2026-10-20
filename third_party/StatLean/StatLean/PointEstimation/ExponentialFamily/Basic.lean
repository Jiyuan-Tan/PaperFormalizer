module
public import StatLean.PointEstimation.ExponentialFamily.Defs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Notation
public import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity

@[expose] public section

/-!
# Exponential families — basic structural properties

The elementary facts that make the data model of `ExponentialFamily.Defs` usable:

* `ExpFamily.natSet_convex` — the natural parameter set is convex (Hölder);
* `ExpFamily.isProbabilityMeasure_P` — members indexed by the natural parameter set are
  probability measures (for a nonzero reference measure);
* `ExpFamily.P_eq_zero_of_notMem` — the junk convention: off the natural parameter set the
  member is the zero measure;
* `ExpFamily.P_eq_withDensity` — the member in explicit density form,
  `dP_η/dν = exp(⟨η, T⟩ − A(η))`;
* `ExpFamily.P_ofDensity_eq` — the classical presentation `exp(⟨η, T⟩ − A(η))·h dμ` recovered
  for families built with `ExpFamily.ofDensity`;
* `ExpFamily.pow` / `ExpFamily.natSet_pow` / `ExpFamily.pi_P_eq_pow_P` — stability under
  i.i.d. sampling: the `n`-fold product of members is the member of the product family whose
  natural statistic is `x ↦ ∑ i, T(xᵢ)`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.5
(Exponential Families), equation (5.2) and the convexity of the natural parameter space.
(`TPE2 §1.5 (5.2)`.)

**Proof formalization notes.**
* Convexity of the natural parameter set is Hölder's inequality applied to the factorization
  `exp⟨a·η₀ + b·η₁, T⟩ = (exp⟨η₀, T⟩)^a · (exp⟨η₁, T⟩)^b` with conjugate exponents `1/a`,
  `1/b`. It holds for an arbitrary reference measure — no finiteness assumption.
* `isProbabilityMeasure_P` genuinely needs `E.base ≠ 0`: for the zero reference measure every
  member is the zero measure. This is the only place a nondegeneracy input is unavoidable
  among the density lemmas — `P_eq_withDensity` holds unconditionally because both sides
  collapse to `0` when `E.base = 0` (there `A(η) = log 0 = 0` and the normalizer is `0`).
* The i.i.d. statement is given as a **measure equality** rather than as an
  `IsCanonicalRepr`: the equality is the reusable form (it rewrites under any parametrization),
  and `IsCanonicalRepr (fun θ : Ξ' => Measure.pi fun _ => E.P θ) (E.pow n) (↑·)` follows from
  it by `fun θ => pi_P_eq_pow_P …` for any `Ξ' ⊆ E.natSet`.
* `pow` needs `[BorelSpace V] [SecondCountableTopology V]` only to know that a finite sum in
  `V` is measurable (`MeasurableAdd₂` is derived from `ContinuousAdd` there); both hold in
  every intended instantiation (`V = ℝ`, `V = EuclideanSpace ℝ (Fin s)`).
* `natSet_pow` is stated as the inclusion `E.natSet ⊆ (E.pow n).natSet`, which is the
  direction consumers need and is true for every `n` (including `n = 0`, where the product
  reference measure is a Dirac mass and the right-hand side is everything). The reverse
  inclusion also holds for `n ≥ 1` but is not needed.

**Bibliographic comments.** Exponential families originate with R. A. Fisher ("Two new
properties of mathematical likelihood," *Proc. R. Soc. Lond. A* **144** (1934), 285–307),
G. Darmois ("Sur les lois de probabilité à estimation exhaustive," *C. R. Acad. Sci. Paris*
**200** (1935), 1265–1266), B. O. Koopman ("On distributions admitting a sufficient
statistic," *Trans. Amer. Math. Soc.* **39** (1936), 399–409) and E. J. G. Pitman
("Sufficient statistics and intrinsic accuracy," *Proc. Camb. Phil. Soc.* **32** (1936),
567–579). Convexity of the natural parameter set and the closure of the class under
convolution of independent components are part of the systematic treatments of
O. Barndorff-Nielsen (*Information and Exponential Families in Statistical Theory*, Wiley,
1978) and L. D. Brown (*Fundamentals of Statistical Exponential Families*, IMS Lecture
Notes 9, 1986).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

namespace ExpFamily

section Members

variable [OpensMeasurableSpace V]

/-- The integrand `x ↦ exp⟨c, T x⟩` defining the natural parameter set is measurable: the linear
functional `⟨c, ·⟩` is continuous, hence measurable, and composes with the measurable statistic. -/
private theorem measurable_exp_inner (E : ExpFamily 𝓧 V) (c : V) :
    Measurable fun x => Real.exp ⟪c, E.stat x⟫_ℝ :=
  (((continuous_const.inner continuous_id).measurable).comp E.stat_meas).exp

/-- The natural parameter set is **convex**. -/
theorem natSet_convex (E : ExpFamily 𝓧 V) : Convex ℝ E.natSet := by
  rintro η₀ h₀ η₁ h₁ a b ha hb hab
  simp only [ExpFamily.natSet, Set.mem_setOf_eq] at h₀ h₁ ⊢
  refine ((h₀.const_mul a).add (h₁.const_mul b)).mono'
      (E.measurable_exp_inner _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, inner_add_left,
    real_inner_smul_left, real_inner_smul_left]
  calc Real.exp (a * ⟪η₀, E.stat x⟫_ℝ + b * ⟪η₁, E.stat x⟫_ℝ)
      = Real.exp ⟪η₀, E.stat x⟫_ℝ ^ a * Real.exp ⟪η₁, E.stat x⟫_ℝ ^ b := by
        rw [Real.exp_add, mul_comm a ⟪η₀, E.stat x⟫_ℝ, mul_comm b ⟪η₁, E.stat x⟫_ℝ,
          Real.exp_mul, Real.exp_mul]
    _ ≤ a * Real.exp ⟪η₀, E.stat x⟫_ℝ + b * Real.exp ⟪η₁, E.stat x⟫_ℝ :=
        Real.geom_mean_le_arith_mean2_weighted ha hb (Real.exp_pos _).le (Real.exp_pos _).le hab

/-- Members indexed by the natural parameter set are **probability measures**. -/
theorem isProbabilityMeasure_P (E : ExpFamily 𝓧 V) {η : V}
    -- USER-INPUT: nondegenerate reference measure; without it every member is the zero
    -- measure and the normalization is vacuous
    (hbase : E.base ≠ 0)
    -- USER-INPUT: the natural parameter lies where the family is defined
    (hη : η ∈ E.natSet) :
    IsProbabilityMeasure (E.P η) := by
  haveI : NeZero E.base := ⟨hbase⟩
  exact isProbabilityMeasure_tilted hη

/-- **Junk convention**: off the natural parameter set the member is the zero measure. -/
theorem P_eq_zero_of_notMem (E : ExpFamily 𝓧 V) {η : V}
    -- LEAN-ONLY: the parameter is outside the domain of definition; records the junk value
    -- inherited from `Measure.tilted`, so that consumers never need a side condition
    (hη : η ∉ E.natSet) :
    E.P η = 0 :=
  tilted_of_not_integrable hη

/-- **Explicit density form** of a member: `dP_η/dν = exp(⟨η, T⟩ − A(η))`. -/
theorem P_eq_withDensity (E : ExpFamily 𝓧 V) {η : V}
    -- USER-INPUT: the natural parameter lies where the family is defined
    (hη : η ∈ E.natSet) :
    E.P η = E.base.withDensity
      fun x => ENNReal.ofReal (Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η)) := by
  rcases eq_or_ne E.base 0 with hb | hb
  · rw [show E.P η = E.base.tilted fun x => ⟪η, E.stat x⟫_ℝ from rfl, hb,
      tilted_zero_measure, withDensity_zero_left]
  · haveI : NeZero E.base := ⟨hb⟩
    have hpos : 0 < ∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base := integral_exp_pos hη
    rw [show E.P η = E.base.tilted fun x => ⟪η, E.stat x⟫_ℝ from rfl, Measure.tilted]
    refine withDensity_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [show E.logPartition η = Real.log (∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base) from rfl,
      Real.exp_sub, Real.exp_log hpos]

/-- **Classical presentation**: for a family built by absorbing a carrier `h` into the
reference measure, the member has density `exp(⟨η, T x⟩ − A(η))·h(x)` with respect to `μ`. -/
theorem P_ofDensity_eq (μ : Measure 𝓧) {h : 𝓧 → ℝ≥0∞}
    -- USER-INPUT: measurable carrier; the classical presentation's `h`
    (hh : Measurable h)
    {T : 𝓧 → V}
    -- USER-INPUT: measurable natural statistic
    (hT : Measurable T) {η : V}
    -- USER-INPUT: the natural parameter lies where the family is defined
    (hη : η ∈ (ofDensity μ h T hT).natSet) :
    (ofDensity μ h T hT).P η
      = μ.withDensity fun x =>
          ENNReal.ofReal (Real.exp (⟪η, T x⟫_ℝ - (ofDensity μ h T hT).logPartition η)) * h x := by
  set A := (ofDensity μ h T hT).logPartition η with hA
  have hg : Measurable fun x => ENNReal.ofReal (Real.exp (⟪η, T x⟫_ℝ - A)) :=
    ((((continuous_const.inner continuous_id).measurable.comp hT).sub
      measurable_const).exp).ennreal_ofReal
  rw [P_eq_withDensity (ofDensity μ h T hT) hη]
  change (μ.withDensity h).withDensity (fun x => ENNReal.ofReal (Real.exp (⟪η, T x⟫_ℝ - A)))
      = μ.withDensity fun x => ENNReal.ofReal (Real.exp (⟪η, T x⟫_ℝ - A)) * h x
  rw [← withDensity_mul _ hh hg]
  exact withDensity_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

end Members

section Product

variable [BorelSpace V] [SecondCountableTopology V]

/-- The **`n`-fold i.i.d. product family**: the reference measure is the product of `n` copies
of `E.base` and the natural statistic is `x ↦ ∑ i, T(xᵢ)`. This is the exponential family in
which an i.i.d. sample of size `n` from `E` lives; its log-partition function is `n·A(η)`. -/
noncomputable def pow (E : ExpFamily 𝓧 V) (n : ℕ) : ExpFamily (Fin n → 𝓧) V where
  base := Measure.pi fun _ => E.base
  stat := fun x => ∑ i, E.stat (x i)
  stat_meas := by
    have h : ∀ i : Fin n, Measurable fun x : Fin n → 𝓧 => E.stat (x i) := fun i =>
      E.stat_meas.comp (measurable_pi_apply i)
    exact Finset.measurable_sum Finset.univ fun i _ => h i

/-- The natural parameter set of the product family contains that of the one-observation
family. -/
theorem natSet_pow (E : ExpFamily 𝓧 V)
    -- LEAN-ONLY: σ-finiteness of the reference measure, so that the product measure has its
    -- expected Tonelli behaviour; every dominated statistical model satisfies it
    [SigmaFinite E.base] (n : ℕ) :
    E.natSet ⊆ (E.pow n).natSet := by
  intro η hη
  simp only [ExpFamily.natSet, Set.mem_setOf_eq] at hη ⊢
  have hprod : Integrable (fun x : Fin n → 𝓧 => ∏ i, Real.exp ⟪η, E.stat (x i)⟫_ℝ)
      (Measure.pi fun _ => E.base) := Integrable.fintype_prod fun _ => hη
  refine hprod.congr (Filter.Eventually.of_forall fun x => ?_)
  change ∏ i, Real.exp ⟪η, E.stat (x i)⟫_ℝ = Real.exp ⟪η, (E.pow n).stat x⟫_ℝ
  rw [show (E.pow n).stat x = ∑ i, E.stat (x i) from rfl, inner_sum, Real.exp_sum]

/-- **Stability under i.i.d. sampling**: the `n`-fold product of the member `P_η` is the
member of the product family at the same natural parameter. -/
theorem pi_P_eq_pow_P (E : ExpFamily 𝓧 V)
    -- LEAN-ONLY: σ-finiteness of the reference measure, needed for Tonelli on the product
    [SigmaFinite E.base] (n : ℕ) {η : V}
    -- USER-INPUT: the natural parameter lies where the family is defined
    (hη : η ∈ E.natSet) :
    (Measure.pi fun _ : Fin n => E.P η) = (E.pow n).P η := by
  have hηpow : η ∈ (E.pow n).natSet := E.natSet_pow n hη
  have hfun : (fun x : Fin n → 𝓧 => Real.exp ⟪η, ∑ i, E.stat (x i)⟫_ℝ)
      = fun x => ∏ i, Real.exp ⟪η, E.stat (x i)⟫_ℝ := by
    funext x; rw [inner_sum, Real.exp_sum]
  have hApow : (E.pow n).logPartition η = (n : ℝ) * E.logPartition η := by
    change Real.log (∫ x : Fin n → 𝓧, Real.exp ⟪η, ∑ i, E.stat (x i)⟫_ℝ
          ∂(Measure.pi fun _ => E.base))
        = (n : ℝ) * Real.log (∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base)
    rw [hfun, integral_fintype_prod_eq_pow (f := fun y => Real.exp ⟪η, E.stat y⟫_ℝ),
      Fintype.card_fin, Real.log_pow]
  have hg : Measurable fun x => ENNReal.ofReal (Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η)) :=
    (((continuous_const.inner continuous_id).measurable.comp E.stat_meas).sub
      measurable_const).exp.ennreal_ofReal
  haveI : IsZeroOrProbabilityMeasure (E.base.withDensity
      fun x => ENNReal.ofReal (Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η))) := by
    rw [← P_eq_withDensity E hη, show E.P η = E.base.tilted fun x => ⟪η, E.stat x⟫_ℝ from rfl]
    infer_instance
  rw [show (Measure.pi fun _ : Fin n => E.P η)
        = Measure.pi fun _ : Fin n => E.base.withDensity
            fun x => ENNReal.ofReal (Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η)) by
      simp_rw [P_eq_withDensity E hη],
    ← pi_withDensity_prod (fun _ : Fin n => hg), P_eq_withDensity (E.pow n) hηpow, hApow]
  refine withDensity_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change ∏ i, ENNReal.ofReal (Real.exp (⟪η, E.stat (x i)⟫_ℝ - E.logPartition η))
      = ENNReal.ofReal (Real.exp (⟪η, (E.pow n).stat x⟫_ℝ - (n : ℝ) * E.logPartition η))
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  congr 1
  rw [show (E.pow n).stat x = ∑ i, E.stat (x i) from rfl, ← Real.exp_sum]
  congr 1
  rw [Finset.sum_sub_distrib, ← inner_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

end Product

end ExpFamily

end StatLean.PointEstimation
