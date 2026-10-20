module
public import StatLean.HypothesisTesting.Tests.Defs
public import StatLean.PointEstimation.ExponentialFamily.Defs
public import StatLean.HypothesisTesting.Unbiased.PowerContinuity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# Admissibility of convex acceptance regions in an exponential family

Optimality within a restricted class — invariant tests, say — does not by itself make a
test admissible: a uniformly most powerful invariant test can be beaten uniformly by a
test that is not invariant. Admissibility therefore has to be established separately, and
the classical route for exponential families is *convexity of the acceptance region*.

Two notions are distinguished. A test `φ₀` is **`α`-admissible** against a class of
alternatives when no level-`α` competitor has power at least as large everywhere on that
class without matching it there. It is **d-admissible** when the two-sided comparison —
power at least as large on the alternatives *and* at most as large on the null — forces
equality of the power functions throughout. The second is the decision-theoretic notion;
neither implies the other in general.

The main theorem says: for an exponential family on the natural-statistic scale, if the
acceptance region `A₀` is **closed and convex**, and if every open half-space missing `A₀`
points in a direction along which the alternative class contains an unbounded ray, then
any competing acceptance region that is uniformly no worse than `A₀` on the alternatives
is contained in `A₀` up to a null set. The mechanism is geometric: a competitor
protruding from a closed convex set can be separated from it by a hyperplane, and pushing
the natural parameter to infinity along the direction of that hyperplane makes the
protruding part dominate the likelihood, so the competitor would have to be *strictly*
worse somewhere on the alternatives. Admissibility of `φ₀` follows; if in addition the
size `α` is attained at a point of the closure of the null class, the sharper
`α`-admissibility follows too.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.7
(Admissibility), Theorem 6.7.1 (in an exponential family a test with closed convex acceptance
region is d-admissible) and Corollary 6.7.1 (α-admissibility). (`TSH4 §6.7 Thm 6.7.1, Cor
6.7.1`.)

**Main results.**
* `IsDAdmissible`, `IsAlphaAdmissible` — the two admissibility notions;
* `statScaleFamily`, `statScaleBase` — the induced family and dominating measure on the
  natural-statistic scale;
* `acceptance_subset_of_power_le` — closed convex acceptance region: any uniformly
  no-worse competitor is a.e. contained in it;
* `isDAdmissible_of_convex_acceptance`, `isAlphaAdmissible_of_size_attained` — the two
  admissibility conclusions.

**Proof formalization notes.**
* Everything is stated **on the natural-statistic scale**: acceptance regions are subsets
  of `V = EuclideanSpace ℝ (Fin s)`, the model is the family of laws of the natural
  statistic (`statScaleFamily`), and the null set in the conclusion is measured by the
  image of the reference measure (`statScaleBase`). The source identifies the sample space
  with the statistic scale for this theorem; the sample-space reading is the pullback of
  the statement along the natural statistic.
* The ray condition is transcribed verbatim: *whenever* the open half-space
  `{t : ⟨a, t⟩ > c}` misses `A₀`, there is a point of the alternative class and a sequence
  of scalars tending to infinity keeping `θ* + λₙ a` in the alternative class.
* `IsDAdmissible` quantifies over **all** critical functions, with no level restriction —
  the level enters only in `IsAlphaAdmissible`. This matches the source's two definitions.
* `φ₀` is the **nonrandomized** indicator of the complement of `A₀`. The source notes that
  competitors may be randomized but that nonrandomization of `φ₀` is essential, which is
  why the acceptance region — not merely a critical function — is the primitive here.
* In the `α`-admissibility corollary, `θ₀` is required to lie in the natural parameter set
  as well as in the closure of the null class: this is the content of the source's
  "finite point", i.e. an actual parameter rather than a limit at infinity. Continuity of
  the power function in the natural parameter, used to pass from `θ₀` back into the null
  class, is a property of exponential families and is therefore *not* a hypothesis: it is
  a derivation obligation inside the proof, discharged by `continuous_power_expFamily`.
  **Signature amendment (documented deviation):** that continuity result is a
  `ContinuousOn` over `interior E.natSet` and is sharp — on the boundary of the natural
  parameter set the power function of an exponential family need not be continuous (see the
  counterexample in its docstring) — so "actual parameter" is read as `θ₀ ∈ interior
  E.natSet`, and `Θ_H ⊆ interior E.natSet` is added so that the level bound can be
  transported along `𝓝[Θ_H] θ₀`.
* The separation step is the geometric Hahn–Banach theorem for a closed convex set and an
  exterior point (`geometric_hahn_banach_closed_point` in Mathlib's
  `Analysis.LocallyConvex.Separation`). It is used through
  `exists_halfspace_of_measure_ne_zero`, which turns the pointwise separation into a
  *single* half-space carrying positive mass by second countability (Lindelöf) — an
  uncountable union of half-spaces would give no subadditivity.
* The tilt-asymptotic core is `acceptance_subset_of_power_le_const`, stated with a free
  finite constant `K`: pushing the natural parameter to infinity along the separating
  direction beats any constant, and it is the `K = ε⁻¹` instance that reduces a *randomized*
  competitor to its `ε`-superlevel sets, which is how `isDAdmissible_of_convex_acceptance`
  is obtained without a Neyman–Pearson reduction.

**Bibliographic comments.** Admissibility of tests with convex acceptance regions in
exponential families, and the ray condition delimiting the alternative classes against
which admissibility holds, come from the work of C. Stein ("The admissibility of Hotelling's
$T^2$-test," *Ann. Math. Statist.* **27** (1956), 616–623) and A. Birnbaum
("Characterizations of complete classes of tests of some multiparametric hypotheses, with
applications to likelihood ratio tests," *Ann. Math. Statist.* **26** (1955), 21–36); the
complete-class theory for such problems was extended by K. Matthes and D. R. Truax
("Tests of composite hypotheses for the multivariate exponential family," *Ann. Math.
Statist.* **38** (1967), 681–697). Admissibility of the one- and two-sided $t$-tests
against all invariant classes of alternatives is due to E. L. Lehmann and C. Stein
(1953), building on their earlier work on non-parametric hypotheses (*Ann. Math. Statist.*
**20** (1949), 28–45).
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation (ExpFamily)

/-! ## The two admissibility notions -/

section Admissible

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **d-admissibility** of `φ₀` for testing `Θ_H` against a class of alternatives `Θ'`:
if a critical function is at least as powerful as `φ₀` everywhere on `Θ'` and at most as
powerful everywhere on `Θ_H`, then its power function agrees with that of `φ₀` throughout
`Θ_H ∪ Θ'`. No level restriction is imposed on the competitor. -/
def IsDAdmissible (P : Θ → Measure 𝓧) (Θ_H Θ' : Set Θ) (φ₀ : 𝓧 → ℝ) : Prop :=
  ∀ φ : 𝓧 → ℝ, IsCriticalFn φ →
    (∀ θ ∈ Θ', power P φ₀ θ ≤ power P φ θ) →
    (∀ θ ∈ Θ_H, power P φ θ ≤ power P φ₀ θ) →
    ∀ θ ∈ Θ_H ∪ Θ', power P φ θ = power P φ₀ θ

/-- **`α`-admissibility** of `φ₀` for testing `Θ_H` against a class of alternatives `Θ'`:
every level-`α` competitor that is at least as powerful as `φ₀` everywhere on `Θ'` in fact
has the same power as `φ₀` there. -/
def IsAlphaAdmissible (P : Θ → Measure 𝓧) (Θ_H Θ' : Set Θ) (α : ℝ) (φ₀ : 𝓧 → ℝ) : Prop :=
  ∀ φ : 𝓧 → ℝ, IsCriticalFn φ → IsLevel P Θ_H φ α →
    (∀ θ ∈ Θ', power P φ₀ θ ≤ power P φ θ) →
    ∀ θ ∈ Θ', power P φ θ = power P φ₀ θ

end Admissible

/-! ## The exponential family on the natural-statistic scale -/

section StatScale

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {s : ℕ}

/-- The **induced family on the natural-statistic scale**: the law of the natural
statistic under the canonical member indexed by `η`. Off the natural parameter set the
member measure is the zero measure, and so is its image. -/
noncomputable def statScaleFamily (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    (η : EuclideanSpace ℝ (Fin s)) : Measure (EuclideanSpace ℝ (Fin s)) :=
  (E.P η).map E.stat

/-- The **dominating measure on the natural-statistic scale**: the image of the reference
measure of the family under the natural statistic. Null sets for it are the sets the
admissibility conclusion is allowed to ignore. -/
noncomputable def statScaleBase (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s))) :
    Measure (EuclideanSpace ℝ (Fin s)) :=
  E.base.map E.stat

end StatScale

/-! ## Closed convex acceptance regions are admissible -/

section Convex

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {s : ℕ}

/-- **Separation, in countable form.** If a set has positive measure outside a closed convex
`A₀`, then *some single* open half-space missing `A₀` already carries positive mass of it.

The complement of `A₀` is covered by the open half-spaces produced by
`geometric_hahn_banach_closed_point` at each of its points; a Euclidean space is
second countable, hence Lindelöf, so countably many of them suffice
(`TopologicalSpace.isOpen_iUnion_countable`) and countable subadditivity finishes. -/
private theorem exists_halfspace_of_measure_ne_zero {ρ : Measure (EuclideanSpace ℝ (Fin s))}
    {A₀ A : Set (EuclideanSpace ℝ (Fin s))}
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀) (hpos : ρ (A \ A₀) ≠ 0) :
    ∃ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ ∧ ρ (A ∩ {t | c < ⟪a, t⟫_ℝ}) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  refine hpos ?_
  -- a separating open half-space at every point off `A₀`
  have hsep : ∀ p : {q : EuclideanSpace ℝ (Fin s) // q ∉ A₀},
      ∃ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
        A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ ∧ (p : EuclideanSpace ℝ (Fin s)) ∈ {t | c < ⟪a, t⟫_ℝ} := by
    rintro ⟨p, hp⟩
    obtain ⟨f, u, hf, hup⟩ := geometric_hahn_banach_closed_point hA₀convex hA₀closed hp
    refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin s))).symm f, u, ?_, ?_⟩
    · ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and, not_lt, InnerProductSpace.toDual_symm_apply]
      exact fun hy => (hf y hy).le
    · simpa only [Set.mem_setOf_eq, InnerProductSpace.toDual_symm_apply] using hup
  choose a c hemp hmem using hsep
  have hopen : ∀ p, IsOpen {t : EuclideanSpace ℝ (Fin s) | c p < ⟪a p, t⟫_ℝ} := fun p =>
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  obtain ⟨Tc, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable
      (fun p => {t : EuclideanSpace ℝ (Fin s) | c p < ⟪a p, t⟫_ℝ}) hopen
  have hsub : A \ A₀ ⊆ ⋃ p ∈ Tc, (A ∩ {t | c p < ⟪a p, t⟫_ℝ}) := by
    intro x hx
    have hxU : x ∈ ⋃ p, {t : EuclideanSpace ℝ (Fin s) | c p < ⟪a p, t⟫_ℝ} :=
      Set.mem_iUnion.mpr ⟨⟨x, hx.2⟩, hmem ⟨x, hx.2⟩⟩
    rw [← hTU] at hxU
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hxU
    exact Set.mem_iUnion₂.mpr ⟨p, hp, ⟨hx.1, hxp⟩⟩
  exact measure_mono_null hsub
    ((measure_biUnion_null_iff hTc).mpr fun p _ => hcon (a p) (c p) (hemp p))

/-- **Constant-factor form of the containment lemma.** If `A₀` is closed and convex, the
ray condition holds, and the acceptance probability of `A` is bounded on the alternatives by
a *fixed multiple* `K` of that of `A₀`, then `A ⊆ A₀` up to a null set. The multiple costs
nothing: pushing the tilt to infinity beats any finite constant. `K = 1` gives
`acceptance_subset_of_power_le`; `K = ε⁻¹` handles a randomized competitor through its
`ε`-superlevel sets. -/
private theorem acceptance_subset_of_power_le_const
    (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {Θ' A₀ A : Set (EuclideanSpace ℝ (Fin s))}
    (hΘ' : Θ' ⊆ E.natSet)
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀)
    (hA₀meas : MeasurableSet A₀) (hAmeas : MeasurableSet A)
    (hray : ∀ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ →
        ∃ θstar ∈ Θ', ∃ lam : ℕ → ℝ,
          Filter.Tendsto lam Filter.atTop Filter.atTop ∧ ∀ n, θstar + lam n • a ∈ Θ')
    (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (hpow : ∀ θ ∈ Θ', statScaleFamily E θ A ≤ K * statScaleFamily E θ A₀) :
    statScaleBase E (A \ A₀) = 0 := by
  classical
  by_contra hne
  -- **Step 1.** Some open half-space missing `A₀` carries base mass of `A`.
  obtain ⟨a, c, hemp, hmass⟩ := exists_halfspace_of_measure_ne_zero hA₀closed hA₀convex hne
  -- **Step 2.** Shrink it to a *strictly* separated half-space, still of positive mass.
  have hunion : A ∩ {t | c < ⟪a, t⟫_ℝ}
      = ⋃ k : ℕ, A ∩ {t | c + 1 / ((k : ℝ) + 1) < ⟪a, t⟫_ℝ} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    refine ⟨fun ⟨ht, hlt⟩ => ?_, fun ⟨k, ht, hlt⟩ => ?_⟩
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      exact ⟨k, ht, by linarith⟩
    · have hp : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      exact ⟨ht, by linarith⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ,
      statScaleBase E (A ∩ {t | c + 1 / ((k : ℝ) + 1) < ⟪a, t⟫_ℝ}) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hmass (by rw [hunion]; exact measure_iUnion_null hall)
  set δ : ℝ := 1 / ((k : ℝ) + 1) with hδdef
  have hδpos : (0:ℝ) < δ := by rw [hδdef]; positivity
  -- **Step 3.** The ray along which the natural parameter is pushed to infinity.
  obtain ⟨θs, hθs, lam, hlamtop, hlamΘ⟩ := hray a c hemp
  have hTm : Measurable E.stat := E.stat_meas
  have hinnermeas : ∀ v : EuclideanSpace ℝ (Fin s),
      Measurable fun t : EuclideanSpace ℝ (Fin s) => ⟪v, t⟫_ℝ := fun v =>
    (continuous_const.inner continuous_id).measurable
  have hHmeas : MeasurableSet {t : EuclideanSpace ℝ (Fin s) | c + δ < ⟪a, t⟫_ℝ} :=
    measurableSet_lt measurable_const (hinnermeas a)
  set W : Set 𝓧 := E.stat ⁻¹' (A ∩ {t | c + δ < ⟪a, t⟫_ℝ}) with hWdef
  have hWmeas : MeasurableSet W := (hAmeas.inter hHmeas).preimage hTm
  have hWpos : E.base W ≠ 0 := by
    rw [hWdef, ← Measure.map_apply hTm (hAmeas.inter hHmeas)]
    exact hk
  have hbase0 : E.base ≠ 0 := fun h => hWpos (by rw [h]; rfl)
  -- The `θ*`-weight and its total / partial masses.
  set F : 𝓧 → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp ⟪θs, E.stat x⟫_ℝ) with hFdef
  have hFmeas : Measurable F :=
    (Real.measurable_exp.comp ((hinnermeas θs).comp hTm)).ennreal_ofReal
  set M : ℝ≥0∞ := ∫⁻ x, F x ∂E.base with hMdef
  set m : ℝ≥0∞ := ∫⁻ x in W, F x ∂E.base with hmdef
  have hMfin : M ≠ ⊤ := by
    rw [hMdef, hFdef, ← ofReal_integral_eq_lintegral_ofReal (hΘ' hθs)
      (ae_of_all _ fun x => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_ne_top
  have hMKfin : K * M ≠ ⊤ := ENNReal.mul_ne_top hK hMfin
  have hmM : m ≤ M := setLIntegral_le_lintegral _ _
  have hmfin : m ≠ ⊤ := ne_top_of_le_ne_top hMfin hmM
  have hmpos : m ≠ 0 := by
    intro h0
    have h1 : ∀ᵐ x ∂(E.base.restrict W), F x = 0 := (lintegral_eq_zero_iff hFmeas).mp h0
    rw [ae_iff] at h1
    have h3 : {x : 𝓧 | ¬ F x = 0} = Set.univ := by
      ext x
      simp only [hFdef, Set.mem_setOf_eq, Set.mem_univ, iff_true, ENNReal.ofReal_eq_zero, not_le]
      exact Real.exp_pos _
    rw [h3, Measure.restrict_apply_univ] at h1
    exact hWpos h1
  -- **Step 4.** Pick the index at which the tilt already dominates.
  set r : ℝ := (K * M).toReal / m.toReal with hrdef
  have hmtoReal : 0 < m.toReal := ENNReal.toReal_pos hmpos hmfin
  have hrnn : (0:ℝ) ≤ r := by rw [hrdef]; positivity
  obtain ⟨n, hn⟩ :=
    (hlamtop.eventually_ge_atTop (max 0 ((Real.log (r + 1) + 1) / δ))).exists
  have hlam0 : 0 ≤ lam n := le_trans (le_max_left _ _) hn
  have hlarge : r + 1 < Real.exp (lam n * δ) := by
    have h1 : (Real.log (r + 1) + 1) / δ ≤ lam n := le_trans (le_max_right _ _) hn
    rw [div_le_iff₀ hδpos] at h1
    calc r + 1 = Real.exp (Real.log (r + 1)) := (Real.exp_log (by linarith)).symm
      _ < Real.exp (lam n * δ) := Real.exp_lt_exp.mpr (by linarith)
  -- **Step 5.** The analytic core: the tilted comparison at that index.
  have hfinal : m * ENNReal.ofReal (Real.exp (lam n * δ)) ≤ K * M := by
    set η : EuclideanSpace ℝ (Fin s) := θs + lam n • a with hηdef
    have hηnat : η ∈ E.natSet := hΘ' (hlamΘ n)
    have hsplit : ∀ x : 𝓧,
        ⟪η, E.stat x⟫_ℝ = ⟪θs, E.stat x⟫_ℝ + lam n * ⟪a, E.stat x⟫_ℝ := by
      intro x; rw [hηdef, inner_add_left, real_inner_smul_left]
    have hZpos : 0 < ∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base := by
      rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hηnat]
      have hsupp : Function.support (fun x => Real.exp ⟪η, E.stat x⟫_ℝ) = Set.univ := by
        ext x; simp [Function.mem_support, (Real.exp_pos _).ne']
      rw [hsupp, Measure.measure_univ_pos]
      exact hbase0
    -- the normalizer factors out of both sides
    have hexpand : ∀ B : Set (EuclideanSpace ℝ (Fin s)), MeasurableSet B →
        statScaleFamily E η B
          = (∫⁻ x in E.stat ⁻¹' B, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base)
            * ENNReal.ofReal (∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base)⁻¹ := by
      intro B hB
      rw [statScaleFamily, Measure.map_apply hTm hB]
      simp only [ExpFamily.P]
      rw [tilted_apply' _ _ (hB.preimage hTm),
        ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr fun x => by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.exp_pos _).le]
    have hκ0 : ENNReal.ofReal (∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base)⁻¹ ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact inv_pos.mpr hZpos
    have hIle :
        (∫⁻ x in E.stat ⁻¹' A, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base)
          ≤ K * ∫⁻ x in E.stat ⁻¹' A₀, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base := by
      have h := hpow η (hlamΘ n)
      rw [hexpand A hAmeas, hexpand A₀ hA₀meas, ← mul_assoc] at h
      exact (ENNReal.mul_le_mul_iff_left hκ0 ENNReal.ofReal_ne_top).mp h
    -- upper bound on the `A₀` side
    have hupper :
        (∫⁻ x in E.stat ⁻¹' A₀, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base)
          ≤ M * ENNReal.ofReal (Real.exp (lam n * c)) := by
      have hpt : ∀ x ∈ E.stat ⁻¹' A₀,
          ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ)
            ≤ F x * ENNReal.ofReal (Real.exp (lam n * c)) := by
        intro x hx
        have hle : ⟪a, E.stat x⟫_ℝ ≤ c := by
          by_contra hgt
          push_neg at hgt
          have hmem : E.stat x ∈ A₀ ∩ {t | c < ⟪a, t⟫_ℝ} := ⟨hx, hgt⟩
          rw [hemp] at hmem
          exact hmem
        rw [hsplit x, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, hFdef]
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hle hlam0))) _
      calc ∫⁻ x in E.stat ⁻¹' A₀, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base
          ≤ ∫⁻ x in E.stat ⁻¹' A₀, F x * ENNReal.ofReal (Real.exp (lam n * c)) ∂E.base :=
            lintegral_mono_ae
              ((ae_restrict_iff' (hA₀meas.preimage hTm)).mpr (ae_of_all _ hpt))
        _ ≤ ∫⁻ x, F x * ENNReal.ofReal (Real.exp (lam n * c)) ∂E.base :=
            setLIntegral_le_lintegral _ _
        _ = M * ENNReal.ofReal (Real.exp (lam n * c)) := by
            rw [hMdef, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    -- lower bound on the `A` side
    have hlower : m * ENNReal.ofReal (Real.exp (lam n * (c + δ)))
        ≤ ∫⁻ x in E.stat ⁻¹' A, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base := by
      have hpt : ∀ x ∈ W, F x * ENNReal.ofReal (Real.exp (lam n * (c + δ)))
          ≤ ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) := by
        intro x hx
        have hgt : c + δ < ⟪a, E.stat x⟫_ℝ := hx.2
        rw [hsplit x, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, hFdef]
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hgt.le hlam0))) _
      calc m * ENNReal.ofReal (Real.exp (lam n * (c + δ)))
          = ∫⁻ x in W, F x * ENNReal.ofReal (Real.exp (lam n * (c + δ))) ∂E.base := by
            rw [hmdef, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ∫⁻ x in W, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base :=
            lintegral_mono_ae ((ae_restrict_iff' hWmeas).mpr (ae_of_all _ hpt))
        _ ≤ ∫⁻ x in E.stat ⁻¹' A, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base :=
            lintegral_mono' (Measure.restrict_mono (fun x hx => hx.1) le_rfl) le_rfl
    -- cancel the common factor `e^{λc}`
    have hchain : (m * ENNReal.ofReal (Real.exp (lam n * δ)))
        * ENNReal.ofReal (Real.exp (lam n * c))
          ≤ (K * M) * ENNReal.ofReal (Real.exp (lam n * c)) := by
      refine le_trans (le_of_eq ?_) (le_trans hlower (le_trans hIle ?_))
      · rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        ring_nf
      · rw [mul_assoc]; exact mul_le_mul_right hupper K
    refine (ENNReal.mul_le_mul_iff_left ?_ ENNReal.ofReal_ne_top).mp hchain
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  -- **Step 6.** But the chosen index makes the left-hand side strictly bigger.
  have hcontra : K * M < m * ENNReal.ofReal (Real.exp (lam n * δ)) := by
    have hMr : (K * M).toReal < m.toReal * (r + 1) := by
      rw [hrdef, mul_add, mul_one, mul_div_cancel₀ _ hmtoReal.ne']
      linarith
    calc K * M = ENNReal.ofReal (K * M).toReal := (ENNReal.ofReal_toReal hMKfin).symm
      _ < ENNReal.ofReal (m.toReal * (r + 1)) := by
          exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg |>.mpr hMr
      _ ≤ ENNReal.ofReal (m.toReal * Real.exp (lam n * δ)) := by
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left hlarge.le hmtoReal.le)
      _ = m * ENNReal.ofReal (Real.exp (lam n * δ)) := by
          rw [ENNReal.ofReal_mul hmtoReal.le, ENNReal.ofReal_toReal hmfin]
  exact absurd hfinal (not_le.mpr hcontra)

/-- **A competitor no worse than a closed convex acceptance region is contained in it.**
If `A₀` is closed and convex and every open half-space missing `A₀` points along a
direction in which the alternative class contains an unbounded ray, then any acceptance
region `A` whose acceptance probability is everywhere on the alternatives at most that of
`A₀` satisfies `A ⊆ A₀` up to a null set. -/
theorem acceptance_subset_of_power_le (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {Θ_H Θ' A₀ A : Set (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: null and alternative classes sit inside the natural parameter set,
    -- are nonempty and disjoint
    (hΘH : Θ_H ⊆ E.natSet) (hΘ' : Θ' ⊆ E.natSet)
    (hHne : Θ_H.Nonempty) (h'ne : Θ'.Nonempty) (hdisj : Disjoint Θ_H Θ')
    -- USER-INPUT: the acceptance region is closed and convex
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀)
    -- LEAN-ONLY: measurability of the two acceptance regions, needed to speak of their
    -- probabilities at all
    (hA₀meas : MeasurableSet A₀) (hAmeas : MeasurableSet A)
    -- USER-INPUT: the ray condition — whenever an open half-space misses `A₀`, the
    -- alternative class contains an unbounded ray in the direction of that half-space
    (hray : ∀ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ →
        ∃ θstar ∈ Θ', ∃ lam : ℕ → ℝ,
          Filter.Tendsto lam Filter.atTop Filter.atTop ∧ ∀ n, θstar + lam n • a ∈ Θ')
    -- USER-INPUT: `A` is nowhere on the alternatives a better acceptance region than `A₀`
    (hpow : ∀ θ ∈ Θ', statScaleFamily E θ A ≤ statScaleFamily E θ A₀) :
    statScaleBase E (A \ A₀) = 0 :=
  acceptance_subset_of_power_le_const E hΘ' hA₀closed hA₀convex hA₀meas hAmeas hray 1
    ENNReal.one_ne_top (by simpa using hpow)

/-- **The two-sided domination collapses the competitor onto the acceptance region.** If
`φ` dominates `1_{A₀ᶜ}` on the alternatives (`h1`) and is dominated by it at a *single*
parameter `θH` of the natural set (`h2`), then the two power functions agree throughout the
natural set. This is the analytic content shared by the two admissibility statements: in
`isDAdmissible_of_convex_acceptance` the point `θH` is any point of `Θ_H`, in
`isAlphaAdmissible_of_size_attained` it is the finite point `θ₀` at which the size is
attained. -/
private theorem power_eq_indicator_of_dominating
    (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {Θ' A₀ : Set (EuclideanSpace ℝ (Fin s))} {φ : EuclideanSpace ℝ (Fin s) → ℝ}
    {θH : EuclideanSpace ℝ (Fin s)}
    (hΘ' : Θ' ⊆ E.natSet)
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀)
    (hA₀meas : MeasurableSet A₀)
    (hray : ∀ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ →
        ∃ θstar ∈ Θ', ∃ lam : ℕ → ℝ,
          Filter.Tendsto lam Filter.atTop Filter.atTop ∧ ∀ n, θstar + lam n • a ∈ Θ')
    (hφ : IsCriticalFn φ)
    (h1 : ∀ θ ∈ Θ', power (statScaleFamily E) (A₀ᶜ.indicator fun _ => (1 : ℝ)) θ
      ≤ power (statScaleFamily E) φ θ)
    (hθHnat : θH ∈ E.natSet)
    (h2 : power (statScaleFamily E) φ θH
      ≤ power (statScaleFamily E) (A₀ᶜ.indicator fun _ => (1 : ℝ)) θH) :
    ∀ η ∈ E.natSet, power (statScaleFamily E) φ η
      = power (statScaleFamily E) (A₀ᶜ.indicator fun _ => (1 : ℝ)) η := by
  classical
  by_cases hb : E.base = 0
  · intro _ _
    simp [power, statScaleFamily, ExpFamily.P, hb, MeasureTheory.tilted_zero_measure]
  haveI : NeZero E.base := ⟨hb⟩
  have hφ₀meas : Measurable (A₀ᶜ.indicator fun _ => (1 : ℝ)) :=
    measurable_const.indicator hA₀meas.compl
  have hφ₀b : ∀ t, (A₀ᶜ.indicator fun _ => (1 : ℝ)) t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t
    by_cases h : t ∈ A₀ᶜ
    · rw [Set.indicator_of_mem h]; norm_num
    · rw [Set.indicator_of_notMem h]; norm_num
  have hprob : ∀ η ∈ E.natSet, IsProbabilityMeasure (statScaleFamily E η) := by
    intro η hη
    haveI : IsProbabilityMeasure (E.P η) :=
      MeasureTheory.isProbabilityMeasure_tilted hη
    exact Measure.isProbabilityMeasure_map E.stat_meas.aemeasurable
  have hIntg : ∀ f : EuclideanSpace ℝ (Fin s) → ℝ, Measurable f →
      (∀ t, f t ∈ Set.Icc (0 : ℝ) 1) → ∀ η ∈ E.natSet,
      Integrable f (statScaleFamily E η) := by
    intro f hf hbd η hη
    haveI := hprob η hη
    exact (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hbd t).1], (hbd t).2⟩)
  -- absolute continuity both ways between the tilted members and the base, on `natSet`
  have hac : ∀ η : EuclideanSpace ℝ (Fin s), statScaleFamily E η ≪ statScaleBase E :=
    fun η => Measure.AbsolutelyContinuous.map
      (MeasureTheory.tilted_absolutelyContinuous _ _) E.stat_meas
  have hacRev : ∀ η ∈ E.natSet, statScaleBase E ≪ statScaleFamily E η := fun η hη =>
    Measure.AbsolutelyContinuous.map
      (MeasureTheory.absolutelyContinuous_tilted hη) E.stat_meas
  -- **Step A.** The competitor rejects (value `1`) almost everywhere off `A₀`.
  have hkey : ∀ ε : ℝ, 0 < ε → ε < 1 →
      statScaleBase E ({t | φ t < 1 - ε} \ A₀) = 0 := by
    intro ε hε hε1
    refine acceptance_subset_of_power_le_const E hΘ' hA₀closed hA₀convex hA₀meas
      (measurableSet_lt hφ.1 measurable_const) hray (ENNReal.ofReal ε⁻¹)
      ENNReal.ofReal_ne_top ?_
    intro η hη
    haveI := hprob η (hΘ' hη)
    set Q : Measure (EuclideanSpace ℝ (Fin s)) := statScaleFamily E η with hQdef
    set Aε : Set (EuclideanSpace ℝ (Fin s)) := {t | φ t < 1 - ε} with hAεdef
    have hAεmeas : MeasurableSet Aε := measurableSet_lt hφ.1 measurable_const
    have hφint : Integrable φ Q := hIntg φ hφ.1 hφ.2 η (hΘ' hη)
    have hφ₀int : Integrable (A₀ᶜ.indicator fun _ => (1 : ℝ)) Q :=
      hIntg _ hφ₀meas hφ₀b η (hΘ' hη)
    -- `ε · Q(Aε) ≤ ∫ (1 − φ) ≤ ∫ (1 − φ₀) = Q(A₀)`
    have hstep1 : ε * (Q Aε).toReal ≤ ∫ t in Aε, (1 - φ t) ∂Q := by
      have hconst : ∫ _t in Aε, ε ∂Q = (Q Aε).toReal * ε := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]
      rw [mul_comm, ← hconst]
      refine setIntegral_mono_on (integrableOn_const (by finiteness)) ?_ hAεmeas ?_
      · exact ((integrable_const (1 : ℝ)).sub hφint).integrableOn
      · intro t ht
        have hlt : φ t < 1 - ε := ht
        linarith
    have hstep2 : ∫ t in Aε, (1 - φ t) ∂Q ≤ ∫ t, (1 - φ t) ∂Q :=
      setIntegral_le_integral ((integrable_const (1 : ℝ)).sub hφint)
        (ae_of_all _ fun t => by
          simp only [Pi.zero_apply]
          linarith [(hφ.2 t).2])
    have hstep3 : ∫ t, (1 - φ t) ∂Q = 1 - power (statScaleFamily E) φ η := by
      have hone : ∫ _t : EuclideanSpace ℝ (Fin s), (1 : ℝ) ∂Q = 1 := by simp
      rw [integral_sub (integrable_const (1 : ℝ)) hφint, hone]
      rfl
    have hstep4 : ∫ t, ((A₀ᶜ.indicator fun _ => (1 : ℝ)) t) ∂Q = (Q A₀ᶜ).toReal := by
      have := integral_indicator_one (μ := Q) hA₀meas.compl
      simpa [measureReal_def] using! this
    have hstep5 : 1 - power (statScaleFamily E) (A₀ᶜ.indicator fun _ => (1 : ℝ)) η
        = (Q A₀).toReal := by
      have hc : (Q A₀ᶜ).toReal = 1 - (Q A₀).toReal := by
        have h := measureReal_compl (μ := Q) hA₀meas
        simpa [measureReal_def, measure_univ] using h
      simp only [power, ← hQdef]
      rw [hstep4, hc]; ring
    have hreal : ε * (Q Aε).toReal ≤ (Q A₀).toReal := by
      have hmono := h1 η hη
      calc ε * (Q Aε).toReal ≤ ∫ t, (1 - φ t) ∂Q := le_trans hstep1 hstep2
        _ = 1 - power (statScaleFamily E) φ η := hstep3
        _ ≤ 1 - power (statScaleFamily E) (A₀ᶜ.indicator fun _ => (1 : ℝ)) η := by linarith
        _ = (Q A₀).toReal := hstep5
    -- back to `ℝ≥0∞`
    have hfin : Q Aε ≠ ⊤ := measure_ne_top _ _
    have hfin0 : Q A₀ ≠ ⊤ := measure_ne_top _ _
    calc Q Aε = ENNReal.ofReal (Q Aε).toReal := (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal (ε⁻¹ * (Q A₀).toReal) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← le_div_iff₀' hε, div_eq_inv_mul] at hreal
          exact hreal
      _ = ENNReal.ofReal ε⁻¹ * Q A₀ := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr hε.le), ENNReal.ofReal_toReal hfin0]
  have hlt1 : statScaleBase E ({t | φ t < 1} \ A₀) = 0 := by
    have hun : {t | φ t < 1} \ A₀
        = ⋃ k : ℕ, ({t | φ t < 1 - 1 / ((k : ℝ) + 2)} \ A₀) := by
      ext t
      simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_iUnion]
      refine ⟨fun ⟨hlt, hA⟩ => ?_, fun ⟨k, hlt, hA⟩ => ?_⟩
      · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        have hmono : 1 / ((k : ℝ) + 2) < 1 / ((k : ℝ) + 1) := by
          apply one_div_lt_one_div_of_lt
          · positivity
          · linarith
        exact ⟨k, by linarith, hA⟩
      · have hp : (0:ℝ) < 1 / ((k : ℝ) + 2) := by positivity
        exact ⟨by linarith, hA⟩
    rw [hun]
    refine measure_iUnion_null fun k => hkey _ (by positivity) ?_
    have h1' : (1:ℝ) ≤ (k : ℝ) + 2 := by
      have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h2' : (0:ℝ) < (k : ℝ) + 2 := by positivity
    rw [div_lt_one h2']; linarith
  -- **Step B.** Hence `φ₀ ≤ φ` off a base-null set, so `φ` is never less powerful.
  have hge : (A₀ᶜ.indicator fun _ => (1 : ℝ)) ≤ᵐ[statScaleBase E] φ := by
    have hsub : {t | ¬ ((A₀ᶜ.indicator fun _ => (1 : ℝ)) t ≤ φ t)} ⊆ {t | φ t < 1} \ A₀ := by
      intro t ht
      simp only [Set.mem_setOf_eq, not_le] at ht
      by_cases hA : t ∈ A₀
      · rw [Set.indicator_of_notMem (by simpa using hA)] at ht
        exact absurd ht (not_lt.mpr (hφ.2 t).1)
      · rw [Set.indicator_of_mem (by simpa using hA)] at ht
        exact ⟨ht, hA⟩
    rw [Filter.EventuallyLE, ae_iff]
    exact measure_mono_null hsub hlt1
  have hpowge : ∀ η ∈ E.natSet,
      power (statScaleFamily E) (A₀ᶜ.indicator fun _ => (1 : ℝ)) η
        ≤ power (statScaleFamily E) φ η := by
    intro η hη
    exact integral_mono_ae (hIntg _ hφ₀meas hφ₀b η hη) (hIntg φ hφ.1 hφ.2 η hη)
      (hge.filter_mono (hac η).ae_le)
  -- **Step C.** On the null class the two-sided domination forces `φ = φ₀` a.e.
  haveI := hprob θH hθHnat
  have hint0 : ∫ t, (φ t - (A₀ᶜ.indicator fun _ => (1 : ℝ)) t) ∂(statScaleFamily E θH) = 0 := by
    rw [integral_sub (hIntg φ hφ.1 hφ.2 θH hθHnat) (hIntg _ hφ₀meas hφ₀b θH hθHnat)]
    have := le_antisymm h2 (hpowge θH hθHnat)
    simp only [power] at this
    linarith
  have haeH : φ =ᵐ[statScaleFamily E θH] (A₀ᶜ.indicator fun _ => (1 : ℝ)) := by
    have hnn : (0 : EuclideanSpace ℝ (Fin s) → ℝ)
        ≤ᵐ[statScaleFamily E θH] fun t => φ t - (A₀ᶜ.indicator fun _ => (1 : ℝ)) t := by
      filter_upwards [hge.filter_mono (hac θH).ae_le] with t ht
      simpa using ht
    have hz := (integral_eq_zero_iff_of_nonneg_ae hnn
      ((hIntg φ hφ.1 hφ.2 θH hθHnat).sub (hIntg _ hφ₀meas hφ₀b θH hθHnat))).mp hint0
    filter_upwards [hz] with t ht
    simpa [sub_eq_zero] using ht
  have haeBase : φ =ᵐ[statScaleBase E] (A₀ᶜ.indicator fun _ => (1 : ℝ)) :=
    haeH.filter_mono (hacRev θH hθHnat).ae_le
  intro η₁ _
  simp only [power]
  exact integral_congr_ae (haeBase.filter_mono (hac η₁).ae_le)

/-- **A closed convex acceptance region is d-admissible.** -/
theorem isDAdmissible_of_convex_acceptance (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {Θ_H Θ' A₀ : Set (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: null and alternative classes sit inside the natural parameter set,
    -- are nonempty and disjoint
    (hΘH : Θ_H ⊆ E.natSet) (hΘ' : Θ' ⊆ E.natSet)
    (hHne : Θ_H.Nonempty) (h'ne : Θ'.Nonempty) (hdisj : Disjoint Θ_H Θ')
    -- USER-INPUT: the acceptance region is closed and convex
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀)
    -- LEAN-ONLY: measurability of the acceptance region
    (hA₀meas : MeasurableSet A₀)
    -- USER-INPUT: the ray condition
    (hray : ∀ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ →
        ∃ θstar ∈ Θ', ∃ lam : ℕ → ℝ,
          Filter.Tendsto lam Filter.atTop Filter.atTop ∧ ∀ n, θstar + lam n • a ∈ Θ') :
    IsDAdmissible (statScaleFamily E) Θ_H Θ'
      (A₀ᶜ.indicator fun _ => (1 : ℝ)) := by
  intro φ hφ h1 h2 θ hθ
  obtain ⟨θH, hθH⟩ := hHne
  exact power_eq_indicator_of_dominating E hΘ' hA₀closed hA₀convex hA₀meas hray hφ h1
    (hΘH hθH) (h2 θH hθH) θ (by rcases hθ with h | h; exacts [hΘH h, hΘ' h])

/-- **A closed convex acceptance region whose size is attained is `α`-admissible.** If in
addition the size of the test is `α` and there is an actual parameter point in the closure
of the null class at which the power equals `α`, then the test is `α`-admissible. -/
theorem isAlphaAdmissible_of_size_attained (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {Θ_H Θ' A₀ : Set (EuclideanSpace ℝ (Fin s))} {α : ℝ}
    {θ₀ : EuclideanSpace ℝ (Fin s)}
    -- USER-INPUT: null and alternative classes sit inside the natural parameter set,
    -- are nonempty and disjoint
    (hΘH : Θ_H ⊆ E.natSet) (hΘ' : Θ' ⊆ E.natSet)
    (hHne : Θ_H.Nonempty) (h'ne : Θ'.Nonempty) (hdisj : Disjoint Θ_H Θ')
    -- USER-INPUT: the acceptance region is closed and convex
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀)
    -- LEAN-ONLY: measurability of the acceptance region
    (hA₀meas : MeasurableSet A₀)
    -- USER-INPUT: the ray condition
    (hray : ∀ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ →
        ∃ θstar ∈ Θ', ∃ lam : ℕ → ℝ,
          Filter.Tendsto lam Filter.atTop Filter.atTop ∧ ∀ n, θstar + lam n • a ∈ Θ')
    -- USER-INPUT: the test has level `α` on the null class
    (hlevel : IsLevel (statScaleFamily E) Θ_H (A₀ᶜ.indicator fun _ => (1 : ℝ)) α)
    -- USER-INPUT: the size is attained at a point of the closure of the null class which
    -- is an actual parameter (the source's "finite point")
    -- AMENDMENT: "actual parameter" is read as membership of the *interior* of the natural
    -- parameter set, and the null class is likewise required to sit in that interior. This
    -- is forced: the step that turns the level hypothesis on `Θ_H` into a bound at `θ₀`
    -- is continuity of `η ↦ power (statScaleFamily E) φ η`, and `continuous_power_expFamily`
    -- (which is sharp — see the counterexample in its docstring) is a `ContinuousOn` over
    -- `interior E.natSet`. On the boundary of the natural parameter set the power function
    -- of an exponential family genuinely need not be continuous.
    (hΘHint : Θ_H ⊆ interior E.natSet)
    (hθ₀closure : θ₀ ∈ closure Θ_H) (hθ₀nat : θ₀ ∈ interior E.natSet)
    (hθ₀size : power (statScaleFamily E) (A₀ᶜ.indicator fun _ => (1 : ℝ)) θ₀ = α) :
    IsAlphaAdmissible (statScaleFamily E) Θ_H Θ' α
      (A₀ᶜ.indicator fun _ => (1 : ℝ)) := by
  intro φ hφ hlevelφ h1 θ hθ
  -- the power function on the statistic scale is the raw power of `φ ∘ T`
  have htrans : ∀ η : EuclideanSpace ℝ (Fin s),
      power (statScaleFamily E) φ η = powerAgainst (E.P η) (fun x => φ (E.stat x)) := by
    intro η
    simp only [power, powerAgainst, statScaleFamily]
    exact integral_map E.stat_meas.aemeasurable hφ.1.aestronglyMeasurable
  have hcont : ContinuousOn (fun η => power (statScaleFamily E) φ η) (interior E.natSet) := by
    simpa only [htrans] using
      continuous_power_expFamily E (φ := fun x => φ (E.stat x))
        ⟨hφ.1.comp E.stat_meas, fun x => hφ.2 _⟩
  -- the level bound passes from `Θ_H` to the finite point `θ₀` by continuity
  have hθ₀le : power (statScaleFamily E) φ θ₀ ≤ α := by
    haveI : (nhdsWithin θ₀ Θ_H).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hθ₀closure
    exact le_of_tendsto ((hcont θ₀ hθ₀nat).mono hΘHint)
      (Filter.eventually_of_mem self_mem_nhdsWithin hlevelφ)
  exact power_eq_indicator_of_dominating E hΘ' hA₀closed hA₀convex hA₀meas hray hφ h1
    (interior_subset hθ₀nat) (by rw [hθ₀size]; exact hθ₀le) θ (hΘ' hθ)

end Convex

end StatLean.HypothesisTesting
