module
public import StatLean.HypothesisTesting.Unbiased.ConditionalExpFamily
public import StatLean.HypothesisTesting.Unbiased.PowerContinuity
public import StatLean.HypothesisTesting.ForMathlib.QuantileFunction
public import StatLean.PointEstimation.Completeness.Defs
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Convex.Topology
public import StatLean.PointEstimation.ForMathlib.MGFUniquenessPi

@[expose] public section

/-!
# UMP unbiased tests for multiparameter exponential families

For a canonical `(U, T)` exponential family
`dP^{U,T}_{θ,ϑ}(u,t) = C(θ,ϑ)·exp(θu + ⟪ϑ,t⟫)·dν(u,t)` on a convex parameter set `Ω` that is
not contained in a proper linear subspace, the four testing problems about the parameter of
interest `θ` (the nuisance parameters `ϑ` being unspecified),

| null | alternative | test |
|---|---|---|
| `θ ≤ θ₀` | `θ > θ₀` | reject for large `u` |
| `θ ≤ θ₁` or `θ ≥ θ₂` | `θ₁ < θ < θ₂` | reject *inside* an interval in `u` |
| `θ₁ ≤ θ ≤ θ₂` | `θ < θ₁` or `θ > θ₂` | reject *outside* an interval in `u` |
| `θ = θ₀` | `θ ≠ θ₀` | reject *outside* an interval in `u` |

all admit UMP unbiased level-`α` tests, obtained by solving the corresponding one-parameter
problem **conditionally on `T = t`** and reinterpreting the result as a test of `(U, T)`.
The names `_inside` / `_outside` refer to the shape of the rejection region in `u`, not to
the shape of the null set.

**⚠ The four optimality theorems were FALSE in the frozen form transcribed here**, for two
independent reasons, and all four have been **REPAIRED**.

1. *The transcription dropped the source's standing convention that the observation is the
   sufficient statistic.* `IsCanonicalUT` constrains only the law of the pair `(U, T)`, while
   `IsUMPU` quantifies over all critical functions of the sample space; taking `U` and `T`
   constant makes the hypotheses vacuous and the conclusion false. Explicit counterexamples
   are formalized in the section `ConditionalUMPUCounterexample` below, one per theorem. The
   repair is the added hypothesis `hsuff : SufficiencyReducible P Ω U T`; the counterexamples
   are retained because they are what certifies that it is not decoration.
2. *The non-degeneracy hypothesis was mis-transcribed.* The source's "`Ω` is not contained in
   a linear space of dimension less than `k+1`" means an *affine* flat; the frozen
   `Submodule.span ℝ Ω = ⊤` is strictly weaker and does not suffice. For `Ξ = ℝ` the convex
   set `Ω = {(θ, 1 − θ) : θ ∈ [-1,1]}` has full linear span and reaches strictly below and
   above `θ₀ = 0`, yet its boundary surface `{p ∈ Ω | p.1 = 0}` is a *single point*, so the
   boundary family of laws of `T` is a one-element family and carries no completeness — the
   step from similarity to Neyman structure collapses. The repair is the added hypothesis
   `hΩ_aff : affineSpan ℝ Ω = ⊤` (see `boundedlyComplete_boundary`).

The two remaining amendments are the instances `[BorelSpace Ξ] [FiniteDimensional ℝ Ξ]`: the
first is what makes the canonical exponent measurable, the second is what turns
`hΩ_aff` into nonempty interior and hence makes the boundary slice `k`-dimensional.

**Status.** `isUMPU_conditional_oneSided`, `_inside` and `_outside` are **PROVED**, with no
lifted brick left: `boundedlyComplete_boundary` (bounded completeness of the laws of `T` over
a boundary surface — the Lehmann–Scheffé input) is now proved here, by writing every boundary
law of `T` as an exponential tilt of the law at one interior boundary parameter and applying
Laplace-transform uniqueness through the isometry
`Ξ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ Ξ))`. `isUMPU_conditional_point` additionally needs
the *derivative* side condition for a competitor, and is documented at the theorem.

The machinery is elementary and self-contained: conditionally on `T = t` all members of the
family are exponential tilts of one another (`ae_condDistrib_expTilt`), and every optimality
statement is the variation-diminishing inequality `∫ g·(k e^{cu} − k e^{cC}) ≥ 0` for a `g`
changing sign at the critical value (`integral_expTilt_signed`, and its two-threshold
companion `integral_expTilt_signed_interval` built from the three-exponential separation).
Continuity of the power function along segments of `Ω` — proved here from convexity alone,
by the two-point envelope `e^{(1−s)a+sb} ≤ e^a + e^b` — is what upgrades the level inequality
at a boundary parameter to similarity.

The constants are functions of `t`, determined by conditional size equations; the point-null
case carries in addition the conditional derivative condition
`E_{θ₀}[U·φ ∣ t] = α·E_{θ₀}[U ∣ t]`, which is what unbiasedness contributes and which may
not be dropped.

Contents:

* `condOneSidedTest`, `condInsideTest`, `condOutsideTest` — the three conditional critical
  functions, as functions of `(u, t)`;
* `isUMPU_conditional_oneSided` / `_inside` / `_outside` / `_point` — the four optimality
  theorems;
* `exists_measurable_conditional_constants` — measurable selection of the constants;
* `expTilt`, `integral_expTilt_signed`, `integral_expTilt_signed_interval` — the fibrewise
  variation-diminishing inequalities, in one- and two-threshold form;
* `ae_condDistrib_expTilt`, `integral_comp_sign_of_condZero`,
  `integral_comp_sign_of_condZero_interval` — the conditional-to-unconditional engines;
* `tendsto_integral_canonical_segment`, `integral_comp_eq_of_le_of_segment` — continuity of
  the power along segments of `Ω`, and the similarity it yields at a boundary parameter;
* `interior_slice_nonempty`, `boundedlyComplete_boundary` — the geometry of the boundary slice
  and the Lehmann–Scheffé bounded-completeness input;
* `ConditionalUMPUCounterexample.not_isUMPU_conditional_*_counterexample` — the four
  refutations of the frozen optimality statements;
* `reparamUT`, `statTransformUT`, `inner_exponent_reparam`, `isCanonicalUT_reparam` — the
  reduction to canonical form for a parameter of interest `θ* = a₀θ + ⟪a, ϑ⟫`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 4 (Unbiasedness: Theory
and First Applications), §4.4 (UMP Unbiased Tests for Multiparameter Exponential Families),
Theorem 4.4.1 (the UMP unbiased tests `φ₁`–`φ₄` for a multiparameter exponential family).
(`TSH4 §4.4 Thm 4.4.1`.)

**Proof formalization notes.**
* "The parameter set is not contained in a linear space of dimension less than `k+1`" is
  transcribed as `Submodule.span ℝ Ω = ⊤` in the ambient `ℝ × Ξ`: for a `k`-dimensional
  nuisance space `Ξ` the ambient dimension is `k+1`, so spanning the ambient space is
  exactly the stated non-degeneracy. Together with convexity it is what makes each boundary
  slice `ω_j = {(θ,ϑ) ∈ Ω : θ = θ_j}` contain a `k`-dimensional rectangle, hence makes the
  family of laws of `T` on `ω_j` complete — the input that upgrades similarity to Neyman
  structure.
* The conditional size conditions are imposed for **almost every** `t` rather than for every
  `t`. This is the weaker hypothesis (hence the stronger theorem), it is all the averaging
  identity `integral_eq_integral_condDistrib` consumes, and it is what the measurable
  selection actually delivers, since the conditional distributions themselves are only
  determined up to null sets.
* The size conditions are imposed at *every* parameter of `Ω` whose coordinate of interest
  equals the relevant `θ_j`; by `condDistrib_eq_of_fst_eq` this is no stronger than
  imposing them at one such parameter, but stating it this way keeps the theorems
  independent of that derivation.
* The constants `C(·)`, `γ(·)` and their defining equations are *data*: they are supplied by
  the caller and their existence is the separate theorem
  `exists_measurable_conditional_constants`.
* Only members of `P` with parameter in `Ω` are evaluated: both the null and the alternative
  sets in the conclusions are subsets of `Ω`.

**Bibliographic comments.** The construction of UMP unbiased tests for multiparameter
exponential families by conditioning on the sufficient statistic for the nuisance parameters
is due to J. Neyman and E. S. Pearson ("Contributions to the theory of testing statistical
hypotheses," *Statistical Research Memoirs* **1** (1936), 1–37) and J. Neyman ("Outline of a
theory of statistical estimation based on the classical theory of probability," *Phil.
Trans. R. Soc. A* **236** (1937), 333–380); the completeness theory underlying the step from
similar tests to tests with Neyman structure is due to E. L. Lehmann and H. Scheffé
("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10** (1950), 305–340;
**15** (1955), 219–236).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

variable {𝓧 Ξ : Type*} [MeasurableSpace 𝓧]
  [NormedAddCommGroup Ξ] [InnerProductSpace ℝ Ξ] [MeasurableSpace Ξ]

/-! ## The conditional critical functions -/

/-- **One-sided conditional test**: on the surface `T = t`, reject when `u` exceeds the
critical value `C₀(t)`, randomize with probability `γ₀(t)` when `u = C₀(t)`.

Edge behaviour: the value at `u = C₀(t)` is `γ₀(t)` regardless of whether `γ₀ t ∈ [0,1]`;
the membership is a hypothesis of the theorems, not of the definition. -/
noncomputable def condOneSidedTest (C₀ γ₀ : Ξ → ℝ) : ℝ × Ξ → ℝ :=
  fun z => if C₀ z.2 < z.1 then 1 else if z.1 = C₀ z.2 then γ₀ z.2 else 0

/-- **Inside-interval conditional test**: on the surface `T = t`, reject when `u` lies
strictly between `C₁(t)` and `C₂(t)`, randomizing at the two endpoints.

Edge behaviour: if `C₁ t = C₂ t` the lower randomization value `γ₁ t` takes precedence. -/
noncomputable def condInsideTest (C₁ C₂ γ₁ γ₂ : Ξ → ℝ) : ℝ × Ξ → ℝ :=
  fun z => if C₁ z.2 < z.1 ∧ z.1 < C₂ z.2 then 1
    else if z.1 = C₁ z.2 then γ₁ z.2
    else if z.1 = C₂ z.2 then γ₂ z.2 else 0

/-- **Outside-interval conditional test**: on the surface `T = t`, reject when `u` lies
outside `[C₁(t), C₂(t)]`, randomizing at the two endpoints.

Edge behaviour: if `C₁ t = C₂ t` the lower randomization value `γ₁ t` takes precedence. -/
noncomputable def condOutsideTest (C₁ C₂ γ₁ γ₂ : Ξ → ℝ) : ℝ × Ξ → ℝ :=
  fun z => if z.1 < C₁ z.2 ∨ C₂ z.2 < z.1 then 1
    else if z.1 = C₁ z.2 then γ₁ z.2
    else if z.1 = C₂ z.2 then γ₂ z.2 else 0

/-! ## The sufficiency-reduction hypothesis (the repair) -/

/-- **Sufficiency of `(U, T)`, in the form the optimality theorems consume.** Every critical
function on the sample space is matched, *in power at every parameter of `Ω`*, by a critical
function of the pair `(U, T)` alone.

This is the operative content of "`(U, T)` is a sufficient statistic for `P` on `Ω`": the
Rao–Blackwellization `ψ' = E[ψ ∣ U, T]` is parameter-free by sufficiency, is again a critical
function, and has the same power as `ψ` at every parameter. It holds trivially — with
`ψ' = ψ` — in the source's setting, where the sample space *is* the range of `(U, T)`
(`sufficiencyReducible_prod`), and it fails in the counterexample family below, where
`(U, T)` is constant. -/
def SufficiencyReducible (P : ℝ × Ξ → Measure 𝓧) (Ω : Set (ℝ × Ξ)) (U : 𝓧 → ℝ) (T : 𝓧 → Ξ) :
    Prop :=
  ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → ∃ ψ' : ℝ × Ξ → ℝ, IsCriticalFn ψ' ∧
    ∀ p ∈ Ω, ∫ x, ψ' (U x, T x) ∂(P p) = ∫ x, ψ x ∂(P p)

/-- **In the source's setting the reduction hypothesis is vacuous.** When the sample space is
the range `ℝ × Ξ` of the sufficient statistic and `(U, T) = (Prod.fst, Prod.snd)`, every
critical function already *is* a function of `(U, T)`. So the amended theorems specialize to
exactly the statement of `TSH4 §4.4 Thm 4.4.1`. -/
theorem sufficiencyReducible_prod (P : ℝ × Ξ → Measure (ℝ × Ξ)) (Ω : Set (ℝ × Ξ)) :
    SufficiencyReducible P Ω Prod.fst Prod.snd :=
  fun ψ hψ => ⟨ψ, hψ, fun _ _ => rfl⟩

/-! ## ⚠ The four optimality statements are FALSE as stated: an explicit counterexample

`IsCanonicalUT P Ω U T ν C` constrains **only the law of the pair `(U, T)`**; it says nothing
about the rest of the sample space `𝓧`. `IsUMPU`, on the other hand, demands optimality
against *every* critical function on `𝓧`. So as soon as `𝓧` carries information about the
parameter of interest that `(U, T)` does not see, a test built from `(U, T)` alone loses.
Taking `U` and `T` **constant** makes `IsCanonicalUT` hold vacuously (with `ν` a Dirac mass
and `C ≡ 1`) while leaving `P` completely free, which is the counterexample below:

* `𝓧 = Bool`, `Ξ = ℝ`, `U ≡ 0`, `T ≡ 0`, `ν = δ₍₀,₀₎`, `C ≡ 1`, `Ω = univ`, `α = 1/2`;
* `P p =` the Dirac mass at `true` when `p` is in the alternative set, the fair coin
  otherwise;
* the conditional test with `C₀ ≡ 0` and boundary weight `γ₀ ≡ 1/2` is the **constant**
  `1/2`, and its conditional size is `1/2 = α` on every surface, so all hypotheses hold;
* but `ψ = 1{bit = true}` is a critical function, unbiased at level `1/2` (power `1/2` on the
  null set, power `1` on the alternative), and strictly beats the conditional test.

The construction is uniform in the alternative set, so the *same* family refutes all four
theorems (`_oneSided`, `_inside`, `_outside`, `_point`); the four refutations are
`not_isUMPU_conditional_oneSided_counterexample` and its siblings below.

**REPAIR (APPLIED).** The source (TSH4 §4.4 Thm 4.4.1) states the theorem for the model *of
the sufficient statistic*: there `𝓧` **is** the range of `(U, T)`. Rather than specialize the
type — which would prevent the theorems from being applied to a model carried on its own
sample space — the four statements now carry the single extra hypothesis
`SufficiencyReducible P Ω U T`: every critical function on `𝓧` is matched, *in power at every
parameter of `Ω`*, by a critical function of `(U, T)` alone. This is exactly the operative
content of "`(U, T)` is sufficient for `P` on `Ω`" (Rao–Blackwellize: `E[ψ ∣ U, T]` does not
depend on the parameter and has the same power at every parameter), and it holds trivially,
with `ψ' = ψ`, in the source's setting `𝓧 = ℝ × Ξ`, `U = Prod.fst`, `T = Prod.snd`
(`sufficiencyReducible_prod`). It fails in the counterexample family, where `(U, T)` is
constant and the auxiliary bit of `𝓧` is invisible to it — which is what makes the
counterexample a counterexample.

A second, independent defect of the frozen statements — the mis-transcribed non-degeneracy
hypothesis — is described in the file docstring and at `boundedlyComplete_boundary`; it is
repaired by the added `hΩ_aff : affineSpan ℝ Ω = ⊤`.

After both repairs, `_oneSided`, `_inside` and `_outside` are proved. Contrary to what an
earlier draft of this file recorded, the boundary device needs neither
`PowerContinuity.continuous_power_expFamily` nor `Ω ⊆ interior natSet`: continuity of the
power along a segment of `Ω` follows from convexity of `Ω` alone, by the two-point envelope
(`tendsto_integral_canonical_segment`). Completeness of the laws of `T` on a boundary slice is
`boundedlyComplete_boundary`, proved here. What remains is — for the point null only — the
derivative side condition, documented at `isUMPU_conditional_point`.
-/

namespace ConditionalUMPUCounterexample

/-- Interest statistic of the counterexample: constant, hence carrying no information. -/
def cxU : Bool → ℝ := fun _ => 0

/-- Nuisance statistic of the counterexample: constant. -/
def cxT : Bool → ℝ := fun _ => 0

lemma measurable_cxU : Measurable cxU := measurable_const

lemma measurable_cxT : Measurable cxT := measurable_const

/-- The fair coin on `Bool`. -/
noncomputable def cxCoin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure cxCoin := by
  refine ⟨?_⟩
  simp only [cxCoin, Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.add_halves 1

lemma cxCoin_true : cxCoin {true} = 1 / 2 := by simp [cxCoin]

open Classical in
/-- The model: an auxiliary bit which is deterministically `true` on the alternative set `K`
and a fair coin elsewhere. The statistic `(U, T)` is blind to it. -/
noncomputable def cxP (K : Set (ℝ × ℝ)) : ℝ × ℝ → Measure Bool :=
  fun p => if p ∈ K then Measure.dirac true else cxCoin

instance cxP_isProbabilityMeasure (K : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    IsProbabilityMeasure (cxP K p) := by
  rw [cxP]; split <;> infer_instance

/-- The base measure of the counterexample: the Dirac mass at the only value `(U, T)`
takes. -/
noncomputable def cxν : Measure (ℝ × ℝ) := Measure.dirac (0, 0)

/-- The competitor: reject exactly when the auxiliary bit is `true`. -/
def cxψ : Bool → ℝ := fun b => if b then 1 else 0

/-- **The canonical form holds vacuously.** With a constant statistic the law of `(U, T)` is
a Dirac mass for every parameter, and the canonical density evaluates to `1` there. -/
theorem isCanonicalUT_cx (K : Set (ℝ × ℝ)) :
    IsCanonicalUT (cxP K) Set.univ cxU cxT cxν (fun _ => 1) := by
  intro p _
  have hmap : (cxP K p).map (fun x => (cxU x, cxT x)) = Measure.dirac ((0 : ℝ), (0 : ℝ)) := by
    simp only [cxU, cxT]
    rw [Measure.map_const, measure_univ, one_smul]
  have hae : (fun z : ℝ × ℝ => ENNReal.ofReal (1 * Real.exp (p.1 * z.1 + ⟪p.2, z.2⟫_ℝ)))
      =ᵐ[Measure.dirac ((0 : ℝ), (0 : ℝ))] 1 := by
    rw [ae_dirac_eq]
    refine Filter.eventually_pure.mpr ?_
    simp
  rw [hmap, cxν, withDensity_congr_ae hae, withDensity_one]

/-- **The conditional size of any test is its value at the single atom.** The disintegration
identity `integral_eq_integral_condDistrib` computes the conditional size without identifying
the conditional distribution: the law of `T` is a Dirac mass, so the average of the
conditional sizes *is* the conditional size, and it equals the (constant) unconditional
power. -/
theorem condSize_cx (K : Set (ℝ × ℝ)) (p : ℝ × ℝ) (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (v : ℝ) (hv : ψ (0, 0) = v) :
    ∀ᵐ t ∂((cxP K p).map cxT),
      ∫ u, ψ (u, t) ∂(condDistrib cxU cxT (cxP K p) t) = v := by
  have hcxT : cxT = fun _ : Bool => (0 : ℝ) := rfl
  have hmapT : (cxP K p).map cxT = Measure.dirac (0 : ℝ) := by
    rw [hcxT, Measure.map_const, measure_univ, one_smul]
  have hdis := integral_eq_integral_condDistrib (P := cxP K) (U := cxU) (T := cxT) (p := p)
    (φ := ψ) measurable_cxU measurable_cxT hψ
    (by simp only [cxU, cxT]; exact integrable_const _)
  have hLHS : ∫ x, ψ (cxU x, cxT x) ∂(cxP K p) = v := by
    simp only [cxU, cxT, hv]
    rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hmapT] at hdis ⊢
  rw [integral_dirac] at hdis
  rw [ae_dirac_eq]
  exact Filter.eventually_pure.mpr (hdis.symm.trans hLHS)

/-- On the alternative set the competitor has power `1`. -/
theorem power_cxψ_mem {K : Set (ℝ × ℝ)} {p : ℝ × ℝ} (h : p ∈ K) :
    power (cxP K) cxψ p = 1 := by
  have hP : cxP K p = Measure.dirac true := by simp only [cxP, if_pos h]
  rw [power, hP, integral_dirac]
  simp [cxψ]

/-- Off the alternative set the competitor has power `1/2`. -/
theorem power_cxψ_notMem {K : Set (ℝ × ℝ)} {p : ℝ × ℝ} (h : p ∉ K) :
    power (cxP K) cxψ p = 1 / 2 := by
  have hP : cxP K p = cxCoin := by simp only [cxP, if_neg h]
  have hint : Integrable cxψ cxCoin := Integrable.of_finite
  rw [power, hP, integral_fintype hint]
  simp only [Fintype.sum_bool, cxψ, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
    add_zero]
  rw [measureReal_def, cxCoin_true]
  norm_num

/-- A constant test has constant power. -/
theorem power_const_cx (K : Set (ℝ × ℝ)) (v : ℝ) (p : ℝ × ℝ) :
    power (cxP K) (fun _ => v) p = v := by
  rw [power, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

/-- **The refutation engine.** In the counterexample family, a conditional test that is
constantly equal to the level `α < 1` cannot be UMP unbiased: the auxiliary-bit test is
unbiased and has power `1` on the alternative. -/
theorem not_isUMPU_cx {K Θ₀ Θ₁ : Set (ℝ × ℝ)} {α : ℝ} {φ : Bool → ℝ}
    (hα : α = 1 / 2) (hφc : ∀ x, φ x = α)
    (hnull : ∀ q ∈ Θ₀, q ∉ K) (halt : Θ₁ ⊆ K) {q₁ : ℝ × ℝ} (hq₁ : q₁ ∈ Θ₁) :
    ¬ IsUMPU (cxP K) Θ₀ Θ₁ α φ := by
  classical
  intro h
  have hψcrit : IsCriticalFn cxψ :=
    ⟨Measurable.of_discrete, fun b => by cases b <;> norm_num [cxψ]⟩
  have hψunb : IsUnbiasedTest (cxP K) Θ₀ Θ₁ α cxψ := by
    constructor
    · intro q hq
      rw [power_cxψ_notMem (hnull q hq)]
      linarith
    · intro q hq
      rw [power_cxψ_mem (halt hq)]
      linarith
  have hcmp := h.2.2 cxψ hψcrit hψunb q₁ hq₁
  rw [power_cxψ_mem (halt hq₁)] at hcmp
  have hpow : power (cxP K) φ q₁ = α := by
    have : φ = fun _ => α := funext hφc
    rw [this, power_const_cx]
  rw [hpow] at hcmp
  linarith

/-! ### The constants of the counterexample and the four refutations -/

/-- Threshold of the counterexample's conditional test. -/
def cxC₀ : ℝ → ℝ := fun _ => 0

/-- Boundary weight of the counterexample's conditional test. -/
noncomputable def cxγ₀ : ℝ → ℝ := fun _ => 1 / 2

lemma measurable_cxC₀ : Measurable cxC₀ := measurable_const

lemma measurable_cxγ₀ : Measurable cxγ₀ := measurable_const

lemma cxγ₀_mem (t : ℝ) : cxγ₀ t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> norm_num [cxγ₀]

lemma cxC₀_le (t : ℝ) : cxC₀ t ≤ cxC₀ t := le_rfl

private lemma measurableSet_cx_pos : MeasurableSet {z : ℝ × ℝ | (0 : ℝ) < z.1} :=
  measurableSet_lt measurable_const measurable_fst

private lemma measurableSet_cx_neg : MeasurableSet {z : ℝ × ℝ | z.1 < (0 : ℝ)} :=
  measurableSet_lt measurable_fst measurable_const

private lemma measurableSet_cx_eq : MeasurableSet {z : ℝ × ℝ | z.1 = (0 : ℝ)} :=
  measurableSet_eq_fun measurable_fst measurable_const

lemma measurable_cxOneSided : Measurable (condOneSidedTest cxC₀ cxγ₀) := by
  have h : condOneSidedTest cxC₀ cxγ₀
      = fun z : ℝ × ℝ => if (0 : ℝ) < z.1 then 1 else if z.1 = 0 then 1 / 2 else 0 := rfl
  rw [h]
  exact Measurable.ite measurableSet_cx_pos measurable_const
    (Measurable.ite measurableSet_cx_eq measurable_const measurable_const)

lemma measurable_cxInside : Measurable (condInsideTest cxC₀ cxC₀ cxγ₀ cxγ₀) := by
  have h : condInsideTest cxC₀ cxC₀ cxγ₀ cxγ₀
      = fun z : ℝ × ℝ => if (0 : ℝ) < z.1 ∧ z.1 < 0 then 1
        else if z.1 = 0 then 1 / 2 else if z.1 = 0 then 1 / 2 else 0 := rfl
  rw [h]
  exact Measurable.ite (measurableSet_cx_pos.inter measurableSet_cx_neg) measurable_const
    (Measurable.ite measurableSet_cx_eq measurable_const
      (Measurable.ite measurableSet_cx_eq measurable_const measurable_const))

lemma measurable_cxOutside : Measurable (condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀) := by
  have h : condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀
      = fun z : ℝ × ℝ => if z.1 < 0 ∨ (0 : ℝ) < z.1 then 1
        else if z.1 = 0 then 1 / 2 else if z.1 = 0 then 1 / 2 else 0 := rfl
  rw [h]
  exact Measurable.ite (measurableSet_cx_neg.union measurableSet_cx_pos) measurable_const
    (Measurable.ite measurableSet_cx_eq measurable_const
      (Measurable.ite measurableSet_cx_eq measurable_const measurable_const))

lemma cxOneSided_val : condOneSidedTest cxC₀ cxγ₀ ((0 : ℝ), (0 : ℝ)) = 1 / 2 := by
  norm_num [condOneSidedTest, cxC₀, cxγ₀]

lemma cxInside_val : condInsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ ((0 : ℝ), (0 : ℝ)) = 1 / 2 := by
  norm_num [condInsideTest, cxC₀, cxγ₀]

lemma cxOutside_val : condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ ((0 : ℝ), (0 : ℝ)) = 1 / 2 := by
  norm_num [condOutsideTest, cxC₀, cxγ₀]

/-- **`isUMPU_conditional_oneSided` WITHOUT the amendment `hsuff` is false**
(`SufficiencyReducible` fails here: `(U, T)` is constant, so every critical function
of `(U, T)` has constant power, while `cxψ` does not.)

Old wording: `isUMPU_conditional_oneSided` is false as stated.** Every hypothesis of that theorem is
satisfied by the counterexample family (with `θ₀ = 0`, `α = 1/2`, `Ω = univ`), yet the
conclusion fails. -/
theorem not_isUMPU_conditional_oneSided_counterexample :
    Measurable cxU ∧ Measurable cxT ∧
      IsCanonicalUT (cxP {p : ℝ × ℝ | 0 < p.1}) Set.univ cxU cxT cxν (fun _ => 1) ∧
      Convex ℝ (Set.univ : Set (ℝ × ℝ)) ∧
      Submodule.span ℝ (Set.univ : Set (ℝ × ℝ)) = ⊤ ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 0) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (0 : ℝ) < p.1) ∧
      (0 : ℝ) < 1 / 2 ∧ (1 : ℝ) / 2 < 1 ∧
      Measurable cxC₀ ∧ Measurable cxγ₀ ∧ (∀ t, cxγ₀ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 = 0 →
        ∀ᵐ t ∂((cxP {p : ℝ × ℝ | 0 < p.1} p).map cxT),
          ∫ u, condOneSidedTest cxC₀ cxγ₀ (u, t)
            ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | 0 < p.1} p) t) = 1 / 2) ∧
      ¬ IsUMPU (cxP {p : ℝ × ℝ | 0 < p.1})
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | p.1 ≤ 0}
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | (0 : ℝ) < p.1} (1 / 2)
          (fun x => condOneSidedTest cxC₀ cxγ₀ (cxU x, cxT x)) := by
  refine ⟨measurable_cxU, measurable_cxT, isCanonicalUT_cx _, convex_univ, by simp,
    ⟨(-1, 0), Set.mem_univ _, by norm_num⟩, ⟨(1, 0), Set.mem_univ _, by norm_num⟩,
    by norm_num, by norm_num,
    measurable_cxC₀, measurable_cxγ₀, cxγ₀_mem, fun p _ _ =>
      condSize_cx _ p _ measurable_cxOneSided _ cxOneSided_val, ?_⟩
  refine not_isUMPU_cx rfl (fun x => ?_) (fun q hq => ?_) (fun q hq => hq.2)
    (q₁ := (1, 0)) ⟨Set.mem_univ _, by norm_num⟩
  · simpa [cxU, cxT] using cxOneSided_val
  · simpa using not_lt.mpr hq.2

/-- **`isUMPU_conditional_inside` WITHOUT the amendment `hsuff` is false**
(`SufficiencyReducible` fails here: `(U, T)` is constant, so every critical function
of `(U, T)` has constant power, while `cxψ` does not.)

Old wording: `isUMPU_conditional_inside` is false as stated**, by the same counterexample family
(here with `θ₁ = 0 < θ₂ = 1`, `α = 1/2`; the alternative set is `{0 < θ < 1}`). -/
theorem not_isUMPU_conditional_inside_counterexample :
    Measurable cxU ∧ Measurable cxT ∧
      IsCanonicalUT (cxP {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1}) Set.univ cxU cxT cxν (fun _ => 1) ∧
      Convex ℝ (Set.univ : Set (ℝ × ℝ)) ∧
      Submodule.span ℝ (Set.univ : Set (ℝ × ℝ)) = ⊤ ∧
      (0 : ℝ) < 1 ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 0) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (0 : ℝ) < p.1) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 1) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (1 : ℝ) < p.1) ∧
      (0 : ℝ) < 1 / 2 ∧ (1 : ℝ) / 2 < 1 ∧
      Measurable cxC₀ ∧ Measurable cxγ₀ ∧ (∀ t, cxγ₀ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, cxC₀ t ≤ cxC₀ t) ∧
      (∀ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 = 0 ∨ p.1 = 1 →
        ∀ᵐ t ∂((cxP {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1} p).map cxT),
          ∫ u, condInsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (u, t)
            ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1} p) t) = 1 / 2) ∧
      ¬ IsUMPU (cxP {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1})
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | p.1 ≤ 0 ∨ 1 ≤ p.1}
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | (0 : ℝ) < p.1 ∧ p.1 < 1} (1 / 2)
          (fun x => condInsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (cxU x, cxT x)) := by
  refine ⟨measurable_cxU, measurable_cxT, isCanonicalUT_cx _, convex_univ, by simp,
    by norm_num, ⟨(-1, 0), Set.mem_univ _, by norm_num⟩,
    ⟨(1, 0), Set.mem_univ _, by norm_num⟩, ⟨(0, 0), Set.mem_univ _, by norm_num⟩,
    ⟨(2, 0), Set.mem_univ _, by norm_num⟩, by norm_num, by norm_num,
    measurable_cxC₀, measurable_cxγ₀, cxγ₀_mem, cxC₀_le, fun p _ _ =>
      condSize_cx _ p _ measurable_cxInside _ cxInside_val, ?_⟩
  refine not_isUMPU_cx rfl (fun x => ?_) (fun q hq => ?_) (fun q hq => hq.2)
    (q₁ := (1 / 2, 0)) ⟨Set.mem_univ _, by norm_num⟩
  · simpa [cxU, cxT] using cxInside_val
  · rcases hq.2 with h | h
    · exact fun hmem => absurd hmem.1 (not_lt.mpr h)
    · exact fun hmem => absurd hmem.2 (not_lt.mpr h)

/-- **`isUMPU_conditional_outside` WITHOUT the amendment `hsuff` is false**
(`SufficiencyReducible` fails here: `(U, T)` is constant, so every critical function
of `(U, T)` has constant power, while `cxψ` does not.)

Old wording: `isUMPU_conditional_outside` is false as stated**, by the same counterexample family
(here with `θ₁ = 0 < θ₂ = 1`, `α = 1/2`; the alternative set is `{θ < 0 ∨ 1 < θ}`). -/
theorem not_isUMPU_conditional_outside_counterexample :
    Measurable cxU ∧ Measurable cxT ∧
      IsCanonicalUT (cxP {p : ℝ × ℝ | p.1 < 0 ∨ 1 < p.1}) Set.univ cxU cxT cxν (fun _ => 1) ∧
      Convex ℝ (Set.univ : Set (ℝ × ℝ)) ∧
      Submodule.span ℝ (Set.univ : Set (ℝ × ℝ)) = ⊤ ∧
      (0 : ℝ) < 1 ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 0) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (0 : ℝ) < p.1) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 1) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (1 : ℝ) < p.1) ∧
      (0 : ℝ) < 1 / 2 ∧ (1 : ℝ) / 2 < 1 ∧
      Measurable cxC₀ ∧ Measurable cxγ₀ ∧ (∀ t, cxγ₀ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, cxC₀ t ≤ cxC₀ t) ∧
      (∀ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 = 0 ∨ p.1 = 1 →
        ∀ᵐ t ∂((cxP {p : ℝ × ℝ | p.1 < 0 ∨ 1 < p.1} p).map cxT),
          ∫ u, condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (u, t)
            ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 < 0 ∨ 1 < p.1} p) t) = 1 / 2) ∧
      ¬ IsUMPU (cxP {p : ℝ × ℝ | p.1 < 0 ∨ 1 < p.1})
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | (0 : ℝ) ≤ p.1 ∧ p.1 ≤ 1}
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | p.1 < 0 ∨ 1 < p.1} (1 / 2)
          (fun x => condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (cxU x, cxT x)) := by
  refine ⟨measurable_cxU, measurable_cxT, isCanonicalUT_cx _, convex_univ, by simp,
    by norm_num, ⟨(-1, 0), Set.mem_univ _, by norm_num⟩,
    ⟨(1, 0), Set.mem_univ _, by norm_num⟩, ⟨(0, 0), Set.mem_univ _, by norm_num⟩,
    ⟨(2, 0), Set.mem_univ _, by norm_num⟩, by norm_num, by norm_num,
    measurable_cxC₀, measurable_cxγ₀, cxγ₀_mem, cxC₀_le, fun p _ _ =>
      condSize_cx _ p _ measurable_cxOutside _ cxOutside_val, ?_⟩
  refine not_isUMPU_cx rfl (fun x => ?_) (fun q hq => ?_) (fun q hq => hq.2)
    (q₁ := (2, 0)) ⟨Set.mem_univ _, by norm_num⟩
  · simpa [cxU, cxT] using cxOutside_val
  · rintro (h | h)
    · exact absurd hq.2.1 (not_le.mpr h)
    · exact absurd hq.2.2 (not_le.mpr h)

/-- **`isUMPU_conditional_point` WITHOUT the amendment `hsuff` is false**
(`SufficiencyReducible` fails here: `(U, T)` is constant, so every critical function
of `(U, T)` has constant power, while `cxψ` does not.)

Old wording: `isUMPU_conditional_point` is false as stated**, by the same counterexample family
(here `θ₀ = 0`, `α = 1/2`); note that the conditional derivative condition `hderiv` also
holds, both sides being `0` because the interest statistic is constant `0`. -/
theorem not_isUMPU_conditional_point_counterexample :
    Measurable cxU ∧ Measurable cxT ∧
      IsCanonicalUT (cxP {p : ℝ × ℝ | p.1 ≠ 0}) Set.univ cxU cxT cxν (fun _ => 1) ∧
      Convex ℝ (Set.univ : Set (ℝ × ℝ)) ∧
      Submodule.span ℝ (Set.univ : Set (ℝ × ℝ)) = ⊤ ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 0) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (0 : ℝ) < p.1) ∧
      (0 : ℝ) < 1 / 2 ∧ (1 : ℝ) / 2 < 1 ∧
      Measurable cxC₀ ∧ Measurable cxγ₀ ∧ (∀ t, cxγ₀ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, cxC₀ t ≤ cxC₀ t) ∧
      (∀ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 = 0 →
        ∀ᵐ t ∂((cxP {p : ℝ × ℝ | p.1 ≠ 0} p).map cxT),
          ∫ u, condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (u, t)
            ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 ≠ 0} p) t) = 1 / 2) ∧
      (∀ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 = 0 →
        ∀ᵐ t ∂((cxP {p : ℝ × ℝ | p.1 ≠ 0} p).map cxT),
          ∫ u, u * condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (u, t)
              ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 ≠ 0} p) t)
            = 1 / 2 * ∫ u, u ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 ≠ 0} p) t)) ∧
      ¬ IsUMPU (cxP {p : ℝ × ℝ | p.1 ≠ 0})
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | p.1 = 0}
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | p.1 ≠ 0} (1 / 2)
          (fun x => condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (cxU x, cxT x)) := by
  have hderiv : ∀ p : ℝ × ℝ, ∀ᵐ t ∂((cxP {p : ℝ × ℝ | p.1 ≠ 0} p).map cxT),
      ∫ u, u * condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (u, t)
          ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 ≠ 0} p) t)
        = 1 / 2 * ∫ u, u ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 ≠ 0} p) t) := by
    intro p
    have h₁ := condSize_cx {p : ℝ × ℝ | p.1 ≠ 0} p
      (fun z => z.1 * condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ z)
      (measurable_fst.mul measurable_cxOutside) 0 (by simp)
    have h₂ := condSize_cx {p : ℝ × ℝ | p.1 ≠ 0} p (fun z => z.1) measurable_fst 0 rfl
    filter_upwards [h₁, h₂] with t ht₁ ht₂
    rw [ht₁, ht₂, mul_zero]
  refine ⟨measurable_cxU, measurable_cxT, isCanonicalUT_cx _, convex_univ, by simp,
    ⟨(-1, 0), Set.mem_univ _, by norm_num⟩, ⟨(1, 0), Set.mem_univ _, by norm_num⟩,
    by norm_num, by norm_num,
    measurable_cxC₀, measurable_cxγ₀, cxγ₀_mem, cxC₀_le, fun p _ _ =>
      condSize_cx _ p _ measurable_cxOutside _ cxOutside_val, fun p _ _ => hderiv p, ?_⟩
  refine not_isUMPU_cx rfl (fun x => ?_) (fun q hq => ?_) (fun q hq => hq.2)
    (q₁ := (1, 0)) ⟨Set.mem_univ _, by norm_num⟩
  · simpa [cxU, cxT] using cxOutside_val
  · simpa using hq.2

end ConditionalUMPUCounterexample

/-! ## Fibrewise toolkit: exponential tilts on the conditional line

Conditionally on `T = t` all members of a canonical `(U, T)` family are exponential tilts of
one another: by `ConditionalExpFamily.condDistrib_expFamily_of_isCanonicalUT` the conditional
law at `(θ, ϑ)` is `(νt t).withDensity (u ↦ Ct t θ · e^{θu})`, so the law at `θ` is the law at
`θ₀` tilted by `k·e^{(θ−θ₀)u}` with `k = Ct t θ / Ct t θ₀`. Everything the four theorems need
about the fibres is the elementary "variation-diminishing" inequality below, applied to
`g = φ − ψ` (optimality) or to `g = φ − α` (level and unbiasedness). -/

section FibreTilt

/-- Integration against a `withDensity` whose density is the `ENNReal.ofReal` of a
nonnegative real function. No hypothesis on `g`: both sides are junk-compatible. -/
private lemma integral_withDensity_ofReal_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ} (hf : Measurable f) (hfnn : ∀ a, 0 ≤ f a) (g : α → ℝ) :
    ∫ a, g a ∂(μ.withDensity fun a => ENNReal.ofReal (f a)) = ∫ a, g a * f a ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (hfnn a), mul_comm]

/-- The exponential tilt of a measure on the line by the density `k·e^{cu}`. -/
private noncomputable def expTilt (Q : Measure ℝ) (k c : ℝ) : Measure ℝ :=
  Q.withDensity fun u => ENNReal.ofReal (k * Real.exp (c * u))

private lemma measurable_expTiltDensity (k c : ℝ) :
    Measurable fun u : ℝ => ENNReal.ofReal (k * Real.exp (c * u)) :=
  (((measurable_const.mul measurable_id).exp).const_mul k).ennreal_ofReal

/-- Integrals against a tilt are integrals of the tilted integrand. No hypothesis on `g`:
both sides are junk-compatible. -/
private lemma integral_expTilt (Q : Measure ℝ) {k : ℝ} (hk : 0 ≤ k) (c : ℝ) (g : ℝ → ℝ) :
    ∫ u, g u ∂(expTilt Q k c) = ∫ u, g u * (k * Real.exp (c * u)) ∂Q :=
  integral_withDensity_ofReal_mul Q ((measurable_const.mul measurable_id).exp.const_mul k)
    (fun _ => by positivity) g

/-- A tilt with a nonpositive factor is the zero measure, hence never a probability
measure. -/
private lemma expTilt_factor_pos {Q : Measure ℝ} {k c : ℝ}
    (hprob : IsProbabilityMeasure (expTilt Q k c)) : 0 < k := by
  by_contra hcon
  push Not at hcon
  have hdens : (fun u : ℝ => ENNReal.ofReal (k * Real.exp (c * u))) = 0 := by
    funext u
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero]
    have h := mul_nonneg (neg_nonneg.mpr hcon) (Real.exp_pos (c * u)).le
    rw [neg_mul] at h
    linarith
  have h1 : (expTilt Q k c) Set.univ = 1 := hprob.measure_univ
  rw [expTilt, hdens, withDensity_zero] at h1
  simp at h1

/-- **Two members of a canonical one-parameter family on the line are exponential tilts of
one another.** This is the fibrewise content of `IsCanonicalUT`. -/
private lemma withDensity_line_tilt (μ : Measure ℝ) {a b θ θ₀ : ℝ} (ha : 0 < a) :
    (μ.withDensity fun u => ENNReal.ofReal (b * Real.exp (θ * u)))
      = expTilt (μ.withDensity fun u => ENNReal.ofReal (a * Real.exp (θ₀ * u)))
        (b / a) (θ - θ₀) := by
  rw [expTilt, ← withDensity_mul _ (measurable_expTiltDensity a θ₀)
    (measurable_expTiltDensity (b / a) (θ - θ₀))]
  congr 1
  funext u
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hexp : Real.exp (θ * u) = Real.exp ((θ - θ₀) * u) * Real.exp (θ₀ * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  field_simp

/-- **A tilt which is again a probability measure has an integrable density of total mass
one.** This is the only place the normalization of the conditional families is used. -/
private lemma integrable_expTiltDensity {Q : Measure ℝ} {k c : ℝ} (hk : 0 ≤ k)
    (hprob : IsProbabilityMeasure (expTilt Q k c)) :
    Integrable (fun u => k * Real.exp (c * u)) Q ∧
      ∫ u, k * Real.exp (c * u) ∂Q = 1 := by
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[Q] fun u => k * Real.exp (c * u) :=
    Filter.Eventually.of_forall fun u => by
      have h : (0 : ℝ) ≤ k * Real.exp (c * u) := by positivity
      simpa using h
  have hm : Measurable fun u : ℝ => k * Real.exp (c * u) :=
    (measurable_const.mul measurable_id).exp.const_mul k
  have hlin : ∫⁻ u, ENNReal.ofReal (k * Real.exp (c * u)) ∂Q = 1 := by
    have := hprob.measure_univ
    rwa [expTilt, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at this
  have hint : Integrable (fun u => k * Real.exp (c * u)) Q :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hnn).mp
      (by rw [hlin]; exact ENNReal.one_ne_top)
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable, hlin,
    ENNReal.toReal_one]

/-- **The fibrewise variation-diminishing inequality.** Let `g` be bounded by `1`, nonnegative
strictly above the threshold `C` and nonpositive strictly below it. Tilting by `k·e^{cu}` then
moves `∫g` in the direction of the sign of `c`, relative to the reference value
`k·e^{cC}·∫g`; the proof is the pointwise inequality
`g(u)·(k e^{cu} − k e^{cC}) ≥ 0`, whose two factors change sign at the same point `C`. -/
private lemma integral_expTilt_signed {Q : Measure ℝ} [IsProbabilityMeasure Q] {k c C : ℝ}
    (hk : 0 ≤ k) (hprob : IsProbabilityMeasure (expTilt Q k c))
    {g : ℝ → ℝ} (hgm : Measurable g) (hgb : ∀ u, |g u| ≤ 1)
    (hgpos : ∀ u, C < u → 0 ≤ g u) (hgneg : ∀ u, u < C → g u ≤ 0) :
    (0 ≤ c → k * Real.exp (c * C) * (∫ u, g u ∂Q) ≤ ∫ u, g u ∂(expTilt Q k c)) ∧
      (c ≤ 0 → ∫ u, g u ∂(expTilt Q k c) ≤ k * Real.exp (c * C) * (∫ u, g u ∂Q)) := by
  obtain ⟨hdint, -⟩ := integrable_expTiltDensity hk hprob
  have hgint : Integrable g Q :=
    Integrable.mono' (integrable_const (1 : ℝ)) hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hgb u)
  have hprod : Integrable (fun u => g u * (k * Real.exp (c * u))) Q :=
    hdint.bdd_mul (c := 1) hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hgb u)
  have hsplit : ∫ u, g u * (k * Real.exp (c * u) - k * Real.exp (c * C)) ∂Q
      = (∫ u, g u ∂(expTilt Q k c)) - k * Real.exp (c * C) * ∫ u, g u ∂Q := by
    have h1 : (fun u => g u * (k * Real.exp (c * u) - k * Real.exp (c * C)))
        = fun u => g u * (k * Real.exp (c * u)) - k * Real.exp (c * C) * g u := by
      funext u; ring
    rw [h1, integral_sub hprod (hgint.const_mul _), integral_const_mul,
      integral_expTilt Q hk c g]
  constructor
  · intro hc
    have hpt : ∀ u, 0 ≤ g u * (k * Real.exp (c * u) - k * Real.exp (c * C)) := by
      intro u
      rcases lt_trichotomy u C with h | h | h
      · have hle : k * Real.exp (c * u) ≤ k * Real.exp (c * C) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h.le hc)) hk
        have hprodnn := mul_nonneg (neg_nonneg.mpr (hgneg u h))
          (neg_nonneg.mpr (by linarith :
            k * Real.exp (c * u) - k * Real.exp (c * C) ≤ 0))
        rwa [neg_mul_neg] at hprodnn
      · rw [h]; ring_nf; exact le_rfl
      · have hle : k * Real.exp (c * C) ≤ k * Real.exp (c * u) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h.le hc)) hk
        exact mul_nonneg (hgpos u h) (by linarith)
    have hI : (0 : ℝ) ≤ ∫ u, g u * (k * Real.exp (c * u) - k * Real.exp (c * C)) ∂Q :=
      integral_nonneg hpt
    rw [hsplit] at hI
    linarith
  · intro hc
    have hpt : ∀ u, g u * (k * Real.exp (c * u) - k * Real.exp (c * C)) ≤ 0 := by
      intro u
      rcases lt_trichotomy u C with h | h | h
      · have hle : k * Real.exp (c * C) ≤ k * Real.exp (c * u) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left h.le hc)) hk
        have hprodnn := mul_nonneg (neg_nonneg.mpr (hgneg u h))
          (by linarith : (0 : ℝ) ≤ k * Real.exp (c * u) - k * Real.exp (c * C))
        rw [neg_mul] at hprodnn
        linarith
      · rw [h]; ring_nf; exact le_rfl
      · have hle : k * Real.exp (c * u) ≤ k * Real.exp (c * C) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left h.le hc)) hk
        have hprodnn := mul_nonneg (hgpos u h)
          (neg_nonneg.mpr (by linarith :
            k * Real.exp (c * u) - k * Real.exp (c * C) ≤ 0))
        rw [mul_neg] at hprodnn
        linarith
    have hI : ∫ u, g u * (k * Real.exp (c * u) - k * Real.exp (c * C)) ∂Q ≤ 0 :=
      integral_nonpos hpt
    rw [hsplit] at hI
    linarith

/-! ### Three-exponential separation (ported from `Unbiased/OneParamTwoSided.lean`,
where these are `private`; they are the convex-geometry core of the two-constraint
Neyman–Pearson step and are reused here fibrewise) -/

/-- **Chord separation for a convex function on `[0,∞)`.** Given `0 < w₁ ≤ w₂` and a
supporting line at `w₁` (used only in the degenerate case `w₁ = w₂`), the secant through
`(w₁, G w₁)` and `(w₂, G w₂)` dominates `G` on `[w₁, w₂]` and is dominated by `G` outside. -/
private lemma exists_chord_of_convexOn {G : ℝ → ℝ} (hG : ConvexOn ℝ (Set.Ici (0 : ℝ)) G)
    {w₁ w₂ : ℝ} (h1 : 0 < w₁) (h12 : w₁ ≤ w₂)
    (hsupp : ∃ b : ℝ, ∀ w, 0 ≤ w → G w₁ + b * (w - w₁) ≤ G w) :
    ∃ a b : ℝ, (∀ w, w₁ ≤ w → w ≤ w₂ → G w ≤ a + b * w) ∧
      (∀ w, 0 ≤ w → (w ≤ w₁ ∨ w₂ ≤ w) → a + b * w ≤ G w) := by
  rcases eq_or_lt_of_le h12 with rfl | hlt
  · obtain ⟨b, hb⟩ := hsupp
    refine ⟨G w₁ - b * w₁, b, ?_, ?_⟩
    · intro w hw1 hw2
      have hww : w = w₁ := le_antisymm hw2 hw1
      subst hww
      linarith
    · intro w hw _
      have := hb w hw
      linarith
  · have hne : w₂ - w₁ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
    obtain ⟨a, b, hA1, hA2⟩ : ∃ a b : ℝ, a + b * w₁ = G w₁ ∧ a + b * w₂ = G w₂ := by
      refine ⟨G w₁ - ((G w₂ - G w₁) / (w₂ - w₁)) * w₁, (G w₂ - G w₁) / (w₂ - w₁), by ring, ?_⟩
      field_simp
      ring
    have hcvx : ∀ x y u v : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ u → 0 ≤ v → u + v = 1 →
        G (u * x + v * y) ≤ u * G x + v * G y := by
      intro x y u v hx hy hu hv huv
      simpa using hG.2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hu hv huv
    refine ⟨a, b, ?_, ?_⟩
    · intro w hw1 hw2
      have hu : 0 ≤ (w₂ - w) / (w₂ - w₁) := div_nonneg (by linarith) (by linarith)
      have hv : 0 ≤ (w - w₁) / (w₂ - w₁) := div_nonneg (by linarith) (by linarith)
      have huv : (w₂ - w) / (w₂ - w₁) + (w - w₁) / (w₂ - w₁) = 1 := by field_simp; ring
      have hcomb : (w₂ - w) / (w₂ - w₁) * w₁ + (w - w₁) / (w₂ - w₁) * w₂ = w := by
        field_simp; ring
      have h := hcvx w₁ w₂ _ _ h1.le (by linarith) hu hv huv
      rw [hcomb] at h
      have haff : (w₂ - w) / (w₂ - w₁) * (a + b * w₁) + (w - w₁) / (w₂ - w₁) * (a + b * w₂)
          = a + b * w := by field_simp; ring
      rw [hA1, hA2] at haff
      linarith
    · rintro w hw (hc | hc)
      · -- `w ≤ w₁`: write `w₁` as a convex combination of `w₂` and `w`
        have hden : (0 : ℝ) < w₂ - w := by linarith
        have hu : 0 ≤ (w₁ - w) / (w₂ - w) := div_nonneg (by linarith) (by linarith)
        have hv : 0 < (w₂ - w₁) / (w₂ - w) := div_pos (by linarith) hden
        have huv : (w₁ - w) / (w₂ - w) + (w₂ - w₁) / (w₂ - w) = 1 := by field_simp; ring
        have hcomb : (w₁ - w) / (w₂ - w) * w₂ + (w₂ - w₁) / (w₂ - w) * w = w₁ := by
          field_simp; ring
        have h := hcvx w₂ w ((w₁ - w) / (w₂ - w)) ((w₂ - w₁) / (w₂ - w)) (by linarith) hw hu
          hv.le huv
        rw [hcomb] at h
        have haff : (w₁ - w) / (w₂ - w) * (a + b * w₂) + (w₂ - w₁) / (w₂ - w) * (a + b * w)
            = a + b * w₁ := by field_simp; ring
        rw [hA1, hA2] at haff
        have hstep : (w₂ - w₁) / (w₂ - w) * (a + b * w) ≤ (w₂ - w₁) / (w₂ - w) * G w := by
          linarith
        exact le_of_mul_le_mul_left hstep hv
      · -- `w₂ ≤ w`: write `w₂` as a convex combination of `w` and `w₁`
        have hden : (0 : ℝ) < w - w₁ := by linarith
        have hu : 0 < (w₂ - w₁) / (w - w₁) := div_pos (by linarith) hden
        have hv : 0 ≤ (w - w₂) / (w - w₁) := div_nonneg (by linarith) (by linarith)
        have huv : (w₂ - w₁) / (w - w₁) + (w - w₂) / (w - w₁) = 1 := by field_simp; ring
        have hcomb : (w₂ - w₁) / (w - w₁) * w + (w - w₂) / (w - w₁) * w₁ = w₂ := by
          field_simp; ring
        have h := hcvx w w₁ ((w₂ - w₁) / (w - w₁)) ((w - w₂) / (w - w₁)) hw h1.le hu.le hv huv
        rw [hcomb] at h
        have haff : (w₂ - w₁) / (w - w₁) * (a + b * w) + (w - w₂) / (w - w₁) * (a + b * w₁)
            = a + b * w₂ := by field_simp; ring
        rw [hA1, hA2] at haff
        have hstep : (w₂ - w₁) / (w - w₁) * (a + b * w) ≤ (w₂ - w₁) / (w - w₁) * G w := by
          linarith
        exact le_of_mul_le_mul_left hstep hu

/-- The concave companion of `exists_chord_of_convexOn`, by negation. -/
private lemma exists_chord_of_concaveOn {G : ℝ → ℝ} (hG : ConcaveOn ℝ (Set.Ici (0 : ℝ)) G)
    {w₁ w₂ : ℝ} (h1 : 0 < w₁) (h12 : w₁ ≤ w₂)
    (hsupp : ∃ b : ℝ, ∀ w, 0 ≤ w → G w ≤ G w₁ + b * (w - w₁)) :
    ∃ a b : ℝ, (∀ w, w₁ ≤ w → w ≤ w₂ → a + b * w ≤ G w) ∧
      (∀ w, 0 ≤ w → (w ≤ w₁ ∨ w₂ ≤ w) → G w ≤ a + b * w) := by
  have hsupp' : ∃ b : ℝ, ∀ w, 0 ≤ w → (-G) w₁ + b * (w - w₁) ≤ (-G) w := by
    obtain ⟨b, hb⟩ := hsupp
    refine ⟨-b, fun w hw => ?_⟩
    have := hb w hw
    simp only [Pi.neg_apply]
    linarith
  obtain ⟨a, b, hin, hout⟩ := exists_chord_of_convexOn hG.neg h1 h12 hsupp'
  refine ⟨-a, -b, fun w hw1 hw2 => ?_, fun w hw hc => ?_⟩
  · have := hin w hw1 hw2
    simp only [Pi.neg_apply] at this
    linarith
  · have := hout w hw hc
    simp only [Pi.neg_apply] at this
    linarith

/-- Supporting line from below for `w ↦ w^λ` at `w₁ > 0`, for `λ ≥ 1` (Bernoulli). -/
private lemma rpow_supporting_ge {lam w₁ : ℝ} (hlam : 1 ≤ lam) (h1 : 0 < w₁) :
    ∀ w, 0 ≤ w → w₁ ^ lam + (lam * w₁ ^ lam / w₁) * (w - w₁) ≤ w ^ lam := by
  intro w hw
  have hdn : 0 ≤ w / w₁ := div_nonneg hw h1.le
  have hs : (-1 : ℝ) ≤ w / w₁ - 1 := by linarith
  have hB := one_add_mul_self_le_rpow_one_add hs hlam
  rw [show (1 : ℝ) + (w / w₁ - 1) = w / w₁ by ring] at hB
  have hsplit : w ^ lam = w₁ ^ lam * (w / w₁) ^ lam := by
    rw [← Real.mul_rpow h1.le hdn]
    congr 1
    field_simp
  have hp : (0 : ℝ) < w₁ ^ lam := Real.rpow_pos_of_pos h1 lam
  have hmul := mul_le_mul_of_nonneg_left hB hp.le
  have heq : w₁ ^ lam * (1 + lam * (w / w₁ - 1))
      = w₁ ^ lam + (lam * w₁ ^ lam / w₁) * (w - w₁) := by
    field_simp
  rw [heq] at hmul
  rw [hsplit]
  exact hmul

/-- Supporting line from above for `w ↦ w^λ` at `w₁ > 0`, for `0 ≤ λ ≤ 1` (Bernoulli). -/
private lemma rpow_supporting_le {lam w₁ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (h1 : 0 < w₁) :
    ∀ w, 0 ≤ w → w ^ lam ≤ w₁ ^ lam + (lam * w₁ ^ lam / w₁) * (w - w₁) := by
  intro w hw
  have hdn : 0 ≤ w / w₁ := div_nonneg hw h1.le
  have hs : (-1 : ℝ) ≤ w / w₁ - 1 := by linarith
  have hB := rpow_one_add_le_one_add_mul_self hs hlam0 hlam1
  rw [show (1 : ℝ) + (w / w₁ - 1) = w / w₁ by ring] at hB
  have hsplit : w ^ lam = w₁ ^ lam * (w / w₁) ^ lam := by
    rw [← Real.mul_rpow h1.le hdn]
    congr 1
    field_simp
  have hp : (0 : ℝ) < w₁ ^ lam := Real.rpow_pos_of_pos h1 lam
  have hmul := mul_le_mul_of_nonneg_left hB hp.le
  have heq : w₁ ^ lam * (1 + lam * (w / w₁ - 1))
      = w₁ ^ lam + (lam * w₁ ^ lam / w₁) * (w - w₁) := by
    field_simp
  rw [heq] at hmul
  rw [hsplit]
  exact hmul

/-- The substitution `w = e^{(θ₂−θ₁)t}` turns a three-exponential combination into an affine
function of `w` compared against `w^λ`, `λ = (ϑ−θ₁)/(θ₂−θ₁)`, all scaled by `e^{θ₁t} > 0`. -/
private lemma exp3_factor (θ₁ θ₂ ϑ a b t : ℝ) (h12 : θ₁ < θ₂) :
    a * Real.exp (θ₁ * t) + b * Real.exp (θ₂ * t)
        = Real.exp (θ₁ * t) * (a + b * Real.exp ((θ₂ - θ₁) * t)) ∧
      Real.exp (ϑ * t)
        = Real.exp (θ₁ * t) * Real.exp ((θ₂ - θ₁) * t) ^ ((ϑ - θ₁) / (θ₂ - θ₁)) := by
  have hβ : θ₂ - θ₁ ≠ 0 := sub_ne_zero.mpr (ne_of_gt h12)
  have hW : Real.exp (θ₁ * t) * Real.exp ((θ₂ - θ₁) * t) = Real.exp (θ₂ * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have hrp : Real.exp ((θ₂ - θ₁) * t) ^ ((ϑ - θ₁) / (θ₂ - θ₁))
      = Real.exp ((ϑ - θ₁) * t) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    field_simp
  refine ⟨by rw [← hW]; ring, ?_⟩
  rw [hrp, ← Real.exp_add]
  congr 1
  ring

/-- **Three-exponential separation, alternative above the interval.** For `θ₁ < θ₂ < ϑ` there
is a combination `a e^{θ₁t} + b e^{θ₂t}` dominating `e^{ϑt}` on `[C₁, C₂]` and dominated by it
outside. (Strict convexity of `w ↦ w^λ`, `λ > 1`, in the variable `w = e^{(θ₂−θ₁)t}`.) -/
private lemma exists_sep_exp3_gt {θ₁ θ₂ ϑ : ℝ} (h12 : θ₁ < θ₂) (hϑ : θ₂ < ϑ)
    {C₁ C₂ : ℝ} (hC : C₁ ≤ C₂) :
    ∃ a b : ℝ,
      (∀ t, C₁ ≤ t → t ≤ C₂ →
        Real.exp (ϑ * t) ≤ a * Real.exp (θ₁ * t) + b * Real.exp (θ₂ * t)) ∧
      (∀ t, t ≤ C₁ ∨ C₂ ≤ t →
        a * Real.exp (θ₁ * t) + b * Real.exp (θ₂ * t) ≤ Real.exp (ϑ * t)) := by
  have hβ : (0 : ℝ) < θ₂ - θ₁ := by linarith
  have hlam : 1 ≤ (ϑ - θ₁) / (θ₂ - θ₁) := by
    rw [le_div_iff₀ hβ]; linarith
  have hw₁pos : (0 : ℝ) < Real.exp ((θ₂ - θ₁) * C₁) := Real.exp_pos _
  have hww : Real.exp ((θ₂ - θ₁) * C₁) ≤ Real.exp ((θ₂ - θ₁) * C₂) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hC hβ.le)
  obtain ⟨a, b, hin, hout⟩ := exists_chord_of_convexOn (convexOn_rpow hlam) hw₁pos hww
    ⟨_, rpow_supporting_ge hlam hw₁pos⟩
  refine ⟨a, b, fun t ht1 ht2 => ?_, fun t ht => ?_⟩
  · obtain ⟨hf1, hf2⟩ := exp3_factor θ₁ θ₂ ϑ a b t h12
    rw [hf1, hf2]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    exact hin _ (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht1 hβ.le))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht2 hβ.le))
  · obtain ⟨hf1, hf2⟩ := exp3_factor θ₁ θ₂ ϑ a b t h12
    rw [hf1, hf2]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine hout _ (Real.exp_pos _).le ?_
    rcases ht with h | h
    · exact Or.inl (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hβ.le))
    · exact Or.inr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hβ.le))

/-- **Three-exponential separation, parameter inside the interval.** For `θ₁ < ϑ < θ₂` the
signs are reversed: the combination is dominated by `e^{ϑt}` on `[C₁, C₂]` and dominates it
outside. (Strict concavity of `w ↦ w^λ`, `0 < λ < 1`.) -/
private lemma exists_sep_exp3_mid {θ₁ θ₂ ϑ : ℝ} (h1 : θ₁ < ϑ) (h2 : ϑ < θ₂)
    {C₁ C₂ : ℝ} (hC : C₁ ≤ C₂) :
    ∃ a b : ℝ,
      (∀ t, C₁ ≤ t → t ≤ C₂ →
        a * Real.exp (θ₁ * t) + b * Real.exp (θ₂ * t) ≤ Real.exp (ϑ * t)) ∧
      (∀ t, t ≤ C₁ ∨ C₂ ≤ t →
        Real.exp (ϑ * t) ≤ a * Real.exp (θ₁ * t) + b * Real.exp (θ₂ * t)) := by
  have h12 : θ₁ < θ₂ := lt_trans h1 h2
  have hβ : (0 : ℝ) < θ₂ - θ₁ := by linarith
  have hlam0 : (0 : ℝ) ≤ (ϑ - θ₁) / (θ₂ - θ₁) := div_nonneg (by linarith) hβ.le
  have hlam1 : (ϑ - θ₁) / (θ₂ - θ₁) ≤ 1 := by
    rw [div_le_one hβ]; linarith
  have hw₁pos : (0 : ℝ) < Real.exp ((θ₂ - θ₁) * C₁) := Real.exp_pos _
  have hww : Real.exp ((θ₂ - θ₁) * C₁) ≤ Real.exp ((θ₂ - θ₁) * C₂) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hC hβ.le)
  obtain ⟨a, b, hin, hout⟩ :=
    exists_chord_of_concaveOn (Real.concaveOn_rpow hlam0 hlam1) hw₁pos hww
      ⟨_, rpow_supporting_le hlam0 hlam1 hw₁pos⟩
  refine ⟨a, b, fun t ht1 ht2 => ?_, fun t ht => ?_⟩
  · obtain ⟨hf1, hf2⟩ := exp3_factor θ₁ θ₂ ϑ a b t h12
    rw [hf1, hf2]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    exact hin _ (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht1 hβ.le))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht2 hβ.le))
  · obtain ⟨hf1, hf2⟩ := exp3_factor θ₁ θ₂ ϑ a b t h12
    rw [hf1, hf2]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine hout _ (Real.exp_pos _).le ?_
    rcases ht with h | h
    · exact Or.inl (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hβ.le))
    · exact Or.inr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hβ.le))

/-- **Three-exponential separation, alternative outside the interval** (either side). The
left-hand case is the right-hand one read through `t ↦ −t`. -/
private lemma exists_sep_exp3_out {θ₁ θ₂ ϑ : ℝ} (h12 : θ₁ < θ₂) (hϑ : ϑ < θ₁ ∨ θ₂ < ϑ)
    {C₁ C₂ : ℝ} (hC : C₁ ≤ C₂) :
    ∃ a b : ℝ,
      (∀ t, C₁ ≤ t → t ≤ C₂ →
        Real.exp (ϑ * t) ≤ a * Real.exp (θ₁ * t) + b * Real.exp (θ₂ * t)) ∧
      (∀ t, t ≤ C₁ ∨ C₂ ≤ t →
        a * Real.exp (θ₁ * t) + b * Real.exp (θ₂ * t) ≤ Real.exp (ϑ * t)) := by
  rcases hϑ with h | h
  · obtain ⟨a, b, hin, hout⟩ := exists_sep_exp3_gt (θ₁ := -θ₂) (θ₂ := -θ₁) (ϑ := -ϑ)
      (by linarith) (by linarith) (C₁ := -C₂) (C₂ := -C₁) (by linarith)
    refine ⟨b, a, fun t ht1 ht2 => ?_, fun t ht => ?_⟩
    · have h' := hin (-t) (by linarith) (by linarith)
      simp only [neg_mul_neg] at h'
      linarith
    · have h' : (-θ₂) * (-t) ≤ (-θ₂) * (-t) := le_rfl
      rcases ht with hc | hc
      · have h'' := hout (-t) (Or.inr (by linarith))
        simp only [neg_mul_neg] at h''
        linarith
      · have h'' := hout (-t) (Or.inl (by linarith))
        simp only [neg_mul_neg] at h''
        linarith
  · exact exists_sep_exp3_gt h12 h hC


/-- **The two-threshold fibrewise inequality.** `Q` is the conditional law at the lower
endpoint `θ₁`, `expTilt Q k₂ s` the one at `θ₂ = θ₁ + s`, and `expTilt Q k' r` the one at
`θ' = θ₁ + r`. For `g` nonnegative outside `[C₁, C₂]`, nonpositive inside, and with vanishing
integral against *both* endpoint laws, the integral against the third law is nonnegative when
`θ'` lies outside `[θ₁, θ₂]` and nonpositive when it lies strictly inside. The two signs are
the two three-exponential separations `exists_sep_exp3_out` and `exists_sep_exp3_mid`. -/
private lemma integral_expTilt_signed_interval {Q : Measure ℝ} [IsProbabilityMeasure Q]
    {k₂ s k' r C₁ C₂ : ℝ} (hs : 0 < s) (hC : C₁ ≤ C₂)
    (hQ₂ : IsProbabilityMeasure (expTilt Q k₂ s))
    (hQ' : IsProbabilityMeasure (expTilt Q k' r))
    {g : ℝ → ℝ} (hgm : Measurable g) (hgb : ∀ u, |g u| ≤ 1)
    (hgpos : ∀ u, u < C₁ ∨ C₂ < u → 0 ≤ g u)
    (hgneg : ∀ u, C₁ < u → u < C₂ → g u ≤ 0)
    (h1 : ∫ u, g u ∂Q = 0) (h2 : ∫ u, g u ∂(expTilt Q k₂ s) = 0) :
    ((r < 0 ∨ s < r) → 0 ≤ ∫ u, g u ∂(expTilt Q k' r)) ∧
      (0 < r → r < s → ∫ u, g u ∂(expTilt Q k' r) ≤ 0) := by
  have hk₂ : 0 < k₂ := expTilt_factor_pos hQ₂
  have hk' : 0 < k' := expTilt_factor_pos hQ'
  obtain ⟨hd₂, -⟩ := integrable_expTiltDensity hk₂.le hQ₂
  obtain ⟨hd', -⟩ := integrable_expTiltDensity hk'.le hQ'
  have hbare : ∀ (k c : ℝ), 0 < k → Integrable (fun u => k * Real.exp (c * u)) Q →
      Integrable (fun u => Real.exp (c * u)) Q := by
    intro k c hk hint
    refine (hint.const_mul k⁻¹).congr (Filter.Eventually.of_forall fun u => ?_)
    field_simp
  have he₂ : Integrable (fun u => Real.exp (s * u)) Q := hbare k₂ s hk₂ hd₂
  have he' : Integrable (fun u => Real.exp (r * u)) Q := hbare k' r hk' hd'
  have hg : Integrable g Q :=
    Integrable.mono' (integrable_const (1 : ℝ)) hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hgb u)
  have hgbdd : ∀ᵐ u ∂Q, ‖g u‖ ≤ 1 :=
    Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hgb u
  have hge₂ : Integrable (fun u => g u * Real.exp (s * u)) Q :=
    he₂.bdd_mul (c := 1) hgm.aestronglyMeasurable hgbdd
  have hge' : Integrable (fun u => g u * Real.exp (r * u)) Q :=
    he'.bdd_mul (c := 1) hgm.aestronglyMeasurable hgbdd
  have hpull : ∀ (k c : ℝ), 0 ≤ k → ∫ u, g u ∂(expTilt Q k c)
      = k * ∫ u, g u * Real.exp (c * u) ∂Q := by
    intro k c hk
    rw [integral_expTilt Q hk c g, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  have hc2 : ∫ u, g u * Real.exp (s * u) ∂Q = 0 := by
    have h := hpull k₂ s hk₂.le
    rw [h2] at h
    rcases mul_eq_zero.mp h.symm with hz | hz
    · exact absurd hz (ne_of_gt hk₂)
    · exact hz
  constructor
  · intro hoside
    obtain ⟨a, b, hin, hout⟩ :=
      exists_sep_exp3_out (θ₁ := 0) (θ₂ := s) (ϑ := r) hs hoside hC
    simp only [zero_mul, Real.exp_zero, mul_one] at hin hout
    have hpt : ∀ u, 0 ≤ g u * (Real.exp (r * u) - (a + b * Real.exp (s * u))) := by
      intro u
      rcases lt_trichotomy u C₁ with h | h | h
      · exact mul_nonneg (hgpos u (Or.inl h)) (by linarith [hout u (Or.inl h.le)])
      · have hD1 := hout u (Or.inl (le_of_eq h))
        have hD2 := hin u (by linarith) (by linarith)
        have hz : Real.exp (r * u) - (a + b * Real.exp (s * u)) = 0 := by linarith
        rw [hz, mul_zero]
      · rcases lt_trichotomy u C₂ with h2 | h2 | h2
        · have hD := hin u h.le h2.le
          have hprodnn := mul_nonneg (neg_nonneg.mpr (hgneg u h h2))
            (neg_nonneg.mpr (by linarith :
              Real.exp (r * u) - (a + b * Real.exp (s * u)) ≤ 0))
          rwa [neg_mul_neg] at hprodnn
        · have hD1 := hin u h.le (le_of_eq h2)
          have hD2 := hout u (Or.inr (by linarith))
          have hz : Real.exp (r * u) - (a + b * Real.exp (s * u)) = 0 := by linarith
          rw [hz, mul_zero]
        · exact mul_nonneg (hgpos u (Or.inr h2)) (by linarith [hout u (Or.inr h2.le)])
    have hI : (0 : ℝ) ≤ ∫ u, g u * (Real.exp (r * u) - (a + b * Real.exp (s * u))) ∂Q :=
      integral_nonneg hpt
    have heq : (fun u => g u * (Real.exp (r * u) - (a + b * Real.exp (s * u))))
        = fun u => g u * Real.exp (r * u) - (a * g u + b * (g u * Real.exp (s * u))) := by
      funext u; ring
    have hA : Integrable (fun u => a * g u) Q := hg.const_mul a
    have hB : Integrable (fun u => b * (g u * Real.exp (s * u))) Q := hge₂.const_mul b
    have hsum : Integrable (fun u => a * g u + b * (g u * Real.exp (s * u))) Q := hA.add hB
    have hzs : ∫ u, (a * g u + b * (g u * Real.exp (s * u))) ∂Q = 0 := by
      rw [integral_add hA hB, integral_const_mul, integral_const_mul, h1, hc2]
      ring
    rw [heq, integral_sub hge' hsum, hzs, sub_zero] at hI
    rw [hpull k' r hk'.le]
    exact mul_nonneg hk'.le hI
  · intro hr0 hrs
    obtain ⟨a, b, hin, hout⟩ :=
      exists_sep_exp3_mid (θ₁ := 0) (θ₂ := s) (ϑ := r) hr0 hrs hC
    simp only [zero_mul, Real.exp_zero, mul_one] at hin hout
    have hpt : ∀ u, g u * (Real.exp (r * u) - (a + b * Real.exp (s * u))) ≤ 0 := by
      intro u
      rcases lt_trichotomy u C₁ with h | h | h
      · have hD := hout u (Or.inl h.le)
        have hprodnn := mul_nonneg (hgpos u (Or.inl h))
          (neg_nonneg.mpr (by linarith :
            Real.exp (r * u) - (a + b * Real.exp (s * u)) ≤ 0))
        rw [mul_neg] at hprodnn
        linarith
      · have hD1 := hout u (Or.inl (le_of_eq h))
        have hD2 := hin u (by linarith) (by linarith)
        have hz : Real.exp (r * u) - (a + b * Real.exp (s * u)) = 0 := by linarith
        rw [hz, mul_zero]
      · rcases lt_trichotomy u C₂ with h2 | h2 | h2
        · have hD := hin u h.le h2.le
          have hprodnn := mul_nonneg (neg_nonneg.mpr (hgneg u h h2))
            (by linarith : (0 : ℝ) ≤ Real.exp (r * u) - (a + b * Real.exp (s * u)))
          rw [neg_mul] at hprodnn
          linarith
        · have hD1 := hin u h.le (le_of_eq h2)
          have hD2 := hout u (Or.inr (by linarith))
          have hz : Real.exp (r * u) - (a + b * Real.exp (s * u)) = 0 := by linarith
          rw [hz, mul_zero]
        · have hD := hout u (Or.inr h2.le)
          have hprodnn := mul_nonneg (hgpos u (Or.inr h2))
            (neg_nonneg.mpr (by linarith :
              Real.exp (r * u) - (a + b * Real.exp (s * u)) ≤ 0))
          rw [mul_neg] at hprodnn
          linarith
    have hI : ∫ u, g u * (Real.exp (r * u) - (a + b * Real.exp (s * u))) ∂Q ≤ 0 :=
      integral_nonpos hpt
    have heq : (fun u => g u * (Real.exp (r * u) - (a + b * Real.exp (s * u))))
        = fun u => g u * Real.exp (r * u) - (a * g u + b * (g u * Real.exp (s * u))) := by
      funext u; ring
    have hA : Integrable (fun u => a * g u) Q := hg.const_mul a
    have hB : Integrable (fun u => b * (g u * Real.exp (s * u))) Q := hge₂.const_mul b
    have hsum : Integrable (fun u => a * g u + b * (g u * Real.exp (s * u))) Q := hA.add hB
    have hzs : ∫ u, (a * g u + b * (g u * Real.exp (s * u))) ∂Q = 0 := by
      rw [integral_add hA hB, integral_const_mul, integral_const_mul, h1, hc2]
      ring
    rw [heq, integral_sub hge' hsum, hzs, sub_zero] at hI
    rw [hpull k' r hk'.le]
    exact mul_nonpos_of_nonneg_of_nonpos hk'.le hI

end FibreTilt

/-! ## Global toolkit: the canonical `(U, T)` family on its own scale

The canonical hypothesis `IsCanonicalUT` identifies the law of `(U, T)` with a `ν`-density.
Everything below is read off from that identification: the normalizing constant is strictly
positive, the laws of `(U, T)` — hence of `T` — are mutually equivalent across `Ω`, and the
power of a test of `(U, T)` is a ratio of two `ν`-integrals which is continuous along segments
of `Ω`, by the two-point envelope `e^{(1−s)a+sb} ≤ e^a + e^b`. -/

section CanonicalGlobal

/-- The canonical exponent `⟪(θ, ϑ), (u, t)⟫ = θu + ⟪ϑ, t⟫`. -/
private noncomputable def canExp (r z : ℝ × Ξ) : ℝ := r.1 * z.1 + ⟪r.2, z.2⟫_ℝ

private lemma canExp_apply (r z : ℝ × Ξ) : canExp r z = r.1 * z.1 + ⟪r.2, z.2⟫_ℝ := rfl

private lemma measurable_canExp [OpensMeasurableSpace Ξ] (r : ℝ × Ξ) :
    Measurable fun z : ℝ × Ξ => canExp r z := by
  have h : Measurable fun z : ℝ × Ξ => ⟪r.2, z.2⟫_ℝ :=
    ((innerSL ℝ r.2).continuous.measurable).comp measurable_snd
  exact (measurable_const.mul measurable_fst).add h

/-- The canonical exponent is affine in the parameter. -/
private lemma canExp_segment (p q : ℝ × Ξ) (s : ℝ) (z : ℝ × Ξ) :
    canExp ((1 - s) • p + s • q) z = (1 - s) * canExp p z + s * canExp q z := by
  simp only [canExp, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    inner_add_left, real_inner_smul_left]
  ring

/-- **Two-point envelope.** A convex combination of exponentials is below the sum of the two
endpoint exponentials — the dominating function for every segment of `Ω`. -/
private lemma exp_segment_le {a b s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    Real.exp ((1 - s) * a + s * b) ≤ Real.exp a + Real.exp b := by
  have hle : (1 - s) * a + s * b ≤ max a b := by
    have ha : a ≤ max a b := le_max_left _ _
    have hb : b ≤ max a b := le_max_right _ _
    nlinarith
  calc Real.exp ((1 - s) * a + s * b) ≤ Real.exp (max a b) := Real.exp_le_exp.mpr hle
    _ ≤ Real.exp a + Real.exp b := by
        rcases max_cases a b with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; linarith [Real.exp_pos b]
        · rw [h]; linarith [Real.exp_pos a]

variable {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
  {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ}

/-- The law of `(U, T)` is a probability measure. -/
private lemma isProbabilityMeasure_mapUT [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (p : ℝ × Ξ) :
    IsProbabilityMeasure ((P p).map fun x => (U x, T x)) :=
  Measure.isProbabilityMeasure_map (hU.prodMk hT).aemeasurable

/-- **The normalizing constant is strictly positive on `Ω`.** If `C p ≤ 0` the canonical
density vanishes identically and the law of `(U, T)` is the zero measure, which it is not. -/
private lemma canonicalUT_const_pos [OpensMeasurableSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {p : ℝ × Ξ} (hp : p ∈ Ω) : 0 < C p := by
  by_contra hcon
  push Not at hcon
  have hdens : (fun z : ℝ × Ξ => ENNReal.ofReal (C p * Real.exp (canExp p z))) = 0 := by
    funext z
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero]
    have h := mul_nonneg (neg_nonneg.mpr hcon) (Real.exp_pos (canExp p z)).le
    rw [neg_mul] at h
    linarith
  haveI := isProbabilityMeasure_mapUT (P := P) hU hT p
  have h1 : ((P p).map fun x => (U x, T x)) Set.univ = 1 := measure_univ
  rw [hUT p hp] at h1
  simp only [canExp_apply] at hdens
  rw [hdens, withDensity_zero] at h1
  simp at h1

/-- **Integrability and normalization of the canonical density.** -/
private lemma integrable_canExp [OpensMeasurableSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {p : ℝ × Ξ} (hp : p ∈ Ω) :
    Integrable (fun z => Real.exp (canExp p z)) ν ∧
      C p * ∫ z, Real.exp (canExp p z) ∂ν = 1 := by
  have hCp := canonicalUT_const_pos hU hT hUT hp
  have hm : Measurable fun z : ℝ × Ξ => C p * Real.exp (canExp p z) :=
    (measurable_canExp p).exp.const_mul _
  have hnn : (0 : (ℝ × Ξ) → ℝ) ≤ᵐ[ν] fun z => C p * Real.exp (canExp p z) :=
    Filter.Eventually.of_forall fun z => by
      have h : (0 : ℝ) ≤ C p * Real.exp (canExp p z) := by positivity
      simpa using h
  haveI := isProbabilityMeasure_mapUT (P := P) hU hT p
  have hlin : ∫⁻ z, ENNReal.ofReal (C p * Real.exp (canExp p z)) ∂ν = 1 := by
    have h1 : ((P p).map fun x => (U x, T x)) Set.univ = 1 := measure_univ
    rw [hUT p hp, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h1
    exact h1
  have hint : Integrable (fun z => C p * Real.exp (canExp p z)) ν :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hnn).mp
      (by rw [hlin]; exact ENNReal.one_ne_top)
  have hval : ∫ z, C p * Real.exp (canExp p z) ∂ν = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable, hlin,
      ENNReal.toReal_one]
  refine ⟨?_, ?_⟩
  · have := hint.const_mul (C p)⁻¹
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    field_simp
  · rw [integral_const_mul] at hval; exact hval

/-- **Every test of `(U, T)` has power a ratio of two `ν`-integrals.** -/
private lemma integral_comp_UT_eq [OpensMeasurableSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {p : ℝ × Ξ} (hp : p ∈ Ω) {g : ℝ × Ξ → ℝ} (hg : Measurable g) :
    ∫ x, g (U x, T x) ∂(P p) = C p * ∫ z, g z * Real.exp (canExp p z) ∂ν := by
  have hmap : ∫ x, g (U x, T x) ∂(P p)
      = ∫ z, g z ∂((P p).map fun x => (U x, T x)) :=
    (integral_map (hU.prodMk hT).aemeasurable hg.aestronglyMeasurable).symm
  rw [hmap, hUT p hp]
  have hnn : ∀ z : ℝ × Ξ, 0 ≤ C p * Real.exp (canExp p z) := fun z => by
    have := canonicalUT_const_pos hU hT hUT hp
    positivity
  simp only [← canExp_apply]
  rw [integral_withDensity_ofReal_mul ν ((measurable_canExp p).exp.const_mul _) hnn g,
    ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)

/-- **Integrability of a function of `(U, T)` is integrability of its canonical density.**
The `Integrable` twin of `integral_comp_UT_eq`, and — unlike that lemma, which is about
bounded `g` in every application — the form that an *unbounded* integrand needs. Both
directions are used: the "`→`" one reads an integrability statement at one parameter down to
`ν`, the "`←`" one reads it back up at another parameter, and composing them is exactly the
tilt transfer `integrable_statLaw_tilt` below. -/
private lemma integrable_comp_UT_iff [OpensMeasurableSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {p : ℝ × Ξ} (hp : p ∈ Ω) {g : ℝ × Ξ → ℝ} (hg : Measurable g) :
    Integrable (fun x => g (U x, T x)) (P p)
      ↔ Integrable (fun z => g z * Real.exp (canExp p z)) ν := by
  have hCp := canonicalUT_const_pos hU hT hUT hp
  have hdm : Measurable fun z : ℝ × Ξ => ENNReal.ofReal (C p * Real.exp (canExp p z)) :=
    ((measurable_canExp p).exp.const_mul (C p)).ennreal_ofReal
  have hstep : Integrable (fun x => g (U x, T x)) (P p)
      ↔ Integrable g ((P p).map fun x => (U x, T x)) :=
    (integrable_map_measure hg.aestronglyMeasurable (hU.prodMk hT).aemeasurable).symm
  rw [hstep, hUT p hp]
  simp only [← canExp_apply]
  rw [integrable_withDensity_iff_integrable_smul' hdm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hne : C p ≠ 0 := ne_of_gt hCp
  constructor
  · intro hI
    refine (hI.const_mul (C p)⁻¹).congr (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    field_simp
  · intro hI
    refine (hI.const_mul (C p)).congr (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    ring

/-- **Tilt transfer of integrability between two boundary laws of `T`.** If `f` is integrable
for the law of `T` at `(θ₀, ϑ)`, then `f · e^{⟪ϑ − ϑ₁, ·⟫}` is integrable for the law of `T`
at `(θ₀, ϑ₁)` — the two boundary laws differ exactly by that exponential tilt.

This is the step that removes the boundedness hypothesis from `boundedlyComplete_boundary`:
that proof used `|f| ≤ Cb` for one purpose only, namely to dominate the tilted integrand, and
the domination is unnecessary once the integrability is *transported* rather than re-proved.
The route is `integrable_comp_UT_iff` downwards at `(θ₀, ϑ)`, the pointwise identity
`e^{canExp (θ₀,ϑ) z} = e^{⟪ϑ − ϑ₁, z.2⟫}·e^{canExp (θ₀,ϑ₁) z}` (the `u`-part of the canonical
exponent is the same at both parameters because they share the first coordinate), and
`integrable_comp_UT_iff` upwards at `(θ₀, ϑ₁)`. -/
private lemma integrable_statLaw_tilt [OpensMeasurableSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {θ₀ : ℝ} {ϑ ϑ₁ : Ξ} (hϑ : ((θ₀, ϑ) : ℝ × Ξ) ∈ Ω) (hϑ₁ : ((θ₀, ϑ₁) : ℝ × Ξ) ∈ Ω)
    {f : Ξ → ℝ} (hf : Measurable f)
    (hfi : Integrable f ((P ((θ₀, ϑ) : ℝ × Ξ)).map T)) :
    Integrable (fun t : Ξ => f t * Real.exp ⟪ϑ - ϑ₁, t⟫_ℝ)
      ((P ((θ₀, ϑ₁) : ℝ × Ξ)).map T) := by
  have hinnerm : Measurable fun t : Ξ => ⟪ϑ - ϑ₁, t⟫_ℝ :=
    (innerSL ℝ (ϑ - ϑ₁)).continuous.measurable
  have h1 : Integrable (fun x => f (T x)) (P ((θ₀, ϑ) : ℝ × Ξ)) :=
    (integrable_map_measure hf.aestronglyMeasurable hT.aemeasurable).1 hfi
  have h2 : Integrable (fun z : ℝ × Ξ => f z.2 * Real.exp (canExp ((θ₀, ϑ) : ℝ × Ξ) z)) ν :=
    (integrable_comp_UT_iff hU hT hUT hϑ (hf.comp measurable_snd)).1 h1
  have heq : ∀ z : ℝ × Ξ,
      (f z.2 * Real.exp ⟪ϑ - ϑ₁, z.2⟫_ℝ) * Real.exp (canExp ((θ₀, ϑ₁) : ℝ × Ξ) z)
        = f z.2 * Real.exp (canExp ((θ₀, ϑ) : ℝ × Ξ) z) := by
    intro z
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    simp only [canExp_apply, inner_sub_left]
    ring
  have h3 : Integrable (fun z : ℝ × Ξ =>
      (f z.2 * Real.exp ⟪ϑ - ϑ₁, z.2⟫_ℝ) * Real.exp (canExp ((θ₀, ϑ₁) : ℝ × Ξ) z)) ν :=
    h2.congr (Filter.Eventually.of_forall fun z => (heq z).symm)
  have h4 : Integrable
      (fun x => (fun z : ℝ × Ξ => f z.2 * Real.exp ⟪ϑ - ϑ₁, z.2⟫_ℝ) (U x, T x))
      (P ((θ₀, ϑ₁) : ℝ × Ξ)) :=
    (integrable_comp_UT_iff hU hT hUT hϑ₁
      ((hf.comp measurable_snd).mul ((hinnerm.comp measurable_snd).exp))).2 h3
  exact (integrable_map_measure (hf.mul hinnerm.exp).aestronglyMeasurable
    hT.aemeasurable).2 h4

/-- **The laws of `(U, T)` are mutually equivalent across `Ω`**: the canonical density is
finite and everywhere strictly positive, so each of them is equivalent to `ν`. -/
private lemma mapUT_ac [OpensMeasurableSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {p q : ℝ × Ξ} (hp : p ∈ Ω) (hq : q ∈ Ω) :
    (P p).map (fun x => (U x, T x)) ≪ (P q).map fun x => (U x, T x) := by
  have hCq := canonicalUT_const_pos hU hT hUT hq
  rw [hUT p hp, hUT q hq]
  simp only [← canExp_apply]
  refine (withDensity_absolutelyContinuous ν _).trans
    (withDensity_absolutelyContinuous' ?_ ?_)
  · exact ((measurable_canExp q).exp.const_mul (C q)).ennreal_ofReal.aemeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have : (0 : ℝ) < C q * Real.exp (canExp q z) := by positivity
    exact this

/-- **The laws of `T` are mutually equivalent across `Ω`.** -/
private lemma statLaw_ac [OpensMeasurableSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {p q : ℝ × Ξ} (hp : p ∈ Ω) (hq : q ∈ Ω) : (P p).map T ≪ (P q).map T := by
  have hsnd : ∀ r : ℝ × Ξ, ((P r).map fun x => (U x, T x)).map Prod.snd = (P r).map T := by
    intro r
    rw [Measure.map_map measurable_snd (hU.prodMk hT)]
    rfl
  have := (mapUT_ac hU hT hUT hp hq).map (f := Prod.snd) measurable_snd
  rwa [hsnd p, hsnd q] at this

/-- **Power is continuous along segments of `Ω`.** For a critical function of the pair
`(U, T)`, the power at `(1−sₙ)p + sₙq` converges to the power at `p` as `sₙ → 0`. Both the
numerator and the denominator of the ratio representation converge by dominated convergence,
the dominating function being the two-point envelope `e^{⟪p,·⟫} + e^{⟪q,·⟫}`, which is
`ν`-integrable because both endpoints lie in `Ω`. This is what upgrades the level inequality
at a boundary parameter to similarity, and it uses only convexity of `Ω`. -/
private lemma tendsto_integral_canonical_segment [OpensMeasurableSpace Ξ]
    [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    (hΩ : Convex ℝ Ω) {p q : ℝ × Ξ} (hp : p ∈ Ω) (hq : q ∈ Ω)
    {g : ℝ × Ξ → ℝ} (hgm : Measurable g) (hgb : ∀ z, |g z| ≤ 1)
    {s : ℕ → ℝ} (hs01 : ∀ n, s n ∈ Set.Icc (0 : ℝ) 1)
    (hs : Filter.Tendsto s Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, g (U x, T x) ∂(P ((1 - s n) • p + s n • q)))
      Filter.atTop (nhds (∫ x, g (U x, T x) ∂(P p))) := by
  set r : ℕ → ℝ × Ξ := fun n => (1 - s n) • p + s n • q with hrdef
  have hrΩ : ∀ n, r n ∈ Ω := fun n =>
    hΩ hp hq (by linarith [(hs01 n).2]) (hs01 n).1 (by ring)
  obtain ⟨hIp, hnormp⟩ := integrable_canExp hU hT hUT hp
  obtain ⟨hIq, -⟩ := integrable_canExp hU hT hUT hq
  have hCp := canonicalUT_const_pos hU hT hUT hp
  -- the two-point envelope dominates every exponential on the segment
  have hdom : ∀ n, ∀ z : ℝ × Ξ,
      Real.exp (canExp (r n) z) ≤ Real.exp (canExp p z) + Real.exp (canExp q z) := by
    intro n z
    rw [hrdef, canExp_segment]
    exact exp_segment_le (hs01 n).1 (hs01 n).2
  -- dominated convergence for an arbitrary bounded weight
  have hJ : ∀ h : ℝ × Ξ → ℝ, Measurable h → (∀ z, |h z| ≤ 1) →
      Filter.Tendsto (fun n => ∫ z, h z * Real.exp (canExp (r n) z) ∂ν) Filter.atTop
        (nhds (∫ z, h z * Real.exp (canExp p z) ∂ν)) := by
    intro h hhm hhb
    refine tendsto_integral_of_dominated_convergence
      (fun z => Real.exp (canExp p z) + Real.exp (canExp q z))
      (fun n => (hhm.mul (measurable_canExp (r n)).exp).aestronglyMeasurable)
      (hIp.add hIq) (fun n => Filter.Eventually.of_forall fun z => ?_)
      (Filter.Eventually.of_forall fun z => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |h z| * Real.exp (canExp (r n) z) ≤ 1 * Real.exp (canExp (r n) z) := by
            gcongr; exact hhb z
        _ = Real.exp (canExp (r n) z) := one_mul _
        _ ≤ _ := hdom n z
    · have hlin : Filter.Tendsto (fun n => (1 - s n) * canExp p z + s n * canExp q z)
          Filter.atTop (nhds (canExp p z)) := by
        have h1 : Filter.Tendsto (fun n => 1 - s n) Filter.atTop (nhds (1 : ℝ)) := by
          simpa using Filter.Tendsto.const_sub (1 : ℝ) hs
        have h2 := (h1.mul_const (canExp p z)).add (hs.mul_const (canExp q z))
        simpa using h2
      have hcomp := ((Real.continuous_exp.tendsto (canExp p z)).comp hlin).const_mul (h z)
      refine hcomp.congr fun n => ?_
      rw [Function.comp_apply, hrdef, canExp_segment]
  -- the ratio representation of the power
  have hratio : ∀ n, ∫ x, g (U x, T x) ∂(P (r n))
      = (∫ z, g z * Real.exp (canExp (r n) z) ∂ν)
        / ∫ z, Real.exp (canExp (r n) z) ∂ν := by
    intro n
    obtain ⟨-, hnorm⟩ := integrable_canExp hU hT hUT (hrΩ n)
    have hCn := canonicalUT_const_pos hU hT hUT (hrΩ n)
    have hIn : (∫ z, Real.exp (canExp (r n) z) ∂ν) = 1 / C (r n) := by
      field_simp
      linarith [hnorm]
    rw [integral_comp_UT_eq hU hT hUT (hrΩ n) hgm, hIn]
    field_simp
  have hratiop : ∫ x, g (U x, T x) ∂(P p)
      = (∫ z, g z * Real.exp (canExp p z) ∂ν) / ∫ z, Real.exp (canExp p z) ∂ν := by
    have hIn : (∫ z, Real.exp (canExp p z) ∂ν) = 1 / C p := by
      field_simp
      linarith [hnormp]
    rw [integral_comp_UT_eq hU hT hUT hp hgm, hIn]
    field_simp
  have hden : (∫ z, Real.exp (canExp p z) ∂ν) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hnormp
    exact absurd hnormp (by norm_num)
  have hnum := hJ g hgm hgb
  have hdenlim := hJ (fun _ => (1 : ℝ)) measurable_const (fun _ => by norm_num)
  simp only [one_mul] at hdenlim
  simp only [hratiop]
  exact (hnum.div hdenlim hden).congr fun n => (hratio n).symm

/-- A convex parameter set reaching strictly below and strictly above `θ₀` meets the boundary
surface `θ = θ₀`. -/
private lemma exists_mem_fst_eq (hΩ : Convex ℝ Ω) {θ₀ : ℝ}
    (hlt : ∃ p ∈ Ω, p.1 < θ₀) (hgt : ∃ p ∈ Ω, θ₀ < p.1) : ∃ p ∈ Ω, p.1 = θ₀ := by
  obtain ⟨a, ha, halt⟩ := hlt
  obtain ⟨b, hb, hbgt⟩ := hgt
  set s : ℝ := (θ₀ - a.1) / (b.1 - a.1) with hs
  have hden : (0 : ℝ) < b.1 - a.1 := by linarith
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hden.le
  have hs1 : s ≤ 1 := by rw [hs, div_le_one hden]; linarith
  refine ⟨(1 - s) • a + s • b, hΩ ha hb (by linarith) hs0 (by ring), ?_⟩
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hs]
  field_simp
  ring


/-! ### Conditional bridge -/

/-- The law of `T` is a probability measure. -/
private lemma isProbabilityMeasure_statLaw [∀ p, IsProbabilityMeasure (P p)]
    (hT : Measurable T) (p : ℝ × Ξ) : IsProbabilityMeasure ((P p).map T) :=
  Measure.isProbabilityMeasure_map hT.aemeasurable

/-- The conditional power is a measurable function of the conditioning variable. -/
private lemma measurable_condPower (hU : Measurable U) (hT : Measurable T)
    {φ : ℝ × Ξ → ℝ} (hφ : Measurable φ) (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    Measurable fun t => ∫ u, φ (u, t) ∂(condDistrib U T μ t) := by
  have h : StronglyMeasurable fun q : Ξ × ℝ => φ (q.2, q.1) :=
    (hφ.comp (measurable_snd.prodMk measurable_fst)).stronglyMeasurable
  exact (h.integral_kernel_prod_right' (κ := condDistrib U T μ)).measurable

/-- The conditional power of a `[-1,1]`-valued test lies in `[-1,1]`. -/
private lemma abs_condPower_le (μ : Measure 𝓧) [IsFiniteMeasure μ] {φ : ℝ × Ξ → ℝ}
    (hU : Measurable U) (hT : Measurable T) (hφb : ∀ z, |φ z| ≤ 1) (t : Ξ) :
    |∫ u, φ (u, t) ∂(condDistrib U T μ t)| ≤ 1 := by
  haveI : IsProbabilityMeasure (condDistrib U T μ t) := inferInstance
  have h := norm_integral_le_of_norm_le_const (C := (1 : ℝ))
    (μ := condDistrib U T μ t) (f := fun u => φ (u, t))
    (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hφb _)
  rw [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at h
  exact h

/-- **The power is the average of the conditional powers.** -/
private lemma integral_comp_eq_integral_condPower [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) {φ : ℝ × Ξ → ℝ} (hφ : Measurable φ)
    (hφb : ∀ z, |φ z| ≤ 1) (p : ℝ × Ξ) :
    ∫ x, φ (U x, T x) ∂(P p)
      = ∫ t, (∫ u, φ (u, t) ∂(condDistrib U T (P p) t)) ∂((P p).map T) :=
  integral_eq_integral_condDistrib hU hT hφ
    (Integrable.mono' (integrable_const (1 : ℝ))
      ((hφ.comp (hU.prodMk hT)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hφb _))

/-- **The conditional laws are exponential tilts of one another.** For `(P p).map T`-almost
every `t`, the conditional law of `U` given `T = t` at `p` is the `(p.1 − p₀.1)`-tilt of the
conditional law at the reference parameter `p₀`. -/
private lemma ae_condDistrib_expTilt [BorelSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {p₀ p : ℝ × Ξ} (hp₀ : p₀ ∈ Ω) (hp : p ∈ Ω) :
    ∀ᵐ t ∂((P p).map T), ∃ k : ℝ, 0 ≤ k ∧
      condDistrib U T (P p) t = expTilt (condDistrib U T (P p₀) t) k (p.1 - p₀.1) := by
  obtain ⟨νt, Ct, hct⟩ := condDistrib_expFamily_of_isCanonicalUT hU hT hUT
  have h2 : ∀ᵐ t ∂((P p).map T), condDistrib U T (P p₀) t
      = (νt t).withDensity fun u => ENNReal.ofReal (Ct t p₀.1 * Real.exp (p₀.1 * u)) :=
    Filter.Eventually.filter_mono (statLaw_ac hU hT hUT hp hp₀).ae_le (hct p₀ hp₀)
  filter_upwards [hct p hp, h2] with t ht1 ht2
  haveI hpr0 : IsProbabilityMeasure (condDistrib U T (P p₀) t) := inferInstance
  haveI hpr : IsProbabilityMeasure (condDistrib U T (P p) t) := inferInstance
  have hapos : 0 < Ct t p₀.1 := by
    refine expTilt_factor_pos (Q := νt t) (k := Ct t p₀.1) (c := p₀.1) ?_
    rw [expTilt, ← ht2]; exact hpr0
  have hbpos : 0 < Ct t p.1 := by
    refine expTilt_factor_pos (Q := νt t) (k := Ct t p.1) (c := p.1) ?_
    rw [expTilt, ← ht1]; exact hpr
  refine ⟨Ct t p.1 / Ct t p₀.1, (div_pos hbpos hapos).le, ?_⟩
  rw [ht1, ht2]
  exact withDensity_line_tilt (νt t) hapos

/-- **Similarity at a boundary parameter.** A critical function of `(U, T)` whose power is at
most `α` at `p₀` and at least `α` at every interior point of a segment leaving `p₀` inside
`Ω` has power exactly `α` at `p₀`. -/
private lemma integral_comp_eq_of_le_of_segment [BorelSpace Ξ]
    [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    (hΩ : Convex ℝ Ω) {p₀ q : ℝ × Ξ} (hp₀ : p₀ ∈ Ω) (hq : q ∈ Ω)
    {ψ : ℝ × Ξ → ℝ} (hψm : Measurable ψ) (hψb : ∀ z, |ψ z| ≤ 1) {α : ℝ}
    (hle : ∫ x, ψ (U x, T x) ∂(P p₀) ≤ α)
    (hge : ∀ s : ℝ, 0 < s → s ≤ 1 →
      α ≤ ∫ x, ψ (U x, T x) ∂(P ((1 - s) • p₀ + s • q))) :
    ∫ x, ψ (U x, T x) ∂(P p₀) = α := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have h01 : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    refine ⟨(hpos n).le, ?_⟩
    rw [div_le_one (by positivity)]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hto0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := tendsto_integral_canonical_segment hU hT hUT hΩ hp₀ hq hψm hψb h01 hto0
  have hge' : α ≤ ∫ x, ψ (U x, T x) ∂(P p₀) :=
    ge_of_tendsto' hlim fun n => hge _ (hpos n) (h01 n).2
  linarith

/-- **An interior point of `Ω` on the boundary surface.** For a convex parameter set whose
affine span is everything, in finite dimension, and which reaches strictly below and strictly
above `θ₀`, the surface `θ = θ₀` meets the *interior* of `Ω`.

The two hypotheses are exactly the two amendments discussed at `boundedlyComplete_boundary`:
`affineSpan ℝ Ω = ⊤` (not the weaker `Submodule.span ℝ Ω = ⊤`) and finite dimension.

Besides feeding `interior_slice_nonempty`, this is the brick that lets the *pure-`θ`* segment
`(θ₀ ± ε, ϑ₀)` be taken inside `Ω`, which is what the derivative side condition of the point
null needs (see `isUMPU_conditional_point`); along a general segment of `Ω` the derivative of
the power picks up the nuisance directions. -/
private lemma exists_interior_boundary_point [FiniteDimensional ℝ Ξ]
    (hΩ_convex : Convex ℝ Ω) (hΩ_aff : affineSpan ℝ Ω = ⊤) {θ₀ : ℝ}
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1) :
    ∃ w : ℝ × Ξ, w ∈ interior Ω ∧ w.1 = θ₀ := by
  obtain ⟨z, hz⟩ := (Convex.interior_nonempty_iff_affineSpan_eq_top hΩ_convex).2 hΩ_aff
  -- push an interior point of `Ω` onto the surface `θ = θ₀` along a segment
  have hstep : ∀ q : ℝ × Ξ, q ∈ Ω → z.1 < θ₀ → θ₀ < q.1 →
        ∃ w : ℝ × Ξ, w ∈ interior Ω ∧ w.1 = θ₀ := by
    intro q hq hz1 hq1
    set s : ℝ := (θ₀ - z.1) / (q.1 - z.1) with hsdef
    have hden : 0 < q.1 - z.1 := by linarith
    have hs0 : 0 < s := div_pos (by linarith) hden
    have hs1 : s < 1 := by
      rw [hsdef, div_lt_one hden]; linarith
    refine ⟨(1 - s) • z + s • q,
      Convex.combo_interior_self_mem_interior hΩ_convex hz hq (by linarith) hs0.le (by ring),
      ?_⟩
    have hfst : ((1 - s) • z + s • q).1 = (1 - s) * z.1 + s * q.1 := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    have hkey : s * (q.1 - z.1) = θ₀ - z.1 := by
      rw [hsdef]; field_simp
    rw [hfst]
    linear_combination hkey
  rcases lt_trichotomy z.1 θ₀ with h | h | h
  · obtain ⟨q, hq, hqθ⟩ := hΩ_gt
    exact hstep q hq h hqθ
  · exact ⟨z, hz, h⟩
  · -- symmetric: reflect the first coordinate
    obtain ⟨q, hq, hqθ⟩ := hΩ_lt
    set t : ℝ := (z.1 - θ₀) / (z.1 - q.1) with htdef
    have hden : 0 < z.1 - q.1 := by linarith
    have ht0 : 0 < t := div_pos (by linarith) hden
    have ht1 : t < 1 := by rw [htdef, div_lt_one hden]; linarith
    refine ⟨(1 - t) • z + t • q,
      Convex.combo_interior_self_mem_interior hΩ_convex hz hq (by linarith) ht0.le (by ring),
      ?_⟩
    have hfst : ((1 - t) • z + t • q).1 = (1 - t) * z.1 + t * q.1 := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    have hkey : t * (z.1 - q.1) = z.1 - θ₀ := by
      rw [htdef]; field_simp
    rw [hfst]
    linear_combination -hkey

/-- **An interior point of the boundary slice.** The slice `{ϑ | (θ₀, ϑ) ∈ Ω}` has nonempty
interior in `Ξ`; this is what makes the boundary family of laws of `T` a `k`-dimensional
exponential family, hence complete. -/
private lemma interior_slice_nonempty [FiniteDimensional ℝ Ξ]
    (hΩ_convex : Convex ℝ Ω) (hΩ_aff : affineSpan ℝ Ω = ⊤) {θ₀ : ℝ}
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1) :
    (interior {ϑ : Ξ | (θ₀, ϑ) ∈ Ω}).Nonempty := by
  obtain ⟨w, hw, hwθ⟩ := exists_interior_boundary_point hΩ_convex hΩ_aff hΩ_lt hΩ_gt
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior w hw
  have hsub : Metric.ball w.2 r ⊆ {ϑ : Ξ | (θ₀, ϑ) ∈ Ω} := by
    intro ϑ hϑ
    have hmem : ((θ₀, ϑ) : ℝ × Ξ) ∈ Metric.ball w r := by
      rw [Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ (Metric.mem_ball.1 hϑ)
      rw [hwθ]
      simpa using hr
    have hΩmem : ((θ₀, ϑ) : ℝ × Ξ) ∈ Ω := interior_subset (hball hmem)
    exact hΩmem
  exact ⟨w.2, mem_interior.2 ⟨Metric.ball w.2 r, hsub, Metric.isOpen_ball,
    Metric.mem_ball_self hr⟩⟩

/-- **Bounded completeness of the boundary family.**

The laws of `T` over a boundary surface `ω = {p ∈ Ω | p.1 = θ₀}` are boundedly complete.

This is the Lehmann–Scheffé input of `TSH4 §4.4 Thm 4.4.1`. The source derives it from
convexity of `Ω` together with the non-degeneracy "`Ω` is not contained in a linear space of
dimension less than `k+1`": with parameters of `Ω` strictly on both sides of `θ₀`, those force
the slice `{ϑ | (θ₀, ϑ) ∈ Ω}` to have nonempty interior in `Ξ` (`interior_slice_nonempty`); on
that slice the laws of `T` form a canonical exponential family in `ϑ`, so Laplace-transform
uniqueness gives completeness.

**Proof.** The base measure `ν` of `IsCanonicalUT` is not assumed σ-finite, and its `Ξ`-margin
need not be either, so the exponential family is *not* set up against a `ϑ`-free base measure
here. Instead, one interior boundary parameter `ϑ₁` is fixed and every other boundary law of
`T` is written as the `(ϑ − ϑ₁)`-exponential tilt of the probability measure
`μ₁ = (P (θ₀, ϑ₁)).map T` — an identity read off `integral_comp_UT_eq` on both sides, the
`u`-integration cancelling because the tilting factor depends on `z` only through `z.2`. That
makes the reference measure a probability measure, hence σ-finite, and the vanishing
hypothesis becomes the vanishing of the Laplace transform of `f` against `μ₁` on the
translated slice `S − ϑ₁`, which has `0` in its interior. Transporting along the isometry
`(stdOrthonormalBasis ℝ Ξ).repr : Ξ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ Ξ))` — inner
products, and therefore the whole Laplace transform, are preserved — puts the statement in
the form of `PointEstimation.ae_eq_zero_of_integral_exp_inner_eq_zero`. Mutual equivalence of
the boundary laws (`statLaw_ac`) then carries `f =ᵐ[μ₁] 0` to every boundary parameter.

**Two flagged amendments, both indispensable.**
* `[FiniteDimensional ℝ Ξ]`: an infinite-dimensional convex set can have full span, or full
  affine span, without having any interior point, and then the slice family need not be
  complete.
* `hΩ_aff : affineSpan ℝ Ω = ⊤` — and **not** the frozen `Submodule.span ℝ Ω = ⊤`, which is
  strictly weaker and does **not** suffice. Degenerate example: `Ξ = ℝ`,
  `Ω = {(θ, 1 − θ) : θ ∈ [-1, 1]}` is convex, has `Submodule.span ℝ Ω = ⊤` (it contains
  `(0,1)` and `(1,0)`) and reaches strictly below and above `θ₀ = 0`, yet its boundary
  surface `{p ∈ Ω | p.1 = 0}` is the single point `(0,1)`, so the boundary family of laws of
  `T` is a *one-element* family and is not complete. `affineSpan ℝ Ω = ⊤` is the faithful
  reading of the source's "not contained in a linear space of dimension less than `k+1`"
  ("linear space" = affine flat), and in finite dimension it is exactly what makes the
  boundary slice `k`-dimensional.

**Unbounded, not just boundedly, complete.** `f` is only required to be measurable and
*integrable* for each boundary law — not bounded. This matters: the derivative side condition
of the point null, `E_{θ₀}[Uψ ∣ t] = α·E_{θ₀}[U ∣ t]`, tests a function of `t` built from the
unbounded `U`, so `IsBoundedlyCompleteFamily` is too weak for it. The upstream
`PointEstimation.ae_eq_zero_of_integral_exp_inner_eq_zero` was always stated for arbitrary
measurable `f`; the only place the old proof used a bound `|f| ≤ Cb` was to dominate the
tilted integrand `f · e^{⟪ϑ − ϑ₁, ·⟫}` against `μ₁`, and that integrability is *transported*
from the law at `(θ₀, ϑ)` by `integrable_statLaw_tilt` instead. `boundedlyComplete_boundary`
below is the bounded corollary, and is what the three other optimality theorems consume.

**The hypotheses are only asked at parameters interior to `Ω`.** `hfint`/`hfzero` quantify
over `(θ₀, ϑ) ∈ interior Ω`, not over the whole boundary slice, and the reference parameter
`ϑ₁` is taken from `exists_interior_boundary_point` rather than from
`interior_slice_nonempty`. Nothing is lost — the slice `S'` of admissible tilt directions is
then literally *open*, so `interior S' = S' ∋ 0` and the Laplace-uniqueness input applies
verbatim, while the conclusion is still `f =ᵐ 0` for **every** `p ∈ Ω` because the laws of
`T` are mutually equivalent (`statLaw_ac`). This weakening is what makes the lemma usable at
`isUMPU_conditional_point`: the derivative side condition is only available where a *pure-`θ`
window* `(θ₀ ± η, ϑ)` fits inside `Ω`, which for a general convex `Ω` holds at interior
points of the surface but can fail at boundary points of it (e.g. at the apex of a triangle
whose base straddles `θ₀`). -/
private lemma complete_boundary [BorelSpace Ξ] [FiniteDimensional ℝ Ξ]
    [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    (hΩ_convex : Convex ℝ Ω) (hΩ_aff : affineSpan ℝ Ω = ⊤) {θ₀ : ℝ}
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1)
    {f : Ξ → ℝ} (hf : Measurable f)
    (hfint : ∀ ϑ : Ξ, ((θ₀, ϑ) : ℝ × Ξ) ∈ interior Ω →
      Integrable f ((P ((θ₀, ϑ) : ℝ × Ξ)).map T))
    (hfzero : ∀ ϑ : Ξ, ((θ₀, ϑ) : ℝ × Ξ) ∈ interior Ω →
      ∫ t, f t ∂((P ((θ₀, ϑ) : ℝ × Ξ)).map T) = 0)
    {p : ℝ × Ξ} (hp : p ∈ Ω) :
    f =ᵐ[(P p).map T] 0 := by
  classical
  -- a boundary point interior to `Ω` *itself*, used as the reference parameter
  obtain ⟨w, hwint, hwθ⟩ := exists_interior_boundary_point hΩ_convex hΩ_aff hΩ_lt hΩ_gt
  set ϑ₁ : Ξ := w.2 with hϑ₁def
  have hw1 : ((θ₀, ϑ₁) : ℝ × Ξ) = w := by rw [hϑ₁def, ← hwθ]
  have hϑ₁int : ((θ₀, ϑ₁) : ℝ × Ξ) ∈ interior Ω := by rw [hw1]; exact hwint
  have hϑ₁ : ((θ₀, ϑ₁) : ℝ × Ξ) ∈ Ω := interior_subset hϑ₁int
  have hinnerm : ∀ η : Ξ, Measurable fun t : Ξ => ⟪η, t⟫_ℝ := fun η =>
    (innerSL ℝ η).continuous.measurable
  have hinnerm' : ∀ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ Ξ)),
      Measurable fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ Ξ)) => ⟪y, z⟫_ℝ := fun y =>
    (innerSL ℝ y).continuous.measurable
  haveI hμ₁prob : IsProbabilityMeasure ((P ((θ₀, ϑ₁) : ℝ × Ξ)).map T) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  set μ₁ : Measure Ξ := (P ((θ₀, ϑ₁) : ℝ × Ξ)).map T with hμ₁
  -- (1) Every boundary law of `T` is the `(ϑ − ϑ₁)`-exponential tilt of `μ₁`, so the vanishing
  -- hypothesis becomes the vanishing of a Laplace transform on the slice.
  have hkey : ∀ ϑ : Ξ, ((θ₀, ϑ) : ℝ × Ξ) ∈ interior Ω →
      ∫ t, f t * Real.exp ⟪ϑ - ϑ₁, t⟫_ℝ ∂μ₁ = 0 := by
    intro ϑ hϑint
    have hϑ : ((θ₀, ϑ) : ℝ × Ξ) ∈ Ω := interior_subset hϑint
    have hCϑ : 0 < C ((θ₀, ϑ) : ℝ × Ξ) := canonicalUT_const_pos hU hT hUT hϑ
    have hgm : Measurable fun z : ℝ × Ξ => f z.2 * Real.exp ⟪ϑ - ϑ₁, z.2⟫_ℝ :=
      (hf.comp measurable_snd).mul (((hinnerm (ϑ - ϑ₁)).comp measurable_snd).exp)
    have h1 : ∫ t, f t * Real.exp ⟪ϑ - ϑ₁, t⟫_ℝ ∂μ₁
        = C ((θ₀, ϑ₁) : ℝ × Ξ) * ∫ z, (f z.2 * Real.exp ⟪ϑ - ϑ₁, z.2⟫_ℝ) *
            Real.exp (canExp ((θ₀, ϑ₁) : ℝ × Ξ) z) ∂ν := by
      rw [hμ₁, integral_map hT.aemeasurable
        ((hf.fun_mul ((hinnerm (ϑ - ϑ₁)).exp)).aestronglyMeasurable)]
      exact integral_comp_UT_eq hU hT hUT hϑ₁ hgm
    have h2 : ∫ z, (f z.2 * Real.exp ⟪ϑ - ϑ₁, z.2⟫_ℝ) *
          Real.exp (canExp ((θ₀, ϑ₁) : ℝ × Ξ) z) ∂ν
        = ∫ z, f z.2 * Real.exp (canExp ((θ₀, ϑ) : ℝ × Ξ) z) ∂ν := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      dsimp only
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      simp only [canExp_apply, inner_sub_left]
      ring
    have h3 : C ((θ₀, ϑ) : ℝ × Ξ) * ∫ z, f z.2 * Real.exp (canExp ((θ₀, ϑ) : ℝ × Ξ) z) ∂ν = 0 := by
      rw [← integral_comp_UT_eq hU hT hUT hϑ (g := fun z : ℝ × Ξ => f z.2)
        (hf.comp measurable_snd)]
      have hz := hfzero ϑ hϑint
      rwa [integral_map hT.aemeasurable hf.aestronglyMeasurable] at hz
    have h4 : ∫ z, f z.2 * Real.exp (canExp ((θ₀, ϑ) : ℝ × Ξ) z) ∂ν = 0 := by
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hCϑ.ne'
      · exact h
    rw [h1, h2, h4, mul_zero]
  -- (2) Transport to `EuclideanSpace` and apply Laplace-transform uniqueness.
  set e : Ξ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Ξ)) :=
    (stdOrthonormalBasis ℝ Ξ).repr with hedef
  have hemeas : Measurable e := e.continuous.measurable
  have hesymm : Measurable e.symm := e.symm.continuous.measurable
  haveI : IsProbabilityMeasure μ₁ := hμ₁prob
  set ν' : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ Ξ))) := μ₁.map e with hν'
  haveI hν'prob : IsProbabilityMeasure ν' := by
    rw [hν']; exact Measure.isProbabilityMeasure_map hemeas.aemeasurable
  set f' : EuclideanSpace ℝ (Fin (Module.finrank ℝ Ξ)) → ℝ := fun y => f (e.symm y) with hf'def
  have hf'm : Measurable f' := hf.comp hesymm
  set S' : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ Ξ))) :=
    {y | ((θ₀, e.symm y + ϑ₁) : ℝ × Ξ) ∈ interior Ω} with hS'def
  have hbridge : ∀ (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ Ξ))) (t : Ξ),
      f' (e t) * Real.exp ⟪y, e t⟫_ℝ = f t * Real.exp ⟪e.symm y, t⟫_ℝ := by
    intro y t
    have hin : ⟪y, e t⟫_ℝ = ⟪e.symm y, t⟫_ℝ := by
      conv_lhs => rw [← e.apply_symm_apply y]
      exact e.inner_map_map _ _
    rw [hf'def, hin]
    simp only [LinearIsometryEquiv.symm_apply_apply]
  -- `S'` is now literally an open set, so its interior is itself and contains `0`
  have hS'open : IsOpen S' := by
    have hcont : Continuous fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ Ξ)) =>
        ((θ₀, e.symm y + ϑ₁) : ℝ × Ξ) :=
      continuous_const.prodMk (e.symm.continuous.add continuous_const)
    exact isOpen_interior.preimage hcont
  have hS'int : (interior S').Nonempty := by
    refine ⟨0, ?_⟩
    rw [hS'open.interior_eq, hS'def]
    simpa using hϑ₁int
  have hint' : ∀ y ∈ S', Integrable (fun z => f' z * Real.exp ⟪y, z⟫_ℝ) ν' := by
    intro y hy
    have hϑmemI : ((θ₀, e.symm y + ϑ₁) : ℝ × Ξ) ∈ interior Ω := hy
    have hϑmem : ((θ₀, e.symm y + ϑ₁) : ℝ × Ξ) ∈ Ω := interior_subset hϑmemI
    -- the tilted integrability is TRANSPORTED from the law at `(θ₀, e.symm y + ϑ₁)`,
    -- not dominated by a bound on `f`; this is the only step that used `|f| ≤ Cb`
    have hIt : Integrable (fun t : Ξ => f t * Real.exp ⟪e.symm y, t⟫_ℝ) μ₁ := by
      have htr := integrable_statLaw_tilt hU hT hUT hϑmem hϑ₁ hf (hfint _ hϑmemI)
      rw [add_sub_cancel_right] at htr
      rw [hμ₁]
      exact htr
    have hmy : Measurable fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ Ξ)) =>
        f' z * Real.exp ⟪y, z⟫_ℝ := hf'm.mul (hinnerm' y).exp
    rw [hν']
    refine (integrable_map_measure hmy.aestronglyMeasurable hemeas.aemeasurable).2 ?_
    exact hIt.congr (Filter.Eventually.of_forall fun t => (hbridge y t).symm)
  have hzero' : ∀ y ∈ S', ∫ z, f' z * Real.exp ⟪y, z⟫_ℝ ∂ν' = 0 := by
    intro y hy
    have hϑmemI : ((θ₀, e.symm y + ϑ₁) : ℝ × Ξ) ∈ interior Ω := hy
    have hk := hkey (e.symm y + ϑ₁) hϑmemI
    rw [add_sub_cancel_right] at hk
    have hmy : Measurable fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ Ξ)) =>
        f' z * Real.exp ⟪y, z⟫_ℝ := hf'm.mul (hinnerm' y).exp
    rw [hν', integral_map hemeas.aemeasurable hmy.aestronglyMeasurable]
    refine Eq.trans ?_ hk
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => hbridge y t)
  have hae0 : f' =ᵐ[ν'] 0 :=
    PointEstimation.ae_eq_zero_of_integral_exp_inner_eq_zero hf'm hS'int hint' hzero'
  have haeμ : ∀ᵐ t ∂μ₁, f t = 0 := by
    have hset : MeasurableSet {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ Ξ)) | f' y = 0} :=
      hf'm (measurableSet_singleton (0 : ℝ))
    have hae0' : ∀ᵐ y ∂(μ₁.map e), f' y = 0 := by rw [← hν']; exact hae0
    have h := (ae_map_iff hemeas.aemeasurable hset).1 hae0'
    filter_upwards [h] with t ht
    simpa only [hf'def, LinearIsometryEquiv.symm_apply_apply] using ht
  have hac : (P p).map T ≪ μ₁ := by
    rw [hμ₁]; exact statLaw_ac hU hT hUT hp hϑ₁
  exact haeμ.filter_mono hac.ae_le

/-- **Bounded completeness of the boundary family.** The special case of `complete_boundary`
in which `f` is uniformly bounded: on the boundary laws — probability measures — a bounded
measurable function is automatically integrable, so the integrability hypothesis is free.
This is the form the three closed optimality theorems of this file consume. -/
private lemma boundedlyComplete_boundary [BorelSpace Ξ] [FiniteDimensional ℝ Ξ]
    [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    (hΩ_convex : Convex ℝ Ω) (hΩ_aff : affineSpan ℝ Ω = ⊤) {θ₀ : ℝ}
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1) :
    PointEstimation.IsBoundedlyCompleteFamily
      fun p : {p : ℝ × Ξ // p ∈ Ω ∧ p.1 = θ₀} => (P (p : ℝ × Ξ)).map T := by
  intro f hf hbdd hzero p
  obtain ⟨Cb, hCb⟩ := hbdd
  refine complete_boundary hU hT hUT hΩ_convex hΩ_aff hΩ_lt hΩ_gt hf
    (fun ϑ _ => ?_) (fun ϑ hϑ => hzero ⟨(θ₀, ϑ), interior_subset hϑ, rfl⟩) p.2.1
  haveI : IsProbabilityMeasure ((P ((θ₀, ϑ) : ℝ × Ξ)).map T) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  refine Integrable.mono' (integrable_const Cb) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  exact hCb t

/-- **Similar ⇒ Neyman structure.** A critical function of `(U, T)` which is similar of size
`α` on the whole boundary surface `θ = θ₀` has conditional size `α` for almost every `t`. -/
private lemma ae_condPower_eq_of_similar [BorelSpace Ξ] [FiniteDimensional ℝ Ξ]
    [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    (hΩ_convex : Convex ℝ Ω) (hΩ_aff : affineSpan ℝ Ω = ⊤) {θ₀ α : ℝ}
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1)
    {p₀ : ℝ × Ξ} (hp₀ : p₀ ∈ Ω) (hp₀θ : p₀.1 = θ₀)
    {ψ : ℝ × Ξ → ℝ} (hψm : Measurable ψ) (hψb : ∀ z, |ψ z| ≤ 1)
    (hsim : ∀ p ∈ Ω, p.1 = θ₀ → ∫ x, ψ (U x, T x) ∂(P p) = α) :
    ∀ᵐ t ∂((P p₀).map T), ∫ u, ψ (u, t) ∂(condDistrib U T (P p₀) t) = α := by
  set f : Ξ → ℝ := fun t => (∫ u, ψ (u, t) ∂(condDistrib U T (P p₀) t)) - α with hf
  have hfm : Measurable f := (measurable_condPower hU hT hψm (P p₀)).sub measurable_const
  have hfb : ∃ c, ∀ t, |f t| ≤ c := by
    refine ⟨1 + |α|, fun t => ?_⟩
    have h1 := abs_condPower_le (P p₀) hU hT hψb t
    have h2 : |f t| ≤ |∫ u, ψ (u, t) ∂(condDistrib U T (P p₀) t)| + |α| := abs_sub _ _
    linarith
  have hzero : ∀ p : {p : ℝ × Ξ // p ∈ Ω ∧ p.1 = θ₀},
      ∫ t, f t ∂((P (p : ℝ × Ξ)).map T) = 0 := by
    rintro ⟨p, hpΩ, hpθ⟩
    haveI := isProbabilityMeasure_statLaw (P := P) hT p
    have hcd : ∀ᵐ t ∂((P p).map T),
        (∫ u, ψ (u, t) ∂(condDistrib U T (P p₀) t))
          = ∫ u, ψ (u, t) ∂(condDistrib U T (P p) t) := by
      filter_upwards [condDistrib_eq_of_fst_eq hU hT hUT hpΩ hp₀ (by rw [hpθ, hp₀θ])]
        with t ht
      rw [ht]
    have hint : Integrable (fun t => ∫ u, ψ (u, t) ∂(condDistrib U T (P p₀) t))
        ((P p).map T) :=
      Integrable.mono' (integrable_const (1 : ℝ))
        (measurable_condPower hU hT hψm (P p₀)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs]; exact abs_condPower_le (P p₀) hU hT hψb t)
    rw [hf, integral_sub hint (integrable_const α), integral_congr_ae hcd,
      ← integral_comp_eq_integral_condPower hU hT hψm hψb p, hsim p hpΩ hpθ]
    simp
  have hae := boundedlyComplete_boundary hU hT hUT hΩ_convex hΩ_aff (θ₀ := θ₀) hΩ_lt hΩ_gt
    f hfm hfb hzero ⟨p₀, hp₀, hp₀θ⟩
  filter_upwards [hae] with t ht
  have hz : (∫ u, ψ (u, t) ∂(condDistrib U T (P p₀) t)) - α = 0 := ht
  linarith

/-- **The fibrewise engine.** Let `g` be a bounded measurable function of `(u, t)` which is
nonnegative above the threshold `C₀ t`, nonpositive below it, and has vanishing conditional
integral for almost every `t` at the reference parameter `p₀`. Then its unconditional
integral has the sign of `p.1 − p₀.1`. Applied to `g = φ − α` this gives the level and the
unbiasedness of the conditional one-sided test; applied to `g = φ − ψ` it gives its
optimality against any competitor with the same Neyman structure. -/
private lemma integral_comp_sign_of_condZero [BorelSpace Ξ]
    [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {p₀ p : ℝ × Ξ} (hp₀ : p₀ ∈ Ω) (hp : p ∈ Ω) {C₀ : Ξ → ℝ}
    {g : ℝ × Ξ → ℝ} (hgm : Measurable g) (hgb : ∀ z, |g z| ≤ 1)
    (hgpos : ∀ z : ℝ × Ξ, C₀ z.2 < z.1 → 0 ≤ g z)
    (hgneg : ∀ z : ℝ × Ξ, z.1 < C₀ z.2 → g z ≤ 0)
    (hgzero : ∀ᵐ t ∂((P p₀).map T), ∫ u, g (u, t) ∂(condDistrib U T (P p₀) t) = 0) :
    (p₀.1 ≤ p.1 → 0 ≤ ∫ x, g (U x, T x) ∂(P p)) ∧
      (p.1 ≤ p₀.1 → ∫ x, g (U x, T x) ∂(P p) ≤ 0) := by
  haveI := isProbabilityMeasure_statLaw (P := P) hT p
  have hgzero' : ∀ᵐ t ∂((P p).map T), ∫ u, g (u, t) ∂(condDistrib U T (P p₀) t) = 0 :=
    Filter.Eventually.filter_mono (statLaw_ac hU hT hUT hp hp₀).ae_le hgzero
  have hkey : ∀ᵐ t ∂((P p).map T),
      (p₀.1 ≤ p.1 → 0 ≤ ∫ u, g (u, t) ∂(condDistrib U T (P p) t)) ∧
        (p.1 ≤ p₀.1 → (∫ u, g (u, t) ∂(condDistrib U T (P p) t)) ≤ 0) := by
    filter_upwards [hgzero', ae_condDistrib_expTilt hU hT hUT hp₀ hp] with t ht0 htilt
    obtain ⟨k, hk, htilt⟩ := htilt
    haveI : IsProbabilityMeasure (condDistrib U T (P p₀) t) := inferInstance
    haveI hpr : IsProbabilityMeasure (expTilt (condDistrib U T (P p₀) t) k (p.1 - p₀.1)) := by
      rw [← htilt]; infer_instance
    have hgmt : Measurable fun u : ℝ => g (u, t) :=
      hgm.comp (measurable_id.prodMk measurable_const)
    have hsig := integral_expTilt_signed (Q := condDistrib U T (P p₀) t) (k := k)
      (c := p.1 - p₀.1) (C := C₀ t) hk hpr hgmt (fun u => hgb _)
      (fun u hu => hgpos (u, t) hu) (fun u hu => hgneg (u, t) hu)
    rw [ht0, mul_zero] at hsig
    rw [htilt]
    exact ⟨fun hle => hsig.1 (by linarith), fun hle => hsig.2 (by linarith)⟩
  rw [integral_comp_eq_integral_condPower hU hT hgm hgb p]
  constructor
  · intro hle
    refine integral_nonneg_of_ae ?_
    filter_upwards [hkey] with t ht
    exact ht.1 hle
  · intro hle
    refine integral_nonpos_of_ae ?_
    filter_upwards [hkey] with t ht
    exact ht.2 hle

/-- Bounded measurable functions of `(U, T)` are integrable. -/
private lemma integrable_comp_UT [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) {a : ℝ × Ξ → ℝ} (ham : Measurable a)
    (hab : ∀ z, |a z| ≤ 1) (p : ℝ × Ξ) : Integrable (fun x => a (U x, T x)) (P p) :=
  Integrable.mono' (integrable_const (1 : ℝ))
    ((ham.comp (hU.prodMk hT)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hab _)

/-- Bounded measurable functions are conditionally integrable. -/
private lemma integrable_cond_slice (μ : Measure 𝓧) [IsFiniteMeasure μ]
    (hU : Measurable U) (hT : Measurable T) {a : ℝ × Ξ → ℝ} (ham : Measurable a)
    (hab : ∀ z, |a z| ≤ 1) (t : Ξ) :
    Integrable (fun u => a (u, t)) (condDistrib U T μ t) := by
  haveI : IsProbabilityMeasure (condDistrib U T μ t) := inferInstance
  exact Integrable.mono' (integrable_const (1 : ℝ))
    ((ham.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hab _)

/-- **The two-endpoint fibrewise engine.** The interval analogue of
`integral_comp_sign_of_condZero`: `g` is nonnegative outside the interval
`[C₁ t, C₂ t]` in `u`, nonpositive inside, and has vanishing conditional integral at both
boundary parameters `p₁` (first coordinate `θ₁`) and `p₂` (first coordinate `θ₂`). Then its
unconditional integral is nonnegative outside `[θ₁, θ₂]` and nonpositive strictly inside. -/
private lemma integral_comp_sign_of_condZero_interval [BorelSpace Ξ]
    [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {p₁ p₂ p : ℝ × Ξ} (hp₁ : p₁ ∈ Ω) (hp₂ : p₂ ∈ Ω) (hp : p ∈ Ω) (hlt : p₁.1 < p₂.1)
    {C₁ C₂ : Ξ → ℝ} (hCle : ∀ t, C₁ t ≤ C₂ t)
    {g : ℝ × Ξ → ℝ} (hgm : Measurable g) (hgb : ∀ z, |g z| ≤ 1)
    (hgpos : ∀ z : ℝ × Ξ, z.1 < C₁ z.2 ∨ C₂ z.2 < z.1 → 0 ≤ g z)
    (hgneg : ∀ z : ℝ × Ξ, C₁ z.2 < z.1 → z.1 < C₂ z.2 → g z ≤ 0)
    (hz₁ : ∀ᵐ t ∂((P p₁).map T), ∫ u, g (u, t) ∂(condDistrib U T (P p₁) t) = 0)
    (hz₂ : ∀ᵐ t ∂((P p₂).map T), ∫ u, g (u, t) ∂(condDistrib U T (P p₂) t) = 0) :
    ((p.1 < p₁.1 ∨ p₂.1 < p.1) → 0 ≤ ∫ x, g (U x, T x) ∂(P p)) ∧
      (p₁.1 < p.1 → p.1 < p₂.1 → ∫ x, g (U x, T x) ∂(P p) ≤ 0) := by
  haveI := isProbabilityMeasure_statLaw (P := P) hT p
  have e1 := Filter.Eventually.filter_mono (statLaw_ac hU hT hUT hp hp₁).ae_le hz₁
  have e2 := Filter.Eventually.filter_mono (statLaw_ac hU hT hUT hp hp₂).ae_le hz₂
  have t2 := Filter.Eventually.filter_mono (statLaw_ac hU hT hUT hp hp₂).ae_le
    (ae_condDistrib_expTilt hU hT hUT hp₁ hp₂)
  have tp := ae_condDistrib_expTilt hU hT hUT hp₁ hp
  have hkey : ∀ᵐ t ∂((P p).map T),
      ((p.1 < p₁.1 ∨ p₂.1 < p.1) → 0 ≤ ∫ u, g (u, t) ∂(condDistrib U T (P p) t)) ∧
        (p₁.1 < p.1 → p.1 < p₂.1 →
          ∫ u, g (u, t) ∂(condDistrib U T (P p) t) ≤ 0) := by
    filter_upwards [e1, e2, t2, tp] with t ht1 ht2 hd₂ hdp
    obtain ⟨k₂, hk₂, hteq₂⟩ := hd₂
    obtain ⟨k', hk', hteqp⟩ := hdp
    haveI : IsProbabilityMeasure (condDistrib U T (P p₁) t) := inferInstance
    haveI hQ₂ :
        IsProbabilityMeasure (expTilt (condDistrib U T (P p₁) t) k₂ (p₂.1 - p₁.1)) := by
      rw [← hteq₂]; infer_instance
    haveI hQ' :
        IsProbabilityMeasure (expTilt (condDistrib U T (P p₁) t) k' (p.1 - p₁.1)) := by
      rw [← hteqp]; infer_instance
    have h2' : ∫ u, g (u, t) ∂(expTilt (condDistrib U T (P p₁) t) k₂ (p₂.1 - p₁.1)) = 0 := by
      rw [← hteq₂]; exact ht2
    have hgmt : Measurable fun u : ℝ => g (u, t) :=
      hgm.comp (measurable_id.prodMk measurable_const)
    have hres := integral_expTilt_signed_interval (Q := condDistrib U T (P p₁) t)
      (k₂ := k₂) (s := p₂.1 - p₁.1) (k' := k') (r := p.1 - p₁.1) (C₁ := C₁ t) (C₂ := C₂ t)
      (by linarith) (hCle t) hQ₂ hQ' hgmt (fun u => hgb _)
      (fun u hu => hgpos (u, t) hu) (fun u hu hu2 => hgneg (u, t) hu hu2) ht1 h2'
    rw [hteqp]
    refine ⟨fun h => hres.1 ?_, fun ha hb => hres.2 (by linarith) (by linarith)⟩
    rcases h with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rw [integral_comp_eq_integral_condPower hU hT hgm hgb p]
  constructor
  · intro hside
    refine integral_nonneg_of_ae ?_
    filter_upwards [hkey] with t ht
    exact ht.1 hside
  · intro ha hb
    refine integral_nonpos_of_ae ?_
    filter_upwards [hkey] with t ht
    exact ht.2 ha hb
end CanonicalGlobal

/-! ### Measurability and range of the conditional tests -/

private lemma measurable_condOneSidedTest {C₀ γ₀ : Ξ → ℝ} (hC₀ : Measurable C₀)
    (hγ₀ : Measurable γ₀) : Measurable (condOneSidedTest C₀ γ₀) :=
  Measurable.ite (measurableSet_lt (hC₀.comp measurable_snd) measurable_fst) measurable_const
    (Measurable.ite (measurableSet_eq_fun measurable_fst (hC₀.comp measurable_snd))
      (hγ₀.comp measurable_snd) measurable_const)

private lemma condOneSidedTest_mem_Icc {C₀ γ₀ : Ξ → ℝ}
    (hγ₀_mem : ∀ t, γ₀ t ∈ Set.Icc (0 : ℝ) 1) (z : ℝ × Ξ) :
    condOneSidedTest C₀ γ₀ z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold condOneSidedTest
  split_ifs with h1 h2
  · exact ⟨zero_le_one, le_rfl⟩
  · exact hγ₀_mem z.2
  · exact ⟨le_rfl, zero_le_one⟩

private lemma condOneSidedTest_eq_one {C₀ γ₀ : Ξ → ℝ} {z : ℝ × Ξ} (hz : C₀ z.2 < z.1) :
    condOneSidedTest C₀ γ₀ z = 1 := by
  simp only [condOneSidedTest, if_pos hz]

private lemma condOneSidedTest_eq_zero {C₀ γ₀ : Ξ → ℝ} {z : ℝ × Ξ} (hz : z.1 < C₀ z.2) :
    condOneSidedTest C₀ γ₀ z = 0 := by
  simp only [condOneSidedTest, if_neg (not_lt.mpr hz.le), if_neg (ne_of_lt hz)]

private lemma abs_le_one_of_mem_Icc {f : ℝ × Ξ → ℝ} (h : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (z : ℝ × Ξ) : |f z| ≤ 1 :=
  abs_le.mpr ⟨by linarith [(h z).1], (h z).2⟩

private lemma measurable_condOutsideTest {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} (hC₁ : Measurable C₁)
    (hC₂ : Measurable C₂) (hγ₁ : Measurable γ₁) (hγ₂ : Measurable γ₂) :
    Measurable (condOutsideTest C₁ C₂ γ₁ γ₂) :=
  Measurable.ite
    ((measurableSet_lt measurable_fst (hC₁.comp measurable_snd)).union
      (measurableSet_lt (hC₂.comp measurable_snd) measurable_fst)) measurable_const
    (Measurable.ite (measurableSet_eq_fun measurable_fst (hC₁.comp measurable_snd))
      (hγ₁.comp measurable_snd)
      (Measurable.ite (measurableSet_eq_fun measurable_fst (hC₂.comp measurable_snd))
        (hγ₂.comp measurable_snd) measurable_const))

private lemma measurable_condInsideTest {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} (hC₁ : Measurable C₁)
    (hC₂ : Measurable C₂) (hγ₁ : Measurable γ₁) (hγ₂ : Measurable γ₂) :
    Measurable (condInsideTest C₁ C₂ γ₁ γ₂) :=
  Measurable.ite
    ((measurableSet_lt (hC₁.comp measurable_snd) measurable_fst).inter
      (measurableSet_lt measurable_fst (hC₂.comp measurable_snd))) measurable_const
    (Measurable.ite (measurableSet_eq_fun measurable_fst (hC₁.comp measurable_snd))
      (hγ₁.comp measurable_snd)
      (Measurable.ite (measurableSet_eq_fun measurable_fst (hC₂.comp measurable_snd))
        (hγ₂.comp measurable_snd) measurable_const))

private lemma condOutsideTest_mem_Icc {C₁ C₂ γ₁ γ₂ : Ξ → ℝ}
    (hγ₁_mem : ∀ t, γ₁ t ∈ Set.Icc (0 : ℝ) 1) (hγ₂_mem : ∀ t, γ₂ t ∈ Set.Icc (0 : ℝ) 1)
    (z : ℝ × Ξ) : condOutsideTest C₁ C₂ γ₁ γ₂ z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold condOutsideTest
  split_ifs
  · exact ⟨zero_le_one, le_rfl⟩
  · exact hγ₁_mem z.2
  · exact hγ₂_mem z.2
  · exact ⟨le_rfl, zero_le_one⟩

private lemma condInsideTest_mem_Icc {C₁ C₂ γ₁ γ₂ : Ξ → ℝ}
    (hγ₁_mem : ∀ t, γ₁ t ∈ Set.Icc (0 : ℝ) 1) (hγ₂_mem : ∀ t, γ₂ t ∈ Set.Icc (0 : ℝ) 1)
    (z : ℝ × Ξ) : condInsideTest C₁ C₂ γ₁ γ₂ z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold condInsideTest
  split_ifs
  · exact ⟨zero_le_one, le_rfl⟩
  · exact hγ₁_mem z.2
  · exact hγ₂_mem z.2
  · exact ⟨le_rfl, zero_le_one⟩

private lemma condOutsideTest_eq_one {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} {z : ℝ × Ξ}
    (hz : z.1 < C₁ z.2 ∨ C₂ z.2 < z.1) : condOutsideTest C₁ C₂ γ₁ γ₂ z = 1 := by
  simp only [condOutsideTest, if_pos hz]

private lemma condOutsideTest_eq_zero {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} {z : ℝ × Ξ}
    (h1 : C₁ z.2 < z.1) (h2 : z.1 < C₂ z.2) : condOutsideTest C₁ C₂ γ₁ γ₂ z = 0 := by
  have hn : ¬ (z.1 < C₁ z.2 ∨ C₂ z.2 < z.1) := by
    rintro (h | h) <;> linarith
  simp only [condOutsideTest, if_neg hn, if_neg (ne_of_gt h1), if_neg (ne_of_lt h2)]

private lemma condInsideTest_eq_one {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} {z : ℝ × Ξ}
    (h1 : C₁ z.2 < z.1) (h2 : z.1 < C₂ z.2) : condInsideTest C₁ C₂ γ₁ γ₂ z = 1 := by
  simp only [condInsideTest, if_pos (And.intro h1 h2)]

private lemma condInsideTest_eq_zero {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} (hC : ∀ t, C₁ t ≤ C₂ t)
    {z : ℝ × Ξ} (hz : z.1 < C₁ z.2 ∨ C₂ z.2 < z.1) : condInsideTest C₁ C₂ γ₁ γ₂ z = 0 := by
  have hCz := hC z.2
  have hn : ¬ (C₁ z.2 < z.1 ∧ z.1 < C₂ z.2) := by
    rintro ⟨ha, hb⟩; rcases hz with h | h <;> linarith
  have h1 : z.1 ≠ C₁ z.2 := by rcases hz with h | h; · exact ne_of_lt h
                               · exact ne_of_gt (by linarith)
  have h2 : z.1 ≠ C₂ z.2 := by rcases hz with h | h; · exact ne_of_lt (by linarith)
                               · exact ne_of_gt h
  simp only [condInsideTest, if_neg hn, if_neg h1, if_neg h2]

/-! ## The four UMP unbiased tests -/

/-- **One-sided null.** For `H : θ ≤ θ₀` against `K : θ > θ₀`, the conditional one-sided test
with conditional size `α` on the boundary surface `θ = θ₀` is UMP unbiased at level `α`. -/
theorem isUMPU_conditional_oneSided
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {C₀ γ₀ : Ξ → ℝ} {θ₀ α : ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ p, IsProbabilityMeasure (P p)]
    -- LEAN-ONLY (AMENDMENT): the σ-algebra of `Ξ` is the Borel one and `Ξ` is finite
    -- dimensional; see `boundedlyComplete_boundary` for why finite dimensionality cannot be
    -- dropped, and the docstring amendment note below
    [BorelSpace Ξ] [FiniteDimensional ℝ Ξ]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT (AMENDMENT): `(U, T)` is sufficient, in the operative sense that every
    -- critical function is matched in power by a critical function of `(U, T)`. Without it
    -- the statement is FALSE — see the counterexample section and the note in the docstring
    (hsuff : SufficiencyReducible P Ω U T)
    -- USER-INPUT: the parameter set is convex
    (hΩ_convex : Convex ℝ Ω)
    -- USER-INPUT: the parameter set is not contained in a proper linear subspace
    (hΩ_span : Submodule.span ℝ Ω = ⊤)
    -- USER-INPUT (AMENDMENT): the parameter set is not contained in a proper *affine*
    -- subspace either. This is the faithful reading of the source's "not contained in a
    -- linear space of dimension less than `k+1`", and it is strictly stronger than the
    -- frozen `hΩ_span`, which does not suffice: see `boundedlyComplete_boundary` for a
    -- convex `Ω` with full linear span whose boundary surface is a single point
    (hΩ_aff : affineSpan ℝ Ω = ⊤)
    -- USER-INPUT: the parameter set reaches below and above the null value
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: measurable selection of the critical value and randomization probability
    (hC₀ : Measurable C₀) (hγ₀ : Measurable γ₀)
    -- USER-INPUT: the randomization probability is a probability
    (hγ₀_mem : ∀ t, γ₀ t ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: conditional size `α` on the boundary surface `θ = θ₀`
    (hsize : ∀ p ∈ Ω, p.1 = θ₀ → ∀ᵐ t ∂((P p).map T),
      ∫ u, condOneSidedTest C₀ γ₀ (u, t) ∂(condDistrib U T (P p) t) = α) :
    IsUMPU P {p ∈ Ω | p.1 ≤ θ₀} {p ∈ Ω | θ₀ < p.1} α
      (fun x => condOneSidedTest C₀ γ₀ (U x, T x)) := by
  -- REPAIRED AND PROVED, over one lifted brick. The frozen form was FALSE, refuted by
  -- `ConditionalUMPUCounterexample.not_isUMPU_conditional_oneSided_counterexample`; the
  -- amendment `hsuff : SufficiencyReducible P Ω U T` excludes that counterexample (there
  -- `(U, T)` is constant, so no critical function of `(U, T)` matches the auxiliary-bit test
  -- `cxψ`) and restores the classical statement of `TSH4 §4.4 Thm 4.4.1`; in the source's own
  -- setting `𝓧 = ℝ × Ξ`, `(U, T) = (fst, snd)`, `hsuff` is vacuous
  -- (`sufficiencyReducible_prod`). The proof: level and unbiasedness are the fibrewise
  -- variation-diminishing inequality (`integral_comp_sign_of_condZero` applied to `φ − α`);
  -- optimality reduces by `hsuff` to a test of `(U, T)`, whose power at a boundary parameter
  -- is `α` by continuity along a segment of `Ω` (`integral_comp_eq_of_le_of_segment`), hence
  -- which has Neyman structure (`ae_condPower_eq_of_similar`, over the single lifted brick
  -- `boundedlyComplete_boundary`), and the same fibrewise inequality applied to `φ − ψ`.
  classical
  have hφm : Measurable (condOneSidedTest C₀ γ₀) := measurable_condOneSidedTest hC₀ hγ₀
  have hφIcc : ∀ z : ℝ × Ξ, condOneSidedTest C₀ γ₀ z ∈ Set.Icc (0 : ℝ) 1 :=
    condOneSidedTest_mem_Icc hγ₀_mem
  have hφb : ∀ z : ℝ × Ξ, |condOneSidedTest C₀ γ₀ z| ≤ 1 := abs_le_one_of_mem_Icc hφIcc
  obtain ⟨p₀, hp₀, hp₀θ⟩ := exists_mem_fst_eq hΩ_convex hΩ_lt hΩ_gt
  obtain ⟨qp, hqp, hqpθ⟩ := id hΩ_gt
  haveI hstat : ∀ p : ℝ × Ξ, IsProbabilityMeasure ((P p).map T) := fun p =>
    isProbabilityMeasure_statLaw (P := P) hT p
  have hsize₀ : ∀ᵐ t ∂((P p₀).map T),
      ∫ u, condOneSidedTest C₀ γ₀ (u, t) ∂(condDistrib U T (P p₀) t) = α :=
    hsize p₀ hp₀ hp₀θ
  -- the comparison function `φ − w`, for an arbitrary competitor `w` of the pair
  have hcmp : ∀ w : ℝ × Ξ → ℝ, Measurable w → (∀ z, w z ∈ Set.Icc (0 : ℝ) 1) →
      (∀ᵐ t ∂((P p₀).map T), ∫ u, w (u, t) ∂(condDistrib U T (P p₀) t) = α) →
      ∀ p ∈ Ω, (θ₀ ≤ p.1 → ∫ x, w (U x, T x) ∂(P p)
          ≤ ∫ x, condOneSidedTest C₀ γ₀ (U x, T x) ∂(P p)) ∧
        (p.1 ≤ θ₀ → ∫ x, condOneSidedTest C₀ γ₀ (U x, T x) ∂(P p)
          ≤ ∫ x, w (U x, T x) ∂(P p)) := by
    intro w hwm hwIcc hwsize p hp
    have hwb : ∀ z : ℝ × Ξ, |w z| ≤ 1 := abs_le_one_of_mem_Icc hwIcc
    set g : ℝ × Ξ → ℝ := fun z => condOneSidedTest C₀ γ₀ z - w z with hgdef
    have hgm : Measurable g := hφm.sub hwm
    have hgb : ∀ z, |g z| ≤ 1 := by
      intro z
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 := (hφIcc z).1
        have h2 := (hwIcc z).2
        simp only [hgdef]
        linarith
      · have h1 := (hφIcc z).2
        have h2 := (hwIcc z).1
        simp only [hgdef]
        linarith
    have hgpos : ∀ z : ℝ × Ξ, C₀ z.2 < z.1 → 0 ≤ g z := by
      intro z hz
      have h1 : condOneSidedTest C₀ γ₀ z = 1 := condOneSidedTest_eq_one hz
      have h2 := (hwIcc z).2
      simp only [hgdef, h1]
      linarith
    have hgneg : ∀ z : ℝ × Ξ, z.1 < C₀ z.2 → g z ≤ 0 := by
      intro z hz
      have h1 : condOneSidedTest C₀ γ₀ z = 0 := condOneSidedTest_eq_zero hz
      have h2 := (hwIcc z).1
      simp only [hgdef, h1]
      linarith
    have hgz : ∀ᵐ t ∂((P p₀).map T), ∫ u, g (u, t) ∂(condDistrib U T (P p₀) t) = 0 := by
      filter_upwards [hsize₀, hwsize] with t ht hw
      haveI : IsProbabilityMeasure (condDistrib U T (P p₀) t) := inferInstance
      rw [hgdef]
      rw [integral_sub (integrable_cond_slice (P p₀) hU hT hφm hφb t)
        (integrable_cond_slice (P p₀) hU hT hwm hwb t), ht, hw, sub_self]
    have hsplit : ∫ x, g (U x, T x) ∂(P p)
        = (∫ x, condOneSidedTest C₀ γ₀ (U x, T x) ∂(P p)) - ∫ x, w (U x, T x) ∂(P p) := by
      rw [hgdef]
      exact integral_sub (integrable_comp_UT hU hT hφm hφb p)
        (integrable_comp_UT hU hT hwm hwb p)
    have h := integral_comp_sign_of_condZero hU hT hUT hp₀ hp hgm hgb hgpos hgneg hgz
    rw [hsplit] at h
    exact ⟨fun hle => by linarith [h.1 (by rw [hp₀θ]; exact hle)],
      fun hle => by linarith [h.2 (by rw [hp₀θ]; exact hle)]⟩
  -- level and unbiasedness: compare with the constant test `α`
  have hconstsize : ∀ᵐ t ∂((P p₀).map T),
      ∫ _u, (α : ℝ) ∂(condDistrib U T (P p₀) t) = α := by
    refine Filter.Eventually.of_forall fun t => ?_
    haveI : IsProbabilityMeasure (condDistrib U T (P p₀) t) := inferInstance
    simp
  have hconstIcc : ∀ _z : ℝ × Ξ, (α : ℝ) ∈ Set.Icc (0 : ℝ) 1 := fun _ => ⟨hα₀.le, hα₁.le⟩
  have hconst := hcmp (fun _ => α) measurable_const hconstIcc hconstsize
  have hpowconst : ∀ p : ℝ × Ξ, ∫ _x, (α : ℝ) ∂(P p) = α := fun p => by simp
  refine ⟨⟨hφm.comp (hU.prodMk hT), fun x => hφIcc _⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro p ⟨hpΩ, hple⟩
    simp only [power]
    have := (hconst p hpΩ).2 hple
    rw [hpowconst p] at this
    exact this
  · rintro p ⟨hpΩ, hpgt⟩
    simp only [power]
    have := (hconst p hpΩ).1 hpgt.le
    rw [hpowconst p] at this
    exact this
  · -- optimality
    rintro ψ hψ hunb p' ⟨hp'Ω, hp'θ⟩
    obtain ⟨ψ', hψ'crit, hψ'pow⟩ := hsuff ψ hψ
    have hψ'b : ∀ z : ℝ × Ξ, |ψ' z| ≤ 1 := abs_le_one_of_mem_Icc hψ'crit.2
    have hsim : ∀ p ∈ Ω, p.1 = θ₀ → ∫ x, ψ' (U x, T x) ∂(P p) = α := by
      intro p hp hpθ
      refine integral_comp_eq_of_le_of_segment hU hT hUT hΩ_convex hp hqp
        hψ'crit.1 hψ'b ?_ ?_
      · rw [hψ'pow p hp]
        have := hunb.1 p ⟨hp, le_of_eq hpθ⟩
        simpa only [power] using this
      · intro s hs0 hs1
        have hr : (1 - s) • p + s • qp ∈ Ω :=
          hΩ_convex hp hqp (by linarith) hs0.le (by ring)
        have hrθ : θ₀ < ((1 - s) • p + s • qp).1 := by
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hpθ]
          nlinarith [mul_pos hs0 (sub_pos.mpr hqpθ)]
        rw [hψ'pow _ hr]
        have := hunb.2 _ ⟨hr, hrθ⟩
        simpa only [power] using this
    have hns := ae_condPower_eq_of_similar hU hT hUT hΩ_convex hΩ_aff hΩ_lt hΩ_gt hp₀ hp₀θ
      hψ'crit.1 hψ'b hsim
    have hfin := (hcmp ψ' hψ'crit.1 hψ'crit.2 hns p' hp'Ω).1 hp'θ.le
    simp only [power]
    rw [← hψ'pow p' hp'Ω]
    exact hfin

/-- **Null outside an interval.** For `H : θ ≤ θ₁ or θ ≥ θ₂` against `K : θ₁ < θ < θ₂`, the
conditional test rejecting *inside* an interval in `u`, with conditional size `α` on both
boundary surfaces `θ = θ₁` and `θ = θ₂`, is UMP unbiased at level `α`. -/
theorem isUMPU_conditional_inside
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} {θ₁ θ₂ α : ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ p, IsProbabilityMeasure (P p)]
    -- LEAN-ONLY (AMENDMENT): the σ-algebra of `Ξ` is the Borel one and `Ξ` is finite
    -- dimensional; see `boundedlyComplete_boundary`
    [BorelSpace Ξ] [FiniteDimensional ℝ Ξ]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT (AMENDMENT): `(U, T)` is sufficient, in the operative sense that every
    -- critical function is matched in power by a critical function of `(U, T)`. Without it
    -- the statement is FALSE — see the counterexample section and the note in the docstring
    (hsuff : SufficiencyReducible P Ω U T)
    -- USER-INPUT: the parameter set is convex
    (hΩ_convex : Convex ℝ Ω)
    -- USER-INPUT: the parameter set is not contained in a proper linear subspace
    (hΩ_span : Submodule.span ℝ Ω = ⊤)
    -- USER-INPUT (AMENDMENT): the parameter set is not contained in a proper *affine*
    -- subspace either. This is the faithful reading of the source's "not contained in a
    -- linear space of dimension less than `k+1`", and it is strictly stronger than the
    -- frozen `hΩ_span`, which does not suffice: see `boundedlyComplete_boundary` for a
    -- convex `Ω` with full linear span whose boundary surface is a single point
    (hΩ_aff : affineSpan ℝ Ω = ⊤)
    -- USER-INPUT: the two endpoints are ordered
    (hθ : θ₁ < θ₂)
    -- USER-INPUT: the parameter set reaches below and above each endpoint
    (hΩ_lt₁ : ∃ p ∈ Ω, p.1 < θ₁) (hΩ_gt₁ : ∃ p ∈ Ω, θ₁ < p.1)
    (hΩ_lt₂ : ∃ p ∈ Ω, p.1 < θ₂) (hΩ_gt₂ : ∃ p ∈ Ω, θ₂ < p.1)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: measurable selection of the critical values and randomization
    -- probabilities
    (hC₁ : Measurable C₁) (hC₂ : Measurable C₂)
    (hγ₁ : Measurable γ₁) (hγ₂ : Measurable γ₂)
    -- USER-INPUT: the randomization probabilities are probabilities
    (hγ₁_mem : ∀ t, γ₁ t ∈ Set.Icc (0 : ℝ) 1) (hγ₂_mem : ∀ t, γ₂ t ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the critical values are ordered
    (hC : ∀ t, C₁ t ≤ C₂ t)
    -- USER-INPUT: conditional size `α` on both boundary surfaces
    (hsize : ∀ p ∈ Ω, p.1 = θ₁ ∨ p.1 = θ₂ → ∀ᵐ t ∂((P p).map T),
      ∫ u, condInsideTest C₁ C₂ γ₁ γ₂ (u, t) ∂(condDistrib U T (P p) t) = α) :
    IsUMPU P {p ∈ Ω | p.1 ≤ θ₁ ∨ θ₂ ≤ p.1} {p ∈ Ω | θ₁ < p.1 ∧ p.1 < θ₂} α
      (fun x => condInsideTest C₁ C₂ γ₁ γ₂ (U x, T x)) := by
  -- REPAIRED AND PROVED, over the one lifted brick `boundedlyComplete_boundary`. The frozen
  -- form was FALSE, refuted by
  -- `ConditionalUMPUCounterexample.not_isUMPU_conditional_inside_counterexample`; the
  -- amendment `hsuff : SufficiencyReducible P Ω U T` excludes that counterexample and
  -- restores the classical statement of `TSH4 §4.4 Thm 4.4.1`; in the source's own setting
  -- `𝓧 = ℝ × Ξ`, `(U, T) = (fst, snd)`, `hsuff` is vacuous (`sufficiencyReducible_prod`).
  -- The proof is the one of `isUMPU_conditional_outside` read through `g ↦ −g`: here the
  -- comparison function is `w − φ`, which is again nonnegative outside `[C₁, C₂]` and
  -- nonpositive inside, so the same fibrewise three-exponential separation applies, with the
  -- roles of the two branches exchanged (the alternative is now the *interior* of the
  -- interval).
  classical
  have hφm : Measurable (condInsideTest C₁ C₂ γ₁ γ₂) :=
    measurable_condInsideTest hC₁ hC₂ hγ₁ hγ₂
  have hφIcc : ∀ z : ℝ × Ξ, condInsideTest C₁ C₂ γ₁ γ₂ z ∈ Set.Icc (0 : ℝ) 1 :=
    condInsideTest_mem_Icc hγ₁_mem hγ₂_mem
  have hφb : ∀ z : ℝ × Ξ, |condInsideTest C₁ C₂ γ₁ γ₂ z| ≤ 1 := abs_le_one_of_mem_Icc hφIcc
  obtain ⟨p₁, hp₁, hp₁θ⟩ := exists_mem_fst_eq hΩ_convex hΩ_lt₁ hΩ_gt₁
  obtain ⟨p₂, hp₂, hp₂θ⟩ := exists_mem_fst_eq hΩ_convex hΩ_lt₂ hΩ_gt₂
  haveI hstat : ∀ p : ℝ × Ξ, IsProbabilityMeasure ((P p).map T) := fun p =>
    isProbabilityMeasure_statLaw (P := P) hT p
  have hp₁₂ : p₁.1 < p₂.1 := by rw [hp₁θ, hp₂θ]; exact hθ
  have hsz₁ := hsize p₁ hp₁ (Or.inl hp₁θ)
  have hsz₂ := hsize p₂ hp₂ (Or.inr hp₂θ)
  -- the midpoint of the two boundary parameters is an alternative
  have hqmid : ((1 : ℝ) / 2) • p₁ + ((1 : ℝ) / 2) • p₂ ∈ Ω :=
    hΩ_convex hp₁ hp₂ (by norm_num) (by norm_num) (by norm_num)
  have hqmidθ : (((1 : ℝ) / 2) • p₁ + ((1 : ℝ) / 2) • p₂).1 = (θ₁ + θ₂) / 2 := by
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hp₁θ, hp₂θ]
    ring
  -- the fibrewise comparison against an arbitrary competitor of the pair
  have hcmp : ∀ w : ℝ × Ξ → ℝ, Measurable w → (∀ z, w z ∈ Set.Icc (0 : ℝ) 1) →
      (∀ᵐ t ∂((P p₁).map T), ∫ u, w (u, t) ∂(condDistrib U T (P p₁) t) = α) →
      (∀ᵐ t ∂((P p₂).map T), ∫ u, w (u, t) ∂(condDistrib U T (P p₂) t) = α) →
      ∀ p ∈ Ω, ((p.1 < θ₁ ∨ θ₂ < p.1) →
          ∫ x, condInsideTest C₁ C₂ γ₁ γ₂ (U x, T x) ∂(P p) ≤ ∫ x, w (U x, T x) ∂(P p)) ∧
        (θ₁ < p.1 → p.1 < θ₂ →
          ∫ x, w (U x, T x) ∂(P p)
            ≤ ∫ x, condInsideTest C₁ C₂ γ₁ γ₂ (U x, T x) ∂(P p)) := by
    intro w hwm hwIcc hw₁ hw₂ p hp
    have hwb : ∀ z : ℝ × Ξ, |w z| ≤ 1 := abs_le_one_of_mem_Icc hwIcc
    set g : ℝ × Ξ → ℝ := fun z => w z - condInsideTest C₁ C₂ γ₁ γ₂ z with hgdef
    have hgm : Measurable g := hwm.sub hφm
    have hgb : ∀ z, |g z| ≤ 1 := by
      intro z
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 := (hwIcc z).1
        have h2 := (hφIcc z).2
        simp only [hgdef]; linarith
      · have h1 := (hwIcc z).2
        have h2 := (hφIcc z).1
        simp only [hgdef]; linarith
    have hgpos : ∀ z : ℝ × Ξ, z.1 < C₁ z.2 ∨ C₂ z.2 < z.1 → 0 ≤ g z := by
      intro z hz
      have h1 : condInsideTest C₁ C₂ γ₁ γ₂ z = 0 := condInsideTest_eq_zero hC hz
      have h2 := (hwIcc z).1
      simp only [hgdef, h1]; linarith
    have hgneg : ∀ z : ℝ × Ξ, C₁ z.2 < z.1 → z.1 < C₂ z.2 → g z ≤ 0 := by
      intro z ha hb
      have h1 : condInsideTest C₁ C₂ γ₁ γ₂ z = 1 := condInsideTest_eq_one ha hb
      have h2 := (hwIcc z).2
      simp only [hgdef, h1]; linarith
    have hzc : ∀ (r : ℝ × Ξ),
        (∀ᵐ t ∂((P r).map T),
          ∫ u, condInsideTest C₁ C₂ γ₁ γ₂ (u, t) ∂(condDistrib U T (P r) t) = α) →
        (∀ᵐ t ∂((P r).map T), ∫ u, w (u, t) ∂(condDistrib U T (P r) t) = α) →
        ∀ᵐ t ∂((P r).map T), ∫ u, g (u, t) ∂(condDistrib U T (P r) t) = 0 := by
      intro r ha hb
      filter_upwards [ha, hb] with t hta htb
      haveI : IsProbabilityMeasure (condDistrib U T (P r) t) := inferInstance
      rw [hgdef, integral_sub (integrable_cond_slice (P r) hU hT hwm hwb t)
        (integrable_cond_slice (P r) hU hT hφm hφb t), hta, htb, sub_self]
    have hsplit : ∫ x, g (U x, T x) ∂(P p)
        = (∫ x, w (U x, T x) ∂(P p))
          - ∫ x, condInsideTest C₁ C₂ γ₁ γ₂ (U x, T x) ∂(P p) := by
      rw [hgdef]
      exact integral_sub (integrable_comp_UT hU hT hwm hwb p)
        (integrable_comp_UT hU hT hφm hφb p)
    have h := integral_comp_sign_of_condZero_interval hU hT hUT hp₁ hp₂ hp hp₁₂ hC hgm hgb
      hgpos hgneg (hzc p₁ hsz₁ hw₁) (hzc p₂ hsz₂ hw₂)
    rw [hsplit] at h
    refine ⟨fun hside => ?_, fun ha hb => ?_⟩
    · have := h.1 (by rcases hside with hs | hs
                      · exact Or.inl (by rw [hp₁θ]; exact hs)
                      · exact Or.inr (by rw [hp₂θ]; exact hs))
      linarith
    · have := h.2 (by rw [hp₁θ]; exact ha) (by rw [hp₂θ]; exact hb)
      linarith
  have hconstsize : ∀ r : ℝ × Ξ,
      ∀ᵐ t ∂((P r).map T), ∫ _u, (α : ℝ) ∂(condDistrib U T (P r) t) = α := by
    intro r
    refine Filter.Eventually.of_forall fun t => ?_
    haveI : IsProbabilityMeasure (condDistrib U T (P r) t) := inferInstance
    simp
  have hconstIcc : ∀ _z : ℝ × Ξ, (α : ℝ) ∈ Set.Icc (0 : ℝ) 1 := fun _ => ⟨hα₀.le, hα₁.le⟩
  have hconst := hcmp (fun _ => α) measurable_const hconstIcc (hconstsize p₁) (hconstsize p₂)
  have hpowconst : ∀ p : ℝ × Ξ, ∫ _x, (α : ℝ) ∂(P p) = α := fun p => by simp
  have hbdry : ∀ p ∈ Ω, (p.1 = θ₁ ∨ p.1 = θ₂) →
      ∫ x, condInsideTest C₁ C₂ γ₁ γ₂ (U x, T x) ∂(P p) = α := by
    intro p hp hpθ
    rw [integral_comp_eq_integral_condPower hU hT hφm hφb p,
      integral_congr_ae (hsize p hp hpθ)]
    simp
  refine ⟨⟨hφm.comp (hU.prodMk hT), fun x => hφIcc _⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro p ⟨hpΩ, hside⟩
    simp only [power]
    rcases hside with h | h
    · rcases eq_or_lt_of_le h with he | hl
      · exact le_of_eq (hbdry p hpΩ (Or.inl he))
      · have := (hconst p hpΩ).1 (Or.inl hl)
        rw [hpowconst p] at this
        exact this
    · rcases eq_or_lt_of_le h with he | hl
      · exact le_of_eq (hbdry p hpΩ (Or.inr he.symm))
      · have := (hconst p hpΩ).1 (Or.inr hl)
        rw [hpowconst p] at this
        exact this
  · rintro p ⟨hpΩ, hl, hr⟩
    simp only [power]
    have := (hconst p hpΩ).2 hl hr
    rw [hpowconst p] at this
    exact this
  · rintro ψ hψ hunb p' ⟨hp'Ω, hp'l, hp'r⟩
    obtain ⟨ψ', hψ'crit, hψ'pow⟩ := hsuff ψ hψ
    have hψ'b : ∀ z : ℝ × Ξ, |ψ' z| ≤ 1 := abs_le_one_of_mem_Icc hψ'crit.2
    have hsim : ∀ θ : ℝ, (θ = θ₁ ∨ θ = θ₂) →
        ∀ p ∈ Ω, p.1 = θ → ∫ x, ψ' (U x, T x) ∂(P p) = α := by
      intro θ hcase p hp hpθ
      refine integral_comp_eq_of_le_of_segment hU hT hUT hΩ_convex hp hqmid
        hψ'crit.1 hψ'b ?_ ?_
      · rw [hψ'pow p hp]
        have hnull : p ∈ {p ∈ Ω | p.1 ≤ θ₁ ∨ θ₂ ≤ p.1} := by
          refine ⟨hp, ?_⟩
          rcases hcase with he | he
          · exact Or.inl (by rw [hpθ, he])
          · exact Or.inr (by rw [hpθ, he])
        simpa only [power] using hunb.1 p hnull
      · intro s hs0 hs1
        have hr : (1 - s) • p + s • (((1 : ℝ) / 2) • p₁ + ((1 : ℝ) / 2) • p₂) ∈ Ω :=
          hΩ_convex hp hqmid (by linarith) hs0.le (by ring)
        have hrfst : ((1 - s) • p + s • (((1 : ℝ) / 2) • p₁ + ((1 : ℝ) / 2) • p₂)).1
            = (1 - s) * p.1 + s * ((θ₁ + θ₂) / 2) := by
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hp₁θ, hp₂θ]
          ring
        have hralt : θ₁ < ((1 - s) • p + s • (((1 : ℝ) / 2) • p₁ + ((1 : ℝ) / 2) • p₂)).1 ∧
            ((1 - s) • p + s • (((1 : ℝ) / 2) • p₁ + ((1 : ℝ) / 2) • p₂)).1 < θ₂ := by
          rw [hrfst, hpθ]
          rcases hcase with he | he <;> subst he <;>
            constructor <;> nlinarith [mul_pos hs0 (sub_pos.mpr hθ)]
        rw [hψ'pow _ hr]
        simpa only [power] using hunb.2 _ ⟨hr, hralt.1, hralt.2⟩
    have hns₁ := ae_condPower_eq_of_similar hU hT hUT hΩ_convex hΩ_aff hΩ_lt₁ hΩ_gt₁ hp₁
      hp₁θ hψ'crit.1 hψ'b (hsim θ₁ (Or.inl rfl))
    have hns₂ := ae_condPower_eq_of_similar hU hT hUT hΩ_convex hΩ_aff hΩ_lt₂ hΩ_gt₂ hp₂
      hp₂θ hψ'crit.1 hψ'b (hsim θ₂ (Or.inr rfl))
    have hfin := (hcmp ψ' hψ'crit.1 hψ'crit.2 hns₁ hns₂ p' hp'Ω).2 hp'l hp'r
    simp only [power]
    rw [← hψ'pow p' hp'Ω]
    exact hfin

/-- **Interval null.** For `H : θ₁ ≤ θ ≤ θ₂` against `K : θ < θ₁ or θ > θ₂`, the conditional
test rejecting *outside* an interval in `u`, with conditional size `α` on both boundary
surfaces `θ = θ₁` and `θ = θ₂`, is UMP unbiased at level `α`. -/
theorem isUMPU_conditional_outside
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} {θ₁ θ₂ α : ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ p, IsProbabilityMeasure (P p)]
    -- LEAN-ONLY (AMENDMENT): the σ-algebra of `Ξ` is the Borel one and `Ξ` is finite
    -- dimensional; see `boundedlyComplete_boundary`
    [BorelSpace Ξ] [FiniteDimensional ℝ Ξ]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT (AMENDMENT): `(U, T)` is sufficient, in the operative sense that every
    -- critical function is matched in power by a critical function of `(U, T)`. Without it
    -- the statement is FALSE — see the counterexample section and the note in the docstring
    (hsuff : SufficiencyReducible P Ω U T)
    -- USER-INPUT: the parameter set is convex
    (hΩ_convex : Convex ℝ Ω)
    -- USER-INPUT: the parameter set is not contained in a proper linear subspace
    (hΩ_span : Submodule.span ℝ Ω = ⊤)
    -- USER-INPUT (AMENDMENT): the parameter set is not contained in a proper *affine*
    -- subspace either. This is the faithful reading of the source's "not contained in a
    -- linear space of dimension less than `k+1`", and it is strictly stronger than the
    -- frozen `hΩ_span`, which does not suffice: see `boundedlyComplete_boundary` for a
    -- convex `Ω` with full linear span whose boundary surface is a single point
    (hΩ_aff : affineSpan ℝ Ω = ⊤)
    -- USER-INPUT: the two endpoints are ordered
    (hθ : θ₁ < θ₂)
    -- USER-INPUT: the parameter set reaches below and above each endpoint
    (hΩ_lt₁ : ∃ p ∈ Ω, p.1 < θ₁) (hΩ_gt₁ : ∃ p ∈ Ω, θ₁ < p.1)
    (hΩ_lt₂ : ∃ p ∈ Ω, p.1 < θ₂) (hΩ_gt₂ : ∃ p ∈ Ω, θ₂ < p.1)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: measurable selection of the critical values and randomization
    -- probabilities
    (hC₁ : Measurable C₁) (hC₂ : Measurable C₂)
    (hγ₁ : Measurable γ₁) (hγ₂ : Measurable γ₂)
    -- USER-INPUT: the randomization probabilities are probabilities
    (hγ₁_mem : ∀ t, γ₁ t ∈ Set.Icc (0 : ℝ) 1) (hγ₂_mem : ∀ t, γ₂ t ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the critical values are ordered
    (hC : ∀ t, C₁ t ≤ C₂ t)
    -- USER-INPUT: conditional size `α` on both boundary surfaces
    (hsize : ∀ p ∈ Ω, p.1 = θ₁ ∨ p.1 = θ₂ → ∀ᵐ t ∂((P p).map T),
      ∫ u, condOutsideTest C₁ C₂ γ₁ γ₂ (u, t) ∂(condDistrib U T (P p) t) = α) :
    IsUMPU P {p ∈ Ω | θ₁ ≤ p.1 ∧ p.1 ≤ θ₂} {p ∈ Ω | p.1 < θ₁ ∨ θ₂ < p.1} α
      (fun x => condOutsideTest C₁ C₂ γ₁ γ₂ (U x, T x)) := by
  -- REPAIRED AND PROVED, over the one lifted brick `boundedlyComplete_boundary`. The frozen
  -- form was FALSE, refuted by
  -- `ConditionalUMPUCounterexample.not_isUMPU_conditional_outside_counterexample`; the
  -- amendment `hsuff : SufficiencyReducible P Ω U T` excludes that counterexample and
  -- restores the classical statement of `TSH4 §4.4 Thm 4.4.1`; in the source's own setting
  -- `𝓧 = ℝ × Ξ`, `(U, T) = (fst, snd)`, `hsuff` is vacuous
  -- (`sufficiencyReducible_prod`). Level, unbiasedness and optimality are all
  -- `integral_comp_sign_of_condZero_interval` (the fibrewise three-exponential separation),
  -- applied to `φ − α` and to `φ − ψ`; the Neyman structure of an unbiased competitor at the
  -- two boundary surfaces comes from continuity of its power along segments of `Ω`
  -- (`integral_comp_eq_of_le_of_segment`) and `ae_condPower_eq_of_similar`.
  classical
  have hφm : Measurable (condOutsideTest C₁ C₂ γ₁ γ₂) :=
    measurable_condOutsideTest hC₁ hC₂ hγ₁ hγ₂
  have hφIcc : ∀ z : ℝ × Ξ, condOutsideTest C₁ C₂ γ₁ γ₂ z ∈ Set.Icc (0 : ℝ) 1 :=
    condOutsideTest_mem_Icc hγ₁_mem hγ₂_mem
  have hφb : ∀ z : ℝ × Ξ, |condOutsideTest C₁ C₂ γ₁ γ₂ z| ≤ 1 := abs_le_one_of_mem_Icc hφIcc
  obtain ⟨p₁, hp₁, hp₁θ⟩ := exists_mem_fst_eq hΩ_convex hΩ_lt₁ hΩ_gt₁
  obtain ⟨p₂, hp₂, hp₂θ⟩ := exists_mem_fst_eq hΩ_convex hΩ_lt₂ hΩ_gt₂
  obtain ⟨qlo, hqlo, hqloθ⟩ := id hΩ_lt₁
  obtain ⟨qhi, hqhi, hqhiθ⟩ := id hΩ_gt₂
  haveI hstat : ∀ p : ℝ × Ξ, IsProbabilityMeasure ((P p).map T) := fun p =>
    isProbabilityMeasure_statLaw (P := P) hT p
  have hp₁₂ : p₁.1 < p₂.1 := by rw [hp₁θ, hp₂θ]; exact hθ
  have hsz₁ := hsize p₁ hp₁ (Or.inl hp₁θ)
  have hsz₂ := hsize p₂ hp₂ (Or.inr hp₂θ)
  -- the fibrewise comparison against an arbitrary competitor of the pair with the same
  -- conditional sizes at the two boundary surfaces
  have hcmp : ∀ w : ℝ × Ξ → ℝ, Measurable w → (∀ z, w z ∈ Set.Icc (0 : ℝ) 1) →
      (∀ᵐ t ∂((P p₁).map T), ∫ u, w (u, t) ∂(condDistrib U T (P p₁) t) = α) →
      (∀ᵐ t ∂((P p₂).map T), ∫ u, w (u, t) ∂(condDistrib U T (P p₂) t) = α) →
      ∀ p ∈ Ω, ((p.1 < θ₁ ∨ θ₂ < p.1) →
          ∫ x, w (U x, T x) ∂(P p) ≤ ∫ x, condOutsideTest C₁ C₂ γ₁ γ₂ (U x, T x) ∂(P p)) ∧
        (θ₁ < p.1 → p.1 < θ₂ →
          ∫ x, condOutsideTest C₁ C₂ γ₁ γ₂ (U x, T x) ∂(P p) ≤ ∫ x, w (U x, T x) ∂(P p)) := by
    intro w hwm hwIcc hw₁ hw₂ p hp
    have hwb : ∀ z : ℝ × Ξ, |w z| ≤ 1 := abs_le_one_of_mem_Icc hwIcc
    set g : ℝ × Ξ → ℝ := fun z => condOutsideTest C₁ C₂ γ₁ γ₂ z - w z with hgdef
    have hgm : Measurable g := hφm.sub hwm
    have hgb : ∀ z, |g z| ≤ 1 := by
      intro z
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 := (hφIcc z).1
        have h2 := (hwIcc z).2
        simp only [hgdef]; linarith
      · have h1 := (hφIcc z).2
        have h2 := (hwIcc z).1
        simp only [hgdef]; linarith
    have hgpos : ∀ z : ℝ × Ξ, z.1 < C₁ z.2 ∨ C₂ z.2 < z.1 → 0 ≤ g z := by
      intro z hz
      have h1 : condOutsideTest C₁ C₂ γ₁ γ₂ z = 1 := condOutsideTest_eq_one hz
      have h2 := (hwIcc z).2
      simp only [hgdef, h1]; linarith
    have hgneg : ∀ z : ℝ × Ξ, C₁ z.2 < z.1 → z.1 < C₂ z.2 → g z ≤ 0 := by
      intro z ha hb
      have h1 : condOutsideTest C₁ C₂ γ₁ γ₂ z = 0 := condOutsideTest_eq_zero ha hb
      have h2 := (hwIcc z).1
      simp only [hgdef, h1]; linarith
    have hzc : ∀ (r : ℝ × Ξ),
        (∀ᵐ t ∂((P r).map T),
          ∫ u, condOutsideTest C₁ C₂ γ₁ γ₂ (u, t) ∂(condDistrib U T (P r) t) = α) →
        (∀ᵐ t ∂((P r).map T), ∫ u, w (u, t) ∂(condDistrib U T (P r) t) = α) →
        ∀ᵐ t ∂((P r).map T), ∫ u, g (u, t) ∂(condDistrib U T (P r) t) = 0 := by
      intro r ha hb
      filter_upwards [ha, hb] with t hta htb
      haveI : IsProbabilityMeasure (condDistrib U T (P r) t) := inferInstance
      rw [hgdef, integral_sub (integrable_cond_slice (P r) hU hT hφm hφb t)
        (integrable_cond_slice (P r) hU hT hwm hwb t), hta, htb, sub_self]
    have hsplit : ∫ x, g (U x, T x) ∂(P p)
        = (∫ x, condOutsideTest C₁ C₂ γ₁ γ₂ (U x, T x) ∂(P p))
          - ∫ x, w (U x, T x) ∂(P p) := by
      rw [hgdef]
      exact integral_sub (integrable_comp_UT hU hT hφm hφb p)
        (integrable_comp_UT hU hT hwm hwb p)
    have h := integral_comp_sign_of_condZero_interval hU hT hUT hp₁ hp₂ hp hp₁₂ hC hgm hgb
      hgpos hgneg (hzc p₁ hsz₁ hw₁) (hzc p₂ hsz₂ hw₂)
    rw [hsplit] at h
    refine ⟨fun hside => ?_, fun ha hb => ?_⟩
    · have := h.1 (by rcases hside with hs | hs
                      · exact Or.inl (by rw [hp₁θ]; exact hs)
                      · exact Or.inr (by rw [hp₂θ]; exact hs))
      linarith
    · have := h.2 (by rw [hp₁θ]; exact ha) (by rw [hp₂θ]; exact hb)
      linarith
  -- the constant test `α` has the right conditional sizes
  have hconstsize : ∀ r : ℝ × Ξ,
      ∀ᵐ t ∂((P r).map T), ∫ _u, (α : ℝ) ∂(condDistrib U T (P r) t) = α := by
    intro r
    refine Filter.Eventually.of_forall fun t => ?_
    haveI : IsProbabilityMeasure (condDistrib U T (P r) t) := inferInstance
    simp
  have hconstIcc : ∀ _z : ℝ × Ξ, (α : ℝ) ∈ Set.Icc (0 : ℝ) 1 := fun _ => ⟨hα₀.le, hα₁.le⟩
  have hconst := hcmp (fun _ => α) measurable_const hconstIcc (hconstsize p₁) (hconstsize p₂)
  have hpowconst : ∀ p : ℝ × Ξ, ∫ _x, (α : ℝ) ∂(P p) = α := fun p => by simp
  -- the power at the two boundary surfaces is exactly `α`
  have hbdry : ∀ p ∈ Ω, (p.1 = θ₁ ∨ p.1 = θ₂) →
      ∫ x, condOutsideTest C₁ C₂ γ₁ γ₂ (U x, T x) ∂(P p) = α := by
    intro p hp hpθ
    rw [integral_comp_eq_integral_condPower hU hT hφm hφb p,
      integral_congr_ae (hsize p hp hpθ)]
    simp
  refine ⟨⟨hφm.comp (hU.prodMk hT), fun x => hφIcc _⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro p ⟨hpΩ, hl, hr⟩
    simp only [power]
    rcases eq_or_lt_of_le hl with h | h
    · exact le_of_eq (hbdry p hpΩ (Or.inl h.symm))
    rcases eq_or_lt_of_le hr with h2 | h2
    · exact le_of_eq (hbdry p hpΩ (Or.inr h2))
    have := (hconst p hpΩ).2 h h2
    rw [hpowconst p] at this
    exact this
  · rintro p ⟨hpΩ, hside⟩
    simp only [power]
    have := (hconst p hpΩ).1 hside
    rw [hpowconst p] at this
    exact this
  · rintro ψ hψ hunb p' ⟨hp'Ω, hp'side⟩
    obtain ⟨ψ', hψ'crit, hψ'pow⟩ := hsuff ψ hψ
    have hψ'b : ∀ z : ℝ × Ξ, |ψ' z| ≤ 1 := abs_le_one_of_mem_Icc hψ'crit.2
    -- similarity of `ψ'` on each of the two boundary surfaces
    have hsim : ∀ (θ q : _), q ∈ Ω → (θ = θ₁ ∧ q.1 < θ₁ ∨ θ = θ₂ ∧ θ₂ < q.1) →
        ∀ p ∈ Ω, p.1 = θ → ∫ x, ψ' (U x, T x) ∂(P p) = α := by
      rintro θ q hq hcase p hp hpθ
      refine integral_comp_eq_of_le_of_segment hU hT hUT hΩ_convex hp hq
        hψ'crit.1 hψ'b ?_ ?_
      · rw [hψ'pow p hp]
        have hnull : p ∈ {p ∈ Ω | θ₁ ≤ p.1 ∧ p.1 ≤ θ₂} := by
          refine ⟨hp, ?_, ?_⟩ <;> rcases hcase with ⟨hθe, -⟩ | ⟨hθe, -⟩ <;>
            rw [hpθ, hθe] <;> linarith
        simpa only [power] using hunb.1 p hnull
      · intro s hs0 hs1
        have hr : (1 - s) • p + s • q ∈ Ω :=
          hΩ_convex hp hq (by linarith) hs0.le (by ring)
        have hrfst : ((1 - s) • p + s • q).1 = (1 - s) * p.1 + s * q.1 := by
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        have hralt : ((1 - s) • p + s • q).1 < θ₁ ∨ θ₂ < ((1 - s) • p + s • q).1 := by
          rcases hcase with ⟨hθe, hqθ⟩ | ⟨hθe, hqθ⟩
          · refine Or.inl ?_
            rw [hrfst, hpθ, hθe]
            nlinarith [mul_pos hs0 (sub_pos.mpr hqθ)]
          · refine Or.inr ?_
            rw [hrfst, hpθ, hθe]
            nlinarith [mul_pos hs0 (sub_pos.mpr hqθ)]
        rw [hψ'pow _ hr]
        simpa only [power] using hunb.2 _ ⟨hr, hralt⟩
    have hns₁ := ae_condPower_eq_of_similar hU hT hUT hΩ_convex hΩ_aff hΩ_lt₁ hΩ_gt₁ hp₁
      hp₁θ hψ'crit.1 hψ'b (hsim θ₁ qlo hqlo (Or.inl ⟨rfl, hqloθ⟩))
    have hns₂ := ae_condPower_eq_of_similar hU hT hUT hΩ_convex hΩ_aff hΩ_lt₂ hΩ_gt₂ hp₂
      hp₂θ hψ'crit.1 hψ'b (hsim θ₂ qhi hqhi (Or.inr ⟨rfl, hqhiθ⟩))
    have hfin := (hcmp ψ' hψ'crit.1 hψ'crit.2 hns₁ hns₂ p' hp'Ω).1 hp'side
    simp only [power]
    rw [← hψ'pow p' hp'Ω]
    exact hfin

/-! ### Bricks for the point null

The point-null optimality argument needs, beyond the interval machinery above, a separation
by an *affine* function (rather than by a three-exponential combination) and an exponential
majorant for `|u|`. Both are proved here; what is still missing is recorded at
`isUMPU_conditional_point`. -/

/-- Three-point convexity of `u ↦ exp (c u)`, in cleared-denominator form. -/
private lemma exp_three_point (c : ℝ) {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    (z - x) * Real.exp (c * y)
      ≤ (z - y) * Real.exp (c * x) + (y - x) * Real.exp (c * z) := by
  have hzx : 0 < z - x := by linarith
  have hzxne : z - x ≠ 0 := ne_of_gt hzx
  set a : ℝ := (z - y) / (z - x) with ha
  set b : ℝ := (y - x) / (z - x) with hb
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hzx.le
  have hb0 : 0 ≤ b := div_nonneg (by linarith) hzx.le
  have hab : a + b = 1 := by
    rw [ha, hb]; field_simp; ring
  have hmid : a * (c * x) + b * (c * z) = c * y := by
    rw [ha, hb]; field_simp; ring
  have hconv := convexOn_exp.2 (Set.mem_univ (c * x)) (Set.mem_univ (c * z)) ha0 hb0 hab
  simp only [smul_eq_mul] at hconv
  rw [hmid] at hconv
  have h := mul_le_mul_of_nonneg_left hconv hzx.le
  have hae : (z - x) * a = z - y := by rw [ha]; field_simp
  have hbe : (z - x) * b = y - x := by rw [hb]; field_simp
  have hrw : (z - x) * (a * Real.exp (c * x) + b * Real.exp (c * z))
      = (z - y) * Real.exp (c * x) + (y - x) * Real.exp (c * z) := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, hae, hbe]
  linarith [h, hrw.le, hrw.ge]

/-- **Secant separation.** For `C₁ < C₂` there is an affine function `A + B u` which meets
`exp (c u)` at `C₁` and at `C₂`, lies above it inside the interval and below it outside.

This is the separation the *point* null needs, and it is the exact analogue of the
three-exponential separations `exists_sep_exp3_gt` / `exists_sep_exp3_lt` used for the
interval nulls: with `g = φ − ψ` — the difference of the outside-interval test and a
competitor — one gets `g(u)·(exp (c u) − A − B u) ≥ 0` for every `u`, because `g ≥ 0`
outside `[C₁, C₂]` and `g ≤ 0` inside, and the two side conditions of the point null
(`∫ g dκ = 0` and `∫ u g(u) dκ = 0`) annihilate the two affine terms `A` and `B u`.

The two endpoint equalities are what makes the interval closed on both sides: they let the
boundary atoms be assigned to either side without changing the integral. -/
private lemma exists_sep_line (c : ℝ) {C₁ C₂ : ℝ} (hC : C₁ < C₂) :
    ∃ A B : ℝ,
      Real.exp (c * C₁) - A - B * C₁ = 0 ∧ Real.exp (c * C₂) - A - B * C₂ = 0 ∧
      (∀ u : ℝ, C₁ < u → u < C₂ → Real.exp (c * u) - A - B * u ≤ 0) ∧
      (∀ u : ℝ, u < C₁ ∨ C₂ < u → 0 ≤ Real.exp (c * u) - A - B * u) := by
  set E₁ : ℝ := Real.exp (c * C₁) with hE₁
  set E₂ : ℝ := Real.exp (c * C₂) with hE₂
  have hd : (0 : ℝ) < C₂ - C₁ := by linarith
  set B : ℝ := (E₂ - E₁) / (C₂ - C₁) with hB
  set A : ℝ := E₁ - B * C₁ with hA
  have hBd : B * (C₂ - C₁) = E₂ - E₁ := by
    rw [hB]; field_simp
  refine ⟨A, B, by rw [hA]; ring, ?_, ?_, ?_⟩
  · rw [hA]; linear_combination -hBd
  · intro u h1 h2
    have h3 := exp_three_point c h1 h2
    have hzero : (C₂ - u) * E₁ + (u - C₁) * E₂ - (C₂ - C₁) * (A + B * u) = 0 := by
      rw [hA]; linear_combination (C₁ - u) * hBd
    nlinarith [h3, hzero, hd]
  · intro u hu
    rcases hu with h | h
    · have h3 := exp_three_point c h hC
      have hzero : (C₂ - u) * E₁ + (u - C₁) * E₂ - (C₂ - C₁) * (A + B * u) = 0 := by
        rw [hA]; linear_combination (C₁ - u) * hBd
      nlinarith [h3, hzero, hd]
    · have h3 := exp_three_point c hC h
      have hzero : (C₂ - u) * E₁ + (u - C₁) * E₂ - (C₂ - C₁) * (A + B * u) = 0 := by
        rw [hA]; linear_combination (C₁ - u) * hBd
      nlinarith [h3, hzero, hd]

/-- **Two-point exponential majorant for `|u|`.** For every `δ > 0`,
`|u| ≤ δ⁻¹ (e^{δu} + e^{−δu})`.

This is what makes `u` conditionally integrable under every member of a canonical family
that reaches strictly below and strictly above a given parameter: the two tilts by `±δ` are
probability measures, so their densities are integrable, and the majorant transfers that to
`|u|`. It is the missing integrability input of item (c) at
`isUMPU_conditional_point`. -/
private lemma abs_le_exp_add_exp_neg {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    |u| ≤ (Real.exp (δ * u) + Real.exp (-(δ * u))) / δ := by
  have hpos : (0 : ℝ) < Real.exp (δ * u) := Real.exp_pos _
  have hneg : (0 : ℝ) < Real.exp (-(δ * u)) := Real.exp_pos _
  have habs : |δ * u| ≤ Real.exp |δ * u| := by
    have := Real.add_one_le_exp |δ * u|
    linarith
  have hcase : Real.exp |δ * u| ≤ Real.exp (δ * u) + Real.exp (-(δ * u)) := by
    rcases abs_cases (δ * u) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; linarith
    · rw [h]; linarith
  have hdu : |δ * u| = δ * |u| := by
    rw [abs_mul, abs_of_pos hδ]
  rw [le_div_iff₀ hδ, mul_comm]
  calc δ * |u| = |δ * u| := hdu.symm
    _ ≤ Real.exp |δ * u| := habs
    _ ≤ Real.exp (δ * u) + Real.exp (-(δ * u)) := hcase

/-- **Differentiation of the canonical `ν`-integral in the natural parameter `θ`.** For a
bounded measurable `g` and a nuisance coordinate `ϑ₀` at which the pure-`θ` segment
`(θ₀ ± η, ϑ₀)` lies in `Ω`,

`d/dθ ∫ g(z) e^{θ z₁ + ⟪ϑ₀, z₂⟫} dν(z) ∣_{θ₀} = ∫ g(z) z₁ e^{θ₀ z₁ + ⟪ϑ₀, z₂⟫} dν(z)`,

and the right-hand integrand is `ν`-integrable.

This is the analytic half of item (b) at `isUMPU_conditional_point`. It is stated at the
level of the base measure `ν` rather than of the power, because that is what makes it usable
*twice* — at the competitor `ψ` and at `g ≡ 1` — which is what eliminates the normalizer: the
power is `C(θ,ϑ₀)·∫ψ e^{canExp}` and only the *product* is pinned down by `IsCanonicalUT`, but
`C(θ,ϑ₀)·∫1·e^{canExp} = 1` (`integrable_canExp`), so the power is the ratio
`(∫ψ e^{canExp})/(∫ e^{canExp})` of two functions this lemma differentiates, and the quotient
rule finishes without ever differentiating `C` directly.

**The dominating function.** For `|θ − θ₀| ≤ η/2` the derivative integrand is majorised,
independently of `θ`, by a fixed combination of three *members of the family*:

`|g z · z₁ · e^{θ z₁ + c}| ≤ (2/η)·(e^{(θ₀+η)z₁+c} + 2e^{θ₀z₁+c} + e^{(θ₀−η)z₁+c})`.

Two factors of the two-point majorant `abs_le_exp_add_exp_neg` at half-width `η/2` produce
it: one absorbs `|z₁|`, the other absorbs the drift `e^{(θ−θ₀)z₁}`, and their product
telescopes because `e^{(η/2)z₁}·e^{−(η/2)z₁} = 1`. Each of the three terms is `ν`-integrable
by `integrable_canExp`, precisely because `(θ₀ ± η, ϑ₀)` and `(θ₀, ϑ₀)` are all in `Ω` — which
is what `exists_twoSided_boundary_pair` (via `exists_interior_boundary_point`) supplies. -/
private lemma hasDerivAt_integral_canExp {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)}
    {U : 𝓧 → ℝ} {T : 𝓧 → Ξ} {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ}
    [OpensMeasurableSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {θ₀ : ℝ} {ϑ₀ : Ξ} {η : ℝ} (hη : 0 < η)
    (h0 : ((θ₀, ϑ₀) : ℝ × Ξ) ∈ Ω)
    (hlo : ((θ₀ - η, ϑ₀) : ℝ × Ξ) ∈ Ω) (hhi : ((θ₀ + η, ϑ₀) : ℝ × Ξ) ∈ Ω)
    {g : ℝ × Ξ → ℝ} (hg : Measurable g) (hgb : ∀ z, |g z| ≤ 1) :
    Integrable (fun z : ℝ × Ξ => g z * z.1 * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z)) ν ∧
      HasDerivAt (fun θ : ℝ => ∫ z, g z * Real.exp (canExp ((θ, ϑ₀) : ℝ × Ξ) z) ∂ν)
        (∫ z, g z * z.1 * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) ∂ν) θ₀ := by
  classical
  have hhalf : (0 : ℝ) < η / 2 := by linarith
  -- measurability of the two integrand families
  have hmexp : ∀ θ : ℝ, Measurable fun z : ℝ × Ξ =>
      Real.exp (canExp ((θ, ϑ₀) : ℝ × Ξ) z) := fun θ => (measurable_canExp _).exp
  have hFm : ∀ θ : ℝ, Measurable fun z : ℝ × Ξ =>
      g z * Real.exp (canExp ((θ, ϑ₀) : ℝ × Ξ) z) := fun θ => hg.mul (hmexp θ)
  have hF'm : Measurable fun z : ℝ × Ξ =>
      g z * z.1 * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) :=
    (hg.mul measurable_fst).mul (hmexp θ₀)
  -- the three family members that make up the dominating function
  have hI0 := (integrable_canExp hU hT hUT h0).1
  have hIlo := (integrable_canExp hU hT hUT hlo).1
  have hIhi := (integrable_canExp hU hT hUT hhi).1
  set bound : ℝ × Ξ → ℝ := fun z => (2 / η) *
    (Real.exp (canExp ((θ₀ + η, ϑ₀) : ℝ × Ξ) z)
      + 2 * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z)
      + Real.exp (canExp ((θ₀ - η, ϑ₀) : ℝ × Ξ) z)) with hbound_def
  have hbound_int : Integrable bound ν := by
    rw [hbound_def]
    exact ((hIhi.add (hI0.const_mul 2)).add hIlo).const_mul _
  -- the uniform majorant
  have hmaj : ∀ z : ℝ × Ξ, ∀ θ ∈ Metric.ball θ₀ (η / 2),
      ‖g z * z.1 * Real.exp (canExp ((θ, ϑ₀) : ℝ × Ξ) z)‖ ≤ bound z := by
    intro z θ hθ
    have hθ' : |θ - θ₀| < η / 2 := by
      rwa [Metric.mem_ball, Real.dist_eq] at hθ
    set u : ℝ := z.1 with hu
    set c : ℝ := ⟪ϑ₀, z.2⟫_ℝ with hc
    have hcan : ∀ t : ℝ, canExp ((t, ϑ₀) : ℝ × Ξ) z = t * u + c := fun t => rfl
    set A : ℝ := Real.exp (η / 2 * u) with hA
    set B : ℝ := Real.exp (-(η / 2 * u)) with hB
    have hApos : 0 < A := Real.exp_pos _
    have hBpos : 0 < B := Real.exp_pos _
    have hAB : A * B = 1 := by
      rw [hA, hB, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    -- `|u| ≤ (2/η)(A + B)`
    have habs : |u| ≤ 2 / η * (A + B) := by
      have hthis := abs_le_exp_add_exp_neg hhalf u
      rw [le_div_iff₀ hhalf, ← hA, ← hB] at hthis
      rw [div_mul_eq_mul_div, le_div_iff₀ hη]
      linarith
    -- the drift factor `e^{(θ−θ₀)u} ≤ A + B`
    have hdrift : Real.exp ((θ - θ₀) * u) ≤ A + B := by
      have hle : (θ - θ₀) * u ≤ max (η / 2 * u) (-(η / 2 * u)) := by
        rcases le_total 0 u with hu0 | hu0
        · refine le_trans ?_ (le_max_left _ _)
          have : θ - θ₀ ≤ η / 2 := le_of_lt (lt_of_abs_lt hθ')
          nlinarith
        · refine le_trans ?_ (le_max_right _ _)
          have : -(η / 2) ≤ θ - θ₀ := by
            have := neg_lt_of_abs_lt hθ'
            linarith
          nlinarith
      calc Real.exp ((θ - θ₀) * u) ≤ Real.exp (max (η / 2 * u) (-(η / 2 * u))) :=
            Real.exp_le_exp.2 hle
        _ ≤ A + B := by
            rcases max_cases (η / 2 * u) (-(η / 2 * u)) with ⟨hm, -⟩ | ⟨hm, -⟩
            · rw [hm, ← hA]; linarith
            · rw [hm, ← hB]; linarith
    -- split off the base exponential and assemble
    have hsplit : Real.exp (canExp ((θ, ϑ₀) : ℝ × Ξ) z)
        = Real.exp ((θ - θ₀) * u) * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) := by
      rw [hcan, hcan, ← Real.exp_add]
      congr 1
      ring
    have hE0 : 0 < Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) := Real.exp_pos _
    have hstep : ‖g z * u * Real.exp (canExp ((θ, ϑ₀) : ℝ × Ξ) z)‖
        ≤ (2 / η * (A + B)) * ((A + B) * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), hsplit]
      have h1 : |g z| * |u| ≤ 1 * (2 / η * (A + B)) :=
        mul_le_mul (hgb z) habs (abs_nonneg _) zero_le_one
      have h2 : Real.exp ((θ - θ₀) * u) * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z)
          ≤ (A + B) * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) :=
        mul_le_mul_of_nonneg_right hdrift hE0.le
      have h3 : (0 : ℝ) ≤ Real.exp ((θ - θ₀) * u)
          * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) := by positivity
      calc |g z| * |u| * (Real.exp ((θ - θ₀) * u)
            * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z))
          ≤ (2 / η * (A + B)) * (Real.exp ((θ - θ₀) * u)
              * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z)) := by
            refine mul_le_mul_of_nonneg_right ?_ h3
            simpa using h1
        _ ≤ (2 / η * (A + B)) * ((A + B)
              * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z)) := by
            refine mul_le_mul_of_nonneg_left h2 ?_
            positivity
    refine hstep.trans (le_of_eq ?_)
    -- `(A+B)² = e^{ηu} + 2 + e^{−ηu}` because `A·B = 1`
    have hA2 : A * A = Real.exp (canExp ((θ₀ + η, ϑ₀) : ℝ × Ξ) z)
        / Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) := by
      rw [hA, ← Real.exp_add, hcan, hcan, ← Real.exp_sub]
      congr 1
      ring
    have hB2 : B * B = Real.exp (canExp ((θ₀ - η, ϑ₀) : ℝ × Ξ) z)
        / Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) := by
      rw [hB, ← Real.exp_add, hcan, hcan, ← Real.exp_sub]
      congr 1
      ring
    rw [hbound_def]
    field_simp [hA2, hB2] at *
    nlinarith [hAB, hE0, hA2, hB2]
  -- pointwise differentiability in `θ`
  have hdiff : ∀ z : ℝ × Ξ, ∀ θ ∈ Metric.ball θ₀ (η / 2),
      HasDerivAt (fun t : ℝ => g z * Real.exp (canExp ((t, ϑ₀) : ℝ × Ξ) z))
        (g z * z.1 * Real.exp (canExp ((θ, ϑ₀) : ℝ × Ξ) z)) θ := by
    intro z θ _
    have hlin : HasDerivAt (fun t : ℝ => canExp ((t, ϑ₀) : ℝ × Ξ) z) z.1 θ := by
      simp only [canExp_apply]
      simpa using ((hasDerivAt_id θ).mul_const z.1).add_const (⟪ϑ₀, z.2⟫_ℝ)
    have h2 := hlin.exp.const_mul (g z)
    have heq : g z * z.1 * Real.exp (canExp ((θ, ϑ₀) : ℝ × Ξ) z)
        = g z * (Real.exp (canExp ((θ, ϑ₀) : ℝ × Ξ) z) * z.1) := by ring
    rw [heq]
    exact h2
  -- the base integral exists
  have hF_int : Integrable (fun z : ℝ × Ξ =>
      g z * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z)) ν := by
    refine Integrable.mono' hI0 (hFm θ₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have := hgb z
    nlinarith [Real.exp_pos (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z)]
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds θ₀ hhalf)
    (Filter.Eventually.of_forall fun θ => (hFm θ).aestronglyMeasurable) hF_int
    hF'm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hmaj z) hbound_int
    (Filter.Eventually.of_forall fun z => hdiff z)

/-- **`U` is integrable at a parameter with a pure-`θ` window.** If `(θ₀ ± δ, ϑ₀) ∈ Ω` then
`U` is `P (θ₀, ϑ₀)`-integrable.

The full-measure twin of `exists_boundary_ae_integrable_id`, and by the same two-point
majorant `abs_le_exp_add_exp_neg` — but here the two tilted exponentials are integrable for a
reason available only since `integrable_comp_UT_iff`: taking `g z := e^{±δ z₁}` in that
equivalence turns `e^{±δ z₁}·e^{canExp (θ₀,ϑ₀) z}` into `e^{canExp (θ₀ ± δ, ϑ₀) z}`, which is
`ν`-integrable by `integrable_canExp` precisely because the shifted parameters are in `Ω`.

This is what the disintegration `∫ E[g ∣ T] d((P p).map T) = E[g]` needs at item (d) of
`isUMPU_conditional_point`; the integrability of `U·ψ` for a critical `ψ` follows from it by
`|U·ψ| ≤ |U|`. -/
private lemma integrable_U_of_twoSided {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)}
    {U : 𝓧 → ℝ} {T : 𝓧 → Ξ} {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ}
    [OpensMeasurableSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {θ₀ : ℝ} {ϑ₀ : Ξ} {δ : ℝ} (hδ : 0 < δ)
    (hlo : ((θ₀ - δ, ϑ₀) : ℝ × Ξ) ∈ Ω) (hhi : ((θ₀ + δ, ϑ₀) : ℝ × Ξ) ∈ Ω)
    (h0 : ((θ₀, ϑ₀) : ℝ × Ξ) ∈ Ω) :
    Integrable U (P ((θ₀, ϑ₀) : ℝ × Ξ)) := by
  have htilt : ∀ (c : ℝ), ((θ₀ + c, ϑ₀) : ℝ × Ξ) ∈ Ω →
      Integrable (fun x => Real.exp (c * U x)) (P ((θ₀, ϑ₀) : ℝ × Ξ)) := by
    intro c hc
    refine (integrable_comp_UT_iff hU hT hUT h0 (g := fun z : ℝ × Ξ => Real.exp (c * z.1))
      (measurable_const.mul measurable_fst).exp).2 ?_
    refine ((integrable_canExp hU hT hUT hc).1).congr
      (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [← Real.exp_add]
    congr 1
    simp only [canExp_apply]
    ring
  have hplus := htilt δ hhi
  have hminus : Integrable (fun x => Real.exp (-δ * U x)) (P ((θ₀, ϑ₀) : ℝ × Ξ)) := by
    have h := htilt (-δ) (by simpa [sub_eq_add_neg] using hlo)
    simpa using h
  refine Integrable.mono' ((hplus.add hminus).const_mul δ⁻¹) hU.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hmaj := abs_le_exp_add_exp_neg hδ (U x)
  rw [div_eq_inv_mul, ← neg_mul] at hmaj
  simpa [Real.norm_eq_abs] using hmaj

/-- **The derivative side condition, at the level of the full measure.** If a bounded
measurable test `ψ` of `(U, T)` has power exactly `α` at the boundary parameter `(θ₀, ϑ₀)` and
power at least `α` all along the pure-`θ` segment `(θ₀ ± η, ϑ₀) ⊆ Ω`, then

`E_{(θ₀,ϑ₀)}[U·ψ] = α · E_{(θ₀,ϑ₀)}[U]`.

This is item (b) of `isUMPU_conditional_point` in full: it is the analytic content of
unbiasedness, namely that the power function of the conditional problem has a *minimum* at
`θ₀` and therefore a vanishing derivative there.

**Why no normalizer has to be differentiated.** `integrable_canExp` gives
`C(θ,ϑ₀)·∫e^{canExp (θ,ϑ₀)} dν = 1`, so along the segment the power is the ratio
`N(θ)/D(θ)` with `N(θ) = ∫ψ e^{canExp (θ,ϑ₀)} dν` and `D(θ) = ∫e^{canExp (θ,ϑ₀)} dν` — both
differentiated by `hasDerivAt_integral_canExp` (at `g := ψ` and at `g := 1`), and `C` never
appears. `HasDerivAt.div` plus `IsLocalMin.hasDerivAt_eq_zero` give `N'(θ₀)D(θ₀) =
N(θ₀)D'(θ₀)`, and `integral_comp_UT_eq` reads `C·N'(θ₀) = E[Uψ]`, `C·D'(θ₀) = E[U]`,
`N(θ₀)/D(θ₀) = α` off it. -/
private lemma integral_U_mul_eq_of_boundary_min {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)}
    {U : 𝓧 → ℝ} {T : 𝓧 → Ξ} {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ}
    [OpensMeasurableSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    (hΩ_convex : Convex ℝ Ω)
    {θ₀ α : ℝ} {ϑ₀ : Ξ} {η : ℝ} (hη : 0 < η)
    (h0 : ((θ₀, ϑ₀) : ℝ × Ξ) ∈ Ω)
    (hlo : ((θ₀ - η, ϑ₀) : ℝ × Ξ) ∈ Ω) (hhi : ((θ₀ + η, ϑ₀) : ℝ × Ξ) ∈ Ω)
    {ψ : ℝ × Ξ → ℝ} (hψm : Measurable ψ) (hψb : ∀ z, |ψ z| ≤ 1)
    (hval : ∫ x, ψ (U x, T x) ∂(P ((θ₀, ϑ₀) : ℝ × Ξ)) = α)
    (hmin : ∀ θ : ℝ, |θ - θ₀| ≤ η → α ≤ ∫ x, ψ (U x, T x) ∂(P ((θ, ϑ₀) : ℝ × Ξ))) :
    ∫ x, U x * ψ (U x, T x) ∂(P ((θ₀, ϑ₀) : ℝ × Ξ))
      = α * ∫ x, U x ∂(P ((θ₀, ϑ₀) : ℝ × Ξ)) := by
  classical
  have hηne : η ≠ 0 := ne_of_gt hη
  -- the whole pure-`θ` window lies in `Ω`, by convexity between the two endpoints
  have hseg : ∀ θ : ℝ, |θ - θ₀| ≤ η → ((θ, ϑ₀) : ℝ × Ξ) ∈ Ω := by
    intro θ hθ
    obtain ⟨hθ1, hθ2⟩ := abs_le.1 hθ
    have h2η : (0 : ℝ) < 2 * η := by linarith
    have hb0 : (0 : ℝ) ≤ (θ - (θ₀ - η)) / (2 * η) := div_nonneg (by linarith) h2η.le
    have ha0 : (0 : ℝ) ≤ 1 - (θ - (θ₀ - η)) / (2 * η) := by
      rw [sub_nonneg, div_le_one h2η]; linarith
    have hmem := hΩ_convex hlo hhi ha0 hb0 (by ring)
    have hpt : (1 - (θ - (θ₀ - η)) / (2 * η)) • ((θ₀ - η, ϑ₀) : ℝ × Ξ)
        + ((θ - (θ₀ - η)) / (2 * η)) • ((θ₀ + η, ϑ₀) : ℝ × Ξ) = ((θ, ϑ₀) : ℝ × Ξ) := by
      have hsum : (1 - (θ - (θ₀ - η)) / (2 * η)) + (θ - (θ₀ - η)) / (2 * η) = 1 := by ring
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        field_simp
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, ← add_smul, hsum, one_smul]
    rwa [hpt] at hmem
  -- numerator and denominator of the power along the segment
  set N : ℝ → ℝ := fun θ => ∫ z, ψ z * Real.exp (canExp ((θ, ϑ₀) : ℝ × Ξ) z) ∂ν with hN
  set D : ℝ → ℝ := fun θ => ∫ z, Real.exp (canExp ((θ, ϑ₀) : ℝ × Ξ) z) ∂ν with hD
  have hCD : ∀ θ : ℝ, ((θ, ϑ₀) : ℝ × Ξ) ∈ Ω → C ((θ, ϑ₀) : ℝ × Ξ) * D θ = 1 := fun θ hθ =>
    (integrable_canExp hU hT hUT hθ).2
  have hDpos : ∀ θ : ℝ, ((θ, ϑ₀) : ℝ × Ξ) ∈ Ω → 0 < D θ := by
    intro θ hθ
    have hC := canonicalUT_const_pos hU hT hUT hθ
    have h1 := hCD θ hθ
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hpow : ∀ θ : ℝ, ((θ, ϑ₀) : ℝ × Ξ) ∈ Ω →
      ∫ x, ψ (U x, T x) ∂(P ((θ, ϑ₀) : ℝ × Ξ)) = N θ / D θ := by
    intro θ hθ
    rw [integral_comp_UT_eq hU hT hUT hθ hψm, eq_div_iff (hDpos θ hθ).ne']
    linear_combination N θ * hCD θ hθ
  -- differentiate numerator and denominator
  have hdN : HasDerivAt N
      (∫ z, ψ z * z.1 * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) ∂ν) θ₀ := by
    have h := (hasDerivAt_integral_canExp hU hT hUT hη h0 hlo hhi hψm hψb).2
    rw [hN]
    exact h
  have hdD : HasDerivAt D (∫ z, z.1 * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) ∂ν) θ₀ := by
    have h := (hasDerivAt_integral_canExp hU hT hUT hη h0 hlo hhi
      (g := fun _ : ℝ × Ξ => (1 : ℝ)) measurable_const (fun _ => by norm_num)).2
    simp only [one_mul] at h
    rw [hD]
    exact h
  have hDne : D θ₀ ≠ 0 := (hDpos θ₀ h0).ne'
  have hdiv := hdN.div hdD hDne
  -- unbiasedness ⟹ the ratio has a local minimum at `θ₀`
  have hlocmin : IsLocalMin (fun θ => N θ / D θ) θ₀ := by
    filter_upwards [Metric.ball_mem_nhds θ₀ hη] with θ hθ
    have hθ' : |θ - θ₀| ≤ η := by
      rw [Metric.mem_ball, Real.dist_eq] at hθ
      exact hθ.le
    have hmem := hseg θ hθ'
    show N θ₀ / D θ₀ ≤ N θ / D θ
    rw [← hpow θ hmem, ← hpow θ₀ h0, hval]
    exact hmin θ hθ'
  have hzero := hlocmin.hasDerivAt_eq_zero hdiv
  have hnum := (div_eq_zero_iff.1 hzero).resolve_right (pow_ne_zero 2 hDne)
  -- read the two `ν`-integrals back as expectations
  have hUψ : ∫ x, U x * ψ (U x, T x) ∂(P ((θ₀, ϑ₀) : ℝ × Ξ))
      = C ((θ₀, ϑ₀) : ℝ × Ξ)
        * ∫ z, ψ z * z.1 * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) ∂ν := by
    rw [integral_comp_UT_eq hU hT hUT h0 (g := fun z : ℝ × Ξ => z.1 * ψ z)
      (measurable_fst.mul hψm)]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  have hUonly : ∫ x, U x ∂(P ((θ₀, ϑ₀) : ℝ × Ξ))
      = C ((θ₀, ϑ₀) : ℝ × Ξ)
        * ∫ z, z.1 * Real.exp (canExp ((θ₀, ϑ₀) : ℝ × Ξ) z) ∂ν :=
    integral_comp_UT_eq hU hT hUT h0 (g := fun z : ℝ × Ξ => z.1) measurable_fst
  have hαval : α = N θ₀ / D θ₀ := by rw [← hpow θ₀ h0, hval]
  rw [hUψ, hUonly, hαval, div_mul_eq_mul_div, eq_div_iff hDne]
  linear_combination C ((θ₀, ϑ₀) : ℝ × Ξ) * hnum

/-- **Two-point envelope for the derivative along a canonical segment.** For the affine
exponent `L(s) = (1−s)a + sb` and a half-width `η > 0`,
`|b − a|·e^{L(s)} ≤ η⁻¹(e^{L(s−η)} + e^{L(s+η)})`.

The left-hand side is `|d/ds e^{L(s)}|`, and the two exponentials on the right are the
values of the *same* exponent at the two shifted segment parameters — that is, densities of
two members of the canonical family. So this is the dominating function that differentiation
under the integral sign needs at item (b) of `isUMPU_conditional_point`: on
`[s₀ − η, s₀ + η]` the `s`-derivative of the integrand is dominated by a fixed integrable
function, uniformly in `s`. It is the exact analogue, one derivative up, of
`exp_segment_le`, and it rests on the same two-point majorant `abs_le_exp_add_exp_neg` that
supplies the conditional integrability of `U` in item (c). -/
private lemma abs_sub_mul_exp_segment_le (a b s : ℝ) {η : ℝ} (hη : 0 < η) :
    |b - a| * Real.exp ((1 - s) * a + s * b)
      ≤ η⁻¹ * (Real.exp ((1 - (s - η)) * a + (s - η) * b)
        + Real.exp ((1 - (s + η)) * a + (s + η) * b)) := by
  have e1 : (1 - (s - η)) * a + (s - η) * b = ((1 - s) * a + s * b) + -(η * (b - a)) := by
    ring
  have e2 : (1 - (s + η)) * a + (s + η) * b = ((1 - s) * a + s * b) + η * (b - a) := by ring
  rw [e1, e2]
  have hLpos : 0 < Real.exp ((1 - s) * a + s * b) := Real.exp_pos _
  have h1 : |b - a| ≤ (Real.exp (η * (b - a)) + Real.exp (-(η * (b - a)))) / η :=
    abs_le_exp_add_exp_neg hη (b - a)
  have h2 := mul_le_mul_of_nonneg_right h1 hLpos.le
  refine h2.trans (le_of_eq ?_)
  rw [Real.exp_add ((1 - s) * a + s * b) (-(η * (b - a))),
    Real.exp_add ((1 - s) * a + s * b) (η * (b - a))]
  field_simp
  ring

/-- **A two-sided pair of boundary parameters on a common nuisance coordinate.** Under the
amendments `hΩ_aff` and `[FiniteDimensional ℝ Ξ]` the surface `θ = θ₀` meets the *interior*
of `Ω` (`exists_interior_boundary_point`), so a whole ball around such a point lies in `Ω`.
In particular there is a `δ > 0` for which all three of `(θ₀, ϑ₀)`, `(θ₀ − δ, ϑ₀)` and
`(θ₀ + δ, ϑ₀)` are in `Ω`, with the **same** nuisance coordinate `ϑ₀`.

This is exactly what `hΩ_lt`/`hΩ_gt` alone fail to give: those hypotheses produce two
parameters straddling `θ₀`, but on unrelated nuisance coordinates, whereas
`ae_condDistrib_expTilt` compares two conditional laws by a tilt in the *`θ`*-direction only
when the nuisance coordinate is held fixed. Moving the two straddling parameters onto a
common `ϑ₀` is the step that threads item (a) into item (c) at `isUMPU_conditional_point`. -/
private lemma exists_twoSided_boundary_pair {Ω : Set (ℝ × Ξ)} [FiniteDimensional ℝ Ξ]
    (hΩ_convex : Convex ℝ Ω) (hΩ_aff : affineSpan ℝ Ω = ⊤) {θ₀ : ℝ}
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1) :
    ∃ (ϑ₀ : Ξ) (δ : ℝ), 0 < δ ∧ ((θ₀, ϑ₀) : ℝ × Ξ) ∈ Ω ∧
      ((θ₀ - δ, ϑ₀) : ℝ × Ξ) ∈ Ω ∧ ((θ₀ + δ, ϑ₀) : ℝ × Ξ) ∈ Ω := by
  obtain ⟨w, hw, hwθ⟩ := exists_interior_boundary_point hΩ_convex hΩ_aff hΩ_lt hΩ_gt
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior w hw
  have hwe : ((θ₀, w.2) : ℝ × Ξ) = w := by rw [← hwθ]
  -- every first-coordinate shift by less than `r` stays in the ball, hence in `Ω`
  have hshift : ∀ c : ℝ, |c - θ₀| < r → ((c, w.2) : ℝ × Ξ) ∈ Ω := by
    intro c hc
    refine interior_subset (hball ?_)
    rw [Metric.mem_ball, Prod.dist_eq]
    refine max_lt ?_ (by simpa using hr)
    rw [Real.dist_eq, hwθ]
    exact hc
  refine ⟨w.2, r / 2, by positivity, ?_, ?_, ?_⟩
  · rw [hwe]; exact interior_subset hw
  · exact hshift _ (by rw [show θ₀ - r / 2 - θ₀ = -(r / 2) by ring, abs_neg,
      abs_of_pos (by positivity)]; linarith)
  · exact hshift _ (by rw [show θ₀ + r / 2 - θ₀ = r / 2 by ring,
      abs_of_pos (by positivity)]; linarith)

/-- **Conditional integrability of `U` on the boundary surface.** At the boundary parameter
`w = (θ₀, ϑ₀)` produced by `exists_twoSided_boundary_pair`, the identity `u ↦ u` is
`condDistrib U T (P w) t`-integrable for `(P w).map T`-almost every `t`.

Mechanism. The two neighbours `(θ₀ ± δ, ϑ₀)` share the nuisance coordinate of `w`, so
`ae_condDistrib_expTilt` presents their conditional laws as the `(±δ)`-tilts of
`κ_t = condDistrib U T (P w) t` — a tilt in the `θ`-direction, which is what makes the
exponents `±δ·u` rather than an inner product against a nuisance increment. Both tilts are
probability measures, so `integrable_expTiltDensity` makes `u ↦ e^{δu}` and `u ↦ e^{−δu}`
both `κ_t`-integrable, and `abs_le_exp_add_exp_neg` majorises `|u|` by `δ⁻¹` times their sum.
The a.e.-`t` bookkeeping is the transport of the two tilt statements — each stated a.e. for
the law of `T` at its *own* parameter — back to `(P w).map T`, which is `statLaw_ac`.

This is the conditional-integrability input of item (c) at `isUMPU_conditional_point`. -/
private lemma exists_boundary_ae_integrable_id
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ}
    [BorelSpace Ξ] [FiniteDimensional ℝ Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    (hΩ_convex : Convex ℝ Ω) (hΩ_aff : affineSpan ℝ Ω = ⊤) {θ₀ : ℝ}
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1) :
    ∃ ϑ₀ : Ξ, ((θ₀, ϑ₀) : ℝ × Ξ) ∈ Ω ∧
      ∀ᵐ t ∂((P (θ₀, ϑ₀)).map T),
        Integrable (fun u : ℝ => u) (condDistrib U T (P (θ₀, ϑ₀)) t) := by
  obtain ⟨ϑ₀, δ, hδ, hw, hlo, hhi⟩ :=
    exists_twoSided_boundary_pair hΩ_convex hΩ_aff hΩ_lt hΩ_gt
  refine ⟨ϑ₀, hw, ?_⟩
  -- transport both tilt statements from their own `T`-laws back to the one at `w`
  have hhi' := Filter.Eventually.filter_mono (statLaw_ac hU hT hUT hw hhi).ae_le
    (ae_condDistrib_expTilt hU hT hUT hw hhi)
  have hlo' := Filter.Eventually.filter_mono (statLaw_ac hU hT hUT hw hlo).ae_le
    (ae_condDistrib_expTilt hU hT hUT hw hlo)
  filter_upwards [hhi', hlo'] with t ht1 ht2
  obtain ⟨k₁, hk₁, he₁⟩ := ht1
  obtain ⟨k₂, hk₂, he₂⟩ := ht2
  have hc₁ : ((θ₀ + δ, ϑ₀) : ℝ × Ξ).1 - ((θ₀, ϑ₀) : ℝ × Ξ).1 = δ := by
    simp only []; ring
  have hc₂ : ((θ₀ - δ, ϑ₀) : ℝ × Ξ).1 - ((θ₀, ϑ₀) : ℝ × Ξ).1 = -δ := by
    simp only []; ring
  rw [hc₁] at he₁
  rw [hc₂] at he₂
  haveI hpr₁ : IsProbabilityMeasure
      (expTilt (condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) k₁ δ) := by
    rw [← he₁]; infer_instance
  haveI hpr₂ : IsProbabilityMeasure
      (expTilt (condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) k₂ (-δ)) := by
    rw [← he₂]; infer_instance
  have hk₁pos : 0 < k₁ := expTilt_factor_pos hpr₁
  have hk₂pos : 0 < k₂ := expTilt_factor_pos hpr₂
  have hE₁ : Integrable (fun u : ℝ => Real.exp (δ * u))
      (condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) := by
    have h := ((integrable_expTiltDensity hk₁ hpr₁).1).const_mul k₁⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hk₁pos)] using h
  have hE₂ : Integrable (fun u : ℝ => Real.exp (-δ * u))
      (condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) := by
    have h := ((integrable_expTiltDensity hk₂ hpr₂).1).const_mul k₂⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hk₂pos)] using h
  refine Integrable.mono' ((hE₁.add hE₂).const_mul δ⁻¹)
    measurable_id.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  have hmaj := abs_le_exp_add_exp_neg hδ u
  rw [div_eq_inv_mul, ← neg_mul] at hmaj
  simpa [Real.norm_eq_abs] using hmaj

/-- **Secant separation, degenerate interval allowed.** The `C₁ ≤ C₂` form of
`exists_sep_line`. When `C₁ < C₂` it *is* `exists_sep_line`; when `C₁ = C₂` the secant
degenerates to the **tangent** of `u ↦ e^{cu}` at that point, which meets the exponential
there (so the endpoint equalities still hold) and lies below it everywhere else, the
"inside" clause becoming vacuous.

The point-null engine below needs exactly this: the hypothesis `C₁ t ≤ C₂ t` of
`isUMPU_conditional_point` permits a degenerate conditional interval, and no nondegeneracy
is available fibre by fibre. -/
private lemma exists_sep_line_le (c : ℝ) {C₁ C₂ : ℝ} (hC : C₁ ≤ C₂) :
    ∃ A B : ℝ,
      Real.exp (c * C₁) - A - B * C₁ = 0 ∧ Real.exp (c * C₂) - A - B * C₂ = 0 ∧
      (∀ u : ℝ, C₁ < u → u < C₂ → Real.exp (c * u) - A - B * u ≤ 0) ∧
      (∀ u : ℝ, u < C₁ ∨ C₂ < u → 0 ≤ Real.exp (c * u) - A - B * u) := by
  rcases eq_or_lt_of_le hC with heq | hlt
  · subst heq
    refine ⟨Real.exp (c * C₁) - c * Real.exp (c * C₁) * C₁, c * Real.exp (c * C₁),
      by ring, by ring, fun u h1 h2 => absurd h1 (not_lt.mpr h2.le), fun u _ => ?_⟩
    have hE : (0 : ℝ) < Real.exp (c * C₁) := Real.exp_pos _
    have h := Real.add_one_le_exp (c * u - c * C₁)
    have h2 := mul_le_mul_of_nonneg_left h hE.le
    have hsplit : Real.exp (c * u) = Real.exp (c * C₁) * Real.exp (c * u - c * C₁) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    nlinarith [h2]
  · exact exists_sep_line c hlt

/-- **The fibrewise point-null inequality.** Let `g` be bounded by `1`, nonnegative outside
`[C₁, C₂]` and nonpositive inside, with **both** side conditions at the reference measure `Q`:
`∫ g dQ = 0` and `∫ u·g(u) dQ = 0` (the latter requires `u` to be `Q`-integrable). Then every
exponential tilt of `Q` gives `g` a nonnegative integral.

This is the point-null analogue of `integral_expTilt_signed` / `integral_expTilt_signed_interval`
and the reason the alternative may be *two-sided*: the separating object is the affine
function `A + Bu` of `exists_sep_line_le`, which lies below `e^{cu}` outside `[C₁, C₂]` and
above it inside for **either** sign of `c`, convexity of `exp` being sign-blind. The two side
conditions annihilate the two affine terms, leaving `∫ g(u) e^{cu} dQ ≥ 0`. -/
private lemma integral_expTilt_signed_point {Q : Measure ℝ} [IsProbabilityMeasure Q]
    {k c C₁ C₂ : ℝ} (hCle : C₁ ≤ C₂) (hk : 0 ≤ k)
    (hprob : IsProbabilityMeasure (expTilt Q k c))
    {g : ℝ → ℝ} (hgm : Measurable g) (hgb : ∀ u, |g u| ≤ 1)
    (hgpos : ∀ u : ℝ, u < C₁ ∨ C₂ < u → 0 ≤ g u)
    (hgneg : ∀ u : ℝ, C₁ < u → u < C₂ → g u ≤ 0)
    (hid : Integrable (fun u : ℝ => u) Q)
    (hz : ∫ u, g u ∂Q = 0) (hz' : ∫ u, u * g u ∂Q = 0) :
    0 ≤ ∫ u, g u ∂(expTilt Q k c) := by
  obtain ⟨A, B, h1, h2, hin, hout⟩ := exists_sep_line_le c hCle
  obtain ⟨hdint, -⟩ := integrable_expTiltDensity hk hprob
  have hkpos : 0 < k := expTilt_factor_pos hprob
  have hkne : k ≠ 0 := ne_of_gt hkpos
  have hgnorm : ∀ᵐ u ∂Q, ‖g u‖ ≤ 1 :=
    Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hgb u
  have hgint : Integrable g Q :=
    Integrable.mono' (integrable_const (1 : ℝ)) hgm.aestronglyMeasurable hgnorm
  have hugint : Integrable (fun u : ℝ => u * g u) Q :=
    hid.mul_bdd hgm.aestronglyMeasurable hgnorm
  have hprodint : Integrable (fun u => g u * (k * Real.exp (c * u))) Q :=
    hdint.bdd_mul hgm.aestronglyMeasurable hgnorm
  have hgexp : Integrable (fun u => g u * Real.exp (c * u)) Q := by
    refine (hprodint.const_mul k⁻¹).congr (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [show k⁻¹ * (g u * (k * Real.exp (c * u)))
        = k⁻¹ * k * (g u * Real.exp (c * u)) by ring, inv_mul_cancel₀ hkne, one_mul]
  -- the separating affine function has the sign of `g` at every point
  have hpt : ∀ u : ℝ, 0 ≤ g u * (Real.exp (c * u) - A - B * u) := by
    intro u
    rcases lt_trichotomy u C₁ with h | h | h
    · exact mul_nonneg (hgpos u (Or.inl h)) (hout u (Or.inl h))
    · have hzero : Real.exp (c * u) - A - B * u = 0 := by rw [h]; exact h1
      simp [hzero]
    · rcases lt_trichotomy u C₂ with h' | h' | h'
      · have hprodnn := mul_nonneg (neg_nonneg.mpr (hgneg u h h'))
          (neg_nonneg.mpr (hin u h h'))
        rwa [neg_mul_neg] at hprodnn
      · have hzero : Real.exp (c * u) - A - B * u = 0 := by rw [h']; exact h2
        simp [hzero]
      · exact mul_nonneg (hgpos u (Or.inr h')) (hout u (Or.inr h'))
  have hsplit : ∫ u, g u * (Real.exp (c * u) - A - B * u) ∂Q
      = (∫ u, g u * Real.exp (c * u) ∂Q) - A * (∫ u, g u ∂Q) - B * ∫ u, u * g u ∂Q := by
    have hfun : (fun u => g u * (Real.exp (c * u) - A - B * u))
        = fun u => (g u * Real.exp (c * u) - A * g u) - B * (u * g u) := by
      funext u; ring
    rw [hfun, integral_sub (hgexp.sub' (hgint.const_mul A)) (hugint.const_mul B),
      integral_sub hgexp (hgint.const_mul A), integral_const_mul, integral_const_mul]
  have hI : (0 : ℝ) ≤ ∫ u, g u * (Real.exp (c * u) - A - B * u) ∂Q := integral_nonneg hpt
  rw [hsplit, hz, hz'] at hI
  have hI' : (0 : ℝ) ≤ ∫ u, g u * Real.exp (c * u) ∂Q := by linarith
  rw [integral_expTilt Q hk c g,
    show (fun u => g u * (k * Real.exp (c * u)))
      = fun u => k * (g u * Real.exp (c * u)) by funext u; ring, integral_const_mul]
  exact mul_nonneg hk hI'

/-- **A pure-`θ` window at an interior parameter.** Around a point of `interior Ω` the whole
`θ`-segment through it, of some positive half-width, lies in `Ω`. This is the form in which
item (b) of `isUMPU_conditional_point` consumes interiority: it supplies simultaneously the
two endpoints `(θ₀ ± δ, ϑ)` that `integrable_U_of_twoSided` and `hasDerivAt_integral_canExp`
need, and the whole window on which unbiasedness is read as a local minimum. -/
private lemma exists_pure_theta_window {Ω : Set (ℝ × Ξ)} {θ₀ : ℝ} {ϑ : Ξ}
    (h : ((θ₀, ϑ) : ℝ × Ξ) ∈ interior Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ, |θ - θ₀| ≤ δ → ((θ, ϑ) : ℝ × Ξ) ∈ Ω := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ h
  refine ⟨r / 2, by positivity, fun θ hθ => ?_⟩
  refine interior_subset (hball ?_)
  rw [Metric.mem_ball, Prod.dist_eq]
  refine max_lt ?_ (by simpa using hr)
  rw [Real.dist_eq]
  change |θ - θ₀| < r
  linarith

/-- **Disintegration of integrability.** If `φ(U, T)` is integrable then its conditional
integral is an integrable function of `T`. The `Integrable` companion of
`integral_eq_integral_condDistrib`, and what item (d) of `isUMPU_conditional_point` needs to
split `∫ (E[Uψ ∣ t] − α·E[U ∣ t]) dP^T` into two convergent halves; for the *bounded*
integrands of the interval theorems this was free from `integrable_const`. -/
private lemma integrable_condPower_of_integrable {P : ℝ × Ξ → Measure 𝓧} {U : 𝓧 → ℝ}
    {T : 𝓧 → Ξ} [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) {φ : ℝ × Ξ → ℝ} (hφ : Measurable φ)
    {p : ℝ × Ξ} (hint : Integrable (fun x => φ (U x, T x)) (P p)) :
    Integrable (fun t => ∫ u, φ (u, t) ∂(condDistrib U T (P p) t)) ((P p).map T) := by
  have hgm : Measurable fun z : Ξ × ℝ => φ (z.2, z.1) :=
    hφ.comp (measurable_snd.prodMk measurable_fst)
  have h : Integrable (fun z : Ξ × ℝ => φ (z.2, z.1)) ((P p).map fun x => (T x, U x)) := by
    rw [integrable_map_measure hgm.aestronglyMeasurable (hT.prodMk hU).aemeasurable]
    exact hint
  exact h.integral_condDistrib_map hU.aemeasurable

/-- **The point-null fibrewise engine, globalised.** The analogue of
`integral_comp_sign_of_condZero_interval` for a *single* boundary surface: `g` is bounded,
nonnegative outside the conditional interval and nonpositive inside, and satisfies at the
reference parameter `p₀` **both** conditional side conditions — vanishing conditional
integral and vanishing conditional first moment. Then its unconditional integral is
nonnegative at **every** parameter of `Ω`, on either side of `θ₀`.

Applied to `g = φ − α` this is simultaneously the level (equality on the surface) and the
unbiasedness of the point-null conditional test; applied to `g = φ − ψ` it is its
optimality. -/
private lemma integral_comp_sign_of_condZero_point {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)}
    {U : 𝓧 → ℝ} {T : 𝓧 → Ξ} {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ}
    [BorelSpace Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    {p₀ p : ℝ × Ξ} (hp₀ : p₀ ∈ Ω) (hp : p ∈ Ω)
    {C₁ C₂ : Ξ → ℝ} (hCle : ∀ t, C₁ t ≤ C₂ t)
    {g : ℝ × Ξ → ℝ} (hgm : Measurable g) (hgb : ∀ z, |g z| ≤ 1)
    (hgpos : ∀ z : ℝ × Ξ, z.1 < C₁ z.2 ∨ C₂ z.2 < z.1 → 0 ≤ g z)
    (hgneg : ∀ z : ℝ × Ξ, C₁ z.2 < z.1 → z.1 < C₂ z.2 → g z ≤ 0)
    (hid : ∀ᵐ t ∂((P p₀).map T), Integrable (fun u : ℝ => u) (condDistrib U T (P p₀) t))
    (hz : ∀ᵐ t ∂((P p₀).map T), ∫ u, g (u, t) ∂(condDistrib U T (P p₀) t) = 0)
    (hz' : ∀ᵐ t ∂((P p₀).map T), ∫ u, u * g (u, t) ∂(condDistrib U T (P p₀) t) = 0) :
    0 ≤ ∫ x, g (U x, T x) ∂(P p) := by
  haveI := isProbabilityMeasure_statLaw (P := P) hT p
  have hac := (statLaw_ac hU hT hUT hp hp₀).ae_le
  have e1 := Filter.Eventually.filter_mono hac hid
  have e2 := Filter.Eventually.filter_mono hac hz
  have e3 := Filter.Eventually.filter_mono hac hz'
  have hkey : ∀ᵐ t ∂((P p).map T), 0 ≤ ∫ u, g (u, t) ∂(condDistrib U T (P p) t) := by
    filter_upwards [e1, e2, e3, ae_condDistrib_expTilt hU hT hUT hp₀ hp] with t h1 h2 h3 hd
    obtain ⟨k, hk, hteq⟩ := hd
    haveI : IsProbabilityMeasure (condDistrib U T (P p₀) t) := inferInstance
    haveI hQ : IsProbabilityMeasure (expTilt (condDistrib U T (P p₀) t) k (p.1 - p₀.1)) := by
      rw [← hteq]; infer_instance
    have hgmt : Measurable fun u : ℝ => g (u, t) :=
      hgm.comp (measurable_id.prodMk measurable_const)
    rw [hteq]
    exact integral_expTilt_signed_point (hCle t) hk hQ hgmt (fun u => hgb _)
      (fun u hu => hgpos (u, t) hu) (fun u ha hb => hgneg (u, t) ha hb) h1 h2 h3
  rw [integral_comp_eq_integral_condPower hU hT hgm hgb p]
  exact integral_nonneg_of_ae hkey

/-- **The conditional derivative side condition of an unbiased competitor.** *Item (d) of
`isUMPU_conditional_point`.* A critical function of `(U, T)` which is similar of size `α` on
the boundary surface `θ = θ₀` and has power at least `α` off it satisfies

`E_{θ₀}[U·ψ ∣ t] = α · E_{θ₀}[U ∣ t]` for almost every `t`.

The full-measure identity `E[Uψ] = α·E[U]` holds at every *interior* boundary parameter by
`integral_U_mul_eq_of_boundary_min` (unbiasedness ⟹ vanishing derivative of the power along
the pure-`θ` window supplied by `exists_pure_theta_window`). The passage to the conditional
statement is `complete_boundary` applied to `t ↦ E[Uψ ∣ t] − α·E[U ∣ t]` — completeness
rather than *bounded* completeness, because `U` is unbounded — the disintegration of the
full-measure identity being legitimate because `integrable_U_of_twoSided` makes `U`, hence
`U·ψ`, integrable there, and `integrable_condPower_of_integrable` makes the two conditional
halves separately integrable. -/
private lemma ae_condDeriv_eq_of_similar {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)}
    {U : 𝓧 → ℝ} {T : 𝓧 → Ξ} {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ}
    [BorelSpace Ξ] [FiniteDimensional ℝ Ξ] [∀ p, IsProbabilityMeasure (P p)]
    (hU : Measurable U) (hT : Measurable T) (hUT : IsCanonicalUT P Ω U T ν C)
    (hΩ_convex : Convex ℝ Ω) (hΩ_aff : affineSpan ℝ Ω = ⊤) {θ₀ α : ℝ}
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1)
    {p₀ : ℝ × Ξ} (hp₀ : p₀ ∈ Ω) (hp₀θ : p₀.1 = θ₀)
    {ψ : ℝ × Ξ → ℝ} (hψm : Measurable ψ) (hψb : ∀ z, |ψ z| ≤ 1)
    (hsim : ∀ p ∈ Ω, p.1 = θ₀ → ∫ x, ψ (U x, T x) ∂(P p) = α)
    (hge : ∀ p ∈ Ω, p.1 ≠ θ₀ → α ≤ ∫ x, ψ (U x, T x) ∂(P p)) :
    ∀ᵐ t ∂((P p₀).map T),
      ∫ u, u * ψ (u, t) ∂(condDistrib U T (P p₀) t)
        = α * ∫ u, u ∂(condDistrib U T (P p₀) t) := by
  classical
  have hmul : Measurable fun z : ℝ × Ξ => z.1 * ψ z := measurable_fst.mul hψm
  have hfm : Measurable fun t : Ξ =>
      (∫ u, u * ψ (u, t) ∂(condDistrib U T (P p₀) t))
        - α * ∫ u, u ∂(condDistrib U T (P p₀) t) :=
    (measurable_condPower hU hT hmul (P p₀)).sub
      ((measurable_condPower hU hT measurable_fst (P p₀)).const_mul α)
  -- at every interior boundary parameter the difference is integrable and averages to zero
  have hboth : ∀ ϑ : Ξ, ((θ₀, ϑ) : ℝ × Ξ) ∈ interior Ω →
      Integrable (fun t : Ξ => (∫ u, u * ψ (u, t) ∂(condDistrib U T (P p₀) t))
          - α * ∫ u, u ∂(condDistrib U T (P p₀) t)) ((P ((θ₀, ϑ) : ℝ × Ξ)).map T) ∧
        ∫ t, ((∫ u, u * ψ (u, t) ∂(condDistrib U T (P p₀) t))
          - α * ∫ u, u ∂(condDistrib U T (P p₀) t)) ∂((P ((θ₀, ϑ) : ℝ × Ξ)).map T) = 0 := by
    intro ϑ hϑint
    have hq : ((θ₀, ϑ) : ℝ × Ξ) ∈ Ω := interior_subset hϑint
    obtain ⟨δ, hδ, hwin⟩ := exists_pure_theta_window hϑint
    have hlo : ((θ₀ - δ, ϑ) : ℝ × Ξ) ∈ Ω :=
      hwin _ (by rw [show θ₀ - δ - θ₀ = -δ by ring, abs_neg, abs_of_pos hδ])
    have hhi : ((θ₀ + δ, ϑ) : ℝ × Ξ) ∈ Ω :=
      hwin _ (by rw [show θ₀ + δ - θ₀ = δ by ring, abs_of_pos hδ])
    -- `U` and `U·ψ` are integrable at this parameter
    have hIU : Integrable U (P ((θ₀, ϑ) : ℝ × Ξ)) :=
      integrable_U_of_twoSided hU hT hUT hδ hlo hhi hq
    have hIUψ : Integrable (fun x => U x * ψ (U x, T x)) (P ((θ₀, ϑ) : ℝ × Ξ)) :=
      hIU.mul_bdd ((hψm.comp (hU.prodMk hT)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hψb _)
    -- the conditional law does not depend on the nuisance coordinate
    have hcd : ∀ᵐ t ∂((P ((θ₀, ϑ) : ℝ × Ξ)).map T),
        condDistrib U T (P ((θ₀, ϑ) : ℝ × Ξ)) t = condDistrib U T (P p₀) t :=
      condDistrib_eq_of_fst_eq hU hT hUT hq hp₀ (by rw [hp₀θ])
    have hfeq : (fun t : Ξ => (∫ u, u * ψ (u, t) ∂(condDistrib U T (P p₀) t))
          - α * ∫ u, u ∂(condDistrib U T (P p₀) t))
        =ᵐ[(P ((θ₀, ϑ) : ℝ × Ξ)).map T]
        fun t : Ξ => (∫ u, u * ψ (u, t) ∂(condDistrib U T (P ((θ₀, ϑ) : ℝ × Ξ)) t))
          - α * ∫ u, u ∂(condDistrib U T (P ((θ₀, ϑ) : ℝ × Ξ)) t) := by
      filter_upwards [hcd] with t ht
      rw [ht]
    have hI1 : Integrable (fun t : Ξ => ∫ u, u * ψ (u, t)
        ∂(condDistrib U T (P ((θ₀, ϑ) : ℝ × Ξ)) t)) ((P ((θ₀, ϑ) : ℝ × Ξ)).map T) :=
      integrable_condPower_of_integrable hU hT hmul hIUψ
    have hI2 : Integrable (fun t : Ξ => ∫ u, u
        ∂(condDistrib U T (P ((θ₀, ϑ) : ℝ × Ξ)) t)) ((P ((θ₀, ϑ) : ℝ × Ξ)).map T) :=
      integrable_condPower_of_integrable hU hT measurable_fst hIU
    refine ⟨(hI1.sub' (hI2.const_mul α)).congr hfeq.symm, ?_⟩
    -- the two conditional halves average to the two full-measure expectations
    have hd1 : ∫ x, U x * ψ (U x, T x) ∂(P ((θ₀, ϑ) : ℝ × Ξ))
        = ∫ t, (∫ u, u * ψ (u, t) ∂(condDistrib U T (P ((θ₀, ϑ) : ℝ × Ξ)) t))
            ∂((P ((θ₀, ϑ) : ℝ × Ξ)).map T) :=
      integral_eq_integral_condDistrib hU hT hmul hIUψ
    have hd2 : ∫ x, U x ∂(P ((θ₀, ϑ) : ℝ × Ξ))
        = ∫ t, (∫ u, u ∂(condDistrib U T (P ((θ₀, ϑ) : ℝ × Ξ)) t))
            ∂((P ((θ₀, ϑ) : ℝ × Ξ)).map T) :=
      integral_eq_integral_condDistrib hU hT measurable_fst hIU
    -- unbiasedness along the pure-`θ` window kills the derivative of the power
    have hmin : ∀ θ : ℝ, |θ - θ₀| ≤ δ →
        α ≤ ∫ x, ψ (U x, T x) ∂(P ((θ, ϑ) : ℝ × Ξ)) := by
      intro θ hθ
      rcases eq_or_ne θ θ₀ with rfl | hne
      · exact le_of_eq (hsim _ (hwin _ hθ) rfl).symm
      · exact hge _ (hwin _ hθ) hne
    have hres := integral_U_mul_eq_of_boundary_min hU hT hUT hΩ_convex hδ hq hlo hhi
      hψm hψb (hsim _ hq rfl) hmin
    rw [integral_congr_ae hfeq, integral_sub hI1 (hI2.const_mul α), integral_const_mul,
      ← hd1, ← hd2]
    linarith
  have hae := complete_boundary hU hT hUT hΩ_convex hΩ_aff hΩ_lt hΩ_gt hfm
    (fun ϑ hϑ => (hboth ϑ hϑ).1) (fun ϑ hϑ => (hboth ϑ hϑ).2) hp₀
  filter_upwards [hae] with t ht
  have hz : (∫ u, u * ψ (u, t) ∂(condDistrib U T (P p₀) t))
      - α * ∫ u, u ∂(condDistrib U T (P p₀) t) = 0 := ht
  linarith

/-- **Point null.** For `H : θ = θ₀` against `K : θ ≠ θ₀`, the conditional test rejecting
*outside* an interval in `u` is UMP unbiased at level `α`, provided its constants satisfy
**both** conditional conditions on the boundary surface `θ = θ₀`:

* the conditional size condition `E_{θ₀}[φ ∣ t] = α`, and
* the conditional derivative condition `E_{θ₀}[U·φ ∣ t] = α·E_{θ₀}[U ∣ t]`,

the second being the analytic content of unbiasedness (the power function of the conditional
problem has a minimum at `θ₀`). -/
theorem isUMPU_conditional_point
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} {θ₀ α : ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ p, IsProbabilityMeasure (P p)]
    -- LEAN-ONLY (AMENDMENT): the σ-algebra of `Ξ` is the Borel one and `Ξ` is finite
    -- dimensional; see `boundedlyComplete_boundary`
    [BorelSpace Ξ] [FiniteDimensional ℝ Ξ]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT (AMENDMENT): `(U, T)` is sufficient, in the operative sense that every
    -- critical function is matched in power by a critical function of `(U, T)`. Without it
    -- the statement is FALSE — see the counterexample section and the note in the docstring
    (hsuff : SufficiencyReducible P Ω U T)
    -- USER-INPUT: the parameter set is convex
    (hΩ_convex : Convex ℝ Ω)
    -- USER-INPUT: the parameter set is not contained in a proper linear subspace
    (hΩ_span : Submodule.span ℝ Ω = ⊤)
    -- USER-INPUT (AMENDMENT): the parameter set is not contained in a proper *affine*
    -- subspace either. This is the faithful reading of the source's "not contained in a
    -- linear space of dimension less than `k+1`", and it is strictly stronger than the
    -- frozen `hΩ_span`, which does not suffice: see `boundedlyComplete_boundary` for a
    -- convex `Ω` with full linear span whose boundary surface is a single point
    (hΩ_aff : affineSpan ℝ Ω = ⊤)
    -- USER-INPUT: the parameter set reaches below and above the null value
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: measurable selection of the critical values and randomization
    -- probabilities
    (hC₁ : Measurable C₁) (hC₂ : Measurable C₂)
    (hγ₁ : Measurable γ₁) (hγ₂ : Measurable γ₂)
    -- USER-INPUT: the randomization probabilities are probabilities
    (hγ₁_mem : ∀ t, γ₁ t ∈ Set.Icc (0 : ℝ) 1) (hγ₂_mem : ∀ t, γ₂ t ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the critical values are ordered
    (hC : ∀ t, C₁ t ≤ C₂ t)
    -- USER-INPUT: conditional size condition on the boundary surface `θ = θ₀`
    (hsize : ∀ p ∈ Ω, p.1 = θ₀ → ∀ᵐ t ∂((P p).map T),
      ∫ u, condOutsideTest C₁ C₂ γ₁ γ₂ (u, t) ∂(condDistrib U T (P p) t) = α)
    -- USER-INPUT: conditional derivative (unbiasedness) condition on the same surface
    (hderiv : ∀ p ∈ Ω, p.1 = θ₀ → ∀ᵐ t ∂((P p).map T),
      ∫ u, u * condOutsideTest C₁ C₂ γ₁ γ₂ (u, t) ∂(condDistrib U T (P p) t)
        = α * ∫ u, u ∂(condDistrib U T (P p) t)) :
    IsUMPU P {p ∈ Ω | p.1 = θ₀} {p ∈ Ω | p.1 ≠ θ₀} α
      (fun x => condOutsideTest C₁ C₂ γ₁ γ₂ (U x, T x)) := by
  -- REPAIRED AND PROVED (wave 8). Both repairs of the other three theorems are applied here
  -- as well (`hsuff`, `hΩ_aff`, `[BorelSpace Ξ] [FiniteDimensional ℝ Ξ]`): the frozen form was
  -- FALSE, refuted by
  -- `ConditionalUMPUCounterexample.not_isUMPU_conditional_point_counterexample`, and the
  -- degenerate-`Ω` defect of the file docstring applies verbatim.
  --
  -- The proof mirrors `isUMPU_conditional_outside` line for line, with the two-constraint
  -- engine `integral_comp_sign_of_condZero_point` in place of the two-endpoint engine
  -- `integral_comp_sign_of_condZero_interval`. The alternative `θ ≠ θ₀` is two-sided and is
  -- covered in one stroke, because the separating object `exists_sep_line_le` is the secant
  -- (or, on a degenerate fibre, the tangent) of `u ↦ e^{cu}` and convexity of `exp` is blind
  -- to the sign of `c = θ − θ₀`.
  --
  -- The reference parameter is the interior boundary point `(θ₀, ϑ₀)` of
  -- `exists_boundary_ae_integrable_id`, at which `U` is conditionally integrable — needed
  -- because the point null carries a *second* side condition, on the conditional first
  -- moment, which is what the affine separation consumes. For the competitor that second
  -- condition is `ae_condDeriv_eq_of_similar` (item (d)), whose full-measure input is the
  -- vanishing derivative of the power at a minimum, `integral_U_mul_eq_of_boundary_min`
  -- (item (b)), and whose conditional transfer is the unbounded `complete_boundary` (item
  -- (c)); the first condition is `ae_condPower_eq_of_similar` exactly as in the interval
  -- theorems.
  classical
  have hφm : Measurable (condOutsideTest C₁ C₂ γ₁ γ₂) :=
    measurable_condOutsideTest hC₁ hC₂ hγ₁ hγ₂
  have hφIcc : ∀ z : ℝ × Ξ, condOutsideTest C₁ C₂ γ₁ γ₂ z ∈ Set.Icc (0 : ℝ) 1 :=
    condOutsideTest_mem_Icc hγ₁_mem hγ₂_mem
  have hφb : ∀ z : ℝ × Ξ, |condOutsideTest C₁ C₂ γ₁ γ₂ z| ≤ 1 := abs_le_one_of_mem_Icc hφIcc
  haveI hstat : ∀ p : ℝ × Ξ, IsProbabilityMeasure ((P p).map T) := fun p =>
    isProbabilityMeasure_statLaw (P := P) hT p
  -- the reference boundary parameter, at which `U` is conditionally integrable
  obtain ⟨ϑ₀, hp₀Ω, hp₀int⟩ :=
    exists_boundary_ae_integrable_id hU hT hUT hΩ_convex hΩ_aff hΩ_lt hΩ_gt
  have hp₀θ : ((θ₀, ϑ₀) : ℝ × Ξ).1 = θ₀ := rfl
  have hsz₀ := hsize _ hp₀Ω hp₀θ
  have hdv₀ := hderiv _ hp₀Ω hp₀θ
  -- the comparison against any competitor sharing the two conditional side conditions
  have hcmp : ∀ w : ℝ × Ξ → ℝ, Measurable w → (∀ z, w z ∈ Set.Icc (0 : ℝ) 1) →
      (∀ᵐ t ∂((P ((θ₀, ϑ₀) : ℝ × Ξ)).map T),
        ∫ u, w (u, t) ∂(condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) = α) →
      (∀ᵐ t ∂((P ((θ₀, ϑ₀) : ℝ × Ξ)).map T),
        ∫ u, u * w (u, t) ∂(condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t)
          = α * ∫ u, u ∂(condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t)) →
      ∀ p ∈ Ω, ∫ x, w (U x, T x) ∂(P p)
        ≤ ∫ x, condOutsideTest C₁ C₂ γ₁ γ₂ (U x, T x) ∂(P p) := by
    intro w hwm hwIcc hw₁ hw₂ p hp
    have hwb : ∀ z : ℝ × Ξ, |w z| ≤ 1 := abs_le_one_of_mem_Icc hwIcc
    set g : ℝ × Ξ → ℝ := fun z => condOutsideTest C₁ C₂ γ₁ γ₂ z - w z with hgdef
    have hgm : Measurable g := hφm.sub hwm
    have hgb : ∀ z, |g z| ≤ 1 := by
      intro z
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 := (hφIcc z).1
        have h2 := (hwIcc z).2
        simp only [hgdef]; linarith
      · have h1 := (hφIcc z).2
        have h2 := (hwIcc z).1
        simp only [hgdef]; linarith
    have hgpos : ∀ z : ℝ × Ξ, z.1 < C₁ z.2 ∨ C₂ z.2 < z.1 → 0 ≤ g z := by
      intro z hz
      have h1 : condOutsideTest C₁ C₂ γ₁ γ₂ z = 1 := condOutsideTest_eq_one hz
      have h2 := (hwIcc z).2
      simp only [hgdef, h1]; linarith
    have hgneg : ∀ z : ℝ × Ξ, C₁ z.2 < z.1 → z.1 < C₂ z.2 → g z ≤ 0 := by
      intro z ha hb
      have h1 : condOutsideTest C₁ C₂ γ₁ γ₂ z = 0 := condOutsideTest_eq_zero ha hb
      have h2 := (hwIcc z).1
      simp only [hgdef, h1]; linarith
    -- the two conditional side conditions for the difference
    have hzc : ∀ᵐ t ∂((P ((θ₀, ϑ₀) : ℝ × Ξ)).map T),
        ∫ u, g (u, t) ∂(condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) = 0 := by
      filter_upwards [hsz₀, hw₁] with t hta htb
      haveI : IsProbabilityMeasure (condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) := inferInstance
      have hfun : (fun u : ℝ => g (u, t))
          = fun u : ℝ => condOutsideTest C₁ C₂ γ₁ γ₂ (u, t) - w (u, t) := by
        funext u; simp only [hgdef]
      rw [hfun, integral_sub
        (integrable_cond_slice (P ((θ₀, ϑ₀) : ℝ × Ξ)) hU hT hφm hφb t)
        (integrable_cond_slice (P ((θ₀, ϑ₀) : ℝ × Ξ)) hU hT hwm hwb t), hta, htb, sub_self]
    have hzc' : ∀ᵐ t ∂((P ((θ₀, ϑ₀) : ℝ × Ξ)).map T),
        ∫ u, u * g (u, t) ∂(condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) = 0 := by
      filter_upwards [hp₀int, hdv₀, hw₂] with t hti hta htb
      have hIφ : Integrable (fun u : ℝ => u * condOutsideTest C₁ C₂ γ₁ γ₂ (u, t))
          (condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) :=
        hti.mul_bdd ((hφm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hφb _)
      have hIw : Integrable (fun u : ℝ => u * w (u, t))
          (condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) :=
        hti.mul_bdd ((hwm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hwb _)
      have hfun : (fun u : ℝ => u * g (u, t))
          = fun u : ℝ => u * condOutsideTest C₁ C₂ γ₁ γ₂ (u, t) - u * w (u, t) := by
        funext u; simp only [hgdef]; ring
      rw [hfun, integral_sub hIφ hIw, hta, htb, sub_self]
    have hsplit : ∫ x, g (U x, T x) ∂(P p)
        = (∫ x, condOutsideTest C₁ C₂ γ₁ γ₂ (U x, T x) ∂(P p))
          - ∫ x, w (U x, T x) ∂(P p) := by
      rw [hgdef]
      exact integral_sub (integrable_comp_UT hU hT hφm hφb p)
        (integrable_comp_UT hU hT hwm hwb p)
    have h := integral_comp_sign_of_condZero_point hU hT hUT hp₀Ω hp hC hgm hgb hgpos hgneg
      hp₀int hzc hzc'
    rw [hsplit] at h
    linarith
  -- the constant test `α` satisfies both side conditions
  have hconstsize : ∀ᵐ t ∂((P ((θ₀, ϑ₀) : ℝ × Ξ)).map T),
      ∫ _u, (α : ℝ) ∂(condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) = α := by
    refine Filter.Eventually.of_forall fun t => ?_
    haveI : IsProbabilityMeasure (condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) := inferInstance
    simp
  have hconstderiv : ∀ᵐ t ∂((P ((θ₀, ϑ₀) : ℝ × Ξ)).map T),
      ∫ u, u * (α : ℝ) ∂(condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t)
        = α * ∫ u, u ∂(condDistrib U T (P ((θ₀, ϑ₀) : ℝ × Ξ)) t) := by
    refine Filter.Eventually.of_forall fun t => ?_
    rw [integral_mul_const, mul_comm]
  have hconstIcc : ∀ _z : ℝ × Ξ, (α : ℝ) ∈ Set.Icc (0 : ℝ) 1 := fun _ => ⟨hα₀.le, hα₁.le⟩
  have hconst := hcmp (fun _ => α) measurable_const hconstIcc hconstsize hconstderiv
  have hpowconst : ∀ p : ℝ × Ξ, ∫ _x, (α : ℝ) ∂(P p) = α := fun p => by simp
  -- the power on the boundary surface is exactly `α`
  have hbdry : ∀ p ∈ Ω, p.1 = θ₀ →
      ∫ x, condOutsideTest C₁ C₂ γ₁ γ₂ (U x, T x) ∂(P p) = α := by
    intro p hp hpθ
    rw [integral_comp_eq_integral_condPower hU hT hφm hφb p,
      integral_congr_ae (hsize p hp hpθ)]
    simp
  refine ⟨⟨hφm.comp (hU.prodMk hT), fun x => hφIcc _⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro p ⟨hpΩ, hpθ⟩
    simp only [power]
    exact le_of_eq (hbdry p hpΩ hpθ)
  · rintro p ⟨hpΩ, -⟩
    simp only [power]
    have := hconst p hpΩ
    rw [hpowconst p] at this
    exact this
  · rintro ψ hψ hunb p' ⟨hp'Ω, hp'ne⟩
    obtain ⟨ψ', hψ'crit, hψ'pow⟩ := hsuff ψ hψ
    have hψ'b : ∀ z : ℝ × Ξ, |ψ' z| ≤ 1 := abs_le_one_of_mem_Icc hψ'crit.2
    obtain ⟨q, hq, hqθ⟩ := id hΩ_gt
    -- unbiasedness forces similarity on the boundary surface
    have hsim : ∀ p ∈ Ω, p.1 = θ₀ → ∫ x, ψ' (U x, T x) ∂(P p) = α := by
      intro p hp hpθ
      refine integral_comp_eq_of_le_of_segment hU hT hUT hΩ_convex hp hq
        hψ'crit.1 hψ'b ?_ ?_
      · rw [hψ'pow p hp]
        simpa only [power] using hunb.1 p ⟨hp, hpθ⟩
      · intro s hs0 hs1
        have hr : (1 - s) • p + s • q ∈ Ω :=
          hΩ_convex hp hq (by linarith) hs0.le (by ring)
        have hrfst : ((1 - s) • p + s • q).1 = (1 - s) * p.1 + s * q.1 := by
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        have hrne : ((1 - s) • p + s • q).1 ≠ θ₀ := by
          rw [hrfst, hpθ]
          intro hcon
          nlinarith [mul_pos hs0 (sub_pos.mpr hqθ)]
        rw [hψ'pow _ hr]
        simpa only [power] using hunb.2 _ ⟨hr, hrne⟩
    have hge : ∀ p ∈ Ω, p.1 ≠ θ₀ → α ≤ ∫ x, ψ' (U x, T x) ∂(P p) := by
      intro p hp hpne
      rw [hψ'pow p hp]
      simpa only [power] using hunb.2 p ⟨hp, hpne⟩
    -- the two conditional side conditions of the competitor
    have hns := ae_condPower_eq_of_similar hU hT hUT hΩ_convex hΩ_aff hΩ_lt hΩ_gt hp₀Ω hp₀θ
      hψ'crit.1 hψ'b hsim
    have hnd := ae_condDeriv_eq_of_similar hU hT hUT hΩ_convex hΩ_aff hΩ_lt hΩ_gt hp₀Ω hp₀θ
      hψ'crit.1 hψ'b hsim hge
    have hfin := hcmp ψ' hψ'crit.1 hψ'crit.2 hns hnd p' hp'Ω
    simp only [power]
    rw [← hψ'pow p' hp'Ω]
    exact hfin

/-! ## Measurable selection of the conditional constants -/

/-- The conditional critical value at level `α`: the `(1−α)`-quantile of the distribution
function of `μ`. Explicit — this is what makes the selection measurable in the conditioning
variable, `t ↦ critC (κ t) α` being a quantile of a measurable family of CDFs. -/
private noncomputable def critC (μ : Measure ℝ) (α : ℝ) : ℝ := quantile (⇑(cdf μ)) (1 - α)

/-- The matching randomization weight: the fraction of the atom at `critC μ α` needed to make
the size exactly `α`. Division by zero returns `0`, which is precisely the correct value when
there is no atom (there the size is already exactly `α`). -/
private noncomputable def critGamma (μ : Measure ℝ) (α : ℝ) : ℝ :=
  (α - (μ {x : ℝ | critC μ α < x}).toReal) / (μ {x : ℝ | x = critC μ α}).toReal

/-- The `(1−α)`-sublevel set of a distribution function is nonempty (the CDF tends to `1`)
and bounded below (it tends to `0`), for `0 < α < 1`. -/
private lemma cdf_sublevel_nonempty_bddBelow (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    {y : ℝ | 1 - α ≤ cdf μ y}.Nonempty ∧ BddBelow {y : ℝ | 1 - α ≤ cdf μ y} := by
  constructor
  · obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt
      (show 1 - α < 1 by linarith)).exists
    exact ⟨y, le_of_lt hy⟩
  · obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp
      ((tendsto_cdf_atBot μ).eventually_lt_const (show (0 : ℝ) < 1 - α by linarith))
    refine ⟨b, fun y hy => ?_⟩
    simp only [Set.mem_setOf_eq] at hy
    by_contra hcon
    exact absurd (hb y (not_le.mp hcon).le) (not_lt.mpr hy)

/-- **Galois property of the conditional critical value.** `critC μ α ≤ x` iff the CDF has
already reached `1 − α` at `x`. This is what turns the measurability of `t ↦ cdf (κ t) x`
into the measurability of `t ↦ critC (κ t) α`. -/
private lemma critC_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (x : ℝ) : critC μ α ≤ x ↔ 1 - α ≤ cdf μ x :=
  quantile_le_iff (monotone_cdf (μ := μ)) (fun y => (cdf μ).right_continuous y)
    (cdf_sublevel_nonempty_bddBelow μ hα0 hα1).1 (cdf_sublevel_nonempty_bddBelow μ hα0 hα1).2

/-- **The explicit constants attain the level exactly.** The one-sided test with threshold
`critC μ α` and boundary weight `critGamma μ α` has size exactly `α`, and the weight is a
probability. Same computation as `QuantileFunction.exists_critical_constants`, carried out
for the *named* constants rather than existentially. -/
private lemma critical_constants_explicit (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    0 ≤ critGamma μ α ∧ critGamma μ α ≤ 1 ∧
      (μ {x : ℝ | critC μ α < x}).toReal
        + critGamma μ α * (μ {x : ℝ | x = critC μ α}).toReal = α := by
  have hmono : Monotone (⇑(cdf μ)) := monotone_cdf (μ := μ)
  set C := critC μ α with hCdef
  set L := Function.leftLim (⇑(cdf μ)) C with hLdef
  have hA : 1 - α ≤ cdf μ C := (critC_le_iff μ hα0 hα1 C).mp le_rfl
  have hB : ∀ y, y < C → cdf μ y < 1 - α := by
    intro y hy
    by_contra h
    exact absurd ((critC_le_iff μ hα0 hα1 y).mpr (not_lt.mp h)) (not_le.mpr hy)
  have hLle : L ≤ cdf μ C := Monotone.leftLim_le hmono le_rfl
  have hLbound : L ≤ 1 - α := by
    have htend : Filter.Tendsto (⇑(cdf μ)) (nhdsWithin C (Set.Iio C)) (nhds L) :=
      hmono.tendsto_leftLim C
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hB y hy).le
  have hg : (μ {x : ℝ | C < x}).toReal = 1 - cdf μ C := by
    have hIoi := (cdf μ).measure_Ioi (tendsto_cdf_atTop μ) C
    rw [measure_cdf] at hIoi
    have hset : {x : ℝ | C < x} = Set.Ioi C := rfl
    rw [hset, hIoi, ENNReal.toReal_ofReal (by linarith [cdf_le_one (μ := μ) C])]
  have hj : (μ {x : ℝ | x = C}).toReal = cdf μ C - L := by
    have hsing := (cdf μ).measure_singleton C
    rw [measure_cdf] at hsing
    have hset : {x : ℝ | x = C} = {C} := by ext x; simp
    rw [hset, hsing, ENNReal.toReal_ofReal (by linarith [hLle])]
  have hgle : 1 - cdf μ C ≤ α := by linarith [hA]
  have hgnn : 0 ≤ 1 - cdf μ C := by linarith [cdf_le_one (μ := μ) C]
  have hjnn : 0 ≤ cdf μ C - L := by linarith [hLle]
  have hαle : α ≤ (1 - cdf μ C) + (cdf μ C - L) := by linarith [hLbound]
  have hγ : critGamma μ α = (α - (1 - cdf μ C)) / (cdf μ C - L) := by
    rw [critGamma, hg, hj]
  rcases eq_or_lt_of_le hjnn with hj0 | hjpos
  · -- no atom: the size is already exactly `α` and the weight is `0`
    have hval : (1 - cdf μ C) = α := le_antisymm hgle (by linarith [hαle, hj0])
    have hγ0 : critGamma μ α = 0 := by rw [hγ, ← hj0, div_zero]
    refine ⟨by rw [hγ0], by rw [hγ0]; norm_num, ?_⟩
    rw [hg, hj, hγ0, hval]
    ring
  · refine ⟨by rw [hγ]; exact div_nonneg (by linarith [hgle]) (le_of_lt hjpos), ?_, ?_⟩
    · rw [hγ, div_le_one hjpos]; linarith [hαle]
    · rw [hg, hj, hγ, div_mul_cancel₀ _ (ne_of_gt hjpos)]; ring

/-- The distribution function of a Markov kernel is measurable in the conditioning variable,
for each fixed argument. -/
private lemma measurable_cdf_kernel (κ : Kernel Ξ ℝ) [IsMarkovKernel κ] (x : ℝ) :
    Measurable fun t => cdf (κ t) x := by
  simp only [cdf_eq_real, measureReal_def]
  exact ENNReal.measurable_toReal.comp (κ.measurable_coe measurableSet_Iic)

/-- The one-sided conditional test integrates to `size = tail + weight · atom`. -/
private lemma integral_condOneSidedTest (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (C₀ γ₀ : Ξ → ℝ) (t : Ξ) :
    ∫ u, condOneSidedTest C₀ γ₀ (u, t) ∂μ
      = (μ {x : ℝ | C₀ t < x}).toReal + γ₀ t * (μ {x : ℝ | x = C₀ t}).toReal := by
  have hs₁ : MeasurableSet {x : ℝ | C₀ t < x} := measurableSet_Ioi
  have hs₂ : MeasurableSet {x : ℝ | x = C₀ t} := by
    have : {x : ℝ | x = C₀ t} = {C₀ t} := by ext x; simp
    rw [this]; exact measurableSet_singleton _
  have hfun : (fun u => condOneSidedTest C₀ γ₀ (u, t))
      = fun u => ({x : ℝ | C₀ t < x}.indicator (fun _ => (1 : ℝ)) u
          + γ₀ t * {x : ℝ | x = C₀ t}.indicator (fun _ => (1 : ℝ)) u) := by
    funext u
    simp only [condOneSidedTest]
    by_cases h1 : C₀ t < u
    · have hm1 : u ∈ {x : ℝ | C₀ t < x} := h1
      have hn2 : u ∉ {x : ℝ | x = C₀ t} := by
        simp only [Set.mem_setOf_eq]; linarith
      rw [if_pos h1, Set.indicator_of_mem hm1, Set.indicator_of_notMem hn2]
      ring
    · have hn1 : u ∉ {x : ℝ | C₀ t < x} := h1
      rw [if_neg h1, Set.indicator_of_notMem hn1]
      by_cases h2 : u = C₀ t
      · have hm2 : u ∈ {x : ℝ | x = C₀ t} := h2
        rw [if_pos h2, Set.indicator_of_mem hm2]
        ring
      · have hn2 : u ∉ {x : ℝ | x = C₀ t} := h2
        rw [if_neg h2, Set.indicator_of_notMem hn2]
        ring
  rw [hfun, integral_add ((integrable_const (1 : ℝ)).indicator hs₁)
    (((integrable_const (1 : ℝ)).indicator hs₂).const_mul _), integral_const_mul,
    integral_indicator_const _ hs₁, integral_indicator_const _ hs₂]
  simp [measureReal_def]

/-- **Existence of measurable conditional constants (one-sided case).**

There is a measurable choice of critical value `C₀(t)` and randomization probability `γ₀(t)`
achieving conditional size `α` on the surface `T = t`, for almost every `t`.

Construction: with `F_t(u) = P_{θ₀}{U ≤ u ∣ t}` the conditional distribution function (the
`cdf` of the Markov kernel `condDistrib U T (P p₀)` evaluated at `t`), the size equation
reads `[1 − F_t(C)] + γ·[F_t(C) − F_t(C−)] = α`, solved by the conditional quantile
`C₀(t) = inf {u | F_t(u) ≥ 1 − α}` (`critC`) together with the matching interpolation weight
`γ₀(t) = (α − P_t(C₀(t), ∞)) / P_t{C₀(t)}` (`critGamma`; the junk value `x / 0 = 0` is the
correct one, since with no atom the tail already has mass exactly `α`).

The two measurability steps are, in this proof, both cheap, and *no* joint measurability of
`(u, t) ↦ F_t(u)` is needed:

* `C₀` is measurable because its sublevel sets are superlevel sets of a fixed-argument CDF:
  `C₀(t) ≤ x ↔ 1 − α ≤ F_t(x)` (the Galois property `quantile_le_iff`, here `critC_le_iff`),
  and `t ↦ F_t(x) = (κ t (Iic x)).toReal` is measurable for each fixed `x` because `κ` is a
  kernel;
* the tail and the atom at the *varying* threshold `C₀(t)` are measurable because
  `{(t,u) | C₀(t) < u}` and `{(t,u) | u = C₀(t)}` are measurable subsets of the product and
  a kernel evaluated on the sections of a measurable set is measurable
  (`Kernel.measurable_kernel_prodMk_left`).

The conclusion is in fact obtained for *every* `t`, not just almost every `t`: the
conditional laws are probability measures for every `t` since `condDistrib` is a Markov
kernel. Neither the exponential-family form `hUT` nor the measurability of `U` and `T` is
used; they are kept in the signature as stated. -/
theorem exists_measurable_conditional_constants
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {α : ℝ} {p₀ : ℝ × Ξ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ p, IsProbabilityMeasure (P p)]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT: the reference parameter belongs to the parameter set
    (hp₀ : p₀ ∈ Ω)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C₀ γ₀ : Ξ → ℝ, Measurable C₀ ∧ Measurable γ₀ ∧
      (∀ t, γ₀ t ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ᵐ t ∂((P p₀).map T),
        ∫ u, condOneSidedTest C₀ γ₀ (u, t) ∂(condDistrib U T (P p₀) t) = α := by
  classical
  set κ : Kernel Ξ ℝ := condDistrib U T (P p₀) with hκ
  -- the critical value is measurable because its sublevel sets are CDF superlevel sets
  have hC₀m : Measurable fun t => critC (κ t) α := by
    refine measurable_of_Iic fun x => ?_
    have hset : (fun t => critC (κ t) α) ⁻¹' Set.Iic x = {t | 1 - α ≤ cdf (κ t) x} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
      exact critC_le_iff (κ t) hα₀ hα₁ x
    rw [hset]
    exact measurableSet_le measurable_const (measurable_cdf_kernel κ x)
  -- the tail and the atom at a *varying* threshold are measurable, by the joint
  -- measurability of a kernel on sections of a measurable set of the product
  have htail : Measurable fun t => (κ t {x : ℝ | critC (κ t) α < x}).toReal :=
    ENNReal.measurable_toReal.comp (Kernel.measurable_kernel_prodMk_left
      (measurableSet_lt (hC₀m.comp measurable_fst) measurable_snd))
  have hatom : Measurable fun t => (κ t {x : ℝ | x = critC (κ t) α}).toReal :=
    ENNReal.measurable_toReal.comp (Kernel.measurable_kernel_prodMk_left
      (measurableSet_eq_fun measurable_snd (hC₀m.comp measurable_fst)))
  refine ⟨fun t => critC (κ t) α, fun t => critGamma (κ t) α, hC₀m, ?_, ?_, ?_⟩
  · simp only [critGamma]
    exact (measurable_const.sub htail).div hatom
  · exact fun t => ⟨(critical_constants_explicit (κ t) hα₀ hα₁).1,
      (critical_constants_explicit (κ t) hα₀ hα₁).2.1⟩
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [integral_condOneSidedTest (κ t) _ _ t]
    exact (critical_constants_explicit (κ t) hα₀ hα₁).2.2

/-! ## Reduction to canonical form -/

/-- Reparametrization of the parameter of interest: `(θ, ϑ) ↦ (a₀θ + ⟪a, ϑ⟫, ϑ)`. -/
def reparamUT (a₀ : ℝ) (a : Ξ) : ℝ × Ξ → ℝ × Ξ :=
  fun p => (a₀ * p.1 + ⟪a, p.2⟫_ℝ, p.2)

/-- Inverse reparametrization `(θ*, ϑ) ↦ ((θ* − ⟪a, ϑ⟫)/a₀, ϑ)`; for `a₀ = 0` it degenerates
to the junk value `0` in the first coordinate. -/
noncomputable def reparamUTInv (a₀ : ℝ) (a : Ξ) : ℝ × Ξ → ℝ × Ξ :=
  fun q => ((q.1 - ⟪a, q.2⟫_ℝ) / a₀, q.2)

/-- The matching transformation of the sufficient statistic: `(u, t) ↦ (u/a₀, t − (u/a₀)·a)`;
for `a₀ = 0` it degenerates to the junk value `(0, t)`. -/
noncomputable def statTransformUT (a₀ : ℝ) (a : Ξ) : ℝ × Ξ → ℝ × Ξ :=
  fun z => (z.1 / a₀, z.2 - (z.1 / a₀) • a)

/-- **The exponent identity behind the reduction to canonical form.**

`θ·u + ⟪ϑ, t⟫ = (a₀θ + ⟪a, ϑ⟫)·(u/a₀) + ⟪ϑ, t − (u/a₀)·a⟫`: the canonical exponent is
unchanged when the parameter of interest is replaced by the linear combination
`θ* = a₀θ + ⟪a, ϑ⟫` and the statistic by `U* = U/a₀`, `T* = T − (U/a₀)·a`. -/
theorem inner_exponent_reparam {a₀ : ℝ} (a : Ξ) (θ : ℝ) (ϑ : Ξ) (u : ℝ) (t : Ξ)
    -- USER-INPUT: the coefficient of the parameter of interest is nonzero
    (ha₀ : a₀ ≠ 0) :
    θ * u + ⟪ϑ, t⟫_ℝ
      = (a₀ * θ + ⟪a, ϑ⟫_ℝ) * (u / a₀) + ⟪ϑ, t - (u / a₀) • a⟫_ℝ := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_comm a ϑ]
  field_simp
  ring

/-- Push-forward of a `withDensity` along a measurable map whose density is a pull-back:
if the density on the source is `D ∘ S`, then `S`-image of the tilt is the `D`-tilt of the
`S`-image. No injectivity of `S` is needed — only that the source density factors through
`S`. Change-of-variables for `withDensity`, proved set by set with `setLIntegral_map`. -/
private lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {S : α → β} {D : β → ℝ≥0∞} (hS : Measurable S) (hD : Measurable D) :
    (μ.withDensity fun z => D (S z)).map S = (μ.map S).withDensity D := by
  ext B hB
  rw [Measure.map_apply hS hB, withDensity_apply _ (hS hB), withDensity_apply _ hB,
    setLIntegral_map hB hD hS]

/-- Measurability of the canonical exponential density on `ℝ × Ξ` (local copy of the
namesake in `ConditionalExpFamily`, which is `private` to that file). -/
private lemma measurable_canonicalDensity' [OpensMeasurableSpace Ξ] (c θ : ℝ) (ϑ : Ξ) :
    Measurable fun z : ℝ × Ξ => ENNReal.ofReal (c * Real.exp (θ * z.1 + ⟪ϑ, z.2⟫_ℝ)) := by
  have h : Measurable fun z : ℝ × Ξ => ⟪ϑ, z.2⟫_ℝ :=
    ((innerSL ℝ ϑ).continuous.measurable).comp measurable_snd
  exact (((measurable_const.mul measurable_fst).add h).exp.const_mul c).ennreal_ofReal

/-- **Reduction to canonical form.**

A canonical `(U, T)` family is again canonical after the change of parameter of interest
`θ* = a₀θ + ⟪a, ϑ⟫` (`a₀ ≠ 0`), with statistic `U* = U/a₀`, `T* = T − (U/a₀)·a` and base
measure the image of `ν` under the same transformation. Consequently the four optimality
theorems above apply verbatim to hypotheses about `θ*`.

The proof is the change of variables `map_withDensity_comp` along `S = statTransformUT a₀ a`
— whose defining property is exactly `inner_exponent_reparam`, i.e. the reparametrized
density pulled back along `S` is the original density — together with `map_map` to move `S`
past the statistic. The measurability of `(U, T)` is *not* a hypothesis, and is not needed:
if it fails, the left-hand side is the zero measure by `Measure.map_of_not_aemeasurable`, and
so is the right-hand side, because `S` has a measurable left inverse `(v,s) ↦ (a₀v, s + v·a)`
(so `S ∘ (U,T)` is no more measurable than `(U,T)`) and the change of variables identifies
the right-hand side with the `S`-image of `(P p).map (U,T) = 0`.

**FLAGGED SIGNATURE AMENDMENT.** The instances `[BorelSpace Ξ]` and
`[SecondCountableTopology Ξ]` were *added*. They are what makes the shear
`S : (u,t) ↦ (u/a₀, t − (u/a₀)·a)` — a continuous map `ℝ × Ξ → ℝ × Ξ` — measurable: the
frozen `[MeasurableSpace Ξ]` is unrelated to the topology of `Ξ`, and even with
`[BorelSpace Ξ]` alone the product σ-algebra of `ℝ × Ξ` need not contain the Borel sets of
the product topology, which is what second countability supplies (`Prod.borelSpace`). Both
hold for every intended instantiation `Ξ = EuclideanSpace ℝ (Fin k)`. Nothing else in the
statement changes. -/
theorem isCanonicalUT_reparam
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {a₀ : ℝ} {a : Ξ}
    -- LEAN-ONLY (AMENDMENT): the σ-algebra of `Ξ` is the Borel one and `Ξ` is second
    -- countable, so that the continuous shear `statTransformUT a₀ a` is measurable
    [BorelSpace Ξ] [SecondCountableTopology Ξ]
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT: the coefficient of the parameter of interest is nonzero
    (ha₀ : a₀ ≠ 0) :
    IsCanonicalUT (fun q => P (reparamUTInv a₀ a q)) (reparamUT a₀ a '' Ω)
      (fun x => U x / a₀) (fun x => T x - (U x / a₀) • a)
      (ν.map (statTransformUT a₀ a)) (fun q => C (reparamUTInv a₀ a q)) := by
  -- the shear and its left inverse are continuous, hence measurable
  have hScont : Continuous (statTransformUT a₀ a) := by
    unfold statTransformUT; fun_prop
  have hS : Measurable (statTransformUT a₀ a) := hScont.measurable
  have hS' : Measurable fun w : ℝ × Ξ => (a₀ * w.1, w.2 + w.1 • a) :=
    (by fun_prop : Continuous fun w : ℝ × Ξ => (a₀ * w.1, w.2 + w.1 • a)).measurable
  have hSS' : ∀ z : ℝ × Ξ,
      (fun w : ℝ × Ξ => (a₀ * w.1, w.2 + w.1 • a)) (statTransformUT a₀ a z) = z := by
    intro z
    have h1 : a₀ * (z.1 / a₀) = z.1 := by field_simp
    have h2 : z.2 - (z.1 / a₀) • a + (z.1 / a₀) • a = z.2 := by abel
    simp only [statTransformUT, h1, h2]
  intro q hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hinv : reparamUTInv a₀ a (reparamUT a₀ a p) = p := by
    have h1 : (a₀ * p.1 + ⟪a, p.2⟫_ℝ - ⟪a, p.2⟫_ℝ) / a₀ = p.1 := by
      rw [add_sub_cancel_right]; field_simp
    simp only [reparamUTInv, reparamUT, h1]
  simp only [hinv]
  -- the reparametrized density pulled back along the shear is the original density
  have hD : Measurable fun z : ℝ × Ξ => ENNReal.ofReal (C p *
      Real.exp ((reparamUT a₀ a p).1 * z.1 + ⟪(reparamUT a₀ a p).2, z.2⟫_ℝ)) :=
    measurable_canonicalDensity' _ _ _
  have hdens : ∀ z : ℝ × Ξ, ENNReal.ofReal (C p *
      Real.exp ((reparamUT a₀ a p).1 * (statTransformUT a₀ a z).1
        + ⟪(reparamUT a₀ a p).2, (statTransformUT a₀ a z).2⟫_ℝ))
      = ENNReal.ofReal (C p * Real.exp (p.1 * z.1 + ⟪p.2, z.2⟫_ℝ)) := by
    intro z
    simp only [reparamUT, statTransformUT]
    rw [← inner_exponent_reparam a p.1 p.2 z.1 z.2 ha₀]
  have hkey : (ν.map (statTransformUT a₀ a)).withDensity (fun z => ENNReal.ofReal (C p *
        Real.exp ((reparamUT a₀ a p).1 * z.1 + ⟪(reparamUT a₀ a p).2, z.2⟫_ℝ)))
      = ((P p).map fun x => (U x, T x)).map (statTransformUT a₀ a) := by
    rw [hUT p hp, ← map_withDensity_comp ν hS hD]
    congr 1
    congr 1
    funext z
    exact hdens z
  rw [hkey]
  -- move the shear past the statistic; both sides vanish if the statistic is not measurable
  by_cases hf : AEMeasurable (fun x => (U x, T x)) (P p)
  · rw [AEMeasurable.map_map_of_aemeasurable hS.aemeasurable hf]
    rfl
  · have hf' : ¬ AEMeasurable (fun x => (U x / a₀, T x - (U x / a₀) • a)) (P p) := by
      intro hc
      have hcomp : ((fun w : ℝ × Ξ => (a₀ * w.1, w.2 + w.1 • a)) ∘
          fun x => (U x / a₀, T x - (U x / a₀) • a)) = fun x => (U x, T x) := by
        funext x
        exact hSS' (U x, T x)
      have := hS'.comp_aemeasurable hc
      rw [hcomp] at this
      exact hf this
    rw [Measure.map_of_not_aemeasurable hf, Measure.map_of_not_aemeasurable hf']
    simp

end StatLean.HypothesisTesting
