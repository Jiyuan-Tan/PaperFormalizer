module
public import StatLean.AsymptoticStatistics.Asymptotics.ZEstimator
public import StatLean.AsymptoticStatistics.EmpiricalProcess.RandomFunctions
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import StatLean.AsymptoticStatistics.ForMathlib.IidWLLN
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterSlutsky
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-!
# Z-estimator semiparametric efficiency from Taylor and Donsker conditions

This file derives the `asympLinear_25_54` condition of `EfficientScoreEqAssumptions`
from the hypotheses in the book: a Donsker class containing the estimated efficient
scores w.p.a.1 (vdV thm:25.54 hyp 6), the L²-consistency of the estimated
score (eq:25.53), the no-bias condition (eq:25.52), the estimating-equation
`√n · 𝕡_n ℓ̃_{θ̂_n,η̂_n} →_P 0`, the consistency of `θ̂_n`, and the
DQM-in-θ Taylor regularity for `θ ↦ ℓ̃_{θ,η}`.

Strong-regularity / Taylor route. The book's proof (vdV §25.5) decomposes
the residual into a random-index empirical-process step closed by Lemma 19.24,
an algebraic rewrite using the no-bias condition (eq:25.52) and the estimating
equation, and a second-order Taylor decomposition of
`(P_{θ̂_n,η} − P) ℓ̃_{θ̂_n,η̂_n}` via the DQM-in-θ Taylor identity
(vdV §7.2 Theorem 7.2 + Lemma 7.6).

Reference: vdV §25.5, eq:25.52 (no-bias), eq:25.53 (Donsker / regularity),
thm:25.54 (Z-estimator semiparametric efficiency); Lemma 19.24; vdV §7.2
Theorem 7.2 + Lemma 7.6 (DQM-Taylor). Main declarations:
`zEstimator_asympLinear_of_taylor` and `toEfficientScoreEqAssumptions`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal Function

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.Asymptotics.ZEstimator
open AsymptoticStatistics.EmpiricalProcess

variable {Ω : Type} [MeasurableSpace Ω]

/-- The integral functional `integralL2 P` evaluated at any `f : Lp ℝ 2 P`
agrees with the ordinary integral `∫ (f : Ω → ℝ) ∂P`. Variant of the
bridge stated piecewise elsewhere for `MemLp.toLp` outputs; this version
takes the Lp element directly. -/
private lemma integralL2_eq_integral
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    integralL2 P f = ∫ ω, (f : Ω → ℝ) ω ∂P := by
  change ⟪oneL2 P, f⟫_ℝ = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have h_one_ae : ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  filter_upwards [h_one_ae] with a ha
  have hcomm :
      ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a, (f : Ω → ℝ) a⟫_ℝ
        = (f : Ω → ℝ) a * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
  rw [hcomm, ha]
  ring

/-- Mean-zero property of `↥(L2ZeroMean P)` elements expressed at the
`Ω → ℝ` representative level: any element of `L2ZeroMean P` has integral
zero under `P`. -/
private lemma L2ZeroMean.integral_coeFn_eq_zero
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ↥(L2ZeroMean P)) :
    ∫ ω, (((f : Lp ℝ 2 P)) : Ω → ℝ) ω ∂P = 0 := by
  -- `f.2` is `(f : Lp ℝ 2 P) ∈ L2ZeroMean P`, defeq to membership in
  -- `LinearMap.ker (integralL2 P).toLinearMap`. Stating it explicitly in
  -- kernel form lets `LinearMap.mem_ker` rewrite to the equation form.
  have h_in_ker : (f : Lp ℝ 2 P) ∈
      LinearMap.ker (integralL2 P).toLinearMap := f.2
  rw [LinearMap.mem_ker] at h_in_ker
  rw [← integralL2_eq_integral]
  exact h_in_ker

/-- **`(1/n) · Σ ℓ̇ + Ĩ →_P 0`.**

Application of `iid_lln_in_prob_l1` to `score_l_dot ∈ L²(P) ⊂ L¹(P)`,
combined with the Bartlett identity `E_P[ℓ̇] = -Ĩ`.

Specifically: `(1/n)·Σ ℓ̇(Xᵢ) - ∫ℓ̇ ∂P →_P 0` gives `(1/n)·Σ ℓ̇(Xᵢ) →_P -Ĩ`,
and equivalently `(1/n)·Σ ℓ̇(Xᵢ) + Ĩ →_P 0`. Mirrors
`score_l_dot_avg_plus_info_oP`. -/
private lemma score_l_dot_avg_plus_info_oP
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {score_l_dot : Lp ℝ 2 P}
    (h_bartlett :
      ∫ ω, (score_l_dot : Ω → ℝ) ω ∂P = -efficientInformation S_θ T_nuis v) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
                   + efficientInformation S_θ T_nuis v|})
      atTop (𝓝 0) := by
  -- Apply iid_lln_in_prob_l1 with f = score_l_dot ∈ L¹.
  -- Bridge: |(1/n)Σℓ̇ + Ĩ| = |(1/n)Σℓ̇ - (-Ĩ)| = |(1/n)Σℓ̇ - ∫ℓ̇ ∂P| (h_bartlett).
  have hf_int : Integrable (fun ω => (score_l_dot : Ω → ℝ) ω) P :=
    (Lp.memLp score_l_dot).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_lln := iid_lln_in_prob_l1 (fun ω => (score_l_dot : Ω → ℝ) ω) hf_int
  intro ε hε
  -- Rewrite the goal sets to match h_lln's form
  have h_set_eq : ∀ n : ℕ,
      {X : Fin n → Ω |
        ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
                 + efficientInformation S_θ T_nuis v|}
      = {X : Fin n → Ω |
          ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
                   - ∫ ω, (score_l_dot : Ω → ℝ) ω ∂P|} := by
    intro n
    ext X
    simp only [Set.mem_setOf_eq]
    rw [h_bartlett]
    constructor
    · intro h; convert h using 2; ring
    · intro h; convert h using 2; ring
  simp_rw [h_set_eq]
  exact h_lln ε hε

/-- Strong-regularity hypothesis bundle for the Z-estimator discharge.

Replaces the bundled `asympLinear_25_54` field of
`EfficientScoreEqAssumptions` with the book-level primitives of
vdV thm:25.54: a Donsker class for the estimated efficient scores,
L²-consistency of the score estimate, the no-bias condition, the
estimating equation, consistency of `θ̂_n`, and a DQM-in-θ Taylor
regularity hypothesis on the efficient score.

**Parameters** (in addition to the standard model identity):
- `score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ)` — the random function
  `(n, X) ↦ ℓ̃_{θ̂_n(X), η̂_n(X)}` viewed as a measurable element of
  `L²(P)` for each sample. This is determined by the nuisance estimator
  `η̂_n` and the model's score map.
- `score_truth : Ω → ℝ` — a measurable representative of
  `efficientScore S_θ T_nuis v` in `L²(P)`. Supplied as a separate
  parameter (rather than coerced from `↥(L2ZeroMean P)`) so that
  measurability and Donsker-class-membership conditions can be stated
  on a concrete function rather than an a.e.-equivalence class.
- `donsker_class : Set (Ω → ℝ)` — the P-Donsker class containing both
  `score_truth` and (with probability tending to 1) the random functions
  `score_func_seq n`.
- `score_l_dot : Lp ℝ 2 P` — the L²(P)-derivative `ℓ̇` of the map
  `θ ↦ ℓ̃_{θ,η}` at θ₀ (vdV §7.2 Lemma 7.6 derivative; consumed by the
  Taylor remainder bound).

Every field traces back to a primitive in vdV §25.5. See the docstring
on each field for the book reference.

Reference: vdV §25.5, thm:25.54; eq:25.52, eq:25.53 (book primitives);
Lemma 19.24.

The hypotheses are organized into three structures:
- `ZEstimatorTaylorCoreBase`: every field of vdV's thm:25.54 hypothesis
  set **except** the no-bias condition (25.52) **and** the
  estimating-equation rate (`score_eq`). These fields give Steps 3 and 4
  (Taylor-remainder Cauchy–Schwarz and the Bartlett LLN on `ℓ̇`). This is
  also the base for the explicit-bias variant of thm:25.59,
  which drops `score_eq` and reinstates it with an explicit bias residual.
- `ZEstimatorTaylorCore`: extends `Base` with `score_eq`. The
  hypothesis bundle for thm:25.54's Taylor-route AL conclusion and
  thm:25.59's bias=0 specialization.
- `ZEstimatorTaylorHyp`: extends `Core` with the `no_bias` field used in
  Steps 1 and 2 of vdV's Donsker argument.
-/
structure ZEstimatorTaylorCoreBase
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (estimator : ∀ n, (Fin n → Ω) → ℝ)
    (score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ))
    (score_truth : Ω → ℝ)
    (donsker_class : Set (Ω → ℝ))
    (score_l_dot : Lp ℝ 2 P)
    (θ₀ : ℝ) : Prop where
  /-- vdV §25.4: efficient information `Ĩ_{θ₀,η₀}` is positive. Required
  to invert `Ĩ` in the EIF formula `(1/Ĩ) • ℓ̃` and for the Z-estimator
  influence function to be well-defined. -/
  hI_pos : 0 < efficientInformation S_θ T_nuis v
  /-- The truth representative `score_truth` is measurable. Used in this
  to derive the explicit outer-probability tail used by
  `donsker_random_function_consistency_core`; that theorem itself does
  not require this measurability input. Trivially satisfied by any concrete
  `score_truth` constructed from a measurable model. -/
  truth_meas : Measurable score_truth
  /-- `score_truth` is in `L²(P)`. This is a hypothesis of Lemma 19.24 and
  is also used by the Taylor algebra and integrability
  arguments below. Holds for any efficient score by
  `score_l2 (efficientScore …)`. -/
  truth_memLp : MemLp score_truth 2 P
  /-- `score_truth` agrees `P`-a.e. with the abstract efficient score
  `efficientScore S_θ T_nuis v`, connecting the abstract L²₀(P) element
  to the measurable representative needed by Lemma 19.24. -/
  truth_aeEq :
    (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ)
      =ᵐ[P] score_truth
  /-- vdV thm:25.54 hyp 6: the truth `score_truth` belongs to the
  Donsker class. -/
  truth_in_donsker : score_truth ∈ donsker_class
  /-- vdV thm:25.54 hyp 6: the random function family is P-Donsker. -/
  is_donsker : IsPDonsker donsker_class P
  /-- `score_func_seq n` is jointly measurable in (sample, ω). This gives
  measurability in the Markov derivation of the explicit outer tail; it is not
  a hypothesis of Lemma 19.24 itself. -/
  score_func_meas : ∀ n,
    Measurable (fun p : (Fin n → Ω) × Ω => score_func_seq n p.1 p.2)
  /-- vdV thm:25.54 hyp 6 (w.p.a.1 form): for every n, the random
  function `score_func_seq n X` belongs to the Donsker class for every
  sample `X`. (The "w.p.a.1" weakening is folded into the always-true
  case here; the Donsker class may have to be enlarged to
  absorb measure-zero exceptions, which is standard Donsker-class
  practice.) -/
  score_func_in_donsker : ∀ n (X : Fin n → Ω), score_func_seq n X ∈ donsker_class
  /-- A sufficient form of vdV equation (25.53): the expected
  squared L²(P)-distance between `score_func_seq` and `score_truth` tends to
  zero under `Pⁿ`. Together with `score_l2_int`, it yields by Markov's
  inequality the explicit outer-probability tail required by
  `donsker_random_function_consistency_core`; the core does not consume an
  expectation hypothesis. -/
  score_l2_consistency :
    Tendsto (fun n =>
      ∫ X, (∫ x, (score_func_seq n X x - score_truth x) ^ 2 ∂P)
        ∂(Measure.pi (fun _ : Fin n => P)))
      atTop (𝓝 0)
  /-- Integrability of the squared L²-distance under `Pⁿ`. This condition
  supplies the integrability premise of
  `markov_distL2_tail`, from which `step1_random_index_oP` derives the
  outer-probability tail. It is not a hypothesis of Lemma 19.24 itself. -/
  score_l2_int : ∀ n, MeasureTheory.Integrable
    (fun X : Fin n → Ω => ∫ x, (score_func_seq n X x - score_truth x) ^ 2 ∂P)
    (Measure.pi (fun _ : Fin n => P))
  /-- vdV thm:25.54 hyp 5: `θ̂_n` is consistent for `θ₀` under `Pⁿ`. -/
  consistency : ∀ ε > 0, Tendsto
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω | ε ≤ |estimator n X - θ₀|})
    atTop (𝓝 0)
  /-- `estimator n` is measurable for every `n`. Required so that the
  `Pⁿ`-measure of sets carved out by `estimator n` (used for small-`n`
  initial-segment tightness) is well-defined as the Lebesgue
  measure rather than only the outer measure. Trivially holds for any
  concretely constructed Z-estimator. -/
  estimator_meas : ∀ n, Measurable (estimator n)
  /-- vdV §7.2 Theorem 7.2 + Lemma 7.6 (DQM-in-θ Taylor identity): the
  efficient score map `θ ↦ ℓ̃_{θ,η}` is L²(P)-differentiable at θ₀ with
  derivative `score_l_dot ∈ L²(P)`. Stated as a quantitative L²
  remainder estimate: for every ε > 0, there is a δ > 0 such that for
  all `|h| ≤ δ`,
  `‖ℓ̃_{θ₀+h,η} − ℓ̃_{θ₀,η} − h · ℓ̇‖_{L²(P)} ≤ ε · |h|`.

  Encoded here on the random sequence `score_func_seq` directly: the
  empirical L² Taylor remainder
  `Σᵢ (score_func_seq n X (X_i) − score_truth(X_i) − (estimator n X − θ₀)·ℓ̇(X_i))²`
  vanishes faster than `1/n` under `Pⁿ`. This is the form consumed by
  the residual decomposition (Step 3 of the proof). -/
  score_l2_taylor : ∀ ε > 0, Tendsto
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ ∑ i : Fin n,
          (score_func_seq n X (X i)
            - score_truth (X i)
            - (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) ^ 2})
    atTop (𝓝 0)
  /-- Semiparametric Bartlett identity: `E_P[ℓ̇] = -Ĩ`.

  Derived in vdV §7.2 by differentiating `E_{P_{θ,η}}[ℓ̃_{θ,η}] = 0` in
  θ. Mirrors the `score_l_dot_bartlett` field in `OneStepTaylorHyp` (the
  same primitive is needed in both discharge layers). -/
  score_l_dot_bartlett :
    ∫ ω, (score_l_dot : Ω → ℝ) ω ∂P = -efficientInformation S_θ T_nuis v

/-- vdV thm:25.54 / 25.59-bias=0 hypothesis bundle (Taylor route).

Extends `ZEstimatorTaylorCoreBase` with the estimating-equation rate
`score_eq`. These hypotheses imply Steps 5 and 6 and the asymptotic-linear
conclusion `zEstimator_asympLinear_of_taylor`. They also give the bias-zero
specialization of thm:25.59.

The explicit-bias variant of thm:25.59 takes `ZEstimatorTaylorCoreBase`
directly with bias-residual fields added, since `score_eq` is
incompatible with non-trivial bias (would force bias = o_P(1)). -/
structure ZEstimatorTaylorCore
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (estimator : ∀ n, (Fin n → Ω) → ℝ)
    (score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ))
    (score_truth : Ω → ℝ)
    (donsker_class : Set (Ω → ℝ))
    (score_l_dot : Lp ℝ 2 P)
    (θ₀ : ℝ) : Prop
    extends ZEstimatorTaylorCoreBase P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀ where
  /-- vdV thm:25.54 hyp 4: the Z-estimator solves the estimating equation
  up to `o_P(n^{-1/2})`:
  `√n · 𝕡_n ℓ̃_{θ̂_n(X), η̂_n(X)} = o_P(1)` under `Pⁿ`. -/
  score_eq : ∀ ε > 0, Tendsto
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ |(Real.sqrt n)⁻¹ *
              (∑ i : Fin n, score_func_seq n X (X i))|})
    atTop (𝓝 0)

/-- vdV thm:25.54 strong-regularity bundle (Taylor route).

Extends `ZEstimatorTaylorCore` with the no-bias condition (25.52). This field
is used by `step1_random_index_oP` and `step2_score_eq_to_no_bias` in vdV's
§25.5 Donsker argument; Steps 3–6 and `zEstimator_asympLinear_of_taylor` do
not use it.

Reference: vdV §25.5, thm:25.54; eq:25.52 (the no-bias condition added
by this extension).
-/
structure ZEstimatorTaylorHyp
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (estimator : ∀ n, (Fin n → Ω) → ℝ)
    (score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ))
    (score_truth : Ω → ℝ)
    (donsker_class : Set (Ω → ℝ))
    (score_l_dot : Lp ℝ 2 P)
    (θ₀ : ℝ) : Prop
    extends ZEstimatorTaylorCore P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀ where
  /-- vdV eq:25.52 (no-bias condition):
  `√n · P_{θ̂_n,η} ℓ̃_{θ̂_n,η̂_n} = o_P(1 + √n‖θ̂_n − θ₀‖)`.

  Encoded here as the tightest local form: `√n · ∫ score_func_seq n X dP
  →_P 0` under `Pⁿ`. (The `+ √n‖θ̂_n − θ₀‖` slack is absorbed by combining
  with the consistency hypothesis at proof time.) Concrete model files
  prove this from a model-specific bias control (vdV §25.5, eq:25.52). -/
  no_bias : ∀ ε > 0, Tendsto
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ |Real.sqrt n * (∫ x, score_func_seq n X x ∂P)|})
    atTop (𝓝 0)

section StepLemmas

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
variable {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
variable [T_nuis.HasOrthogonalProjection] {v : Θ}
variable {estimator : ∀ n, (Fin n → Ω) → ℝ}
variable {score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ)}
variable {score_truth : Ω → ℝ}
variable {donsker_class : Set (Ω → ℝ)}
variable {score_l_dot : Lp ℝ 2 P}
variable {θ₀ : ℝ}

/-- **Step 1 (random-index empirical-process bound).**

`G_n(score_func_seq n X) − G_n(score_truth) →_P 0` under `Pⁿ`, where
`G_n f X := √n · ((1/n) Σᵢ f(X_i) − ∫ f dP)` is the centred √n-scaled
empirical process (`EmpiricalProcess.empiricalProcess`).

Equivalent unrolled form: for every ε > 0,
`Pⁿ {X | ε ≤ |(1/√n) Σᵢ (score_func_seq n X (X_i) − score_truth(X_i))
                 − √n ∫ (score_func_seq n X − score_truth) dP|} → 0`.

**Proof strategy.** Derive the explicit outer-probability L² tail by applying
`markov_distL2_tail` to the random pair `score_func_seq` and the constant
function `score_truth`, then apply vdV Lemma 19.24
(`donsker_random_function_consistency_core`) at:
* `F := donsker_class`
* `f₀ := score_truth` with `truth_memLp`
* `f_hat := score_func_seq` (with `score_func_in_donsker` and the derived
  explicit outer tail).

The stronger `truth_meas`, `score_func_meas`, `score_l2_int`, and
`score_l2_consistency` fields are used only to derive this Markov bound; they
are not hypotheses of Lemma 19.24 itself.

The bridging step from Lem 19.24's `(Ξ, μ, X : ℕ → Ξ → Ω)` setup to the
`Pⁿ := Measure.pi (fun _ : Fin n => P)` setup uses the iid product
extension: take `Ξ := ℕ → Ω`, `μ := Measure.pi (fun _ : ℕ => P)`,
`X i ξ := ξ i`, then the joint law of `(X 0, …, X_{n-1})` under `μ` is
exactly `Pⁿ`. The conclusion of Lem 19.24 (probability under `μ`)
transfers via this projection. -/
private lemma step1_random_index_oP
    (h : ZEstimatorTaylorHyp P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |(Real.sqrt n)⁻¹ *
                  (∑ i : Fin n,
                    (score_func_seq n X (X i) - score_truth (X i)))
                - Real.sqrt n
                  * (∫ ω, (score_func_seq n X ω - score_truth ω) ∂P)|})
      atTop (𝓝 0) := by
  -- Bridge `Pⁿ` to `μ := infinitePi (const P)` via `pi_const_eq_infinitePi_map`,
  -- then apply Lem 19.24 (`donsker_random_function_consistency_core`) at:
  --   Ξ := ℕ → Ω, μ := infinitePi (const P), X i ξ := ξ i,
  --   f_hat n ξ := score_func_seq n (fun i : Fin n => ξ i.val),
  --   f₀ := score_truth.
  intro ε hε
  set μ : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P) with hμ_def
  -- Iid hypotheses for Lem 19.24.
  have hX_meas : ∀ i : ℕ, Measurable (fun ξ : ℕ → Ω => ξ i) := fun i =>
    measurable_pi_apply i
  -- Mutual independence of evaluations under `infinitePi` (the
  -- strengthened `IsAsymptoticallyEquicontinuous` predicate consumes
  -- `iIndepFun` directly, no pairwise downgrade needed).
  have h_iIndep : ProbabilityTheory.iIndepFun
      (fun (i : ℕ) (ξ : ℕ → Ω) => ξ i) μ := by
    have := ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => P)
      (X := fun _ : ℕ => id) (mX := fun _ => measurable_id)
    simpa using this
  -- Joint law of every coordinate is `P` under `μ` via `infinitePi_map_eval`.
  have hX_law : μ.map (fun ξ : ℕ → Ω => ξ 0) = P := by
    have h_eval : (fun ξ : ℕ → Ω => ξ 0) = Function.eval (0 : ℕ) := rfl
    rw [h_eval, hμ_def, MeasureTheory.Measure.infinitePi_map_eval]
  have hX_idem : ∀ i : ℕ, ProbabilityTheory.IdentDistrib
      (fun ξ : ℕ → Ω => ξ i) (fun ξ : ℕ → Ω => ξ 0) μ μ := by
    intro i
    refine ⟨(hX_meas i).aemeasurable, (hX_meas 0).aemeasurable, ?_⟩
    have h0 : μ.map (fun ξ : ℕ → Ω => ξ 0) = P := hX_law
    have hi : μ.map (fun ξ : ℕ → Ω => ξ i) = P := by
      have h_eval : (fun ξ : ℕ → Ω => ξ i) = Function.eval (i : ℕ) := rfl
      rw [h_eval, hμ_def, MeasureTheory.Measure.infinitePi_map_eval]
    rw [hi, h0]
  -- The random function family.
  set f_hat : ℕ → (ℕ → Ω) → (Ω → ℝ) := fun n ξ =>
    score_func_seq n (fun i : Fin n => ξ i.val) with hf_hat_def
  -- Joint measurability of `f_hat n` from `h.score_func_meas`.
  have h_proj_meas : ∀ n : ℕ,
      Measurable (fun ξ : ℕ → Ω => fun i : Fin n => ξ i.val) := by
    intro n
    refine measurable_pi_lambda _ (fun _ => ?_)
    exact measurable_pi_apply _
  have hf_hat_meas : ∀ n, Measurable (Function.uncurry (f_hat n)) := by
    intro n
    -- Function.uncurry (f_hat n) : (ℕ → Ω) × Ω → ℝ,
    --   = (ξ, ω) ↦ score_func_seq n (proj_n ξ) ω
    --   = (h.score_func_meas n) ∘ (proj_n × id)
    have hcomp : Function.uncurry (f_hat n)
        = (fun p : (Fin n → Ω) × Ω => score_func_seq n p.1 p.2)
            ∘ (fun p : (ℕ → Ω) × Ω => ((fun i : Fin n => p.1 i.val), p.2)) := by
      funext p; rfl
    rw [hcomp]
    refine (h.score_func_meas n).comp ?_
    refine Measurable.prodMk ?_ measurable_snd
    exact (h_proj_meas n).comp measurable_fst
  have hf_hat_range : ∀ n ξ, f_hat n ξ ∈ donsker_class := fun n ξ =>
    h.score_func_in_donsker n _
  -- L²-consistency + integrability under μ — derived from
  -- `h.score_l2_consistency` and `h.score_l2_int` (under Pⁿ) via
  -- `pi_const_eq_infinitePi_map`.
  have h_inner_strMeas : ∀ n : ℕ, StronglyMeasurable
      (fun X : Fin n → Ω =>
        ∫ x, (score_func_seq n X x - score_truth x) ^ 2 ∂P) := by
    intro n
    have h_joint : Measurable (fun p : (Fin n → Ω) × Ω =>
        (score_func_seq n p.1 p.2 - score_truth p.2) ^ 2) :=
      ((h.score_func_meas n).sub
        (h.truth_meas.comp measurable_snd)).pow_const 2
    exact h_joint.stronglyMeasurable.integral_prod_right'
  have h_l2_eq : ∀ n : ℕ,
      ∫ ξ, (∫ x, (f_hat n ξ x - score_truth x) ^ 2 ∂P) ∂μ
      = ∫ X, (∫ x, (score_func_seq n X x - score_truth x) ^ 2 ∂P)
          ∂(Measure.pi (fun _ : Fin n => P)) := by
    intro n
    rw [AsymptoticStatistics.pi_const_eq_infinitePi_map P n,
      MeasureTheory.integral_map (h_proj_meas n).aemeasurable
        (h_inner_strMeas n).aestronglyMeasurable]
  have h_l2_μ : Tendsto (fun n : ℕ =>
      ∫ ξ, (∫ x, (f_hat n ξ x - score_truth x) ^ 2 ∂P) ∂μ) atTop (𝓝 0) := by
    refine (Tendsto.congr (fun n => (h_l2_eq n).symm) ?_)
    exact h.score_l2_consistency
  -- Integrability under μ — transport `h.score_l2_int` along
  -- `pi_const_eq_infinitePi_map`.
  have h_l2_int_μ : ∀ n, MeasureTheory.Integrable
      (fun ξ : ℕ → Ω => ∫ x, (f_hat n ξ x - score_truth x) ^ 2 ∂P) μ := by
    intro n
    have h_pi := h.score_l2_int n
    rw [AsymptoticStatistics.pi_const_eq_infinitePi_map P n] at h_pi
    exact (MeasureTheory.integrable_map_measure
      (h_inner_strMeas n).aestronglyMeasurable
      (h_proj_meas n).aemeasurable).mp h_pi
  -- Derive the explicit outer-probability tail from the
  -- expectation and integrability assumptions by Markov's inequality.
  set ghat : ℕ → (ℕ → Ω) → (Ω → ℝ) := fun _ _ => score_truth with hghat_def
  have hghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)) := by
    intro n
    exact h.truth_meas.comp measurable_snd
  have h_outer_tail : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      μ.outerMeasureStar {ξ | δ < distL2 P (f_hat n ξ) score_truth})
      atTop (𝓝 0) := by
    intro δ hδ
    have htail : Tendsto (fun n =>
        μ {ξ | δ ≤ distL2 P (f_hat n ξ) (ghat n ξ)}) atTop (𝓝 0) := by
      exact markov_distL2_tail (F := donsker_class) μ f_hat ghat
        hf_hat_meas hghat_meas
        (fun n => by simpa [hghat_def] using h_l2_int_μ n)
        (by simpa [hghat_def] using h_l2_μ) hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => ?_)
    calc
      μ.outerMeasureStar {ξ | δ < distL2 P (f_hat n ξ) score_truth}
          ≤ μ.outerMeasureStar {ξ | δ ≤ distL2 P (f_hat n ξ) score_truth} :=
            outerMeasureStar_mono μ (by
              intro ξ hξ
              change δ < distL2 P (f_hat n ξ) score_truth at hξ
              change δ ≤ distL2 P (f_hat n ξ) score_truth
              exact le_of_lt hξ)
      _ ≤ μ {ξ | δ ≤ distL2 P (f_hat n ξ) score_truth} :=
        AsymptoticStatistics.outerMeasureStar_le_measure μ _
  -- Apply Lem 19.24 at η := ε/2.
  have h_lem19_24 := donsker_random_function_consistency_core
    (F := donsker_class) (P := P) h.is_donsker
    score_truth h.truth_memLp
    (Ξ := ℕ → Ω) (μ := μ)
    (X := fun (i : ℕ) (ξ : ℕ → Ω) => ξ i) hX_meas h_iIndep hX_idem hX_law
    f_hat hf_hat_range h_outer_tail
    (ε / 2) (by linarith)
  -- Translate the conclusion under μ to the conclusion under Pⁿ.
  -- Lem 19.24 gives:
  --   μ {ξ | ε/2 < |EP P n (fun i : Fin n => ξ i.val) (f_hat n ξ)
  --              - EP P n (fun i : Fin n => ξ i.val) score_truth|} → 0
  -- and the set on `Pⁿ` we want is, for `n ≥ 1`:
  --   {X | ε ≤ |(1/√n) Σ (score_func_seq n X (X i) - score_truth (X i))
  --              - √n * ∫ (score_func_seq n X ω - score_truth ω) ∂P|}
  -- which rewrites via `empiricalProcess` def to the same shape.
  -- Squeeze `μ`-form between 0 and the Lem 19.24 bound.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lem19_24
  · exact Filter.Eventually.of_forall (fun _ => zero_le)
  · -- For each n, the Pⁿ-set is ⊆ μ-preimage of an μ-set. Bridge via
    -- `pi_meas_eq_infinitePi_meas_of_truncate`.
    refine Filter.Eventually.of_forall (fun n => ?_)
    -- Identify the Pⁿ-measure with μ-pre-image measure via `pi_const_eq_infinitePi_map`.
    have h_truncate_meas :
        Measurable (fun ξ : ℕ → Ω => fun i : Fin n => ξ i.val) := h_proj_meas n
    -- Define the Pⁿ-set and μ-set; show Pⁿ-set ⊆ truncate⁻¹ (μ-set ∩ ...).
    set S_pi : Set (Fin n → Ω) := {X : Fin n → Ω |
        ε ≤ |(Real.sqrt n)⁻¹ *
                (∑ i : Fin n,
                  (score_func_seq n X (X i) - score_truth (X i)))
              - Real.sqrt n
                * (∫ ω, (score_func_seq n X ω - score_truth ω) ∂P)|} with hS_pi_def
    set S_mu : Set (ℕ → Ω) := {ξ : ℕ → Ω | ε / 2 <
        |EmpiricalProcess.empiricalProcess P n
            (fun i : Fin n => (fun ξ : ℕ → Ω => ξ i.val) ξ) (f_hat n ξ)
          - EmpiricalProcess.empiricalProcess P n
            (fun i : Fin n => (fun ξ : ℕ → Ω => ξ i.val) ξ) score_truth|} with hS_mu_def
    -- Measurability of `S_pi`.
    have h_S_pi_meas : MeasurableSet S_pi := by
      refine measurableSet_le measurable_const ?_
      refine Measurable.abs ?_
      have h_sum : Measurable (fun X : Fin n → Ω =>
          ∑ i : Fin n, (score_func_seq n X (X i) - score_truth (X i))) := by
        refine Finset.measurable_sum _ (fun i _ => ?_)
        refine Measurable.sub ?_ (h.truth_meas.comp (measurable_pi_apply i))
        -- score_func_seq n X (X i) is the joint score_func_meas precomposed with
        -- (id, eval i).
        have hcomp : (fun X : Fin n → Ω => score_func_seq n X (X i))
            = (fun p : (Fin n → Ω) × Ω => score_func_seq n p.1 p.2)
                ∘ (fun X : Fin n → Ω => (X, X i)) := by
          funext X; rfl
        rw [hcomp]
        exact (h.score_func_meas n).comp
          (Measurable.prodMk measurable_id (measurable_pi_apply i))
      have h_int : Measurable (fun X : Fin n → Ω =>
          ∫ ω, (score_func_seq n X ω - score_truth ω) ∂P) := by
        have h_joint : Measurable (fun p : (Fin n → Ω) × Ω =>
            score_func_seq n p.1 p.2 - score_truth p.2) :=
          (h.score_func_meas n).sub (h.truth_meas.comp measurable_snd)
        exact h_joint.stronglyMeasurable.integral_prod_right'.measurable
      refine Measurable.sub ?_ ?_
      · exact (measurable_const.mul h_sum)
      · exact (measurable_const.mul h_int)
    -- Inclusion: truncate⁻¹ S_pi ⊆ S_mu (i.e. if Pⁿ-condition holds at proj_n ξ,
    -- then the μ-condition with η = ε/2 holds at ξ).
    have h_incl : (fun ξ : ℕ → Ω => fun i : Fin n => ξ i.val) ⁻¹' S_pi ⊆ S_mu := by
      intro ξ hξ
      simp only [Set.mem_preimage, hS_pi_def, Set.mem_setOf_eq] at hξ
      simp only [hS_mu_def, Set.mem_setOf_eq]
      -- Unfold empiricalProcess.
      unfold EmpiricalProcess.empiricalProcess EmpiricalProcess.empiricalAvg
      -- Goal: ε/2 < |√n * ((1/n)·Σ (f_hat n ξ) (ξ i.val) - ∫f_hat n ξ ∂P)
      --             - √n * ((1/n)·Σ score_truth (ξ i.val) - ∫score_truth ∂P)|.
      -- The hypothesis gives the projected empirical-score inequality
      -- ε ≤ |(1/√n)·Σ(score_func_seq n proj X(_) - score_truth(_))
      --      - √n · ∫(score_func_seq n proj X(_) - score_truth(_)) ∂P|.
      -- where proj X = (fun i : Fin n => ξ i.val).
      -- Rewrite the μ side as the same expression after algebra.
      -- For n = 0, hξ ⇒ ε ≤ 0 (RHS is 0), contradiction.
      by_cases hn0 : n = 0
      · subst hn0
        simp at hξ
        linarith
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR_pos
      have h_sqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt h_sqrt_pos
      have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
      -- Algebra: (1/√n)·Σ - √n·∫ = √n·((1/n)·Σ - ∫).
      have h_inv_eq : (Real.sqrt (n : ℝ))⁻¹ = Real.sqrt n * ((n : ℝ)⁻¹) := by
        have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
          Real.mul_self_sqrt hnR_pos.le
        calc (Real.sqrt (n : ℝ))⁻¹
            = (Real.sqrt n)⁻¹ * 1 := by rw [mul_one]
          _ = (Real.sqrt n)⁻¹ * (Real.sqrt n * Real.sqrt n * (n : ℝ)⁻¹) := by
              rw [h_sqrt_sq, mul_inv_cancel₀ hnR_ne]
          _ = ((Real.sqrt n)⁻¹ * Real.sqrt n) * (Real.sqrt n * (n : ℝ)⁻¹) := by ring
          _ = 1 * (Real.sqrt n * (n : ℝ)⁻¹) := by
              rw [inv_mul_cancel₀ h_sqrt_ne]
          _ = Real.sqrt n * ((n : ℝ)⁻¹) := by rw [one_mul]
      -- Algebraic identity: LHS_Pⁿ = EP_diff where EP_diff is the empiricalProcess
      -- difference. Holds whether or not `score_func_seq` is integrable, by case
      -- analysis on integrability *and* using `∫score_truth dP = 0` (from
      -- `truth_aeEq` + `L2ZeroMean`).
      have h_truth_int : Integrable score_truth P :=
        h.truth_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_truth_zero : ∫ ω, score_truth ω ∂P = 0 := by
        rw [← integral_congr_ae h.truth_aeEq]
        exact L2ZeroMean.integral_coeFn_eq_zero _
      have h_int_split :
          ∫ ω, (score_func_seq n (fun i : Fin n => ξ i.val) ω
                  - score_truth ω) ∂P
          = (∫ ω, score_func_seq n (fun i : Fin n => ξ i.val) ω ∂P)
            - ∫ ω, score_truth ω ∂P := by
        by_cases h_int : Integrable
            (fun ω => score_func_seq n (fun i : Fin n => ξ i.val) ω) P
        · exact MeasureTheory.integral_sub h_int h_truth_int
        · rw [MeasureTheory.integral_undef h_int]
          have h_diff_not_int : ¬ Integrable
              (fun ω => score_func_seq n (fun i : Fin n => ξ i.val) ω
                        - score_truth ω) P := by
            intro h_diff_int
            apply h_int
            have hrw : (fun ω => score_func_seq n
                          (fun i : Fin n => ξ i.val) ω)
                = (fun ω => (score_func_seq n (fun i : Fin n => ξ i.val) ω
                              - score_truth ω) + score_truth ω) := by
              funext ω; ring
            rw [hrw]
            exact h_diff_int.add h_truth_int
          rw [MeasureTheory.integral_undef h_diff_not_int]
          rw [h_truth_zero]
          ring
      -- Algebra: (1/√n)·Σ(a - b) - √n·∫(a - b) = √n·((1/n)·Σa - ∫a) - √n·((1/n)·Σb - ∫b)
      -- after splitting Σ(a-b) = Σa - Σb (free) and ∫(a-b) = ∫a - ∫b (h_int_split).
      have h_pn_form : (Real.sqrt n)⁻¹ *
                  (∑ i : Fin n,
                    (score_func_seq n (fun i : Fin n => ξ i.val) (ξ i.val)
                      - score_truth (ξ i.val)))
                - Real.sqrt n
                  * (∫ ω, (score_func_seq n (fun i : Fin n => ξ i.val) ω
                            - score_truth ω) ∂P)
              = Real.sqrt n
                * ((n : ℝ)⁻¹ * (∑ i : Fin n, f_hat n ξ (ξ i.val))
                  - ∫ x, f_hat n ξ x ∂P)
                - Real.sqrt n
                  * ((n : ℝ)⁻¹ * (∑ i : Fin n, score_truth (ξ i.val))
                    - ∫ x, score_truth x ∂P) := by
        simp only [hf_hat_def]
        rw [h_inv_eq, Finset.sum_sub_distrib, h_int_split]
        ring
      rw [h_pn_form] at hξ
      -- This is the required μ-form after weakening the threshold from ε to ε/2.
      have h_le : ε / 2 < ε := by linarith
      exact lt_of_lt_of_le h_le hξ
    -- Apply the bridge `pi_meas_eq_infinitePi_meas_of_truncate`.
    have h_bridge := AsymptoticStatistics.pi_meas_eq_infinitePi_meas_of_truncate
      P n h_S_pi_meas
    rw [h_bridge]
    -- Pⁿ-set after bridge equals μ-preimage measure; show ≤ μ S_mu.
    refine measure_mono ?_
    intro ξ hξ
    exact h_incl hξ

/-- **Step 2 (no-bias rewrite).**

`√n · (∫ score_func_seq n X − score_truth dP) = G_n(score_truth) + o_P(1)`
modulo absorbing the `score_eq` (estimating equation) term.

Combining Step 1 with the score equation (`h.score_eq`,
`√n · 𝕡_n score_func_seq →_P 0`) gives the relation between
the estimated-score bias and the empirical process used at the start of
vdV's §25.5 proof. Indeed,
`√n · 𝕡_n ℓ̃_{θ̂_n,η̂_n} = G_n(ℓ̃_{θ̂_n,η̂_n}) + √n · ∫ ℓ̃_{θ̂_n,η̂_n} dP`.
By Step 1, `G_n(ℓ̃_{θ̂_n,η̂_n}) = G_n(ℓ̃) + o_P(1)`. By `score_eq`,
the left side is `o_P(1)`, and hence
`√n · ∫ ℓ̃_{θ̂_n,η̂_n} dP = −G_n(ℓ̃) + o_P(1)`.

Thus the bias term `√n · ∫ ℓ̃_{θ̂_n,η̂_n} dP` is expressed in terms of
`G_n(ℓ̃)`, the asymptotically Gaussian centred score sum under the truth. -/
private lemma step2_score_eq_to_no_bias
    (h : ZEstimatorTaylorHyp P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |Real.sqrt n * (∫ ω, score_func_seq n X ω ∂P)
                + (Real.sqrt n)⁻¹
                  * (∑ i : Fin n, score_truth (X i))|})
      atTop (𝓝 0) := by
  intro ε hε
  -- `score_truth` has mean zero under `P` (since it's a.e. equal to
  -- an element of `↥(L2ZeroMean P)` via `truth_aeEq`). This collapses
  -- `√n · ∫ score_truth dP = 0` in the algebraic identity below.
  have h_truth_zero : ∫ ω, score_truth ω ∂P = 0 := by
    rw [← integral_congr_ae h.truth_aeEq]
    exact L2ZeroMean.integral_coeFn_eq_zero _
  -- Apply `score_eq` at threshold ε/2 (giving `(1/√n)·Σ score_func_seq →_P 0`)
  -- and `step1_random_index_oP` at threshold ε/2 (giving the random-index
  -- `G_n` bound).
  have h_se := h.score_eq (ε / 2) (by linarith)
  have h_s1 := step1_random_index_oP h (ε / 2) (by linarith)
  -- Set inclusion + union bound. Define
  --   `A_n X := √n · ∫ score_func_seq n X dP`,
  --   `B_n X := (1/√n) · Σᵢ score_truth(X_i)`,
  --   `C_n X := (1/√n) · Σᵢ score_func_seq n X (X_i)` (score_eq integrand),
  --   `D_n X := (1/√n) · Σᵢ (score_func_seq n X (X_i) − score_truth(X_i))
  --              − √n · ∫ (score_func_seq n X − score_truth) dP` (Step 1 integrand).
  -- Algebraic identity (Pⁿ-a.e., on the `score_func_seq n X`-integrable set;
  -- uses `h_truth_zero` to drop `√n · ∫ score_truth dP`):
  --   A_n + B_n = C_n − D_n.
  -- Hence `|A_n + B_n| ≤ |C_n| + |D_n|` and
  --   {X | ε ≤ |A_n + B_n|} ⊆ {X | ε/2 ≤ |C_n|} ∪ {X | ε/2 ≤ |D_n|} (Pⁿ-a.e.).
  -- Combine with `measure_mono` + `measure_union_le`:
  --   Pⁿ {ε ≤ |A_n + B_n|} ≤ Pⁿ {ε/2 ≤ |C_n|} + Pⁿ {ε/2 ≤ |D_n|}.
  -- Squeeze from constant zero + `h_se.add h_s1` (the RHS sum → 0).
  have h_upper : Tendsto
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε / 2 ≤ |(Real.sqrt n)⁻¹
                * (∑ i : Fin n, score_func_seq n X (X i))|}
        + (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε / 2 ≤ |(Real.sqrt n)⁻¹ *
                    (∑ i : Fin n,
                      (score_func_seq n X (X i) - score_truth (X i)))
                  - Real.sqrt n
                    * (∫ ω, (score_func_seq n X ω - score_truth ω) ∂P)|})
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using h_se.add h_s1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
  · exact Filter.Eventually.of_forall (fun _ => zero_le)
  · -- Set-inclusion + union bound (the algebraic identity step).
    -- Even without integrability of `score_func_seq n X`, the identity
    -- `A_n + B_n = C_n - D_n` holds: in the non-integrable case, both
    -- `∫ score_func dP` and `∫ (score_func − score_truth) dP` are zero
    -- by Mathlib's convention (the latter because `score_func − score_truth`
    -- is also non-integrable, since `score_truth ∈ L¹`). This gives the
    -- inclusion `{ε ≤ |A_n + B_n|} ⊆ {ε/2 ≤ |C_n|} ∪ {ε/2 ≤ |D_n|}`
    -- *everywhere* (not just Pⁿ-a.e.), so `measure_mono` + `measure_union_le`
    -- finishes.
    have h_truth_int : Integrable score_truth P :=
      h.truth_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    refine Filter.Eventually.of_forall (fun n => ?_)
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro X hX
    simp only [Set.mem_setOf_eq, Set.mem_union] at hX ⊢
    -- Set up the four quantities A, B, C, D; show A + B = C - D, then
    -- triangle: |A + B| ≤ |C| + |D|; pair with `hX` (|A+B| ≥ ε) to get
    -- `|C| ≥ ε/2 ∨ |D| ≥ ε/2`.
    set A_n : ℝ := Real.sqrt n * (∫ ω, score_func_seq n X ω ∂P) with hA_def
    set B_n : ℝ := (Real.sqrt n)⁻¹ * (∑ i : Fin n, score_truth (X i)) with hB_def
    set C_n : ℝ := (Real.sqrt n)⁻¹ * (∑ i : Fin n, score_func_seq n X (X i))
      with hC_def
    set D_n : ℝ :=
      (Real.sqrt n)⁻¹ *
        (∑ i : Fin n, (score_func_seq n X (X i) - score_truth (X i)))
      - Real.sqrt n
        * (∫ ω, (score_func_seq n X ω - score_truth ω) ∂P) with hD_def
    -- Algebraic identity A + B = C - D.
    have h_sum_split :
        (∑ i : Fin n,
            (score_func_seq n X (X i) - score_truth (X i)))
        = (∑ i : Fin n, score_func_seq n X (X i))
          - ∑ i : Fin n, score_truth (X i) := by
      rw [Finset.sum_sub_distrib]
    -- Integral split: ∫ score_func_seq − ∫ score_truth
    -- (with case-on-integrability handling).
    have h_int_split :
        ∫ ω, (score_func_seq n X ω - score_truth ω) ∂P
        = (∫ ω, score_func_seq n X ω ∂P) - ∫ ω, score_truth ω ∂P := by
      by_cases h_int : Integrable (fun ω => score_func_seq n X ω) P
      · exact MeasureTheory.integral_sub h_int h_truth_int
      · rw [MeasureTheory.integral_undef h_int]
        have h_diff_not_int : ¬ Integrable
            (fun ω => score_func_seq n X ω - score_truth ω) P := by
          intro h_diff_int
          apply h_int
          have hrw :
              (fun ω => score_func_seq n X ω)
              = (fun ω => (score_func_seq n X ω - score_truth ω)
                          + score_truth ω) := by
            funext ω; ring
          rw [hrw]
          exact h_diff_int.add h_truth_int
        rw [MeasureTheory.integral_undef h_diff_not_int, h_truth_zero]
        ring
    have h_AB_eq : A_n + B_n = C_n - D_n := by
      simp only [hA_def, hB_def, hC_def, hD_def, h_sum_split, h_int_split,
        h_truth_zero]
      ring
    -- Triangle: |A + B| = |C - D| ≤ |C| + |D|.
    have h_tri : |A_n + B_n| ≤ |C_n| + |D_n| := by
      rw [h_AB_eq]
      calc |C_n - D_n|
          = |C_n + (-D_n)| := by ring_nf
        _ ≤ |C_n| + |-D_n| := abs_add_le _ _
        _ = |C_n| + |D_n| := by rw [abs_neg]
    -- Conclude `|C| ≥ ε/2 ∨ |D| ≥ ε/2` from |A + B| ≥ ε.
    by_contra hc
    push Not at hc
    obtain ⟨hcC, hcD⟩ := hc
    have h_lt : |A_n + B_n| < ε := by
      have h1 : |C_n| < ε / 2 := hcC
      have h2 : |D_n| < ε / 2 := hcD
      linarith [h_tri]
    exact absurd hX (not_le.mpr h_lt)

/-- **Step 3 (Taylor remainder vanishes in the `(1/√n)` scale).**

`(1/√n) · Σᵢ r_n(X_i) →_P 0` under `Pⁿ`, where
`r_n(X_i) := score_func_seq n X (X_i) − score_truth(X_i)
              − (estimator n X − θ₀) · ℓ̇(X_i)`
is the empirical Taylor remainder for the score map at θ₀.

**Proof strategy.** Cauchy-Schwarz on the empirical L² remainder:
  `|(1/√n) · Σᵢ r_n(X_i)|² ≤ (1/n) · n · Σᵢ r_n(X_i)² = Σᵢ r_n(X_i)²`,
so `|(1/√n) Σ r_n| ≤ √(Σ r_n²)`. The hypothesis `score_l2_taylor`
(`Σᵢ r_n(X_i)² →_P 0` under `Pⁿ`) plus continuity of `√·` at `0` give
the conclusion via squeeze.

This is the vanishing second-order term in the strong-regularity argument of
vdV §25.5, and is the same Taylor-remainder estimate used in
`oneStep_asympLinear_of_taylor`. -/
lemma step3_taylor_remainder_oP
    (h : ZEstimatorTaylorCoreBase P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |(Real.sqrt n)⁻¹ *
                (∑ i : Fin n,
                  (score_func_seq n X (X i)
                    - score_truth (X i)
                    - (estimator n X - θ₀)
                      * (score_l_dot : Ω → ℝ) (X i)))|})
      atTop (𝓝 0) := by
  intro ε hε
  -- Apply `score_l2_taylor` at threshold `ε²`.
  have h_taylor := h.score_l2_taylor (ε^2) (by positivity)
  -- Squeeze: `0 ≤ Pⁿ{ε ≤ |(1/√n)·Σ r_n|} ≤ Pⁿ{ε² ≤ Σ r_n²} → 0`.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_taylor
  · exact Filter.Eventually.of_forall (fun _ => zero_le)
  · -- Set inclusion via Cauchy-Schwarz: `(Σ r_n)² ≤ n · Σ r_n²`.
    -- Skip n = 0 (where the LHS set is empty since `(0)⁻¹ * 0 = 0 < ε`).
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply measure_mono
    intro X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
    set r_seq : Fin n → ℝ := fun i =>
      score_func_seq n X (X i)
        - score_truth (X i)
        - (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)
      with h_r_seq_def
    -- Cauchy-Schwarz: `(Σ rᵢ)² ≤ n · Σ rᵢ²`.
    have h_cs : (∑ i : Fin n, r_seq i) ^ 2 ≤ ↑n * (∑ i : Fin n, (r_seq i) ^ 2) := by
      have h_apply :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun _ : Fin n => (1 : ℝ)) r_seq
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one] at h_apply
      exact h_apply
    -- Square `hX` to bound `ε² ≤ ((1/√n)·Σ r)² = (Σ r)² / n ≤ Σ r²`.
    have h_abs_sq : ε^2 ≤ ((Real.sqrt ↑n)⁻¹ * (∑ i : Fin n, r_seq i)) ^ 2 := by
      have hε_le_abs := hX
      have h_abs_nn :
          (0 : ℝ) ≤ |(Real.sqrt ↑n)⁻¹ * (∑ i : Fin n, r_seq i)| := abs_nonneg _
      have h_pow := sq_le_sq' (by linarith) hε_le_abs
      rw [sq_abs] at h_pow
      exact h_pow
    have h_pow_eq :
        ((Real.sqrt ↑n)⁻¹ * (∑ i : Fin n, r_seq i)) ^ 2
          = (∑ i : Fin n, r_seq i) ^ 2 / ↑n := by
      rw [mul_pow, inv_pow, Real.sq_sqrt h_n_pos.le]
      ring
    calc ε^2
        ≤ ((Real.sqrt ↑n)⁻¹ * (∑ i : Fin n, r_seq i)) ^ 2 := h_abs_sq
      _ = (∑ i : Fin n, r_seq i) ^ 2 / ↑n := h_pow_eq
      _ ≤ ↑n * (∑ i : Fin n, (r_seq i) ^ 2) / ↑n := by
          apply div_le_div_of_nonneg_right h_cs h_n_pos.le
      _ = ∑ i : Fin n, (r_seq i) ^ 2 := by
          field_simp

/-- **Markov bound on the centred score-truth partial sum.**

For all ε > 0, ∃ M such that for all n,
  `Pⁿ(|(1/√n)·Σᵢ score_truth(X_i)| ≥ M) ≤ ε`.

**Proof sketch.** By `truth_aeEq`, `score_truth` has mean zero and lies in
`L²(P)` with `‖score_truth‖²_{L²} = Ĩ < ∞`. iid-sum variance linearity:
`E^Pⁿ[((1/√n) Σ score_truth)²] = ‖score_truth‖²_{L²}`. Markov + Chebyshev:
`Pⁿ{|(1/√n)·Σ| ≥ M} ≤ ‖score_truth‖²_{L²} / M²`. Choose `M = √(‖score_truth‖²/ε)`.
Mirrors `score_sum_bddAbove_in_prob`. -/
private lemma score_truth_sum_bddAbove_in_prob
    (h : ZEstimatorTaylorCore P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀) :
    ∀ ε > 0, ∃ M : ℝ, ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          M ≤ |(Real.sqrt n)⁻¹ * (∑ i : Fin n, score_truth (X i))|}
      ≤ ENNReal.ofReal ε := by
  intro ε hε
  -- `score_truth` has mean zero under `P` (via `truth_aeEq` + the
  -- `L2ZeroMean` constraint on `efficientScore`).
  have h_mean_zero : ∫ ω, score_truth ω ∂P = 0 := by
    rw [← integral_congr_ae h.truth_aeEq]
    exact L2ZeroMean.integral_coeFn_eq_zero _
  -- Variance bound: `Var[score_truth; P] ≤ ∫ score_truth² ∂P`.
  set V : ℝ := ProbabilityTheory.variance score_truth P with hV_def
  have hV_nn : 0 ≤ V := by
    change (0 : ℝ) ≤ (ProbabilityTheory.evariance score_truth P).toReal
    exact ENNReal.toReal_nonneg
  -- Choose M = √(V/ε + 1) > 0 with M² ≥ V/ε + 1, so V/M² < ε.
  refine ⟨Real.sqrt (V / ε + 1), fun n => ?_⟩
  set M : ℝ := Real.sqrt (V / ε + 1) with hM_def
  have hVε_nn : 0 ≤ V / ε + 1 := by positivity
  have hVε_pos : 0 < V / ε + 1 := by
    have : 0 ≤ V / ε := div_nonneg hV_nn hε.le
    linarith
  have hM_pos : 0 < M := Real.sqrt_pos.mpr hVε_pos
  have hM_sq : M ^ 2 = V / ε + 1 := Real.sq_sqrt hVε_nn
  have hVM : V / M ^ 2 ≤ ε := by
    rw [hM_sq]
    rcases eq_or_lt_of_le hV_nn with hV_zero | hV_pos
    · -- V = 0: 0 / (V/ε + 1) = 0 ≤ ε.
      rw [← hV_zero, zero_div]
      exact hε.le
    · -- V > 0: V/(V/ε + 1) ≤ V/(V/ε) = ε.
      have hVε_pos : 0 < V / ε := div_pos hV_pos hε
      have h1 : V / ε + 1 ≥ V / ε := by linarith
      have h2 : V / (V / ε + 1) ≤ V / (V / ε) :=
        div_le_div_of_nonneg_left hV_pos.le hVε_pos h1
      have h3 : V / (V / ε) = ε := by field_simp
      linarith
  -- n = 0: the LHS set is empty since (√0)⁻¹ * 0 = 0 < M.
  by_cases hn0 : n = 0
  · subst hn0
    have h_set_empty : {X : Fin 0 → Ω |
        M ≤ |(Real.sqrt (0 : ℕ))⁻¹ * (∑ i : Fin 0, score_truth (X i))|}
        = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le,
        Nat.cast_zero, Real.sqrt_zero, inv_zero,
        mul_zero, abs_zero, Fin.sum_univ_zero]
      exact hM_pos
    rw [h_set_empty, measure_empty]
    exact bot_le
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR_pos
  have h_sqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt h_sqrt_pos
  -- Setup: define `Z X := (√n)⁻¹ * Σᵢ score_truth (X i)` as a real-valued function
  -- on `Fin n → Ω`. Bound `Pⁿ {M ≤ |Z|}` via Chebyshev, using
  --   `(Pⁿ)[Z] = 0` and `Var[Z; Pⁿ] = Var[score_truth; P] = V`.
  -- Each `Y_i := score_truth ∘ eval i` is MemLp 2 Pⁿ via measure-preserving.
  have h_truth_mp : ∀ i : Fin n,
      MemLp (fun X : Fin n → Ω => score_truth (X i)) 2
        (Measure.pi (fun _ : Fin n => P)) := by
    intro i
    have hmp :
        MeasureTheory.MeasurePreserving (Function.eval i)
          (Measure.pi (fun _ : Fin n => P)) P :=
      MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => P) i
    exact h.truth_memLp.comp_measurePreserving hmp
  -- Sum is MemLp 2 Pⁿ.
  have h_sum_mLp :
      MemLp (fun X : Fin n → Ω => ∑ i : Fin n, score_truth (X i)) 2
        (Measure.pi (fun _ : Fin n => P)) :=
    memLp_finset_sum (Finset.univ : Finset (Fin n))
      (fun i _ => h_truth_mp i)
  -- Constant scaling by `(√n)⁻¹` preserves MemLp 2.
  have h_Z_mLp :
      MemLp (fun X : Fin n → Ω =>
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, score_truth (X i)) 2
        (Measure.pi (fun _ : Fin n => P)) :=
    h_sum_mLp.const_mul _
  -- Mean of Z under Pⁿ is 0.
  have h_aesm : AEStronglyMeasurable score_truth P :=
    h.truth_memLp.aestronglyMeasurable
  have h_int_truth_pi : ∀ i : Fin n,
      ∫ X : Fin n → Ω, score_truth (X i) ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
    intro i
    have : ∫ X : Fin n → Ω, score_truth (X i)
              ∂(Measure.pi (fun _ : Fin n => P))
            = ∫ ω, score_truth ω ∂P :=
      MeasureTheory.integral_comp_eval (i := i)
        (μ := fun _ : Fin n => P) h_aesm
    rw [this, h_mean_zero]
  have h_Z_mean :
      ∫ X : Fin n → Ω, ((Real.sqrt n)⁻¹ * ∑ i : Fin n, score_truth (X i))
        ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
    have h_int_sum :
        ∫ X : Fin n → Ω, (∑ i : Fin n, score_truth (X i))
          ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
      rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset (Fin n))
            (fun i _ => (h_truth_mp i).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2))]
      apply Finset.sum_eq_zero
      intro i _
      exact h_int_truth_pi i
    rw [MeasureTheory.integral_const_mul, h_int_sum, mul_zero]
  -- Variance of Z under Pⁿ equals Var[score_truth; P].
  have h_Z_var :
      ProbabilityTheory.variance (fun X : Fin n → Ω =>
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, score_truth (X i))
        (Measure.pi (fun _ : Fin n => P)) = V := by
    -- Var[(1/√n) · Σ Y_i] = (1/n) · Var[Σ Y_i] = (1/n) · n · V = V.
    rw [ProbabilityTheory.variance_const_mul]
    -- Goal: (1/√n)² · Var[Σ; Pⁿ] = V.
    -- Apply variance_sum_pi with X i := score_truth (constant in i).
    have h_var_sum :
        ProbabilityTheory.variance
          (fun X : Fin n → Ω => ∑ i : Fin n, score_truth (X i))
          (Measure.pi (fun _ : Fin n => P))
        = ∑ _ : Fin n, V := by
      have h_pi := ProbabilityTheory.variance_sum_pi
        (μ := fun _ : Fin n => P)
        (X := fun _ : Fin n => score_truth)
        (fun _ => h.truth_memLp)
      -- The conclusion features `∑ i, fun ω ↦ X i (ω i)` as a function-valued sum;
      -- bridge to our `fun ω ↦ ∑ i, X i (ω i)` form via `Finset.sum_apply`.
      have h_fun_eq :
          (∑ i : Fin n, fun ω : Fin n → Ω => score_truth (ω i))
            = fun X : Fin n → Ω => ∑ i : Fin n, score_truth (X i) := by
        funext X
        simp [Finset.sum_apply]
      rw [h_fun_eq] at h_pi
      exact h_pi
    rw [h_var_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    -- Goal: (√n)⁻¹^2 * (n * V) = V.
    have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
      Real.mul_self_sqrt hnR_pos.le
    have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
    have h_inv_sq : (Real.sqrt n)⁻¹ ^ 2 = (n : ℝ)⁻¹ := by
      rw [inv_pow, sq, h_sqrt_sq]
    rw [h_inv_sq]
    field_simp
  -- Apply Chebyshev: Pⁿ {M ≤ |Z − E[Z]|} ≤ ENNReal.ofReal (Var/M²).
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have h_cheb := ProbabilityTheory.meas_ge_le_variance_div_sq h_Z_mLp hM_pos
  rw [h_Z_mean] at h_cheb
  rw [h_Z_var] at h_cheb
  -- The set in h_cheb is `{X | M ≤ |Z X − 0|}` = `{X | M ≤ |Z X|}`.
  have h_set_eq :
      {X : Fin n → Ω |
          M ≤ |((Real.sqrt n)⁻¹ * ∑ i : Fin n, score_truth (X i)) - 0|}
        = {X : Fin n → Ω |
          M ≤ |(Real.sqrt n)⁻¹ * ∑ i : Fin n, score_truth (X i)|} := by
    ext X; simp
  rw [h_set_eq] at h_cheb
  refine h_cheb.trans ?_
  exact ENNReal.ofReal_le_ofReal hVM

/-- **Finite-`n` tightness of `√n(estimator − θ₀)`.**

For any fixed n, the random variable `X ↦ √n(estimator n X − θ₀)` is a
measurable function on the finite measure `Pⁿ`; tightness of finite measures
gives `Pⁿ{|√n(est − θ₀)| ≥ M_n} → 0` as `M_n → ∞`. Combining over a finite
initial segment produces a single bound `M_init` covering all `n < N`.

The proof takes the maximum of the individual bounds for finitely many `n`,
using measurability of `estimator n` and tightness of finite
measures (`MeasureTheory.tendsto_measure_compl_atTop` or similar). Used to
absorb the small-n initial segment in `step5_sqrt_n_consistency` after the
bootstrap pins down large-n behaviour. -/
private lemma step5_finite_initial_segment_tightness
    (h : ZEstimatorTaylorCore P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ n < N,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | M ≤ |Real.sqrt n * (estimator n X - θ₀)|}
      ≤ ENNReal.ofReal ε := by
  -- Per-`n` finite-measure tightness: for each n < N, the antitone family
  -- of measurable sets `{X | (k : ℝ) ≤ |√n · (estimator n X - θ₀)|}`
  -- (indexed by `k : ℕ`) has empty intersection (the absolute value is
  -- real-valued, hence finite), so its measure tends to 0 as k → ∞.
  -- Take the max of per-n bounds.
  have h_per : ∀ n,
      ∀ ε > 0, ∃ M : ℕ,
        (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | (M : ℝ) ≤ |Real.sqrt n * (estimator n X - θ₀)|}
        ≤ ENNReal.ofReal ε := by
    intro n ε' hε'
    set g : (Fin n → Ω) → ℝ := fun X => Real.sqrt n * (estimator n X - θ₀)
      with hg_def
    have hg_meas : Measurable g := by
      have h_est : Measurable (estimator n) := h.estimator_meas n
      have h_sub : Measurable (fun X : Fin n → Ω => estimator n X - θ₀) :=
        h_est.sub_const θ₀
      exact h_sub.const_mul _
    set s : ℕ → Set (Fin n → Ω) := fun k => {X | (k : ℝ) ≤ |g X|}
      with hs_def
    have hs_meas : ∀ k, MeasurableSet (s k) := by
      intro k
      exact measurableSet_le measurable_const hg_meas.abs
    have hs_anti : Antitone s := by
      intro k₁ k₂ hk X hX
      simp only [s, Set.mem_setOf_eq] at hX ⊢
      have h_cast : (k₁ : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast hk
      linarith
    have hs_inter_empty : ⋂ k, s k = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro X hX
      simp only [s, Set.mem_iInter, Set.mem_setOf_eq] at hX
      -- `|g X| < ⌈|g X|⌉ + 1`, but `(⌈|g X|⌉ + 1 : ℕ) ≤ |g X|`. Contradiction.
      have h_abs_nn : (0 : ℝ) ≤ |g X| := abs_nonneg _
      have h_lt : |g X| < (⌊|g X|⌋₊ + 1 : ℕ) := by
        have : (⌊|g X|⌋₊ : ℝ) ≤ |g X| := Nat.floor_le h_abs_nn
        have h2 : |g X| < ⌊|g X|⌋₊ + 1 := Nat.lt_floor_add_one _
        push_cast
        linarith
      have h_ge := hX (⌊|g X|⌋₊ + 1)
      linarith
    have h_finite_first : (Measure.pi (fun _ : Fin n => P)) (s 0) ≠ ⊤ :=
      measure_ne_top _ _
    have h_tendsto : Tendsto
        (fun k => (Measure.pi (fun _ : Fin n => P)) (s k)) atTop
        (𝓝 ((Measure.pi (fun _ : Fin n => P)) (⋂ k, s k))) :=
      MeasureTheory.tendsto_measure_iInter_atTop
        (fun k => (hs_meas k).nullMeasurableSet) hs_anti ⟨0, h_finite_first⟩
    rw [hs_inter_empty, MeasureTheory.measure_empty] at h_tendsto
    rw [ENNReal.tendsto_atTop_zero] at h_tendsto
    obtain ⟨M, hM⟩ := h_tendsto (ENNReal.ofReal ε') (by positivity)
    exact ⟨M, hM M le_rfl⟩
  classical
  -- Take the max of per-n natural bounds for n ∈ Finset.range N, cast to ℝ.
  let f : ℕ → ℕ := fun n => Classical.choose (h_per n ε hε)
  have hf : ∀ n, (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω | (f n : ℝ) ≤ |Real.sqrt n * (estimator n X - θ₀)|}
      ≤ ENNReal.ofReal ε := fun n => Classical.choose_spec (h_per n ε hε)
  refine ⟨((Finset.range N).sup f : ℕ), fun n hn => ?_⟩
  have h_le : (f n : ℝ) ≤ (((Finset.range N).sup f : ℕ) : ℝ) := by
    exact_mod_cast Finset.le_sup (f := f) (Finset.mem_range.mpr hn)
  refine le_trans (measure_mono ?_) (hf n)
  intro X hX
  simp only [Set.mem_setOf_eq] at hX ⊢
  exact h_le.trans hX

/-- **Step 4 (LLN on `ℓ̇` + Bartlett identity).**

`(1/n) · Σᵢ ℓ̇(X_i) →_P −Ĩ` under `Pⁿ`.

**Proof strategy.** Apply the iid weak law of large numbers to the
function `ℓ̇ ∈ L²(P) ⊂ L¹(P)`: under iid product `Pⁿ`,
`(1/n) Σᵢ ℓ̇(X_i) →_P E_P[ℓ̇]`. The semiparametric Bartlett identity
`score_l_dot_bartlett` gives `E_P[ℓ̇] = −efficientInformation S_θ T_nuis v`,
yielding the stated probability limit.

The product-law form `(1/n) Σᵢ f(X_i) →_P E[f]` follows from
`MeasureTheory.lln_strong_iid` after identifying the finite product
coordinates. -/
lemma step4_score_dot_lln
    (h : ZEstimatorTaylorCoreBase P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
                + efficientInformation S_θ T_nuis v|})
      atTop (𝓝 0) :=
  score_l_dot_avg_plus_info_oP h.score_l_dot_bartlett

/-- **Step 5 (√n-consistency derivation).**

`√n · (estimator n X − θ₀) = O_P(1)` under `Pⁿ`: for every ε > 0 there
is a uniform M such that `Pⁿ{X | M ≤ |√n(estimator − θ₀)|} ≤ ε` for all n.

**Proof strategy.** Substitute the Taylor identity
`score_func_seq n X (X_i) = score_truth(X_i) + (estimator − θ₀) ℓ̇(X_i) + r_n(X_i)`
into the score-equation `score_eq` (which states
`(1/√n) Σ score_func_seq n X (X_i) →_P 0`). After rearrangement:
`(1/√n) Σ score_truth(X_i)
   + √n(estimator − θ₀) · (1/n) Σ ℓ̇(X_i)
   + (1/√n) Σ r_n(X_i) →_P 0`.

Invoke Step 3 (`(1/√n) Σ r_n(X_i) →_P 0`), Step 4
(`(1/n) Σ ℓ̇(X_i) →_P −Ĩ`), and the L²-CLT-bound
`(1/√n) Σ score_truth(X_i) = O_P(1)` (Chebyshev with second-moment
`E_P[score_truth²] = Ĩ`) to pin
`√n(estimator − θ₀) · (Ĩ + o_P(1)) = O_P(1) + o_P(1)`. The hypothesis
`hI_pos` keeps `Ĩ` bounded away from zero, so
`√n(estimator − θ₀) = O_P(1)`.

This is the bootstrap step that the book's original §25.5 proof handles
via Lem 19.24 + Donsker (Step 1 / Step 2 above) and the Taylor route
handles via direct Cauchy-Schwarz + boundedness arguments. -/
private lemma step5_sqrt_n_consistency
    (h : ZEstimatorTaylorCore P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀) :
    ∀ ε > 0, ∃ M : ℝ, ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | M ≤ |Real.sqrt n * (estimator n X - θ₀)|}
      ≤ ENNReal.ofReal ε := by
  intro ε hε
  set Ĩ : ℝ := efficientInformation S_θ T_nuis v with hĨ_def
  have hĨ_pos : 0 < Ĩ := h.hI_pos
  -- Allocate ε/4 to each of four contributions: |S_n|, |R_n|, |LHS_n|, |D_n − 0|.
  -- The "D_n" piece (= (1/n)Σℓ̇ + Ĩ) controls when (1/n)Σℓ̇ stays close to −Ĩ.
  have hε4 : 0 < ε / 4 := by linarith
  -- Markov bound on `(1/√n) Σ score_truth(X_i)` — uniform over n.
  obtain ⟨M_S, hM_S⟩ := score_truth_sum_bddAbove_in_prob h (ε / 4) hε4
  -- Choose `M_target := max(6·M_S/Ĩ, 6/Ĩ, 1)` and a threshold C := M·Ĩ/6.
  -- Choose `M` so that `M·Ĩ/6 ≥ M_S`, absorbing the score-truth bound.
  set M_main : ℝ := max (6 * (M_S + 1) / Ĩ) 1 with hM_main_def
  have hM_main_pos : 0 < M_main := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM_threshold : M_S ≤ M_main * Ĩ / 6 := by
    have h1 : M_S < (M_S + 1) := by linarith
    have h2 : 6 * (M_S + 1) / Ĩ ≤ M_main := le_max_left _ _
    have h3 : 6 * (M_S + 1) / Ĩ * Ĩ / 6 = M_S + 1 := by field_simp
    have h4 : 6 * (M_S + 1) / Ĩ * Ĩ / 6 ≤ M_main * Ĩ / 6 := by
      have := mul_le_mul_of_nonneg_right h2 hĨ_pos.le
      have hineq : 6 * (M_S + 1) / Ĩ * Ĩ ≤ M_main * Ĩ := this
      linarith
    linarith [h3 ▸ h4]
  -- For large `n`, each of `|D_n|`, `|R_n|`, and `|LHS_n|` has an ε/4 bound
  -- at threshold `M·Ĩ/6`.
  -- Apply step3, step4, h.score_eq each at threshold M_main·Ĩ/6.
  have hThresh_pos : 0 < M_main * Ĩ / 6 := by positivity
  have h_step3_inst := step3_taylor_remainder_oP h.toZEstimatorTaylorCoreBase (M_main * Ĩ / 6)
      hThresh_pos
  have h_step4_inst := step4_score_dot_lln h.toZEstimatorTaylorCoreBase (Ĩ / 2) (by positivity)
  have h_score_eq_inst := h.score_eq (M_main * Ĩ / 6) hThresh_pos
  -- Convert each Tendsto-to-zero into "eventually ≤ ε/4" via ENNReal.tendsto_nhds_zero.
  rw [ENNReal.tendsto_nhds_zero] at h_step3_inst
  rw [ENNReal.tendsto_nhds_zero] at h_step4_inst
  rw [ENNReal.tendsto_nhds_zero] at h_score_eq_inst
  have h_step3_le := h_step3_inst (ENNReal.ofReal (ε / 4)) (by positivity)
  have h_step4_le := h_step4_inst (ENNReal.ofReal (ε / 4)) (by positivity)
  have h_se_le := h_score_eq_inst (ENNReal.ofReal (ε / 4)) (by positivity)
  -- Combine the three eventually's into a single one with explicit threshold N.
  have h_eventual : ∀ᶠ n in atTop, ∀ (X : Fin n → Ω),
      True → True := Filter.Eventually.of_forall (fun _ _ _ => trivial)
  -- Extract a uniform N from the three eventuallys.
  obtain ⟨N3, hN3⟩ := (h_step3_le.and (h_step4_le.and h_se_le)).exists
  -- For n ≥ N3, the three measures are each ≤ ε/4.
  -- However the .exists doesn't quite capture the "for all n ≥ N" form; use
  -- `Filter.eventually_atTop` directly.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N,
      ((Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω |
              M_main * Ĩ / 6 ≤ |(Real.sqrt n)⁻¹ *
                (∑ i : Fin n,
                  (score_func_seq n X (X i)
                    - score_truth (X i)
                    - (estimator n X - θ₀)
                      * (score_l_dot : Ω → ℝ) (X i)))|}
          ≤ ENNReal.ofReal (ε / 4))
        ∧ ((Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω |
              Ĩ / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
                + Ĩ|}
          ≤ ENNReal.ofReal (ε / 4))
        ∧ ((Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω |
              M_main * Ĩ / 6 ≤ |(Real.sqrt n)⁻¹ *
                (∑ i : Fin n, score_func_seq n X (X i))|}
          ≤ ENNReal.ofReal (ε / 4)) := by
    rw [Filter.eventually_atTop] at h_step3_le h_step4_le h_se_le
    obtain ⟨N1, hN1⟩ := h_step3_le
    obtain ⟨N2, hN2⟩ := h_step4_le
    obtain ⟨N3, hN3⟩ := h_se_le
    refine ⟨max (max N1 N2) N3, fun n hn => ?_⟩
    refine ⟨hN1 n ?_, hN2 n ?_, hN3 n ?_⟩ <;>
      [exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn);
       exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn);
       exact le_trans (le_max_right _ _) hn]
  -- Tightness on the finite initial segment {n < N}.
  obtain ⟨M_init, hM_init⟩ :=
    step5_finite_initial_segment_tightness h N (ε / 4) hε4
  -- Final M.
  refine ⟨max M_main M_init, fun n => ?_⟩
  by_cases hnN : n < N
  · -- The finite initial segment is bounded by `M_init`.
    refine le_trans (measure_mono ?_) ((hM_init n hnN).trans ?_)
    · intro X hX; exact (le_max_right M_main M_init).trans hX
    · exact ENNReal.ofReal_le_ofReal (by linarith)
  · push Not at hnN
    -- Large-n: use the bootstrap union bound.
    obtain ⟨h3, h4, hse⟩ := hN n hnN
    -- Set inclusion: {M ≤ |√n(est-θ₀)|} ⊆ {Ĩ/2 ≤ |D_n|} ∪ {M·Ĩ/6 ≤ |S_n|}
    --                                       ∪ {M·Ĩ/6 ≤ |R_n|} ∪ {M·Ĩ/6 ≤ |LHS_n|}.
    have h_incl :
        {X : Fin n → Ω | max M_main M_init ≤ |Real.sqrt n * (estimator n X - θ₀)|}
        ⊆ ({X : Fin n → Ω |
              Ĩ / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
                + Ĩ|} ∪
            {X : Fin n → Ω |
              M_main * Ĩ / 6 ≤ |(Real.sqrt n)⁻¹ * (∑ i : Fin n, score_truth (X i))|})
          ∪ ({X : Fin n → Ω |
                M_main * Ĩ / 6 ≤ |(Real.sqrt n)⁻¹ *
                  (∑ i : Fin n,
                    (score_func_seq n X (X i)
                      - score_truth (X i)
                      - (estimator n X - θ₀)
                        * (score_l_dot : Ω → ℝ) (X i)))|} ∪
              {X : Fin n → Ω |
                M_main * Ĩ / 6 ≤ |(Real.sqrt n)⁻¹ *
                  (∑ i : Fin n, score_func_seq n X (X i))|}) := by
      intro X hX
      simp only [Set.mem_setOf_eq, Set.mem_union] at hX ⊢
      by_contra hc
      push Not at hc
      obtain ⟨⟨hcD, hcS⟩, hcR, hcLHS⟩ := hc
      -- Pointwise empirical identity:
      --  (1/√n) Σ score_func_seq = (1/√n) Σ score_truth
      --                            + √n(est-θ₀) · (1/n) Σ ℓ̇
      --                            + (1/√n) Σ r_n.
      -- So √n(est-θ₀) · ((1/n)Σℓ̇ + Ĩ) - √n(est-θ₀)·Ĩ
      --     = (1/√n) Σ score_func_seq - (1/√n) Σ score_truth - (1/√n) Σ r_n.
      -- I.e. √n(est-θ₀)·(D_n - Ĩ) = LHS_n - S_n - R_n,
      -- so √n(est-θ₀)·(Ĩ - D_n) = -LHS_n + S_n + R_n.
      set LHS_n : ℝ :=
        (Real.sqrt n)⁻¹ * (∑ i : Fin n, score_func_seq n X (X i)) with hLHS_def
      set S_n : ℝ :=
        (Real.sqrt n)⁻¹ * (∑ i : Fin n, score_truth (X i)) with hS_def
      set R_n : ℝ :=
        (Real.sqrt n)⁻¹ *
          (∑ i : Fin n,
            (score_func_seq n X (X i)
              - score_truth (X i)
              - (estimator n X - θ₀)
                * (score_l_dot : Ω → ℝ) (X i))) with hR_def
      set D_n : ℝ :=
        (n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) + Ĩ with hD_def
      set Δ_n : ℝ := Real.sqrt n * (estimator n X - θ₀) with hΔ_def
      -- When `n = 0`, `Δ_n = 0` and the left-side set is empty; otherwise
      -- `√n > 0` and the following algebra applies.
      by_cases hn0 : n = 0
      · subst hn0
        -- Δ_n definitionally is Real.sqrt 0 * ... = 0.
        have h_Δ_zero : Δ_n = 0 := by
          simp only [hΔ_def, Nat.cast_zero, Real.sqrt_zero, zero_mul]
        rw [h_Δ_zero, abs_zero] at hX
        have hM_le_max : M_main ≤ max M_main M_init := le_max_left _ _
        linarith [hM_main_pos, hM_le_max, hX]
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
      have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR_pos
      have h_sqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt h_sqrt_pos
      have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
      -- Pointwise, by the definition of `r_n`,
      --   score_func_seq(X_i) = score_truth(X_i) + (est-θ₀)·ℓ̇(X_i) + r_n(X_i),
      -- so summing and multiplying by `1/√n` gives
      --   LHS_n = S_n + (est-θ₀)·(1/√n)·Σℓ̇ + R_n
      --         = S_n + Δ_n · ((1/n)·Σℓ̇) + R_n,
      -- because `Δ_n = √n·(est-θ₀)` and `(√n)² = n` for `n > 0`.
      -- Consequently,
      --   LHS_n = S_n + Δ_n · ((1/n)·Σℓ̇) + R_n
      --         = S_n + Δ_n · (D_n - Ĩ) + R_n.
      have h_sum_split : ∀ i : Fin n,
          score_func_seq n X (X i)
            = score_truth (X i)
              + (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)
              + (score_func_seq n X (X i)
                  - score_truth (X i)
                  - (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) := by
        intro i; ring
      have h_sum_eq :
          (∑ i : Fin n, score_func_seq n X (X i))
            = (∑ i : Fin n, score_truth (X i))
              + (estimator n X - θ₀)
                  * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
              + (∑ i : Fin n,
                  (score_func_seq n X (X i)
                    - score_truth (X i)
                    - (estimator n X - θ₀)
                      * (score_l_dot : Ω → ℝ) (X i))) := by
        rw [Finset.mul_sum]
        rw [show (∑ i : Fin n, score_func_seq n X (X i))
            = (∑ i : Fin n,
                (score_truth (X i)
                  + (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)
                  + (score_func_seq n X (X i)
                      - score_truth (X i)
                      - (estimator n X - θ₀)
                        * (score_l_dot : Ω → ℝ) (X i))))
            from Finset.sum_congr rfl (fun i _ => h_sum_split i)]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have h_identity : LHS_n = S_n + Δ_n * (D_n - Ĩ) + R_n := by
        simp only [hLHS_def, hS_def, hR_def, hD_def, hΔ_def]
        rw [h_sum_eq]
        -- The identity reduces to the algebraic bridge
        --   (√n)⁻¹ · (est-θ₀) · Σℓ̇ = √n · (est-θ₀) · n⁻¹ · Σℓ̇
        -- which holds because (√n)⁻¹ = √n · n⁻¹ (multiply both sides by n
        -- and use n = (√n)²).
        have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
          Real.mul_self_sqrt hnR_pos.le
        -- (√n)⁻¹ = √n · n⁻¹ (using n = √n · √n).
        have h_inv_eq : (Real.sqrt (n : ℝ))⁻¹ = Real.sqrt n * ((n : ℝ)⁻¹) := by
          calc (Real.sqrt (n : ℝ))⁻¹
              = (Real.sqrt n)⁻¹ * 1 := by rw [mul_one]
            _ = (Real.sqrt n)⁻¹ * (Real.sqrt n * Real.sqrt n * (n : ℝ)⁻¹) := by
                rw [h_sqrt_sq, mul_inv_cancel₀ hnR_ne]
            _ = ((Real.sqrt n)⁻¹ * Real.sqrt n) * (Real.sqrt n * (n : ℝ)⁻¹) := by ring
            _ = 1 * (Real.sqrt n * (n : ℝ)⁻¹) := by
                rw [inv_mul_cancel₀ h_sqrt_ne]
            _ = Real.sqrt n * ((n : ℝ)⁻¹) := by rw [one_mul]
        rw [h_inv_eq]
        ring
      -- From h_identity: Δ_n · (Ĩ − D_n) = S_n + R_n − LHS_n.
      have h_rearr : Δ_n * (Ĩ - D_n) = S_n + R_n - LHS_n := by
        have := h_identity
        linarith
      -- Triangle inequality: |Δ_n · (Ĩ − D_n)| ≤ |S_n| + |R_n| + |LHS_n|.
      have h_tri : |Δ_n| * |Ĩ - D_n| ≤ |S_n| + |R_n| + |LHS_n| := by
        rw [← abs_mul, h_rearr]
        calc |S_n + R_n - LHS_n|
            = |S_n + R_n + (-LHS_n)| := by ring_nf
          _ ≤ |S_n + R_n| + |-LHS_n| := abs_add_le _ _
          _ = |S_n + R_n| + |LHS_n| := by rw [abs_neg]
          _ ≤ (|S_n| + |R_n|) + |LHS_n| := by linarith [abs_add_le S_n R_n]
      -- Bounds: after push Not, hcS, hcR, hcLHS, hcD are already strict inequalities.
      have h_R_lt : |R_n| < M_main * Ĩ / 6 := hcR
      have h_LHS_lt : |LHS_n| < M_main * Ĩ / 6 := hcLHS
      have h_S_lt : |S_n| < M_main * Ĩ / 6 := hcS
      have h_D_lt : |D_n| < Ĩ / 2 := hcD
      have h_diff_lower : Ĩ / 2 < |Ĩ - D_n| := by
        have h1 : |Ĩ| - |D_n| ≤ |Ĩ - D_n| := abs_sub_abs_le_abs_sub Ĩ D_n
        have h2 : |Ĩ| = Ĩ := abs_of_pos hĨ_pos
        linarith
      -- |Δ_n| · Ĩ/2 < |Δ_n| · |Ĩ - D_n| ≤ |S_n| + |R_n| + |LHS_n| < M·Ĩ/2.
      have h_lhs_abs : max M_main M_init ≤ |Δ_n| := hX
      have h_Δ_pos : 0 < |Δ_n| :=
        lt_of_lt_of_le hM_main_pos (le_trans (le_max_left _ _) h_lhs_abs)
      have h_lower : |Δ_n| * (Ĩ / 2) < |Δ_n| * |Ĩ - D_n| :=
        (mul_lt_mul_iff_right₀ h_Δ_pos).mpr h_diff_lower
      have h_upper : |S_n| + |R_n| + |LHS_n| < 3 * (M_main * Ĩ / 6) := by linarith
      have h_combined : |Δ_n| * (Ĩ / 2) < M_main * (Ĩ / 2) := by
        have h_lt : |Δ_n| * (Ĩ / 2) < 3 * (M_main * Ĩ / 6) := by
          linarith [h_lower, h_tri, h_upper]
        nlinarith [h_lt]
      have hĨhalf : 0 < Ĩ / 2 := by positivity
      have h_Δ_lt_M : |Δ_n| < M_main :=
        (mul_lt_mul_iff_left₀ hĨhalf).mp h_combined
      -- But |Δ_n| ≥ max M_main M_init ≥ M_main, contradiction.
      linarith [le_max_left M_main M_init, h_lhs_abs]
    -- Apply the union bound to the inclusion.
    have h_meas_bd :
        (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω |
              max M_main M_init ≤ |Real.sqrt n * (estimator n X - θ₀)|}
        ≤ ((Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω |
                Ĩ / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
                  + Ĩ|}
            + (Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω |
                M_main * Ĩ / 6 ≤ |(Real.sqrt n)⁻¹ * (∑ i : Fin n, score_truth (X i))|})
          + ((Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω |
                M_main * Ĩ / 6 ≤ |(Real.sqrt n)⁻¹ *
                  (∑ i : Fin n,
                    (score_func_seq n X (X i)
                      - score_truth (X i)
                      - (estimator n X - θ₀)
                        * (score_l_dot : Ω → ℝ) (X i)))|}
            + (Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω |
                M_main * Ĩ / 6 ≤ |(Real.sqrt n)⁻¹ *
                  (∑ i : Fin n, score_func_seq n X (X i))|}) := by
      refine le_trans (measure_mono h_incl) ?_
      refine le_trans (measure_union_le _ _) ?_
      exact add_le_add (measure_union_le _ _) (measure_union_le _ _)
    -- Apply hM_S, hM_threshold (i.e., S_n bound), and the three eventually-bounds.
    have hS_apply : (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          M_main * Ĩ / 6 ≤ |(Real.sqrt n)⁻¹ * (∑ i : Fin n, score_truth (X i))|}
        ≤ ENNReal.ofReal (ε / 4) := by
      refine le_trans (measure_mono ?_) (hM_S n)
      intro X hX
      simp only [Set.mem_setOf_eq] at hX ⊢
      exact le_trans hM_threshold hX
    -- Sum of four ENNReal.ofReal (ε/4) terms = ENNReal.ofReal ε.
    have hε4_nn : (0 : ℝ) ≤ ε / 4 := by linarith
    have h_sum_eps : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
                      + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4))
                    = ENNReal.ofReal ε := by
      -- Coalesce both inner pairs at once via single rw.
      have h1 : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
                  = ENNReal.ofReal (ε / 4 + ε / 4) :=
        (ENNReal.ofReal_add hε4_nn hε4_nn).symm
      rw [h1]
      rw [(ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ ε/4 + ε/4)
            (by linarith : (0:ℝ) ≤ ε/4 + ε/4)).symm]
      congr 1; ring
    refine le_trans h_meas_bd ?_
    refine le_trans (add_le_add (add_le_add h4 hS_apply) (add_le_add h3 hse)) ?_
    exact h_sum_eps.le

/-- **Step 6 (asymptotic-linear residual decomposition).**

`√n(estimator − θ₀) − (1/Ĩ) · (1/√n) · Σᵢ score_truth(X_i) →_P 0`
under `Pⁿ`, i.e. the asymptotic-linear conclusion in raw functional form.

**Proof strategy.** From the score-equation + Taylor substitution
(same algebraic identity as Step 5):
`(1/√n) Σ score_truth(X_i)
   + √n(estimator − θ₀) · (1/n) Σ ℓ̇(X_i)
   + (1/√n) Σ r_n(X_i) →_P 0`.

Step 4 gives `(1/n) Σ ℓ̇(X_i) →_P −Ĩ`. Combining with Step 5
(`√n(estimator − θ₀) = O_P(1)`):
`√n(estimator − θ₀) · (1/n) Σ ℓ̇(X_i) = −Ĩ · √n(estimator − θ₀) + o_P(1)`.

Step 3 gives `(1/√n) Σ r_n(X_i) →_P 0`.

So the identity becomes
`(1/√n) Σ score_truth(X_i) − Ĩ · √n(estimator − θ₀) + o_P(1) →_P 0`,
i.e. `Ĩ · √n(estimator − θ₀) − (1/√n) Σ score_truth(X_i) →_P 0`.

Dividing through by `Ĩ > 0` (hypothesis `hI_pos`) yields the conclusion.

This is the residual-decomposition output that the main theorem wraps
into `AsymptoticallyLinearAt` form (modulo an `aestronglyMeasurable`
representative shuffle on the influence function side). -/
private lemma step6_residual_oP
    (h : ZEstimatorTaylorCore P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |Real.sqrt n * (estimator n X - θ₀)
                - (1 / efficientInformation S_θ T_nuis v)
                  * ((Real.sqrt n)⁻¹
                    * (∑ i : Fin n, score_truth (X i)))|})
      atTop (𝓝 0) := by
  intro ε hε
  set Ĩ : ℝ := efficientInformation S_θ T_nuis v with hĨ_def
  have hĨ_pos : 0 < Ĩ := h.hI_pos
  have hĨ_ne : Ĩ ≠ 0 := ne_of_gt hĨ_pos
  -- Inner key: for any real η > 0, eventually the residual measure ≤ ENNReal.ofReal η.
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |Real.sqrt n * (estimator n X - θ₀)
                - (1 / Ĩ) * ((Real.sqrt n)⁻¹
                  * (∑ i : Fin n, score_truth (X i)))|}
      ≤ ENNReal.ofReal η := by
    intro η hη
    have hη4 : 0 < η / 4 := by linarith
    have hη4_nn : (0 : ℝ) ≤ η / 4 := by linarith
    -- O_P(1) bound on √n(estimator − θ₀) from Step 5.
    obtain ⟨M_raw, hM_raw⟩ := step5_sqrt_n_consistency h (η / 4) hη4
    set M : ℝ := max M_raw 1 with hM_def
    have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hM_ne : M ≠ 0 := ne_of_gt hM_pos
    have hM_bound : ∀ n,
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | M ≤ |Real.sqrt n * (estimator n X - θ₀)|}
        ≤ ENNReal.ofReal (η / 4) := by
      intro n
      refine le_trans (measure_mono ?_) (hM_raw n)
      intro X hX; exact (le_max_left M_raw 1).trans hX
    -- Thresholds for the o_P(1) ingredients.
    have h_τD_pos : (0 : ℝ) < ε * Ĩ / (3 * M) := by positivity
    have h_τR_pos : (0 : ℝ) < ε * Ĩ / 3 := by positivity
    have h_step4_inst := step4_score_dot_lln h.toZEstimatorTaylorCoreBase (ε * Ĩ / (3 * M)) h_τD_pos
    have h_step3_inst := step3_taylor_remainder_oP h.toZEstimatorTaylorCoreBase (ε * Ĩ / 3) h_τR_pos
    have h_se_inst := h.score_eq (ε * Ĩ / 3) h_τR_pos
    rw [ENNReal.tendsto_nhds_zero] at h_step4_inst h_step3_inst h_se_inst
    have h_step4_le := h_step4_inst (ENNReal.ofReal (η / 4)) (by positivity)
    have h_step3_le := h_step3_inst (ENNReal.ofReal (η / 4)) (by positivity)
    have h_se_le := h_se_inst (ENNReal.ofReal (η / 4)) (by positivity)
    -- Combine the three eventually-bounds into a single eventually.
    filter_upwards [h_step4_le, h_step3_le, h_se_le] with n h4 h3 hse
    -- Set inclusion: residual ≥ ε ⇒ at least one of four sets is hit.
    have h_incl :
        {X : Fin n → Ω |
          ε ≤ |Real.sqrt n * (estimator n X - θ₀)
                - (1 / Ĩ) * ((Real.sqrt n)⁻¹
                  * (∑ i : Fin n, score_truth (X i)))|}
        ⊆ ({X : Fin n → Ω |
              M ≤ |Real.sqrt n * (estimator n X - θ₀)|} ∪
            {X : Fin n → Ω |
              ε * Ĩ / (3 * M) ≤ |(n : ℝ)⁻¹ *
                (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) + Ĩ|})
          ∪ ({X : Fin n → Ω |
                ε * Ĩ / 3 ≤ |(Real.sqrt n)⁻¹ *
                  (∑ i : Fin n,
                    (score_func_seq n X (X i)
                      - score_truth (X i)
                      - (estimator n X - θ₀)
                        * (score_l_dot : Ω → ℝ) (X i)))|} ∪
              {X : Fin n → Ω |
                ε * Ĩ / 3 ≤ |(Real.sqrt n)⁻¹ *
                  (∑ i : Fin n, score_func_seq n X (X i))|}) := by
      intro X hX
      simp only [Set.mem_setOf_eq, Set.mem_union] at hX ⊢
      by_contra hc
      push Not at hc
      obtain ⟨⟨hcΔ, hcD⟩, hcR, hcLHS⟩ := hc
      -- Abbreviations matching Step 5's identity.
      set LHS_n : ℝ :=
        (Real.sqrt n)⁻¹ * (∑ i : Fin n, score_func_seq n X (X i)) with hLHS_def
      set S_n : ℝ :=
        (Real.sqrt n)⁻¹ * (∑ i : Fin n, score_truth (X i)) with hS_def
      set R_n : ℝ :=
        (Real.sqrt n)⁻¹ *
          (∑ i : Fin n,
            (score_func_seq n X (X i)
              - score_truth (X i)
              - (estimator n X - θ₀)
                * (score_l_dot : Ω → ℝ) (X i))) with hR_def
      set D_n : ℝ :=
        (n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) + Ĩ with hD_def
      set Δ_n : ℝ := Real.sqrt n * (estimator n X - θ₀) with hΔ_def
      -- n = 0 special case: Δ_0 = S_0 = 0, so |residual| = 0 < ε.
      by_cases hn0 : n = 0
      · subst hn0
        have h_Δ_zero : Δ_n = 0 := by
          simp only [hΔ_def, Nat.cast_zero, Real.sqrt_zero, zero_mul]
        have h_S_zero : S_n = 0 := by
          simp only [hS_def, Nat.cast_zero, Real.sqrt_zero, inv_zero,
            zero_mul]
        rw [h_Δ_zero, h_S_zero, mul_zero, sub_zero, abs_zero] at hX
        linarith
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
      have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR_pos
      have h_sqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt h_sqrt_pos
      have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
      -- Algebraic identity LHS_n = S_n + Δ_n · (D_n − Ĩ) + R_n (same as Step 5).
      have h_sum_split : ∀ i : Fin n,
          score_func_seq n X (X i)
            = score_truth (X i)
              + (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)
              + (score_func_seq n X (X i)
                  - score_truth (X i)
                  - (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) := by
        intro i; ring
      have h_sum_eq :
          (∑ i : Fin n, score_func_seq n X (X i))
            = (∑ i : Fin n, score_truth (X i))
              + (estimator n X - θ₀)
                  * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
              + (∑ i : Fin n,
                  (score_func_seq n X (X i)
                    - score_truth (X i)
                    - (estimator n X - θ₀)
                      * (score_l_dot : Ω → ℝ) (X i))) := by
        rw [Finset.mul_sum]
        rw [show (∑ i : Fin n, score_func_seq n X (X i))
            = (∑ i : Fin n,
                (score_truth (X i)
                  + (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)
                  + (score_func_seq n X (X i)
                      - score_truth (X i)
                      - (estimator n X - θ₀)
                        * (score_l_dot : Ω → ℝ) (X i))))
            from Finset.sum_congr rfl (fun i _ => h_sum_split i)]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have h_identity : LHS_n = S_n + Δ_n * (D_n - Ĩ) + R_n := by
        simp only [hLHS_def, hS_def, hR_def, hD_def, hΔ_def]
        rw [h_sum_eq]
        have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
          Real.mul_self_sqrt hnR_pos.le
        have h_inv_eq : (Real.sqrt (n : ℝ))⁻¹ = Real.sqrt n * ((n : ℝ)⁻¹) := by
          calc (Real.sqrt (n : ℝ))⁻¹
              = (Real.sqrt n)⁻¹ * 1 := by rw [mul_one]
            _ = (Real.sqrt n)⁻¹ * (Real.sqrt n * Real.sqrt n * (n : ℝ)⁻¹) := by
                rw [h_sqrt_sq, mul_inv_cancel₀ hnR_ne]
            _ = ((Real.sqrt n)⁻¹ * Real.sqrt n) * (Real.sqrt n * (n : ℝ)⁻¹) := by ring
            _ = 1 * (Real.sqrt n * (n : ℝ)⁻¹) := by
                rw [inv_mul_cancel₀ h_sqrt_ne]
            _ = Real.sqrt n * ((n : ℝ)⁻¹) := by rw [one_mul]
        rw [h_inv_eq]
        ring
      -- Rearranged residual: Δ_n − S_n/Ĩ = (1/Ĩ) · (R_n − LHS_n + Δ_n · D_n).
      have h_target_eq : Δ_n - (1 / Ĩ) * S_n
          = (1 / Ĩ) * (R_n - LHS_n + Δ_n * D_n) := by
        have h := h_identity
        field_simp
        linarith
      -- Strict bounds from the by_contra/push Not.
      have hcD' : |D_n| < ε * Ĩ / (3 * M) := hcD
      have hcR' : |R_n| < ε * Ĩ / 3 := hcR
      have hcLHS' : |LHS_n| < ε * Ĩ / 3 := hcLHS
      have hcΔ' : |Δ_n| < M := hcΔ
      -- Triangle inequality on the rearranged residual.
      have h1Ĩ_nn : 0 ≤ 1 / Ĩ := by positivity
      have h_neg_LHS : |-LHS_n| = |LHS_n| := abs_neg _
      have h_split_ΔD : |Δ_n * D_n| = |Δ_n| * |D_n| := abs_mul _ _
      have h_tri : |Δ_n - (1 / Ĩ) * S_n|
          ≤ (1 / Ĩ) * (|R_n| + |LHS_n| + |Δ_n| * |D_n|) := by
        rw [h_target_eq, abs_mul, abs_of_nonneg h1Ĩ_nn]
        refine mul_le_mul_of_nonneg_left ?_ h1Ĩ_nn
        calc |R_n - LHS_n + Δ_n * D_n|
            = |R_n + (-LHS_n) + Δ_n * D_n| := by ring_nf
          _ ≤ |R_n + (-LHS_n)| + |Δ_n * D_n| := abs_add_le _ _
          _ ≤ (|R_n| + |-LHS_n|) + |Δ_n * D_n| := by
              linarith [abs_add_le R_n (-LHS_n)]
          _ = |R_n| + |LHS_n| + |Δ_n| * |D_n| := by
              rw [h_neg_LHS, h_split_ΔD]
      -- Bound the cross term: |Δ_n| · |D_n| < M · (ε·Ĩ/(3M)) = ε·Ĩ/3.
      have h_prod_lt : |Δ_n| * |D_n| < ε * Ĩ / 3 := by
        have h_step1 : |Δ_n| * |D_n| ≤ M * |D_n| :=
          mul_le_mul_of_nonneg_right hcΔ'.le (abs_nonneg _)
        have h_step2 : M * |D_n| < M * (ε * Ĩ / (3 * M)) :=
          mul_lt_mul_of_pos_left hcD' hM_pos
        have h_step3' : M * (ε * Ĩ / (3 * M)) = ε * Ĩ / 3 := by
          field_simp
        linarith
      -- Sum: < ε·Ĩ.
      have h_sum_lt : |R_n| + |LHS_n| + |Δ_n| * |D_n| < ε * Ĩ := by linarith
      -- Final residual bound: |Δ_n − S_n/Ĩ| < ε.
      have h_target_lt : |Δ_n - (1 / Ĩ) * S_n| < ε := by
        calc |Δ_n - (1 / Ĩ) * S_n|
            ≤ (1 / Ĩ) * (|R_n| + |LHS_n| + |Δ_n| * |D_n|) := h_tri
          _ < (1 / Ĩ) * (ε * Ĩ) :=
              mul_lt_mul_of_pos_left h_sum_lt (by positivity)
          _ = ε := by field_simp
      exact absurd hX (not_le.mpr h_target_lt)
    -- Apply the union bound to the inclusion.
    have h_meas_bd :
        (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω |
              ε ≤ |Real.sqrt n * (estimator n X - θ₀)
                    - (1 / Ĩ) * ((Real.sqrt n)⁻¹
                      * (∑ i : Fin n, score_truth (X i)))|}
        ≤ ((Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω | M ≤ |Real.sqrt n * (estimator n X - θ₀)|}
            + (Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω |
                ε * Ĩ / (3 * M) ≤ |(n : ℝ)⁻¹ *
                  (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) + Ĩ|})
          + ((Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω |
                ε * Ĩ / 3 ≤ |(Real.sqrt n)⁻¹ *
                  (∑ i : Fin n,
                    (score_func_seq n X (X i)
                      - score_truth (X i)
                      - (estimator n X - θ₀)
                        * (score_l_dot : Ω → ℝ) (X i)))|}
            + (Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω |
                ε * Ĩ / 3 ≤ |(Real.sqrt n)⁻¹ * (∑ i : Fin n,
                  score_func_seq n X (X i))|}) := by
      refine le_trans (measure_mono h_incl) ?_
      refine le_trans (measure_union_le _ _) ?_
      exact add_le_add (measure_union_le _ _) (measure_union_le _ _)
    have h_M_le : (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | M ≤ |Real.sqrt n * (estimator n X - θ₀)|}
        ≤ ENNReal.ofReal (η / 4) := hM_bound n
    have h_sum_eps : ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4)
                      + (ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4))
                    = ENNReal.ofReal η := by
      have h1 : ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4)
                  = ENNReal.ofReal (η / 4 + η / 4) :=
        (ENNReal.ofReal_add hη4_nn hη4_nn).symm
      rw [h1]
      rw [(ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ η/4 + η/4)
            (by linarith : (0:ℝ) ≤ η/4 + η/4)).symm]
      congr 1; ring
    refine le_trans h_meas_bd ?_
    refine le_trans (add_le_add (add_le_add h_M_le h4) (add_le_add h3 hse)) ?_
    exact h_sum_eps.le
  -- Conclude the Tendsto from the real-`η` key, casing on c = ⊤.
  rw [ENNReal.tendsto_nhds_zero]
  intro c hc
  by_cases hc_inf : c = ⊤
  · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
  · have hc_real_pos : 0 < ENNReal.toReal c :=
      ENNReal.toReal_pos hc.ne' hc_inf
    filter_upwards [key (ENNReal.toReal c) hc_real_pos] with n hn
    exact hn.trans (ENNReal.ofReal_toReal hc_inf).le

end StepLemmas

namespace ZEstimatorTaylorCore

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
variable {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
variable [T_nuis.HasOrthogonalProjection] {v : Θ}
variable {estimator : ∀ n, (Fin n → Ω) → ℝ}
variable {score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ)}
variable {score_truth : Ω → ℝ}
variable {donsker_class : Set (Ω → ℝ)}
variable {score_l_dot : Lp ℝ 2 P}
variable {θ₀ : ℝ}

/-- vdV thm:25.54 — discharge of `asympLinear_25_54` from book primitives.

Given the strong-regularity bundle `ZEstimatorTaylorHyp`, the Z-estimator
`estimator` is asymptotically linear at `P` with influence function
`(1/Ĩ_{θ₀,η₀}) • ℓ̃_{θ₀,η₀}` and centering `θ₀`.

**Proof outline (Taylor route — vdV §25.5 strong-regularity remark):**

The score equation `score_eq` says `(1/√n) Σᵢ score_func_seq n X (X_i) →_P 0`.
Substitute the empirical Taylor identity (encoded via `score_l2_taylor` and
the function `score_l_dot`):
  `score_func_seq n X (X_i) = score_truth(X_i)
                                + (estimator − θ₀) · ℓ̇(X_i)
                                + r_n(X_i)`
where `r_n` is the empirical L²-Taylor remainder.

After rearrangement under `Pⁿ`:
  `(1/√n) Σ score_truth(X_i)
     + √n(estimator − θ₀) · (1/n) Σ ℓ̇(X_i)
     + (1/√n) Σ r_n(X_i) →_P 0`.

The proof combines four `o_P` ingredients:

* **Step 3** (`step3_taylor_remainder_oP`): `(1/√n) Σ r_n(X_i) →_P 0`
  via Cauchy-Schwarz on `score_l2_taylor`.
* **Step 4** (`step4_score_dot_lln`): `(1/n) Σ ℓ̇(X_i) →_P −Ĩ`
  via iid LLN + the Bartlett identity `score_l_dot_bartlett`.
* **Step 5** (`step5_sqrt_n_consistency`): `√n(estimator − θ₀) = O_P(1)`
  derived from Steps 3–4 + score equation + L²-CLT bound on the truth.
* **Step 6** (`step6_residual_oP`): combines Steps 3–5 to extract
  `√n(estimator − θ₀) − (1/Ĩ)·(1/√n)·Σ score_truth(X_i) →_P 0`.

The main theorem unwraps Step 6 into `AsymptoticallyLinearAt` form by
substituting the influence-function representation
`((1/Ĩ) • efficientScore : Lp ℝ 2 P)(X_i) = (1/Ĩ) · score_truth(X_i)`
modulo `truth_aeEq` and the `Lp.coeFn`/`smul` distributivity on Lp.

The book's original Donsker route: Step 1 (`step1_random_index_oP`)
invokes Lem 19.24 to produce `G_n(score_func_seq) − G_n(score_truth) →_P 0`;
Step 2 (`step2_score_eq_to_no_bias`) produces the corresponding algebraic
rewrite using `no_bias`. These lemmas give the connection to vdV's §25.5
Donsker proof, while the theorem below uses the Taylor argument. -/
theorem zEstimator_asympLinear_of_taylor
    (h : ZEstimatorTaylorCore P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀) :
    AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) θ₀ := by
  -- Goal: ∀ ε > 0, Pⁿ {X | ε ≤ |√n (estimator − θ₀)
  --                            − (1/√n) Σᵢ ((1/Ĩ) • ℓ̃)(X_i)|} → 0.
  intro ε hε
  set Ĩ : ℝ := efficientInformation S_θ T_nuis v with hĨ_def
  set effScoreLp : Lp ℝ 2 P :=
    ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) with h_eff_def
  -- Step 6 yields the residual in `score_truth` form:
  --   Pⁿ {X | ε ≤ |√n(est-θ₀) - (1/Ĩ)·(1/√n)·Σ score_truth(X_i)|} → 0.
  have h6 := step6_residual_oP h ε hε
  -- (a) P-a.e. equality `((((1/Ĩ) • effScoreLp) : Lp).coeFn) ω = (1/Ĩ) * score_truth ω`
  -- via `Lp.coeFn_smul` + `truth_aeEq`. Note `Submodule.coe_smul` makes the
  -- ↥(L2ZeroMean P) → Lp coercion commute with smul (defeq for submodules),
  -- so `((1/Ĩ) • efficientScore : ↥)` coerces to `(1/Ĩ) • effScoreLp`.
  have h_eq_P :
      (fun ω => ((((1 / Ĩ) • effScoreLp) : Lp ℝ 2 P) : Ω → ℝ) ω)
        =ᵐ[P] fun ω => (1 / Ĩ) * score_truth ω := by
    have h_truth_aeEq : (effScoreLp : Ω → ℝ) =ᵐ[P] score_truth := h.truth_aeEq
    filter_upwards [Lp.coeFn_smul ((1 / Ĩ) : ℝ) effScoreLp, h_truth_aeEq]
      with ω h_smul h_truth
    rw [h_smul]
    change (1 / Ĩ) * _ = _
    rw [h_truth]
  -- Per-coordinate Pⁿ-a.e. lift via `measurePreserving_eval` (the i-th coord
  -- projection is measure-preserving from `Pⁿ` to `P`).
  refine h6.congr (fun n => ?_)
  refine MeasureTheory.measure_congr ?_
  have h_eq_Pi : ∀ (i : Fin n),
      (fun X : Fin n → Ω =>
          ((((1 / Ĩ) • effScoreLp) : Lp ℝ 2 P) : Ω → ℝ) (X i))
        =ᵐ[Measure.pi (fun _ : Fin n => P)]
          fun X => (1 / Ĩ) * score_truth (X i) := by
    intro i
    have h_mp :
        MeasureTheory.MeasurePreserving (Function.eval i)
          (Measure.pi (fun _ : Fin n => P)) P :=
      MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => P) i
    exact h_eq_P.comp_tendsto h_mp.quasiMeasurePreserving.tendsto_ae
  -- Pⁿ-a.e. set equality of the AL set and Step 6's set, via the per-coord
  -- lift + sum congruence + algebraic rearrangement
  --   `(1/√n) · Σᵢ ((1/Ĩ) • effScoreLp)(X_i) = (1/Ĩ) · ((1/√n) · Σᵢ score_truth(X_i))`.
  have h_eq_sum : ∀ᵐ X ∂(Measure.pi (fun _ : Fin n => P)),
      ∀ (i : Fin n),
        ((((1 / Ĩ) • effScoreLp) : Lp ℝ 2 P) : Ω → ℝ) (X i)
        = (1 / Ĩ) * score_truth (X i) := by
    rw [ae_all_iff]
    exact h_eq_Pi
  filter_upwards [h_eq_sum] with X h_X
  -- Goal: `{X | …Step 6 inner…} X = {X | …AL inner…} X` (Prop equality).
  -- Sum identity from `h_X` (per-coord) + `Submodule.coe_smul` defeq:
  --   `↑↑↑((1/Ĩ) • efficientScore : ↥)` = `↑↑((1/Ĩ) • effScoreLp)` via `show`.
  have h_sum_eq :
      (∑ i : Fin n,
          ((((1 / efficientInformation S_θ T_nuis v) • efficientScore S_θ T_nuis v
              : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) (X i))
        = (1 / Ĩ) * (∑ i : Fin n, score_truth (X i)) := by
    change (∑ i : Fin n, ((((1 / Ĩ) • effScoreLp) : Lp ℝ 2 P) : Ω → ℝ) (X i)) = _
    rw [Finset.sum_congr rfl (fun i _ => h_X i), ← Finset.mul_sum]
  -- Inner-expression equality: Step 6 inner = AL inner.
  have h_inner_eq :
      Real.sqrt ↑n * (estimator n X - θ₀)
          - 1 / efficientInformation S_θ T_nuis v
            * ((Real.sqrt ↑n)⁻¹ * (∑ i : Fin n, score_truth (X i)))
        = Real.sqrt ↑n * (estimator n X - θ₀)
          - (Real.sqrt ↑n)⁻¹
            * (∑ i : Fin n,
                ((((1 / efficientInformation S_θ T_nuis v) • efficientScore S_θ T_nuis v
                    : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) (X i)) := by
    rw [h_sum_eq, show (1 : ℝ) / efficientInformation S_θ T_nuis v = 1 / Ĩ from rfl]
    ring
  -- Close via `congrArg` lifting `h_inner_eq` to `(ε ≤ |·|)`.
  exact congrArg (fun x : ℝ => ε ≤ |x|) h_inner_eq

/-- Constructs `EfficientScoreEqAssumptions` from the Taylor conditions and
the EIF hypotheses `h_mem` and `h_dψ`. -/
def toEfficientScoreEqAssumptions
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    (h : ZEstimatorTaylorCore P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀)
    (h_mem :
      (1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v ∈ T)
    (h_dψ : ∀ g : T,
      dψ g
        = (1 / efficientInformation S_θ T_nuis v)
            * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    EfficientScoreEqAssumptions P Θ S_θ T_nuis v T dψ estimator θ₀ where
  h_mem := h_mem
  h_dψ := h_dψ
  hI_pos := h.hI_pos
  asympLinear_25_54 := zEstimator_asympLinear_of_taylor h

end ZEstimatorTaylorCore

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
