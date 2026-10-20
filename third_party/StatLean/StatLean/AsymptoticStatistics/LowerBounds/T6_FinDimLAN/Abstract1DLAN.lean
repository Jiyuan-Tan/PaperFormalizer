module
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.ForMathlib.QMDAnalytic
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs
public import StatLean.AsymptoticStatistics.DQM.Defs
public import StatLean.AsymptoticStatistics.ParametricFamily.FisherInformation
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.LANExpansion
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

/-!
# 1D LAN expansion adapter for the abstract `QMDPath` (vdV §25.3)

This file bridges `Core.QMDPath` (the abstract quadratic-mean-differentiable
path, without the bounded-density specialisation) to the project's 1-D
`DifferentiableQuadraticMean` / `LAN_expansion_iii` machinery. It builds the
`L²(γ.dominating)` membership of `√p_t`, of `score · √p_0`, and of the QMD
residual `√p_t - √p_0 - (t/2)·score·√p_0`; wraps the path as a 1-D
`ParametricFamily`; establishes its `DifferentiableQuadraticMean`; and applies
`LAN_expansion_iii` at `k = 1` to obtain the LAN expansion.

Headline declarations: `QMDPath.to1DParametricFamily`, `QMDPath.dqm`,
`QMDPath.lanExpansion1D`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace QMDPath

open AsymptoticStatistics.Core.Hilbert

/-- L²(γ.dominating)-membership of `√p_t` for any `t`.

For each `t`, `(γ.curve t)` is a probability measure absolutely continuous
w.r.t. `γ.dominating`, and `γ.dominating` is σ-finite. The conclusion is the
`RnDerivSqrt.memLp_sqrt_rnDeriv` Hellinger-type bound:
`‖√p_t‖²_{L²(γ.dominating)} = (γ.curve t)(univ) = 1`. -/
theorem memLp_sqrt_rnDeriv (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (t : ℝ) :
    MemLp (fun ω => Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal)
      2 γ.dominating := by
  haveI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  haveI : SigmaFinite γ.dominating := γ.dominating_sigmaFinite
  exact AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
    (γ.curve_absContinuous t)

/-- L²(γ.dominating)-membership of `score · √p_0`.

The score is typed `↥(L2ZeroMean P)`, hence `(γ.score : Ω → ℝ) ∈ L²(P)`.
With `P ≪ γ.dominating` (from `curve_at_zero` + `curve_absContinuous 0`)
and `γ.dominating` σ-finite, the bridge `withDensity_rnDeriv_eq` plus
`integrable_withDensity_iff` translates `∫ score² dP < ∞` (given by
`Lp.memLp γ.score`) to `∫ (score · √p_0)² dγ.dominating < ∞`.

This is the *dual* of
`RnDerivSqrt.memLp_two_of_memLp_two_mul_sqrt_rnDeriv` (which goes the
other direction, μ → P). The two are symmetric uses of the same
`integrable_withDensity_iff` bridge.

We bypass the `qmd_limit` route (`memLp_two_score_mul_sqrt_of_qmd`)
because the score is typed against `P` (not `γ.dominating`); for the
score-term-at-zero specifically, the direct `P ≪ γ.dominating` route
is cleaner than re-deriving an L²(`γ.dominating`)-equivalent statement
from the abstract `qmd_limit`. -/
theorem memLp_score_term_at_zero (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P) :
    MemLp (fun ω =>
        (γ.score : Ω → ℝ) ω
          * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
      2 γ.dominating := by
  haveI : SigmaFinite γ.dominating := γ.dominating_sigmaFinite
  -- `P ≪ γ.dominating` from `curve_at_zero` + `curve_absContinuous 0`.
  have hP_ac : P ≪ γ.dominating := by
    have h0 := γ.curve_absContinuous 0
    rwa [γ.curve_at_zero] at h0
  -- The score, as the underlying function of an `L²(P)` element, is in `L²(P)`.
  have h_score_memLp : MemLp ((γ.score : Lp ℝ 2 P) : Ω → ℝ) 2 P :=
    Lp.memLp _
  -- Square-integrability of the score under `P`.
  have h_score_sq_int :
      Integrable (fun ω => (γ.score : Ω → ℝ) ω ^ 2) P :=
    h_score_memLp.integrable_sq
  -- The canonical Lp representative is `StronglyMeasurable`.
  have h_score_sm : StronglyMeasurable ((γ.score : Lp ℝ 2 P) : Ω → ℝ) :=
    Lp.stronglyMeasurable _
  have h_score_sm' : StronglyMeasurable (fun ω => (γ.score : Ω → ℝ) ω) :=
    h_score_sm
  -- Pointwise rewrite key: `(curve 0).rnDeriv γ.dominating = P.rnDeriv γ.dominating`
  -- using `curve_at_zero : γ.curve 0 = P`.
  have h_curve0_eq : (γ.curve 0).rnDeriv γ.dominating
        = P.rnDeriv γ.dominating := by
    rw [γ.curve_at_zero]
  -- Square-root of the rnDeriv is measurable.
  have h_sqrt_meas : Measurable
      (fun ω => Real.sqrt (P.rnDeriv γ.dominating ω).toReal) :=
    (Measure.measurable_rnDeriv P γ.dominating).ennreal_toReal.sqrt
  -- AEStronglyMeasurability of the product on `γ.dominating`.
  have h_prod_meas :
      AEStronglyMeasurable
        (fun ω => (γ.score : Ω → ℝ) ω
          * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
        γ.dominating := by
    refine h_score_sm'.aestronglyMeasurable.mul ?_
    rw [h_curve0_eq]
    exact h_sqrt_meas.aestronglyMeasurable
  -- Reduce `MemLp 2` to `Integrable (·²)`.
  rw [memLp_two_iff_integrable_sq h_prod_meas]
  -- Pointwise: `(score · √p_0)² = score² · p_0.toReal`,
  -- using `(curve 0).rnDeriv = P.rnDeriv`.
  have h_pw :
      (fun ω => ((γ.score : Ω → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal) ^ 2)
        = fun ω => (γ.score : Ω → ℝ) ω ^ 2
            * (P.rnDeriv γ.dominating ω).toReal := by
    funext ω
    have hpt : ((γ.curve 0).rnDeriv γ.dominating ω)
        = P.rnDeriv γ.dominating ω := congrFun h_curve0_eq ω
    rw [hpt, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  rw [h_pw]
  -- Use `integrable_withDensity_iff` to translate
  -- `∫ score² · p_0 dγ.dominating < ∞ ⟺ ∫ score² dP < ∞` (the latter is `h_score_sq_int`).
  have hP_eq : P = γ.dominating.withDensity (P.rnDeriv γ.dominating) :=
    (Measure.withDensity_rnDeriv_eq P γ.dominating hP_ac).symm
  have h_iff := MeasureTheory.integrable_withDensity_iff
      (Measure.measurable_rnDeriv P γ.dominating)
      (Measure.rnDeriv_lt_top P γ.dominating)
      (g := fun ω => (γ.score : Ω → ℝ) ω ^ 2)
  rw [← hP_eq] at h_iff
  exact h_iff.mp h_score_sq_int

/-- The QMD residual at scale `t`:
`√p_t(ω) − √p_0(ω) − (t/2) · score(ω) · √p_0(ω)`.

Matches the pointwise form of the structure's `qmd_limit` lambda and of
`ForMathlib.QMDAnalytic.qmdRem` with `g := (γ.score : Ω → ℝ)`. The DQM
bridge uses this as the residual function up to the `(1/2)·⟨h, ℓ⟩`
re-norming dictated by `DifferentiableQuadraticMean.isLittleO`. -/
noncomputable def qmdResidual (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (t : ℝ) : Ω → ℝ := fun ω =>
  Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
    - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
    - (t / 2) * (γ.score : Ω → ℝ) ω
        * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal

/-- L²(γ.dominating)-membership of the QMD residual.

Each summand is `MemLp 2 γ.dominating`:
* `√p_t` and `√p_0` by `memLp_sqrt_rnDeriv`.
* `(t/2) · score · √p_0` by `memLp_score_term_at_zero` rescaled with
  `MemLp.const_mul`.

The overall membership follows by `MemLp.sub` applied twice. -/
theorem residual_memLp (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P) (t : ℝ) :
    MemLp (qmdResidual γ t) 2 γ.dominating := by
  -- Three L² ingredients.
  have h_pt : MemLp (fun ω =>
      Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal) 2 γ.dominating :=
    memLp_sqrt_rnDeriv γ t
  have h_p0 : MemLp (fun ω =>
      Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal) 2 γ.dominating :=
    memLp_sqrt_rnDeriv γ 0
  have h_score_p0 : MemLp (fun ω =>
      (γ.score : Ω → ℝ) ω
        * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
      2 γ.dominating := memLp_score_term_at_zero γ
  -- Rescale `score · √p_0` by `t/2`. Pointwise:
  -- `(t/2) * score * √p_0 = (t/2) * (score * √p_0)`.
  have h_scaled : MemLp (fun ω =>
      (t / 2) * (γ.score : Ω → ℝ) ω
        * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
      2 γ.dominating := by
    have h := h_score_p0.const_mul (t / 2)
    -- `h : MemLp (fun ω => (t/2) * ((γ.score) ω * √p_0)) 2 γ.dominating`,
    -- rewrite to the associativity-shifted form used in `qmdResidual`.
    have h_eq : (fun ω =>
          (t / 2) * ((γ.score : Ω → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal))
        = fun ω =>
          (t / 2) * (γ.score : Ω → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal := by
      funext ω; ring
    rw [h_eq] at h
    exact h
  -- Combine via `MemLp.sub`.
  unfold qmdResidual
  exact (h_pt.sub h_p0).sub h_scaled

/-! ### Step 2. The 1D `ParametricFamily` adapter

Wrap the abstract path γ as a `ParametricFamily Ω (EuclideanSpace ℝ (Fin 1))`
indexed by `EuclideanSpace ℝ (Fin 1)` (the parameter type expected by
`LAN_expansion_iii`, invoked at `k = 1` in `lanExpansion1D`).

Density: `((curve θ).rnDeriv γ.dominating).toReal`, with
`θ ∈ EuclideanSpace ℝ (Fin 1)` extracted as `θ 0 : ℝ`. Mirrors
`boundedDensityPath_to1DParametricFamily` modulo `P → γ.dominating` for
the dominating measure. -/
noncomputable def to1DParametricFamily
    (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P) :
    AsymptoticStatistics.ParametricFamily Ω
      (EuclideanSpace ℝ (Fin 1)) where
  density θ ω := ((γ.curve (θ 0)).rnDeriv γ.dominating ω).toReal
  density_meas _ :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  density_nonneg _ _ := ENNReal.toReal_nonneg

/-- The 1D score function as a `EuclideanSpace ℝ (Fin 1)`-valued map:
package the scalar `γ.score(ω) ∈ ℝ` into the singleton vector
`EuclideanSpace.single 0 (γ.score(ω))`. -/
noncomputable def score1D
    (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P) :
    Ω → EuclideanSpace ℝ (Fin 1) :=
  fun ω => EuclideanSpace.single 0 (((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω)

/-- For `θ : EuclideanSpace ℝ (Fin 1)`, `‖θ‖² = (θ 0)²`. -/
private lemma euclideanSpace_norm_sq_fin1 (θ : EuclideanSpace ℝ (Fin 1)) :
    ‖θ‖ ^ 2 = θ 0 ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  have hsum_nn : 0 ≤ ∑ i : Fin 1, ‖θ i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.sq_sqrt hsum_nn]
  simp

/-- For `θ : EuclideanSpace ℝ (Fin 1)`, `‖θ‖ = |θ 0|`. -/
private lemma euclideanSpace_norm_fin1 (θ : EuclideanSpace ℝ (Fin 1)) :
    ‖θ‖ = |θ 0| := by
  have h_sq := euclideanSpace_norm_sq_fin1 θ
  have h_norm_nn : 0 ≤ ‖θ‖ := norm_nonneg _
  have h_abs_nn : 0 ≤ |θ 0| := abs_nonneg _
  nlinarith [h_sq, sq_abs (θ 0), Real.sq_sqrt h_norm_nn,
    Real.sqrt_sq h_norm_nn, Real.sqrt_sq h_abs_nn]

/-- The pointwise DQM-residual at shift `h ∈ EuclideanSpace ℝ (Fin 1)`
equals `qmdResidual γ (h 0) ω`. The `(1/2)·⟪h, score1D⟫` re-normings
unwind to `(h 0 / 2) · score(ω)`. -/
private lemma dqm_residual_pointwise_eq
    (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (h : EuclideanSpace ℝ (Fin 1)) (ω : Ω) :
    (to1DParametricFamily γ).sqrtDensity (0 + h) ω
      - (to1DParametricFamily γ).sqrtDensity 0 ω
      - (1/2 : ℝ) * @inner ℝ _ _ h (score1D γ ω)
          * (to1DParametricFamily γ).sqrtDensity 0 ω
    = qmdResidual γ (h 0) ω := by
  unfold AsymptoticStatistics.ParametricFamily.sqrtDensity
    to1DParametricFamily qmdResidual score1D
  have h_inner :
      @inner ℝ _ _ h (EuclideanSpace.single 0 (((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω))
        = ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω * h 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_one]
    have h_single : EuclideanSpace.single (0 : Fin 1)
        (((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω) (0 : Fin 1)
          = ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω := by
      simp
    rw [h_single]
    change ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω * h 0
        = ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω * h 0
    rfl
  have h_zero_apply : ((0 : EuclideanSpace ℝ (Fin 1)) 0) = 0 := rfl
  have h_add_apply : ((0 + h) 0) = h 0 := by rw [zero_add]
  change Real.sqrt ((γ.curve ((0 + h) 0)).rnDeriv γ.dominating ω).toReal
        - Real.sqrt ((γ.curve
            ((0 : EuclideanSpace ℝ (Fin 1)) 0)).rnDeriv γ.dominating ω).toReal
        - (1/2 : ℝ) *
            @inner ℝ _ _ h (EuclideanSpace.single 0 (((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω))
            * Real.sqrt ((γ.curve
                ((0 : EuclideanSpace ℝ (Fin 1)) 0)).rnDeriv γ.dominating ω).toReal
      = Real.sqrt ((γ.curve (h 0)).rnDeriv γ.dominating ω).toReal
        - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
        - (h 0 / 2) * ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
  rw [h_zero_apply, h_add_apply, h_inner]
  ring

/-- The DQM Hellinger residual function (as a function of ω, parameterised
by h) equals `fun ω ↦ qmdResidual γ (h 0) ω`. -/
private lemma dqm_residual_funext
    (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (h : EuclideanSpace ℝ (Fin 1)) :
    (fun ω =>
      (to1DParametricFamily γ).sqrtDensity (0 + h) ω
        - (to1DParametricFamily γ).sqrtDensity 0 ω
        - (1/2 : ℝ) * @inner ℝ _ _ h (score1D γ ω)
            * (to1DParametricFamily γ).sqrtDensity 0 ω)
      = fun ω => qmdResidual γ (h 0) ω :=
  funext fun ω => dqm_residual_pointwise_eq γ h ω

/-- Squared form of the DQM-residual function equality, for use under integrals. -/
private lemma dqm_residual_sq_funext
    (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (h : EuclideanSpace ℝ (Fin 1)) :
    (fun ω =>
      ((to1DParametricFamily γ).sqrtDensity (0 + h) ω
        - (to1DParametricFamily γ).sqrtDensity 0 ω
        - (1/2 : ℝ) * @inner ℝ _ _ h (score1D γ ω)
            * (to1DParametricFamily γ).sqrtDensity 0 ω) ^ 2)
      = fun ω => qmdResidual γ (h 0) ω ^ 2 := by
  funext ω
  rw [dqm_residual_pointwise_eq γ h ω]

/-- Bridge: the Bochner integral of `qmdResidual² dγ.dominating` equals
`(eLpNorm qmdResidual 2 γ.dominating).toReal ^ 2`, given MemLp.
This unifies the abstract structure's `qmd_limit_toReal_sq` derived
form (the corollary of the structure's ℝ≥0∞-form `qmd_limit` field,
giving `(eLpNorm).toReal²/t² → 0`) with DQM's
`∫ residual² ∂μ`-integral form needed for `IsLittleO`. -/
private lemma integral_qmdResidual_sq_eq_eLpNorm_toReal_sq
    (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P) (t : ℝ) :
    ∫ ω, qmdResidual γ t ω ^ 2 ∂γ.dominating
      = (eLpNorm (qmdResidual γ t) 2 γ.dominating).toReal ^ 2 := by
  have h_residual_memLp : MemLp (qmdResidual γ t) 2 γ.dominating :=
    residual_memLp γ t
  have h_sqrt :=
    AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal
      h_residual_memLp
  have h_int_nn : 0 ≤ ∫ ω, qmdResidual γ t ω ^ 2 ∂γ.dominating :=
    integral_nonneg fun _ => sq_nonneg _
  have := congrArg (fun x => x ^ 2) h_sqrt
  rw [Real.sq_sqrt h_int_nn] at this
  exact this

/-- 1D `DifferentiableQuadraticMean` for the abstract `QMDPath`'s
parametric family at `θ = 0`, with score `score1D γ`. The `mem` field
follows from `residual_memLp` + the funext bridge; the `isLittleO` field
follows from `γ.qmd_limit_toReal_sq` (qualitative `Tendsto` along `𝓝[≠] 0`,
derived from the structure's ℝ≥0∞-form `qmd_limit`),
combined with the integral/eLpNorm bridge above and a composition along
`θ ↦ θ 0`. -/
theorem dqm (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P) :
    AsymptoticStatistics.DifferentiableQuadraticMean
      (to1DParametricFamily γ) γ.dominating
      (0 : EuclideanSpace ℝ (Fin 1)) (score1D γ) := by
  refine ⟨?_, ?_⟩
  · -- mem: eventually MemLp.
    -- The MemLp of the residual holds for ALL t, so we can use Eventually.of_forall.
    refine Filter.Eventually.of_forall (fun h => ?_)
    rw [dqm_residual_funext γ h]
    exact residual_memLp γ (h 0)
  · -- isLittleO: ∫ residual² ∂γ.dominating =o[𝓝 0] ‖h‖².
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    -- From `γ.qmd_limit_toReal_sq` (derived from the ℝ≥0∞-form `qmd_limit`),
    -- get an Iio-ball for `(eLpNorm…).toReal²/t² < ε`.
    have h_qmd := AsymptoticStatistics.Core.QMDPath.QMDPath.qmd_limit_toReal_sq γ
    -- The qmd_limit is over `𝓝[≠] 0`. Convert: for `ε > 0`,
    -- there exists δ > 0 such that for all 0 < |t| < δ,
    -- `(eLpNorm …).toReal² / t² < ε`.
    have h_iso : Set.Iio ε ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hε
    have h_ev_t : ∀ᶠ t : ℝ in 𝓝[≠] 0,
        (eLpNorm (fun ω : Ω =>
          Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
            - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
            - (t / 2) * (γ.score : Ω → ℝ) ω
                * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
          2 γ.dominating).toReal ^ 2 / t ^ 2 < ε := h_qmd h_iso
    -- Recast the inner expression as `qmdResidual γ t ω` via funext.
    have h_residual_eq : ∀ t : ℝ,
        (fun ω : Ω =>
          Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
            - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
            - (t / 2) * (γ.score : Ω → ℝ) ω
                * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
          = qmdResidual γ t := by
      intro t; funext ω; rfl
    -- Convert the t-eventually condition to a θ-eventually one along
    -- `θ ↦ θ 0` from EuclideanSpace ℝ (Fin 1) to ℝ. Continuity of `θ ↦ θ 0`
    -- gives `Tendsto (θ ↦ θ 0) (𝓝 0) (𝓝 0)`. Together with the `θ ≠ 0`
    -- side, it tends along the punctured filter only when `θ 0 ≠ 0`.
    -- Strategy: work with the membership form `t ∈ Iio ε` — recover the
    -- `t = 0` case manually (then residual is 0 a.e., int = 0).
    -- 1) Mem-of-nhds for the ε-set in ℝ (without the punctured filter):
    --    use `mem_nhdsWithin` to extract a neighborhood `U` of 0 in ℝ such
    --    that `∀ t ∈ U, t ≠ 0 → ratio t < ε`.
    have h_ev_t' :
        ∀ᶠ t : ℝ in 𝓝 0,
          t ≠ 0 →
            (eLpNorm (qmdResidual γ t) 2 γ.dominating).toReal ^ 2 / t ^ 2 < ε := by
      rw [eventually_nhdsWithin_iff] at h_ev_t
      -- Rewrite the function inside via h_residual_eq.
      filter_upwards [h_ev_t] with t ht ht_ne
      have hres := ht ht_ne
      rw [h_residual_eq t] at hres
      exact hres
    -- 2) Compose with continuity of `θ ↦ θ 0`. Use the norm-domination
    -- `|θ 0| ≤ ‖θ‖` and `Tendsto ‖θ‖ → 0` from continuous_norm.
    have h_proj_tendsto : Tendsto (fun θ : EuclideanSpace ℝ (Fin 1) => θ 0)
        (𝓝 0) (𝓝 0) := by
      have h_norm_tendsto : Tendsto
          (fun θ : EuclideanSpace ℝ (Fin 1) => ‖θ‖) (𝓝 0) (𝓝 0) := by
        have := (continuous_norm (E := EuclideanSpace ℝ (Fin 1))).tendsto 0
        simpa [norm_zero] using this
      -- |θ 0| ≤ ‖θ‖ via euclideanSpace_norm_sq_fin1: ‖θ‖² = (θ 0)².
      rw [Metric.tendsto_nhds_nhds] at h_norm_tendsto ⊢
      intro ε hε
      obtain ⟨δ, hδ_pos, hδ⟩ := h_norm_tendsto ε hε
      refine ⟨δ, hδ_pos, ?_⟩
      intro θ hθ
      have h_norm_lt : ‖θ‖ < ε := by
        have := hδ hθ; simpa [dist_zero_right] using this
      have h_norm_sq_eq : ‖θ‖ ^ 2 = (θ 0) ^ 2 := euclideanSpace_norm_sq_fin1 θ
      have h_abs_le : |θ 0| ≤ ‖θ‖ := by
        have h_sq_le : (θ 0) ^ 2 ≤ ‖θ‖ ^ 2 := by rw [h_norm_sq_eq]
        have := Real.sqrt_le_sqrt h_sq_le
        rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at this
      simp only [dist_zero_right, Real.norm_eq_abs]
      exact lt_of_le_of_lt h_abs_le h_norm_lt
    have h_ev_θ :
        ∀ᶠ θ : EuclideanSpace ℝ (Fin 1) in 𝓝 0,
          θ 0 ≠ 0 →
            (eLpNorm (qmdResidual γ (θ 0)) 2 γ.dominating).toReal ^ 2 / (θ 0) ^ 2
              < ε :=
      h_proj_tendsto.eventually h_ev_t'
    -- Final goal: `‖∫ residual² ∂μ‖ ≤ ε * ‖‖θ‖²‖`.
    simp_rw [dqm_residual_sq_funext γ]
    -- Both sides are nonneg, so we can drop norms:
    have h_int_nn :
        ∀ θ : EuclideanSpace ℝ (Fin 1),
          0 ≤ ∫ ω, qmdResidual γ (θ 0) ω ^ 2 ∂γ.dominating := fun θ =>
      integral_nonneg fun _ => sq_nonneg _
    have h_norm_sq_nn :
        ∀ θ : EuclideanSpace ℝ (Fin 1), 0 ≤ ‖θ‖ ^ 2 := fun _ => sq_nonneg _
    filter_upwards [h_ev_θ] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (h_int_nn θ),
        Real.norm_eq_abs, abs_of_nonneg (h_norm_sq_nn θ)]
    -- Split on θ = 0 vs θ ≠ 0.
    by_cases h_θ_zero : θ = 0
    · -- θ = 0 case: residual is zero (h 0 = 0 ⇒ qmdResidual γ 0 ≡ 0 by definition).
      have h_θ0_zero : (θ : EuclideanSpace ℝ (Fin 1)) 0 = 0 := by
        rw [h_θ_zero]; rfl
      have h_norm_zero : ‖θ‖ = 0 := by rw [h_θ_zero]; exact norm_zero
      have h_norm_sq_zero : ‖θ‖ ^ 2 = 0 := by rw [h_norm_zero]; ring
      -- qmdResidual γ 0 ω = √p_0 - √p_0 - 0 = 0. Use `unfold qmdResidual`.
      have h_res_zero : ∀ ω, qmdResidual γ 0 ω = 0 := by
        intro ω
        unfold qmdResidual
        simp
      have h_int_zero :
          ∫ ω, qmdResidual γ (θ 0) ω ^ 2 ∂γ.dominating = 0 := by
        rw [h_θ0_zero]
        simp [h_res_zero]
      rw [h_int_zero, h_norm_sq_zero]
      simp [le_of_lt hε]
    · -- θ ≠ 0 case: use h_ev_θ directly.
      have h_θ0_ne : θ 0 ≠ 0 := by
        intro h
        apply h_θ_zero
        ext i
        fin_cases i
        exact h
      have hθ_lt := hθ h_θ0_ne
      -- Convert `(eLpNorm).toReal² / (θ 0)² < ε` to bound on integral.
      rw [integral_qmdResidual_sq_eq_eLpNorm_toReal_sq γ (θ 0)]
      -- Now goal: `(eLpNorm…).toReal² ≤ ε · ‖θ‖²`.
      have h_t_sq_pos : 0 < (θ 0) ^ 2 := by positivity
      have h_norm_sq_eq : ‖θ‖ ^ 2 = (θ 0) ^ 2 := euclideanSpace_norm_sq_fin1 θ
      -- From hθ_lt : (eLpNorm…).toReal² / (θ 0)² < ε
      -- Multiply both sides by (θ 0)² > 0.
      have h_le : (eLpNorm (qmdResidual γ (θ 0)) 2 γ.dominating).toReal ^ 2
            ≤ ε * (θ 0) ^ 2 := by
        have := (div_lt_iff₀ h_t_sq_pos).mp hθ_lt
        linarith
      rw [h_norm_sq_eq]
      exact h_le

/-! ### Step 3. LAN expansion bridge

Compose `to1DParametricFamily` + `IsPDFOf` (induced from
`Measure.integral_toReal_rnDeriv`) + `dqm` with
`Asymptotics.LAN.LANExpansion.LAN_expansion_iii` at `k = 1` to obtain the
genuine LAN expansion of the log-likelihood ratio along the abstract
QMDPath. -/

/-- Helper: `IsPDFOf (to1DParametricFamily γ) γ.dominating`. The density
integrates to 1 (since each `curve θ` is a probability measure absolutely
continuous w.r.t. `γ.dominating`) and is `γ.dominating`-integrable. Both
proofs lean on the `[SigmaFinite γ.dominating]` instance from
`Core.QMDPath`. -/
private theorem isPDFOf
    (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P) :
    AsymptoticStatistics.IsPDFOf
      (to1DParametricFamily γ) γ.dominating where
  density_integral_eq_one θ := by
    haveI : IsProbabilityMeasure (γ.curve (θ 0)) := γ.curve_isProbability (θ 0)
    have h_ac : γ.curve (θ 0) ≪ γ.dominating := γ.curve_absContinuous (θ 0)
    have h_int :=
      MeasureTheory.Measure.integral_toReal_rnDeriv
        (μ := γ.curve (θ 0)) (ν := γ.dominating) h_ac
    have h_univ : (γ.curve (θ 0)).real Set.univ = 1 := by
      have := isProbabilityMeasure_iff.mp ‹_›
      simp [Measure.real, this]
    change ∫ ω, ((γ.curve (θ 0)).rnDeriv γ.dominating ω).toReal ∂γ.dominating = 1
    rw [h_int, h_univ]
  density_integrable θ := by
    haveI : IsProbabilityMeasure (γ.curve (θ 0)) := γ.curve_isProbability (θ 0)
    have h_int :=
      MeasureTheory.Measure.integrable_toReal_rnDeriv
        (μ := γ.curve (θ 0)) (ν := γ.dominating)
    change Integrable
      (fun ω => ((γ.curve (θ 0)).rnDeriv γ.dominating ω).toReal) γ.dominating
    exact h_int

/-- 1D LAN expansion for the abstract `QMDPath`: applying
`Asymptotics.LAN.LANExpansion.LAN_expansion_iii` at `k = 1` to the
`QMDPath`-derived parametric family. The output is the standard
`TendstoInMeasure` form
`Σᵢ log(p_{h_n/√n}/p_0) − (1/√n)·Σᵢ ⟪h, ℓ Xᵢ⟫ + (1/2)·I(h,h) →_P 0`. -/
theorem lanExpansion1D
    (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (h : EuclideanSpace ℝ (Fin 1)) (h_n : ℕ → EuclideanSpace ℝ (Fin 1))
    (hconv : Tendsto h_n atTop (𝓝 h))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω' → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) P')
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P' P')
    (hlaw : Measure.map (X 0) P'
              = γ.dominating.withDensity (fun x => ENNReal.ofReal
                  ((to1DParametricFamily γ).density 0 x)))
    (hℓ_meas : Measurable (score1D γ)) :
    TendstoInMeasure P'
      (fun n ω =>
        (∑ i ∈ Finset.range n,
          Real.log
            ((to1DParametricFamily γ).density
                (0 + (Real.sqrt n)⁻¹ • h_n n) (X i ω) /
              (to1DParametricFamily γ).density 0 (X i ω)))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
            @inner ℝ _ _ h (score1D γ (X i ω))
        + (1/2 : ℝ) *
          AsymptoticStatistics.fisherInformation
            (to1DParametricFamily γ) γ.dominating 0
            (score1D γ) h h)
      Filter.atTop (fun _ => (0 : ℝ)) := by
  have h_pdf := isPDFOf γ
  have h_dqm := dqm γ
  exact AsymptoticStatistics.LANExpansion.LAN_expansion_iii
    P' (to1DParametricFamily γ) γ.dominating
    0 (score1D γ) hℓ_meas
    (h_pdf.density_integral_eq_one 0)
    (h_pdf.density_integrable 0)
    (fun t u => h_pdf.density_integral_eq_one (0 + t • u))
    (fun t u => h_pdf.density_integrable (0 + t • u))
    h_dqm h h_n hconv X hX_meas hindep hident hlaw

end QMDPath
end AsymptoticStatistics.LowerBounds.T6_FinDimLAN
