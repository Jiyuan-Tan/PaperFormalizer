module
public import StatLean.AsymptoticStatistics.ParametricFamily.UnboundedSubmodel
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorDerivations
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# Per-direction 1D QMDPath restriction of the sigmoid `unboundedParamSubmodel`

For each direction `h : EuclideanSpace ℝ (Fin m)`, this file produces
a `QMDPath P` whose curve at parameter `t` is
`P.withDensity (fun ω => ENNReal.ofReal (density (t • h) ω))`
and whose score is `linPerturbScore g_P h ∈ ↥(L2ZeroMean P)`. It is built
directly from the m-dim `unboundedParamSubmodel_DQM` by chain rule along
the linear curve `t ↦ t • h`.

References:
* van der Vaart §25.16: sigmoid construction.
* van der Vaart §25.3: QMDPath / DQM definitions.

Headline declaration: `unboundedParamSubmodel_oneDimPath`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped InnerProductSpace ENNReal NNReal BigOperators

namespace AsymptoticStatistics.LowerBounds.RegularEstimator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.ParametricFamily
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## The 1D-restriction QMDPath of `unboundedParamSubmodel` -/

section OneDimPath

variable {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
variable (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
variable (h : EuclideanSpace ℝ (Fin m))

/-- The 1D-restriction curve: `t ↦ P.withDensity (density (t • h))` for the
sigmoid `unboundedParamSubmodel`. -/
noncomputable def unboundedOneDimCurve : ℝ → Measure Ω := fun t =>
  P.withDensity (fun ω => ENNReal.ofReal
    ((unboundedParamSubmodel g_P h_orth).density (t • h) ω))

/-- Measurability of the 1D-curve's density (for any `t`). -/
private lemma unboundedOneDimCurve_density_meas (t : ℝ) :
    Measurable
      (fun ω => ENNReal.ofReal
        ((unboundedParamSubmodel g_P h_orth).density (t • h) ω)) :=
  ((unboundedParamSubmodel g_P h_orth).density_meas _).ennreal_ofReal

/-- At `t = 0`, the 1D curve equals `P` (since `density 0 ω = 1`). -/
lemma unboundedOneDimCurve_at_zero :
    unboundedOneDimCurve g_P h_orth h 0 = P := by
  unfold unboundedOneDimCurve
  have h_const : (fun ω => ENNReal.ofReal
      ((unboundedParamSubmodel g_P h_orth).density ((0 : ℝ) • h) ω))
        = fun _ => (1 : ℝ≥0∞) := by
    funext ω
    rw [zero_smul]
    rw [unboundedParamSubmodel_density_zero_eq_one g_P h_orth ω]
    exact ENNReal.ofReal_one
  rw [h_const]
  exact MeasureTheory.withDensity_one

/-- Each 1D-curve measure is a probability measure. -/
lemma unboundedOneDimCurve_isProbability (t : ℝ) :
    IsProbabilityMeasure (unboundedOneDimCurve g_P h_orth h t) := by
  unfold unboundedOneDimCurve
  refine ⟨?_⟩
  -- (P.withDensity ofReal(density (t • h))) univ
  -- = ∫⁻ ω, ofReal (density (t • h) ω) ∂P
  -- = ENNReal.ofReal (∫ density dP)  (since density ≥ 0)
  -- = ENNReal.ofReal 1 = 1.
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h_int : ∫ ω, (unboundedParamSubmodel g_P h_orth).density (t • h) ω ∂P = 1 :=
    integral_unboundedSubmodelDensity_eq_one g_P (t • h)
  have h_nn : ∀ ω, 0 ≤ (unboundedParamSubmodel g_P h_orth).density (t • h) ω :=
    fun ω => unboundedSubmodelDensity_nonneg g_P (t • h) ω
  have h_intble : Integrable
      ((unboundedParamSubmodel g_P h_orth).density (t • h)) P :=
    unboundedSubmodelDensity_integrable g_P (t • h)
  rw [← ofReal_integral_eq_lintegral_ofReal h_intble
        (Filter.Eventually.of_forall h_nn), h_int, ENNReal.ofReal_one]

/-- Absolute continuity of each 1D-curve measure w.r.t. `P`. -/
lemma unboundedOneDimCurve_absContinuous (t : ℝ) :
    unboundedOneDimCurve g_P h_orth h t ≪ P := by
  unfold unboundedOneDimCurve
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

/-- Pointwise RN-derivative formula: `(curve t).rnDeriv P =ᵐ[P] ofReal (density (t • h))`. -/
private lemma unboundedOneDimCurve_rnDeriv (t : ℝ) :
    (unboundedOneDimCurve g_P h_orth h t).rnDeriv P =ᵐ[P]
      fun ω => ENNReal.ofReal
        ((unboundedParamSubmodel g_P h_orth).density (t • h) ω) := by
  unfold unboundedOneDimCurve
  exact Measure.rnDeriv_withDensity₀ P
    (unboundedOneDimCurve_density_meas g_P h_orth h t).aemeasurable

/-! ### Chain rule: derive the 1D `qmd_limit` from the m-dim DQM

The m-dim `unboundedParamSubmodel_DQM` says:

  `∫ x, (√(p(θ)) - √(p(0)) - (1/2)⟨θ, g_P_total x⟩√(p(0)))² ∂P
      =o[𝓝 0] (fun θ => ‖θ‖²)`

Specialising `θ = t • h` and using `⟨t • h, g_P_total x⟩ = t · linPerturb g_P h x`,
the integrand becomes:

  `∫ x, (√(p(t·h)) - 1 - (t/2)·linPerturb g_P h x)² ∂P  =  o(‖t • h‖²) = o(t²·‖h‖²)`

Then dividing by `|t|`, taking square roots, and converting to `ℝ≥0∞`-form
gives the QMDPath `qmd_limit` shape:

  `(eLpNorm res 2 P) / ENNReal.ofReal |t| → 0` as `t → 0`.

Two boundary cases:
* `h = 0`: the curve is constantly `P`, the residual is 0, trivial.
* `t = 0` excluded by `𝓝[≠] 0` filter; for `t ≠ 0`, `|t| > 0`, division well-defined. -/

/-- Definition of the QMD residual for the 1D-restriction curve, in the
canonical `QMDPath.qmd_limit` shape. Used to keep `eLpNorm` arguments
manageable below. -/
noncomputable def oneDimQmdResidual
    (g : ↥(L2ZeroMean P)) (curve : ℝ → Measure Ω) (t : ℝ) : Ω → ℝ :=
  fun ω =>
    Real.sqrt ((curve t).rnDeriv P ω).toReal
      - Real.sqrt ((curve 0).rnDeriv P ω).toReal
      - (t / 2) * (g : Ω → ℝ) ω
          * Real.sqrt ((curve 0).rnDeriv P ω).toReal

/-- Rewrite the 1D `qmd_limit` residual in terms of the parametric density.
For our curve, `(curve t).rnDeriv P ω = ofReal (density (t • h) ω)` a.e.,
and `(curve 0).rnDeriv P ω = 1` a.e., so the residual simplifies to:
`√(density (t • h) ω) - 1 - (t/2) · linPerturbScore ω · 1`. -/
private lemma oneDimQmdResidual_ae_eq (t : ℝ) :
    oneDimQmdResidual (linPerturbScore g_P h)
        (unboundedOneDimCurve g_P h_orth h) t
      =ᵐ[P]
    fun ω => Real.sqrt ((unboundedParamSubmodel g_P h_orth).density (t • h) ω)
              - 1
              - (t / 2) * ((linPerturbScore g_P h : Lp ℝ 2 P) : Ω → ℝ) ω := by
  have h_rn_t := unboundedOneDimCurve_rnDeriv g_P h_orth h t
  have h_rn_0 : (unboundedOneDimCurve g_P h_orth h 0).rnDeriv P =ᵐ[P]
      fun _ => (1 : ℝ≥0∞) := by
    rw [unboundedOneDimCurve_at_zero]
    exact Measure.rnDeriv_self P
  filter_upwards [h_rn_t, h_rn_0] with ω hωt hω0
  unfold oneDimQmdResidual
  rw [hωt, hω0]
  have h_dens_nn : (0 : ℝ) ≤
      (unboundedParamSubmodel g_P h_orth).density (t • h) ω :=
    unboundedSubmodelDensity_nonneg g_P (t • h) ω
  rw [ENNReal.toReal_ofReal h_dens_nn, ENNReal.toReal_one,
      Real.sqrt_one, mul_one]

/-- The 1D residual in terms of the m-dim DQM residual. Substituting
`θ = t • h` in the m-dim DQM residual `√p(θ) - √p(0) - (1/2)⟨θ, g_P_total⟩√p(0)`,
and using `√p(0) = 1`, `⟨t • h, g_P_total x⟩ = t · linPerturb g_P h x`,
and `linPerturb g_P h x =ᵐ[P] (linPerturbScore g_P h : Ω → ℝ) x`. -/
private lemma oneDimQmdResidual_eq_mdim_residual_ae (t : ℝ) :
    oneDimQmdResidual (linPerturbScore g_P h)
        (unboundedOneDimCurve g_P h_orth h) t
      =ᵐ[P]
    fun ω => (unboundedParamSubmodel g_P h_orth).sqrtDensity (0 + t • h) ω
              - (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω
              - (1/2 : ℝ) * @inner ℝ _ _ (t • h) (g_P_total g_P ω)
                  * (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω := by
  have h_oneDim := oneDimQmdResidual_ae_eq g_P h_orth h t
  have h_score_ae := linPerturbScore_coe_ae g_P h
  filter_upwards [h_oneDim, h_score_ae] with ω hω h_score_ω
  -- LHS = √(density (t • h) ω) - 1 - (t/2) * linPerturbScore ω.
  -- RHS = sqrtDensity (t • h) ω - sqrtDensity 0 ω - (1/2)⟨t • h, g_P_total ω⟩·sqrtDensity 0 ω
  --     = √(density (t • h) ω) - 1 - (1/2) · t · linPerturb g_P h ω · 1
  --     = √(density (t • h) ω) - 1 - (t/2) · linPerturb g_P h ω.
  rw [hω]
  unfold ParametricFamily.sqrtDensity
  -- After unfolding: √(density (0 + t • h) ω) - √(density 0 ω) - …
  rw [zero_add,
      unboundedParamSubmodel_density_zero_eq_one g_P h_orth ω, Real.sqrt_one,
      mul_one]
  -- Use inner_g_P_total_eq_linPerturb to turn ⟨t • h, g_P_total ω⟩ into linPerturb (t • h) ω.
  rw [inner_g_P_total_eq_linPerturb]
  -- linPerturb (t • h) ω = t * linPerturb h ω.
  have h_linPerturb_smul : linPerturb g_P (t • h) ω = t * linPerturb g_P h ω := by
    unfold linPerturb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    have h_smul : (t • h) i = t * h i := by
      simp [PiLp.smul_apply, smul_eq_mul]
    rw [h_smul]; ring
  rw [h_linPerturb_smul]
  -- Replace linPerturb h ω with (linPerturbScore g_P h : Ω → ℝ) ω via h_score_ω.
  rw [← h_score_ω]
  ring

/-- The 1D residual (squared, integrated) equals the m-dim DQM residual at
`θ = t • h`. Folds `oneDimQmdResidual_eq_mdim_residual_ae` into the integral form
that the DQM `isLittleO` hypothesis provides. -/
private lemma integral_oneDimQmdResidual_sq_eq_mdim
    (t : ℝ) :
    ∫ ω, (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t ω) ^ 2 ∂P
      =
    ∫ ω, ((unboundedParamSubmodel g_P h_orth).sqrtDensity (0 + t • h) ω
              - (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω
              - (1/2 : ℝ) * @inner ℝ _ _ (t • h) (g_P_total g_P ω)
                  * (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω) ^ 2 ∂P := by
  apply integral_congr_ae
  filter_upwards [oneDimQmdResidual_eq_mdim_residual_ae g_P h_orth h t] with ω hω
  rw [hω]

/-- MemLp of the 1D residual at `t`, eventually as `t → 0`. Lifted from
the m-dim DQM `.mem` field (which gives MemLp eventually for `θ → 0`)
specialised along the continuous curve `t ↦ t • h`. -/
private lemma oneDimQmdResidual_memLp_eventually :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      MemLp (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t) 2 P := by
  -- The m-dim DQM `.mem` field gives MemLp eventually in `θ`. Compose with
  -- the continuous curve `t ↦ t • h` (which tends to 0 as t → 0) to get the
  -- per-t form, then bridge via the ae-equality of residuals.
  have h_mdim_dqm := unboundedParamSubmodel_DQM g_P h_orth
  have h_mem := h_mdim_dqm.mem
  -- The continuous curve `t ↦ t • h : ℝ → Θ` tends to 0 as t → 0.
  have h_smul_tendsto :
      Tendsto (fun t : ℝ => t • h) (𝓝 (0 : ℝ)) (𝓝 (0 : EuclideanSpace ℝ (Fin m))) := by
    have h_cont : Continuous (fun t : ℝ => t • h) :=
      continuous_id.smul continuous_const
    simpa using h_cont.tendsto (0 : ℝ)
  -- Pull back `h_mem` along the curve.
  have h_mem_along : ∀ᶠ t : ℝ in 𝓝 0,
      MemLp (fun ω => (unboundedParamSubmodel g_P h_orth).sqrtDensity (0 + t • h) ω
              - (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω
              - (1/2 : ℝ) * @inner ℝ _ _ (t • h) (g_P_total g_P ω)
                  * (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω) 2 P :=
    h_smul_tendsto.eventually h_mem
  filter_upwards [h_mem_along] with t h_mem_t
  exact MeasureTheory.MemLp.ae_eq
    (oneDimQmdResidual_eq_mdim_residual_ae g_P h_orth h t).symm h_mem_t

/-- The 1D `qmd_limit`: `(eLpNorm res 2 P) / ENNReal.ofReal |t| → 0`
as `t → 0` along `𝓝[≠] 0`.

Strategy: bound `eLpNorm res 2 P = √(∫ res²)` via `sqrt_integral_sq_eq_eLpNorm_toReal`,
then use the m-dim DQM `isLittleO` rate `∫ residual(θ)² ∂P =o[𝓝 0] ‖θ‖²`
specialised at `θ = t • h` to get `(eLpNorm res 2 P).toReal / |t| → 0`,
then lift to `ℝ≥0∞`. -/
lemma oneDimQmd_limit_aux :
    Tendsto
      (fun t : ℝ =>
        eLpNorm (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t) 2 P / ENNReal.ofReal |t|)
      (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)) := by
  classical
  -- Step 1: from m-dim DQM, get `∫ residual(θ)² ∂P =o[𝓝 0] ‖θ‖²`.
  have h_mdim_dqm := unboundedParamSubmodel_DQM g_P h_orth
  have h_isLittleO := h_mdim_dqm.isLittleO
  -- Step 2: specialise via composition with `t ↦ t • h` (continuous, tends to 0).
  have h_smul_tendsto :
      Tendsto (fun t : ℝ => t • h) (𝓝 (0 : ℝ)) (𝓝 (0 : EuclideanSpace ℝ (Fin m))) := by
    have h_cont : Continuous (fun t : ℝ => t • h) :=
      continuous_id.smul continuous_const
    simpa using h_cont.tendsto (0 : ℝ)
  have h_isLittleO_along :
      (fun t : ℝ => ∫ ω,
        ((unboundedParamSubmodel g_P h_orth).sqrtDensity (0 + t • h) ω
          - (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω
          - (1/2 : ℝ) * @inner ℝ _ _ (t • h) (g_P_total g_P ω)
              * (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω) ^ 2 ∂P)
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => ‖t • h‖ ^ 2) :=
    h_isLittleO.comp_tendsto h_smul_tendsto
  -- Step 3: Convert =o[𝓝 0] to Tendsto along 𝓝[≠] 0 of the toReal ratio.
  -- Specifically: `(eLpNorm res 2 P).toReal / |t| → 0`.
  -- Using sqrt of the integral form via sqrt_integral_sq_eq_eLpNorm_toReal.
  have h_norm_smul : ∀ t : ℝ, ‖t • h‖ = |t| * ‖h‖ := by
    intro t; rw [norm_smul, Real.norm_eq_abs]
  have h_ratio_tendsto :
      Tendsto
        (fun t : ℝ => (eLpNorm
          (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t) 2 P).toReal / |t|)
        (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    -- Strategy: show this is dominated by ‖h‖ · √(∫ res(t•h)² / ‖t•h‖²) → 0
    -- when ‖h‖ ≠ 0; trivial when ‖h‖ = 0.
    by_cases h_h_zero : h = 0
    · -- h = 0: t • h = 0, residual is constant 0, eLpNorm = 0.
      subst h_h_zero
      refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht_ne
      have h_res_zero : oneDimQmdResidual (linPerturbScore g_P (0 : EuclideanSpace ℝ (Fin m)))
            (unboundedOneDimCurve g_P h_orth (0 : EuclideanSpace ℝ (Fin m))) t
            =ᵐ[P] (fun _ => (0 : ℝ)) := by
        have h_oneDim := oneDimQmdResidual_ae_eq g_P h_orth (0 : EuclideanSpace ℝ (Fin m)) t
        have h_score_zero : (linPerturbScore g_P (0 : EuclideanSpace ℝ (Fin m)) : Ω → ℝ)
            =ᵐ[P] (fun _ => (0 : ℝ)) := by
          have h1 := linPerturbScore_coe_ae g_P (0 : EuclideanSpace ℝ (Fin m))
          filter_upwards [h1] with ω h1ω
          rw [h1ω]
          unfold linPerturb
          simp
        filter_upwards [h_oneDim, h_score_zero] with ω hω hsc_ω
        rw [hω]
        -- LHS form: √(density (t • 0) ω) - 1 - (t/2) * linPerturbScore ω.
        -- t • 0 = 0, density 0 ω = 1, √1 = 1. linPerturbScore 0 ω = 0.
        rw [smul_zero, unboundedParamSubmodel_density_zero_eq_one g_P h_orth ω,
            Real.sqrt_one, hsc_ω]
        ring
      have h_eLp_zero :
          eLpNorm (oneDimQmdResidual (linPerturbScore g_P (0 : EuclideanSpace ℝ (Fin m)))
            (unboundedOneDimCurve g_P h_orth (0 : EuclideanSpace ℝ (Fin m))) t) 2 P = 0 := by
        rw [eLpNorm_congr_ae h_res_zero]
        simp
      rw [h_eLp_zero, ENNReal.toReal_zero, zero_div]
    · -- h ≠ 0: use ‖h‖ > 0 to divide.
      have h_h_norm_pos : 0 < ‖h‖ := norm_pos_iff.mpr h_h_zero
      have h_h_norm_ne_zero : (‖h‖ : ℝ) ≠ 0 := ne_of_gt h_h_norm_pos
      -- The m-dim DQM integral rate: ∫ residual(t•h)² ∂P / (|t|·‖h‖)² → 0.
      -- This means ∫ residual(t•h)² ∂P / t² ≤ ε · ‖h‖² eventually,
      -- so √(∫ residual(t•h)²) / |t| ≤ √ε · ‖h‖ eventually.
      -- Translate to ratio form for the 1D residual using ae-eq.
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      -- Pick threshold for the m-dim rate: ε' = (ε / (2 · ‖h‖))² > 0 (use ε/2
      -- so the final bound is strict `< ε` rather than `≤ ε`).
      set ε' : ℝ := (ε / (2 * ‖h‖)) ^ 2 with hε'_def
      have hε'_pos : 0 < ε' := by
        apply sq_pos_of_ne_zero
        exact div_ne_zero (ne_of_gt hε)
          (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) h_h_norm_ne_zero)
      have h_ratio_lt := (Asymptotics.isLittleO_iff.mp h_isLittleO_along) hε'_pos
      rw [Metric.eventually_nhds_iff] at h_ratio_lt
      obtain ⟨δ_lo, hδ_lo_pos, hδ_lo_sub⟩ := h_ratio_lt
      -- Also get eventually MemLp for small t (needed for the sqrt_integral bridge).
      have h_memLp_ev := oneDimQmdResidual_memLp_eventually g_P h_orth h
      rw [Metric.eventually_nhds_iff] at h_memLp_ev
      obtain ⟨δ_mem, hδ_mem_pos, hδ_mem_sub⟩ := h_memLp_ev
      -- Take the minimum of the two radii.
      set δ_inner : ℝ := min δ_lo δ_mem with hδ_inner_def
      have hδ_inner_pos : 0 < δ_inner := lt_min hδ_lo_pos hδ_mem_pos
      refine ⟨δ_inner, hδ_inner_pos, fun {t} ht_mem_compl ht_dist => ?_⟩
      -- ht_mem_compl : t ∈ {0}ᶜ (= t ≠ 0); ht_dist : dist t 0 < δ_inner.
      have ht_ne : t ≠ 0 := ht_mem_compl
      have ht_dist_lo : dist t 0 < δ_lo := lt_of_lt_of_le ht_dist (min_le_left _ _)
      have ht_dist_mem : dist t 0 < δ_mem := lt_of_lt_of_le ht_dist (min_le_right _ _)
      have h_t_lt := hδ_lo_sub (by simpa [dist_zero_right] using ht_dist_lo)
      have h_memLp_1D := hδ_mem_sub (by simpa [dist_zero_right] using ht_dist_mem)
      -- h_t_lt: ‖integral‖ ≤ ε' * ‖‖t • h‖²‖.
      have h_t_abs_pos : 0 < |t| := abs_pos.mpr ht_ne
      -- The m-dim rate gives:
      -- ∫ residual(t•h)² ∂P ≤ ε' · ‖t • h‖² = ε' · |t|² · ‖h‖².
      have h_int_le :
          ∫ ω, ((unboundedParamSubmodel g_P h_orth).sqrtDensity (0 + t • h) ω
                - (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω
                - (1/2 : ℝ) * @inner ℝ _ _ (t • h) (g_P_total g_P ω)
                    * (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω) ^ 2 ∂P
          ≤ ε' * (|t| ^ 2 * ‖h‖ ^ 2) := by
        have h_int_nn : 0 ≤ ∫ ω,
            ((unboundedParamSubmodel g_P h_orth).sqrtDensity (0 + t • h) ω
              - (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω
              - (1/2 : ℝ) * @inner ℝ _ _ (t • h) (g_P_total g_P ω)
                  * (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω) ^ 2 ∂P :=
          MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
        have h_norm_sq_nn : 0 ≤ ‖t • h‖ ^ 2 := sq_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg h_int_nn,
            Real.norm_eq_abs, abs_of_nonneg h_norm_sq_nn] at h_t_lt
        have h_norm_sq_eq : ‖t • h‖ ^ 2 = |t| ^ 2 * ‖h‖ ^ 2 := by
          rw [h_norm_smul]; ring
        rw [h_norm_sq_eq] at h_t_lt
        exact h_t_lt
      -- Translate to ∫ (1D residual)² ∂P ≤ ε' · |t|² · ‖h‖² via
      -- `integral_oneDimQmdResidual_sq_eq_mdim`.
      rw [← integral_oneDimQmdResidual_sq_eq_mdim g_P h_orth h t] at h_int_le
      -- (h_memLp_1D obtained above from the shrunk δ_inner.)
      have h_sqrt_eq :
          Real.sqrt (∫ ω, (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t ω) ^ 2 ∂P) =
          (eLpNorm (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t) 2 P).toReal :=
        AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal
          h_memLp_1D
      -- √(LHS) ≤ √(ε' · |t|² · ‖h‖²) = √ε' · |t| · ‖h‖.
      have h_int_nn_1D : 0 ≤ ∫ ω, (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t ω) ^ 2 ∂P :=
        MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
      have h_rhs_nn : 0 ≤ ε' * (|t| ^ 2 * ‖h‖ ^ 2) :=
        mul_nonneg hε'_pos.le (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have h_sqrt_le : Real.sqrt (∫ ω, (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t ω) ^ 2 ∂P)
          ≤ Real.sqrt (ε' * (|t| ^ 2 * ‖h‖ ^ 2)) :=
        Real.sqrt_le_sqrt h_int_le
      rw [h_sqrt_eq] at h_sqrt_le
      -- √(ε' · |t|² · ‖h‖²) = √ε' · |t| · ‖h‖ = (ε / ‖h‖) · |t| · ‖h‖ = ε · |t|.
      have h_sqrt_ε' : Real.sqrt ε' = ε / (2 * ‖h‖) := by
        change Real.sqrt ((ε / (2 * ‖h‖)) ^ 2) = ε / (2 * ‖h‖)
        rw [Real.sqrt_sq]
        apply div_nonneg hε.le
        exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h_h_norm_pos.le
      have h_sqrt_rhs : Real.sqrt (ε' * (|t| ^ 2 * ‖h‖ ^ 2))
          = (ε / (2 * ‖h‖)) * (|t| * ‖h‖) := by
        have h_factor : ε' * (|t| ^ 2 * ‖h‖ ^ 2) = (Real.sqrt ε' * (|t| * ‖h‖)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hε'_pos.le, mul_pow]
        rw [h_factor,
            Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _)
              (mul_nonneg (abs_nonneg _) h_h_norm_pos.le)),
            h_sqrt_ε']
      rw [h_sqrt_rhs] at h_sqrt_le
      -- Simplify: (ε / (2·‖h‖)) · |t| · ‖h‖ = ε · |t| / 2.
      have h_simp : (ε / (2 * ‖h‖)) * (|t| * ‖h‖) = ε * |t| / 2 := by
        field_simp
      rw [h_simp] at h_sqrt_le
      -- Now divide both sides by |t| (> 0):
      -- (eLpNorm).toReal / |t| ≤ ε / 2 < ε.
      have h_eLpNorm_nn : 0 ≤ (eLpNorm (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t) 2 P).toReal :=
        ENNReal.toReal_nonneg
      have h_div_le : (eLpNorm (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t) 2 P).toReal / |t| ≤ ε / 2 := by
        rw [div_le_iff₀ h_t_abs_pos]
        linarith
      -- Final: dist (… / |t|) 0 < ε via ε/2 < ε.
      rw [Real.dist_eq, sub_zero, abs_of_nonneg
        (div_nonneg h_eLpNorm_nn (abs_nonneg _))]
      have h_eps_half : ε / 2 < ε := by linarith
      exact lt_of_le_of_lt h_div_le h_eps_half
  -- Step 4: Lift the real-valued ratio Tendsto to ℝ≥0∞.
  -- (eLpNorm).toReal / |t| → 0 in ℝ  ⟹  ofReal((eLpNorm).toReal / |t|) → 0 in ℝ≥0∞.
  -- And ofReal((eLpNorm).toReal / |t|) = eLpNorm / ofReal |t| when finite (use memLp).
  have h_lift :
      Tendsto (fun t : ℝ => ENNReal.ofReal
        ((eLpNorm (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t) 2 P).toReal / |t|))
        (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)) := by
    have h_eq : ENNReal.ofReal (0 : ℝ) = 0 := ENNReal.ofReal_zero
    rw [← h_eq]
    exact (ENNReal.continuous_ofReal.tendsto _).comp h_ratio_tendsto
  -- Bridge: eLpNorm / ofReal|t| = ofReal((eLpNorm).toReal / |t|) eventually
  -- (when eLpNorm finite, i.e., via the eventually-MemLp).
  have h_self_ne : {x : ℝ | x ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := self_mem_nhdsWithin
  have h_memLp_ev : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      MemLp (oneDimQmdResidual (linPerturbScore g_P h)
            (unboundedOneDimCurve g_P h_orth h) t) 2 P :=
    (oneDimQmdResidual_memLp_eventually g_P h_orth h).filter_mono nhdsWithin_le_nhds
  refine h_lift.congr' ?_
  filter_upwards [h_self_ne, h_memLp_ev] with t ht_ne h_memLp_t
  have h_eLp_ne_top :
      eLpNorm (oneDimQmdResidual (linPerturbScore g_P h)
        (unboundedOneDimCurve g_P h_orth h) t) 2 P ≠ ⊤ := h_memLp_t.2.ne
  have h_abs_pos : 0 < |t| := abs_pos.mpr ht_ne
  -- ofReal((eLpNorm).toReal / |t|) = ofReal((eLpNorm).toReal) / ofReal |t|
  --                                = eLpNorm / ofReal |t|.
  rw [ENNReal.ofReal_div_of_pos h_abs_pos,
      ENNReal.ofReal_toReal h_eLp_ne_top]

/-- **The 1D-restriction QMDPath** of `unboundedParamSubmodel` along
direction `h`. Built directly from the m-dim `unboundedParamSubmodel_DQM`
by chain rule along `t ↦ t • h`. -/
noncomputable def unboundedParamSubmodel_oneDimPath : QMDPath P where
  curve := unboundedOneDimCurve g_P h_orth h
  curve_at_zero := unboundedOneDimCurve_at_zero g_P h_orth h
  curve_isProbability := unboundedOneDimCurve_isProbability g_P h_orth h
  dominating := P
  dominating_sigmaFinite := inferInstance
  curve_absContinuous := unboundedOneDimCurve_absContinuous g_P h_orth h
  score := linPerturbScore g_P h
  qmd_limit := oneDimQmd_limit_aux g_P h_orth h

/-- The score of `unboundedParamSubmodel_oneDimPath` is `linPerturbScore g_P h`. -/
@[simp] theorem unboundedParamSubmodel_oneDimPath_score :
    (unboundedParamSubmodel_oneDimPath g_P h_orth h).score
      = linPerturbScore g_P h := rfl

/-- The curve of `unboundedParamSubmodel_oneDimPath` at `t` is
`P.withDensity (fun ω => ENNReal.ofReal (density (t • h) ω))`. Useful
for downstream rewrites. -/
@[simp] theorem unboundedParamSubmodel_oneDimPath_curve (t : ℝ) :
    (unboundedParamSubmodel_oneDimPath g_P h_orth h).curve t
      = P.withDensity (fun ω => ENNReal.ofReal
          ((unboundedParamSubmodel g_P h_orth).density (t • h) ω)) := rfl

end OneDimPath

/-! ## Tangent-space membership -/

/-- The score of `unboundedParamSubmodel_oneDimPath` lies in the tangent
space `tangentSpace T_set` whenever each `g_P i` does. The score is the
finite linear combination `∑ i, h i • g_P i`, which is in any submodule
containing each `g_P i`. -/
theorem unboundedParamSubmodel_oneDimPath_score_mem_tangentSpace
    {m : ℕ} (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h : EuclideanSpace ℝ (Fin m)) :
    (unboundedParamSubmodel_oneDimPath g_P h_orth h).score
      ∈ tangentSpace T_set := by
  rw [unboundedParamSubmodel_oneDimPath_score]
  exact linPerturbScore_mem_tangentSpace T_set g_P h_in_T h

end AsymptoticStatistics.LowerBounds.RegularEstimator
