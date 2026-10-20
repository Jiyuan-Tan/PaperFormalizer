module
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasResidualExplicit

@[expose] public section

/-!
# Z-estimator bias-residual expansion (vdV-faithful form)

vdV-faithful explicit-bias variant (literal `√n P_{θ̂_n,η} ℓ̃`).

Expresses the bias term literally as the integral against an estimator-shifted
1D submodel of measures (rather than as an opaque parameter).
This file introduces:

- `vdV_bias_term submodel estimator θ₀ score_func_seq n X` — the literal
  Lean encoding of vdV's `√n · P_{θ̂_n, η} ℓ̃_{θ̂_n, η̂_n}`.
- `ZEstimatorBiasResidualVdVFaithfulHyp` — a hypothesis bundle that
  takes the 1D submodel as a structure parameter and bundles the
  vdV-faithful estimating-equation residual + √n-consistency.
- `zEstimator_biasResidual_asympLinear_of_taylor_vdV_faithful` — the
  AL-with-bias theorem with bias parameter set to the literal vdV form.

The η-side of vdV's `P_{θ̂_n, η}` is baked into the `submodel`
parameter: concrete consumers supply a θ-only path with truth η₀
fixed. See the main theorem's docstring for the full reading of the
correspondence to vdV's symbol.

Reference: vdV §25.8 (Efficient Score Equations), thm:25.59.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal Function

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.Asymptotics.ZEstimator

variable {Ω : Type} [MeasurableSpace Ω]

/-- *Lean encoding of vdV's bias term `√n · P_{θ̂_n,η} ℓ̃_{θ̂_n,η̂_n}`.*

Integrates the random nuisance-estimated efficient score
`score_func_seq n X = ℓ̃_{θ̂_n(X), η̂_n(X)}` against the 1D-submodel
measure at the estimator's shift `estimator n X − θ₀`. Concrete
consumers supply `submodel : ℝ → Measure Ω` as the θ-only path
`fun t => P_{θ₀ + t·v, η₀}` (with truth η₀ fixed); then
`submodel (estimator n X − θ₀) = P_{θ̂_n(X), η₀}` literally, and
the result is `√n · P_{θ̂_n, η₀} ℓ̃_{θ̂_n, η̂_n}` — vdV's bias term. -/
noncomputable def vdV_bias_term
    (submodel : ℝ → Measure Ω)
    (estimator : ∀ n, (Fin n → Ω) → ℝ)
    (θ₀ : ℝ)
    (score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ))
    (n : ℕ) (X : Fin n → Ω) : ℝ :=
  Real.sqrt n * ∫ ω, score_func_seq n X ω ∂(submodel (estimator n X - θ₀))

/-- *vdV-faithful thm:25.59 hypothesis bundle.*

Extends `ZEstimatorTaylorCoreBase` with three vdV-faithful fields: the
submodel-at-truth identity, the literal bias-shifted estimating equation,
and the √n-consistency hypothesis. The bias is the derived
`vdV_bias_term` integrated against the supplied `submodel`.

Concrete consumers supply:
- `submodel : ℝ → Measure Ω` — the 1D θ-only path through truth in the
  direction `v`. Typically constructed from a parametric family via
  `MeasureTheory.Measure.withDensity` or from `QMDPath`. No structural
  QMD compatibility is enforced here (the consumer reconciles with
  `score_l2_taylor` / `score_l_dot_bartlett` model-side).
- `submodel_at_zero : submodel 0 = P` — proven by construction from the
  consumer's parametric family.
- `vdV_score_eq_with_bias` — vdV's bias-shifted estimating-equation
  condition `√n · 𝕡_n ℓ̃ − √n · P_{θ̂_n, η} ℓ̃ →_P 0`. This is the Lean
  encoding of the residual `√n · 𝕡_n ℓ̃_{θ̂_n, η̂_n} = vdV_bias + o_P(1)`.
- `sqrt_n_consistency` — `√n · (estimator − θ₀) = O_P(1)`.

Reference: vdV §25.8 (Efficient Score Equations), thm:25.59 hypotheses
(everything in thm:25.54 except (25.52), with explicit bias). -/
structure ZEstimatorBiasResidualVdVFaithfulHyp
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (estimator : ∀ n, (Fin n → Ω) → ℝ)
    (score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ))
    (score_truth : Ω → ℝ)
    (donsker_class : Set (Ω → ℝ))
    (score_l_dot : Lp ℝ 2 P)
    (θ₀ : ℝ)
    (submodel : ℝ → Measure Ω) : Prop
    extends ZEstimatorTaylorCoreBase P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀ where
  /-- The 1D submodel passes through truth at `t = 0`.
  Concrete consumers prove this from their parametric family (e.g.,
  `(P.withDensity (density (θ₀ + 0·v))) = P` since `density θ₀ = (truth density)`). -/
  submodel_at_zero : submodel 0 = P
  /-- vdV thm:25.59 (estimating equation modulo vdV's bias):
  `√n · 𝕡_n ℓ̃_{θ̂_n, η̂_n} − √n · P_{θ̂_n, η} ℓ̃_{θ̂_n, η̂_n} →_P 0`.
  In Lean: `√n · (1/√n)·Σ score_func_seq − vdV_bias_term submodel … →_P 0`. -/
  vdV_score_eq_with_bias : ∀ ε > 0, Tendsto
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ |(Real.sqrt n)⁻¹
              * (∑ i : Fin n, score_func_seq n X (X i))
              - vdV_bias_term submodel estimator θ₀ score_func_seq n X|})
    atTop (𝓝 0)
  sqrt_n_consistency : ∀ ε > 0, ∃ M : ℝ, ∀ n : ℕ,
    (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω | M ≤ |Real.sqrt n * (estimator n X - θ₀)|}
    ≤ ENNReal.ofReal ε

namespace ZEstimatorBiasResidualVdVFaithfulHyp

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
variable {submodel : ℝ → Measure Ω}

/-- *vdV thm:25.59 — Z-estimator bias-residual expansion (vdV-faithful form).*

From the bundle `ZEstimatorBiasResidualVdVFaithfulHyp`, the Z-estimator
satisfies vdV's bias-residual asymptotic-linear expansion **with the
literal bias term** $\sqrt n\,P_{\hat\theta_n,\eta_0}\,\tilde\ell_{\hat\theta_n,\hat\eta_n}$:

$$\sqrt n\,(\hat\theta_n-\theta_0) = \tilde I^{-1}\cdot\frac{1}{\sqrt n}\sum
   \tilde\ell(X_i) - \tilde I^{-1}\cdot\sqrt n\,P_{\hat\theta_n,\eta_0}\,
     \tilde\ell_{\hat\theta_n,\hat\eta_n} + o_P(1).$$

I.e., `AsymptoticallyLinearWithBiasAt` with bias parameter
`-(1/Ĩ) * vdV_bias_term submodel estimator θ₀ score_func_seq`.

**Correspondence to vdV's expansion.** vdV writes
$$\sqrt n\,(\hat\theta_n-\theta) = (1/\sqrt n)\sum \tilde I^{-1}\tilde\ell(X_i)
   + \sqrt n\,P_{\hat\theta_n,\eta}\,\tilde\ell_{\hat\theta_n,\hat\eta_n} + o_P(1).$$
The `-(1/Ĩ)` factor comes from solving the Taylor-route identity
`Ĩ Δ_n = S_n − bias_n + o_P(1)` for `Δ_n`; vdV's notation absorbs the
sign and factor via the chain rule on `∂_θ P_θ ℓ̃|_{θ_0}`. Both
formulations describe the same residual.

**The η side of `P_{θ̂_n, η}`** in vdV's notation refers to truth's `η_0`
(NOT the random `η̂_n` in the integrand). Our `submodel : ℝ → Measure Ω`
is **constructed by the consumer** as a θ-only 1D path through
truth `(θ_0, η_0)` — the η_0 is baked into the consumer's `submodel`
definition, so `submodel (estimator n X − θ_0) = P_{θ̂_n(X), η_0}` literally.

**The integrand** `score_func_seq n X = ℓ̃_{θ̂_n(X), η̂_n(X)}` is the
random nuisance-estimated efficient score (with the estimator's η̂_n).
This matches vdV's mixed integrand exactly.

**Proof**: instantiate `ZEstimatorBiasResidualExplicitTaylorHyp` with
`bias := vdV_bias_term submodel estimator θ₀ score_func_seq` and apply
`zEstimator_biasResidual_asympLinear_of_taylor_explicit`. The three new
fields (`vdV_score_eq_with_bias`, `sqrt_n_consistency`,
`submodel_at_zero`) map respectively to the explicit-bundle's
`score_eq_with_bias`, `sqrt_n_consistency`, and an unused-by-the-proof
identity (`submodel_at_zero` is documentation/consumer-reconciliation,
not consumed in the proof itself).

Reference: vdV §25.8 (Efficient Score Equations), thm:25.59. -/
theorem zEstimator_biasResidual_asympLinear_of_taylor_vdV_faithful
    (h : ZEstimatorBiasResidualVdVFaithfulHyp P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀ submodel) :
    AsymptoticallyLinearWithBiasAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) θ₀
      (fun n X => -(1 / efficientInformation S_θ T_nuis v)
                  * vdV_bias_term submodel estimator θ₀ score_func_seq n X) := by
  -- Reduce to the existing explicit-bias discharge by setting
  -- `bias := vdV_bias_term submodel estimator θ₀ score_func_seq`.
  have h_explicit : ZEstimatorBiasResidualExplicitTaylorHyp P Θ S_θ T_nuis v
      estimator score_func_seq score_truth donsker_class score_l_dot θ₀
      (vdV_bias_term submodel estimator θ₀ score_func_seq) := {
    toZEstimatorTaylorCoreBase := h.toZEstimatorTaylorCoreBase,
    score_eq_with_bias := h.vdV_score_eq_with_bias,
    sqrt_n_consistency := h.sqrt_n_consistency }
  exact
      ZEstimatorBiasResidualExplicitTaylorHyp.zEstimator_biasResidual_asympLinear_of_taylor_explicit
    h_explicit

/-- **vdV-faithful Taylor assumptions as a bias-residual bundle.**

Constructs `EfficientScoreEqBiasResidualAssumptions` from
`ZEstimatorBiasResidualVdVFaithfulHyp` and the EIF-construction inputs `h_mem` and
`h_dψ`, with residual
`(fun n X => -(1 / efficientInformation S_θ T_nuis v) *
  vdV_bias_term submodel estimator θ₀ score_func_seq n X)`. Positivity of the efficient
information is inherited from `h.hI_pos`, and `asympLinear_25_59` is supplied by
`zEstimator_biasResidual_asympLinear_of_taylor_vdV_faithful`.

Reference: vdV §25.8 (Efficient Score Equations), thm:25.59. -/
def toEfficientScoreEqBiasResidualAssumptions_vdV_faithful
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    (h : ZEstimatorBiasResidualVdVFaithfulHyp P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀ submodel)
    (h_mem :
      (1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v ∈ T)
    (h_dψ : ∀ g : T,
      dψ g
        = (1 / efficientInformation S_θ T_nuis v)
            * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    EfficientScoreEqBiasResidualAssumptions P Θ S_θ T_nuis v T dψ
      estimator
      (fun n X => -(1 / efficientInformation S_θ T_nuis v)
                  * vdV_bias_term submodel estimator θ₀ score_func_seq n X) θ₀ where
  h_mem := h_mem
  h_dψ := h_dψ
  hI_pos := h.hI_pos
  asympLinear_25_59 :=
    zEstimator_biasResidual_asympLinear_of_taylor_vdV_faithful h

end ZEstimatorBiasResidualVdVFaithfulHyp

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
