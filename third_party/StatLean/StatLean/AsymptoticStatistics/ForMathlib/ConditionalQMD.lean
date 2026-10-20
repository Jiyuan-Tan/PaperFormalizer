module
public import StatLean.AsymptoticStatistics.ForMathlib.RnDerivSqrt
public import StatLean.AsymptoticStatistics.ForMathlib.QMDAnalytic
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Conditional quadratic-mean-differentiable paths (censoring-kernel form)

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.5.3
(Coarsening At Random, book p.379-381).

This file introduces the *conditional* analogue of `Core.QMDPath.QMDPath`: a
differentiable submodel `t ↦ rₜ(δ | y)` of the conditional density of the
censoring/coarsening variable `Δ` given the full observation `Y`, together with
its per-fibre score `b₀(δ | y)`. Where `QMDPath` differentiates a curve of
full-data laws `t ↦ Pₜ`, `ConditionalQMDPath` differentiates a curve of Markov
kernels `t ↦ rₜ : Kernel 𝓨 𝓓`, with the Hellinger limit taken against the
*product* reference `Q ⊗ ν` on `𝓨 × 𝓓`, with `P_full = Q ⊗ₘ r`.

The genuinely deep censoring-score facts that CAR forces on `b₀`:
  * `conditionalScore_factorsThrough` — `b₀(δ | y)` is a function of `x = M(y,δ)`
    only (proved in `ParametricFamily/CARScore.lean`);
  * `conditionalScore_fibre_mean_zero` — `∫ b₀(δ|y) r(δ|y) dν(δ) = 0` for a.e. `y`
    (proved below).

Headline declarations: `ConditionalQMDPath`, `conditionalScore_fibre_mean_zero`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

set_option linter.dupNamespace false

namespace AsymptoticStatistics.ForMathlib.ConditionalQMD

variable {𝓨 𝓓 : Type*} [MeasurableSpace 𝓨] [MeasurableSpace 𝓓]

/-- A *conditional quadratic-mean-differentiable path* of the censoring kernel
`r : Kernel 𝓨 𝓓` at reference measures `Q` (on `𝓨`) and `ν` (on `𝓓`): a curve
`t ↦ curve t : ℝ → Kernel 𝓨 𝓓` of Markov kernels through `r` (at `t = 0`), each
fibre `curve t y` dominated by `ν`, with per-fibre score field
`score : 𝓨 → 𝓓 → ℝ` (`b₀(δ | y)`) whose half is the L²(Q ⊗ ν) derivative of the
square-root conditional density.

Reference: vdV §25.5.3, book p.380 (differentiable submodel of the conditional
censoring density under CAR). This is the *conditional* analogue of
`Core.QMDPath.QMDPath`; the double-integral Hellinger limit against `Q ⊗ ν` is
the fibrewise QMD condition integrated over the covariate law `Q`. -/
structure ConditionalQMDPath (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (ν : Measure 𝓓) [SigmaFinite ν] (r : Kernel 𝓨 𝓓) [IsMarkovKernel r] where
  /-- Constitutive (vdV §25.5.3 p.380): the curve of conditional censoring
  kernels `t ↦ rₜ(· | ·)`. -/
  curve : ℝ → Kernel 𝓨 𝓓
  /-- Constitutive (vdV §25.5.3 p.380): the curve passes through `r` at `t = 0`. -/
  curve_at_zero : curve 0 = r
  /-- Constitutive (vdV §25.5.3 p.380): each `curve t` is a Markov kernel (a
  genuine conditional probability). -/
  curve_markov : ∀ t, IsMarkovKernel (curve t)
  /-- Constitutive (vdV §25.5.3 p.380): each fibre `curve t y` is absolutely
  continuous w.r.t. the dominating measure `ν`, so its `ν`-density exists. -/
  curve_absCont : ∀ (t : ℝ) (y : 𝓨), curve t y ≪ ν
  /-- Constitutive (vdV §25.5.3 p.380): the *per-fibre score* `b₀(δ | y)` of the
  conditional submodel. The CAR restriction (that it factors through `x`) and the
  per-fibre mean-zero identity are *derived* consequences, not fields. -/
  score : 𝓨 → 𝓓 → ℝ
  /-- Constitutive (vdV §25.5.3 p.380): joint measurability of the score in
  `(y, δ)`, required to integrate it against `Q ⊗ ν` and each fibre `r y`. -/
  score_meas : Measurable (Function.uncurry score)
  /-- Constitutive (vdV §25.5.3 p.380, eq analogous to eq:25.13): the QMD limit
  on the square-root conditional densities, taken in `ℝ≥0∞`-form against the
  product reference `Q ⊗ ν`. Writing `pₜ(y, δ) := ((curve t y).rnDeriv ν δ).toReal`,
    `‖√pₜ − √p₀ − (t/2)·score·√p₀‖_{L²(Q ⊗ ν)} / |t| → 0`
  as `t → 0` along `𝓝[≠] 0`. The `ℝ≥0∞`-quotient form (rather than a
  `.toReal²/t²` form) genuinely forces square-integrability of the residual for
  small `t`; see `Core.QMDPath.QMDPath.qmd_limit` for the rationale. -/
  qmd_limit :
    Tendsto
      (fun t : ℝ =>
        eLpNorm (fun p : 𝓨 × 𝓓 =>
          Real.sqrt ((curve t p.1).rnDeriv ν p.2).toReal
            - Real.sqrt ((curve 0 p.1).rnDeriv ν p.2).toReal
            - (t / 2) * score p.1 p.2
                * Real.sqrt ((curve 0 p.1).rnDeriv ν p.2).toReal)
          2 (Q.prod ν) / ENNReal.ofReal |t|)
      (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞))
  /-- Constitutive (vdV §25.5.3 p.380): the per-fibre QMD limit — "for every fixed y
  fix a differentiable submodel t ↦ rₜ(·|y) with score b₀(δ|y)". For every y, the
  fibre curve t ↦ (curve t) y is a dominated QMD path against ν with score (score y ·).
  The joint `qmd_limit` alone does not give this: the Fubini descent joint → per-fibre
  is not mathematically valid (an a.e.-`Q ⊗ ν` residual bound does not fibre into an
  a.e.-`ν` bound for a.e. `y`), so the per-fibre limit is a genuine constitutive field. -/
  qmd_limit_fibre : ∀ y : 𝓨,
    AsymptoticStatistics.ForMathlib.QMDAnalytic.IsQMDLimit
      (fun t => curve t y) ν (score y)

namespace ConditionalQMDPath

variable {Q : Measure 𝓨} [IsProbabilityMeasure Q]
  {ν : Measure 𝓓} [SigmaFinite ν] {r : Kernel 𝓨 𝓓} [IsMarkovKernel r]

/-- Each fibre `curve t y` of a `ConditionalQMDPath` is a probability measure
(the kernel is Markov). -/
instance instIsProbabilityMeasureCurve (γ : ConditionalQMDPath Q ν r) (t : ℝ)
    (y : 𝓨) : IsProbabilityMeasure (γ.curve t y) := by
  haveI := γ.curve_markov t
  infer_instance

end ConditionalQMDPath

/-- *Per-fibre mean-zero of the conditional score* (vdV §25.5.3, book p.380).

For a.e. covariate value `y` (in fact for *every* `y`), the conditional score
integrates to zero against its own fibre: `∫ b₀(δ | y) r(δ | y) dν(δ) = 0`,
equivalently `∫ b₀(δ | y) d(r y)(δ) = 0`. This is the per-fibre specialisation of
the mean-zero half of vdV lem:25.14 (the score of a QMD path has mean zero).

Book excerpt (vdV p.380): "Because it corresponds to a score for the conditional
model, it is further restricted by the equations
`∫ b₀(δ | y) r(δ | y) dν(δ) = E_R(b(X) | Y = y) = 0` for every `y`."

Proof: apply `QMDAnalytic.integral_score_eq_zero_of_qmd` to each fibre
`t ↦ curve t y` — a dominated QMD path against `ν` with score `b₀(· | y)`,
witnessed by the constitutive `qmd_limit_fibre` field — then rewrite
`curve 0 = r`. The identity is pointwise in `y`, so no Fubini descent from the
joint limit is needed (that descent is in fact invalid; see `qmd_limit_fibre`). -/
theorem conditionalScore_fibre_mean_zero
    {Q : Measure 𝓨} [IsProbabilityMeasure Q]
    {ν : Measure 𝓓} [SigmaFinite ν] {r : Kernel 𝓨 𝓓} [IsMarkovKernel r]
    (γ : ConditionalQMDPath Q ν r) :
    ∀ᵐ y ∂Q, ∫ δ, γ.score y δ ∂(r y) = 0 := by
  -- The identity holds for *every* `y`, so weaken the pointwise statement to a.e.
  refine Filter.Eventually.of_forall (fun y => ?_)
  -- The fibre `t ↦ (curve t) y` is a dominated QMD path against `ν` with score
  -- `b₀(· | y) = γ.score y`; feed it to the Stage-2 analytic engine.
  have h_qmd : QMDAnalytic.IsQMDLimit (fun t => γ.curve t y) ν (γ.score y) :=
    γ.qmd_limit_fibre y
  have h_prob : ∀ t, IsProbabilityMeasure ((fun t => γ.curve t y) t) := by
    intro t; haveI := γ.curve_markov t; infer_instance
  have h_ac : ∀ t, (fun t => γ.curve t y) t ≪ ν := fun t => γ.curve_absCont t y
  have hg_meas : Measurable (γ.score y) := γ.score_meas.comp measurable_prodMk_left
  have h_g_sqrt : MemLp (fun δ => γ.score y δ
      * Real.sqrt (((fun t => γ.curve t y) 0).rnDeriv ν δ).toReal) 2 ν :=
    QMDAnalytic.memLp_two_score_mul_sqrt_of_qmd h_prob h_ac hg_meas h_qmd
  have h := QMDAnalytic.integral_score_eq_zero_of_qmd h_prob h_ac hg_meas h_g_sqrt h_qmd
  -- `h : ∫ δ, γ.score y δ ∂((curve 0) y) = 0`; rewrite `curve 0 = r`.
  simpa only [γ.curve_at_zero] using h

end AsymptoticStatistics.ForMathlib.ConditionalQMD
