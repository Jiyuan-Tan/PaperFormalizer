module
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateComplexMGFCoeff

@[expose] public section

/-!
# Multivariate complex moment-generating function: joint analyticity on `ℂᵐ`

Mathlib ships the one-dimensional analytic-MGF result
`ProbabilityTheory.analyticOnNhd_complexMGF`: for a real random variable
`X : Ω → ℝ` and a probability measure `μ`, the function
`z ↦ ∫ ω, cexp(z * X ω) ∂μ` is analytic on the open vertical strip
`{z : ℂ | z.re ∈ interior (integrableExpSet X μ)}`. The multivariate
analogue is not packaged in Mathlib.

This file provides the headline brick `analyticOnNhd_complexMGF_pi`: for a
measurable random vector `X : Ω → EuclideanSpace ℝ (Fin m)` whose
multivariate MGF exists in every real direction, the complex MGF
`F(z) := ∫ ω, cexp(∑ᵢ zᵢ Xᵢ(ω)) ∂μ` is analytic on all of `ℂᵐ`. The
closure routes through `MultivariateComplexMGFCoeff.analyticOnNhd_mgf`,
which builds an explicit `FormalMultilinearSeries` of infinite radius and
verifies `HasFPowerSeriesOnBall ... 0 ⊤` directly.

The hypothesis `h_mgf` (for every real direction `t`, the integral
`∫ ω, exp(∑ i, t i * X ω i) ∂μ` is finite) is the multivariate analogue
of saying the 1-D MGF exists on all of `ℝ`, equivalently each marginal
has `integrableExpSet = univ`. This is the cleanest precondition for the
entire (univ-analytic) conclusion.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics.ForMathlib.MultivariateComplexMGF

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Auxiliary norm bound on the complex integrand -/

/-- Pointwise norm of the complex multivariate exponential.

For any `z : Fin m → ℂ` and any real vector `x : Fin m → ℝ`,
`‖cexp(∑ i, z i * x i)‖ = exp(∑ i, z i.re * x i)`. Used to lift real
integrability of `exp(∑ i, t i * X ω i)` to `ℝ`-norm-integrability of
the complex integrand at `t + i s`. -/
lemma norm_cexp_sum_mul {m : ℕ} (z : Fin m → ℂ) (x : Fin m → ℝ) :
    ‖Complex.exp (∑ i, z i * (x i : ℂ))‖
      = Real.exp (∑ i, (z i).re * x i) := by
  rw [Complex.norm_exp]
  -- The real part of `∑ i, z i * x i` is `∑ i, (z i).re * x i` since
  -- `(z * x).re = z.re * x.re - z.im * x.im` and `(x i : ℂ).im = 0`.
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Complex.mul_re]

/-! ### Integrability lift from real polycube to complex polystrip -/

omit [IsProbabilityMeasure μ] in
/-- *Integrability lift.* If `Real.exp(∑ i, t i * X ω i)` is integrable
for the real direction `t`, then the complex integrand
`Complex.exp(∑ i, z i * (X ω i : ℂ))` is `μ`-integrable for any
`z : Fin m → ℂ` whose **real part** equals `t`.

This is the standard "complex MGF inherits integrability from its real
shadow" step, used both to define `F` cleanly and to feed the dominated
convergence in the analyticity proof. -/
lemma integrable_cexp_of_re
    {m : ℕ} (X : Ω → EuclideanSpace ℝ (Fin m))
    (hX : Measurable X) (z : Fin m → ℂ)
    (h_re : Integrable (fun ω => Real.exp (∑ i, (z i).re * X ω i)) μ) :
    Integrable
      (fun ω => Complex.exp (∑ i, z i * (X ω i : ℂ))) μ := by
  -- Measurability of the complex integrand.
  have hmeas :
      AEStronglyMeasurable
        (fun ω => Complex.exp (∑ i, z i * (X ω i : ℂ))) μ := by
    refine Complex.continuous_exp.comp_aestronglyMeasurable ?_
    -- Swap `fun ω => ∑ i, …` with `∑ i, fun ω => …`.
    -- The composition `WithLp.ofLp ∘ X : Ω → (Fin m → ℝ)` is measurable.
    have hX' : Measurable (fun ω => (WithLp.ofLp (X ω) : Fin m → ℝ)) :=
      (WithLp.measurable_ofLp 2 (Fin m → ℝ)).comp hX
    have h_each : ∀ i : Fin m,
        AEStronglyMeasurable (fun ω => z i * (X ω i : ℂ)) μ := by
      intro i
      refine (continuous_const.mul Complex.continuous_ofReal).comp_aestronglyMeasurable ?_
      exact ((measurable_pi_apply i).comp hX').aestronglyMeasurable
    have hsum :
        AEStronglyMeasurable (∑ i : Fin m, fun ω => z i * (X ω i : ℂ)) μ :=
      Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => h_each i)
    -- `(∑ i, f i) ω = ∑ i, f i ω`.
    have hswap :
        (∑ i : Fin m, fun ω => z i * (X ω i : ℂ))
          = fun ω => ∑ i : Fin m, z i * (X ω i : ℂ) := by
      ext ω
      simp [Finset.sum_apply]
    rw [hswap] at hsum
    exact hsum
  -- Pointwise norm equals the real shadow.
  have hbound : ∀ ω,
      ‖Complex.exp (∑ i, z i * (X ω i : ℂ))‖
        = Real.exp (∑ i, (z i).re * X ω i) := by
    intro ω
    exact norm_cexp_sum_mul z (fun i => X ω i)
  -- Lift integrability via `integrable_norm_iff`.
  rw [← integrable_norm_iff hmeas]
  refine h_re.congr ?_
  exact Filter.Eventually.of_forall fun ω => (hbound ω).symm

/-! ### Polycube domination (Hölder reuse of 1-D `integrableExpSet`)

Mathlib's 1-D proof bounds `|X|^n · exp(z.re X)` on a real interval
`[z.re - t, z.re + t]` via Hölder + the integrability of `exp((z.re ± t) X)`.
The multivariable analogue extends this to a real polycube
`∏ i, [t i - δ, t i + δ]`, with each marginal `exp(t i * X i)`
integrable.
-/

/-- Multivariate Cauchy / Hartogs for the complex MGF.

Encapsulates the closure step of `analyticOnNhd_complexMGF_pi`: given
that the complex-MGF integral is well-defined at every `z : Fin m → ℂ`
(via `integrable_cexp_of_re`), the function is jointly analytic on
`ℂᵐ`.

The proof routes through
`AsymptoticStatistics.ForMathlib.MultivariateComplexMGFCoeff.analyticOnNhd_mgf`,
which exhibits an explicit `FormalMultilinearSeries` of infinite radius
and verifies `HasFPowerSeriesOnBall ... 0 ⊤` directly (no multivariable
Cauchy / Hartogs needed; only the 1-D Banach-algebra exponential power
series + DCT). -/
theorem multivariate_complexMGF_analytic
    {m : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin m))
    (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ)
    (_h_int_complex : ∀ z : Fin m → ℂ,
      Integrable
        (fun ω => Complex.exp (∑ i, z i * (X ω i : ℂ))) μ) :
    AnalyticOnNhd ℂ
      (fun z : Fin m → ℂ =>
        ∫ ω, Complex.exp (∑ i, z i * (X ω i : ℂ)) ∂μ)
      Set.univ := by
  -- Pass through the `MultivariateComplexMGFCoeff.analyticOnNhd_mgf` brick,
  -- which builds the formal multilinear series and verifies
  -- `HasFPowerSeriesOnBall ... 0 ⊤` directly.
  -- We need to transport between `EuclideanSpace ℝ (Fin m)` and `Fin m → ℝ`.
  -- These are definitionally equal up to `WithLp.ofLp`.
  have hX' : Measurable (fun ω => (WithLp.ofLp (X ω) : Fin m → ℝ)) :=
    (WithLp.measurable_ofLp 2 (Fin m → ℝ)).comp hX
  exact AsymptoticStatistics.ForMathlib.MultivariateComplexMGFCoeff.analyticOnNhd_mgf
    (fun ω => WithLp.ofLp (X ω)) hX' h_mgf

/-- Multivariate complex MGF analyticity.

For any real-valued random vector `X : Ω → EuclideanSpace ℝ (Fin m)`
that is measurable and whose multivariate MGF exists in every real
direction (i.e. `Real.exp(∑ i, t i * X ω i)` is `μ`-integrable for
every `t : Fin m → ℝ`), the complex MGF
`F(z) := ∫ ω, cexp(∑ i, z i * X ω i) ∂μ` is analytic on `ℂᵐ`.

The body chains through `multivariate_complexMGF_analytic`, which routes
to the `MultivariateComplexMGFCoeff` infrastructure (explicit power
series + `HasFPowerSeriesOnBall ... 0 ⊤` + `Metric.eball_top`). The
integrability lift is proven inline. -/
theorem analyticOnNhd_complexMGF_pi
    {m : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin m))
    (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ) :
    AnalyticOnNhd ℂ
      (fun z : Fin m → ℂ =>
        ∫ ω, Complex.exp (∑ i, z i * (X ω i : ℂ)) ∂μ)
      Set.univ := by
  -- Verify the integrability lift at every `z : Fin m → ℂ`. This shows
  -- the function `F(z)` is well-defined (not formally zero by
  -- `integral_undef`) at every point of the alleged analyticity domain.
  have h_int_complex : ∀ z : Fin m → ℂ,
      Integrable
        (fun ω => Complex.exp (∑ i, z i * (X ω i : ℂ))) μ := by
    intro z
    exact integrable_cexp_of_re X hX z (h_mgf (fun i => (z i).re))
  -- Closure step: jointly analytic on ℂᵐ via the explicit power series.
  exact multivariate_complexMGF_analytic X hX h_mgf h_int_complex

end AsymptoticStatistics.ForMathlib.MultivariateComplexMGF
