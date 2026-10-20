module
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
Square-root density helpers for absolutely continuous measures.

When `ν ≪ μ` with `μ` σ-finite, the Radon–Nikodym derivative
`p := ν.rnDeriv μ` is `μ`-a.e. finite, and `√p ∈ L²(μ)` with
`‖√p‖²_{L²(μ)} = ν(univ)`. The bridge between `L²(μ)`-membership of
`g · √p` and `L²(ν)`-membership of `g`, plus the integral identity
`∫ g dν = ∫ g · p dμ`, is what `Core/QMDPath.score_in_L2ZeroMean` needs
to lift its bare-function score to `↥(L2ZeroMean P)`.

These theorem-agnostic lemmas belong to the `ForMathlib` layer.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.ForMathlib.RnDerivSqrt

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Pointwise identity: `√(x.toReal)² = x.toReal` since `x.toReal ≥ 0`. -/
private lemma sqrt_rnDeriv_sq_eq (ν μ : Measure Ω) :
    (fun ω => Real.sqrt ((ν.rnDeriv μ ω).toReal) ^ 2)
      = fun ω => (ν.rnDeriv μ ω).toReal := by
  funext ω; exact Real.sq_sqrt ENNReal.toReal_nonneg

/-- For a finite measure `ν ≪ μ` with `μ` σ-finite, the square-root density
`√(dν/dμ)` is in `L²(μ)`. The norm is computed in `integral_sqrt_rnDeriv_sq`. -/
lemma memLp_sqrt_rnDeriv {ν μ : Measure Ω} [SigmaFinite μ] [IsFiniteMeasure ν]
    (_h_ac : ν ≪ μ) :
    MemLp (fun ω => Real.sqrt (ν.rnDeriv μ ω).toReal) 2 μ := by
  have h_meas : AEStronglyMeasurable
      (fun ω => Real.sqrt ((ν.rnDeriv μ ω).toReal)) μ :=
    ((Measure.measurable_rnDeriv ν μ).ennreal_toReal.sqrt).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq h_meas, sqrt_rnDeriv_sq_eq]
  exact Measure.integrable_toReal_rnDeriv

/-- Hellinger-type identity: the squared `L²(μ)`-norm of `√(dν/dμ)` equals
`ν(univ)`. For `ν` a probability measure this reduces to `1`. -/
lemma integral_sqrt_rnDeriv_sq {ν μ : Measure Ω} [SigmaFinite μ] [IsFiniteMeasure ν]
    (h_ac : ν ≪ μ) :
    ∫ ω, Real.sqrt (ν.rnDeriv μ ω).toReal ^ 2 ∂μ = (ν Set.univ).toReal := by
  rw [sqrt_rnDeriv_sq_eq, Measure.integral_toReal_rnDeriv h_ac, Measure.real_def]

/-- Bridge: if `g · √(dP/dμ) ∈ L²(μ)` and `P ≪ μ` with `μ` σ-finite, then
`g ∈ L²(P)`. -/
lemma memLp_two_of_memLp_two_mul_sqrt_rnDeriv
    {P μ : Measure Ω} [IsFiniteMeasure P] [SigmaFinite μ] (h_ac : P ≪ μ)
    {g : Ω → ℝ} (hg_meas : AEStronglyMeasurable g P)
    (h : MemLp (fun ω => g ω * Real.sqrt (P.rnDeriv μ ω).toReal) 2 μ) :
    MemLp g 2 P := by
  -- We aim for `Integrable (g²) P`, then use `memLp_two_iff_integrable_sq`.
  rw [memLp_two_iff_integrable_sq hg_meas]
  -- `P = μ.withDensity (P.rnDeriv μ)` since `P ≪ μ` and both σ-finite.
  have hP : P = μ.withDensity (P.rnDeriv μ) :=
    (Measure.withDensity_rnDeriv_eq P μ h_ac).symm
  rw [hP, MeasureTheory.integrable_withDensity_iff
        (Measure.measurable_rnDeriv P μ) (Measure.rnDeriv_lt_top P μ)]
  -- Goal: `Integrable (fun x => g x ^ 2 * (P.rnDeriv μ x).toReal) μ`.
  -- This equals `Integrable ((g · √p_0)^2) μ` pointwise, which is `MemLp.integrable_sq`
  -- on the hypothesis `h`.
  have h_sq := h.integrable_sq
  -- Pointwise rewrite `(g · √p_0)^2 = g^2 · p_0.toReal`:
  have h_eq : (fun ω => (g ω * Real.sqrt (P.rnDeriv μ ω).toReal) ^ 2)
                = fun ω => g ω ^ 2 * (P.rnDeriv μ ω).toReal := by
    funext ω
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  rwa [h_eq] at h_sq

/-- Integral identity: `∫ g dP = ∫ g · (dP/dμ) dμ` for `P ≪ μ` with `μ`
σ-finite. The integrability of `g` under `P` is not needed for the
equality (both sides are defined as Bochner integrals, which fall back to
`0` when the integrand fails integrability). -/
lemma integral_eq_integral_mul_rnDeriv_of_ac
    {P μ : Measure Ω} [IsFiniteMeasure P] [SigmaFinite μ] (h_ac : P ≪ μ)
    (g : Ω → ℝ) :
    ∫ ω, g ω ∂P = ∫ ω, g ω * (P.rnDeriv μ ω).toReal ∂μ := by
  rw [← MeasureTheory.integral_rnDeriv_smul h_ac]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  simp [smul_eq_mul, mul_comm]

/-- Set-form of `integral_eq_integral_mul_rnDeriv_of_ac`: `∫_G g dP = ∫_G g·(dP/dμ) dμ`
for any measurable `G`. Obtained by applying the `univ`-form to `Set.indicator G g`. -/
lemma setIntegral_eq_setIntegral_mul_rnDeriv_of_ac
    {P μ : Measure Ω} [IsFiniteMeasure P] [SigmaFinite μ] (h_ac : P ≪ μ)
    (g : Ω → ℝ) {G : Set Ω} (hG : MeasurableSet G) :
    ∫ ω in G, g ω ∂P = ∫ ω in G, g ω * (P.rnDeriv μ ω).toReal ∂μ := by
  rw [← integral_indicator hG,
      integral_eq_integral_mul_rnDeriv_of_ac h_ac (G.indicator g),
      ← integral_indicator hG]
  simp only [Set.indicator_mul_left]

end AsymptoticStatistics.ForMathlib.RnDerivSqrt
