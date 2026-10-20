module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Absolute first moment of the standard Gaussian

For $g \sim N(0,1)$,
$$ \mathbb{E}\,|g| \;=\; \sqrt{\tfrac{2}{\pi}}, $$
an exact equality (not an inequality). Absent from Mathlib at our pin
(verified); Mathlib-only imports — candidate upstream. This is the source of
the sharp constant $\sqrt{2\pi} = 2\sqrt{\pi/2}$ (the book's display constant
$3$) in the Gaussian symmetrization Lemma 6.6.2 (upper bound).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.6, p. 185 ($\mathbb{E}|g_i| = \sqrt{2/\pi}$ in
the proof of Lemma 6.6.2).

**Proof formalization notes.** Route: unfold `gaussianReal 0 1` as
`withDensity` of `gaussianPDFReal` (variance ≠ 0 branch), split
$\int_{\mathbb{R}} |x|\,\varphi(x)\,dx$ at $0$ by evenness into
$2\int_0^\infty x\,\varphi(x)\,dx$, and evaluate the improper integral of
$x e^{-x^2/2}$ over `Ioi 0` by the antiderivative $-e^{-x^2/2}$
(`integral_Ioi_of_hasDerivAt_of_tendsto`); several `toReal`/`ofReal`
conversions on the density are expected. Integrability from
`memLp_id_gaussianReal` at `p = 1`. Named-sorry fallback of this work item:
`integral_abs_id_gaussianReal` itself (the integrability lemma proven);
downstream Lemma 6.6.2-upper then carries exactly one visible debt.

**Bibliographic comments.** The half-normal mean $\sqrt{2/\pi}$ is classical
(the first absolute moment of the normal law appears already in Gauss's
*Theoria motus*, 1809, and the folded-normal literature); it is standard
material and not attributable to a research paper.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `|g|` is integrable for `g ∼ N(0,1)`. -/
-- LEAN-ONLY: via `memLp_id_gaussianReal` at `p = 1`; no book content.
theorem integrable_abs_id_gaussianReal :
    Integrable (fun x => |x|) (gaussianReal 0 1) := by
  have h : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by simp))
  simpa using h.abs

/-- **Absolute first moment of the standard Gaussian** (HDP §6.6, p. 185):
`E|g| = √(2/π)`, an exact equality. Named-sorry debt candidate of this work
item. -/
theorem integral_abs_id_gaussianReal :
    ∫ x, |x| ∂(gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
  -- Rewrite the Gaussian integral as a weighted volume integral against the pdf.
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
  simp only [smul_eq_mul]
  -- The pdf `φ(x) = (√(2π))⁻¹ · exp(-x²/2)`.
  have hpdf : ∀ x : ℝ,
      gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal_def]
    have h1 : Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)) = Real.sqrt (2 * Real.pi) := by
      norm_num
    have h2 : (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) = -(1 / 2) * x ^ 2 := by
      push_cast; ring
    rw [h1, h2]
  -- `x · exp(-x²/2)` is integrable on the whole line (a Gaussian moment).
  have hXexp : Integrable (fun x : ℝ => x * Real.exp (-(1 / 2) * x ^ 2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 1) (by norm_num)
    simpa [Real.rpow_one] using h
  -- Integrability of the two antiderivative-derivatives and of the full integrand.
  have hEvalInt : Integrable (fun x : ℝ => (-(Real.sqrt (2 * Real.pi))⁻¹)
      * (Real.exp (-(1 / 2) * x ^ 2) * (-x))) :=
    (hXexp.const_mul (Real.sqrt (2 * Real.pi))⁻¹).congr
      (Filter.Eventually.of_forall (fun x => by ring))
  have hEvalGInt : Integrable (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹
      * (Real.exp (-(1 / 2) * x ^ 2) * (-x))) :=
    (hXexp.const_mul (-(Real.sqrt (2 * Real.pi))⁻¹)).congr
      (Filter.Eventually.of_forall (fun x => by ring))
  have hAbsXexp : Integrable (fun x : ℝ => |x| * Real.exp (-(1 / 2) * x ^ 2)) :=
    hXexp.abs.congr (Filter.Eventually.of_forall
      (fun x => by simp only [abs_mul, abs_of_nonneg (Real.exp_pos _).le]))
  have hf_int : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * |x|) :=
    (hAbsXexp.const_mul (Real.sqrt (2 * Real.pi))⁻¹).congr
      (Filter.Eventually.of_forall (fun x => by simp only [hpdf]; ring))
  -- Derivative of `exp(-x²/2)`.
  have hE_deriv : ∀ x : ℝ, HasDerivAt (fun x => Real.exp (-(1 / 2) * x ^ 2))
      (Real.exp (-(1 / 2) * x ^ 2) * (-x)) x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have hin : HasDerivAt (fun x : ℝ => -(1 / 2) * x ^ 2) (-x) x := by
      have h := h2.const_mul (-(1 / 2 : ℝ))
      rw [show (-(1 / 2 : ℝ)) * (2 * x) = -x from by ring] at h
      exact h
    exact hin.exp
  -- Limits at ±∞.
  have hExp_top : Filter.Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => -(1 / 2) * x ^ 2) Filter.atTop Filter.atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by norm_num) (Filter.tendsto_pow_atTop (by norm_num))
    exact Real.tendsto_exp_atBot.comp h1
  have hExp_bot : Filter.Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2))
      Filter.atBot (nhds 0) := by
    have hx2 : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atBot Filter.atTop := by
      have hpow : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop :=
        Filter.tendsto_pow_atTop (by norm_num)
      have := hpow.comp (Filter.tendsto_neg_atBot_atTop (G := ℝ))
      simpa only [Function.comp_def, neg_sq] using this
    have h1 : Filter.Tendsto (fun x : ℝ => -(1 / 2) * x ^ 2) Filter.atBot Filter.atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by norm_num) hx2
    exact Real.tendsto_exp_atBot.comp h1
  have hF_top : Filter.Tendsto (fun x : ℝ => (-(Real.sqrt (2 * Real.pi))⁻¹)
      * Real.exp (-(1 / 2) * x ^ 2)) Filter.atTop (nhds 0) := by
    simpa using hExp_top.const_mul (-(Real.sqrt (2 * Real.pi))⁻¹)
  have hG_bot : Filter.Tendsto (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹
      * Real.exp (-(1 / 2) * x ^ 2)) Filter.atBot (nhds 0) := by
    simpa using hExp_bot.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  -- The two half-line integrals both evaluate to `(√(2π))⁻¹`.
  have hIoival : ∫ x in Set.Ioi (0 : ℝ), gaussianPDFReal 0 1 x * |x|
      = (Real.sqrt (2 * Real.pi))⁻¹ := by
    have hEq : Set.EqOn (fun x => gaussianPDFReal 0 1 x * |x|)
        (fun x => (-(Real.sqrt (2 * Real.pi))⁻¹) * (Real.exp (-(1 / 2) * x ^ 2) * (-x)))
        (Set.Ioi 0) := by
      intro x hx
      have hxpos : (0 : ℝ) < x := hx
      simp only [hpdf x, abs_of_nonneg hxpos.le]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hEq,
      integral_Ioi_of_hasDerivAt_of_tendsto'
        (f := fun x => (-(Real.sqrt (2 * Real.pi))⁻¹) * Real.exp (-(1 / 2) * x ^ 2))
        (fun x _ => (hE_deriv x).const_mul (-(Real.sqrt (2 * Real.pi))⁻¹))
        hEvalInt.integrableOn hF_top]
    simp
  have hIicval : ∫ x in Set.Iic (0 : ℝ), gaussianPDFReal 0 1 x * |x|
      = (Real.sqrt (2 * Real.pi))⁻¹ := by
    have hEq : Set.EqOn (fun x => gaussianPDFReal 0 1 x * |x|)
        (fun x => (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-(1 / 2) * x ^ 2) * (-x)))
        (Set.Iic 0) := by
      intro x hx
      have hxnp : x ≤ 0 := hx
      simp only [hpdf x, abs_of_nonpos hxnp]; ring
    rw [setIntegral_congr_fun measurableSet_Iic hEq,
      integral_Iic_of_hasDerivAt_of_tendsto'
        (f := fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * x ^ 2))
        (fun x _ => (hE_deriv x).const_mul (Real.sqrt (2 * Real.pi))⁻¹)
        hEvalGInt.integrableOn hG_bot]
    simp
  -- Split the line integral at `0` and combine.
  rw [← integral_add_compl (s := Set.Iic (0 : ℝ)) measurableSet_Iic hf_int, Set.compl_Iic,
    hIicval, hIoival]
  -- `2·(√(2π))⁻¹ = √(2/π)`.
  have hs : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [← two_mul, ← div_eq_mul_inv, div_eq_iff hs.ne', ← Real.sqrt_mul (by positivity),
    show (2 / Real.pi) * (2 * Real.pi) = 4 by field_simp; ring,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end StatLean.ConcentrationInequalities
