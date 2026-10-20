module
public import StatLean.Bayesian.EmpiricalBayes.Defs
public import StatLean.Bayesian.ForMathlib.GaussianDeriv

@[expose] public section

/-!
# Tweedie's formula

The most important empirical-Bayes theorem: for a Gaussian likelihood `X ∣ θ ∼ N(θ, v)` with any
prior `G`, the posterior mean of `θ` given the observation is
$$\mathbb E[\theta \mid X = x] = x + v\,\frac{d}{dx}\log f_G(x),$$
where `f_G(x) = ∫ N(x; θ, v)\,G(dθ)` is the marginal density — the posterior mean depends on `G`
only through the *marginal*, which is directly estimable from data. This connects empirical Bayes,
shrinkage, density estimation, and modern large-scale inference.

**Reference.** Not in Robert. B. Efron, *Large-Scale Inference*, Cambridge University Press, 2010,
§1.5, eq. (1.24)–(1.26); B. Efron, "Tweedie's formula and selection bias," *J. Amer. Statist.
Assoc.* 106 (2011), 1602–1614; the formula is credited to M. C. K. Tweedie (via H. Robbins 1956).

**Proof formalization notes.** The Gaussian score identity `(θ−x)·pdf = v·∂ₓ pdf`
(`ForMathlib.GaussianDeriv.hasDerivAt_gaussianPDFReal`) rewrites the numerator
`∫ θ·pdf dG = x·f_G(x) + v·f_G'(x)`; dividing by `f_G(x) > 0` and using `f_G'/f_G = (log f_G)'`
yields the formula. Moving `∂ₓ` inside `∫ · dG(θ)` (`hasDerivAt_gaussianMarginalPDF`) needs a
`G`-integrable envelope for the score, which holds when the prior has a finite first moment
(`Integrable (fun θ => θ) G`) — a genuine analytic side-condition (USER-INPUT, Efron §1.5), not
derivable from the setup. The variance companion needs a finite second moment.

**Bibliographic comments.** Tweedie's formula is the exponential-family posterior-mean identity
attributed by Robbins (1956) to M. C. K. Tweedie; its empirical-Bayes and selection-bias
applications are Efron's (2011). It is the continuous analogue of Robbins's Poisson rule and the
basis of g-modeling (Efron 2016) and of the general-maximum-likelihood empirical Bayes of Jiang and
Zhang (2009).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- The **Gaussian marginal density** `f_G(x) = ∫ N(x; θ, v) G(dθ)` (Efron §1.5). -/
noncomputable def gaussianMarginalPDF (G : Measure ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  ∫ θ, gaussianPDFReal θ v x ∂G

/-- **Tweedie's estimator** `x + v·(log f_G)'(x)` (Efron eq. (1.26)). -/
noncomputable def tweedieEstimator (G : Measure ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  x + (v : ℝ) * deriv (fun y => Real.log (gaussianMarginalPDF G v y)) x

/-- The Gaussian pdf is bounded by its peak `(√(2πv))⁻¹` (the exponential factor is `≤ 1`). -/
private theorem gaussianPDFReal_le_peak (θ : ℝ) (v : ℝ≥0) (y : ℝ) :
    gaussianPDFReal θ v y ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  rw [gaussianPDFReal]
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [Real.exp_le_one_iff, neg_div]
  exact neg_nonpos.mpr (by positivity)

/-- **Differentiation of the marginal under the integral**: the spatial derivative of the Gaussian
marginal density is the `G`-average of the pointwise Gaussian score (Efron §1.5). -/
theorem hasDerivAt_gaussianMarginalPDF (G : Measure ℝ) [IsFiniteMeasure G] (v : ℝ≥0)
    -- USER-INPUT: nondegenerate variance; Efron §1.5
    (hv : v ≠ 0)
    -- USER-INPUT: finite prior first moment (integrable Gaussian-score envelope); Efron §1.5
    (hmean : Integrable (fun θ => θ) G) (x : ℝ) :
    HasDerivAt (gaussianMarginalPDF G v)
      (∫ θ, (θ - x) / (v : ℝ) * gaussianPDFReal θ v x ∂G) x := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by rw [NNReal.coe_pos]; exact zero_lt_iff.mpr hv
  set C : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ with hC
  -- `θ ↦ gaussianPDFReal θ v y` is continuous (hence a.e.-strongly-measurable) for every `y`.
  have hcont_pdf : ∀ y : ℝ, Continuous (fun θ => gaussianPDFReal θ v y) := by
    intro y; unfold gaussianPDFReal; fun_prop
  -- Hypotheses of the parametric differentiation-under-the-integral theorem.
  have hF_meas : ∀ᶠ y in nhds x,
      AEStronglyMeasurable (fun θ => gaussianPDFReal θ v y) G :=
    Filter.Eventually.of_forall fun y => (hcont_pdf y).aestronglyMeasurable
  have hF_int : Integrable (fun θ => gaussianPDFReal θ v x) G := by
    refine (integrable_const C).mono' (hcont_pdf x).aestronglyMeasurable (ae_of_all _ ?_)
    intro θ
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg θ v x)]
    exact gaussianPDFReal_le_peak θ v x
  have hF'_meas : AEStronglyMeasurable
      (fun θ => (θ - x) / (v : ℝ) * gaussianPDFReal θ v x) G := by
    apply Continuous.aestronglyMeasurable
    unfold gaussianPDFReal; fun_prop
  have hbound_int : Integrable (fun θ => (|θ| + (|x| + 1)) / (v : ℝ) * C) G :=
    ((hmean.abs.add (integrable_const _)).div_const _).mul_const _
  have h_bound : ∀ᵐ θ ∂G, ∀ y ∈ Metric.ball x 1,
      ‖(θ - y) / (v : ℝ) * gaussianPDFReal θ v y‖ ≤ (|θ| + (|x| + 1)) / (v : ℝ) * C := by
    refine ae_of_all _ fun θ y hy => ?_
    rw [Metric.mem_ball, Real.dist_eq] at hy
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hvpos,
      abs_of_nonneg (gaussianPDFReal_nonneg θ v y)]
    have ht1 : |θ - y| ≤ |θ| + |y| := by
      calc |θ - y| ≤ |θ - 0| + |0 - y| := abs_sub_le θ 0 y
        _ = |θ| + |y| := by simp
    have ht2 : |y| ≤ |x| + 1 := by
      have := abs_sub_abs_le_abs_sub y x; linarith
    refine mul_le_mul ?_ (gaussianPDFReal_le_peak θ v y)
      (gaussianPDFReal_nonneg θ v y) (by positivity)
    gcongr
    linarith
  have h_diff : ∀ᵐ θ ∂G, ∀ y ∈ Metric.ball x 1,
      HasDerivAt (fun z => gaussianPDFReal θ v z)
        ((θ - y) / (v : ℝ) * gaussianPDFReal θ v y) y :=
    ae_of_all _ fun θ y _ => hasDerivAt_gaussianPDFReal θ v hv y
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (F := fun y θ => gaussianPDFReal θ v y)
    (F' := fun y θ => (θ - y) / (v : ℝ) * gaussianPDFReal θ v y)
    (bound := fun θ => (|θ| + (|x| + 1)) / (v : ℝ) * C)
    (Metric.ball_mem_nhds x one_pos)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact main.2

/-- **Tweedie's formula** (3F.9): the posterior mean of the Gaussian location equals
`x + v·(log f_G)'(x)` (Efron eq. (1.26)). -/
theorem tweedie_normal_posteriorMean (G : Measure ℝ) [IsProbabilityMeasure G] (v : ℝ≥0)
    -- USER-INPUT: nondegenerate variance; Efron §1.5
    (hv : v ≠ 0)
    -- USER-INPUT: finite prior first moment; Efron §1.5
    (hmean : Integrable (fun θ => θ) G)
    -- USER-INPUT: nondegenerate marginal at `x`; Efron §1.5
    (x : ℝ) (hpos : 0 < gaussianMarginalPDF G v x) :
    (∫ θ, θ * gaussianPDFReal θ v x ∂G) / gaussianMarginalPDF G v x = tweedieEstimator G v x := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by rw [NNReal.coe_pos]; exact zero_lt_iff.mpr hv
  have hv' : (v : ℝ) ≠ 0 := ne_of_gt hvpos
  set C : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ with hC
  -- Integrability of the numerator pieces (bounded by the Gaussian peak, times `θ`).
  have hIntpdf : Integrable (fun θ => gaussianPDFReal θ v x) G := by
    have hmeas : AEStronglyMeasurable (fun θ => gaussianPDFReal θ v x) G := by
      apply Continuous.aestronglyMeasurable; unfold gaussianPDFReal; fun_prop
    refine (integrable_const C).mono' hmeas (ae_of_all _ ?_)
    intro θ
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg θ v x)]
    exact gaussianPDFReal_le_peak θ v x
  have hIntθpdf : Integrable (fun θ => θ * gaussianPDFReal θ v x) G := by
    have hmeas : AEStronglyMeasurable (fun θ => θ * gaussianPDFReal θ v x) G := by
      apply Continuous.aestronglyMeasurable; unfold gaussianPDFReal; fun_prop
    refine (hmean.abs.mul_const C).mono' hmeas (ae_of_all _ ?_)
    intro θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg θ v x)]
    exact mul_le_mul_of_nonneg_left (gaussianPDFReal_le_peak θ v x) (abs_nonneg θ)
  -- Marginal derivative and its logarithmic derivative.
  have hderiv := hasDerivAt_gaussianMarginalPDF G v hv hmean x
  have hlogderiv : deriv (fun y => Real.log (gaussianMarginalPDF G v y)) x
      = (∫ θ, (θ - x) / (v : ℝ) * gaussianPDFReal θ v x ∂G) / gaussianMarginalPDF G v x :=
    (hderiv.log hpos.ne').deriv
  -- Gaussian-score identity: `∫ (θ−x)/v·pdf = v⁻¹·(∫θ·pdf − x·f_G(x))`.
  have hInt_eq : ∫ θ, (θ - x) / (v : ℝ) * gaussianPDFReal θ v x ∂G
      = (v : ℝ)⁻¹ * ((∫ θ, θ * gaussianPDFReal θ v x ∂G) - x * gaussianMarginalPDF G v x) := by
    have hpt : (fun θ => (θ - x) / (v : ℝ) * gaussianPDFReal θ v x)
        = fun θ => (v : ℝ)⁻¹ * (θ * gaussianPDFReal θ v x - x * gaussianPDFReal θ v x) := by
      funext θ; ring
    rw [hpt, integral_const_mul, integral_sub hIntθpdf (hIntpdf.const_mul x), integral_const_mul]
    rfl
  rw [tweedieEstimator, hlogderiv, hInt_eq]
  field_simp
  ring

/-- **Second differentiation of the marginal under the integral**: the spatial derivative of the
Gaussian score integral (which is `f_G'`) is the `G`-average of the second-order Gaussian score;
needs a finite second prior moment for the dominating envelope (Efron §1.5). -/
private theorem hasDerivAt_score_gaussianMarginalPDF (G : Measure ℝ) [IsFiniteMeasure G]
    (v : ℝ≥0) (hv : v ≠ 0) (hmean : Integrable (fun θ => θ) G)
    (hsq : Integrable (fun θ => θ ^ 2) G) (x : ℝ) :
    HasDerivAt (fun y => ∫ θ, (θ - y) / (v : ℝ) * gaussianPDFReal θ v y ∂G)
      (∫ θ, (-(1 : ℝ) / (v : ℝ) + (θ - x) ^ 2 / (v : ℝ) ^ 2) * gaussianPDFReal θ v x ∂G) x := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by rw [NNReal.coe_pos]; exact zero_lt_iff.mpr hv
  have hv' : (v : ℝ) ≠ 0 := ne_of_gt hvpos
  set C : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ with hC
  have hInt_absSq : ∀ a : ℝ, Integrable (fun θ => (|θ| + a) ^ 2) G := by
    intro a
    have e : (fun θ => (|θ| + a) ^ 2) = fun θ => θ ^ 2 + (2 * a) * |θ| + a ^ 2 := by
      funext θ; rw [← sq_abs θ]; ring
    rw [e]
    exact (hsq.add (hmean.abs.const_mul (2 * a))).add (integrable_const _)
  have hcont : ∀ y : ℝ, Continuous (fun θ => (θ - y) / (v : ℝ) * gaussianPDFReal θ v y) := by
    intro y; unfold gaussianPDFReal; fun_prop
  have hF_meas : ∀ᶠ y in nhds x,
      AEStronglyMeasurable (fun θ => (θ - y) / (v : ℝ) * gaussianPDFReal θ v y) G :=
    Filter.Eventually.of_forall fun y => (hcont y).aestronglyMeasurable
  have hF_int : Integrable (fun θ => (θ - x) / (v : ℝ) * gaussianPDFReal θ v x) G := by
    have hbd : Integrable (fun θ => (|θ| + |x|) / (v : ℝ) * C) G :=
      (((hmean.abs.add (integrable_const _)).div_const _).mul_const _)
    refine hbd.mono' (hcont x).aestronglyMeasurable (ae_of_all _ ?_)
    intro θ
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hvpos,
      abs_of_nonneg (gaussianPDFReal_nonneg θ v x)]
    have ht : |θ - x| ≤ |θ| + |x| := by
      calc |θ - x| ≤ |θ - 0| + |0 - x| := abs_sub_le θ 0 x
        _ = |θ| + |x| := by simp
    exact mul_le_mul ((div_le_div_iff_of_pos_right hvpos).mpr ht)
      (gaussianPDFReal_le_peak θ v x) (gaussianPDFReal_nonneg θ v x) (by positivity)
  have hF'_meas : AEStronglyMeasurable
      (fun θ => (-(1 : ℝ) / (v : ℝ) + (θ - x) ^ 2 / (v : ℝ) ^ 2) * gaussianPDFReal θ v x) G := by
    apply Continuous.aestronglyMeasurable; unfold gaussianPDFReal; fun_prop
  have hbound_int : Integrable
      (fun θ => (1 / (v : ℝ) + (|θ| + (|x| + 1)) ^ 2 / (v : ℝ) ^ 2) * C) G := by
    have e : (fun θ => (1 / (v : ℝ) + (|θ| + (|x| + 1)) ^ 2 / (v : ℝ) ^ 2) * C)
        = fun θ => 1 / (v : ℝ) * C + C / (v : ℝ) ^ 2 * (|θ| + (|x| + 1)) ^ 2 := by
      funext θ; ring
    rw [e]
    exact (integrable_const _).add ((hInt_absSq (|x| + 1)).const_mul _)
  have h_bound : ∀ᵐ θ ∂G, ∀ y ∈ Metric.ball x 1,
      ‖(-(1 : ℝ) / (v : ℝ) + (θ - y) ^ 2 / (v : ℝ) ^ 2) * gaussianPDFReal θ v y‖
        ≤ (1 / (v : ℝ) + (|θ| + (|x| + 1)) ^ 2 / (v : ℝ) ^ 2) * C := by
    refine ae_of_all _ fun θ y hy => ?_
    rw [Metric.mem_ball, Real.dist_eq] at hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg θ v y)]
    have hyx : |θ - y| ≤ |θ| + (|x| + 1) := by
      have ht1 : |θ - y| ≤ |θ| + |y| := by
        calc |θ - y| ≤ |θ - 0| + |0 - y| := abs_sub_le θ 0 y
          _ = |θ| + |y| := by simp
      have ht2 : |y| ≤ |x| + 1 := by
        have := abs_sub_abs_le_abs_sub y x; linarith
      linarith
    have hcoef : |(-(1 : ℝ) / (v : ℝ) + (θ - y) ^ 2 / (v : ℝ) ^ 2)|
        ≤ 1 / (v : ℝ) + (|θ| + (|x| + 1)) ^ 2 / (v : ℝ) ^ 2 := by
      refine (abs_add_le _ _).trans ?_
      have h1 : |(-(1 : ℝ) / (v : ℝ))| = 1 / (v : ℝ) := by
        rw [abs_div, abs_neg, abs_one, abs_of_pos hvpos]
      have h2 : |((θ - y) ^ 2 / (v : ℝ) ^ 2)| = (θ - y) ^ 2 / (v : ℝ) ^ 2 := by
        rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity : (0:ℝ) < (v:ℝ)^2)]
      rw [h1, h2]
      have hsqle : (θ - y) ^ 2 ≤ (|θ| + (|x| + 1)) ^ 2 := by
        rw [← sq_abs (θ - y)]
        exact pow_le_pow_left₀ (abs_nonneg _) hyx 2
      have := (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < (v:ℝ)^2)).mpr hsqle
      linarith
    exact mul_le_mul hcoef (gaussianPDFReal_le_peak θ v y) (gaussianPDFReal_nonneg θ v y)
      (by positivity)
  have h_diff : ∀ᵐ θ ∂G, ∀ y ∈ Metric.ball x 1,
      HasDerivAt (fun z => (θ - z) / (v : ℝ) * gaussianPDFReal θ v z)
        ((-(1 : ℝ) / (v : ℝ) + (θ - y) ^ 2 / (v : ℝ) ^ 2) * gaussianPDFReal θ v y) y := by
    refine ae_of_all _ fun θ y _ => ?_
    have hu : HasDerivAt (fun z => (θ - z) / (v : ℝ)) ((0 - 1) / (v : ℝ)) y :=
      ((hasDerivAt_const y θ).sub (hasDerivAt_id y)).div_const _
    have hw := hasDerivAt_gaussianPDFReal θ v hv y
    have hmul := hu.fun_mul hw
    refine hmul.congr_deriv ?_
    field_simp
    ring
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (F := fun y θ => (θ - y) / (v : ℝ) * gaussianPDFReal θ v y)
    (F' := fun y θ => (-(1 : ℝ) / (v : ℝ) + (θ - y) ^ 2 / (v : ℝ) ^ 2) * gaussianPDFReal θ v y)
    (bound := fun θ => (1 / (v : ℝ) + (|θ| + (|x| + 1)) ^ 2 / (v : ℝ) ^ 2) * C)
    (Metric.ball_mem_nhds x one_pos)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact main.2

/-- **Tweedie's variance formula** (3F.10, stretch): the posterior variance is
`v + v²·(log f_G)''(x)` (Efron §1.5). -/
theorem tweedie_normal_posteriorVariance (G : Measure ℝ) [IsProbabilityMeasure G] (v : ℝ≥0)
    -- USER-INPUT: nondegenerate variance; Efron §1.5
    (hv : v ≠ 0)
    -- USER-INPUT: finite prior second moment; Efron §1.5
    (hsq : Integrable (fun θ => θ ^ 2) G)
    -- USER-INPUT: nondegenerate marginal at `x`; Efron §1.5
    (x : ℝ) (hpos : 0 < gaussianMarginalPDF G v x) :
    (∫ θ, (θ - tweedieEstimator G v x) ^ 2 * gaussianPDFReal θ v x ∂G) / gaussianMarginalPDF G v x
      = (v : ℝ) + (v : ℝ) ^ 2 * deriv (deriv (fun y => Real.log (gaussianMarginalPDF G v y))) x := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by rw [NNReal.coe_pos]; exact zero_lt_iff.mpr hv
  have hv' : (v : ℝ) ≠ 0 := ne_of_gt hvpos
  set C : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ with hC
  -- First moment integrable, derived from the second moment on a finite measure.
  have hmean : Integrable (fun θ => θ) G := by
    have hb : Integrable (fun θ => 1 + θ ^ 2) G := (integrable_const (1 : ℝ)).add hsq
    refine hb.mono' (by fun_prop) (ae_of_all _ fun θ => ?_)
    simp only [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|θ| - 1), sq_abs θ, abs_nonneg θ]
  -- Polynomial-in-`|θ|` integrability.
  have hInt_absSq : ∀ a : ℝ, Integrable (fun θ => (|θ| + a) ^ 2) G := by
    intro a
    have e : (fun θ => (|θ| + a) ^ 2) = fun θ => θ ^ 2 + (2 * a) * |θ| + a ^ 2 := by
      funext θ; rw [← sq_abs θ]; ring
    rw [e]
    exact (hsq.add (hmean.abs.const_mul (2 * a))).add (integrable_const _)
  -- Integrability of the moment integrands against the pdf at `x`.
  have hIntpdf : Integrable (fun θ => gaussianPDFReal θ v x) G := by
    refine (integrable_const C).mono'
      (by apply Continuous.aestronglyMeasurable; unfold gaussianPDFReal; fun_prop)
      (ae_of_all _ ?_)
    intro θ; rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg θ v x)]
    exact gaussianPDFReal_le_peak θ v x
  have hIntθpdf : Integrable (fun θ => θ * gaussianPDFReal θ v x) G := by
    refine (hmean.abs.mul_const C).mono'
      (by apply Continuous.aestronglyMeasurable; unfold gaussianPDFReal; fun_prop)
      (ae_of_all _ ?_)
    intro θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg θ v x)]
    exact mul_le_mul_of_nonneg_left (gaussianPDFReal_le_peak θ v x) (abs_nonneg θ)
  have hIntθ2pdf : Integrable (fun θ => θ ^ 2 * gaussianPDFReal θ v x) G := by
    refine (hsq.mul_const C).mono'
      (by apply Continuous.aestronglyMeasurable; unfold gaussianPDFReal; fun_prop)
      (ae_of_all _ ?_)
    intro θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg θ),
      abs_of_nonneg (gaussianPDFReal_nonneg θ v x)]
    exact mul_le_mul_of_nonneg_left (gaussianPDFReal_le_peak θ v x) (sq_nonneg θ)
  have hIntsqc : Integrable (fun θ => (θ - x) ^ 2 * gaussianPDFReal θ v x) G := by
    refine ((hInt_absSq |x|).mul_const C).mono'
      (by apply Continuous.aestronglyMeasurable; unfold gaussianPDFReal; fun_prop)
      (ae_of_all _ ?_)
    intro θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (gaussianPDFReal_nonneg θ v x)]
    have hsqle : (θ - x) ^ 2 ≤ (|θ| + |x|) ^ 2 := by
      rw [← sq_abs (θ - x)]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      calc |θ - x| ≤ |θ - 0| + |0 - x| := abs_sub_le θ 0 x
        _ = |θ| + |x| := by simp
    exact mul_le_mul hsqle (gaussianPDFReal_le_peak θ v x) (gaussianPDFReal_nonneg θ v x)
      (by positivity)
  -- The marginal is differentiable everywhere with the score integral as derivative.
  have hderiv_all : ∀ y, HasDerivAt (gaussianMarginalPDF G v)
      (∫ θ, (θ - y) / (v : ℝ) * gaussianPDFReal θ v y ∂G) y :=
    fun y => hasDerivAt_gaussianMarginalPDF G v hv hmean y
  -- The marginal is positive everywhere (integral of a strictly positive density).
  have hpos_all : ∀ y, 0 < gaussianMarginalPDF G v y := by
    intro y
    have hInty : Integrable (fun θ => gaussianPDFReal θ v y) G := by
      refine (integrable_const C).mono'
        (by apply Continuous.aestronglyMeasurable; unfold gaussianPDFReal; fun_prop)
        (ae_of_all _ ?_)
      intro θ; rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg θ v y)]
      exact gaussianPDFReal_le_peak θ v y
    rw [gaussianMarginalPDF,
      integral_pos_iff_support_of_nonneg (fun θ => gaussianPDFReal_nonneg θ v y) hInty]
    have hsupp : Function.support (fun θ => gaussianPDFReal θ v y) = Set.univ :=
      Set.eq_univ_iff_forall.mpr fun θ => (gaussianPDFReal_pos θ v y hv).ne'
    rw [hsupp, measure_univ]
    exact one_pos
  have hfx : gaussianMarginalPDF G v x ≠ 0 := hpos.ne'
  have hfxi : (∫ θ, gaussianPDFReal θ v x ∂G) ≠ 0 := hpos.ne'
  -- Second derivative of the marginal, via the second differentiation-under-integral lemma.
  have hderiv2 := hasDerivAt_score_gaussianMarginalPDF G v hv hmean hsq x
  -- Second derivative of `log f_G` at `x`, by the quotient rule on `f_G'/f_G`.
  have hlog2val : deriv (deriv (fun y => Real.log (gaussianMarginalPDF G v y))) x
      = ((∫ θ, (-(1 : ℝ) / (v : ℝ) + (θ - x) ^ 2 / (v : ℝ) ^ 2) * gaussianPDFReal θ v x ∂G)
            * gaussianMarginalPDF G v x
          - (∫ θ, (θ - x) / (v : ℝ) * gaussianPDFReal θ v x ∂G)
            * (∫ θ, (θ - x) / (v : ℝ) * gaussianPDFReal θ v x ∂G))
        / gaussianMarginalPDF G v x ^ 2 := by
    have hEq : deriv (fun y => Real.log (gaussianMarginalPDF G v y))
        = fun y => (∫ θ, (θ - y) / (v : ℝ) * gaussianPDFReal θ v y ∂G)
            / gaussianMarginalPDF G v y := by
      funext y; exact ((hderiv_all y).log (hpos_all y).ne').deriv
    rw [hEq]
    exact (hderiv2.div (hderiv_all x) hfx).deriv
  -- Score identity `f_G'(x) = v⁻¹(∫θ·pdf − x·f_G(x))`.
  have hM1x : ∫ θ, (θ - x) / (v : ℝ) * gaussianPDFReal θ v x ∂G
      = (v : ℝ)⁻¹ * ((∫ θ, θ * gaussianPDFReal θ v x ∂G)
          - x * (∫ θ, gaussianPDFReal θ v x ∂G)) := by
    have hpt : (fun θ => (θ - x) / (v : ℝ) * gaussianPDFReal θ v x)
        = fun θ => (v : ℝ)⁻¹ * (θ * gaussianPDFReal θ v x - x * gaussianPDFReal θ v x) := by
      funext θ; ring
    rw [hpt, integral_const_mul, integral_sub hIntθpdf (hIntpdf.const_mul x), integral_const_mul]
  -- Second-order score identity `f_G''(x) = −v⁻¹f_G(x) + v⁻²∫(θ−x)²pdf`.
  have hM2P : ∫ θ, (-(1 : ℝ) / (v : ℝ) + (θ - x) ^ 2 / (v : ℝ) ^ 2) * gaussianPDFReal θ v x ∂G
      = -(v : ℝ)⁻¹ * (∫ θ, gaussianPDFReal θ v x ∂G)
          + ((v : ℝ)⁻¹) ^ 2 * (∫ θ, (θ - x) ^ 2 * gaussianPDFReal θ v x ∂G) := by
    have hpt : (fun θ => (-(1 : ℝ) / (v : ℝ) + (θ - x) ^ 2 / (v : ℝ) ^ 2) * gaussianPDFReal θ v x)
        = fun θ => (-(v : ℝ)⁻¹) * gaussianPDFReal θ v x
            + ((v : ℝ)⁻¹) ^ 2 * ((θ - x) ^ 2 * gaussianPDFReal θ v x) := by
      funext θ; ring
    rw [hpt, integral_add (hIntpdf.const_mul _) (hIntsqc.const_mul _),
      integral_const_mul, integral_const_mul]
  -- Expand `∫(θ−x)²pdf`.
  have hP : ∫ θ, (θ - x) ^ 2 * gaussianPDFReal θ v x ∂G
      = (∫ θ, θ ^ 2 * gaussianPDFReal θ v x ∂G)
          - 2 * x * (∫ θ, θ * gaussianPDFReal θ v x ∂G)
          + x ^ 2 * (∫ θ, gaussianPDFReal θ v x ∂G) := by
    have hpt : (fun θ => (θ - x) ^ 2 * gaussianPDFReal θ v x)
        = fun θ => θ ^ 2 * gaussianPDFReal θ v x - 2 * x * (θ * gaussianPDFReal θ v x)
            + x ^ 2 * gaussianPDFReal θ v x := by
      funext θ; ring
    have hIntA : Integrable (fun θ => θ ^ 2 * gaussianPDFReal θ v x
        - 2 * x * (θ * gaussianPDFReal θ v x)) G := hIntθ2pdf.sub (hIntθpdf.const_mul (2 * x))
    rw [hpt, integral_add hIntA (hIntpdf.const_mul (x ^ 2)),
      integral_sub hIntθ2pdf (hIntθpdf.const_mul (2 * x)), integral_const_mul, integral_const_mul]
  -- Expand the posterior second central moment numerator.
  have hLHSnum : ∫ θ, (θ - tweedieEstimator G v x) ^ 2 * gaussianPDFReal θ v x ∂G
      = (∫ θ, θ ^ 2 * gaussianPDFReal θ v x ∂G)
          - 2 * tweedieEstimator G v x * (∫ θ, θ * gaussianPDFReal θ v x ∂G)
          + tweedieEstimator G v x ^ 2 * (∫ θ, gaussianPDFReal θ v x ∂G) := by
    have hpt : (fun θ => (θ - tweedieEstimator G v x) ^ 2 * gaussianPDFReal θ v x)
        = fun θ => θ ^ 2 * gaussianPDFReal θ v x
            - 2 * tweedieEstimator G v x * (θ * gaussianPDFReal θ v x)
            + tweedieEstimator G v x ^ 2 * gaussianPDFReal θ v x := by
      funext θ; ring
    have hIntA : Integrable (fun θ => θ ^ 2 * gaussianPDFReal θ v x
        - 2 * tweedieEstimator G v x * (θ * gaussianPDFReal θ v x)) G :=
      hIntθ2pdf.sub (hIntθpdf.const_mul (2 * tweedieEstimator G v x))
    rw [hpt, integral_add hIntA (hIntpdf.const_mul (tweedieEstimator G v x ^ 2)),
      integral_sub hIntθ2pdf (hIntθpdf.const_mul (2 * tweedieEstimator G v x)),
      integral_const_mul, integral_const_mul]
  -- Posterior mean identity (Tweedie's formula): `∫θ·pdf = m·f_G(x)`.
  have hN1 : ∫ θ, θ * gaussianPDFReal θ v x ∂G
      = tweedieEstimator G v x * (∫ θ, gaussianPDFReal θ v x ∂G) :=
    (div_eq_iff hfx).mp (tweedie_normal_posteriorMean G v hv hmean x hpos)
  -- Assemble: rewrite second-log-derivative and all integral identities, then field algebra.
  rw [hlog2val, hLHSnum, hM2P, hM1x, hP, hN1]
  simp only [gaussianMarginalPDF]
  field_simp
  ring

end StatLean.Bayesian
