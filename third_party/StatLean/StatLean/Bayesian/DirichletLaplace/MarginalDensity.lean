module
public import StatLean.Bayesian.DirichletLaplace.Defs
public import StatLean.Bayesian.ForMathlib.GammaBounds
public import StatLean.Bayesian.ForMathlib.BindWithDensity
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# Dirichlet–Laplace marginal density (C2)

The univariate Dirichlet–Laplace marginal `DLₐ` (BPPD eq. (10)) is a scale mixture
`θ | ψ ~ Laplace(ψ)`, `ψ ~ Gamma(shape a, rate 1/2)`. This file computes its **Lebesgue density**
in the mixture-integral form and records the basic analytic API used by the density bounds
(`DensityBounds`, C3), the product-density bounds (`PriorDensityBounds`, C4), and the small-ball
estimates (`PriorSmallBall`, C5).

Objects:
* `dlDensity a` — the marginal density `f_{DL,a}(x) = ∫₀^∞ g_{a,1/2}(ψ) · ℓ_ψ(x) dψ` against
  Lebesgue measure (`g_{a,1/2}` the `Gamma(a, rate 1/2)` density, `ℓ_ψ` the centered `Laplace(ψ)`
  density). This is the **mixture-integral** density, *not* the Bessel-function closed form of
  BPPD Proposition 3.1 (a documented non-goal).
* `dlNormConst a = (1/2)^{a+1}/Γ(a)` — the leading constant of `f_{DL,a}` (the `Gamma` prefactor
  `(1/2)^a/Γ(a)` times the Laplace prefactor `1/2`).

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, Journal of the American Statistical Association 110 (2015), 1479–1490
(arXiv:1401.5398). Prior (10)/(11); Proposition 3.1 (marginal density).

**Proof formalization notes.**
* `dlMarginal_eq_withDensity`: unfold the mixture `bind` through `Measure.bind_withDensity` (F3)
  and the `Gamma`-`withDensity` representation `gammaMeasure a 2⁻¹ = volume.withDensity (gammaPDF …)`;
  `lintegral_withDensity` collapses `∫ ℓ_ψ dGamma` to the Lebesgue integral `∫ g_{a,1/2}(ψ) ℓ_ψ(·)`.
* **P1** (`lintegral_dlDensity_eq_one`): total mass `1`, i.e. `f_{DL,a}` is a probability density —
  immediate from `dlMarginal_eq_withDensity` and `isProbabilityMeasure_dlMarginal`.
* **P2** (`dlDensity_anti`): `f_{DL,a}` is nonincreasing in `|x|`, since each Laplace mixand
  `ℓ_ψ(x) = (2ψ)^{-1} e^{-|x|/ψ}` is nonincreasing in `|x|` and the `Gamma` weight is nonnegative
  (`lintegral_mono`, pointwise in `ψ`).
* `dlMarginal_abs_gt_eq_mixture`: the tail `ℙ_{DL,a}(|θ| > δ)` equals `∫ e^{-δ/ψ} dGamma_{a,1/2}(ψ)`
  (each Laplace tail is `ℙ(|θ| > δ | ψ) = e^{-δ/ψ}`, `laplaceMeasure_abs_gt`, F1) — the starting
  point of Lemma 3.3 (C3).
* `dlNormConst` two-sided bounds `a/8 ≤ C(a) ≤ (e/2)·a` on `0 < a ≤ 1`, from the elementary `Γ`
  bounds `1/(e a) ≤ Γ(a) ≤ 2/a` (F2). These feed the `17 a` / `a/64` prefactors of C3.

**Bibliographic comments.** The double-exponential (Laplace) prior as a sparsity-inducing prior
originates with the Bayesian Lasso (T. Park and G. Casella, *J. Amer. Statist. Assoc.* 103 (2008),
681–686); the representation of a heavy-tailed marginal as a global–local scale mixture is the
organizing idea of the shrinkage-prior literature (N. G. Polson and J. G. Scott, *Bayesian
Statistics 9*, Oxford, 2011). The Dirichlet–Laplace prior formalized here is the specific
`Gamma`-mixture-of-Laplace construction of Bhattacharya–Pati–Pillai–Dunson achieving the optimal
posterior-contraction rate in the sparse normal-means problem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-! ### The marginal density and its normalizing constant -/

/-- **Dirichlet–Laplace marginal density** `f_{DL,a}` against Lebesgue measure (BPPD eq. (10)/(11),
mixture-integral form — *not* the Bessel closed form of Proposition 3.1). Pointwise
`f_{DL,a}(x) = ∫₀^∞ g_{a,1/2}(ψ) · ℓ_ψ(x) dψ`, where `g_{a,1/2}` is the `Gamma(a, rate 1/2)` density
(`gammaPDF a 2⁻¹`) and `ℓ_ψ` is the centered `Laplace(ψ)` density (`laplacePDF ψ`). Edge behavior:
at `x = 0` (and, more generally, whenever `a ≤ 1`) the integral is `+∞` — the DL marginal has an
integrable pole at the origin — so the value is a genuine `ℝ≥0∞`. -/
noncomputable def dlDensity (a : ℝ) : ℝ → ℝ≥0∞ :=
  fun x => ∫⁻ ψ, gammaPDF a 2⁻¹ ψ * laplacePDF ψ x ∂volume

/-- **Leading normalizing constant** of the DL marginal density, `C(a) = (1/2)^{a+1} / Γ(a)`
(BPPD §3.1): the product of the `Gamma(a, rate 1/2)` prefactor `(1/2)^a/Γ(a)` with the Laplace
prefactor `1/2`. For `a ≤ 0` it inherits Mathlib's `Real.Gamma` pole conventions and carries no
statistical meaning; every content lemma assumes `0 < a`. -/
noncomputable def dlNormConst (a : ℝ) : ℝ := (1 / 2 : ℝ) ^ (a + 1) / Real.Gamma a

variable {a δ : ℝ}

/-- Pointwise product identity (for `ψ > 0`): the Gamma×Laplace real integrand collapses to the
`dlNormConst`-form `C(a)·ψ^{a-2}·e^{-ψ/2-|x|/ψ}`. The workhorse of the density integral form and the
density bounds. -/
private lemma gammaLaplaceReal_eq {a x ψ : ℝ} (hψ : 0 < ψ) :
    gammaPDFReal a 2⁻¹ ψ * laplacePDFReal ψ x
      = dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ) := by
  rw [gammaPDFReal, if_pos hψ.le, laplacePDFReal, dlNormConst]
  have hE : Real.exp (-(2⁻¹ * ψ)) * Real.exp (-|x| / ψ)
      = Real.exp (-ψ / 2 - |x| / ψ) := by rw [← Real.exp_add]; ring_nf
  have hpow : (1 / 2 : ℝ) ^ (a + 1) = (1 / 2 : ℝ) ^ a * (1 / 2) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have hψpow : ψ ^ (a - 2) = ψ ^ (a - 1) * ψ⁻¹ := by
    rw [← Real.rpow_neg_one ψ, ← Real.rpow_add hψ]; ring_nf
  rw [hpow, hψpow, ← hE, show (2⁻¹ : ℝ) = (1 / 2 : ℝ) by norm_num, mul_inv]
  ring

/-- `ℝ≥0∞`-valued pointwise product identity (for `ψ > 0`): the Gamma×Laplace `ℝ≥0∞` integrand equals
`ofReal (C(a)·ψ^{a-2}·e^{-ψ/2-|x|/ψ})`. Exposed for the density bounds (C3). -/
lemma gammaLaplace_ennreal {a x ψ : ℝ} (ha : 0 < a) (hψ : 0 < ψ) :
    gammaPDF a 2⁻¹ ψ * laplacePDF ψ x
      = ENNReal.ofReal (dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ)) := by
  rw [gammaPDF, laplacePDF,
    ← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha (by norm_num) ψ), gammaLaplaceReal_eq hψ]

/-- Quadratic lower bound on `exp`: `e^{-t} ≤ 4/t²` for `t > 0` (from `t/2 ≤ e^{t/2}`). -/
private lemma exp_neg_le_four_div_sq {t : ℝ} (ht : 0 < t) : Real.exp (-t) ≤ 4 / t ^ 2 := by
  have hexp2 : t ^ 2 / 4 ≤ Real.exp t := by
    have hh : t / 2 ≤ Real.exp (t / 2) := by have := Real.add_one_le_exp (t / 2); linarith
    have he : Real.exp (t / 2) ^ 2 = Real.exp t := by rw [sq, ← Real.exp_add]; ring_nf
    nlinarith [hh, Real.exp_pos (t / 2), ht.le, he]
  rw [Real.exp_neg, show (4 : ℝ) / t ^ 2 = (t ^ 2 / 4)⁻¹ by rw [inv_div]]
  exact inv_anti₀ (by positivity) hexp2

/-- `x ↦ f_{DL,a}(x)` is measurable: a parametrized Lebesgue integral of the jointly measurable
integrand `(ψ, x) ↦ gammaPDF a 2⁻¹ ψ · laplacePDF ψ x`. -/
lemma measurable_dlDensity : Measurable (dlDensity a) := by
  refine measurable_lintegral_param volume ?_
  have h1 : Measurable (fun p : ℝ × ℝ => gammaPDF a 2⁻¹ p.1) :=
    (ProbabilityTheory.measurable_gammaPDFReal a 2⁻¹).ennreal_ofReal.comp measurable_fst
  have h2 : Measurable (fun p : ℝ × ℝ => laplacePDF p.1 p.2) := measurable_laplacePDF_uncurry
  exact h1.mul h2

/-- The DL marginal is the `withDensity` of `f_{DL,a}` against Lebesgue measure (BPPD eq. (11)). -/
lemma dlMarginal_eq_withDensity
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a) :
    dlMarginal a = volume.withDensity (dlDensity a) := by
  haveI : IsProbabilityMeasure (gammaMeasure a 2⁻¹) :=
    isProbabilityMeasure_gammaMeasure ha (by norm_num)
  rw [dlMarginal_eq_bind ha]
  unfold laplaceMeasure
  rw [Measure.bind_withDensity (gammaMeasure a 2⁻¹) volume measurable_laplacePDF_uncurry]
  congr 1
  funext x
  have hg : Measurable (fun b => laplacePDF b x) :=
    measurable_laplacePDF_uncurry.comp (measurable_id.prodMk measurable_const)
  have hf : Measurable (gammaPDF a 2⁻¹) :=
    (ProbabilityTheory.measurable_gammaPDFReal a 2⁻¹).ennreal_ofReal
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hf hg]
  rfl

/-- **Integrability** of the real mixture integrand on `(0, ∞)` for `x ≠ 0`: near `0` the factor
`e^{-|x|/ψ}` kills the `ψ^{a-2}` pole, near `∞` the factor `e^{-ψ/2}` dominates. -/
lemma integrable_dlDensity_integrand
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a)
    -- LEAN-ONLY: off the origin, where the integrand is integrable
    {x : ℝ} (hx : x ≠ 0) :
    IntegrableOn
      (fun ψ => dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ))
      (Set.Ioi (0 : ℝ)) := by
  have hr : 0 < |x| := abs_pos.mpr hx
  -- dominating integrable function `(4/|x|²)·ψ^a·e^{-ψ/2}`
  have hg_int : IntegrableOn (fun ψ => ψ ^ a * Real.exp (-ψ / 2)) (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := a) (p := 1) (b := 1 / 2)
      (by linarith) zero_lt_one (by norm_num)
    refine h.congr_fun (fun ψ _ => ?_) measurableSet_Ioi
    dsimp only; rw [Real.rpow_one]; ring_nf
  have hdom : IntegrableOn (fun ψ => 4 / |x| ^ 2 * (ψ ^ a * Real.exp (-ψ / 2)))
      (Set.Ioi (0 : ℝ)) := hg_int.const_mul _
  -- the (unscaled) core integrand is continuous on `Ioi 0`, hence a.e.-strongly-measurable
  have hcont : ContinuousOn (fun ψ : ℝ => ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ))
      (Set.Ioi (0 : ℝ)) := by
    refine ContinuousOn.mul (continuousOn_id.rpow_const fun ψ hψ => Or.inl (ne_of_gt hψ)) ?_
    refine Real.continuous_exp.comp_continuousOn (ContinuousOn.sub ?_ ?_)
    · exact continuousOn_id.neg.div_const 2
    · exact continuousOn_const.div continuousOn_id fun ψ hψ => ne_of_gt hψ
  -- the (unscaled) core integrand is dominated by `hdom`
  have hcore : IntegrableOn (fun ψ => ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ))
      (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' hdom (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun ψ hψ => ?_)
    have hψ : 0 < ψ := hψ
    have h1 : Real.exp (-ψ / 2 - |x| / ψ)
        = Real.exp (-ψ / 2) * Real.exp (-|x| / ψ) := by rw [← Real.exp_add]; ring_nf
    have ht : 0 < |x| / ψ := div_pos hr hψ
    have h2 : Real.exp (-|x| / ψ) ≤ 4 * ψ ^ 2 / |x| ^ 2 := by
      have := exp_neg_le_four_div_sq ht
      rw [show -|x| / ψ = -(|x| / ψ) by ring]
      refine this.trans_eq ?_
      rw [div_pow, div_div_eq_mul_div]
    have hpsq : ψ ^ (a - 2) * ψ ^ (2 : ℝ) = ψ ^ a := by
      rw [← Real.rpow_add hψ]; ring_nf
    rw [Real.norm_of_nonneg (by positivity)]
    calc ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ)
        = ψ ^ (a - 2) * Real.exp (-ψ / 2) * Real.exp (-|x| / ψ) := by rw [h1]; ring
      _ ≤ ψ ^ (a - 2) * Real.exp (-ψ / 2) * (4 * ψ ^ 2 / |x| ^ 2) := by gcongr
      _ = 4 / |x| ^ 2 * (ψ ^ a * Real.exp (-ψ / 2)) := by
          rw [show (ψ ^ 2 : ℝ) = ψ ^ (2 : ℝ) by rw [Real.rpow_two], ← hpsq]; ring
  -- reintroduce the `dlNormConst a` constant factor
  have hfun : (fun ψ => dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ))
      = (fun ψ => dlNormConst a * (ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ))) := by
    funext ψ; ring
  rw [IntegrableOn, hfun]
  exact hcore.const_mul (dlNormConst a)

/-- **Real integral form** away from the origin: for `x ≠ 0` the mixture integral is finite and is
the `ℝ≥0∞`-coercion of the Bochner integral of `C(a) · ψ^{a-2} · exp(-ψ/2 - |x|/ψ)` over `(0, ∞)`
(the integrand `gammaPDFReal a 2⁻¹ ψ · laplacePDFReal ψ x` on `ψ > 0`, with the two prefactors
collected into `dlNormConst a`). This is the form on which C3's `u = |x|/ψ` substitutions operate. -/
lemma dlDensity_eq_ofReal_integral
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a)
    -- LEAN-ONLY: off the origin, where the density is finite; the pole at 0 is excluded
    {x : ℝ} (hx : x ≠ 0) :
    dlDensity a x
      = ENNReal.ofReal (∫ ψ in Set.Ioi (0 : ℝ),
          dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ)) := by
  -- discard the `ψ ≤ 0` half (integrand vanishes there)
  have h0 : ∫⁻ ψ in Set.Iic 0, gammaPDF a 2⁻¹ ψ * laplacePDF ψ x ∂volume = 0 := by
    rw [setLIntegral_congr (Iio_ae_eq_Iic (a := (0 : ℝ))).symm,
      setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
        (fun ψ (hψ : ψ < 0) => by rw [gammaPDF_of_neg hψ, zero_mul]), lintegral_zero]
  have hsplit : dlDensity a x
      = ∫⁻ ψ in Set.Ioi 0, gammaPDF a 2⁻¹ ψ * laplacePDF ψ x ∂volume := by
    rw [dlDensity, ← lintegral_add_compl
      (fun ψ => gammaPDF a 2⁻¹ ψ * laplacePDF ψ x) measurableSet_Iic, h0, zero_add, Set.compl_Iic]
  rw [hsplit,
    setLIntegral_congr_fun measurableSet_Ioi
      (fun ψ (hψ : 0 < ψ) => gammaLaplace_ennreal ha hψ),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_dlDensity_integrand ha hx)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun ψ (hψ : 0 < ψ) =>
        mul_nonneg (mul_nonneg
          (div_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.Gamma_pos_of_pos ha).le)
          (Real.rpow_nonneg hψ.le _)) (Real.exp_pos _).le))]

/-- **P1 (total mass one).** `f_{DL,a}` integrates to `1` — the DL marginal is a probability density
(BPPD eq. (10)); immediate from `dlMarginal_eq_withDensity` and `isProbabilityMeasure_dlMarginal`. -/
lemma lintegral_dlDensity_eq_one
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a) :
    ∫⁻ x, dlDensity a x ∂volume = 1 := by
  have h1 : (dlMarginal a) Set.univ = 1 := measure_univ
  rw [dlMarginal_eq_withDensity ha, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h1
  exact h1

/-- **P2 (monotone in `|x|`).** The DL marginal density is nonincreasing in `|x|`: for `|x| ≤ |y|`,
`f_{DL,a}(y) ≤ f_{DL,a}(x)`. Each Laplace mixand is nonincreasing in `|·|` and the `Gamma` weight is
nonnegative, so the inequality holds pointwise in `ψ` and passes through the integral. -/
lemma dlDensity_anti {x y : ℝ} (hxy : |x| ≤ |y|) :
    dlDensity a y ≤ dlDensity a x := by
  refine lintegral_mono fun ψ => ?_
  refine mul_le_mul' le_rfl ?_
  -- pointwise `laplacePDF ψ y ≤ laplacePDF ψ x`
  rcases le_or_gt ψ 0 with hψ | hψ
  · have hz : laplacePDF ψ y = 0 := by
      simp only [laplacePDF, laplacePDFReal, ENNReal.ofReal_eq_zero]
      have h2ψ : (2 * ψ)⁻¹ ≤ 0 := inv_nonpos.mpr (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg h2ψ (Real.exp_pos _).le
    rw [hz]; exact zero_le
  · refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    gcongr

/-- **Tail as a `Gamma`-mixture of Laplace tails.** Since `θ | ψ ~ Laplace(ψ)` has
`ℙ(|θ| > δ) = e^{-δ/ψ}`, marginalizing over `ψ ~ Gamma(a, rate 1/2)` gives
`ℙ_{DL,a}(|θ| > δ) = ∫ e^{-δ/ψ} dGamma_{a,1/2}(ψ)` — the starting identity for Lemma 3.3 (C3). -/
lemma dlMarginal_abs_gt_eq_mixture
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a)
    -- USER-INPUT: nonnegative tail threshold; BPPD §3.1 (Lemma 3.3)
    (hδ : 0 ≤ δ) :
    dlMarginal a {x | δ < |x|}
      = ∫⁻ ψ, ENNReal.ofReal (Real.exp (-δ / ψ)) ∂(gammaMeasure a 2⁻¹) := by
  have hmeas : MeasurableSet {x : ℝ | δ < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hκmeas : Measurable (fun b => laplaceMeasure b) :=
    Measure.measurable_of_measurable_coe _ (fun s hs => measurable_laplaceMeasure_apply hs)
  rw [dlMarginal_eq_bind ha, Measure.bind_apply hmeas hκmeas.aemeasurable]
  refine lintegral_congr_ae ?_
  have hpos : ∀ᵐ ψ ∂(gammaMeasure a 2⁻¹), 0 < ψ := by
    rw [ae_iff]
    simp only [not_lt]
    exact gammaMeasure_Iic_eq_zero ha (by norm_num)
  filter_upwards [hpos] with ψ hψ
  exact laplaceMeasure_abs_gt hψ hδ

/-! ### Two-sided bounds on the leading constant (from `GammaBounds`, F2) -/

/-- `C(a) > 0` for `0 < a`. -/
lemma dlNormConst_pos
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a) :
    0 < dlNormConst a :=
  div_pos (by positivity) (Real.Gamma_pos_of_pos ha)

/-- **Upper bound** `C(a) ≤ (e/2)·a` on `0 < a ≤ 1`, from `Γ(a) ≥ 1/(e a)` (`inv_e_mul_le_Gamma`,
F2) and `(1/2)^{a+1} ≤ 1/2`. Source of the `17 a` prefactor in the density upper bound P3 (C3). -/
lemma dlNormConst_le
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1; BPPD §3.1
    (ha1 : a ≤ 1) :
    dlNormConst a ≤ Real.exp 1 / 2 * a := by
  have hGpos : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hnum : (1 / 2 : ℝ) ^ (a + 1) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (a + 1) ≤ (1 / 2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_one]
  have hlow : 1 / (Real.exp 1 * a) ≤ Real.Gamma a := inv_e_mul_le_Gamma ha ha1
  have hea : (0 : ℝ) < Real.exp 1 * a := by positivity
  calc dlNormConst a = (1 / 2 : ℝ) ^ (a + 1) / Real.Gamma a := rfl
    _ ≤ (1 / 2) / (1 / (Real.exp 1 * a)) :=
        div_le_div₀ (by norm_num) hnum (by positivity) hlow
    _ = Real.exp 1 / 2 * a := by rw [div_div_eq_mul_div]; ring

/-- **Lower bound** `a/8 ≤ C(a)` on `0 < a ≤ 1`, from `Γ(a) ≤ 2/a` (`Gamma_le_two_div`, F2) and
`(1/2)^{a+1} ≥ 1/4`. Source of the `a/64` prefactor in the density lower bound P4 (C3). -/
lemma dlNormConst_ge
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1; BPPD §3.1
    (ha1 : a ≤ 1) :
    a / 8 ≤ dlNormConst a := by
  have hGpos : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hnum : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) ^ (a + 1) := by
    calc (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ (2 : ℝ) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      _ ≤ (1 / 2 : ℝ) ^ (a + 1) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
  have hup : Real.Gamma a ≤ 2 / a := Gamma_le_two_div ha ha1
  calc a / 8 = (1 / 4) / (2 / a) := by rw [div_div_eq_mul_div]; ring
    _ ≤ (1 / 2 : ℝ) ^ (a + 1) / Real.Gamma a :=
        div_le_div₀ (by positivity) hnum hGpos hup
    _ = dlNormConst a := rfl

end StatLean.Bayesian
