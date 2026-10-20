module
public import StatLean.Minimaxity.LeCam.TwoPoint
public import StatLean.Minimaxity.ForMathlib.LeCamInequality
public import StatLean.Minimaxity.ForMathlib.HellingerDivergence
public import StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Minimax rate for the uniform location family

A non-regular parametric estimation problem exhibiting a faster-than-$1/n$ rate. Consider the
uniform location family $\{\mathrm{Uniform}[\theta,\theta+1] : \theta\in\mathbb{R}\}$, and let
$P_\theta = \mathrm{Uniform}[\theta,\theta+1]^{\otimes n}$ be the law of $n$ i.i.d. observations.
Because two such distributions with distinct $\theta$ have infinite Kullback–Leibler divergence,
the standard Pinsker route to Le Cam's two-point lower bound is unavailable; instead one bounds the
total variation distance through the **squared Hellinger distance** (Le Cam's inequality, Wainwright
Lemma 15.3). For the unit-interval shift one computes
$$H^2\bigl(\mathrm{Uniform}[0,1]\,\Vert\,\mathrm{Uniform}[\theta,\theta+1]\bigr) = 2\theta
  \qquad (0\le\theta\le 1),$$
so the affinity of a single sample is $\rho = 1-\theta$ and tensorization gives the exact $n$-fold
value $H^2(P_0\Vert P_\theta) = 2 - 2(1-\theta)^n$. Taking the separation $\theta = 1/n$ and using
$(1-1/n)^n \ge 1/4$ for $n\ge 2$ yields a two-point bound whose induced minimax risk under squared
error obeys
$$\inf_{\hat\theta}\;\sup_{\theta}\;\mathbb{E}_\theta\bigl[(\hat\theta-\theta)^2\bigr]
  \;\ge\; \frac{1-1/\sqrt{2}}{128}\cdot\frac{1}{n^2},$$
the characteristic $n^{-2}$ rate of a non-regular problem (Example 15.5).

The formalization restricts to $n \ge 2$: at $n=1$ the two shifted unit-uniforms $[0,1]$ and $[1,2]$
are almost-everywhere disjoint, forcing total variation distance $1$ and making the two-point bound
vacuous. This is no loss, since the textbook statement is an $n\to\infty$ rate. The explicit
constant $\tfrac{1-1/\sqrt2}{128}$ is the provable constant produced by the chain of inequalities
above; the book states only the order of the rate.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.5
(uniform shift family); the supporting tools are Le Cam's two-point inequality and the
total-variation/Hellinger bound (Lemma 15.3).

**Proof formalization notes.**
* `one_sub_inv_pow_ge_quarter` (with helper `pow_le_four_mul`): the numeric fact
  $(1-1/n)^n \ge 1/4$ for $n\ge 2$ (the minimum is attained at $n=2$, where it equals $1/4$),
  reduced via Bernoulli's inequality `one_add_mul_le_pow`.
* The `Bridge` section reproduces the exact $n$-fold squared-Hellinger tensorization
  $H^2(\mathbb{P}^{\otimes n}\Vert\mathbb{Q}^{\otimes n}) = 2 - 2\rho^n$, which the public
  `HellingerDivergence`/`HellingerProduct` API exposes only in the lossy form
  $H^2(\otimes n)\le n\,H^2$. The `private` helpers `sqHellWith'`, `sqHellinger_eq_ofReal_integral'`,
  `sqHellWith_transfer'` (dominating-measure invariance), `pi_absCont_add'`, `sqHellinger_pi_factor'`
  and `sqHellinger_pi_eq_ofReal_product_integral'` assemble the product factorization against
  `Measure.pi (μ + ν)` and combine with the public `integral_product_residual_sq_eq`.
* `sqHellinger_unit_shift`: $H^2(\mathrm{Unif}[0,1]\Vert\mathrm{Unif}[\theta,\theta+1]) = 2\theta$,
  obtained from the Lebesgue measure $2\theta$ of the symmetric difference of the two unit intervals.
* `uniform_two_point_tvDist_bound`: Le Cam's inequality (`lecam_tv_le_hellinger`) on the $n$-fold
  product with separation $\theta = 1/n$, giving $1 - \lVert\cdot\rVert_{\mathrm{TV}} \ge
  (1-1/\sqrt2)/16$.
* `uniform_location_minimax_rate`: the two-point minimax reduction (`minimax_two_point`) with the
  above total-variation bound, delivering the final $n^{-2}$ rate.

**Bibliographic comments.** This is a classical example rather than a result with a single
seminal source. The uniform shift (location) family is the canonical illustration of a *non-regular*
parametric model whose minimax rate $n^{-2}$ is faster than the parametric $n^{-1}$, because the
log-likelihood is not differentiable in quadratic mean and the densities have non-overlapping
supports for separated parameters. The phenomenon and its analysis via Hellinger-based two-point
bounds are folklore, treated as worked examples in standard references — e.g. Wainwright (2019),
Example 15.5, and in the asymptotic-statistics literature on irregular/super-efficient estimation
(cf. L. Le Cam, *Asymptotic Methods in Statistical Decision Theory*, Springer, 1986; I. A.
Ibragimov and R. Z. Has'minskii, *Statistical Estimation: Asymptotic Theory*, Springer, 1981, which
treat the uniform/discontinuous-density case and its non-standard $n^{-1}$-in-$\theta$,
$n^{-2}$-in-risk behavior). No single original paper is the source of the bound formalized here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open AsymptoticStatistics.ForMathlib.HellingerProduct

namespace StatLean.Minimaxity

/-! ## Numeric lemma: `(1 − 1/n)ⁿ ≥ 1/4` for `n ≥ 2`. -/

/-- Auxiliary: `nⁿ ≤ 4·(n−1)ⁿ` for `n ≥ 2`. Induction; the step uses the decreasing-sequence
fact `((n+1)/n)^(n+1) ≤ (n/(n−1))ⁿ`, itself reduced to Bernoulli `one_add_mul_le_pow`. -/
private lemma pow_le_four_mul (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ n ≤ 4 * ((n : ℝ) - 1) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hm2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hMpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hM21 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
    have hne : (n : ℝ) ^ 2 - 1 ≠ 0 := hM21.ne'
    have key : ((n : ℝ) + 1) ^ (n + 1) ≤ 4 * (n : ℝ) ^ (n + 1) := by
      have ha_pos : (0 : ℝ) < 1 / ((n : ℝ) ^ 2 - 1) := by positivity
      have hPpos : (0 : ℝ) < ((n : ℝ) ^ 2 - 1) ^ n := pow_pos hM21 n
      have hBern := one_add_mul_le_pow
        (a := 1 / ((n : ℝ) ^ 2 - 1)) (by linarith : (-2 : ℝ) ≤ 1 / ((n : ℝ) ^ 2 - 1)) n
      have hfactor : (1 + 1 / ((n : ℝ) ^ 2 - 1)) * ((n : ℝ) ^ 2 - 1) = (n : ℝ) ^ 2 := by
        field_simp; ring
      have hexpand : (1 + 1 / ((n : ℝ) ^ 2 - 1)) ^ n * ((n : ℝ) ^ 2 - 1) ^ n
          = ((n : ℝ) ^ 2) ^ n := by rw [← mul_pow, hfactor]
      have h1 : (1 + (n : ℝ) * (1 / ((n : ℝ) ^ 2 - 1))) * ((n : ℝ) ^ 2 - 1) ^ n
          ≤ ((n : ℝ) ^ 2) ^ n := by
        calc (1 + (n : ℝ) * (1 / ((n : ℝ) ^ 2 - 1))) * ((n : ℝ) ^ 2 - 1) ^ n
            ≤ (1 + 1 / ((n : ℝ) ^ 2 - 1)) ^ n * ((n : ℝ) ^ 2 - 1) ^ n :=
              mul_le_mul_of_nonneg_right hBern hPpos.le
          _ = ((n : ℝ) ^ 2) ^ n := hexpand
      have hDEC : ((n : ℝ) + 1) * ((n : ℝ) ^ 2 - 1) ^ n ≤ (n : ℝ) * ((n : ℝ) ^ 2) ^ n := by
        have hstep : (n : ℝ) * ((1 + (n : ℝ) * (1 / ((n : ℝ) ^ 2 - 1))) * ((n : ℝ) ^ 2 - 1) ^ n)
            ≤ (n : ℝ) * ((n : ℝ) ^ 2) ^ n := mul_le_mul_of_nonneg_left h1 hMpos.le
        refine le_trans ?_ hstep
        have hcoef : ((n : ℝ) + 1) ≤ (n : ℝ) * (1 + (n : ℝ) * (1 / ((n : ℝ) ^ 2 - 1))) := by
          rw [mul_add, mul_one]
          have h2a : (n : ℝ) * ((n : ℝ) * (1 / ((n : ℝ) ^ 2 - 1)))
              = 1 + 1 / ((n : ℝ) ^ 2 - 1) := by field_simp; ring
          have : (1 : ℝ) ≤ (n : ℝ) * ((n : ℝ) * (1 / ((n : ℝ) ^ 2 - 1))) := by
            rw [h2a]; linarith [ha_pos]
          linarith
        calc ((n : ℝ) + 1) * ((n : ℝ) ^ 2 - 1) ^ n
            ≤ ((n : ℝ) * (1 + (n : ℝ) * (1 / ((n : ℝ) ^ 2 - 1)))) * ((n : ℝ) ^ 2 - 1) ^ n :=
              mul_le_mul_of_nonneg_right hcoef hPpos.le
          _ = (n : ℝ) * ((1 + (n : ℝ) * (1 / ((n : ℝ) ^ 2 - 1))) * ((n : ℝ) ^ 2 - 1) ^ n) := by
              ring
      have hMfac : ((n : ℝ) ^ 2 - 1) ^ n = ((n : ℝ) + 1) ^ n * ((n : ℝ) - 1) ^ n := by
        rw [← mul_pow]; congr 1; ring
      rw [hMfac] at hDEC
      have hL : ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ n * ((n : ℝ) - 1) ^ n)
          = ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) - 1) ^ n := by rw [pow_succ]; ring
      have hR : (n : ℝ) * ((n : ℝ) ^ 2) ^ n = (n : ℝ) ^ (2 * n + 1) := by
        rw [← pow_mul, pow_succ']
      rw [hL, hR] at hDEC
      have hIH2 : (n : ℝ) ^ (2 * n + 1) ≤ 4 * ((n : ℝ) - 1) ^ n * (n : ℝ) ^ (n + 1) := by
        have hmul := mul_le_mul_of_nonneg_right ih
          (show (0 : ℝ) ≤ (n : ℝ) ^ (n + 1) by positivity)
        rw [show (n : ℝ) ^ n * (n : ℝ) ^ (n + 1) = (n : ℝ) ^ (2 * n + 1) by
          rw [← pow_add]; congr 1; omega] at hmul
        linarith [hmul]
      have hcomb : ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) - 1) ^ n
          ≤ (4 * (n : ℝ) ^ (n + 1)) * ((n : ℝ) - 1) ^ n := by
        calc ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) - 1) ^ n
            ≤ (n : ℝ) ^ (2 * n + 1) := hDEC
          _ ≤ 4 * ((n : ℝ) - 1) ^ n * (n : ℝ) ^ (n + 1) := hIH2
          _ = (4 * (n : ℝ) ^ (n + 1)) * ((n : ℝ) - 1) ^ n := by ring
      have hDn : (0 : ℝ) < ((n : ℝ) - 1) ^ n := pow_pos (by linarith) n
      exact le_of_mul_le_mul_right hcomb hDn
    calc ((n + 1 : ℕ) : ℝ) ^ (n + 1)
        = ((n : ℝ) + 1) ^ (n + 1) := by push_cast; ring
      _ ≤ 4 * (n : ℝ) ^ (n + 1) := key
      _ = 4 * (((n + 1 : ℕ) : ℝ) - 1) ^ (n + 1) := by push_cast; ring

/-- For `n ≥ 2`, `(1 − 1/n)ⁿ ≥ 1/4` (minimum at `n = 2`, where it equals `1/4`). -/
private lemma one_sub_inv_pow_ge_quarter (n : ℕ) (hn : 2 ≤ n) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (n : ℝ)) ^ n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have haux := pow_le_four_mul n hn
  have hnn : (0 : ℝ) < (n : ℝ) ^ n := by positivity
  rw [show (1 : ℝ) - 1 / (n : ℝ) = ((n : ℝ) - 1) / (n : ℝ) by field_simp, div_pow,
    le_div_iff₀ hnn]
  linarith [haux]

/-! ## Exact `n`-fold squared-Hellinger bridge.

The closed-form tensorization `H²(ℙ^{⊗n} ‖ ℚ^{⊗n}) = 2 − 2·ρⁿ` (with affinity `ρ`) is not exposed
publicly by `HellingerDivergence`/`HellingerProduct` (only the lossy `H²(⊗n) ≤ n·H²` is). We
reproduce the needed dominating-measure-invariance and product-factorization bridges here as
`private` helpers, then combine with the public `integral_product_residual_sq_eq`
(`= 2 − 2·ρⁿ`). -/

section Bridge

variable {α : Type*} {mα : MeasurableSpace α}

private theorem absCont_left' (μ ν : Measure α) : μ ≪ μ + ν :=
  Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)

private theorem absCont_right' (μ ν : Measure α) : ν ≪ μ + ν :=
  Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)

/-- Squared-Hellinger lintegral against an arbitrary common dominating reference `ξ`
(`sqHellinger μ ν` is the special case `ξ = μ + ν`, definitionally). -/
private noncomputable def sqHellWith' (A B ξ : Measure α) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal
    ((Real.sqrt (A.rnDeriv ξ x).toReal - Real.sqrt (B.rnDeriv ξ x).toReal) ^ 2) ∂ξ

/-- Bridge of `sqHellinger` to the real `L²`-residual integral against `ξ = μ + ν`. -/
private theorem sqHellinger_eq_ofReal_integral' (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger μ ν = ENNReal.ofReal
      (∫ ω, (Real.sqrt (μ.rnDeriv (μ + ν) ω).toReal
              - Real.sqrt (ν.rnDeriv (μ + ν) ω).toReal) ^ 2 ∂(μ + ν)) := by
  have hμ := absCont_left' μ ν
  have hν := absCont_right' μ ν
  have hint := (hellinger_per_sample_residual_memLp_two hμ hν).integrable_sq
  unfold sqHellinger
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm

/-- Dominating-measure invariance of the squared-Hellinger lintegral. -/
private theorem sqHellWith_transfer' (A B ξ' ξ : Measure α)
    [SigmaFinite A] [SigmaFinite B] [SigmaFinite ξ'] [SigmaFinite ξ]
    (hAξ' : A ≪ ξ') (hBξ' : B ≪ ξ') (hξ'ξ : ξ' ≪ ξ) :
    sqHellWith' A B ξ' = sqHellWith' A B ξ := by
  unfold sqHellWith'
  set w := ξ'.rnDeriv ξ with hw
  have hw_meas : Measurable w := Measure.measurable_rnDeriv _ _
  have hξ'eq : ξ' = ξ.withDensity w := (Measure.withDensity_rnDeriv_eq _ _ hξ'ξ).symm
  set F : α → ℝ≥0∞ := fun x => ENNReal.ofReal
      ((Real.sqrt (A.rnDeriv ξ' x).toReal - Real.sqrt (B.rnDeriv ξ' x).toReal) ^ 2) with hF
  have hF_meas : Measurable F := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.pow _ measurable_const
    exact ((((Measure.measurable_rnDeriv A ξ').ennreal_toReal).sqrt).sub
      (((Measure.measurable_rnDeriv B ξ').ennreal_toReal).sqrt))
  rw [hξ'eq, lintegral_withDensity_eq_lintegral_mul ξ hw_meas hF_meas]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := ξ) hAξ',
    Measure.rnDeriv_mul_rnDeriv (κ := ξ) hBξ',
    Measure.rnDeriv_lt_top ξ' ξ] with x hAx hBx hwx
  rw [Pi.mul_apply] at hAx hBx
  set wr := (w x).toReal with hwr
  have hwr_nn : 0 ≤ wr := ENNReal.toReal_nonneg
  set a' := (A.rnDeriv ξ' x).toReal with ha'
  set b' := (B.rnDeriv ξ' x).toReal with hb'
  have ha_eq : (A.rnDeriv ξ x).toReal = wr * a' := by
    rw [← hAx, ENNReal.toReal_mul, hwr, ha']; ring
  have hb_eq : (B.rnDeriv ξ x).toReal = wr * b' := by
    rw [← hBx, ENNReal.toReal_mul, hwr, hb']; ring
  change (w x * F x) = ENNReal.ofReal
      ((Real.sqrt (A.rnDeriv ξ x).toReal - Real.sqrt (B.rnDeriv ξ x).toReal) ^ 2)
  rw [hF]
  simp only []
  rw [show w x = ENNReal.ofReal wr from (ENNReal.ofReal_toReal hwx.ne).symm,
    ← ENNReal.ofReal_mul hwr_nn]
  congr 1
  rw [ha_eq, hb_eq, Real.sqrt_mul hwr_nn, Real.sqrt_mul hwr_nn]
  have hsq : Real.sqrt wr ^ 2 = wr := Real.sq_sqrt hwr_nn
  have hexp : (Real.sqrt wr * Real.sqrt a' - Real.sqrt wr * Real.sqrt b') ^ 2
       = Real.sqrt wr ^ 2 * (Real.sqrt a' - Real.sqrt b') ^ 2 := by ring
  rw [hexp, hsq]

/-- Absolute continuity of i.i.d. products under coordinatewise domination. -/
private theorem pi_absCont_add' (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : Fin n => μ) ≪ (Measure.pi fun _ : Fin n => (μ + ν)) := by
  have hμ : μ ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  set ξ : Measure α := μ + ν with hξ
  have hfμ : Measurable (μ.rnDeriv ξ) := Measure.measurable_rnDeriv _ _
  haveI : ∀ _ : Fin n, SigmaFinite ((ξ).withDensity (μ.rnDeriv ξ)) := by
    intro _; rw [Measure.withDensity_rnDeriv_eq _ _ hμ]; infer_instance
  have hpiμ : (Measure.pi fun _ : Fin n => μ)
      = (Measure.pi fun _ : Fin n => ξ).withDensity (fun x => ∏ j, μ.rnDeriv ξ (x j)) := by
    rw [pi_withDensity_prod (fun _ => hfμ)]
    congr 1; ext i; rw [Measure.withDensity_rnDeriv_eq _ _ hμ]
  rw [hpiμ]
  exact withDensity_absolutelyContinuous _ _

/-- Product factorization of the squared-Hellinger lintegral against `Measure.pi (μ + ν)`. -/
private theorem sqHellinger_pi_factor' (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellWith' (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
        (Measure.pi fun _ : Fin n => (μ + ν))
      = ENNReal.ofReal
          (∫ X : Fin n → α,
            ((∏ j, Real.sqrt (μ.rnDeriv (μ + ν) (X j)).toReal)
              - ∏ j, Real.sqrt (ν.rnDeriv (μ + ν) (X j)).toReal) ^ 2
            ∂(Measure.pi fun _ : Fin n => (μ + ν))) := by
  have hμ : μ ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hν : ν ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  set ξ : Measure α := μ + ν with hξ
  have hfμ : Measurable (μ.rnDeriv ξ) := Measure.measurable_rnDeriv _ _
  have hfν : Measurable (ν.rnDeriv ξ) := Measure.measurable_rnDeriv _ _
  haveI : ∀ _ : Fin n, SigmaFinite ((ξ).withDensity (μ.rnDeriv ξ)) := by
    intro _; rw [Measure.withDensity_rnDeriv_eq _ _ hμ]; infer_instance
  haveI : ∀ _ : Fin n, SigmaFinite ((ξ).withDensity (ν.rnDeriv ξ)) := by
    intro _; rw [Measure.withDensity_rnDeriv_eq _ _ hν]; infer_instance
  have hpiμ : (Measure.pi fun _ : Fin n => μ)
      = (Measure.pi fun _ : Fin n => ξ).withDensity (fun x => ∏ j, μ.rnDeriv ξ (x j)) := by
    rw [pi_withDensity_prod (fun _ => hfμ)]
    congr 1; ext i; rw [Measure.withDensity_rnDeriv_eq _ _ hμ]
  have hpiν : (Measure.pi fun _ : Fin n => ν)
      = (Measure.pi fun _ : Fin n => ξ).withDensity (fun x => ∏ j, ν.rnDeriv ξ (x j)) := by
    rw [pi_withDensity_prod (fun _ => hfν)]
    congr 1; ext i; rw [Measure.withDensity_rnDeriv_eq _ _ hν]
  have hrnμ : (Measure.pi fun _ : Fin n => μ).rnDeriv (Measure.pi fun _ : Fin n => ξ)
      =ᵐ[Measure.pi fun _ : Fin n => ξ] (fun x => ∏ j, μ.rnDeriv ξ (x j)) := by
    conv_lhs => rw [hpiμ]
    exact Measure.rnDeriv_withDensity _
      (Finset.measurable_prod _ (fun j _ => hfμ.comp (measurable_pi_apply j)))
  have hrnν : (Measure.pi fun _ : Fin n => ν).rnDeriv (Measure.pi fun _ : Fin n => ξ)
      =ᵐ[Measure.pi fun _ : Fin n => ξ] (fun x => ∏ j, ν.rnDeriv ξ (x j)) := by
    conv_lhs => rw [hpiν]
    exact Measure.rnDeriv_withDensity _
      (Finset.measurable_prod _ (fun j _ => hfν.comp (measurable_pi_apply j)))
  unfold sqHellWith'
  rw [show (Measure.pi fun _ : Fin n => (μ + ν)) = (Measure.pi fun _ : Fin n => ξ) from rfl]
  rw [lintegral_congr_ae (g := fun X => ENNReal.ofReal
      (((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
        - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2))]
  · rw [← ofReal_integral_eq_lintegral_ofReal]
    · exact (hellinger_product_residual_memLp_two_perCoord (μ := μ) (ν := ν) (ξ := ξ)
        (n := n) hμ hν).integrable_sq
    · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  · filter_upwards [hrnμ, hrnν] with x hx hy
    rw [hx, hy, ← prod_sqrt_eq_sqrt_prod_toReal, ← prod_sqrt_eq_sqrt_prod_toReal]

/-- Exact `n`-fold squared Hellinger as `ENNReal.ofReal` of the product residual integral. -/
private theorem sqHellinger_pi_eq_ofReal_product_integral' (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
      = ENNReal.ofReal
          (∫ X : Fin n → α,
            ((∏ j, Real.sqrt (μ.rnDeriv (μ + ν) (X j)).toReal)
              - ∏ j, Real.sqrt (ν.rnDeriv (μ + ν) (X j)).toReal) ^ 2
            ∂(Measure.pi fun _ : Fin n => (μ + ν))) := by
  set A := Measure.pi fun _ : Fin n => μ with hA
  set B := Measure.pi fun _ : Fin n => ν with hB
  set P := Measure.pi fun _ : Fin n => (μ + ν) with hP
  have hAP : A ≪ P := pi_absCont_add' n μ ν
  have hBP : B ≪ P := by
    have := pi_absCont_add' n ν μ
    rwa [add_comm ν μ] at this
  have hAAB : A ≪ A + B := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hBAB : B ≪ A + B := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  set ζ := (A + B) + P with hζ
  have hABζ : (A + B) ≪ ζ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hPζ : P ≪ ζ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  change sqHellWith' A B (A + B) = _
  rw [sqHellWith_transfer' A B (A + B) ζ hAAB hBAB hABζ,
      ← sqHellWith_transfer' A B P ζ hAP hBP hPζ]
  exact sqHellinger_pi_factor' n μ ν

end Bridge

/-! ## Single-sample squared Hellinger of the unit-interval shift. -/

/-- **Single-sample squared Hellinger of the unit-interval shift.** For `θ ∈ [0, 1]`,
`H²(Unif[0,1] ‖ Unif[θ, θ+1]) = 2θ` — the symmetric difference of the two unit intervals has
Lebesgue measure `2θ`. -/
private lemma sqHellinger_unit_shift (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    sqHellinger (volume.restrict (Set.Icc (0 : ℝ) 1))
        (volume.restrict (Set.Icc θ (θ + 1)))
      = ENNReal.ofReal (2 * θ) := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμdef
  set ν : Measure ℝ := volume.restrict (Set.Icc θ (θ + 1)) with hνdef
  have hμv : μ ≪ volume := by rw [hμdef]; exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hνv : ν ≪ volume := by rw [hνdef]; exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hμμν : μ ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hνμν : ν ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hμνv : μ + ν ≪ volume := hμv.add_left hνv
  -- transfer to Lebesgue reference
  rw [show sqHellinger μ ν = sqHellWith' μ ν (μ + ν) from rfl,
      sqHellWith_transfer' μ ν (μ + ν) volume hμμν hνμν hμνv]
  -- replace rnDerivs by indicators a.e.
  have hrnμ : μ.rnDeriv volume =ᵐ[volume] (Set.Icc (0 : ℝ) 1).indicator 1 := by
    rw [hμdef]; exact Measure.rnDeriv_restrict_self volume measurableSet_Icc
  have hrnν : ν.rnDeriv volume =ᵐ[volume] (Set.Icc θ (θ + 1)).indicator 1 := by
    rw [hνdef]; exact Measure.rnDeriv_restrict_self volume measurableSet_Icc
  set A : Set ℝ := Set.Icc (0 : ℝ) 1 with hA
  set B : Set ℝ := Set.Icc θ (θ + 1) with hB
  have hABset : A \ B = Set.Ico 0 θ := by
    rw [hA, hB]; ext x
    simp only [Set.mem_diff, Set.mem_Icc, Set.mem_Ico, not_and, not_le]
    constructor
    · rintro ⟨⟨hx0, hx1⟩, h⟩
      refine ⟨hx0, ?_⟩
      by_contra hxθ
      push_neg at hxθ
      have := h hxθ; linarith
    · rintro ⟨hx0, hxθ⟩
      refine ⟨⟨hx0, by linarith⟩, ?_⟩
      intro hθx; linarith
  have hBAset : B \ A = Set.Ioc 1 (θ + 1) := by
    rw [hA, hB]; ext x
    simp only [Set.mem_diff, Set.mem_Icc, Set.mem_Ioc, not_and, not_le]
    constructor
    · rintro ⟨⟨hθx, hx1⟩, h⟩
      have hx0 : (0 : ℝ) ≤ x := by linarith
      exact ⟨h hx0, hx1⟩
    · rintro ⟨h1x, hxθ1⟩
      refine ⟨⟨by linarith, hxθ1⟩, ?_⟩
      intro hx0; linarith
  -- pointwise: integrand = indicator (A\B) + indicator (B\A)
  unfold sqHellWith'
  have hpt : (fun x => ENNReal.ofReal
        ((Real.sqrt (μ.rnDeriv volume x).toReal
          - Real.sqrt (ν.rnDeriv volume x).toReal) ^ 2))
      =ᵐ[volume] (fun x => (A \ B).indicator (fun _ => (1 : ℝ≥0∞)) x
          + (B \ A).indicator (fun _ => (1 : ℝ≥0∞)) x) := by
    filter_upwards [hrnμ, hrnν] with x hx hy
    rw [hx, hy]
    by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
      simp [Set.indicator_apply, Set.mem_diff, hxA, hxB]
  rw [lintegral_congr_ae hpt]
  have hAmeas : MeasurableSet (A \ B) := by rw [hA, hB]; exact measurableSet_Icc.diff measurableSet_Icc
  have hBmeas : MeasurableSet (B \ A) := by rw [hA, hB]; exact measurableSet_Icc.diff measurableSet_Icc
  rw [lintegral_add_left (measurable_const.indicator hAmeas)]
  have hvolAB : ∫⁻ x, (A \ B).indicator (fun _ => (1 : ℝ≥0∞)) x ∂volume = volume (A \ B) := by
    rw [lintegral_indicator hAmeas]; simp
  have hvolBA : ∫⁻ x, (B \ A).indicator (fun _ => (1 : ℝ≥0∞)) x ∂volume = volume (B \ A) := by
    rw [lintegral_indicator hBmeas]; simp
  rw [hvolAB, hvolBA, hABset, hBAset, Real.volume_Ico, Real.volume_Ioc,
    show θ - 0 = θ by ring, show θ + 1 - 1 = θ by ring, ← ENNReal.ofReal_add hθ0 hθ0]
  congr 1; ring

/-- **Crux: two-point total-variation bound for the uniform location family.** With the separation
`θ₁ = 1/n`, Le Cam's inequality (Wainwright Lemma 15.3, `lecam_tv_le_hellinger`) applied to the
`n`-fold product, together with the squared-Hellinger computation for the unit-interval shift,
yields `1 − ‖·‖_TV ≥ (1 − 1/√2)/16`. -/
-- LEAN-ONLY: n ≥ 2 (at n=1 the shifted unit-uniforms [0,1],[1,2] are a.e. disjoint ⇒ TV=1, so the
-- two-point bound is vacuous); Wainwright Ex 15.5 is an n→∞ rate.
private lemma uniform_two_point_tvDist_bound (n : ℕ) (hn : 2 ≤ n)
    (P : Kernel ℝ (Fin n → ℝ)) [IsMarkovKernel P]
    (hP : ∀ θ : ℝ, P θ = Measure.pi fun _ : Fin n => volume.restrict (Set.Icc θ (θ + 1))) :
    ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 16) ≤ 1 - tvDist (P 0) (P ((n : ℝ)⁻¹)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  set θ : ℝ := (n : ℝ)⁻¹ with hθdef
  have hθ0 : (0 : ℝ) < θ := by rw [hθdef]; positivity
  have hθ0' : (0 : ℝ) ≤ θ := hθ0.le
  have hθ1 : θ ≤ 1 := by rw [hθdef]; exact inv_le_one_of_one_le₀ hn1
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμdef
  set ν : Measure ℝ := volume.restrict (Set.Icc θ (θ + 1)) with hνdef
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [hμdef]; refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num
  haveI hνprob : IsProbabilityMeasure ν := by
    rw [hνdef]; refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Icc, show θ + 1 - θ = 1 by ring]; norm_num
  have hP0 : P 0 = Measure.pi fun _ : Fin n => μ := by
    rw [hP 0]; simp only [zero_add, hμdef]
  have hPθ : P θ = Measure.pi fun _ : Fin n => ν := by rw [hP θ, hνdef]
  have hsingle : sqHellinger μ ν = ENNReal.ofReal (2 * θ) := sqHellinger_unit_shift θ hθ0' hθ1
  -- affinity value `ρ = 1 − θ`
  have haff : (∫ ω, Real.sqrt (μ.rnDeriv (μ + ν) ω).toReal
        * Real.sqrt (ν.rnDeriv (μ + ν) ω).toReal ∂(μ + ν)) = 1 - θ := by
    have hper := integral_per_sample_residual_sq_eq (absCont_left' μ ν) (absCont_right' μ ν)
    have hbridge := sqHellinger_eq_ofReal_integral' μ ν
    have hle1 := integral_sqrt_mul_sqrt_le_one (absCont_left' μ ν) (absCont_right' μ ν)
    have h1 : ENNReal.ofReal (2 * θ)
        = ENNReal.ofReal (2 - 2 * (∫ ω, Real.sqrt (μ.rnDeriv (μ + ν) ω).toReal
            * Real.sqrt (ν.rnDeriv (μ + ν) ω).toReal ∂(μ + ν))) := by
      rw [← hsingle, hbridge, hper]
    have h2 : 2 * θ = 2 - 2 * (∫ ω, Real.sqrt (μ.rnDeriv (μ + ν) ω).toReal
            * Real.sqrt (ν.rnDeriv (μ + ν) ω).toReal ∂(μ + ν)) := by
      have hc := congrArg ENNReal.toReal h1
      rwa [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith [hle1])] at hc
    linear_combination h2 / 2
  -- exact `n`-fold squared Hellinger `= 2 − 2 ρⁿ`
  have hnfold : sqHellinger (P 0) (P θ) = ENNReal.ofReal (2 - 2 * (1 - θ) ^ n) := by
    rw [hP0, hPθ, sqHellinger_pi_eq_ofReal_product_integral' n μ ν,
        integral_product_residual_sq_eq (absCont_left' μ ν) (absCont_right' μ ν), haff]
  -- power bound `ρⁿ ≥ 1/4`
  have hcpos : (0 : ℝ) ≤ 1 - θ := by linarith
  have hc14 : (1 / 4 : ℝ) ≤ (1 - θ) ^ n := by
    have h := one_sub_inv_pow_ge_quarter n hn
    rwa [show (1 : ℝ) - 1 / (n : ℝ) = 1 - θ by rw [hθdef]; ring] at h
  have hc1 : (1 - θ) ^ n ≤ 1 := pow_le_one₀ hcpos (by linarith)
  -- abstract `R = 2 − 2 ρⁿ`
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 - 2 * (1 - θ) ^ n := ⟨_, rfl⟩
  have hR0 : (0 : ℝ) ≤ R := by rw [hRdef]; linarith [hc1]
  have hRle : R ≤ 3 / 2 := by rw [hRdef]; linarith [hc14]
  -- Le Cam (Lemma 15.3) on the `n`-fold product
  have hlecam := lecam_tv_le_hellinger (P 0) (P θ)
  rw [hnfold, ← hRdef] at hlecam
  -- rewrite the Hellinger RHS as `ofReal (√R · √(1 − R/4))`
  have h1sub : (1 : ℝ≥0∞) - ENNReal.ofReal R / 4 = ENNReal.ofReal (1 - R / 4) := by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
        ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
        show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
        ← ENNReal.ofReal_sub _ (by positivity : (0 : ℝ) ≤ R / 4)]
  have hrhs : (ENNReal.ofReal R) ^ (1 / 2 : ℝ) * (1 - ENNReal.ofReal R / 4) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt R * Real.sqrt (1 - R / 4)) := by
    simp only [h1sub]
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg R)]
    congr 1
    · rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hR0 (by norm_num)]
    · rw [Real.sqrt_eq_rpow,
        ENNReal.ofReal_rpow_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - R / 4) (by norm_num)]
  rw [hrhs, ← Real.sqrt_mul hR0] at hlecam
  -- numeric: `√(R·(1−R/4)) ≤ 31/32` (since `R ≤ 3/2`)
  have hbound : Real.sqrt (R * (1 - R / 4)) ≤ 31 / 32 := by
    have hRR : R * (1 - R / 4) ≤ 15 / 16 := by
      nlinarith [hRle, hR0, mul_nonneg (show (0 : ℝ) ≤ 3 / 2 - R by linarith)
        (show (0 : ℝ) ≤ 5 / 2 - R by linarith)]
    calc Real.sqrt (R * (1 - R / 4)) ≤ Real.sqrt (15 / 16) := Real.sqrt_le_sqrt hRR
      _ ≤ 31 / 32 := by
        rw [show (31 : ℝ) / 32 = Real.sqrt ((31 / 32) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num)
  have hT : tvDist (P 0) (P θ) ≤ ENNReal.ofReal (31 / 32) :=
    le_trans hlecam (ENNReal.ofReal_le_ofReal hbound)
  -- conclude `1 − ‖·‖_TV ≥ (1 − 1/√2)/16`
  have hfin : (1 : ℝ≥0∞) - ENNReal.ofReal (31 / 32) ≤ 1 - tvDist (P 0) (P θ) :=
    tsub_le_tsub_left hT 1
  have h132 : (1 : ℝ≥0∞) - ENNReal.ofReal (31 / 32) = ENNReal.ofReal (1 / 32) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ← ENNReal.ofReal_sub _ (by norm_num)]
    norm_num
  have hcmp : ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 16) ≤ ENNReal.ofReal (1 / 32) := by
    apply ENNReal.ofReal_le_ofReal
    have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hs2 : Real.sqrt 2 ≤ 2 := by
      have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ 4 by norm_num)
      rwa [show Real.sqrt 4 = 2 from by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)] at h
    have hinv : (1 : ℝ) / 2 ≤ 1 / Real.sqrt 2 := one_div_le_one_div_of_le h2pos hs2
    linarith
  calc ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 16)
      ≤ ENNReal.ofReal (1 / 32) := hcmp
    _ = (1 : ℝ≥0∞) - ENNReal.ofReal (31 / 32) := h132.symm
    _ ≤ 1 - tvDist (P 0) (P θ) := hfin

/-- **Minimax rate for the uniform location family** (Wainwright Example 15.5): for the `n`-sample
model `P θ = Uniform[θ, θ+1]^{⊗n}`, the minimax risk for estimating `θ` under squared error is at
least `(1 − 1/√2)/128 · n⁻²` — the faster `n⁻²` rate of a non-regular problem.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.5. -/
-- LEAN-ONLY: n ≥ 2 (at n=1 the two shifted unit-uniforms are a.e. disjoint ⇒ TV=1 and the
-- two-point bound is vacuous); Wainwright Ex 15.5 is an n→∞ rate.
theorem uniform_location_minimax_rate (n : ℕ) (hn : 2 ≤ n)
    (P : Kernel ℝ (Fin n → ℝ)) [IsMarkovKernel P]
    -- USER-INPUT: `P θ` is the `n`-fold i.i.d. `Uniform[θ, θ+1]` product; Wainwright §15.2, Ex 15.5.
    (hP : ∀ θ : ℝ, P θ = Measure.pi fun _ : Fin n => volume.restrict (Set.Icc θ (θ + 1))) :
    ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 128 / (n : ℝ) ^ 2)
      ≤ minimaxRiskDist (· ^ 2) id P := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnne : (n : ℝ) ≠ 0 := hn0.ne'
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hB : (0 : ℝ) ≤ (1 - 1 / Real.sqrt 2) / 16 := by
    have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have : 1 / Real.sqrt 2 ≤ 1 := (div_le_one h2pos).mpr hsqrt2
    linarith
  have hθ₁0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have hsep : 2 * ENNReal.ofReal ((n : ℝ)⁻¹ / 2) ≤ edist (0 : ℝ) ((n : ℝ)⁻¹) := by
    rw [edist_dist, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hθ₁0,
        show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply le_of_eq; congr 1; ring
  have hcrux := uniform_two_point_tvDist_bound n hn P hP
  have hΦδ : (fun x : ℝ≥0∞ => x ^ 2) (ENNReal.ofReal ((n : ℝ)⁻¹ / 2))
      = ENNReal.ofReal (((n : ℝ)⁻¹ / 2) ^ 2) := by
    change (ENNReal.ofReal ((n : ℝ)⁻¹ / 2)) ^ 2 = _
    rw [← ENNReal.ofReal_pow (by positivity)]
  refine le_trans ?_ (minimax_two_point (fun x : ℝ≥0∞ => x ^ 2) id P 0
    ((n : ℝ)⁻¹) (ENNReal.ofReal ((n : ℝ)⁻¹ / 2)) hΦ hsep)
  beta_reduce at hΦδ
  rw [hΦδ]
  have h2inv : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  have hcompute : ENNReal.ofReal (((n : ℝ)⁻¹ / 2) ^ 2) / 2 * ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 16)
      = ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 128 / (n : ℝ) ^ 2) := by
    rw [div_eq_mul_inv, h2inv, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  calc ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 128 / (n : ℝ) ^ 2)
      = ENNReal.ofReal (((n : ℝ)⁻¹ / 2) ^ 2) / 2 * ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 16) :=
        hcompute.symm
    _ ≤ ENNReal.ofReal (((n : ℝ)⁻¹ / 2) ^ 2) / 2 * (1 - tvDist (P 0) (P ((n : ℝ)⁻¹))) :=
        mul_le_mul' le_rfl hcrux

end StatLean.Minimaxity
