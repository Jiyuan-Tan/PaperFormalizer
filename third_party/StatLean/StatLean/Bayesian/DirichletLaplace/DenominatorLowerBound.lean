module
public import StatLean.Bayesian.DirichletLaplace.Defs
public import StatLean.Bayesian.ForMathlib.GaussianShift
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-!
# Denominator lower bound for the Dirichlet–Laplace posterior (C7)

The posterior ratio `dlNumer / dlDenom` is only useful once the denominator `dlDenom θ* π y`
(the marginal likelihood `m(y) = ∫ dN(θ,I)/dN(θ*,I)(y) dΠ(θ)`) is bounded *below* on a set of `y`
of high probability under the truth `θ*`. This is the Castillo–van der Vaart evidence lower bound
(a "prior-mass / Kullback–Leibler neighbourhood" argument).

The two-step estimate:

* **Jensen** (`dlDenom_ge_jensen`). Restricting the integral to the ball `B = B(θ*, r)` and applying
  Jensen's inequality to the convex exponential gives
  `dlDenom θ* π y ≥ Π(B)·exp(⟪aveShift, y − θ*⟫ − r²/2)`,
  where `aveShift = ⨍_{B} (θ − θ*) dΠ` is the average displacement of the prior over the ball
  (`‖aveShift‖ ≤ r`).
* **Gaussian tail** (`measure_dlDenom_lt_le`, the Castillo–van der Vaart Lemma 5.2 analogue). Under
  `y ∼ N(θ*, I)`, the event `{dlDenom < e^{−r²}·Π(B)}` is contained (via the Jensen bound) in
  `{⟪aveShift, y − θ*⟫ < −r²/2}`, whose probability is `≤ exp(−(r²/2)²/(2‖aveShift‖²)) ≤ exp(−r²/8)`
  because `‖aveShift‖ ≤ r`.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, Journal of the American Statistical Association 110 (2015), 1479–1490
(arXiv:1401.5398). §6 (denominator / evidence lower bound). The evidence-lower-bound event is the
analogue of I. Castillo and A. W. van der Vaart, "Needles and straw in a haystack: posterior
concentration for possibly sparse sequences," *Ann. Statist.* 40 (2012), 2069–2101, Lemma 5.2.

**Proof formalization notes.** `aveShift` is a genuine `EuclideanSpace ℝ ι`-valued Bochner set
average `⨍`; its norm bound is `norm_setAverage_le`-style (each `θ − θ*` has norm `≤ r` on the ball).
The Jensen step uses `ConvexOn.map_average_le` with `Real.convexOn_exp` on the normalized restricted
prior `(Π B)⁻¹ • Π.restrict B` (the integrand `⟪θ − θ*, y − θ*⟫ − ‖θ − θ*‖²/2` is bounded on the
ball, so it is integrable). The tail step reduces to the 1-dimensional Gaussian
`stdGaussianShift_inner_ge_le` (from `ForMathlib.GaussianShift`) applied to the direction
`c = aveShift` with variance `‖aveShift‖² ≤ r²`. Edge cases: `Π(B) = 0` collapses the target event
to `∅`; `aveShift = 0` makes the standardized deviation `+∞` and the tail `0`. `[IsProbabilityMeasure
π]` is carried because the intended `π` is the DL prior and finiteness of `Π(B)` is needed for the
Jensen normalization.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Average displacement of the prior over a ball** (BPPD §6, evidence lower bound helper).

`aveShift π θ* r = ⨍_{B(θ*, r)} (θ − θ*) dΠ` is the Bochner set average of the displacement
`θ ↦ θ − θ*` over the closed ball of radius `r`. It is the location around which the log-likelihood
ratio is linearized in the Jensen step.

Edge behaviour: when `Π(B(θ*, r)) = 0` or `= ∞` the set average `⨍` returns `0` (Mathlib's
convention `(μ s).toReal⁻¹ • ∫ = 0`), consistent with the trivial lower bound in that case. -/
noncomputable def aveShift (π : Measure (EuclideanSpace ℝ ι)) (θstar : EuclideanSpace ℝ ι)
    (r : ℝ) : EuclideanSpace ℝ ι :=
  ⨍ θ in Metric.closedBall θstar r, (θ - θstar) ∂π

/-- The average displacement stays inside the ball: `‖aveShift π θ* r‖ ≤ r`. Every point `θ` of the
ball has `‖θ − θ*‖ ≤ r`, and the set average of a norm-bounded function is norm-bounded by the same
constant (degenerate `Π(B) ∈ {0, ∞}` gives `aveShift = 0 ≤ r`). -/
lemma norm_aveShift_le (π : Measure (EuclideanSpace ℝ ι)) (θstar : EuclideanSpace ℝ ι) {r : ℝ}
    -- LEAN-ONLY: radius nonneg, else `closedBall = ∅`, `aveShift = 0` and `0 ≤ r` fails
    (hr : 0 ≤ r) :
    ‖aveShift π θstar r‖ ≤ r := by
  unfold aveShift
  rw [setAverage_eq, norm_smul]
  set s := Metric.closedBall θstar r with hs
  have hbound : ∀ θ ∈ s, ‖θ - θstar‖ ≤ r := by
    intro θ hθ; rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hθ
  rcases eq_or_ne (π s) ∞ with hinf | hfin
  · have h0 : π.real s = 0 := by simp [measureReal_def, hinf]
    rw [h0]; simp only [inv_zero, norm_zero, zero_mul]; exact hr
  · have hle : ‖∫ θ in s, (θ - θstar) ∂π‖ ≤ r * π.real s :=
      norm_setIntegral_le_of_norm_le_const hfin.lt_top hbound
    rcases eq_or_ne (π.real s) 0 with h0 | h0
    · rw [h0]; simp only [inv_zero, norm_zero, zero_mul]; exact hr
    · rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg)]
      calc (π.real s)⁻¹ * ‖∫ θ in s, (θ - θstar) ∂π‖
          ≤ (π.real s)⁻¹ * (r * π.real s) :=
            mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr measureReal_nonneg)
        _ = r := by field_simp

/-- **Jensen evidence lower bound** (BPPD §6).

Restricting `dlDenom` to the ball `B(θ*, r)` and applying Jensen to the exponential yields

  `Π(B(θ*, r))·exp(⟪aveShift π θ* r, y − θ*⟫ − r²/2) ≤ dlDenom θ* π y`.

The linear term `⟪aveShift, y − θ*⟫` is the average of `⟪θ − θ*, y − θ*⟫` over the ball; the
quadratic penalty `r²/2` bounds the average of `‖θ − θ*‖²/2 ≤ r²/2`. -/
lemma dlDenom_ge_jensen (π : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure π]
    (θstar y : EuclideanSpace ℝ ι) {r : ℝ}
    -- USER-INPUT: 0 < r (ball radius positive; CvdV Lem 5.2 setup); BPPD §6
    (hr : 0 < r) :
    π (Metric.closedBall θstar r)
        * ENNReal.ofReal (Real.exp (⟪aveShift π θstar r, y - θstar⟫ - r ^ 2 / 2))
      ≤ dlDenom θstar π y := by
  classical
  set B := Metric.closedBall θstar r with hB
  set w := y - θstar with hw
  set gx : EuclideanSpace ℝ ι → ℝ :=
    fun θ => ⟪θ - θstar, w⟫ - ‖θ - θstar‖ ^ 2 / 2 with hgx
  have hmB : MeasurableSet B := measurableSet_closedBall
  have hLR : ∀ θ : EuclideanSpace ℝ ι, dlLR θstar θ y = ENNReal.ofReal (Real.exp (gx θ)) :=
    fun θ => rfl
  -- reduce to the ball
  refine le_trans ?_ (dlNumer_le_dlDenom θstar π B y)
  rw [dlNumer]
  -- edge case: prior gives zero mass to the ball
  rcases eq_or_ne (π B) 0 with hB0 | hB0
  · rw [hB0, zero_mul]; exact zero_le
  have hBtop : π B ≠ ∞ := measure_ne_top π B
  have hm_pos : 0 < π.real B := ENNReal.toReal_pos hB0 hBtop
  -- continuity of the ingredients
  have hcont_disp : Continuous (fun θ : EuclideanSpace ℝ ι => θ - θstar) := by fun_prop
  have hcont_f1 : Continuous (fun θ : EuclideanSpace ℝ ι => (⟪θ - θstar, w⟫ : ℝ)) :=
    hcont_disp.inner continuous_const
  have hcont_f2 : Continuous (fun θ : EuclideanSpace ℝ ι => ‖θ - θstar‖ ^ 2 / 2) :=
    (hcont_disp.norm.pow 2).div_const 2
  have hcont_gx : Continuous gx := by rw [hgx]; exact hcont_f1.sub hcont_f2
  have hcont_exp : Continuous (fun θ => Real.exp (gx θ)) := Real.continuous_exp.comp hcont_gx
  -- pointwise bounds on the ball
  have hbound_disp : ∀ᵐ θ ∂π.restrict B, ‖θ - θstar‖ ≤ r :=
    (ae_restrict_mem hmB).mono fun θ hθ => by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hθ
  have hbound_f1 : ∀ᵐ θ ∂π.restrict B, ‖(⟪θ - θstar, w⟫ : ℝ)‖ ≤ r * ‖w‖ :=
    (ae_restrict_mem hmB).mono fun θ hθ => by
      have hd : ‖θ - θstar‖ ≤ r := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hθ
      calc ‖(⟪θ - θstar, w⟫ : ℝ)‖ = |⟪θ - θstar, w⟫| := Real.norm_eq_abs _
        _ ≤ ‖θ - θstar‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ ≤ r * ‖w‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
  have hbound_f2 : ∀ᵐ θ ∂π.restrict B, ‖‖θ - θstar‖ ^ 2 / 2‖ ≤ r ^ 2 / 2 :=
    (ae_restrict_mem hmB).mono fun θ hθ => by
      have hd : ‖θ - θstar‖ ≤ r := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (θ - θstar), hd]
  have hbound_exp : ∀ᵐ θ ∂π.restrict B, ‖Real.exp (gx θ)‖ ≤ Real.exp (r * ‖w‖) :=
    (ae_restrict_mem hmB).mono fun θ hθ => by
      have hd : ‖θ - θstar‖ ≤ r := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      have hf1le : (⟪θ - θstar, w⟫ : ℝ) ≤ r * ‖w‖ :=
        (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
      simp only [hgx]
      nlinarith [norm_nonneg (θ - θstar), hf1le]
  -- integrability on the ball (all functions are bounded there)
  have hdisp_intble : IntegrableOn (fun θ : EuclideanSpace ℝ ι => θ - θstar) B π :=
    IntegrableOn.of_bound hBtop.lt_top hcont_disp.aestronglyMeasurable r hbound_disp
  have hf1_intble : IntegrableOn (fun θ : EuclideanSpace ℝ ι => (⟪θ - θstar, w⟫ : ℝ)) B π :=
    IntegrableOn.of_bound hBtop.lt_top hcont_f1.aestronglyMeasurable (r * ‖w‖) hbound_f1
  have hf2_intble : IntegrableOn (fun θ : EuclideanSpace ℝ ι => ‖θ - θstar‖ ^ 2 / 2) B π :=
    IntegrableOn.of_bound hBtop.lt_top hcont_f2.aestronglyMeasurable (r ^ 2 / 2) hbound_f2
  have hgx_int : IntegrableOn gx B π := by rw [hgx]; exact hf1_intble.sub hf2_intble
  have hexp_int : IntegrableOn (fun θ => Real.exp (gx θ)) B π :=
    IntegrableOn.of_bound hBtop.lt_top hcont_exp.aestronglyMeasurable
      (Real.exp (r * ‖w‖)) hbound_exp
  have hnn : 0 ≤ᵐ[π.restrict B] fun θ => Real.exp (gx θ) :=
    Filter.Eventually.of_forall fun θ => (Real.exp_pos _).le
  -- the linear term of the average equals `π.real B • ⟪aveShift, w⟫`
  have hf1_int : ∫ θ in B, (⟪θ - θstar, w⟫ : ℝ) ∂π = π.real B * ⟪aveShift π θstar r, w⟫ := by
    have hcomm : ∫ θ in B, (⟪θ - θstar, w⟫ : ℝ) ∂π = ∫ θ in B, (⟪w, θ - θstar⟫ : ℝ) ∂π :=
      integral_congr_ae (Filter.Eventually.of_forall fun θ => real_inner_comm w (θ - θstar))
    have hdint : ∫ θ in B, (θ - θstar) ∂π = π.real B • aveShift π θstar r :=
      (measure_smul_setAverage (fun θ => θ - θstar) hBtop).symm
    rw [hcomm, integral_inner hdisp_intble w, hdint, real_inner_smul_right,
      real_inner_comm w (aveShift π θstar r)]
  -- the quadratic term is bounded by `π.real B * (r²/2)`
  have hf2_le : ∫ θ in B, ‖θ - θstar‖ ^ 2 / 2 ∂π ≤ π.real B * (r ^ 2 / 2) := by
    calc ∫ θ in B, ‖θ - θstar‖ ^ 2 / 2 ∂π
        ≤ ∫ _ in B, r ^ 2 / 2 ∂π := by
          refine setIntegral_mono_on hf2_intble (integrable_const _).integrableOn hmB ?_
          intro θ hθ
          have hd : ‖θ - θstar‖ ≤ r := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hθ
          nlinarith [norm_nonneg (θ - θstar), hd]
      _ = π.real B • (r ^ 2 / 2) := setIntegral_const _
      _ = π.real B * (r ^ 2 / 2) := by rw [smul_eq_mul]
  -- rewrite the restricted lintegral through Jensen's set-average identity
  have hkey : (∫⁻ θ in B, dlLR θstar θ y ∂π)
      = ENNReal.ofReal (⨍ θ in B, Real.exp (gx θ) ∂π) * π B := by
    have h := ofReal_setAverage (μ := π) (f := fun θ => Real.exp (gx θ)) hexp_int hnn
    rw [h, ENNReal.div_mul_cancel hB0 hBtop]
    simp_rw [hLR]
  rw [hkey, mul_comm (ENNReal.ofReal (⨍ θ in B, Real.exp (gx θ) ∂π)) (π B)]
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  -- `A ≤ ⨍_B gx`, then Jensen `exp(⨍_B gx) ≤ ⨍_B exp gx`
  have hA : ⟪aveShift π θstar r, w⟫ - r ^ 2 / 2 ≤ ⨍ θ in B, gx θ ∂π := by
    rw [setAverage_eq, smul_eq_mul, le_inv_mul_iff₀ hm_pos]
    have hgxsplit : ∫ θ in B, gx θ ∂π
        = ∫ θ in B, (⟪θ - θstar, w⟫ : ℝ) ∂π - ∫ θ in B, ‖θ - θstar‖ ^ 2 / 2 ∂π :=
      integral_sub hf1_intble hf2_intble
    rw [hgxsplit, hf1_int, mul_sub]
    linarith [hf2_le]
  have hjensen : Real.exp (⨍ θ in B, gx θ ∂π) ≤ ⨍ θ in B, Real.exp (gx θ) ∂π :=
    ConvexOn.map_set_average_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
      hB0 hBtop (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hgx_int hexp_int
  exact (Real.exp_le_exp.mpr hA).trans hjensen

/-- **Castillo–van der Vaart Lemma 5.2 analogue: the denominator is not too small** (BPPD §6).

Under the true model `y ∼ N(θ*, I)` (the measure `gaussShiftKernel ι θ*`), the probability that the
marginal likelihood `dlDenom θ* π y` falls below `e^{−r²}·Π(B(θ*, r))` is at most `e^{−r²/8}`.

Combining the Jensen bound `dlDenom ≥ Π(B)·exp(⟪aveShift, y − θ*⟫ − r²/2)` with the target event
gives the inclusion `{dlDenom < e^{−r²}Π(B)} ⊆ {⟪aveShift, y − θ*⟫ < −r²/2}` (when `Π(B) > 0`; the
event is empty otherwise), and the 1-dimensional Gaussian tail with variance `‖aveShift‖² ≤ r²`
gives `exp(−(r²/2)²/(2r²)) = exp(−r²/8)`. -/
lemma measure_dlDenom_lt_le (π : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure π]
    (θstar : EuclideanSpace ℝ ι) {r : ℝ}
    -- USER-INPUT: 0 < r (ball radius positive; CvdV Lem 5.2 setup); BPPD §6
    (hr : 0 < r) :
    (gaussShiftKernel ι θstar)
        {y | dlDenom θstar π y
          < ENNReal.ofReal (Real.exp (-(r ^ 2))) * π (Metric.closedBall θstar r)}
      ≤ ENNReal.ofReal (Real.exp (-(r ^ 2 / 8))) := by
  classical
  set B := Metric.closedBall θstar r with hB
  set c := aveShift π θstar r with hc
  have hnorm : ‖c‖ ≤ r := norm_aveShift_le π θstar hr.le
  set E := {y : EuclideanSpace ℝ ι | dlDenom θstar π y
      < ENNReal.ofReal (Real.exp (-(r ^ 2))) * π B} with hE
  -- edge case: prior gives zero mass to the ball ⟹ the event is empty
  rcases eq_or_ne (π B) 0 with hB0 | hB0
  · have hEmp : E = ∅ := by
      ext y
      simp only [hE, hB0, mul_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact zero_le
    rw [hEmp, measure_empty]; exact zero_le
  have hBtop : π B ≠ ∞ := measure_ne_top π B
  -- Jensen ⟹ the event sits inside a Gaussian half-space
  set H := {y : EuclideanSpace ℝ ι | r ^ 2 / 2 ≤ ⟪-c, y - θstar⟫} with hH
  have hsub : E ⊆ H := by
    intro y hy
    simp only [hE, Set.mem_setOf_eq] at hy
    have hjen := dlDenom_ge_jensen π θstar y hr
    have hlt : π B * ENNReal.ofReal (Real.exp (⟪c, y - θstar⟫ - r ^ 2 / 2))
        < ENNReal.ofReal (Real.exp (-(r ^ 2))) * π B := lt_of_le_of_lt hjen hy
    rw [mul_comm (ENNReal.ofReal (Real.exp (-(r ^ 2)))) (π B)] at hlt
    have hlt2 := (ENNReal.mul_lt_mul_iff_right hB0 hBtop).mp hlt
    rw [ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)] at hlt2
    have hlt3 := Real.exp_lt_exp.mp hlt2
    simp only [hH, Set.mem_setOf_eq, inner_neg_left]
    linarith
  -- degenerate direction: the half-space is empty (`r²/2 ≤ 0` is false)
  rcases eq_or_ne c 0 with hc0 | hc0
  · have hrp : (0 : ℝ) < r ^ 2 / 2 := by have := pow_pos hr 2; linarith
    have hHempty : H = ∅ := by
      ext y
      simp only [hH, hc0, neg_zero, inner_zero_left, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_le]
      linarith
    calc (gaussShiftKernel ι θstar) E
        ≤ (gaussShiftKernel ι θstar) H := measure_mono hsub
      _ = 0 := by rw [hHempty, measure_empty]
      _ ≤ _ := zero_le
  · -- genuine Gaussian tail: variance `‖c‖² ≤ r²`
    have hcsq : ‖c‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg c, hnorm]
    have hcsq_pos : 0 < ‖c‖ ^ 2 := by positivity
    have harg : r ^ 2 / 8 ≤ (r ^ 2 / 2) ^ 2 / (2 * ‖c‖ ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [hcsq, pow_pos hr 2]
    have harg2 : -((r ^ 2 / 2) ^ 2) / (2 * ‖c‖ ^ 2) ≤ -(r ^ 2 / 8) := by
      rw [neg_div]; exact neg_le_neg harg
    calc (gaussShiftKernel ι θstar) E
        ≤ (gaussShiftKernel ι θstar) H := measure_mono hsub
      _ = ((stdGaussian (EuclideanSpace ℝ ι)).map (· + θstar)) H := by
          rw [gaussShiftKernel_apply]
      _ ≤ ENNReal.ofReal (Real.exp (-((r ^ 2 / 2) ^ 2) / (2 * ‖-c‖ ^ 2))) :=
          stdGaussianShift_inner_ge_le θstar (-c) (r ^ 2 / 2) (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp (-(r ^ 2 / 8))) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          rw [norm_neg]
          exact harg2

end StatLean.Bayesian
