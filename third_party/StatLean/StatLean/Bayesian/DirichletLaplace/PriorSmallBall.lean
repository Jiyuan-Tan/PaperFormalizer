module
public import StatLean.Bayesian.DirichletLaplace.DensityBounds
public import StatLean.Bayesian.ForMathlib.PiLintegralFintype
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/-!
# Dirichlet–Laplace prior: support-count MGF, Chernoff tail, and small-ball lower bound

The two prior-side probabilistic engines of the compressibility argument, both consequences of the
**product** structure of `dlPrior` (independent, identically distributed coordinates):

* `dlPrior_count_mgf` — the moment generating function of the δ-support size `dlSuppCount δ` under
  the prior factorizes: `∫ c^{|supp_δ(θ)|} dΠ = ((1−ζ) + ζ·c)^{card ι}`, where
  `ζ = ζ(δ) = Π(|θ₁| > δ)` is the per-coordinate exceedance probability.
* `dlPrior_count_ge_le` — the **Chernoff bound** it yields:
  `Π(|supp_δ(θ)| ≥ k) ≤ exp(card ι·z·(c−1) − k·log c)` for any tilt `c > 1` and any upper bound `z`
  on `ζ` (supplied downstream by Lemma 3.3, C3).
* `dlPrior_box_ge`, `dlPrior_ball_zero_ge` — the **small-ball lower bound**: a coordinatewise box
  is contained in the Euclidean ball, so `Π(B(0,r)) ≥ (1 − ζ(s))^{card ι} ≥ exp(−2·card ι·w)` with
  the per-coordinate threshold `s = min(r/√(card ι), 1/2)` (deviation D7) and `w` an upper bound on
  the tail `ζ(s)`.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, J. Amer. Statist. Assoc. 110 (2015), 1479–1490 (arXiv:1401.5398). §6 (the
denominator/support-count analysis); the tensorization identity of eq. (26) is the special case
`c = 1` boundary of the MGF here.

**Proof formalization notes.** `dlPrior_count_mgf` pushes `c^{dlSuppCount}` through the
`WithLp.toLp 2` pushforward (support count is invariant) and factorizes with `lintegral_pi_prod'`
(F4), each factor being `E[c^{1[|θⱼ|>δ]}] = (1−ζ) + ζ·c`. `dlPrior_count_ge_le` is Markov applied to
the tilted variable `c^{dlSuppCount}` followed by `1 + t ≤ eᵗ` and `ζ ≤ z`. `dlPrior_box_ge` is the
box-probability factorization; `dlPrior_ball_zero_ge` uses the inclusion
`{θ | ∀ j, |θⱼ| ≤ s} ⊆ B(0,r)` for `s ≤ r/√(card ι)` and `(1−x)^m ≥ e^{−2xm}` for `x ≤ 1/2`.
*Deviation D7:* the per-coordinate threshold is clamped to `1/2` because `r/√(card ι)` may exceed
`1` when `qₙ log n > n`.

**Bibliographic comments.** Bounding the number of "large" coordinates by a binomial Chernoff tail
is the Bayesian analogue of the frequentist support-recovery counting arguments (Donoho–Johnstone,
*Biometrika* 81 (1994), 425–455); the small-ball / prior-mass condition on Kullback–Leibler
neighborhoods is the Ghosal–Ghosh–van der Vaart (*Ann. Statist.* 28 (2000), 500–531) prior-mass
requirement, here verified for the Dirichlet–Laplace prior.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- Coordinate evaluation on `EuclideanSpace ℝ ι` is measurable. -/
private lemma measurable_eucl_coord (j : ι) :
    Measurable (fun θ : EuclideanSpace ℝ ι => θ j) :=
  (measurable_pi_apply j).comp (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable

/-- `WithLp.toLp 2` as a measurable function (with the plain-function head, for `rw`). -/
private lemma measurable_toLp :
    Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
  (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable

/-- `θ ↦ c ^ dlSuppCount δ θ` is measurable. -/
private lemma measurable_pow_suppCount (c : ℝ≥0∞) (δ : ℝ) :
    Measurable (fun θ : EuclideanSpace ℝ ι => c ^ dlSuppCount δ θ) :=
  (measurable_of_countable (fun n : ℕ => c ^ n)).comp (measurable_dlSuppCount δ)

/-- **Support-count MGF under the product prior.** For any tilt `c`, the moment generating function
of the δ-support size factorizes over coordinates:
`∫ c^{|supp_δ(θ)|} dΠ = ((1−ζ) + ζ·c)^{card ι}`, `ζ = Π(|θ₁| > δ)`. -/
theorem dlPrior_count_mgf {a δ : ℝ} (c : ℝ≥0∞) :
    ∫⁻ θ, c ^ dlSuppCount δ θ ∂(dlPrior a ι)
      = ((1 - dlMarginal a {x : ℝ | δ < |x|}) + dlMarginal a {x : ℝ | δ < |x|} * c)
          ^ Fintype.card ι := by
  set ζ := dlMarginal a {x : ℝ | δ < |x|} with hζ
  have hs : MeasurableSet {x : ℝ | δ < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hif : Measurable (fun y : ℝ => if δ < |y| then c else 1) :=
    Measurable.ite hs measurable_const measurable_const
  rw [dlPrior, lintegral_map (measurable_pow_suppCount c δ)
    measurable_toLp]
  have hpt : ∀ x : ι → ℝ, c ^ dlSuppCount δ (WithLp.toLp 2 x)
      = ∏ j, (if δ < |x j| then c else 1) := by
    intro x
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    congr 1
  simp_rw [hpt]
  rw [lintegral_pi_prod_fintype (dlMarginal a) (fun _ => hif)]
  have hc_s : ∫⁻ y in {x : ℝ | δ < |x|}, (if δ < |y| then c else 1) ∂(dlMarginal a) = c * ζ := by
    rw [setLIntegral_congr_fun hs (g := fun _ => c) (fun y hy => by
      simp only [Set.mem_setOf_eq] at hy; simp [hy]), setLIntegral_const]
  have hc_sc : ∫⁻ y in {x : ℝ | δ < |x|}ᶜ, (if δ < |y| then c else 1) ∂(dlMarginal a) = 1 - ζ := by
    rw [setLIntegral_congr_fun hs.compl (g := fun _ => 1) (fun y hy => by
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy; simp [hy]),
      setLIntegral_const, one_mul, prob_compl_eq_one_sub hs]
  have hfactor : ∫⁻ y, (if δ < |y| then c else 1) ∂(dlMarginal a) = (1 - ζ) + ζ * c := by
    rw [← lintegral_add_compl (fun y => if δ < |y| then c else 1) hs, hc_s, hc_sc, add_comm,
      mul_comm c ζ]
  rw [hfactor, Finset.prod_const, Finset.card_univ]

/-- **Chernoff tail for the δ-support size** (BPPD §6): tilting by `c > 1` and using `1 + t ≤ eᵗ`,
`Π(|supp_δ(θ)| ≥ k) ≤ exp(card ι · z · (c−1) − k · log c)` for any upper bound `z` on the
per-coordinate exceedance probability `ζ(δ)`. -/
theorem dlPrior_count_ge_le {a δ z c : ℝ}
    -- USER-INPUT: admissible tilt `c > 1`; Markov/Chernoff, BPPD §6
    (hc : 1 < c) (k : ℕ)
    -- USER-INPUT: `z` bounds the per-coordinate exceedance prob ζ(δ) (supplied by Lemma 3.3, C3)
    (hz : (dlMarginal a {x : ℝ | δ < |x|}).toReal ≤ z) :
    dlPrior a ι {θ | k ≤ dlSuppCount δ θ}
      ≤ ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ) * z * (c - 1) - (k : ℝ) * Real.log c)) := by
  set ζ := dlMarginal a {x : ℝ | δ < |x|} with hζdef
  set C := ENNReal.ofReal c with hCdef
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hcpos : (0 : ℝ) < c := by linarith
  have hζ1 : ζ ≤ 1 := prob_le_one
  have hζtop : ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hζ1
  have hζr1 : ζ.toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top hζ1
  have hζrn : (0 : ℝ) ≤ ζ.toReal := ENNReal.toReal_nonneg
  have hC1 : (1 : ℝ≥0∞) ≤ C := by
    rw [hCdef, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hc.le
  have hCne0 : C ≠ 0 := by rw [hCdef]; exact (ENNReal.ofReal_pos.mpr hcpos).ne'
  have hCtop : C ≠ ⊤ := ENNReal.ofReal_ne_top
  set M := dlPrior a ι {θ | k ≤ dlSuppCount δ θ} with hMdef
  -- Markov on the tilted variable.
  have hmark := mul_meas_ge_le_lintegral₀ (μ := dlPrior a ι)
    (measurable_pow_suppCount C δ).aemeasurable (C ^ k)
  have hsub : {θ : EuclideanSpace ℝ ι | k ≤ dlSuppCount δ θ}
      ⊆ {θ | C ^ k ≤ C ^ dlSuppCount δ θ} := fun θ hθ => pow_le_pow_right' hC1 hθ
  have step1 : C ^ k * M ≤ ((1 - ζ) + ζ * C) ^ Fintype.card ι := by
    refine (mul_le_mul_right (measure_mono hsub) (C ^ k)).trans ?_
    exact hmark.trans_eq (dlPrior_count_mgf C)
  -- The MGF factor is bounded by `exp(z (c-1))`.
  have hfactoreq : (1 - ζ) + ζ * C = ENNReal.ofReal ((1 - ζ.toReal) + ζ.toReal * c) := by
    have h1sub : (1 : ℝ≥0∞) - ζ = ENNReal.ofReal (1 - ζ.toReal) := by
      rw [ENNReal.ofReal_sub _ hζrn, ENNReal.ofReal_one, ENNReal.ofReal_toReal hζtop]
    have hmul : ζ * C = ENNReal.ofReal (ζ.toReal * c) := by
      rw [hCdef, ← ENNReal.ofReal_toReal hζtop, ← ENNReal.ofReal_mul hζrn,
        ENNReal.ofReal_toReal hζtop]
    rw [h1sub, hmul, ← ENNReal.ofReal_add (by linarith) (by positivity)]
  have hfac : (1 - ζ) + ζ * C ≤ ENNReal.ofReal (Real.exp (z * (c - 1))) := by
    rw [hfactoreq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle1 : (1 - ζ.toReal) + ζ.toReal * c ≤ Real.exp (ζ.toReal * (c - 1)) := by
      have h := Real.add_one_le_exp (ζ.toReal * (c - 1))
      nlinarith [h]
    have hle2 : Real.exp (ζ.toReal * (c - 1)) ≤ Real.exp (z * (c - 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz (by linarith))
    exact hle1.trans hle2
  have hfaccard : ((1 - ζ) + ζ * C) ^ Fintype.card ι
      ≤ ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ) * z * (c - 1))) := by
    refine (pow_le_pow_left' hfac (Fintype.card ι)).trans ?_
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    congr 1; ring
  -- Cancel `C ^ k` and finish.
  have hck_exp : Real.exp ((k : ℝ) * Real.log c) = c ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log hcpos]
  have hCk : C ^ k = ENNReal.ofReal (c ^ k) := by rw [hCdef, ← ENNReal.ofReal_pow hc0]
  have hRHSmul : ENNReal.ofReal
      (Real.exp ((Fintype.card ι : ℝ) * z * (c - 1) - (k : ℝ) * Real.log c)) * C ^ k
      = ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ) * z * (c - 1))) := by
    rw [hCk, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← hck_exp, ← Real.exp_add,
      sub_add_cancel]
  have hstep : M * C ^ k ≤ ENNReal.ofReal
      (Real.exp ((Fintype.card ι : ℝ) * z * (c - 1) - (k : ℝ) * Real.log c)) * C ^ k := by
    rw [hRHSmul, mul_comm M]
    exact step1.trans hfaccard
  exact (ENNReal.mul_le_mul_iff_left (pow_ne_zero k hCne0) (ENNReal.pow_ne_top hCtop)).mp hstep

/-- Box-probability factorization: the prior mass of the coordinatewise box `{θ | ∀ j, |θⱼ| ≤ s}`
is at least the product `Π(|θ₁| ≤ s)^{card ι}` of one-dimensional masses. -/
theorem dlPrior_box_ge {a s : ℝ} :
    (dlMarginal a {x : ℝ | |x| ≤ s}) ^ Fintype.card ι
      ≤ dlPrior a ι {θ | ∀ j, |θ j| ≤ s} := by
  have hB : MeasurableSet {θ : EuclideanSpace ℝ ι | ∀ j, |θ j| ≤ s} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le ((measurable_eucl_coord j).abs) measurable_const
  have hpre : (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) ⁻¹' {θ | ∀ j, |θ j| ≤ s}
      = Set.univ.pi (fun _ => {y : ℝ | |y| ≤ s}) := by
    ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ_pi, PiLp.toLp_apply]
  have hcalc : dlPrior a ι {θ | ∀ j, |θ j| ≤ s}
      = (dlMarginal a {x : ℝ | |x| ≤ s}) ^ Fintype.card ι := by
    rw [dlPrior, Measure.map_apply measurable_toLp hB, hpre,
      Measure.pi_pi, Finset.prod_const, Finset.card_univ]
  exact hcalc.ge

/-- **Small-ball lower bound at the origin** (BPPD §6, deviation D7): with per-coordinate threshold
`s = min(r/√(card ι), 1/2)` and any upper bound `w` on the tail `ζ(s) = Π(|θ₁| > s)`, the prior
charges the ball `B(0,r)` with at least `exp(−2·card ι·w)`. -/
theorem dlPrior_ball_zero_ge {a r w : ℝ}
    -- USER-INPUT: positive radius; BPPD §6
    (hr : 0 < r)
    -- USER-INPUT: `w` bounds the tail at the clamped threshold s = min(r/√m, 1/2); D7
    (hw : (dlMarginal a
        {x : ℝ | min (r / Real.sqrt (Fintype.card ι : ℝ)) (1 / 2) < |x|}).toReal ≤ w)
    -- USER-INPUT: `w ≤ 1/2` unlocks the per-coordinate bound `1 − x ≥ exp(−2x)` (deviation D7;
    -- necessary — the conclusion is false without it, see the counterexample the closure comments).
    (hw2 : w ≤ 1 / 2) :
    ENNReal.ofReal (Real.exp (-2 * (Fintype.card ι : ℝ) * w))
      ≤ dlPrior a ι (Metric.closedBall 0 r) := by
  set m : ℝ := (Fintype.card ι : ℝ) with hm_def
  set s : ℝ := min (r / Real.sqrt m) (1 / 2) with hs_def
  set ζ := dlMarginal a {x : ℝ | s < |x|} with hζ
  have hs_nonneg : 0 ≤ s := le_min (by positivity) (by norm_num)
  -- The coordinatewise box sits inside the Euclidean ball of radius `r`.
  have hbox_sub : {θ : EuclideanSpace ℝ ι | ∀ j, |θ j| ≤ s} ⊆ Metric.closedBall 0 r := by
    intro θ hθ
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsr : Real.sqrt m * s ≤ r := by
      rcases eq_or_lt_of_le (Real.sqrt_nonneg m) with h0 | hpos
      · rw [← h0]; simpa using hr.le
      · calc Real.sqrt m * s ≤ Real.sqrt m * (r / Real.sqrt m) :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) hpos.le
          _ = r := by field_simp
    refine le_trans ?_ hsr
    have hsum : ∑ j, θ j ^ 2 ≤ m * s ^ 2 := by
      calc ∑ j, θ j ^ 2 ≤ ∑ _j : ι, s ^ 2 :=
            Finset.sum_le_sum fun j _ => by nlinarith [hθ j, abs_nonneg (θ j), sq_abs (θ j)]
        _ = m * s ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ‖θ‖ = Real.sqrt (‖θ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (∑ j, θ j ^ 2) := by rw [EuclideanSpace.real_norm_sq_eq]
      _ ≤ Real.sqrt (m * s ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt m * s := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs_nonneg]
  -- The box mass factorizes and dominates `(1 - ζ)^card`.
  have hcompl_eq : (1 : ℝ≥0∞) - ζ = dlMarginal a {x : ℝ | |x| ≤ s} := by
    have hset : {x : ℝ | |x| ≤ s} = {x : ℝ | s < |x|}ᶜ := by ext x; simp [not_lt]
    rw [hset, prob_compl_eq_one_sub (measurableSet_lt measurable_const continuous_abs.measurable)]
  have hbox_mass : (1 - ζ) ^ Fintype.card ι ≤ dlPrior a ι {θ | ∀ j, |θ j| ≤ s} := by
    rw [hcompl_eq]; exact dlPrior_box_ge
  -- Reduce to the scalar bound.
  have hζ1 : ζ ≤ 1 := prob_le_one
  have hζtop : ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hζ1
  have hζr1 : ζ.toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top hζ1
  have hζrn : (0 : ℝ) ≤ ζ.toReal := ENNReal.toReal_nonneg
  have h1subζ : (1 : ℝ≥0∞) - ζ = ENNReal.ofReal (1 - ζ.toReal) := by
    rw [ENNReal.ofReal_sub _ hζrn, ENNReal.ofReal_one, ENNReal.ofReal_toReal hζtop]
  have hreal : ENNReal.ofReal (Real.exp (-2 * m * w))
      ≤ (1 - ζ) ^ Fintype.card ι := by
    rw [h1subζ, ← ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 1 - ζ.toReal)]
    refine ENNReal.ofReal_le_ofReal ?_
    -- Per-coordinate `exp(-2w) ≤ 1/(1+2w) ≤ 1 - ζ.toReal`, using `ζ.toReal ≤ w ≤ 1/2`
    -- (`1/(1+2w) ≤ 1-ζ` reduces to `w(1-2ζ) + (w-ζ) ≥ 0`), then raise to the `card` power.
    have hw0 : (0 : ℝ) ≤ w := le_trans hζrn hw
    have hpos : (0 : ℝ) < 1 + 2 * w := by linarith
    have hE : (1 : ℝ) + 2 * w ≤ Real.exp (2 * w) := by
      have := Real.add_one_le_exp (2 * w); linarith
    have hinv : Real.exp (-2 * w) ≤ 1 / (1 + 2 * w) := by
      rw [show (-2 * w : ℝ) = -(2 * w) from by ring, Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le hpos hE
    have hquad : 1 / (1 + 2 * w) ≤ 1 - ζ.toReal := by
      rw [div_le_iff₀ hpos]
      nlinarith [hw, hw2, hζrn,
        mul_nonneg hw0 (by linarith : (0 : ℝ) ≤ 1 - 2 * ζ.toReal)]
    have hexp : Real.exp (-2 * w) ≤ 1 - ζ.toReal := le_trans hinv hquad
    calc Real.exp (-2 * m * w)
        = Real.exp (-2 * w) ^ (Fintype.card ι) := by
          rw [← Real.exp_nat_mul]; congr 1; rw [hm_def]; push_cast; ring
      _ ≤ (1 - ζ.toReal) ^ (Fintype.card ι) :=
          pow_le_pow_left₀ (Real.exp_nonneg _) hexp _
  exact hreal.trans (hbox_mass.trans (measure_mono hbox_sub))

end StatLean.Bayesian
