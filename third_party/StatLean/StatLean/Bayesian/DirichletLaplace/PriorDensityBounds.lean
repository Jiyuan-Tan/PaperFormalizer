module
public import StatLean.Bayesian.DirichletLaplace.DensityBounds
public import StatLean.Bayesian.ForMathlib.PiLintegralFintype
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# Dirichlet–Laplace joint prior density and its two-sided bounds (Lemma 3.2)

This file lifts the univariate marginal density bounds of `DirichletLaplace.DensityBounds`
(P3/P4/P5) to the **joint** `ι`-fold product density of the Dirichlet–Laplace prior, and packages
them as measure-vs-Lebesgue comparisons. These are the density inputs to Lemma 6.1 (`C14`).

Contents:
* `dlPrior_eq_withDensity` — the DL prior is Lebesgue with the product density
  `θ ↦ ∏ⱼ dlDensity a (θⱼ)` (BPPD eq. (10) joint form; via `pi_withDensity'` + the volume-preserving
  `WithLp.toLp`).
* `prod_dlDensity_le` — **Lemma 3.2 (13)**: on the coordinates of a support set `S` the product
  density is `≤ (17·a·δ^{a−1})^{|S|}`.
* `sum_sqrt_abs_le` — the two-step Cauchy–Schwarz bound `∑ⱼ √|θⱼ| ≤ (card ι)^{3/4}‖θ‖^{1/2}` that
  converts the coordinate-wise `√|·|` exponent of the lower bound into a norm.
* `prod_dlDensity_ge` — **Lemma 3.2 (14)**: the uniform log-form lower bound
  `∏ⱼ dlDensity a (θⱼ) ≥ (a/64)^{card ι}·exp(−3·card ι − (7/2)∑ⱼ√|θⱼ|)`.
* `dlPrior_le_of_subset`, `dlPrior_ball_ge_volume` — set-vs-volume comparisons in both directions,
  obtained from the `withDensity` representation.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, J. Amer. Statist. Assoc. 110 (2015), 1479–1490 (arXiv:1401.5398). Prior (10),
Lemma 3.2, eqs. (13)–(14).

**Proof formalization notes.** `dlPrior_eq_withDensity` unfolds `dlPrior` (a `Measure.pi`-of-marginals
pushed through `WithLp.toLp 2`), rewrites each marginal by `dlMarginal_eq_withDensity` (C2), applies
`pi_withDensity'` (F4, the `Fintype ι` upgrade of `pi_withDensity`), and transports across the
volume-preserving `WithLp.toLp 2` (`PiLp.volume_preserving_toLp`). The product bounds are `Finset`
products of the univariate C3 bounds; `prod_dlDensity_ge` combines the per-coordinate uniform
log-form P4 with `Real.exp_sum`. The Lebesgue comparisons are `withDensity_apply` +
`setLIntegral_mono`/`setLIntegral_le`.
*Deviations (see the milestone plan).* D5: the mixture-restriction lower bound has exponent
`−(7/2)√|x|` (not the paper's sketched `−2√|x|`), which is why `prod_dlDensity_ge` carries the
`7/2` factor. D8: the density **upper** bound (and hence `prod_dlDensity_le`) genuinely needs
`a ≤ 1/2` (the `Γ(1−a)` blow-up), whereas the lower bound needs only `a ≤ 1`.

**Bibliographic comments.** The product structure of the DL prior density is what reduces the
`n`-dimensional prior-mass estimates to `n` independent univariate calculations; the `√|·|`
tails are the signature of the Laplace-scale mixture and are the mechanism behind the prior's
near-minimax concentration (Bhattacharya–Pati–Pillai–Dunson 2015; cf. the Gaussian-scale-mixture
program of Polson–Scott, "Shrink globally, act locally," *Bayesian Statistics 9*, 2011).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- Coordinate evaluation on `EuclideanSpace ℝ ι` is measurable. -/
private lemma measurable_eucl_coord (j : ι) :
    Measurable (fun θ : EuclideanSpace ℝ ι => θ j) :=
  (measurable_pi_apply j).comp (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable

/-- The joint density `θ ↦ ∏ⱼ dlDensity a (θⱼ)` is measurable. -/
private lemma measurable_prod_dlDensity (a : ℝ) :
    Measurable (fun θ : EuclideanSpace ℝ ι => ∏ j, dlDensity a (θ j)) :=
  Finset.measurable_prod _ fun j _ => measurable_dlDensity.comp (measurable_eucl_coord j)

/-- `withDensity` transports along a measurable embedding: for `f` an embedding and `g` a density,
`(μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g`. -/
private lemma measurableEmbedding_withDensity_map {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure α)
    {g : β → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity (fun x => g (f x))).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [hf.map_apply, withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hf.measurable]

/-- **Product-density representation of the DL prior** (BPPD eq. (10), joint form): for `0 < a`,
`dlPrior a ι` is Lebesgue measure on `EuclideanSpace ℝ ι` weighted by the product density
`θ ↦ ∏ⱼ dlDensity a (θⱼ)`. -/
theorem dlPrior_eq_withDensity {a : ℝ}
    -- USER-INPUT: prior scale positive so the marginal is the Laplace–Gamma mixture; BPPD (10)
    (ha : 0 < a) :
    dlPrior a ι
      = (volume : Measure (EuclideanSpace ℝ ι)).withDensity (fun θ => ∏ j, dlDensity a (θ j)) := by
  haveI hsf : SigmaFinite ((volume : Measure ℝ).withDensity (dlDensity a)) := by
    rw [← dlMarginal_eq_withDensity ha]; infer_instance
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
  have hg : Measurable (fun θ : EuclideanSpace ℝ ι => ∏ j, dlDensity a (θ j)) :=
    measurable_prod_dlDensity a
  -- Rewrite the pi-of-marginals as a withDensity of the product density.
  have hpi : (Measure.pi fun _ : ι => dlMarginal a)
      = (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity
          (fun x => ∏ i, dlDensity a (x i)) := by
    rw [show (fun _ : ι => dlMarginal a)
        = (fun _ : ι => (volume : Measure ℝ).withDensity (dlDensity a)) from
        funext fun _ => dlMarginal_eq_withDensity ha]
    exact pi_withDensity_fintype volume (fun _ => measurable_dlDensity)
  rw [dlPrior, hpi, show (Measure.pi fun _ : ι => (volume : Measure ℝ))
      = (volume : Measure (ι → ℝ)) from MeasureTheory.volume_pi.symm]
  have hmap := measurableEmbedding_withDensity_map hemb (volume : Measure (ι → ℝ)) hg
  rw [(PiLp.volume_preserving_toLp ι).map_eq] at hmap
  exact hmap

/-- **Lemma 3.2 (13)** (BPPD): on a support set `S` all of whose coordinates exceed the resolution
`δ`, the product of the coordinate DL densities is at most `(17·a·δ^{a−1})^{|S|}`. Needs `a ≤ 1/2`
(deviation D8) and `δ ∈ (0,1]`. -/
theorem prod_dlDensity_le {a δ : ℝ}
    -- USER-INPUT: prior scale in the admissible range for the density upper bound; BPPD Lem 3.2, D8
    (ha : 0 < a) (ha' : a ≤ 1 / 2)
    -- USER-INPUT: resolution in the Lemma 3.3 window (0,1]; BPPD Lem 3.2/3.3
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {S : Finset ι} {θ : EuclideanSpace ℝ ι}
    -- USER-INPUT: `S` indexes coordinates above the resolution; BPPD Lem 3.2
    (hθ : ∀ j ∈ S, δ < |θ j|) :
    ∏ j ∈ S, dlDensity a (θ j) ≤ ENNReal.ofReal ((17 * a * δ ^ (a - 1)) ^ S.card) := by
  have hCnn : (0 : ℝ) ≤ 17 * a * δ ^ (a - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) ha.le) (Real.rpow_pos_of_pos hδ _).le
  calc ∏ j ∈ S, dlDensity a (θ j)
      ≤ ∏ _j ∈ S, ENNReal.ofReal (17 * a * δ ^ (a - 1)) :=
        Finset.prod_le_prod' fun j hj => dlDensity_le ha ha' hδ hδ1 (hθ j hj).le
    _ = (ENNReal.ofReal (17 * a * δ ^ (a - 1))) ^ S.card := by rw [Finset.prod_const]
    _ = ENNReal.ofReal ((17 * a * δ ^ (a - 1)) ^ S.card) := (ENNReal.ofReal_pow hCnn _).symm

/-- Two-step Cauchy–Schwarz bound converting the coordinate-wise `√|·|` sum of the lower bound into
a norm: `∑ⱼ √|θⱼ| ≤ (card ι)^{3/4}·‖θ‖^{1/2}`. -/
theorem sum_sqrt_abs_le (θ : EuclideanSpace ℝ ι) :
    ∑ j, Real.sqrt |θ j| ≤ (Fintype.card ι : ℝ) ^ (3 / 4 : ℝ) * ‖θ‖ ^ (1 / 2 : ℝ) := by
  set m : ℝ := (Fintype.card ι : ℝ) with hm_def
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hnn : 0 ≤ ∑ j, Real.sqrt |θ j| := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  -- Step A: (∑ √|θⱼ|)² ≤ m · ∑ |θⱼ|
  have stepA : (∑ j, Real.sqrt |θ j|) ^ 2 ≤ m * ∑ j, |θ j| := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
      (f := fun j => Real.sqrt |θ j|)
    simp only [Real.sq_sqrt (abs_nonneg _), Finset.card_univ] at h
    exact h
  -- Step B: ∑ |θⱼ| ≤ √m · ‖θ‖
  have stepB : ∑ j, |θ j| ≤ Real.sqrt m * ‖θ‖ := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun j => |θ j|)
    rw [Finset.card_univ] at h
    have hnorm : ∑ j, |θ j| ^ 2 = ‖θ‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_congr rfl fun j _ => sq_abs _
    rw [hnorm] at h
    have hrhs : m * ‖θ‖ ^ 2 = (Real.sqrt m * ‖θ‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hm]
    rw [hrhs] at h
    have hsnn : 0 ≤ ∑ j, |θ j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq hsnn,
      Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))] at this
  -- Algebraic identities relating the rpow-target to the √-form.
  have hmm : m ^ (3 / 2 : ℝ) = m * Real.sqrt m := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hm (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hR : (m ^ (3 / 4 : ℝ) * ‖θ‖ ^ (1 / 2 : ℝ)) ^ 2 = m ^ (3 / 2 : ℝ) * ‖θ‖ := by
    rw [mul_pow, ← Real.rpow_natCast (m ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hm,
      ← Real.rpow_natCast (‖θ‖ ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  -- Combine into a squared bound and take square roots.
  have key : (∑ j, Real.sqrt |θ j|) ^ 2 ≤ (m ^ (3 / 4 : ℝ) * ‖θ‖ ^ (1 / 2 : ℝ)) ^ 2 := by
    refine stepA.trans ((mul_le_mul_of_nonneg_left stepB hm).trans (le_of_eq ?_))
    rw [hR, hmm, ← mul_assoc]
  have hrhs_nn : 0 ≤ m ^ (3 / 4 : ℝ) * ‖θ‖ ^ (1 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hm _) (Real.rpow_nonneg (norm_nonneg _) _)
  have := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hrhs_nn] at this

/-- **Lemma 3.2 (14)** (BPPD), uniform log-form (deviation D5): the joint DL density is bounded
below by `(a/64)^{card ι}·exp(−3·card ι − (7/2)∑ⱼ√|θⱼ|)`. Needs only `a ≤ 1`. -/
theorem prod_dlDensity_ge {a : ℝ}
    -- USER-INPUT: prior scale in the admissible range for the density lower bound; BPPD Lem 3.2
    (ha : 0 < a) (ha' : a ≤ 1) (θ : EuclideanSpace ℝ ι) :
    ENNReal.ofReal ((a / 64) ^ Fintype.card ι *
        Real.exp (-3 * (Fintype.card ι : ℝ) - (7 / 2) * (∑ j, Real.sqrt |θ j|)))
      ≤ ∏ j, dlDensity a (θ j) := by
  refine le_trans (le_of_eq ?_)
    (Finset.prod_le_prod' fun j _ => dlDensity_ge ha ha' (θ j))
  rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => by positivity]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 1
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum,
    nsmul_eq_mul]
  ring

/-- Upper set-vs-volume comparison: on a measurable region `C` where the joint density is uniformly
`≤ c`, the DL prior charges `C` with at most `c ·` its Lebesgue volume. -/
theorem dlPrior_le_of_subset {a : ℝ}
    -- USER-INPUT: prior scale positive; BPPD (10)
    (ha : 0 < a) {C : Set (EuclideanSpace ℝ ι)}
    -- LEAN-ONLY: target region measurable (regularity)
    (hC : MeasurableSet C) {c : ℝ≥0∞}
    -- USER-INPUT: uniform density upper bound on `C`; instantiated from Lemma 3.2 (13)
    (hc : ∀ θ ∈ C, ∏ j, dlDensity a (θ j) ≤ c) :
    dlPrior a ι C ≤ c * volume C := by
  rw [dlPrior_eq_withDensity ha, withDensity_apply _ hC, ← setLIntegral_const C c]
  exact setLIntegral_mono measurable_const hc

/-- Lower set-vs-volume comparison on a ball: where the joint density is uniformly `≥ c` over a
closed ball, the DL prior charges the ball with at least `c ·` its Lebesgue volume. -/
theorem dlPrior_ball_ge_volume {a : ℝ}
    -- USER-INPUT: prior scale positive; BPPD (10)
    (ha : 0 < a) (θ₀ : EuclideanSpace ℝ ι) (r : ℝ) {c : ℝ≥0∞}
    -- USER-INPUT: uniform density lower bound on the ball; instantiated from Lemma 3.2 (14)
    (hc : ∀ θ ∈ Metric.closedBall θ₀ r, c ≤ ∏ j, dlDensity a (θ j)) :
    c * volume (Metric.closedBall θ₀ r) ≤ dlPrior a ι (Metric.closedBall θ₀ r) := by
  rw [dlPrior_eq_withDensity ha, withDensity_apply _ measurableSet_closedBall,
    ← setLIntegral_const (Metric.closedBall θ₀ r) c]
  exact setLIntegral_mono (measurable_prod_dlDensity a) hc

end StatLean.Bayesian
