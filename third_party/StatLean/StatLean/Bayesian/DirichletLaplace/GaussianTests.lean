module
public import StatLean.Bayesian.DirichletLaplace.Defs
public import StatLean.Bayesian.ForMathlib.GaussianShift

@[expose] public section

/-!
# Gaussian midpoint tests for the Dirichlet–Laplace posterior (C8)

The consistency argument for the DL posterior (BPPD §6) tests the true parameter `θ₀` against a
net point `φ` using a single linear statistic of the data `y ∼ N(θ, I)`. This file builds that
test and bounds its two error probabilities.

Writing `d = ‖φ − θ₀‖` for the separation between the null and the net point, the test rejects on

  `dlTestSet θ₀ φ ρ = {y | d·(d − ρ)/2 ≤ ⟪y − θ₀, φ − θ₀⟫}`,

a closed half-space with normal direction `φ − θ₀`. Under the null `y ∼ N(θ₀, I)` the statistic
`⟪y − θ₀, φ − θ₀⟫` is centered Gaussian with variance `d²`, so the Type I error is
`≤ exp(−(d − ρ)²/8)`; under any alternative `y ∼ N(θ, I)` with `‖θ − φ‖ ≤ ρ` the statistic has mean
`≥ d(d − ρ)`, so the Type II error `μ(dlTestSetᶜ)` is bounded by the same quantity.

**Deviation D4 (two-parameter midpoint test).** The paper's single-radius `jr`-net makes the test
degenerate (a net point can coincide with `θ₀`) and the na\"ive `d/3`-margin test is inconsistent
with the covering geometry. We instead use the **two-parameter midpoint test** above (threshold
`d(d − ρ)/2` rather than `d²/2`), which keeps a symmetric margin `d(d − ρ)/2` on both sides and
yields the matched bound `exp(−(d − ρ)²/8)` for both error types. Downstream (`ShellDecomposition`),
`jr/4`-nets give `d − ρ ≥ (7/8)jr`, converting this into `exp(−j²r²/12)`. This replaces the paper's
`2√β` Neyman–Pearson bound by the non-optimized `(1 + β)` bookkeeping (same order, no NP machinery).

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, Journal of the American Statistical Association 110 (2015), 1479–1490
(arXiv:1401.5398). §6 (tests for the sieve / net points); deviation D4 (two-parameter midpoint
test).

**Proof formalization notes.** The two tail bounds both reduce, via the 1-dimensional
inner-product pushforward `stdGaussian_map_inner : (stdGaussian E).map (⟪c, ·⟫) = gaussianReal 0 ‖c‖₊²`
and the Gaussian tail `stdGaussianShift_inner_ge_le` from `ForMathlib.GaussianShift`, to the scalar
Gaussian tail `P(N(0, d²) ≥ t) ≤ exp(−t²/(2d²))` at `t = d(d − ρ)/2`, giving `exp(−(d − ρ)²/8)`.
For the Type II bound the mean shift `⟪θ − θ₀, φ − θ₀⟫ = ⟪θ − φ, φ − θ₀⟫ + d² ≥ d(d − ρ)` (from
`‖θ − φ‖ ≤ ρ` and Cauchy–Schwarz) is subtracted first.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Two-parameter midpoint test acceptance region** (BPPD §6, deviation D4).

With `d = ‖φ − θ₀‖` the separation between the null `θ₀` and the net point `φ`, the test rejects
`θ₀` in favour of `φ` on the closed half-space

  `{y | d·(d − ρ)/2 ≤ ⟪y − θ₀, φ − θ₀⟫}`.

The margin parameter `ρ` is the radius of the alternative ball around `φ`; the midpoint threshold
`d(d − ρ)/2` sits halfway between the null mean `0` and the least alternative mean `d(d − ρ)` of the
statistic `⟪y − θ₀, φ − θ₀⟫`.

Edge behaviour: for `ρ ≥ d` the threshold is `≤ 0`, the test degenerates, and the error bounds
below are vacuous — those cases are excluded by the hypothesis `ρ < ‖φ − θ₀‖`. -/
noncomputable def dlTestSet (θ₀ φ : EuclideanSpace ℝ ι) (ρ : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {y | ‖φ - θ₀‖ * (‖φ - θ₀‖ - ρ) / 2 ≤ ⟪y - θ₀, φ - θ₀⟫}

/-- The test acceptance region is a measurable (closed half-space): `y ↦ ⟪y − θ₀, φ − θ₀⟫` is
continuous, hence measurable, and `dlTestSet` is the preimage of `Ici _`. -/
lemma measurableSet_dlTestSet (θ₀ φ : EuclideanSpace ℝ ι) (ρ : ℝ) :
    MeasurableSet (dlTestSet θ₀ φ ρ) := by
  unfold dlTestSet
  apply measurableSet_le measurable_const
  fun_prop

/-- **Type I error bound** (BPPD §6, deviation D4).

Under the null `y ∼ N(θ₀, I)`, the probability of (wrongly) rejecting `θ₀` is
`≤ exp(−(‖φ − θ₀‖ − ρ)²/8)`. The statistic `⟪y − θ₀, φ − θ₀⟫` is `N(0, ‖φ − θ₀‖²)`, and the
threshold `‖φ − θ₀‖·(‖φ − θ₀‖ − ρ)/2` gives the standardized deviation `(‖φ − θ₀‖ − ρ)/2`. -/
lemma measure_dlTestSet_le (θ₀ φ : EuclideanSpace ℝ ι) {ρ : ℝ}
    -- USER-INPUT: 0 ≤ ρ (net radius nonneg); BPPD §6 / D4
    (hρ0 : 0 ≤ ρ)
    -- USER-INPUT: ρ < ‖φ − θ₀‖ (net point strictly separated from null; positive margin); BPPD §6 / D4
    (hρd : ρ < ‖φ - θ₀‖) :
    (gaussShiftKernel ι θ₀) (dlTestSet θ₀ φ ρ)
      ≤ ENNReal.ofReal (Real.exp (-((‖φ - θ₀‖ - ρ) ^ 2 / 8))) := by
  rw [gaussShiftKernel_apply θ₀]
  have hd : (0 : ℝ) < ‖φ - θ₀‖ := lt_of_le_of_lt hρ0 hρd
  have ht : 0 ≤ ‖φ - θ₀‖ * (‖φ - θ₀‖ - ρ) / 2 := by
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (norm_nonneg _) (by linarith)
  -- Rewrite the acceptance region with the inner product in `stdGaussianShift`-order.
  have hset_eq : dlTestSet θ₀ φ ρ
      = {y : EuclideanSpace ℝ ι | ‖φ - θ₀‖ * (‖φ - θ₀‖ - ρ) / 2 ≤ ⟪φ - θ₀, y - θ₀⟫} := by
    unfold dlTestSet; ext y; simp only [Set.mem_setOf_eq]; rw [real_inner_comm]
  rw [hset_eq]
  refine (stdGaussianShift_inner_ge_le θ₀ (φ - θ₀) _ ht).trans_eq ?_
  congr 2
  have hdne : ‖φ - θ₀‖ ≠ 0 := hd.ne'
  field_simp
  ring

/-- **Type II error bound** (BPPD §6, deviation D4).

Under any alternative `y ∼ N(θ, I)` with `‖θ − φ‖ ≤ ρ`, the probability of (wrongly) accepting
`θ₀` — i.e. landing in the complement of the acceptance region — is
`≤ exp(−(‖φ − θ₀‖ − ρ)²/8)`. Here `⟪y − θ₀, φ − θ₀⟫` has mean
`⟪θ − θ₀, φ − θ₀⟫ ≥ ‖φ − θ₀‖·(‖φ − θ₀‖ − ρ)` (Cauchy–Schwarz on `‖θ − φ‖ ≤ ρ`) and variance
`‖φ − θ₀‖²`, so the downward deviation to the midpoint threshold is again standardized to
`(‖φ − θ₀‖ − ρ)/2`. -/
lemma measure_compl_dlTestSet_le (θ₀ φ θ : EuclideanSpace ℝ ι) {ρ : ℝ}
    -- USER-INPUT: 0 ≤ ρ (net radius nonneg); BPPD §6 / D4
    (hρ0 : 0 ≤ ρ)
    -- USER-INPUT: ρ < ‖φ − θ₀‖ (positive margin); BPPD §6 / D4
    (hρd : ρ < ‖φ - θ₀‖)
    -- USER-INPUT: ‖θ − φ‖ ≤ ρ (alternative θ lies in the ρ-ball around the net point φ); BPPD §6 / D4
    (hθφ : ‖θ - φ‖ ≤ ρ) :
    (gaussShiftKernel ι θ) (dlTestSet θ₀ φ ρ)ᶜ
      ≤ ENNReal.ofReal (Real.exp (-((‖φ - θ₀‖ - ρ) ^ 2 / 8))) := by
  rw [gaussShiftKernel_apply θ]
  have hd : (0 : ℝ) < ‖φ - θ₀‖ := lt_of_le_of_lt hρ0 hρd
  have ht : 0 ≤ ‖φ - θ₀‖ * (‖φ - θ₀‖ - ρ) / 2 := by
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (norm_nonneg _) (by linarith)
  -- The statistic's mean under `θ` is at least `d(d − ρ)` (Cauchy–Schwarz on `‖θ − φ‖ ≤ ρ`).
  have hmean : ‖φ - θ₀‖ * (‖φ - θ₀‖ - ρ) ≤ ⟪θ - θ₀, φ - θ₀⟫ := by
    have hself : ⟪φ - θ₀, φ - θ₀⟫ = ‖φ - θ₀‖ ^ 2 := real_inner_self_eq_norm_sq _
    have hsplit : ⟪θ - θ₀, φ - θ₀⟫ = ⟪θ - φ, φ - θ₀⟫ + ‖φ - θ₀‖ ^ 2 := by
      rw [← hself, ← inner_add_left]; congr 1; abel
    have hcs : -(ρ * ‖φ - θ₀‖) ≤ ⟪θ - φ, φ - θ₀⟫ := by
      have h1 : |⟪θ - φ, φ - θ₀⟫| ≤ ‖θ - φ‖ * ‖φ - θ₀‖ := abs_real_inner_le_norm _ _
      have h2 : ‖θ - φ‖ * ‖φ - θ₀‖ ≤ ρ * ‖φ - θ₀‖ :=
        mul_le_mul_of_nonneg_right hθφ (norm_nonneg _)
      have h3 := abs_le.mp h1
      linarith [h3.1, h3.2]
    rw [hsplit]; nlinarith [hcs]
  -- The complement is contained in the reflected half-space `{d(d−ρ)/2 ≤ ⟪−(φ−θ₀), y − θ⟫}`.
  have hsub : (dlTestSet θ₀ φ ρ)ᶜ
      ⊆ {y : EuclideanSpace ℝ ι |
          ‖φ - θ₀‖ * (‖φ - θ₀‖ - ρ) / 2 ≤ ⟪-(φ - θ₀), y - θ⟫} := by
    intro y hy
    simp only [dlTestSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hy
    simp only [Set.mem_setOf_eq]
    rw [inner_neg_left, real_inner_comm]
    have hdecomp : ⟪y - θ₀, φ - θ₀⟫ = ⟪y - θ, φ - θ₀⟫ + ⟪θ - θ₀, φ - θ₀⟫ := by
      rw [← inner_add_left]; congr 1; abel
    linarith [hy, hmean, hdecomp]
  calc ((stdGaussian (EuclideanSpace ℝ ι)).map (· + θ)) (dlTestSet θ₀ φ ρ)ᶜ
      ≤ ((stdGaussian (EuclideanSpace ℝ ι)).map (· + θ))
          {y : EuclideanSpace ℝ ι |
            ‖φ - θ₀‖ * (‖φ - θ₀‖ - ρ) / 2 ≤ ⟪-(φ - θ₀), y - θ⟫} :=
        measure_mono hsub
    _ ≤ _ := by
        refine (stdGaussianShift_inner_ge_le θ (-(φ - θ₀)) _ ht).trans_eq ?_
        congr 2
        rw [norm_neg]
        have hdne : ‖φ - θ₀‖ ≠ 0 := hd.ne'
        field_simp
        ring

end StatLean.Bayesian
