module
public import StatLean.TimeSeries.ARMA.ScoreAnalysis
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Probability.StrongLaw

@[expose] public section

/-!
# Consistency of the ARMA Gaussian MLE (Hannan program, step 1)

The consistency half of the commissioned Hannan Theorem 3.2 proof: the profiled
Gaussian criterion `armaProfileCriterion` converges (uniformly on compact subsets of
the constraint set) to a deterministic contrast that is uniquely minimized at the true
parameter, so approximate minimizers converge in probability.

* `armaContrast` — the limit contrast `K(θ) = log σ²_θ` where `σ²_θ` is the one-step
  prediction variance of the true process under the working model θ (by the
  Kolmogorov–Szegő/innovations identity the criterion's log-det term vanishes in the
  limit: `T⁻¹ log det Γ_T(θ) → 0` on the constraint set);
* `armaContrast_uniqueMin` — identifiability: `K(θ) ≥ K(θ₀)` with equality iff the
  transfer functions agree; under coprime minimal orders, iff `θ = θ₀`;
* `logdet_armaToeplitz_vanishes` — the Szegő-type limit `T⁻¹ log det Γ_T(θ) → 0`
  (from the innovations recursion: `det Γ_T = ∏ ν_j` and `ν_j → σ²_∞ = 1` for the
  unit-variance model ACVF, geometric rate on the constraint set);
* `criterion_tendsto_contrast` — pointwise stochastic convergence of the profiled
  criterion (ergodic-type LLN for the quadratic form; the α-mixing route via the
  batch-C toolbox after Pham–Tran, or the direct L² route via MA(∞) truncation —
  proof plan in the lane prompt);
* `mle_consistent` — approximate minimizers over the constraint set converge in
  probability to `θ₀` (argmin-consistency wiring following the
  `StatLean/Bayesian` `ArgminConsistency` pattern; compactness supplied by
  restricting to a compact `𝓑`-subset containing `θ₀`, as Hannan does).

**Status (2026-08-09, wave `ts/s1b-arma-finish`): this module is `sorry`-free and
axiom-clean.** `mle_consistent` is proved; its last ingredient — local stochastic
equicontinuity — is the public `armaProfileS_locallyEquicontinuous`. Two further public
bricks were produced on the way and are meant to be cited downstream:

* `linearProcess_avgSq_tendstoInProb` — the *generic* one-filter second-moment LLN
  `T⁻¹ Σ_{t<T} W_{t+1}² →p σ² Σ_n c_n²` for any absolutely summable `c`, proved by the
  same ergodic-theorem-free progression device as `armaResidualSS_tendstoInProb` (of
  which it is **not** an instance: a general `c` is not an ARMA transfer sequence);
* `exists_armaPi_l1_lipschitz` — the **Lipschitz** `ℓ¹` bound on `θ ↦ π(θ)` over a compact
  set of invertible parameters (new in wave `ts/s12b-model-repairs`, 2026-08-09; proved by
  the resolvent identity plus the `ℓ¹` convolution inequality, *not* by Cauchy estimates on
  `∂π/∂θ`). This is the quantitative upgrade of `exists_armaPi_l1_modulus` that
  `ARMA/Diagnostics.lean`'s residue (B) needs;
* `exists_uniform_geometric_bound_arma` and `exists_armaPi_l1_modulus` (from the previous
  wave), the deterministic uniformity inputs.

The Gram-tail *difference* modulus that the 2026-08-09 route note demanded turned out to
be unnecessary: consistency only needs a one-sided bound, so a `θ`-uniform `o_p(1)` bound
on the correction term suffices, and that follows from the entrywise rank-one dominance
`|G_{ij}| ≤ (1 − r²)⁻¹h_ih_j` — see `gramTail_uniform_tendstoInProb`.

**Reference.** Hannan (1973) §2; Brockwell & Davis (1991) §10.8 (Props 10.8.1–10.8.3);
FY Theorem 3.2 cites both. (`Hannan 1973 / B&D §10.8`.)
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-- The **asymptotic one-step prediction variance** of the unit-variance true model
`θ₀ = (b₀, a₀)` filtered through the working model `θ = (b, a)`: in spectral terms
`σ²(θ; θ₀) = exp(∫ log(g_{θ₀}/g_θ)) · 1`-shaped; realized time-domain as
`Σ_j c_j²` where `c = π(θ) ∗ ψ(θ₀)` is the composite filter (the coefficients of
`(b(z)/a(z)) · (a₀(z)/b₀(z))`). -/
noncomputable def armaContrastVar {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ)
    (b : Fin p → ℝ) (a : Fin q → ℝ) : ℝ :=
  ∑' n : ℕ, (∑ jk ∈ Finset.range (n + 1),
    armaPi b a jk * armaPsi b0 a0 (n - jk)) ^ 2

section CompositeFilter

/-! ### The composite filter `c = π(θ) ∗ ψ(θ₀)`

The inversion coefficients `π(b, a)` are the transfer coefficients of the *reversed*
parameter pair: `arPoly b = maPoly (−b)` and `maPoly a = arPoly (−a)` (the sign
conventions of `arPoly`/`maPoly` differ by exactly the sign of the coefficients), so
`armaPi b a = armaPsi (−a) (−b)` and the whole `ARMAExistence` analytic layer
(geometric decay in particular) applies verbatim to `π`. -/

private lemma coeff_arPoly_zero' {p : ℕ} (b : Fin p → ℝ) : (arPoly b).coeff 0 = 1 := by
  simp [arPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

private lemma coeff_maPoly_zero' {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  simp [maPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

/-- The AR polynomial of the negated coefficients is the MA polynomial. -/
private lemma arPoly_neg {q : ℕ} (a : Fin q → ℝ) : arPoly (fun j => -a j) = maPoly a := by
  simp [arPoly, maPoly, sub_eq_add_neg]

/-- The MA polynomial of the negated coefficients is the AR polynomial. -/
private lemma maPoly_neg {p : ℕ} (b : Fin p → ℝ) : maPoly (fun i => -b i) = arPoly b := by
  simp [arPoly, maPoly, sub_eq_add_neg]

/-- The inversion coefficients are the transfer coefficients of the reversed pair. -/
private lemma armaPi_eq_armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    armaPi b a n = armaPsi (fun j => -a j) (fun i => -b i) n := by
  rw [armaPi, armaPsi, maPoly_neg, arPoly_neg]

private lemma armaPi_zero {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
    armaPi b a 0 = 1 := by
  rw [armaPi_eq_armaPsi, armaPsi_zero]

/-- **Geometric decay of the inversion coefficients** on the constraint set (the
`ψ`-statement of `ARMAExistence` read through `armaPi_eq_armaPsi`). -/
private lemma exists_geometric_bound_armaPi {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n, |armaPi b a n| ≤ C * r ^ n := by
  have hroot : NoRootClosedDisc (fun j => -a j) := by
    intro z hz
    rw [arPoly_neg]
    exact hB.2 z hz
  obtain ⟨C, hC, r, hr0, hr1, hbnd⟩ := exists_geometric_bound_armaPsi (fun i => -b i) hroot
  exact ⟨C, hC, r, hr0, hr1, fun n => by rw [armaPi_eq_armaPsi]; exact hbnd n⟩

/-! ### The locally uniform geometric bound (the `mle_consistent` brick)

`exists_geometric_bound_armaPsi` (and hence `exists_geometric_bound_armaPi` above) is
stated *non-quantitatively*: it produces `C` and `r` with no control by the radius or by
the sup-bound of the transfer function, so it cannot be used as a black box to get a
bound that is uniform over a compact family of parameters. This block redoes its Cauchy
estimate carrying the radius and the sup-bound as parameters
(`abs_armaPsi_le_of_disc_bounds`), and then runs the compactness recipe
(`exists_radius_nonvanishing`, `exists_disc_bounds`) to obtain the uniform statement
`exists_uniform_geometric_bound_arma`, which is the single brick both halves of
`mle_consistent`'s remaining debt — the continuity of `θ ↦ armaContrastVar θ₀ θ` and the
stochastic-equicontinuity estimate — were reduced to. -/

section GeometricBrick

open Metric Polynomial
open scoped ENNReal Real

private lemma hasSum_polyEval_mul {c : ℕ → ℂ} {z S : ℂ} (P : Polynomial ℂ)
    (h : HasSum (fun n => c n * z ^ n) S) :
    HasSum (fun n => (∑ k ∈ Finset.range (n + 1), P.coeff k * c (n - k)) * z ^ n)
      (P.eval z * S) := by
  classical
  have hcz : ∀ k, P.natDegree < k → P.coeff k = 0 := fun k hk =>
    Polynomial.coeff_eq_zero_of_natDegree_lt hk
  have hkey : ∀ k : ℕ, HasSum (fun m => (if k ≤ m then P.coeff k * c (m - k) else 0) * z ^ m)
      (P.coeff k * z ^ k * S) := by
    intro k
    have h1 : HasSum (fun n => P.coeff k * z ^ k * (c n * z ^ n)) (P.coeff k * z ^ k * S) :=
      h.mul_left _
    have hg : Function.Injective (fun n : ℕ => k + n) := add_right_injective k
    have hzero : ∀ x ∉ Set.range (fun n : ℕ => k + n),
        (if k ≤ x then P.coeff k * c (x - k) else 0) * z ^ x = 0 := by
      intro x hx
      rw [if_neg, zero_mul]
      intro hkx
      exact hx ⟨x - k, by show k + (x - k) = x; omega⟩
    refine (hg.hasSum_iff hzero).1 ?_
    have heq : ((fun m => (if k ≤ m then P.coeff k * c (m - k) else 0) * z ^ m) ∘
        fun n : ℕ => k + n) = fun n => P.coeff k * z ^ k * (c n * z ^ n) := by
      funext n
      simp only [Function.comp_apply, if_pos (Nat.le_add_right k n), Nat.add_sub_cancel_left,
        pow_add]
      ring
    rw [heq]
    exact h1
  have hsum := hasSum_sum (s := Finset.range (P.natDegree + 1)) (fun k _ => hkey k)
  have hrhs : ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * z ^ k * S = P.eval z * S := by
    rw [← Finset.sum_mul, ← Polynomial.eval_eq_sum_range]
  rw [hrhs] at hsum
  have hfun : (fun m => ∑ k ∈ Finset.range (P.natDegree + 1),
        (if k ≤ m then P.coeff k * c (m - k) else 0) * z ^ m)
      = fun n => (∑ k ∈ Finset.range (n + 1), P.coeff k * c (n - k)) * z ^ n := by
    funext m
    rw [← Finset.sum_mul]
    congr 1
    obtain ⟨N, hNd, hNm⟩ : ∃ N : ℕ, P.natDegree ≤ N ∧ m ≤ N :=
      ⟨max P.natDegree m, le_max_left _ _, le_max_right _ _⟩
    have e1 : ∑ k ∈ Finset.range (P.natDegree + 1),
          (if k ≤ m then P.coeff k * c (m - k) else 0)
        = ∑ k ∈ Finset.range (N + 1), (if k ≤ m then P.coeff k * c (m - k) else 0) := by
      have hsub : Finset.range (P.natDegree + 1) ⊆ Finset.range (N + 1) := by
        intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
      refine Finset.sum_subset hsub fun k _ hk => ?_
      simp only [Finset.mem_range, not_lt] at hk
      rw [hcz k (by omega)]
      simp
    have e2 : ∑ k ∈ Finset.range (m + 1), P.coeff k * c (m - k)
        = ∑ k ∈ Finset.range (N + 1), (if k ≤ m then P.coeff k * c (m - k) else 0) := by
      have hsub : Finset.range (m + 1) ⊆ Finset.range (N + 1) := by
        intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
      rw [← Finset.sum_subset hsub (fun k _ hk => by
        simp only [Finset.mem_range, not_lt] at hk
        rw [if_neg (by omega)])]
      exact Finset.sum_congr rfl fun k hk => by
        simp only [Finset.mem_range] at hk
        rw [if_pos (by omega)]
    rw [e1, e2]
  rwa [hfun] at hsum

private lemma hasSum_polyEval (P : Polynomial ℂ) (z : ℂ) :
    HasSum (fun n => P.coeff n * z ^ n) (P.eval z) := by
  classical
  have h : HasSum (fun n => P.coeff n * z ^ n)
      (∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * z ^ n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      show P.coeff n * z ^ n = 0
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul])
  rwa [← Polynomial.eval_eq_sum_range] at h
/-- **Quantitative Cauchy estimate for the ARMA transfer coefficients.** -/
private lemma abs_armaPsi_le_of_disc_bounds {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {R Mnum dlow : ℝ} (hR : 1 < R) (hd : 0 < dlow)
    (hlow : ∀ z : ℂ, ‖z‖ ≤ R → dlow ≤ ‖Polynomial.aeval z (arPoly b)‖)
    (hup : ∀ z : ℂ, ‖z‖ ≤ R → ‖Polynomial.aeval z (maPoly a)‖ ≤ Mnum) (n : ℕ) :
    |armaPsi b a n| ≤ (Mnum / dlow) * (R⁻¹) ^ n := by
  classical
  have hR0 : (0:ℝ) < R := lt_trans zero_lt_one hR
  obtain ⟨A, hAdef⟩ : ∃ A : Polynomial ℂ, A = (maPoly a).map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Polynomial ℂ, B = (arPoly b).map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  have hAc : ∀ k, A.coeff k = ((maPoly a).coeff k : ℂ) := by
    intro k; rw [hAdef, Polynomial.coeff_map]; simp
  have hBc : ∀ k, B.coeff k = ((arPoly b).coeff k : ℂ) := by
    intro k; rw [hBdef, Polynomial.coeff_map]; simp
  have hAev : ∀ z : ℂ, A.eval z = Polynomial.aeval z (maPoly a) := by
    intro z; rw [hAdef, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hBev : ∀ z : ℂ, B.eval z = Polynomial.aeval z (arPoly b) := by
    intro z; rw [hBdef, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hBne : ∀ z : ℂ, ‖z‖ ≤ R → B.eval z ≠ 0 := by
    intro z hz h0
    have := hlow z hz
    rw [← hBev, h0, norm_zero] at this
    linarith
  have hb : NoRootClosedDisc b := by
    intro z hz
    rw [← hBev]
    exact hBne z (le_trans hz (le_of_lt hR))
  have hsum : Summable fun n => |armaPsi b a n| := summable_abs_armaPsi a hb
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun z => A.eval z / B.eval z := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      P = FormalMultilinearSeries.ofScalars ℂ (fun n => ((armaPsi b a n : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hΨnorm : ∀ n, ‖Ψ n‖ = |armaPsi b a n| := by
    intro n; rw [hΨ, FormalMultilinearSeries.ofScalars_norm]; simp
  have hΨapp : ∀ (n : ℕ) (z : ℂ), Ψ n (fun _ => z) = ((armaPsi b a n : ℝ) : ℂ) * z ^ n := by
    intro n z; rw [hΨ, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hrad1 : (1 : ℝ≥0∞) ≤ Ψ.radius := by
    have := Ψ.le_radius_of_bound (∑' n, |armaPsi b a n|) (r := 1) (fun n => by
      rw [hΨnorm]
      simpa using hsum.le_tsum n (fun m _ => abs_nonneg _))
    simpa using this
  -- the power series sums to `g` on the open unit ball
  have hHasSum : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => Ψ n (fun _ => z)) (g z) := by
    intro z hz
    have hzle : ‖z‖ ≤ 1 := le_of_lt hz
    have hzR : ‖z‖ ≤ R := le_trans hzle (le_of_lt hR)
    have hsz : Summable fun n => ((armaPsi b a n : ℝ) : ℂ) * z ^ n := by
      refine Summable.of_norm (hsum.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_))
      rw [norm_mul, norm_pow]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      have : ‖z‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hzle
      nlinarith [abs_nonneg (armaPsi b a n), pow_nonneg (norm_nonneg z) n]
    have hS := hsz.hasSum
    have h1 := hasSum_polyEval_mul (c := fun n => ((armaPsi b a n : ℝ) : ℂ)) B hS
    have hcoef : ∀ m : ℕ,
        (∑ k ∈ Finset.range (m + 1), B.coeff k * ((armaPsi b a (m - k) : ℝ) : ℂ))
          = A.coeff m := by
      intro m
      rw [hAc, ← arPoly_conv_armaPsi b a m]
      push_cast [hBc]
      rfl
    simp only [hcoef] at h1
    have hkey := h1.unique (hasSum_polyEval A z)
    have hval : g z = ∑' n, ((armaPsi b a n : ℝ) : ℂ) * z ^ n := by
      rw [hgdef]
      simp only
      rw [← hkey]
      exact mul_div_cancel_left₀ _ (hBne z hzR)
    simp only [hΨapp]
    rw [hval]
    exact hS
  have hΨball : HasFPowerSeriesOnBall g Ψ 0 1 :=
    { r_le := hrad1
      r_pos := by norm_num
      hasSum := by
        intro y hy
        rw [zero_add]
        refine hHasSum y ?_
        have h1 : ‖y‖ₑ < 1 := by simpa [edist_eq_enorm_sub] using hy
        rw [show ((1:ℝ≥0∞)) = ((1:NNReal) : ℝ≥0∞) by simp, enorm_lt_coe] at h1
        exact_mod_cast h1 }
  -- differentiability on the larger closed ball
  have hdiff : DifferentiableOn ℂ g (Metric.closedBall 0 R) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rw [hgdef]
    exact A.differentiableAt.div B.differentiableAt (hBne z hz)
  obtain ⟨R', hR'c⟩ : ∃ R' : NNReal, ((R' : ℝ)) = R :=
    ⟨R.toNNReal, Real.coe_toNNReal _ hR0.le⟩
  have hR'pos : (0:NNReal) < R' := by
    have : (0:ℝ) < (R' : ℝ) := by rw [hR'c]; exact hR0
    exact_mod_cast this
  have hdiff' : DifferentiableOn ℂ g (Metric.closedBall 0 (R' : ℝ)) := by
    rw [hR'c]; exact hdiff
  have hcauchy := hdiff'.hasFPowerSeriesOnBall hR'pos
  have heq : Ψ = cauchyPowerSeries g 0 (R' : ℝ) :=
    hΨball.hasFPowerSeriesAt.eq_formalMultilinearSeries hcauchy.hasFPowerSeriesAt
  -- the sup bound on the circle
  have hgbd : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ Mnum / dlow := by
    intro z hz
    have h1 : ‖A.eval z‖ ≤ Mnum := by rw [hAev]; exact hup z hz
    have h2 : dlow ≤ ‖B.eval z‖ := by rw [hBev]; exact hlow z hz
    have hBz : 0 < ‖B.eval z‖ := lt_of_lt_of_le hd h2
    rw [hgdef]
    simp only [norm_div]
    rw [div_le_div_iff₀ hBz hd]
    nlinarith [norm_nonneg (A.eval z)]
  have hcont : Continuous fun θ : ℝ => ‖g (circleMap 0 R θ)‖ := by
    refine (hdiff.continuousOn.comp_continuous (continuous_circleMap 0 R) ?_).norm
    intro θ
    simp [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hR0.le]
  have hint : (∫ θ in (0:ℝ)..(2*π), ‖g (circleMap 0 R θ)‖) ≤ 2*π*(Mnum/dlow) := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume)
      (le_of_lt Real.two_pi_pos) (hcont.intervalIntegrable 0 (2*π))
      (intervalIntegrable_const (c := Mnum / dlow))
      (fun x _ => hgbd _ (by simp [norm_circleMap_zero, abs_of_nonneg hR0.le]))
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
    exact hmono
  have hMd : 0 ≤ Mnum / dlow := le_trans (norm_nonneg _) (hgbd 0 (by simp [hR0.le]))
  have hfin := norm_cauchyPowerSeries_le g 0 (R' : ℝ) n
  rw [← heq, hΨnorm, hR'c] at hfin
  refine hfin.trans ?_
  have hpow : (0:ℝ) ≤ |R|⁻¹ ^ n := by positivity
  have hfac : (2 * π)⁻¹ * (∫ θ in (0:ℝ)..(2*π), ‖g (circleMap 0 R θ)‖) ≤ Mnum / dlow := by
    have h2pi : (0:ℝ) < 2 * π := Real.two_pi_pos
    rw [inv_mul_le_iff₀ h2pi]
    linarith [hint]
  have habsR : |R| = R := abs_of_nonneg hR0.le
  rw [habsR]
  exact mul_le_mul_of_nonneg_right hfac (by positivity)


/-- **Step A of the compactness recipe**: a radius `R > 1` on which a compactly-indexed
continuous family of denominators, nonvanishing on the closed unit disc, is still
nonvanishing. -/
private lemma exists_radius_nonvanishing {ι : Type*} [TopologicalSpace ι] {K : Set ι}
    (hK : IsCompact K) {den : ι → ℂ → ℂ}
    (hden : Continuous fun x : ι × ℂ => den x.1 x.2)
    (hne : ∀ x ∈ K, ∀ z : ℂ, ‖z‖ ≤ 1 → den x z ≠ 0) :
    ∃ R : ℝ, 1 < R ∧ R ≤ 2 ∧ ∀ x ∈ K, ∀ z : ℂ, ‖z‖ ≤ R → den x z ≠ 0 := by
  classical
  -- the "polar" parametrisation `z = s · w`, `‖w‖ ≤ 1`, `s ∈ [1, 2]`
  have hcont : Continuous fun w : ι × ℂ × ℝ => den w.1 ((w.2.2 : ℂ) * w.2.1) := by
    have hmap : Continuous fun w : ι × ℂ × ℝ => ((w.1, ((w.2.2 : ℂ) * w.2.1)) : ι × ℂ) :=
      continuous_fst.prodMk (((Complex.continuous_ofReal.comp
        (continuous_snd.comp continuous_snd))).mul (continuous_fst.comp continuous_snd))
    exact hden.comp hmap
  have hD : IsCompact (K ×ˢ (Metric.closedBall (0:ℂ) 1 ×ˢ Set.Icc (1:ℝ) 2)) :=
    hK.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hZ : IsCompact ((K ×ˢ (Metric.closedBall (0:ℂ) 1 ×ˢ Set.Icc (1:ℝ) 2)) ∩
      {w : ι × ℂ × ℝ | den w.1 ((w.2.2 : ℂ) * w.2.1) = 0}) :=
    hD.inter_right (isClosed_eq hcont continuous_const)
  -- the decomposition `z = s · (z / s)` with `s = max ‖z‖ 1`
  have hdecomp : ∀ (R : ℝ), R ≤ 2 → ∀ (x : ι), x ∈ K → ∀ z : ℂ, ‖z‖ ≤ R →
      ∃ w : ℂ, ∃ s : ℝ, ‖w‖ ≤ 1 ∧ 1 ≤ s ∧ s ≤ 2 ∧ s ≤ max R 1 ∧ (s : ℂ) * w = z := by
    intro R hR2 x hx z hz
    rcases le_or_gt ‖z‖ 1 with h | h
    · exact ⟨z, 1, h, le_rfl, by norm_num, le_max_right _ _, by norm_num⟩
    · refine ⟨z / (‖z‖ : ℂ), ‖z‖, ?_, le_of_lt h, le_trans hz hR2, ?_, ?_⟩
      · rw [norm_div]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
        rw [div_self (by positivity)]
      · exact le_trans hz (le_max_left _ _)
      · have hzne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact ne_of_gt (lt_trans zero_lt_one h)
        field_simp
  rcases Set.eq_empty_or_nonempty ((K ×ˢ (Metric.closedBall (0:ℂ) 1 ×ˢ Set.Icc (1:ℝ) 2)) ∩
      {w : ι × ℂ × ℝ | den w.1 ((w.2.2 : ℂ) * w.2.1) = 0}) with hempty | hne'
  · refine ⟨2, by norm_num, le_rfl, fun x hx z hz => ?_⟩
    obtain ⟨w, s, hw, hs1, hs2, _, hsw⟩ := hdecomp 2 le_rfl x hx z hz
    intro h0
    have : (x, w, s) ∈ (K ×ˢ (Metric.closedBall (0:ℂ) 1 ×ˢ Set.Icc (1:ℝ) 2)) ∩
        {w : ι × ℂ × ℝ | den w.1 ((w.2.2 : ℂ) * w.2.1) = 0} := by
      refine ⟨⟨hx, ?_, ?_⟩, ?_⟩
      · simpa [Metric.mem_closedBall, dist_zero_right] using hw
      · exact ⟨hs1, hs2⟩
      · simpa [hsw] using h0
    rw [hempty] at this
    exact this
  · obtain ⟨w0, hw0mem, hw0min⟩ := hZ.exists_isMinOn hne'
      ((continuous_snd.comp continuous_snd).continuousOn)
    have hs0 : 1 < w0.2.2 := by
      rcases lt_or_eq_of_le hw0mem.1.2.2.1 with h | h
      · exact h
      · exfalso
        refine hne w0.1 hw0mem.1.1 w0.2.1 (by
          simpa [Metric.mem_closedBall, dist_zero_right] using hw0mem.1.2.1) ?_
        have := hw0mem.2
        simp only [Set.mem_setOf_eq] at this
        rwa [← h, Complex.ofReal_one, one_mul] at this
    refine ⟨min ((1 + w0.2.2) / 2) 2, ?_, min_le_right _ _, fun x hx z hz => ?_⟩
    · exact lt_min (by linarith) (by norm_num)
    · obtain ⟨w, s, hw, hs1, hs2, hsR, hsw⟩ :=
        hdecomp (min ((1 + w0.2.2) / 2) 2) (min_le_right _ _) x hx z hz
      intro h0
      have hmem : (x, w, s) ∈ (K ×ˢ (Metric.closedBall (0:ℂ) 1 ×ˢ Set.Icc (1:ℝ) 2)) ∩
          {w : ι × ℂ × ℝ | den w.1 ((w.2.2 : ℂ) * w.2.1) = 0} := by
        refine ⟨⟨hx, ?_, ⟨hs1, hs2⟩⟩, ?_⟩
        · simpa [Metric.mem_closedBall, dist_zero_right] using hw
        · simpa [hsw] using h0
      have hmin := hw0min hmem
      have hlt : s < w0.2.2 := by
        have h1 : s ≤ max (min ((1 + w0.2.2) / 2) 2) 1 := hsR
        have h2 : max (min ((1 + w0.2.2) / 2) 2) 1 < w0.2.2 := by
          refine max_lt ?_ hs0
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        linarith
      exact absurd hmin (not_le.2 hlt)

/-- **Step B of the compactness recipe**: uniform numerator/denominator bounds on a
closed disc of radius `R > 1`. -/
private lemma exists_disc_bounds {ι : Type*} [TopologicalSpace ι] {K : Set ι}
    (hK : IsCompact K) {num den : ι → ℂ → ℂ}
    (hnum : Continuous fun x : ι × ℂ => num x.1 x.2)
    (hden : Continuous fun x : ι × ℂ => den x.1 x.2)
    (hne : ∀ x ∈ K, ∀ z : ℂ, ‖z‖ ≤ 1 → den x z ≠ 0) :
    ∃ R Mnum dlow : ℝ, 1 < R ∧ 0 < dlow ∧
      (∀ x ∈ K, ∀ z : ℂ, ‖z‖ ≤ R → dlow ≤ ‖den x z‖) ∧
      (∀ x ∈ K, ∀ z : ℂ, ‖z‖ ≤ R → ‖num x z‖ ≤ Mnum) := by
  classical
  obtain ⟨R, hR1, hR2, hRne⟩ := exists_radius_nonvanishing hK hden hne
  rcases Set.eq_empty_or_nonempty K with rfl | hKne
  · exact ⟨R, 0, 1, hR1, one_pos, by simp, by simp⟩
  have hR0 : (0:ℝ) < R := lt_trans zero_lt_one hR1
  have hcpt : IsCompact (K ×ˢ Metric.closedBall (0:ℂ) R) :=
    hK.prod (isCompact_closedBall _ _)
  have hcne : (K ×ˢ Metric.closedBall (0:ℂ) R).Nonempty :=
    hKne.prod (Metric.nonempty_closedBall.2 hR0.le)
  obtain ⟨x0, hx0, hmin⟩ := hcpt.exists_isMinOn hcne
    (Continuous.continuousOn (hden.norm))
  obtain ⟨x1, hx1, hmax⟩ := hcpt.exists_isMaxOn hcne
    (Continuous.continuousOn (hnum.norm))
  have hmem : ∀ (x : ι), x ∈ K → ∀ z : ℂ, ‖z‖ ≤ R → (x, z) ∈ K ×ˢ Metric.closedBall (0:ℂ) R := by
    intro x hx z hz
    exact ⟨hx, by simpa [Metric.mem_closedBall, dist_zero_right] using hz⟩
  refine ⟨R, ‖num x1.1 x1.2‖, ‖den x0.1 x0.2‖, hR1, ?_, ?_, ?_⟩
  · refine norm_pos_iff.2 (hRne x0.1 hx0.1 x0.2 ?_)
    simpa [Metric.mem_closedBall, dist_zero_right] using hx0.2
  · intro x hx z hz
    exact hmin (hmem x hx z hz)
  · intro x hx z hz
    exact hmax (hmem x hx z hz)


private lemma aeval_arPoly_complex {p : ℕ} (b : Fin p → ℝ) (z : ℂ) :
    Polynomial.aeval z (arPoly b) = 1 - ∑ i : Fin p, (b i : ℂ) * z ^ ((i : ℕ) + 1) := by
  simp [arPoly]

private lemma aeval_maPoly_complex {q : ℕ} (a : Fin q → ℝ) (z : ℂ) :
    Polynomial.aeval z (maPoly a) = 1 + ∑ j : Fin q, (a j : ℂ) * z ^ ((j : ℕ) + 1) := by
  simp [maPoly]

private lemma continuous_aeval_arPoly {p q : ℕ} :
    Continuous fun x : ((Fin p → ℝ) × (Fin q → ℝ)) × ℂ =>
      Polynomial.aeval x.2 (arPoly x.1.1) := by
  simp only [aeval_arPoly_complex]
  fun_prop

private lemma continuous_aeval_maPoly {p q : ℕ} :
    Continuous fun x : ((Fin p → ℝ) × (Fin q → ℝ)) × ℂ =>
      Polynomial.aeval x.2 (maPoly x.1.2) := by
  simp only [aeval_maPoly_complex]
  fun_prop

/-- **THE BRICK**: a locally uniform geometric bound on the ARMA transfer and inversion
coefficients over a compact set of invertible parameters. -/
theorem exists_uniform_geometric_bound_arma {p q : ℕ}
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))} (hK : IsCompact K)
    (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
      (∀ ba ∈ K, ∀ n, |armaPsi ba.1 ba.2 n| ≤ C * r ^ n) ∧
      (∀ ba ∈ K, ∀ n, |armaPi ba.1 ba.2 n| ≤ C * r ^ n) := by
  classical
  obtain ⟨R₁, M₁, d₁, hR₁, hd₁, hlow₁, hup₁⟩ :=
    exists_disc_bounds (num := fun ba : (Fin p → ℝ) × (Fin q → ℝ) => fun z : ℂ =>
        Polynomial.aeval z (maPoly ba.2))
      (den := fun ba : (Fin p → ℝ) × (Fin q → ℝ) => fun z : ℂ =>
        Polynomial.aeval z (arPoly ba.1))
      hK continuous_aeval_maPoly continuous_aeval_arPoly
      (fun ba hba z hz => (hKB ba hba).1 z hz)
  obtain ⟨R₂, M₂, d₂, hR₂, hd₂, hlow₂, hup₂⟩ :=
    exists_disc_bounds (num := fun ba : (Fin p → ℝ) × (Fin q → ℝ) => fun z : ℂ =>
        Polynomial.aeval z (arPoly ba.1))
      (den := fun ba : (Fin p → ℝ) × (Fin q → ℝ) => fun z : ℂ =>
        Polynomial.aeval z (maPoly ba.2))
      hK continuous_aeval_arPoly continuous_aeval_maPoly
      (fun ba hba z hz => (hKB ba hba).2 z hz)
  have hR : 1 < min R₁ R₂ := lt_min hR₁ hR₂
  have hRpos : (0:ℝ) < min R₁ R₂ := lt_trans zero_lt_one hR
  have hC1 : M₁ / d₁ ≤ max 1 (max (M₁ / d₁) (M₂ / d₂)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hC2 : M₂ / d₂ ≤ max 1 (max (M₁ / d₁) (M₂ / d₂)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max 1 (max (M₁ / d₁) (M₂ / d₂)), (min R₁ R₂)⁻¹, le_max_left _ _, by positivity,
    inv_lt_one_of_one_lt₀ hR, ?_, ?_⟩
  · intro ba hba n
    refine le_trans (abs_armaPsi_le_of_disc_bounds ba.1 ba.2 hR hd₁
      (fun z hz => hlow₁ ba hba z (le_trans hz (min_le_left _ _)))
      (fun z hz => hup₁ ba hba z (le_trans hz (min_le_left _ _))) n) ?_
    exact mul_le_mul_of_nonneg_right hC1 (by positivity)
  · intro ba hba n
    rw [armaPi_eq_armaPsi]
    have hlow' : ∀ z : ℂ, ‖z‖ ≤ min R₁ R₂ →
        d₂ ≤ ‖Polynomial.aeval z (arPoly fun j => -ba.2 j)‖ := by
      intro z hz
      rw [arPoly_neg]
      exact hlow₂ ba hba z (le_trans hz (min_le_right _ _))
    have hup' : ∀ z : ℂ, ‖z‖ ≤ min R₁ R₂ →
        ‖Polynomial.aeval z (maPoly fun i => -ba.1 i)‖ ≤ M₂ := by
      intro z hz
      rw [maPoly_neg]
      exact hup₂ ba hba z (le_trans hz (min_le_right _ _))
    refine le_trans (abs_armaPsi_le_of_disc_bounds _ _ hR hd₂ hlow' hup' n) ?_
    exact mul_le_mul_of_nonneg_right hC2 (by positivity)

end GeometricBrick

/-- A single pair `(C, r)` dominating both filters of the composite. -/
private lemma exists_common_geometric_bound {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
      (∀ n, |armaPi b a n| ≤ C * r ^ n) ∧ (∀ n, |armaPsi b0 a0 n| ≤ C * r ^ n) := by
  obtain ⟨C₁, hC₁, r₁, hr₁0, hr₁1, hb₁⟩ := exists_geometric_bound_armaPi hB
  obtain ⟨C₂, hC₂, r₂, hr₂0, hr₂1, hb₂⟩ := exists_geometric_bound_armaPsi a0 hB0.1
  refine ⟨max 1 (max C₁ C₂), max r₁ r₂, le_max_left _ _, le_trans hr₁0 (le_max_left _ _),
    max_lt hr₁1 hr₂1, fun n => ?_, fun n => ?_⟩
  · refine (hb₁ n).trans (mul_le_mul (le_trans (le_max_left _ _) (le_max_right _ _))
      (pow_le_pow_left₀ hr₁0 (le_max_left _ _) n) (by positivity) ?_)
    exact le_trans zero_le_one (le_max_left _ _)
  · refine (hb₂ n).trans (mul_le_mul (le_trans (le_max_right _ _) (le_max_right _ _))
      (pow_le_pow_left₀ hr₂0 (le_max_right _ _) n) (by positivity) ?_)
    exact le_trans zero_le_one (le_max_left _ _)

/-- The composite filter coefficients `c_n = Σ_{k ≤ n} π_k(θ) ψ_{n−k}(θ₀)`. -/
private noncomputable def contrastCoeff {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ)
    (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) : ℝ :=
  ∑ jk ∈ Finset.range (n + 1), armaPi b a jk * armaPsi b0 a0 (n - jk)

private lemma armaContrastVar_eq_tsum {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ)
    (b : Fin p → ℝ) (a : Fin q → ℝ) :
    armaContrastVar b0 a0 b a = ∑' n : ℕ, contrastCoeff b0 a0 b a n ^ 2 := rfl

private lemma contrastCoeff_zero {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ)
    (b : Fin p → ℝ) (a : Fin q → ℝ) : contrastCoeff b0 a0 b a 0 = 1 := by
  simp [contrastCoeff, armaPi_zero, armaPsi_zero]

/-- The composite filter inherits (a polynomially corrected) geometric decay. -/
private lemma abs_contrastCoeff_le {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r)
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) (hψ : ∀ n, |armaPsi b0 a0 n| ≤ C * r ^ n)
    (n : ℕ) : |contrastCoeff b0 a0 b a n| ≤ C ^ 2 * ((n : ℝ) + 1) * r ^ n := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (n + 1),
      |armaPi b a k * armaPsi b0 a0 (n - k)| ≤ C ^ 2 * r ^ n := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [abs_mul]
    calc |armaPi b a k| * |armaPsi b0 a0 (n - k)|
        ≤ (C * r ^ k) * (C * r ^ (n - k)) :=
          mul_le_mul (hπ k) (hψ _) (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (r ^ k * r ^ (n - k)) := by ring
      _ = C ^ 2 * r ^ n := by rw [← pow_add]; congr 2; omega
  calc ∑ k ∈ Finset.range (n + 1), |armaPi b a k * armaPsi b0 a0 (n - k)|
      ≤ ∑ _k ∈ Finset.range (n + 1), C ^ 2 * r ^ n := Finset.sum_le_sum hterm
    _ = C ^ 2 * ((n : ℝ) + 1) * r ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- Summability of the squared composite filter (geometric with a quadratic
correction). -/
private lemma summable_sq_contrastCoeff {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    Summable fun n : ℕ => contrastCoeff b0 a0 b a n ^ 2 := by
  obtain ⟨C, r, hC, hr0, hr1, hπ, hψ⟩ := exists_common_geometric_bound hB0 hB
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hr2 : ‖r ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    nlinarith
  have hgeom : Summable fun n : ℕ => ((n : ℝ) + 1) ^ 2 * (r ^ 2) ^ n := by
    have h0 : Summable fun n : ℕ => (r ^ 2) ^ n := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hr2
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * (r ^ 2) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr2
    have h2 : Summable fun n : ℕ => (n : ℝ) ^ 2 * (r ^ 2) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr2
    have := (h2.add (h1.mul_left 2)).add h0
    refine this.congr fun n => ?_
    ring
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_)
    (hgeom.mul_left (C ^ 4))
  have habs := abs_contrastCoeff_le hC hr0 hπ hψ n
  have hnn : 0 ≤ C ^ 2 * ((n : ℝ) + 1) * r ^ n := by positivity
  calc contrastCoeff b0 a0 b a n ^ 2 = |contrastCoeff b0 a0 b a n| ^ 2 := (sq_abs _).symm
    _ ≤ (C ^ 2 * ((n : ℝ) + 1) * r ^ n) ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = C ^ 4 * (((n : ℝ) + 1) ^ 2 * (r ^ 2) ^ n) := by
        rw [← pow_mul, mul_comm 2 n, pow_mul]
        ring

/-- The composite filter is the coefficient sequence of the composite transfer function
`(b(z)/a(z)) · (a₀(z)/b₀(z))`. -/
private lemma contrastCoeff_eq_coeff {p q : ℕ} (b0 b : Fin p → ℝ) (a0 a : Fin q → ℝ) (n : ℕ) :
    contrastCoeff b0 a0 b a n
      = PowerSeries.coeff n
          ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
              ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
            ((((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)) *
              ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

/-- The contrast variance is `1` exactly when the composite filter is `δ₀`. -/
private lemma armaContrastVar_eq_one_iff_coeff {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    armaContrastVar b0 a0 b a = 1 ↔ ∀ n : ℕ, n ≠ 0 → contrastCoeff b0 a0 b a n = 0 := by
  have hsum := summable_sq_contrastCoeff hB0 hB
  constructor
  · intro hvar n hn
    have hpair := hsum.sum_le_tsum ({0, n} : Finset ℕ) (fun i _ => sq_nonneg _)
    rw [Finset.sum_pair (Ne.symm hn), ← armaContrastVar_eq_tsum, hvar,
      contrastCoeff_zero, one_pow] at hpair
    have hle : contrastCoeff b0 a0 b a n ^ 2 ≤ 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hle (sq_nonneg _))
  · intro hzero
    rw [armaContrastVar_eq_tsum]
    have h : ∀ n : ℕ, contrastCoeff b0 a0 b a n ^ 2 = if n = 0 then 1 else 0 := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [contrastCoeff_zero, if_pos rfl, one_pow]
      · rw [hzero n hn, if_neg hn]
        ring
    rw [tsum_congr h]
    exact tsum_ite_eq (0 : ℕ) (fun _ : ℕ => (1 : ℝ))

/-- **Identifiability, honest form** (this is what the contrast variance sees): the
contrast variance equals `1` exactly when the two transfer functions agree, i.e.
`b(z) a₀(z) = b₀(z) a(z)` as polynomials. Recovering `(b, a) = (b₀, a₀)` from this needs
the *working* pair to be coprime as well — see `armaContrastVar_eq_one_not_identifiable`. -/
private lemma armaContrastVar_eq_one_iff_transfer {p q : ℕ} {b0 b : Fin p → ℝ}
    {a0 a : Fin q → ℝ} (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    armaContrastVar b0 a0 b a = 1 ↔ arPoly b * maPoly a0 = arPoly b0 * maPoly a := by
  have hAne : PowerSeries.constantCoeff (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_maPoly_zero']
    exact one_ne_zero
  have hB0ne : PowerSeries.constantCoeff (((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_arPoly_zero']
    exact one_ne_zero
  have hcoeff : armaContrastVar b0 a0 b a = 1 ↔
      (((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
          ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
        ((((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)) *
          ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) = 1 := by
    rw [armaContrastVar_eq_one_iff_coeff hB0 hB, PowerSeries.ext_iff]
    constructor
    · intro h n
      rw [← contrastCoeff_eq_coeff, PowerSeries.coeff_one]
      rcases eq_or_ne n 0 with rfl | hn
      · rw [contrastCoeff_zero, if_pos rfl]
      · rw [h n hn, if_neg hn]
    · intro h n hn
      have := h n
      rw [← contrastCoeff_eq_coeff, PowerSeries.coeff_one, if_neg hn] at this
      exact this
  rw [hcoeff]
  constructor
  · intro h
    have h2 : ((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
        ((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)
        = ((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ) *
            ((maPoly a : Polynomial ℝ) : PowerSeries ℝ) := by
      have hmul := congrArg (fun S => S * ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
        (((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))) h
      simp only [one_mul] at hmul
      rw [show ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
          ((((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
          ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
            (((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))
          = ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
              (((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ))) *
            (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
                ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
              (((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ))) *
                ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)) from by ring,
        PowerSeries.mul_inv_cancel _ hAne, PowerSeries.mul_inv_cancel _ hB0ne, mul_one,
        mul_one] at hmul
      rw [hmul]
      ring
    refine (Polynomial.coe_inj (R := ℝ)).1 ?_
    rw [Polynomial.coe_mul, Polynomial.coe_mul]
    exact h2
  · intro h
    have h2 : ((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
        ((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)
        = ((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ) *
            ((maPoly a : Polynomial ℝ) : PowerSeries ℝ) := by
      rw [← Polynomial.coe_mul, ← Polynomial.coe_mul, h]
    calc ((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
          ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹ *
          ((((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
        = (((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
            ((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)) *
          (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹ *
            ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) := by ring
      _ = (((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ) *
            ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
          (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹ *
            ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) := by rw [h2]
      _ = ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
          ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) := by ring
      _ = 1 := by
          rw [PowerSeries.mul_inv_cancel _ hAne, PowerSeries.mul_inv_cancel _ hB0ne, mul_one]

/-- **Falsity witness for the frozen forward implication of `armaContrastVar_eq_one_iff`.**

With `p = q = 1`, true parameters `b₀ = a₀ = 0` (so `b₀(z) = a₀(z) = 1`: white noise, and
`IsCoprime 1 1` holds) and working parameters `b = 1/2`, `a = −1/2`, the working transfer
function is `b(z)/a(z) = (1 − z/2)/(1 − z/2) = 1`: the working model is a *non-minimal*
representation of the same white noise. Both parameter pairs lie in `𝓑`, the contrast
variance is `1`, yet `b ≠ b₀`. Identifiability of the *parameters* needs coprimality of
the **working** pair too (or a search region of minimal representations); the contrast
variance only ever sees the transfer function — `armaContrastVar_eq_one_iff_transfer`. -/
private lemma arPoly_witness_zero : arPoly (fun _ : Fin 1 => (0 : ℝ)) = 1 := by simp [arPoly]

private lemma maPoly_witness_zero : maPoly (fun _ : Fin 1 => (0 : ℝ)) = 1 := by simp [maPoly]

private lemma maPoly_witness_neg :
    maPoly (fun _ : Fin 1 => (-(1 / 2) : ℝ)) = arPoly (fun _ : Fin 1 => (1 / 2 : ℝ)) :=
  maPoly_neg (fun _ : Fin 1 => (1 / 2 : ℝ))

private lemma noRoot_witness : NoRootClosedDisc (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
  intro z hz hzero
  have hev : Polynomial.aeval z (arPoly (fun _ : Fin 1 => (1 / 2 : ℝ))) = 1 - z / 2 := by
    simp [arPoly]
    ring
  rw [hev] at hzero
  have hz2 : z = 2 := by linear_combination -2 * hzero
  rw [hz2] at hz
  norm_num at hz

private lemma invertible_witness_zero :
    ARMAInvertibleParams (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) := by
  constructor
  · intro z _
    rw [arPoly_witness_zero]
    simp
  · intro z _
    rw [maPoly_witness_zero]
    simp

private lemma invertible_witness_half :
    ARMAInvertibleParams (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ : Fin 1 => (-(1 / 2) : ℝ)) := by
  refine ⟨noRoot_witness, fun z hz => ?_⟩
  rw [maPoly_witness_neg]
  exact noRoot_witness z hz

private theorem armaContrastVar_eq_one_not_identifiable :
    ∃ (b0 b : Fin 1 → ℝ) (a0 a : Fin 1 → ℝ),
      ARMAInvertibleParams b0 a0 ∧ ARMAInvertibleParams b a ∧
        IsCoprime (arPoly b0) (maPoly a0) ∧ armaContrastVar b0 a0 b a = 1 ∧ b ≠ b0 := by
  refine ⟨fun _ => 0, fun _ => 1 / 2, fun _ => 0, fun _ => -(1 / 2),
    invertible_witness_zero, invertible_witness_half, ?_, ?_, ?_⟩
  · rw [arPoly_witness_zero, maPoly_witness_zero]
    exact isCoprime_one_left
  · refine (armaContrastVar_eq_one_iff_transfer invertible_witness_zero
      invertible_witness_half).2 ?_
    rw [arPoly_witness_zero, maPoly_witness_zero, maPoly_witness_neg, mul_one, one_mul]
  · intro h
    have := congrFun h 0
    norm_num at this

/-- The two witness pairs have the **same transfer coefficients** (both are white noise:
`(1 − z/2)/(1 − z/2) = 1 = 1/1`). -/
private lemma armaPsi_witness_eq :
    armaPsi (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ : Fin 1 => (-(1 / 2) : ℝ))
      = armaPsi (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) := by
  have hne : PowerSeries.constantCoeff
      (((arPoly (fun _ : Fin 1 => (1 / 2 : ℝ)) : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_arPoly_zero']
    exact one_ne_zero
  funext n
  rw [armaPsi, armaPsi, maPoly_witness_neg, arPoly_witness_zero, maPoly_witness_zero,
    PowerSeries.mul_inv_cancel _ hne]
  simp

/-- **Falsity witness for `mle_consistent` as frozen**: two *distinct* parameter points of
the constraint set, the first one coprime (a legitimate `θ₀`), at which the profiled
criterion is identically equal *for every sample of every length*. Taking
`K = {θ₀, θ₁}` (finite, hence compact, and containing `θ₀`) and the constant sequence
`θ T ω = θ₁` satisfies every hypothesis of `mle_consistent` — including `hargmin` with
`δT = 0` — while `dist (θ T ω) θ₀` is a fixed positive number. -/
private theorem mle_consistent_not_identifiable :
    ∃ θ0 θ1 : (Fin 1 → ℝ) × (Fin 1 → ℝ),
      ARMAInvertibleParams θ0.1 θ0.2 ∧ ARMAInvertibleParams θ1.1 θ1.2 ∧
        IsCoprime (arPoly θ0.1) (maPoly θ0.2) ∧ θ0 ≠ θ1 ∧
        ∀ (T : ℕ) (x : Fin T → ℝ),
          armaProfileCriterion θ1.1 θ1.2 x = armaProfileCriterion θ0.1 θ0.2 x := by
  refine ⟨(fun _ => 0, fun _ => 0), (fun _ => 1 / 2, fun _ => -(1 / 2)),
    invertible_witness_zero, invertible_witness_half, ?_, ?_, ?_⟩
  · rw [arPoly_witness_zero, maPoly_witness_zero]
    exact isCoprime_one_left
  · intro h
    have := congrFun (congrArg Prod.fst h) 0
    norm_num at this
  · intro T x
    have hacvf : armaACVF (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ : Fin 1 => (-(1 / 2) : ℝ))
        = armaACVF (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) := by
      funext k
      simp only [armaACVF, armaPsi_witness_eq]
    have hT : armaToeplitz (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ : Fin 1 => (-(1 / 2) : ℝ)) T
        = armaToeplitz (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) T := by
      ext i j
      simp only [armaToeplitz, Matrix.of_apply, hacvf]
    simp only [armaProfileCriterion, armaProfileS, hT]

end CompositeFilter

section PolyIdentifiability

/-! ### The polynomial step of identifiability

`arPoly`/`maPoly` are *normalized at the origin*: both have constant coefficient `1`.
That normalization is what turns "associated" into "equal" below: a unit of `ℝ[X]` is a
nonzero constant, and matching constant coefficients pins it to `1`. Together with
injectivity of `arPoly` (read off coefficient `i + 1`) this converts the cross equation
`b(z)a₀(z) = b₀(z)a(z)` of `armaContrastVar_eq_one_iff_transfer` into equality of the
parameter vectors, provided *both* pairs are coprime. -/

/-- The coefficients of the AR polynomial `b(z) = 1 − b₁z − ⋯ − b_p z^p`. -/
private lemma coeff_arPoly' {p : ℕ} (b : Fin p → ℝ) (m : ℕ) :
    (arPoly b).coeff m
      = (if m = 0 then (1 : ℝ) else 0) - ∑ i : Fin p, if m = (i : ℕ) + 1 then b i else 0 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

private lemma coeff_arPoly_succ' {p : ℕ} (b : Fin p → ℝ) (j : Fin p) :
    (arPoly b).coeff ((j : ℕ) + 1) = -(b j) := by
  rw [coeff_arPoly']
  simp [Fin.val_eq_val, Finset.sum_ite_eq]

/-- `arPoly` is injective: coefficient `i + 1` is `−bᵢ`. -/
private lemma arPoly_injective' {p : ℕ} :
    Function.Injective (arPoly : (Fin p → ℝ) → Polynomial ℝ) := by
  intro b b' h
  funext i
  have hc := congrArg (fun r => Polynomial.coeff r ((i : ℕ) + 1)) h
  simp only [coeff_arPoly_succ'] at hc
  linarith

/-- `maPoly` is injective (through `arPoly_neg`). -/
private lemma maPoly_injective' {q : ℕ} :
    Function.Injective (maPoly : (Fin q → ℝ) → Polynomial ℝ) := by
  intro a a' h
  rw [← arPoly_neg, ← arPoly_neg] at h
  have hneg := arPoly_injective' h
  funext j
  have := congrFun hneg j
  simpa using this

private lemma arPoly_ne_zero' {p : ℕ} (b : Fin p → ℝ) : arPoly b ≠ 0 := by
  intro h
  have h1 := coeff_arPoly_zero' b
  rw [h] at h1
  simp at h1

/-- Two polynomials with constant coefficient `1` that divide each other are **equal**:
the unit relating them is a constant, and the normalization pins that constant to `1`. -/
private lemma eq_of_dvd_dvd_of_coeff_zero_eq_one {f g : Polynomial ℝ}
    (hf : f.coeff 0 = 1) (hg : g.coeff 0 = 1) (h1 : f ∣ g) (h2 : g ∣ f) : f = g := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  have hf0 : f ≠ 0 := fun h => by rw [h] at hf; simp at hf
  have hcd : c * d = 1 := by
    have hstep : f * (c * d) = f * 1 := by
      rw [mul_one, ← mul_assoc, ← hc, ← hd]
    exact mul_left_cancel₀ hf0 hstep
  have hcu : IsUnit c := ⟨⟨c, d, hcd, by rw [mul_comm]; exact hcd⟩, rfl⟩
  have hcC : c = Polynomial.C (c.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hcu)
  have hc0 : c.coeff 0 = 1 := by
    have h0 := congrArg (fun r => Polynomial.coeff r 0) hc
    simp only [Polynomial.mul_coeff_zero, hf, hg, one_mul] at h0
    exact h0.symm
  rw [hc, hcC, hc0, map_one, mul_one]

/-- **Minimal representations are unique**: if `b(z)a₀(z) = b₀(z)a(z)` and both pairs are
coprime, then the parameter vectors coincide. This is the polynomial content of
identifiability; the analytic content is `armaContrastVar_eq_one_iff_transfer`. -/
private lemma eq_of_transfer_eq {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hcop : IsCoprime (arPoly b0) (maPoly a0)) (hcopW : IsCoprime (arPoly b) (maPoly a))
    (hT : arPoly b * maPoly a0 = arPoly b0 * maPoly a) : b = b0 ∧ a = a0 := by
  -- `b₀ ∣ b·a₀` and `b₀` is coprime to `a₀`, hence `b₀ ∣ b`; symmetrically `b ∣ b₀`.
  have hd1 : arPoly b0 ∣ arPoly b := hcop.dvd_of_dvd_mul_right ⟨maPoly a, hT⟩
  have hd2 : arPoly b ∣ arPoly b0 := hcopW.dvd_of_dvd_mul_right ⟨maPoly a0, hT.symm⟩
  -- Both are normalized at the origin, so mutual divisibility is equality.
  have hb : arPoly b = arPoly b0 :=
    eq_of_dvd_dvd_of_coeff_zero_eq_one (coeff_arPoly_zero' b) (coeff_arPoly_zero' b0) hd2 hd1
  rw [hb] at hT
  exact ⟨arPoly_injective' hb,
    (maPoly_injective' (mul_left_cancel₀ (arPoly_ne_zero' b0) hT)).symm⟩

end PolyIdentifiability

/-- The composite filter has leading coefficient `1`, so the contrast variance is at
least `1`, with equality iff the working model matches the true transfer function. -/
theorem one_le_armaContrastVar {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    1 ≤ armaContrastVar b0 a0 b a := by
  have hsum := summable_sq_contrastCoeff hB0 hB
  have h0 : contrastCoeff b0 a0 b a 0 ^ 2 ≤ ∑' n : ℕ, contrastCoeff b0 a0 b a n ^ 2 :=
    hsum.le_tsum 0 fun n _ => sq_nonneg _
  rw [armaContrastVar_eq_tsum]
  rwa [contrastCoeff_zero, one_pow] at h0

/-- **Identifiability**: contrast variance `= 1` iff the transfer functions agree,
i.e. `b(z) a₀(z) = b₀(z) a(z)`; under coprimality and equal orders, iff the
parameters agree. -/
theorem armaContrastVar_eq_one_iff {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a)
    -- USER-INPUT: coprime minimal true orders; Hannan 1973
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    -- USER-INPUT: minimality of the *working* model too. Added 2026-08-09 after a
    -- Lean witness (`armaContrastVar_eq_one_not_identifiable`: `p = q = 1`,
    -- `b₀ = a₀ = 0`, `b = 1/2`, `a = −1/2`) showed that constraining only the true
    -- pair leaves the contrast blind to common factors in the working pair — the
    -- criterion sees the transfer function alone. Hannan 1973 §2 searches over
    -- minimal models.
    (hcopW : IsCoprime (arPoly b) (maPoly a)) :
    armaContrastVar b0 a0 b a = 1 ↔ b = b0 ∧ a = a0 := by
  constructor
  · -- **Was FALSE as originally frozen** — with only the *true* pair constrained to be
    -- coprime, a non-minimal working pair with the same transfer function is a
    -- counterexample: `armaContrastVar_eq_one_not_identifiable` exhibits (in Lean)
    -- `p = q = 1`, `b₀ = a₀ = 0`, `b = 1/2`, `a = −1/2`, where both pairs are in `𝓑`,
    -- `IsCoprime (arPoly b₀) (maPoly a₀)` holds, the contrast variance is `1`, and
    -- `b ≠ b₀`. The witness is kept above as documentation. `hcopW` (minimality of the
    -- *working* model, Hannan 1973 §2) excludes it, and then the criterion's
    -- transfer-function reading plus the polynomial step close the branch.
    intro h
    exact eq_of_transfer_eq hcop hcopW ((armaContrastVar_eq_one_iff_transfer hB0 hB).1 h)
  · rintro ⟨rfl, rfl⟩
    exact (armaContrastVar_eq_one_iff_transfer hB0 hB).2 rfl

/-! ### Continuity of the contrast in the working parameter, and the uniform gap -/

private lemma maPoly_conv_armaPi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (maPoly a).coeff k * armaPi b a (n - k)
      = (arPoly b).coeff n := by
  have h := arPoly_conv_armaPsi (fun j => -a j) (fun i => -b i) n
  rw [arPoly_neg, maPoly_neg] at h
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => by rw [armaPi_eq_armaPsi]

private lemma coeff_maPoly' {q : ℕ} (a : Fin q → ℝ) (m : ℕ) :
    (maPoly a).coeff m
      = (if m = 0 then (1 : ℝ) else 0) + ∑ j : Fin q, if m = (j : ℕ) + 1 then a j else 0 := by
  simp [maPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow, Polynomial.coeff_one]

private lemma continuous_coeff_maPoly {q : ℕ} (m : ℕ) :
    Continuous fun a : Fin q → ℝ => (maPoly a).coeff m := by
  simp only [coeff_maPoly']
  refine continuous_const.add (continuous_finset_sum _ fun j _ => ?_)
  by_cases h : m = (j : ℕ) + 1
  · simpa [h] using (continuous_apply j)
  · simpa [h] using continuous_const

private lemma continuous_coeff_arPoly {p : ℕ} (m : ℕ) :
    Continuous fun b : Fin p → ℝ => (arPoly b).coeff m := by
  simp only [coeff_arPoly']
  refine continuous_const.sub (continuous_finset_sum _ fun i _ => ?_)
  by_cases h : m = (i : ℕ) + 1
  · simpa [h] using (continuous_apply i)
  · simpa [h] using continuous_const

/-- Each inversion coefficient is a polynomial — in particular continuous — function of
the parameters (`a(0) = 1` makes the recursion explicit). -/
private lemma continuous_armaPi {p q : ℕ} (n : ℕ) :
    Continuous fun ba : (Fin p → ℝ) × (Fin q → ℝ) => armaPi ba.1 ba.2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hrec : ∀ ba : (Fin p → ℝ) × (Fin q → ℝ), armaPi ba.1 ba.2 n
        = (arPoly ba.1).coeff n
          - ∑ i ∈ Finset.range n, (maPoly ba.2).coeff (i + 1) * armaPi ba.1 ba.2 (n - (i + 1)) := by
      intro ba
      have h := maPoly_conv_armaPi ba.1 ba.2 n
      rw [Finset.sum_range_succ', coeff_maPoly_zero', one_mul, Nat.sub_zero] at h
      linarith
    simp only [hrec]
    refine (continuous_coeff_arPoly n).comp continuous_fst |>.sub
      (continuous_finset_sum _ fun i hi => ?_)
    have hi' : i < n := Finset.mem_range.1 hi
    exact ((continuous_coeff_maPoly (i + 1)).comp continuous_snd).mul (ih _ (by omega))

private lemma continuous_contrastCoeff {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ) (n : ℕ) :
    Continuous fun ba : (Fin p → ℝ) × (Fin q → ℝ) => contrastCoeff b0 a0 ba.1 ba.2 n := by
  unfold contrastCoeff
  exact continuous_finset_sum _ fun k _ => (continuous_armaPi k).mul continuous_const

private lemma summable_geom_env (C : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => C ^ 4 * (((n : ℝ) + 1) ^ 2 * (r ^ 2) ^ n) := by
  have hr2 : ‖r ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    nlinarith
  have h0 : Summable fun n : ℕ => (r ^ 2) ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hr2
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * (r ^ 2) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr2
  have h2 : Summable fun n : ℕ => (n : ℝ) ^ 2 * (r ^ 2) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr2
  refine (((h2.add (h1.mul_left 2)).add h0).mul_left (C ^ 4)).congr fun n => ?_
  ring

/-- **Continuity of the contrast variance in the working parameter**, on a compact set of
invertible pairs. Each summand `c_n(θ)²` is a *polynomial* in the entries of `θ`
(`continuous_armaPi`), and the brick `exists_uniform_geometric_bound_arma` supplies the
uniform envelope `C⁴(n+1)²(r²)ⁿ` that `continuousOn_tsum` needs. This is the half of
`mle_consistent`(ii) that was missing. -/
private lemma continuousOn_armaContrastVar {p q : ℕ} {b0 : Fin p → ℝ} {a0 : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0)
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))} (hK : IsCompact K)
    (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2) :
    ContinuousOn (fun ba : (Fin p → ℝ) × (Fin q → ℝ) =>
      armaContrastVar b0 a0 ba.1 ba.2) K := by
  obtain ⟨C₁, r₁, hC₁, hr₁0, hr₁1, _, hπK⟩ := exists_uniform_geometric_bound_arma hK hKB
  obtain ⟨C₂, hC₂, r₂, hr₂0, hr₂1, hψ0⟩ := exists_geometric_bound_armaPsi a0 hB0.1
  obtain ⟨C, r, hC, hr0, hr1, hπ, hψ⟩ :
      ∃ C r : ℝ, 1 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
        (∀ ba ∈ K, ∀ n, |armaPi ba.1 ba.2 n| ≤ C * r ^ n) ∧
        (∀ n, |armaPsi b0 a0 n| ≤ C * r ^ n) := by
    refine ⟨max C₁ (max 1 C₂), max r₁ r₂, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans hr₁0 (le_max_left _ _), max_lt hr₁1 hr₂1, fun ba hba n => ?_, fun n => ?_⟩
    · refine (hπK ba hba n).trans (mul_le_mul (le_max_left _ _)
        (pow_le_pow_left₀ hr₁0 (le_max_left _ _) n) (by positivity) ?_)
      exact le_trans zero_le_one (le_trans (le_max_left _ _) (le_max_right _ _))
    · refine (hψ0 n).trans (mul_le_mul (le_trans (le_max_right _ _) (le_max_right _ _))
        (pow_le_pow_left₀ hr₂0 (le_max_right _ _) n) (by positivity) ?_)
      exact le_trans zero_le_one (le_trans (le_max_left _ _) (le_max_right _ _))
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  refine continuousOn_tsum (u := fun n : ℕ => C ^ 4 * (((n : ℝ) + 1) ^ 2 * (r ^ 2) ^ n))
    (fun n => ((continuous_contrastCoeff b0 a0 n).pow 2).continuousOn)
    (summable_geom_env C hr0 hr1) (fun n ba hba => ?_)
  have habs := abs_contrastCoeff_le hC hr0 (hπ ba hba) hψ n
  have hnn : 0 ≤ C ^ 2 * ((n : ℝ) + 1) * r ^ n := by positivity
  calc ‖contrastCoeff b0 a0 ba.1 ba.2 n ^ 2‖
      = |contrastCoeff b0 a0 ba.1 ba.2 n| ^ 2 := by
        rw [Real.norm_eq_abs, abs_pow]
    _ ≤ (C ^ 2 * ((n : ℝ) + 1) * r ^ n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = C ^ 4 * (((n : ℝ) + 1) ^ 2 * (r ^ 2) ^ n) := by
        rw [← pow_mul, mul_comm 2 n, pow_mul]; ring

/-- **The uniform contrast gap** — `mle_consistent`(ii). Away from the truth the contrast
variance is bounded away from `1` on the compact identifiable region: pointwise
strictness is `armaContrastVar_eq_one_iff`, and `continuousOn_armaContrastVar` plus
compactness of `K ∩ {dist · θ₀ ≥ δ}` turn it into a uniform gap. -/
private lemma exists_contrast_gap {p q : ℕ} {b0 : Fin p → ℝ} {a0 : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hcop : IsCoprime (arPoly b0) (maPoly a0))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))} (hK : IsCompact K)
    (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
    (hcopK : ∀ ba ∈ K, IsCoprime (arPoly ba.1) (maPoly ba.2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ ba ∈ K, δ ≤ dist ba (b0, a0) →
      1 + γ ≤ armaContrastVar b0 a0 ba.1 ba.2 := by
  classical
  have hScl : IsCompact (K ∩ {ba : (Fin p → ℝ) × (Fin q → ℝ) | δ ≤ dist ba (b0, a0)}) :=
    hK.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  rcases Set.eq_empty_or_nonempty
      (K ∩ {ba : (Fin p → ℝ) × (Fin q → ℝ) | δ ≤ dist ba (b0, a0)}) with hemp | hne
  · refine ⟨1, one_pos, fun ba hba hd => ?_⟩
    exact absurd (Set.mem_inter hba hd) (by rw [hemp]; exact Set.notMem_empty _)
  · obtain ⟨ba0, hba0, hmin⟩ := hScl.exists_isMinOn hne
      ((continuousOn_armaContrastVar hB0 hK hKB).mono Set.inter_subset_left)
    have hgt : 1 < armaContrastVar b0 a0 ba0.1 ba0.2 := by
      rcases lt_or_eq_of_le (one_le_armaContrastVar hB0 (hKB ba0 hba0.1)) with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨hb, ha⟩ := (armaContrastVar_eq_one_iff hB0 (hKB ba0 hba0.1) hcop
          (hcopK ba0 hba0.1)).1 h1.symm
        have hzero : ba0 = (b0, a0) := Prod.ext hb ha
        have hd := hba0.2
        rw [Set.mem_setOf_eq, hzero, dist_self] at hd
        linarith
    refine ⟨armaContrastVar b0 a0 ba0.1 ba0.2 - 1, by linarith, fun ba hba hd => ?_⟩
    have hle := hmin (Set.mem_inter hba hd)
    simp only [Set.mem_setOf_eq] at hle
    linarith



/-- **The `ℓ¹` modulus of continuity of the inversion filter on a compact set** — the
deterministic first input of the stochastic-equicontinuity estimate `mle_consistent`(iii).

Each `π_n` is a polynomial in the parameters (`continuous_armaPi`) and the brick
`exists_uniform_geometric_bound_arma` supplies the uniform envelope `2C rⁿ`, so
`(θ, θ') ↦ Σ_n |π_n(θ) − π_n(θ')|` is continuous on the compact `K × K` and vanishes on
the diagonal; the modulus is then the minimal distance on the (compact) super-level set. -/
lemma exists_armaPi_l1_modulus {p q : ℕ}
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))} (hK : IsCompact K)
    (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ba ∈ K, ∀ ba' ∈ K, dist ba ba' < ρ →
      ∑' n : ℕ, |armaPi ba.1 ba.2 n - armaPi ba'.1 ba'.2 n| < ε := by
  classical
  obtain ⟨C, r, hC, hr0, hr1, _, hπK⟩ := exists_uniform_geometric_bound_arma hK hKB
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hgeom : Summable fun n : ℕ => 2 * C * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left (2 * C)
  have hFcont : ContinuousOn (fun z : ((Fin p → ℝ) × (Fin q → ℝ)) ×
      ((Fin p → ℝ) × (Fin q → ℝ)) =>
        ∑' n : ℕ, |armaPi z.1.1 z.1.2 n - armaPi z.2.1 z.2.2 n|) (K ×ˢ K) := by
    refine continuousOn_tsum (u := fun n : ℕ => 2 * C * r ^ n)
      (fun n => (((continuous_armaPi n).comp continuous_fst).sub
        ((continuous_armaPi n).comp continuous_snd)).abs.continuousOn) hgeom
      (fun n z hz => ?_)
    have h1 := hπK z.1 hz.1 n
    have h2 := hπK z.2 hz.2 n
    have habs : |armaPi z.1.1 z.1.2 n - armaPi z.2.1 z.2.2 n|
        ≤ |armaPi z.1.1 z.1.2 n| + |armaPi z.2.1 z.2.2 n| := abs_sub _ _
    rw [Real.norm_eq_abs, abs_abs]
    linarith
  haveI : CompactSpace ↥(K ×ˢ K) := isCompact_iff_compactSpace.1 (hK.prod hK)
  obtain ⟨F, hF⟩ : ∃ F : ↥(K ×ˢ K) → ℝ, F = (K ×ˢ K).restrict
      (fun z : ((Fin p → ℝ) × (Fin q → ℝ)) × ((Fin p → ℝ) × (Fin q → ℝ)) =>
        ∑' n : ℕ, |armaPi z.1.1 z.1.2 n - armaPi z.2.1 z.2.2 n|) := ⟨_, rfl⟩
  have hFc : Continuous F := by
    rw [hF]; exact continuousOn_iff_continuous_restrict.1 hFcont
  have hdc : Continuous fun s : ↥(K ×ˢ K) => dist s.1.1 s.1.2 :=
    (continuous_fst.comp continuous_subtype_val).dist
      (continuous_snd.comp continuous_subtype_val)
  have hAcl : IsClosed {s : ↥(K ×ˢ K) | ε ≤ F s} := isClosed_le continuous_const hFc
  rcases Set.eq_empty_or_nonempty {s : ↥(K ×ˢ K) | ε ≤ F s} with hemp | hAne
  · refine ⟨1, one_pos, fun ba hba ba' hba' _ => ?_⟩
    by_contra hcon
    have : (⟨(ba, ba'), Set.mk_mem_prod hba hba'⟩ : ↥(K ×ˢ K)) ∈ {s | ε ≤ F s} := by
      simpa [hF, Set.restrict_apply] using! not_lt.1 hcon
    rw [hemp] at this
    exact this
  · obtain ⟨s0, hs0, hmin⟩ := hAcl.isCompact.exists_isMinOn hAne hdc.continuousOn
    have hpos : 0 < dist s0.1.1 s0.1.2 := by
      rcases (dist_nonneg (x := s0.1.1) (y := s0.1.2)).lt_or_eq with h | h
      · exact h
      · exfalso
        have heq : s0.1.1 = s0.1.2 := dist_eq_zero.1 h.symm
        have hzero : F s0 = 0 := by
          rw [hF]
          show ∑' n : ℕ, |armaPi s0.1.1.1 s0.1.1.2 n - armaPi s0.1.2.1 s0.1.2.2 n| = 0
          rw [heq]
          simp
        have := hs0
        simp only [Set.mem_setOf_eq, hzero] at this
        linarith
    refine ⟨dist s0.1.1 s0.1.2, hpos, fun ba hba ba' hba' hd => ?_⟩
    by_contra hcon
    have hmemA : (⟨(ba, ba'), Set.mk_mem_prod hba hba'⟩ : ↥(K ×ˢ K)) ∈ {s | ε ≤ F s} := by
      simpa [hF, Set.restrict_apply] using! not_lt.1 hcon
    have hge := hmin hmemA
    simp only [Set.mem_setOf_eq] at hge
    linarith

/-! ### From the modulus to a Lipschitz bound

The modulus above is what `mle_consistent` needs; the residual-correlogram claim of
`ARMA/Diagnostics.lean` needs the *quantitative* form, because it must convert an
`o_p(T^{−1/2})` parameter error into an `o_p(T^{−1/2})` filter error — a modulus only
delivers `o_p(1)`, one full factor of `√T` short (the point recorded at that file's
residue (B)). The route is the **resolvent identity** rather than derivatives: with
`A = a(z)`, `B = b(z)` and `π = B/A`,

  `π − π′ = ((B − B′) + (A′ − A)·π′) · A⁻¹`,

so the `ℓ¹` (Banach-algebra) bound gives
`‖π − π′‖₁ ≤ (‖B − B′‖₁ + ‖A′ − A‖₁‖π′‖₁)·‖A⁻¹‖₁`. The two polynomial differences are
finitely supported with coefficients the parameter differences, and `‖π′‖₁`, `‖A⁻¹‖₁` are
uniformly bounded on a compact set of invertible parameters by
`exists_uniform_geometric_bound_arma` (applied to `K` and to its zero-AR slice, the latter
carrying `A⁻¹ = π(0, a)`). No Cauchy estimate and no `∂π/∂θ` is needed. -/

/-- The `ℓ¹` convolution bound for formal power series (the `ℓ¹` Banach-algebra
inequality, coefficientwise). -/
private lemma tsum_abs_coeff_mul_le (φ ψ : PowerSeries ℝ)
    (hφ : Summable fun n => |PowerSeries.coeff n φ|)
    (hψ : Summable fun n => |PowerSeries.coeff n ψ|) :
    (Summable fun n => |PowerSeries.coeff n (φ * ψ)|) ∧
      ∑' n, |PowerSeries.coeff n (φ * ψ)|
        ≤ (∑' n, |PowerSeries.coeff n φ|) * ∑' n, |PowerSeries.coeff n ψ| := by
  classical
  have hfn : Summable fun n => ‖|PowerSeries.coeff n φ|‖ := by
    simpa only [Real.norm_eq_abs, abs_abs] using hφ
  have hgn : Summable fun n => ‖|PowerSeries.coeff n ψ|‖ := by
    simpa only [Real.norm_eq_abs, abs_abs] using hψ
  have hWs : Summable fun n : ℕ => ∑ kl ∈ Finset.antidiagonal n,
      |PowerSeries.coeff kl.1 φ| * |PowerSeries.coeff kl.2 ψ| := by
    have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn
    refine h.of_nonneg_of_le (fun n => Finset.sum_nonneg fun kl _ => by positivity) fun n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun kl _ => by positivity)]
  have hsum : ((∑' n, |PowerSeries.coeff n φ|) * ∑' n, |PowerSeries.coeff n ψ|)
      = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n,
          |PowerSeries.coeff kl.1 φ| * |PowerSeries.coeff kl.2 ψ| :=
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  have hle : ∀ n : ℕ, |PowerSeries.coeff n (φ * ψ)|
      ≤ ∑ kl ∈ Finset.antidiagonal n,
          |PowerSeries.coeff kl.1 φ| * |PowerSeries.coeff kl.2 ψ| := by
    intro n
    rw [PowerSeries.coeff_mul]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun kl _ => ?_)
    rw [abs_mul]
  have hsummable : Summable fun n => |PowerSeries.coeff n (φ * ψ)| :=
    hWs.of_nonneg_of_le (fun n => abs_nonneg _) hle
  exact ⟨hsummable, by rw [hsum]; exact hsummable.tsum_le_tsum hle hWs⟩

/-- The **resolvent identity** for the inversion filters: with `A = a(z)`, `B = b(z)`,
`π = B/A`, one has `π − π' = ((B − B') + (A' − A)·π')·A⁻¹`. -/
private lemma armaPi_series_sub {p q : ℕ} (b b' : Fin p → ℝ) (a a' : Fin q → ℝ)
    (hA : PowerSeries.constantCoeff (R := ℝ) ((maPoly a : Polynomial ℝ) : PowerSeries ℝ) ≠ 0)
    (hA' : PowerSeries.constantCoeff (R := ℝ) ((maPoly a' : Polynomial ℝ) : PowerSeries ℝ) ≠ 0) :
    ((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
        (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹
      - ((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
        (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹
      = ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
            - ((arPoly b' : Polynomial ℝ) : PowerSeries ℝ))
          + (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ)
              - ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
            (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
              (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹))
        * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹ := by
  have e1 : (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
      (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hA
  have e2 : (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ)) *
      (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hA'
  linear_combination (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
      (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹) * e1
    - (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
      (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹) * e2

private lemma constantCoeff_maPoly_ne {q : ℕ} (a : Fin q → ℝ) :
    PowerSeries.constantCoeff (R := ℝ) ((maPoly a : Polynomial ℝ) : PowerSeries ℝ) ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe]
  simp [maPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

private lemma coeff_inv_maPoly (p : ℕ) {q : ℕ} (a : Fin q → ℝ) (n : ℕ) :
    PowerSeries.coeff n ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = armaPi (fun _ : Fin p => (0 : ℝ)) a n := by
  unfold armaPi
  have h : arPoly (fun _ : Fin p => (0 : ℝ)) = 1 := by simp [arPoly]
  rw [h]
  simp

/-- The `ℓ¹` norm of the AR-polynomial difference is controlled by the parameter
distance: crude constant `(p+1)·p`, which is all a Lipschitz statement needs. -/
private lemma l1_arPoly_sub {p : ℕ} (b b' : Fin p → ℝ) :
    (Summable fun n : ℕ => |(arPoly b).coeff n - (arPoly b').coeff n|) ∧
      ∑' n : ℕ, |(arPoly b).coeff n - (arPoly b').coeff n|
        ≤ ((p : ℝ) + 1) * ∑ i : Fin p, |b i - b' i| := by
  classical
  have hcoeff : ∀ n : ℕ, (arPoly b).coeff n - (arPoly b').coeff n
      = -∑ i : Fin p, (if n = (i : ℕ) + 1 then b i - b' i else 0) := by
    intro n
    rw [coeff_arPoly', coeff_arPoly']
    have : ∑ i : Fin p, (if n = (i : ℕ) + 1 then b i - b' i else 0)
        = (∑ i : Fin p, if n = (i : ℕ) + 1 then b i else 0)
          - ∑ i : Fin p, if n = (i : ℕ) + 1 then b' i else 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by by_cases h : n = (i : ℕ) + 1 <;> simp [h]
    rw [this]
    ring
  have hbd : ∀ n : ℕ, |(arPoly b).coeff n - (arPoly b').coeff n| ≤ ∑ i : Fin p, |b i - b' i| := by
    intro n
    rw [hcoeff n, abs_neg]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    by_cases h : n = (i : ℕ) + 1 <;> simp [h, abs_nonneg]
  have hzero : ∀ n ∉ Finset.range (p + 1),
      |(arPoly b).coeff n - (arPoly b').coeff n| = 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [hcoeff n]
    have : ∀ i : Fin p, (if n = (i : ℕ) + 1 then b i - b' i else 0) = 0 := by
      intro i
      have hne : n ≠ (i : ℕ) + 1 := by
        have := i.isLt
        omega
      simp [hne]
    simp [this]
  have hsummable : Summable fun n : ℕ => |(arPoly b).coeff n - (arPoly b').coeff n| :=
    summable_of_ne_finset_zero hzero
  refine ⟨hsummable, ?_⟩
  rw [tsum_eq_sum hzero]
  refine le_trans (Finset.sum_le_sum fun n _ => hbd n) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  exact le_rfl

private lemma l1_maPoly_sub {q : ℕ} (a a' : Fin q → ℝ) :
    (Summable fun n : ℕ => |(maPoly a').coeff n - (maPoly a).coeff n|) ∧
      ∑' n : ℕ, |(maPoly a').coeff n - (maPoly a).coeff n|
        ≤ ((q : ℝ) + 1) * ∑ j : Fin q, |a j - a' j| := by
  classical
  have hcoeff : ∀ n : ℕ, (maPoly a').coeff n - (maPoly a).coeff n
      = ∑ j : Fin q, (if n = (j : ℕ) + 1 then a' j - a j else 0) := by
    intro n
    rw [coeff_maPoly', coeff_maPoly']
    have : ∑ j : Fin q, (if n = (j : ℕ) + 1 then a' j - a j else 0)
        = (∑ j : Fin q, if n = (j : ℕ) + 1 then a' j else 0)
          - ∑ j : Fin q, if n = (j : ℕ) + 1 then a j else 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by by_cases h : n = (j : ℕ) + 1 <;> simp [h]
    rw [this]
    ring
  have hbd : ∀ n : ℕ, |(maPoly a').coeff n - (maPoly a).coeff n|
      ≤ ∑ j : Fin q, |a j - a' j| := by
    intro n
    rw [hcoeff n]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    by_cases h : n = (j : ℕ) + 1
    · simp only [h, if_pos]
      rw [abs_sub_comm]
    · simp [h, abs_nonneg]
  have hzero : ∀ n ∉ Finset.range (q + 1),
      |(maPoly a').coeff n - (maPoly a).coeff n| = 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [hcoeff n]
    have : ∀ j : Fin q, (if n = (j : ℕ) + 1 then a' j - a j else 0) = 0 := by
      intro j
      have hne : n ≠ (j : ℕ) + 1 := by
        have := j.isLt
        omega
      simp [hne]
    simp [this]
  have hsummable : Summable fun n : ℕ => |(maPoly a').coeff n - (maPoly a).coeff n| :=
    summable_of_ne_finset_zero hzero
  refine ⟨hsummable, ?_⟩
  rw [tsum_eq_sum hzero]
  refine le_trans (Finset.sum_le_sum fun n _ => hbd n) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  exact le_rfl


/-- **The `ℓ¹` Lipschitz bound for the inversion filter** on a compact set of invertible
parameters — the quantitative upgrade of `exists_armaPi_l1_modulus`. -/
theorem exists_armaPi_l1_lipschitz {p q : ℕ}
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))} (hK : IsCompact K)
    (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ba ∈ K, ∀ ba' ∈ K,
      ∑' n : ℕ, |armaPi ba.1 ba.2 n - armaPi ba'.1 ba'.2 n| ≤ L * dist ba ba' := by
  classical
  obtain ⟨C₁, r₁, hC₁, hr₁0, hr₁1, _, hπK⟩ := exists_uniform_geometric_bound_arma hK hKB
  have hK₀ : IsCompact ((fun ba : (Fin p → ℝ) × (Fin q → ℝ) => ((0 : Fin p → ℝ), ba.2)) '' K) :=
    hK.image (by fun_prop)
  have hK₀B : ∀ ba ∈ (fun ba : (Fin p → ℝ) × (Fin q → ℝ) => ((0 : Fin p → ℝ), ba.2)) '' K,
      ARMAInvertibleParams ba.1 ba.2 := by
    rintro _ ⟨ba, hba, rfl⟩
    exact ⟨fun z _ => by simp [arPoly], (hKB ba hba).2⟩
  obtain ⟨C₂, r₂, hC₂, hr₂0, hr₂1, _, hπK₀⟩ := exists_uniform_geometric_bound_arma hK₀ hK₀B
  -- one envelope for both filters
  obtain ⟨C, r, hC, hr0, hr1, hb1, hb2⟩ : ∃ C r : ℝ, 1 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
      (∀ ba ∈ K, ∀ n, |armaPi ba.1 ba.2 n| ≤ C * r ^ n) ∧
      (∀ ba ∈ K, ∀ n, |armaPi (fun _ : Fin p => (0 : ℝ)) ba.2 n| ≤ C * r ^ n) := by
    refine ⟨max C₁ C₂, max r₁ r₂, le_trans hC₁ (le_max_left _ _),
      le_trans hr₁0 (le_max_left _ _), max_lt hr₁1 hr₂1, fun ba hba n => ?_, fun ba hba n => ?_⟩
    · exact (hπK ba hba n).trans (mul_le_mul (le_max_left _ _)
        (pow_le_pow_left₀ hr₁0 (le_max_left _ _) n) (by positivity)
        (le_trans zero_le_one (le_trans hC₁ (le_max_left _ _))))
    · exact (hπK₀ _ ⟨ba, hba, rfl⟩ n).trans (mul_le_mul (le_max_right _ _)
        (pow_le_pow_left₀ hr₂0 (le_max_right _ _) n) (by positivity)
        (le_trans zero_le_one (le_trans hC₁ (le_max_left _ _))))
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hMnn : (0 : ℝ) ≤ C / (1 - r) := by
    have : (0 : ℝ) < 1 - r := by linarith
    positivity
  have hgeo : ∀ f : ℕ → ℝ, (∀ n, |f n| ≤ C * r ^ n) →
      (Summable fun n => |f n|) ∧ ∑' n, |f n| ≤ C / (1 - r) := by
    intro f hf
    have hgs : Summable fun n : ℕ => C * r ^ n :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left C
    have hsummable : Summable fun n => |f n| :=
      hgs.of_nonneg_of_le (fun n => abs_nonneg _) hf
    refine ⟨hsummable, ?_⟩
    have hle := hsummable.tsum_le_tsum hf hgs
    rwa [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, ← div_eq_mul_inv] at hle
  refine ⟨(C / (1 - r)) * (((p : ℝ) + 1) * (p : ℝ)
      + ((q : ℝ) + 1) * (q : ℝ) * (C / (1 - r))), by positivity, ?_⟩
  intro ba hba ba' hba'
  obtain ⟨b, a⟩ := ba
  obtain ⟨b', a'⟩ := ba'
  simp only at *
  -- the parameter distance dominates every coordinate difference
  have hd0 : (0 : ℝ) ≤ dist (b, a) (b', a') := dist_nonneg
  have hbd : ∑ i : Fin p, |b i - b' i| ≤ (p : ℝ) * dist (b, a) (b', a') := by
    have hterm : ∀ i : Fin p, |b i - b' i| ≤ dist (b, a) (b', a') := by
      intro i
      have h1 : |b i - b' i| = dist (b i) (b' i) := (Real.dist_eq _ _).symm
      rw [h1]
      exact le_trans (dist_le_pi_dist b b' i) (le_max_left _ _)
    calc ∑ i : Fin p, |b i - b' i| ≤ ∑ _i : Fin p, dist (b, a) (b', a') :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (p : ℝ) * dist (b, a) (b', a') := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have had : ∑ j : Fin q, |a j - a' j| ≤ (q : ℝ) * dist (b, a) (b', a') := by
    have hterm : ∀ j : Fin q, |a j - a' j| ≤ dist (b, a) (b', a') := by
      intro j
      have h1 : |a j - a' j| = dist (a j) (a' j) := (Real.dist_eq _ _).symm
      rw [h1]
      exact le_trans (dist_le_pi_dist a a' j) (le_max_right _ _)
    calc ∑ j : Fin q, |a j - a' j| ≤ ∑ _j : Fin q, dist (b, a) (b', a') :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = (q : ℝ) * dist (b, a) (b', a') := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the resolvent identity, coefficientwise
  have hid := armaPi_series_sub b b' a a' (constantCoeff_maPoly_ne a) (constantCoeff_maPoly_ne a')
  have hcoeffD : ∀ n : ℕ, armaPi b a n - armaPi b' a' n
      = PowerSeries.coeff n
        (((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
              - ((arPoly b' : Polynomial ℝ) : PowerSeries ℝ))
            + (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ)
                - ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
              (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
                (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹))
          * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹) := by
    intro n
    rw [← hid, map_sub]
    rfl
  -- the four `ℓ¹` inputs
  obtain ⟨hs1, hb1'⟩ := l1_arPoly_sub b b'
  obtain ⟨hs2, hb2'⟩ := l1_maPoly_sub a a'
  obtain ⟨hs3, hb3⟩ := hgeo (fun n => armaPi b' a' n) (hb1 (b', a') hba')
  obtain ⟨hs4, hb4⟩ := hgeo (fun n => armaPi (fun _ : Fin p => (0 : ℝ)) a n) (hb2 (b, a) hba)
  have hcR1 : ∀ n : ℕ, PowerSeries.coeff n
      (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
        - ((arPoly b' : Polynomial ℝ) : PowerSeries ℝ))
      = (arPoly b).coeff n - (arPoly b').coeff n := by
    intro n; rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe]
  have hcA : ∀ n : ℕ, PowerSeries.coeff n
      (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ)
        - ((maPoly a : Polynomial ℝ) : PowerSeries ℝ))
      = (maPoly a').coeff n - (maPoly a).coeff n := by
    intro n; rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe]
  have hcPi : ∀ n : ℕ, PowerSeries.coeff n
      (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
        (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹) = armaPi b' a' n := fun n => rfl
  have hcP : ∀ n : ℕ, PowerSeries.coeff n ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = armaPi (fun _ : Fin p => (0 : ℝ)) a n := coeff_inv_maPoly p a
  -- `‖(A' − A)·π'‖₁ ≤ ‖A' − A‖₁ ‖π'‖₁`
  obtain ⟨hs5, hb5⟩ := tsum_abs_coeff_mul_le
    (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ)
      - ((maPoly a : Polynomial ℝ) : PowerSeries ℝ))
    (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
      (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
    (by simpa only [hcA] using hs2) (by simpa only [hcPi] using hs3)
  -- the sum `R = (B − B') + (A' − A)π'`
  have hcR : ∀ n : ℕ, PowerSeries.coeff n
      ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
          - ((arPoly b' : Polynomial ℝ) : PowerSeries ℝ))
        + (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ)
            - ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
          (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
            (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹))
      = PowerSeries.coeff n
          (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
            - ((arPoly b' : Polynomial ℝ) : PowerSeries ℝ))
        + PowerSeries.coeff n
          ((((maPoly a' : Polynomial ℝ) : PowerSeries ℝ)
              - ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
            (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
              (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹)) := fun n => map_add _ _ _
  have hsR : Summable fun n : ℕ => |PowerSeries.coeff n
      ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
          - ((arPoly b' : Polynomial ℝ) : PowerSeries ℝ))
        + (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ)
            - ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
          (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
            (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹))| := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      (((by simpa only [hcR1] using hs1 : Summable fun n : ℕ => |PowerSeries.coeff n
        (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
          - ((arPoly b' : Polynomial ℝ) : PowerSeries ℝ))|)).add hs5)
    rw [hcR n]
    exact abs_add_le _ _
  have hbR : ∑' n : ℕ, |PowerSeries.coeff n
      ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
          - ((arPoly b' : Polynomial ℝ) : PowerSeries ℝ))
        + (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ)
            - ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
          (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
            (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹))|
      ≤ ((p : ℝ) + 1) * ((p : ℝ) * dist (b, a) (b', a'))
        + ((q : ℝ) + 1) * ((q : ℝ) * dist (b, a) (b', a')) * (C / (1 - r)) := by
    have hs1' : Summable fun n : ℕ => |PowerSeries.coeff n
        (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
          - ((arPoly b' : Polynomial ℝ) : PowerSeries ℝ))| := by simpa only [hcR1] using hs1
    have hstep := hsR.tsum_le_tsum (fun n => by rw [hcR n]; exact abs_add_le _ _) (hs1'.add hs5)
    rw [hs1'.tsum_add hs5] at hstep
    have hpart1 : ∑' n : ℕ, |PowerSeries.coeff n
        (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
          - ((arPoly b' : Polynomial ℝ) : PowerSeries ℝ))|
        ≤ ((p : ℝ) + 1) * ((p : ℝ) * dist (b, a) (b', a')) := by
      have h := hb1'
      simp only [hcR1]
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left hbd (by positivity)
    have hpart2 : ∑' n : ℕ, |PowerSeries.coeff n
        ((((maPoly a' : Polynomial ℝ) : PowerSeries ℝ)
            - ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
          (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
            (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹))|
        ≤ ((q : ℝ) + 1) * ((q : ℝ) * dist (b, a) (b', a')) * (C / (1 - r)) := by
      refine le_trans hb5 ?_
      have hA1 : ∑' n : ℕ, |PowerSeries.coeff n
          (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ)
            - ((maPoly a : Polynomial ℝ) : PowerSeries ℝ))|
          ≤ ((q : ℝ) + 1) * ((q : ℝ) * dist (b, a) (b', a')) := by
        simp only [hcA]
        exact le_trans hb2' (mul_le_mul_of_nonneg_left had (by positivity))
      have hA2 : ∑' n : ℕ, |PowerSeries.coeff n
          (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
            (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹)| ≤ C / (1 - r) := by
        simpa only [hcPi] using hb3
      have hnn1 : (0 : ℝ) ≤ ∑' n : ℕ, |PowerSeries.coeff n
          (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
            (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹)| :=
        tsum_nonneg fun n => abs_nonneg _
      have hnn2 : (0 : ℝ) ≤ ((q : ℝ) + 1) * ((q : ℝ) * dist (b, a) (b', a')) := by positivity
      calc _ ≤ (((q : ℝ) + 1) * ((q : ℝ) * dist (b, a) (b', a'))) *
              ∑' n : ℕ, |PowerSeries.coeff n
                (((arPoly b' : Polynomial ℝ) : PowerSeries ℝ) *
                  (((maPoly a' : Polynomial ℝ) : PowerSeries ℝ))⁻¹)| :=
            mul_le_mul_of_nonneg_right hA1 hnn1
        _ ≤ _ := mul_le_mul_of_nonneg_left hA2 hnn2
    linarith
  -- multiply by `A⁻¹`
  obtain ⟨_, hb6⟩ := tsum_abs_coeff_mul_le _
    ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹) hsR (by simpa only [hcP] using hs4)
  simp only [hcoeffD]
  refine le_trans hb6 ?_
  have hPle : ∑' n : ℕ, |PowerSeries.coeff n
      ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)| ≤ C / (1 - r) := by
    simpa only [hcP] using hb4
  have hnnR : (0 : ℝ) ≤ ((p : ℝ) + 1) * ((p : ℝ) * dist (b, a) (b', a'))
      + ((q : ℝ) + 1) * ((q : ℝ) * dist (b, a) (b', a')) * (C / (1 - r)) := by positivity
  have hnnP : (0 : ℝ) ≤ ∑' n : ℕ, |PowerSeries.coeff n
      ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)| := tsum_nonneg fun n => abs_nonneg _
  calc _ ≤ (((p : ℝ) + 1) * ((p : ℝ) * dist (b, a) (b', a'))
            + ((q : ℝ) + 1) * ((q : ℝ) * dist (b, a) (b', a')) * (C / (1 - r)))
          * ∑' n : ℕ, |PowerSeries.coeff n
              ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)| :=
        mul_le_mul_of_nonneg_right (by linarith [hbR]) hnnP
    _ ≤ (((p : ℝ) + 1) * ((p : ℝ) * dist (b, a) (b', a'))
            + ((q : ℝ) + 1) * ((q : ℝ) * dist (b, a) (b', a')) * (C / (1 - r)))
          * (C / (1 - r)) := mul_le_mul_of_nonneg_left hPle hnnR
    _ = (C / (1 - r)) * (((p : ℝ) + 1) * (p : ℝ)
          + ((q : ℝ) + 1) * (q : ℝ) * (C / (1 - r))) * dist (b, a) (b', a') := by ring


section Szego

/-! ### The Szegő-type limit `T⁻¹ log det Γ_T → 0`

The route avoids the innovations recursion entirely. With `ψ̃(m, s) = ψ_{m−s} 1{s ≤ m}`
the Cholesky-type kernel of the model ACVF (`Γ_{st} = Σ_m ψ̃(m,s) ψ̃(m,t)`) and
`π̃(i, k) = π_{k−i} 1{i ≤ k}` the (upper-triangular, unit-diagonal, determinant-one)
inversion matrix, the whitened matrix `N_T = Π_T Γ_T Π_Tᵀ` has entries
`N_{ij} = Σ_m u_i(m) u_j(m)` with `u_i(m) = Σ_{k<T} π̃(i,k) ψ̃(m,k)`. The convolution
identity `π ∗ ψ = δ` makes `u_i(m) = 1{i = m}` for every `m < T`, so

  `N_T = 1 + G_T`,  `G_{ij} = Σ_{m ≥ T} u_i(m) u_j(m)`,

with `G_T` positive semidefinite and — this is the whole point — of *bounded trace*:
`|u_i(m)| ≤ C²(T − i) r^{m−i}` gives `tr G_T ≤ C⁴ Σ_{d ≥ 1} d² r^{2d}/(1 − r²) =: K`
uniformly in `T`. Since `det Γ_T = det N_T = ∏(1 + λ_j(G_T))`,

  `0 ≤ log det Γ_T ≤ Σ_j λ_j(G_T) = tr G_T ≤ K`,

which is `O(1)`, not merely `O(T)`: dividing by `T` gives the limit. -/

open Matrix

variable {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}

/-- The **one-sided transfer kernel** `ψ̃(m, s) = ψ_{m−s} 1{s ≤ m}` (the lower-triangular
unit-diagonal Cholesky-type factor of the model ACVF). -/
private noncomputable def psiK (b : Fin p → ℝ) (a : Fin q → ℝ) (m s : ℕ) : ℝ :=
  if s ≤ m then armaPsi b a (m - s) else 0

/-- The **one-sided inversion kernel** `π̃(i, k) = π_{k−i} 1{i ≤ k}`. -/
noncomputable def piK (b : Fin p → ℝ) (a : Fin q → ℝ) (i k : ℕ) : ℝ :=
  if i ≤ k then armaPi b a (k - i) else 0

private lemma psiK_eq_zero (b : Fin p → ℝ) (a : Fin q → ℝ) {m s : ℕ} (h : m < s) :
    psiK b a m s = 0 := by
  simp [psiK, Nat.not_le.2 h]

private lemma piK_eq_zero (b : Fin p → ℝ) (a : Fin q → ℝ) {i k : ℕ} (h : k < i) :
    piK b a i k = 0 := by
  simp [piK, Nat.not_le.2 h]

private lemma piK_self (b : Fin p → ℝ) (a : Fin q → ℝ) (i : ℕ) : piK b a i i = 1 := by
  simp [piK, armaPi_zero]

/-- **The convolution identity `π ∗ ψ = δ`** (the two power series are inverse). -/
lemma armaPi_conv_armaPsi (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), armaPi b a k * armaPsi b a (n - k)
      = if n = 0 then 1 else 0 := by
  have hAne : PowerSeries.constantCoeff (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_maPoly_zero']
    exact one_ne_zero
  have hBne : PowerSeries.constantCoeff (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_arPoly_zero']
    exact one_ne_zero
  have key : ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
        ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
      (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))) *
        ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) = 1 := by
    calc ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
          ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
        (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))) *
          ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
        = ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
          ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) := by ring
      _ = 1 := by
          rw [PowerSeries.mul_inv_cancel _ hAne, PowerSeries.mul_inv_cancel _ hBne, mul_one]
  have hc := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_one] at hc
  exact hc

/-- The filtered kernel `u_i(m) = Σ_{k<T} π̃(i,k) ψ̃(m,k)`: the rows of `Π_T Ψ̃`. -/
private noncomputable def uSeq (b : Fin p → ℝ) (a : Fin q → ℝ) (T i m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range T, piK b a i k * psiK b a m k

/-- **Whitening below the horizon**: for `m < T` the filtered kernel is `1{i = m}` —
this is the convolution identity `π ∗ ψ = δ`, and it is what makes `Π Γ Πᵀ − 1` a
*tail* Gram matrix. -/
private lemma uSeq_eq_of_lt (b : Fin p → ℝ) (a : Fin q → ℝ) {T i m : ℕ} (hm : m < T) :
    uSeq b a T i m = if i = m then 1 else 0 := by
  have hsub : Finset.range (m + 1) ⊆ Finset.range T := Finset.range_mono hm
  have hrestrict : uSeq b a T i m
      = ∑ k ∈ Finset.range (m + 1), piK b a i k * psiK b a m k := by
    refine (Finset.sum_subset hsub ?_).symm
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [psiK_eq_zero b a (by omega), mul_zero]
  have hpsi : ∑ k ∈ Finset.range (m + 1), piK b a i k * psiK b a m k
      = ∑ k ∈ Finset.range (m + 1), piK b a i k * armaPsi b a (m - k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [psiK, if_pos (by omega)]
  rw [hrestrict, hpsi]
  by_cases him : i ≤ m
  · have hzero : ∑ k ∈ Finset.Ico 0 i, piK b a i k * armaPsi b a (m - k) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [piK_eq_zero b a hk.2, zero_mul]
    have hsplit : ∑ k ∈ Finset.range (m + 1), piK b a i k * armaPsi b a (m - k)
        = ∑ k ∈ Finset.Ico i (m + 1), piK b a i k * armaPsi b a (m - k) := by
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun k => piK b a i k * armaPsi b a (m - k))
          (Nat.zero_le i) (by omega : i ≤ m + 1), hzero, zero_add]
    have hshift : ∑ k ∈ Finset.Ico i (m + 1), piK b a i k * armaPsi b a (m - k)
        = ∑ d ∈ Finset.range ((m - i) + 1), armaPi b a d * armaPsi b a ((m - i) - d) := by
      rw [Finset.sum_Ico_eq_sum_range, show m + 1 - i = (m - i) + 1 by omega]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [piK, if_pos (Nat.le_add_right _ _)]
      congr 2 <;> omega
    rw [hsplit, hshift, armaPi_conv_armaPsi]
    by_cases h : i = m
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · rw [Finset.sum_eq_zero fun k hk => by
      rw [Finset.mem_range] at hk
      rw [piK_eq_zero b a (by omega), zero_mul], if_neg (by omega)]

/-- **Above the horizon**: the geometric estimate `|u_i(m)| ≤ C²(T − i) r^{m−i}`, whose
`(T − i)` factor (rather than `T`) is what keeps the trace bounded. -/
private lemma abs_uSeq_le {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r)
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) (hψ : ∀ n, |armaPsi b a n| ≤ C * r ^ n)
    {T i m : ℕ} (hi : i < T) (hm : T ≤ m) :
    |uSeq b a T i m| ≤ C ^ 2 * ((T : ℝ) - i) * r ^ (m - i) := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hzero : ∑ k ∈ Finset.Ico 0 i, piK b a i k * psiK b a m k = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [Finset.mem_Ico] at hk
      rw [piK_eq_zero b a hk.2, zero_mul]
  have hsplit : uSeq b a T i m = ∑ k ∈ Finset.Ico i T, piK b a i k * psiK b a m k := by
    rw [uSeq, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun k => piK b a i k * psiK b a m k)
        (Nat.zero_le i) (le_of_lt hi), hzero, zero_add]
  have hterm : ∀ k ∈ Finset.Ico i T,
      |piK b a i k * psiK b a m k| ≤ C ^ 2 * r ^ (m - i) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hkm : k ≤ m := by omega
    rw [piK, if_pos hk.1, psiK, if_pos hkm, abs_mul]
    calc |armaPi b a (k - i)| * |armaPsi b a (m - k)|
        ≤ (C * r ^ (k - i)) * (C * r ^ (m - k)) :=
          mul_le_mul (hπ _) (hψ _) (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (r ^ (k - i) * r ^ (m - k)) := by ring
      _ = C ^ 2 * r ^ (m - i) := by rw [← pow_add]; congr 2; omega
  calc |uSeq b a T i m| ≤ ∑ k ∈ Finset.Ico i T, |piK b a i k * psiK b a m k| := by
        rw [hsplit]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Ico i T, C ^ 2 * r ^ (m - i) := Finset.sum_le_sum hterm
    _ = C ^ 2 * ((T : ℝ) - i) * r ^ (m - i) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have : ((T - i : ℕ) : ℝ) = (T : ℝ) - i := by
          push_cast [Nat.cast_sub (le_of_lt hi)]
          ring
        rw [this]
        ring

/-- Each kernel product is summable in the absolute time `m` (geometric ψ-decay). -/
private lemma summable_psiK_mul (a : Fin q → ℝ) (hb : NoRootClosedDisc b) (s t : ℕ) :
    Summable fun m : ℕ => psiK b a m s * psiK b a m t := by
  obtain ⟨C, hC, r₀, hr₀, hr₁, hbnd₀⟩ := exists_geometric_bound_armaPsi a hb
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = max r₀ (1 / 2) := ⟨_, rfl⟩
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) (hrdef ▸ le_max_right r₀ (1 / 2))
  have hrlt : r < 1 := hrdef ▸ max_lt hr₁ (by norm_num)
  have hbnd : ∀ n, |armaPsi b a n| ≤ C * r ^ n := fun n =>
    (hbnd₀ n).trans (by
      have h : r₀ ^ n ≤ r ^ n := pow_le_pow_left₀ hr₀ (hrdef ▸ le_max_left r₀ (1 / 2)) n
      nlinarith)
  have hCr : ∀ u : ℕ, 0 ≤ C / r ^ u := fun u => div_nonneg hC (by positivity)
  have hker : ∀ m u : ℕ, |psiK b a m u| ≤ C / r ^ u * r ^ m := by
    intro m u
    unfold psiK
    split_ifs with h
    · have hsplit : r ^ m = r ^ (m - u) * r ^ u := by rw [← pow_add]; congr 1; omega
      calc |armaPsi b a (m - u)| ≤ C * r ^ (m - u) := hbnd _
        _ = C / r ^ u * (r ^ (m - u) * r ^ u) := by field_simp
        _ = C / r ^ u * r ^ m := by rw [← hsplit]
    · rw [abs_zero]
      exact mul_nonneg (hCr u) (by positivity)
  refine Summable.of_abs (Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => ?_)
    ((summable_geometric_of_lt_one (sq_nonneg r) (by nlinarith)).mul_left
      (C / r ^ s * (C / r ^ t))))
  rw [abs_mul]
  calc |psiK b a m s| * |psiK b a m t|
      ≤ (C / r ^ s * r ^ m) * (C / r ^ t * r ^ m) :=
        mul_le_mul (hker m s) (hker m t) (abs_nonneg _) (mul_nonneg (hCr s) (by positivity))
    _ = C / r ^ s * (C / r ^ t) * (r ^ 2) ^ m := by rw [← pow_mul]; ring

/-- **The Cholesky-type factorization of the model ACVF**: `γ(s − t) = Σ_m ψ̃(m,s) ψ̃(m,t)`. -/
private lemma armaACVF_eq_tsum_psiK (a : Fin q → ℝ) (hb : NoRootClosedDisc b) (s t : ℕ) :
    armaACVF b a ((s : ℤ) - (t : ℤ)) = ∑' m : ℕ, psiK b a m s * psiK b a m t := by
  have main : ∀ u v : ℕ, v ≤ u →
      armaACVF b a ((u : ℤ) - (v : ℤ)) = ∑' m : ℕ, psiK b a m u * psiK b a m v := by
    intro u v hvu
    have hs := summable_psiK_mul a hb u v
    have hzero : ∑ i ∈ Finset.range u, psiK b a i u * psiK b a i v = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [psiK_eq_zero b a (Finset.mem_range.1 hi), zero_mul]
    have hsplit := hs.sum_add_tsum_nat_add u
    rw [hzero, zero_add] at hsplit
    rw [← hsplit, armaACVF, show ((u : ℤ) - (v : ℤ)).natAbs = u - v by omega]
    refine tsum_congr fun j => ?_
    have h1 : psiK b a (j + u) u = armaPsi b a j := by simp [psiK]
    have h2 : psiK b a (j + u) v = armaPsi b a (j + (u - v)) := by
      rw [psiK, if_pos (by omega)]
      congr 1
      omega
    rw [h1, h2]
  rcases le_total t s with h | h
  · exact main s t h
  · have hsymm : armaACVF b a ((s : ℤ) - (t : ℤ)) = armaACVF b a ((t : ℤ) - (s : ℤ)) := by
      simp only [armaACVF, show ((s : ℤ) - (t : ℤ)).natAbs = ((t : ℤ) - (s : ℤ)).natAbs by omega]
    rw [hsymm, main t s h]
    exact tsum_congr fun m => mul_comm _ _

/-- Fubini for a weighted Gram pairing of `ℓ²`-type sequences. -/
private lemma tsum_weighted_gram {T : ℕ} (v : Fin T → ℕ → ℝ)
    (hv : ∀ i j, Summable fun m : ℕ => v i m * v j m) (c d : Fin T → ℝ) :
    ∑' m : ℕ, (∑ i, c i * v i m) * (∑ j, d j * v j m)
      = ∑ i, ∑ j, c i * d j * ∑' m : ℕ, v i m * v j m := by
  have hsummand : ∀ i j : Fin T, Summable fun m : ℕ => (c i * v i m) * (d j * v j m) := by
    intro i j
    exact ((hv i j).mul_left (c i * d j)).congr fun m => by ring
  have hexp : ∀ m : ℕ, (∑ i, c i * v i m) * (∑ j, d j * v j m)
      = ∑ i, ∑ j, (c i * v i m) * (d j * v j m) := fun m => Finset.sum_mul_sum _ _ _ _
  rw [tsum_congr hexp,
    Summable.tsum_finsetSum (fun i _ => summable_sum fun j _ => hsummand i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum (fun j _ => hsummand i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by ring

private lemma summable_uSeq_mul (hb : NoRootClosedDisc b) (T i j : ℕ) :
    Summable fun m : ℕ => uSeq b a T i m * uSeq b a T j m := by
  have h : ∀ m : ℕ, uSeq b a T i m * uSeq b a T j m
      = ∑ k ∈ Finset.range T, ∑ l ∈ Finset.range T,
          (piK b a i k * piK b a j l) * (psiK b a m k * psiK b a m l) := by
    intro m
    rw [uSeq, uSeq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  refine Summable.congr ?_ fun m => (h m).symm
  exact summable_sum fun k _ => summable_sum fun l _ => (summable_psiK_mul a hb k l).mul_left _

/-- The **inversion matrix** `Π_T` (upper triangular with unit diagonal). -/
noncomputable def piMat (b : Fin p → ℝ) (a : Fin q → ℝ) (T : ℕ) :
    Matrix (Fin T) (Fin T) ℝ :=
  Matrix.of fun i k => piK b a (i : ℕ) (k : ℕ)

/-- The **tail Gram matrix** `G_T = Π_T Γ_T Π_Tᵀ − 1`. -/
private noncomputable def gramTail (b : Fin p → ℝ) (a : Fin q → ℝ) (T : ℕ) :
    Matrix (Fin T) (Fin T) ℝ :=
  Matrix.of fun i j => ∑' m : ℕ, uSeq b a T (i : ℕ) (m + T) * uSeq b a T (j : ℕ) (m + T)

private lemma det_piMat (b : Fin p → ℝ) (a : Fin q → ℝ) (T : ℕ) : (piMat b a T).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [piMat, piK_self]
  · intro i j hij
    exact piK_eq_zero b a hij

/-- **The whitened Toeplitz matrix is `1` plus a tail Gram matrix.** -/
private lemma piMat_mul_toeplitz_mul_transpose (hB : ARMAInvertibleParams b a) (T : ℕ) :
    piMat b a T * armaToeplitz b a T * (piMat b a T)ᵀ = 1 + gramTail b a T := by
  have huFin : ∀ x m : ℕ,
      uSeq b a T x m = ∑ k : Fin T, piK b a x (k : ℕ) * psiK b a m (k : ℕ) := by
    intro x m
    rw [uSeq, ← Fin.sum_univ_eq_sum_range (fun k => piK b a x k * psiK b a m k) T]
  ext i j
  have hgram := tsum_weighted_gram (T := T) (fun k m => psiK b a m (k : ℕ))
    (fun k l => summable_psiK_mul a hB.1 (k : ℕ) (l : ℕ))
    (fun k => piK b a (i : ℕ) (k : ℕ)) (fun l => piK b a (j : ℕ) (l : ℕ))
  have hentry : (piMat b a T * armaToeplitz b a T * (piMat b a T)ᵀ) i j
      = ∑' m : ℕ, uSeq b a T (i : ℕ) m * uSeq b a T (j : ℕ) m := by
    simp only [huFin]
    rw [hgram]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, piMat, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hΓ : (∑' m : ℕ, psiK b a m (l : ℕ) * psiK b a m (k : ℕ)) = armaToeplitz b a T l k :=
      (armaACVF_eq_tsum_psiK a hB.1 (l : ℕ) (k : ℕ)).symm
    rw [hΓ]
    ring
  rw [hentry]
  have hsplit := (summable_uSeq_mul (a := a) hB.1 T (i : ℕ) (j : ℕ)).sum_add_tsum_nat_add T
  rw [← hsplit]
  have hhead : ∑ m ∈ Finset.range T, uSeq b a T (i : ℕ) m * uSeq b a T (j : ℕ) m
      = (1 : Matrix (Fin T) (Fin T) ℝ) i j := by
    have hterm : ∀ m ∈ Finset.range T,
        uSeq b a T (i : ℕ) m * uSeq b a T (j : ℕ) m
          = (if (i : ℕ) = m then (1 : ℝ) else 0) * (if (j : ℕ) = m then 1 else 0) := by
      intro m hm
      rw [Finset.mem_range] at hm
      rw [uSeq_eq_of_lt b a hm, uSeq_eq_of_lt b a hm]
    rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single (i : ℕ)]
    · rw [if_pos rfl, one_mul, Matrix.one_apply]
      by_cases h : i = j
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (by simpa [Fin.ext_iff, eq_comm] using h)]
    · intro m _ hm
      rw [if_neg (Ne.symm hm), zero_mul]
    · intro h
      exact absurd (Finset.mem_range.2 i.isLt) h
  rw [hhead]
  rfl

private lemma gramTail_posSemidef (hB : ARMAInvertibleParams b a) (T : ℕ) :
    (gramTail b a T).PosSemidef := by
  have hsummable : ∀ i j : Fin T,
      Summable fun m : ℕ => uSeq b a T (i : ℕ) (m + T) * uSeq b a T (j : ℕ) (m + T) :=
    fun i j => (summable_nat_add_iff T).2 (summable_uSeq_mul (a := a) hB.1 T (i : ℕ) (j : ℕ))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, gramTail, Matrix.of_apply]
    exact tsum_congr fun m => mul_comm _ _
  · have hquad : star c ⬝ᵥ (gramTail b a T *ᵥ c)
        = ∑' m : ℕ, (∑ i, c i * uSeq b a T (i : ℕ) (m + T)) *
            (∑ j, c j * uSeq b a T (j : ℕ) (m + T)) := by
      rw [tsum_weighted_gram (fun i m => uSeq b a T (i : ℕ) (m + T)) hsummable c c]
      simp only [dotProduct, mulVec, gramTail, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hquad]
    refine tsum_nonneg fun m => ?_
    exact mul_self_nonneg _

/-- **The uniform trace bound**: `tr G_T ≤ K` with `K` free of `T` — the quantitative
heart of the Szegő limit. -/
private lemma trace_gramTail_le {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) (hψ : ∀ n, |armaPsi b a n| ≤ C * r ^ n)
    (hB : ARMAInvertibleParams b a) (T : ℕ) :
    (gramTail b a T).trace
      ≤ C ^ 4 / (1 - r ^ 2) * ∑' d : ℕ, ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hr2 : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have hr2lt : r ^ 2 < 1 := by nlinarith
  have hgeom : Summable fun m : ℕ => (r ^ 2) ^ m := summable_geometric_of_lt_one hr2 hr2lt
  have hgeomval : ∑' m : ℕ, (r ^ 2) ^ m = (1 - r ^ 2)⁻¹ := tsum_geometric_of_lt_one hr2 hr2lt
  have hmaj : Summable fun d : ℕ => ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := by
    have h0 : Summable fun n : ℕ => (r ^ 2) ^ n := hgeom
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * (r ^ 2) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr2]; exact hr2lt)
    have h2 : Summable fun n : ℕ => (n : ℝ) ^ 2 * (r ^ 2) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr2]; exact hr2lt)
    have hsum := ((h2.add (h1.mul_left 2)).add h0).mul_right (r ^ 2)
    refine hsum.congr fun n => ?_
    rw [pow_succ]
    ring
  -- the diagonal estimate
  have hdiag : ∀ i : Fin T, gramTail b a T i i
      ≤ C ^ 4 / (1 - r ^ 2) * (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) := by
    intro i
    have hi : (i : ℕ) < T := i.isLt
    have hterm : ∀ m : ℕ,
        uSeq b a T (i : ℕ) (m + T) * uSeq b a T (i : ℕ) (m + T)
          ≤ C ^ 4 * (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) *
              (r ^ 2) ^ m := by
      intro m
      have hb := abs_uSeq_le hC hr0 hπ hψ hi (Nat.le_add_left T m)
      have hcast : ((T : ℝ) - (i : ℕ)) = ((T - (i : ℕ) : ℕ) : ℝ) := by
        rw [Nat.cast_sub (le_of_lt hi)]
      have hexp : r ^ (m + T - (i : ℕ)) = r ^ m * r ^ (T - (i : ℕ)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hcast, hexp] at hb
      have hsq : (uSeq b a T (i : ℕ) (m + T)) ^ 2
          ≤ (C ^ 2 * ((T - (i : ℕ) : ℕ) : ℝ) * (r ^ m * r ^ (T - (i : ℕ)))) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      calc uSeq b a T (i : ℕ) (m + T) * uSeq b a T (i : ℕ) (m + T)
          = (uSeq b a T (i : ℕ) (m + T)) ^ 2 := (sq _).symm
        _ ≤ (C ^ 2 * ((T - (i : ℕ) : ℕ) : ℝ) * (r ^ m * r ^ (T - (i : ℕ)))) ^ 2 := hsq
        _ = C ^ 4 * (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) *
              (r ^ 2) ^ m := by
            rw [← pow_mul, ← pow_mul, mul_comm 2 m, mul_comm 2 (T - (i : ℕ)), pow_mul, pow_mul]
            ring
    have hsum1 : Summable fun m : ℕ =>
        uSeq b a T (i : ℕ) (m + T) * uSeq b a T (i : ℕ) (m + T) :=
      (summable_nat_add_iff T).2 (summable_uSeq_mul (a := a) hB.1 T (i : ℕ) (i : ℕ))
    have hsum2 := hgeom.mul_left
      (C ^ 4 * (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))))
    have := hsum1.tsum_le_tsum hterm hsum2
    rw [tsum_mul_left, hgeomval] at this
    calc gramTail b a T i i
        = ∑' m : ℕ, uSeq b a T (i : ℕ) (m + T) * uSeq b a T (i : ℕ) (m + T) := rfl
      _ ≤ C ^ 4 * (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) *
            (1 - r ^ 2)⁻¹ := this
      _ = C ^ 4 / (1 - r ^ 2) *
            (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) := by
          rw [div_eq_mul_inv]
          ring
  have hconst : (0 : ℝ) ≤ C ^ 4 / (1 - r ^ 2) := by
    have : (0 : ℝ) < 1 - r ^ 2 := by nlinarith
    positivity
  calc (gramTail b a T).trace
      = ∑ i : Fin T, gramTail b a T i i := rfl
    _ ≤ ∑ i : Fin T, C ^ 4 / (1 - r ^ 2) *
          (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) :=
        Finset.sum_le_sum fun i _ => hdiag i
    _ = C ^ 4 / (1 - r ^ 2) *
          ∑ i ∈ Finset.range T, ((T - i : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ (T - i) := by
        rw [← Finset.mul_sum,
          Fin.sum_univ_eq_sum_range (fun i => ((T - i : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ (T - i)) T]
    _ ≤ C ^ 4 / (1 - r ^ 2) * ∑' d : ℕ, ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hconst
        have hreflect : ∑ i ∈ Finset.range T, ((T - i : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ (T - i)
            = ∑ d ∈ Finset.range T, ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := by
          rw [← Finset.sum_range_reflect
            (fun d => ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1)) T]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          have h1 : T - 1 - i + 1 = T - i := by omega
          rw [h1]
          congr 1
          rw [Nat.cast_sub (by omega : i ≤ T)]
          have : ((T - 1 - i : ℕ) : ℝ) + 1 = (T : ℝ) - i := by
            rw [Nat.cast_sub (by omega : i ≤ T - 1), Nat.cast_sub (by omega : 1 ≤ T)]
            push_cast
            ring
          rw [this]
        rw [hreflect]
        exact hmaj.sum_le_tsum _ (fun d _ => by positivity)

/-- `det (1 + G) = ∏(1 + λ_j(G))` for positive semidefinite `G`: bounded below by `1`,
and its logarithm bounded above by `tr G`. -/
private lemma det_one_add_bounds {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ}
    (hGh : G.IsHermitian) (hnn : ∀ i, 0 ≤ Matrix.IsHermitian.eigenvalues hGh i) :
    1 ≤ (1 + G).det ∧ Real.log (1 + G).det ≤ G.trace := by
  obtain ⟨d, hd⟩ : ∃ d : Fin n → ℝ, d = Matrix.IsHermitian.eigenvalues hGh := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : unitary (Matrix (Fin n) (Fin n) ℝ),
      U = Matrix.IsHermitian.eigenvectorUnitary hGh := ⟨_, rfl⟩
  have hnn' : ∀ i, 0 ≤ d i := by rw [hd]; exact hnn
  have hdet : (1 + G).det = ∏ i, (1 + d i) := by
    have hspec : (1 : Matrix (Fin n) (Fin n) ℝ) + G
        = Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) U
            (1 + Matrix.diagonal (RCLike.ofReal ∘ d)) := by
      rw [map_add, map_one, hd, hU, ← Matrix.IsHermitian.spectral_theorem hGh]
    have hUdet : ((U : Matrix (Fin n) (Fin n) ℝ)).det *
        (star (U : Matrix (Fin n) (Fin n) ℝ)).det = 1 := by
      have hmul : (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 := by
        simp
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    have hdiag : (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.diagonal (RCLike.ofReal ∘ d)
        = Matrix.diagonal fun i => 1 + d i := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_add]
      rfl
    rw [hspec, Unitary.conjStarAlgAut_apply, hdiag, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal]
    calc ((U : Matrix (Fin n) (Fin n) ℝ)).det * (∏ i, (1 + d i))
          * (star (U : Matrix (Fin n) (Fin n) ℝ)).det
        = (((U : Matrix (Fin n) (Fin n) ℝ)).det *
            (star (U : Matrix (Fin n) (Fin n) ℝ)).det) * ∏ i, (1 + d i) := by ring
      _ = ∏ i, (1 + d i) := by rw [hUdet, one_mul]
  have htrace : G.trace = ∑ i, d i := by
    rw [hd]
    simpa using Matrix.IsHermitian.trace_eq_sum_eigenvalues hGh
  refine ⟨?_, ?_⟩
  · rw [hdet]
    exact Finset.one_le_prod fun i _ => by linarith [hnn' i]
  · rw [hdet, htrace, Real.log_prod fun i _ => by
      have := hnn' i
      positivity]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := Real.log_le_sub_one_of_pos (x := 1 + d i) (by linarith [hnn' i])
    linarith

/-- The two-sided bound `0 ≤ log det Γ_T ≤ K` with `K` free of `T`. -/
private lemma log_det_armaToeplitz_bounds {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) (hψ : ∀ n, |armaPsi b a n| ≤ C * r ^ n)
    (hB : ARMAInvertibleParams b a) (T : ℕ) :
    0 ≤ Real.log (armaToeplitz b a T).det ∧
      Real.log (armaToeplitz b a T).det
        ≤ C ^ 4 / (1 - r ^ 2) * ∑' d : ℕ, ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := by
  have hdet : (armaToeplitz b a T).det = (1 + gramTail b a T).det := by
    rw [← piMat_mul_toeplitz_mul_transpose hB T, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, det_piMat]
    ring
  have hpsd := gramTail_posSemidef (a := a) hB T
  obtain ⟨h1, h2⟩ := det_one_add_bounds hpsd.1 (Matrix.PosSemidef.eigenvalues_nonneg hpsd)
  refine ⟨?_, ?_⟩
  · rw [hdet]
    exact Real.log_nonneg h1
  · rw [hdet]
    exact h2.trans (trace_gramTail_le hC hr0 hr1 hπ hψ hB T)

/-- `1 + G_T` has determinant `≥ 1`, hence is invertible (the eigenvalue bound already
used for the Szegő estimate). -/
private lemma one_add_gramTail_det_isUnit (hB : ARMAInvertibleParams b a) (T : ℕ) :
    IsUnit (((1 : Matrix (Fin T) (Fin T) ℝ) + gramTail b a T).det) := by
  have hpsd := gramTail_posSemidef (a := a) hB T
  obtain ⟨h1, -⟩ := det_one_add_bounds hpsd.1 (Matrix.PosSemidef.eigenvalues_nonneg hpsd)
  exact (by linarith : (0 : ℝ) < ((1 : Matrix (Fin T) (Fin T) ℝ)
    + gramTail b a T).det).ne'.isUnit

/-! ### The correction term `(B)`: three deterministic matrix bricks

These are the deterministic half of step (B) of the route recorded at
`armaProfileS_tendstoInProb`. They replace the operator-norm/eigenbasis argument
sketched there by an elementary Schur test: for a *positive semidefinite* `M` the
off-diagonal entries are dominated by the diagonal (`abs_entry_le_of_posSemidef`),
which turns the pairing `Σ_{ij} M_ij S_ij` — i.e. `tr(M S)` for symmetric `S` — into
`(row sum bound of S) · tr M` (`sum_entry_mul_le_of_posSemidef`), with no spectral
theory at all. -/

/-- **Off-diagonal entries of a psd matrix are dominated by the diagonal**:
`|M_ij| ≤ (M_ii + M_jj)/2`, by testing the quadratic form at `e_i ± e_j`. -/
private lemma abs_entry_le_of_posSemidef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (i j : Fin n) : |M i j| ≤ (M i i + M j j) / 2 := by
  have hsym : M j i = M i j := by
    have h := hM.1
    calc M j i = Mᴴ i j := by simp [Matrix.conjTranspose_apply]
      _ = M i j := by rw [h]
  have key : ∀ s : ℝ, 0 ≤ M i i + s * s * M j j + 2 * s * M i j := by
    intro s
    have hx := hM.dotProduct_mulVec_nonneg (Pi.single i (1 : ℝ) + Pi.single j s)
    simp only [star_trivial, Matrix.mulVec_add, add_dotProduct, dotProduct_add,
      single_dotProduct, Matrix.mulVec_single] at hx
    simp only [Pi.smul_apply, Matrix.col_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, mul_one] at hx
    rw [hsym] at hx
    nlinarith [hx]
  have h1 := key 1
  have h2 := key (-1)
  rw [abs_le]
  constructor <;> nlinarith

/-- **The Schur-test trace bound** `tr(M S) ≤ R · tr M` for positive semidefinite `M`
and symmetric `S` whose row sums are bounded by `R`. This is the substitute for
`tr(A B) ≤ ‖A‖_op tr B`: no operator norm and no eigenbasis are needed, because
`|M_ij| ≤ (M_ii + M_jj)/2` already redistributes the whole pairing onto the diagonal
of `M`. -/
private lemma sum_entry_mul_le_of_posSemidef {n : ℕ} {M S : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (hS : ∀ i j, S i j = S j i) {R : ℝ}
    (hrow : ∀ i, ∑ j, |S i j| ≤ R) :
    ∑ i, ∑ j, M i j * S i j ≤ R * M.trace := by
  have hdiag : ∀ i, 0 ≤ M i i := fun i => hM.diag_nonneg
  have hstep : ∑ i, ∑ j, M i j * S i j
      ≤ ∑ i, ∑ j, (M i i / 2) * |S i j| + ∑ i, ∑ j, (M j j / 2) * |S i j| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : M i j * S i j ≤ |M i j| * |S i j| := by
      calc M i j * S i j ≤ |M i j * S i j| := le_abs_self _
        _ = |M i j| * |S i j| := abs_mul _ _
    have h2 : |M i j| * |S i j| ≤ ((M i i + M j j) / 2) * |S i j| :=
      mul_le_mul_of_nonneg_right (abs_entry_le_of_posSemidef hM i j) (abs_nonneg _)
    nlinarith [h1, h2]
  have hA : ∑ i, ∑ j, (M i i / 2) * |S i j| ≤ R / 2 * M.trace := by
    have hrow' : ∀ i : Fin n, ∑ j, (M i i / 2) * |S i j| ≤ (M i i / 2) * R := by
      intro i
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hrow i) (by linarith [hdiag i])
    calc ∑ i, ∑ j, (M i i / 2) * |S i j| ≤ ∑ i, (M i i / 2) * R :=
          Finset.sum_le_sum fun i _ => hrow' i
      _ = R / 2 * M.trace := by
          have htr : M.trace = ∑ i, M i i := rfl
          rw [htr, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  have hB : ∑ i, ∑ j, (M j j / 2) * |S i j| ≤ R / 2 * M.trace := by
    rw [Finset.sum_comm]
    have hcol : ∀ j : Fin n, ∑ i, (M j j / 2) * |S i j| ≤ (M j j / 2) * R := by
      intro j
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith [hdiag j])
      calc ∑ i, |S i j| = ∑ i, |S j i| := Finset.sum_congr rfl fun i _ => by rw [hS i j]
        _ ≤ R := hrow j
    calc ∑ j, ∑ i, (M j j / 2) * |S i j| ≤ ∑ j, (M j j / 2) * R :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = R / 2 * M.trace := by
          have htr : M.trace = ∑ i, M i i := rfl
          rw [htr, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- **The resolvent sandwich** `xᵀ G x ≥ xᵀ x − xᵀ (1 + G)⁻¹ x ≥ 0` for positive
semidefinite `G` with `1 + G` invertible. Substituting `x = (1 + G) y` makes both
halves polynomial identities in `y`: with `a = ‖y‖²`, `b = yᵀ G y`, `c = ‖G y‖²`,
`d = (Gy)ᵀ G (Gy)`,

  `xᵀ (1+G)⁻¹ x = a + b`,  `xᵀ x = a + 2b + c`,  `xᵀ G x = b + 2c + d`,

so the two gaps are `b + c ≥ 0` and `c + d ≥ 0`. No spectral theory, and in particular
no positive semidefiniteness of `(1 + G)⁻¹ G` itself, is needed. -/
private lemma quadForm_one_add_inv_bounds {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosSemidef) (hdet : IsUnit (((1 : Matrix (Fin n) (Fin n) ℝ) + G).det))
    (x : Fin n → ℝ) :
    x ⬝ᵥ ((1 + G)⁻¹ *ᵥ x) ≤ x ⬝ᵥ x ∧
      x ⬝ᵥ x - x ⬝ᵥ (G *ᵥ x) ≤ x ⬝ᵥ ((1 + G)⁻¹ *ᵥ x) := by
  have hGT : Gᵀ = G := by
    ext i j
    have h := congrFun (congrFun hG.1 i) j
    simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using h
  have hswap : ∀ v w : Fin n → ℝ, v ⬝ᵥ (G *ᵥ w) = (G *ᵥ v) ⬝ᵥ w := by
    intro v w
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hGT]
  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = (1 + G)⁻¹ *ᵥ x := ⟨_, rfl⟩
  have hxy : x = y + G *ᵥ y := by
    have h1 : (1 + G) *ᵥ y = x := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    rw [← h1, Matrix.add_mulVec, Matrix.one_mulVec]
  have hb : 0 ≤ y ⬝ᵥ (G *ᵥ y) := by
    have := hG.dotProduct_mulVec_nonneg y
    rwa [star_trivial] at this
  have hd : 0 ≤ (G *ᵥ y) ⬝ᵥ (G *ᵥ (G *ᵥ y)) := by
    have := hG.dotProduct_mulVec_nonneg (G *ᵥ y)
    rwa [star_trivial] at this
  have hc : 0 ≤ (G *ᵥ y) ⬝ᵥ (G *ᵥ y) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have e1 : x ⬝ᵥ ((1 + G)⁻¹ *ᵥ x) = y ⬝ᵥ y + y ⬝ᵥ (G *ᵥ y) := by
    rw [← hy]
    nth_rewrite 1 [hxy]
    rw [add_dotProduct, dotProduct_comm (G *ᵥ y) y]
  have e2 : x ⬝ᵥ x = y ⬝ᵥ y + 2 * (y ⬝ᵥ (G *ᵥ y)) + (G *ᵥ y) ⬝ᵥ (G *ᵥ y) := by
    rw [hxy, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm (G *ᵥ y) y]
    ring
  have e3 : x ⬝ᵥ (G *ᵥ x) = y ⬝ᵥ (G *ᵥ y) + 2 * ((G *ᵥ y) ⬝ᵥ (G *ᵥ y))
      + (G *ᵥ y) ⬝ᵥ (G *ᵥ (G *ᵥ y)) := by
    rw [hxy, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_comm (G *ᵥ y) (G *ᵥ y), hswap y (G *ᵥ y)]
    ring
  constructor <;> rw [e1] <;> [rw [e2]; rw [e2, e3]] <;> linarith

/-- **Finite-section identity for the profiling quadratic form.** Inverting
`Π_T Γ_T Π_Tᵀ = 1 + G_T` (legitimate: `det Π_T = 1` and `1 + G_T` is positive definite)
gives `Γ_T⁻¹ = Π_Tᵀ (1 + G_T)⁻¹ Π_T`, hence

  `S_T(θ) = xᵀ Γ_T(θ)⁻¹ x = uᵀ (1 + G_T)⁻¹ u`,  `u = Π_T x`,

where `u_i = Σ_{j ≤ i} π_{i−j}(θ) x_j` is exactly the **truncated θ-residual** at time
`i`. This is the deterministic half of `armaProfileS_tendstoInProb`: it converts the
matrix-inverse statistic into the residual sum of squares plus a correction governed by
`G_T`, whose trace is bounded uniformly in `T` (`trace_gramTail_le`). See the debt note
at `armaProfileS_tendstoInProb` for what remains. -/
private lemma armaProfileS_eq_gramTail_quadForm (hB : ARMAInvertibleParams b a) (T : ℕ)
    (x : Fin T → ℝ) :
    armaProfileS b a x
      = dotProduct (Matrix.mulVec (piMat b a T) x)
          (Matrix.mulVec ((1 + gramTail b a T)⁻¹) (Matrix.mulVec (piMat b a T) x)) := by
  have hPi : IsUnit ((piMat b a T).det) := by rw [det_piMat]; exact isUnit_one
  have hPiTr : IsUnit (((piMat b a T)ᵀ).det) := by rw [Matrix.det_transpose]; exact hPi
  have hN : IsUnit (((1 : Matrix (Fin T) (Fin T) ℝ) + gramTail b a T).det) :=
    one_add_gramTail_det_isUnit hB T
  -- the whitened identity, solved for `Pi * Gamma`
  have h1 : piMat b a T * armaToeplitz b a T
      = (1 + gramTail b a T) * ((piMat b a T)ᵀ)⁻¹ := by
    calc piMat b a T * armaToeplitz b a T
        = piMat b a T * armaToeplitz b a T * ((piMat b a T)ᵀ * ((piMat b a T)ᵀ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hPiTr, mul_one]
      _ = piMat b a T * armaToeplitz b a T * (piMat b a T)ᵀ * ((piMat b a T)ᵀ)⁻¹ := by
          simp only [mul_assoc]
      _ = (1 + gramTail b a T) * ((piMat b a T)ᵀ)⁻¹ := by
          rw [piMat_mul_toeplitz_mul_transpose hB T]
  -- hence the inverse factorises through the whitener
  have hinv : (armaToeplitz b a T)⁻¹
      = (piMat b a T)ᵀ * (1 + gramTail b a T)⁻¹ * piMat b a T := by
    refine Matrix.inv_eq_left_inv ?_
    calc (piMat b a T)ᵀ * (1 + gramTail b a T)⁻¹ * piMat b a T * armaToeplitz b a T
        = (piMat b a T)ᵀ * (1 + gramTail b a T)⁻¹
            * (piMat b a T * armaToeplitz b a T) := by
          simp only [mul_assoc]
      _ = (piMat b a T)ᵀ * (1 + gramTail b a T)⁻¹
            * ((1 + gramTail b a T) * ((piMat b a T)ᵀ)⁻¹) := by rw [h1]
      _ = (piMat b a T)ᵀ * ((1 + gramTail b a T)⁻¹ * (1 + gramTail b a T))
            * ((piMat b a T)ᵀ)⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by
          rw [Matrix.nonsing_inv_mul _ hN, mul_one, Matrix.mul_nonsing_inv _ hPiTr]
  rw [armaProfileS, hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **The residual sandwich** (the deterministic half of step (B) of the route recorded
at `armaProfileS_tendstoInProb`): with `u = Π_T x` the vector of truncated `θ`-residuals,

  `‖u‖² − uᵀ G_T u  ≤  S_T(θ)  ≤  ‖u‖²`.

Combining `armaProfileS_eq_gramTail_quadForm` (the finite-section identity) with
`quadForm_one_add_inv_bounds`, this reduces the profiling statistic to the residual sum
of squares up to an error controlled by the *bounded-trace* Gram tail `G_T`
(`trace_gramTail_le`) — no operator norm, no eigenbasis, and no positive
semidefiniteness of `(1 + G_T)⁻¹ G_T`. -/
private lemma armaProfileS_sandwich (hB : ARMAInvertibleParams b a) (T : ℕ)
    (x : Fin T → ℝ) :
    armaProfileS b a x ≤ (piMat b a T *ᵥ x) ⬝ᵥ (piMat b a T *ᵥ x) ∧
      (piMat b a T *ᵥ x) ⬝ᵥ (piMat b a T *ᵥ x)
          - (piMat b a T *ᵥ x) ⬝ᵥ (gramTail b a T *ᵥ (piMat b a T *ᵥ x))
        ≤ armaProfileS b a x := by
  rw [armaProfileS_eq_gramTail_quadForm hB T x]
  exact quadForm_one_add_inv_bounds (gramTail_posSemidef hB T)
    (one_add_gramTail_det_isUnit hB T) _

/-! ### Uniform-in-`θ` control of the Gram tail

`trace_gramTail_le` bounds `tr G_T(θ)` for **one** `θ`; the uniform law of large numbers
that `mle_consistent`(iii) consumes must instead dominate the quadratic form
`uᵀ G_T(θ) u` for *every* `θ` in the compact `K` at once, by a single `θ`-free random
variable — one Markov inequality then controls the whole supremum. The route:

* the entrywise bound `|G_{ij}| ≤ (1 − r²)⁻¹ h_i h_j`, `h_i = C²(T − i) r^{T−i}`
  (`abs_gramTail_entry_le`), factorises the quadratic form as
  `uᵀ G u ≤ (1 − r²)⁻¹ (Σ_i h_i |u_i|)²` (`quadForm_gramTail_le_sq`) — no eigenvalues and
  no operator norm are involved;
* `|u_i| = |Σ_k π̃(i,k) x_k|` is dominated by the `θ`-free envelope
  `Σ_k C r^{k−i}|x_k|` (`residEnv`, `abs_mulVec_piMat_le`);
* `Σ_i h_i ≤ C² Σ_{d ≥ 1} d r^d` is bounded uniformly in `T` (`sum_weight_le`).

Both `C` and `r` come from the locally uniform brick
`exists_uniform_geometric_bound_arma`, which is exactly why the envelope is `θ`-free.
This **supersedes** the 2026-08-09 route note at `mle_consistent`, which asked for the
Gram tail's *difference* modulus `Σ_j |G_T(θ)_{ij} − G_T(θ′)_{ij}| ≤ L(ρ)`: no such
modulus is needed, because a uniform `o_p(1)` bound on the correction term itself is
enough for the one-sided (lower) estimate that consistency uses. -/

/-- **Entrywise geometric bound on the tail Gram matrix**: `|G_{ij}| ≤ (1 − r²)⁻¹ h_i h_j`
with `h_i = C²(T − i) r^{T−i}` the same weight that `trace_gramTail_le` sums on the
diagonal. -/
private lemma abs_gramTail_entry_le {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) (hψ : ∀ n, |armaPsi b a n| ≤ C * r ^ n)
    (hB : ARMAInvertibleParams b a) {T : ℕ} (i j : Fin T) :
    |gramTail b a T i j| ≤ (1 - r ^ 2)⁻¹ *
      ((C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ))) *
        (C ^ 2 * ((T : ℝ) - (j : ℕ)) * r ^ (T - (j : ℕ)))) := by
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have hr2 : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have hr2lt : r ^ 2 < 1 := by nlinarith
  have hgeom : Summable fun m : ℕ => (r ^ 2) ^ m := summable_geometric_of_lt_one hr2 hr2lt
  have hsum : Summable fun m : ℕ =>
      uSeq b a T (i : ℕ) (m + T) * uSeq b a T (j : ℕ) (m + T) :=
    (summable_nat_add_iff T).2 (summable_uSeq_mul (a := a) hB.1 T (i : ℕ) (j : ℕ))
  have habs : Summable fun m : ℕ =>
      |uSeq b a T (i : ℕ) (m + T) * uSeq b a T (j : ℕ) (m + T)| := hsum.abs
  have hTi : (0 : ℝ) ≤ (T : ℝ) - (i : ℕ) := by
    have : ((i : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast le_of_lt i.isLt
    linarith
  have hterm : ∀ m : ℕ, |uSeq b a T (i : ℕ) (m + T) * uSeq b a T (j : ℕ) (m + T)|
      ≤ (C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ))) *
          (C ^ 2 * ((T : ℝ) - (j : ℕ)) * r ^ (T - (j : ℕ))) * (r ^ 2) ^ m := by
    intro m
    have hbi := abs_uSeq_le hC hr0 hπ hψ i.isLt (Nat.le_add_left T m)
    have hbj := abs_uSeq_le hC hr0 hπ hψ j.isLt (Nat.le_add_left T m)
    have hei : r ^ (m + T - (i : ℕ)) = r ^ m * r ^ (T - (i : ℕ)) := by
      rw [← pow_add]; congr 1; omega
    have hej : r ^ (m + T - (j : ℕ)) = r ^ m * r ^ (T - (j : ℕ)) := by
      rw [← pow_add]; congr 1; omega
    rw [hei] at hbi
    rw [hej] at hbj
    have hnn : (0 : ℝ) ≤ C ^ 2 * ((T : ℝ) - (i : ℕ)) * (r ^ m * r ^ (T - (i : ℕ))) := by
      positivity
    have hrm : (r ^ 2) ^ m = r ^ m * r ^ m := by rw [sq, mul_pow]
    rw [abs_mul]
    calc |uSeq b a T (i : ℕ) (m + T)| * |uSeq b a T (j : ℕ) (m + T)|
        ≤ (C ^ 2 * ((T : ℝ) - (i : ℕ)) * (r ^ m * r ^ (T - (i : ℕ)))) *
            (C ^ 2 * ((T : ℝ) - (j : ℕ)) * (r ^ m * r ^ (T - (j : ℕ)))) :=
          mul_le_mul hbi hbj (abs_nonneg _) hnn
      _ = _ := by rw [hrm]; ring
  show |∑' m : ℕ, uSeq b a T (i : ℕ) (m + T) * uSeq b a T (j : ℕ) (m + T)| ≤ _
  calc |∑' m : ℕ, uSeq b a T (i : ℕ) (m + T) * uSeq b a T (j : ℕ) (m + T)|
      ≤ ∑' m : ℕ, |uSeq b a T (i : ℕ) (m + T) * uSeq b a T (j : ℕ) (m + T)| := by
        simpa [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f := fun m : ℕ =>
            uSeq b a T (i : ℕ) (m + T) * uSeq b a T (j : ℕ) (m + T))
            (by simpa [Real.norm_eq_abs] using habs)
    _ ≤ ∑' _m : ℕ, (C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ))) *
          (C ^ 2 * ((T : ℝ) - (j : ℕ)) * r ^ (T - (j : ℕ))) * (r ^ 2) ^ _m :=
        habs.tsum_le_tsum hterm (hgeom.mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr2 hr2lt]; ring

/-- **The Gram-tail quadratic form factorises** through the same weight: the entrywise
bound is a rank-one dominance, so the double sum collapses to a square. -/
private lemma quadForm_gramTail_le_sq {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) (hψ : ∀ n, |armaPsi b a n| ≤ C * r ^ n)
    (hB : ARMAInvertibleParams b a) {T : ℕ} (v : Fin T → ℝ) :
    v ⬝ᵥ (gramTail b a T *ᵥ v) ≤ (1 - r ^ 2)⁻¹ *
      (∑ i : Fin T, C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) * |v i|) ^ 2 := by
  have hr2lt : r ^ 2 < 1 := by nlinarith [sq_nonneg r]
  have hinv : (0 : ℝ) ≤ (1 - r ^ 2)⁻¹ := by
    have h : (0 : ℝ) < 1 - r ^ 2 := by linarith
    positivity
  have hexp : v ⬝ᵥ (gramTail b a T *ᵥ v)
      = ∑ i : Fin T, ∑ j : Fin T, v i * (gramTail b a T i j * v j) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
  have hstep : ∀ i j : Fin T, v i * (gramTail b a T i j * v j)
      ≤ (1 - r ^ 2)⁻¹ *
        ((C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) * |v i|) *
          (C ^ 2 * ((T : ℝ) - (j : ℕ)) * r ^ (T - (j : ℕ)) * |v j|)) := by
    intro i j
    have hE := abs_gramTail_entry_le hC hr0 hr1 hπ hψ hB i j
    have h1 : |v i| * |gramTail b a T i j|
        ≤ |v i| * ((1 - r ^ 2)⁻¹ *
            ((C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ))) *
              (C ^ 2 * ((T : ℝ) - (j : ℕ)) * r ^ (T - (j : ℕ))))) :=
      mul_le_mul_of_nonneg_left hE (abs_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (v j))
    calc v i * (gramTail b a T i j * v j)
        ≤ |v i * (gramTail b a T i j * v j)| := le_abs_self _
      _ = |v i| * |gramTail b a T i j| * |v j| := by rw [abs_mul, abs_mul]; ring
      _ ≤ _ := h2
      _ = _ := by ring
  rw [hexp]
  calc ∑ i : Fin T, ∑ j : Fin T, v i * (gramTail b a T i j * v j)
      ≤ ∑ i : Fin T, ∑ j : Fin T, (1 - r ^ 2)⁻¹ *
          ((C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) * |v i|) *
            (C ^ 2 * ((T : ℝ) - (j : ℕ)) * r ^ (T - (j : ℕ)) * |v j|)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hstep i j
    _ = _ := by
        have hprod : (∑ i : Fin T, C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) * |v i|) *
            (∑ j : Fin T, C ^ 2 * ((T : ℝ) - (j : ℕ)) * r ^ (T - (j : ℕ)) * |v j|)
            = ∑ i : Fin T, ∑ j : Fin T,
              (C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) * |v i|) *
                (C ^ 2 * ((T : ℝ) - (j : ℕ)) * r ^ (T - (j : ℕ)) * |v j|) :=
          Finset.sum_mul_sum _ _ _ _
        have hsq : ∀ S : ℝ, S ^ 2 = S * S := fun S => sq S
        rw [hsq (∑ i : Fin T, C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) * |v i|),
          hprod, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- The **`θ`-free envelope** of a truncated residual row: with `|π_n(θ)| ≤ C rⁿ` valid
uniformly over the compact parameter set, every row of `Π_T(θ) x` is dominated by it. -/
private noncomputable def residEnv (C r : ℝ) {T : ℕ} (x : Fin T → ℝ) (i : Fin T) : ℝ :=
  ∑ k : Fin T, (if (i : ℕ) ≤ (k : ℕ) then C * r ^ ((k : ℕ) - (i : ℕ)) else 0) * |x k|

private lemma residEnv_nonneg {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) {T : ℕ}
    (x : Fin T → ℝ) (i : Fin T) : 0 ≤ residEnv C r x i := by
  refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (abs_nonneg _)
  split_ifs <;> positivity

private lemma abs_mulVec_piMat_le {C r : ℝ}
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) {T : ℕ} (x : Fin T → ℝ) (i : Fin T) :
    |(piMat b a T *ᵥ x) i| ≤ residEnv C r x i := by
  have hexp : (piMat b a T *ᵥ x) i = ∑ k : Fin T, piK b a (i : ℕ) (k : ℕ) * x k := rfl
  rw [hexp, residEnv]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  by_cases hik : (i : ℕ) ≤ (k : ℕ)
  · rw [if_pos hik, piK, if_pos hik]
    exact mul_le_mul_of_nonneg_right (hπ _) (abs_nonneg _)
  · rw [if_neg hik, piK, if_neg hik, abs_zero, zero_mul]

/-- The Gram weight `h_i = (T − i) r^{T−i}` has bounded total mass, uniformly in `T`. -/
private lemma sum_weight_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (T : ℕ) :
    ∑ i : Fin T, ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ))
      ≤ ∑' d : ℕ, ((d : ℝ) + 1) * r ^ (d + 1) := by
  have hmaj : Summable fun d : ℕ => ((d : ℝ) + 1) * r ^ (d + 1) := by
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * r ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    have h0 : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr1
    have hsum := (h1.add h0).mul_right r
    refine hsum.congr fun n => ?_
    rw [pow_succ]
    ring
  have hstep : ∑ i : Fin T, ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ))
      = ∑ d ∈ Finset.range T, ((d : ℝ) + 1) * r ^ (d + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => ((T : ℝ) - n) * r ^ (T - n)) T,
      ← Finset.sum_range_reflect (fun d => ((d : ℝ) + 1) * r ^ (d + 1)) T]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have h1 : T - 1 - i + 1 = T - i := by omega
    rw [h1]
    congr 1
    rw [Nat.cast_sub (by omega : i ≤ T - 1), Nat.cast_sub (by omega : 1 ≤ T)]
    push_cast
    ring
  rw [hstep]
  exact hmaj.sum_le_tsum _ fun d _ => mul_nonneg (by positivity) (pow_nonneg hr0 _)

/-- **The `θ`-free domination of the Gram-tail correction.** -/
private lemma quadForm_gramTail_le_env {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) (hψ : ∀ n, |armaPsi b a n| ≤ C * r ^ n)
    (hB : ARMAInvertibleParams b a) {T : ℕ} (x : Fin T → ℝ) :
    (piMat b a T *ᵥ x) ⬝ᵥ (gramTail b a T *ᵥ (piMat b a T *ᵥ x))
      ≤ (1 - r ^ 2)⁻¹ *
        (∑ i : Fin T, C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) *
          residEnv C r x i) ^ 2 := by
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have hr2lt : r ^ 2 < 1 := by nlinarith [sq_nonneg r]
  have hinv : (0 : ℝ) ≤ (1 - r ^ 2)⁻¹ := by
    have h : (0 : ℝ) < 1 - r ^ 2 := by linarith
    positivity
  refine le_trans (quadForm_gramTail_le_sq hC hr0 hr1 hπ hψ hB _) ?_
  refine mul_le_mul_of_nonneg_left ?_ hinv
  have hwnn : ∀ i : Fin T, (0 : ℝ) ≤ C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) := by
    intro i
    have hle : ((i : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast le_of_lt i.isLt
    have h1 : (0 : ℝ) ≤ (T : ℝ) - (i : ℕ) := by linarith
    positivity
  have hmono : ∑ i : Fin T, C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) *
        |(piMat b a T *ᵥ x) i|
      ≤ ∑ i : Fin T, C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) * residEnv C r x i :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (abs_mulVec_piMat_le hπ x i) (hwnn i)
  have hnn0 : (0 : ℝ) ≤ ∑ i : Fin T, C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) *
      |(piMat b a T *ᵥ x) i| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hwnn i) (abs_nonneg _)
  exact pow_le_pow_left₀ hnn0 hmono 2

end Szego

/-- **Szegő-type limit**: on the constraint set, `T⁻¹ log det Γ_T(b, a) → 0`
(unit-variance model; `det Γ_T = ∏_{j<T} ν_j` with innovations variances `ν_j ↓ 1`
geometrically). -/
theorem logdet_armaToeplitz_vanishes {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * Real.log (armaToeplitz b a T).det)
      atTop (𝓝 0) := by
  obtain ⟨C, r, hC, hr0, hr1, hπ, hψ⟩ := exists_common_geometric_bound hB hB
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
      K = C ^ 4 / (1 - r ^ 2) * ∑' d : ℕ, ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := ⟨_, rfl⟩
  refine squeeze_zero_norm (fun T => ?_) (tendsto_const_div_atTop_nhds_zero_nat K)
  obtain ⟨hlow, hhigh⟩ := log_det_armaToeplitz_bounds hC hr0 hr1 hπ hψ hB T
  have hTnn : (0 : ℝ) ≤ (T : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg T)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hTnn hlow), div_eq_mul_inv, mul_comm K]
  exact mul_le_mul_of_nonneg_left (hKdef ▸ hhigh) hTnn

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Step (B): the correction term `T⁻¹ uᵀ G_T u` vanishes in probability

The remaining ingredients of step (B) of the route recorded at
`armaProfileS_tendstoInProb`. The deterministic bricks are in the `Szego` section above;
here the second-moment matrix `E[u_i u_j]` of the truncated residual vector is computed
and Schur-tested, and Markov's inequality finishes. -/

/-- A linear process over white noise has vanishing mean (the `L²` limit of partial sums
of centred noise). -/
private lemma integral_linearProcess_eq_zero [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ) (hψ : Summable fun j => |ψ j|)
    (hε : IsWhiteNoise ε σ2 μ) (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    ∫ ω, X t ω ∂μ = 0 := by
  have hmem : MemLp (X t) 2 μ := hX.memLp hψ hε hmeas t
  have hint : Integrable (X t) μ := hmem.integrable one_le_two
  have hFmem : ∀ N : ℕ,
      MemLp (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ := by
    intro N
    exact memLp_finset_sum _ fun j _ => (hε.memLp _).const_mul (ψ j)
  have hFzero : ∀ N : ℕ, ∫ ω, (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) ∂μ = 0 := by
    intro N
    rw [integral_finset_sum _ fun j _ => ((hε.memLp _).integrable one_le_two).const_mul (ψ j)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, hε.integral_eq_zero, mul_zero]
  have hL1 : Tendsto (fun N : ℕ => ∫⁻ ω,
      ‖(∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) - X t ω‖ₑ ∂μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hX t)
      (fun N => zero_le) fun N => ?_
    rw [← eLpNorm_one_eq_lintegral_enorm]
    refine le_trans (eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (by norm_num) ?_) ?_
    · exact ((hFmem N).sub hmem).aestronglyMeasurable
    · refine le_of_eq ?_
      rw [show (fun ω => (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) - X t ω)
            = -fun ω => X t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω from by
          funext ω; simp, eLpNorm_neg]
  have hlim := tendsto_integral_of_L1 (X t) hint.aestronglyMeasurable
    (Eventually.of_forall fun N => (hFmem N).integrable one_le_two) hL1
  simp only [hFzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **The second-moment structure of a linear process**: `E[X_s X_t] = σ² γ(s − t)`, the
mean being zero. -/
private lemma integral_mul_linearProcess [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ) (hψ : Summable fun j => |ψ j|)
    (hε : IsWhiteNoise ε σ2 μ) (hmeas : ∀ t, Measurable (X t)) (s t : ℤ) :
    ∫ ω, X s ω * X t ω ∂μ = σ2 * ∑' j : ℕ, ψ j * ψ (j + (s - t).natAbs) := by
  obtain ⟨hstat, hacvf⟩ := hX.isStationary hψ hε hmeas
  have hmem : ∀ r, MemLp (X r) 2 μ := fun r => hX.memLp hψ hε hmeas r
  have hz : ∀ r, ∫ ω, X r ω ∂μ = 0 := fun r =>
    integral_linearProcess_eq_zero hX hψ hε hmeas r
  have hidx : t + (s - t) = s := by ring
  have hshift : cov[X s, X t; μ] = acvf X μ (s - t) := by
    have h := hstat.cov_shift t (s - t)
    rwa [hidx] at h
  have hsub := covariance_eq_sub (μ := μ) (hmem s) (hmem t)
  rw [hshift, hacvf (s - t)] at hsub
  have hprod : μ[X s * X t] = ∫ ω, X s ω * X t ω ∂μ := by simp [Pi.mul_apply]
  rw [hprod, hz s, hz t] at hsub
  linarith [hsub]

/-- Transporting a finite sum of absolute values into a `tsum` along an injection. -/
private lemma finsum_abs_le_tsum {T : ℕ} {ι : Type*} [DecidableEq ι] (F : Fin T → ℝ)
    (g : ι → ℝ) (f : Fin T → ι) (hs : Summable g) (hg : ∀ n, 0 ≤ g n) (s : Finset (Fin T))
    (hzero : ∀ i, i ∉ s → F i = 0) (hbd : ∀ i ∈ s, |F i| ≤ g (f i))
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i = f j → i = j) :
    ∑ i : Fin T, |F i| ≤ ∑' n, g n := by
  have hrestrict : ∑ i : Fin T, |F i| = ∑ i ∈ s, |F i| := by
    refine (Finset.sum_subset (Finset.subset_univ s) fun i _ hi => ?_).symm
    rw [hzero i hi, abs_zero]
  calc ∑ i : Fin T, |F i| = ∑ i ∈ s, |F i| := hrestrict
    _ ≤ ∑ i ∈ s, g (f i) := Finset.sum_le_sum hbd
    _ = ∑ n ∈ s.image f, g n := (Finset.sum_image hinj).symm
    _ ≤ ∑' n, g n := hs.sum_le_tsum _ fun n _ => hg n

/-- Row sums of the one-sided inversion kernel are bounded by `Σ|π|`, uniformly in `T`. -/
private lemma sum_abs_piK_row {T : ℕ} (hπ : Summable fun n => |armaPi b a n|) (i : Fin T) :
    ∑ k : Fin T, |piK b a (i : ℕ) (k : ℕ)| ≤ ∑' n : ℕ, |armaPi b a n| := by
  refine finsum_abs_le_tsum _ (fun n => |armaPi b a n|) (fun k => (k : ℕ) - (i : ℕ)) hπ
    (fun n => abs_nonneg _) (Finset.univ.filter fun k : Fin T => (i : ℕ) ≤ (k : ℕ))
    (fun k hk => ?_) (fun k hk => ?_) (fun k hk l hl hkl => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
    exact piK_eq_zero b a hk
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [piK, if_pos hk]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hl
    have hkl' : (k : ℕ) - (i : ℕ) = (l : ℕ) - (i : ℕ) := hkl
    exact Fin.ext (by omega)

/-- Column sums of the one-sided inversion kernel are bounded by `Σ|π|`. -/
private lemma sum_abs_piK_col {T : ℕ} (hπ : Summable fun n => |armaPi b a n|) (l : Fin T) :
    ∑ j : Fin T, |piK b a (j : ℕ) (l : ℕ)| ≤ ∑' n : ℕ, |armaPi b a n| := by
  refine finsum_abs_le_tsum _ (fun n => |armaPi b a n|) (fun j => (l : ℕ) - (j : ℕ)) hπ
    (fun n => abs_nonneg _) (Finset.univ.filter fun j : Fin T => (j : ℕ) ≤ (l : ℕ))
    (fun j hj => ?_) (fun j hj => ?_) (fun j hj k hk hjk => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
    exact piK_eq_zero b a hj
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [piK, if_pos hj]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
    have hjk' : (l : ℕ) - (j : ℕ) = (l : ℕ) - (k : ℕ) := hjk
    exact Fin.ext (by omega)

/-- The `θ`-free envelope's coefficient row (see `residEnv`) has `ℓ¹` norm at most
`C/(1 − r)`, uniformly in `T` and in the row. -/
private lemma sum_geomCoeff_le {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    {T : ℕ} (i : Fin T) :
    ∑ k : Fin T, (if (i : ℕ) ≤ (k : ℕ) then C * r ^ ((k : ℕ) - (i : ℕ)) else 0)
      ≤ C / (1 - r) := by
  classical
  have hs : Summable fun n : ℕ => C * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hval : ∑' n : ℕ, C * r ^ n = C / (1 - r) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  have habs : ∑ k : Fin T,
      |(if (i : ℕ) ≤ (k : ℕ) then C * r ^ ((k : ℕ) - (i : ℕ)) else 0)|
      = ∑ k : Fin T, (if (i : ℕ) ≤ (k : ℕ) then C * r ^ ((k : ℕ) - (i : ℕ)) else 0) := by
    refine Finset.sum_congr rfl fun k _ => abs_of_nonneg ?_
    split_ifs <;> positivity
  rw [← habs, ← hval]
  refine finsum_abs_le_tsum _ (fun n : ℕ => C * r ^ n) (fun k => (k : ℕ) - (i : ℕ)) hs
    (fun n => by positivity)
    (Finset.univ.filter fun k : Fin T => (i : ℕ) ≤ (k : ℕ)) (fun k hk => ?_)
    (fun k hk => ?_) (fun k hk l hl hkl => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
    rw [if_neg (by omega)]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [if_pos hk, abs_of_nonneg (by positivity)]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hl
    have hkl' : (k : ℕ) - (i : ℕ) = (l : ℕ) - (i : ℕ) := hkl
    exact Fin.ext (by omega)

/-! #### The `θ`-oscillation of the residual sum of squares

The second deterministic input of `mle_consistent`(iii): a *pathwise* Lipschitz-type
estimate for `θ ↦ ‖Π_T(θ) x‖²` whose constant is the `ℓ¹` modulus of `π`
(`exists_armaPi_l1_modulus`) — no derivative `∂π/∂θ` and no expectation. The Schur test
is applied in the bilinear form `Σ_i |(Ax)_i| |(Bx)_i| ≤ D_A D_B ‖x‖²`; the elementary
`|x_k||x_l| ≤ (x_k² + x_l²)/2` is what turns the double kernel sum into the plain
`‖x‖²`, so only row *and* column sums of both kernels are needed. -/

private lemma sum_triple_le {T : ℕ} (A B : Fin T → Fin T → ℝ) (y : Fin T → ℝ)
    (hy : ∀ k, 0 ≤ y k) {DA DB : ℝ}
    (hAcol : ∀ k : Fin T, ∑ i : Fin T, |A i k| ≤ DA)
    (hBrow : ∀ i : Fin T, ∑ l : Fin T, |B i l| ≤ DB) (hDB : 0 ≤ DB) :
    ∑ i : Fin T, ∑ k : Fin T, ∑ l : Fin T, |A i k| * |B i l| * y k
      ≤ DA * DB * ∑ k : Fin T, y k := by
  have h1 : ∀ i k : Fin T, ∑ l : Fin T, |A i k| * |B i l| * y k ≤ |A i k| * y k * DB := by
    intro i k
    have hrw : ∑ l : Fin T, |A i k| * |B i l| * y k
        = (|A i k| * y k) * ∑ l : Fin T, |B i l| := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left (hBrow i) (mul_nonneg (abs_nonneg _) (hy k))
  calc ∑ i : Fin T, ∑ k : Fin T, ∑ l : Fin T, |A i k| * |B i l| * y k
      ≤ ∑ i : Fin T, ∑ k : Fin T, |A i k| * y k * DB :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => h1 i k
    _ = ∑ k : Fin T, (∑ i : Fin T, |A i k|) * (y k * DB) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ k : Fin T, DA * (y k * DB) :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hAcol k) (mul_nonneg (hy k) hDB)
    _ = DA * DB * ∑ k : Fin T, y k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- **The bilinear Schur test**: two doubly summable kernels applied to the same vector
pair up to `‖x‖²` with the product of their `ℓ¹` bounds. -/
private lemma sum_abs_bilin_le {T : ℕ} (A B : Fin T → Fin T → ℝ) (x : Fin T → ℝ)
    {DA DB : ℝ} (hArow : ∀ i : Fin T, ∑ k : Fin T, |A i k| ≤ DA)
    (hAcol : ∀ k : Fin T, ∑ i : Fin T, |A i k| ≤ DA)
    (hBrow : ∀ i : Fin T, ∑ l : Fin T, |B i l| ≤ DB)
    (hBcol : ∀ l : Fin T, ∑ i : Fin T, |B i l| ≤ DB) (hDA : 0 ≤ DA) (hDB : 0 ≤ DB) :
    ∑ i : Fin T, |∑ k : Fin T, A i k * x k| * |∑ l : Fin T, B i l * x l|
      ≤ DA * DB * ∑ k : Fin T, x k ^ 2 := by
  have hstep : ∀ i : Fin T, |∑ k : Fin T, A i k * x k| * |∑ l : Fin T, B i l * x l|
      ≤ ∑ k : Fin T, ∑ l : Fin T, |A i k| * |B i l| * ((x k ^ 2 + x l ^ 2) / 2) := by
    intro i
    have h1 : |∑ k : Fin T, A i k * x k| ≤ ∑ k : Fin T, |A i k| * |x k| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
    have h2 : |∑ l : Fin T, B i l * x l| ≤ ∑ l : Fin T, |B i l| * |x l| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun l _ => ?_)
      rw [abs_mul]
    have hn1 : (0 : ℝ) ≤ ∑ k : Fin T, |A i k| * |x k| :=
      Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc |∑ k : Fin T, A i k * x k| * |∑ l : Fin T, B i l * x l|
        ≤ (∑ k : Fin T, |A i k| * |x k|) * (∑ l : Fin T, |B i l| * |x l|) :=
          mul_le_mul h1 h2 (abs_nonneg _) hn1
      _ = ∑ k : Fin T, ∑ l : Fin T, (|A i k| * |x k|) * (|B i l| * |x l|) :=
          Finset.sum_mul_sum _ _ _ _
      _ ≤ ∑ k : Fin T, ∑ l : Fin T, |A i k| * |B i l| * ((x k ^ 2 + x l ^ 2) / 2) := by
          refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
          have hxx : |x k| * |x l| ≤ (x k ^ 2 + x l ^ 2) / 2 := by
            nlinarith [sq_nonneg (|x k| - |x l|), sq_abs (x k), sq_abs (x l)]
          have hre : (|A i k| * |x k|) * (|B i l| * |x l|)
              = (|A i k| * |B i l|) * (|x k| * |x l|) := by ring
          rw [hre]
          exact mul_le_mul_of_nonneg_left hxx (by positivity)
  have hsplit : ∑ i : Fin T, ∑ k : Fin T, ∑ l : Fin T,
        |A i k| * |B i l| * ((x k ^ 2 + x l ^ 2) / 2)
      = (∑ i : Fin T, ∑ k : Fin T, ∑ l : Fin T, |A i k| * |B i l| * (x k ^ 2 / 2))
        + ∑ i : Fin T, ∑ l : Fin T, ∑ k : Fin T, |B i l| * |A i k| * (x l ^ 2 / 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin T)))
      (t := (Finset.univ : Finset (Fin T)))
      (f := fun l k => |B i l| * |A i k| * (x l ^ 2 / 2)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  refine le_trans (Finset.sum_le_sum fun i _ => hstep i) ?_
  rw [hsplit]
  have hy : ∀ k : Fin T, (0 : ℝ) ≤ x k ^ 2 / 2 := fun k => by positivity
  have hA := sum_triple_le A B (fun k => x k ^ 2 / 2) hy hAcol hBrow hDB
  have hB' := sum_triple_le B A (fun l => x l ^ 2 / 2) hy hBcol hArow hDA
  have hhalf : ∑ k : Fin T, x k ^ 2 / 2 = (∑ k : Fin T, x k ^ 2) / 2 := by
    rw [Finset.sum_div]
  rw [hhalf] at hA hB'
  linarith

/-- Row sums of the difference of two inversion kernels are bounded by the `ℓ¹` modulus
of `π` — the input supplied by `exists_armaPi_l1_modulus`. -/
private lemma sum_abs_piK_sub_row {p q : ℕ} {b1 b2 : Fin p → ℝ} {a1 a2 : Fin q → ℝ}
    {T : ℕ} (hd : Summable fun n => |armaPi b1 a1 n - armaPi b2 a2 n|) (i : Fin T) :
    ∑ k : Fin T, |piK b1 a1 (i : ℕ) (k : ℕ) - piK b2 a2 (i : ℕ) (k : ℕ)|
      ≤ ∑' n : ℕ, |armaPi b1 a1 n - armaPi b2 a2 n| := by
  classical
  refine finsum_abs_le_tsum _ (fun n => |armaPi b1 a1 n - armaPi b2 a2 n|)
    (fun k => (k : ℕ) - (i : ℕ)) hd (fun n => abs_nonneg _)
    (Finset.univ.filter fun k : Fin T => (i : ℕ) ≤ (k : ℕ)) (fun k hk => ?_)
    (fun k hk => ?_) (fun k hk l hl hkl => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
    rw [piK_eq_zero b1 a1 hk, piK_eq_zero b2 a2 hk, sub_zero]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [piK, if_pos hk, piK, if_pos hk]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hl
    have hkl' : (k : ℕ) - (i : ℕ) = (l : ℕ) - (i : ℕ) := hkl
    exact Fin.ext (by omega)

/-- Column sums of the difference of two inversion kernels. -/
private lemma sum_abs_piK_sub_col {p q : ℕ} {b1 b2 : Fin p → ℝ} {a1 a2 : Fin q → ℝ}
    {T : ℕ} (hd : Summable fun n => |armaPi b1 a1 n - armaPi b2 a2 n|) (l : Fin T) :
    ∑ i : Fin T, |piK b1 a1 (i : ℕ) (l : ℕ) - piK b2 a2 (i : ℕ) (l : ℕ)|
      ≤ ∑' n : ℕ, |armaPi b1 a1 n - armaPi b2 a2 n| := by
  classical
  refine finsum_abs_le_tsum _ (fun n => |armaPi b1 a1 n - armaPi b2 a2 n|)
    (fun j => (l : ℕ) - (j : ℕ)) hd (fun n => abs_nonneg _)
    (Finset.univ.filter fun j : Fin T => (j : ℕ) ≤ (l : ℕ)) (fun j hj => ?_)
    (fun j hj => ?_) (fun j hj k hk hjk => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
    rw [piK_eq_zero b1 a1 hj, piK_eq_zero b2 a2 hj, sub_zero]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [piK, if_pos hj, piK, if_pos hj]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
    have hjk' : (l : ℕ) - (j : ℕ) = (l : ℕ) - (k : ℕ) := hjk
    exact Fin.ext (by omega)

open Matrix in
/-- **The pathwise `θ`-oscillation of the residual sum of squares**: the whole `θ`
dependence is carried by the `ℓ¹` modulus of `π`, and the random factor is `‖x‖²`. -/
private lemma abs_residSS_sub_le {p q : ℕ} {b1 b2 : Fin p → ℝ} {a1 a2 : Fin q → ℝ}
    (h1 : Summable fun n => |armaPi b1 a1 n|) (h2 : Summable fun n => |armaPi b2 a2 n|)
    {T : ℕ} (x : Fin T → ℝ) :
    |(piMat b1 a1 T *ᵥ x) ⬝ᵥ (piMat b1 a1 T *ᵥ x)
        - (piMat b2 a2 T *ᵥ x) ⬝ᵥ (piMat b2 a2 T *ᵥ x)|
      ≤ (∑' n : ℕ, |armaPi b1 a1 n - armaPi b2 a2 n|) *
          ((∑' n : ℕ, |armaPi b1 a1 n|) + (∑' n : ℕ, |armaPi b2 a2 n|)) *
          ∑ k : Fin T, x k ^ 2 := by
  have hd : Summable fun n => |armaPi b1 a1 n - armaPi b2 a2 n| := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => abs_sub _ _) (h1.add h2)
  have hD0 : (0 : ℝ) ≤ ∑' n : ℕ, |armaPi b1 a1 n - armaPi b2 a2 n| :=
    tsum_nonneg fun n => abs_nonneg _
  have hP1 : (0 : ℝ) ≤ ∑' n : ℕ, |armaPi b1 a1 n| := tsum_nonneg fun n => abs_nonneg _
  have hP2 : (0 : ℝ) ≤ ∑' n : ℕ, |armaPi b2 a2 n| := tsum_nonneg fun n => abs_nonneg _
  have hid : ∀ i : Fin T, (piMat b1 a1 T *ᵥ x) i - (piMat b2 a2 T *ᵥ x) i
      = ∑ k : Fin T, (piK b1 a1 (i : ℕ) (k : ℕ) - piK b2 a2 (i : ℕ) (k : ℕ)) * x k := by
    intro i
    show (∑ k : Fin T, piK b1 a1 (i : ℕ) (k : ℕ) * x k)
        - (∑ k : Fin T, piK b2 a2 (i : ℕ) (k : ℕ) * x k) = _
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdiff : (piMat b1 a1 T *ᵥ x) ⬝ᵥ (piMat b1 a1 T *ᵥ x)
        - (piMat b2 a2 T *ᵥ x) ⬝ᵥ (piMat b2 a2 T *ᵥ x)
      = ∑ i : Fin T, ((piMat b1 a1 T *ᵥ x) i - (piMat b2 a2 T *ᵥ x) i) *
          ((piMat b1 a1 T *ᵥ x) i + (piMat b2 a2 T *ᵥ x) i) := by
    simp only [dotProduct]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hterm : ∀ i : Fin T,
      |((piMat b1 a1 T *ᵥ x) i - (piMat b2 a2 T *ᵥ x) i) *
          ((piMat b1 a1 T *ᵥ x) i + (piMat b2 a2 T *ᵥ x) i)|
        ≤ |∑ k : Fin T, (piK b1 a1 (i : ℕ) (k : ℕ) - piK b2 a2 (i : ℕ) (k : ℕ)) * x k| *
            |∑ l : Fin T, piK b1 a1 (i : ℕ) (l : ℕ) * x l|
          + |∑ k : Fin T, (piK b1 a1 (i : ℕ) (k : ℕ) - piK b2 a2 (i : ℕ) (k : ℕ)) * x k| *
            |∑ l : Fin T, piK b2 a2 (i : ℕ) (l : ℕ) * x l| := by
    intro i
    rw [abs_mul, hid i, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact abs_add_le _ _
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => hterm i) ?_
  rw [Finset.sum_add_distrib]
  have hb1 := sum_abs_bilin_le
    (fun i k => piK b1 a1 (i : ℕ) (k : ℕ) - piK b2 a2 (i : ℕ) (k : ℕ))
    (fun i l => piK b1 a1 (i : ℕ) (l : ℕ)) x
    (sum_abs_piK_sub_row hd) (sum_abs_piK_sub_col hd)
    (sum_abs_piK_row h1) (sum_abs_piK_col h1) hD0 hP1
  have hb2 := sum_abs_bilin_le
    (fun i k => piK b1 a1 (i : ℕ) (k : ℕ) - piK b2 a2 (i : ℕ) (k : ℕ))
    (fun i l => piK b2 a2 (i : ℕ) (l : ℕ)) x
    (sum_abs_piK_sub_row hd) (sum_abs_piK_sub_col hd)
    (sum_abs_piK_row h2) (sum_abs_piK_col h2) hD0 hP2
  have hsum0 : (0 : ℝ) ≤ ∑ k : Fin T, x k ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  nlinarith [hb1, hb2]

/-- Row sums of the (absolutely summable) model ACVF kernel. -/
private lemma sum_abs_acvfK {p' q' : ℕ} {b' : Fin p' → ℝ} {a' : Fin q' → ℝ} {T : ℕ}
    (hγ : Summable fun m : ℤ => |armaACVF b' a' m|) (c : ℝ) (hc : 0 ≤ c) (k : Fin T) :
    ∑ l : Fin T, |c * armaACVF b' a' (((k : ℕ) : ℤ) - ((l : ℕ) : ℤ))|
      ≤ c * ∑' m : ℤ, |armaACVF b' a' m| := by
  have hstep : ∑ l : Fin T, |c * armaACVF b' a' (((k : ℕ) : ℤ) - ((l : ℕ) : ℤ))|
      = c * ∑ l : Fin T, |armaACVF b' a' (((k : ℕ) : ℤ) - ((l : ℕ) : ℤ))| := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [abs_mul, abs_of_nonneg hc]
  rw [hstep]
  refine mul_le_mul_of_nonneg_left ?_ hc
  refine finsum_abs_le_tsum _ (fun m => |armaACVF b' a' m|)
    (fun l => ((k : ℕ) : ℤ) - ((l : ℕ) : ℤ)) hγ (fun n => abs_nonneg _) Finset.univ
    (fun l hl => absurd (Finset.mem_univ l) hl) (fun l _ => le_of_eq rfl) (fun l _ j _ hlj => ?_)
  have hlj' : ((k : ℕ) : ℤ) - ((l : ℕ) : ℤ) = ((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) := hlj
  exact Fin.ext (by omega)

/-- **The Schur-test row bound** for a doubly filtered kernel: the row sums of
`Σ_{k,l} A_k B_{jl} g_{kl}` are bounded by `P · (P · Γ)`. -/
private lemma rowSum_kernel_le {T : ℕ} (A : Fin T → ℝ) (B : Fin T → Fin T → ℝ)
    (g : Fin T → Fin T → ℝ) {P Γ : ℝ} (hA : ∑ k, |A k| ≤ P) (hB : ∀ l, ∑ j, |B j l| ≤ P)
    (hg : ∀ k, ∑ l, |g k l| ≤ Γ) (hP : 0 ≤ P) (hΓ : 0 ≤ Γ) :
    ∑ j : Fin T, |∑ k : Fin T, ∑ l : Fin T, A k * B j l * g k l| ≤ P * (P * Γ) := by
  have hstep1 : ∀ j : Fin T, |∑ k : Fin T, ∑ l : Fin T, A k * B j l * g k l|
      ≤ ∑ k : Fin T, ∑ l : Fin T, |A k| * |B j l| * |g k l| := by
    intro j
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul, abs_mul]
  calc ∑ j : Fin T, |∑ k : Fin T, ∑ l : Fin T, A k * B j l * g k l|
      ≤ ∑ j : Fin T, ∑ k : Fin T, ∑ l : Fin T, |A k| * |B j l| * |g k l| :=
        Finset.sum_le_sum fun j _ => hstep1 j
    _ = ∑ k : Fin T, ∑ j : Fin T, ∑ l : Fin T, |A k| * |B j l| * |g k l| := Finset.sum_comm
    _ = ∑ k : Fin T, ∑ l : Fin T, ∑ j : Fin T, |A k| * |B j l| * |g k l| :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ ≤ ∑ k : Fin T, ∑ l : Fin T, |A k| * |g k l| * P := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        have hrw : ∑ j : Fin T, |A k| * |B j l| * |g k l|
            = (|A k| * |g k l|) * ∑ j : Fin T, |B j l| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hrw]
        exact mul_le_mul_of_nonneg_left (hB l) (by positivity)
    _ ≤ ∑ k : Fin T, |A k| * P * Γ := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hrw : ∑ l : Fin T, |A k| * |g k l| * P = (|A k| * P) * ∑ l : Fin T, |g k l| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [hrw]
        exact mul_le_mul_of_nonneg_left (hg k) (by positivity)
    _ = (∑ k : Fin T, |A k|) * (P * Γ) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ P * (P * Γ) := mul_le_mul_of_nonneg_right hA (by positivity)

open Matrix in
/-- **The expected quadratic form of a psd matrix** against a random vector is controlled
by the trace, once the second-moment matrix has bounded row sums (this is where
`sum_entry_mul_le_of_posSemidef` is used). -/
private lemma integral_quadForm_le {T : ℕ} (G : Matrix (Fin T) (Fin T) ℝ) (hG : G.PosSemidef)
    (u : Fin T → Ω → ℝ) (hu : ∀ i, MemLp (u i) 2 μ) {R : ℝ}
    (hrow : ∀ i, ∑ j, |∫ ω, u i ω * u j ω ∂μ| ≤ R) :
    ∫ ω, (fun i => u i ω) ⬝ᵥ (G *ᵥ fun i => u i ω) ∂μ ≤ R * G.trace := by
  have hint : ∀ i j : Fin T, Integrable (fun ω => u i ω * u j ω) μ := by
    intro i j
    have h := (hu i).integrable_mul (hu j)
    exact h.congr (by filter_upwards with ω using rfl)
  have hexp : ∀ ω, (fun i => u i ω) ⬝ᵥ (G *ᵥ fun i => u i ω)
      = ∑ i : Fin T, ∑ j : Fin T, G i j * (u i ω * u j ω) := by
    intro ω
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  calc ∫ ω, (fun i => u i ω) ⬝ᵥ (G *ᵥ fun i => u i ω) ∂μ
      = ∑ i : Fin T, ∑ j : Fin T, G i j * ∫ ω, u i ω * u j ω ∂μ := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
          integral_finset_sum _ fun i _ =>
            integrable_finset_sum _ fun j _ => (hint i j).const_mul (G i j)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finset_sum _ fun j _ => (hint i j).const_mul (G i j)]
        exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    _ ≤ R * G.trace := by
        refine sum_entry_mul_le_of_posSemidef hG (fun i j => ?_) hrow
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

open Matrix in
/-- Integrability of the quadratic form (same finite-sum expansion as
`integral_quadForm_le`). -/
private lemma integrable_quadForm {T : ℕ} (G : Matrix (Fin T) (Fin T) ℝ)
    (u : Fin T → Ω → ℝ) (hu : ∀ i, MemLp (u i) 2 μ) :
    Integrable (fun ω => (fun i => u i ω) ⬝ᵥ (G *ᵥ fun i => u i ω)) μ := by
  have hint : ∀ i j : Fin T, Integrable (fun ω => u i ω * u j ω) μ := by
    intro i j
    have h := (hu i).integrable_mul (hu j)
    exact h.congr (by filter_upwards with ω using rfl)
  refine Integrable.congr (integrable_finset_sum (Finset.univ : Finset (Fin T)) fun i _ =>
    integrable_finset_sum (Finset.univ : Finset (Fin T)) fun j _ =>
      (hint i j).const_mul (G i j)) ?_
  filter_upwards with ω
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

open Matrix in
/-- **Step (B) — the correction term vanishes in probability**:
`T⁻¹ uᵀ G_T u →p 0` for `u = Π_T x` the truncated `θ`-residual vector of the true
process.

The proof is the one recorded at `armaProfileS_tendstoInProb`, with the operator-norm
step replaced by the Schur test: `E[u_i u_j] = σ² Σ_{k,l} π̃(i,k) π̃(j,l) γ_{θ₀}(k − l)`
has row sums bounded by `(Σ|π|)² · σ² Σ|γ|` uniformly in `T` and `i`
(`rowSum_kernel_le` over `sum_abs_piK_row`, `sum_abs_piK_col`, `sum_abs_acvfK`), so
`E[uᵀ G_T u] ≤ R · tr G_T ≤ R · K` with `K` the uniform trace bound
(`trace_gramTail_le`). Markov's inequality on the nonnegative variable `T⁻¹ uᵀ G_T u`
finishes. -/
private lemma gramTail_quadForm_tendstoInProb [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (hwn : IsWhiteNoise ε σ2 μ) (hσ : 0 ≤ σ2)
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T : ℕ => (μ {ω | η ≤ (T : ℝ)⁻¹ *
        ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
          (gramTail b a T *ᵥ
            (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))}).toReal)
      atTop (𝓝 0) := by
  have hπ : Summable fun n => |armaPi b a n| := summable_abs_armaPi hB
  have hγ : Summable fun k : ℤ => |armaACVF b0 a0 k| := summable_abs_armaACVF hB0
  have hψ : Summable fun n => |armaPsi b0 a0 n| := summable_abs_armaPsi a0 hB0.1
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ∑' n : ℕ, |armaPi b a n| := ⟨_, rfl⟩
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : ℝ, Γ = ∑' m : ℤ, |armaACVF b0 a0 m| := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := hPdef ▸ tsum_nonneg fun n => abs_nonneg _
  have hΓ0 : 0 ≤ Γ := hΓdef ▸ tsum_nonneg fun m => abs_nonneg _
  obtain ⟨C, r, hC, hr0, hr1, hπg, hψg⟩ := exists_common_geometric_bound hB hB
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
      K = C ^ 4 / (1 - r ^ 2) * ∑' d : ℕ, ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := ⟨_, rfl⟩
  have hKtr : ∀ T : ℕ, (gramTail b a T).trace ≤ K := fun T =>
    hKdef ▸ trace_gramTail_le hC hr0 hr1 hπg hψg hB T
  have hK0 : 0 ≤ K := by simpa using hKtr 0
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = P * (P * (σ2 * Γ)) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  -- the entries of the residual vector, and their second moments
  have humem : ∀ (T : ℕ) (i : Fin T),
      MemLp (fun ω => (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i) 2 μ := by
    intro T i
    have : (fun ω => (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i)
        = fun ω => ∑ k : Fin T, piK b a (i : ℕ) (k : ℕ) * X (((k : ℕ) : ℤ) + 1) ω := rfl
    rw [this]
    exact memLp_finset_sum _ fun k _ =>
      (hcausal.memLp hψ hwn hmeas _).const_mul (piK b a (i : ℕ) (k : ℕ))
  have hmoment : ∀ (T : ℕ) (i j : Fin T),
      ∫ ω, (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i *
        (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) j ∂μ
        = ∑ k : Fin T, ∑ l : Fin T, piK b a (i : ℕ) (k : ℕ) * piK b a (j : ℕ) (l : ℕ) *
            (σ2 * armaACVF b0 a0 (((k : ℕ) : ℤ) - ((l : ℕ) : ℤ))) := by
    intro T i j
    have hXint : ∀ k l : Fin T, Integrable
        (fun ω => X (((k : ℕ) : ℤ) + 1) ω * X (((l : ℕ) : ℤ) + 1) ω) μ := by
      intro k l
      have h := (hcausal.memLp hψ hwn hmeas (((k : ℕ) : ℤ) + 1)).integrable_mul
        (hcausal.memLp hψ hwn hmeas (((l : ℕ) : ℤ) + 1))
      exact h.congr (by filter_upwards with ω using rfl)
    have hexp : ∀ ω, (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i *
        (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) j
        = ∑ k : Fin T, ∑ l : Fin T, (piK b a (i : ℕ) (k : ℕ) * piK b a (j : ℕ) (l : ℕ)) *
            (X (((k : ℕ) : ℤ) + 1) ω * X (((l : ℕ) : ℤ) + 1) ω) := by
      intro ω
      show (∑ k : Fin T, piK b a (i : ℕ) (k : ℕ) * X (((k : ℕ) : ℤ) + 1) ω) *
          (∑ l : Fin T, piK b a (j : ℕ) (l : ℕ) * X (((l : ℕ) : ℤ) + 1) ω) = _
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
      integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ =>
        (hXint k l).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ fun l _ => (hXint k l).const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hidx : ((((k : ℕ) : ℤ) + 1) - (((l : ℕ) : ℤ) + 1))
        = ((k : ℕ) : ℤ) - ((l : ℕ) : ℤ) := by ring
    rw [integral_const_mul, integral_mul_linearProcess hcausal hψ hwn hmeas, hidx, armaACVF]
  -- the row-sum bound, uniform in `T` and in the row index
  have hrow : ∀ (T : ℕ) (i : Fin T),
      ∑ j : Fin T, |∫ ω, (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i *
        (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) j ∂μ| ≤ R := by
    intro T i
    have hcongr : ∀ j : Fin T,
        |∫ ω, (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i *
          (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) j ∂μ|
          = |∑ k : Fin T, ∑ l : Fin T, piK b a (i : ℕ) (k : ℕ) * piK b a (j : ℕ) (l : ℕ) *
              (σ2 * armaACVF b0 a0 (((k : ℕ) : ℤ) - ((l : ℕ) : ℤ)))| := by
      intro j; rw [hmoment T i j]
    rw [Finset.sum_congr rfl fun j _ => hcongr j, hRdef]
    exact rowSum_kernel_le _ _ _ (hPdef ▸ sum_abs_piK_row hπ i)
      (fun l => hPdef ▸ sum_abs_piK_col hπ l)
      (fun k => hΓdef ▸ sum_abs_acvfK hγ σ2 hσ k) hP0 (by positivity)
  -- Markov
  refine squeeze_zero' (Eventually.of_forall fun T => ENNReal.toReal_nonneg) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (R * K / η))
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hpsd := gramTail_posSemidef hB T
  have hZnn : 0 ≤ᵐ[μ] fun ω => (T : ℝ)⁻¹ *
      ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
        (gramTail b a T *ᵥ (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))) := by
    filter_upwards with ω
    refine mul_nonneg (by positivity) ?_
    have := hpsd.dotProduct_mulVec_nonneg
      (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
    rwa [star_trivial] at this
  have hZint : Integrable (fun ω =>
      (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
        (gramTail b a T *ᵥ (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))) μ :=
    integrable_quadForm (gramTail b a T) _ (humem T)
  have hbnd : ∫ ω, (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
      (gramTail b a T *ᵥ (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)) ∂μ
      ≤ R * K := by
    refine le_trans (integral_quadForm_le (gramTail b a T) hpsd _ (humem T) (hrow T)) ?_
    exact mul_le_mul_of_nonneg_left (hKtr T) hR0
  have hmark := mul_meas_ge_le_integral_of_nonneg hZnn (hZint.const_mul (T : ℝ)⁻¹) η
  rw [integral_const_mul] at hmark
  have hle : η * (μ.real {ω | η ≤ (T : ℝ)⁻¹ *
      ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
        (gramTail b a T *ᵥ (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))})
      ≤ (T : ℝ)⁻¹ * (R * K) :=
    hmark.trans (mul_le_mul_of_nonneg_left hbnd (by positivity))
  rw [measureReal_def] at hle
  have key : ∀ M : ℝ, 0 ≤ M → η * M ≤ (T : ℝ)⁻¹ * (R * K) → M ≤ R * K / η / T := by
    intro M hM0 hM
    rw [div_div, le_div_iff₀ (by positivity)]
    have h3 : (T : ℝ)⁻¹ * (R * K) * T = R * K := by field_simp
    have h4 := mul_le_mul_of_nonneg_right hM (le_of_lt hTpos)
    rw [h3] at h4
    nlinarith [h4]
  exact key _ ENNReal.toReal_nonneg hle


/-! ### Step (C): the residual sum-of-squares LLN

The machinery of the ergodic-theorem-free route recorded at
`armaResidualSS_tendstoInProb`: an `L²`-norm bookkeeping device, the doubly truncated
residual `z_i^{(m)} = Σ_{d,n<m} π_d ψ_n ε_{i+1+d−n}` (a fixed linear functional of a
*finite* block of the i.i.d. noise), its shift-invariance in law, and the independence
of the blocks along an arithmetic progression of step `2m`. -/

/-- The `L²(μ)` norm of a real function, as a real number. A bookkeeping device: the
defect estimates below are triangle inequalities, and this makes them one-liners. -/
noncomputable def l2n (μ : Measure Ω) (f : Ω → ℝ) : ℝ := Real.sqrt (∫ ω, f ω ^ 2 ∂μ)

lemma l2n_nonneg (μ : Measure Ω) (f : Ω → ℝ) : 0 ≤ l2n μ f := Real.sqrt_nonneg _

private lemma real_inner_mul' (x y : ℝ) : inner ℝ x y = x * y := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp [mul_comm]

private lemma inner_toLp' {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [real_inner_mul', h1, h2]

private lemma l2n_eq_norm_toLp {f : Ω → ℝ} (hf : MemLp f 2 μ) : l2n μ f = ‖hf.toLp f‖ := by
  have h : ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp' hf hf]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  rw [l2n, ← h, Real.sqrt_sq (norm_nonneg _)]

lemma l2n_add_le {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    l2n μ (fun ω => f ω + g ω) ≤ l2n μ f + l2n μ g := by
  have hfg : MemLp (fun ω => f ω + g ω) 2 μ := hf.add hg
  rw [l2n_eq_norm_toLp hfg, l2n_eq_norm_toLp hf, l2n_eq_norm_toLp hg]
  have hsum : hfg.toLp (fun ω => f ω + g ω) = hf.toLp f + hg.toLp g := rfl
  rw [hsum]
  exact norm_add_le _ _

lemma l2n_finset_sum_le {ι : Type*} (s : Finset ι) (F : ι → Ω → ℝ)
    (hF : ∀ i, MemLp (F i) 2 μ) :
    l2n μ (fun ω => ∑ i ∈ s, F i ω) ≤ ∑ i ∈ s, l2n μ (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [l2n]
  | insert i s hi ih =>
      have hstep : (fun ω => ∑ j ∈ insert i s, F j ω)
          = fun ω => F i ω + ∑ j ∈ s, F j ω := by
        funext ω; rw [Finset.sum_insert hi]
      rw [hstep, Finset.sum_insert hi]
      have := l2n_add_le (hF i) (memLp_finset_sum (μ := μ) s fun j _ => hF j)
      linarith [ih]

lemma l2n_const_mul (c : ℝ) (f : Ω → ℝ) :
    l2n μ (fun ω => c * f ω) = |c| * l2n μ f := by
  have hpt : ∀ ω : Ω, (c * f ω) ^ 2 = c ^ 2 * f ω ^ 2 := fun ω => by ring
  have hint : ∫ ω, (c * f ω) ^ 2 ∂μ = c ^ 2 * ∫ ω, f ω ^ 2 ∂μ := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  rw [l2n, l2n, hint, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma integral_sq_le_of_l2n_le {f : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : l2n μ f ≤ c) :
    ∫ ω, f ω ^ 2 ∂μ ≤ c ^ 2 := by
  have h0 : 0 ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hsq : l2n μ f ^ 2 = ∫ ω, f ω ^ 2 ∂μ := Real.sq_sqrt h0
  nlinarith [l2n_nonneg μ f]

/-- **Shift invariance of finite i.i.d. blocks**: the joint law of `(ε_{u a + k})_a` does
not depend on the shift `k`. (The same device as in `LinearProcess.lean`, which keeps its
copy `private`.) -/
private lemma map_noise_block' [IsProbabilityMeasure μ] {A : Type*} [Finite A] {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (u : A → ℤ) (k : ℤ) :
    μ.map (fun ω a => ε (u a + k) ω) = μ.map (fun ω a => ε (u a) ω) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  set S : Finset ℤ := Finset.image u Finset.univ with hS
  set ρ : A → {x // x ∈ S} :=
    fun a => ⟨u a, Finset.mem_image_of_mem u (Finset.mem_univ a)⟩ with hρ
  have hlaw : ∀ c : ℤ, μ.map (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω)
      = Measure.pi (fun _ : {x // x ∈ S} => μ.map (ε 0)) := by
    intro c
    have hinj : Function.Injective (fun b : {x // x ∈ S} => (b : ℤ) + c) := by
      intro b1 b2 h
      exact Subtype.ext (by simpa using h)
    have hindep : iIndepFun (fun b : {x // x ∈ S} => ε ((b : ℤ) + c)) μ :=
      hε.iIndep.precomp hinj
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun b => (hε.measurable _).aemeasurable).1 hindep]
    exact congrArg Measure.pi (funext fun b => (hε.identDistrib _ 0).map_eq)
  have hmb : ∀ c : ℤ, Measurable (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω) :=
    fun c => measurable_pi_lambda _ fun b => hε.measurable _
  have hcomp : Measurable (fun v : {x // x ∈ S} → ℝ => v ∘ ρ) :=
    measurable_pi_lambda _ fun a => measurable_pi_apply (ρ a)
  have hfac : ∀ c : ℤ, (fun ω a => ε (u a + c) ω)
      = (fun v : {x // x ∈ S} → ℝ => v ∘ ρ) ∘ (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω) :=
    fun c => rfl
  have hzero : (fun ω a => ε (u a) ω)
      = (fun v : {x // x ∈ S} → ℝ => v ∘ ρ) ∘
        (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + 0) ω) := by
    funext ω a
    simp only [Function.comp_apply, add_zero, hρ]
  rw [hfac k, hzero, ← Measure.map_map hcomp (hmb k), ← Measure.map_map hcomp (hmb 0),
    hlaw k, hlaw 0]

/-- The **doubly truncated residual** `z_i^{(m)} = Σ_{d,n<m} π_d ψ_n ε_{i+1+d−n}`: the
`m`-truncation of the composite filter applied to the `m`-truncation of the linear
process. It is a fixed linear functional of the noise block over the window
`[i+1−m, i+m]`, which is what makes the progression device work. -/
private noncomputable def blockResid (π ψ : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (m i : ℕ) : Ω → ℝ :=
  fun ω => ∑ x : Fin m × Fin m,
    π (x.1 : ℕ) * ψ (x.2 : ℕ) * ε (1 + ((x.1 : ℕ) : ℤ) - ((x.2 : ℕ) : ℤ) + (i : ℤ)) ω

private lemma measurable_blockResid {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t))
    (π ψ : ℕ → ℝ) (m i : ℕ) : Measurable (blockResid π ψ ε m i) :=
  Finset.measurable_sum _ fun _ _ => (hm _).const_mul _

private lemma memLp_blockResid [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsWhiteNoise ε σ2 μ) (π ψ : ℕ → ℝ) (m i : ℕ) :
    MemLp (blockResid π ψ ε m i) 2 μ :=
  memLp_finset_sum _ fun _ _ => (hε.memLp _).const_mul _

/-- The block index map `x ↦ 1 + x₁ − x₂` of the window. -/
private def blkIdx (m : ℕ) : Fin m × Fin m → ℤ :=
  fun x => 1 + ((x.1 : ℕ) : ℤ) - ((x.2 : ℕ) : ℤ)

/-- The linear functional the block is fed through. -/
private noncomputable def blkFun (π ψ : ℕ → ℝ) (m : ℕ) : (Fin m × Fin m → ℝ) → ℝ :=
  fun v => ∑ x : Fin m × Fin m, π (x.1 : ℕ) * ψ (x.2 : ℕ) * v x

private lemma measurable_blkFun (π ψ : ℕ → ℝ) (m : ℕ) : Measurable (blkFun π ψ m) :=
  Finset.measurable_sum _ fun x _ => (measurable_pi_apply x).const_mul _

/-- **Shift invariance in law of the truncated residual**: `z_i^{(m)}` has the same law
as `z_0^{(m)}`, hence `IdentDistrib` for the squares. -/
private lemma identDistrib_blockResid_sq [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε σ2 μ) (π ψ : ℕ → ℝ) (m i j : ℕ) :
    IdentDistrib (fun ω => blockResid π ψ ε m i ω ^ 2)
      (fun ω => blockResid π ψ ε m j ω ^ 2) μ μ := by
  have hΦ : Measurable (fun v : Fin m × Fin m → ℝ => (blkFun π ψ m v) ^ 2) :=
    (measurable_blkFun π ψ m).pow_const 2
  have hblk : ∀ c : ℤ, Measurable (fun ω (x : Fin m × Fin m) => ε (blkIdx m x + c) ω) :=
    fun c => measurable_pi_lambda _ fun _ => hε.measurable _
  have hfac : ∀ c : ℕ, (fun ω => blockResid π ψ ε m c ω ^ 2)
      = (fun v : Fin m × Fin m → ℝ => (blkFun π ψ m v) ^ 2)
        ∘ (fun ω (x : Fin m × Fin m) => ε (blkIdx m x + (c : ℤ)) ω) := fun c => rfl
  have hmap : ∀ c : ℕ, μ.map (fun ω => blockResid π ψ ε m c ω ^ 2)
      = Measure.map (fun v : Fin m × Fin m → ℝ => (blkFun π ψ m v) ^ 2)
          (μ.map (fun ω (x : Fin m × Fin m) => ε (blkIdx m x) ω)) := by
    intro c
    rw [hfac c, ← Measure.map_map hΦ (hblk (c : ℤ)), map_noise_block' hε (blkIdx m) (c : ℤ)]
  refine ⟨?_, ?_, ?_⟩
  · exact ((measurable_blockResid hε.measurable π ψ m i).pow_const 2).aemeasurable
  · exact ((measurable_blockResid hε.measurable π ψ m j).pow_const 2).aemeasurable
  · rw [hmap i, hmap j]

/-- **Independence along a progression of step `2m`**: the windows of `z_i^{(m)}` and
`z_j^{(m)}` are disjoint blocks of the i.i.d. noise as soon as `j ≥ i + 2m`. -/
private lemma indepFun_blockResid_sq [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε σ2 μ) (π ψ : ℕ → ℝ) {m i j : ℕ} (hij : i + 2 * m ≤ j) :
    IndepFun (fun ω => blockResid π ψ ε m i ω ^ 2)
      (fun ω => blockResid π ψ ε m j ω ^ 2) μ := by
  classical
  set S : ℕ → Finset ℤ := fun c => Finset.Icc ((c : ℤ) + 1 - (m : ℤ)) ((c : ℤ) + (m : ℤ))
    with hSdef
  have hmem : ∀ (c : ℕ) (x : Fin m × Fin m), blkIdx m x + (c : ℤ) ∈ S c := by
    intro c x
    have h1 := x.1.isLt
    have h2 := x.2.isLt
    simp only [hSdef, Finset.mem_Icc, blkIdx]
    omega
  have hdisj : Disjoint (S i) (S j) := by
    refine Finset.disjoint_left.2 fun x hx hx' => ?_
    simp only [hSdef, Finset.mem_Icc] at hx hx'
    omega
  set Φ : ∀ c : ℕ, ({x // x ∈ S c} → ℝ) → ℝ := fun c v =>
    (∑ x : Fin m × Fin m,
      π (x.1 : ℕ) * ψ (x.2 : ℕ) * v ⟨blkIdx m x + (c : ℤ), hmem c x⟩) ^ 2 with hΦdef
  have hΦm : ∀ c : ℕ, Measurable (Φ c) := by
    intro c
    rw [hΦdef]
    refine Measurable.pow_const (Finset.measurable_sum _ fun x _ => ?_) 2
    exact Measurable.const_mul (measurable_pi_apply
      (⟨blkIdx m x + (c : ℤ), hmem c x⟩ : {y // y ∈ S c})) _
  have hfac : ∀ c : ℕ, (fun ω => blockResid π ψ ε m c ω ^ 2)
      = (Φ c) ∘ (fun ω (y : {x // x ∈ S c}) => ε (y : ℤ) ω) := fun c => rfl
  have hbase := ProbabilityTheory.iIndepFun.indepFun_finset (μ := μ) (f := ε) (S i) (S j)
    hdisj hε.iIndep hε.measurable
  rw [hfac i, hfac j]
  exact hbase.comp (hΦm i) (hΦm j)

/-- The **truncated composite filter** `c_r^{(m)} = Σ_{d+n=r, d,n<m} π_d ψ_n`; it agrees
with `contrastCoeff` below the truncation level (`cTrunc_eq_of_lt`). -/
private noncomputable def cTrunc (π ψ : ℕ → ℝ) (m r : ℕ) : ℝ :=
  ∑ x : Fin m × Fin m, if (x.1 : ℕ) + (x.2 : ℕ) = r then π (x.1 : ℕ) * ψ (x.2 : ℕ) else 0

/-- Second moments of white noise: `E[ε_α ε_β] = σ² δ_{αβ}` (the means vanish). -/
private lemma integral_noise_mul' [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsWhiteNoise ε σ2 μ) (α β : ℤ) :
    ∫ ω, ε α ω * ε β ω ∂μ = if α = β then σ2 else 0 := by
  have h := covariance_eq_sub (hε.memLp α) (hε.memLp β)
  rw [hε.integral_eq_zero α, zero_mul, sub_zero] at h
  have h2 : μ[ε α * ε β] = ∫ ω, ε α ω * ε β ω ∂μ := by simp [Pi.mul_apply]
  rw [h2] at h
  rw [← h]
  by_cases hab : α = β
  · subst hab
    rw [if_pos rfl, covariance_self (hε.memLp α).aestronglyMeasurable.aemeasurable,
      hε.variance_eq α]
  · rw [if_neg hab, hε.uncorrelated α β hab]

/-- **The window form of the second moment**: `E[(z_i^{(m)})²] = σ² Σ_{x,y} 1{x₁−x₂ =
y₁−y₂} π ψ π ψ`. The constraint is on the *difference* of the two block coordinates,
because the block index is `1 + d − n + i`. -/
private lemma integral_blockResid_sq [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsWhiteNoise ε σ2 μ) (π ψ : ℕ → ℝ) (m i : ℕ) :
    ∫ ω, blockResid π ψ ε m i ω ^ 2 ∂μ
      = σ2 * ∑ x : Fin m × Fin m, ∑ y : Fin m × Fin m,
          (if ((x.1 : ℕ) : ℤ) - ((x.2 : ℕ) : ℤ) = ((y.1 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ)
            then (π (x.1 : ℕ) * ψ (x.2 : ℕ)) * (π (y.1 : ℕ) * ψ (y.2 : ℕ)) else 0) := by
  classical
  set c : Fin m × Fin m → ℝ := fun x => π (x.1 : ℕ) * ψ (x.2 : ℕ) with hc
  set t : Fin m × Fin m → ℤ :=
    fun x => 1 + ((x.1 : ℕ) : ℤ) - ((x.2 : ℕ) : ℤ) + (i : ℤ) with ht
  have hint : ∀ x y : Fin m × Fin m, Integrable (fun ω => ε (t x) ω * ε (t y) ω) μ := by
    intro x y
    exact ((hε.memLp (t x)).integrable_mul (hε.memLp (t y))).congr
      (Filter.Eventually.of_forall fun ω => rfl)
  have hpt : ∀ ω, blockResid π ψ ε m i ω ^ 2
      = ∑ x : Fin m × Fin m, ∑ y : Fin m × Fin m,
          (c x * c y) * (ε (t x) ω * ε (t y) ω) := by
    intro ω
    show (∑ x : Fin m × Fin m, c x * ε (t x) ω) ^ 2 = _
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finset_sum _ fun x _ =>
      integrable_finset_sum _ fun y _ => (hint x y).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finset_sum _ fun y _ => (hint x y).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hcm : ∫ ω, (c x * c y) * (ε (t x) ω * ε (t y) ω) ∂μ
      = (c x * c y) * ∫ ω, ε (t x) ω * ε (t y) ω ∂μ := integral_const_mul _ _
  rw [hcm, integral_noise_mul' hε]
  have hiff : (t x = t y) ↔
      (((x.1 : ℕ) : ℤ) - ((x.2 : ℕ) : ℤ) = ((y.1 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ)) := by
    simp only [ht]
    omega
  by_cases h : ((x.1 : ℕ) : ℤ) - ((x.2 : ℕ) : ℤ) = ((y.1 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ)
  · rw [if_pos (hiff.2 h), if_pos h]
    simp only [hc]
    ring
  · rw [if_neg (fun hh => h (hiff.1 hh)), if_neg h]
    ring

/-- **The combinatorial Parseval identity**, the step that replaces a Fourier argument:
the swap `((d,n),(d′,n′)) ↦ ((d,n′),(d′,n))` is an involution of the index set carrying
the *difference* constraint `d − n = d′ − n′` to the *sum* constraint `d + n′ = d′ + n`,
and it leaves the summand `π_d ψ_n π_{d′} ψ_{n′}` untouched. So the second moment of the
window equals the sum of squares of the truncated composite filter. -/
private lemma sum_pairs_swap (π ψ : ℕ → ℝ) (m : ℕ) :
    (∑ x : Fin m × Fin m, ∑ y : Fin m × Fin m,
        (if ((x.1 : ℕ) : ℤ) - ((x.2 : ℕ) : ℤ) = ((y.1 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ)
          then (π (x.1 : ℕ) * ψ (x.2 : ℕ)) * (π (y.1 : ℕ) * ψ (y.2 : ℕ)) else 0))
      = ∑ x : Fin m × Fin m, ∑ y : Fin m × Fin m,
        (if (x.1 : ℕ) + (x.2 : ℕ) = (y.1 : ℕ) + (y.2 : ℕ)
          then (π (x.1 : ℕ) * ψ (x.2 : ℕ)) * (π (y.1 : ℕ) * ψ (y.2 : ℕ)) else 0) := by
  classical
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    (⟨fun z : (Fin m × Fin m) × (Fin m × Fin m) => ((z.1.1, z.2.2), (z.2.1, z.1.2)),
      fun z : (Fin m × Fin m) × (Fin m × Fin m) => ((z.1.1, z.2.2), (z.2.1, z.1.2)),
      fun z => rfl, fun z => rfl⟩) _ _ ?_
  rintro ⟨⟨d, n⟩, ⟨d', n'⟩⟩
  simp only [Equiv.coe_fn_mk]
  by_cases h : ((d : ℕ) : ℤ) - ((n : ℕ) : ℤ) = ((d' : ℕ) : ℤ) - ((n' : ℕ) : ℤ)
  · rw [if_pos h, if_pos (by omega : (d : ℕ) + (n' : ℕ) = (d' : ℕ) + (n : ℕ))]
    ring
  · rw [if_neg h, if_neg (by omega : ¬((d : ℕ) + (n' : ℕ) = (d' : ℕ) + (n : ℕ)))]

/-- The sum-constrained pairing collapses fibrewise into `Σ_r (c_r^{(m)})²`. -/
private lemma sum_sq_cTrunc (π ψ : ℕ → ℝ) (m : ℕ) :
    ∑ r ∈ Finset.range (2 * m), cTrunc π ψ m r ^ 2
      = ∑ x : Fin m × Fin m, ∑ y : Fin m × Fin m,
        (if (x.1 : ℕ) + (x.2 : ℕ) = (y.1 : ℕ) + (y.2 : ℕ)
          then (π (x.1 : ℕ) * ψ (x.2 : ℕ)) * (π (y.1 : ℕ) * ψ (y.2 : ℕ)) else 0) := by
  classical
  have hexp : ∀ r : ℕ, cTrunc π ψ m r ^ 2
      = ∑ x : Fin m × Fin m, ∑ y : Fin m × Fin m,
          (if (x.1 : ℕ) + (x.2 : ℕ) = r then π (x.1 : ℕ) * ψ (x.2 : ℕ) else 0) *
          (if (y.1 : ℕ) + (y.2 : ℕ) = r then π (y.1 : ℕ) * ψ (y.2 : ℕ) else 0) := by
    intro r
    rw [cTrunc, sq, Finset.sum_mul_sum]
  simp only [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hx : (x.1 : ℕ) + (x.2 : ℕ) ∈ Finset.range (2 * m) := by
    have h1 := x.1.isLt
    have h2 := x.2.isLt
    simp only [Finset.mem_range]
    omega
  by_cases h : (x.1 : ℕ) + (x.2 : ℕ) = (y.1 : ℕ) + (y.2 : ℕ)
  · rw [if_pos h, Finset.sum_eq_single ((x.1 : ℕ) + (x.2 : ℕ))]
    · rw [if_pos rfl, if_pos h.symm]
    · intro r _ hr
      rw [if_neg (Ne.symm hr), zero_mul]
    · intro hnot
      exact absurd hx hnot
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases h1 : (x.1 : ℕ) + (x.2 : ℕ) = r
    · rw [if_neg (by omega : ¬((y.1 : ℕ) + (y.2 : ℕ) = r)), mul_zero]
    · rw [if_neg h1, zero_mul]

/-- **The second moment of the truncated residual**: `E[(z_i^{(m)})²] = σ² Σ_r
(c_r^{(m)})²`, the same at every `i`. -/
private lemma integral_blockResid_sq_eq [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsWhiteNoise ε σ2 μ) (π ψ : ℕ → ℝ) (m i : ℕ) :
    ∫ ω, blockResid π ψ ε m i ω ^ 2 ∂μ
      = σ2 * ∑ r ∈ Finset.range (2 * m), cTrunc π ψ m r ^ 2 := by
  rw [integral_blockResid_sq hε π ψ m i, sum_pairs_swap π ψ m, sum_sq_cTrunc π ψ m]

private lemma sum_fin_prod_eq {M : Type*} [AddCommMonoid M] (m : ℕ) (F : ℕ → ℕ → M) :
    ∑ x : Fin m × Fin m, F (x.1 : ℕ) (x.2 : ℕ)
      = ∑ d ∈ Finset.range m, ∑ n ∈ Finset.range m, F d n := by
  have h1 : ∑ x : Fin m × Fin m, F (x.1 : ℕ) (x.2 : ℕ)
      = ∑ d : Fin m, ∑ n : Fin m, F (d : ℕ) (n : ℕ) := Fintype.sum_prod_type _
  rw [h1, ← Fin.sum_univ_eq_sum_range (fun d => ∑ n ∈ Finset.range m, F d n) m]
  exact Finset.sum_congr rfl fun d _ => Fin.sum_univ_eq_sum_range (fun n => F d n) m

private lemma sum_ite_add_eq (π ψ : ℕ → ℝ) (m r d : ℕ) :
    ∑ n ∈ Finset.range m, (if d + n = r then π d * ψ n else 0)
      = if d ≤ r ∧ r - d < m then π d * ψ (r - d) else 0 := by
  by_cases h : d ≤ r ∧ r - d < m
  · rw [if_pos h, Finset.sum_eq_single (r - d)]
    · rw [if_pos (by omega)]
    · intro n _ hn
      rw [if_neg (by omega)]
    · intro hnot
      exact absurd (Finset.mem_range.2 h.2) hnot
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_range] at hn
    rcases not_and_or.1 h with h1 | h1 <;> exact if_neg (by omega)

private lemma cTrunc_eq_sum_range (π ψ : ℕ → ℝ) (m r : ℕ) :
    cTrunc π ψ m r
      = ∑ d ∈ Finset.range m, (if d ≤ r ∧ r - d < m then π d * ψ (r - d) else 0) := by
  have h : (∑ x : Fin m × Fin m,
        if (x.1 : ℕ) + (x.2 : ℕ) = r then π (x.1 : ℕ) * ψ (x.2 : ℕ) else 0)
      = ∑ d ∈ Finset.range m, ∑ n ∈ Finset.range m, (if d + n = r then π d * ψ n else 0) :=
    sum_fin_prod_eq m (fun d n => if d + n = r then π d * ψ n else 0)
  rw [cTrunc, h]
  exact Finset.sum_congr rfl fun d _ => sum_ite_add_eq π ψ m r d

/-- Below the truncation level the truncated composite filter is the composite filter. -/
private lemma cTrunc_eq_of_lt (π ψ : ℕ → ℝ) {m r : ℕ} (hr : r < m) :
    cTrunc π ψ m r = ∑ d ∈ Finset.range (r + 1), π d * ψ (r - d) := by
  rw [cTrunc_eq_sum_range]
  have hsub : Finset.range (r + 1) ⊆ Finset.range m := Finset.range_mono hr
  have hz : ∀ d ∈ Finset.range m, d ∉ Finset.range (r + 1) →
      (if d ≤ r ∧ r - d < m then π d * ψ (r - d) else 0) = 0 := by
    intro d hd hd'
    simp only [Finset.mem_range] at hd hd'
    rw [if_neg (by omega)]
  rw [← Finset.sum_subset hsub hz]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_range] at hd
  rw [if_pos (⟨by omega, by omega⟩ : d ≤ r ∧ r - d < m)]

private lemma abs_cTrunc_le (π ψ : ℕ → ℝ) (m r : ℕ) :
    |cTrunc π ψ m r| ≤ ∑ d ∈ Finset.range (r + 1), |π d| * |ψ (r - d)| := by
  classical
  rw [cTrunc_eq_sum_range]
  have hstep : ∀ d ∈ Finset.range m,
      |if d ≤ r ∧ r - d < m then π d * ψ (r - d) else 0|
        ≤ if d ∈ Finset.range (r + 1) then |π d| * |ψ (r - d)| else 0 := by
    intro d _
    by_cases hdr : d ∈ Finset.range (r + 1)
    · rw [if_pos hdr]
      by_cases hcond : d ≤ r ∧ r - d < m
      · rw [if_pos hcond, abs_mul]
      · rw [if_neg hcond, abs_zero]
        positivity
    · rw [if_neg hdr]
      rw [Finset.mem_range] at hdr
      rw [if_neg (by omega), abs_zero]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum hstep) ?_)
  rw [Finset.sum_ite_mem]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    fun i _ _ => by positivity

private lemma sum_abs_conv_le {π ψ : ℕ → ℝ} {C r0 : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r0)
    (hπ : ∀ n, |π n| ≤ C * r0 ^ n) (hψ : ∀ n, |ψ n| ≤ C * r0 ^ n) (r : ℕ) :
    ∑ d ∈ Finset.range (r + 1), |π d| * |ψ (r - d)| ≤ C ^ 2 * ((r : ℝ) + 1) * r0 ^ r := by
  have hterm : ∀ d ∈ Finset.range (r + 1), |π d| * |ψ (r - d)| ≤ C ^ 2 * r0 ^ r := by
    intro d hd
    rw [Finset.mem_range] at hd
    calc |π d| * |ψ (r - d)| ≤ (C * r0 ^ d) * (C * r0 ^ (r - d)) :=
          mul_le_mul (hπ d) (hψ _) (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (r0 ^ d * r0 ^ (r - d)) := by ring
      _ = C ^ 2 * r0 ^ r := by rw [← pow_add]; congr 2; omega
  calc ∑ d ∈ Finset.range (r + 1), |π d| * |ψ (r - d)|
      ≤ ∑ _d ∈ Finset.range (r + 1), C ^ 2 * r0 ^ r := Finset.sum_le_sum hterm
    _ = C ^ 2 * ((r : ℝ) + 1) * r0 ^ r := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

private lemma summable_sq_geom_poly {C r0 : ℝ} (hr0 : 0 ≤ r0) (hr1 : r0 < 1) :
    Summable fun n : ℕ => (C ^ 2 * ((n : ℝ) + 1) * r0 ^ n) ^ 2 := by
  have hr2 : ‖r0 ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r0)]
    nlinarith
  have hgeom : Summable fun n : ℕ => ((n : ℝ) + 1) ^ 2 * (r0 ^ 2) ^ n := by
    have h0 : Summable fun n : ℕ => (r0 ^ 2) ^ n := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hr2
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * (r0 ^ 2) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr2
    have h2 : Summable fun n : ℕ => (n : ℝ) ^ 2 * (r0 ^ 2) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr2
    exact ((h2.add (h1.mul_left 2)).add h0).congr fun n => by ring
  refine (hgeom.mul_left (C ^ 4)).congr fun n => ?_
  rw [← pow_mul, mul_comm 2 n, pow_mul]
  ring

/-- **The truncated second moment converges to the contrast variance.** Below the
truncation level the truncated filter *is* the composite filter, and the `m` extra terms
are dominated by the (summable) geometric envelope's tail. -/
private lemma tendsto_sum_sq_cTrunc {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    Tendsto (fun m : ℕ =>
        ∑ r ∈ Finset.range (2 * m), cTrunc (armaPi b a) (armaPsi b0 a0) m r ^ 2)
      atTop (𝓝 (armaContrastVar b0 a0 b a)) := by
  obtain ⟨C, r0, hC, hr0, hr1, hπ, hψ⟩ := exists_common_geometric_bound hB0 hB
  set B : ℕ → ℝ := fun r => C ^ 2 * ((r : ℝ) + 1) * r0 ^ r with hBdef
  have hB0' : ∀ r : ℕ, 0 ≤ B r := by
    intro r
    have : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
    rw [hBdef]
    positivity
  have hBsum : Summable fun r : ℕ => B r ^ 2 := summable_sq_geom_poly hr0 hr1
  have hcT : ∀ m r : ℕ, |cTrunc (armaPi b a) (armaPsi b0 a0) m r| ≤ B r := fun m r =>
    le_trans (abs_cTrunc_le _ _ m r) (sum_abs_conv_le hC hr0 hπ hψ r)
  -- the head of the truncated sum is the exact composite filter
  have hsplit : ∀ m : ℕ,
      ∑ r ∈ Finset.range (2 * m), cTrunc (armaPi b a) (armaPsi b0 a0) m r ^ 2
        = (∑ r ∈ Finset.range m, contrastCoeff b0 a0 b a r ^ 2)
          + ∑ r ∈ Finset.Ico m (2 * m), cTrunc (armaPi b a) (armaPsi b0 a0) m r ^ 2 := by
    intro m
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : m ≤ 2 * m)]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [cTrunc_eq_of_lt _ _ (Finset.mem_range.1 hr)]
    rfl
  have hP : Tendsto (fun m : ℕ => ∑ r ∈ Finset.range m, contrastCoeff b0 a0 b a r ^ 2) atTop
      (𝓝 (armaContrastVar b0 a0 b a)) := by
    rw [armaContrastVar_eq_tsum]
    exact (summable_sq_contrastCoeff hB0 hB).hasSum.tendsto_sum_nat
  -- the tail is dominated by the envelope's tail
  have htail : Tendsto (fun m : ℕ => ∑' k : ℕ, B (k + m) ^ 2) atTop (𝓝 0) := by
    have h1 : ∀ m : ℕ, (∑' k : ℕ, B (k + m) ^ 2)
        = (∑' r : ℕ, B r ^ 2) - ∑ r ∈ Finset.range m, B r ^ 2 := by
      intro m
      have h := hBsum.sum_add_tsum_nat_add m
      linarith
    simp only [h1]
    have h2 := hBsum.hasSum.tendsto_sum_nat
    have h3 : Tendsto (fun m : ℕ => (∑' r : ℕ, B r ^ 2) - ∑ r ∈ Finset.range m, B r ^ 2) atTop
        (𝓝 ((∑' r : ℕ, B r ^ 2) - ∑' r : ℕ, B r ^ 2)) := tendsto_const_nhds.sub h2
    simpa using h3
  have hR : Tendsto (fun m : ℕ =>
      ∑ r ∈ Finset.Ico m (2 * m), cTrunc (armaPi b a) (armaPsi b0 a0) m r ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => Finset.sum_nonneg fun r _ => sq_nonneg _) (fun m => ?_) htail
    have hshift : Summable fun k : ℕ => B (k + m) ^ 2 :=
      (summable_nat_add_iff m).2 hBsum
    rw [Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ k ∈ Finset.range (2 * m - m),
        cTrunc (armaPi b a) (armaPsi b0 a0) m (m + k) ^ 2 ≤ B (k + m) ^ 2 := by
      intro k _
      have h := hcT m (m + k)
      have h0 := hB0' (m + k)
      have habs : |cTrunc (armaPi b a) (armaPsi b0 a0) m (m + k)| ^ 2
          = cTrunc (armaPi b a) (armaPsi b0 a0) m (m + k) ^ 2 := sq_abs _
      rw [show k + m = m + k by omega]
      nlinarith [abs_nonneg (cTrunc (armaPi b a) (armaPsi b0 a0) m (m + k))]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    exact hshift.sum_le_tsum _ (fun k _ => sq_nonneg _)
  have hfin := hP.add hR
  rw [add_zero] at hfin
  exact Filter.Tendsto.congr (fun m => (hsplit m).symm) hfin

private lemma inv_mul_le_inv_mul {c t x y : ℝ} (hc : 0 < c) (hct : c ≤ t) (hx : 0 ≤ x)
    (hxy : x ≤ y) : t⁻¹ * x ≤ c⁻¹ * y := by
  have ht : 0 < t := lt_of_lt_of_le hc hct
  have hpos : 0 < t * c := mul_pos ht hc
  refine le_of_mul_le_mul_right ?_ hpos
  have e1 : t⁻¹ * x * (t * c) = x * c := by field_simp <;> ring
  have e2 : c⁻¹ * y * (t * c) = y * t := by field_simp <;> ring
  rw [e1, e2]
  nlinarith

/-- Splitting `range (N·L)` into the `L` arithmetic progressions of step `L`. -/
private lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] {L : ℕ} (hL : 0 < L) (N : ℕ)
    (F : ℕ → M) :
    ∑ i ∈ Finset.range (N * L), F i
      = ∑ k ∈ Finset.range L, ∑ j ∈ Finset.range N, F (k + j * L) := by
  classical
  rw [← Finset.sum_product']
  refine (Finset.sum_nbij' (fun x : ℕ × ℕ => x.1 + x.2 * L) (fun i : ℕ => (i % L, i / L))
    ?_ ?_ ?_ ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    simp only [Finset.mem_range]
    calc x.1 + x.2 * L < L + x.2 * L := by omega
      _ = (x.2 + 1) * L := by ring
      _ ≤ N * L := Nat.mul_le_mul_right L (by omega)
  · intro i hi
    rw [Finset.mem_range] at hi
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hL, (Nat.div_lt_iff_lt_mul hL).2 hi⟩
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    have h1 : (x.1 + x.2 * L) % L = x.1 := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx.1]
    have h2 : (x.1 + x.2 * L) / L = x.2 := by
      rw [Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hx.1, zero_add]
    show ((x.1 + x.2 * L) % L, (x.1 + x.2 * L) / L) = x
    rw [h1, h2]
  · intro i _
    exact Nat.mod_add_div' i L
  · intro x _
    rfl

/-- **From the block subsequence to the full sequence**: for a monotone nonnegative
partial-sum sequence, convergence of `S_{NL}/(NL)` upgrades to convergence of `S_T/T`.
The two comparison sequences differ from the block averages by the factors
`(N+1)/N` and `N/(N+1)`, both of which tend to `1`. -/
private lemma tendsto_avg_of_tendsto_block {L : ℕ} (hL : 0 < L) {S : ℕ → ℝ} {M : ℝ}
    (hmono : Monotone S) (hpos : ∀ n, 0 ≤ S n)
    (hA : Tendsto (fun N : ℕ => ((N * L : ℕ) : ℝ)⁻¹ * S (N * L)) atTop (𝓝 M)) :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * S T) atTop (𝓝 M) := by
  set A : ℕ → ℝ := fun N => ((N * L : ℕ) : ℝ)⁻¹ * S (N * L) with hAdef
  have hφ : Tendsto (fun T : ℕ => T / L) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun c => ⟨c * L, fun T hT => ?_⟩
    exact (Nat.le_div_iff_mul_le hL).2 hT
  have hratio : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    field_simp
  have hratio' : Tendsto (fun N : ℕ => (N : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => (((N : ℝ) + 1) / (N : ℝ))⁻¹) atTop (𝓝 (1 : ℝ)⁻¹) :=
      hratio.inv₀ one_ne_zero
    rw [inv_one] at h1
    refine h1.congr' ?_
    filter_upwards with N
    rw [inv_div]
  have hupN : Tendsto (fun N : ℕ => A (N + 1) * (((N : ℝ) + 1) / (N : ℝ))) atTop (𝓝 M) := by
    have h1 : Tendsto (fun N : ℕ => A (N + 1)) atTop (𝓝 M) :=
      hA.comp (tendsto_atTop_atTop.2 fun c => ⟨c, fun n hn => by omega⟩)
    simpa using h1.mul hratio
  have hloN : Tendsto (fun N : ℕ => A N * ((N : ℝ) / ((N : ℝ) + 1))) atTop (𝓝 M) := by
    simpa using hA.mul hratio'
  have hup := hupN.comp hφ
  have hlo := hloN.comp hφ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [eventually_ge_atTop L] with T hT
    have hTpos : 0 < T := lt_of_lt_of_le hL hT
    set N := T / L with hNdef
    have hN1 : 1 ≤ N := (Nat.one_le_div_iff hL).2 hT
    have hlow : N * L ≤ T := Nat.div_mul_le_self T L
    have hhigh : T < (N + 1) * L := (Nat.div_lt_iff_lt_mul hL).1 (Nat.lt_succ_self N)
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hcast : ((N * L : ℕ) : ℝ) = (N : ℝ) * (L : ℝ) := by push_cast; ring
    have hcast' : (((N + 1) * L : ℕ) : ℝ) = ((N : ℝ) + 1) * (L : ℝ) := by push_cast; ring
    have hrewrite : A N * ((N : ℝ) / ((N : ℝ) + 1))
        = (((N + 1) * L : ℕ) : ℝ)⁻¹ * S (N * L) := by
      have h1 : (N : ℝ) ≠ 0 := ne_of_gt hNR
      have h2 : (L : ℝ) ≠ 0 := ne_of_gt hLR
      have h3 : ((N : ℝ) + 1) ≠ 0 := by positivity
      simp only [hAdef, hcast, hcast']
      field_simp <;> ring
    show A N * ((N : ℝ) / ((N : ℝ) + 1)) ≤ (T : ℝ)⁻¹ * S T
    rw [hrewrite]
    refine inv_mul_le_inv_mul (by exact_mod_cast hTpos) ?_ (hpos _) (hmono hlow)
    rw [hcast']
    calc (T : ℝ) ≤ (((N + 1) * L : ℕ) : ℝ) := by exact_mod_cast hhigh.le
      _ = ((N : ℝ) + 1) * (L : ℝ) := hcast'
  · filter_upwards [eventually_ge_atTop L] with T hT
    have hTpos : 0 < T := lt_of_lt_of_le hL hT
    set N := T / L with hNdef
    have hN1 : 1 ≤ N := (Nat.one_le_div_iff hL).2 hT
    have hlow : N * L ≤ T := Nat.div_mul_le_self T L
    have hhigh : T < (N + 1) * L := (Nat.div_lt_iff_lt_mul hL).1 (Nat.lt_succ_self N)
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hcast : ((N * L : ℕ) : ℝ) = (N : ℝ) * (L : ℝ) := by push_cast; ring
    have hcast' : (((N + 1) * L : ℕ) : ℝ) = ((N : ℝ) + 1) * (L : ℝ) := by push_cast; ring
    have hrewrite : A (N + 1) * (((N : ℝ) + 1) / (N : ℝ))
        = ((N * L : ℕ) : ℝ)⁻¹ * S ((N + 1) * L) := by
      have h1 : (N : ℝ) ≠ 0 := ne_of_gt hNR
      have h2 : (L : ℝ) ≠ 0 := ne_of_gt hLR
      have h3 : ((N : ℝ) + 1) ≠ 0 := by positivity
      simp only [hAdef, hcast, hcast']
      field_simp <;> ring
    show (T : ℝ)⁻¹ * S T ≤ A (N + 1) * (((N : ℝ) + 1) / (N : ℝ))
    rw [hrewrite]
    refine inv_mul_le_inv_mul ?_ ?_ (hpos _) (hmono hhigh.le)
    · rw [hcast]; positivity
    · rw [hcast]
      calc (N : ℝ) * (L : ℝ) = ((N * L : ℕ) : ℝ) := hcast.symm
        _ ≤ (T : ℝ) := by exact_mod_cast hlow

private lemma integrable_blockResid_sq [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsWhiteNoise ε σ2 μ) (π ψ : ℕ → ℝ) (m i : ℕ) :
    Integrable (fun ω => blockResid π ψ ε m i ω ^ 2) μ := by
  have h := (memLp_blockResid hε π ψ m i).integrable_mul (memLp_blockResid hε π ψ m i)
  exact h.congr (Filter.Eventually.of_forall fun ω => by simp [Pi.mul_apply, sq])

/-- **The `m`-dependent strong law**: along each of the `2m` arithmetic progressions of
step `2m` the squares `(z_i^{(m)})²` are i.i.d. and integrable, so Etemadi's strong law
applies progression by progression; summing the `2m` of them and passing from the block
subsequence to the full sequence gives the Cesàro limit. -/
private lemma ae_tendsto_avg_blockResid_sq [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε σ2 μ) (π ψ : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun T : ℕ => (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, blockResid π ψ ε m i ω ^ 2) atTop
      (𝓝 (∫ ω, blockResid π ψ ε m 0 ω ^ 2 ∂μ)) := by
  classical
  have hwn := hε.isWhiteNoise
  have hL : 0 < 2 * m := by omega
  set M : ℝ := ∫ ω, blockResid π ψ ε m 0 ω ^ 2 ∂μ with hMdef
  have hMi : ∀ i : ℕ, ∫ ω, blockResid π ψ ε m i ω ^ 2 ∂μ = M := by
    intro i
    rw [hMdef, integral_blockResid_sq_eq hwn π ψ m i, integral_blockResid_sq_eq hwn π ψ m 0]
  have hprog : ∀ k : ℕ, ∀ᵐ ω ∂μ, Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
        blockResid π ψ ε m (k + j * (2 * m)) ω ^ 2) atTop (𝓝 M) := by
    intro k
    have hkey : ∀ u v : ℕ, u < v → IndepFun
        (fun ω => blockResid π ψ ε m (k + u * (2 * m)) ω ^ 2)
        (fun ω => blockResid π ψ ε m (k + v * (2 * m)) ω ^ 2) μ := by
      intro u v huv
      refine indepFun_blockResid_sq hε π ψ ?_
      have h2 : (u + 1) * (2 * m) ≤ v * (2 * m) := Nat.mul_le_mul_right _ (by omega)
      have e : k + u * (2 * m) + 2 * m = k + (u + 1) * (2 * m) := by ring
      rw [e]
      exact Nat.add_le_add_left h2 k
    have hsl := ProbabilityTheory.strong_law_ae
      (fun j : ℕ => fun ω => blockResid π ψ ε m (k + j * (2 * m)) ω ^ 2)
      (integrable_blockResid_sq hwn π ψ m (k + 0 * (2 * m)))
      (by
        intro j j' hjj'
        simp only [Function.onFun]
        rcases lt_or_gt_of_ne hjj' with h | h
        · exact hkey j j' h
        · exact (hkey j' j h).symm)
      (fun j => identDistrib_blockResid_sq hε π ψ m _ _)
    have hM0 : (μ[fun ω => blockResid π ψ ε m (k + 0 * (2 * m)) ω ^ 2]) = M := hMi _
    rw [hM0] at hsl
    filter_upwards [hsl] with ω hω
    simpa using hω
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
        blockResid π ψ ε m (k + j * (2 * m)) ω ^ 2) atTop (𝓝 M) := ae_all_iff.2 hprog
  filter_upwards [hall] with ω hω
  set f : ℕ → ℝ := fun i => blockResid π ψ ε m i ω ^ 2 with hfdef
  have hf0 : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
  have hmono : Monotone (fun T : ℕ => ∑ i ∈ Finset.range T, f i) := by
    intro T1 T2 h
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ => hf0 i
  have hpos : ∀ n : ℕ, 0 ≤ ∑ i ∈ Finset.range n, f i := fun n =>
    Finset.sum_nonneg fun i _ => hf0 i
  refine tendsto_avg_of_tendsto_block (S := fun T : ℕ => ∑ i ∈ Finset.range T, f i)
    hL hmono hpos ?_
  have hgs : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (2 * m),
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, f (k + j * (2 * m))) atTop
      (𝓝 (∑ _k ∈ Finset.range (2 * m), M)) :=
    tendsto_finset_sum _ fun k _ => hω k
  have hsum : ∑ _k ∈ Finset.range (2 * m), M = ((2 * m : ℕ) : ℝ) * M := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum] at hgs
  have hmne : ((2 * m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hfin : Tendsto (fun N : ℕ => ((2 * m : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (2 * m),
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, f (k + j * (2 * m))) atTop (𝓝 M) := by
    have h := hgs.const_mul (((2 * m : ℕ) : ℝ)⁻¹)
    have he : ((2 * m : ℕ) : ℝ)⁻¹ * (((2 * m : ℕ) : ℝ) * M) = M := by
      field_simp
    rw [he] at h
    exact h
  refine hfin.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hcast : ((N * (2 * m) : ℕ) : ℝ) = (N : ℝ) * ((2 * m : ℕ) : ℝ) := by push_cast; ring
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsplit := sum_range_mul_split hL N f
  show ((2 * m : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (2 * m),
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, f (k + j * (2 * m))
    = ((N * (2 * m) : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (N * (2 * m)), f i
  rw [hsplit, hcast, ← Finset.mul_sum, mul_inv]
  ring

lemma l2n_abs (f : Ω → ℝ) : l2n μ (fun ω => |f ω|) = l2n μ f := by
  simp only [l2n, sq_abs]

private lemma l2n_neg (f : Ω → ℝ) : l2n μ (fun ω => -f ω) = l2n μ f := by
  simp only [l2n, neg_pow, even_two.neg_pow]

private lemma l2n_sub_le_add {f g h : Ω → ℝ} (hfh : MemLp (fun ω => f ω - h ω) 2 μ)
    (hhg : MemLp (fun ω => h ω - g ω) 2 μ) :
    l2n μ (fun ω => f ω - g ω)
      ≤ l2n μ (fun ω => f ω - h ω) + l2n μ (fun ω => h ω - g ω) := by
  have he : (fun ω => f ω - g ω) = fun ω => (f ω - h ω) + (h ω - g ω) := by
    funext ω; ring
  rw [he]
  exact l2n_add_le hfh hhg

private lemma l2n_eq_eLpNorm_toReal {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    l2n μ f = (eLpNorm f 2 μ).toReal := by
  rw [l2n_eq_norm_toLp hf, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_ae hf.coeFn_toLp

/-- Cauchy–Schwarz in the form used below. -/
lemma integral_abs_mul_le [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, |f ω * g ω| ∂μ ≤ l2n μ f * l2n μ g := by
  have hfa : MemLp (fun ω => |f ω|) 2 μ := hf.abs
  have hga : MemLp (fun ω => |g ω|) 2 μ := hg.abs
  have h := real_inner_le_norm (hfa.toLp _) (hga.toLp _)
  rw [inner_toLp' hfa hga] at h
  have heq : ∫ ω, |f ω * g ω| ∂μ = ∫ ω, |f ω| * |g ω| ∂μ := by
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => abs_mul (f ω) (g ω))
  rw [heq, ← l2n_abs f, ← l2n_abs g, l2n_eq_norm_toLp hfa, l2n_eq_norm_toLp hga]
  exact h

lemma l2n_noise [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsWhiteNoise ε σ2 μ) (t : ℤ) : l2n μ (ε t) = Real.sqrt σ2 := by
  have h : ∫ ω, ε t ω ^ 2 ∂μ = σ2 := by
    have h1 : ∫ ω, ε t ω ^ 2 ∂μ = ∫ ω, ε t ω * ε t ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => sq (ε t ω))
    rw [h1, integral_noise_mul' hε, if_pos rfl]
  rw [l2n, h]

private lemma l2n_linearProcess_eq [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ) (hψ : Summable fun j => |ψ j|)
    (hε : IsWhiteNoise ε σ2 μ) (hmeas : ∀ t, Measurable (X t)) (s t : ℤ) :
    l2n μ (X s) = l2n μ (X t) := by
  have hsq : ∀ r : ℤ, ∫ ω, X r ω ^ 2 ∂μ = σ2 * ∑' j : ℕ, ψ j * ψ (j + (0 : ℤ).natAbs) := by
    intro r
    have h1 : ∫ ω, X r ω ^ 2 ∂μ = ∫ ω, X r ω * X r ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => sq (X r ω))
    rw [h1, integral_mul_linearProcess hX hψ hε hmeas r r, sub_self]
  rw [l2n, l2n, hsq s, hsq t]

/-- **Uniform `L²` control of the `ψ`-truncation defect**: `‖X_t − Σ_{n<N} ψ_n ε_{t−n}‖₂ ≤
(Σ_{n ≥ N}|ψ_n|)·√σ²`, the bound being independent of `t`. This is what lets the
progression device use a *finite* window of the noise. -/
lemma l2n_sub_psum_le [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ) (hψ : Summable fun j => |ψ j|)
    (hε : IsWhiteNoise ε σ2 μ) (hmeas : ∀ t, Measurable (X t)) (t : ℤ) (N : ℕ) :
    l2n μ (fun ω => X t ω - ∑ n ∈ Finset.range N, ψ n * ε (t - (n : ℕ)) ω)
      ≤ (∑' k : ℕ, |ψ (k + N)|) * Real.sqrt σ2 := by
  classical
  have hσ0 : 0 ≤ Real.sqrt σ2 := Real.sqrt_nonneg _
  have hmemX : MemLp (X t) 2 μ := hX.memLp hψ hε hmeas t
  have hmemP : ∀ K : ℕ, MemLp (fun ω => ∑ n ∈ Finset.range K, ψ n * ε (t - (n : ℕ)) ω) 2 μ :=
    fun K => memLp_finset_sum _ fun n _ => (hε.memLp _).const_mul _
  have hshift : Summable fun k : ℕ => |ψ (k + N)| := (summable_nat_add_iff N).2 hψ
  -- the increment between two truncation levels is controlled by the coefficient tail
  have hincr : ∀ K : ℕ, N ≤ K →
      l2n μ (fun ω => (∑ n ∈ Finset.range K, ψ n * ε (t - (n : ℕ)) ω)
          - ∑ n ∈ Finset.range N, ψ n * ε (t - (n : ℕ)) ω)
        ≤ (∑' k : ℕ, |ψ (k + N)|) * Real.sqrt σ2 := by
    intro K hK
    have hdiff : (fun ω => (∑ n ∈ Finset.range K, ψ n * ε (t - (n : ℕ)) ω)
        - ∑ n ∈ Finset.range N, ψ n * ε (t - (n : ℕ)) ω)
        = fun ω => ∑ n ∈ Finset.Ico N K, ψ n * ε (t - (n : ℕ)) ω := by
      funext ω
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun n => ψ n * ε (t - (n : ℕ)) ω) (Nat.zero_le N) hK]
      rw [Finset.range_eq_Ico]
      ring
    rw [hdiff]
    refine le_trans (l2n_finset_sum_le _ _ fun n => (hε.memLp _).const_mul _) ?_
    have hterm : ∀ n ∈ Finset.Ico N K, l2n μ (fun ω => ψ n * ε (t - (n : ℕ)) ω)
        ≤ |ψ n| * Real.sqrt σ2 := by
      intro n _
      rw [l2n_const_mul, l2n_noise hε]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ hσ0
    rw [Finset.sum_Ico_eq_sum_range]
    have hre : ∑ k ∈ Finset.range (K - N), |ψ (N + k)|
        = ∑ k ∈ Finset.range (K - N), |ψ (k + N)| :=
      Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm N k]
    rw [hre]
    exact hshift.sum_le_tsum _ fun k _ => abs_nonneg _
  -- pass to the limit in the truncation level
  have hlim : Tendsto (fun K : ℕ =>
      l2n μ (fun ω => X t ω - ∑ n ∈ Finset.range K, ψ n * ε (t - (n : ℕ)) ω)
        + (∑' k : ℕ, |ψ (k + N)|) * Real.sqrt σ2) atTop
      (𝓝 (0 + (∑' k : ℕ, |ψ (k + N)|) * Real.sqrt σ2)) := by
    refine Filter.Tendsto.add ?_ tendsto_const_nhds
    have h1 : ∀ K : ℕ,
        l2n μ (fun ω => X t ω - ∑ n ∈ Finset.range K, ψ n * ε (t - (n : ℕ)) ω)
          = (eLpNorm (fun ω => X t ω - ∑ n ∈ Finset.range K, ψ n * ε (t - (n : ℕ)) ω)
              2 μ).toReal := fun K =>
      l2n_eq_eLpNorm_toReal (hmemX.sub (hmemP K))
    simp only [h1]
    simpa using! (ENNReal.continuousAt_toReal (by simp)).tendsto.comp (hX t)
  rw [zero_add] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop N] with K hK
  refine le_trans (l2n_sub_le_add (hmemX.sub (hmemP K)) ((hmemP K).sub (hmemP N))) ?_
  linarith [hincr K hK]

/-- The `L²` norm of the `θ`-free envelope row is `≤ C(1 − r)⁻¹ c₀`, uniformly in `T`
and in the row index. -/
private lemma l2n_residEnv_le [IsProbabilityMeasure μ] {C r c0 : ℝ} (hC : 0 ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r < 1) {X : ℤ → Ω → ℝ} (hmem : ∀ t : ℤ, MemLp (X t) 2 μ)
    (hc : ∀ t : ℤ, l2n μ (X t) = c0) {T : ℕ} (i : Fin T) :
    l2n μ (fun ω => residEnv C r (fun k : Fin T => X (((k : ℕ) : ℤ) + 1) ω) i)
      ≤ C / (1 - r) * c0 := by
  have hc0 : 0 ≤ c0 := by rw [← hc 0]; exact l2n_nonneg _ _
  have hmemk : ∀ k : Fin T, MemLp (fun ω =>
      (if (i : ℕ) ≤ (k : ℕ) then C * r ^ ((k : ℕ) - (i : ℕ)) else 0) *
        |X (((k : ℕ) : ℤ) + 1) ω|) 2 μ := fun k => (hmem _).abs.const_mul _
  have hEq : (fun ω => residEnv C r (fun k : Fin T => X (((k : ℕ) : ℤ) + 1) ω) i)
      = fun ω => ∑ k : Fin T,
        (if (i : ℕ) ≤ (k : ℕ) then C * r ^ ((k : ℕ) - (i : ℕ)) else 0) *
          |X (((k : ℕ) : ℤ) + 1) ω| := rfl
  have hval : ∀ k : Fin T, l2n μ (fun ω =>
      (if (i : ℕ) ≤ (k : ℕ) then C * r ^ ((k : ℕ) - (i : ℕ)) else 0) *
        |X (((k : ℕ) : ℤ) + 1) ω|)
      = (if (i : ℕ) ≤ (k : ℕ) then C * r ^ ((k : ℕ) - (i : ℕ)) else 0) * c0 := by
    intro k
    rw [l2n_const_mul, l2n_abs, hc, abs_of_nonneg]
    split_ifs <;> positivity
  rw [hEq]
  refine le_trans (l2n_finset_sum_le _ _ hmemk) ?_
  rw [Finset.sum_congr rfl fun k _ => hval k, ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_geomCoeff_le hC hr0 hr1 i) hc0

open Matrix in
/-- **Step (B), uniformly over the compact parameter set** — the widened form of
`gramTail_quadForm_tendstoInProb` that `mle_consistent`(iii) needs.

The correction term `T⁻¹ uᵀ G_T(θ) u` is `o_p(1)` *simultaneously* for all `θ ∈ K`,
because `quadForm_gramTail_le_env` dominates it by `(1 − r²)⁻¹ W_T²` with a `θ`-free
`W_T` whose `L²` norm is `O(1)` (`l2n_residEnv_le`, `sum_weight_le`, Minkowski). One
Markov inequality then gives the rate `O(1/T)` for the whole supremum — which is why no
*difference* modulus for the Gram tail is required. -/
private lemma gramTail_uniform_tendstoInProb [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (hwn : IsWhiteNoise ε σ2 μ) (hB0 : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ) (hmeas : ∀ t, Measurable (X t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))} (hK : IsCompact K)
    (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T : ℕ => (μ {ω | ∃ ba ∈ K, η ≤ (T : ℝ)⁻¹ *
        ((piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
          (gramTail ba.1 ba.2 T *ᵥ
            (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))}).toReal)
      atTop (𝓝 0) := by
  obtain ⟨C, r, hC, hr0, hr1, hψK, hπK⟩ := exists_uniform_geometric_bound_arma hK hKB
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have hr2lt : r ^ 2 < 1 := by nlinarith [sq_nonneg r]
  have hpos : (0 : ℝ) < 1 - r ^ 2 := by linarith
  have hψs : Summable fun n => |armaPsi b0 a0 n| := summable_abs_armaPsi a0 hB0.1
  have hmemX : ∀ t : ℤ, MemLp (X t) 2 μ := fun t => hcausal.memLp hψs hwn hmeas t
  obtain ⟨c0, hc⟩ : ∃ c0 : ℝ, ∀ t : ℤ, l2n μ (X t) = c0 :=
    ⟨l2n μ (X 0), fun t => l2n_linearProcess_eq hcausal hψs hwn hmeas t 0⟩
  have hc0 : 0 ≤ c0 := by rw [← hc 0]; exact l2n_nonneg _ _
  obtain ⟨W, hWdef⟩ : ∃ W : (T : ℕ) → Ω → ℝ, W = fun T ω =>
      ∑ i : Fin T, C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) *
        residEnv C r (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = C ^ 2 * (∑' d : ℕ, ((d : ℝ) + 1) * r ^ (d + 1)) *
      (C / (1 - r) * c0) := ⟨_, rfl⟩
  have hH0 : (0 : ℝ) ≤ ∑' d : ℕ, ((d : ℝ) + 1) * r ^ (d + 1) :=
    le_trans (sum_weight_le hr0 hr1 0) (by simp)
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    have hr1' : (0 : ℝ) < 1 - r := by linarith
    have : (0 : ℝ) ≤ C / (1 - r) * c0 := by positivity
    positivity
  have hEmem : ∀ (T : ℕ) (i : Fin T), MemLp
      (fun ω => residEnv C r (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i) 2 μ :=
    fun T i => memLp_finset_sum _ fun k _ => (hmemX _).abs.const_mul _
  have hwnn : ∀ (T : ℕ) (i : Fin T),
      (0 : ℝ) ≤ C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) := by
    intro T i
    have hle : ((i : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast le_of_lt i.isLt
    have h1 : (0 : ℝ) ≤ (T : ℝ) - (i : ℕ) := by linarith
    positivity
  have hWmem : ∀ T : ℕ, MemLp (W T) 2 μ := by
    intro T
    rw [hWdef]
    exact memLp_finset_sum _ fun i _ => (hEmem T i).const_mul _
  have hWl2 : ∀ T : ℕ, l2n μ (W T) ≤ A := by
    intro T
    rw [hWdef]
    refine le_trans (l2n_finset_sum_le _ _ fun i => (hEmem T i).const_mul _) ?_
    have hval : ∀ i : Fin T,
        l2n μ (fun ω => C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) *
          residEnv C r (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i)
          ≤ C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) * (C / (1 - r) * c0) := by
      intro i
      rw [l2n_const_mul, abs_of_nonneg (hwnn T i)]
      exact mul_le_mul_of_nonneg_left (l2n_residEnv_le hC0 hr0 hr1 hmemX hc i) (hwnn T i)
    refine le_trans (Finset.sum_le_sum fun i _ => hval i) ?_
    rw [← Finset.sum_mul, hAdef]
    have hcoef : ∑ i : Fin T, C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ))
        ≤ C ^ 2 * ∑' d : ℕ, ((d : ℝ) + 1) * r ^ (d + 1) := by
      have hrw : ∑ i : Fin T, C ^ 2 * ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ))
          = C ^ 2 * ∑ i : Fin T, ((T : ℝ) - (i : ℕ)) * r ^ (T - (i : ℕ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_left (sum_weight_le hr0 hr1 T) (by positivity)
    refine mul_le_mul_of_nonneg_right hcoef ?_
    have hr1' : (0 : ℝ) < 1 - r := by linarith
    positivity
  refine squeeze_zero' (Eventually.of_forall fun T => ENNReal.toReal_nonneg) ?_
    (tendsto_const_div_atTop_nhds_zero_nat ((1 - r ^ 2)⁻¹ * A ^ 2 / η))
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hsub : {ω | ∃ ba ∈ K, η ≤ (T : ℝ)⁻¹ *
      ((piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
        (gramTail ba.1 ba.2 T *ᵥ
          (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))}
      ⊆ {ω | η ≤ (T : ℝ)⁻¹ * ((1 - r ^ 2)⁻¹ * (W T ω) ^ 2)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    obtain ⟨ba, hba, hle⟩ := hω
    refine le_trans hle (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hdom := quadForm_gramTail_le_env (b := ba.1) (a := ba.2) hC hr0 hr1
      (hπK ba hba) (hψK ba hba) (hKB ba hba)
      (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
    rw [hWdef]
    exact hdom
  have hZnn : 0 ≤ᵐ[μ] fun ω => (T : ℝ)⁻¹ * ((1 - r ^ 2)⁻¹ * (W T ω) ^ 2) := by
    filter_upwards with ω
    have h1 : (0 : ℝ) ≤ (1 - r ^ 2)⁻¹ := le_of_lt (by positivity)
    have h2 : (0 : ℝ) ≤ (T : ℝ)⁻¹ := by positivity
    have h3 : (0 : ℝ) ≤ (W T ω) ^ 2 := sq_nonneg _
    exact mul_nonneg h2 (mul_nonneg h1 h3)
  have hWsq : Integrable (fun ω => (W T ω) ^ 2) μ := by
    have hmul := (hWmem T).integrable_mul (hWmem T)
    exact hmul.congr (Filter.Eventually.of_forall fun ω => (sq (W T ω)).symm)
  have hZint : Integrable (fun ω => (1 - r ^ 2)⁻¹ * (W T ω) ^ 2) μ := hWsq.const_mul _
  have hbnd : ∫ ω, (1 - r ^ 2)⁻¹ * (W T ω) ^ 2 ∂μ ≤ (1 - r ^ 2)⁻¹ * A ^ 2 := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_sq_le_of_l2n_le hA0 (hWl2 T))
      (le_of_lt (by positivity))
  have hmark := mul_meas_ge_le_integral_of_nonneg hZnn (hZint.const_mul (T : ℝ)⁻¹) η
  rw [integral_const_mul] at hmark
  have hle2 : η * (μ.real {ω | η ≤ (T : ℝ)⁻¹ * ((1 - r ^ 2)⁻¹ * (W T ω) ^ 2)})
      ≤ (T : ℝ)⁻¹ * ((1 - r ^ 2)⁻¹ * A ^ 2) :=
    hmark.trans (mul_le_mul_of_nonneg_left hbnd (by positivity))
  rw [measureReal_def] at hle2
  have key : ∀ M : ℝ, 0 ≤ M → η * M ≤ (T : ℝ)⁻¹ * ((1 - r ^ 2)⁻¹ * A ^ 2) →
      M ≤ (1 - r ^ 2)⁻¹ * A ^ 2 / η / T := by
    intro M hM0 hM
    rw [div_div, le_div_iff₀ (by positivity)]
    have h3 : (T : ℝ)⁻¹ * ((1 - r ^ 2)⁻¹ * A ^ 2) * T = (1 - r ^ 2)⁻¹ * A ^ 2 := by
      field_simp
    have h4 := mul_le_mul_of_nonneg_right hM (le_of_lt hTpos)
    rw [h3] at h4
    nlinarith [h4]
  refine le_trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)) ?_
  exact key _ ENNReal.toReal_nonneg hle2

/-- A block `Σ_{N ≤ d < K} π_d x_{i+1+d}` of the (time-reversed) residual. The rows of
`Π_T` are `icoResid π X 0 (T − i) i`. -/
private noncomputable def icoResid (π : ℕ → ℝ) (X : ℤ → Ω → ℝ) (N K i : ℕ) : Ω → ℝ :=
  fun ω => ∑ d ∈ Finset.Ico N K, π d * X ((i : ℤ) + 1 + (d : ℕ)) ω

private lemma memLp_icoResid {X : ℤ → Ω → ℝ} (hmem : ∀ t : ℤ, MemLp (X t) 2 μ)
    (π : ℕ → ℝ) (N K i : ℕ) : MemLp (icoResid π X N K i) 2 μ :=
  memLp_finset_sum _ fun _ _ => (hmem _).const_mul _

private lemma l2n_icoResid_le {X : ℤ → Ω → ℝ} {π : ℕ → ℝ} {c0 : ℝ}
    (hmem : ∀ t : ℤ, MemLp (X t) 2 μ) (hc : ∀ t : ℤ, l2n μ (X t) = c0)
    (hπ : Summable fun n => |π n|) (N K i : ℕ) :
    l2n μ (icoResid π X N K i) ≤ (∑' k : ℕ, |π (k + N)|) * c0 := by
  have hc0 : 0 ≤ c0 := by rw [← hc 0]; exact l2n_nonneg _ _
  refine le_trans (l2n_finset_sum_le _ _ fun d => (hmem _).const_mul _) ?_
  have hterm : ∀ d ∈ Finset.Ico N K,
      l2n μ (fun ω => π d * X ((i : ℤ) + 1 + (d : ℕ)) ω) = |π d| * c0 := by
    intro d _
    rw [l2n_const_mul, hc]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hc0
  rw [Finset.sum_Ico_eq_sum_range]
  have hre : ∑ k ∈ Finset.range (K - N), |π (N + k)|
      = ∑ k ∈ Finset.range (K - N), |π (k + N)| :=
    Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm N k]
  rw [hre]
  exact ((summable_nat_add_iff N).2 hπ).sum_le_tsum _ fun k _ => abs_nonneg _

private lemma icoResid_sub {X : ℤ → Ω → ℝ} (π : ℕ → ℝ) {K K' : ℕ} (h : K ≤ K') (i : ℕ) :
    (fun ω => icoResid π X 0 K' i ω - icoResid π X 0 K i ω) = icoResid π X K K' i := by
  funext ω
  simp only [icoResid]
  rw [← Finset.sum_Ico_consecutive (fun d => π d * X ((i : ℤ) + 1 + (d : ℕ)) ω)
    (Nat.zero_le K) h]
  ring

/-- The two truncation levels of the composite filter differ by at most the coefficient
tail at the smaller level. -/
private lemma l2n_icoResid_diff_le {X : ℤ → Ω → ℝ} {π : ℕ → ℝ} {c0 : ℝ}
    (hmem : ∀ t : ℤ, MemLp (X t) 2 μ) (hc : ∀ t : ℤ, l2n μ (X t) = c0)
    (hπ : Summable fun n => |π n|) (K K' i : ℕ) :
    l2n μ (fun ω => icoResid π X 0 K i ω - icoResid π X 0 K' i ω)
      ≤ (∑' k : ℕ, |π (k + min K K')|) * c0 := by
  rcases le_total K K' with h | h
  · have hmin : min K K' = K := min_eq_left h
    rw [hmin]
    have he : (fun ω => icoResid π X 0 K i ω - icoResid π X 0 K' i ω)
        = fun ω => -(icoResid π X K K' i ω) := by
      rw [← icoResid_sub π h i]
      funext ω
      ring
    rw [he, l2n_neg]
    exact l2n_icoResid_le hmem hc hπ K K' i
  · have hmin : min K K' = K' := min_eq_right h
    rw [hmin, icoResid_sub π h i]
    exact l2n_icoResid_le hmem hc hπ K' K i

private lemma blockResid_eq_sum (π ψ : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (m i : ℕ) (ω : Ω) :
    blockResid π ψ ε m i ω
      = ∑ d ∈ Finset.range m,
          π d * ∑ n ∈ Finset.range m, ψ n * ε ((i : ℤ) + 1 + (d : ℕ) - (n : ℕ)) ω := by
  have h : (∑ x : Fin m × Fin m, π (x.1 : ℕ) * ψ (x.2 : ℕ) *
        ε (1 + ((x.1 : ℕ) : ℤ) - ((x.2 : ℕ) : ℤ) + (i : ℤ)) ω)
      = ∑ d ∈ Finset.range m, ∑ n ∈ Finset.range m,
          π d * ψ n * ε (1 + (d : ℤ) - (n : ℤ) + (i : ℤ)) ω :=
    sum_fin_prod_eq m (fun d n => π d * ψ n * ε (1 + (d : ℤ) - (n : ℤ) + (i : ℤ)) ω)
  rw [blockResid, h]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have harg : (1 : ℤ) + (d : ℤ) - (n : ℤ) + (i : ℤ) = (i : ℤ) + 1 + (d : ℕ) - (n : ℕ) := by
    push_cast
    ring
  rw [harg]
  ring

/-- The `L²` defect between the `m`-truncated residual and its doubly truncated
(finite-noise-window) version: only the `ψ`-tail survives. -/
private lemma l2n_icoResid_sub_blockResid [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ) (hψ : Summable fun j => |ψ j|)
    (hε : IsWhiteNoise ε σ2 μ) (hmeas : ∀ t, Measurable (X t))
    {π : ℕ → ℝ} (hπ : Summable fun n => |π n|) (m i : ℕ) :
    l2n μ (fun ω => icoResid π X 0 m i ω - blockResid π ψ ε m i ω)
      ≤ (∑' n : ℕ, |π n|) * ((∑' k : ℕ, |ψ (k + m)|) * Real.sqrt σ2) := by
  have htail0 : 0 ≤ (∑' k : ℕ, |ψ (k + m)|) * Real.sqrt σ2 := by
    refine mul_nonneg (tsum_nonneg fun k => abs_nonneg _) (Real.sqrt_nonneg _)
  have hmemX : ∀ t : ℤ, MemLp (X t) 2 μ := fun t => hX.memLp hψ hε hmeas t
  have hmemP : ∀ (t : ℤ) (K : ℕ),
      MemLp (fun ω => ∑ n ∈ Finset.range K, ψ n * ε (t - (n : ℕ)) ω) 2 μ :=
    fun t K => memLp_finset_sum _ fun n _ => (hε.memLp _).const_mul _
  have hrw : (fun ω => icoResid π X 0 m i ω - blockResid π ψ ε m i ω)
      = fun ω => ∑ d ∈ Finset.range m, π d *
          (X ((i : ℤ) + 1 + (d : ℕ)) ω
            - ∑ n ∈ Finset.range m, ψ n * ε (((i : ℤ) + 1 + (d : ℕ)) - (n : ℕ)) ω) := by
    funext ω
    rw [blockResid_eq_sum, icoResid, Finset.range_eq_Ico]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [hrw]
  refine le_trans (l2n_finset_sum_le _ _ fun d =>
    ((hmemX _).sub (hmemP _ m)).const_mul _) ?_
  have hterm : ∀ d ∈ Finset.range m,
      l2n μ (fun ω => π d * (X ((i : ℤ) + 1 + (d : ℕ)) ω
        - ∑ n ∈ Finset.range m, ψ n * ε (((i : ℤ) + 1 + (d : ℕ)) - (n : ℕ)) ω))
        ≤ |π d| * ((∑' k : ℕ, |ψ (k + m)|) * Real.sqrt σ2) := by
    intro d _
    rw [l2n_const_mul]
    exact mul_le_mul_of_nonneg_left (l2n_sub_psum_le hX hψ hε hmeas _ m) (abs_nonneg _)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ htail0
  exact hπ.sum_le_tsum _ fun n _ => abs_nonneg _

private lemma l2n_blockResid_le [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hψ : Summable fun j => |ψ j|) (hε : IsWhiteNoise ε σ2 μ)
    {π : ℕ → ℝ} (hπ : Summable fun n => |π n|) (m i : ℕ) :
    l2n μ (blockResid π ψ ε m i) ≤ (∑' n : ℕ, |π n|) * ((∑' n : ℕ, |ψ n|) * Real.sqrt σ2) := by
  have hΨ0 : 0 ≤ (∑' n : ℕ, |ψ n|) * Real.sqrt σ2 :=
    mul_nonneg (tsum_nonneg fun k => abs_nonneg _) (Real.sqrt_nonneg _)
  have hmemP : ∀ t : ℤ, MemLp (fun ω => ∑ n ∈ Finset.range m, ψ n * ε (t - (n : ℕ)) ω) 2 μ :=
    fun t => memLp_finset_sum _ fun n _ => (hε.memLp _).const_mul _
  have hrw : blockResid π ψ ε m i
      = fun ω => ∑ d ∈ Finset.range m, π d *
          ∑ n ∈ Finset.range m, ψ n * ε (((i : ℤ) + 1 + (d : ℕ)) - (n : ℕ)) ω := by
    funext ω
    exact blockResid_eq_sum π ψ ε m i ω
  rw [hrw]
  refine le_trans (l2n_finset_sum_le _ _ fun d => (hmemP _).const_mul _) ?_
  have hinner : ∀ t : ℤ, l2n μ (fun ω => ∑ n ∈ Finset.range m, ψ n * ε (t - (n : ℕ)) ω)
      ≤ (∑' n : ℕ, |ψ n|) * Real.sqrt σ2 := by
    intro t
    refine le_trans (l2n_finset_sum_le _ _ fun n => (hε.memLp _).const_mul _) ?_
    have hterm : ∀ n ∈ Finset.range m, l2n μ (fun ω => ψ n * ε (t - (n : ℕ)) ω)
        = |ψ n| * Real.sqrt σ2 := by
      intro n _
      rw [l2n_const_mul, l2n_noise hε]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hψ.sum_le_tsum _ fun n _ => abs_nonneg _)
      (Real.sqrt_nonneg _)
  have hterm : ∀ d ∈ Finset.range m,
      l2n μ (fun ω => π d * ∑ n ∈ Finset.range m,
          ψ n * ε (((i : ℤ) + 1 + (d : ℕ)) - (n : ℕ)) ω)
        ≤ |π d| * ((∑' n : ℕ, |ψ n|) * Real.sqrt σ2) := by
    intro d _
    rw [l2n_const_mul]
    exact mul_le_mul_of_nonneg_left (hinner _) (abs_nonneg _)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hπ.sum_le_tsum _ fun n _ => abs_nonneg _) hΨ0

private lemma tail_le_tsum {π : ℕ → ℝ} (hπ : Summable fun n => |π n|) (N : ℕ) :
    (∑' k : ℕ, |π (k + N)|) ≤ ∑' n : ℕ, |π n| := by
  have h := hπ.sum_add_tsum_nat_add N
  have h0 : 0 ≤ ∑ n ∈ Finset.range N, |π n| := Finset.sum_nonneg fun n _ => abs_nonneg _
  linarith

private lemma tendsto_tail_zero {f : ℕ → ℝ} (hf : Summable fun n => |f n|) :
    Tendsto (fun m : ℕ => ∑' k : ℕ, |f (k + m)|) atTop (𝓝 0) := by
  have h1 : ∀ m : ℕ, (∑' k : ℕ, |f (k + m)|)
      = (∑' n : ℕ, |f n|) - ∑ n ∈ Finset.range m, |f n| := by
    intro m
    have h := hf.sum_add_tsum_nat_add m
    linarith
  simp only [h1]
  have h3 : Tendsto (fun m : ℕ => (∑' n : ℕ, |f n|) - ∑ n ∈ Finset.range m, |f n|) atTop
      (𝓝 ((∑' n : ℕ, |f n|) - ∑' n : ℕ, |f n|)) :=
    tendsto_const_nhds.sub hf.hasSum.tendsto_sum_nat
  simpa using h3

private lemma tail_min_le {π : ℕ → ℝ} (hπ : Summable fun n => |π n|) (K m : ℕ) :
    (∑' k : ℕ, |π (k + min K m)|)
      ≤ (∑' k : ℕ, |π (k + m)|) + (if K < m then ∑' n : ℕ, |π n| else 0) := by
  by_cases hKm : K < m
  · rw [if_pos hKm, min_eq_left (le_of_lt hKm)]
    have h1 := tail_le_tsum hπ K
    have h2 : (0 : ℝ) ≤ ∑' k : ℕ, |π (k + m)| := tsum_nonneg fun k => abs_nonneg _
    linarith
  · rw [if_neg hKm, min_eq_right (by omega), add_zero]

/-- The edge correction is supported on the last `m` indices. -/
private lemma sum_edge_le (T m : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ∑ i ∈ Finset.range T, (if T - i < m then c else 0) ≤ (m : ℝ) * c := by
  classical
  have hsub : (Finset.range T).filter (fun i => T - i < m) ⊆ Finset.Ico (T - m) T := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_Ico]
    omega
  have hcard : ((Finset.range T).filter (fun i => T - i < m)).card ≤ m := by
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Nat.card_Ico]
    omega
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc

/-- **The per-row defect estimate**: the row of `Π_T` at `i` and the finite-noise-window
residual `z_i^{(m)}` differ in `L²` by the `π`-tail at `min(T − i, m)` plus the
`ψ`-tail at `m`. -/
private lemma l2n_row_sub_blockResid [IsProbabilityMeasure μ] {ψ π : ℕ → ℝ} {σ2 c0 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ) (hψ : Summable fun j => |ψ j|)
    (hε : IsWhiteNoise ε σ2 μ) (hmeas : ∀ t, Measurable (X t))
    (hπ : Summable fun n => |π n|) (hc : ∀ t : ℤ, l2n μ (X t) = c0) (K m i : ℕ) :
    l2n μ (fun ω => icoResid π X 0 K i ω - blockResid π ψ ε m i ω)
      ≤ (∑' k : ℕ, |π (k + min K m)|) * c0
        + (∑' n : ℕ, |π n|) * ((∑' k : ℕ, |ψ (k + m)|) * Real.sqrt σ2) := by
  have hmemX : ∀ t : ℤ, MemLp (X t) 2 μ := fun t => hX.memLp hψ hε hmeas t
  have h1 : MemLp (fun ω => icoResid π X 0 K i ω - icoResid π X 0 m i ω) 2 μ :=
    (memLp_icoResid hmemX π 0 K i).sub (memLp_icoResid hmemX π 0 m i)
  have h2 : MemLp (fun ω => icoResid π X 0 m i ω - blockResid π ψ ε m i ω) 2 μ :=
    (memLp_icoResid hmemX π 0 m i).sub (memLp_blockResid hε π ψ m i)
  refine le_trans (l2n_sub_le_add h1 h2) (add_le_add ?_ ?_)
  · exact l2n_icoResid_diff_le hmemX hc hπ K m i
  · exact l2n_icoResid_sub_blockResid hX hψ hε hmeas hπ m i

/-- **The `L¹` comparison**: the Cesàro sum of the squared rows of `Π_T` and its
finite-noise-window surrogate differ, in mean, by the coefficient tails plus an edge term
supported on the last `m` rows. Cauchy–Schwarz is applied row by row, so only *second*
moments of the noise are used — this is the point at which the recorded "fourth
cumulants" obstruction to a direct `L²` law is bypassed. -/
private lemma integral_defect_le [IsProbabilityMeasure μ] {ψ π : ℕ → ℝ} {σ2 c0 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ) (hψ : Summable fun j => |ψ j|)
    (hε : IsWhiteNoise ε σ2 μ) (hmeas : ∀ t, Measurable (X t))
    (hπ : Summable fun n => |π n|) (hc : ∀ t : ℤ, l2n μ (X t) = c0) (m T : ℕ) :
    ∫ ω, ∑ i ∈ Finset.range T,
        |icoResid π X 0 (T - i) i ω ^ 2 - blockResid π ψ ε m i ω ^ 2| ∂μ
      ≤ ((T : ℝ) * ((∑' k : ℕ, |π (k + m)|) * c0
            + (∑' n : ℕ, |π n|) * ((∑' k : ℕ, |ψ (k + m)|) * Real.sqrt σ2))
          + (m : ℝ) * ((∑' n : ℕ, |π n|) * c0))
        * ((∑' n : ℕ, |π n|) * c0
            + (∑' n : ℕ, |π n|) * ((∑' n : ℕ, |ψ n|) * Real.sqrt σ2)) := by
  classical
  have hmemX : ∀ t : ℤ, MemLp (X t) 2 μ := fun t => hX.memLp hψ hε hmeas t
  have hc0 : 0 ≤ c0 := by rw [← hc 0]; exact l2n_nonneg _ _
  have hP0 : (0 : ℝ) ≤ ∑' n : ℕ, |π n| := tsum_nonneg fun n => abs_nonneg _
  have hQ0 : (0 : ℝ) ≤ ∑' n : ℕ, |ψ n| := tsum_nonneg fun n => abs_nonneg _
  have hs0 : (0 : ℝ) ≤ Real.sqrt σ2 := Real.sqrt_nonneg _
  set G : ℝ := (∑' n : ℕ, |π n|) * c0
      + (∑' n : ℕ, |π n|) * ((∑' n : ℕ, |ψ n|) * Real.sqrt σ2) with hGdef
  have hG0 : 0 ≤ G := by rw [hGdef]; positivity
  set rho : ℝ := (∑' k : ℕ, |π (k + m)|) * c0
      + (∑' n : ℕ, |π n|) * ((∑' k : ℕ, |ψ (k + m)|) * Real.sqrt σ2) with hrhodef
  have hint : ∀ i : ℕ, Integrable (fun ω =>
      |icoResid π X 0 (T - i) i ω ^ 2 - blockResid π ψ ε m i ω ^ 2|) μ := by
    intro i
    have h1 : Integrable (fun ω => icoResid π X 0 (T - i) i ω ^ 2) μ := by
      have h := (memLp_icoResid hmemX π 0 (T - i) i).integrable_mul
        (memLp_icoResid hmemX π 0 (T - i) i)
      exact h.congr (Filter.Eventually.of_forall fun ω => by simp [Pi.mul_apply, sq])
    exact (h1.sub (integrable_blockResid_sq hε π ψ m i)).abs
  rw [integral_finset_sum _ fun i _ => hint i]
  have hper : ∀ i ∈ Finset.range T,
      ∫ ω, |icoResid π X 0 (T - i) i ω ^ 2 - blockResid π ψ ε m i ω ^ 2| ∂μ
        ≤ (rho + (if T - i < m then (∑' n : ℕ, |π n|) else 0) * c0) * G := by
    intro i _
    have hfac : ∀ ω, |icoResid π X 0 (T - i) i ω ^ 2 - blockResid π ψ ε m i ω ^ 2|
        = |(icoResid π X 0 (T - i) i ω - blockResid π ψ ε m i ω)
            * (icoResid π X 0 (T - i) i ω + blockResid π ψ ε m i ω)| := by
      intro ω
      congr 1
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hfac)]
    have hd : l2n μ (fun ω => icoResid π X 0 (T - i) i ω - blockResid π ψ ε m i ω)
        ≤ rho + (if T - i < m then (∑' n : ℕ, |π n|) else 0) * c0 := by
      refine le_trans (l2n_row_sub_blockResid hX hψ hε hmeas hπ hc (T - i) m i) ?_
      have h3 := mul_le_mul_of_nonneg_right (tail_min_le hπ (T - i) m) hc0
      rw [add_mul] at h3
      rw [hrhodef]
      linarith
    have hsm : l2n μ (fun ω => icoResid π X 0 (T - i) i ω + blockResid π ψ ε m i ω) ≤ G := by
      refine le_trans (l2n_add_le (memLp_icoResid hmemX π 0 (T - i) i)
        (memLp_blockResid hε π ψ m i)) ?_
      have h1 : l2n μ (icoResid π X 0 (T - i) i) ≤ (∑' n : ℕ, |π n|) * c0 := by
        have h := l2n_icoResid_le hmemX hc hπ 0 (T - i) i
        simpa using h
      have h2 := l2n_blockResid_le hψ hε hπ m i
      rw [hGdef]
      linarith
    have hd0 : 0 ≤ rho + (if T - i < m then (∑' n : ℕ, |π n|) else 0) * c0 :=
      le_trans (l2n_nonneg μ _) hd
    refine le_trans (integral_abs_mul_le
      ((memLp_icoResid hmemX π 0 (T - i) i).sub (memLp_blockResid hε π ψ m i))
      ((memLp_icoResid hmemX π 0 (T - i) i).add (memLp_blockResid hε π ψ m i))) ?_
    exact mul_le_mul hd hsm (l2n_nonneg _ _) hd0
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hG0
  have hsplit : ∑ i ∈ Finset.range T,
      (rho + (if T - i < m then (∑' n : ℕ, |π n|) else 0) * c0)
      = (T : ℝ) * rho + ∑ i ∈ Finset.range T,
          (if T - i < m then (∑' n : ℕ, |π n|) * c0 else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : T - i < m
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi, zero_mul]
  rw [hsplit]
  have hedge := sum_edge_le T m (c := (∑' n : ℕ, |π n|) * c0) (by positivity)
  linarith

-- The residual-row identity below re-unifies the full `piMat`/`dotProduct` statement at
-- width `T` several times, which exceeds the default heartbeat budget at `whnf`.
set_option maxHeartbeats 1600000 in
open Matrix in
/-- **Step (C) of the `armaProfileS_tendstoInProb` route — PROVED**: the residual
sum-of-squares LLN `T⁻¹‖Π_T x‖² →p σ² · Σ_j c_j²`.

This is the **only** remaining gap in `armaProfileS_tendstoInProb`; steps (A) and (B) are
proved. It is stated here as a named theorem rather than left as an anonymous `have` inside
that proof, so that a sorry census names it (project charter §2, "`sorry` is a planned
debt": lift it to a top-level lemma so future sessions see the gap).

**The route, as executed (ergodic-theorem-free).** The Mathlib pin has **no** pointwise
(Birkhoff) ergodic theorem — only von Neumann's mean ergodic theorem, an `L²` statement
that does not reach the `L¹` variable `r_t(θ)²` — and a *direct* `L²` LLN for `r_t(θ)²`
is genuinely blocked by fourth cumulants. Neither is needed:

* **the finite-window surrogate** `blockResid`: `z_i^{(m)} = Σ_{d,n<m} π_d ψ_n ε_{i+1+d−n}`
  truncates *both* the composite filter and the linear process, so it is a fixed linear
  functional of the noise over the window `[i+1−m, i+m]` — the double truncation is what
  makes the window finite (truncating only the filter still leaves the whole noise past);
* **the progression device**: along `i ≡ k (mod 2m)` the windows are disjoint, so
  `(z_i^{(m)})²` is i.i.d. (shift invariance of finite i.i.d. blocks for the law,
  `iIndepFun.indepFun_finset` for the independence) and `L¹`, and Etemadi's
  `ProbabilityTheory.strong_law_ae` applies progression by progression. Summing the `2m`
  progressions handles `T` of the form `N·(2m)`; the general `T` follows from monotonicity
  of the partial sums (`tendsto_avg_of_tendsto_block`);
* **the second moment is exactly right**, by a *combinatorial* Parseval identity rather
  than a Fourier one: the involution `((d,n),(d′,n′)) ↦ ((d,n′),(d′,n))` carries the
  difference constraint `d − n = d′ − n′` (which is what `E[ε_a ε_b] = σ²δ_{ab}` produces
  on the *reversed* window) to the sum constraint `d + n = d′ + n′` (which is the square of
  the composite filter), leaving the summand fixed. Hence
  `E[(z_i^{(m)})²] = σ² Σ_r (c_r^{(m)})² → σ² Σ_r c_r²`;
* **the `m → ∞` transfer uses second moments only**: row by row,
  `∫|u_i² − z_i²| = ∫|(u_i − z_i)(u_i + z_i)| ≤ ‖u_i − z_i‖₂ (‖u_i‖₂ + ‖z_i‖₂)`, and
  `‖u_i − z_i‖₂` is bounded by the `π`-tail at `min(T − i, m)` plus `Σ|π| ·` the `ψ`-tail
  at `m`. The `min` produces an edge term supported on the last `m` rows only, which costs
  `O(m/T)`. Markov then gives the `L¹` half and the three-`ε` split finishes.

**Orientation.** `Π_T` is *upper* triangular, so its rows are the **time-reversed**
residuals `u_i = Σ_{j ≥ 0} π_j(θ) x_{i+j}` truncated at `x_T` (`icoResid`); the composite
filter is therefore truncated *forwards* in `i`, and the surrogate's window is centred at
`i + 1`, not at `1`. -/
theorem armaResidualSS_tendstoInProb [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t)) {η' : ℝ} (hη' : 0 < η') :
    Tendsto (fun T : ℕ => (μ {ω | η' ≤
        |(T : ℝ)⁻¹ * ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
            (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
          - σ2 * armaContrastVar b0 a0 b a|}).toReal)
      atTop (𝓝 0) := by
  classical
  have hπs : Summable fun n => |armaPi b a n| := summable_abs_armaPi hB
  have hψs : Summable fun n => |armaPsi b0 a0 n| := summable_abs_armaPsi a0 hB0.1
  have hwn : IsWhiteNoise ε σ2 μ := h.whiteNoise
  have hmemX : ∀ t : ℤ, MemLp (X t) 2 μ := fun t => hcausal.memLp hψs hwn hmeas t
  obtain ⟨c0, hc⟩ : ∃ c0 : ℝ, ∀ t : ℤ, l2n μ (X t) = c0 :=
    ⟨l2n μ (X 0), fun t => l2n_linearProcess_eq hcausal hψs hwn hmeas t 0⟩
  have hc0 : 0 ≤ c0 := by rw [← hc 0]; exact l2n_nonneg _ _
  have hs0 : (0 : ℝ) ≤ Real.sqrt σ2 := Real.sqrt_nonneg _
  obtain ⟨P, hPdef⟩ : ∃ x : ℝ, x = ∑' n : ℕ, |armaPi b a n| := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ x : ℝ, x = ∑' n : ℕ, |armaPsi b0 a0 n| := ⟨_, rfl⟩
  obtain ⟨tp, htpdef⟩ : ∃ f : ℕ → ℝ, f = fun m => ∑' k : ℕ, |armaPi b a (k + m)| := ⟨_, rfl⟩
  obtain ⟨tq, htqdef⟩ : ∃ f : ℕ → ℝ, f = fun m => ∑' k : ℕ, |armaPsi b0 a0 (k + m)| :=
    ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ x : ℝ, x = P * c0 + P * (Q * Real.sqrt σ2) := ⟨_, rfl⟩
  obtain ⟨rho, hrhodef⟩ : ∃ f : ℕ → ℝ,
      f = fun m => tp m * c0 + P * (tq m * Real.sqrt σ2) := ⟨_, rfl⟩
  obtain ⟨Mm, hMmdef⟩ : ∃ f : ℕ → ℝ,
      f = fun m => σ2 * ∑ r ∈ Finset.range (2 * m),
        cTrunc (armaPi b a) (armaPsi b0 a0) m r ^ 2 := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hPdef]; exact tsum_nonneg fun n => abs_nonneg _
  have hQ0 : 0 ≤ Q := by rw [hQdef]; exact tsum_nonneg fun n => abs_nonneg _
  have hG0 : 0 ≤ G := by rw [hGdef]; positivity
  -- **(0)** the quadratic form is the sum of the squared (time-reversed) residual rows
  have hquad : ∀ (T : ℕ) (ω : Ω),
      ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
        (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
        = ∑ i ∈ Finset.range T, icoResid (armaPi b a) X 0 (T - i) i ω ^ 2 := by
    intro T ω
    have hrow : ∀ i : Fin T,
        (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i
          = icoResid (armaPi b a) X 0 (T - (i : ℕ)) (i : ℕ) ω := by
      intro i
      have h1 : (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i
          = ∑ k : Fin T, piK b a (i : ℕ) (k : ℕ) * X (((k : ℕ) : ℤ) + 1) ω := rfl
      rw [h1, Fin.sum_univ_eq_sum_range
        (fun k => piK b a (i : ℕ) k * X ((k : ℤ) + 1) ω) T]
      have hzero : ∑ k ∈ Finset.Ico 0 (i : ℕ),
          piK b a (i : ℕ) k * X ((k : ℤ) + 1) ω = 0 :=
        Finset.sum_eq_zero fun k hk => by
          rw [Finset.mem_Ico] at hk
          rw [piK_eq_zero b a hk.2, zero_mul]
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun k => piK b a (i : ℕ) k * X ((k : ℤ) + 1) ω)
          (Nat.zero_le (i : ℕ)) (le_of_lt i.isLt), hzero, zero_add,
        Finset.sum_Ico_eq_sum_range, icoResid, ← Finset.range_eq_Ico]
      refine Finset.sum_congr rfl fun d _ => ?_
      have hp : piK b a (i : ℕ) ((i : ℕ) + d) = armaPi b a d := by
        rw [piK, if_pos (Nat.le_add_right _ _)]
        congr 1
        omega
      have hx : ((((i : ℕ) + d : ℕ)) : ℤ) + 1 = ((i : ℕ) : ℤ) + 1 + (d : ℕ) := by
        push_cast
        ring
      rw [hp, hx]
    have hdot : ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
        (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
        = ∑ i : Fin T, icoResid (armaPi b a) X 0 (T - (i : ℕ)) (i : ℕ) ω ^ 2 := by
      have hd : ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
          (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
          = ∑ i : Fin T, (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i
              * (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) i := rfl
      rw [hd]
      exact Finset.sum_congr rfl fun i _ => by rw [hrow i]; ring
    rw [hdot]
    exact Fin.sum_univ_eq_sum_range
      (fun i => icoResid (armaPi b a) X 0 (T - i) i ω ^ 2) T
  -- **(1)** the `L¹` comparison with the finite-window surrogate
  have hIle : ∀ m T : ℕ, ∫ ω, ∑ i ∈ Finset.range T,
      |icoResid (armaPi b a) X 0 (T - i) i ω ^ 2
        - blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2| ∂μ
      ≤ ((T : ℝ) * rho m + (m : ℝ) * (P * c0)) * G := by
    intro m T
    rw [hrhodef, hGdef, hPdef, hQdef, htpdef, htqdef]
    exact integral_defect_le hcausal hψs hwn hmeas hπs hc m T
  -- **(2)** Markov
  have hmarkov : ∀ (m T : ℕ), 0 < T →
      (μ {ω | η' / 3 ≤
        |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, icoResid (armaPi b a) X 0 (T - i) i ω ^ 2
          - (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
              blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2|}).toReal
        ≤ 3 / η' * (rho m * G) + 3 / η' * ((m : ℝ) * (P * c0) * G / T) := by
    intro m T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have hintD : Integrable (fun ω => ∑ i ∈ Finset.range T,
        |icoResid (armaPi b a) X 0 (T - i) i ω ^ 2
          - blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2|) μ := by
      refine integrable_finset_sum _ fun i _ => ?_
      have h1 : Integrable (fun ω => icoResid (armaPi b a) X 0 (T - i) i ω ^ 2) μ := by
        have hh := (memLp_icoResid hmemX (armaPi b a) 0 (T - i) i).integrable_mul
          (memLp_icoResid hmemX (armaPi b a) 0 (T - i) i)
        exact hh.congr (Filter.Eventually.of_forall fun ω => by simp [Pi.mul_apply, sq])
      exact (h1.sub (integrable_blockResid_sq hwn _ _ m i)).abs
    have hDnn : 0 ≤ᵐ[μ] fun ω => (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
        |icoResid (armaPi b a) X 0 (T - i) i ω ^ 2
          - blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2| := by
      filter_upwards with ω
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    have hsubset : {ω | η' / 3 ≤
          |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, icoResid (armaPi b a) X 0 (T - i) i ω ^ 2
            - (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
                blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2|}
        ⊆ {ω | η' / 3 ≤ (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
            |icoResid (armaPi b a) X 0 (T - i) i ω ^ 2
              - blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2|} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      refine le_trans hω ?_
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (T : ℝ)⁻¹),
        ← Finset.sum_sub_distrib]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    have hmark := mul_meas_ge_le_integral_of_nonneg hDnn (hintD.const_mul (T : ℝ)⁻¹) (η' / 3)
    rw [integral_const_mul] at hmark
    rw [measureReal_def] at hmark
    have hstep : (T : ℝ)⁻¹ * ∫ ω, ∑ i ∈ Finset.range T,
        |icoResid (armaPi b a) X 0 (T - i) i ω ^ 2
          - blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2| ∂μ
        ≤ rho m * G + (m : ℝ) * (P * c0) * G / T := by
      have h1 := mul_le_mul_of_nonneg_left (hIle m T) (by positivity : (0 : ℝ) ≤ (T : ℝ)⁻¹)
      have h2 : (T : ℝ)⁻¹ * (((T : ℝ) * rho m + (m : ℝ) * (P * c0)) * G)
          = rho m * G + (m : ℝ) * (P * c0) * G / T := by
        field_simp <;> ring
      linarith [h1, h2.le, h2.ge]
    have hkey : η' / 3 * (μ {ω | η' / 3 ≤ (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
        |icoResid (armaPi b a) X 0 (T - i) i ω ^ 2
          - blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2|}).toReal
        ≤ rho m * G + (m : ℝ) * (P * c0) * G / T := le_trans hmark hstep
    have hmono := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsubset)
    have hinv : (3 : ℝ) / η' * (η' / 3) = 1 := by field_simp
    have hscale := mul_le_mul_of_nonneg_left hkey
      (le_of_lt (show (0 : ℝ) < 3 / η' by positivity))
    rw [← mul_assoc, hinv, one_mul, mul_add] at hscale
    linarith [hmono, hscale]
  -- **(3)** the `m`-dependent law of large numbers, in probability
  have hLLN : ∀ m : ℕ, 0 < m → Tendsto (fun T : ℕ => (μ {ω | η' / 3 ≤
      |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
          blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2 - Mm m|}).toReal)
      atTop (𝓝 0) := by
    intro m hm
    have hae := ae_tendsto_avg_blockResid_sq hiid (armaPi b a) (armaPsi b0 a0) hm
    have heq : (∫ ω, blockResid (armaPi b a) (armaPsi b0 a0) ε m 0 ω ^ 2 ∂μ) = Mm m := by
      rw [hMmdef]
      exact integral_blockResid_sq_eq hwn _ _ m 0
    rw [heq] at hae
    have hmf : ∀ T : ℕ, AEStronglyMeasurable (fun ω => (T : ℝ)⁻¹ *
        ∑ i ∈ Finset.range T, blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2) μ := by
      intro T
      refine AEStronglyMeasurable.const_mul ?_ _
      exact (Finset.measurable_sum _ fun i _ =>
        ((measurable_blockResid hiid.measurable _ _ m i).pow_const 2)).aestronglyMeasurable
    have htim := MeasureTheory.tendstoInMeasure_of_tendsto_ae (g := fun _ : Ω => Mm m) hmf
      (by filter_upwards [hae] with ω hω using hω)
    have hz := htim (ENNReal.ofReal (η' / 3)) (ENNReal.ofReal_pos.2 (by linarith))
    have hset : ∀ T : ℕ,
        {ω | ENNReal.ofReal (η' / 3) ≤ edist ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
            blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2) (Mm m)}
        = {ω | η' / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
            blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2 - Mm m|} := by
      intro T
      ext ω
      simp only [Set.mem_setOf_eq, edist_dist, Real.dist_eq,
        ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
    have hz2 : Tendsto (fun T : ℕ => (μ {ω | ENNReal.ofReal (η' / 3) ≤
        edist ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
          blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2) (Mm m)}).toReal)
        atTop (𝓝 0) := by
      simpa using! (ENNReal.tendsto_toReal (by simp)).comp hz
    exact hz2.congr fun T => congrArg ENNReal.toReal (congrArg μ (hset T))
  -- **(4)** the deterministic limits
  have hrhoT : Tendsto rho atTop (𝓝 0) := by
    rw [hrhodef]
    have h1 : Tendsto tp atTop (𝓝 0) := by rw [htpdef]; exact tendsto_tail_zero hπs
    have h2 : Tendsto tq atTop (𝓝 0) := by rw [htqdef]; exact tendsto_tail_zero hψs
    have h3 := (h1.mul_const c0).add ((h2.mul_const (Real.sqrt σ2)).const_mul P)
    simpa using h3
  have hMmT : Tendsto Mm atTop (𝓝 (σ2 * armaContrastVar b0 a0 b a)) := by
    rw [hMmdef]
    exact (tendsto_sum_sq_cTrunc hB0 hB).const_mul σ2
  -- **(5)** assembly
  have hgoalset : ∀ T : ℕ,
      {ω | η' ≤ |(T : ℝ)⁻¹ * ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
          (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
        - σ2 * armaContrastVar b0 a0 b a|}
      = {ω | η' ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
          icoResid (armaPi b a) X 0 (T - i) i ω ^ 2 - σ2 * armaContrastVar b0 a0 b a|} := by
    intro T
    ext ω
    simp only [Set.mem_setOf_eq, hquad T ω]
  simp only [hgoalset]
  refine Metric.tendsto_atTop.2 fun ζ hζ => ?_
  obtain ⟨m, hm1, hmb, hmM⟩ : ∃ m : ℕ, 0 < m ∧ 3 / η' * (rho m * G) < ζ / 3 ∧
      |Mm m - σ2 * armaContrastVar b0 a0 b a| < η' / 3 := by
    have e1 : ∀ᶠ m : ℕ in atTop, 3 / η' * (rho m * G) < ζ / 3 := by
      have h0 : Tendsto (fun m : ℕ => 3 / η' * (rho m * G)) atTop (𝓝 0) := by
        simpa using (hrhoT.mul_const G).const_mul (3 / η')
      exact h0.eventually (gt_mem_nhds (by linarith))
    have e2 : ∀ᶠ m : ℕ in atTop, |Mm m - σ2 * armaContrastVar b0 a0 b a| < η' / 3 := by
      have h1 : Tendsto (fun m : ℕ => Mm m - σ2 * armaContrastVar b0 a0 b a) atTop (𝓝 0) := by
        simpa using hMmT.sub (tendsto_const_nhds (x := σ2 * armaContrastVar b0 a0 b a))
      have h0 : Tendsto (fun m : ℕ => |Mm m - σ2 * armaContrastVar b0 a0 b a|) atTop (𝓝 0) := by
        simpa using h1.abs
      exact h0.eventually (gt_mem_nhds (by linarith))
    obtain ⟨m, ⟨⟨h1, h2⟩, h3⟩⟩ := ((e1.and e2).and (eventually_gt_atTop 0)).exists
    exact ⟨m, h3, h1, h2⟩
  have hTterm : Tendsto (fun T : ℕ => 3 / η' * ((m : ℝ) * (P * c0) * G / T)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℕ => ((m : ℝ) * (P * c0) * G) / (T : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using h1.const_mul (3 / η')
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (((hTterm.eventually (gt_mem_nhds (show (0 : ℝ) < ζ / 3 by linarith))).and
      ((hLLN m hm1).eventually (gt_mem_nhds (show (0 : ℝ) < ζ / 3 by linarith)))).and
      (eventually_gt_atTop 0))
  refine ⟨N, fun T hT => ?_⟩
  obtain ⟨⟨hT1, hT2⟩, hT3⟩ := hN T hT
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  have hsub : {ω | η' ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
        icoResid (armaPi b a) X 0 (T - i) i ω ^ 2 - σ2 * armaContrastVar b0 a0 b a|}
      ⊆ {ω | η' / 3 ≤
          |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, icoResid (armaPi b a) X 0 (T - i) i ω ^ 2
            - (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
                blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2|}
        ∪ {ω | η' / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
              blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2 - Mm m|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have e1 := abs_sub_le
      ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, icoResid (armaPi b a) X 0 (T - i) i ω ^ 2)
      ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
        blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2)
      (σ2 * armaContrastVar b0 a0 b a)
    have e2 := abs_sub_le
      ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
        blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2)
      (Mm m) (σ2 * armaContrastVar b0 a0 b a)
    linarith
  calc (μ {ω | η' ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
        icoResid (armaPi b a) X 0 (T - i) i ω ^ 2 - σ2 * armaContrastVar b0 a0 b a|}).toReal
      ≤ (μ ({ω | η' / 3 ≤
          |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, icoResid (armaPi b a) X 0 (T - i) i ω ^ 2
            - (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
                blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2|}
        ∪ {ω | η' / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
              blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2 - Mm m|})).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    _ ≤ (μ {ω | η' / 3 ≤
          |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, icoResid (armaPi b a) X 0 (T - i) i ω ^ 2
            - (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
                blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2|}).toReal
        + (μ {ω | η' / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
              blockResid (armaPi b a) (armaPsi b0 a0) ε m i ω ^ 2 - Mm m|}).toReal := by
        refine le_trans (ENNReal.toReal_mono (by finiteness) (measure_union_le _ _)) ?_
        exact le_of_eq (ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _))
    _ < ζ := by
        have hmk := hmarkov m T hT3
        linarith

-- The `have hCLLN := armaResidualSS_tendstoInProb …` application below re-unifies the
-- full matrix statement (piMat/dotProduct at width `T`), which exceeds the default
-- heartbeat budget at `whnf`.
open Matrix in
set_option maxHeartbeats 1600000 in
/-- **The one missing analytic input of this lane** (named debt): the *quadratic-form
law of large numbers*

  `T⁻¹ · xᵀ Γ_T(θ)⁻¹ x  →p  σ² · armaContrastVar θ₀ θ`

for data from the true ARMA law. Everything else in `criterion_tendsto_contrast` is
discharged from this input below (the `log`-continuity transfer and the deterministic
`T⁻¹ log det Γ_T → 0`, which is PROVED as `logdet_armaToeplitz_vanishes`).

**The earlier verdict on this debt — "needs the pointwise ergodic theorem, which the
pin does not have" — is OVERTURNED.** The pin really does lack Birkhoff (it carries
only von Neumann's mean ergodic theorem, `Analysis/InnerProductSpace/MeanErgodic.lean`,
which is an `L²` statement and so does not reach the `L¹` variable `r_t(θ)²`; the repo
records the same gap at `Mixing/LimitTheorems.slln_of_alphaMixing_debt`). But *this*
statistic does not need it. The route, and what is actually left:

* **(A) deterministic half — PROVED** as `armaProfileS_eq_gramTail_quadForm`:
  `S_T = uᵀ (1 + G_T)⁻¹ u` with `u = Π_T x` the vector of truncated `θ`-residuals.
  Writing `(1 + G)⁻¹ = 1 − (1 + G)⁻¹G` splits this into `‖u‖² − uᵀ (1+G)⁻¹G u`.
* **(B) the correction term — PROVED** as `gramTail_quadForm_tendstoInProb`, and the
  deterministic sandwich it feeds is `armaProfileS_sandwich`:
  `‖u‖² − uᵀ G_T u ≤ S_T ≤ ‖u‖²`. Two amendments to the plan recorded above were
  needed, and both simplify it:
  - the positive semidefiniteness of `(1+G)⁻¹G` is **not** needed, and neither is any
    eigenbasis: substituting `x = (1+G)y` turns both halves of the sandwich into the
    polynomial identities `b + c ≥ 0`, `c + d ≥ 0` (`quadForm_one_add_inv_bounds`);
  - the trace inequality `tr(AB) ≤ ‖A‖_op tr B` is **not** needed either. For psd `M`
    one has `|M_ij| ≤ (M_ii + M_jj)/2` (`abs_entry_le_of_posSemidef`), which already
    redistributes the pairing onto the diagonal:
    `tr(M S) ≤ (max_i Σ_j |S_ij|) · tr M` (`sum_entry_mul_le_of_posSemidef`). This
    Schur test is what the row sums of `E[u_i u_j] = σ² Σ_{k,l} π̃(i,k) π̃(j,l) γ(k−l)`
    feed, via `summable_abs_armaPi` and `summable_abs_armaACVF` exactly as predicted
    (`rowSum_kernel_le`). Since `Cov u` never appears as an operator, no bound on it is
    needed; the second-moment matrix is used directly, and its mean-zero input
    (`integral_linearProcess_eq_zero`, `integral_mul_linearProcess`) is proved here.
* **(C) — PROVED** as the named lemma `armaResidualSS_tendstoInProb` above:
  `T⁻¹‖u‖² →p σ² Σ_j c_j²`, ergodic-theorem-free. See its docstring for the executed
  route. Two amendments to the plan recorded here were needed:
  - the truncation must be *double* (`blockResid`): truncating only the composite filter
    at lag `m` leaves each `r_t^{(m)}` a function of the *entire* noise past, so the
    progressions are not independent. Truncating the linear process at `m` as well makes
    the window `[i+1−m, i+m]` finite, and the progression step is `2m`, not `m`;
  - the `m → ∞` transfer is *not* the two-factor Cauchy–Schwarz recorded above but the
    row-by-row one, `∫|u_i² − z_i²| ≤ ‖u_i − z_i‖₂ (‖u_i‖₂ + ‖z_i‖₂)`, followed by a
    single Markov inequality. Both use second moments only, so the recorded "fourth
    cumulants" obstruction (real, but only against a *direct* `L²` LLN for `r_t(θ)²`)
    is untouched. The edge effect appears as the `min(T − i, m)` in the `π`-tail and
    costs `O(m/T)`.
  Its second-moment computation goes through a **combinatorial** Parseval identity — the
  involution `((d,n),(d′,n′)) ↦ ((d,n′),(d′,n))` — rather than a Fourier argument; the
  time-reversal of `Π_T` is exactly what turns the sum constraint into the difference
  constraint, so the reversal is not merely harmless bookkeeping but the reason the
  identity is needed.

  **Orientation (correcting the note at `armaProfileS_eq_gramTail_quadForm`).** `Π_T`
  is *upper* triangular (`det_piMat` proves determinant one from
  `piK b a i k = 0` for `k < i`), so its rows are the *time-reversed* residuals
  `u_i = Σ_{j ≥ 0} π_j(θ) x_{i+j}`, truncated at `x_T` — not `Σ_{j ≤ i} π_{i−j} x_j`
  truncated at `x_1`. This changes nothing in the limit, since
  `E[u_i²] = σ² Σ_{d,e ≥ 0} π_d π_e γ_{θ₀}(e − d)` is symmetric in the reversal
  (`γ` is even) and tends to `σ² Σ_n c_n²` as `i` recedes from the truncation; but an
  implementation of (C) must truncate the composite filter *forwards* in `i`. -/
theorem armaProfileS_tendstoInProb [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T : ℕ => (μ {ω | η ≤
        |(T : ℝ)⁻¹ * armaProfileS b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          - σ2 * armaContrastVar b0 a0 b a|}).toReal)
      atTop (𝓝 0) := by
  -- **(C)** — the residual sum of squares LLN; the single remaining gap, now the named
  -- debt `armaResidualSS_tendstoInProb` above.
  -- no type ascription: the `have` takes the debt's stated type verbatim, so there is
  -- no second copy of the matrix statement to re-unify against
  have hCLLN := fun (η' : ℝ) (hη' : 0 < η') =>
    armaResidualSS_tendstoInProb (b := b) (a := a) h hiid hσ hB0 hB hcausal hmeas hη'
  -- **(B)** — the correction term, proved above.
  have hB2 := gramTail_quadForm_tendstoInProb (b0 := b0) (a0 := a0) h.whiteNoise (le_of_lt hσ)
    hB0 hB hcausal hmeas (η := η / 2) (by linarith)
  have hsum : Tendsto (fun T : ℕ =>
      (μ {ω | η / 2 ≤
        |(T : ℝ)⁻¹ * ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
            (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
          - σ2 * armaContrastVar b0 a0 b a|}).toReal
      + (μ {ω | η / 2 ≤ (T : ℝ)⁻¹ *
          ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
            (gramTail b a T *ᵥ
              (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))}).toReal)
      atTop (𝓝 0) := by
    simpa using (hCLLN (η / 2) (by linarith)).add hB2
  refine squeeze_zero' (Eventually.of_forall fun T => ENNReal.toReal_nonneg) ?_ hsum
  filter_upwards with T
  -- the sandwich turns the event into the union of the two events above
  have hsub : {ω | η ≤
        |(T : ℝ)⁻¹ * armaProfileS b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          - σ2 * armaContrastVar b0 a0 b a|}
      ⊆ {ω | η / 2 ≤
          |(T : ℝ)⁻¹ * ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
            - σ2 * armaContrastVar b0 a0 b a|}
        ∪ {ω | η / 2 ≤ (T : ℝ)⁻¹ *
            ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (gramTail b a T *ᵥ
                (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    obtain ⟨hup, hlow⟩ :=
      armaProfileS_sandwich hB T (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
    have hTnn : (0 : ℝ) ≤ (T : ℝ)⁻¹ := by positivity
    have hup' := mul_le_mul_of_nonneg_left hup hTnn
    have hlow' := mul_le_mul_of_nonneg_left hlow hTnn
    rw [mul_sub] at hlow'
    have habs := abs_lt.1 h1
    rcases le_abs.1 hω with hcase | hcase <;> linarith [habs.1, habs.2]
  calc (μ {ω | η ≤
        |(T : ℝ)⁻¹ * armaProfileS b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          - σ2 * armaContrastVar b0 a0 b a|}).toReal
      ≤ (μ ({ω | η / 2 ≤
          |(T : ℝ)⁻¹ * ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
            - σ2 * armaContrastVar b0 a0 b a|}
        ∪ {ω | η / 2 ≤ (T : ℝ)⁻¹ *
            ((piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (gramTail b a T *ᵥ
                (piMat b a T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))})).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    _ ≤ _ := by
        refine le_trans (ENNReal.toReal_mono (by finiteness) (measure_union_le _ _)) ?_
        exact le_of_eq (ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _))

/-! ### The generic linear-process second-moment LLN

`armaResidualSS_tendstoInProb` is stated for the *composite* filter `π(θ) ∗ ψ(θ₀)` of the
ARMA problem; the ingredient that the rest of the Hannan program consumed (the Brown
input (2) and the sample-PACF linearization of `ARMA/MLEAsymptotics.lean`, both since
removed) is the plain one-filter statement for an **arbitrary** absolutely summable
coefficient sequence, which
is *not* an instance of it (a general `c` is not an ARMA transfer sequence). It is proved
here by the same ergodic-theorem-free device, and is strictly simpler: with `π = δ` the
`min(T − i, m)` edge term of `integral_defect_le` disappears, so the `L¹` defect is
`O(T · tail_m)` with no `O(m)` correction. -/

/-- The Kronecker filter `δ`, whose `blockResid` surrogate is the plain truncation
`Σ_{n < m} c_n ε_{t−n}`. -/
private noncomputable def deltaFilter : ℕ → ℝ := fun n => if n = 0 then 1 else 0

private lemma summable_abs_deltaFilter : Summable fun n => |deltaFilter n| := by
  refine summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) fun n hn => ?_
  simp only [Finset.mem_singleton] at hn
  simp [deltaFilter, hn]

private lemma tsum_abs_deltaFilter : ∑' n : ℕ, |deltaFilter n| = 1 := by
  have h : (fun n : ℕ => |deltaFilter n|) = fun n : ℕ => if n = 0 then (1 : ℝ) else 0 := by
    funext n
    by_cases hn : n = 0 <;> simp [deltaFilter, hn]
  rw [h]
  simpa using tsum_ite_eq (0 : ℕ) (1 : ℝ)

omit [MeasurableSpace Ω] in
/-- With `π = δ` the doubly truncated surrogate is the plain `m`-truncation of the
linear process. -/
private lemma blockResid_deltaFilter {ε : ℤ → Ω → ℝ} (c : ℕ → ℝ) {m : ℕ} (hm : 0 < m)
    (i : ℕ) (ω : Ω) :
    blockResid deltaFilter c ε m i ω
      = ∑ n ∈ Finset.range m, c n * ε (((i : ℤ) + 1) - (n : ℕ)) ω := by
  classical
  rw [blockResid, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rw [← Fin.sum_univ_eq_sum_range (fun n : ℕ => c n * ε (((i : ℤ) + 1) - (n : ℕ)) ω) m]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hd : deltaFilter ((⟨0, hm⟩ : Fin m) : ℕ) = 1 := by simp [deltaFilter]
    rw [hd, one_mul]
    congr 2
    push_cast
    ring
  · intro d _ hd
    refine Finset.sum_eq_zero fun n _ => ?_
    have hd0 : (d : ℕ) ≠ 0 := fun hc => hd (Fin.ext hc)
    simp [deltaFilter, hd0]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

/-- With `π = δ` the truncated composite filter is the truncation of `c` itself. -/
private lemma cTrunc_deltaFilter (c : ℕ → ℝ) {m : ℕ} (hm : 0 < m) (r : ℕ) :
    cTrunc deltaFilter c m r = if r < m then c r else 0 := by
  classical
  rw [cTrunc, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · have hd : deltaFilter ((⟨0, hm⟩ : Fin m) : ℕ) = 1 := by simp [deltaFilter]
    by_cases hr : r < m
    · rw [if_pos hr, Finset.sum_eq_single (⟨r, hr⟩ : Fin m)]
      · simp [hd]
      · intro n _ hn
        have : (n : ℕ) ≠ r := fun hc => hn (Fin.ext hc)
        simp [this]
      · intro hc
        exact absurd (Finset.mem_univ _) hc
    · rw [if_neg hr]
      refine Finset.sum_eq_zero fun n _ => ?_
      refine if_neg ?_
      have hnlt := n.isLt
      simp only [Fin.val_mk, zero_add]
      omega
  · intro d _ hd
    refine Finset.sum_eq_zero fun n _ => ?_
    have hd0 : (d : ℕ) ≠ 0 := fun hc => hd (Fin.ext hc)
    simp [deltaFilter, hd0]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

private lemma sum_sq_cTrunc_deltaFilter (c : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    ∑ r ∈ Finset.range (2 * m), cTrunc deltaFilter c m r ^ 2
      = ∑ r ∈ Finset.range m, c r ^ 2 := by
  classical
  rw [Finset.sum_congr rfl fun r _ => by rw [cTrunc_deltaFilter c hm r]]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * m)) (fun r => r < m)]
  have h1 : ((Finset.range (2 * m)).filter fun r => r < m) = Finset.range m := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have h2 : ∑ r ∈ (Finset.range (2 * m)).filter (fun r => ¬ r < m),
      (if r < m then c r else 0) ^ 2 = 0 :=
    Finset.sum_eq_zero fun r hr => by
      rw [if_neg (Finset.mem_filter.1 hr).2]
      ring
  rw [h1, h2, add_zero]
  exact Finset.sum_congr rfl fun r hr => by rw [if_pos (Finset.mem_range.1 hr)]

/-- **The second-moment LLN for a linear process** (the one-filter form of
`armaResidualSS_tendstoInProb`): for i.i.d. noise and any absolutely summable `c`,

  `T⁻¹ Σ_{t < T} W_{t+1}² →p σ² Σ_n c_n²`.

Ergodic-theorem-free: the surrogate `z_i^{(m)} = Σ_{n<m} c_n ε_{i+1−n}` is a fixed linear
functional of a *finite* block of the noise, so along `i ≡ k (mod 2m)` the squares are
i.i.d. and `L¹` and Etemadi's `strong_law_ae` applies progression by progression; the
`m → ∞` transfer is the row-by-row `∫|u² − z²| ≤ ‖u − z‖₂(‖u‖₂ + ‖z‖₂)`, which uses second
moments only. -/
theorem linearProcess_avgSq_tendstoInProb [IsProbabilityMeasure μ] {c : ℕ → ℝ} {σ2 : ℝ}
    {W ε : ℤ → Ω → ℝ} (hiid : IsIIDNoise ε σ2 μ)
    (hc : Summable fun n => |c n|) (hW : IsLinearProcessOf c W ε μ)
    (hWmeas : ∀ t, Measurable (W t)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T : ℕ => (μ {ω | η ≤ |(T : ℝ)⁻¹ *
        ∑ i ∈ Finset.range T, W ((i : ℤ) + 1) ω ^ 2 - σ2 * ∑' n : ℕ, c n ^ 2|}).toReal)
      atTop (𝓝 0) := by
  classical
  have hwn : IsWhiteNoise ε σ2 μ := hiid.isWhiteNoise
  have hmemW : ∀ t : ℤ, MemLp (W t) 2 μ := fun t => hW.memLp hc hwn hWmeas t
  have hs0 : (0 : ℝ) ≤ Real.sqrt σ2 := Real.sqrt_nonneg _
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, ∀ t : ℤ, l2n μ (W t) = c0 :=
    ⟨l2n μ (W 0), fun t => l2n_linearProcess_eq hW hc hwn hWmeas t 0⟩
  have hc0nn : 0 ≤ c0 := by rw [← hc0 0]; exact l2n_nonneg _ _
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ∑' n : ℕ, |c n| := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hPdef]; exact tsum_nonneg fun n => abs_nonneg _
  obtain ⟨tl, htldef⟩ : ∃ f : ℕ → ℝ, f = fun m => ∑' k : ℕ, |c (k + m)| := ⟨_, rfl⟩
  have htl0 : ∀ m, 0 ≤ tl m := by
    intro m; rw [htldef]; exact tsum_nonneg fun k => abs_nonneg _
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = c0 + P * Real.sqrt σ2 := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hGdef]; positivity
  have hsqsum : Summable fun n : ℕ => c n ^ 2 := by
    refine Summable.of_norm_bounded_eventually (g := fun n => |c n|) hc ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [(hc.tendsto_atTop_zero.eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))] with n hn
    have h1 : |c n| ≤ 1 := le_of_lt hn
    have h2 : |c n ^ 2| = |c n| * |c n| := by rw [sq, abs_mul]
    rw [Real.norm_eq_abs, h2]
    nlinarith [abs_nonneg (c n)]
  obtain ⟨Mm, hMmdef⟩ : ∃ f : ℕ → ℝ, f = fun m => σ2 * ∑ r ∈ Finset.range m, c r ^ 2 :=
    ⟨_, rfl⟩
  -- **(1)** the `L¹` comparison with the finite-window surrogate: no edge term
  have hIle : ∀ m T : ℕ, 0 < m →
      ∫ ω, ∑ i ∈ Finset.range T,
        |W ((i : ℤ) + 1) ω ^ 2 - blockResid deltaFilter c ε m i ω ^ 2| ∂μ
      ≤ (T : ℝ) * (tl m * Real.sqrt σ2 * G) := by
    intro m T hm
    have hint : ∀ i : ℕ, Integrable (fun ω =>
        |W ((i : ℤ) + 1) ω ^ 2 - blockResid deltaFilter c ε m i ω ^ 2|) μ := by
      intro i
      have h1 : Integrable (fun ω => W ((i : ℤ) + 1) ω ^ 2) μ := by
        have hh := (hmemW ((i : ℤ) + 1)).integrable_mul (hmemW ((i : ℤ) + 1))
        exact hh.congr (Filter.Eventually.of_forall fun ω => by simp [Pi.mul_apply, sq])
      exact (h1.sub (integrable_blockResid_sq hwn _ _ m i)).abs
    rw [integral_finset_sum _ fun i _ => hint i]
    have hper : ∀ i ∈ Finset.range T,
        ∫ ω, |W ((i : ℤ) + 1) ω ^ 2 - blockResid deltaFilter c ε m i ω ^ 2| ∂μ
          ≤ tl m * Real.sqrt σ2 * G := by
      intro i _
      have hfac : ∀ ω, |W ((i : ℤ) + 1) ω ^ 2 - blockResid deltaFilter c ε m i ω ^ 2|
          = |(W ((i : ℤ) + 1) ω - blockResid deltaFilter c ε m i ω)
              * (W ((i : ℤ) + 1) ω + blockResid deltaFilter c ε m i ω)| := by
        intro ω
        congr 1
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hfac)]
      have hdiff : l2n μ (fun ω =>
          W ((i : ℤ) + 1) ω - blockResid deltaFilter c ε m i ω) ≤ tl m * Real.sqrt σ2 := by
        have hrw : (fun ω => W ((i : ℤ) + 1) ω - blockResid deltaFilter c ε m i ω)
            = fun ω => W ((i : ℤ) + 1) ω
              - ∑ n ∈ Finset.range m, c n * ε (((i : ℤ) + 1) - (n : ℕ)) ω := by
          funext ω
          rw [blockResid_deltaFilter c hm i ω]
        rw [hrw, htldef]
        exact l2n_sub_psum_le hW hc hwn hWmeas ((i : ℤ) + 1) m
      have hsm : l2n μ (fun ω =>
          W ((i : ℤ) + 1) ω + blockResid deltaFilter c ε m i ω) ≤ G := by
        refine le_trans (l2n_add_le (hmemW _) (memLp_blockResid hwn deltaFilter c m i)) ?_
        have h2 := l2n_blockResid_le hc hwn summable_abs_deltaFilter m i
        rw [tsum_abs_deltaFilter, one_mul] at h2
        rw [hGdef, hc0, hPdef]
        linarith
      refine le_trans (integral_abs_mul_le ((hmemW _).sub (memLp_blockResid hwn _ _ m i))
        ((hmemW _).add (memLp_blockResid hwn _ _ m i))) ?_
      exact mul_le_mul hdiff hsm (l2n_nonneg _ _)
        (mul_nonneg (htl0 m) hs0)
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- **(2)** Markov
  have hmarkov : ∀ (m T : ℕ), 0 < m → 0 < T →
      (μ {ω | η / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, W ((i : ℤ) + 1) ω ^ 2
        - (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
            blockResid deltaFilter c ε m i ω ^ 2|}).toReal
        ≤ 3 / η * (tl m * Real.sqrt σ2 * G) := by
    intro m T hm hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have hintD : Integrable (fun ω => ∑ i ∈ Finset.range T,
        |W ((i : ℤ) + 1) ω ^ 2 - blockResid deltaFilter c ε m i ω ^ 2|) μ := by
      refine integrable_finset_sum _ fun i _ => ?_
      have h1 : Integrable (fun ω => W ((i : ℤ) + 1) ω ^ 2) μ := by
        have hh := (hmemW ((i : ℤ) + 1)).integrable_mul (hmemW ((i : ℤ) + 1))
        exact hh.congr (Filter.Eventually.of_forall fun ω => by simp [Pi.mul_apply, sq])
      exact (h1.sub (integrable_blockResid_sq hwn _ _ m i)).abs
    have hDnn : 0 ≤ᵐ[μ] fun ω => (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
        |W ((i : ℤ) + 1) ω ^ 2 - blockResid deltaFilter c ε m i ω ^ 2| := by
      filter_upwards with ω
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    have hsubset : {ω | η / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, W ((i : ℤ) + 1) ω ^ 2
          - (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
              blockResid deltaFilter c ε m i ω ^ 2|}
        ⊆ {ω | η / 3 ≤ (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
            |W ((i : ℤ) + 1) ω ^ 2 - blockResid deltaFilter c ε m i ω ^ 2|} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      refine le_trans hω ?_
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (T : ℝ)⁻¹),
        ← Finset.sum_sub_distrib]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    have hmark := mul_meas_ge_le_integral_of_nonneg hDnn (hintD.const_mul (T : ℝ)⁻¹) (η / 3)
    rw [integral_const_mul, measureReal_def] at hmark
    have hstep : (T : ℝ)⁻¹ * ∫ ω, ∑ i ∈ Finset.range T,
        |W ((i : ℤ) + 1) ω ^ 2 - blockResid deltaFilter c ε m i ω ^ 2| ∂μ
        ≤ tl m * Real.sqrt σ2 * G := by
      have h1 := mul_le_mul_of_nonneg_left (hIle m T hm)
        (by positivity : (0 : ℝ) ≤ (T : ℝ)⁻¹)
      have h2 : (T : ℝ)⁻¹ * ((T : ℝ) * (tl m * Real.sqrt σ2 * G))
          = tl m * Real.sqrt σ2 * G := by field_simp
      linarith [h1, h2.le, h2.ge]
    have hkey : η / 3 * (μ {ω | η / 3 ≤ (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
        |W ((i : ℤ) + 1) ω ^ 2 - blockResid deltaFilter c ε m i ω ^ 2|}).toReal
        ≤ tl m * Real.sqrt σ2 * G := le_trans hmark hstep
    have hmono := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsubset)
    have hinv : (3 : ℝ) / η * (η / 3) = 1 := by field_simp
    have hscale := mul_le_mul_of_nonneg_left hkey
      (le_of_lt (show (0 : ℝ) < 3 / η by positivity))
    rw [← mul_assoc, hinv, one_mul] at hscale
    linarith [hmono, hscale]
  -- **(3)** the `m`-dependent law of large numbers, in probability
  have hLLN : ∀ m : ℕ, 0 < m → Tendsto (fun T : ℕ => (μ {ω | η / 3 ≤
      |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
          blockResid deltaFilter c ε m i ω ^ 2 - Mm m|}).toReal) atTop (𝓝 0) := by
    intro m hm
    have hae := ae_tendsto_avg_blockResid_sq hiid deltaFilter c hm
    have heq : (∫ ω, blockResid deltaFilter c ε m 0 ω ^ 2 ∂μ) = Mm m := by
      rw [hMmdef, integral_blockResid_sq_eq hwn _ _ m 0, sum_sq_cTrunc_deltaFilter c hm]
    rw [heq] at hae
    have hmf : ∀ T : ℕ, AEStronglyMeasurable (fun ω => (T : ℝ)⁻¹ *
        ∑ i ∈ Finset.range T, blockResid deltaFilter c ε m i ω ^ 2) μ := by
      intro T
      refine AEStronglyMeasurable.const_mul ?_ _
      exact (Finset.measurable_sum _ fun i _ =>
        ((measurable_blockResid hiid.measurable _ _ m i).pow_const 2)).aestronglyMeasurable
    have htim := MeasureTheory.tendstoInMeasure_of_tendsto_ae (g := fun _ : Ω => Mm m) hmf
      (by filter_upwards [hae] with ω hω using hω)
    have hz := htim (ENNReal.ofReal (η / 3)) (ENNReal.ofReal_pos.2 (by linarith))
    have hset : ∀ T : ℕ,
        {ω | ENNReal.ofReal (η / 3) ≤ edist ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
            blockResid deltaFilter c ε m i ω ^ 2) (Mm m)}
        = {ω | η / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
            blockResid deltaFilter c ε m i ω ^ 2 - Mm m|} := by
      intro T
      ext ω
      simp only [Set.mem_setOf_eq, edist_dist, Real.dist_eq,
        ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
    have hz2 : Tendsto (fun T : ℕ => (μ {ω | ENNReal.ofReal (η / 3) ≤
        edist ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
          blockResid deltaFilter c ε m i ω ^ 2) (Mm m)}).toReal) atTop (𝓝 0) := by
      simpa using! (ENNReal.tendsto_toReal (by simp)).comp hz
    exact hz2.congr fun T => congrArg ENNReal.toReal (congrArg μ (hset T))
  -- **(4)** the deterministic limits
  have htlT : Tendsto tl atTop (𝓝 0) := by rw [htldef]; exact tendsto_tail_zero hc
  have hMmT : Tendsto Mm atTop (𝓝 (σ2 * ∑' n : ℕ, c n ^ 2)) := by
    rw [hMmdef]
    exact (hsqsum.hasSum.tendsto_sum_nat).const_mul σ2
  -- **(5)** assembly
  refine Metric.tendsto_atTop.2 fun ζ hζ => ?_
  obtain ⟨m, hm1, hmb, hmM⟩ : ∃ m : ℕ, 0 < m ∧
      3 / η * (tl m * Real.sqrt σ2 * G) < ζ / 3 ∧
      |Mm m - σ2 * ∑' n : ℕ, c n ^ 2| < η / 3 := by
    have e1 : ∀ᶠ m : ℕ in atTop, 3 / η * (tl m * Real.sqrt σ2 * G) < ζ / 3 := by
      have h0 : Tendsto (fun m : ℕ => 3 / η * (tl m * Real.sqrt σ2 * G)) atTop (𝓝 0) := by
        simpa using ((htlT.mul_const (Real.sqrt σ2)).mul_const G).const_mul (3 / η)
      exact h0.eventually (gt_mem_nhds (by linarith))
    have e2 : ∀ᶠ m : ℕ in atTop, |Mm m - σ2 * ∑' n : ℕ, c n ^ 2| < η / 3 := by
      have h1 : Tendsto (fun m : ℕ => Mm m - σ2 * ∑' n : ℕ, c n ^ 2) atTop (𝓝 0) := by
        have := hMmT.sub (tendsto_const_nhds (x := σ2 * ∑' n : ℕ, c n ^ 2))
        rwa [sub_self] at this
      have h0 : Tendsto (fun m : ℕ => |Mm m - σ2 * ∑' n : ℕ, c n ^ 2|) atTop (𝓝 0) := by
        simpa using h1.abs
      exact h0.eventually (gt_mem_nhds (by linarith))
    obtain ⟨m, ⟨⟨h1, h2⟩, h3⟩⟩ := ((e1.and e2).and (eventually_gt_atTop 0)).exists
    exact ⟨m, h3, h1, h2⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (((hLLN m hm1).eventually (gt_mem_nhds (show (0 : ℝ) < ζ / 3 by linarith))).and
      (eventually_gt_atTop 0))
  refine ⟨N, fun T hT => ?_⟩
  obtain ⟨hT2, hT3⟩ := hN T hT
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  have hsub : {ω | η ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, W ((i : ℤ) + 1) ω ^ 2
        - σ2 * ∑' n : ℕ, c n ^ 2|}
      ⊆ {ω | η / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, W ((i : ℤ) + 1) ω ^ 2
            - (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
                blockResid deltaFilter c ε m i ω ^ 2|}
        ∪ {ω | η / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
              blockResid deltaFilter c ε m i ω ^ 2 - Mm m|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h3 := abs_lt.1 hmM
    have h4 := abs_lt.1 h1
    have h5 := abs_lt.1 h2
    rcases le_abs.1 hω with hcase | hcase <;> linarith
  calc (μ {ω | η ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, W ((i : ℤ) + 1) ω ^ 2
        - σ2 * ∑' n : ℕ, c n ^ 2|}).toReal
      ≤ (μ ({ω | η / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, W ((i : ℤ) + 1) ω ^ 2
            - (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
                blockResid deltaFilter c ε m i ω ^ 2|}
          ∪ {ω | η / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
                blockResid deltaFilter c ε m i ω ^ 2 - Mm m|})).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    _ ≤ (μ {ω | η / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, W ((i : ℤ) + 1) ω ^ 2
            - (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
                blockResid deltaFilter c ε m i ω ^ 2|}).toReal
        + (μ {ω | η / 3 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T,
              blockResid deltaFilter c ε m i ω ^ 2 - Mm m|}).toReal := by
        refine le_trans (ENNReal.toReal_mono (by finiteness) (measure_union_le _ _)) ?_
        exact le_of_eq (ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _))
    _ < ζ := by
        have := hmarkov m T hm1 hT3
        linarith

/-! ### The data's own second moment, and local stochastic equicontinuity

The oscillation estimate `abs_residSS_sub_le` prices the `θ`-dependence of `‖Π_T(θ)x‖²`
against the **random** factor `T⁻¹‖x‖²`, so the assembly needs that factor to be
`O_p(1)` with a *deterministic* bound — a bound "with probability `1 − κ`" would not
survive the `T → ∞` limit at a fixed radius `ρ`. It is: `T⁻¹‖x‖²` is the residual sum of
squares at the **zero parameter** `(0, 0)`, whose inversion filter is the identity, so
`armaResidualSS_tendstoInProb` applies verbatim. -/

private lemma arPoly_zero_fun {p : ℕ} : arPoly (fun _ : Fin p => (0 : ℝ)) = 1 := by
  simp [arPoly]

private lemma maPoly_zero_fun {q : ℕ} : maPoly (fun _ : Fin q => (0 : ℝ)) = 1 := by
  simp [maPoly]

private lemma invertible_zero_fun {p q : ℕ} :
    ARMAInvertibleParams (fun _ : Fin p => (0 : ℝ)) (fun _ : Fin q => (0 : ℝ)) := by
  constructor
  · intro z _
    rw [arPoly_zero_fun]
    simp
  · intro z _
    rw [maPoly_zero_fun]
    simp

private lemma armaPi_zero_fun {p q : ℕ} (n : ℕ) :
    armaPi (fun _ : Fin p => (0 : ℝ)) (fun _ : Fin q => (0 : ℝ)) n
      = if n = 0 then 1 else 0 := by
  rw [armaPi, arPoly_zero_fun, maPoly_zero_fun]
  simp [PowerSeries.coeff_one]

open Matrix in
/-- At the zero parameter the inversion matrix is the identity. -/
private lemma piMat_zero_fun {p q : ℕ} (T : ℕ) :
    piMat (fun _ : Fin p => (0 : ℝ)) (fun _ : Fin q => (0 : ℝ)) T = 1 := by
  ext i j
  show piK (fun _ : Fin p => (0 : ℝ)) (fun _ : Fin q => (0 : ℝ)) (i : ℕ) (j : ℕ)
      = (1 : Matrix (Fin T) (Fin T) ℝ) i j
  rw [piK, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos le_rfl, if_pos rfl, armaPi_zero_fun, if_pos (by omega)]
  · by_cases hle : (i : ℕ) ≤ (j : ℕ)
    · have hne : (j : ℕ) - (i : ℕ) ≠ 0 := by
        have : (i : ℕ) ≠ (j : ℕ) := fun hc => hij (Fin.ext hc)
        omega
      rw [if_pos hle, if_neg hij, armaPi_zero_fun, if_neg hne]
    · rw [if_neg hle, if_neg hij]

open Matrix in
/-- **`T⁻¹‖x‖²` is bounded in probability by a deterministic constant.** -/
lemma normSq_bounded_inProb [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t)) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun T : ℕ => (μ {ω | M ≤ (T : ℝ)⁻¹ *
        ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2}).toReal) atTop (𝓝 0) := by
  have hlim := armaResidualSS_tendstoInProb (b := fun _ : Fin p => (0 : ℝ))
    (a := fun _ : Fin q => (0 : ℝ)) h hiid hσ hB0 invertible_zero_fun hcausal hmeas
    (η' := 1) one_pos
  have hcv : (1 : ℝ) ≤ armaContrastVar b0 a0
      (fun _ : Fin p => (0 : ℝ)) (fun _ : Fin q => (0 : ℝ)) :=
    one_le_armaContrastVar hB0 invertible_zero_fun
  refine ⟨σ2 * armaContrastVar b0 a0 (fun _ : Fin p => (0 : ℝ))
      (fun _ : Fin q => (0 : ℝ)) + 1, by nlinarith, ?_⟩
  refine squeeze_zero' (Eventually.of_forall fun T => ENNReal.toReal_nonneg) ?_ hlim
  filter_upwards with T
  refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono fun ω hω => ?_)
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hq : ((piMat (fun _ : Fin p => (0 : ℝ)) (fun _ : Fin q => (0 : ℝ)) T *ᵥ
        fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
      (piMat (fun _ : Fin p => (0 : ℝ)) (fun _ : Fin q => (0 : ℝ)) T *ᵥ
        fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
      = ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2 := by
    rw [piMat_zero_fun, Matrix.one_mulVec]
    exact Finset.sum_congr rfl fun k _ => (sq _).symm
  rw [hq]
  rw [le_abs]
  left
  linarith

open Matrix in
/-- **Local stochastic equicontinuity of the profiled sum of squares** — ingredient (iii)
of `mle_consistent`, and the content of `MLEAsymptotics.armaProfileS_equicontinuous`.

The proof needs **no** `∂π/∂θ` and **no** difference modulus for the Gram tail. Writing
`Γ_T(θ)⁻¹ = Π_Tᵀ(1 + G_T)⁻¹Π_T` and using the two-sided sandwich
`‖Π_T(θ)x‖² − uᵀG_Tu ≤ S_T(θ) ≤ ‖Π_T(θ)x‖²` (`armaProfileS_sandwich`), the oscillation
splits into

* the **residual** part `T⁻¹|‖Π_T(θ)x‖² − ‖Π_T(θ₀)x‖²|`, which `abs_residSS_sub_le`
  bounds *pathwise* by `(Σ_n|π_n(θ) − π_n(θ₀)|)·(Σ|π(θ)| + Σ|π(θ₀)|)·T⁻¹‖x‖²`, the first
  factor being the `ℓ¹` modulus `exists_armaPi_l1_modulus` and the last one `O_p(1)` by
  `normSq_bounded_inProb`;
* the **Gram-tail** parts `T⁻¹uᵀG_T(θ)u` at `θ` and at `θ₀`, both `o_p(1)` *uniformly*
  over the compact `K ∪ {θ₀}` by `gramTail_uniform_tendstoInProb`.

The two shortcuts recorded as dead at `mle_consistent` really are dead — but they are
not needed: the uniform `o_p(1)` bound on the correction term replaces them. -/
theorem armaProfileS_locallyEquicontinuous [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))} (hK : IsCompact K)
    (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun T : ℕ => (μ {ω | ∃ ba ∈ K, dist ba (b0, a0) < ρ ∧
          η ≤ |armaProfileS ba.1 ba.2 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T
            - armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T|}).toReal)
        atTop (𝓝 0) := by
  classical
  have hK'c : IsCompact (insert ((b0, a0) : (Fin p → ℝ) × (Fin q → ℝ)) K) := hK.insert _
  have hK'B : ∀ ba ∈ insert ((b0, a0) : (Fin p → ℝ) × (Fin q → ℝ)) K,
      ARMAInvertibleParams ba.1 ba.2 := by
    intro ba hba
    rcases hba with rfl | hba
    · exact hB0
    · exact hKB ba hba
  have h0K' : ((b0, a0) : (Fin p → ℝ) × (Fin q → ℝ))
      ∈ insert ((b0, a0) : (Fin p → ℝ) × (Fin q → ℝ)) K := Set.mem_insert _ _
  have hKK' : K ⊆ insert ((b0, a0) : (Fin p → ℝ) × (Fin q → ℝ)) K := Set.subset_insert _ _
  obtain ⟨C, r, hC, hr0, hr1, hψK, hπK⟩ := exists_uniform_geometric_bound_arma hK'c hK'B
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hr1' : (0 : ℝ) < 1 - r := by linarith
  have hPpos : (0 : ℝ) < C / (1 - r) := by positivity
  have hPbd : ∀ ba ∈ insert ((b0, a0) : (Fin p → ℝ) × (Fin q → ℝ)) K,
      ∑' n : ℕ, |armaPi ba.1 ba.2 n| ≤ C / (1 - r) := by
    intro ba hba
    have hs : Summable fun n => |armaPi ba.1 ba.2 n| := summable_abs_armaPi (hK'B ba hba)
    have hg : Summable fun n : ℕ => C * r ^ n :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left C
    refine le_trans (hs.tsum_le_tsum (fun n => hπK ba hba n) hg) ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  obtain ⟨M, hM0, hMt⟩ := normSq_bounded_inProb h hiid hσ hB0 hcausal hmeas
  obtain ⟨ρ, hρ, hmod⟩ := exists_armaPi_l1_modulus hK'c hK'B
    (ε := η / (3 * (2 * (C / (1 - r))) * M)) (by positivity)
  refine ⟨ρ, hρ, ?_⟩
  have hG := gramTail_uniform_tendstoInProb (b0 := b0) (a0 := a0) h.whiteNoise hB0
    hcausal hmeas hK'c hK'B (η := η / 3) (by linarith)
  have hsum : Tendsto (fun T : ℕ =>
      (μ {ω | M ≤ (T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2}).toReal
      + (μ {ω | ∃ ba ∈ insert ((b0, a0) : (Fin p → ℝ) × (Fin q → ℝ)) K, η / 3 ≤
          (T : ℝ)⁻¹ *
            ((piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (gramTail ba.1 ba.2 T *ᵥ
                (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))}).toReal)
      atTop (𝓝 0) := by simpa using hMt.add hG
  refine squeeze_zero' (Eventually.of_forall fun T => ENNReal.toReal_nonneg) ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hTnn : (0 : ℝ) ≤ (T : ℝ)⁻¹ := by positivity
  have hsub : {ω | ∃ ba ∈ K, dist ba (b0, a0) < ρ ∧
        η ≤ |armaProfileS ba.1 ba.2 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T
          - armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T|}
      ⊆ {ω | M ≤ (T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2}
        ∪ {ω | ∃ ba ∈ insert ((b0, a0) : (Fin p → ℝ) × (Fin q → ℝ)) K, η / 3 ≤
            (T : ℝ)⁻¹ *
              ((piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                (gramTail ba.1 ba.2 T *ᵥ
                  (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    obtain ⟨ba, hba, hd, hbig⟩ := hω
    by_contra hcon
    push_neg at hcon
    obtain ⟨hE1, hE2⟩ := hcon
    have hQ0 : (0 : ℝ) ≤ (T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2 :=
      mul_nonneg hTnn (Finset.sum_nonneg fun k _ => sq_nonneg _)
    have hD1 := hE2 ba (hKK' hba)
    have hD0 := hE2 (b0, a0) h0K'
    obtain ⟨hup1, hlow1⟩ := armaProfileS_sandwich (hKB ba hba) T
      (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
    obtain ⟨hup0, hlow0⟩ := armaProfileS_sandwich hB0 T
      (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
    -- the residual-part oscillation, priced by the `ℓ¹` modulus
    have hosc := abs_residSS_sub_le (b1 := ba.1) (a1 := ba.2) (b2 := b0) (a2 := a0)
      (summable_abs_armaPi (hKB ba hba)) (summable_abs_armaPi hB0)
      (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
    have hDl1 : ∑' n : ℕ, |armaPi ba.1 ba.2 n - armaPi b0 a0 n|
        ≤ η / (3 * (2 * (C / (1 - r))) * M) :=
      le_of_lt (hmod ba (hKK' hba) (b0, a0) h0K' hd)
    have hDl0 : (0 : ℝ) ≤ ∑' n : ℕ, |armaPi ba.1 ba.2 n - armaPi b0 a0 n| :=
      tsum_nonneg fun n => abs_nonneg _
    have hPP : (∑' n : ℕ, |armaPi ba.1 ba.2 n|) + (∑' n : ℕ, |armaPi b0 a0 n|)
        ≤ 2 * (C / (1 - r)) := by
      have h1 := hPbd ba (hKK' hba)
      have h2 := hPbd (b0, a0) h0K'
      linarith
    have hPP0 : (0 : ℝ) ≤ (∑' n : ℕ, |armaPi ba.1 ba.2 n|) + (∑' n : ℕ, |armaPi b0 a0 n|) :=
      add_nonneg (tsum_nonneg fun n => abs_nonneg _) (tsum_nonneg fun n => abs_nonneg _)
    have hprod1 : (∑' n : ℕ, |armaPi ba.1 ba.2 n - armaPi b0 a0 n|) *
          ((∑' n : ℕ, |armaPi ba.1 ba.2 n|) + (∑' n : ℕ, |armaPi b0 a0 n|))
        ≤ η / (3 * (2 * (C / (1 - r))) * M) * (2 * (C / (1 - r))) :=
      mul_le_mul hDl1 hPP hPP0 (by positivity)
    have hprod2 : (∑' n : ℕ, |armaPi ba.1 ba.2 n - armaPi b0 a0 n|) *
          ((∑' n : ℕ, |armaPi ba.1 ba.2 n|) + (∑' n : ℕ, |armaPi b0 a0 n|)) *
          ((T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2)
        ≤ η / (3 * (2 * (C / (1 - r))) * M) * (2 * (C / (1 - r))) * M :=
      mul_le_mul hprod1 (le_of_lt hE1) hQ0 (by positivity)
    have hval : η / (3 * (2 * (C / (1 - r))) * M) * (2 * (C / (1 - r))) * M = η / 3 := by
      field_simp
    have hoscT : |(T : ℝ)⁻¹ * ((piMat ba.1 ba.2 T *ᵥ
          fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
            (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
        - (T : ℝ)⁻¹ * ((piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
            (piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))| ≤ η / 3 := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hTnn]
      have hstep := mul_le_mul_of_nonneg_left hosc hTnn
      calc (T : ℝ)⁻¹ * |(piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
            - (piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)|
          ≤ (T : ℝ)⁻¹ * ((∑' n : ℕ, |armaPi ba.1 ba.2 n - armaPi b0 a0 n|) *
              ((∑' n : ℕ, |armaPi ba.1 ba.2 n|) + (∑' n : ℕ, |armaPi b0 a0 n|)) *
              ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2) := hstep
        _ = (∑' n : ℕ, |armaPi ba.1 ba.2 n - armaPi b0 a0 n|) *
              ((∑' n : ℕ, |armaPi ba.1 ba.2 n|) + (∑' n : ℕ, |armaPi b0 a0 n|)) *
              ((T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2) := by ring
        _ ≤ η / 3 := by rw [← hval]; exact hprod2
    -- assemble: the sandwich turns the three pieces into a strict `< η`
    have hs1u := mul_le_mul_of_nonneg_left hup1 hTnn
    have hs1l := mul_le_mul_of_nonneg_left hlow1 hTnn
    have hs0u := mul_le_mul_of_nonneg_left hup0 hTnn
    have hs0l := mul_le_mul_of_nonneg_left hlow0 hTnn
    rw [mul_sub] at hs1l hs0l
    have habs := abs_le.1 hoscT
    rw [div_eq_inv_mul, div_eq_inv_mul] at hbig
    rcases le_abs.1 hbig with hcase | hcase <;> linarith [habs.1, habs.2]
  calc (μ {ω | ∃ ba ∈ K, dist ba (b0, a0) < ρ ∧
        η ≤ |armaProfileS ba.1 ba.2 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T
          - armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T|}).toReal
      ≤ (μ ({ω | M ≤ (T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2}
          ∪ {ω | ∃ ba ∈ insert ((b0, a0) : (Fin p → ℝ) × (Fin q → ℝ)) K, η / 3 ≤
              (T : ℝ)⁻¹ *
                ((piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                  (gramTail ba.1 ba.2 T *ᵥ
                    (piMat ba.1 ba.2 T *ᵥ
                      fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))})).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    _ ≤ _ := by
        refine le_trans (ENNReal.toReal_mono (by finiteness) (measure_union_le _ _)) ?_
        exact le_of_eq (ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _))

/-- **Pointwise LLN for the profiled criterion**: at each fixed `θ` in the constraint
set, `armaProfileCriterion θ (data_T) →p log(σ² · armaContrastVar θ₀ θ)` under the
true ARMA law. -/
theorem criterion_tendsto_contrast [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ => (μ {ω | δ ≤
        |armaProfileCriterion b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          - Real.log (σ2 * armaContrastVar b0 a0 b a)|}).toReal)
      atTop (𝓝 0) := by
  -- the limit is `≥ σ² > 0`, so `log` is continuous there (`one_le_armaContrastVar`)
  have hc : 0 < σ2 * armaContrastVar b0 a0 b a := by
    nlinarith [one_le_armaContrastVar hB0 hB]
  obtain ⟨η, hη, hlog⟩ : ∃ η > 0, ∀ y : ℝ, |y - σ2 * armaContrastVar b0 a0 b a| < η →
      |Real.log y - Real.log (σ2 * armaContrastVar b0 a0 b a)| < δ / 2 := by
    have hcont : ContinuousAt Real.log (σ2 * armaContrastVar b0 a0 b a) :=
      Real.continuousAt_log (ne_of_gt hc)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨η, hη, hball⟩ := hcont (δ / 2) (by linarith)
    refine ⟨η, hη, fun y hy => ?_⟩
    have := hball (x := y) (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this
  -- the log-determinant term is deterministic and vanishes
  have hLsmall : ∀ᶠ T : ℕ in atTop,
      |(T : ℝ)⁻¹ * Real.log (armaToeplitz b a T).det| < δ / 2 := by
    have hball := (logdet_armaToeplitz_vanishes hB).eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by linarith : (0 : ℝ) < δ / 2))
    filter_upwards [hball] with T hT
    simpa [Real.dist_eq] using hT
  refine squeeze_zero' (Eventually.of_forall fun T => ENNReal.toReal_nonneg) ?_
    (armaProfileS_tendstoInProb h hiid hσ hB0 hB hcausal hmeas hη)
  filter_upwards [hLsmall] with T hT
  refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono fun ω hω => ?_)
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  have h1 := hlog _ hcon
  have hsplit : armaProfileCriterion b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
        - Real.log (σ2 * armaContrastVar b0 a0 b a)
      = (Real.log ((T : ℝ)⁻¹ *
            armaProfileS b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
          - Real.log (σ2 * armaContrastVar b0 a0 b a))
        + (T : ℝ)⁻¹ * Real.log (armaToeplitz b a T).det := by
    rw [armaProfileCriterion, div_eq_inv_mul]
    ring
  rw [hsplit] at hω
  have habs := abs_add_le
    (Real.log ((T : ℝ)⁻¹ * armaProfileS b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
      - Real.log (σ2 * armaContrastVar b0 a0 b a))
    ((T : ℝ)⁻¹ * Real.log (armaToeplitz b a T).det)
  linarith

/-- At the truth the contrast variance is `1` (the coprimality-free half of
`armaContrastVar_eq_one_iff`: the composite filter is `π(θ₀) ∗ ψ(θ₀) = δ`). -/
private lemma armaContrastVar_self {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ) :
    armaContrastVar b0 a0 b0 a0 = 1 := by
  have hterm : ∀ n : ℕ,
      (∑ jk ∈ Finset.range (n + 1), armaPi b0 a0 jk * armaPsi b0 a0 (n - jk)) ^ 2
        = if n = 0 then (1 : ℝ) else 0 := by
    intro n
    rw [armaPi_conv_armaPsi]
    split_ifs <;> norm_num
  rw [armaContrastVar, tsum_congr hterm]
  simpa using tsum_ite_eq (0 : ℕ) (1 : ℝ)

/-- The arithmetic of the tolerance `e = σ² min(1, γ)/8`: three tolerances still fit
strictly inside the contrast gap, even after the `exp(e')` slack. -/
private lemma contrast_tolerance_pos {σ2 γ e : ℝ} (hσ : 0 < σ2) (hγ : 0 < γ)
    (he1 : e ≤ σ2 / 8) : 0 < σ2 * (1 + γ) - 3 * e := by
  nlinarith [mul_pos hσ hγ]

/-- ... and the same tolerance defeats the exponentiated criterion comparison. -/
private lemma contrast_tolerance_absurd {σ2 γ e : ℝ} (hσ : 0 < σ2) (hγ : 0 < γ)
    (he1 : e ≤ σ2 / 8) (he2 : e ≤ σ2 * γ / 8)
    (hfinal : σ2 * (1 + γ) - 3 * e ≤ (σ2 + e) * (1 + γ / 4)) : False := by
  have hprodγ : e * γ ≤ σ2 / 8 * γ := mul_le_mul_of_nonneg_right he1 (le_of_lt hγ)
  nlinarith [mul_pos hσ hγ]

-- The assembly re-unifies the full four-fold union of `Fin T`-indexed matrix events
-- several times, which exceeds the default heartbeat budget at `whnf`.
set_option maxHeartbeats 1600000 in
open Matrix in
/-- **Consistency of approximate MLE sequences** over a compact identifiable
neighbourhood: any measurable approximate-minimizer sequence of the profiled
criterion over a compact `K ⊆ 𝓑` containing `θ₀` in its interior converges in
probability to `θ₀`. -/
theorem mle_consistent [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))}
    -- USER-INPUT: compact identifiable search region containing the truth; Hannan §2
    (hK : IsCompact K) (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
    -- USER-INPUT: the search region consists of MINIMAL models. Added 2026-08-09 after
    -- the Lean witness `mle_consistent_not_identifiable` (`K = {(0,0), (1/2, −1/2)}`,
    -- on which the profiled criterion is constant, so a constant estimator sequence
    -- satisfies `hargmin` while staying a fixed distance from θ₀). Hannan 1973 §2.
    (hcopK : ∀ ba ∈ K, IsCoprime (arPoly ba.1) (maPoly ba.2))
    (hK0 : (b0, a0) ∈ K)
    (θ : (T : ℕ) → Ω → (Fin p → ℝ) × (Fin q → ℝ))
    (hθmeas : ∀ T, Measurable (θ T))
    {δT : ℕ → ℝ} (hδT : Tendsto δT atTop (𝓝 0)) (hδT0 : ∀ T, 0 ≤ δT T)
    -- USER-INPUT: approximate minimization over K; FY eq. (3.10) (argmax corrected)
    (hargmin : ∀ (T : ℕ) (ω : Ω), θ T ω ∈ K ∧ ∀ ba ∈ K,
      armaProfileCriterion (θ T ω).1 (θ T ω).2
          (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
        ≤ armaProfileCriterion ba.1 ba.2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) + δT T)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ =>
        (μ {ω | δ ≤ dist (θ T ω) (b0, a0)}).toReal) atTop (𝓝 0) := by
  -- **NO LONGER FALSE AS FROZEN.** The earlier refutation
  -- (`mle_consistent_not_identifiable`, kept above as documentation: `p = q = 1`,
  -- `b₀ = a₀ = 0`, `K = {(0,0), (1/2, −1/2)}`, on which the profiled criterion is
  -- *constant*, so the constant sequence `θ T ω = (1/2, −1/2)` satisfies `hargmin` with
  -- `δT = 0` while staying a fixed distance from `θ₀`) attacked the OLD signature, which
  -- did not constrain the working pairs in `K`. The repair it asked for —
  -- `hcopK : ∀ ba ∈ K, IsCoprime (arPoly ba.1) (maPoly ba.2)` — is now a hypothesis, and
  -- it excludes that witness. What remains is analytic debt, not falsity:
  --
  --   (i)   `criterion_tendsto_contrast` — PROVED here and now UNCONDITIONAL: steps (A),
  --         (B) and (C) of `armaProfileS_tendstoInProb` are all proved
  --         (`armaResidualSS_tendstoInProb` closed the last one), so this item is no
  --         longer debt;
  --   (ii)  the positive contrast gap `inf {K(θ) − K(θ₀) : θ ∈ K, dist θ θ₀ ≥ δ} > 0`
  --         — **PROVED** (2026-08-09) as `exists_contrast_gap` above. Its pointwise half
  --         was already available (`armaContrastVar_eq_one_iff` + `one_le_armaContrastVar`
  --         give `armaContrastVar θ₀ θ > 1` for `θ ∈ K`, `θ ≠ θ₀`); the missing
  --         continuity of `θ ↦ armaContrastVar θ₀ θ` is `continuousOn_armaContrastVar`,
  --         which is `continuousOn_tsum` over the brick's envelope `C⁴(n+1)²(r²)ⁿ` with
  --         each `contrastCoeff` continuous by `continuous_armaPi` (every `π_n` is a
  --         *polynomial* in the entries of `(b, a)`, by the recursion
  --         `maPoly_conv_armaPi`, whose leading coefficient `a(0)` is `1`);
  --   (iii) a stochastic-equicontinuity / finite-subcover step making the convergence in
  --         (i) uniform over `K` — **THE ONLY ITEM LEFT**. A finite subcover alone does
  --         not suffice: (i) is pointwise in `θ`, so interpolating between cover centres
  --         needs equicontinuity of `θ ↦ armaProfileCriterion θ (data_T)` in probability
  --         (`MLEAsymptotics.armaProfileS_equicontinuous`, still open).
  --
  --  **The geometric-bound brick is PROVED** (2026-08-09):
  --  `exists_uniform_geometric_bound_arma` (above) supplies, for any compact `K ⊆ 𝓑`,
  --  one pair `(C, r)` with `r < 1` bounding `|armaPi θ n|` *and* `|armaPsi θ n|` by
  --  `C rⁿ` uniformly in `θ ∈ K`. Its proof does what the 2026-08-08 note asked for:
  --  `exists_geometric_bound_armaPsi` really cannot be used as a black box (it is stated
  --  non-quantitatively), so its Cauchy estimate is redone carrying the radius and the
  --  sup-bound as parameters (`abs_armaPsi_le_of_disc_bounds`), and the compactness step
  --  is `exists_radius_nonvanishing` + `exists_disc_bounds`. **Amendment to that note's
  --  recipe**: no Lipschitz-in-`z` constant is needed to push the radius past `1`. The
  --  polar parametrisation `z = s · w` (`‖w‖ ≤ 1`, `s ∈ [1, 2]`) makes the zero set
  --  compact, so the *minimum of its `s`-coordinate* is already `> 1`.
  --
  --  **What (iii) still needs, and what is already in place.** The route is the pathwise
  --  θ-Lipschitz estimate, not an expectation bound:
  --  `T⁻¹|S_T(θ) − S_T(θ')| ≤ L(ρ) · Cst · T⁻¹‖x‖²` with `L(ρ) → 0` and `T⁻¹‖x‖²`
  --  bounded in probability. Write `Γ_T(θ)⁻¹ = Π_Tᵀ(1 + G_T)⁻¹Π_T` and split the
  --  difference into three terms,
  --      `[Π−Π′]ᵀ(1+G)⁻¹Π  +  Π′ᵀ[(1+G)⁻¹−(1+G′)⁻¹]Π  +  Π′ᵀ(1+G′)⁻¹[Π−Π′]`,
  --  using `(1+G)⁻¹ ⪯ 1` and the Schur test (`rowSum_kernel_le`) for the operator
  --  bounds. The first and third terms are controlled by the **`ℓ¹` modulus of `π`,
  --  which is PROVED here**: `exists_armaPi_l1_modulus`. The one genuinely missing
  --  ingredient is the matching modulus for the *Gram tail*, i.e. a bound
  --  `∑_j |G_T(θ)_{ij} − G_T(θ')_{ij}| ≤ L(ρ)` uniform in `T` and `i`; the entries are
  --  `G_{ij} = ∑_{m ≥ T} u_i(m)u_j(m)` with `|u_i(m)| ≤ C²(T−i)r^{m−i}`, so this is
  --  `trace_gramTail_le`'s estimate redone in difference form off the same modulus.
  --  (Recorded after checking that the shortcuts do **not** work: the pathwise bound
  --  `T⁻¹ uᵀG u ≤ K P² · T⁻¹‖x‖²` is `O_p(1)`, not `o_p(1)`, and the sandwich's constant
  --  factor `(1 + K)⁻¹ ⪯ (1+G)⁻¹` costs an `O(1)` additive `log(1+K)` in the criterion,
  --  so neither replaces the modulus. The `∂π/∂θ` companion the 2026-08-08 note asked
  --  for is **not** needed: a modulus of continuity suffices, and it is free from
  --  compactness of `K × K` plus the brick.)
  --
  --  **(iii) is now PROVED** (2026-08-09, wave `ts/s1b-arma-finish`), and the Gram-tail
  --  *difference* modulus asked for just above turned out to be **unnecessary**: the
  --  consistency argument only ever needs a one-sided (lower) bound on `S_T(θ)/T` over
  --  the far set, so it suffices that the correction term `T⁻¹uᵀG_T(θ)u` be `o_p(1)`
  --  *uniformly in `θ ∈ K`*, not that its `θ`-oscillation be small. The entrywise bound
  --  `|G_{ij}| ≤ (1−r²)⁻¹h_ih_j`, `h_i = C²(T−i)r^{T−i}`, factorises the quadratic form
  --  into the square of a **`θ`-free** envelope (`quadForm_gramTail_le_env`), whose `L²`
  --  norm is `O(1)` by Minkowski; one Markov inequality then covers the whole supremum
  --  at rate `O(1/T)` (`gramTail_uniform_tendstoInProb`). The residual part is priced by
  --  the `ℓ¹` modulus exactly as predicted (`abs_residSS_sub_le`), and the random factor
  --  `T⁻¹‖x‖²` it multiplies is `O_p(1)` with a **deterministic** bound because it is
  --  itself a residual sum of squares — the one at the zero parameter, whose inversion
  --  filter is the identity (`normSq_bounded_inProb`). The two "shortcuts" declared dead
  --  above really are dead; they are simply not on the route.
  classical
  -- **(ii)** the uniform contrast gap
  obtain ⟨γ, hγ, hgap⟩ := exists_contrast_gap hB0 hcop hK hKB hcopK hδ
  -- the locally uniform geometric brick over `K`
  obtain ⟨C, r, hC, hr0, hr1, hψK, hπK⟩ := exists_uniform_geometric_bound_arma hK hKB
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hr1' : (0 : ℝ) < 1 - r := by linarith
  have hPpos : (0 : ℝ) < C / (1 - r) := by positivity
  have hPbd : ∀ ba ∈ K, ∑' n : ℕ, |armaPi ba.1 ba.2 n| ≤ C / (1 - r) := by
    intro ba hba
    have hs : Summable fun n => |armaPi ba.1 ba.2 n| := summable_abs_armaPi (hKB ba hba)
    have hg : Summable fun n : ℕ => C * r ^ n :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left C
    refine le_trans (hs.tsum_le_tsum (fun n => hπK ba hba n) hg) ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  obtain ⟨M, hM0, hMt⟩ := normSq_bounded_inProb h hiid hσ hB0 hcausal hmeas
  -- the tolerance `e` (three of them fit inside the gap) and the log-scale slack `e'`
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = σ2 * min 1 γ / 8 := ⟨_, rfl⟩
  have hminpos : (0 : ℝ) < min 1 γ := lt_min one_pos hγ
  have he0 : 0 < e := by rw [hedef]; positivity
  have he1 : e ≤ σ2 / 8 := by
    rw [hedef]
    have : min 1 γ ≤ 1 := min_le_left _ _
    nlinarith
  have he2 : e ≤ σ2 * γ / 8 := by
    rw [hedef]
    have : min 1 γ ≤ γ := min_le_right _ _
    nlinarith
  obtain ⟨e', he'def⟩ : ∃ e' : ℝ, e' = Real.log (1 + γ / 4) := ⟨_, rfl⟩
  have he'0 : 0 < e' := by rw [he'def]; exact Real.log_pos (by linarith)
  have hexpe' : Real.exp e' = 1 + γ / 4 := by
    rw [he'def]; exact Real.exp_log (by linarith)
  -- the `ℓ¹` modulus at the scale the oscillation estimate needs
  obtain ⟨ρ, hρ, hmod⟩ := exists_armaPi_l1_modulus hK hKB
    (ε := e / (2 * (C / (1 - r)) * M)) (by positivity)
  -- a finite `ρ`-cover of the far set, by points of the far set
  have hfarc : IsCompact (K ∩ {ba : (Fin p → ℝ) × (Fin q → ℝ) | δ ≤ dist ba (b0, a0)}) :=
    hK.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  obtain ⟨s, hsK, hsfin, hscov⟩ := hfarc.elim_finite_subcover_image
    (c := fun ba : (Fin p → ℝ) × (Fin q → ℝ) => Metric.ball ba ρ)
    (fun ba _ => Metric.isOpen_ball)
    (fun ba hba => Set.mem_biUnion hba (Metric.mem_ball_self hρ))
  -- the four families of bad events
  have hzero := armaResidualSS_tendstoInProb (b := b0) (a := a0) h hiid hσ hB0 hB0
    hcausal hmeas he0
  have hG := gramTail_uniform_tendstoInProb (b0 := b0) (a0 := a0) h.whiteNoise hB0
    hcausal hmeas hK hKB he0
  have hcentre : ∀ ba ∈ hsfin.toFinset, Tendsto (fun T : ℕ => (μ {ω | e ≤
      |(T : ℝ)⁻¹ * ((piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
          (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
        - σ2 * armaContrastVar b0 a0 ba.1 ba.2|}).toReal) atTop (𝓝 0) := by
    intro ba hba
    exact armaResidualSS_tendstoInProb h hiid hσ hB0
      (hKB ba (hsK (hsfin.mem_toFinset.1 hba)).1) hcausal hmeas he0
  have hfinsum : Tendsto (fun T : ℕ => ∑ ba ∈ hsfin.toFinset, (μ {ω | e ≤
      |(T : ℝ)⁻¹ * ((piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
          (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
        - σ2 * armaContrastVar b0 a0 ba.1 ba.2|}).toReal) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum hsfin.toFinset hcentre
  have hsum := ((hzero.add hMt).add hG).add hfinsum
  rw [add_zero, add_zero, add_zero] at hsum
  -- the two deterministic eventual conditions
  have hlog : ∀ᶠ T : ℕ in atTop,
      |(T : ℝ)⁻¹ * Real.log (armaToeplitz b0 a0 T).det| < e' / 2 := by
    have hball := (logdet_armaToeplitz_vanishes hB0).eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by linarith : (0 : ℝ) < e' / 2))
    filter_upwards [hball] with T hTb
    simpa [Real.dist_eq] using hTb
  have hdel : ∀ᶠ T : ℕ in atTop, δT T < e' / 2 := by
    have hball := hδT.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by linarith : (0 : ℝ) < e' / 2))
    filter_upwards [hball] with T hTb
    have habs := abs_lt.1 (by simpa [Real.dist_eq] using hTb)
    linarith [habs.2]
  refine squeeze_zero' (Eventually.of_forall fun T => ENNReal.toReal_nonneg) ?_ hsum
  filter_upwards [eventually_ge_atTop 1, hlog, hdel] with T hT hlogT hdelT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hTnn : (0 : ℝ) ≤ (T : ℝ)⁻¹ := by positivity
  have hunion : ∀ A B : Set Ω, (μ (A ∪ B)).toReal ≤ (μ A).toReal + (μ B).toReal := by
    intro A B
    refine le_trans (ENNReal.toReal_mono (by finiteness) (measure_union_le A B)) ?_
    exact le_of_eq (ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _))
  have hsub : {ω | δ ≤ dist (θ T ω) (b0, a0)}
      ⊆ ({ω | e ≤ |(T : ℝ)⁻¹ *
            ((piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
            - σ2 * armaContrastVar b0 a0 b0 a0|}
        ∪ {ω | M ≤ (T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2}
        ∪ {ω | ∃ ba ∈ K, e ≤ (T : ℝ)⁻¹ *
            ((piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (gramTail ba.1 ba.2 T *ᵥ
                (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))})
        ∪ ⋃ ba ∈ hsfin.toFinset, {ω | e ≤
            |(T : ℝ)⁻¹ * ((piMat ba.1 ba.2 T *ᵥ
                fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
              - σ2 * armaContrastVar b0 a0 ba.1 ba.2|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨⟨hn1, hn2⟩, hn3⟩, hn4⟩ := hcon
    simp only [Set.mem_setOf_eq, not_le] at hn1 hn2
    simp only [Set.mem_setOf_eq, not_exists, not_and, not_le] at hn3
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hn4
    -- the estimate is in the far set, hence in some cover ball
    have hθK : θ T ω ∈ K := (hargmin T ω).1
    obtain ⟨bj, hbjs, hmem⟩ := Set.mem_iUnion₂.1 (hscov ⟨hθK, hω⟩)
    have hbjK : bj ∈ K := (hsK hbjs).1
    have hbjfar : δ ≤ dist bj (b0, a0) := (hsK hbjs).2
    have hdist : dist (θ T ω) bj < ρ := Metric.mem_ball.1 hmem
    have hn4' := hn4 bj (hsfin.mem_toFinset.2 hbjs)
    -- the residual-part oscillation between the estimate and the cover centre
    have hQ0 : (0 : ℝ) ≤ (T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2 :=
      mul_nonneg hTnn (Finset.sum_nonneg fun k _ => sq_nonneg _)
    have hosc := abs_residSS_sub_le (b1 := (θ T ω).1) (a1 := (θ T ω).2)
      (b2 := bj.1) (a2 := bj.2) (summable_abs_armaPi (hKB _ hθK))
      (summable_abs_armaPi (hKB bj hbjK)) (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
    have hDl1 : ∑' n : ℕ, |armaPi (θ T ω).1 (θ T ω).2 n - armaPi bj.1 bj.2 n|
        ≤ e / (2 * (C / (1 - r)) * M) := le_of_lt (hmod _ hθK bj hbjK hdist)
    have hDl0 : (0 : ℝ) ≤ ∑' n : ℕ, |armaPi (θ T ω).1 (θ T ω).2 n - armaPi bj.1 bj.2 n| :=
      tsum_nonneg fun n => abs_nonneg _
    have hPP : (∑' n : ℕ, |armaPi (θ T ω).1 (θ T ω).2 n|) + (∑' n : ℕ, |armaPi bj.1 bj.2 n|)
        ≤ 2 * (C / (1 - r)) := by
      have h1 := hPbd _ hθK
      have h2 := hPbd bj hbjK
      linarith
    have hPP0 : (0 : ℝ) ≤ (∑' n : ℕ, |armaPi (θ T ω).1 (θ T ω).2 n|)
        + (∑' n : ℕ, |armaPi bj.1 bj.2 n|) :=
      add_nonneg (tsum_nonneg fun n => abs_nonneg _) (tsum_nonneg fun n => abs_nonneg _)
    have hval : e / (2 * (C / (1 - r)) * M) * (2 * (C / (1 - r))) * M = e := by field_simp
    have hprod : (∑' n : ℕ, |armaPi (θ T ω).1 (θ T ω).2 n - armaPi bj.1 bj.2 n|) *
          ((∑' n : ℕ, |armaPi (θ T ω).1 (θ T ω).2 n|) + (∑' n : ℕ, |armaPi bj.1 bj.2 n|)) *
          ((T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2) ≤ e := by
      rw [← hval]
      exact mul_le_mul (mul_le_mul hDl1 hPP hPP0 (by positivity)) (le_of_lt hn2) hQ0
        (by positivity)
    have hoscT : |(T : ℝ)⁻¹ * ((piMat (θ T ω).1 (θ T ω).2 T *ᵥ
          fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
            (piMat (θ T ω).1 (θ T ω).2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
        - (T : ℝ)⁻¹ * ((piMat bj.1 bj.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
            (piMat bj.1 bj.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))| ≤ e := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hTnn]
      calc (T : ℝ)⁻¹ * |(piMat (θ T ω).1 (θ T ω).2 T *ᵥ
              fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (piMat (θ T ω).1 (θ T ω).2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
            - (piMat bj.1 bj.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (piMat bj.1 bj.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)|
          ≤ (T : ℝ)⁻¹ * ((∑' n : ℕ,
              |armaPi (θ T ω).1 (θ T ω).2 n - armaPi bj.1 bj.2 n|) *
              ((∑' n : ℕ, |armaPi (θ T ω).1 (θ T ω).2 n|)
                + (∑' n : ℕ, |armaPi bj.1 bj.2 n|)) *
              ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2) :=
            mul_le_mul_of_nonneg_left hosc hTnn
        _ = (∑' n : ℕ, |armaPi (θ T ω).1 (θ T ω).2 n - armaPi bj.1 bj.2 n|) *
              ((∑' n : ℕ, |armaPi (θ T ω).1 (θ T ω).2 n|)
                + (∑' n : ℕ, |armaPi bj.1 bj.2 n|)) *
              ((T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2) := by ring
        _ ≤ e := hprod
    -- the two sandwiches
    obtain ⟨hup1, hlow1⟩ := armaProfileS_sandwich (hKB _ hθK) T
      (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
    obtain ⟨hup0, hlow0⟩ := armaProfileS_sandwich hB0 T
      (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
    have hs1l := mul_le_mul_of_nonneg_left hlow1 hTnn
    have hs0u := mul_le_mul_of_nonneg_left hup0 hTnn
    have hs0l := mul_le_mul_of_nonneg_left hlow0 hTnn
    rw [mul_sub] at hs1l hs0l
    have hD1 := hn3 _ hθK
    have hD0 := hn3 (b0, a0) hK0
    have habsosc := abs_le.1 hoscT
    have habsj := abs_lt.1 hn4'
    have habs0 := abs_lt.1 hn1
    rw [armaContrastVar_self] at habs0
    simp only [mul_one] at habs0
    have hgapj : 1 + γ ≤ armaContrastVar b0 a0 bj.1 bj.2 := hgap bj hbjK hbjfar
    have hσcv : σ2 * (1 + γ) ≤ σ2 * armaContrastVar b0 a0 bj.1 bj.2 :=
      mul_le_mul_of_nonneg_left hgapj (le_of_lt hσ)
    -- the lower bound at the estimate and the upper bound at the truth
    have hApos : (0 : ℝ) < σ2 * (1 + γ) - 3 * e := contrast_tolerance_pos hσ hγ he1
    have hSlow : σ2 * (1 + γ) - 3 * e
        ≤ (T : ℝ)⁻¹ * armaProfileS (θ T ω).1 (θ T ω).2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) := by
      linarith [habsosc.1, habsj.1, hD1]
    have hS0pos : (0 : ℝ) < (T : ℝ)⁻¹ * armaProfileS b0 a0
        (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) := by
      linarith [habs0.1, hD0, he1]
    have hS0up : (T : ℝ)⁻¹ * armaProfileS b0 a0
        (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ≤ σ2 + e := by
      linarith [habs0.2]
    -- the criterion comparison
    have hlogdet1 := (log_det_armaToeplitz_bounds hC hr0 hr1 (hπK _ hθK) (hψK _ hθK)
      (hKB _ hθK) T).1
    have hcrit1 : Real.log (σ2 * (1 + γ) - 3 * e)
        ≤ armaProfileCriterion (θ T ω).1 (θ T ω).2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) := by
      rw [armaProfileCriterion, div_eq_inv_mul]
      have hmono := Real.log_le_log hApos hSlow
      have hnn := mul_nonneg hTnn hlogdet1
      linarith
    have hcrit0 : armaProfileCriterion b0 a0
        (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ≤ Real.log (σ2 + e) + e' / 2 := by
      rw [armaProfileCriterion, div_eq_inv_mul]
      have hmono := Real.log_le_log hS0pos hS0up
      have habsl := abs_lt.1 hlogT
      linarith [habsl.2]
    have hcmp := (hargmin T ω).2 (b0, a0) hK0
    have hchain : Real.log (σ2 * (1 + γ) - 3 * e) ≤ Real.log (σ2 + e) + e' := by
      linarith
    have hfinal : σ2 * (1 + γ) - 3 * e ≤ (σ2 + e) * (1 + γ / 4) := by
      have h1 : Real.exp (Real.log (σ2 * (1 + γ) - 3 * e))
          ≤ Real.exp (Real.log (σ2 + e) + e') := Real.exp_le_exp.2 hchain
      rw [Real.exp_log hApos, Real.exp_add, Real.exp_log (by linarith : (0 : ℝ) < σ2 + e),
        hexpe'] at h1
      exact h1
    exact contrast_tolerance_absurd hσ hγ he1 he2 hfinal
  calc (μ {ω | δ ≤ dist (θ T ω) (b0, a0)}).toReal
      ≤ (μ (({ω | e ≤ |(T : ℝ)⁻¹ *
            ((piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
            - σ2 * armaContrastVar b0 a0 b0 a0|}
        ∪ {ω | M ≤ (T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2}
        ∪ {ω | ∃ ba ∈ K, e ≤ (T : ℝ)⁻¹ *
            ((piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
              (gramTail ba.1 ba.2 T *ᵥ
                (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))})
        ∪ ⋃ ba ∈ hsfin.toFinset, {ω | e ≤
            |(T : ℝ)⁻¹ * ((piMat ba.1 ba.2 T *ᵥ
                fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
              - σ2 * armaContrastVar b0 a0 ba.1 ba.2|})).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    _ ≤ _ := by
        have hbi : (μ (⋃ ba ∈ hsfin.toFinset, {ω | e ≤
            |(T : ℝ)⁻¹ * ((piMat ba.1 ba.2 T *ᵥ
                fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
              - σ2 * armaContrastVar b0 a0 ba.1 ba.2|})).toReal
            ≤ ∑ ba ∈ hsfin.toFinset, (μ {ω | e ≤
                |(T : ℝ)⁻¹ * ((piMat ba.1 ba.2 T *ᵥ
                    fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                    (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
                  - σ2 * armaContrastVar b0 a0 ba.1 ba.2|}).toReal := by
          refine le_trans (ENNReal.toReal_mono
            (ENNReal.sum_ne_top.2 fun ba _ => measure_ne_top μ _)
            (measure_biUnion_finset_le _ _)) ?_
          exact le_of_eq (ENNReal.toReal_sum fun ba _ => measure_ne_top μ _)
        have h1 := hunion (({ω | e ≤ |(T : ℝ)⁻¹ *
              ((piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                (piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
              - σ2 * armaContrastVar b0 a0 b0 a0|}
          ∪ {ω | M ≤ (T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2})
          ∪ {ω | ∃ ba ∈ K, e ≤ (T : ℝ)⁻¹ *
              ((piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                (gramTail ba.1 ba.2 T *ᵥ
                  (piMat ba.1 ba.2 T *ᵥ
                    fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))})
          (⋃ ba ∈ hsfin.toFinset, {ω | e ≤
              |(T : ℝ)⁻¹ * ((piMat ba.1 ba.2 T *ᵥ
                  fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                  (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
                - σ2 * armaContrastVar b0 a0 ba.1 ba.2|})
        have h2 := hunion ({ω | e ≤ |(T : ℝ)⁻¹ *
              ((piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                (piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
              - σ2 * armaContrastVar b0 a0 b0 a0|}
          ∪ {ω | M ≤ (T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2})
          {ω | ∃ ba ∈ K, e ≤ (T : ℝ)⁻¹ *
              ((piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                (gramTail ba.1 ba.2 T *ᵥ
                  (piMat ba.1 ba.2 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)))}
        have h3 := hunion {ω | e ≤ |(T : ℝ)⁻¹ *
              ((piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ⬝ᵥ
                (piMat b0 a0 T *ᵥ fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
              - σ2 * armaContrastVar b0 a0 b0 a0|}
          {ω | M ≤ (T : ℝ)⁻¹ * ∑ k : Fin T, X (((k : ℕ) : ℤ) + 1) ω ^ 2}
        linarith

end Process

end StatLean.TimeSeries
