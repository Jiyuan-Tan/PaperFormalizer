module
public import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.DeterministicGuarantee
public import StatLean.ConcentrationInequalities.SubGaussian.Defs
public import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
public import StatLean.ConcentrationInequalities.SubGaussian.TailBounds
public import StatLean.ConcentrationInequalities.Maximal.FiniteMaximal
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Lasso support recovery under i.i.d. sub-Gaussian noise (Corollary 7.22)

This is the probabilistic specialization of the deterministic primal-dual witness guarantee
(Theorem 7.21). Consider the sparse linear model $y = X\theta^\* + w$ with $S$-sparse signal
$\theta^\*$ (support $S$, $|S| = s$, $s < d$), design $X \in \mathbb{R}^{n\times d}$, and noise
vector $w = (w_1,\dots,w_n)$ whose components are independent, zero-mean, and
$\sigma$-sub-Gaussian (variance proxy $\sigma^2$). Assume the lower-eigenvalue condition (A3),
$\tfrac1n \lVert X_S v\rVert_2^2 \ge c_{\min}\lVert v\rVert_2^2$ with $c_{\min} > 0$; the mutual
incoherence condition (A4) with parameter $\alpha < 1$; and the $C$-column-normalization
$\lVert X_j\rVert_2 \le C\sqrt n$ for every column $j$.

With the regularization choice (7.46)
$$\lambda_n \;=\; \frac{2C\sigma}{1-\alpha}\left(\sqrt{\tfrac{2\log(d-s)}{n}} + \delta\right),
\qquad \delta > 0,$$
the following hold with probability at least $1 - 4e^{-n\delta^2/2}$: the Lasso solution
$\hat\beta$ is unique, its support is contained in $S$ (no false inclusion), and it satisfies
the $\ell_\infty$ bound (7.47)
$$\bigl\lVert (\hat\beta - \theta^\*)_S \bigr\rVert_\infty
  \;\le\; \frac{\sigma}{\sqrt{c_{\min}}}\left(\sqrt{\tfrac{2\log s}{n}} + \delta\right)
        \;+\; \lVert (X_S^\top X_S / n)^{-1}\rVert_\infty \,\lambda_n .$$

*Alignment with the Lean statement / added hypotheses.* The Lean conclusion is the lower bound
$1 - 4e^{-n\delta^2/2}$ on the measure of the good event $\{\text{no false inclusion} \wedge
\ell_\infty\text{ bound}\}$; uniqueness on this event is supplied separately by
`lasso_support_recovery_unique`. Beyond the book hypotheses we add: $n > 0$ and $0 < s < d$ (so
that $\log s$ and $\log(d-s)$ are well defined), and $\sigma^2 > 0$ as a `LEAN-ONLY` simplifier
(the degenerate $\sigma^2 = 0$ case, where the noise is a.s. zero, is handled by a separate
trivial path). The constants match the book exactly.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019, Chapter 7 (Sparse linear models in high dimensions), §7.5
(Variable or model selection consistency), Corollary 7.22; regularization choice Eq (7.46),
$\ell_\infty$ bound Eq (7.47). The deterministic backbone is Theorem 7.21.

**Proof formalization notes.** Proof shell (mirrors `Lasso/RandomNoise.lean`): the two random
max-terms of (7.45)/(7.44) — $\lVert X_{S^c}^\top \Pi_{S^\perp}(X)\, w/n\rVert_\infty$ (max over
$d-s$ coordinates, each sub-Gaussian with proxy $\le C^2\sigma^2/n$ via projection contractivity
+ column normalization) and $\lVert (X_S^\top X_S/n)^{-1} X_S^\top\, w/n\rVert_\infty$ (max over
$s$ coordinates, each sub-Gaussian with proxy $\le \sigma^2/(c_{\min} n)$ via the inverse-Gram
operator bound) — are controlled by the maximal inequality `tail_max_le`; the $\lambda$ choice
(7.46) makes the regularization condition (7.44) hold, and a union bound gives $4e^{-n\delta^2/2}$.
On the good event, Theorem 7.21 (a)–(c) gives uniqueness, $\operatorname{supp}\subseteq S$, and
the bound (7.47).

Reuses: `IsSubGaussian`, `isSubGaussian_const_mul`, `HasSubgaussianMGF.sum_of_iIndepFun`,
`tail_max_le`, `projPerp_apply_norm_le`, `norm_gramInv_mulVec_le`, and Theorem 7.21.

**Bibliographic comments.** The primal-dual witness analysis of $\ell_1$-regularized least
squares originates with M. J. Wainwright, "Sharp thresholds for high-dimensional and noisy
sparsity recovery using $\ell_1$-constrained quadratic programming (Lasso)," *IEEE Transactions
on Information Theory*, vol. 55, no. 5, pp. 2183–2202, 2009. That paper introduced the mutual
incoherence and lower-eigenvalue conditions and established the support-recovery thresholds for
Gaussian designs; Corollary 7.22 of Wainwright (2019) restates the result under the
i.i.d. sub-Gaussian noise model with a fixed (deterministic) design satisfying the same
conditions.
-/

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.HighDimensionalStatistics
open StatLean.ConcentrationInequalities

variable {n d : ℕ}
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## Generic helper lemmas (private) -/

/-- Adjoint identity for `dotProduct` across rectangular matrices:
`x ⬝ᵥ (B v) = (Bᵀ x) ⬝ᵥ v`. -/
private lemma dotP_mulVec {α β : Type*} [Fintype α] [Fintype β]
    (B : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ) :
    x ⬝ᵥ B.mulVec y = (Bᵀ.mulVec x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose]

/-- A linear combination `∑ᵢ aᵢ wᵢ` of independent centered sub-Gaussian noise is sub-Gaussian
with any proxy `p` dominating `(∑ᵢ aᵢ²) σ²`. Mirrors `RandomNoise.colInner_isSubGaussian`. -/
private lemma linearComb_isSubGaussian
    {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (a : Fin n → ℝ) (w : Fin n → Ω → ℝ) (σ2 : ℝ≥0) (μ : Measure Ω)
    -- USER-INPUT: each noise component sub-Gaussian with proxy σ²; Wainwright Cor 7.22
    (hw_sg : ∀ i, IsSubGaussian (w i) σ2 μ)
    -- USER-INPUT: noise components jointly independent; Wainwright Cor 7.22
    (hw_indep : iIndepFun w μ)
    -- USER-INPUT: each noise component centered; Wainwright Cor 7.22
    (hw_zero : ∀ i, ∫ ω, w i ω ∂μ = 0)
    (p : ℝ≥0) (hp : (∑ i, (a i) ^ 2) * (σ2 : ℝ) ≤ (p : ℝ)) :
    IsSubGaussian (fun ω => ∑ i : Fin n, a i * w i ω) p μ := by
  have hw_int : ∀ i, Integrable (w i) μ := fun i => by
    have h := (isSubGaussian_iff.mp (hw_sg i)).integrable
    simp only [hw_zero i, sub_zero] at h; exact h
  have hY_sg : ∀ i : Fin n, HasSubgaussianMGF (fun ω => a i * w i ω)
      (⟨(a i) ^ 2, sq_nonneg _⟩ * σ2 : ℝ≥0) μ := by
    intro i
    have hsg_scaled := isSubGaussian_const_mul (hw_sg i) (a i)
    have hmean : ∫ ω, a i * w i ω ∂μ = 0 := by
      simp only [integral_const_mul, hw_zero i, mul_zero]
    simp only [isSubGaussian_iff, hmean, sub_zero] at hsg_scaled
    exact hsg_scaled
  have hY_indep : iIndepFun (fun i ω => a i * w i ω) μ :=
    hw_indep.comp (fun i x => a i * x) (fun i => measurable_const.mul measurable_id)
  have hsum_mg : HasSubgaussianMGF (fun ω => ∑ i : Fin n, a i * w i ω)
      (∑ i : Fin n, ⟨(a i) ^ 2, sq_nonneg _⟩ * σ2 : ℝ≥0) μ := by
    have := HasSubgaussianMGF.sum_of_iIndepFun hY_indep
      (c := fun i => ⟨(a i) ^ 2, sq_nonneg _⟩ * σ2) (s := Finset.univ)
      (fun i _ => hY_sg i)
    simpa using this
  have hproxy_le : (∑ i : Fin n, ⟨(a i) ^ 2, sq_nonneg _⟩ * σ2 : ℝ≥0) ≤ p := by
    rw [← NNReal.coe_le_coe, NNReal.coe_sum]
    change ∑ i : Fin n, (a i) ^ 2 * (σ2 : ℝ) ≤ p
    rw [← Finset.sum_mul]; exact hp
  have hsum_up : HasSubgaussianMGF (fun ω => ∑ i : Fin n, a i * w i ω) p μ :=
    ⟨hsum_mg.integrable_exp_mul, fun t => (hsum_mg.mgf_le t).trans (by
      apply Real.exp_le_exp.mpr; gcongr)⟩
  have hsum_mean : ∫ ω, ∑ i : Fin n, a i * w i ω ∂μ = 0 := by
    rw [integral_finset_sum Finset.univ (fun i _ => (hw_int i).const_mul (a i))]
    simp_rw [integral_const_mul, hw_zero, mul_zero, Finset.sum_const_zero]
  unfold IsSubGaussian
  simp only [hsum_mean, sub_zero]
  exact hsum_up

/-- Two-sided finite maximal tail over an arbitrary finite index, mirroring
`tail_max_le` but using `measure_abs_sub_integral_lt_le` and a general `Fintype`. -/
private lemma tail_max_abs_le'
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ι : Type*} [Fintype ι] [Nonempty ι] {μ : Measure Ω} {σ2 : ℝ≥0}
    {X : ι → Ω → ℝ}
    (hcenter : ∀ j, ∫ x, X j x ∂μ = 0)
    (hX : ∀ j, IsSubGaussian (X j) σ2 μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < ⨆ j, |X j ω|}
      ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * Real.exp (-t ^ 2 / (2 * σ2)))) := by
  have hbdd : ∀ ω, BddAbove (Set.range (fun j => |X j ω|)) := fun ω => Finite.bddAbove_range _
  have heq : {ω | t < ⨆ j, |X j ω|} = ⋃ j, {ω | t < |X j ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun h => (lt_ciSup_iff (hbdd ω)).mp h,
           fun ⟨j, hj⟩ => lt_of_lt_of_le hj (le_ciSup (hbdd ω) j)⟩
  rw [heq]
  calc μ (⋃ j, {ω | t < |X j ω|})
      ≤ ∑ j : ι, μ {ω | t < |X j ω|} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : ι, ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ2))) := by
          apply Finset.sum_le_sum; intro j _
          have hj := (hX j).measure_abs_sub_integral_lt_le ht
          simp only [hcenter j, sub_zero] at hj
          exact hj
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * Real.exp (-t ^ 2 / (2 * σ2)))) := by
          rw [Finset.sum_const, Finset.card_univ, ← ENNReal.ofReal_nsmul, nsmul_eq_mul]

/-- Real-analysis core of the union bound: with `t = √cmaxsq·(√(2 log m/n)+δ)` and proxy
`cmaxsq/n`, `m·exp(−t²/(2(cmaxsq/n))) ≤ exp(−nδ²/2)` (via `(a+b)² ≥ a²+b²`). -/
private lemma exp_tail_bound (m t cmaxsq n δ : ℝ)
    (hm : 1 ≤ m) (hn : 0 < n) (hδ : 0 < δ) (hden : 0 < cmaxsq)
    (ht : t = Real.sqrt cmaxsq * (Real.sqrt (2 * Real.log m / n) + δ)) :
    m * Real.exp (-t ^ 2 / (2 * (cmaxsq / n))) ≤ Real.exp (-n * δ ^ 2 / 2) := by
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hb_nn : 0 ≤ Real.sqrt (2 * Real.log m / n) := Real.sqrt_nonneg _
  have hbsq : (Real.sqrt (2 * Real.log m / n)) ^ 2 = 2 * Real.log m / n :=
    Real.sq_sqrt (by positivity)
  have hKsq : (Real.sqrt cmaxsq) ^ 2 = cmaxsq := Real.sq_sqrt hden.le
  have hnb : n * (Real.sqrt (2 * Real.log m / n)) ^ 2 = 2 * Real.log m := by
    rw [hbsq]; field_simp
  have ht2 : t ^ 2 / (2 * (cmaxsq / n))
      = n * (Real.sqrt (2 * Real.log m / n) + δ) ^ 2 / 2 := by
    rw [ht, mul_pow, hKsq]; field_simp
  have hexpand : n * (Real.sqrt (2 * Real.log m / n) + δ) ^ 2 / 2
      = Real.log m + n * (Real.sqrt (2 * Real.log m / n)) * δ + n * δ ^ 2 / 2 := by
    have h0 : n * (Real.sqrt (2 * Real.log m / n) + δ) ^ 2
        = n * (Real.sqrt (2 * Real.log m / n)) ^ 2
          + 2 * (n * (Real.sqrt (2 * Real.log m / n)) * δ) + n * δ ^ 2 := by ring
    rw [h0, hnb]; ring
  have key : Real.log m + n * δ ^ 2 / 2 ≤ t ^ 2 / (2 * (cmaxsq / n)) := by
    rw [ht2, hexpand]
    have hpos : 0 ≤ n * (Real.sqrt (2 * Real.log m / n)) * δ :=
      mul_nonneg (mul_nonneg hn.le hb_nn) hδ.le
    linarith
  calc m * Real.exp (-t ^ 2 / (2 * (cmaxsq / n)))
      = Real.exp (Real.log m) * Real.exp (-t ^ 2 / (2 * (cmaxsq / n))) := by
        rw [Real.exp_log hm0]
    _ = Real.exp (Real.log m + -t ^ 2 / (2 * (cmaxsq / n))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-n * δ ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        have hneg : -t ^ 2 / (2 * (cmaxsq / n)) = -(t ^ 2 / (2 * (cmaxsq / n))) := by ring
        rw [hneg]; linarith [key]

/-- `projPerp` is symmetric (reproved here from the public `gramInv_isHermitian`). -/
private lemma projPerp_transpose_eq {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2) :
    (projPerp X S)ᵀ = projPerp X S := by
  have hgit : (gramInv X S)ᵀ = gramInv X S := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact gramInv_isHermitian X S hn hcmin hcoer
  unfold projPerp
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, hgit, ← Matrix.mul_assoc]

/-- `(XₛᵀXₛ/n)⁻¹` acts as `n · (XₛᵀXₛ)⁻¹` on vectors. -/
private lemma gramInvNorm_mulVec_eq {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2)
    (v : {x // x ∈ S} → ℝ) :
    (gramInvNorm X S).mulVec v = (n : ℝ) • (gramInv X S).mulVec v := by
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hunit := gram_isUnit_det X S hn hcmin hcoer
  have hggi : gram X S * gramInv X S = 1 := by
    rw [gramInv]; exact Matrix.mul_nonsing_inv _ hunit
  have hrec : gramInvNorm X S = (n : ℝ) • gramInv X S := by
    unfold gramInvNorm
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hggi, one_div_mul_cancel hne, one_smul]
  rw [hrec, Matrix.smul_mulVec]

/-- Squared ℓ² norm of a `toLp` vector is the sum of squared coordinates. -/
private lemma norm_toLp_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ l, (v l) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]

/-- **Corollary 7.22** (Wainwright §7.5): Lasso support recovery under i.i.d. sub-Gaussian
noise. With the regularization choice (7.46), with probability at least `1 − 4e^{−nδ²/2}` the
Lasso solution has support contained in `S` and satisfies the ℓ∞ error bound (7.47).

The noise components `w i : Ω → ℝ` assemble into the response `Y ω = X θ* + w(ω)`. The
conclusion is the high-probability event {no false inclusion ∧ ℓ∞ bound}; uniqueness (7.21a)
also holds on this event via `lasso_support_recovery_unique`. -/
theorem lasso_support_recovery_subgaussian
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : EuclideanSpace ℝ (Fin d))
    (S : Finset (Fin d))
    (w : Fin n → Ω → ℝ)
    (σ2 : ℝ≥0)
    (μ : Measure Ω)
    (lam α cmin C δ : ℝ)
    (βhat : Ω → EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: 0 < n; Wainwright §7.5
    (hn : 0 < n)
    -- USER-INPUT: 0 < |S| (nonempty support, for log s); Wainwright §7.5
    (hs : 0 < S.card)
    -- USER-INPUT: |S| < d (for log(d − s)); Wainwright §7.5
    (hsd : S.card < d)
    -- USER-INPUT: θ* supported on S; Wainwright §7.5 (S-sparse model)
    (hsupp : ∀ j ∉ S, θstar.ofLp j = 0)
    -- USER-INPUT: lower-eigenvalue condition (A3); Wainwright §7.5.1 (7.43a)
    (hA3 : LowerEigenvalue X S cmin)
    -- USER-INPUT: 0 < cmin; Wainwright §7.5.1 (7.43a)
    (hcmin : 0 < cmin)
    -- USER-INPUT: mutual incoherence (A4); Wainwright §7.5.1 (7.43b)
    (hA4 : MutualIncoherence X S α)
    -- USER-INPUT: 0 ≤ α; Wainwright §7.5.1
    (hα0 : 0 ≤ α)
    -- USER-INPUT: α < 1; Wainwright §7.5.1
    (hα1 : α < 1)
    -- USER-INPUT: C-column-normalization; Wainwright Cor 7.22
    (hcol : ColumnNormalized X C)
    -- USER-INPUT: noise components jointly independent; Wainwright Cor 7.22
    (hw_indep : iIndepFun w μ)
    -- USER-INPUT: each noise component sub-Gaussian with variance proxy σ²; Wainwright Cor 7.22
    (hw_sg : ∀ i, IsSubGaussian (w i) σ2 μ)
    -- USER-INPUT: each noise component centered; Wainwright Cor 7.22
    (hw_zero : ∀ i, ∫ ω, w i ω ∂μ = 0)
    -- USER-INPUT: 0 < δ; Wainwright Cor 7.22 (7.46)
    (hδ : 0 < δ)
    -- LEAN-ONLY: 0 < σ²; the σ² = 0 case (noise a.s. 0) holds by a separate trivial path
    (hσ2 : 0 < (σ2 : ℝ))
    -- USER-INPUT: regularization choice λₙ = (2Cσ/(1−α))(√(2log(d−s)/n) + δ); Wainwright (7.46)
    (hlam : lam = (2 * C * Real.sqrt σ2 / (1 - α)) *
      (Real.sqrt (2 * Real.log ((d : ℝ) - S.card) / n) + δ))
    -- USER-INPUT: β̂ ω minimises the Lasso for response Y ω = X θ* + w(ω); Wainwright Cor 7.22
    (hLasso : ∀ ω, IsLassoEstimator X
      (designMap X θstar + WithLp.toLp 2 (fun i => w i ω)) lam (βhat ω)) :
    ENNReal.ofReal (1 - 4 * Real.exp (-(n : ℝ) * δ ^ 2 / 2)) ≤
      μ {ω | (∀ j ∉ S, (βhat ω).ofLp j = 0) ∧
        linfNorm (restrict S (βhat ω - θstar)) ≤
          Real.sqrt σ2 / Real.sqrt cmin * (Real.sqrt (2 * Real.log (S.card) / n) + δ)
          + matLinftyNorm (gramInvNorm X S) * lam} := by
  classical
  haveI : IsProbabilityMeasure μ := hw_indep.isProbabilityMeasure
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2 := hA3
  have hw_int : ∀ i, Integrable (w i) μ := fun i => by
    have h := (isSubGaussian_iff.mp (hw_sg i)).integrable
    simp only [hw_zero i, sub_zero] at h; exact h
  haveI : Nonempty {x // x ∈ S} := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hs; exact ⟨⟨a, ha⟩⟩
  haveI : Nonempty {x // x ∈ Sᶜ} := by
    have hcpos : 0 < Sᶜ.card := by rw [Finset.card_compl, Fintype.card_fin]; omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcpos; exact ⟨⟨a, ha⟩⟩
  set noiseVec : Ω → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 (fun i => w i ω)
    with hnoise
  set m1 : ℝ := (d : ℝ) - (S.card : ℝ) with hm1def
  -- C > 0 : otherwise all columns vanish and (A3) fails.
  have hC_pos : 0 < C := by
    obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hs
    set eS : EuclideanSpace ℝ {x // x ∈ S} :=
      WithLp.toLp 2 (Pi.single (⟨i0, hi0⟩ : {x // x ∈ S}) (1 : ℝ)) with heS
    have heSofLp : eS.ofLp = Pi.single (⟨i0, hi0⟩ : {x // x ∈ S}) (1 : ℝ) :=
      WithLp.ofLp_toLp 2 _
    have hds : designSub X S eS = col X i0 := by
      apply WithLp.ofLp_injective 2
      funext l
      rw [designSub_apply, heSofLp, col, WithLp.ofLp_toLp]
      simp only [Matrix.mulVec, dotProduct, Xsub, Matrix.submatrix_apply, id_eq]
      rw [Finset.sum_eq_single (⟨i0, hi0⟩ : {x // x ∈ S})]
      · rw [Pi.single_eq_same, mul_one]
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have heSnorm : ‖eS‖ ^ 2 = 1 := by
      rw [heS, norm_toLp_sq, Finset.sum_eq_single (⟨i0, hi0⟩ : {x // x ∈ S})]
      · simp
      · intro l _ hl; rw [Pi.single_eq_of_ne hl]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    have hcle : ‖col X i0‖ ≤ C * Real.sqrt n := hcol i0
    have hcnn : (0 : ℝ) ≤ C * Real.sqrt n := le_trans (norm_nonneg _) hcle
    have hCnn : 0 ≤ C :=
      (mul_nonneg_iff_of_pos_right (Real.sqrt_pos.mpr hn_pos)).mp hcnn
    have hA3e := hcoer eS
    rw [hds, heSnorm, mul_one] at hA3e
    -- cmin ≤ (1/n) ‖col X i0‖² ≤ (1/n)(C√n)² = C²
    have hsqn : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn_pos.le
    have hcle2 : ‖col X i0‖ ^ 2 ≤ C ^ 2 * n := by
      have h := mul_le_mul hcle hcle (norm_nonneg _) hcnn
      rw [← pow_two, ← pow_two, mul_pow, hsqn] at h
      exact h
    have hcmin_le : cmin ≤ C ^ 2 := by
      have hstep : (1 / (n : ℝ)) * ‖col X i0‖ ^ 2 ≤ (1 / (n : ℝ)) * (C ^ 2 * n) :=
        mul_le_mul_of_nonneg_left hcle2 (by positivity)
      rw [show (1 / (n : ℝ)) * (C ^ 2 * n) = C ^ 2 by field_simp] at hstep
      exact le_trans hA3e hstep
    rcases hCnn.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hcmin_le; norm_num at hcmin_le; linarith [hcmin]
  -- proxies
  set p1 : ℝ≥0 := Real.toNNReal (C ^ 2 * (σ2 : ℝ) / n) with hp1
  set p2 : ℝ≥0 := Real.toNNReal ((σ2 : ℝ) / (cmin * n)) with hp2
  have hp1c : (p1 : ℝ) = C ^ 2 * (σ2 : ℝ) / n := Real.coe_toNNReal _ (by positivity)
  have hp2c : (p2 : ℝ) = (σ2 : ℝ) / (cmin * n) :=
    Real.coe_toNNReal _ (div_nonneg (NNReal.coe_nonneg σ2) (by positivity))
  -- the two coordinate families
  set Yp : {x // x ∈ Sᶜ} → Ω → ℝ :=
    fun j ω => ((Xsub X Sᶜ)ᵀ.mulVec ((1 / (n : ℝ)) • (projPerp X S).mulVec (noiseVec ω).ofLp)) j
    with hYp
  set Yg : {x // x ∈ S} → Ω → ℝ :=
    fun i ω => ((gramInvNorm X S).mulVec ((1 / (n : ℝ)) • (Xsub X S)ᵀ.mulVec (noiseVec ω).ofLp)) i
    with hYg
  -- pointwise linear-functional identities
  have hproj_id : ∀ (j : {x // x ∈ Sᶜ}) (ω : Ω),
      Yp j ω = ∑ l, ((1 / (n : ℝ)) * ((projPerp X S).mulVec (col X j.val).ofLp) l) * w l ω := by
    intro j ω
    change ((Xsub X Sᶜ)ᵀ.mulVec ((1 / (n : ℝ)) • (projPerp X S).mulVec (noiseVec ω).ofLp)) j = _
    have hw' : (noiseVec ω).ofLp = (fun i => w i ω) := WithLp.ofLp_toLp 2 _
    rw [Xsub_transpose_mulVec_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hw']
    calc ∑ k, X k j.val * (1 / (n : ℝ) * ((projPerp X S).mulVec (fun i => w i ω)) k)
        = (1 / (n : ℝ)) * ((col X j.val).ofLp ⬝ᵥ (projPerp X S).mulVec (fun i => w i ω)) := by
          rw [show (col X j.val).ofLp ⬝ᵥ (projPerp X S).mulVec (fun i => w i ω)
                = ∑ k, (col X j.val).ofLp k * ((projPerp X S).mulVec (fun i => w i ω)) k from rfl,
              Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [col, WithLp.ofLp_toLp]; ring
      _ = (1 / (n : ℝ)) * (((projPerp X S)ᵀ.mulVec (col X j.val).ofLp) ⬝ᵥ (fun i => w i ω)) := by
          rw [dotP_mulVec]
      _ = (1 / (n : ℝ)) * (((projPerp X S).mulVec (col X j.val).ofLp) ⬝ᵥ (fun i => w i ω)) := by
          rw [projPerp_transpose_eq X S hn hcmin hcoer]
      _ = ∑ l, 1 / (n : ℝ) * ((projPerp X S).mulVec (col X j.val).ofLp) l * w l ω := by
          rw [show ((projPerp X S).mulVec (col X j.val).ofLp) ⬝ᵥ (fun i => w i ω)
                = ∑ l, ((projPerp X S).mulVec (col X j.val).ofLp) l * w l ω from rfl,
              Finset.mul_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_); ring
  have hgram_id : ∀ (i : {x // x ∈ S}) (ω : Ω),
      Yg i ω = ∑ l, ((Xsub X S).mulVec ((gramInv X S).mulVec (Pi.single i (1 : ℝ)))) l * w l ω := by
    intro i ω
    change ((gramInvNorm X S).mulVec ((1 / (n : ℝ)) • (Xsub X S)ᵀ.mulVec (noiseVec ω).ofLp)) i = _
    have hw' : (noiseVec ω).ofLp = (fun k => w k ω) := WithLp.ofLp_toLp 2 _
    have hsymGI : (gramInv X S)ᵀ = gramInv X S := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact gramInv_isHermitian X S hn hcmin hcoer
    rw [gramInvNorm_mulVec_eq X S hn hcmin hcoer, Pi.smul_apply, smul_eq_mul,
        Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hw']
    rw [← mul_assoc, show (n : ℝ) * (1 / (n : ℝ)) = 1 by field_simp, one_mul]
    rw [show ((gramInv X S).mulVec ((Xsub X S)ᵀ.mulVec (fun k => w k ω))) i
          = (Pi.single i (1 : ℝ)) ⬝ᵥ ((gramInv X S).mulVec ((Xsub X S)ᵀ.mulVec (fun k => w k ω)))
        from by rw [single_dotProduct, one_mul]]
    rw [dotP_mulVec, hsymGI, dotP_mulVec, Matrix.transpose_transpose]
    rfl
  -- sub-Gaussianity of each coordinate
  have hproj_sg : ∀ j, IsSubGaussian (fun ω => Yp j ω) p1 μ := by
    intro j
    rw [show (fun ω => Yp j ω)
        = (fun ω => ∑ l, ((1 / (n : ℝ)) * ((projPerp X S).mulVec (col X j.val).ofLp) l) * w l ω)
      from funext (hproj_id j)]
    refine linearComb_isSubGaussian
      (fun l => (1 / (n : ℝ)) * ((projPerp X S).mulVec (col X j.val).ofLp) l)
      w σ2 μ hw_sg hw_indep hw_zero p1 ?_
    set vproj : Fin n → ℝ := (projPerp X S).mulVec (col X j.val).ofLp with hvproj
    have hPv : ‖(WithLp.toLp 2 vproj : EuclideanSpace ℝ (Fin n))‖ ≤ C * Real.sqrt n :=
      le_trans (projPerp_apply_norm_le X S hn hcmin hcoer (col X j.val)) (hcol j.val)
    have hsumsq : ∑ l, ((1 / (n : ℝ)) * vproj l) ^ 2 ≤ C ^ 2 / n := by
      have h1 : ∑ l, ((1 / (n : ℝ)) * vproj l) ^ 2 = (1 / (n : ℝ)) ^ 2 * ∑ l, (vproj l) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l _ => ?_); ring
      rw [h1, ← norm_toLp_sq]
      have hPv2 : ‖(WithLp.toLp 2 vproj : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ (C * Real.sqrt n) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hPv 2
      calc (1 / (n : ℝ)) ^ 2 * ‖(WithLp.toLp 2 vproj : EuclideanSpace ℝ (Fin n))‖ ^ 2
          ≤ (1 / (n : ℝ)) ^ 2 * (C * Real.sqrt n) ^ 2 :=
            mul_le_mul_of_nonneg_left hPv2 (by positivity)
        _ = C ^ 2 / n := by rw [mul_pow, Real.sq_sqrt hn_pos.le]; field_simp
    rw [hp1c]
    calc (∑ l, ((1 / (n : ℝ)) * vproj l) ^ 2) * (σ2 : ℝ)
        ≤ (C ^ 2 / n) * (σ2 : ℝ) := mul_le_mul_of_nonneg_right hsumsq (NNReal.coe_nonneg σ2)
      _ = C ^ 2 * (σ2 : ℝ) / n := by ring
  have hgram_sg : ∀ i, IsSubGaussian (fun ω => Yg i ω) p2 μ := by
    intro i
    rw [show (fun ω => Yg i ω)
        = (fun ω => ∑ l, ((Xsub X S).mulVec ((gramInv X S).mulVec (Pi.single i (1 : ℝ)))) l * w l ω)
      from funext (hgram_id i)]
    refine linearComb_isSubGaussian
      (fun l => ((Xsub X S).mulVec ((gramInv X S).mulVec (Pi.single i (1 : ℝ)))) l)
      w σ2 μ hw_sg hw_indep hw_zero p2 ?_
    set eVec : EuclideanSpace ℝ {x // x ∈ S} := WithLp.toLp 2 (Pi.single i (1 : ℝ)) with heVec
    have heVofLp : eVec.ofLp = Pi.single i (1 : ℝ) := WithLp.ofLp_toLp 2 _
    set gVec : EuclideanSpace ℝ {x // x ∈ S} :=
      WithLp.toLp 2 ((gramInv X S).mulVec eVec.ofLp) with hgVec
    have hgVofLp : gVec.ofLp = (gramInv X S).mulVec eVec.ofLp := WithLp.ofLp_toLp 2 _
    have hsymGI : (gramInv X S)ᵀ = gramInv X S := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact gramInv_isHermitian X S hn hcmin hcoer
    have hggi : gram X S * gramInv X S = 1 := by
      rw [gramInv]; exact Matrix.mul_nonsing_inv _ (gram_isUnit_det X S hn hcmin hcoer)
    set g : {x // x ∈ S} → ℝ := (gramInv X S).mulVec (Pi.single i (1 : ℝ)) with hg_def
    have hXtX : (Xsub X S)ᵀ.mulVec ((Xsub X S).mulVec g) = (gram X S).mulVec g := by
      unfold gram; rw [Matrix.mulVec_mulVec]
    have hgg : (gram X S).mulVec g = Pi.single i (1 : ℝ) := by
      rw [hg_def, Matrix.mulVec_mulVec, hggi, Matrix.one_mulVec]
    have hexp : ∑ l, (((Xsub X S).mulVec g) l) ^ 2
        = eVec.ofLp ⬝ᵥ (gramInv X S).mulVec eVec.ofLp := by
      have hsq_dot : ∑ l, (((Xsub X S).mulVec g) l) ^ 2
          = ((Xsub X S).mulVec g) ⬝ᵥ ((Xsub X S).mulVec g) := by
        simp only [pow_two]; rfl
      rw [hsq_dot, dotP_mulVec, hXtX, hgg, heVofLp, hg_def]
    have heInner : ⟪eVec, gVec⟫_ℝ = eVec.ofLp ⬝ᵥ (gramInv X S).mulVec eVec.ofLp := by
      simp only [PiLp.inner_apply]
      change gVec.ofLp ⬝ᵥ eVec.ofLp = eVec.ofLp ⬝ᵥ (gramInv X S).mulVec eVec.ofLp
      rw [hgVofLp, dotProduct_comm]
    have hCS : eVec.ofLp ⬝ᵥ (gramInv X S).mulVec eVec.ofLp ≤ ‖eVec‖ * ‖gVec‖ := by
      rw [← heInner]; exact real_inner_le_norm eVec gVec
    have hgVnorm : ‖gVec‖ ≤ (1 / (cmin * n)) * ‖eVec‖ :=
      norm_gramInv_mulVec_le X S hn hcmin hcoer eVec
    have heVnorm : ‖eVec‖ = 1 := by
      have heVsq : ‖eVec‖ ^ 2 = 1 := by
        rw [heVec, norm_toLp_sq, Finset.sum_eq_single i]
        · simp
        · intro l _ hl; rw [Pi.single_eq_of_ne hl]; ring
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [← Real.sqrt_sq (norm_nonneg eVec), heVsq, Real.sqrt_one]
    have hsumsq : ∑ l, (((Xsub X S).mulVec g) l) ^ 2 ≤ 1 / (cmin * n) := by
      rw [hexp]
      have h1 : ‖eVec‖ * ‖gVec‖ ≤ 1 / (cmin * n) := by
        rw [heVnorm, one_mul]
        calc ‖gVec‖ ≤ (1 / (cmin * n)) * ‖eVec‖ := hgVnorm
          _ = 1 / (cmin * n) := by rw [heVnorm, mul_one]
      exact le_trans hCS h1
    rw [hp2c]
    calc (∑ l, (((Xsub X S).mulVec g) l) ^ 2) * (σ2 : ℝ)
        ≤ (1 / (cmin * n)) * (σ2 : ℝ) := mul_le_mul_of_nonneg_right hsumsq (NNReal.coe_nonneg σ2)
      _ = (σ2 : ℝ) / (cmin * n) := by ring
  -- centeredness of each coordinate
  have hproj_center : ∀ j, ∫ ω, Yp j ω ∂μ = 0 := by
    intro j
    simp_rw [hproj_id j]
    rw [integral_finset_sum Finset.univ (fun l _ => (hw_int l).const_mul _)]
    simp_rw [integral_const_mul, hw_zero, mul_zero, Finset.sum_const_zero]
  have hgram_center : ∀ i, ∫ ω, Yg i ω ∂μ = 0 := by
    intro i
    simp_rw [hgram_id i]
    rw [integral_finset_sum Finset.univ (fun l _ => (hw_int l).const_mul _)]
    simp_rw [integral_const_mul, hw_zero, mul_zero, Finset.sum_const_zero]
  -- thresholds
  set t1 : ℝ := C * Real.sqrt σ2 * (Real.sqrt (2 * Real.log m1 / n) + δ) with ht1def
  set t' : ℝ := Real.sqrt σ2 / Real.sqrt cmin * (Real.sqrt (2 * Real.log (S.card) / n) + δ)
    with ht'def
  have hm1le : 1 ≤ m1 := by
    have : (S.card : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hsd
    rw [hm1def]; linarith
  have hms : 1 ≤ (S.card : ℝ) := by exact_mod_cast hs
  have ht1nn : 0 ≤ t1 := by
    rw [ht1def]; have := Real.sqrt_nonneg (2 * Real.log m1 / n); positivity
  have htpnn : 0 ≤ t' := by
    rw [ht'def]; have := Real.sqrt_nonneg (2 * Real.log (S.card) / n); positivity
  have h1a : 0 < 1 - α := by linarith
  -- regularization: lam = (2/(1-α)) t1 > 0
  have hlampos : 0 < lam := by
    have hsq : 0 < Real.sqrt σ2 := Real.sqrt_pos.mpr hσ2
    have hfac : 0 < Real.sqrt (2 * Real.log m1 / n) + δ := by
      have := Real.sqrt_nonneg (2 * Real.log m1 / n); linarith
    rw [hlam]
    exact mul_pos (div_pos (mul_pos (mul_pos two_pos hC_pos) hsq) h1a) hfac
  have hlam_t1 : lam = (2 / (1 - α)) * t1 := by rw [hlam, ht1def]; field_simp
  -- tail bound for the regularization event (G1)
  have htail1 : μ {ω | lam ≥ (2 / (1 - α)) * projNoiseLinf X S (noiseVec ω)}ᶜ
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * δ ^ 2 / 2)) := by
    have hsub1 : {ω | lam ≥ (2 / (1 - α)) * projNoiseLinf X S (noiseVec ω)}ᶜ
        ⊆ {ω | t1 < ⨆ j, |Yp j ω|} := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, ge_iff_le, not_le] at hω
      have h2a : 0 < 2 / (1 - α) := by positivity
      rw [hlam_t1] at hω
      exact lt_of_mul_lt_mul_left hω h2a.le
    refine le_trans (measure_mono hsub1) ?_
    have hbound := tail_max_abs_le' (μ := μ) (σ2 := p1) (X := Yp) hproj_center hproj_sg ht1nn
    refine le_trans hbound (ENNReal.ofReal_le_ofReal ?_)
    have hcard : (Fintype.card {x // x ∈ Sᶜ} : ℝ) = m1 := by
      rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hm1def,
        Nat.cast_sub hsd.le]
    rw [hcard]
    have ht1form : t1 = Real.sqrt (C ^ 2 * (σ2 : ℝ)) * (Real.sqrt (2 * Real.log m1 / n) + δ) := by
      rw [ht1def, Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC_pos.le]
    have hetb := exp_tail_bound m1 t1 (C ^ 2 * (σ2 : ℝ)) n δ hm1le hn_pos hδ
      (by positivity) ht1form
    rw [hp1c]
    rw [show m1 * (2 * Real.exp (-t1 ^ 2 / (2 * (C ^ 2 * (σ2 : ℝ) / n))))
        = 2 * (m1 * Real.exp (-t1 ^ 2 / (2 * (C ^ 2 * (σ2 : ℝ) / n)))) by ring]
    linarith [hetb]
  -- tail bound for the ℓ∞ event (G2)
  have htail2 : μ {ω | (⨆ i, |Yg i ω|) ≤ t'}ᶜ
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * δ ^ 2 / 2)) := by
    have hsub2 : {ω | (⨆ i, |Yg i ω|) ≤ t'}ᶜ ⊆ {ω | t' < ⨆ i, |Yg i ω|} := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
      exact hω
    refine le_trans (measure_mono hsub2) ?_
    have hbound := tail_max_abs_le' (μ := μ) (σ2 := p2) (X := Yg) hgram_center hgram_sg htpnn
    refine le_trans hbound (ENNReal.ofReal_le_ofReal ?_)
    have hcard : (Fintype.card {x // x ∈ S} : ℝ) = (S.card : ℝ) := by rw [Fintype.card_coe]
    rw [hcard]
    have htpform : t' = Real.sqrt ((σ2 : ℝ) / cmin)
        * (Real.sqrt (2 * Real.log (S.card) / n) + δ) := by
      rw [ht'def, Real.sqrt_div (NNReal.coe_nonneg σ2)]
    have hetb := exp_tail_bound (S.card : ℝ) t' ((σ2 : ℝ) / cmin) n δ hms hn_pos hδ
      (by positivity) htpform
    rw [hp2c, show (σ2 : ℝ) / (cmin * n) = (σ2 : ℝ) / cmin / n from (div_div _ _ _).symm]
    rw [show (S.card : ℝ) * (2 * Real.exp (-t' ^ 2 / (2 * ((σ2 : ℝ) / cmin / n))))
        = 2 * ((S.card : ℝ) * Real.exp (-t' ^ 2 / (2 * ((σ2 : ℝ) / cmin / n)))) by ring]
    linarith [hetb]
  -- union bound: μ((G1 ∩ G2)ᶜ) ≤ 4 exp(-nδ²/2)
  set G1 : Set Ω := {ω | lam ≥ (2 / (1 - α)) * projNoiseLinf X S (noiseVec ω)} with hG1
  set G2 : Set Ω := {ω | (⨆ i, |Yg i ω|) ≤ t'} with hG2
  have hexp_nn : (0 : ℝ) ≤ 2 * Real.exp (-(n : ℝ) * δ ^ 2 / 2) := by positivity
  have hunion : μ (G1 ∩ G2)ᶜ ≤ ENNReal.ofReal (4 * Real.exp (-(n : ℝ) * δ ^ 2 / 2)) := by
    rw [Set.compl_inter]
    refine le_trans (measure_union_le _ _) ?_
    refine le_trans (add_le_add htail1 htail2) ?_
    rw [← ENNReal.ofReal_add hexp_nn hexp_nn]
    apply ENNReal.ofReal_le_ofReal
    linarith [Real.exp_pos (-(n : ℝ) * δ ^ 2 / 2)]
  have hexp4_nn : (0 : ℝ) ≤ 4 * Real.exp (-(n : ℝ) * δ ^ 2 / 2) := by positivity
  have hmeas : ENNReal.ofReal (1 - 4 * Real.exp (-(n : ℝ) * δ ^ 2 / 2)) ≤ μ (G1 ∩ G2) := by
    have hcover : (1 : ℝ≥0∞)
        ≤ μ (G1 ∩ G2) + ENNReal.ofReal (4 * Real.exp (-(n : ℝ) * δ ^ 2 / 2)) := by
      calc (1 : ℝ≥0∞) = μ Set.univ := (measure_univ).symm
        _ = μ ((G1 ∩ G2) ∪ (G1 ∩ G2)ᶜ) := by rw [Set.union_compl_self]
        _ ≤ μ (G1 ∩ G2) + μ (G1 ∩ G2)ᶜ := measure_union_le _ _
        _ ≤ μ (G1 ∩ G2) + ENNReal.ofReal (4 * Real.exp (-(n : ℝ) * δ ^ 2 / 2)) :=
            add_le_add le_rfl hunion
    rw [ENNReal.ofReal_sub 1 hexp4_nn, ENNReal.ofReal_one]
    exact tsub_le_iff_right.mpr hcover
  -- final: G1 ∩ G2 ⊆ good event
  have hsub : G1 ∩ G2 ⊆ {ω | (∀ j ∉ S, (βhat ω).ofLp j = 0) ∧
      linfNorm (restrict S (βhat ω - θstar)) ≤
        t' + matLinftyNorm (gramInvNorm X S) * lam} := by
    intro ω hω
    obtain ⟨hP1, hP2⟩ := hω
    refine ⟨?_, ?_⟩
    · exact lasso_support_recovery_no_false_inclusion X S θstar (noiseVec ω) lam α cmin
        hn hsupp hA3 hcmin hA4 hα0 hα1 hlampos hP1 (βhat ω) (hLasso ω)
    · have hlinf := lasso_support_recovery_linf X S θstar (noiseVec ω) lam α cmin
        hn hsupp hA3 hcmin hA4 hα0 hα1 hlampos hP1 (βhat ω) (hLasso ω)
      refine le_trans hlinf ?_
      unfold supportRecoveryBound
      gcongr
      exact hP2
  exact le_trans hmeas (measure_mono hsub)

end StatLean.HighDimensionalStatistics
