module
public import StatLean.Minimaxity.Fano.FanoLowerBound
public import StatLean.Minimaxity.ForMathlib.GaussianMaxEntropy
public import StatLean.Minimaxity.ForMathlib.GaussianKLMulti
public import StatLean.Minimaxity.ForMathlib.Packing.SpherePacking
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.RowCol

@[expose] public section

/-!
# Minimax lower bound for principal component analysis in the spiked covariance model

In the spiked covariance model the observations are $n$ i.i.d. draws
$Z \sim \mathcal{N}(0,\, I_d + \nu\, \theta^* (\theta^*)^\top)$, where the leading eigenvector
$\theta^*$ lies on the unit sphere $\mathbb{S}^{d-1}$ and $\nu > 0$ is the signal strength. Estimating
$\theta^*$ under squared Euclidean loss $\|\cdot\|_2^2$, the minimax risk is bounded below by
$$
\inf_{\widehat\theta}\ \sup_{\theta^* \in \mathbb{S}^{d-1}}\
  \mathbb{E}\,\bigl\| \widehat\theta - \theta^* \bigr\|_2^2
\ \gtrsim\ \min\!\left\{ \frac{1 + \nu}{\nu^2}\cdot\frac{d}{n},\ 1 \right\}.
$$
The bound is proved by Fano's method, combining the Gaussian maximum-entropy bound on the mutual
information with a $1/2$-packing of the unit sphere of cardinality $2^{\Omega(d)}$.

Two deviations from the book are made explicit in the formalized statement:
* The leading multiplicative constant is loosened from the book's $1/128$ to $1/2048$, the value
  provable from the $\log M \ge d/10$ sphere-packing brick (`exists_sphere_packing`, Example 5.8).
* A dimension floor $d \ge 40$ is imposed: Fano's method requires $e^{\Omega(d)}$ hypotheses, so the
  small-$d$ regime (handled in the book by a separate two-point bound) is excluded; Example 15.19 is
  stated as a large-$d$ rate.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.4, Example 15.19
(the spiked covariance / PCA lower bound), using Lemma 15.17 (Gaussian maximum-entropy
mutual-information bound) and Example 5.8 ($1/2$-packing of the unit sphere).

**Proof formalization notes.** The chain mirrors the book's Fano argument:
* **Spiked-covariance matrix algebra.** `spiked_posDef`, `spiked_det`, and `spiked_inv` establish
  that $S = I + \nu u u^\top$ is positive definite with $\det S = 1 + \nu$ and Sherman–Morrison
  inverse $S^{-1} = I - \tfrac{\nu}{1+\nu} u u^\top$ for a unit vector $u$.
* **Pairwise KL divergence.** `trace_spiked_inv_mul`, `klDiv_spiked`, and `klDiv_pca_pair` compute the
  single-sample KL between two spiked Gaussians as
  $\tfrac12\,\nu^2 (1 - \langle u_a, u_b\rangle^2)/(1+\nu)$ — the equal determinants cancel the
  log-det terms — and tensorize it to the $n$-fold product law.
* **Sphere packing and tilting.** `pca_fano_config` builds the $2\delta$-separated hypothesis family
  by tilting a $1/2$-packing of $\mathbb{S}^{m-1}$ ($d = m+1$) into the sphere via
  $\theta_a = (s, \delta\, w_a)$ with $s^2 + \delta^2 = 1$, choosing
  $\delta^2 \asymp \min\{(1+\nu)/\nu^2 \cdot d/n,\, 1\}$; the dot-product/norm bridge lemmas
  (`euclid_self_dot`, `euclid_dot_le`, `tilt_dot`) convert between Euclidean norms and coordinate dot
  products.
* **Mutual-information bound.** The per-pair KL is bounded by $2 n \nu^2 \delta^2/(1+\nu)$, averaged
  via `mutualInformation_le_avg_pairwise_kl`, and combined with $\log M \ge m/10$ so that Fano's
  $(1 - \cdot)$ factor stays $\ge 1/2$.
* **Assembly.** `pca_minimax_rate` feeds the configuration into `minimax_fano_lower_bound`.

**Bibliographic comments.** The spiked covariance model originates with I. M. Johnstone, *On the
distribution of the largest eigenvalue in principal components analysis*, Annals of Statistics 29
(2001), 295–327, which introduced $\mathcal{N}(0, I + \nu\, \theta\theta^\top)$ as a stylized model
for high-dimensional PCA. The minimax lower bound for estimating the leading eigenvector (and, more
generally, the principal subspace) over the unit sphere is due to V. Q. Vu and J. Lei, *Minimax
sparse principal subspace estimation in high dimensions*, Annals of Statistics 41 (2013), no. 6,
2905–2947 (arXiv:1211.0373); the dense (non-sparse) special case of their Theorem 3.1 gives exactly
the rate $\min\{(1+\nu)/\nu^2 \cdot d/n,\, 1\}$ formalized here, and Wainwright's Example 15.19 is a
streamlined exposition of that argument. Related minimax analyses of the spiked model include
A. Birnbaum, I. M. Johnstone, B. Nadler, and D. Paul, *Minimax bounds for sparse PCA with noisy
high-dimensional data*, Annals of Statistics 41 (2013), 1055–1084, and T. T. Cai, Z. Ma, and Y. Wu,
*Sparse PCA: optimal rates and adaptive estimation*, Annals of Statistics 41 (2013), 3074–3110.
-/

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal

namespace StatLean.Minimaxity

/-! ### Rank-one spiked covariance: positive-definiteness, determinant, inverse

For a unit vector `u` (`u ⬝ᵥ u = 1`) and `ν > 0`, the spiked covariance `S = I + ν u uᵀ` is
positive definite with `det S = 1 + ν` and (Sherman–Morrison) `S⁻¹ = I − ν/(1+ν) · u uᵀ`. These are
the matrix-algebra inputs to the single-sample Gaussian KL formula below. -/

/-- The spiked covariance `I + ν u uᵀ` is positive definite (`ν ≥ 0`). -/
private lemma spiked_posDef {d : ℕ} (u : Fin d → ℝ) {ν : ℝ} (hν : 0 ≤ ν) :
    (1 + ν • Matrix.vecMulVec u u).PosDef := by
  refine Matrix.PosDef.one.add_posSemidef ?_
  have h : (Matrix.vecMulVec u u).PosSemidef := by
    have := Matrix.posSemidef_vecMulVec_self_star (R := ℝ) u
    simpa using this
  exact h.smul hν

/-- `det (I + ν u uᵀ) = 1 + ν` for a unit vector `u`. -/
private lemma spiked_det {d : ℕ} (u : Fin d → ℝ) (hu : u ⬝ᵥ u = 1) (ν : ℝ) :
    (1 + ν • Matrix.vecMulVec u u).det = 1 + ν := by
  have hsv : ν • Matrix.vecMulVec u u = Matrix.vecMulVec (ν • u) u := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsv, Matrix.vecMulVec_eq (Fin 1), Matrix.det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, hu, smul_eq_mul, mul_one]

/-- Sherman–Morrison inverse `(I + ν u uᵀ)⁻¹ = I − ν/(1+ν) · u uᵀ` for a unit vector `u`,
`ν > 0`. -/
private lemma spiked_inv {d : ℕ} (u : Fin d → ℝ) (hu : u ⬝ᵥ u = 1) {ν : ℝ} (hν : 0 < ν) :
    (1 + ν • Matrix.vecMulVec u u)⁻¹
      = 1 - (ν / (1 + ν)) • Matrix.vecMulVec u u := by
  have hν1 : (1 : ℝ) + ν ≠ 0 := by positivity
  set c := ν / (1 + ν) with hc_def
  set Q := Matrix.vecMulVec u u with hQ_def
  have hQQ : Q * Q = Q := by rw [hQ_def, Matrix.vecMulVec_mul_vecMulVec, hu, one_smul]
  have hsub : (1 : Matrix (Fin d) (Fin d) ℝ) - c • Q = 1 + (-c) • Q := by
    rw [neg_smul, ← sub_eq_add_neg]
  refine Matrix.inv_eq_right_inv ?_
  have hscal : ν + (-c) + ν * (-c) = 0 := by rw [hc_def]; field_simp; ring
  have e : (1 : Matrix (Fin d) (Fin d) ℝ) + ν • Q + ((-c) • Q + (ν * (-c)) • Q)
      = 1 + (ν + (-c) + ν * (-c)) • Q := by
    rw [add_smul, add_smul]; abel
  rw [hsub, mul_add, mul_one, add_mul, one_mul, smul_mul_smul_comm, hQQ, e,
    hscal, zero_smul, add_zero]

/-- The trace `tr(S_b⁻¹ S_a) = d + ν²(1 − ⟨u_a,u_b⟩²)/(1+ν)` for spiked covariances `S = I + ν u uᵀ`
on unit vectors. The Sherman–Morrison inverse collapses the product to a rank-one correction. -/
private lemma trace_spiked_inv_mul {d : ℕ} (ua ub : Fin d → ℝ)
    (hua : ua ⬝ᵥ ua = 1) (hub : ub ⬝ᵥ ub = 1) {ν : ℝ} (hν : 0 < ν) :
    ((1 + ν • Matrix.vecMulVec ub ub)⁻¹ * (1 + ν • Matrix.vecMulVec ua ua)).trace
      = (d : ℝ) + ν ^ 2 * (1 - (ua ⬝ᵥ ub) ^ 2) / (1 + ν) := by
  have hν1 : (1 : ℝ) + ν ≠ 0 := by positivity
  set c := ν / (1 + ν) with hc_def
  rw [spiked_inv ub hub hν]
  set Qa := Matrix.vecMulVec ua ua with hQa
  set Qb := Matrix.vecMulVec ub ub with hQb
  have htr1 : (1 : Matrix (Fin d) (Fin d) ℝ).trace = (d : ℝ) := by
    rw [Matrix.trace_one, Fintype.card_fin]
  have htrQa : Qa.trace = 1 := by rw [hQa, Matrix.trace_vecMulVec, hua]
  have htrQb : Qb.trace = 1 := by rw [hQb, Matrix.trace_vecMulVec, hub]
  have htrQbQa : (Qb * Qa).trace = (ua ⬝ᵥ ub) ^ 2 := by
    rw [hQb, hQa, Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul,
      smul_eq_mul, dotProduct_comm ub ua]
    ring
  have hmat : (1 - c • Qb) * (1 + ν • Qa)
      = 1 + ν • Qa - (c • Qb + (c * ν) • (Qb * Qa)) := by
    rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm]
  rw [hmat]
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, htr1, htrQa, htrQb, htrQbQa,
    smul_eq_mul]
  rw [hc_def]
  field_simp
  ring

/-- **Single-sample pairwise KL** between two spiked-covariance Gaussians on unit vectors `u_a,u_b`:
`D(𝒩(0, I+ν u_a u_aᵀ) ‖ 𝒩(0, I+ν u_b u_bᵀ)) = ½ · ν²(1 − ⟨u_a,u_b⟩²)/(1+ν)`. The equal determinants
`1+ν` cancel the log-det terms, leaving the trace term computed in `trace_spiked_inv_mul`. -/
private lemma klDiv_spiked {d : ℕ} (ua ub : Fin d → ℝ)
    (hua : ua ⬝ᵥ ua = 1) (hub : ub ⬝ᵥ ub = 1) {ν : ℝ} (hν : 0 < ν) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (1 + ν • Matrix.vecMulVec ua ua))
          (multivariateGaussian 0 (1 + ν • Matrix.vecMulVec ub ub))
      = ENNReal.ofReal (2⁻¹ * (ν ^ 2 * (1 - (ua ⬝ᵥ ub) ^ 2) / (1 + ν))) := by
  rw [klDiv_multivariateGaussian_zero _ _ (spiked_posDef ua hν.le) (spiked_posDef ub hν.le),
    spiked_det ua hua ν, spiked_det ub hub ν, trace_spiked_inv_mul ua ub hua hub hν]
  congr 1
  ring

/-- **`n`-fold pairwise KL** between the product spiked-covariance laws (one sample per coordinate):
`D(P_a ‖ P_b) = n · ½ ν²(1 − ⟨u_a,u_b⟩²)/(1+ν)`, by i.i.d. tensorization. -/
private lemma klDiv_pca_pair {n d : ℕ} (ua ub : Fin d → ℝ)
    (hua : ua ⬝ᵥ ua = 1) (hub : ub ⬝ᵥ ub = 1) {ν : ℝ} (hν : 0 < ν) :
    klDiv (Measure.pi fun _ : Fin n =>
            multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (1 + ν • Matrix.vecMulVec ua ua))
          (Measure.pi fun _ : Fin n =>
            multivariateGaussian 0 (1 + ν • Matrix.vecMulVec ub ub))
      = ENNReal.ofReal ((n : ℝ) * (2⁻¹ * (ν ^ 2 * (1 - (ua ⬝ᵥ ub) ^ 2) / (1 + ν)))) := by
  haveI : IsProbabilityMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (1 + ν • Matrix.vecMulVec ua ua)) := by
    haveI := isGaussian_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin d)))
      (S := 1 + ν • Matrix.vecMulVec ua ua); infer_instance
  haveI : IsProbabilityMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (1 + ν • Matrix.vecMulVec ub ub)) := by
    haveI := isGaussian_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin d)))
      (S := 1 + ν • Matrix.vecMulVec ub ub); infer_instance
  rw [klDiv_pi_eq_nsmul, klDiv_spiked ua ub hua hub hν, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]

/-! ### Euclidean dot products vs. norms (coercion bridge) -/

/-- The self dot product of (the coordinate function of) a Euclidean vector is its squared norm. -/
private lemma euclid_self_dot {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    (x : Fin k → ℝ) ⬝ᵥ (x : Fin k → ℝ) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct, sq]

/-- Cauchy–Schwarz for the coordinate dot product of two Euclidean vectors. -/
private lemma euclid_dot_le {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    |(x : Fin k → ℝ) ⬝ᵥ (y : Fin k → ℝ)| ≤ ‖x‖ * ‖y‖ := by
  set a : Fin k → ℝ := (x : Fin k → ℝ) with ha
  set b : Fin k → ℝ := (y : Fin k → ℝ) with hb
  have h2 : (a ⬝ᵥ b) ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    calc (a ⬝ᵥ b) ^ 2 = (∑ i, a i * b i) ^ 2 := by rw [dotProduct]
      _ ≤ (∑ i, a i ^ 2) * ∑ i, b i ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (a ⬝ᵥ a) * (b ⬝ᵥ b) := by simp only [dotProduct, sq]
      _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by rw [ha, hb, euclid_self_dot, euclid_self_dot]
      _ = (‖x‖ * ‖y‖) ^ 2 := by ring
  calc |a ⬝ᵥ b| = Real.sqrt ((a ⬝ᵥ b) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((‖x‖ * ‖y‖) ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖x‖ * ‖y‖ := Real.sqrt_sq (by positivity)

/-- Dot product of two `e₀`-tilted vectors `Fin.cons s (δ • w)`:
`⟨cons s (δw₁), cons s (δw₂)⟩ = s² + δ²⟨w₁,w₂⟩`. The orthogonal head coordinate `s` contributes
`s²`, the tail scales by `δ²`. -/
private lemma tilt_dot {m : ℕ} (s δ : ℝ) (w₁ w₂ : EuclideanSpace ℝ (Fin m)) :
    (Fin.cons s (fun j => δ * (w₁ : Fin m → ℝ) j) : Fin (m + 1) → ℝ) ⬝ᵥ
      (Fin.cons s (fun j => δ * (w₂ : Fin m → ℝ) j))
      = s ^ 2 + δ ^ 2 * ((w₁ : Fin m → ℝ) ⬝ᵥ (w₂ : Fin m → ℝ)) := by
  simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [Finset.mul_sum]
  congr 1
  · rw [sq]
  · apply Finset.sum_congr rfl
    intro j _
    rw [sq]; ring

/-- **Crux: Fano configuration for the spiked-covariance PCA lower bound.** A `1/2`-packing of the
unit sphere (Wainwright Example 5.8, `exists_sphere_packing`) of cardinality `2^Ω(d)` gives a
`2δ`-separated family with `δ² ≍ min{(1+ν)/ν²·d/n, 1}`; the Gaussian maximum-entropy bound on the
mutual information (Lemma 15.17) keeps `I(Z;J) ≤ ½ log M`, so Fano's `(1 − ·)` factor is `≥ ½`. -/
private lemma pca_fano_config {n d : ℕ} (hn : 1 ≤ n)
    -- LEAN-ONLY: d ≥ d₀ — Fano's method needs e^{Ω(d)} hypotheses; the small-d regime is a separate
    -- two-point bound. Wainwright Ex 15.19 is a large-d rate.
    (hd0 : 40 ≤ d) (ν : ℝ) (hν : 0 < ν)
    (P : Kernel (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (Fin n → EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel P]
    (hP : ∀ θ, P θ = Measure.pi fun _ : Fin n =>
      multivariateGaussian 0 (1 + ν • vecMulVec (θ : Fin d → ℝ) (θ : Fin d → ℝ))) :
    ∃ (M : ℕ) (_ : NeZero M) (θfam : Fin M → Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)
      (hθ : Measurable θfam) (δ : ℝ≥0∞),
      2 ≤ M ∧ IsSeparatedFamily (Subtype.val) θfam δ ∧
      ENNReal.ofReal (2048⁻¹ * min ((1 + ν) / ν ^ 2 * (d / n)) 1)
        ≤ (fun x : ℝ≥0∞ => x ^ 2) δ
            * (1 - (mutualInformation (P.comap θfam hθ) + ENNReal.ofReal (Real.log 2))
                    / ENNReal.ofReal (Real.log (M : ℝ))) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hm : 39 ≤ m := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hν1 : (0 : ℝ) < 1 + ν := by linarith
  -- target ratio, tilt parameter
  set t : ℝ := (1 + ν) / ν ^ 2 * ((↑(m + 1) : ℝ) / ↑n) with ht_def
  have ht0 : 0 ≤ t := by rw [ht_def]; positivity
  set δsq : ℝ := min (64⁻¹ * t) 1 with hδsq_def
  have hδsq0 : 0 ≤ δsq := le_min (by positivity) (by norm_num)
  have hδsq1 : δsq ≤ 1 := min_le_right _ _
  set δ0 : ℝ := Real.sqrt δsq with hδ0_def
  have hδ0nonneg : 0 ≤ δ0 := Real.sqrt_nonneg _
  have hδ0sq : δ0 ^ 2 = δsq := Real.sq_sqrt hδsq0
  set s : ℝ := Real.sqrt (1 - δsq) with hs_def
  have hs2 : s ^ 2 = 1 - δsq := Real.sq_sqrt (by linarith)
  -- packing
  obtain ⟨T, hTlog, hTunit, hTsep⟩ := exists_sphere_packing m
  set M := T.card with hM_def
  have hlogM : (m : ℝ) / 10 ≤ Real.log M := hTlog
  have hM2 : 2 ≤ M := by
    by_contra h; push_neg at h
    have hM1 : (M : ℝ) ≤ 1 := by exact_mod_cast (by omega : M ≤ 1)
    have hnp : (0 : ℝ) ≤ M := by positivity
    have := Real.log_nonpos hnp hM1
    have hmge : (39 : ℝ) ≤ m := by exact_mod_cast hm
    linarith [hlogM, this]
  haveI : NeZero M := ⟨by omega⟩
  -- index the packing
  set e := T.equivFin with he_def
  set pv : Fin M → EuclideanSpace ℝ (Fin m) := fun a => (e.symm a : EuclideanSpace ℝ (Fin m))
    with hpv_def
  have hpv_mem : ∀ a, pv a ∈ T := fun a => (e.symm a).2
  have hpv_unit : ∀ a, ‖pv a‖ = 1 := fun a => hTunit _ (hpv_mem a)
  have hpv_ne : ∀ a b, a ≠ b → pv a ≠ pv b := by
    intro a b hab hcon
    exact hab (e.symm.injective (Subtype.coe_injective hcon))
  have hpv_sep : ∀ a b, a ≠ b → (1 / 2 : ℝ) ≤ ‖pv a - pv b‖ :=
    fun a b hab => hTsep _ (hpv_mem a) _ (hpv_mem b) (hpv_ne a b hab)
  -- the tilted unit vectors
  set θvec : Fin M → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun a => (WithLp.toLp 2 (Fin.cons s (fun j => δ0 * (pv a : Fin m → ℝ) j))) with hθvec_def
  have hcoe : ∀ a, ((θvec a : EuclideanSpace ℝ (Fin (m + 1))) : Fin (m + 1) → ℝ)
      = Fin.cons s (fun j => δ0 * (pv a : Fin m → ℝ) j) := fun a => rfl
  have hθdot : ∀ a, ((θvec a : Fin (m + 1) → ℝ)) ⬝ᵥ (θvec a : Fin (m + 1) → ℝ) = 1 := by
    intro a
    rw [hcoe a, tilt_dot, euclid_self_dot, hpv_unit a, hs2, hδ0sq]; ring
  have hθnorm : ∀ a, ‖θvec a‖ = 1 := by
    intro a
    have h1 : ‖θvec a‖ ^ 2 = 1 := by rw [← euclid_self_dot (θvec a)]; exact hθdot a
    calc ‖θvec a‖ = Real.sqrt (‖θvec a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt 1 := by rw [h1]
      _ = 1 := Real.sqrt_one
  set θfam : Fin M → Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
    fun a => ⟨θvec a, mem_sphere_zero_iff_norm.mpr (hθnorm a)⟩ with hθfam_def
  have hθmeas : Measurable θfam := measurable_of_countable _
  -- separation of the family (norm of differences)
  have hsubnorm : ∀ j k, ‖θvec j - θvec k‖ ^ 2 = δ0 ^ 2 * ‖pv j - pv k‖ ^ 2 := by
    intro j k
    have hcoesub : ((θvec j - θvec k : EuclideanSpace ℝ (Fin (m + 1))) : Fin (m + 1) → ℝ)
        = Fin.cons 0 (fun i => δ0 * ((pv j - pv k : EuclideanSpace ℝ (Fin m)) : Fin m → ℝ) i) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [hcoe, PiLp.sub_apply, Fin.cons_zero]
      · intro i'
        simp [PiLp.sub_apply, hcoe, Fin.cons_succ]; ring
    rw [← euclid_self_dot (θvec j - θvec k), ← euclid_self_dot (pv j - pv k), hcoesub, tilt_dot]
    ring
  have hsep_norm : ∀ j k, j ≠ k → δ0 / 2 ≤ ‖θvec j - θvec k‖ := by
    intro j k hjk
    have hb : (1 / 2 : ℝ) ≤ ‖pv j - pv k‖ := hpv_sep j k hjk
    have hsq : (δ0 / 2) ^ 2 ≤ ‖θvec j - θvec k‖ ^ 2 := by
      rw [hsubnorm]
      have hb2 : (1 / 2 : ℝ) ^ 2 ≤ ‖pv j - pv k‖ ^ 2 := by
        nlinarith [hb, norm_nonneg (pv j - pv k)]
      nlinarith [hb2, hδ0sq, hδsq0, sq_nonneg δ0]
    calc δ0 / 2 = Real.sqrt ((δ0 / 2) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ Real.sqrt (‖θvec j - θvec k‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖θvec j - θvec k‖ := Real.sqrt_sq (norm_nonneg _)
  -- the comap kernel and its mutual information
  haveI : IsMarkovKernel (P.comap θfam hθmeas) := Kernel.IsMarkovKernel.comap P hθmeas
  set Qc := P.comap θfam hθmeas with hQc_def
  set ua : Fin M → (Fin (m + 1) → ℝ) :=
    fun a => ((θfam a : EuclideanSpace ℝ (Fin (m + 1))) : Fin (m + 1) → ℝ) with hua_def
  have hua1 : ∀ a, ua a ⬝ᵥ ua a = 1 := fun a => hθdot a
  have hpd_bound : ∀ j k, |(pv j : Fin m → ℝ) ⬝ᵥ (pv k : Fin m → ℝ)| ≤ 1 := by
    intro j k
    have := euclid_dot_le (pv j) (pv k)
    rw [hpv_unit j, hpv_unit k, mul_one] at this
    exact this
  have hrho : ∀ j k, ua j ⬝ᵥ ua k
      = (1 - δsq) + δsq * ((pv j : Fin m → ℝ) ⬝ᵥ (pv k : Fin m → ℝ)) := by
    intro j k
    show ((θvec j : Fin (m + 1) → ℝ)) ⬝ᵥ (θvec k : Fin (m + 1) → ℝ) = _
    rw [hcoe j, hcoe k, tilt_dot, hs2, hδ0sq]
  have hQc_eq : ∀ a, Qc a = Measure.pi (fun _ : Fin n =>
      multivariateGaussian 0 (1 + ν • Matrix.vecMulVec (ua a) (ua a))) := by
    intro a
    rw [hQc_def, Kernel.comap_apply P hθmeas a, hP (θfam a)]
  have hQcKL : ∀ j k, klDiv (Qc j) (Qc k)
      = ENNReal.ofReal ((n : ℝ) * (2⁻¹ * (ν ^ 2 * (1 - (ua j ⬝ᵥ ua k) ^ 2) / (1 + ν)))) := by
    intro j k
    rw [hQc_eq j, hQc_eq k]
    exact klDiv_pca_pair (ua j) (ua k) (hua1 j) (hua1 k) hν
  -- the per-pair KL bound `≤ ofReal (2 n ν² δsq / (1+ν))`
  set Cb : ℝ := 2 * (n : ℝ) * ν ^ 2 * δsq / (1 + ν) with hCb_def
  have hbound_term : ∀ j k, klDiv (Qc j) (Qc k) ≤ ENNReal.ofReal Cb := by
    intro j k
    rw [hQcKL j k]
    apply ENNReal.ofReal_le_ofReal
    set pd := (pv j : Fin m → ℝ) ⬝ᵥ (pv k : Fin m → ℝ) with hpd_def
    have hpdle : pd ≤ 1 := le_of_abs_le (hpd_bound j k)
    have hpdge : -1 ≤ pd := neg_le_of_abs_le (hpd_bound j k)
    rw [hrho j k]
    have h1mrho : 1 - ((1 - δsq) + δsq * pd) ^ 2 ≤ 4 * δsq := by
      nlinarith [hpdle, hpdge, hδsq0, hδsq1,
        mul_nonneg hδsq0 (by linarith : (0 : ℝ) ≤ 1 - pd),
        sq_nonneg (δsq * (1 - pd)),
        mul_nonneg hδsq0 (by linarith : (0 : ℝ) ≤ 1 + pd)]
    have hnν : (0 : ℝ) ≤ (n : ℝ) * ν ^ 2 := by positivity
    have hAB : (n : ℝ) * ν ^ 2 * (1 - ((1 - δsq) + δsq * pd) ^ 2) / 2
        ≤ 2 * (n : ℝ) * ν ^ 2 * δsq := by
      nlinarith [mul_nonneg hnν (by linarith [h1mrho] :
        (0 : ℝ) ≤ 4 * δsq - (1 - ((1 - δsq) + δsq * pd) ^ 2))]
    rw [hCb_def,
      show (n : ℝ) * (2⁻¹ * (ν ^ 2 * (1 - ((1 - δsq) + δsq * pd) ^ 2) / (1 + ν)))
        = ((n : ℝ) * ν ^ 2 * (1 - ((1 - δsq) + δsq * pd) ^ 2) / 2) / (1 + ν) from by ring,
      show 2 * (n : ℝ) * ν ^ 2 * δsq / (1 + ν) = (2 * (n : ℝ) * ν ^ 2 * δsq) / (1 + ν) from by ring]
    exact (div_le_div_iff_of_pos_right hν1).mpr hAB
  -- mutual information bound
  have hMI : mutualInformation Qc ≤ ENNReal.ofReal Cb := by
    refine le_trans (mutualInformation_le_avg_pairwise_kl Qc) ?_
    have hsumle : ∑ j, ∑ k, klDiv (Qc j) (Qc k)
        ≤ ∑ _j : Fin M, ∑ _k : Fin M, ENNReal.ofReal Cb := by
      apply Finset.sum_le_sum; intro j _
      apply Finset.sum_le_sum; intro k _
      exact hbound_term j k
    refine le_trans (mul_le_mul_right hsumle _) ?_
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      nsmul_eq_mul]
    have hMne0 : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
    have hMtop : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
    rw [show ((M : ℝ≥0∞) ^ 2)⁻¹ * ((M : ℝ≥0∞) * ((M : ℝ≥0∞) * ENNReal.ofReal Cb))
        = (((M : ℝ≥0∞) ^ 2)⁻¹ * (M : ℝ≥0∞) ^ 2) * ENNReal.ofReal Cb from by ring,
      ENNReal.inv_mul_cancel (by positivity) (by
        simp [ENNReal.pow_eq_top_iff, hMtop]), one_mul]
  -- real Fano arithmetic: `Cb + log 2 ≤ ½ log M`
  have hCble : Cb ≤ (↑(m + 1) : ℝ) / 32 := by
    have hstep : Cb ≤ 2 * (n : ℝ) * ν ^ 2 * (64⁻¹ * t) / (1 + ν) := by
      rw [hCb_def]; gcongr; exact min_le_left _ _
    have heq : 2 * (n : ℝ) * ν ^ 2 * (64⁻¹ * t) / (1 + ν) = (↑(m + 1) : ℝ) / 32 := by
      rw [ht_def]; field_simp; ring
    linarith [hstep, heq.le]
  have hfano_real : Cb + Real.log 2 ≤ 2⁻¹ * Real.log M := by
    have hlog2 := Real.log_two_lt_d9
    have hmge : (39 : ℝ) ≤ m := by exact_mod_cast hm
    have hcast : (↑(m + 1) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hCble
    linarith [hCble, hlog2, hlogM]
  -- assemble: bracket ≥ 1/2
  have hlogMpos : 0 < Real.log M := by
    have hmge : (39 : ℝ) ≤ m := by exact_mod_cast hm
    linarith [hlogM]
  have hdiv : (mutualInformation Qc + ENNReal.ofReal (Real.log 2))
      / ENNReal.ofReal (Real.log M) ≤ 2⁻¹ := by
    rw [ENNReal.div_le_iff (by positivity) (by simp)]
    calc mutualInformation Qc + ENNReal.ofReal (Real.log 2)
        ≤ ENNReal.ofReal Cb + ENNReal.ofReal (Real.log 2) := by gcongr
      _ = ENNReal.ofReal (Cb + Real.log 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (Real.log_nonneg (by norm_num))]
      _ ≤ ENNReal.ofReal (2⁻¹ * Real.log M) := ENNReal.ofReal_le_ofReal hfano_real
      _ = 2⁻¹ * ENNReal.ofReal (Real.log M) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; congr 1; simp [ENNReal.ofReal_ofNat]
  have hbracket : (2⁻¹ : ℝ≥0∞) ≤ 1 - (mutualInformation Qc + ENNReal.ofReal (Real.log 2))
      / ENNReal.ofReal (Real.log M) := by
    have h := tsub_le_tsub_left hdiv (1 : ℝ≥0∞)
    rwa [ENNReal.one_sub_inv_two] at h
  -- final inequality
  refine ⟨M, inferInstance, θfam, hθmeas, ENNReal.ofReal (δ0 / 4), hM2, ?_, ?_⟩
  · -- separated family
    intro j k hjk
    have : 2 * ENNReal.ofReal (δ0 / 4) = ENNReal.ofReal (δ0 / 2) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    show 2 * ENNReal.ofReal (δ0 / 4) ≤ edist (Subtype.val (θfam j)) (Subtype.val (θfam k))
    rw [this, edist_dist, dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal (hsep_norm j k hjk)
  · -- the squared-separation × bracket bound
    have hδexist_sq : (fun x : ℝ≥0∞ => x ^ 2) (ENNReal.ofReal (δ0 / 4))
        = ENNReal.ofReal (δsq / 16) := by
      simp only
      rw [← ENNReal.ofReal_pow (by linarith)]
      congr 1
      rw [div_pow, hδ0sq]; norm_num
    rw [hδexist_sq]
    have hmin : 64⁻¹ * min t 1 ≤ min (64⁻¹ * t) 1 := by
      refine le_min ?_ ?_
      · exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
      · calc 64⁻¹ * min t 1 ≤ 64⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
          _ ≤ 1 := by norm_num
    have hfinal_real : 2048⁻¹ * min t 1 ≤ δsq / 32 := by
      rw [hδsq_def]; linarith [hmin]
    calc ENNReal.ofReal (2048⁻¹ * min t 1)
        ≤ ENNReal.ofReal (δsq / 16) * ENNReal.ofReal 2⁻¹ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [show δsq / 16 * 2⁻¹ = δsq / 32 from by ring]
          exact hfinal_real
      _ ≤ ENNReal.ofReal (δsq / 16)
            * (1 - (mutualInformation Qc + ENNReal.ofReal (Real.log 2))
                / ENNReal.ofReal (Real.log M)) := by
          gcongr
          rw [show ENNReal.ofReal 2⁻¹ = (2⁻¹ : ℝ≥0∞) from by simp [ENNReal.ofReal_inv_of_pos]]
          exact hbracket

/-- **Minimax risk for PCA in the spiked model** (Wainwright Example 15.19): for `n` i.i.d. samples
from `𝒩(0, Iᵈ + ν θ*θ*ᵀ)` with `θ*` on the unit sphere, the minimax risk for estimating `θ*` in
squared Euclidean norm is at least `c·min{(1+ν)/ν²·d/n, 1}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.4, Example 15.19. -/
theorem pca_minimax_rate {n d : ℕ} (hn : 1 ≤ n)
    -- LEAN-ONLY: d ≥ d₀ — Fano's method needs e^{Ω(d)} hypotheses; the small-d regime is a separate
    -- two-point bound. Wainwright Ex 15.19 is a large-d rate.
    (hd0 : 40 ≤ d) (ν : ℝ) (hν : 0 < ν)
    (P : Kernel (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (Fin n → EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel P]
    -- USER-INPUT: `Z ∼ 𝒩(0, Iᵈ + ν θθᵀ)^{⊗n}` (spiked covariance model); Wainwright Ex 15.19.
    (hP : ∀ θ, P θ = Measure.pi fun _ : Fin n =>
      multivariateGaussian 0 (1 + ν • vecMulVec (θ : Fin d → ℝ) (θ : Fin d → ℝ))) :
    -- USER-INPUT: constant loosened from book 128⁻¹ to the value provable from the n/10
    -- sphere-packing brick (Wainwright Ex 15.19; CLAUDE.md §1).
    ENNReal.ofReal (2048⁻¹ * min ((1 + ν) / ν ^ 2 * (d / n)) 1)
      ≤ minimaxRiskDist (· ^ 2) (Subtype.val) P := by
  obtain ⟨M, hMne, θfam, hθ, δ, hM, hsep, hbound⟩ := pca_fano_config hn hd0 ν hν P hP
  haveI := hMne
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have key := minimax_fano_lower_bound (fun x : ℝ≥0∞ => x ^ 2) (Subtype.val) P θfam hθ δ hM hΦ hsep
  exact le_trans hbound key

end StatLean.Minimaxity
