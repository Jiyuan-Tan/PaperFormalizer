module
public import StatLean.Minimaxity.Fano.MutualInformation
public import StatLean.Minimaxity.ForMathlib.GaussianKLMulti
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# Gaussian maximum-entropy mutual-information bound

When the observation conditioned on the index is Gaussian, the mutual information admits a
log-determinant bound coming from the maximum-entropy property of the multivariate Gaussian.
Suppose the conditional law of the observation given the index is centered Gaussian,
$Z \mid J = j \sim \mathcal{N}(0, \Sigma^j)$, for $j = 1, \dots, M$. Then the mutual information
between $Z$ and the uniformly distributed index $J$ satisfies
$$
  I(Z; J) \;\le\; \tfrac12\Bigl( \log\det \operatorname{cov}(Z)
    \;-\; \tfrac{1}{M}\sum_{j=1}^{M} \log\det \Sigma^j \Bigr),
$$
where $\Sigma^j = \operatorname{cov}(Z \mid J = j)$ is positive definite and
$\operatorname{cov}(Z) = \tfrac{1}{M}\sum_{j=1}^{M}\Sigma^j$ is the covariance of the zero-mean
Gaussian mixture. This refines the convexity bound (Eq. (15.34)) and is the key tool for the PCA
lower bound (Example 15.19).

Added hypotheses relative to the book: each component covariance $\Sigma^j$ is assumed positive
definite, and the means are taken to be zero (the relevant minimax constructions in §15.3.4 use
centered Gaussian components), so $\operatorname{cov}(Z)$ is the average of the $\Sigma^j$ rather
than carrying the between-means contribution.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds),
§15.3.4, Lemma 15.17, Eq. (15.42).

**Proof formalization notes.** The proof avoids differential entropy entirely. The mixture
distribution minimizes the average KL divergence over all candidate reference measures
(`sum_klDiv_mixture_le`), so the average $\tfrac1M\sum_j D(\mathcal{N}(0,\Sigma^j) \,\|\, \text{mixture})$
is bounded above by comparing against the matched zero-mean Gaussian $G = \mathcal{N}(0, \operatorname{cov}(Z))$.
Each $D(\mathcal{N}(0,\Sigma^j) \,\|\, G)$ has the closed form
$\tfrac12(\log\det\operatorname{cov}(Z) - \log\det\Sigma^j + \operatorname{tr}(\operatorname{cov}(Z)^{-1}\Sigma^j) - d)$
(`klDiv_multivariateGaussian_zero`), and the trace terms average to
$\operatorname{tr}\bigl(\operatorname{cov}(Z)^{-1}\cdot\tfrac1M\sum_j\Sigma^j\bigr) = \operatorname{tr}(I) = d$,
cancelling the $-d$. Nonnegativity of each closed-form summand is the matrix Gibbs inequality
(`logdet_trace_nonneg`): after whitening by $R = B^{-1/2}$, the expression diagonalizes to
$\tfrac12\sum_i (\Lambda_i - 1 - \log\Lambda_i) \ge 0$ via $\log x \le x - 1$. This replaces the
book's appeal to the Gaussian maximum-entropy theorem (Exercise 15.14) and concavity of
$\log\det$ with an explicit KL computation. The auxiliary lemma `logdet_trace_nonneg` shares the
same diagonalization as `klDiv_multivariateGaussian_zero` but exposes the *sign* rather than the
value.

**Bibliographic comments.** This is a folklore consequence of the Gaussian maximum-entropy
principle and carries no single seminal origin. The maximum-entropy property of the multivariate
Gaussian — that among all distributions with a fixed covariance the Gaussian maximizes differential
entropy — originates with C. E. Shannon, "A Mathematical Theory of Communication," *Bell System
Technical Journal* 27 (1948), 379–423 and 623–656. The standard modern reference is T. M. Cover and
J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006 (the maximum-entropy
characterization is Theorem 8.6.5). The mutual-information bound stated here is the packaging of that
principle for minimax analysis given in Wainwright (2019), Lemma 15.17; we are not aware of a
distinct primary-research source for this specific inequality.
-/

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal MatrixOrder

namespace StatLean.Minimaxity

/-- **Matrix Gibbs inequality** (nonnegativity of the centered-Gaussian KL formula). For positive
definite `A, B`, the relative-entropy integrand `½ (log det B − log det A + tr(B⁻¹A) − d)` is
nonnegative. After whitening by `R = B^{-1/2}` the matrix `C = R A R` is positive definite with
eigenvalues `Λᵢ > 0`, and the expression equals `½ Σᵢ (Λᵢ − 1 − log Λᵢ) ≥ 0` since
`log x ≤ x − 1`. (Same diagonalization as `klDiv_multivariateGaussian_zero`, kept separate because
that lemma only exposes the *value*, not its sign.) -/
private lemma logdet_trace_nonneg {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    (0 : ℝ) ≤ 2⁻¹ * (Real.log B.det - Real.log A.det + (B⁻¹ * A).trace - d) := by
  classical
  have hBdetU : IsUnit B.det := isUnit_iff_ne_zero.mpr hB.det_pos.ne'
  have hAdetne : A.det ≠ 0 := hA.det_pos.ne'
  have hBdetne : B.det ≠ 0 := hB.det_pos.ne'
  set R : Matrix (Fin d) (Fin d) ℝ := CFC.sqrt B⁻¹ with hR_def
  have hBinv0 : (0 : Matrix (Fin d) (Fin d) ℝ) ≤ B⁻¹ :=
    Matrix.nonneg_iff_posSemidef.mpr hB.inv.posSemidef
  have hRR : R * R = B⁻¹ := by rw [hR_def]; exact CFC.sqrt_mul_sqrt_self B⁻¹ hBinv0
  have hRsa : IsSelfAdjoint R := by rw [hR_def]; exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B⁻¹)
  have hRtransp : Rᵀ = R := by
    have h : star R = R := hRsa
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hRunit : IsUnit R := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    have hsq : R.det * R.det = B⁻¹.det := by rw [← Matrix.det_mul, hRR]
    rw [h0, mul_zero] at hsq
    exact hB.inv.det_pos.ne' hsq.symm
  have hRmulVecInj : Function.Injective R.mulVec := Matrix.mulVec_injective_of_isUnit hRunit
  set C : Matrix (Fin d) (Fin d) ℝ := R * A * R with hC_def
  have hC : C.PosDef := by
    rw [hC_def]
    have h := hA.conjTranspose_mul_mul_same hRmulVecInj
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hRtransp] at h
  have hCdetB : C.det * B.det = A.det := by
    have h1 : C.det * B.det = A.det * ((R * R).det * B.det) := by
      rw [hC_def]; simp only [Matrix.det_mul]; ring
    rw [h1, hRR, ← Matrix.det_mul, Matrix.nonsing_inv_mul B hBdetU, Matrix.det_one, mul_one]
  have hlogdetC : Real.log C.det = Real.log A.det - Real.log B.det := by
    rw [eq_div_of_mul_eq hBdetne hCdetB, Real.log_div hAdetne hBdetne]
  have htraceC : C.trace = (B⁻¹ * A).trace := by
    rw [hC_def, Matrix.trace_mul_cycle, hRR]
  set Λ : Fin d → ℝ := hC.1.eigenvalues with hΛ_def
  have hΛpos : ∀ i, 0 < Λ i := fun i => hC.eigenvalues_pos i
  have hsumΛ : ∑ i, Λ i = (B⁻¹ * A).trace := by
    rw [← htraceC, hC.1.trace_eq_sum_eigenvalues]
    simp only [hΛ_def, RCLike.ofReal_real_eq_id, id_eq]
  have hsumlog : ∑ i, Real.log (Λ i) = Real.log A.det - Real.log B.det := by
    rw [← hlogdetC, hC.1.det_eq_prod_eigenvalues]
    simp only [hΛ_def, RCLike.ofReal_real_eq_id, id_eq]
    rw [Real.log_prod (fun i _ => (hΛpos i).ne')]
  -- The whole expression is `½ Σᵢ (Λᵢ − 1 − log Λᵢ)`.
  have hexpr : Real.log B.det - Real.log A.det + (B⁻¹ * A).trace - (d : ℝ)
      = ∑ i, (Λ i - 1 - Real.log (Λ i)) := by
    simp only [Finset.sum_sub_distrib]
    rw [hsumΛ, hsumlog, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  rw [hexpr]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => ?_))
  linarith [Real.log_le_sub_one_of_pos (hΛpos i)]

/-- **Residual analytic core of Lemma 15.17.** The average KL divergence from each zero-mean
Gaussian component `Q j = 𝒩(0, Σʲ)` to the mixture is bounded by the log-determinant gap. We avoid
differential entropy entirely: the mixture minimizes the average KL (`sum_klDiv_mixture_le`), so we
may compare to the matched Gaussian `G = 𝒩(0, cov(Z))`. Each `D(𝒩(0,Σʲ) ‖ G)` has the closed form
`½ (log det cov(Z) − log det Σʲ + tr(cov(Z)⁻¹ Σʲ) − d)` (`klDiv_multivariateGaussian_zero`), and the
trace terms average to `tr(cov(Z)⁻¹ · (1/M) Σⱼ Σʲ) = tr(I) = d`, cancelling the `−d`. -/
private lemma sum_klDiv_le_logdet {M d : ℕ} [NeZero M]
    (Q : Kernel (Fin M) (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel Q]
    (S : Fin M → Matrix (Fin d) (Fin d) ℝ) (covZ : Matrix (Fin d) (Fin d) ℝ)
    -- USER-INPUT: each component covariance Σʲ is positive-definite
    -- (Wainwright Lemma 15.17 — Σʲ = cov(Z|J=j)).
    (hS : ∀ j, (S j).PosDef)
    (hQ : ∀ j, Q j = multivariateGaussian 0 (S j))
    (hcov : covZ = (M : ℝ)⁻¹ • ∑ j, S j) :
    (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) (mixture Q)
      ≤ ENNReal.ofReal
          (2⁻¹ * (Real.log covZ.det - (M : ℝ)⁻¹ * ∑ j, Real.log (S j).det)) := by
  classical
  haveI : Nonempty (Fin M) := ⟨(0 : Fin M)⟩
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast NeZero.pos M
  have hM0 : (M : ℝ) ≠ 0 := hMpos.ne'
  have hMinv : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
  -- The mixture covariance is positive definite (average of positive-definite matrices).
  have hcovPD : covZ.PosDef := by
    rw [hcov]
    exact (Matrix.posDef_sum Finset.univ_nonempty (fun i _ => hS i)).smul (by positivity)
  have hcovU : IsUnit covZ.det := isUnit_iff_ne_zero.mpr hcovPD.det_pos.ne'
  set G : Measure (EuclideanSpace ℝ (Fin d)) := multivariateGaussian 0 covZ with hG_def
  -- Step 1+2: the mixture minimizes the average KL, so compare against the matched Gaussian `G`.
  have hmix : mixture Q = (M : ℝ≥0∞)⁻¹ • ∑ k, Q k := mixture_eq_inv_smul_sum Q
  have hstep2 : ∑ j, klDiv (Q j) (mixture Q) ≤ ∑ j, klDiv (Q j) G := by
    rw [hmix]; exact sum_klDiv_mixture_le (fun j => Q j) G
  -- Step 3: closed form for each matched-Gaussian KL divergence.
  have hval : ∀ j, klDiv (Q j) G
      = ENNReal.ofReal
          (2⁻¹ * (Real.log covZ.det - Real.log (S j).det + (covZ⁻¹ * S j).trace - d)) := by
    intro j
    rw [hQ j, hG_def, klDiv_multivariateGaussian_zero (S j) covZ (hS j) hcovPD]
  have hrnn : ∀ j ∈ (Finset.univ : Finset (Fin M)),
      (0 : ℝ) ≤ 2⁻¹ * (Real.log covZ.det - Real.log (S j).det + (covZ⁻¹ * S j).trace - d) :=
    fun j _ => logdet_trace_nonneg (S j) covZ (hS j) hcovPD
  -- Trace identity: `Σⱼ tr(cov(Z)⁻¹ Σʲ) = tr(cov(Z)⁻¹ Σⱼ Σʲ) = M · tr(I) = M · d`.
  have hsumS : ∑ j, S j = (M : ℝ) • covZ := by
    rw [hcov, smul_smul, mul_inv_cancel₀ hM0, one_smul]
  have htrace : ∑ j, (covZ⁻¹ * S j).trace = (M : ℝ) * d := by
    rw [← Matrix.trace_sum, ← Finset.mul_sum, hsumS, mul_smul_comm,
      Matrix.nonsing_inv_mul covZ hcovU, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul]
  -- Real-number computation of the averaged closed form.
  have hreal : (M : ℝ)⁻¹ *
      ∑ j, (2⁻¹ * (Real.log covZ.det - Real.log (S j).det + (covZ⁻¹ * S j).trace - d))
      = 2⁻¹ * (Real.log covZ.det - (M : ℝ)⁻¹ * ∑ j, Real.log (S j).det) := by
    have hsplit : ∑ j, (2⁻¹ * (Real.log covZ.det - Real.log (S j).det + (covZ⁻¹ * S j).trace - d))
        = 2⁻¹ * ((M : ℝ) * Real.log covZ.det - (∑ j, Real.log (S j).det)
            + (∑ j, (covZ⁻¹ * S j).trace) - (M : ℝ) * d) := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        nsmul_eq_mul]
    rw [hsplit, htrace]
    field_simp
    ring
  -- Assemble in `ℝ≥0∞`.
  have key : ∑ j, klDiv (Q j) G
      = ENNReal.ofReal
          (∑ j, 2⁻¹ * (Real.log covZ.det - Real.log (S j).det + (covZ⁻¹ * S j).trace - d)) := by
    rw [Finset.sum_congr rfl (fun j _ => hval j), ← ENNReal.ofReal_sum_of_nonneg hrnn]
  have hMcast : (M : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((M : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hMpos, ENNReal.ofReal_natCast]
  calc (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) (mixture Q)
      ≤ (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) G := by gcongr
    _ = ENNReal.ofReal ((M : ℝ)⁻¹) *
          ENNReal.ofReal
            (∑ j, 2⁻¹ * (Real.log covZ.det - Real.log (S j).det + (covZ⁻¹ * S j).trace - d)) := by
          rw [key, hMcast]
    _ = ENNReal.ofReal ((M : ℝ)⁻¹ *
          ∑ j, 2⁻¹ * (Real.log covZ.det - Real.log (S j).det + (covZ⁻¹ * S j).trace - d)) := by
          rw [← ENNReal.ofReal_mul hMinv]
    _ = ENNReal.ofReal
          (2⁻¹ * (Real.log covZ.det - (M : ℝ)⁻¹ * ∑ j, Real.log (S j).det)) := by rw [hreal]

/-- **Gaussian maximum-entropy mutual-information bound** (Wainwright Lemma 15.17, Eq. (15.42)):
if `Z | J = j ∼ 𝒩(0, Σʲ)`, then `I(Z; J) ≤ ½(log det cov(Z) − (1/M) Σⱼ log det Σʲ)`, where
`cov(Z) = (1/M) Σⱼ Σʲ` is the covariance of the zero-mean Gaussian mixture.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.4, Lemma 15.17. -/
theorem gaussian_mutualInfo_le {M d : ℕ} [NeZero M]
    (Q : Kernel (Fin M) (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel Q]
    (S : Fin M → Matrix (Fin d) (Fin d) ℝ) (covZ : Matrix (Fin d) (Fin d) ℝ)
    -- USER-INPUT: each component covariance Σʲ is positive-definite
    -- (Wainwright Lemma 15.17 — Σʲ = cov(Z|J=j)).
    (hS : ∀ j, (S j).PosDef)
    -- USER-INPUT: `Z | J = j ∼ 𝒩(0, Σʲ)`; Wainwright §15.3.4, Lemma 15.17.
    (hQ : ∀ j, Q j = multivariateGaussian 0 (S j))
    -- USER-INPUT: `cov(Z) = (1/M) Σⱼ Σʲ` (mixture covariance, zero means); Wainwright §15.3.4.
    (hcov : covZ = (M : ℝ)⁻¹ • ∑ j, S j) :
    mutualInformation Q
      ≤ ENNReal.ofReal
          (2⁻¹ * (Real.log covZ.det - (M : ℝ)⁻¹ * ∑ j, Real.log (S j).det)) := by
  unfold mutualInformation
  exact sum_klDiv_le_logdet Q S covZ hS hQ hcov

end StatLean.Minimaxity
