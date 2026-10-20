module
public import StatLean.AsymptoticStatistics.ForMathlib.Anderson
public import StatLean.AsymptoticStatistics.ForMathlib.BowlShaped
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import StatLean.AsymptoticStatistics.ForMathlib.MarkovKernelProhorov
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianWeakLimit
public import StatLean.AsymptoticStatistics.ForMathlib.PortmanteauLscBridge
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Decision.Risk.Defs
public import Mathlib.Probability.Decision.Risk.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# Gaussian shift Bayes risk computations (minimax via Anderson's lemma)

Concrete realization of the Bayesian path underlying the minimax property of the
linear estimator in a Gaussian shift (normal location) experiment. The "Gaussian
shift" experiment here is the LAN limit experiment of parametric families:
- prior on the shift `h`: $\pi_\tau = N(0, \tau^2 I)$ (Gaussian, parametrized by $\tau > 0$);
- likelihood (one observation): $X \mid h \sim N(h,\, J^{-1})$, with $J$ the
  (nonsingular) Fisher information, so $J^{-1}$ plays the role of vdV's known
  covariance $\Sigma$;
- target: $A h$, a linear functional of the shift;
- loss: a bowl-shaped function $L$ (sublevel sets $\{x : L(x) \le c\}$ convex and
  symmetric about the origin).

By Bayes' rule on Gaussian densities, the posterior is
$h \mid X = x \sim N(\Sigma_\tau J x,\ \Sigma_\tau)$ with
$\Sigma_\tau := (J + \tau^{-2} I)^{-1} = (\Sigma^{-1} + \Lambda^{-1})^{-1}$ where
$\Lambda = \tau^2 I$ is the prior covariance. The Bayes risk at prior parameter
$\tau$ is $r^\ast(\pi_\tau) = \int L \, dN(0,\, A \Sigma_\tau A^{\mathsf T})$, and
taking the noninformative limit gives
$\sup_{\tau > 0} r^\ast(\pi_\tau) = \int L \, dN(0,\, A J^{-1} A^{\mathsf T})$.
Anderson's lemma — convoluting a centered Gaussian with any probability measure
cannot decrease a bowl-shaped loss integral — supplies the monotonicity that
makes the linear estimator $AX$ minimax: the maximum risk of any randomized
estimator of $A h$ is at least $\int L \, dN(0,\, A J^{-1} A^{\mathsf T})$.

Headline declarations: `bayesRiskAtTau`, `gaussianShift_bayes_risk_sup_eq_target`,
`bowl_shaped_loss_risk_kernel_form` (the kernel form of Proposition 8.6, the
lower bound on Bayes/minimax risk in the limit experiment).

We define `bayesRiskAtTau` directly as the explicit integral form
$\int L \, dN(0,\, A \Sigma_\tau A^{\mathsf T})$; the abstract Bayes risk
identification happens in the chapter assembly.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 8 (Efficiency of Estimators), §8.4 (Estimating Normal Means), Lemma 8.5
(Anderson's lemma) and Proposition 8.6 (minimaxity of `AX`). The result is the
Gaussian-side engine of the Local Asymptotic Minimax Theorem (Theorem 8.11, §8.7),
which is its downstream consumer.

**Proof formalization notes.**
The Bayesian argument of vdV's proof of Proposition 8.6 is formalized verbatim
at the level of the limit experiment. Take a normal prior $H \sim N(0, \tau^2 I)$
and view the likelihood $N(h, J^{-1})$ as the conditional law of $X$ given
$H = h$. A standard complete-the-square calculation gives the Gaussian posterior
$N(\Sigma_\tau J X,\ \Sigma_\tau)$ with $\Sigma_\tau = (J + \tau^{-2} I)^{-1}$;
the innovation $G_\tau := A(H - \Sigma_\tau J X)$ has law $N(0, A \Sigma_\tau A^{\mathsf T})$
and is **independent** of $X$. Because a supremum dominates an average,
$\sup_h \mathbb E_h L(T - A h) \ge \mathbb E\, L(G_\tau + W_\tau) \ge \mathbb E\, L(G_\tau)$
by Anderson's lemma (applied to the Gaussian $G_\tau$ convolved with the residual
$W_\tau$), for every $\tau$. As $\tau \to \infty$ the prior flattens,
$\Sigma_\tau \to J^{-1}$ in PSD order, $G_\tau \rightsquigarrow N(0, A J^{-1} A^{\mathsf T})$,
and the liminf of the right side is at least the target integral by the
portmanteau lemma.

Key load-bearing pieces in this file:
- `posteriorCov` ($\Sigma_\tau$), `posteriorMean`, `marginalGaussianShift`,
  and the joint pushforward identity `joint_pushforward_eq` (the
  independence-of-innovation step, proved via `IsGaussian.ext` on matching
  means and covariance bilinear forms).
- `posteriorCov_le_inv` ($\Sigma_\tau \preceq J^{-1}$ in PSD order) — the matrix
  algebra feeding the easy direction `bayesRiskAtTau_le_target` (Anderson's
  PSD-monotone form).
- `target_le_iSup_bayesRiskAtTau` — the hard direction, closed unconditionally
  for lower-semicontinuous `L` via Lévy weak continuity
  (`posteriorCov_tendsto_inv`) plus the Portmanteau lsc bridge.
- `gaussianShift_bayes_risk_sup_eq_target` assembles both directions; it is the
  single largest direct consumer of Anderson's PSD-monotone form in the Theorem
  8.11 proof.

Book-vs-Lean note: vdV states the result for known covariance $\Sigma$ and prior
$N(0, \Lambda)$ with $\Lambda \to \infty$; we instantiate $\Sigma = J^{-1}$ (limit
experiment) and the scalar flat-prior family $\Lambda = \tau^2 I$, $\tau \to \infty$,
which suffices for the LAM application and matches the displayed posterior
$(\Sigma^{-1} + \Lambda^{-1})^{-1}$.

**Bibliographic comments.**
Anderson's lemma is Lemma 8.5 in vdV and originates in T. W. Anderson, "The
integral of a symmetric unimodal function over a symmetric convex set and some
probability inequalities," *Proceedings of the American Mathematical Society*
**6** (1955), 170–176 (Theorem 1 and its corollaries): for a symmetric convex
set $K$ and a symmetric unimodal density, the set's probability content is
maximized when centered; equivalently $\int L\, dN(0,\Sigma) \le \int L\, d[N(0,\Sigma) * M]$
for every bowl-shaped $L$ and probability measure $M$. The minimax/asymptotic
optimality framing of the Gaussian shift experiment — the convolution theorem
and the local asymptotic minimax theorem that Proposition 8.6 serves — is due to
J. Hájek, "A characterization of limiting distributions of regular estimates,"
*Z. Wahrscheinlichkeitstheorie verw. Gebiete* **14** (1970), 323–330, and
J. Hájek, "Local asymptotic minimax and admissibility in estimation,"
*Proc. Sixth Berkeley Symp. Math. Statist. Probab.*, Vol. 1 (1972), 175–194,
building on L. Le Cam's theory of limit experiments.
-/

open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped ENNReal NNReal Topology Pointwise

namespace AsymptoticStatistics
namespace GaussianShiftMinimax

variable {k d : ℕ}

/-- **Conditional posterior covariance** `Σ_τ = (J + τ⁻²I)⁻¹`.

Derived from Bayes' rule on Gaussians: posterior precision = prior precision +
likelihood precision = `τ⁻²I + J`. -/
noncomputable def posteriorCov (J : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  (J + (τ^2)⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))⁻¹

/-- **Bayes risk at flat-prior parameter τ** — the explicit `∫ L dN(0, A Σ_τ Aᵀ)` form.

By Anderson's lemma applied to the Gaussian posterior (see
`gaussianShift_bayes_risk_explicit` for the abstract-risk identification),
this equals the Bayes risk in the Gaussian shift experiment with prior
`π_τ = N(0, τ²I)`, linear target `A h`, and bowl-shaped loss `L`. -/
noncomputable def bayesRiskAtTau
    (J : Matrix (Fin k) (Fin k) ℝ)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (L : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, L y ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
              (A * posteriorCov J τ * A.transpose))

/-- **`posteriorCov` is `PosDef`** when `J` is `PosDef` and `τ > 0`.

**Proof**: `J + (τ²)⁻¹•I` is `PosDef` (sum of two PosDef matrices), and
inverse of `PosDef` is `PosDef`. -/
theorem posteriorCov_posDef
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ : ℝ} (hτ : 0 < τ) :
    (posteriorCov J τ).PosDef := by
  unfold posteriorCov
  exact (hJ.add (Matrix.PosDef.one.smul (by positivity))).inv

/-- **Gaussian shift Bayes risk equals the explicit integral form**.

For Gaussian prior `π_τ = N(0, τ²I)`, linear target `A h`, bowl-shaped loss `L`
on the Gaussian shift experiment `X | h ~ multivariateGaussian h J⁻¹`:

The Bayes risk equals `bayesRiskAtTau J A L τ = ∫ L dN(0, A Σ_τ Aᵀ)`.

The Bayes optimal estimator is `T̂*(X) = A Σ_τ J X` (linear in X = `A · μ_τ(X)`,
the posterior mean of `A h`). By Anderson's lemma applied to the Gaussian
posterior, no other estimator does better.

**Proof outline**:

1. **Posterior is Gaussian**: `h | X = x ~ multivariateGaussian (Σ_τ J x) Σ_τ`.
   Derivation: posterior density ∝ prior density × likelihood density, both
   Gaussian → product of Gaussians is Gaussian (complete-the-square argument
   on the quadratic form in the exponent, or charFun uniqueness).

2. **Conditional risk via Anderson**: For any estimator `T̂(X)` of `A h`:
   `E[L(A h - T̂(X)) | X = x] = ∫ L((A μ_τ(x) - T̂(x)) - z) dN(0, A Σ_τ Aᵀ)(z)`,
   the LHS being a translate of the integral on the RHS. By Anderson
   (`anderson_lemma_loss`), this is ≥ `∫ L dN(0, A Σ_τ Aᵀ)` with equality
   iff `T̂(x) = A μ_τ(x)`.

3. **Marginalize**: Integrate the conditional risk against the marginal
   distribution of `X`, recover `r*(π_τ) = bayesRiskAtTau J A L τ`.

The conclusion is stated as the definitional equality
`bayesRiskAtTau J A L τ = (the integral form)`; the identification with the
abstract Bayes risk happens in the chapter assembly. -/
theorem gaussianShift_bayes_risk_explicit
    {J : Matrix (Fin k) (Fin k) ℝ} (_hJ : J.PosDef)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (L : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (_hL_bowl : BowlShaped L)
    {τ : ℝ} (_hτ : 0 < τ) :
    bayesRiskAtTau J A L τ
      = ∫⁻ y, L y ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
                    (A * posteriorCov J τ * A.transpose)) := by
  rfl

/-- **Matrix-algebra lemma — `posteriorCov J τ ≼ J⁻¹` in PSD order**.

For `J.PosDef` and `τ > 0`, `J⁻¹ - posteriorCov J τ = J⁻¹ - (J + (τ²)⁻¹•I)⁻¹`
is positive semidefinite.

**Proof sketch**:

The matrix identity
  `J⁻¹ - (J + ε•I)⁻¹ = ε • (posteriorCov J τ) * J⁻¹`
holds (where `ε := (τ²)⁻¹`), which can be verified by multiplying both sides
by `(J + ε•I)`:
  `(J + ε•I) * J⁻¹ - I = ε•I + ε² * J⁻¹`,
so `J⁻¹ - posteriorCov J τ` is `ε` times the symmetric product of two
commuting PSD matrices `posteriorCov J τ` and `J⁻¹`.

For the PSD conclusion, use that the product of two commuting symmetric PSD
matrices is PSD. Equivalently:
  `posteriorCov J τ * J⁻¹ = (posteriorCov J τ)^(1/2) * J⁻¹ * (posteriorCov J τ)^(1/2)`
(since `posteriorCov J τ` and `J⁻¹` commute, so does the square root with
`J⁻¹`). The RHS is `Bᵀ * X * B` with `X = J⁻¹` PSD and `B = (posteriorCov)^(1/2)`
symmetric, hence PSD by `Matrix.PosSemidef.mul_mul_conjTranspose_same`.

**Proof**: prove `M * (J⁻¹ - M⁻¹) * M = ε•1 + ε²•J⁻¹` (PSD), where
`M := J + ε•1`. Then by `Matrix.IsUnit.posSemidef_star_right_conjugate_iff`
(with `U = M` invertible, `star M = M` for symmetric M), the conjugation
`(M * X * star M).PosSemidef ↔ X.PosSemidef`, giving `(J⁻¹ - M⁻¹).PosSemidef`. -/
lemma posteriorCov_le_inv
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ : ℝ} (hτ : 0 < τ) :
    (J⁻¹ - posteriorCov J τ).PosSemidef := by
  set ε : ℝ := (τ^2)⁻¹ with hε_def
  have hε : 0 < ε := by positivity
  set M : Matrix (Fin k) (Fin k) ℝ := J + ε • (1 : Matrix _ _ _) with hM_def
  have hM : M.PosDef := hJ.add (Matrix.PosDef.one.smul hε)
  change (J⁻¹ - M⁻¹).PosSemidef
  -- Inverse identities.
  have hJ_unit : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ.isUnit
  have hM_unit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ_unit
  have hJJ' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJ_unit
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM_unit
  -- Key identity: `M * (J⁻¹ - M⁻¹) * M = ε•1 + ε²•J⁻¹`.
  have hKey : M * (J⁻¹ - M⁻¹) * M = ε • (1 : Matrix _ _ _) + (ε^2) • J⁻¹ := by
    -- Distribute: M * (J⁻¹ - M⁻¹) * M = M*J⁻¹*M - M*M⁻¹*M = M*J⁻¹*M - M.
    rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [show M * M⁻¹ * M = J + ε • (1 : Matrix _ _ _) by
      rw [hMM, Matrix.one_mul, hM_def]]
    -- Compute `M * J⁻¹ * M = J + 2ε•1 + ε²•J⁻¹`:
    have hMJM : M * J⁻¹ * M
        = J + ε • (1 : Matrix _ _ _) + ε • (1 : Matrix _ _ _) + (ε^2) • J⁻¹ := by
      simp only [hM_def, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
                 Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add]
      rw [hJJ, hJJ']
      simp only [Matrix.one_mul]
      rw [smul_smul, ← pow_two]
      abel
    rw [hMJM]
    abel
  -- Convert (M * X * M) PSD to X PSD via conjugation iff.
  -- M is symmetric (Hermitian), so star M = M.
  have hM_star : star M = M := hM.1
  have hMstarM : M * (J⁻¹ - M⁻¹) * star M = M * (J⁻¹ - M⁻¹) * M := by
    rw [hM_star]
  rw [← Matrix.IsUnit.posSemidef_star_right_conjugate_iff hM.isUnit, hMstarM, hKey]
  -- ε•1 + ε²•J⁻¹ is PSD.
  exact (Matrix.PosDef.one.smul hε).posSemidef.add
    (hJ.inv.smul (by positivity)).posSemidef

/-- **Posterior mean estimator** for the Gaussian shift experiment.

Given prior `π_τ = N(0, τ²I)` on `h ∈ Θk` and likelihood `X | h ~ N(h, J⁻¹)`,
the Bayes posterior is `h | X = x ~ N(posteriorMean J τ x, posteriorCov J τ)`,
where `posteriorMean J τ x = posteriorCov J τ · J · x` is linear in `x`.

This is the load-bearing linear estimator for the innovations representation
(`gaussianShift_innovations_repr`) — under the joint `(h, X) ~ π_τ ⊗ Plim`,
the random variable `g := h - posteriorMean J τ X` has marginal
`N(0, posteriorCov J τ)` AND is independent of `X`. -/
noncomputable def posteriorMean (J : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 _).symm ((posteriorCov J τ * J).mulVec ((WithLp.equiv 2 _) x))

/-- **Marginal of `X` under the joint Gaussian-shift experiment**.

For prior `h ~ N(0, τ²I)` and likelihood `X | h ~ N(h, J⁻¹)`, the marginal
distribution of `X` is `N(0, J⁻¹ + τ²I)` (mixture: `X = h + ε` with
`h ~ N(0, τ²I)` and `ε ~ N(0, J⁻¹)` independent). -/
noncomputable def marginalGaussianShift (J : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin k)) :=
  multivariateGaussian 0 (J⁻¹ + (τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))

/-- **Translation pushforward of multivariate Gaussian.**

`multivariateGaussian μ S = (multivariateGaussian 0 S).map (μ + ·)`. Direct
consequence of the Mathlib def `multivariateGaussian μ S = stdGaussian.map (fun x ↦ μ + sqrt(S) x)`
unfolded as `(stdGaussian.map (sqrt S)).map (μ + ·) = (multivariateGaussian 0 S).map (μ + ·)`.

Used by `gaussianShift_innovations_repr` to rewrite the conditional Gaussian
likelihood `N(h, J⁻¹)` as a translation of the noise law `N(0, J⁻¹)`. -/
lemma multivariateGaussian_eq_translate
    (μ : EuclideanSpace ℝ (Fin k)) (S : Matrix (Fin k) (Fin k) ℝ) :
    multivariateGaussian μ S
      = (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S).map (fun ε => μ + ε) := by
  unfold multivariateGaussian
  rw [Measure.map_map (measurable_const_add μ) (by fun_prop)]
  congr 1
  funext x
  simp

/-- **Shift CLM**: `(h, ε) ↦ (h, h + ε)` on `Θk × Θk`.

Pushes an independent product `(prior × noise) = N(0, τ²I) × N(0, J⁻¹)` to
the joint distribution of `(h, X = h + ε)` under the Gaussian-shift
experiment. Continuous-linear, so `IsGaussian.map` applies. -/
noncomputable def shiftCLM (k : ℕ) :
    EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
      →L[ℝ] EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)))
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))
      + ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)))

@[simp] lemma shiftCLM_apply (h ε : EuclideanSpace ℝ (Fin k)) :
    shiftCLM k (h, ε) = (h, h + ε) := rfl

/-- **Posterior CLM**: `(x, g) ↦ (g + posteriorMean J τ x, x)` on `Θk × Θk`.

Pushes an independent product `(marginal × posterior) = N(0, J⁻¹ + τ²I) ×
N(0, posteriorCov)` to the joint `(h, X)` distribution. Continuous-linear,
so `IsGaussian.map` applies.

The first component uses `matrixToEuclideanCLMRect (posteriorCov J τ * J)`
to express `posteriorMean(x) = (Σ_τ * J).mulVec x` as a CLM. -/
noncomputable def posteriorCLM (J : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) :
    EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
      →L[ℝ] EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) :=
  let M : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    matrixToEuclideanCLMRect (posteriorCov J τ * J)
  ContinuousLinearMap.prod
    (ContinuousLinearMap.snd ℝ _ _ + M.comp (ContinuousLinearMap.fst ℝ _ _))
    (ContinuousLinearMap.fst ℝ _ _)

@[simp] lemma posteriorCLM_apply (J : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (x g : EuclideanSpace ℝ (Fin k)) :
    posteriorCLM J τ (x, g) = (g + posteriorMean J τ x, x) := rfl

/-- `posteriorMean J τ` as a continuous linear map (= rectangular matrix CLM). -/
lemma posteriorMean_eq_clm (J : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) :
    (fun x : EuclideanSpace ℝ (Fin k) => posteriorMean J τ x)
      = matrixToEuclideanCLMRect (posteriorCov J τ * J) := rfl

/-- **Variance of a dual functional under multivariate Gaussian**.

For `μ = multivariateGaussian m S` on `EuclideanSpace ℝ (Fin k)` and
`L : StrongDual ℝ (EuclideanSpace ℝ (Fin k))`, the variance of `L`
under `μ` equals `vᵀ S v` where `v := (Riesz⁻¹) L` is the Riesz
representative of `L` in `EuclideanSpace ℝ (Fin k)`.

**Proof**: By `covarianceBilinDual_self_eq_variance`, `Var(L; μ) =
covarianceBilinDual μ L L`. By `toDual_symm_apply`, `L u = ⟨v, u⟩` where
`v := (toDual ℝ E).symm L`. So `Var(L; μ) = Var(⟨v, ·⟩; μ) = covarianceBilin μ v v`
by `covarianceBilin_self`. Finally `covarianceBilin (mvg m S) v v = v.ofLp ⬝ S v.ofLp`
by `covarianceBilin_multivariateGaussian`. -/
lemma variance_dual_multivariateGaussian
    (m : EuclideanSpace ℝ (Fin k)) {S : Matrix (Fin k) (Fin k) ℝ}
    (hS : S.PosSemidef) (L : StrongDual ℝ (EuclideanSpace ℝ (Fin k))) :
    variance L (multivariateGaussian m S)
      = ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm L).ofLp
          ⬝ᵥ S.mulVec
            ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm L).ofLp := by
  set v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm L with hv_def
  have h_inner : (⇑L : EuclideanSpace ℝ (Fin k) → ℝ) = fun u => inner ℝ v u := by
    funext u
    exact (InnerProductSpace.toDual_symm_apply (y := L) (x := u)).symm
  rw [show variance L (multivariateGaussian m S)
        = variance (fun u => inner ℝ v u) (multivariateGaussian m S) by
      conv_lhs => rw [show (⇑L : _ → ℝ) = fun u => inner ℝ v u from h_inner]]
  rw [← covarianceBilin_self IsGaussian.memLp_two_id v,
      covarianceBilin_multivariateGaussian hS]

/-- **Riesz of composition**: for `K : F →L[ℝ] ℝ` and `T : E →L[ℝ] F`, the Riesz
representative of `K.comp T` is the adjoint of `T` applied to the Riesz
representative of `K`.

The proof uses `ext_inner_left` + `real_inner_comm` +
`adjoint_inner_left` + `toDual_symm_apply`. -/
private lemma toDual_symm_comp {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K : F →L[ℝ] ℝ) (T : E →L[ℝ] F) :
    (InnerProductSpace.toDual ℝ E).symm (K.comp T)
      = (ContinuousLinearMap.adjoint T) ((InnerProductSpace.toDual ℝ F).symm K) := by
  apply ext_inner_left ℝ
  intro v
  rw [← real_inner_comm v, ← real_inner_comm v,
      InnerProductSpace.toDual_symm_apply,
      ContinuousLinearMap.adjoint_inner_left,
      InnerProductSpace.toDual_symm_apply]
  rfl

/-- **Joint pushforward equality** — substantive Bayesian-Gaussian core.

The two pushforward measures on `Θk × Θk` (both `IsGaussian`) agree:
- LHS: independent prior+noise pushed forward by `shiftCLM` (i.e., `(h, h+ε)`).
- RHS: independent marginal+posterior pushed forward by `posteriorCLM`
  (i.e., `(g + posteriorMean(x), x)`).

**Mathematical proof** via `IsGaussian.ext`:
1. Both `IsGaussian` on `Θk × Θk` (`IsGaussian.prod` + `isGaussian_map`).
2. Both means: `(0, 0)` — linear pushforward of zero-mean indep product.
3. Both covariance bilinear forms equal the block form
   `((u₁, u₂), (v₁, v₂)) ↦ τ²⟨u₁+u₂, v₁+v₂⟩ + ⟨J⁻¹ u₂, v₂⟩`
   (i.e., block matrix `[[τ²I, τ²I], [τ²I, J⁻¹+τ²I]]`).

LHS covariance: direct via `covarianceBilin_map` + adjoint `S* (u₁, u₂) =
(u₁+u₂, u₂)` + block-diag prod covariance.

RHS covariance: matrix algebra using `Σ_τ J = I - τ⁻²Σ_τ` (from
`Σ_τ⁻¹ = J + τ⁻²I`):
- (2,2): `M_τ = J⁻¹+τ²I` ✓.
- (1,2)=(2,1): `JΣ_τ M_τ = τ²I` (one rewrite via the key identity).
- (1,1): `JΣ_τ M_τ Σ_τ J + Σ_τ = τ²I` (via (1,2) + telescoping). -/
theorem joint_pushforward_eq
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ : ℝ} (hτ : 0 < τ) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
          ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹)).map (shiftCLM k)
      = ((marginalGaussianShift J τ).prod
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
            (posteriorCov J τ))).map (posteriorCLM J τ) := by
  -- Use `IsGaussian.ext_covarianceBilinDual` on Banach `Θk × Θk`.
  -- Mathlib's `IsGaussian.ext` requires `[InnerProductSpace ℝ E]`, which is NOT a
  -- default instance on `Θk × Θk` (it is installed only on `WithLp 2 (E × F)`).
  -- Use the more general `_covarianceBilinDual` form on Banach space `Θk × Θk` instead.
  --
  -- `[IsGaussian _]` instances for both LHS and RHS: by `IsGaussian.prod` on each
  -- `multivariateGaussian` factor + `isGaussian_map` for the CLM pushforward.
  -- Manual unfold: `marginalGaussianShift` is a non-transparent `def`, so we
  -- need to expose the underlying `multivariateGaussian` to trigger instance search.
  haveI hπ_X : IsGaussian (marginalGaussianShift J τ) := by
    unfold marginalGaussianShift; infer_instance
  refine IsGaussian.ext_covarianceBilinDual ?_ ?_
  · -- **Means equal**: both `((prod).map CLM)[id] = CLM (prod[id]) = CLM (0, 0) = (0, 0)`.
    -- Helper: prod of zero-mean Gaussians has zero mean.
    -- `∫ p, p ∂(μ.prod ν) = (∫ p, p.1 ∂μ.prod ν, ∫ p, p.2 ∂μ.prod ν)` by `integral_pair`,
    -- and each component reduces to single-Gaussian mean via `Measure.fst_prod` / `_snd_prod`.
    -- Helper: prod of zero-mean Gaussians has zero mean (`integral_pair` + projections).
    have h_prod_mean : ∀ (μ ν : Measure (EuclideanSpace ℝ (Fin k)))
        [IsGaussian μ] [IsGaussian ν]
        (_hμ : ∫ x, x ∂μ = (0 : EuclideanSpace ℝ (Fin k)))
        (_hν : ∫ x, x ∂ν = (0 : EuclideanSpace ℝ (Fin k))),
        ∫ p, p ∂(μ.prod ν)
          = (0 : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) := by
      intro μ ν _ _ hμ hν
      haveI : IsGaussian (μ.prod ν) := inferInstance
      have hint : Integrable (id : EuclideanSpace ℝ (Fin k)
          × EuclideanSpace ℝ (Fin k) → _) (μ.prod ν) := IsGaussian.integrable_id
      have h_pair : ∫ p, p ∂(μ.prod ν)
          = (∫ p, p.1 ∂(μ.prod ν), ∫ p, p.2 ∂(μ.prod ν)) :=
        integral_pair hint.fst hint.snd
      rw [h_pair]
      have h_fst : ∫ p, p.1 ∂(μ.prod ν) = ∫ x, x ∂μ := by
        have hmap : ∫ y, (id : _ → EuclideanSpace ℝ (Fin k)) y ∂(μ.prod ν).map Prod.fst
            = ∫ x, (id : _ → EuclideanSpace ℝ (Fin k)) (Prod.fst x) ∂(μ.prod ν) :=
          MeasureTheory.integral_map measurable_fst.aemeasurable
            (by exact (measurable_id.aestronglyMeasurable))
        simp only [id_eq] at hmap
        rw [show ((μ.prod ν).map Prod.fst) = μ from Measure.fst_prod] at hmap
        exact hmap.symm
      have h_snd : ∫ p, p.2 ∂(μ.prod ν) = ∫ x, x ∂ν := by
        have hmap : ∫ y, (id : _ → EuclideanSpace ℝ (Fin k)) y ∂(μ.prod ν).map Prod.snd
            = ∫ x, (id : _ → EuclideanSpace ℝ (Fin k)) (Prod.snd x) ∂(μ.prod ν) :=
          MeasureTheory.integral_map measurable_snd.aemeasurable
            (by exact (measurable_id.aestronglyMeasurable))
        simp only [id_eq] at hmap
        rw [show ((μ.prod ν).map Prod.snd) = ν from Measure.snd_prod] at hmap
        exact hmap.symm
      rw [h_fst, h_snd, hμ, hν]
      rfl
    -- LHS mean = (0, 0).
    have h_lhs_mean : ∫ p, p ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
            ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))).prod
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹)).map (shiftCLM k))
          = (0 : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) := by
      have hInt_prod : Integrable (id : EuclideanSpace ℝ (Fin k)
          × EuclideanSpace ℝ (Fin k) → _)
          ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
              ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹)) :=
        IsGaussian.integrable_id
      have hmap : ∫ y, y ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
              ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹)).map (shiftCLM k))
          = ∫ p, shiftCLM k p ∂((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
              ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹)) := by
        have := MeasureTheory.integral_map
          (μ := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
              ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹))
          (φ := shiftCLM k)
          (f := id)
          (shiftCLM k).continuous.measurable.aemeasurable
          measurable_id.aestronglyMeasurable
        simpa using this
      rw [hmap, (shiftCLM k).integral_comp_id_comm hInt_prod,
          h_prod_mean _ _ integral_id_multivariateGaussian
            integral_id_multivariateGaussian, (shiftCLM k).map_zero]
    -- RHS mean = (0, 0).
    have h_rhs_mean : ∫ p, p ∂(((marginalGaussianShift J τ).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
              (posteriorCov J τ))).map (posteriorCLM J τ))
          = (0 : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) := by
      have hInt_prod : Integrable (id : EuclideanSpace ℝ (Fin k)
          × EuclideanSpace ℝ (Fin k) → _)
          ((marginalGaussianShift J τ).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (posteriorCov J τ))) :=
        IsGaussian.integrable_id
      have hmap : ∫ y, y ∂(((marginalGaussianShift J τ).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
              (posteriorCov J τ))).map (posteriorCLM J τ))
          = ∫ p, posteriorCLM J τ p ∂((marginalGaussianShift J τ).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (posteriorCov J τ))) := by
        have := MeasureTheory.integral_map
          (μ := (marginalGaussianShift J τ).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (posteriorCov J τ)))
          (φ := posteriorCLM J τ)
          (f := id)
          (posteriorCLM J τ).continuous.measurable.aemeasurable
          measurable_id.aestronglyMeasurable
        simpa using this
      have hπ_X_mean : ∫ x, x ∂(marginalGaussianShift J τ)
          = (0 : EuclideanSpace ℝ (Fin k)) := by
        unfold marginalGaussianShift; exact integral_id_multivariateGaussian
      rw [hmap, (posteriorCLM J τ).integral_comp_id_comm hInt_prod,
          h_prod_mean _ _ hπ_X_mean integral_id_multivariateGaussian,
          (posteriorCLM J τ).map_zero]
    change ∫ p, p ∂_ = ∫ p, p ∂_
    rw [h_lhs_mean, h_rhs_mean]
  · -- **Covariance bilinear forms equal**: reduce via `toBilinForm_inj` +
    -- `ext_of_isSymm` to "variance equal at every dual functional L".
    rw [← ContinuousLinearMap.toBilinForm_inj]
    apply LinearMap.BilinForm.ext_of_isSymm
      isPosSemidef_covarianceBilinDual.isSymm
      isPosSemidef_covarianceBilinDual.isSymm
    intro L
    -- Goal: `(covarianceBilinDual LHS).toBilinForm L L = (covarianceBilinDual RHS).toBilinForm L
    -- L`.
    -- First reduce both diagonal applications to plain `covarianceBilinDual μ L L`,
    -- then to `variance L μ` via `covarianceBilinDual_self_eq_variance`.
    change covarianceBilinDual
          (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
                ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))).prod
              (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹)).map
            (shiftCLM k)) L L
        = covarianceBilinDual
            (((marginalGaussianShift J τ).prod
                (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
                  (posteriorCov J τ))).map (posteriorCLM J τ)) L L
    rw [covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id,
        covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id]
    -- **Goal**: `variance L LHS_measure = variance L RHS_measure`.
    -- Reduce via `variance_map` (push CLM into integrand) + `variance_dual_prod`
    -- (split prod measure variance via independence).
    rw [ProbabilityTheory.variance_map (L.continuous.measurable.aemeasurable)
          (shiftCLM k).continuous.measurable.aemeasurable,
        ProbabilityTheory.variance_map (L.continuous.measurable.aemeasurable)
          (posteriorCLM J τ).continuous.measurable.aemeasurable]
    -- Now `Var(L ∘ shiftCLM; prod_LHS) = Var(L ∘ posteriorCLM; prod_RHS)`.
    -- Bridge `L ∘ T` to `(L.comp T : StrongDual ℝ (Θk × Θk))` to invoke `variance_dual_prod`.
    have h_shift : (⇑L ∘ ⇑(shiftCLM k))
        = ⇑(L.comp (shiftCLM k) : StrongDual ℝ (EuclideanSpace ℝ (Fin k)
            × EuclideanSpace ℝ (Fin k))) := rfl
    have h_post : (⇑L ∘ ⇑(posteriorCLM J τ))
        = ⇑(L.comp (posteriorCLM J τ) : StrongDual ℝ (EuclideanSpace ℝ (Fin k)
            × EuclideanSpace ℝ (Fin k))) := rfl
    rw [h_shift, h_post]
    haveI hπ_X_prob : IsProbabilityMeasure (marginalGaussianShift J τ) := by
      unfold marginalGaussianShift; infer_instance
    rw [ProbabilityTheory.variance_dual_prod IsGaussian.memLp_two_id IsGaussian.memLp_two_id,
        ProbabilityTheory.variance_dual_prod IsGaussian.memLp_two_id IsGaussian.memLp_two_id]
    -- **Goal**: sum-of-variances equality.
    -- Reduce each `Var(K; multivariateGaussian m S)` via `variance_dual_multivariateGaussian`
    -- to matrix dot-product form `v ⬝ S.mulVec v` where `v` is Riesz representative of `K`.
    --
    -- For `marginalGaussianShift`, must unfold to `multivariateGaussian 0 (J⁻¹ + τ²•1)`
    -- before applying the helper.
    rw [show marginalGaussianShift J τ
          = multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
              (J⁻¹ + (τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ)) from rfl]
    rw [variance_dual_multivariateGaussian _
          (Matrix.PosDef.one.smul (by positivity : (0 : ℝ) < τ^2)).posSemidef _,
        variance_dual_multivariateGaussian _ hJ.inv.posSemidef _,
        variance_dual_multivariateGaussian _
          (hJ.inv.posSemidef.add (Matrix.PosDef.one.smul
            (by positivity : (0 : ℝ) < τ^2)).posSemidef) _,
        variance_dual_multivariateGaussian _
          (posteriorCov_posDef hJ hτ).posSemidef _]
    -- **Step 1: CLM identities for the 4 compositions** (factor out shift/posteriorCLM).
    -- These are pointwise CLM equalities; the corresponding Riesz reps then follow
    -- by `congr_arg`.
    have hCLM_LHS_inl : (L.comp (shiftCLM k)).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin k))
            (EuclideanSpace ℝ (Fin k)))
        = L.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin k))
            (EuclideanSpace ℝ (Fin k)))
          + L.comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k))
              (EuclideanSpace ℝ (Fin k))) := by
      ext h
      change L (shiftCLM k (h, 0)) = L (h, 0) + L (0, h)
      rw [shiftCLM_apply]
      have h1 : ((h, h + 0) : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
          = (h, 0) + (0, h) := by ext <;> simp
      rw [h1, map_add]
    have hCLM_LHS_inr : (L.comp (shiftCLM k)).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k))
            (EuclideanSpace ℝ (Fin k)))
        = L.comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k))
            (EuclideanSpace ℝ (Fin k))) := by
      ext ε
      change L (shiftCLM k (0, ε)) = L (0, ε)
      rw [shiftCLM_apply, zero_add]
    have hCLM_RHS_inr : (L.comp (posteriorCLM J τ)).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k))
            (EuclideanSpace ℝ (Fin k)))
        = L.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin k))
            (EuclideanSpace ℝ (Fin k))) := by
      ext g
      change L (posteriorCLM J τ (0, g)) = L (g, 0)
      rw [posteriorCLM_apply]
      -- (g + posteriorMean J τ 0, 0) = (g + 0, 0) = (g, 0)
      have h0 : posteriorMean J τ (0 : EuclideanSpace ℝ (Fin k)) = 0 := by
        unfold posteriorMean
        simp
      rw [h0, add_zero]
    have hCLM_RHS_inl : (L.comp (posteriorCLM J τ)).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin k))
            (EuclideanSpace ℝ (Fin k)))
        = (L.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin k))
            (EuclideanSpace ℝ (Fin k)))).comp
          (matrixToEuclideanCLMRect (posteriorCov J τ * J))
          + L.comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k))
              (EuclideanSpace ℝ (Fin k))) := by
      ext x
      change L (posteriorCLM J τ (x, 0)) = L (posteriorMean J τ x, 0) + L (0, x)
      rw [posteriorCLM_apply]
      -- (0 + posteriorMean J τ x, x) = (posteriorMean J τ x, x)
      rw [zero_add]
      have h1 : L (posteriorMean J τ x, x)
          = L ((posteriorMean J τ x, 0) + (0, x)) := by congr 1; ext <;> simp
      rw [h1, map_add]
    -- **Step 2**: Substitute CLM identities into Riesz reps + linearize via `map_add` /
    -- `toDual_symm_comp` (Riesz of composition).
    -- Set abbreviations for the outer Riesz reps `u₁ := (toDual.symm) (L.comp inl)` etc.
    set u₁ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm
        (L.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin k))
          (EuclideanSpace ℝ (Fin k)))) with hu₁_def
    set u₂ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm
        (L.comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k))
          (EuclideanSpace ℝ (Fin k)))) with hu₂_def
    -- Riesz expansions:
    -- v₁ := (toDual.symm) ((L.comp shiftCLM).comp inl) = u₁ + u₂.
    have hv₁ : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm
            ((L.comp (shiftCLM k)).comp
              (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin k))
                (EuclideanSpace ℝ (Fin k))))
        = u₁ + u₂ := by
      rw [hCLM_LHS_inl]
      exact map_add _ _ _
    -- v₂ := (toDual.symm) ((L.comp shiftCLM).comp inr) = u₂.
    have hv₂ : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm
            ((L.comp (shiftCLM k)).comp
              (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k))
                (EuclideanSpace ℝ (Fin k))))
        = u₂ := by rw [hCLM_LHS_inr]
    -- v₃ := (toDual.symm) ((L.comp posteriorCLM).comp inl)
    --     = (matrixToEuclideanCLMRect (posteriorCov J τ * J)).adjoint u₁ + u₂.
    have hv₃ : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm
            ((L.comp (posteriorCLM J τ)).comp
              (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin k))
                (EuclideanSpace ℝ (Fin k))))
        = (ContinuousLinearMap.adjoint
            (matrixToEuclideanCLMRect (posteriorCov J τ * J))) u₁ + u₂ := by
      rw [hCLM_RHS_inl, map_add, ← hu₂_def]
      congr 1
      exact toDual_symm_comp _ _
    -- v₄ := (toDual.symm) ((L.comp posteriorCLM).comp inr) = u₁.
    have hv₄ : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm
            ((L.comp (posteriorCLM J τ)).comp
              (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k))
                (EuclideanSpace ℝ (Fin k))))
        = u₁ := by rw [hCLM_RHS_inr]
    rw [hv₁, hv₂, hv₃, hv₄]
    -- **Step 3**: matrix quadratic form equality.
    -- Substitute `M.adjoint` via `matrixToEuclideanCLMRect_adjoint` + symmetry of `Sτ * J`.
    rw [show (ContinuousLinearMap.adjoint
            (matrixToEuclideanCLMRect (posteriorCov J τ * J))) u₁
          = matrixToEuclideanCLMRect ((posteriorCov J τ * J).transpose) u₁ by
        rw [matrixToEuclideanCLMRect_adjoint]]
    rw [WithLp.ofLp_add, WithLp.ofLp_add, ofLp_matrixToEuclideanCLMRect]
    -- **Final matrix quadratic form equality**.
    -- Goal at this point:
    --   (u₁.ofLp + u₂.ofLp) ⬝ᵥ (τ²•1).mulVec (u₁.ofLp + u₂.ofLp) + u₂.ofLp ⬝ᵥ J⁻¹.mulVec u₂.ofLp
    --   = ((Sτ*J)ᵀ.mulVec u₁.ofLp + u₂.ofLp)
    --       ⬝ᵥ (J⁻¹+τ²•1).mulVec ((Sτ*J)ᵀ.mulVec u₁.ofLp + u₂.ofLp)
    --     + u₁.ofLp ⬝ᵥ Sτ.mulVec u₁.ofLp
    --
    -- Strategy: prove the matrix identities below, expand both sides bilinearly,
    -- and match the three coefficient blocks (u₁⬝(·)u₁, u₁⬝(·)u₂, u₂⬝(·)u₂):
    --   K1a: J*Sτ + τ⁻²•Sτ = 1     [from (J + τ⁻²•1)*Sτ = 1]
    --   K1b: Sτ*J + τ⁻²•Sτ = 1     [from Sτ*(J + τ⁻²•1) = 1]
    --   K2:  Sτ*J*(J⁻¹+τ²•1) = τ²•1   [from K1b + algebra]
    --   K3:  (Sτ*J)ᵀ = J*Sτ        [symmetry of Sτ, J]
    --   K4:  (Sτ*J)*Mε*(Sτ*J)ᵀ + Sτ = τ²•1  [from K2, K3, K1a]
    -- Block matches (LHS coef = RHS coef):
    --   (1,1):  τ²•1 = K4
    --   (1,2):  τ²•1 = (Sτ*J)*Mε   (= K2)
    --   (2,2):  τ²•1 + J⁻¹ = Mε    (= add_comm)
    set Sτ : Matrix (Fin k) (Fin k) ℝ := posteriorCov J τ with hSτ_def
    set Mε : Matrix (Fin k) (Fin k) ℝ
        := J⁻¹ + (τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ) with hMε_def
    -- Matrix algebra setup.
    have hτ2_pos : (0 : ℝ) < τ^2 := by positivity
    have hτ2_ne : (τ^2 : ℝ) ≠ 0 := ne_of_gt hτ2_pos
    have hJε_PosDef : (J + (τ^2)⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef :=
      hJ.add (Matrix.PosDef.one.smul (by positivity))
    have hJε_unit_det : IsUnit (J + (τ^2)⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hJε_PosDef.isUnit
    have hJ_unit_det : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).mp hJ.isUnit
    -- Two-sided inverse of (J + τ⁻²•1).
    have hSτ_inv_R : Sτ * (J + (τ^2)⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) = 1 := by
      change (J + (τ^2)⁻¹ • (1 : Matrix _ _ _))⁻¹ * _ = 1
      exact Matrix.nonsing_inv_mul _ hJε_unit_det
    have hSτ_inv_L : (J + (τ^2)⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) * Sτ = 1 := by
      change _ * (J + (τ^2)⁻¹ • (1 : Matrix _ _ _))⁻¹ = 1
      exact Matrix.mul_nonsing_inv _ hJε_unit_det
    -- K1a: J*Sτ + τ⁻²•Sτ = 1.
    have hK1a : J * Sτ + (τ^2)⁻¹ • Sτ = 1 := by
      have := hSτ_inv_L
      rwa [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at this
    -- K1b: Sτ*J + τ⁻²•Sτ = 1.
    have hK1b : Sτ * J + (τ^2)⁻¹ • Sτ = 1 := by
      have := hSτ_inv_R
      rwa [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at this
    have hSτJ_eq : Sτ * J = 1 - (τ^2)⁻¹ • Sτ := eq_sub_of_add_eq hK1b
    have hJSτ_eq : J * Sτ = 1 - (τ^2)⁻¹ • Sτ := eq_sub_of_add_eq hK1a
    -- K3: (Sτ*J)ᵀ = J*Sτ via symmetry.
    have hJ_symm : J.transpose = J := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hJ.isHermitian
    have hSτ_symm : Sτ.transpose = Sτ := by
      rw [hSτ_def, ← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact (posteriorCov_posDef hJ hτ).isHermitian
    have hJinv_symm : J⁻¹.transpose = J⁻¹ := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hJ.inv.isHermitian
    have hMε_symm : Mε.transpose = Mε := by
      rw [hMε_def, Matrix.transpose_add, hJinv_symm, Matrix.transpose_smul,
          Matrix.transpose_one]
    have hτ21_symm : ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ)).transpose
        = (τ^2) • (1 : Matrix _ _ _) := by
      rw [Matrix.transpose_smul, Matrix.transpose_one]
    have hSτJ_T : (Sτ * J).transpose = J * Sτ := by
      rw [Matrix.transpose_mul, hSτ_symm, hJ_symm]
    -- K2: (Sτ*J)*Mε = τ²•1.
    have hJJ_inv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ_unit_det
    have hK2 : Sτ * J * Mε = (τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
      rw [hMε_def, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc,
          hJJ_inv, Matrix.mul_one, hSτJ_eq, smul_sub, smul_smul,
          show (τ^2 : ℝ) * (τ^2)⁻¹ = 1 from mul_inv_cancel₀ hτ2_ne, one_smul]
      abel
    -- K4: (Sτ*J)*Mε*(Sτ*J)ᵀ + Sτ = τ²•1.
    have hK4 : (Sτ * J) * Mε * (Sτ * J).transpose + Sτ
        = (τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
      rw [show Sτ * J * Mε * (Sτ * J).transpose
            = ((τ^2) • (1 : Matrix _ _ _)) * (Sτ * J).transpose from by rw [hK2],
          Matrix.smul_mul, Matrix.one_mul, hSτJ_T, hJSτ_eq, smul_sub, smul_smul,
          show (τ^2 : ℝ) * (τ^2)⁻¹ = 1 from mul_inv_cancel₀ hτ2_ne, one_smul]
      abel
    -- (2,2) block: τ²•1 + J⁻¹ = Mε.
    have hM22 : (τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ) + J⁻¹ = Mε := by
      rw [hMε_def]; abel
    -- Bilinear absorption helpers.
    -- (Aᵀ.mulVec v) ⬝ᵥ w = v ⬝ᵥ A.mulVec w  (adjoint move).
    have hadj : ∀ (A : Matrix (Fin k) (Fin k) ℝ) (v w : Fin k → ℝ),
        A.transpose.mulVec v ⬝ᵥ w = v ⬝ᵥ A.mulVec w := fun A v w => by
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    -- Symmetric quadratic expansion: (u + v) ⬝ A (u + v) = u Au + 2 (u Av) + v Av.
    have hquad : ∀ {A : Matrix (Fin k) (Fin k) ℝ} (_hA : A.transpose = A)
        (u v : Fin k → ℝ),
        (u + v) ⬝ᵥ A.mulVec (u + v)
          = u ⬝ᵥ A.mulVec u + 2 * (u ⬝ᵥ A.mulVec v) + v ⬝ᵥ A.mulVec v := by
      intro A hA u v
      rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
      have hcross : v ⬝ᵥ A.mulVec u = u ⬝ᵥ A.mulVec v := by
        rw [← hadj A v u, hA]
        exact dotProduct_comm _ _
      linarith [hcross]
    -- Apply hquad to the LHS and RHS quadratic terms.
    rw [hquad hτ21_symm u₁.ofLp u₂.ofLp]
    rw [hquad hMε_symm ((Sτ * J).transpose.mulVec u₁.ofLp) u₂.ofLp]
    -- Absorb (Sτ*J)ᵀ in the diagonal RHS term.
    rw [show (Sτ * J).transpose.mulVec u₁.ofLp
            ⬝ᵥ Mε.mulVec ((Sτ * J).transpose.mulVec u₁.ofLp)
          = u₁.ofLp ⬝ᵥ ((Sτ * J) * Mε * (Sτ * J).transpose).mulVec u₁.ofLp from by
        rw [hadj (Sτ * J) u₁.ofLp _, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]]
    -- Absorb (Sτ*J)ᵀ in the cross RHS term.
    rw [show (Sτ * J).transpose.mulVec u₁.ofLp ⬝ᵥ Mε.mulVec u₂.ofLp
          = u₁.ofLp ⬝ᵥ ((Sτ * J) * Mε).mulVec u₂.ofLp from by
        rw [hadj (Sτ * J) u₁.ofLp _, Matrix.mulVec_mulVec]]
    -- Final reduction via three scalar identities (block matching).
    have hDiag : u₁.ofLp ⬝ᵥ ((Sτ * J) * Mε * (Sτ * J).transpose).mulVec u₁.ofLp
        + u₁.ofLp ⬝ᵥ Sτ.mulVec u₁.ofLp
        = u₁.ofLp ⬝ᵥ ((τ^2) • (1 : Matrix _ _ _)).mulVec u₁.ofLp := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, hK4]
    have hCross : u₁.ofLp ⬝ᵥ ((Sτ * J) * Mε).mulVec u₂.ofLp
        = u₁.ofLp ⬝ᵥ ((τ^2) • (1 : Matrix _ _ _)).mulVec u₂.ofLp := by
      rw [hK2]
    have hLhsU2 : u₂.ofLp ⬝ᵥ ((τ^2) • (1 : Matrix _ _ _)).mulVec u₂.ofLp
        + u₂.ofLp ⬝ᵥ J⁻¹.mulVec u₂.ofLp
        = u₂.ofLp ⬝ᵥ Mε.mulVec u₂.ofLp := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, hM22]
    linarith [hDiag, hCross, hLhsU2]

/-- **Innovations representation, post-translation form.**

Iterated-integral version of `joint_pushforward_eq`. The plumbing reduces
each side to `∫⁻ p ∂measure, f p.1 p.2` via Fubini (`lintegral_prod`) +
`lintegral_map`; the substantive content is the measure equality
`joint_pushforward_eq`.

This is the post-translation form of the innovations rep:
`mvg h J⁻¹` has been replaced by `(mvg 0 J⁻¹).map (h + ·)` (handled in
the public-facing `gaussianShift_innovations_repr`). -/
private theorem joint_gaussian_innovations_eq
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ : ℝ} (hτ : 0 < τ)
    (f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) :
    ∫⁻ h, ∫⁻ ε, f h (h + ε)
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
            ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ)))
      = ∫⁻ x, ∫⁻ g, f (g + posteriorMean J τ x) x
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
                (posteriorCov J τ))
            ∂(marginalGaussianShift J τ) := by
  -- Notation.
  set π_τ : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
      ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ)) with hπ_τ
  set ν_J : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹ with hν_J
  set ν_S : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (posteriorCov J τ) with hν_S
  set π_X : Measure (EuclideanSpace ℝ (Fin k)) := marginalGaussianShift J τ with hπ_X
  -- Measurability: `f` and `(p ↦ f p.1 p.2) = Function.uncurry f`.
  have hfu : Measurable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
      => f p.1 p.2) := hf
  -- LHS plumbing: Fubini → product measure → pushforward via `shiftCLM`.
  have h_LHS : ∫⁻ h, ∫⁻ ε, f h (h + ε) ∂ν_J ∂π_τ
      = ∫⁻ p, f p.1 p.2 ∂((π_τ.prod ν_J).map (shiftCLM k)) := by
    -- Step 1: collapse iterated integral to product-measure integral.
    have h_meas_inner : Measurable (fun p : EuclideanSpace ℝ (Fin k)
        × EuclideanSpace ℝ (Fin k) => f p.1 (p.1 + p.2)) := by fun_prop
    rw [← MeasureTheory.lintegral_prod _ h_meas_inner.aemeasurable]
    -- Step 2: identify with pushforward via `shiftCLM`.
    rw [lintegral_map hfu (shiftCLM k).continuous.measurable]
    rfl
  -- RHS plumbing: Fubini → product measure → pushforward via `posteriorCLM`.
  have h_RHS : ∫⁻ x, ∫⁻ g, f (g + posteriorMean J τ x) x ∂ν_S ∂π_X
      = ∫⁻ p, f p.1 p.2 ∂((π_X.prod ν_S).map (posteriorCLM J τ)) := by
    have hMmeas : Measurable (fun x : EuclideanSpace ℝ (Fin k) => posteriorMean J τ x) :=
      (matrixToEuclideanCLMRect (posteriorCov J τ * J)).continuous.measurable
    have h_meas_inner : Measurable (fun p : EuclideanSpace ℝ (Fin k)
        × EuclideanSpace ℝ (Fin k) => f (p.2 + posteriorMean J τ p.1) p.1) := by
      fun_prop
    rw [← MeasureTheory.lintegral_prod _ h_meas_inner.aemeasurable]
    rw [lintegral_map hfu (posteriorCLM J τ).continuous.measurable]
    rfl
  rw [h_LHS, h_RHS, joint_pushforward_eq hJ hτ]

/-- **Innovations representation for the Gaussian shift experiment.**

Under the joint `(h, X) ~ N(0, τ²I) ⊗ N(h, J⁻¹)` (prior + likelihood), the
random variable `g := h - posteriorMean J τ X` has marginal
`N(0, posteriorCov J τ)` AND is **independent of X** (whose marginal is
`marginalGaussianShift J τ = N(0, J⁻¹ + τ²I)`). The substitution
`(h, X) ↔ (g + posteriorMean J τ X, X)` (linear bijection) gives the
iterated-integral identity below.

**This is the load-bearing Bayesian-Gaussian fact** for closing
`avgRisk_gaussianShift_ge_bayesRiskAtTau`.

**Proof structure**: One step
of `multivariateGaussian_eq_translate` rewrites the inner Gaussian likelihood
`N(h, J⁻¹) = (N(0, J⁻¹)).map (h + ·)` and `lintegral_map` reduces LHS to its
post-translation form. The substantive Bayesian-Gaussian content (joint
pushforward equality on `Θk × Θk` via `IsGaussian.ext`) is delegated to
`joint_gaussian_innovations_eq`. -/
theorem gaussianShift_innovations_repr
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ : ℝ} (hτ : 0 < τ)
    (f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) :
    ∫⁻ h, ∫⁻ x, f h x ∂(multivariateGaussian h J⁻¹)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
            ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ)))
      = ∫⁻ x, ∫⁻ g, f (g + posteriorMean J τ x) x
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
                (posteriorCov J τ))
            ∂(marginalGaussianShift J τ) := by
  -- **Step 1**: Rewrite inner Gaussian likelihood as translation pushforward.
  -- `N(h, J⁻¹) = (N(0, J⁻¹)).map (h + ·)`, then `lintegral_map`.
  have h_translate : ∀ h : EuclideanSpace ℝ (Fin k),
      ∫⁻ x, f h x ∂(multivariateGaussian h J⁻¹)
        = ∫⁻ ε, f h (h + ε)
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := fun h => by
    rw [multivariateGaussian_eq_translate h J⁻¹]
    have hf_h : Measurable (fun x => f h x) := by fun_prop
    rw [lintegral_map hf_h (measurable_const_add h)]
  simp_rw [h_translate]
  -- **Step 2**: Apply substantive joint Gaussian identification.
  exact joint_gaussian_innovations_eq hJ hτ f hf

/-- **Easy direction of Step D** — `bayesRiskAtTau ≤ ∫ L dN(0, A J⁻¹ Aᵀ)`.

For each `τ > 0`, the Bayes risk under prior `π_τ` is bounded above by the
target Gaussian integral. Direct application of Anderson's PSD-monotone form
(`gaussian_lintegral_mono_of_psd_le`) using `posteriorCov_le_inv`. -/
lemma bayesRiskAtTau_le_target
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    (A : Matrix (Fin d) (Fin k) ℝ)
    {L : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hL_bowl : BowlShaped L)
    {τ : ℝ} (hτ : 0 < τ) :
    bayesRiskAtTau J A L τ
      ≤ ∫⁻ y, L y ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
                    (A * J⁻¹ * A.transpose)) := by
  -- Σ_τ ≼ J⁻¹ ⇒ A * Σ_τ * Aᵀ ≼ A * J⁻¹ * Aᵀ ⇒ ∫ L dN(0, smaller) ≤ ∫ L dN(0, larger).
  unfold bayesRiskAtTau
  apply gaussian_lintegral_mono_of_psd_le
  · -- A * posteriorCov J τ * Aᵀ PosSemidef
    have hP : (posteriorCov J τ).PosDef := posteriorCov_posDef hJ hτ
    have := hP.posSemidef.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  · -- A * J⁻¹ * Aᵀ PosSemidef
    have hJinv : J⁻¹.PosDef := hJ.inv
    have := hJinv.posSemidef.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  · -- (A * J⁻¹ * Aᵀ - A * posteriorCov J τ * Aᵀ) PosSemidef
    have h_diff : A * J⁻¹ * A.transpose - A * posteriorCov J τ * A.transpose
        = A * (J⁻¹ - posteriorCov J τ) * A.transpose := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [h_diff]
    have h_psd : (J⁻¹ - posteriorCov J τ).PosSemidef := posteriorCov_le_inv hJ hτ
    have := h_psd.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  · exact hL_bowl

/-- **Matrix tendsto: `posteriorCov J τ → J⁻¹` along `τ → ∞`**.

For PosDef `J` and the sequence `τ_n := (n + 1 : ℝ)`, the posterior covariance
`(J + (τ_n²)⁻¹ • I)⁻¹` converges entrywise to `J⁻¹` as `n → ∞`. Used by Step D's
hard direction (sequentialization step). -/
lemma posteriorCov_tendsto_inv {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef) :
    Tendsto (fun n : ℕ => posteriorCov J ((n : ℝ) + 1)) atTop (𝓝 J⁻¹) := by
  -- Step 1: `(n : ℝ) + 1 → ∞` as `n → ∞`.
  have h_n_top : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n; linarith
  -- Step 2: `((n+1)²)⁻¹ → 0`.
  have h_eps : Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) atTop (𝓝 0) := by
    have h_sq_top : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop :=
      (Filter.tendsto_pow_atTop (n := 2) (by decide)).comp h_n_top
    exact tendsto_inv_atTop_zero.comp h_sq_top
  -- Step 3: Inner: `J + ((n+1)²)⁻¹ • 1 → J` entrywise.
  have h_inner : Tendsto (fun n : ℕ => J + (((n : ℝ) + 1) ^ 2)⁻¹ • (1 : Matrix _ _ _))
      atTop (𝓝 J) := by
    have h_smul : Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))
        atTop (𝓝 ((0 : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ))) :=
      h_eps.smul_const _
    have h_add :
        Tendsto (fun n : ℕ => J + (((n : ℝ) + 1) ^ 2)⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))
          atTop (𝓝 (J + (0 : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ))) :=
      (tendsto_const_nhds (x := J)).add h_smul
    simpa using h_add
  -- Step 4: Matrix inverse continuous at J (det J is a unit).
  have h_det_unit : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ.isUnit
  have h_inv_cont : ContinuousAt Inv.inv J := by
    apply continuousAt_matrix_inv
    -- `Ring.inverse` continuous at `J.det` ∈ Units.
    have h_unit : IsUnit J.det := h_det_unit
    have := NormedRing.inverse_continuousAt h_unit.unit
    simpa [IsUnit.unit_spec] using this
  unfold posteriorCov
  exact h_inv_cont.tendsto.comp h_inner

/-- **Hard direction of Step D** — `∫ L dN(0, A J⁻¹ Aᵀ) ≤ ⨆_τ bayesRiskAtTau`,
under `LowerSemicontinuous L`.

The reverse direction. Requires `LowerSemicontinuous L`: without it, an
absolute-continuity (AC) argument for the limit Gaussian is needed (the
"L = lscEnvelope L AE w.r.t. target" bridge), which uses
`multivariateGaussian_frontier_eq_zero_of_convex`.

**Proof structure**:

1. **Sequentialization** (`posteriorCov_tendsto_inv`): `τ_n := (n+1 : ℝ)`,
   `posteriorCov J τ_n → J⁻¹` entrywise as `n → ∞`. Uses
   `continuousAt_matrix_inv` at PosDef `J`.

2. **Matrix product tendsto**: `A * posteriorCov J τ_n * Aᵀ → A * J⁻¹ * Aᵀ`
   by continuity of matrix multiplication.

3. **Weak convergence** (uses `multivariateGaussian_weakly_tendsto_of_seq`):
   `mvgPM 0 (A Σ_{τ_n} Aᵀ) → mvgPM 0 (A J⁻¹ Aᵀ)` weakly.

4. **Open-set Portmanteau** (`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`,
   Mathlib): for any open `G`, `target G ≤ liminf_n perturbed_n G`.

5. **LSC integral inequality** via truncation: for each `M : ℕ`, the
   bounded lsc loss `L_M := L ⊓ M` satisfies (after `.toReal` bridging)
   `∫⁻ L_M d(target) ≤ liminf_n ∫⁻ L_M d(perturbed_n)` by
   `lintegral_le_liminf_lintegral_of_lsc_of_forall_isOpen_measure_le_liminf_measure`
   (`PortmanteauLscBridge`).

6. **MCT lift to general lsc `L`**: `L = sup_M L_M` pointwise; MCT on both
   sides + Step 5 gives `∫⁻ L d(target) ≤ liminf_n ∫⁻ L d(perturbed_n)`.

7. **liminf ≤ sup**: `liminf_n ≤ sup_n bayesRiskAtTau τ_n ≤ ⨆ τ ∈ Ioi 0`.

The `hL_lsc` hypothesis is a real restriction. Common bowl-shaped losses
(norms, indicators of open complement) ARE lsc, so the practical scope is
preserved. The unconditional form requires the singular-PSD `S ≠ 0` branch
(Mathlib subspace Haar). -/
lemma target_le_iSup_bayesRiskAtTau
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (L : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hL_lsc : LowerSemicontinuous L) :
    ∫⁻ y, L y ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
                (A * J⁻¹ * A.transpose))
      ≤ ⨆ τ ∈ Set.Ioi (0 : ℝ), bayesRiskAtTau J A L τ := by
  -- **Step 1**: matrix sequence `posteriorCov J (n+1) → J⁻¹` (helper).
  have h_post_lim : Tendsto (fun n : ℕ => posteriorCov J ((n : ℝ) + 1)) atTop (𝓝 J⁻¹) :=
    posteriorCov_tendsto_inv hJ
  -- **Step 2**: `A * posteriorCov J τ_n * Aᵀ → A * J⁻¹ * Aᵀ` (matrix product continuous).
  have h_S_lim : Tendsto
      (fun n : ℕ => A * posteriorCov J ((n : ℝ) + 1) * A.transpose)
      atTop (𝓝 (A * J⁻¹ * A.transpose)) := by
    have h_left : Tendsto (fun n : ℕ => A * posteriorCov J ((n : ℝ) + 1))
        atTop (𝓝 (A * J⁻¹)) :=
      (continuous_const.matrix_mul continuous_id).continuousAt.tendsto.comp h_post_lim
    exact (continuous_id.matrix_mul continuous_const).continuousAt.tendsto.comp h_left
  -- **Step 3**: each `A * posteriorCov J τ_n * Aᵀ` is PosSemidef.
  have h_S_psd : ∀ᶠ n : ℕ in atTop,
      (A * posteriorCov J ((n : ℝ) + 1) * A.transpose).PosSemidef := by
    refine Filter.Eventually.of_forall fun n => ?_
    have hτ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hP : (posteriorCov J ((n : ℝ) + 1)).PosDef := posteriorCov_posDef hJ hτ
    have := hP.posSemidef.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  -- **Step 4**: target covariance is PosSemidef.
  have h_target_psd : (A * J⁻¹ * A.transpose).PosSemidef := by
    have := hJ.inv.posSemidef.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  -- **Step 5**: weak convergence of probability measures via `_weakly_tendsto_of_seq`.
  have h_weak : Tendsto (fun n : ℕ => multivariateGaussianPM (0 : EuclideanSpace ℝ (Fin d))
        (A * posteriorCov J ((n : ℝ) + 1) * A.transpose))
      atTop (𝓝 (multivariateGaussianPM (0 : EuclideanSpace ℝ (Fin d))
        (A * J⁻¹ * A.transpose))) :=
    multivariateGaussian_weakly_tendsto_of_seq h_target_psd h_S_psd h_S_lim
  -- **Step 6**: open-set Portmanteau bound (Mathlib).
  have h_opens : ∀ G : Set (EuclideanSpace ℝ (Fin d)), IsOpen G →
      (multivariateGaussianPM (0 : EuclideanSpace ℝ (Fin d))
        (A * J⁻¹ * A.transpose) : Measure _) G ≤ atTop.liminf
        (fun n : ℕ => (multivariateGaussianPM (0 : EuclideanSpace ℝ (Fin d))
          (A * posteriorCov J ((n : ℝ) + 1) * A.transpose) : Measure _) G) :=
    fun G hG => MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto h_weak hG
  -- **Step 7**: LSC integral inequality `∫⁻ L d(target) ≤ liminf ∫⁻ L d(perturbed)`.
  -- ENNReal-valued LSC Portmanteau bridge: `f_lsc + h_opens ⇒ liminf-lintegral`.
  -- Uses `lintegral_le_liminf_lintegral_of_lsc_ennreal_of_forall_isOpen_measure_le_liminf_measure`
  -- from `ForMathlib/PortmanteauLscBridge.lean` (parallel to its ℝ-valued sibling,
  -- bridged via `ENNReal.truncateToReal`).
  have h_lsc_portmanteau :
      ∫⁻ y, L y ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
                  (A * J⁻¹ * A.transpose))
        ≤ atTop.liminf (fun n : ℕ =>
            ∫⁻ y, L y ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
              (A * posteriorCov J ((n : ℝ) + 1) * A.transpose))) :=
    lintegral_le_liminf_lintegral_of_lsc_ennreal_of_forall_isOpen_measure_le_liminf_measure
      hL_lsc h_opens
  -- **Step 8**: liminf ≤ ⨆ τ ∈ Ioi 0, bayesRiskAtTau τ.
  refine h_lsc_portmanteau.trans ?_
  -- Each term is ≤ ⨆ τ; in CompleteLattice (ENNReal), liminf ≤ frequent-bound.
  refine Filter.liminf_le_of_frequently_le' (Filter.Eventually.frequently ?_)
  refine Filter.Eventually.of_forall fun n => ?_
  have hτ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact le_iSup₂_of_le ((n : ℝ) + 1) hτ le_rfl

/-- **Sup over flat-prior parameter recovers the target Gaussian integral**.

`⨆_{τ > 0} bayesRiskAtTau J A L τ = ∫ L dN(0, A J⁻¹ Aᵀ)`.

**Proof**: `le_antisymm` of the two named directions
`bayesRiskAtTau_le_target` (easy, via Anderson PSD-monotone + `posteriorCov_le_inv`)
and `target_le_iSup_bayesRiskAtTau` (hard, via Portmanteau lsc bridge,
closed unconditionally for lsc `L`).

**Crucial dependencies**:
- `gaussian_lintegral_mono_of_psd_le` (Anderson PSD-monotone) — easy direction
- `multivariateGaussian_weakly_tendsto_of_seq` (Lévy weak continuity) — hard direction
- `lintegral_le_liminf_lintegral_of_lsc_ennreal_of_forall_isOpen_measure_le_liminf_measure`
  (Portmanteau lsc bridge, ENNReal-valued) — hard direction
- `posteriorCov_le_inv` (matrix algebra) — easy direction

This is the **single largest direct consumer of Anderson's PSD-monotone form**
in the entire 8.11 proof. -/
theorem gaussianShift_bayes_risk_sup_eq_target
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (L : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hL_bowl : BowlShaped L)
    (hL_lsc : LowerSemicontinuous L) :
    ⨆ τ ∈ Set.Ioi (0 : ℝ), bayesRiskAtTau J A L τ
      = ∫⁻ y, L y ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
                    (A * J⁻¹ * A.transpose)) :=
  le_antisymm
    (iSup_le fun _ => iSup_le fun hτ => bayesRiskAtTau_le_target hJ A hL_bowl hτ)
    (target_le_iSup_bayesRiskAtTau hJ A L hL_lsc)

/-- **vdV §8.4 Proposition 8.6, kernel form**.

On the Gaussian-shift limit experiment with prior on `h` of weight `1` at each
`h ∈ ℝ^k` (via the finite-prior + sup-lift) and likelihood
`X | h ~ multivariateGaussian h J⁻¹`, for **any** Markov kernel
`κ : Kernel (ℝ^k) (ℝ^d)` the supremum over shifts of the L-risk dominates the
target Gaussian-shift integral with the canonical Bayes-optimal covariance
`ψDotMat · J⁻¹ · ψDotMatᵀ`.

This is the kernel form of vdV §8.4 Proposition 8.6:
the lower bound on Bayes risk in the limit experiment, expressed directly as a
sup over h of the shift-translated L-integral against the data kernel composed
with `κ`.

Used by `localAsymptoticRisk_ge_target` to bridge from the
Gaussian-shift limit-side Bayes lower bound to the localAsymptoticRisk target. -/
theorem bowl_shaped_loss_risk_kernel_form
    {k d : ℕ} (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (ψDot : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin d))
    (hψDot_meas : Measurable ψDot)
    (ψDotMat : Matrix (Fin d) (Fin k) ℝ)
    (h_ψDot_mat : ∀ h : EuclideanSpace ℝ (Fin k),
      ψDot h = (WithLp.equiv 2 _).symm (ψDotMat.mulVec ((WithLp.equiv 2 _) h)))
    (L : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hL_meas : Measurable L)
    (hL_bowl : BowlShaped L) (hL_lsc : LowerSemicontinuous L)
    (κ : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel κ] :
    (⨆ h : EuclideanSpace ℝ (Fin k),
        ∫⁻ y, L (y - ψDot h)
          ∂((multivariateGaussian h J⁻¹).bind κ))
      ≥ ∫⁻ y, L y ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (ψDotMat * J⁻¹ * ψDotMat.transpose)) := by
  -- Per-kernel risk integrand: `R(h) := ∫⁻ y, L(y - ψDot h) ∂((mvg h J⁻¹).bind κ)`.
  let R : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ :=
    fun h => ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ)
  -- Strategy: for each `τ > 0`, show `bayesRiskAtTau J ψDotMat L τ ≤ ⨆ h, R h`.
  -- Then `target = ⨆_{τ > 0} bayesRiskAtTau τ ≤ ⨆ h, R h` via Step D.
  -- Compose with `gaussianShift_bayes_risk_sup_eq_target`.
  rw [ge_iff_le, ← gaussianShift_bayes_risk_sup_eq_target hJ ψDotMat L hL_bowl hL_lsc]
  -- Reduce to: ∀ τ > 0, `bayesRiskAtTau J ψDotMat L τ ≤ ⨆ h, R h`.
  refine iSup_le fun τ => iSup_le fun (hτ : (0 : ℝ) < τ) => ?_
  change bayesRiskAtTau J ψDotMat L τ ≤ ⨆ h, R h
  -- Setup for the τ-fixed argument.
  set Sτ := posteriorCov J τ with hSτ_def
  set covLink := ψDotMat * Sτ * ψDotMat.transpose with hCovLink_def
  have hSτ_psd : Sτ.PosSemidef := (posteriorCov_posDef hJ hτ).posSemidef
  have hCovLink_psd : covLink.PosSemidef := by
    have := hSτ_psd.mul_mul_conjTranspose_same ψDotMat
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  -- CLM identification and ψDot linearity (additivity is the only piece we need).
  have h_clm_eq : ∀ g : EuclideanSpace ℝ (Fin k),
      matrixToEuclideanCLMRect ψDotMat g = ψDot g := fun g => by
    rw [h_ψDot_mat g]; rfl
  have h_ψDot_add : ∀ a b : EuclideanSpace ℝ (Fin k),
      ψDot (a + b) = ψDot a + ψDot b := fun a b => by
    have hT_add : matrixToEuclideanCLMRect ψDotMat (a + b)
        = matrixToEuclideanCLMRect ψDotMat a + matrixToEuclideanCLMRect ψDotMat b :=
      map_add _ a b
    rw [h_clm_eq, h_clm_eq, h_clm_eq] at hT_add
    exact hT_add
  -- Per-(x,y) inner bound via Anderson translation + reverse rectangular pushforward.
  have h_inner_ge : ∀ (x : EuclideanSpace ℝ (Fin k)) (y : EuclideanSpace ℝ (Fin d)),
      bayesRiskAtTau J ψDotMat L τ
        ≤ ∫⁻ g, L (y - ψDot (g + posteriorMean J τ x))
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) Sτ) := by
    intro x y
    set c := y - ψDot (posteriorMean J τ x) with hc_def
    have h_split : ∀ g : EuclideanSpace ℝ (Fin k),
        y - ψDot (g + posteriorMean J τ x) = c - ψDot g := fun g => by
      rw [h_ψDot_add g (posteriorMean J τ x), hc_def]; abel
    calc bayesRiskAtTau J ψDotMat L τ
        = ∫⁻ z, L z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) covLink) := rfl
      _ ≤ ∫⁻ z, L (c - z) ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) covLink) :=
            lintegral_loss_translated_ge hCovLink_psd hL_bowl c
      _ = ∫⁻ z, L (c - z) ∂((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) Sτ).map
              (matrixToEuclideanCLMRect ψDotMat)) := by
            rw [multivariateGaussian_map_rectangular ψDotMat 0 hSτ_psd]
            rw [show (matrixToEuclideanCLMRect ψDotMat (0 : EuclideanSpace ℝ (Fin k)))
                  = (0 : EuclideanSpace ℝ (Fin d)) from
              (matrixToEuclideanCLMRect ψDotMat).map_zero]
      _ = ∫⁻ g, L (c - matrixToEuclideanCLMRect ψDotMat g)
              ∂(multivariateGaussian 0 Sτ) := by
            have hF_meas : Measurable (fun z : EuclideanSpace ℝ (Fin d) => L (c - z)) := by
              fun_prop
            have hT_meas : Measurable (matrixToEuclideanCLMRect ψDotMat) :=
              (matrixToEuclideanCLMRect ψDotMat).continuous.measurable
            exact lintegral_map hF_meas hT_meas
      _ = ∫⁻ g, L (c - ψDot g) ∂(multivariateGaussian 0 Sτ) := by
            refine lintegral_congr fun g => ?_; rw [h_clm_eq]
      _ = ∫⁻ g, L (y - ψDot (g + posteriorMean J τ x))
              ∂(multivariateGaussian 0 Sτ) := by
            refine lintegral_congr fun g => ?_; rw [h_split]
  -- π_X is the marginal of X under the joint experiment; π_τ is the prior.
  set π_X := marginalGaussianShift J τ with hπ_X_def
  set π_τ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
              ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ)) with hπ_τ_def
  haveI hπ_X_prob : IsProbabilityMeasure π_X := by
    unfold π_X marginalGaussianShift; infer_instance
  haveI hπ_τ_prob : IsProbabilityMeasure π_τ := by
    unfold π_τ; infer_instance
  -- Joint measurability of `finn h x := ∫⁻ y, L(y - ψDot h) ∂(κ x)` on `Θk × Θk`.
  let finn : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) → ℝ≥0∞ :=
    fun h x => ∫⁻ y, L (y - ψDot h) ∂(κ x)
  have hfinn_uncurry_meas : Measurable (Function.uncurry finn) := by
    let snd : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
      Prod.snd
    have hsnd_meas : Measurable snd := measurable_snd
    let κ' : Kernel (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
        (EuclideanSpace ℝ (Fin d)) := κ.comap snd hsnd_meas
    haveI hκ'_markov : IsMarkovKernel κ' := Kernel.IsMarkovKernel.comap κ hsnd_meas
    have h_int_meas : Measurable
        (fun p : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
              × EuclideanSpace ℝ (Fin d) =>
          L (p.2 - ψDot p.1.1)) := by fun_prop
    have h_main : Measurable
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
            ∫⁻ y, L (y - ψDot p.1) ∂(κ' p)) :=
      Measurable.lintegral_kernel_prod_right' (κ := κ') h_int_meas
    convert! h_main using 1
  -- κ as an AEMeasurable function (needed by `lintegral_bind`).
  have hκ_meas : ∀ h : EuclideanSpace ℝ (Fin k),
      AEMeasurable (κ : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin d)))
        (multivariateGaussian h J⁻¹) :=
    fun h => κ.measurable.aemeasurable
  -- Outer chain: bayesRiskAtTau ≤ … ≤ ⨆ h R h.
  calc bayesRiskAtTau J ψDotMat L τ
      = ∫⁻ x, ∫⁻ _y : EuclideanSpace ℝ (Fin d),
              bayesRiskAtTau J ψDotMat L τ ∂(κ x) ∂π_X := by
        have h_inner : ∀ x, ∫⁻ _y : EuclideanSpace ℝ (Fin d),
            bayesRiskAtTau J ψDotMat L τ ∂(κ x)
              = bayesRiskAtTau J ψDotMat L τ := fun x => by
          rw [lintegral_const, measure_univ, mul_one]
        simp_rw [h_inner]
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ x, ∫⁻ y, ∫⁻ g, L (y - ψDot (g + posteriorMean J τ x))
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) Sτ) ∂(κ x) ∂π_X := by
        refine lintegral_mono fun x => ?_
        refine lintegral_mono fun y => ?_
        exact h_inner_ge x y
    _ = ∫⁻ x, ∫⁻ g, ∫⁻ y, L (y - ψDot (g + posteriorMean J τ x))
            ∂(κ x) ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) Sτ) ∂π_X := by
        refine lintegral_congr fun x => ?_
        refine MeasureTheory.lintegral_lintegral_swap ?_
        refine Measurable.aemeasurable ?_
        fun_prop
    _ = ∫⁻ h, ∫⁻ x, ∫⁻ y, L (y - ψDot h) ∂(κ x) ∂(multivariateGaussian h J⁻¹) ∂π_τ := by
        exact (gaussianShift_innovations_repr hJ hτ finn hfinn_uncurry_meas).symm
    _ = ∫⁻ h, ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ) ∂π_τ := by
        refine lintegral_congr fun h => ?_
        have hLh_meas : AEMeasurable (fun y : EuclideanSpace ℝ (Fin d) => L (y - ψDot h))
            ((multivariateGaussian h J⁻¹).bind κ) :=
          (hL_meas.comp (measurable_id.sub_const _)).aemeasurable
        exact (MeasureTheory.Measure.lintegral_bind (hκ_meas h) hLh_meas).symm
    _ = ∫⁻ h, R h ∂π_τ := by
        refine lintegral_congr fun h => ?_; rfl
    _ ≤ ∫⁻ _h, ⨆ h' : EuclideanSpace ℝ (Fin k), R h' ∂π_τ := by
        refine lintegral_mono fun h => ?_
        exact le_iSup R h
    _ = (⨆ h' : EuclideanSpace ℝ (Fin k), R h') * π_τ Set.univ := by rw [lintegral_const]
    _ = ⨆ h' : EuclideanSpace ℝ (Fin k), R h' := by rw [measure_univ, mul_one]

/-- **`posteriorCov` is monotone-non-decreasing in `τ`** (in the PSD order):
for `0 < τ₁ ≤ τ₂`, `posteriorCov J τ₂ - posteriorCov J τ₁` is PSD. -/
lemma posteriorCov_mono_in_tau
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (h_le : τ₁ ≤ τ₂) :
    (posteriorCov J τ₂ - posteriorCov J τ₁).PosSemidef := by
  have hτ₂ : 0 < τ₂ := lt_of_lt_of_le hτ₁ h_le
  set ε₁ : ℝ := (τ₁^2)⁻¹ with hε₁_def
  set ε₂ : ℝ := (τ₂^2)⁻¹ with hε₂_def
  have hε₁ : 0 < ε₁ := by positivity
  have hε₂ : 0 < ε₂ := by positivity
  have h_eps_le : ε₂ ≤ ε₁ := by
    have h_sq : τ₁^2 ≤ τ₂^2 := by
      have := mul_self_le_mul_self hτ₁.le h_le
      simpa [pow_two] using this
    have h_sq_pos₁ : (0 : ℝ) < τ₁^2 := by positivity
    exact inv_anti₀ h_sq_pos₁ h_sq
  set δ : ℝ := ε₁ - ε₂ with hδ_def
  have hδ : 0 ≤ δ := by rw [hδ_def]; linarith
  set M₁ : Matrix (Fin k) (Fin k) ℝ := J + ε₁ • (1 : Matrix _ _ _) with hM₁_def
  set M₂ : Matrix (Fin k) (Fin k) ℝ := J + ε₂ • (1 : Matrix _ _ _) with hM₂_def
  have hM₁ : M₁.PosDef := hJ.add (Matrix.PosDef.one.smul hε₁)
  have hM₂ : M₂.PosDef := hJ.add (Matrix.PosDef.one.smul hε₂)
  change (M₂⁻¹ - M₁⁻¹).PosSemidef
  have hM₂_unit : IsUnit M₂.det := (Matrix.isUnit_iff_isUnit_det M₂).mp hM₂.isUnit
  have hM₁_unit : IsUnit M₁.det := (Matrix.isUnit_iff_isUnit_det M₁).mp hM₁.isUnit
  have hM₂M₂ : M₂ * M₂⁻¹ = 1 := Matrix.mul_nonsing_inv M₂ hM₂_unit
  have hM₂M₂' : M₂⁻¹ * M₂ = 1 := Matrix.nonsing_inv_mul M₂ hM₂_unit
  have hM₁M₁ : M₁ * M₁⁻¹ = 1 := Matrix.mul_nonsing_inv M₁ hM₁_unit
  have hM_diff : M₁ = M₂ + δ • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [hM₁_def, hM₂_def, hδ_def]
    rw [sub_smul]
    abel
  have hKey : M₁ * (M₂⁻¹ - M₁⁻¹) * M₁
      = δ • (1 : Matrix (Fin k) (Fin k) ℝ) + (δ^2) • M₂⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [show M₁ * M₁⁻¹ * M₁ = M₁ by rw [hM₁M₁, Matrix.one_mul]]
    have hMM2M : M₁ * M₂⁻¹ * M₁
        = M₂ + δ • (1 : Matrix _ _ _) + δ • (1 : Matrix _ _ _) + (δ^2) • M₂⁻¹ := by
      conv_lhs => rw [hM_diff]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
                 Matrix.one_mul, Matrix.mul_one, hM₂M₂, hM₂M₂']
      rw [smul_add, smul_smul, ← pow_two]
      abel
    rw [hMM2M, hM_diff]
    abel
  have hM₁_star : star M₁ = M₁ := hM₁.1
  have hMstarM : M₁ * (M₂⁻¹ - M₁⁻¹) * star M₁ = M₁ * (M₂⁻¹ - M₁⁻¹) * M₁ := by
    rw [hM₁_star]
  rw [← Matrix.IsUnit.posSemidef_star_right_conjugate_iff hM₁.isUnit, hMstarM, hKey]
  exact (Matrix.PosDef.one.posSemidef.smul hδ).add (hM₂.inv.posSemidef.smul (by positivity))

/-- **`bayesRiskAtTau` is monotone-non-decreasing in `τ`** for fixed `A` and
bowl-shaped `L`. Uses `posteriorCov_mono_in_tau` + Anderson PSD-monotone. -/
lemma bayesRiskAtTau_mono_in_tau
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    (A : Matrix (Fin d) (Fin k) ℝ)
    {L : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hL_bowl : BowlShaped L)
    {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (h_le : τ₁ ≤ τ₂) :
    bayesRiskAtTau J A L τ₁ ≤ bayesRiskAtTau J A L τ₂ := by
  have hτ₂ : 0 < τ₂ := lt_of_lt_of_le hτ₁ h_le
  unfold bayesRiskAtTau
  apply gaussian_lintegral_mono_of_psd_le
  · have hP : (posteriorCov J τ₁).PosDef := posteriorCov_posDef hJ hτ₁
    have := hP.posSemidef.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  · have hP : (posteriorCov J τ₂).PosDef := posteriorCov_posDef hJ hτ₂
    have := hP.posSemidef.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  · have h_diff :
        A * posteriorCov J τ₂ * A.transpose - A * posteriorCov J τ₁ * A.transpose
          = A * (posteriorCov J τ₂ - posteriorCov J τ₁) * A.transpose := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [h_diff]
    have h_psd : (posteriorCov J τ₂ - posteriorCov J τ₁).PosSemidef :=
      posteriorCov_mono_in_tau hJ hτ₁ h_le
    have := h_psd.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  · exact hL_bowl


end GaussianShiftMinimax
end AsymptoticStatistics
