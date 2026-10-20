module
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity

@[expose] public section

/-!
# Multivariate central limit theorem for iid vectors (Cramér–Wold via Lévy)

Let $Y_1, Y_2, \dots$ be independent and identically distributed random vectors taking
values in $\mathbb{R}^k$, with mean zero and finite covariance matrix $\Sigma$ (positive
semidefinite), so that $\mathbb{E}\langle u, Y_0\rangle = 0$ and
$\mathbb{E}\big[\langle u, Y_0\rangle\,\langle v, Y_0\rangle\big] = u^{\top}\Sigma\, v$
for all directions $u, v \in \mathbb{R}^k$. Then the normalized partial sum
$\frac{1}{\sqrt{n}}\sum_{i=0}^{n-1} Y_i$ converges in distribution to the multivariate
normal law $N(0, \Sigma)$.

This is the device invoked as Step 1 of the score-statistic argument in van der Vaart
Theorem 7.10 (§7.3, Convergence to a Normal Experiment): the asymptotic normality of a
sum of iid score contributions follows from the multivariate CLT applied to those
contributions.

Deviation from the textbook statement: the Lean formalization carries the moment data as
explicit hypotheses on the projections $\langle u, Y_0\rangle$ — zero mean
(`h_zero_mean`), the covariance identity $u^{\top}\Sigma\,v$ (`h_cov`), and a square
integrability assumption `MemLp (Y 0) 2 P` (`hL2`) — rather than abstractly assuming
"$Y_0$ has mean $0$ and covariance $\Sigma$". These together encode exactly the finite
second-moment hypotheses of the classical statement.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 7
(Local Asymptotic Normality), Theorem 7.10 (§7.3, Convergence to a Normal Experiment),
Step 1 of the proof. The underlying classical result is the multivariate Lindeberg–Lévy
CLT together with the Cramér–Wold device (van der Vaart, Chapter 2, §2.3 Characteristic
Functions, Example 2.18 and the Cramér–Wold lemma, p. 16).

**Proof formalization notes.** The proof uses the Cramér–Wold device implemented through
Lévy's continuity theorem. For every test direction $t \in \mathbb{R}^k$, the scalar
projection $Z_i := \langle t, Y_i\rangle$ is iid with zero mean (from `h_zero_mean`) and
variance $t^{\top}\Sigma\, t$ (from `h_cov`). Mathlib's 1D CLT
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`) gives
$\tfrac{1}{\sqrt{n}}\sum_i Z_i \rightsquigarrow N\!\big(0, \operatorname{Var}[Z_0]\big)$.
Its characteristic function at the point $s = 1$ converges to
$\exp(-\operatorname{Var}[Z_0]/2)$, which equals
$\operatorname{charFun}\!\big(N(0,\Sigma)\big)(t)$. Lévy's continuity theorem
(`ProbabilityMeasure.tendsto_of_tendsto_charFun`) promotes this pointwise
characteristic-function convergence to weak convergence in `ProbabilityMeasure`, which
is unpacked as `WeakConverges`.

**Bibliographic comments.** The multivariate central limit theorem is classical folklore
with no single seminal origin; it is the natural vector-valued extension of the
Lindeberg–Lévy theorem. The reduction of multivariate weak convergence to the family of
all one-dimensional projections — the key step here — is the Cramér–Wold device:
H. Cramér and H. Wold, "Some theorems on distribution functions", *Journal of the London
Mathematical Society* 11 (1936), 290–294. The continuity-theorem machinery that converts
pointwise characteristic-function convergence into weak convergence is due to Paul Lévy
(*Calcul des probabilités*, Gauthier-Villars, Paris, 1925).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

namespace AsymptoticStatistics
namespace ScoreCLT

variable {k : ℕ}

/-- **Multivariate central limit theorem** (iid finite-dimensional vectors).

Given iid `EuclideanSpace ℝ (Fin k)`-valued random variables `Y_i` on `(Ω, P)`
with zero mean and covariance matrix `cov` (PosSemidef), the normalized sum
`(1/√n) ∑_{i<n} Y_i` converges weakly to `multivariateGaussian 0 cov`.

**Proof**: Cramér–Wold via Lévy's continuity theorem. For each `t`, the scalar
projection `Z_i := ⟪t, Y_i⟫` is iid with zero mean and variance
`⟨t, cov t⟩`; Mathlib's 1D CLT gives weak convergence of `(√n)⁻¹ ∑ Z_i` to
`gaussianReal 0 ⟨t, cov t⟩`. The characteristic function at `s = 1` converges
accordingly, matching `charFun (multivariateGaussian 0 cov) t`. Lévy's
continuity promotes pointwise charFun convergence to `Tendsto` in
`ProbabilityMeasure`, which unpacks to `WeakConverges`. -/
theorem clt_finDim
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → EuclideanSpace ℝ (Fin k)) (hY_meas : ∀ i, Measurable (Y i))
    (hindep : iIndepFun Y P)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (h_zero_mean : ∀ u : EuclideanSpace ℝ (Fin k),
      (∫ ω, ⟪u, Y 0 ω⟫ ∂P) = 0)
    (cov : Matrix (Fin k) (Fin k) ℝ) (hcov_psd : cov.PosSemidef)
    (h_cov : ∀ u v : EuclideanSpace ℝ (Fin k),
      (∫ ω, ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P) =
        u.ofLp ⬝ᵥ cov.mulVec v.ofLp)
    (hL2 : MemLp (Y 0) 2 P) :
    WeakConverges
      (fun n => P.map (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω))
      (ProbabilityTheory.multivariateGaussian 0 cov) := by
  -- Measurability of the normalized sum.
  have hW_meas : ∀ n : ℕ,
      Measurable (fun ω : Ω => (Real.sqrt n)⁻¹ •
        ∑ i ∈ Finset.range n, Y i ω : Ω → EuclideanSpace ℝ (Fin k)) := fun n =>
    (Finset.measurable_sum _ (fun i _ => hY_meas i)).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  have hP_map_prob : ∀ n : ℕ, IsProbabilityMeasure
      (P.map (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, Y i ω : Ω → EuclideanSpace ℝ (Fin k))) := fun n =>
    Measure.isProbabilityMeasure_map (hW_meas n).aemeasurable
  -- Reduce weak convergence to pointwise charFun convergence via Lévy continuity.
  suffices h_charFun : ∀ t : EuclideanSpace ℝ (Fin k),
      Tendsto (fun n : ℕ => charFun
        (P.map (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ •
          ∑ i ∈ Finset.range n, Y i ω)) t) atTop
        (𝓝 (charFun (ProbabilityTheory.multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin k)) cov) t)) by
    intro f
    have h_levy : Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
        (fun n : ℕ => ⟨P.map (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ •
          ∑ i ∈ Finset.range n, Y i ω), hP_map_prob n⟩)
        atTop (𝓝 ⟨ProbabilityTheory.multivariateGaussian 0 cov, inferInstance⟩) :=
      ProbabilityMeasure.tendsto_of_tendsto_charFun h_charFun
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h_levy) f
  -- Fix a test direction `t`.
  intro t
  -- The 1D projection `Z_i ω := ⟪t, Y_i ω⟫`.
  have hproj_meas : Measurable (fun y : EuclideanSpace ℝ (Fin k) => ⟪t, y⟫ : _ → ℝ) :=
    (continuous_const.inner continuous_id).measurable
  have hZ_meas : ∀ i, Measurable (fun ω : Ω => ⟪t, Y i ω⟫ : Ω → ℝ) :=
    fun i => hproj_meas.comp (hY_meas i)
  -- `Z_i` are iid under `P` (composition of `Y_i` iid with fixed linear functional).
  have hZ_iid : iIndepFun (fun i (ω : Ω) => ⟪t, Y i ω⟫ : ℕ → Ω → ℝ) P :=
    hindep.comp (fun _ => fun y : EuclideanSpace ℝ (Fin k) => ⟪t, y⟫)
      (fun _ => hproj_meas)
  have hZ_ident : ∀ i, IdentDistrib
      (fun ω : Ω => ⟪t, Y i ω⟫) (fun ω : Ω => ⟪t, Y 0 ω⟫) P P := fun i =>
    (hident i).comp (u := fun y : EuclideanSpace ℝ (Fin k) => ⟪t, y⟫) hproj_meas
  -- Zero mean and L² control.
  have hZ_mean : P[fun ω => ⟪t, Y 0 ω⟫] = 0 := h_zero_mean t
  have hZ_L2 : MemLp (fun ω : Ω => ⟪t, Y 0 ω⟫) 2 P := by
    have h := hL2.inner_const (𝕜 := ℝ) t
    exact h.ae_eq (Filter.Eventually.of_forall
      fun ω => (real_inner_comm (Y 0 ω) t).symm)
  -- Variance: `Var[Z_0; P] = ⟨t, cov t⟩_Mat`.
  have hZ_var : Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P] = t.ofLp ⬝ᵥ cov.mulVec t.ofLp := by
    rw [variance_eq_integral (hZ_meas 0).aemeasurable, hZ_mean]
    simp only [sub_zero]
    have h_sq : (fun ω => ⟪t, Y 0 ω⟫ ^ 2)
        =ᵐ[P] (fun ω => ⟪t, Y 0 ω⟫ * ⟪t, Y 0 ω⟫) := by
      filter_upwards with ω; ring
    rw [integral_congr_ae h_sq]
    exact h_cov t t
  have hZ_var_nn : 0 ≤ Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P] := variance_nonneg _ _
  -- Apply Mathlib's 1D CLT to the projection.
  have h1D := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun i ω => ⟪t, Y i ω⟫)
    (Y := (id : ℝ → ℝ))
    (P' := gaussianReal 0 Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P].toNNReal)
    HasLaw.id hZ_L2 hZ_iid hZ_ident
  -- Simplify the summand using `P[Z_0] = 0` via `TendstoInDistribution.congr`.
  have h1D' := h1D.congr (Y := fun (n : ℕ) (ω : Ω) => (Real.sqrt (n : ℝ))⁻¹ *
      ∑ k ∈ Finset.range n, ⟪t, Y k ω⟫)
    (T := (id : ℝ → ℝ))
    (fun (n : ℕ) => Filter.Eventually.of_forall fun ω => by
      change (Real.sqrt (n : ℝ))⁻¹ *
        (∑ k ∈ Finset.range n, ⟪t, Y k ω⟫ - (n : ℝ) * P[fun ω' => ⟪t, Y 0 ω'⟫])
        = (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, ⟪t, Y k ω⟫
      rw [hZ_mean]; ring)
    (Filter.Eventually.of_forall fun _ => rfl)
  -- Extract pointwise charFun convergence at s = 1 via Lévy iff.
  have h_charFun_1D := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp h1D'.tendsto 1
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at h_charFun_1D
  -- Evaluate `charFun (gaussianReal 0 v) 1 = exp(-v/2)`.
  have h_gauss : charFun
      (gaussianReal 0 Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P].toNNReal) 1
      = Complex.exp (- ((Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P] : ℂ)) / 2) := by
    rw [charFun_gaussianReal]
    push_cast
    rw [Real.coe_toNNReal _ hZ_var_nn]
    ring_nf
  rw [h_gauss] at h_charFun_1D
  -- Evaluate `charFun (multivariateGaussian 0 cov) t = exp(-⟨t, cov t⟩/2)`.
  have h_charFun_ν : charFun (ProbabilityTheory.multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin k)) cov) t
      = Complex.exp (- ((Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P] : ℂ)) / 2) := by
    rw [ProbabilityTheory.charFun_multivariateGaussian hcov_psd t]
    rw [show (inner ℝ t (0 : EuclideanSpace ℝ (Fin k))) = (0 : ℝ) from inner_zero_right t]
    rw [hZ_var]
    push_cast
    ring_nf
  rw [h_charFun_ν]
  -- Rewrite LHS: `charFun (P.map W_n) t = charFun (P.map ((√n)⁻¹ * ∑ Z_k)) 1`.
  have h_charFun_lhs : ∀ n : ℕ,
      charFun (P.map (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, Y i ω)) t
      = charFun (P.map (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ *
        ∑ k ∈ Finset.range n, ⟪t, Y k ω⟫)) 1 := by
    intro n
    rw [charFun_apply, charFun_apply_real]
    rw [MeasureTheory.integral_map (hW_meas n).aemeasurable
        (by fun_prop : AEStronglyMeasurable
          (fun x : EuclideanSpace ℝ (Fin k) =>
            Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I))
          (P.map _))]
    rw [MeasureTheory.integral_map
        ((Finset.aemeasurable_fun_sum _
          (fun _ _ => (hZ_meas _).aemeasurable)).const_mul _)
        (by fun_prop : AEStronglyMeasurable
          (fun x : ℝ => Complex.exp (((1 : ℝ) : ℂ) * (x : ℂ) * Complex.I))
          (P.map _))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    congr 1
    -- Goal: `⟪W n ω, t⟫ * I = 1 * ((√n)⁻¹ * ∑ Z_k ω) * I` (both in ℂ)
    have h_inner : (inner ℝ ((Real.sqrt (n : ℝ))⁻¹ •
          ∑ i ∈ Finset.range n, Y i ω : EuclideanSpace ℝ (Fin k)) t : ℝ)
        = (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, ⟪t, Y k ω⟫ := by
      rw [real_inner_smul_left, sum_inner]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact (real_inner_comm (Y i ω) t).symm
    rw [show ⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, Y i ω, t⟫
          = (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, ⟪t, Y k ω⟫ from h_inner]
    push_cast
    ring
  simp_rw [h_charFun_lhs]
  exact h_charFun_1D

end ScoreCLT
end AsymptoticStatistics
