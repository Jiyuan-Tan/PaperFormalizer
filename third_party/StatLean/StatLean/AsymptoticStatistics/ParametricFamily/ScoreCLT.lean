module
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateCLT
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Score-sum central limit theorem (multivariate adapter for Theorem 7.10)

Let $X_1, X_2, \dots$ be independent and identically distributed observations and let
$\dot\ell$ be the score function, viewed as a vector in $\mathbb{R}^k$. Suppose the score
has **mean zero**, $\mathrm{E}\,\dot\ell(X_1) = 0$, and **covariance matrix** equal to the
Fisher information $J$, characterised as a quadratic form by
$\mathrm{E}\bigl[\langle u, \dot\ell(X_1)\rangle\,\langle v, \dot\ell(X_1)\rangle\bigr]
= u^{\top} J\,v$ for all $u, v \in \mathbb{R}^k$. Then the standardised score sum
$$
  \Delta_n \;=\; \frac{1}{\sqrt n}\sum_{i=1}^{n} \dot\ell(X_i)
$$
converges in distribution to a centred multivariate Gaussian with covariance $J$, i.e.
$\Delta_n \rightsquigarrow N(0, J)$.

This is **Step 1** in van der Vaart's proof of the asymptotic representation theorem
(Theorem 7.10): in the notation of that proof, $\Delta_n = n^{-1/2}\sum \dot\ell_\theta(X_i)$
is shown to be a marginal weak limit that is $N(0, J)$-distributed with $J = I_\theta$ the
Fisher information. This file isolates that convergence as the form consumed by the project's
`AsymptoticStatistics.AsymptoticRepresentation`.

**Added hypotheses / deviations from the book.** Van der Vaart obtains the $N(0,J)$ limit as a
direct consequence of differentiability in quadratic mean (which forces the score to have mean
zero and finite Fisher information). This adapter takes those two facts as explicit hypotheses
— mean zero (`h_zero_mean`) and the covariance/Fisher-information identity (`h_cov`), both
phrased through inner products — together with positive semidefiniteness of $J$ (`hJ_psd`) and
square-integrability of the score (`h_L2`, i.e. $\mathrm{E}\,\|\dot\ell(X_1)\|^2 < \infty$).
At the call site these are discharged from DQM via `Score.score_mean_zero` and the Fisher
information definition, so no genuine extra assumption is introduced relative to the book.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998. Chapter 7 (Local Asymptotic
Normality), §7.3 (Convergence to a Normal Experiment; Theorem 7.10, proof; Step 1: the convergence
$\Delta_n = n^{-1/2}\sum \dot\ell_\theta(X_i) \rightsquigarrow N(0, I_\theta)$).

**Proof formalization notes.**

*Why a separate file?* Theorem 7.10's proof builds an *abstract* iid setup `(P, Y)` on
`(ℕ → 𝓧)` from a parametric family `(M, μ, θ₀, ℓ)`. The CLT is consumed in the form

    WeakConverges (fun n => P.map (fun ω => (√n)⁻¹ • ∑ i ∈ range n, Y i ω))
                  (multivariateGaussian 0 J)

with hypotheses that match what the call site has on hand:

* zero mean of `Y 0` *via inner products*: `∀ u, ∫ ⟪u, Y 0 ω⟫ ∂P = 0`,
* covariance of `Y 0` *as a quadratic form on `EuclideanSpace ℝ (Fin k)`*:
  `∀ u v, ∫ ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P = u.ofLp ⬝ᵥ J.mulVec v.ofLp`.

It is a thin adapter on top of the project's underlying iid multivariate CLT brick
`ProbabilityTheory.tendstoInDistribution_multivariate_clt` (in
`StatLean/AsymptoticStatistics/ForMathlib/MultivariateCLT.lean`). The underlying `MultivariateCLT`
brick is stated more generically (with witness `Y' : Ω' → ℝ^k` and an arbitrary `P'`); this
adapter specialises to the `Y' := id`, `P' := multivariateGaussian 0 J` case and converts
`MeasureTheory.TendstoInDistribution` into our test-function-based `WeakConverges`. The
inner-product mean-zero / covariance hypotheses are converted to the brick's expected vector
mean (`h_E_Y0`) and scalar-variance (`h_var`) forms, and the standardising recentering
`n • P[Y 0]` is eliminated using `P[Y 0] = 0`.

*Main result.* `AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim`: weak convergence of
the scaled abstract score sum to `multivariateGaussian 0 J`, under the inner-product zero-mean /
covariance / `MemLp 2` package.

**Bibliographic comments.** The result is the multivariate central limit theorem applied to the
iid sequence of score vectors, and as such it is classical folklore with no single seminal
origin. It is the vector-valued Lindeberg–Lévy CLT — provable from the one-dimensional CLT of
J. W. Lindeberg, "Eine neue Herleitung des Exponentialgesetzes in der Wahrscheinlichkeits-
rechnung," *Mathematische Zeitschrift* 15 (1922), 211–225, via the Cramér–Wold device of
H. Cramér and H. Wold, "Some theorems on distribution functions," *Journal of the London
Mathematical Society* s1-11 (1936), 290–294. Its specific use to establish the $N(0, I_\theta)$
limit of the score sum in local asymptotic normality theory is due to L. Le Cam and is
presented in van der Vaart, *Asymptotic Statistics* (1998), Chapter 7; no primary-source
theorem number is attached to this step beyond the proof of Theorem 7.10.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped Real Topology RealInnerProductSpace ENNReal Matrix
open AsymptoticStatistics

namespace AsymptoticStatistics.ParametricFamily
namespace ScoreCLT

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Multivariate score CLT (finite-dimensional, abstract iid form).**

For an iid sequence `Y i : Ω → EuclideanSpace ℝ (Fin k)` under a probability
measure `P`, with **zero mean** (in the inner-product sense) and **covariance
matrix `J`** (in the inner-product sense), the standardised sum
`(√n)⁻¹ • ∑_{i<n} Y i` converges weakly to `multivariateGaussian 0 J`.

This is the abstract iid form consumed by `AsymptoticRepresentation` after it has built the
Kolmogorov-extension setup `P := Measure.infinitePi (fun _ => ν)` and the
coordinate map `Y i ω := ℓ (ω i)`. The hypotheses are stated against `P` and
`Y 0` directly so the call site can plug in its already-derived score
mean-zero (from `Score.score_mean_zero`) and Fisher-information identity
(from `fisherInformation` definition + the user-supplied matrix bridge `hJ`)
without further manipulation. -/
theorem clt_finDim
    (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ}
    (Y : ℕ → Ω → EuclideanSpace ℝ (Fin k))
    (hY_meas : ∀ i, Measurable (Y i))
    (hY_iid : iIndepFun Y P)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    -- (consequence of DQM via `Score.score_mean_zero`).
    (h_zero_mean : ∀ u : EuclideanSpace ℝ (Fin k), ∫ ω, ⟪u, Y 0 ω⟫ ∂P = 0)
    (J : Matrix (Fin k) (Fin k) ℝ)
    (hJ_psd : J.PosSemidef)
    -- vdV §7.3 (Fisher-information identity, supplied by the call site).
    (h_cov : ∀ u v : EuclideanSpace ℝ (Fin k),
      ∫ ω, ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P = u.ofLp ⬝ᵥ J.mulVec v.ofLp)
    -- (DQM gives Fisher integrability ⇒ `MemLp 2`).
    (h_L2 : MemLp (Y 0) 2 P) :
    WeakConverges
      (fun n : ℕ => P.map (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) := by
  classical
  -- Integrability of `Y 0` from the L² hypothesis.
  have h_int_Y0 : Integrable (Y 0) P := h_L2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  -- `P[Y 0] = 0` from `h_zero_mean` via `integral_eq_zero_of_forall_integral_inner_eq_zero`.
  have h_E_Y0 : P[Y 0] = (0 : EuclideanSpace ℝ (Fin k)) := by
    refine integral_eq_zero_of_forall_integral_inner_eq_zero (𝕜 := ℝ) (Y 0) h_int_Y0 ?_
    intro c
    exact h_zero_mean c
  -- Variance identity: `Var[⟪t, Y 0⟫; P] = t ⬝ᵥ J *ᵥ t`.
  have h_var : ∀ t : EuclideanSpace ℝ (Fin k),
      Var[fun ω => ⟪t, Y 0 ω⟫; P] = t ⬝ᵥ J *ᵥ t := by
    intro t
    have h_AEM : AEMeasurable (fun ω => ⟪t, Y 0 ω⟫) P :=
      ((Measurable.const_inner (c := t) (hY_meas 0))).aemeasurable
    have h_int_zero : ∫ ω, ⟪t, Y 0 ω⟫ ∂P = 0 := h_zero_mean t
    rw [variance_of_integral_eq_zero h_AEM h_int_zero]
    -- `∫ ⟪t, Y 0 ω⟫ ^ 2 = ∫ ⟪t, Y 0 ω⟫ * ⟪t, Y 0 ω⟫ = t.ofLp ⬝ᵥ J.mulVec t.ofLp = t ⬝ᵥ J *ᵥ t`.
    have h_sq : (fun ω => ⟪t, Y 0 ω⟫ ^ 2) = (fun ω => ⟪t, Y 0 ω⟫ * ⟪t, Y 0 ω⟫) := by
      funext ω; rw [sq]
    -- The `rw [h_cov t t]` produces `t.ofLp ⬝ᵥ J.mulVec t.ofLp`, which is
    -- definitionally equal to `t ⬝ᵥ J *ᵥ t` (the goal) through `WithLp`.
    rw [h_sq, h_cov t t]
  -- Build the witness `id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)` with
  -- law `multivariateGaussian 0 J`.
  haveI hG_prob : IsProbabilityMeasure (multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin k)) J) := inferInstance
  have hY_id : HasLaw
      (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) := HasLaw.id
  -- Apply the project's underlying multivariate iid CLT.
  have h_TID :
      MeasureTheory.TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt n)⁻¹ • (∑ k_idx ∈ Finset.range n, Y k_idx ω - n • P[Y 0]))
        atTop (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
        (fun _ => P)
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    tendstoInDistribution_multivariate_clt
      (P := P) (P' := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J)
      (X := Y) (Y := id) (S := J) hJ_psd h_var hY_id h_L2 hY_iid hident
  -- Replace `n • P[Y 0]` by `0` using `h_E_Y0`, simplifying the standardised sum.
  have h_eq : ∀ n : ℕ,
      (fun ω => (Real.sqrt n)⁻¹ • (∑ k_idx ∈ Finset.range n, Y k_idx ω - n • P[Y 0]))
        = (fun ω => (Real.sqrt n)⁻¹ • ∑ k_idx ∈ Finset.range n, Y k_idx ω) := by
    intro n
    funext ω
    rw [h_E_Y0, smul_zero, sub_zero]
  -- Convert `TendstoInDistribution` to `WeakConverges` via the `ProbabilityMeasure`
  -- characterisation `tendsto_iff_forall_integral_tendsto`.
  intro f
  -- Massage the goal so the integrand on the LHS matches `h_TID` after `h_eq`.
  -- `WeakConverges` unfolds to: `Tendsto (fun n => ∫ x, f x ∂(P.map …)) atTop (𝓝 …)`.
  -- The map measure `P.map (fun ω => (√n)⁻¹ • ∑ Y k ω)` agrees with the standardised
  -- one since `P[Y 0] = 0`.
  have h_map_eq : ∀ n : ℕ,
      P.map (fun ω => (Real.sqrt n)⁻¹ • ∑ k_idx ∈ Finset.range n, Y k_idx ω) =
      P.map (fun ω => (Real.sqrt n)⁻¹ •
        (∑ k_idx ∈ Finset.range n, Y k_idx ω - n • P[Y 0])) := by
    intro n
    rw [h_eq n]
  -- Extract the `Tendsto`-on-`ProbabilityMeasure`-objects statement from `h_TID`.
  have h_PM := h_TID.tendsto
  -- Pull this through `tendsto_iff_forall_integral_tendsto` at the bdd-cts test `f`.
  have h_int_tendsto :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h_PM) f
  -- Rewrite the LHS: the map measure equals the simpler `(√n)⁻¹ • ∑` map.
  -- The RHS is `(multivariateGaussian 0 J).map id = multivariateGaussian 0 J`.
  -- Both rewrites reduce `h_int_tendsto` to the goal up to the `ProbabilityMeasure`
  -- coercion, which is definitional.
  have h_map_id :
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
        (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J :=
    Measure.map_id
  -- Rewrite the LHS index by `h_map_eq` and the RHS by `h_map_id`.
  simp only [h_map_id] at h_int_tendsto
  -- The remaining task is to identify the integral of `f` against the standardised-sum
  -- pushforward (with the `n • P[Y 0]` correction term) with the integral against the
  -- simpler pushforward (no correction term). These agree by `h_map_eq` since
  -- `P[Y 0] = 0`; substitute pointwise.
  have h_pointwise : ∀ n : ℕ,
      ∫ x, f x ∂(P.map
        (fun ω => (Real.sqrt n)⁻¹ • (∑ k_idx ∈ Finset.range n, Y k_idx ω - n • P[Y 0]))) =
      ∫ x, f x ∂(P.map
        (fun ω => (Real.sqrt n)⁻¹ • ∑ k_idx ∈ Finset.range n, Y k_idx ω)) := by
    intro n
    rw [← h_map_eq n]
  -- The `ProbabilityMeasure` coercion is definitional; `simpa` rewrites both sides.
  simpa [h_pointwise] using h_int_tendsto

end ScoreCLT
end AsymptoticStatistics.ParametricFamily
