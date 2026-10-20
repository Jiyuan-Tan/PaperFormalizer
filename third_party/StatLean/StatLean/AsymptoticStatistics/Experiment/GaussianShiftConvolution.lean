module
public import StatLean.AsymptoticStatistics.Experiment.EquivariantInLaw
public import StatLean.AsymptoticStatistics.Experiment.GaussianShiftMinimax
public import StatLean.AsymptoticStatistics.ForMathlib.IndepWeakLimit
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianConv
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianWeakLimit
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Kernel.Composition.CompNotation

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

@[expose] public section

/-!
# Convolution structure of equivariant-in-law estimators

Consider the Gaussian shift (Gaussian location) experiment: a single observation
$X \sim N(h, \Sigma)$ on $\mathbb{R}^k$ with unknown mean $h$ and known,
nonsingular covariance matrix $\Sigma$. One wishes to estimate $A h$ for a fixed
matrix $A$. A (possibly randomized) estimator $T$ is *equivariant-in-law* for
$A h$ if the distribution of $T - A h$ under parameter $h$ does not depend on
$h$; this common law is the estimator's *invariant* (or *null*) law $L$.

The convolution theorem asserts that the invariant law of every such estimator
is a smearing of the law of the canonical estimator $A X$: there is a
probability measure $M$ with
$$ L \;=\; N\!\bigl(0,\, A\Sigma A^{\mathsf T}\bigr) \,*\, M, $$
the convolution of the centered Gaussian $N(0, A\Sigma A^{\mathsf T})$ — the
invariant law of $A X$ — with $M$. Intuitively $M$ is the law of an independent
noise term added to $A X$, so $A X$ is the most concentrated equivariant-in-law
estimator. The headline Lean declaration is
`equivariant_in_law_convolution_decomposition`; the covariance is supplied as a
positive-definite matrix $\Sigma$ (the book's "known and nonsingular"
assumption), $A$ is the linear map, the randomized estimator is encoded as a
Markov kernel $T$, and `hT_equiv` is the equivariance-in-law hypothesis. The
conclusion uses Mathlib's convolution-of-measures notation $\mu * \nu$.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 8 (Efficiency of Estimators), §8.4 (Estimating Normal Means),
Proposition 8.4.

**Proof formalization notes.** The proof follows vdV §8.4 in three steps:

* **Step 1 (Bayes setup)**: place a $N(0, \Lambda)$ prior on the parameter $h$;
  the posterior $H \mid X$ is $N\bigl(\mathrm{posteriorMean}\,J\,\tau\,X,\,
  \mathrm{posteriorCov}\,J\,\tau\bigr)$ with $\Lambda = \tau^2 I$ and
  $J = \Sigma^{-1}$. The key Bayesian fact is `gaussianShift_innovations_repr`.

* **Step 2 (Innovations decomposition)**: define the Gaussian innovation
  $G_\Lambda := A\,(H - \mathrm{posteriorMean}\,J\,\tau\,X)$ and the residual
  $W_\Lambda := T(X, U) - A\,\mathrm{posteriorMean}\,J\,\tau\,X$. Then
  $G_\Lambda + W_\Lambda = T - A H$ and $G_\Lambda \perp W_\Lambda$ (the key
  independence). Note the sign convention: vdV literally writes
  $G_\Lambda := A(H - \mu(X))$, but direct algebra with that sign gives
  $G + W = T + AH - 2A\mu$, not $T - AH$; the corrected sign
  $G_\Lambda := A(\mu(X) - H)$ makes $G + W = T - AH$ hold and leaves both the
  (centered, symmetric) Gaussian conditional law of $G_\Lambda$ and the
  independence with $W_\Lambda$ unchanged. See the docstring of `G_Lambda_law`.

* **Step 3 (Lévy continuity assembly)**: equivariance gives $T - A H \sim L$ for
  every $\Lambda$; the characteristic-function factorization gives
  $\hat G_\Lambda \cdot \hat W_\Lambda = \hat L$; as $\Lambda \to \infty$,
  $\hat G_\Lambda \to \hat G$ (continuity in the covariance) with $\hat G$
  nowhere zero, so $\hat W_\Lambda \to \hat L / \hat G$ continuous, whence (Lévy
  continuity) $W_\Lambda \rightsquigarrow W$; joint weak convergence with
  independence plus the continuous mapping theorem yields $G + W \sim L$, and one
  sets $M := \mathrm{law}(W)$.

**Bibliographic comments.** The convolution theorem originates with
J. Hájek, "A characterization of limiting distributions of regular estimates",
*Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete* **14** (1970),
323–330, with a closely related contemporaneous result by N. Inagaki, "On the
limiting distribution of a sequence of estimators with uniformity property",
*Annals of the Institute of Statistical Mathematics* **22** (1970), 1–13. Hájek
proved the general (locally asymptotically normal) form for regular estimator
sequences; the abstract decision-theoretic version is due to L. Le Cam. The
finite-sample statement formalized here — the convolution structure of
equivariant-in-law estimators in the exact Gaussian shift experiment — is vdV's
Proposition 8.4, the simplest (non-asymptotic, single-observation) instance from
which the asymptotic convolution theorem is obtained by the LAN limit-experiment
reduction.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped ENNReal Topology RealInnerProductSpace BoundedContinuousFunction

namespace AsymptoticStatistics
namespace GaussianShiftConvolution

open AsymptoticStatistics.EquivariantInLaw
open AsymptoticStatistics.GaussianShiftMinimax

variable {k d : ℕ}

/-! ## Step 2: Innovations decomposition + independence

We work under prior `H ∼ multivariateGaussian 0 (τ²·I)` and conditional
`X | H ∼ multivariateGaussian H J⁻¹` (with `J = Σ⁻¹`). The randomization
kernel `T` produces `Y := T(X)` conditional on `X`.

For Step 2 we define the **laws** of the random vectors `G_Λ`, `W_Λ`
(rather than the random vectors themselves), since our Kernel-based setup
puts the canonical probability space at the `(H, X, Y)` joint measure
`(prior ⊗ likelihood ⊗ T)` on `ℝᵏ × ℝᵏ × ℝᵈ`.

* `G_Λ := A · (H − posteriorMean J τ X)` — lives on `ℝᵈ`.
* `W_Λ := Y − A · posteriorMean J τ X`   — lives on `ℝᵈ`.
* `T − A·H = G_Λ + W_Λ`.
* `G_Λ ⟂ W_Λ`.
-/

/-- **Joint (H, X, Y) measure on `ℝᵏ × ℝᵏ × ℝᵈ`** under prior `π_τ =
N(0, τ²·I)`, likelihood `X | H ∼ N(H, J⁻¹)`, and randomization kernel
`T : Kernel ℝᵏ ℝᵈ` (only depends on `X`, independent of `H`).

Built by chaining: first sample `H ∼ π_τ`, then `X | H ∼ mvg H J⁻¹`,
then `Y | X ∼ T(X)`. Equivalent to the iterated `bind`s.

Bayes setup of the Prop 8.4 proof (vdV §8.4: "Let H be a random vector with a
normal N(0, Λ)-distribution …").

**Encoding.** Built with two ingredients that both have first-class
measurability lemmas:

1. The joint `μ_HX = (πτ × N(0, J⁻¹)).map (shiftCLM k)` on `ℝᵏ × ℝᵏ`
   (independent prior × noise, then add to get `X = H + ε`).
2. A kernel `K_T := T.comap Prod.snd` from `ℝᵏ × ℝᵏ` to `ℝᵈ` (depends
   only on the `X` coordinate).

The triple is then `(μ_HX ⊗ₘ K_T)` (a measure on `(ℝᵏ × ℝᵏ) × ℝᵈ`),
re-bracketed via `.map (fun ((h, x), y) => (h, x, y))`. All `compProd`
lemmas (measurability, `IsProbability`, Fubini) apply directly. -/
noncomputable def jointHXY
    (J : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin k) ×
             EuclideanSpace ℝ (Fin k) ×
             EuclideanSpace ℝ (Fin d)) :=
  (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
        ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹)).map
      (shiftCLM k) ⊗ₘ (T.comap Prod.snd measurable_snd)).map
    (fun (q : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
        × EuclideanSpace ℝ (Fin d)) => (q.1.1, q.1.2, q.2))

/-- **The G_Λ law** — pushforward of the joint `(H, X, Y)` measure under
the map `(h, x, _) ↦ A · (posteriorMean J τ x − h)` on `ℝᵈ`.

**Sign note.** vdV §8.4 literally writes `G_Λ := A(H − μ(X))`, but then claims
"the sum of the two vectors yields `T − AH`". Direct algebra with the literal
vdV sign gives `G + W = T + AH − 2Aμ`, not `T − AH`; the corrected sign
`G_Λ := A(μ(X) − H)` makes `G + W = T − AH` hold. The Gaussian conditional
distribution `G_Λ | X` is unchanged (`N(0, A·Σ_post·Aᵀ)`: symmetric, so the
sign flip of a centred Gaussian gives the same Gaussian); independence with
`W_Λ` is also unaffected. We therefore adopt the corrected sign here.

vdV §8.4 (modulo sign typo, see note above). -/
noncomputable def G_Lambda_law
    (J : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (jointHXY J τ T).map (fun p =>
    (WithLp.equiv 2 (Fin d → ℝ)).symm
      (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
        (posteriorMean J τ p.2.1 - p.1))))

/-- **The W_Λ law** — pushforward of the joint `(H, X, Y)` measure under
the map `(_, x, y) ↦ y − A · posteriorMean J τ x` on `ℝᵈ`.

vdV §8.4 ("W_Λ := T(X, U) − A(Σ⁻¹ + Λ⁻¹)⁻¹ Σ⁻¹ X"). -/
noncomputable def W_Lambda_law
    (J : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (jointHXY J τ T).map (fun p =>
    p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
      (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (posteriorMean J τ p.2.1))))

/-- **The joint (G_Λ, W_Λ) law** on `ℝᵈ × ℝᵈ`. -/
noncomputable def joint_GW_law
    (J : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  (jointHXY J τ T).map (fun p =>
    ((WithLp.equiv 2 (Fin d → ℝ)).symm
        (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
          (posteriorMean J τ p.2.1 - p.1))),
     p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
        (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (posteriorMean J τ p.2.1)))))

/-- `G_Λ + W_Λ = T − A·H` at the level of joint distributions:
the pushforward of `(G_Λ, W_Λ)` by the sum equals the pushforward of
`(H, X, Y)` by `(h, _, y) ↦ y − A·h`.

Algebra (with the corrected sign of `G_Lambda_law`, see its docstring):
`A·(μ(x) − h) + (y − A·μ(x)) = y − A·h`. Hence both sides are the same
pushforward of `jointHXY J τ T` under `(h, x, y) ↦ y − A·h`. -/
theorem G_plus_W_eq_T_minus_AH
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ : ℝ} (hτ : 0 < τ)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel T] :
    (joint_GW_law J τ A T).map (fun p => p.1 + p.2)
      = (jointHXY J τ T).map (fun p =>
          p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) p.1))) := by
  -- Collapse `(jointHXY.map joint_fn).map sum_fn` to a single pushforward,
  -- then use the pointwise algebra `A·(μ − h) + (y − A·μ) = y − A·h`.
  let _hJ := hJ
  let _hτ := hτ
  unfold joint_GW_law
  -- Measurability needed to compose `map`. `posteriorMean J τ` is a CLM and
  -- `A.mulVec` lifted through `WithLp.equiv` is `matrixToEuclideanCLMRect A`.
  have hμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) => posteriorMean J τ x) :=
    (matrixToEuclideanCLMRect (posteriorCov J τ * J)).continuous.measurable
  have hAμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) =>
      (WithLp.equiv 2 (Fin d → ℝ)).symm
        (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) x))) :=
    (matrixToEuclideanCLMRect A).continuous.measurable
  have h_joint :
      Measurable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
          × EuclideanSpace ℝ (Fin d) =>
        ((WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
              (posteriorMean J τ p.2.1 - p.1))),
         p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
              (posteriorMean J τ p.2.1))))) := by
    refine Measurable.prodMk ?_ ?_
    · exact hAμ.comp ((hμ.comp (measurable_fst.comp measurable_snd)).sub measurable_fst)
    · exact (measurable_snd.comp measurable_snd).sub
        ((hAμ.comp (hμ.comp (measurable_fst.comp measurable_snd))))
  have h_sum : Measurable
      (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => q.1 + q.2) := by
    fun_prop
  rw [Measure.map_map h_sum h_joint]
  -- Now both sides are `jointHXY.map f`; show `f` agrees pointwise.
  congr 1
  funext p
  -- Algebra: A·(μ − h) + (y − A·μ) = y − A·h.
  -- The CLM `matrixToEuclideanCLMRect A` is linear, so applying it to `μ − p.1`
  -- yields `Aμ − Ah`. Then `(Aμ − Ah) + (p.2.2 − Aμ) = p.2.2 − Ah`.
  have hAlin : ∀ u v : EuclideanSpace ℝ (Fin k),
      matrixToEuclideanCLMRect A (u - v)
        = matrixToEuclideanCLMRect A u - matrixToEuclideanCLMRect A v :=
    fun u v => (matrixToEuclideanCLMRect A).map_sub u v
  -- The function form of `matrixToEuclideanCLMRect A x = (WithLp.equiv).symm (A · WithLp.equiv x)`.
  have h_clm_eq : ∀ x : EuclideanSpace ℝ (Fin k),
      matrixToEuclideanCLMRect A x =
        (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) x)) := fun _ => rfl
  set μx : EuclideanSpace ℝ (Fin k) := posteriorMean J τ p.2.1 with hμx_def
  -- LHS of the funext: ((Aμ − Ah), (p.2.2 − Aμ)) summed.
  change (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (μx - p.1)))
        + (p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) μx)))
      = p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) p.1))
  rw [← h_clm_eq (μx - p.1), ← h_clm_eq μx, ← h_clm_eq p.1, hAlin]
  abel

/-- `W_Λ` is a measurable function of `(X, Y)` alone (does
not depend on `H`).

This is one half of the independence argument: `W_Λ` is `σ(X, Y)`-
measurable. -/
theorem W_Lambda_is_function_of_X_Y
    (J : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))) :
    Measurable (fun (p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin d)) =>
      p.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
        (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (posteriorMean J τ p.1)))) := by
  -- `posteriorMean J τ = matrixToEuclideanCLMRect (Σ_τ * J)` is CLM ⇒ measurable.
  -- `A.mulVec ∘ WithLp.equiv` is also a CLM = `matrixToEuclideanCLMRect A`.
  -- The combined map is the composition `matrixToEuclideanCLMRect A ∘
  -- matrixToEuclideanCLMRect (Σ_τ * J) ∘ fst` subtracted from `snd`.
  let _T := T
  have hμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) => posteriorMean J τ x) :=
    (matrixToEuclideanCLMRect (posteriorCov J τ * J)).continuous.measurable
  have hAμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) =>
      (WithLp.equiv 2 (Fin d → ℝ)).symm
        (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) x))) :=
    (matrixToEuclideanCLMRect A).continuous.measurable
  exact measurable_snd.sub ((hAμ.comp hμ).comp measurable_fst)

/-- Conditional law of `G_Λ` given `X = x` is
`multivariateGaussian 0 (A · posteriorCov J τ · Aᵀ)` — **independent of**
`x` (the key Bayesian-Gaussian fact, vdV §8.4 "the conditional
distribution of G_Λ given X is normal with mean 0 and covariance matrix
A(Σ⁻¹ + Λ⁻¹)⁻¹ Aᵀ, independent of X").

**Proof strategy** (closed via chained `map_map` + `joint_pushforward_eq`):
1. `G_Lambda_law` is a pushforward by a map that ignores `Y`, so it equals
   the pushforward of the `(H, X)` marginal of `jointHXY`, which is `μ_HX`.
2. By `joint_pushforward_eq` (lifted from `GaussianShiftMinimax.lean`),
   `μ_HX = ((marginalGaussianShift × N(0, posteriorCov)).map posteriorCLM)`.
3. Composing the maps: `(x, g) ↦ posteriorCLM(x, g) = (g + μ(x), x)`, then
   `G_map(h, x) = A·(μ(x) − h)` gives `A·(μ(x) − (g + μ(x))) = −A·g`.
4. The result is a pushforward of `N(0, posteriorCov)` under
   `g ↦ matrixToEuclideanCLMRect (−A) g`; apply
   `multivariateGaussian_map_rectangular`. The sign cancels in the
   covariance: `(−A) · posteriorCov · (−A)ᵀ = A · posteriorCov · Aᵀ`. -/
theorem G_Lambda_cond_X_eq_gaussian
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ : ℝ} (hτ : 0 < τ)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel T] :
    (G_Lambda_law J τ A T)
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (A * posteriorCov J τ * A.transpose) := by
  -- Notation.
  set πτ : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
      ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ)) with hπτ_def
  set ν_J : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹ with hν_J_def
  set ν_S : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (posteriorCov J τ) with hν_S_def
  set π_X : Measure (EuclideanSpace ℝ (Fin k)) := marginalGaussianShift J τ with hπ_X_def
  haveI : IsProbabilityMeasure πτ := by rw [hπτ_def]; infer_instance
  haveI : IsProbabilityMeasure ν_J := by rw [hν_J_def]; infer_instance
  haveI : IsProbabilityMeasure ν_S := by rw [hν_S_def]; infer_instance
  haveI : IsProbabilityMeasure π_X := by
    rw [hπ_X_def, marginalGaussianShift]; infer_instance
  have hAμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) =>
      (WithLp.equiv 2 (Fin d → ℝ)).symm
        (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) x))) :=
    (matrixToEuclideanCLMRect A).continuous.measurable
  have hμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) => posteriorMean J τ x) :=
    (matrixToEuclideanCLMRect (posteriorCov J τ * J)).continuous.measurable
  set G_map : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
      × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun p => (WithLp.equiv 2 (Fin d → ℝ)).symm
      (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
        (posteriorMean J τ p.2.1 - p.1))) with hG_map_def
  have hG_map_meas : Measurable G_map :=
    hAμ.comp ((hμ.comp (measurable_fst.comp measurable_snd)).sub measurable_fst)
  set G_map' : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
      → EuclideanSpace ℝ (Fin d) :=
    fun p => (WithLp.equiv 2 (Fin d → ℝ)).symm
      (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
        (posteriorMean J τ p.2 - p.1))) with hG_map'_def
  have hG_map'_meas : Measurable G_map' :=
    hAμ.comp ((hμ.comp measurable_snd).sub measurable_fst)
  unfold G_Lambda_law jointHXY
  set μ_HX : Measure (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
    (πτ.prod ν_J).map (shiftCLM k) with hμHX_def
  set K_T : Kernel (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
      (EuclideanSpace ℝ (Fin d)) := T.comap Prod.snd measurable_snd with hKT_def
  haveI : SFinite μ_HX := by rw [hμHX_def]; infer_instance
  haveI : IsMarkovKernel K_T := by rw [hKT_def]; infer_instance
  set rebracket : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
      × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
        × EuclideanSpace ℝ (Fin d) :=
    fun q => (q.1.1, q.1.2, q.2) with hrebracket_def
  have hrebracket_meas : Measurable rebracket := by fun_prop
  change ((μ_HX ⊗ₘ K_T).map rebracket).map G_map
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (A * posteriorCov J τ * A.transpose)
  rw [Measure.map_map hG_map_meas hrebracket_meas]
  have h_factor : (G_map ∘ rebracket) = (G_map' ∘ Prod.fst) := by
    funext q
    rfl
  rw [h_factor, ← Measure.map_map hG_map'_meas measurable_fst]
  have h_fst_compProd : (μ_HX ⊗ₘ K_T).map Prod.fst = μ_HX := by
    have := Measure.fst_compProd μ_HX K_T
    simpa [Measure.fst] using this
  rw [h_fst_compProd]
  have h_joint :
      μ_HX = ((π_X.prod ν_S).map (posteriorCLM J τ)) := by
    rw [hμHX_def, hπτ_def, hν_J_def, hπ_X_def, hν_S_def]
    exact joint_pushforward_eq hJ hτ
  rw [h_joint]
  rw [Measure.map_map hG_map'_meas (posteriorCLM J τ).continuous.measurable]
  have h_compose : ((G_map' ∘ ⇑(posteriorCLM J τ)) : _ → EuclideanSpace ℝ (Fin d))
      = (matrixToEuclideanCLMRect (-A) ∘ Prod.snd) := by
    funext p
    change (WithLp.equiv 2 (Fin d → ℝ)).symm
        (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
          (posteriorMean J τ (posteriorCLM J τ (p.1, p.2)).2
              - (posteriorCLM J τ (p.1, p.2)).1)))
      = matrixToEuclideanCLMRect (-A) (Prod.snd (p.1, p.2))
    rw [posteriorCLM_apply]
    have h_sub : posteriorMean J τ p.1 - (p.2 + posteriorMean J τ p.1) = -p.2 := by
      abel
    rw [h_sub]
    change (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (-p.2)))
        = matrixToEuclideanCLMRect (-A) p.2
    rw [show ((WithLp.equiv 2 (Fin k → ℝ)) (-p.2))
        = -((WithLp.equiv 2 (Fin k → ℝ)) p.2) from by rfl,
        Matrix.mulVec_neg,
        show ((WithLp.equiv 2 (Fin d → ℝ)).symm (-(A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) p.2))))
          = -((WithLp.equiv 2 (Fin d → ℝ)).symm
              (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) p.2))) from by rfl]
    show -((WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) p.2)))
        = matrixToEuclideanCLMRect (-A) p.2
    rw [show matrixToEuclideanCLMRect (-A) p.2
          = (WithLp.equiv 2 (Fin d → ℝ)).symm ((-A).mulVec ((WithLp.equiv 2 (Fin k → ℝ)) p.2))
        from rfl, Matrix.neg_mulVec]
    rfl
  rw [h_compose]
  rw [← Measure.map_map (matrixToEuclideanCLMRect (-A)).continuous.measurable
      measurable_snd]
  rw [show (π_X.prod ν_S).map Prod.snd = ν_S from by
    rw [Measure.map_snd_prod, measure_univ, one_smul]]
  rw [hν_S_def]
  rw [multivariateGaussian_map_rectangular (-A) 0 (posteriorCov_posDef hJ hτ).posSemidef]
  congr 1
  · exact (matrixToEuclideanCLMRect (-A)).map_zero
  · simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg]
    exact neg_neg _

/-- **Bayesian 3D reparametrization of `jointHXY`** (consumed
by `G_Lambda_indep_W_Lambda`).

Under the joint `(H, X, Y)` measure with prior `H ∼ N(0, τ²·I)`, likelihood
`X | H ∼ N(H, J⁻¹)`, and randomization kernel `Y | X ∼ T(X)`, change
variables `g := H − posteriorMean J τ X`. In the new parametrization:
* `g ∼ N(0, posteriorCov J τ) =: ν_S` (Bayesian posterior, X-independent),
* `(X, Y) ∼ (marginalGaussianShift J τ) ⊗ₘ T =: μ_XY` (joint marginal),
* `g ⊥ (X, Y)`.

The reverse map `(g, (x, y)) ↦ (g + posteriorMean J τ x, x, y)` recovers
`jointHXY` from `ν_S × μ_XY`. This is the 3D extension of
`joint_pushforward_eq` (the 2D `(H, X)` version in
`GaussianShiftMinimax.lean`); the proof glues `joint_pushforward_eq` with
`compProd_apply`, `lintegral_map`, and Fubini swap. **Sketch**:
`jointHXY S = ∫⁻ (x, g) ∂(π_X × ν_S), T x ({y | (g + μ(x), x, y) ∈ S})`
(via `lintegral_compProd`, `lintegral_map` with `posteriorCLM`, and
`joint_pushforward_eq`), which by Fubini swap equals
`∫⁻ g ∂ν_S, ∫⁻ x ∂π_X, T x ({y | (g + μ(x), x, y) ∈ S})`,
matching `(ν_S × (π_X ⊗ T)).map pull S` via `lintegral_compProd`.

The gluing requires careful kernel-measurability arguments via
`Kernel.measurable_kernel_prodMk_left`. -/
private lemma jointHXY_eq_reparam
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ : ℝ} (hτ : 0 < τ)
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel T] :
    jointHXY J τ T
      = ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (posteriorCov J τ)).prod
          (marginalGaussianShift J τ ⊗ₘ T)).map
          (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
              × EuclideanSpace ℝ (Fin d) =>
            (p.1 + posteriorMean J τ p.2.1, p.2.1, p.2.2)) := by
  -- Setup notation.
  set πτ : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
      ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ)) with hπτ_def
  set ν_J : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹ with hν_J_def
  set ν_S : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (posteriorCov J τ) with hν_S_def
  set π_X : Measure (EuclideanSpace ℝ (Fin k)) := marginalGaussianShift J τ with hπ_X_def
  haveI : IsProbabilityMeasure πτ := by rw [hπτ_def]; infer_instance
  haveI : IsProbabilityMeasure ν_J := by rw [hν_J_def]; infer_instance
  haveI : IsProbabilityMeasure ν_S := by rw [hν_S_def]; infer_instance
  haveI : IsProbabilityMeasure π_X := by
    rw [hπ_X_def, marginalGaussianShift]; infer_instance
  set μ_HX : Measure (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
    (πτ.prod ν_J).map (shiftCLM k) with hμHX_def
  set K_T : Kernel (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
      (EuclideanSpace ℝ (Fin d)) := T.comap Prod.snd measurable_snd with hKT_def
  haveI : SFinite μ_HX := by rw [hμHX_def]; infer_instance
  haveI : IsMarkovKernel K_T := by rw [hKT_def]; infer_instance
  haveI : IsProbabilityMeasure (π_X ⊗ₘ T) := inferInstance
  -- Measurability bricks.
  have hμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) => posteriorMean J τ x) :=
    (matrixToEuclideanCLMRect (posteriorCov J τ * J)).continuous.measurable
  set rebracket : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
      × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
        × EuclideanSpace ℝ (Fin d) :=
    fun q => (q.1.1, q.1.2, q.2) with hrebracket_def
  have hrebracket_meas : Measurable rebracket := by fun_prop
  set pull : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
      × EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin d) :=
    fun p => (p.1 + posteriorMean J τ p.2.1, p.2.1, p.2.2) with hpull_def
  have hpull_meas : Measurable pull := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact measurable_fst.add (hμ.comp (measurable_fst.comp measurable_snd))
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
  -- Joint pushforward identity for (H, X) marginal (2D version).
  have h_joint :
      μ_HX = ((π_X.prod ν_S).map (posteriorCLM J τ)) := by
    rw [hμHX_def, hπτ_def, hν_J_def, hπ_X_def, hν_S_def]
    exact joint_pushforward_eq hJ hτ
  -- Reduce both sides to integrals over a measurable set `S`.
  ext S hS
  -- LHS computation.
  unfold jointHXY
  -- Use the `set` abbreviations.
  change ((μ_HX ⊗ₘ K_T).map rebracket) S
      = (((ν_S).prod (π_X ⊗ₘ T)).map pull) S
  rw [Measure.map_apply hrebracket_meas hS]
  -- Now LHS = (μ_HX ⊗ₘ K_T) (rebracket ⁻¹' S).
  set s_cyl : Set ((EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
      × EuclideanSpace ℝ (Fin d)) := rebracket ⁻¹' S with hs_cyl_def
  have hs_cyl_meas : MeasurableSet s_cyl := hrebracket_meas hS
  rw [Measure.compProd_apply hs_cyl_meas]
  -- For each (h, x), K_T (h, x) (Prod.mk (h, x) ⁻¹' s_cyl) = T x ({y | (h, x, y) ∈ S}).
  have h_slice : ∀ p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k),
      K_T p (Prod.mk p ⁻¹' s_cyl)
        = T p.2 ({y : EuclideanSpace ℝ (Fin d) | (p.1, p.2, y) ∈ S}) := by
    intro p
    rw [hKT_def, Kernel.comap_apply]
    rfl
  simp_rw [h_slice]
  -- Now LHS = ∫⁻ p ∂μ_HX, T p.2 ({y | (p.1, p.2, y) ∈ S}).
  -- Substitute μ_HX = (π_X.prod ν_S).map posteriorCLM.
  rw [h_joint]
  -- Measurability of the integrand (a function of (h, x)).
  have h_intgr_meas : Measurable (fun p : EuclideanSpace ℝ (Fin k) ×
      EuclideanSpace ℝ (Fin k) => T p.2 ({y : EuclideanSpace ℝ (Fin d) |
        (p.1, p.2, y) ∈ S})) := by
    -- The integrand is `(fun p => K_T p (Prod.mk p ⁻¹' s_cyl))`, which is measurable
    -- by `Kernel.measurable_kernel_prodMk_left` applied to `K_T`.
    have h := Kernel.measurable_kernel_prodMk_left (κ := K_T) hs_cyl_meas
    -- `h : Measurable fun p => K_T p (Prod.mk p ⁻¹' s_cyl)`.
    -- By `h_slice`, this equals the goal pointwise.
    have h_eq : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        K_T p (Prod.mk p ⁻¹' s_cyl))
        = fun p => T p.2 ({y : EuclideanSpace ℝ (Fin d) | (p.1, p.2, y) ∈ S}) := by
      funext p
      exact h_slice p
    rw [h_eq] at h
    exact h
  -- Apply lintegral_map to push the integrand through posteriorCLM.
  rw [lintegral_map h_intgr_meas (posteriorCLM J τ).continuous.measurable]
  -- Now LHS = ∫⁻ q ∂(π_X.prod ν_S), T (posteriorCLM q).2 ({y | (posteriorCLM q.1, (posteriorCLM
  -- q).2, y) ∈ S}).
  -- Simplify via posteriorCLM_apply: (posteriorCLM (x, g)) = (g + μ(x), x).
  -- The integrand at q has shape `T (posteriorCLM J τ q).2 ({y | ((posteriorCLM J τ q).1,
  -- (posteriorCLM J τ q).2, y) ∈ S})`.
  -- Use `lintegral_congr` to rewrite at each q.
  have h_lhs_rewrite : ∀ q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k),
      T (posteriorCLM J τ q).2 ({y : EuclideanSpace ℝ (Fin d) |
        ((posteriorCLM J τ q).1, (posteriorCLM J τ q).2, y) ∈ S})
        = T q.1 ({y : EuclideanSpace ℝ (Fin d) |
          (q.2 + posteriorMean J τ q.1, q.1, y) ∈ S}) := by
    intro q
    rw [show posteriorCLM J τ q = (q.2 + posteriorMean J τ q.1, q.1) from by
      rcases q with ⟨x, g⟩; rw [posteriorCLM_apply]]
  simp_rw [h_lhs_rewrite]
  -- Now LHS = ∫⁻ q ∂(π_X.prod ν_S), T q.1 ({y | (q.2 + μ(q.1), q.1, y) ∈ S}).
  -- Apply Fubini via lintegral_prod (with x : π_X outer, g : ν_S inner).
  have h_intgr_meas' : Measurable (fun q : EuclideanSpace ℝ (Fin k) ×
      EuclideanSpace ℝ (Fin k) => T q.1 ({y : EuclideanSpace ℝ (Fin d) |
        (q.2 + posteriorMean J τ q.1, q.1, y) ∈ S})) := by
    -- This is `h_intgr_meas` composed with the swap-like map `q ↦ posteriorCLM q`.
    have := h_intgr_meas.comp (posteriorCLM J τ).continuous.measurable
    -- `this : Measurable (fun q => T (posteriorCLM q).2 ({y | ((posteriorCLM q).1, (posteriorCLM
    -- q).2, y) ∈ S}))`.
    -- By `posteriorCLM_apply`, `(posteriorCLM (x, g)) = (g + μ(x), x)`, so `.2 = x` and `.1 = g +
    -- μ(x)`.
    exact this
  rw [MeasureTheory.lintegral_prod _ h_intgr_meas'.aemeasurable]
  -- Now LHS = ∫⁻ x ∂π_X, ∫⁻ g ∂ν_S, T x ({y | (g + μ(x), x, y) ∈ S}).
  -- Swap the order of integration: ν_S outer, π_X inner.
  rw [MeasureTheory.lintegral_lintegral_swap h_intgr_meas'.aemeasurable]
  -- Now LHS = ∫⁻ g ∂ν_S, ∫⁻ x ∂π_X, T x ({y | (g + μ(x), x, y) ∈ S}).
  -- RHS computation.
  rw [Measure.map_apply hpull_meas hS]
  -- Now RHS = (ν_S.prod (π_X ⊗ₘ T)) (pull ⁻¹' S).
  rw [Measure.prod_apply (hpull_meas hS)]
  -- Now RHS = ∫⁻ g ∂ν_S, (π_X ⊗ₘ T) (Prod.mk g ⁻¹' (pull ⁻¹' S)).
  -- For each g, simplify the slice and apply compProd_apply.
  congr 1
  funext g
  have h_slice2 : Prod.mk g ⁻¹' (pull ⁻¹' S)
      = {q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin d) |
          (g + posteriorMean J τ q.1, q.1, q.2) ∈ S} := by
    ext q
    simp [hpull_def]
  have hslice_meas : MeasurableSet
      {q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin d) |
        (g + posteriorMean J τ q.1, q.1, q.2) ∈ S} := by
    rw [← h_slice2]
    exact measurable_prodMk_left (hpull_meas hS)
  rw [h_slice2, Measure.compProd_apply hslice_meas]
  -- Now RHS = ∫⁻ x ∂π_X, T x (Prod.mk x ⁻¹' {q | (g + μ(q.1), q.1, q.2) ∈ S}).
  -- Each slice = {y | (g + μ(x), x, y) ∈ S}. These are defeq.
  rfl

/-- **Key independence statement.**
`G_Λ ⟂ W_Λ`, i.e. the joint law factors as the product of marginals.

vdV §8.4: "These vectors are independent, because W_Λ is a
function of (X, U) only, and the conditional distribution of G_Λ given X
is normal with mean 0 and covariance matrix A(Σ⁻¹ + Λ⁻¹)⁻¹ Aᵀ,
independent of X."

**Proof structure** (via `jointHXY_eq_reparam`):
1. Substitute `jointHXY = reparam.map pull` where
   `reparam = ν_S × (π_X ⊗ T)` and `pull(g, (x, y)) = (g + μ(x), x, y)`.
2. After substitution: `joint_GW_law = reparam.map (joint_GW_map ∘ pull)`,
   and `(joint_GW_map ∘ pull)(g, (x, y)) = (−A·g, y − A·μ(x))`,
   i.e. `Prod.map G_lift W_lift` where `G_lift g := matrixToEuclideanCLMRect (−A) g`
   and `W_lift (x, y) := y − A·μ(x)`.
3. Similarly `G_Lambda_law = ν_S.map G_lift`, `W_Lambda_law = (π_X ⊗ T).map W_lift`.
4. By `Measure.map_prod_map`,
   `(ν_S.map G_lift).prod ((π_X ⊗ T).map W_lift) = (ν_S × (π_X ⊗ T)).map (Prod.map G_lift W_lift)`,
   which equals `reparam.map (joint_GW_map ∘ pull) = joint_GW_law`. -/
theorem G_Lambda_indep_W_Lambda
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ : ℝ} (hτ : 0 < τ)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel T] :
    joint_GW_law J τ A T
      = (G_Lambda_law J τ A T).prod (W_Lambda_law J τ A T) := by
  -- Notation.
  set ν_S : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (posteriorCov J τ) with hν_S_def
  set π_X : Measure (EuclideanSpace ℝ (Fin k)) := marginalGaussianShift J τ with hπ_X_def
  haveI : IsProbabilityMeasure ν_S := by rw [hν_S_def]; infer_instance
  haveI : IsProbabilityMeasure π_X := by
    rw [hπ_X_def, marginalGaussianShift]; infer_instance
  haveI : IsProbabilityMeasure (π_X ⊗ₘ T) := inferInstance
  -- Measurability.
  have hAμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) =>
      (WithLp.equiv 2 (Fin d → ℝ)).symm
        (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) x))) :=
    (matrixToEuclideanCLMRect A).continuous.measurable
  have hμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) => posteriorMean J τ x) :=
    (matrixToEuclideanCLMRect (posteriorCov J τ * J)).continuous.measurable
  -- The pull map.
  set pull : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
      × EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin d) :=
    fun p => (p.1 + posteriorMean J τ p.2.1, p.2.1, p.2.2) with hpull_def
  have hpull_meas : Measurable pull := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact measurable_fst.add (hμ.comp (measurable_fst.comp measurable_snd))
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
  -- G_lift and W_lift.
  set G_lift : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin d) :=
    fun g => matrixToEuclideanCLMRect (-A) g with hG_lift_def
  have hG_lift_meas : Measurable G_lift :=
    (matrixToEuclideanCLMRect (-A)).continuous.measurable
  set W_lift : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin d)
      → EuclideanSpace ℝ (Fin d) :=
    fun q => q.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
      (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (posteriorMean J τ q.1))) with hW_lift_def
  have hW_lift_meas : Measurable W_lift :=
    measurable_snd.sub (hAμ.comp (hμ.comp measurable_fst))
  -- Joint GW law unfolded.
  unfold joint_GW_law
  -- Substitute jointHXY = reparam.map pull.
  rw [jointHXY_eq_reparam hJ hτ T]
  -- LHS now: (reparam.map pull).map joint_GW_map
  rw [Measure.map_map (by
    refine Measurable.prodMk ?_ ?_
    · exact hAμ.comp ((hμ.comp (measurable_fst.comp measurable_snd)).sub measurable_fst)
    · exact (measurable_snd.comp measurable_snd).sub
        (hAμ.comp (hμ.comp (measurable_fst.comp measurable_snd)))) hpull_meas]
  -- Now: reparam.map (joint_GW_map ∘ pull).
  -- Identify: joint_GW_map ∘ pull = Prod.map G_lift W_lift ∘ (fst, snd reformulation).
  -- Actually the pair: ((joint_GW_map ∘ pull) (g, (x, y))) = (G_lift g, W_lift (x, y)).
  -- This is `Prod.map G_lift W_lift (g, (x, y))`.
  have h_factor :
      ((fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
            × EuclideanSpace ℝ (Fin d) =>
          ((WithLp.equiv 2 (Fin d → ℝ)).symm
              (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
                (posteriorMean J τ p.2.1 - p.1))),
           p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
              (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (posteriorMean J τ p.2.1))))) ∘ pull)
        = Prod.map G_lift W_lift := by
    funext q
    change ((WithLp.equiv 2 (Fin d → ℝ)).symm
        (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
          (posteriorMean J τ (pull q).2.1 - (pull q).1))),
         (pull q).2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (posteriorMean J τ (pull q).2.1))))
      = (G_lift q.1, W_lift q.2)
    simp only [hpull_def]
    refine Prod.ext ?_ ?_
    · -- A·(μ(x) - (g+μ(x))) = -A·g = G_lift g
      have h_sub : posteriorMean J τ q.2.1 - (q.1 + posteriorMean J τ q.2.1) = -q.1 := by
        abel
      change (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
            (posteriorMean J τ q.2.1 - (q.1 + posteriorMean J τ q.2.1))))
        = matrixToEuclideanCLMRect (-A) q.1
      rw [h_sub]
      -- Now LHS = (WithLp⁻¹) (A · (WithLp (-q.1))) = (WithLp⁻¹) (- A·(WithLp q.1)) = -
      -- (matrixToEuclideanCLMRect A q.1)
      -- RHS = matrixToEuclideanCLMRect (-A) q.1 = (WithLp⁻¹) ((-A)·(WithLp q.1)) = (WithLp⁻¹) (-
      -- A·(WithLp q.1))
      show (WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (-q.1)))
          = matrixToEuclideanCLMRect (-A) q.1
      rw [show ((WithLp.equiv 2 (Fin k → ℝ)) (-q.1))
          = -((WithLp.equiv 2 (Fin k → ℝ)) q.1) from by rfl,
          Matrix.mulVec_neg,
          show ((WithLp.equiv 2 (Fin d → ℝ)).symm (-(A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) q.1))))
            = -((WithLp.equiv 2 (Fin d → ℝ)).symm
                (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) q.1))) from by rfl]
      show -((WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) q.1)))
          = matrixToEuclideanCLMRect (-A) q.1
      rw [show matrixToEuclideanCLMRect (-A) q.1
            = (WithLp.equiv 2 (Fin d → ℝ)).symm ((-A).mulVec ((WithLp.equiv 2 (Fin k → ℝ)) q.1))
          from rfl, Matrix.neg_mulVec]
      rfl
    · -- W_lift (q.2.1, q.2.2) = q.2.2 - A·μ(q.2.1)
      rfl
  rw [h_factor]
  -- LHS now: reparam.map (Prod.map G_lift W_lift) = (ν_S × (π_X ⊗ T)).map (Prod.map G_lift W_lift).
  -- By `Measure.map_prod_map`, this equals (ν_S.map G_lift).prod ((π_X ⊗ T).map W_lift).
  rw [← Measure.map_prod_map ν_S (π_X ⊗ₘ T) hG_lift_meas hW_lift_meas]
  -- Now: (ν_S.map G_lift).prod ((π_X ⊗ T).map W_lift) = (G_Lambda_law).prod (W_Lambda_law).
  -- We need to identify G_Lambda_law and W_Lambda_law.
  congr 1
  · -- ν_S.map G_lift = G_Lambda_law (note direction).
    -- G_Lambda_law J τ A T = mvg 0 (A · posteriorCov · Aᵀ) by G_Lambda_cond_X_eq_gaussian.
    -- And ν_S.map G_lift = (mvg 0 posteriorCov).map (matrixToEuclideanCLMRect (-A))
    --                    = mvg 0 (A · posteriorCov · Aᵀ) by multivariateGaussian_map_rectangular
    --                      + sign cancellation.
    rw [G_Lambda_cond_X_eq_gaussian hJ hτ A T, hν_S_def, hG_lift_def]
    rw [multivariateGaussian_map_rectangular (-A) 0 (posteriorCov_posDef hJ hτ).posSemidef]
    congr 1
    · exact (matrixToEuclideanCLMRect (-A)).map_zero
    · simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg]
      exact neg_neg _
  · -- (π_X ⊗ T).map W_lift = W_Lambda_law (note direction).
    -- W_Lambda_law = jointHXY.map W_map_full where W_map_full(h, x, y) = y - A·μ(x).
    -- Using jointHXY_eq_reparam, this equals reparam.map (W_map_full ∘ pull)
    -- = reparam.map ((W_lift ∘ Prod.snd)) (since W_map_full ignores h)
    -- = (reparam.map Prod.snd).map W_lift
    -- = (π_X ⊗ T).map W_lift  [via map_snd_prod].
    symm
    show (W_Lambda_law J τ A T) = (π_X ⊗ₘ T).map W_lift
    unfold W_Lambda_law
    rw [jointHXY_eq_reparam hJ hτ T]
    rw [Measure.map_map (by
      exact (measurable_snd.comp measurable_snd).sub
        (hAμ.comp (hμ.comp (measurable_fst.comp measurable_snd)))) hpull_meas]
    have h_factor_W :
        ((fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
              × EuclideanSpace ℝ (Fin d) =>
            p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
              (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (posteriorMean J τ p.2.1)))) ∘ pull)
          = W_lift ∘ Prod.snd := by
      funext q
      rfl
    rw [h_factor_W, ← Measure.map_map hW_lift_meas measurable_snd]
    congr 1
    rw [Measure.map_snd_prod, measure_univ, one_smul]

/-! ## Step 3: Levy continuity assembly

### Step 3a: equivariance gives the joint law of `T − A·H` is `L` for every Λ.
-/

/-- Under equivariance, the law of `T − A·H` under the joint
`(H, X, Y)` measure (prior `π_τ`, likelihood, kernel) equals the null
distribution `L`, for every `τ > 0`. (vdV §8.4: "the distribution
of G_Λ + W_Λ = T − AH is L, for every Λ", which uses the fact that
averaging over a Gaussian-prior `h` is the same as the prior average of
the equivariance-invariant law.) -/
theorem T_minus_AH_law_eq_L_under_prior
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ : ℝ} (hτ : 0 < τ)
    {A : Matrix (Fin d) (Fin k) ℝ}
    {T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))}
    [IsMarkovKernel T]
    (hT_equiv : IsEquivariantInLaw T A J⁻¹) :
    (jointHXY J τ T).map (fun p =>
        p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) p.1)))
      = hT_equiv.nullDist := by
  -- Strategy: `jointHXY = (μ_HX ⊗ₘ K_T).map rebracket`, where
  --   μ_HX := (πτ × ν_J).map shiftCLM,  K_T := T.comap Prod.snd,
  --   rebracket ((h,x), y) := (h, x, y).
  -- The post-composition `f ∘ rebracket : ((h, x), y) ↦ y − A·h` does not
  -- depend on `x`. Apply `Measure.ext`, `Measure.map_apply` twice, then
  -- `Measure.compProd_apply` to get an iterated integral. Push through
  -- `μ_HX = (πτ × ν_J).map shiftCLM` via `lintegral_map`, then apply
  -- Fubini (`lintegral_prod`). The inner integrand collapses to
  -- `(T ∘ₘ mvg h J⁻¹) ((· − A·h) ⁻¹' s)` via `multivariateGaussian_eq_translate`,
  -- which is `hT_equiv.nullDist s` by `map_sub_eq_nullDist`.
  let _hJ := hJ
  let _hτ := hτ
  set πτ : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
      ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ)) with hπτ_def
  set ν_J : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹ with hν_J_def
  set μ_HX : Measure (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
    (πτ.prod ν_J).map (shiftCLM k) with hμHX_def
  set K_T : Kernel (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
      (EuclideanSpace ℝ (Fin d)) := T.comap Prod.snd measurable_snd with hKT_def
  set f : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
      × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun p => p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
      (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) p.1)) with hf_def
  have hAμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) =>
      (WithLp.equiv 2 (Fin d → ℝ)).symm
        (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) x))) :=
    (matrixToEuclideanCLMRect A).continuous.measurable
  have hf_meas : Measurable f :=
    (measurable_snd.comp measurable_snd).sub (hAμ.comp measurable_fst)
  -- Instances for compProd / Fubini.
  haveI : IsProbabilityMeasure πτ := by rw [hπτ_def]; infer_instance
  haveI : IsProbabilityMeasure ν_J := by rw [hν_J_def]; infer_instance
  haveI : SFinite μ_HX := by rw [hμHX_def]; infer_instance
  haveI : IsMarkovKernel K_T := by rw [hKT_def]; infer_instance
  -- Now compute the LHS of the goal via `compProd_apply` + Fubini.
  ext s' hs'
  -- Reduce per-`h` to `nullDist s'` via the equivariance hypothesis.
  -- For any `h`, `((mvg h J⁻¹).bind T).map (· − A·h) = nullDist` (by hT_equiv).
  -- Translating mvg h to ν_J + shift gives:
  --   ∫ ε, (T (h+ε)) ((· − A·h) ⁻¹' s') ∂ν_J = nullDist s'.
  have hPer : ∀ h : EuclideanSpace ℝ (Fin k),
      ∫⁻ ε, (T (h + ε))
          ((fun y : EuclideanSpace ℝ (Fin d) => y -
            (WithLp.equiv 2 (Fin d → ℝ)).symm
              (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h))) ⁻¹' s') ∂ν_J
        = hT_equiv.nullDist s' := by
    intro h
    have h_sub_meas : Measurable (fun y : EuclideanSpace ℝ (Fin d) => y -
        (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h))) := by fun_prop
    have h_null := hT_equiv.map_sub_eq_nullDist h
    have h_null_s : ((T ∘ₘ (multivariateGaussian h J⁻¹)).map
        (fun y : EuclideanSpace ℝ (Fin d) => y -
          (WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h)))) s' = hT_equiv.nullDist s' := by
      rw [h_null]
    rw [Measure.map_apply h_sub_meas hs',
        Measure.bind_apply (h_sub_meas hs') T.measurable.aemeasurable,
        multivariateGaussian_eq_translate h J⁻¹,
        lintegral_map (T.measurable_coe (h_sub_meas hs')) (measurable_const_add h)]
        at h_null_s
    exact h_null_s
  rw [Measure.map_apply hf_meas hs']
  unfold jointHXY
  change ((μ_HX ⊗ₘ K_T).map (fun q : (EuclideanSpace ℝ (Fin k) ×
      EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin d) =>
        (q.1.1, q.1.2, q.2))) (f ⁻¹' s') = hT_equiv.nullDist s'
  rw [Measure.map_apply (by fun_prop) (hf_meas hs')]
  -- The preimage of `f ⁻¹' s'` under `rebracket` is `{q | q.2 − A·q.1.1 ∈ s'}`.
  -- Set `s_cyl := this preimage`.
  set s_cyl : Set ((EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
      × EuclideanSpace ℝ (Fin d)) :=
    (fun q : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
        × EuclideanSpace ℝ (Fin d) => (q.1.1, q.1.2, q.2)) ⁻¹' (f ⁻¹' s') with hs_cyl_def
  have hs_cyl_meas : MeasurableSet s_cyl := by
    refine MeasurableSet.preimage ?_ (by fun_prop)
    exact hf_meas hs'
  -- Apply `compProd_apply`.
  rw [Measure.compProd_apply hs_cyl_meas]
  -- For each `p = (h, x)`, `K_T p (Prod.mk p ⁻¹' s_cyl) = T x (slice for h)`.
  -- Simplify the slice: `(Prod.mk (h, x)) ⁻¹' s_cyl = {y | f (h, x, y) ∈ s'} =
  --   {y | y − A·h ∈ s'} = (· − A·h) ⁻¹' s'`.
  have h_slice : ∀ p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k),
      K_T p (Prod.mk p ⁻¹' s_cyl)
        = (T p.2) ((fun y : EuclideanSpace ℝ (Fin d) => y -
            (WithLp.equiv 2 (Fin d → ℝ)).symm
              (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) p.1))) ⁻¹' s') := by
    intro p
    rw [hKT_def, Kernel.comap_apply]
    rfl
  simp_rw [h_slice]
  -- Now: ∫⁻ p, (T p.2) ((· − A·p.1) ⁻¹' s') ∂μ_HX = nullDist s'.
  -- Unfold `μ_HX = (πτ.prod ν_J).map shiftCLM`.
  rw [hμHX_def]
  have h_intgr_meas : Measurable (fun p : EuclideanSpace ℝ (Fin k) ×
      EuclideanSpace ℝ (Fin k) => (T p.2) ((fun y : EuclideanSpace ℝ (Fin d) =>
        y - (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) p.1))) ⁻¹' s')) := by
    -- This is a Kernel-coe `(T x) U_h` where `U_h` depends on `h` measurably.
    -- Apply `measurable_kernel_prodMk_left` to `K_T = T.comap Prod.snd` on the
    -- set `{((h, x), y) | y − A·h ∈ s'}`.
    have h_sub_joint : Measurable (fun py : (EuclideanSpace ℝ (Fin k) ×
        EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin d) =>
          py.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) py.1.1))) :=
      measurable_snd.sub (hAμ.comp (measurable_fst.comp measurable_fst))
    have h_prod_set : MeasurableSet
        {py : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
            × EuclideanSpace ℝ (Fin d) |
          py.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) py.1.1)) ∈ s'} :=
      h_sub_joint hs'
    have := Kernel.measurable_kernel_prodMk_left (κ := K_T) h_prod_set
    -- `this : Measurable (fun p => K_T p (Prod.mk p ⁻¹' s_set))`.
    -- This is defeq to the goal: unfolding `K_T = T.comap Prod.snd` gives
    -- `(T p.2) (Prod.mk p ⁻¹' …)`, which simp-reduces to the goal.
    convert! this using 1
  rw [lintegral_map h_intgr_meas (shiftCLM k).continuous.measurable]
  -- Now integrate over `πτ.prod ν_J`. Use Fubini.
  have hF_meas : Measurable (fun a : EuclideanSpace ℝ (Fin k) ×
      EuclideanSpace ℝ (Fin k) => (T ((shiftCLM k) a).2)
        ((fun y : EuclideanSpace ℝ (Fin d) =>
          y - (WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) ((shiftCLM k) a).1))) ⁻¹' s')) :=
    h_intgr_meas.comp (shiftCLM k).continuous.measurable
  rw [MeasureTheory.lintegral_prod _ hF_meas.aemeasurable]
  -- The integrand at `(h, ε)` is `(T (h+ε)) ((· − A·h) ⁻¹' s')`.
  -- (Since `(shiftCLM k) (h, ε) = (h, h+ε)`, and `.snd = h+ε`, `.fst = h`.)
  simp_rw [shiftCLM_apply]
  -- Inner integral = `hPer h`.
  simp_rw [hPer]
  -- Outer integral = `nullDist s' * (πτ Set.univ) = nullDist s' * 1 = nullDist s'`.
  rw [MeasureTheory.lintegral_const, measure_univ, mul_one]

/-! ### Step 3b: charFun factorization

vdV §8.4: `L̂(t) = Ĝ_Λ(t) · Ŵ_Λ(t)` for every `t`. -/

/-- charFun factorization on the null distribution:
`L̂(t) = (charFun (G_Λ_law)) t · (charFun (W_Λ_law)) t`. Derived from the
sum identity `G_plus_W_eq_T_minus_AH` + independence `G_Lambda_indep_W_Lambda`
+ Mathlib's `charFun_conv` (since `(G_Λ + W_Λ).law = G_Λ.law ∗ W_Λ.law` by
independence). -/
theorem hatL_eq_hatG_mul_hatW
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {τ : ℝ} (hτ : 0 < τ)
    {A : Matrix (Fin d) (Fin k) ℝ}
    {T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))}
    [IsMarkovKernel T]
    (hT_equiv : IsEquivariantInLaw T A J⁻¹)
    (t : EuclideanSpace ℝ (Fin d)) :
    charFun hT_equiv.nullDist t
      = charFun (G_Lambda_law J τ A T) t * charFun (W_Lambda_law J τ A T) t := by
  -- Set up probability-measure instances for the marginals.
  haveI : IsProbabilityMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
        ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))) := inferInstance
  haveI : IsProbabilityMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := inferInstance
  -- `jointHXY` is a probability measure: pushforward of a compProd of a product
  -- probability with a Markov kernel.
  haveI h_joint_prob : IsProbabilityMeasure (jointHXY J τ T) := by
    unfold jointHXY
    refine Measure.isProbabilityMeasure_map ?_
    fun_prop
  -- Marginal measurabilities (needed for `isProbabilityMeasure_map`).
  have hμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) => posteriorMean J τ x) :=
    (matrixToEuclideanCLMRect (posteriorCov J τ * J)).continuous.measurable
  have hAμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) =>
      (WithLp.equiv 2 (Fin d → ℝ)).symm
        (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) x))) :=
    (matrixToEuclideanCLMRect A).continuous.measurable
  have hG_meas : Measurable (fun p : EuclideanSpace ℝ (Fin k) ×
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin d) =>
        (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
            (posteriorMean J τ p.2.1 - p.1)))) :=
    hAμ.comp ((hμ.comp (measurable_fst.comp measurable_snd)).sub measurable_fst)
  have hW_meas : Measurable (fun p : EuclideanSpace ℝ (Fin k) ×
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin d) =>
        p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (posteriorMean J τ p.2.1)))) :=
    (measurable_snd.comp measurable_snd).sub (hAμ.comp (hμ.comp
      (measurable_fst.comp measurable_snd)))
  haveI : IsProbabilityMeasure (G_Lambda_law J τ A T) := by
    unfold G_Lambda_law
    exact Measure.isProbabilityMeasure_map hG_meas.aemeasurable
  haveI : IsProbabilityMeasure (W_Lambda_law J τ A T) := by
    unfold W_Lambda_law
    exact Measure.isProbabilityMeasure_map hW_meas.aemeasurable
  -- Step 1: rewrite `nullDist` as the sum-pushforward of joint_GW_law.
  have h_eq1 : hT_equiv.nullDist
      = (joint_GW_law J τ A T).map (fun p => p.1 + p.2) := by
    rw [G_plus_W_eq_T_minus_AH hJ hτ A T,
        T_minus_AH_law_eq_L_under_prior hJ hτ hT_equiv]
  -- Step 2: by independence, `joint_GW_law = (G_Λ_law).prod (W_Λ_law)`.
  have h_eq2 : (joint_GW_law J τ A T).map (fun p => p.1 + p.2)
      = ((G_Lambda_law J τ A T).prod (W_Lambda_law J τ A T)).map
          (fun p => p.1 + p.2) := by
    rw [G_Lambda_indep_W_Lambda hJ hτ A T]
  -- Step 3: Mathlib's `charFun_map_add_prod_eq_mul`.
  rw [h_eq1, h_eq2, charFun_map_add_prod_eq_mul, Pi.mul_apply]

/-! ### Step 3c: `Ĝ_Λ → Ĝ` (charFun continuity in covariance) + `Ĝ` nowhere zero.
-/

/-- charFun of `multivariateGaussian 0 C` is continuous
in the (PSD) matrix `C` — pointwise in the test point `t`, jointly
continuous as `C → C'`. (Direct from `charFun_multivariateGaussian` +
continuity of `t ↦ exp(−t · C · t / 2)` in `C`.) -/
theorem multivariateGaussian_charFun_continuous_in_cov
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : EuclideanSpace ℝ ι)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {C_seq : ℕ → Matrix ι ι ℝ}
    (hC_seq : ∀ᶠ n in atTop, (C_seq n).PosSemidef)
    (h_tend : Tendsto C_seq atTop (𝓝 C)) :
    Tendsto (fun n =>
        charFun (multivariateGaussian (0 : EuclideanSpace ℝ ι) (C_seq n)) t)
      atTop (𝓝 (charFun (multivariateGaussian (0 : EuclideanSpace ℝ ι) C) t)) := by
  -- Continuous RHS of `charFun_multivariateGaussian` at μ = 0.
  set rhs : Matrix ι ι ℝ → ℂ := fun M =>
    Complex.exp (-(↑(t.ofLp ⬝ᵥ M.mulVec t.ofLp) / 2)) with hrhs_def
  -- Eventually `C_seq n` is PSD ⇒ `charFun (mvg 0 (C_seq n)) t = rhs (C_seq n)`.
  have h_lhs_eq : ∀ᶠ n in atTop,
      charFun (multivariateGaussian (0 : EuclideanSpace ℝ ι) (C_seq n)) t
        = rhs (C_seq n) := by
    filter_upwards [hC_seq] with n h_psd
    rw [charFun_multivariateGaussian h_psd]
    simp [hrhs_def, inner_zero_right]
  -- The fixed limit also reduces via `charFun_multivariateGaussian`.
  have h_rhs_eq :
      charFun (multivariateGaussian (0 : EuclideanSpace ℝ ι) C) t = rhs C := by
    rw [charFun_multivariateGaussian hC]
    simp [hrhs_def, inner_zero_right]
  rw [h_rhs_eq]
  -- Flip `=ᶠ` direction for `Tendsto.congr'`.
  have h_lhs_eq_symm :
      (fun n => rhs (C_seq n)) =ᶠ[atTop]
        fun n => charFun (multivariateGaussian (0 : EuclideanSpace ℝ ι) (C_seq n)) t := by
    filter_upwards [h_lhs_eq] with n h
    exact h.symm
  refine Tendsto.congr' h_lhs_eq_symm ?_
  -- Continuity of `rhs` in `M`, composed with `C_seq → C`.
  have h_cont : Continuous (fun M : Matrix ι ι ℝ => rhs M) := by
    refine Complex.continuous_exp.comp ?_
    refine (Continuous.div_const ?_ 2).neg
    refine Complex.continuous_ofReal.comp ?_
    exact Continuous.dotProduct continuous_const
      (Continuous.matrix_mulVec continuous_id continuous_const)
  exact (h_cont.tendsto C).comp h_tend

/-- `charFun (multivariateGaussian 0 C) t ≠ 0` for every
PSD `C` and every test point `t`. (Direct: charFun formula gives
`exp(−t·C·t/2)`, complex exponential is nowhere zero.) -/
theorem multivariateGaussian_charFun_nonzero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (t : EuclideanSpace ℝ ι) :
    charFun (multivariateGaussian (0 : EuclideanSpace ℝ ι) C) t ≠ 0 := by
  rw [charFun_multivariateGaussian hC]
  exact Complex.exp_ne_zero _

/-! ### Step 3d: Lévy continuity → `W_Λ ⇝ W`.

vdV §8.4: "the characteristic functions of W_Λ converge to a
continuous function, whence W_Λ converges in distribution to some vector
W, by Lévy's continuity theorem." -/

/-- Weak limit of `W_Λ` as `τ → ∞` along a sequence,
via Lévy continuity. The limit `W` is characterized by its charFun
`Ŵ(t) = L̂(t) / Ĝ(t)` where `Ĝ` is the charFun of
`multivariateGaussian 0 (A·J⁻¹·Aᵀ)`. -/
theorem W_Lambda_weak_limit_via_Levy
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {A : Matrix (Fin d) (Fin k) ℝ}
    {T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))}
    [IsMarkovKernel T]
    (hT_equiv : IsEquivariantInLaw T A J⁻¹) :
    ∃ W : Measure (EuclideanSpace ℝ (Fin d)),
      IsProbabilityMeasure W ∧
      (∀ t : EuclideanSpace ℝ (Fin d),
        charFun W t * charFun
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
              (A * J⁻¹ * A.transpose)) t
          = charFun hT_equiv.nullDist t) := by
  set τ : ℕ → ℝ := fun n => (n : ℝ) + 1 with hτ_def
  have hτ_pos : ∀ n, 0 < τ n := fun n => by positivity
  set G_target : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (A * J⁻¹ * A.transpose)
    with hG_target_def
  haveI hG_target_prob : IsProbabilityMeasure G_target := by
    rw [hG_target_def]; infer_instance
  have h_target_psd : (A * J⁻¹ * A.transpose).PosSemidef := by
    have := hJ.inv.posSemidef.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set G_seq : ℕ → Measure (EuclideanSpace ℝ (Fin d)) := fun n =>
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      (A * posteriorCov J (τ n) * A.transpose) with hG_seq_def
  have h_S_psd : ∀ n, (A * posteriorCov J (τ n) * A.transpose).PosSemidef := by
    intro n
    have hP : (posteriorCov J (τ n)).PosDef := posteriorCov_posDef hJ (hτ_pos n)
    have := hP.posSemidef.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have h_S_lim : Tendsto (fun n => A * posteriorCov J (τ n) * A.transpose)
      atTop (𝓝 (A * J⁻¹ * A.transpose)) := by
    have h_post : Tendsto (fun n : ℕ => posteriorCov J (τ n)) atTop (𝓝 J⁻¹) :=
      posteriorCov_tendsto_inv hJ
    have h_left : Tendsto (fun n : ℕ => A * posteriorCov J (τ n))
        atTop (𝓝 (A * J⁻¹)) :=
      (continuous_const.matrix_mul continuous_id).continuousAt.tendsto.comp h_post
    exact (continuous_id.matrix_mul continuous_const).continuousAt.tendsto.comp h_left
  have h_G_charFun_tendsto : ∀ t : EuclideanSpace ℝ (Fin d),
      Tendsto (fun n => charFun (G_seq n) t) atTop
        (𝓝 (charFun G_target t)) := fun t =>
    multivariateGaussian_charFun_continuous_in_cov (ι := Fin d) t
      h_target_psd (Eventually.of_forall h_S_psd) h_S_lim
  have h_G_target_nonzero : ∀ t, charFun G_target t ≠ 0 := fun t =>
    multivariateGaussian_charFun_nonzero h_target_psd t
  have h_G_seq_nonzero : ∀ n t, charFun (G_seq n) t ≠ 0 := fun n t =>
    multivariateGaussian_charFun_nonzero (h_S_psd n) t
  have h_G_law_eq : ∀ n, G_Lambda_law J (τ n) A T = G_seq n := fun n =>
    G_Lambda_cond_X_eq_gaussian hJ (hτ_pos n) A T
  have h_factor : ∀ n t, charFun hT_equiv.nullDist t
      = charFun (G_seq n) t * charFun (W_Lambda_law J (τ n) A T) t := fun n t => by
    rw [hatL_eq_hatG_mul_hatW hJ (hτ_pos n) hT_equiv t, h_G_law_eq n]
  set f_W : EuclideanSpace ℝ (Fin d) → ℂ := fun t =>
    charFun hT_equiv.nullDist t / charFun G_target t with hf_W_def
  have h_W_charFun_eq : ∀ n t, charFun (W_Lambda_law J (τ n) A T) t
      = charFun hT_equiv.nullDist t / charFun (G_seq n) t := fun n t => by
    rw [h_factor n t, mul_comm, mul_div_assoc, div_self (h_G_seq_nonzero n t), mul_one]
  have h_W_charFun_tendsto : ∀ t,
      Tendsto (fun n => charFun (W_Lambda_law J (τ n) A T) t) atTop (𝓝 (f_W t)) := by
    intro t
    simp_rw [h_W_charFun_eq]
    exact (tendsto_const_nhds (x := charFun hT_equiv.nullDist t)).div
      (h_G_charFun_tendsto t) (h_G_target_nonzero t)
  have h_f_W_cont : Continuous f_W :=
    MeasureTheory.continuous_charFun.div MeasureTheory.continuous_charFun h_G_target_nonzero
  have h_W_prob : ∀ n, IsProbabilityMeasure (W_Lambda_law J (τ n) A T) := by
    intro n
    haveI : IsProbabilityMeasure
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
          (((τ n)^2) • (1 : Matrix (Fin k) (Fin k) ℝ))) := inferInstance
    haveI : IsProbabilityMeasure
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := inferInstance
    haveI : IsProbabilityMeasure (jointHXY J (τ n) T) := by
      unfold jointHXY
      refine Measure.isProbabilityMeasure_map ?_
      fun_prop
    have hμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) =>
        posteriorMean J (τ n) x) :=
      (matrixToEuclideanCLMRect (posteriorCov J (τ n) * J)).continuous.measurable
    have hAμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) =>
        (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) x))) :=
      (matrixToEuclideanCLMRect A).continuous.measurable
    have hW_meas : Measurable (fun p : EuclideanSpace ℝ (Fin k) ×
        EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin d) =>
          p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) (posteriorMean J (τ n) p.2.1)))) :=
      (measurable_snd.comp measurable_snd).sub (hAμ.comp (hμ.comp
        (measurable_fst.comp measurable_snd)))
    unfold W_Lambda_law
    exact Measure.isProbabilityMeasure_map hW_meas.aemeasurable
  let μW : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) := fun n =>
    ⟨W_Lambda_law J (τ n) A T, h_W_prob n⟩
  have h_pointwise : ∀ t,
      Tendsto (fun n => charFun ((μW n : Measure _)) t) atTop (𝓝 (f_W t)) :=
    fun t => h_W_charFun_tendsto t
  have h_tight_range : IsTightMeasureSet
      (Set.range (fun n => ((μW n : ProbabilityMeasure _) : Measure _))) :=
    isTightMeasureSet_of_tendsto_charFun (f := f_W)
      h_f_W_cont.continuousAt h_pointwise
  have h_compact : IsCompact (closure (Set.range μW)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert! h_tight_range using 1
    ext μ; constructor
    · rintro ⟨ν, hν_range, rfl⟩
      obtain ⟨n, hn⟩ := hν_range
      exact ⟨n, by simp [← hn]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨μW n, Set.mem_range_self n, rfl⟩
  have h_in_closure : ∀ n, μW n ∈ closure (Set.range μW) :=
    fun n => subset_closure (Set.mem_range_self n)
  obtain ⟨W_PM, _hW_PM_in, φ, hφ_mono, hφ_tend⟩ :=
    h_compact.tendsto_subseq h_in_closure
  have h_W_PM_charFun : ∀ t, charFun ((W_PM : Measure _)) t = f_W t := by
    intro t
    have h_levy : Tendsto (fun n => charFun ((μW (φ n) : Measure _)) t) atTop
        (𝓝 (charFun ((W_PM : Measure _)) t)) :=
      ((ProbabilityMeasure.tendsto_iff_tendsto_charFun (μ₀ := W_PM)
        (μ := fun n => μW (φ n))).mp hφ_tend) t
    have h_W_tend : Tendsto (fun n => charFun ((μW (φ n) : Measure _)) t) atTop
        (𝓝 (f_W t)) :=
      (h_W_charFun_tendsto t).comp hφ_mono.tendsto_atTop
    exact tendsto_nhds_unique h_levy h_W_tend
  refine ⟨(W_PM : Measure _), inferInstance, fun t => ?_⟩
  rw [h_W_PM_charFun t, hf_W_def, div_mul_cancel₀ _ (h_G_target_nonzero t)]

/-! ### Step 3e: joint weak convergence + continuous mapping ⇒ `G + W ∼ L`. -/

/-- Joint weak convergence `(G_Λ, W_Λ) ⇝ (G, W)` along the
prior-variance sequence `τ → ∞`, with `G ⟂ W` in the limit.

Combines independence (`G_Lambda_indep_W_Lambda`, factorization of the joint as
a product for each Λ) with `multivariateGaussian_weakly_tendsto_of_seq`
(`G_Λ ⇝ G` in covariance sense) and `W_Lambda_weak_limit_via_Levy` (`W_Λ ⇝ W`),
then uses the `ForMathlib.IndepWeakLimit` bridge to lift the product of weak
limits to the limit of products.

Conclusion is stated in terms of integrals of bounded continuous functions
(the standard CD-portmanteau characterization of weak convergence on
product spaces), bridged via `ForMathlib.tendsto_prod_of_tendsto`. -/
theorem joint_GW_weak_indep_limit
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {A : Matrix (Fin d) (Fin k) ℝ}
    {T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))}
    [IsMarkovKernel T]
    (hT_equiv : IsEquivariantInLaw T A J⁻¹)
    {τ_seq : ℕ → ℝ} (hτ_seq_pos : ∀ n, 0 < τ_seq n)
    (hτ_seq : Tendsto τ_seq atTop atTop) :
    ∃ W : Measure (EuclideanSpace ℝ (Fin d)),
      IsProbabilityMeasure W ∧
      ∀ f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ,
        Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto
          (fun n => ∫ p, f p ∂(joint_GW_law J (τ_seq n) A T))
          atTop
          (𝓝 (∫ p, f p
              ∂((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
                  (A * J⁻¹ * A.transpose)).prod W))) := by
  -- Setup: G_target and PSD facts along τ_seq.
  set G_target : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (A * J⁻¹ * A.transpose)
    with hG_target_def
  haveI hG_target_prob : IsProbabilityMeasure G_target := by
    rw [hG_target_def]; infer_instance
  have h_target_psd : (A * J⁻¹ * A.transpose).PosSemidef := by
    have := hJ.inv.posSemidef.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have h_S_psd : ∀ n, (A * posteriorCov J (τ_seq n) * A.transpose).PosSemidef := by
    intro n
    have hP : (posteriorCov J (τ_seq n)).PosDef :=
      posteriorCov_posDef hJ (hτ_seq_pos n)
    have := hP.posSemidef.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  -- `posteriorCov J τ_seq_n → J⁻¹` (matrix inv continuous at PosDef J + τ_seq → ∞).
  have h_post_lim :
      Tendsto (fun n => posteriorCov J (τ_seq n)) atTop (𝓝 J⁻¹) := by
    have h_eps : Tendsto (fun n => ((τ_seq n) ^ 2)⁻¹) atTop (𝓝 0) := by
      have h_sq_top : Tendsto (fun n => (τ_seq n) ^ 2) atTop atTop :=
        (Filter.tendsto_pow_atTop (n := 2) (by decide)).comp hτ_seq
      exact tendsto_inv_atTop_zero.comp h_sq_top
    have h_inner : Tendsto (fun n =>
        J + ((τ_seq n) ^ 2)⁻¹ • (1 : Matrix _ _ _)) atTop (𝓝 J) := by
      have h_smul : Tendsto (fun n => ((τ_seq n) ^ 2)⁻¹ •
          (1 : Matrix (Fin k) (Fin k) ℝ)) atTop
          (𝓝 ((0 : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ))) :=
        h_eps.smul_const _
      have := (tendsto_const_nhds (x := J)).add h_smul
      simpa using this
    have h_det_unit : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ.isUnit
    have h_inv_cont : ContinuousAt Inv.inv J := by
      apply continuousAt_matrix_inv
      have := NormedRing.inverse_continuousAt h_det_unit.unit
      simpa [IsUnit.unit_spec] using this
    unfold posteriorCov
    exact h_inv_cont.tendsto.comp h_inner
  have h_S_lim : Tendsto (fun n => A * posteriorCov J (τ_seq n) * A.transpose)
      atTop (𝓝 (A * J⁻¹ * A.transpose)) := by
    have h_left : Tendsto (fun n => A * posteriorCov J (τ_seq n))
        atTop (𝓝 (A * J⁻¹)) :=
      (continuous_const.matrix_mul continuous_id).continuousAt.tendsto.comp h_post_lim
    exact (continuous_id.matrix_mul continuous_const).continuousAt.tendsto.comp h_left
  -- Pointwise charFun convergence for G_Λ.
  have h_G_charFun_tendsto : ∀ t : EuclideanSpace ℝ (Fin d),
      Tendsto (fun n => charFun (multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin d))
          (A * posteriorCov J (τ_seq n) * A.transpose)) t) atTop
        (𝓝 (charFun G_target t)) := fun t =>
    multivariateGaussian_charFun_continuous_in_cov (ι := Fin d) t
      h_target_psd (Eventually.of_forall h_S_psd) h_S_lim
  have h_G_target_nonzero : ∀ t, charFun G_target t ≠ 0 := fun t =>
    multivariateGaussian_charFun_nonzero h_target_psd t
  have h_G_seq_nonzero : ∀ n t, charFun (multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d))
      (A * posteriorCov J (τ_seq n) * A.transpose)) t ≠ 0 := fun n t =>
    multivariateGaussian_charFun_nonzero (h_S_psd n) t
  have h_G_law_eq : ∀ n, G_Lambda_law J (τ_seq n) A T
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (A * posteriorCov J (τ_seq n) * A.transpose) := fun n =>
    G_Lambda_cond_X_eq_gaussian hJ (hτ_seq_pos n) A T
  have h_factor : ∀ n t, charFun hT_equiv.nullDist t
      = charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (A * posteriorCov J (τ_seq n) * A.transpose)) t
        * charFun (W_Lambda_law J (τ_seq n) A T) t := fun n t => by
    rw [hatL_eq_hatG_mul_hatW hJ (hτ_seq_pos n) hT_equiv t, h_G_law_eq n]
  set f_W : EuclideanSpace ℝ (Fin d) → ℂ := fun t =>
    charFun hT_equiv.nullDist t / charFun G_target t with hf_W_def
  have h_W_charFun_tendsto : ∀ t,
      Tendsto (fun n => charFun (W_Lambda_law J (τ_seq n) A T) t) atTop
        (𝓝 (f_W t)) := by
    intro t
    have h_eq : ∀ n, charFun (W_Lambda_law J (τ_seq n) A T) t
        = charFun hT_equiv.nullDist t
          / charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
              (A * posteriorCov J (τ_seq n) * A.transpose)) t := by
      intro n
      rw [h_factor n t, mul_comm, mul_div_assoc, div_self (h_G_seq_nonzero n t),
        mul_one]
    simp_rw [h_eq]
    exact (tendsto_const_nhds (x := charFun hT_equiv.nullDist t)).div
      (h_G_charFun_tendsto t) (h_G_target_nonzero t)
  obtain ⟨W, hW_prob, hW_charFun⟩ := W_Lambda_weak_limit_via_Levy hJ hT_equiv
  -- Show `charFun W = f_W`.
  have h_W_charFun_eq : ∀ t, charFun W t = f_W t := by
    intro t
    rw [hf_W_def, eq_div_iff (h_G_target_nonzero t)]
    exact hW_charFun t
  refine ⟨W, hW_prob, ?_⟩
  intros f hf_cont hf_bdd
  haveI : IsProbabilityMeasure W := hW_prob
  have h_W_prob_n : ∀ n, IsProbabilityMeasure (W_Lambda_law J (τ_seq n) A T) := by
    intro n
    haveI : IsProbabilityMeasure
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
          (((τ_seq n)^2) • (1 : Matrix (Fin k) (Fin k) ℝ))) := inferInstance
    haveI : IsProbabilityMeasure
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := inferInstance
    haveI : IsProbabilityMeasure (jointHXY J (τ_seq n) T) := by
      unfold jointHXY
      refine Measure.isProbabilityMeasure_map ?_
      fun_prop
    have hμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) =>
        posteriorMean J (τ_seq n) x) :=
      (matrixToEuclideanCLMRect (posteriorCov J (τ_seq n) * J)).continuous.measurable
    have hAμ : Measurable (fun x : EuclideanSpace ℝ (Fin k) =>
        (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) x))) :=
      (matrixToEuclideanCLMRect A).continuous.measurable
    have hW_meas : Measurable (fun p : EuclideanSpace ℝ (Fin k) ×
        EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin d) =>
          p.2.2 - (WithLp.equiv 2 (Fin d → ℝ)).symm
            (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ))
              (posteriorMean J (τ_seq n) p.2.1)))) :=
      (measurable_snd.comp measurable_snd).sub (hAμ.comp (hμ.comp
        (measurable_fst.comp measurable_snd)))
    unfold W_Lambda_law
    exact Measure.isProbabilityMeasure_map hW_meas.aemeasurable
  let μW : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) := fun n =>
    ⟨W_Lambda_law J (τ_seq n) A T, h_W_prob_n n⟩
  let μG : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) := fun n =>
    ⟨multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
        (A * posteriorCov J (τ_seq n) * A.transpose), inferInstance⟩
  let W_PM : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) := ⟨W, hW_prob⟩
  let G_PM : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) := ⟨G_target, hG_target_prob⟩
  have h_μW_tend : Tendsto μW atTop (𝓝 W_PM) := by
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro t
    change Tendsto (fun n => charFun (W_Lambda_law J (τ_seq n) A T) t) atTop
      (𝓝 (charFun W t))
    rw [h_W_charFun_eq t]
    exact h_W_charFun_tendsto t
  have h_μG_tend : Tendsto μG atTop (𝓝 G_PM) := by
    have h_seq := multivariateGaussian_weakly_tendsto_of_seq
      h_target_psd (Eventually.of_forall h_S_psd) h_S_lim
    convert! h_seq using 1
  have h_joint_tend : Tendsto (fun n => (μG n).prod (μW n)) atTop
      (𝓝 (G_PM.prod W_PM)) :=
    AsymptoticStatistics.ForMathlib.tendsto_prod_of_tendsto h_μG_tend h_μW_tend
  obtain ⟨C, hC⟩ := hf_bdd
  have h_f_bdd : ∀ x, ‖f x‖ ≤ C := fun x => by
    have := hC x; rwa [Real.norm_eq_abs]
  let fBC : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨f, hf_cont⟩ (2 * C) (by
      intro x y
      calc dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
        _ ≤ C + C := by gcongr <;> exact h_f_bdd _
        _ = 2 * C := by ring)
  have h_int_tend : Tendsto (fun n => ∫ p, f p ∂((μG n).prod (μW n) : Measure _))
      atTop (𝓝 (∫ p, f p ∂(G_PM.prod W_PM : Measure _))) := by
    have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h_joint_tend) fBC
    simpa using! this
  have h_left_eq : ∀ n, ((μG n).prod (μW n) : Measure _)
      = joint_GW_law J (τ_seq n) A T := by
    intro n
    have h_indep := G_Lambda_indep_W_Lambda hJ (hτ_seq_pos n) A T
    change (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
        (A * posteriorCov J (τ_seq n) * A.transpose)).prod
          (W_Lambda_law J (τ_seq n) A T)
      = joint_GW_law J (τ_seq n) A T
    rw [← h_G_law_eq n, ← h_indep]
  have h_right_eq : (G_PM.prod W_PM : Measure _) = G_target.prod W := rfl
  have h_lhs_eq : (fun n => ∫ p, f p ∂((μG n).prod (μW n) : Measure _))
      = (fun n => ∫ p, f p ∂(joint_GW_law J (τ_seq n) A T)) := by
    funext n; rw [h_left_eq n]
  rw [h_lhs_eq] at h_int_tend
  rwa [h_right_eq] at h_int_tend

/-- Continuous-mapping + uniqueness of weak limits applied to
`G_Λ + W_Λ ⇝ G + W`. Since `G_Λ + W_Λ ∼ L` for every Λ (independent of Λ)
and `L = G + W` in distribution, conclude `L = N(0, A·J⁻¹·Aᵀ) ∗ M` with
`M = law(W)`. -/
theorem L_eq_G_plus_W
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    {A : Matrix (Fin d) (Fin k) ℝ}
    {T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))}
    [IsMarkovKernel T]
    (hT_equiv : IsEquivariantInLaw T A J⁻¹) :
    ∃ M : Measure (EuclideanSpace ℝ (Fin d)),
      IsProbabilityMeasure M ∧
      hT_equiv.nullDist
        = (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
            (A * J⁻¹ * A.transpose)) ∗ M := by
  obtain ⟨W, hW_prob, hW_charFun⟩ := W_Lambda_weak_limit_via_Levy hJ hT_equiv
  refine ⟨W, hW_prob, ?_⟩
  set G_target : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (A * J⁻¹ * A.transpose)
    with hG_target_def
  haveI : IsProbabilityMeasure G_target := by rw [hG_target_def]; infer_instance
  haveI : IsProbabilityMeasure W := hW_prob
  refine MeasureTheory.Measure.ext_of_charFun ?_
  funext t
  rw [MeasureTheory.charFun_conv]
  rw [mul_comm]
  exact (hW_charFun t).symm

/-! ## Main theorem (vdV §8.4 Prop 8.4) -/

/-- **vdV §8.4 Proposition 8.4** (Convolution structure of equivariant-in-law
estimators in the Gaussian shift experiment).

> The null distribution `L` of any randomized equivariant-in-law estimator
> of `Ah` can be decomposed as `L = N(0, A·Σ·Aᵀ) * M` for some probability
> measure `M`.

Here `Σ` is supplied as a positive-definite `Matrix (Fin k) (Fin k) ℝ`
(matches vdV's "the covariance matrix Σ is assumed known and nonsingular",
§8.4); `A : Matrix (Fin d) (Fin k) ℝ` is the linear map (vdV §8.4);
`T : Kernel ℝᵏ ℝᵈ` encodes the randomized estimator; `hT_equiv` is the
equivariance-in-law hypothesis on `T` (vdV §8.4 head definition).

The conclusion uses Mathlib's `MeasureTheory.Measure.conv` notation `μ ∗ ν`. -/
theorem equivariant_in_law_convolution_decomposition
    {k d : ℕ}
    {S : Matrix (Fin k) (Fin k) ℝ} (hS_pd : S.PosDef)
    (A : Matrix (Fin d) (Fin k) ℝ)
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel T]
    (hT_equiv : IsEquivariantInLaw T A S) :
    ∃ M : Measure (EuclideanSpace ℝ (Fin d)),
      IsProbabilityMeasure M ∧
      hT_equiv.nullDist
        = (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
            (A * S * A.transpose)) ∗ M := by
  -- Apply `L_eq_G_plus_W` with `J := S⁻¹`. Then `J⁻¹ = (S⁻¹)⁻¹ = S` (PosDef invertibility).
  haveI : Invertible S := hS_pd.isUnit.invertible
  set J : Matrix (Fin k) (Fin k) ℝ := S⁻¹ with hJ_def
  have hJ_pd : J.PosDef := by rw [hJ_def]; exact hS_pd.inv
  have hJ_inv_eq : J⁻¹ = S := by
    rw [hJ_def]; exact Matrix.inv_inv_of_invertible S
  clear_value J
  subst hJ_inv_eq
  exact L_eq_G_plus_W hJ_pd hT_equiv

end GaussianShiftConvolution
end AsymptoticStatistics
