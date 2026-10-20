module
public import StatLean.AsymptoticStatistics.ForMathlib.BowlShaped
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
# Minimax bound in the Gaussian shift experiment

This file formalizes the key Gaussian-shift step ("Lemma 4") inside the
lower-bound proof of the local asymptotic minimax (LAM) theorem. In the
finite-dimensional Gaussian shift experiment, where one observes a single
draw $X \sim N(h, I_m)$ with unknown shift $h$ ranging over a convex cone
$C_m \subseteq \mathbb{R}^m$ of nonempty interior, consider estimating the
scalar functional $h \mapsto A h$ for a continuous linear functional
$A : \mathbb{R}^m \to \mathbb{R}$ (the differential of $\psi$ along the score
basis; the book's general $k$-dimensional coefficient collapses to a single
linear functional when $k = 1$). For any bounded, uniformly continuous,
subconvex ("bowl-shaped") loss $\ell$, the finite-subset minimax risk is
bounded below by the Gaussian integral of the loss against the limit law:
$$
\sup_{I_0 \subset C_m \text{ finite}} \;
  \inf_{T} \; \max_{h \in I_0} \;
  \int \ell\bigl(T(X) - A h\bigr)\, dN(h, I_m)(X)
\;\ge\;
  \int \ell(u)\, dN\!\left(0, \|A\|^2\right)(u),
$$
where the right-hand side uses the scalar limit variance $\|A\|^2$. The
headline declaration is `gaussianShift_minimax`.

Deviations from the book: the statement here is specialized to the scalar
functional ($k = 1$), so the book's covariance matrix $A A^{\mathsf T}$
becomes the scalar variance $\|A\|^2$; the limit Gaussian is encoded as
Mathlib's `gaussianReal 0 ⟨‖A‖^2, _⟩` with the variance carried as a
nonnegative real. The loss is `ℝ≥0∞`-valued (with its real `toReal` bridge
carrying the uniform-continuity hypothesis), matching the book's
nonnegative subconvex loss $\ell : \mathbb{R}^k \to [0, \infty)$.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge
Series in Statistical and Probabilistic Mathematics, Cambridge University
Press, 1998. Chapter 25 (Semiparametric Models), §25.3 (Tangent Spaces and
Information), Theorem 25.21 (LAM, local asymptotic minimax theorem). The
Gaussian-shift inequality formalized here is the core normal-experiment
step underlying that theorem's proof (the assertion that, when the tangent
set is a convex cone, the minimax risk on the left cannot fall below the
normal risk on the right), proved in the book by reduction to the
parametric minimax result of Chapter 8 (Proposition 8.6) together with its
convex-cone strengthening.

**Proof formalization notes.** The book derives this in three steps:
(1) Anderson's lemma on a Gaussian prior $N(c\,h_0,\, c\, I_m)$ identifies
the posterior loss minimum as a Gaussian integral; (2) restricting the
prior to $C_m$ and letting $c \to \infty$ recovers
$\int \ell\, dN(0, \|A\|^2)$; (3) a finite-support density argument plus
Bayes-risk continuity transports the Bayes lower bound to the finite-subset
minimax form. Steps (1)+(2) and step (3) enter the Lean statement as the
hypotheses `hPriorBayesBound` and `hFiniteSupportApprox`; they are combined
via `le_iSup`. (See the per-declaration docstring for the role of each
hypothesis and the `obtain`/`le_trans`/`le_iSup` assembly.)

**Bibliographic comments.** The Gaussian-shift inequality rests on
*Anderson's lemma*: T. W. Anderson, "The integral of a symmetric unimodal
function over a symmetric convex set and some probability inequalities,"
*Proceedings of the American Mathematical Society*, vol. 6, no. 2, pp.
170–176, 1955. Anderson's Theorem 1 shows that the integral of a
nonnegative, symmetric, unimodal function over a symmetric convex set, with
the function shifted by $\lambda y$, is nonincreasing in $\lambda \ge 0$;
its probabilistic corollary states that a centered Gaussian assigns at least
as much mass to a symmetric convex set as any of its shifts, i.e.
$P(X \in C) \ge P(X + a \in C)$. Applied to a bowl-shaped loss (whose
sublevel sets are symmetric and convex) this yields that the unshifted
location estimator is minimax in the Gaussian location problem — the
ingredient van der Vaart invokes (via Proposition 8.6 and its convex-cone
extension) to prove Theorem 25.21.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace AsymptoticStatistics.LowerBounds.GaussianShiftMinimax

open AsymptoticStatistics

variable {m : ℕ}

/-- *Lemma 4 (minimax bound in the Gaussian shift experiment).*

For the finite-dim limit experiment `(N(h, I_m) : h ∈ ℝᵐ)` with
parameter restricted to a convex cone `C_m ⊆ EuclideanSpace ℝ (Fin m)`
of nonempty interior, any bounded uniformly continuous subconvex loss
`ℓ : ℝ → ℝ≥0∞`, and a continuous linear coefficient
`A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ` (the "functional differential"
of `ψ` along the score basis), the finite-subset minimax risk is
bounded below by the Gaussian integral of `ℓ` against `N(0, ‖A‖²)`:

```
sup_{I_0 ⊂ C_m finite} inf_T max_{h∈I_0} ∫⁻ ℓ(T(X) − A h) dN(h, I_m)(X)
  ≥ ∫⁻ u, ℓ u ∂(gaussianReal 0 ‖A‖²).
```

`σ²` is encoded as `⟨‖A‖^2, sq_nonneg _⟩ : ℝ≥0` to match Mathlib's
`gaussianReal : ℝ → ℝ≥0 → Measure ℝ`.

Reference: vdV §25.3 (proof of Theorem 25.21). Proof intent in this
file's header docstring.

Proof: `hPriorBayesBound` supplies a cone-supported prior with a Bayes-risk
lower bound (book steps (1)+(2)); `hFiniteSupportApprox` extracts a
finite-support witness `I_0` with the same bound (book step (3)); the two
are combined via `le_iSup`. -/
theorem gaussianShift_minimax
    (C_m : Set (EuclideanSpace ℝ (Fin m)))
    (_hC_convex : Convex ℝ C_m)
    (_hC_cone : ∀ x ∈ C_m, ∀ t : ℝ, 0 ≤ t → t • x ∈ C_m)
    (_hC_int : (interior C_m).Nonempty)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    -- `AsymptoticStatistics.BowlShaped` from `ForMathlib/BowlShaped.lean` (vdV §8.5).
    (ℓ : ℝ → ℝ≥0∞)
    (_hℓ_bowl : BowlShaped ℓ)
    (_hℓ_bdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ u : ℝ, ℓ u ≤ B)
    -- Stated on the real-valued `toReal` bridge so the standard `UniformContinuous`
    -- predicate applies (`ℓ` is `ℝ≥0∞`-valued; bounded `⇒` finite `⇒` `ofReal ∘ toReal`
    -- is the canonical real proxy).
    (_hℓ_uc : UniformContinuous fun u : ℝ => (ℓ u).toReal)
    -- vdV §25.3 (book steps (1)+(2)). Packages Anderson's lemma on the Gaussian
    -- prior `N(c h₀, c I_m)` (`ForMathlib/Anderson.gaussian_lintegral_mono_of_psd_le`)
    -- and the cone-restriction `π̃_c(C_m) → 1` limit (`c → ∞`).
    --
    -- Stated as: there exists a probability measure `π` on `EuclideanSpace ℝ
    -- (Fin m)` supported in `C_m` (encoded via full measure `π C_m = 1`), whose
    -- Bayes-style integral-of-minimax (the order `inf_T`-then-`∫ ∂π` is the
    -- canonical Bayes risk) lower-bounds the limit Gaussian integral on the right.
    (hPriorBayesBound :
      ∃ (π : Measure (EuclideanSpace ℝ (Fin m))),
        IsProbabilityMeasure π ∧
        π C_m = 1 ∧
        (⨅ T : EuclideanSpace ℝ (Fin m) → ℝ,
          ∫⁻ h, ∫⁻ X, ℓ (T X - A h)
            ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)) ∂π)
          ≥ ∫⁻ u, ℓ u ∂(gaussianReal 0 ⟨‖A‖ ^ 2, sq_nonneg _⟩))
    -- vdV §25.3 (book step (3)): finite-support density of priors on the cone,
    -- with Bayes-risk continuity in the prior. Says: any cone-supported prior `π`
    -- whose `inf_T` Bayes risk is at least `B` admits a *finite-support*
    -- approximation, in the sense that for any such `B` there is a finite
    -- `I_0 ⊂ C_m` with `inf_T max_{h ∈ I_0} risk(T, h) ≥ B`.
    --
    -- Justification (book): probability measures with finite support are
    -- weakly dense in `Prob(K)` for compact `K ⊂ C_m`; the bounded uniformly
    -- continuous loss `ℓ` makes the Bayes integral continuous in the prior;
    -- and the inequality `max_{h ∈ I_0} f(h) ≥ ∫ f dπ_finite` (sup ≥ mean)
    -- transports the Bayes lower bound to the minimax form.
    --
    -- Expressed pointwise in `B` so the consumer can cite it on the value
    -- delivered by `hPriorBayesBound`.
    (hFiniteSupportApprox :
      ∀ {π : Measure (EuclideanSpace ℝ (Fin m))} (_hπ : IsProbabilityMeasure π)
        (_hπC : π C_m = 1) (B : ℝ≥0∞),
        (⨅ T : EuclideanSpace ℝ (Fin m) → ℝ,
          ∫⁻ h, ∫⁻ X, ℓ (T X - A h)
            ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)) ∂π) ≥ B →
        ∃ I_0 : Finset (EuclideanSpace ℝ (Fin m)),
          (I_0 : Set _) ⊆ C_m ∧
          (⨅ T : EuclideanSpace ℝ (Fin m) → ℝ,
            ⨆ h ∈ I_0, ∫⁻ X, ℓ (T X - A h)
              ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)))
            ≥ B) :
    -- LHS: `sup_{I_0 finite ⊂ C_m} inf_{T : EuclideanSpace ℝ (Fin m) → ℝ}
    --        max_{h ∈ I_0} ∫⁻ ℓ(T(X) − A h) ∂(N(h, I_m))`
    --     ≥
    -- RHS: ∫⁻ u, ℓ u ∂(gaussianReal 0 ‖A‖²).
    --
    -- We use `multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)` for `N(h, I_m)`
    -- (Mathlib `multivariateGaussian_zero_one`), and `gaussianReal 0 ⟨‖A‖^2, _⟩` for
    -- the 1D limit Gaussian (Mathlib `Probability/Distributions/Gaussian/Real`).
    (⨆ I_0 : { S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C_m },
        ⨅ T : EuclideanSpace ℝ (Fin m) → ℝ,
          ⨆ h ∈ (I_0 : Finset (EuclideanSpace ℝ (Fin m))),
            ∫⁻ X, ℓ (T X - A h)
              ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)))
      ≥ ∫⁻ u, ℓ u ∂(gaussianReal 0 ⟨‖A‖ ^ 2, sq_nonneg _⟩) := by
  -- Step (1)+(2): extract the cone-supported prior `π` and its Bayes-risk
  -- lower bound from the Anderson-PSD chain (post the cone-restriction
  -- `c → ∞` limit).
  obtain ⟨π, hπ, hπC, hπBound⟩ := hPriorBayesBound
  -- Step (3): apply the finite-support-density approximation to that prior,
  -- with the limit Gaussian integral as the lower bound to be transported.
  obtain ⟨I_0, hI_sub, hI_bd⟩ :=
    hFiniteSupportApprox hπ hπC
      (∫⁻ u, ℓ u ∂(gaussianReal 0 ⟨‖A‖ ^ 2, sq_nonneg _⟩))
      hπBound
  -- Structural step: the supremum over all finite subsets of `C_m` dominates
  -- any individual subset's `inf_T max_{h∈I_0}` value. Specialise the `iSup`
  -- to the witness `⟨I_0, hI_sub⟩`.
  refine le_trans hI_bd ?_
  -- `le_iSup` at the bundled subtype `⟨I_0, hI_sub⟩`.
  exact le_iSup
    (fun I_0' : { S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C_m } =>
      ⨅ T : EuclideanSpace ℝ (Fin m) → ℝ,
        ⨆ h ∈ (I_0' : Finset (EuclideanSpace ℝ (Fin m))),
          ∫⁻ X, ℓ (T X - A h)
            ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)))
    ⟨I_0, hI_sub⟩

end AsymptoticStatistics.LowerBounds.GaussianShiftMinimax
