module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

/-!
# Normal linear models — core data model

The **canonical normal linear model** observes `n` independent Gaussians
`Yᵢ ∼ N(ηᵢ, σ²)` whose mean vector is constrained to a linear subspace; estimation of
mean functionals and of the variance reduces, after an orthogonal change of basis, to
this canonical form. This file fixes:

* `canonicalNormal η σ2` — the product measure `⨂ᵢ N(ηᵢ, σ²)` on `Fin n → ℝ`;
* `gaussianVector ξ σ2` — the same law carried to `EuclideanSpace ℝ (Fin n)` (where the
  subspace geometry lives);
* `linearModel W σ2` — the family `ξ ∈ W ↦ gaussianVector ξ σ2` indexed by a mean
  subspace `W`;
* `lse W` — the least-squares estimator: the orthogonal projection of the observation
  onto `W` (as a map of the full space, `Submodule.starProjection`);
* `residualSumSq W` — the squared residual norm `‖y − lse W y‖²` (the `S²` statistic).

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.4 (Normal
Linear Models), the canonical and subspace forms of the normal linear model. (`TPE2 §3.4`.)

**Proof formalization notes.**
* The product Gaussian lives naturally on the pi-type; `gaussianVector` transports it to
  `EuclideanSpace` along `WithLp.toLp 2` (a measurable equivalence with the pi measurable
  structure), so projection geometry and measure theory coexist.
* `lse` is `Submodule.starProjection` (full-space-valued orthogonal projection);
  finite-dimensional subspaces of `EuclideanSpace` carry the required
  `HasOrthogonalProjection` instance automatically.
* Gauss–Markov statements are moments-only: they constrain a single unknown law through
  mean/covariance hypotheses rather than Gaussianity, and are stated over an abstract
  probability measure on the observation space.

**Bibliographic comments.** Least squares and its optimality among linear unbiased
estimators are due to C. F. Gauss (*Theoria combinationis observationum erroribus
minimis obnoxiae*, 1821/1823) and A. A. Markov (*Wahrscheinlichkeitsrechnung*, 1912);
the modern coordinate-free treatment of the normal linear model follows W. Kruskal
("When are Gauss–Markov and least squares estimators identical?" in *Essays in
Probability and Statistics*, 1965) and H. Scheffé (*The Analysis of Variance*, Wiley,
1959).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.PointEstimation

variable {n : ℕ}

/-- The **canonical normal model**: `n` independent real Gaussians with means `η i` and
common variance `σ2`, as a product measure on `Fin n → ℝ`. -/
noncomputable def canonicalNormal (η : Fin n → ℝ) (σ2 : ℝ≥0) : Measure (Fin n → ℝ) :=
  Measure.pi fun i => gaussianReal (η i) σ2

/-- The canonical normal law transported to `EuclideanSpace ℝ (Fin n)`, where the
subspace geometry lives. -/
noncomputable def gaussianVector (ξ : EuclideanSpace ℝ (Fin n)) (σ2 : ℝ≥0) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (canonicalNormal (fun i => ξ i) σ2).map
    (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))

/-- The **normal linear model** with mean subspace `W` and variance `σ2`: the family of
Gaussian vectors with mean ranging over `W`. -/
noncomputable def linearModel (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (σ2 : ℝ≥0)
    (ξ : W) : Measure (EuclideanSpace ℝ (Fin n)) :=
  gaussianVector (ξ : EuclideanSpace ℝ (Fin n)) σ2

/-- The **least-squares estimator** of the mean vector: orthogonal projection of the
observation onto the mean subspace. -/
noncomputable def lse (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection] (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  W.starProjection y

/-- The **residual sum of squares** `S² = ‖y − ŷ‖²` about the mean subspace `W`. -/
noncomputable def residualSumSq (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection] (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖y - lse W y‖ ^ 2

end StatLean.PointEstimation
