module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# Fixed-design linear model — definitions

Consider the fixed-design linear model with design matrix $X \in \mathbb{R}^{n\times d}$,
unknown coefficient vector $\beta^* \in \mathbb{R}^d$, and response
$Y = X\beta^* + \varepsilon \in \mathbb{R}^n$, where $\varepsilon$ is the noise vector.
The ordinary least-squares (OLS) estimator $\hat\beta^{\mathrm{LS}}$ is defined as a
*minimiser* of the residual sum of squares
$$\hat\beta^{\mathrm{LS}} \in \arg\min_{\beta \in \mathbb{R}^d} \; \|Y - X\beta\|^2,$$
and the prediction mean squared error of a fitted coefficient $\hat\beta$ is
$$\mathrm{MSE}(X\hat\beta) = \tfrac{1}{n}\,\|X\hat\beta - X\beta^*\|^2.$$

These definitions formalise the model setup behind the OLS MSE theorem
(Lu-BDA §7.2, Theorem 7.1). Two deliberate choices, aligned with the Lean
statements below:

* The OLS estimator is characterised by the **minimiser (zero-order)
  condition**, not the closed form $(X^\top X)^{-1} X^\top Y$, which need not
  exist when $X$ is rank-deficient — exactly the regime the MSE theorem covers.
* The degenerate case $n = 0$ yields $\mathrm{MSE} = 0$, since the factor
  $1/n$ is taken to be $0$.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland,
2025 (ISBN 978-3-032-03160-0), Chapter 7 (Ordinary Least Squares), §7.2,
Theorem 7.1 (Mean Squared Error of Least Squares) (model
$Y = X\beta^* + \varepsilon$; OLS as RSS minimiser;
$\mathrm{MSE}(X\hat\beta) = \tfrac{1}{n}\|X\hat\beta - X\beta^*\|^2$).

**Proof formalization notes.**
Vectors live in `EuclideanSpace ℝ (Fin ·)` (the ℓ²/inner-product space used
throughout the library). The design matrix acts as the linear map
`Matrix.toEuclideanLin X : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)`.
These are concept-layer, theorem-agnostic definitions consumed by
`OLS/MSEExpectation.lean` and `OLS/MSEHighProb.lean`. The book's design rank
$r = \mathrm{rank}(X)$ is the dimension of the column space $C(X)$ (the range of
the design map); here `designRank` is taken as `Matrix.rank X`.

**Bibliographic comments.**
The fixed-design linear model and ordinary least squares are classical and
folklore, with no single seminal paper. The method of least squares was
introduced by A. M. Legendre, *Nouvelles méthodes pour la détermination des
orbites des comètes* (Paris, 1805), and given its probabilistic justification by
C. F. Gauss, *Theoria motus corporum coelestium* (1809); the optimality of OLS
among linear unbiased estimators is the Gauss–Markov theorem (Gauss 1821–1823;
A. A. Markov, *Wahrscheinlichkeitsrechnung*, 1912). The prediction-error
analysis used here (MSE of the fitted projection $X\hat\beta$) is standard
material rather than an original research result.
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- The design map `E^d → E^n` induced by the design matrix `X` (Lu-BDA §7.2):
`β ↦ X β`, as a continuous linear-algebraic map between Euclidean spaces. -/
noncomputable def designMap (X : Matrix (Fin n) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin X

/-- **Prediction mean squared error** `MSE(X β̂) = (1/n) ‖X β̂ − X β*‖²`
(Lu-BDA §7.2, Theorem 7.1). Degenerate `n = 0` gives `0` (the `1/n` factor is `0`). -/
noncomputable def mse (X : Matrix (Fin n) (Fin d) ℝ)
    (β βstar : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (n : ℝ)) * ‖designMap X β - designMap X βstar‖ ^ 2

/-- **OLS estimator predicate** (Lu-BDA §7.2): `β̂` is a least-squares estimator for
response `Y` under design `X` iff it minimises the residual sum of squares
`‖Y − X β‖²` over all `β`. This is the zero-order (minimiser) characterisation,
deliberately *not* a closed form, so it is well-defined for rank-deficient `X`. -/
def IsOLSEstimator (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (βhat : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ β, ‖Y - designMap X βhat‖ ^ 2 ≤ ‖Y - designMap X β‖ ^ 2

/-- **Column space** `C(X)` of the design (Lu-BDA §7.2): the range of the design map,
a subspace of `E^n`. The book's `r = rank(X)` is its dimension. -/
noncomputable def columnSpace (X : Matrix (Fin n) (Fin d) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.range (designMap X)

/-- The book's design rank `r = rank(X)` (Lu-BDA §7.2, Theorem 7.1). Equal to the
dimension of the column space; here taken as `Matrix.rank X`. -/
noncomputable def designRank (X : Matrix (Fin n) (Fin d) ℝ) : ℕ :=
  X.rank

end StatLean.HighDimensionalStatistics
