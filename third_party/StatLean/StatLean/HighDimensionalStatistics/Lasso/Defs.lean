module
public import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
public import StatLean.HighDimensionalStatistics.LinearModel.Defs

@[expose] public section

/-!
# Lasso primitives — restricted cone, restricted eigenvalue, Lasso objective

This concept file fixes the three primitives underlying the high-dimensional
Lasso analysis. For a design matrix $X \in \mathbb{R}^{n\times d}$, a response
vector $Y \in \mathbb{R}^n$, a support set $S \subseteq \{1,\dots,d\}$, and
tuning parameter $\lambda > 0$:

* **Restricted cone.** $C_\alpha(S) = \{\Delta : \lVert \Delta_{S^c}\rVert_1 \le
  \alpha\,\lVert \Delta_S\rVert_1\}$, the set of deviation vectors whose
  $\ell^1$ mass off the support $S$ is at most $\alpha$ times the mass on $S$.
  Here $\Delta_S$ is $\Delta$ restricted to coordinates in $S$ (other entries
  zeroed) and $\Delta_{S^c}$ is the restriction to the complement.
* **Restricted eigenvalue condition** $\mathrm{RE}(\kappa,\alpha)$. The
  quadratic loss is $\kappa$-curved along the cone:
  $\tfrac{1}{n}\lVert X\Delta\rVert_2^2 \ge \kappa\,\lVert\Delta\rVert_2^2$ for
  every $\Delta \in C_\alpha(S)$. This is the standard restricted strong
  convexity condition that makes the Lasso identifiable despite $d \gg n$.
* **Lasso objective and estimator.** The penalized least-squares objective
  $L_n(\beta) = \tfrac{1}{2n}\lVert Y - X\beta\rVert_2^2 + \lambda\,\lVert
  \beta\rVert_1$; $\hat\beta$ is a Lasso estimator at level $\lambda$ when it
  minimizes $L_n$ over all $\beta$, i.e. $L_n(\hat\beta) \le L_n(\beta)$ for all
  $\beta$ (a global-minimizer characterization, equivalent to
  $\hat\beta \in \arg\min_\beta L_n(\beta)$).

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 10 (Statistical Properties of Lasso), §10.1
(Restricted Eigenvalue Condition), Definition 10.1 (Restricted Eigenvalue). The
objective $L_n$, cone $C_\alpha(S)$, and condition $\mathrm{RE}(\kappa,\alpha)$
are the setup notation of that chapter.

**Proof formalization notes.** This is a concept (definition-only) file; there
are no proofs to outline. It reuses the $\ell^1$ norm and support-restriction
operators from `ForMathlib/VecNorms.lean` (`l1Norm`, `restrict`) and the design
map from `LinearModel/Defs.lean` (`designMap`). It is theorem-agnostic and is
consumed downstream by `Lasso/DeterministicRate.lean` (the deterministic
Lasso rate, Theorem 10.1) and `Lasso/RandomNoise.lean` (the random-noise
corollary, Corollary 10.1). The $\ell^2$ norms in $\mathrm{RE}$ and in $L_n$ are the
Euclidean norms of the underlying `EuclideanSpace ℝ (Fin _)` vectors.

**Bibliographic comments.** The Lasso estimator originates with R. Tibshirani,
"Regression shrinkage and selection via the lasso," *Journal of the Royal
Statistical Society, Series B*, 58(1):267–288 (1996). The restricted
eigenvalue condition $\mathrm{RE}(\kappa,\alpha)$ formalized here is the
restricted-eigenvalue assumption introduced by P. J. Bickel, Y. Ritov and
A. B. Tsybakov, "Simultaneous analysis of Lasso and Dantzig selector,"
*The Annals of Statistics*, 37(4):1705–1732 (2009); their Assumption
$\mathrm{RE}(s, c_0)$ (Section 4) bounds the design's restricted minimal
eigenvalue over exactly the cone $\{\lVert\Delta_{S^c}\rVert_1 \le c_0
\lVert\Delta_S\rVert_1\}$ used above. Closely related cone/curvature
conditions (the compatibility condition) appear in S. A. van de Geer and
P. Bühlmann, "On the conditions used to prove oracle results for the Lasso,"
*Electronic Journal of Statistics*, 3:1360–1392 (2009). The
$\kappa$/$\alpha$ parametrization used in this file is a specialization of
these conditions.
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- The **restricted cone** `C_α(S) = {Δ : ‖Δ_{Sᶜ}‖₁ ≤ α ‖Δ_S‖₁}` (Lu-BDA §10.1,
Definition 10.1 (Restricted Eigenvalue)):
deviations whose mass off the support `S` is at most `α` times the mass on `S`.
`Δ_S` is `restrict S Δ` and `Δ_{Sᶜ}` is `restrict Sᶜ Δ` from `VecNorms`. -/
def reCone (S : Finset (Fin d)) (α : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {Δ | l1Norm (restrict Sᶜ Δ) ≤ α * l1Norm (restrict S Δ)}

/-- **Restricted eigenvalue condition** `RE(κ, α)` for design `X` and support `S`
(Lu-BDA §10.1, Definition 10.1 (Restricted Eigenvalue)): the loss is `κ`-curved
along the cone `C_α(S)`, i.e.
`(1/n)‖X Δ‖² ≥ κ ‖Δ‖²` for every `Δ ∈ C_α(S)`. -/
def RestrictedEigenvalue (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (κ α : ℝ) : Prop :=
  ∀ Δ ∈ reCone S α, (1 / (n : ℝ)) * ‖designMap X Δ‖ ^ 2 ≥ κ * ‖Δ‖ ^ 2

/-- The **Lasso objective** `L_n(β) = (1/2n)‖Y − X β‖² + λ‖β‖₁` (Lu-BDA §10.2). -/
noncomputable def lassoObjective (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (β : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (2 * (n : ℝ))) * ‖Y - designMap X β‖ ^ 2 + lam * l1Norm β

/-- **Lasso estimator predicate** (Lu-BDA §10.2): `β̂` minimises the Lasso objective at
tuning parameter `λ` over all `β` (zero-order/minimiser characterisation). -/
def IsLassoEstimator (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (βhat : EuclideanSpace ℝ (Fin d)) :
    Prop :=
  ∀ β, lassoObjective X Y lam βhat ≤ lassoObjective X Y lam β

end StatLean.HighDimensionalStatistics
