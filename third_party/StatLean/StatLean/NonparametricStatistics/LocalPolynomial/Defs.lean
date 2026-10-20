module
public import StatLean.NonparametricStatistics.SmoothnessClasses.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Local polynomial estimators — definitions

The local polynomial estimator of order `ℓ` (LP(`ℓ`)) for fixed-design nonparametric
regression, together with its design matrix, weights, and the standing design/kernel
assumptions of its risk analysis:

* `lpBasis ℓ u = (1, u, u²/2!, …, u^ℓ/ℓ!)` — the rescaled monomial basis vector `U(u)`.
* `lpObjective` / `IsLPSolution` — the localized least-squares criterion
  `∑ i (Y i − θᵀU((xᵢ−t)/h))² K((xᵢ−t)/h)` and its minimisers `θ̂(t)`.
* `lpMatrix` — the normalized design matrix
  `B_t = (nh)⁻¹ ∑ i U(zᵢ)U(zᵢ)ᵀ K(zᵢ)`, `zᵢ = (xᵢ−t)/h`.
* `lpRhs` — the right-hand side `a_t = (nh)⁻¹ ∑ i Y i · U(zᵢ) K(zᵢ)` of the normal equations.
* `lpWeight` / `lpEstimator` — the closed-form weights
  `W*ᵢ(t) = (nh)⁻¹ · (B_t⁻¹ U(zᵢ))₀ · K(zᵢ)` and the estimator `f̂(t) = ∑ i Y i · W*ᵢ(t)`.
* `DesignEigenvalueLB` (LP1), `DesignDensityBound` (LP2), `KernelBoxed` (LP3) — the standing
  assumptions, at a fixed sample size.
* `lpWeightConst`, `lpBiasConst`, `lpVarConst`, `lpRateConst` — the explicit constants
  `C* = max{2K_max/λ₀, 4K_max·a₀/λ₀}`, `q₁ = C*·L/ℓ!`, `q₂ = σ²_max·C*²`, and the assembled
  pointwise-rate constant `q₁²·α^{2β} + q₂/α`.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.6: Definition 1.8 (the local polynomial
estimator $LP(\ell)$), Eqs. (1.65)–(1.67) (objective, normal equations, weights), and Assumptions
(LP1)–(LP3).

**Proof formalization notes.**

* *Closed form vs minimiser.* Mirroring the library's least-squares precedent, the estimator is
  defined by the closed-form weights (total, with `Matrix.inv` returning the junk `0` matrix at
  singular `B_t`), and `IsLPSolution` is the honest minimiser predicate; the equivalence under
  `PosDef` is proved in `LocalPolynomial/Quadratic.lean`. Note `(B⁻¹ v) 0 = U(0)ᵀ B⁻¹ v` since
  `U(0) = e₀`.
* *Assumptions at fixed `n`.* The classical assumptions quantify over all `n ≥ n₀`; here each
  predicate speaks about one design vector of one sample size, and asymptotic statements
  quantify externally. (LP2) is stated for all real intervals `[a, b]`; given a design contained
  in `[0,1]` this is equivalent to the classical form restricted to subintervals of `[0,1]`.
* *(LP1) as a quadratic-form bound.* `λ_min(B_t) ≥ λ₀` is encoded as
  `λ₀·‖v‖² ≤ vᵀ B_t v` for all `v` — the exact content used by the proofs, avoiding eigenvalue
  machinery.

**Bibliographic comments.** Local polynomial fitting has a long history in time-series
smoothing (1930s actuarial graduation). Its use in nonparametric regression begins with
C. J. Stone, "Consistent nonparametric regression," *Ann. Statist.* **5** (1977), 595–620; the
now-standard definition via the localized least-squares criterion appears in V. Ya. Katkovnik,
"Linear and nonlinear methods of nonparametric regression analysis," *Soviet Automat. Control*
**5** (1979), 25–34; convergence rates over smoothness classes are due to C. J. Stone,
"Optimal rates of convergence for nonparametric estimators," *Ann. Statist.* **8** (1980),
1348–1360, and "Optimal global rates of convergence for nonparametric regression," *Ann.
Statist.* **10** (1982), 1040–1053. See also J. Fan and I. Gijbels, *Local Polynomial Modelling
and Its Applications*, Chapman & Hall, 1996.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- The rescaled monomial basis vector `U(u) = (1, u, u²/2!, …, u^ℓ/ℓ!)ᵀ ∈ ℝ^{ℓ+1}`. -/
noncomputable def lpBasis (ℓ : ℕ) (u : ℝ) : Fin (ℓ + 1) → ℝ :=
  fun k => u ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ)

/-- The localized least-squares objective of LP(`ℓ`) at evaluation point `t`:
`∑ i, (Y i − θᵀ U((xdat i − t)/h))² · K((xdat i − t)/h)`. -/
noncomputable def lpObjective {n : ℕ} (xdat Y : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ)
    (t : ℝ) (θ : Fin (ℓ + 1) → ℝ) : ℝ :=
  ∑ i, (Y i - ∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k) ^ 2 * K ((xdat i - t) / h)

/-- `θ` is a **local polynomial solution** at `t`: a global minimiser of `lpObjective`. -/
def IsLPSolution {n : ℕ} (xdat Y : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ) (t : ℝ)
    (θ : Fin (ℓ + 1) → ℝ) : Prop :=
  ∀ θ' : Fin (ℓ + 1) → ℝ, lpObjective xdat Y K h ℓ t θ ≤ lpObjective xdat Y K h ℓ t θ'

/-- The normalized local design matrix
`B_t = (nh)⁻¹ ∑ i, U(zᵢ) U(zᵢ)ᵀ K(zᵢ)` with `zᵢ = (xdat i − t)/h`. -/
noncomputable def lpMatrix {n : ℕ} (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ)
    (t : ℝ) : Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ :=
  ((n : ℝ) * h)⁻¹ • ∑ i, K ((xdat i - t) / h) •
    Matrix.vecMulVec (lpBasis ℓ ((xdat i - t) / h)) (lpBasis ℓ ((xdat i - t) / h))

/-- The normal-equations right-hand side `a_t = (nh)⁻¹ ∑ i, Y i · U(zᵢ) K(zᵢ)`. -/
noncomputable def lpRhs {n : ℕ} (xdat Y : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ)
    (t : ℝ) : Fin (ℓ + 1) → ℝ :=
  fun k => ((n : ℝ) * h)⁻¹ *
    ∑ i, Y i * lpBasis ℓ ((xdat i - t) / h) k * K ((xdat i - t) / h)

/-- The closed-form LP(`ℓ`) weights `W*ᵢ(t) = (nh)⁻¹ · (B_t⁻¹ U(zᵢ))₀ · K(zᵢ)`
(the `0`-th coordinate realizes `U(0)ᵀ B_t⁻¹ U(zᵢ)` since `U(0) = e₀`). At singular `B_t` the
Mathlib inverse is the zero matrix, so the weights are total (and vanish). -/
noncomputable def lpWeight {n : ℕ} (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ)
    (t : ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) * h)⁻¹ * (lpMatrix xdat K h ℓ t)⁻¹.mulVec (lpBasis ℓ ((xdat i - t) / h)) 0
    * K ((xdat i - t) / h)

/-- The **local polynomial estimator of order `ℓ`** at `t`, in closed weight form:
`f̂(t) = ∑ i, Y i · W*ᵢ(t)`. Coincides with the first coordinate of any minimiser of
`lpObjective` when `B_t ≻ 0` (proved in `LocalPolynomial/Quadratic.lean`). -/
noncomputable def lpEstimator {n : ℕ} (xdat Y : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ)
    (t : ℝ) : ℝ :=
  ∑ i, Y i * lpWeight xdat K h ℓ t i

/-- **(LP1)** at sample size `n`: uniformly over `t ∈ [0,1]`, the local design matrix has
quadratic form bounded below by `lam0·‖v‖²` (i.e. `λ_min(B_t) ≥ lam0`). -/
def DesignEigenvalueLB {n : ℕ} (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ)
    (lam0 : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v : Fin (ℓ + 1) → ℝ,
    lam0 * ∑ k, (v k) ^ 2 ≤ ∑ k, v k * (lpMatrix xdat K h ℓ t).mulVec v k

/-- **(LP2)** at sample size `n`: the empirical measure of the design puts mass at most
`a₀ · max(b − a, 1/n)` on every interval `[a, b]`. For the regular design `i/n` this holds
with `a₀ = 2`. -/
def DesignDensityBound {n : ℕ} (xdat : Fin n → ℝ) (a₀ : ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b →
    (n : ℝ)⁻¹ * ∑ i, (Set.Icc a b).indicator (fun _ => (1 : ℝ)) (xdat i)
      ≤ a₀ * max (b - a) (n : ℝ)⁻¹

/-- **(LP3)**: the kernel is bounded by `Kmax` and supported in `[−1, 1]`. -/
def KernelBoxed (K : ℝ → ℝ) (Kmax : ℝ) : Prop :=
  (∀ u, |K u| ≤ Kmax) ∧ ∀ u, u ∉ Set.Icc (-1 : ℝ) 1 → K u = 0

/-- The explicit weight constant `C* = max{2·K_max/λ₀, 4·K_max·a₀/λ₀}` of the weight bounds. -/
noncomputable def lpWeightConst (Kmax lam0 a₀ : ℝ) : ℝ :=
  max (2 * Kmax / lam0) (4 * Kmax * a₀ / lam0)

/-- The explicit bias constant `q₁ = C*·L/ℓ!` (with `ℓ = holderIndex β`) of the pointwise bias
bound for LP(`ℓ`) over the Hölder class `Σ(β, L)`. -/
noncomputable def lpBiasConst (β L Kmax lam0 a₀ : ℝ) : ℝ :=
  lpWeightConst Kmax lam0 a₀ * L / (Nat.factorial (holderIndex β) : ℝ)

/-- The explicit variance constant `q₂ = σ²_max·C*²` of the pointwise variance bound. -/
noncomputable def lpVarConst (σmax2 Kmax lam0 a₀ : ℝ) : ℝ :=
  σmax2 * (lpWeightConst Kmax lam0 a₀) ^ 2

/-- The assembled pointwise-rate constant `q₁²·α^{2β} + q₂/α` obtained by substituting the
bandwidth `h = α·n^{−1/(2β+1)}` into `q₁²h^{2β} + q₂/(nh)`. -/
noncomputable def lpRateConst (β L α σmax2 Kmax lam0 a₀ : ℝ) : ℝ :=
  (lpBiasConst β L Kmax lam0 a₀) ^ 2 * α ^ (2 * β) + lpVarConst σmax2 Kmax lam0 a₀ / α

end StatLean.NonparametricStatistics
