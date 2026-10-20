module
public import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
public import StatLean.HighDimensionalStatistics.LinearModel.Defs
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# Fixed-design generalized linear model (exponential family, conditions G1/G2)

This is the data model underlying the high-dimensional GLM corollaries (Corollaries 9.26 / 9.27).
We fix a deterministic design matrix $X \in \mathbb{R}^{n \times d}$, a target regression vector
$\theta^\star \in \mathbb{R}^d$, and independent responses $y_1, \dots, y_n$, where each $y_i$ is
drawn from a one-parameter exponential family with natural parameter equal to the linear predictor
$\eta_i = \langle x_i, \theta^\star\rangle$ (the $i$-th coordinate of $X\theta^\star$) and cumulant
(partition / log-normalizer) function $\psi$. In exponential-family form (Eq. 9.5), the density is
proportional to $\exp\!\big(y\,\eta - \psi(\eta)\big)$, so $\psi'$ is the mean function and $\psi''$
is the variance function.

The two structural conditions formalized here are:

* **Condition G2 (bounded cumulant curvature).** The second derivative satisfies
  $0 \le \psi''(t) \le B^2$ for all $t$, i.e. $\|\psi''\|_\infty \le B^2$. Nonnegativity is automatic
  for an exponential family ($\psi''$ is a variance, so $\psi$ is convex); the upper bound $B^2$ is
  the genuine modeling assumption.
* **Condition G1 (column normalization).** For every column $j$, $\sum_{i} X_{ij}^2 \le n\,C^2$,
  equivalently $\max_j \sqrt{\tfrac{1}{n}\sum_i X_{ij}^2} \le C$.

In place of carrying the density explicitly, the exponential-family structure is encoded by the
moment-generating-function identity
$\mathbb{E}\!\big[e^{s\,y_i}\big] = \exp\!\big(\psi(\eta_i + s) - \psi(\eta_i)\big)$, taken with unit
dispersion ($c(\sigma) = 1$, as in the proof of Corollary 9.26). This identity is precisely what the
corollary's proof uses to center and sub-Gaussian-bound the score. Because the design is fixed, the
score coordinate $V_{ij} = \big(\psi'(\eta_i) - y_i\big)\,X_{ij}$ is a function of $y_i$ alone, so no
conditional-expectation machinery is required.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
University Press, 2019, Chapter 9 (Decomposability and restricted strong convexity), §9.1 and §9.5,
exponential-family GLM Eq. (9.5), conditions G1 (column normalization) and G2
($0 \le \psi'' \le B^2$), with the model serving Corollaries 9.26 / 9.27.

**Proof formalization notes.** This file is a shared data model (`GLMExpFamily`) plus the derived
quantities (linear predictor `linPred`, score coordinate / vector `scoreCoord` / `scoreVec`, GLM
negative-log-likelihood cost `glmCost` matching Eq. 9.7/9.61, and the column-normalization predicate
`IsColumnNormalized` for G1); there is no theorem here to prove. The MGF identity `hmgf` is stated
with dispersion $c(\sigma) = 1$, exactly the normalization used in the Corollary 9.26 proof (p. 288).
The exponential-family curvature facts are recorded as constitutive structure fields: `hψ''_nonneg`
($0 \le \psi''$, convexity of $\psi$) and `hψ''_le` ($\psi'' \le B^2$, condition G2). Fixed design
makes the score a function of `y i` only, so no conditioning is carried. Laptop-only shared data
model; consumed by `ScoreSubGaussian`, `GoodEvent`, `GLMCorollaries`.

**Bibliographic comments.** The unified high-dimensional M-estimator framework that these GLM
corollaries instantiate originates with S. Negahban, P. Ravikumar, M. J. Wainwright and B. Yu, "A
unified framework for high-dimensional analysis of $M$-estimators with decomposable regularizers,"
*Statistical Science* 27(4):538–557, 2012 (DOI 10.1214/12-STS400; arXiv:1010.2731, 2010). That paper
introduces the decomposable-regularizer / restricted-strong-convexity machinery and applies it to
generalized linear models, where the column-normalization condition (here G1) and the bounded
cumulant second derivative (here G2) appear as the regularity assumptions for the GLM example.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {n d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The linear predictor `ηᵢ(θ) = ⟨xᵢ, θ⟩ = ∑ⱼ Xᵢⱼ·θⱼ` (the `i`-th coordinate of `Xθ`). -/
def linPred (X : Matrix (Fin n) (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (i : Fin n) : ℝ :=
  ∑ j, X i j * θ.ofLp j

/-- A **fixed-design generalized linear model** (Wainwright §9.1, eq 9.5; G2). Each response `yᵢ` is an
exponential-family variate with natural parameter `ηᵢ = ⟨xᵢ, θ*⟩` and partition function `ψ`. -/
structure GLMExpFamily (n d : ℕ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- Constitutive: the fixed design matrix `X ∈ ℝ^{n×d}`. -/
  X : Matrix (Fin n) (Fin d) ℝ
  /-- Constitutive: the target regression vector `θ*`. -/
  θstar : EuclideanSpace ℝ (Fin d)
  /-- Constitutive (eq 9.5): the partition / cumulant function `ψ`. -/
  ψ : ℝ → ℝ
  /-- Constitutive: its first derivative `ψ'` (the mean function). -/
  ψ' : ℝ → ℝ
  /-- Constitutive: its second derivative `ψ''` (the variance function). -/
  ψ'' : ℝ → ℝ
  /-- The cumulant bound parameter `B` (condition G2). -/
  B : ℝ
  /-- Constitutive: the responses `yᵢ : Ω → ℝ`. -/
  y : Fin n → Ω → ℝ
  /-- Constitutive: `ψ'` is the derivative of `ψ`. -/
  hψ' : ∀ a, HasDerivAt ψ (ψ' a) a
  /-- Constitutive: `ψ''` is the derivative of `ψ'`. -/
  hψ'' : ∀ a, HasDerivAt ψ' (ψ'' a) a
  /-- Constitutive (exponential family: `ψ''` = conditional variance ≥ 0, so `ψ` is convex). -/
  hψ''_nonneg : ∀ a, 0 ≤ ψ'' a
  /-- Constitutive (G2): bounded second derivative `‖ψ''‖∞ ≤ B²`. -/
  hψ''_le : ∀ a, ψ'' a ≤ B ^ 2
  /-- Constitutive: each response is measurable. -/
  hy_meas : ∀ i, Measurable (y i)
  /-- Constitutive: the responses are jointly independent (fixed design). -/
  hindep : iIndepFun y μ
  /-- Constitutive (eq 9.5): the exponential-family MGF identity
  `𝔼[e^{s·yᵢ}] = exp(ψ(ηᵢ + s) − ψ(ηᵢ))` (with the dispersion `c(σ) = 1`, as in the Cor 9.26 proof). -/
  hmgf : ∀ (i : Fin n) (s : ℝ),
    mgf (y i) μ s = Real.exp (ψ (linPred X θstar i + s) - ψ (linPred X θstar i))

variable {μ : Measure Ω}

/-- The `j`-th coordinate of the score `∇Lₙ(θ*) = (1/n)∑ᵢ Vᵢ`, namely
`(1/n)∑ᵢ (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` (Wainwright Cor 9.26 proof, the random vector `Vᵢⱼ`). -/
noncomputable def scoreCoord (M : GLMExpFamily n d μ) (j : Fin d) (ω : Ω) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (M.ψ' (linPred M.X M.θstar i) - M.y i ω) * M.X i j

/-- The score vector `∇Lₙ(θ*) ∈ ℝ^d`, with coordinates `scoreCoord`. -/
noncomputable def scoreVec (M : GLMExpFamily n d μ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp (p := 2) (fun j => scoreCoord M j ω)

/-- The GLM negative-log-likelihood cost `Lₙ(θ) = (1/n)∑ᵢ[ψ(⟨xᵢ,θ⟩) − yᵢ⟨xᵢ,θ⟩]` (eq 9.7/9.61). -/
noncomputable def glmCost (M : GLMExpFamily n d μ) (ω : Ω) (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (M.ψ (linPred M.X θ i) - M.y i ω * linPred M.X θ i)

/-- **Column-normalization condition (G1)**: `∑ᵢ Xᵢⱼ² ≤ n·C²` for every `j`
(i.e. `maxⱼ √(∑ᵢ Xᵢⱼ²/n) ≤ C`). -/
def IsColumnNormalized (X : Matrix (Fin n) (Fin d) ℝ) (C : ℝ) : Prop :=
  ∀ j, ∑ i, X i j ^ 2 ≤ (n : ℝ) * C ^ 2

end StatLean.HighDimensionalStatistics.MEstimator
