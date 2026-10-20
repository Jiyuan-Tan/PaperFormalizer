module
public import StatLean.HighDimensionalStatistics.ForMathlib.SupportSubmatrix
public import StatLean.HighDimensionalStatistics.ForMathlib.GramMatrix
public import StatLean.HighDimensionalStatistics.Lasso.Defs

@[expose] public section

/-!
# Lasso support recovery — definitions and regularity conditions

Concept-layer book-facing predicates for variable-selection (support) consistency of the
Lagrangian Lasso. Fix a design matrix $X \in \mathbb{R}^{n \times d}$, a true support set
$S \subseteq \{1, \dots, d\}$ with complement $S^c$, and write $X_S$ for the submatrix of
columns indexed by $S$. The Lasso estimator minimizes
$\tfrac{1}{2n}\lVert Y - X\theta\rVert_2^2 + \lambda\lVert\theta\rVert_1$. The conditions
below are the standard hypotheses under which the Lasso recovers $S$ exactly.

* **Lower-eigenvalue condition (A3).** The support Gram submatrix has smallest eigenvalue
  bounded below: $\gamma_{\min}\!\big(\tfrac{1}{n}X_S^\top X_S\big) \ge c_{\min} > 0$.
  Formalized in the equivalent Rayleigh-quotient form
  $c_{\min}\lVert v\rVert^2 \le \tfrac{1}{n}\lVert X_S v\rVert^2$ for all $v$ supported on $S$.
* **Mutual-incoherence condition (A4).** For every off-support column $X_j$ ($j \notin S$),
  the population regression of $X_j$ onto the support columns has small $\ell^1$ mass:
  $\big\lVert (X_S^\top X_S)^{-1} X_S^\top X_j \big\rVert_1 \le \alpha$ (with $\alpha < 1$).
* **$\ell^1$ subdifferential.** $z \in \partial\lVert\theta\rVert_1$, i.e. $z_j = \operatorname{sign}(\theta_j)$
  whenever $\theta_j \neq 0$, and $z_j \in [-1,1]$ when $\theta_j = 0$.
* **Zero-subgradient / KKT condition.** First-order optimality of the Lagrangian Lasso:
  $\tfrac{1}{n}X^\top(X\theta - Y) + \lambda z = 0$ for some $z \in \partial\lVert\theta\rVert_1$.
* **Column normalization.** Every design column has $\ell^2$ norm bounded by $C\sqrt{n}$, i.e.
  $\max_j \lVert X_j\rVert_2 / \sqrt{n} \le C$.
* **$\ell^\infty$ error bound $B(\lambda; X)$.** The estimate of the on-support $\ell^\infty$
  error, $B(\lambda; X) = \big\lVert (\tfrac{1}{n}X_S^\top X_S)^{-1} X_S^\top w / n\big\rVert_\infty
  + \big\lvert\!\big\lvert\!\big\lvert (\tfrac{1}{n}X_S^\top X_S)^{-1}\big\rvert\!\big\rvert\!\big\rvert_\infty \cdot \lambda$,
  with $w$ the noise vector.
* **Projected-noise quantity.** $\big\lVert X_{S^c}^\top \Pi_{S^\perp}(X)\,(w/n)\big\rVert_\infty$,
  appearing on the right-hand side of the regularization-strength condition
  $\lambda \ge \tfrac{2}{1-\alpha}\,\lVert X_{S^c}^\top \Pi_{S^\perp}(X)(w/n)\rVert_\infty$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019, Chapter 7 (Sparse Linear Models in High Dimensions), §7.5
(Variable or model selection consistency). Conditions (A3)/(A4) are §7.5.1, Eq (7.43a)/(7.43b);
the zero-subgradient/KKT condition is §7.5.2, Eq (7.48); the regularization condition is Eq (7.44);
the $\ell^\infty$ bound $B(\lambda; X)$ is Eq (7.45) (Theorem 7.21(c)); the column-normalization
condition is Corollary 7.22.

**Proof formalization notes.** These are the concept-layer (laptop-only) predicates and
quantities consumed by the support-recovery assembly:

* `LowerEigenvalue X S cmin` — condition (A3), Eq (7.43a), in Rayleigh-quotient form.
* `MutualIncoherence X S α`  — condition (A4), Eq (7.43b).
* `IsL1Subgradient z θ`      — $z \in \partial\lVert\theta\rVert_1$ (§7.5.2).
* `IsKKT X Y λ θ z`          — the zero-subgradient/KKT condition, Eq (7.48).
* `ColumnNormalized X C`     — the $C$-column-normalization condition of Corollary 7.22.
* `gramInvNorm X S`          — the inverse of the *normalized* Gram $(\tfrac{1}{n}X_S^\top X_S)^{-1}$ in (7.45).
* `supportRecoveryBound`     — $B(\lambda; X)$, the $\ell^\infty$ error bound of Theorem 7.21(c), Eq (7.45).
* `projNoiseLinf X S w`      — the projected-noise quantity on the RHS of Eq (7.44).

The **Lasso objective itself is reused** from `Lasso/Defs.lean` (`lassoObjective`,
`IsLassoEstimator`) — identical to Wainwright's Lagrangian Lasso (7.18). Reuses
`designSub` / `Xsub` / `col` (`SupportSubmatrix.lean`), `gram` / `gramInv` / `matLinftyNorm`
(`GramMatrix.lean`), and `designMap` / `restrict` (`LinearModel`, `VecNorms`).

**Bibliographic comments.** The mutual-incoherence (irrepresentability) condition together
with the primal-dual witness method for exact Lasso support recovery originate with
M. J. Wainwright, "Sharp thresholds for high-dimensional and noisy sparsity recovery using
$\ell_1$-constrained quadratic programming (Lasso)," *IEEE Transactions on Information Theory*,
vol. 55, no. 5, pp. 2183–2202, May 2009. Conditions (A3)/(A4) and Theorem 7.21 give a
non-asymptotic synthesis of that paper; the incoherence/irrepresentable
condition was independently identified for the noiseless and deterministic-design settings by
P. Zhao and B. Yu, "On model selection consistency of Lasso," *Journal of Machine Learning
Research*, vol. 7, pp. 2541–2563, 2006, and by N. Meinshausen and P. Bühlmann, "High-dimensional
graphs and variable selection with the Lasso," *Annals of Statistics*, vol. 34, no. 3,
pp. 1436–1462, 2006.
-/

open Matrix
open scoped InnerProductSpace

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Lower-eigenvalue condition (A3)** (Wainwright §7.5.1, 7.43a). Constitutive: the
sample Gram submatrix on the support has smallest eigenvalue `≥ cmin > 0`. Stated in
equivalent **quadratic-form (Rayleigh-quotient)** form `cmin·‖v‖² ≤ (1/n)·‖Xₛ v‖²`
for all `v` on the support; this is `γ_min(XₛᵀXₛ/n) ≥ cmin` by Courant–Fischer. -/
def LowerEigenvalue (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) (cmin : ℝ) :
    Prop :=
  ∀ v : EuclideanSpace ℝ {x // x ∈ S},
    cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2

/-- **Mutual-incoherence condition (A4)** (Wainwright §7.5.1, 7.43b). Constitutive:
for every off-support column `X_j` (`j ∉ S`), the regression coefficients of `X_j` on
the support columns have ℓ¹ norm `≤ α`, i.e. `‖(XₛᵀXₛ)⁻¹ Xₛᵀ X_j‖₁ ≤ α`. -/
def MutualIncoherence (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) (α : ℝ) :
    Prop :=
  ∀ j ∉ S,
    (∑ i : {x // x ∈ S},
      |((gramInv X S).mulVec ((Xsub X S)ᵀ.mulVec (col X j).ofLp)) i|) ≤ α

/-- **Subdifferential of the ℓ¹ norm** (Wainwright §7.5.2): `z ∈ ∂‖θ‖₁` iff
`z_j = sign(θ_j)` for every `j`, with `sign 0` free in `[-1,1]`. -/
def IsL1Subgradient (z θ : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ i, (0 < θ.ofLp i → z.ofLp i = 1) ∧ (θ.ofLp i < 0 → z.ofLp i = -1) ∧ |z.ofLp i| ≤ 1

/-- **Zero-subgradient / KKT condition** (Wainwright §7.5.2, 7.48):
`(1/n) Xᵀ(X θ − Y) + λ z = 0`, the optimality condition of the Lagrangian Lasso. -/
def IsKKT (X : Matrix (Fin n) (Fin d) ℝ) (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ)
    (θ z : EuclideanSpace ℝ (Fin d)) : Prop :=
  (1 / (n : ℝ)) • designMap Xᵀ (designMap X θ - Y) + lam • z = 0

/-- **C-column-normalization condition** (Wainwright Cor 7.22): every design column has
ℓ² norm `≤ C√n`, i.e. `max_j ‖X_j‖₂/√n ≤ C`. -/
def ColumnNormalized (X : Matrix (Fin n) (Fin d) ℝ) (C : ℝ) : Prop :=
  ∀ j, ‖col X j‖ ≤ C * Real.sqrt n

/-- The inverse of the *normalized* Gram `(XₛᵀXₛ/n)⁻¹` appearing in the bound (7.45). -/
noncomputable def gramInvNorm (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Matrix {x // x ∈ S} {x // x ∈ S} ℝ :=
  ((1 / (n : ℝ)) • gram X S)⁻¹

/-- **ℓ∞ error bound** `B(λ;X)` of Theorem 7.21(c) (Wainwright 7.45):
`B(λ;X) = ‖(XₛᵀXₛ/n)⁻¹ Xₛᵀ w/n‖_∞ + |||(XₛᵀXₛ/n)⁻¹|||_∞ · λ`. -/
noncomputable def supportRecoveryBound (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d)) (w : EuclideanSpace ℝ (Fin n)) (lam : ℝ) : ℝ :=
  (⨆ i : {x // x ∈ S},
    |((gramInvNorm X S).mulVec
        ((1 / (n : ℝ)) • (Xsub X S)ᵀ.mulVec w.ofLp)) i|)
  + matLinftyNorm (gramInvNorm X S) * lam

/-- The quantity `‖Xₛᶜᵀ Π_{S⊥}(X) (w/n)‖_∞` appearing on the RHS of the regularization
condition (7.44). The condition is `λ ≥ (2/(1−α)) · projNoiseLinf X S w`. -/
noncomputable def projNoiseLinf (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ j : {x // x ∈ Sᶜ},
    |((Xsub X Sᶜ)ᵀ.mulVec ((1 / (n : ℝ)) • (projPerp X S).mulVec w.ofLp)) j|

end StatLean.HighDimensionalStatistics
