module
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section

/-!
# Regularized M-estimators: decomposable regularizers and restricted strong convexity

Concept-layer definitions for the `MEstimator` milestone. Consider a regularized M-estimator
of the form
$$\hat\theta \in \arg\min_{\theta}\bigl\{\, \mathcal L_n(\theta) + \lambda_n\,\Phi(\theta)\,\bigr\},$$
where $\mathcal L_n$ is an empirical cost (loss) and $\Phi$ is a norm acting as the regularizer.
This file formalizes the two structural ingredients on which the general estimation-error
theory rests, together with the auxiliary quantities (error cone, subspace Lipschitz constant,
good event, objective increment, error radius) used to assemble the rates.

* **Decomposability.** A regularizer $\Phi$ is *decomposable* with respect to a subspace pair
  $(M,\,\bar M^{\perp})$ (with $M\subseteq\bar M$) when
  $\Phi(\alpha+\beta)=\Phi(\alpha)+\Phi(\beta)$ for every $\alpha\in M$ and $\beta\in\bar M^{\perp}$.
  We bundle $\Phi$ together with its dual norm $\Phi^*$, the subspace pair, and the generalized
  Hölder inequality $\langle u,v\rangle\le\Phi(u)\,\Phi^*(v)$ (with $\Phi^*$ pinned down as the
  *smallest* norm satisfying Hölder) into the structure `DecomposableReg`.
* **Restricted strong convexity (RSC).** Writing the first-order Taylor error as
  $\mathcal E_n(\Delta)=\mathcal L_n(\theta+\Delta)-\mathcal L_n(\theta)-\langle\nabla\mathcal L_n(\theta),\Delta\rangle$,
  the cost satisfies $\mathrm{RSC}(\kappa,R,\tau^2)$ when
  $\mathcal E_n(\Delta)\ge\tfrac{\kappa}{2}\lVert\Delta\rVert^2-\tau^2\,\Phi(\Delta)^2$ for all
  $\Delta$ with $\lVert\Delta\rVert\le R$, with curvature $\kappa$ and tolerance $\tau^2$.
* **Dual $\Phi^*$-curvature.** The dual-norm analogue of RSC,
  $\Phi^*\!\bigl(\nabla\mathcal L_n(\theta+\Delta)-\nabla\mathcal L_n(\theta)\bigr)\ge\kappa\,\Phi^*(\Delta)-\tau\,\Phi(\Delta)$
  for all $\Delta$ with $\Phi^*(\Delta)\le R$, underlying the $\ell_\infty$ bound.

The space $E$ is a finite-dimensional real inner-product space; $\lVert\cdot\rVert$ is the
inner-product norm and $\Phi$ is a *separate* regularizer norm (e.g. $\ell_1$ while
$\lVert\cdot\rVert=\ell_2$). All projections $\Delta_M$, $\Delta_{\bar M}$, $\theta^*_{M^{\perp}}$,
… are **orthogonal** projections with respect to $\langle\cdot,\cdot\rangle$, realized by
`Submodule.starProjection` (the `E`-valued orthogonal projection).

Laptop-only shared data model: this file fixes the encodings consumed by the deterministic
assembly (`Deviation`, `Bound`, `DualBound`) and the GLM assembly.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019, Chapter 9 (Decomposability and restricted strong convexity).
The regularized M-estimator is Eq (9.3); decomposability of $\Phi$ over $(M,\bar M^{\perp})$ is
Definition 9.9, Eq (9.22); restricted strong convexity is Definition 9.15, Eq (9.38); the
$\Phi^*$-curvature condition is Definition 9.22, Eq (9.55). Auxiliary objects: the subspace
pair $\bar M\supseteq M$ is Eq (9.21); the dual norm and generalized Hölder inequality are
Eq (9.27); the subspace Lipschitz constant $\Psi(\mathcal M)=\sup_{u\in\mathcal M\setminus\{0\}}\Phi(u)/\lVert u\rVert$
is Definition 9.18, Eq (9.44); the good event $\Phi^*(\nabla\mathcal L_n(\theta^*))\le\lambda/2$ is
Eq (9.28)/(9.46); the objective increment $\mathcal F(\Delta)$ is Eq (9.31); the error cone
$\mathbb C(M,\bar M^{\perp})$ is Eq (9.29); the error radius $\varepsilon_n^2$ is Eq (9.47).

**Proof formalization notes.** These are statement-level (concept) definitions consumed
downstream; there are no proofs in this file. The one deliberate book-vs-Lean deviation is in
the error-radius quantity `epsilonSq` (Wainwright Eq (9.47)). The book states leading constant
$9$, slack $(8/\kappa)$, under $\tau^2\Psi^2\le\kappa/64$. Those are only achievable as
$\tau\to 0$: the RSC lower bound is
$\mathcal F(\Delta)\ge(\kappa/2-32\tau^2\Psi^2)\lVert\Delta\rVert^2-(3\lambda/2)\Psi\lVert\Delta\rVert-D$,
so the effective curvature $c=\kappa/2-32\tau^2\Psi^2<\kappa/2$, and at
$\lVert\Delta\rVert^2=9(\lambda/\kappa)^2\Psi^2$ one gets $\mathcal F<0$ for any $\tau>0$
(the book's $\mathcal F>0$ argument fails). The provable bound requires $\tau^2\Psi^2\le\kappa/128$
(so $c\ge\kappa/4$) and uses the `nlinarith`-friendly threshold $\delta^2>(2\beta/c)^2+2D/c$
(with $\beta=(3\lambda/2)\Psi$, $D=2\lambda\Phi+32\tau^2\Phi^2$), giving leading constant $144$
($\sqrt{\,\cdot\,}=12$) and slack $(32/\kappa)$, with strict margin. The estimation rate
$s\cdot\lambda^2/\kappa^2$ is unchanged; only the constants differ. The $\theta^*$ projection in
`epsilonSq`/`errorCone` is onto $M^{\perp}$, matching the $\varepsilon_n^2$ argument label
$(\bar M,M^{\perp})$.

**Bibliographic comments.** The decomposability + restricted-strong-convexity framework
formalized here originates with S. Negahban, P. Ravikumar, M. J. Wainwright and B. Yu,
"A unified framework for high-dimensional analysis of $M$-estimators with decomposable
regularizers," *Statistical Science* 27(4):538–557, 2012 (conference version: NIPS 22, 2009;
preprint arXiv:1010.2731). There, decomposability of $\Phi$ relative to a subspace pair
$(\mathcal M,\bar{\mathcal M}^{\perp})$ is **Definition 1** and restricted strong convexity of the
loss is **Definition 2**; the error cone and the deterministic $\ell_2$-error bound on the good
event are the paper's Theorem 1, which Wainwright's Chapter 9 reproduces and refines (the dual
$\Phi^*$-curvature condition and $\ell_\infty$ bound are a later textbook addition). The cited
equation/definition numbers (9.x) follow Wainwright (2019); the seminal-paper numbering (Def 1,
Def 2, Thm 1) is given for cross-reference.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace

/-- A **decomposable regularizer** together with its dual norm and ambient subspace pair
(Wainwright §9.2). Bundling the dual norm `Φstar` with the Hölder and tightness fields is exactly
"`Φ*` is the dual norm of `Φ`" (eq 9.27, `Φ*(v) = sup_{Φ(u)≤1} ⟨u,v⟩`): `holder` is the
`≥`-direction for every `u`, and `tight` is the variational characterization that pins `Φ*` down
as the *smallest* norm satisfying Hölder. -/
structure DecomposableReg (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- Constitutive (Wainwright §9.2.1): the model subspace `M` (the structure expected of `θ*`). -/
  M : Submodule ℝ E
  /-- Constitutive (Wainwright §9.2.1, eq 9.21): the subspace `M̄ ⊇ M` whose orthogonal complement
  `M̄ᗮ` is the perturbation subspace; in the ideal case `M̄ = M`. -/
  Mbar : Submodule ℝ E
  /-- Constitutive (Wainwright §9.2.1): the subspace pair satisfies `M ⊆ M̄`. -/
  subset_Mbar : M ≤ Mbar
  /-- Constitutive (Wainwright §9.1): the regularizer `Φ`, a norm on `E`. -/
  Φ : Seminorm ℝ E
  /-- Constitutive (Wainwright eq 9.27): the dual norm `Φ*`. -/
  Φstar : Seminorm ℝ E
  /-- Constitutive (Wainwright eq 9.27): generalized Hölder `⟨u,v⟩ ≤ Φ(u)·Φ*(v)`. -/
  holder : ∀ u v : E, ⟪u, v⟫_ℝ ≤ Φ u * Φstar v
  /-- Constitutive (Wainwright eq 9.27): `Φ*` is the *least* norm satisfying Hölder, i.e. the
  variational characterization `Φ*(v) ≤ c` whenever `⟨u,v⟩ ≤ c` for all `Φ(u) ≤ 1`. -/
  tight : ∀ (v : E) (c : ℝ), (∀ u : E, Φ u ≤ 1 → ⟪u, v⟫_ℝ ≤ c) → Φstar v ≤ c
  /-- Constitutive (Wainwright Def 9.9, eq 9.22): decomposability of `Φ` over `(M, M̄ᗮ)`,
  `Φ(α + β) = Φ(α) + Φ(β)` for `α ∈ M`, `β ∈ M̄ᗮ`. -/
  decomp : ∀ α ∈ M, ∀ β ∈ (Mbar)ᗮ, Φ (α + β) = Φ α + Φ β

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The **first-order Taylor-series error** `Eₙ(Δ) = Lₙ(θ + Δ) − Lₙ(θ) − ⟪∇Lₙ(θ), Δ⟫`
(Wainwright eq 9.36). For convex `Lₙ` this is `≥ 0`; restricted strong convexity lower-bounds it
by a quadratic minus a regularizer-slack term. -/
noncomputable def taylorErr (L : E → ℝ) (θ Δ : E) : ℝ :=
  L (θ + Δ) - L θ - ⟪gradient L θ, Δ⟫_ℝ

/-- **Restricted strong convexity** `RSC(κ, R, τ²)` (Wainwright Def 9.15, eq 9.38):
`Eₙ(Δ) ≥ (κ/2)‖Δ‖² − τ²·Φ(Δ)²` for every `Δ` in the ball `‖Δ‖ ≤ R`. Here `τSq = τ_n²` is the
squared tolerance and `κ` the curvature. -/
def RSC (L : E → ℝ) (θ : E) (Φ : Seminorm ℝ E) (κ R τSq : ℝ) : Prop :=
  ∀ Δ : E, ‖Δ‖ ≤ R → taylorErr L θ Δ ≥ κ / 2 * ‖Δ‖ ^ 2 - τSq * (Φ Δ) ^ 2

/-- The **subspace Lipschitz constant** `Ψ(S) = sup_{u ∈ S∖{0}} Φ(u)/‖u‖` (Wainwright Def 9.18,
eq 9.44): the worst-case ratio of the regularizer to the error norm, restricted to `S`. Edge
behavior: `Ψ(0) = sSup ∅ = 0`. -/
noncomputable def subspaceLip (Φ : Seminorm ℝ E) (S : Submodule ℝ E) : ℝ :=
  sSup ((fun u => Φ u / ‖u‖) '' ((S : Set E) \ {0}))

/-- The **good event** `𝔾(λ) = {Φ*(∇Lₙ(θ*)) ≤ λ/2}` (Wainwright eq 9.28/9.46), as a predicate on
the score vector `g = ∇Lₙ(θ*)`: the regularization weight dominates twice the dual norm of the
score. -/
def GoodEvent (Φstar : Seminorm ℝ E) (g : E) (lam : ℝ) : Prop :=
  Φstar g ≤ lam / 2

/-- The **objective increment** `ℱ(Δ) = L(θ*+Δ) − L(θ*) + λ·(Φ(θ*+Δ) − Φ(θ*))` (Wainwright eq 9.31).
By construction `ℱ(0) = 0`; optimality of `θ̂` forces `ℱ(θ̂ − θ*) ≤ 0`. Convex in `Δ` when `L` and `Φ`
are convex and `λ ≥ 0`. -/
noncomputable def Fcal (L : E → ℝ) (Φ : Seminorm ℝ E) (θstar : E) (lam : ℝ) (Δ : E) : ℝ :=
  L (θstar + Δ) - L θstar + lam * (Φ (θstar + Δ) - Φ θstar)

/-- The **error cone** `ℂ(M, M̄ᗮ) = {Δ : Φ(Δ_{M̄ᗮ}) ≤ 3·Φ(Δ_{M̄}) + 4·Φ(θ*_{Mᗮ})}`
(Wainwright eq 9.29): on the good event the error `θ̂ − θ*` is guaranteed to lie here. -/
def errorCone (dr : DecomposableReg E) (θstar : E) : Set E :=
  {Δ : E | dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) ≤
      3 * dr.Φ (dr.Mbar.starProjection Δ) + 4 * dr.Φ ((dr.M)ᗮ.starProjection θstar)}

/-- The error quantity `εₙ²(M̄, Mᗮ)` governing the `ℓ₂` rate in Thm 9.19(b):
`144(λ²/κ²)·Ψ²(M̄) + (32/κ){λ·Φ(θ*_{Mᗮ}) + 16τ²·Φ(θ*_{Mᗮ})²}` — an estimation-error term plus an
approximation-error term. The `θ*` projection is onto `Mᗮ` (the proof projects `θ*` onto the model
subspace `M`, as decomposability requires; the εₙ² argument label `(M̄, M^⊥)` confirms this).

**Book-constant deviation (Wainwright eq 9.47).** The book states leading `9`, slack `(8/κ)`, under
`τ²Ψ² ≤ κ/64`. Those are only achievable as `τ → 0`: the RSC lower bound is
`ℱ(Δ) ≥ (κ/2 − 32τ²Ψ²)‖Δ‖² − (3λ/2)Ψ‖Δ‖ − D`, so the effective curvature `c = κ/2 − 32τ²Ψ² < κ/2`,
and at `‖Δ‖² = 9(λ/κ)²Ψ²` one gets `ℱ < 0` for any `τ > 0` (Lemma 9.21's `ℱ > 0` fails). The provable
bound requires `τ²Ψ² ≤ κ/128` (so `c ≥ κ/4`) and uses the clean nlinarith-friendly threshold
`δ² > (2β/c)² + 2D/c` (`β = (3λ/2)Ψ`, `D = 2λΦ + 32τ²Φ²`), giving leading `144` (`√ = 12`) and slack
`(32/κ)`, with strict margin. Same rate `s·λ²/κ²`; only the constants differ. -/
noncomputable def epsilonSq (dr : DecomposableReg E) (θstar : E) (lam κ τSq : ℝ) : ℝ :=
  144 * (lam ^ 2 / κ ^ 2) * (subspaceLip dr.Φ dr.Mbar) ^ 2 +
    32 / κ * (lam * dr.Φ ((dr.M)ᗮ.starProjection θstar) +
      16 * τSq * (dr.Φ ((dr.M)ᗮ.starProjection θstar)) ^ 2)

/-- The **`Φ*`-norm curvature condition** (Wainwright Def 9.22, eq 9.55):
`Φ*(∇Lₙ(θ + Δ) − ∇Lₙ(θ)) ≥ κ·Φ*(Δ) − τ·Φ(Δ)` for all `Δ` with `Φ*(Δ) ≤ R`. This is the
dual-norm analogue of RSC, underlying the `ℓ∞` bound of Theorem 9.24. -/
def dualCurvature (L : E → ℝ) (θ : E) (Φ Φstar : Seminorm ℝ E) (κ τ R : ℝ) : Prop :=
  ∀ Δ : E, Φstar Δ ≤ R →
    Φstar (gradient L (θ + Δ) - gradient L θ) ≥ κ * Φstar Δ - τ * Φ Δ

end StatLean.HighDimensionalStatistics.MEstimator
