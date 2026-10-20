module
public import Mathlib.Probability.Decision.Risk.Basic
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
# Minimax lower bounds — core data model (minimax risk, M-ary testing, separated families)

Shared data model for the `Minimaxity` area, formalizing the core objects of
Wainwright's minimax lower-bound framework.

Fix a class of distributions $\mathcal{P} = \{P_\theta\}$, a functional $\theta \mapsto \theta(P_\theta)$
taking values in a space equipped with a *semimetric* $\rho$ (a distance allowed to vanish
on distinct points, Wainwright's footnote 1), and an increasing distortion
$\Phi : [0,\infty] \to [0,\infty]$. The associated **distortion loss** of a decision $y$ under
parameter $\theta$ is
$$\ell(\theta, y) \;=\; \Phi\bigl(\rho(\theta(P_\theta),\, y)\bigr),$$
and the **minimax risk** of estimating the functional is
$$\mathfrak{M}\bigl(\theta(\mathcal{P});\, \Phi\circ\rho\bigr)
   \;=\; \inf_{\widehat{\theta}}\ \sup_{\theta}\ \mathbb{E}_{P_\theta}
     \bigl[\Phi\bigl(\rho(\widehat{\theta},\, \theta(P_\theta))\bigr)\bigr],$$
the infimum ranging over all (randomized) estimators (Eq. (15.2)).

The standard reduction from estimation to testing (§15.1.2) replaces this by an
$M$-ary hypothesis test: with the index $J$ drawn uniformly from $\{1,\dots,M\}$, the data
$Z \sim P_{\theta^J}$, and the $0$–$1$ loss $\ell(j,k) = \mathbf{1}[j\neq k]$, the
**$M$-ary testing error**
$$\inf_{\psi}\ \mathbb{Q}\bigl[\psi(Z) \neq J\bigr]$$
is the Bayes risk under the uniform prior, with the marginal of $Z$ given by the **mixture**
$\overline{\mathbb{Q}} = \tfrac{1}{M}\sum_{j} P_{\theta^j}$ (Eq. (15.30)). A finite family
$\{\theta^j\}$ is **$2\delta$-separated** when its functional values are pairwise at
semimetric distance at least $2\delta$ (we adopt the milder $\ge 2\delta$ requirement rather
than $> 2\delta$, per Wainwright's footnote 2).

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.1–§15.1.2,
Eq. (15.2), (15.3); mixture distribution §15.3.1, Eq. (15.30).

**Proof formalization notes.** This is a laptop-only shared data model — definitions only,
no theorems. We build directly on Mathlib's decision-theoretic risk framework
(`ProbabilityTheory.minimaxRisk` / `bayesRisk` / `avgRisk`, in
`Mathlib/Probability/Decision/Risk/`):

* an **estimation problem** is a data-generating kernel `P : Kernel Θ 𝓧` (the family
  `{P_θ}` indexing Wainwright's class `𝒫`) together with a loss `ℓ : Θ → 𝓨 → ℝ≥0∞`;
* a **(randomized) estimator** is a Markov kernel `κ : Kernel 𝓧 𝓨`;
* `minimaxRisk ℓ P = ⨅_κ ⨆_θ ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)` — exactly Wainwright's
  `M(θ(𝒫); ℓ) = inf_θ̂ sup_P 𝔼_P[ℓ]` (Eq. (15.1)/(15.2)).

This file adds the Wainwright-specific wiring on top:

* `distortionLoss Φ g` — the loss `Φ(ρ(θ(P_θ), y))` (Eq. (15.2)), with the semimetric
  `ρ = edist` (Wainwright's `ρ` is a *semimetric*, footnote 1 = `PseudoEMetricSpace`);
* `minimaxRiskDist Φ g P` — the resulting minimax risk `M(θ(𝒫); Φ∘ρ)`;
* `zeroOneLoss` / `uniformPrior` / `multiwayTestingError` — the M-ary hypothesis test
  `inf_ψ ℚ[ψ(Z) ≠ J]` of §15.1.2 as a `bayesRisk` (0–1 loss, uniform prior);
* `mixture` — the mixture distribution `Q̄ = (1/M) Σⱼ P_{θʲ}` (Eq. (15.30));
* `IsSeparatedFamily g θ δ` — a `2δ`-separated finite family in the semimetric `ρ`.

**Bibliographic comments.** These objects are a synthesis of the classical
minimax decision-theory framework, with no single seminal origin. The decision-theoretic
formulation of minimax risk over a family of distributions traces to A. Wald, *Statistical
Decision Functions* (Wiley, 1950). The reduction of minimax estimation to $M$-ary
hypothesis testing over a separated family — the engine behind the Le Cam, Fano, and
Assouad lower-bound methods — is due to L. Le Cam (*Convergence of estimates under
dimensionality restrictions*, Ann. Statist. 1 (1973), 38–53; and *Asymptotic Methods in
Statistical Decision Theory*, Springer, 1986), with the multi-hypothesis / packing variants
developed by Le Cam, P. Assouad (*Deux remarques sur l'estimation*, C. R. Acad. Sci. Paris
296 (1983), 1021–1024), and the information-theoretic Fano bound (R. M. Fano, 1952; see
also I. A. Ibragimov and R. Z. Has'minskii, *Statistical Estimation: Asymptotic Theory*,
Springer, 1981). Chapter 15 of Wainwright collects this folklore into the unified
$\mathfrak{M}(\theta(\mathcal{P}); \Phi\circ\rho)$ formulation used here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

/-- The **distortion loss** `ℓ θ y = Φ(ρ(θ(P_θ), y))` of Wainwright's minimax-risk setup:
an increasing distortion `Φ : ℝ≥0∞ → ℝ≥0∞` of the semimetric `ρ = edist` between the
decision `y : Ω` and the functional value `g θ = θ(P_θ) : Ω` under parameter `θ`.

`Ω` carries the semimetric as a `PseudoEMetricSpace` (Wainwright's `ρ` is a *semimetric* —
a metric possibly with `ρ θ θ' = 0` for `θ ≠ θ'`, footnote 1 — i.e. a pseudo metric).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.1, Eq. (15.2). -/
noncomputable def distortionLoss [PseudoEMetricSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) : Θ → Ω → ℝ≥0∞ :=
  fun θ y => Φ (edist (g θ) y)

/-- Wainwright's **minimax risk** `M(θ(𝒫); Φ∘ρ) = inf_θ̂ sup_θ 𝔼_{P_θ}[Φ(ρ(θ̂, θ(P_θ)))]`,
as the Mathlib `minimaxRisk` of the `distortionLoss`. The model `P : Kernel Θ 𝓧` sends each
parameter `θ` (indexing the class `𝒫`) to its data law `P_θ`; the infimum ranges over all
(randomized) estimators `Kernel 𝓧 Ω`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.1, Eq. (15.2). -/
noncomputable def minimaxRiskDist [PseudoEMetricSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) : ℝ≥0∞ :=
  minimaxRisk (distortionLoss Φ g) P

/-- The **0–1 loss** `ℓ(j, k) = 𝟙[j ≠ k]` of an M-ary hypothesis test: zero when the
guessed index `k` equals the true index `j`, one otherwise.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2. -/
def zeroOneLoss (M : ℕ) : Fin M → Fin M → ℝ≥0∞ :=
  fun j k => if j = k then 0 else 1

/-- The **uniform prior** on the index set `Fin M` — the law of the random index `J`
drawn uniformly from `[M] = {1,…,M}` in an M-ary hypothesis test.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2. -/
noncomputable def uniformPrior (M : ℕ) [NeZero M] : Measure (Fin M) :=
  (PMF.uniformOfFintype (Fin M)).toMeasure

instance (M : ℕ) [NeZero M] : IsProbabilityMeasure (uniformPrior M) := by
  unfold uniformPrior; infer_instance

/-- The **M-ary testing error** `inf_ψ ℚ[ψ(Z) ≠ J]` of §15.1.2: the Bayes risk of the
M-ary hypothesis test with 0–1 loss and uniform prior, where `Q j = P_{θʲ}` is the data
law under hypothesis `j`. Equal to the infimum over (randomized) tests of the
misclassification probability, averaged over a uniformly random index `J`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2, Eq. (15.3). -/
noncomputable def multiwayTestingError {M : ℕ} [NeZero M]
    (Q : Kernel (Fin M) 𝓧) : ℝ≥0∞ :=
  bayesRisk (zeroOneLoss M) Q (uniformPrior M)

/-- The **mixture distribution** `Q̄ = (1/M) Σⱼ P_{θʲ}`: the marginal law of the
observation `Z` when the index `J` is drawn from the uniform prior and `Z ∼ Q J`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.1, Eq. (15.30). -/
noncomputable def mixture {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) : Measure 𝓧 :=
  Q ∘ₘ uniformPrior M

/-- A **`2δ`-separated family** in the semimetric `ρ = edist` on the functional values
(§15.1.2): a finite family of parameters `θfam : Fin M → Θ` whose functional values
`g (θfam j) = θ(P_{θʲ})` are pairwise at semimetric distance `≥ 2δ`. We enforce only the
milder `≥ 2δ` requirement (rather than `> 2δ`), as in Wainwright's footnote 2.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2. -/
def IsSeparatedFamily [PseudoEMetricSpace Ω] {M : ℕ}
    (g : Θ → Ω) (θfam : Fin M → Θ) (δ : ℝ≥0∞) : Prop :=
  ∀ j k, j ≠ k → 2 * δ ≤ edist (g (θfam j)) (g (θfam k))

end StatLean.Minimaxity
