module
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Parametric family of densities

A *parametric statistical model* is a family of probability densities
$\{p_\theta : \theta \in \Theta\}$ on a sample space $\mathcal X$, each taken with
respect to a common dominating $\sigma$-finite measure $\mu$. This file fixes the
basic objects of such a model and the analytic structure used throughout the
local-asymptotic-normality development.

We package a parametric family as the data of a measurable, non-negative map
$\theta \mapsto p_\theta$, where $p_\theta : \mathcal X \to \mathbb R$ is the density
of the $\theta$-th member with respect to $\mu$. A family is a *probability-density
family* (relative to $\mu$) when, for every $\theta$, the density is $\mu$-integrable
and normalised, $\int_{\mathcal X} p_\theta \, d\mu = 1$.

The central analytic object is the **square-root density**
$$ s_\theta(x) \;=\; \sqrt{p_\theta(x)}, $$
which is measurable and non-negative, satisfies $s_\theta^2 = p_\theta$ pointwise, and
— precisely because $\int p_\theta \, d\mu = 1 < \infty$ — belongs to $L^2(\mu)$ with
$\lVert s_\theta \rVert_{L^2(\mu)}^2 = 1$. Representing densities through their square
roots is what turns the (nonlinear) statistical model into a curve in the Hilbert space
$L^2(\mu)$, and is the foundation for differentiability in quadratic mean and the
Hellinger geometry of vdV Chapter 7.

This file contains no theorem with a numbered book counterpart; it sets up the
definitions (`ParametricFamily`, `IsPDFOf`, `sqrtDensity`) and their elementary
measurability / positivity / $L^2$ lemmas.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 7 (Local Asymptotic Normality), §7.2 (Expanding the Likelihood) —
the parametric-model setup and the square-root-density / $L^2(\mu)$ representation
underlying the differentiability-in-quadratic-mean definition.

**Proof formalization notes.**
* We bundle the joint measurability and non-negativity of $\theta \mapsto p_\theta$
  into the `ParametricFamily` structure so downstream lemmas reuse them without
  reproving.
* `IsPDFOf` collects the two universal regularity conditions that otherwise recur as
  separate hypotheses in LAN-style statements — per-$\theta$ normalisation
  ($\int p_\theta \, d\mu = 1$) and per-$\theta$ $\mu$-integrability.
* We deliberately do **not** bundle $\mu$-a.e. strict positivity of $p_\theta$ here.
  vdV's Theorem 7.10 (and the LAN expansion it rests on) needs only the weaker
  condition that the perturbed densities $p_{\theta_0 + t u}$ are strictly positive on
  the support of $p_{\theta_0}$, i.e. $\nu$-a.e. with $\nu = \mu.\mathrm{withDensity}\,
  p_{\theta_0}$. Consumers requiring positivity should take it as a separate
  hypothesis in $\nu$-form rather than baking it into the structure.
* The membership $s_\theta \in L^2(\mu)$ is obtained from $\mu$-integrability of
  $p_\theta$ via `memLp_two_iff_integrable_sq`, using $s_\theta^2 = p_\theta$.

**Bibliographic comments.** The square-root / Hilbert-space representation of a
parametric model — and the resulting Hellinger and $L^2$ geometry — is classical
statistical folklore with no single seminal origin. Its modern asymptotic use
traces through L. Le Cam's work on differentiability in quadratic mean and contiguity
(L. Le Cam, *Asymptotic Methods in Statistical Decision Theory*, Springer, 1986) and
the earlier C. R. Rao / J. Hájek tradition on regular parametric families; the
synthesis followed here is van der Vaart (1998), Chapter 7. No original
research paper is attributed for these definitional objects.
-/

open MeasureTheory

namespace AsymptoticStatistics

/-- A parametric family of (μ-)densities indexed by a parameter `θ : Θ`.

We package the joint measurability/non-negativity assumptions into the structure so that
downstream lemmas can use them without reproving. -/
structure ParametricFamily
    (𝓧 : Type*) [MeasurableSpace 𝓧] (Θ : Type*) where
  /-- Density `p_θ(x)`. -/
  density : Θ → 𝓧 → ℝ
  density_meas : ∀ θ, Measurable (density θ)
  density_nonneg : ∀ θ x, 0 ≤ density θ x

/-- **PDF conditions**: the family `M` is a probability-density family with respect to
the dominating measure `μ`. Bundles the two universal regularity conditions that
typically appear as separate hypotheses in LAN-style theorems — normalisation and
integrability, each for every parameter `θ`.

We deliberately do **not** bundle ae-strict-positivity of `p_θ` here: vdV's
Theorem 7.10 (and the LAN expansion it rests on) only needs the weaker condition
that the perturbation densities `p_{θ₀ + t·u}` are strictly positive on the support
of `p_{θ₀}` (i.e. ν-a.e. where ν = μ.withDensity p_{θ₀}). Consumers requiring that
condition should take it as a separate hypothesis in ν-form, not bake it in here. -/
structure IsPDFOf
    {𝓧 : Type*} [MeasurableSpace 𝓧] {Θ : Type*}
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) : Prop where
  /-- Density integrates to 1 (normalisation). -/
  density_integral_eq_one : ∀ θ, ∫ x, M.density θ x ∂μ = 1
  /-- Density is μ-integrable. -/
  density_integrable : ∀ θ, Integrable (M.density θ) μ

namespace ParametricFamily

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*}

/-! ## Square-root density -/

/-- The square root density `√p_θ`. -/
noncomputable def sqrtDensity (M : ParametricFamily 𝓧 Θ) (θ : Θ) (x : 𝓧) : ℝ :=
  Real.sqrt (M.density θ x)

lemma sqrtDensity_meas (M : ParametricFamily 𝓧 Θ) (θ : Θ) :
    Measurable (M.sqrtDensity θ) :=
  (M.density_meas θ).sqrt

lemma sqrtDensity_nonneg (M : ParametricFamily 𝓧 Θ) (θ : Θ) (x : 𝓧) :
    0 ≤ M.sqrtDensity θ x :=
  Real.sqrt_nonneg _

lemma sqrtDensity_sq (M : ParametricFamily 𝓧 Θ) (θ : Θ) (x : 𝓧) :
    M.sqrtDensity θ x ^ 2 = M.density θ x := by
  unfold sqrtDensity
  exact Real.sq_sqrt (M.density_nonneg θ x)

/-- If a density `p_θ` is integrable, then its square root belongs to `L²(μ)`. -/
lemma sqrtDensity_memLp_two
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ : Θ)
    (hint : Integrable (M.density θ) μ) :
    MemLp (M.sqrtDensity θ) 2 μ := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq
      ((M.sqrtDensity_meas θ).aestronglyMeasurable)).2 ?_
  simpa [M.sqrtDensity_sq] using hint

end ParametricFamily
end AsymptoticStatistics
