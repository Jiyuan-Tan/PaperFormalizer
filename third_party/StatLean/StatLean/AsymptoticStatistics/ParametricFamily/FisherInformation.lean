module
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# Fisher information (bilinear form)

For a parametric family $\{P_\theta\}$ with score function $\dot\ell_\theta : \mathcal X \to \Theta$,
the **Fisher information** at $\theta$ is the symmetric bilinear form on the parameter space
$$ I_\theta(u, v) \;=\; P_\theta\bigl(\langle u, \dot\ell_\theta\rangle\,\langle v, \dot\ell_\theta\rangle\bigr)
   \;=\; \int \langle u, \dot\ell_\theta(x)\rangle\,\langle v, \dot\ell_\theta(x)\rangle \, p_\theta(x)\,d\mu(x). $$
In a finite-dimensional basis this is the matrix $I_\theta = P_\theta\,\dot\ell_\theta\,\dot\ell_\theta^{\mathsf T}$,
i.e. the expected outer product of the score under $P_\theta$.

This file fixes only the **bilinear-form definition**. Here the score $\ell$ is taken as an explicit
argument $\ell : \mathcal X \to \Theta$ (any candidate score), and the family density $p_\theta$ enters
through `M.density θ` integrated against the dominating measure $\mu$; no positive-definiteness or
regularity (square-integrability of the score) is asserted at this level.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical and
Probabilistic Mathematics, Cambridge University Press, 1998. Chapter 7 (Local Asymptotic Normality),
§7.2, definition of the Fisher information matrix $I_\theta = P_\theta\,\dot\ell_\theta\,\dot\ell_\theta^{\mathsf T}$
(score function $\dot\ell_\theta$ introduced in §5.5).

**Proof formalization notes.** This file is a *definition*, not a theorem: `fisherInformation` packages
the bilinear form $(u, v) \mapsto P_\theta(\langle u, \ell\rangle\,\langle v, \ell\rangle)$ as a function
`Θ → Θ → ℝ`. The integral is over the dominating measure $\mu$ weighted by `M.density θ`, matching
$P_\theta$. In a finite-dimensional basis this reproduces the textbook matrix $P_\theta\,\ell_\theta\,\ell_\theta^{\mathsf T}$.

**Bibliographic comments.** The Fisher information originates with R. A. Fisher, "On the mathematical
foundations of theoretical statistics," *Philosophical Transactions of the Royal Society of London,
Series A*, vol. 222, pp. 309–368, 1922, where the "intrinsic accuracy" / amount of information of a
statistic is introduced (§§3–11), and is developed further in R. A. Fisher, "Theory of statistical
estimation," *Proceedings of the Cambridge Philosophical Society*, vol. 22, pp. 700–725, 1925. The
modern multivariate form as the expected outer product of the score, $I_\theta = E_\theta[\dot\ell_\theta\dot\ell_\theta^{\mathsf T}]$,
formalized here is standard (van der Vaart §7.2).
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]

/-- Fisher information as a bilinear form on the parameter space.

`fisherInformation M μ θ ℓ` sends `(u, v) ↦ ∫ ⟨u, ℓ x⟩ ⟨v, ℓ x⟩ dμ(x) · p_θ(x)`,
or equivalently `P_θ (⟨u, ℓ⟩ ⟨v, ℓ⟩)`.

In a finite-dimensional basis this is exactly the matrix `P_θ ℓ_θ ℓ_θᵀ`. -/
noncomputable def fisherInformation
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ : Θ) (ℓ : 𝓧 → Θ) :
    Θ → Θ → ℝ :=
  fun u v => ∫ x, (⟪u, ℓ x⟫ * ⟪v, ℓ x⟫) * M.density θ x ∂μ

end AsymptoticStatistics
