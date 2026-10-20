module
public import StatLean.Bayesian.Dominated.Defs

@[expose] public section

/-!
# Empirical Bayes — core data model (mixture density, two-groups model, local FDR, MLE/NPMLE)

Data model for empirical Bayes and large-scale inference:

* `mixtureDensity p G` — the **marginal (mixture) density** `f_G(x) = ∫ p(θ,x) G(dθ)` of the data
  under a mixing distribution `G` on the parameter (a textbook alias of the dominated-model
  `predictiveDensity`); this is the object empirical Bayes estimates from data;
* `twoGroupsMixture π₀ f₀ f₁` — Efron's **two-groups marginal** `f = π₀ f₀ + (1−π₀) f₁`;
* `localFDR π₀ f₀ f₁` — the **local false discovery rate** `fdr(x) = π₀ f₀(x) / f(x)`, i.e. the
  posterior probability of the null given the observation;
* `IsMarginalMLE` / `IsNPMLE` — optimality predicates for the **parametric** (hyperparameter) and
  **nonparametric** (mixing distribution) maximizers of the marginal likelihood.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §10.4 (the empirical Bayes alternative), p. 478; §10.4.1
(nonparametric EB), p. 479; §10.4.2 (parametric EB), p. 481. The two-groups model and local FDR
are not in Robert; see B. Efron, *Large-Scale Inference: Empirical Bayes Methods for Estimation,
Testing, and Prediction*, Cambridge University Press, 2010, §2.1 and §5.

**Proof formalization notes.** Laptop-only data model — definitions only. `mixtureDensity` is
definitionally `predictiveDensity`; it is renamed to match the empirical-Bayes and large-scale-
inference literature (there the mixing distribution `G` is the object of interest, not a Bayesian
prior). All densities are `ℝ≥0∞`-valued; `localFDR` uses extended-nonnegative division, taking the
junk value `0` where the marginal `f(x)` degenerates. `IsMarginalMLE`/`IsNPMLE` are stated as
optimality *predicates* (the argument maximizes the product marginal likelihood over the relevant
class) rather than as `argmax` functions, so existence and uniqueness are not presupposed.

**Bibliographic comments.** Empirical Bayes is due to H. Robbins, "An empirical Bayes approach to
statistics," *Proc. Third Berkeley Symp. Math. Statist. Probab.* 1 (1956), 157–163. The
nonparametric maximum-likelihood estimate of a mixing distribution and its finite-support geometry
are due to B. G. Lindsay, "The geometry of mixture likelihoods: a general theory," *Ann. Statist.*
11 (1983), 86–94, building on J. Kiefer and J. Wolfowitz (*Ann. Math. Statist.* 27 (1956),
887–906). The two-groups model, local false discovery rate, and the empirical-Bayes reading of
large-scale testing are systematized in Efron's *Large-Scale Inference* (2010), extending the
false-discovery-rate framework of Y. Benjamini and Y. Hochberg (*J. Roy. Statist. Soc. Ser. B* 57
(1995), 289–300).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace StatLean.Bayesian

variable {Λ Θ 𝓧 : Type*} [MeasurableSpace Λ] [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- The **marginal (mixture) density** `f_G(x) = ∫ p(θ,x) G(dθ)` of the data under mixing
distribution `G` (Efron §2; a textbook alias of `predictiveDensity`). -/
noncomputable def mixtureDensity (p : Θ → 𝓧 → ℝ≥0∞) (G : Measure Θ) : 𝓧 → ℝ≥0∞ :=
  predictiveDensity p G

/-- Efron's **two-groups marginal** `f(x) = π₀ f₀(x) + (1 − π₀) f₁(x)` (Efron §2.1). -/
noncomputable def twoGroupsMixture (π₀ : ℝ≥0∞) (f₀ f₁ : 𝓧 → ℝ≥0∞) : 𝓧 → ℝ≥0∞ :=
  fun x => π₀ * f₀ x + (1 - π₀) * f₁ x

/-- The **local false discovery rate** `fdr(x) = π₀ f₀(x) / f(x)`, the posterior probability of the
null given the observation `x` (Efron §5.1). Extended-nonnegative division: `0` where the marginal
degenerates. -/
noncomputable def localFDR (π₀ : ℝ≥0∞) (f₀ f₁ : 𝓧 → ℝ≥0∞) : 𝓧 → ℝ≥0∞ :=
  fun x => (π₀ * f₀ x) / twoGroupsMixture π₀ f₀ f₁ x

/-- **Marginal-MLE optimality**: `λ̂` maximizes the product marginal likelihood
`∏ᵢ f_{Π_λ}(xᵢ)` over the hyperparameter family `priorFamily` (Robert §10.4.2). -/
def IsMarginalMLE {n : ℕ} (priorFamily : Λ → Measure Θ) (p : Θ → 𝓧 → ℝ≥0∞)
    (x : Fin n → 𝓧) (lamHat : Λ) : Prop :=
  ∀ lam, ∏ i, mixtureDensity p (priorFamily lam) (x i)
    ≤ ∏ i, mixtureDensity p (priorFamily lamHat) (x i)

/-- **NPMLE optimality**: the probability measure `Ĝ` maximizes the product marginal likelihood
`∏ᵢ f_G(xᵢ)` over *all* mixing probability measures on `Θ` (Robert §10.4.1; Lindsay 1983). -/
def IsNPMLE {n : ℕ} (p : Θ → 𝓧 → ℝ≥0∞) (x : Fin n → 𝓧) (Ghat : Measure Θ) : Prop :=
  IsProbabilityMeasure Ghat ∧
    ∀ G : Measure Θ, IsProbabilityMeasure G →
      ∏ i, mixtureDensity p G (x i) ≤ ∏ i, mixtureDensity p Ghat (x i)

end StatLean.Bayesian
