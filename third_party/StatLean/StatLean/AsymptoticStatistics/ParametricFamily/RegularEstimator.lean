module
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-!
# Regular estimator sequence

An estimator sequence $T_n$ for the parameter $\psi(\theta)$ is **regular at
$\theta_0$** with limit distribution $L_\theta$ if there is a single probability
measure $L_\theta$ on $\mathbb{R}^d$ such that, for every local perturbation
direction $h \in \mathbb{R}^k$,
$$\sqrt n\,\bigl(T_n - \psi(\theta_0 + h/\sqrt n)\bigr) \;\rightsquigarrow\; L_\theta
\qquad\text{under } P^n_{\theta_0 + h/\sqrt n}.$$
The defining content of *regularity* is that the limiting law $L_\theta$ is the
**same** for every $h$ — the estimator's local behaviour does not depend on the
direction from which the parameter is approached. This is the hypothesis class
for the Hájek–Le Cam Convolution Theorem (vdV §8.5, Theorem 8.8), which states
that under local asymptotic normality $L_\theta$ must be a convolution of the
optimal Gaussian limit with an arbitrary independent factor.

This file contributes only the definition `RegularEstimatorSequence`; the
Convolution Theorem itself and its assembly glue live in
`Ch8/HajekLeCamConvolution.lean`. No additional hypotheses or constant changes
relative to the book: the structure encodes exactly the regularity clause of
vdV §8.5.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 8 (Efficiency of Estimators), §8.5 (Convolution Theorem), the
definition of a regular estimator sequence stated immediately before
Theorem 8.8.

**Proof formalization notes.** This file states a definition, not a theorem, so
there is no proof obligation here. Encoding details:
* `productMeasure M μ θ n` is the $n$-fold product measure of `μ.withDensity
  M.density θ` — i.e. $P^n_\theta$ (see `Ch7/AsymptoticRepresentation.lean`).
* Weak convergence is the project's `WeakConverges` test-function form
  (`ForMathlib/Contiguity.lean`).
* The `limitDist` field is vdV's $L_\theta$; the `tendsto` field is vdV's
  defining convergence clause; the `isProb` field is the "probability measure"
  qualifier vdV's text states explicitly.
* Constitutive check (vdV §8.5): removing either `limitDist` or `tendsto` would
  leave an object that is not a `RegularEstimatorSequence`.

**Bibliographic comments.** The regular-estimator concept and the convolution
theorem it feeds originate with J. Hájek, "A characterization of limiting
distributions of regular estimates", *Zeitschrift für Wahrscheinlichkeitstheorie
und Verwandte Gebiete* **14** (1970), 323–330, with an independent contemporary
treatment by T. Inagaki, "On the limiting distribution of a sequence of
estimators with uniformity property", *Annals of the Institute of Statistical
Mathematics* **22** (1970), 1–13. The modern local-asymptotic-minimax framing in
which this definition sits is due to L. Le Cam (e.g. *Asymptotic Methods in
Statistical Decision Theory*, Springer, 1986); vdV §8.5 follows that synthesis.
-/

open MeasureTheory

namespace AsymptoticStatistics
namespace ParametricFamily

variable {k d : ℕ}
variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **Regular estimator sequence at `θ₀`** (vdV §8.5).

`T n : (Fin n → 𝓧) → ℝᵈ` is a regular estimator sequence for `ψ(θ)` at
`θ₀` iff there exists a probability measure `L_θ` on `ℝᵈ` (the **limit
distribution**) such that for every `h ∈ ℝᵏ`,
$$\sqrt n\, (T_n - \psi(\theta_0 + h/\sqrt n)) \xrightarrow{P^n_{\theta_0 + h/\sqrt n}} L_\theta.$$

Crucially, `L_θ` is **independent of `h`** — that is the *regularity* part.

Encoding notes:
* `productMeasure M μ θ n` is the `n`-fold product measure of `μ.withDensity
  M.density θ` (see `Ch7/AsymptoticRepresentation.lean`).
* Weak convergence is via the project's `WeakConverges` test-function form
  (`ForMathlib/Contiguity.lean`).
* The `limitDist` field is the same as vdV's `L_θ`; `tendsto` IS vdV's
  defining clause.

vdV §8.5: removing either `limitDist` or `tendsto` would not be a
`RegularEstimatorSequence`. The `isProb` field is the "probability measure"
qualifier vdV's text demands explicitly. -/
structure RegularEstimatorSequence
    (M : ParametricFamily 𝓧 (AsymptoticRepresentation.Θ k)) (μ : Measure 𝓧)
    (θ₀ : AsymptoticRepresentation.Θ k)
    (ψ : AsymptoticRepresentation.Θ k → AsymptoticRepresentation.𝓨 d)
    (T : ∀ n, (Fin n → 𝓧) → AsymptoticRepresentation.𝓨 d) : Type where
  /-- vdV §8.5: the common limit distribution `L_θ` (independent of `h`). -/
  limitDist : Measure (AsymptoticRepresentation.𝓨 d)
  /-- vdV §8.5: `L_θ` is a probability measure. -/
  isProb : IsProbabilityMeasure limitDist
  /-- vdV §8.5: for every `h ∈ ℝᵏ`, the rescaled
  recentred statistic `√n (T_n − ψ(θ₀ + h/√n))` weakly converges to
  `limitDist` under `P^n_{θ₀ + h/√n}`. -/
  tendsto : ∀ h : AsymptoticRepresentation.Θ k,
    WeakConverges
      (fun n : ℕ =>
        (AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).map
          (fun x => (Real.sqrt n) •
            (T n x - ψ (θ₀ + (Real.sqrt n)⁻¹ • h))))
      limitDist

/-- The `limitDist` of a `RegularEstimatorSequence` is a probability measure. -/
instance RegularEstimatorSequence.isProbabilityMeasure_limitDist
    {M : ParametricFamily 𝓧 (AsymptoticRepresentation.Θ k)} {μ : Measure 𝓧}
    {θ₀ : AsymptoticRepresentation.Θ k}
    {ψ : AsymptoticRepresentation.Θ k → AsymptoticRepresentation.𝓨 d}
    {T : ∀ n, (Fin n → 𝓧) → AsymptoticRepresentation.𝓨 d}
    (hReg : RegularEstimatorSequence M μ θ₀ ψ T) :
    IsProbabilityMeasure hReg.limitDist :=
  hReg.isProb

end ParametricFamily
end AsymptoticStatistics
