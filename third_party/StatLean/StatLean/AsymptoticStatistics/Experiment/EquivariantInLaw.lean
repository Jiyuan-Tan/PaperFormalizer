module
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Kernel.Composition.CompNotation

@[expose] public section

/-!
# Equivariant-in-law randomized estimators in the Gaussian shift experiment

In the Gaussian shift experiment one observes $X \sim N(h, S)$ with unknown shift
parameter $h \in \mathbb{R}^k$ and known covariance $S$, and wishes to estimate the
linear functional $A h \in \mathbb{R}^d$. A (possibly randomized) estimator $T$ is
called **equivariant-in-law** if the law of the centred error $T(X) - A h$ does not
depend on the parameter $h$: there exists a single probability measure $L$ on
$\mathbb{R}^d$ — the **null distribution** of $T$ — such that, for every
$h \in \mathbb{R}^k$, the distribution of $T(X) - A h$ under $X \sim N(h, S)$ equals
$L$. This invariance is the structural hypothesis behind the convolution theorem,
which forces $L$ to be a convolution of the optimal Gaussian limit with an
additional independent noise component.

This file states only the defining notion and its null-distribution accessor; the
convolution conclusion itself is not formalized here.

**Formalization notes.** We encode the randomized estimator $T$ as a Markov kernel
`Kernel ℝᵏ ℝᵈ`. Given $X \sim N(h, S)$ (modelled by `multivariateGaussian h S`) and
randomization kernel $T$, the law of $T(X)$ at parameter $h$ is the kernel
composition `T ∘ₘ (multivariateGaussian h S)`; the law of $T(X) - A h$ is this
pushed forward by the deterministic translation $y \mapsto y - A h$. Equivariance
asserts that this translated law is one common probability measure $L$ for every
$h$, and $L$ is the **null distribution** of $T$. The covariance matrix that vdV
writes as $\Sigma$ is named `S` in Lean (`Σ` is reserved). The file provides the
structure `IsEquivariantInLaw`, the Skolemized accessor
`IsEquivariantInLaw.nullDist`, the instance establishing that the null distribution
is a probability measure, and the characterising property
`IsEquivariantInLaw.map_sub_eq_nullDist`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 8 (Efficiency of Estimators), §8.4 (Estimating Normal Means),
Proposition 8.4.

**Bibliographic comments.** The notion of an equivariant-in-law (regular) estimator
and the resulting convolution structure originate with the convolution theorem of
J. Hájek, "A characterization of limiting distributions of regular estimates",
*Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte Gebiete* **14** (1970),
323–330, with parallel contributions by L. Le Cam and by N. Inagaki, "On the
limiting distribution of a sequence of estimators with uniformity property",
*Annals of the Institute of Statistical Mathematics* **22** (1970), 1–13. The
finite-dimensional Gaussian-shift formulation used here — a randomized estimator
whose centred error has a parameter-free law — is the standard textbook
distillation of that line of work (vdV §8.4) and, as a stand-alone *definition*,
carries no single seminal origin of its own; it is the device through which the
Hájek–Le Cam convolution theorem is stated.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AsymptoticStatistics
namespace EquivariantInLaw

variable {k d : ℕ}

/-- **Equivariance-in-law for a randomized estimator** (vdV §8.4).

`T` is a randomized estimator of `A·h` based on observing `X ∼ N(h, S)`,
encoded as a Markov kernel `Kernel ℝᵏ ℝᵈ`. `T` is **equivariant-in-law**
iff for every `h`, the distribution of `T(X) − A·h` (under `X ∼ N(h, S)`)
equals one common probability measure `L`. `L` is called the **null
distribution** of `T`. (`S` here is the covariance matrix vdV writes as
`Σ`; `Σ` is reserved in Lean.) -/
structure IsEquivariantInLaw
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)))
    (A : Matrix (Fin d) (Fin k) ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) : Prop where
  /-- vdV §8.4: there exists a probability measure `L`
  on `ℝᵈ` such that for every `h ∈ ℝᵏ`, the law of `T(X) − A·h` under
  `X ∼ N(h, S)` equals `L`. Equivalently, the pushforward of `T ∘ₘ
  multivariateGaussian h S` by `y ↦ y − A·h` is `L` for all `h`. -/
  invariant_law :
    ∃ L : Measure (EuclideanSpace ℝ (Fin d)),
      IsProbabilityMeasure L ∧
      ∀ h : EuclideanSpace ℝ (Fin k),
        (T ∘ₘ (multivariateGaussian h S)).map
            (fun y => y - (WithLp.equiv 2 (Fin d → ℝ)).symm
              (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h)))
          = L

/-- The **null distribution** of an equivariant-in-law estimator
(vdV §8.4, "invariant law `L`"). Skolemized from
`IsEquivariantInLaw.invariant_law`; characterised by
`IsEquivariantInLaw.map_sub_eq_nullDist`. -/
noncomputable def IsEquivariantInLaw.nullDist
    {T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))}
    {A : Matrix (Fin d) (Fin k) ℝ}
    {S : Matrix (Fin k) (Fin k) ℝ}
    (h : IsEquivariantInLaw T A S) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  h.invariant_law.choose

/-- The null distribution is a probability measure. -/
instance IsEquivariantInLaw.isProbabilityMeasure_nullDist
    {T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))}
    {A : Matrix (Fin d) (Fin k) ℝ}
    {S : Matrix (Fin k) (Fin k) ℝ}
    (h : IsEquivariantInLaw T A S) :
    IsProbabilityMeasure h.nullDist :=
  h.invariant_law.choose_spec.1

/-- Characterising property of the null distribution: for every `h`, the
pushforward of the kernel composition by the translation `y ↦ y − A·h`
equals `nullDist`. -/
theorem IsEquivariantInLaw.map_sub_eq_nullDist
    {T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))}
    {A : Matrix (Fin d) (Fin k) ℝ}
    {S : Matrix (Fin k) (Fin k) ℝ}
    (hT : IsEquivariantInLaw T A S) (h : EuclideanSpace ℝ (Fin k)) :
    (T ∘ₘ (multivariateGaussian h S)).map
        (fun y => y - (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h)))
      = hT.nullDist :=
  hT.invariant_law.choose_spec.2 h

end EquivariantInLaw
end AsymptoticStatistics
