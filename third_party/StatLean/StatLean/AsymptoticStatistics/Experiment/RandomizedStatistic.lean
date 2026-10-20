module
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import StatLean.AsymptoticStatistics.Experiment.GaussianShift

@[expose] public section

/-!
# Randomized statistics as Markov kernels

A randomized statistic in an experiment indexed by `h ∈ Θ` is, in van der Vaart's
original presentation, a measurable function `T(X, U)` with auxiliary uniform `U`. The
kernel-theoretic equivalent (taken here as primary) is a Markov kernel `κ : Kernel Θ 𝓨`.
Given a law-of-observation map `ν : Θ → Measure Θ` (e.g. the Gaussian shift family),
the induced law of the randomized statistic at parameter `h` is `(ν h).bind κ : Measure 𝓨`.

vdV §7. Headline declarations: `law` and `preCompose`.
-/

open MeasureTheory ProbabilityTheory

namespace AsymptoticStatistics
namespace RandomizedStatistic

variable {k d : ℕ}

/-- Law of a randomized statistic `κ` at parameter `h`, under an observation law
`ν : Θ → Measure Θ`. Produces a probability measure on the statistic's target space `𝓨`. -/
noncomputable def law
    (ν : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k)))
    (κ : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)))
    (h : EuclideanSpace ℝ (Fin k)) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (ν h).bind κ

instance law_isProbabilityMeasure
    (ν : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k)))
    (κ : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel κ]
    (h : EuclideanSpace ℝ (Fin k)) [IsProbabilityMeasure (ν h)] :
    IsProbabilityMeasure (law ν κ h) := by
  unfold law
  infer_instance

/-- **Compose a deterministic map with a kernel.** Used in Step 7 of Theorem 7.10 to
write `κ ∘ J` (apply `J` to the Gaussian shift before consulting the kernel) as a new
kernel on `Θ`. Wrapper around `Kernel.comap`/`Kernel.deterministic.comp`. -/
noncomputable def preCompose
    (f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) (_hf : Measurable f)
    (κ : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))) :
    Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)) :=
  κ.comap f _hf

end RandomizedStatistic
end AsymptoticStatistics
