module
public import StatLean.AsymptoticStatistics.Core.TangentAbstract
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.Core.Pathwise

@[expose] public section

/-!
# Vector-valued pathwise differentiability

This file defines pathwise differentiability for vector-valued statistical
functionals `ψ : Measure Ω → EuclideanSpace ℝ (Fin k)`, following van der Vaart,
*Asymptotic Statistics*, §25.3.

The headline declaration is `PathwiseDifferentiableAt_vec`.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.PathwiseVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (T : Submodule ℝ ↥(L2ZeroMean P))
variable {k : ℕ}

/-- A vector-valued statistical functional `ψ : Measure Ω → EuclideanSpace ℝ (Fin k)`
is *pathwise differentiable* at `P` relative to the tangent space `T` iff there
exists a continuous-linear derivative `dψ : T →L[ℝ] EuclideanSpace ℝ (Fin k)`
such that for every `QMDPath` at `P` whose score lies in `T`, the difference
quotient `(ψ(γ.curve t) - ψ P) / t` converges to `dψ ⟨γ.score, _⟩` as `t → 0`.

vdV §25.3: the derivative is a continuous linear map from
the tangent space directly into the vector codomain. -/
structure PathwiseDifferentiableAt_vec
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin k)) where
  derivative : T →L[ℝ] EuclideanSpace ℝ (Fin k)
  derivative_spec :
    ∀ (γ : QMDPath.QMDPath P),
      ∀ (h_in_T : (γ.score : ↥(L2ZeroMean P)) ∈ T),
        Filter.Tendsto (fun t : ℝ => t⁻¹ • (ψ (γ.curve t) - ψ P))
          (nhdsWithin 0 {0}ᶜ) (nhds (derivative ⟨γ.score, h_in_T⟩))

end AsymptoticStatistics.Core.PathwiseVec
