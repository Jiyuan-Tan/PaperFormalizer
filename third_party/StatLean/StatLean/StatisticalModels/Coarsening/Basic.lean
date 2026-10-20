module
public import StatLean.StatisticalModels.Coarsening.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

@[expose] public section

/-!
# Coarsening basics — Bool integration bricks, MCAR ⇒ MAR, propensity range

Small reusable facts for the missing-data slice: two-point integration over `Bool` (the
workhorse for every propensity computation), the taxonomy inclusion MCAR ⇒ MAR, the range of
the propensity, and probability preservation of the full/observed-data constructions.

**Reference.** D. B. Rubin, *Biometrika* **63** (1976), §2 (`Rubin76`): MCAR is the special
case of MAR with a data-free mechanism.

**Proof formalization notes.** `Bool` integrals are finite sums (`lintegral_fintype` /
`integral_fintype` with `Bool` enumeration); the MCAR ⇒ MAR proof exhibits the constant
kernel as `(Kernel.const 𝓧 ν).comap Prod.fst` (a `Kernel.ext` computation). Probability of
`fullLaw`/`observedLaw` is `compProd` + `map` preservation (the coarsening map is measurable
— product projections and an `if` on the Boolean coordinate).

**Bibliographic comments.** See `Coarsening.Defs`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.StatisticalModels.Coarsening

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- Two-point lower integral over `Bool`. -/
theorem lintegral_bool (ν : Measure Bool) (f : Bool → ℝ≥0∞) :
    ∫⁻ b, f b ∂ν = f true * ν {true} + f false * ν {false} := by
  rw [lintegral_fintype, Fintype.sum_bool]

/-- Two-point Bochner integral over `Bool`. -/
theorem integral_bool (ν : Measure Bool) [IsFiniteMeasure ν] (f : Bool → ℝ) :
    ∫ b, f b ∂ν = (ν {true}).toReal * f true + (ν {false}).toReal * f false := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
  simp [measureReal_def, smul_eq_mul]

/-- The coarsening map is measurable. -/
theorem measurable_missingObserve :
    Measurable (missingObserve (𝓧 := 𝓧)) := by
  refine measurable_fst.prodMk (measurable_snd.snd.prodMk ?_)
  exact Measurable.ite (measurable_snd.snd (measurableSet_singleton true))
    measurable_snd.fst measurable_const

/-- **MCAR ⇒ MAR** (Rubin76 §2): a data-free mechanism trivially factors through the
covariate. -/
-- LEAN-ONLY: MCAR antecedent; no scope change
theorem IsMCAR.isMAR {ρ : Kernel (𝓧 × ℝ) Bool} (h : IsMCAR ρ) : IsMAR ρ := by
  obtain ⟨ν, rfl⟩ := h
  exact ⟨Kernel.const 𝓧 ν, Kernel.ext fun a => by simp⟩

/-- The propensity is nonnegative. -/
theorem propensity_nonneg (ρ' : Kernel 𝓧 Bool) (x : 𝓧) : 0 ≤ propensity ρ' x :=
  ENNReal.toReal_nonneg

/-- The propensity of a Markov mechanism is at most one. -/
theorem propensity_le_one (ρ' : Kernel 𝓧 Bool) [IsMarkovKernel ρ'] (x : 𝓧) :
    propensity ρ' x ≤ 1 := by
  simpa [propensity] using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ρ' x))

/-- The full-data reassociation `((x, y), r) ↦ (x, y, r)` is measurable. -/
private theorem measurable_fullAssoc :
    Measurable fun p : (𝓧 × ℝ) × Bool => (p.1.1, p.1.2, p.2) :=
  measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)

instance (Q : Measure (𝓧 × ℝ)) (ρ : Kernel (𝓧 × ℝ) Bool)
    [IsProbabilityMeasure Q] [IsMarkovKernel ρ] : IsProbabilityMeasure (fullLaw Q ρ) := by
  exact Measure.isProbabilityMeasure_map measurable_fullAssoc.aemeasurable

instance (Q : Measure (𝓧 × ℝ)) (ρ : Kernel (𝓧 × ℝ) Bool)
    [IsProbabilityMeasure Q] [IsMarkovKernel ρ] : IsProbabilityMeasure (observedLaw Q ρ) := by
  exact Measure.isProbabilityMeasure_map measurable_missingObserve.aemeasurable

end StatLean.StatisticalModels.Coarsening
