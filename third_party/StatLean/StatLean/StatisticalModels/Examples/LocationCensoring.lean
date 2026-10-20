module
public import StatLean.StatisticalModels.Identifiability.Transfer
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-!
# Worked instance: a location family under right censoring

The second Core regression test, seeding the Survival slice: a location family on `ℝ` (a
nonparametric-in-the-carrier model — the base law `μ₀` is arbitrary), the **right-censoring
observation kernel** carrying a full event time `t` to the censored readout
`(t ∧ C, 1{t ≤ C})` with `C ∼ ν` independent, and the destroy-direction identifiability
transfer instantiated: identification from censored data implies identification from complete
data.

**Reference.** Location families: TPE2 §1.1, §3.1 (verify §). The random-censorship readout
`(T ∧ C, 1{T ≤ C})`: E. L. Kaplan and P. Meier, "Nonparametric estimation from incomplete
observations," *J. Amer. Statist. Assoc.* **53** (1958), 457–481, §2 (verify §).

**Proof formalization notes.** The censoring kernel is built compositionally —
`(deterministic id) ×ₖ (const ν)` mapped through `(t, c) ↦ (t ∧ c, decide (t ≤ c))` — so its
measurability is inherited, never proved by hand; its pointwise form and Markov property are
the two lemmas. Tie convention: `Δ = decide (T ≤ C)` (ties count as events) — Book-vs-Lean
note: the classical treatments assume `P(T = C) = 0`, where the convention is immaterial.
Here the kernel only exercises `observe` and the transfer theorems.

**Bibliographic comments.** Random censorship as an explicit observation mechanism goes back
to Kaplan–Meier 1958 and J. Gilbert's 1962 thesis; the kernel packaging is ours.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

open StatLean.PointEstimation

/-! ## The location family -/

/-- The location family of a base law `μ₀`: parameter `θ` shifts the law by `θ`
(TPE2 §3.1 (verify §)). Arbitrary base law — the model structure, not a parametric family. -/
noncomputable def locationFam (μ₀ : Measure ℝ) : ℝ → Measure ℝ :=
  fun θ => μ₀.map (fun x => θ + x)

instance (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (θ : ℝ) :
    IsProbabilityMeasure (locationFam μ₀ θ) := by
  unfold locationFam
  exact Measure.isProbabilityMeasure_map (measurable_const_add θ).aemeasurable

/-- Shifting the data shifts the parameter: the location model is equivariant under
translation (via `pushforward_pushforward`). -/
theorem pushforward_locationFam_shift (μ₀ : Measure ℝ) (c : ℝ) :
    pushforward (locationFam μ₀) (fun x => c + x) = fun θ => locationFam μ₀ (c + θ) := by
  funext θ
  simp only [pushforward, locationFam]
  rw [Measure.map_map (measurable_const_add c) (measurable_const_add θ)]
  have hcomp : ((fun x : ℝ => c + x) ∘ fun x : ℝ => θ + x) = fun x : ℝ => c + θ + x :=
    funext fun x => (add_assoc c θ x).symm
  rw [hcomp]

/-! ## The right-censoring kernel -/

/-- Measurability of the censoring readout map `(t, c) ↦ (t ∧ c, 1{t ≤ c})`; the `Bool`
component is measurable because the preimage of each truth value is the closed set
`{p | p.1 ≤ p.2}` or its complement. -/
private theorem measurable_censorReadout :
    Measurable fun p : ℝ × ℝ => (min p.1 p.2, decide (p.1 ≤ p.2)) := by
  refine (measurable_fst.min measurable_snd).prodMk ?_
  refine measurable_to_countable' fun b => ?_
  have hle : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
  cases b
  · have : (fun p : ℝ × ℝ => decide (p.1 ≤ p.2)) ⁻¹' {false} = {p : ℝ × ℝ | p.1 ≤ p.2}ᶜ := by
      ext p; simp
    rw [this]; exact hle.compl
  · have : (fun p : ℝ × ℝ => decide (p.1 ≤ p.2)) ⁻¹' {true} = {p : ℝ × ℝ | p.1 ≤ p.2} := by
      ext p; simp
    rw [this]; exact hle

/-- **Right-censoring observation kernel** with censoring law `ν`: a full event time `t` is
observed as `(t ∧ C, 1{t ≤ C})`, `C ∼ ν` independent of the data (Kaplan–Meier 1958 §2).
Built compositionally so measurability is inherited. -/
noncomputable def rightCensorKernel (ν : Measure ℝ) : Kernel ℝ (ℝ × Bool) :=
  ((Kernel.deterministic id measurable_id) ×ₖ Kernel.const ℝ ν).map
    (fun p => (min p.1 p.2, decide (p.1 ≤ p.2)))

/-- Pointwise form of the censoring kernel: the law of `(t ∧ C, 1{t ≤ C})` under `C ∼ ν`. -/
theorem rightCensorKernel_apply (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) :
    rightCensorKernel ν t = ν.map (fun c => (min t c, decide (t ≤ c))) := by
  rw [rightCensorKernel, Kernel.map_apply _ measurable_censorReadout, Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map measurable_censorReadout measurable_prodMk_left]
  rfl

instance (ν : Measure ℝ) [IsProbabilityMeasure ν] : IsMarkovKernel (rightCensorKernel ν) := by
  unfold rightCensorKernel
  exact Kernel.IsMarkovKernel.map _ measurable_censorReadout

/-- Identification from right-censored data implies identification from complete data — the
destroy-direction transfer theorem, instantiated. -/
theorem identifiable_of_rightCensored (μ₀ : Measure ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    -- LEAN-ONLY: identifiability certificate being transferred; antecedent, no scope change
    (h : Identifiable (observe (locationFam μ₀) (rightCensorKernel ν))) :
    Identifiable (locationFam μ₀) :=
  identifiable_of_observe _ h

end StatLean.StatisticalModels
