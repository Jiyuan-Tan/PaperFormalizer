module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChangingClassMarginal
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedPointwiseDense
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringBookDifference
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringBookMaximal
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

/-!
# Local difference geometry for changing classes

The results connect metric-local increments of a changing class to global
uniform covering bounds for its difference class.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory

/-- The row-`n` increments indexed by pairs at distance strictly below `δ`.

For nonpositive `δ` the class is empty. -/
def changingLocalDifferenceClass
    {Ω T : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    (f : ℕ → T → Ω → ℝ) (n : ℕ) (δ : ℝ) : Set (Ω → ℝ) :=
  {h | ∃ s t, dist s t < δ ∧ h = fun x => f n s x - f n t x}

/-- Every metric-local row increment belongs to the unrestricted difference
class of that row. -/
theorem changingLocalDifferenceClass_subset_differenceClass
    {Ω T : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    (f : ℕ → T → Ω → ℝ) (n : ℕ) (δ : ℝ) :
    changingLocalDifferenceClass f n δ ⊆ differenceClass (Set.range (f n)) := by
  rintro h ⟨s, t, _, rfl⟩
  exact ⟨f n s, f n t, ⟨s, rfl⟩, ⟨t, rfl⟩, rfl⟩

/-- A metric-local row increment satisfying a strict `L²(P)` bound belongs
to the corresponding strict localized slice of the row range. -/
theorem changingLocalDifferenceClass_subset_strictLocalizedDifferenceClass
    {Ω T : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    (f : ℕ → T → Ω → ℝ) (P : Measure Ω)
    (n : ℕ) (δ r : ℝ)
    (hL2 : ∀ s t, dist s t < δ →
      eLpNorm (fun x => f n s x - f n t x) 2 P < ENNReal.ofReal r) :
    changingLocalDifferenceClass f n δ ⊆
      strictLocalizedDifferenceClass (Set.range (f n)) P r := by
  rintro h ⟨s, t, hst, rfl⟩
  exact ⟨f n s, ⟨s, rfl⟩, f n t, ⟨t, rfl⟩, rfl, hL2 s t hst⟩

/-- Twice a changing envelope dominates every metric-local row increment. -/
theorem isEnvelope_changingLocalDifferenceClass_two
    {Ω T : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    {f : ℕ → T → Ω → ℝ} {Φ : ℕ → Ω → ℝ}
    (hΦ : ChangingEnvelope f Φ) (n : ℕ) (δ : ℝ) :
    IsEnvelope (changingLocalDifferenceClass f n δ) (fun x => 2 * Φ n x) := by
  rintro h ⟨s, t, _, rfl⟩ x
  exact hΦ.increment_abs_le n s t x

/-- Metric-local increments of measurable row functions are measurable. -/
theorem measurable_of_mem_changingLocalDifferenceClass
    {Ω T : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    {f : ℕ → T → Ω → ℝ}
    (hf_meas : ∀ n t, Measurable (f n t))
    {n : ℕ} {δ : ℝ} {h : Ω → ℝ}
    (hh : h ∈ changingLocalDifferenceClass f n δ) : Measurable h := by
  obtain ⟨s, t, _, rfl⟩ := hh
  exact (hf_meas n s).sub (hf_meas n t)

/-- A positive localization radius includes the zero increment obtained by
using the same index twice. -/
theorem zero_mem_changingLocalDifferenceClass
    {Ω T : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    [Nonempty T] (f : ℕ → T → Ω → ℝ) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    (fun _ : Ω => 0) ∈ changingLocalDifferenceClass f n δ := by
  let t : T := Classical.choice inferInstance
  refine ⟨t, t, ?_, ?_⟩
  · simpa using hδ
  · funext x
    simp

/-- The local row-increment entropy is bounded by the row entropy through the
global difference-class comparison. -/
theorem bookUniformCoveringEntropyIntegral_changingLocalDifferenceClass_le
    {Ω T : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    (f : ℕ → T → Ω → ℝ)
    (hf_meas : ∀ n t, Measurable (f n t))
    (Φ : ℕ → Ω → ℝ) (n : ℕ) (r δ : ℝ) :
    bookUniformCoveringEntropyIntegral r
        (changingLocalDifferenceClass f n δ) (fun x => 2 * Φ n x) ≤
      ENNReal.ofReal (Real.sqrt 2) *
        bookUniformCoveringEntropyIntegral r (Set.range (f n)) (Φ n) := by
  exact (bookUniformCoveringEntropyIntegral_mono_class
      (changingLocalDifferenceClass_subset_differenceClass f n δ)
      (fun x => 2 * Φ n x) r).trans
    (bookUniformCoveringEntropyIntegral_differenceClass_le_sqrtTwo_mul
      (Set.range (f n)) (fun g hg => by
        obtain ⟨t, rfl⟩ := hg
        exact hf_meas n t) (Φ n) r)

end AsymptoticStatistics.EmpiricalProcess
