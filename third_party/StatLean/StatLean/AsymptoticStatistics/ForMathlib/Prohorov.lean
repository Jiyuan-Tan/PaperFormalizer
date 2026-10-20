module
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity

@[expose] public section

/-!
# Prohorov-type tightness and subsequence extraction on probability measures

Two Prohorov-flavoured results used in van der Vaart's representation theorem
(Theorem 7.10, §7.3 "Convergence to a Normal Experiment") — "marginal tight ⇒ joint
tight, then pick a weak-convergent subsequence":

* `tight_prod_of_tight_marginals` — tight marginals ⇒ tight joint;
* `extract_weak_subseq` — in a Polish space, a tight sequence of probability measures
  admits a weakly convergent subsequence (via Mathlib's
  `isCompact_closure_of_isTightMeasureSet` + metrizability of `ProbabilityMeasure`).

Plus the convenience rewriting `isTightMeasureSet_range_iff_singleton_tight`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics
namespace Prohorov

/-- **Marginals tight ⇒ joint tight** (on a product of two spaces).

Given a set `S` of probability measures on `X × Y` whose first-marginal and
second-marginal projections are each tight, `S` itself is tight. Standard argument:
cover each marginal by a compact up to `ε/2`; the product of those compacts covers
the joint up to `ε` (the complement is the union of two "strips", each controlled by
its marginal). -/
theorem tight_prod_of_tight_marginals
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (S : Set (Measure (X × Y)))
    (hX : IsTightMeasureSet ((fun μ : Measure (X × Y) => μ.map Prod.fst) '' S))
    (hY : IsTightMeasureSet ((fun μ : Measure (X × Y) => μ.map Prod.snd) '' S)) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hX hY ⊢
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := by
    rw [ENNReal.div_pos_iff]
    exact ⟨hε.ne', by norm_num⟩
  obtain ⟨K_X, hK_X_compact, hK_X⟩ := hX (ε / 2) hε2
  obtain ⟨K_Y, hK_Y_compact, hK_Y⟩ := hY (ε / 2) hε2
  refine ⟨K_X ×ˢ K_Y, hK_X_compact.prod hK_Y_compact, ?_⟩
  intro μ hμ
  -- `(K_X ×ˢ K_Y)ᶜ = (K_X)ᶜ ×ˢ univ ∪ univ ×ˢ (K_Y)ᶜ`, each bounded by a marginal.
  rw [Set.compl_prod_eq_union]
  calc μ ((K_X)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (K_Y)ᶜ)
      ≤ μ ((K_X)ᶜ ×ˢ Set.univ) + μ (Set.univ ×ˢ (K_Y)ᶜ) := measure_union_le _ _
    _ = (μ.map Prod.fst) (K_X)ᶜ + (μ.map Prod.snd) (K_Y)ᶜ := by
        rw [Set.prod_univ, Set.univ_prod,
            Measure.map_apply measurable_fst hK_X_compact.measurableSet.compl,
            Measure.map_apply measurable_snd hK_Y_compact.measurableSet.compl]
    _ ≤ ε / 2 + ε / 2 :=
        add_le_add (hK_X _ ⟨μ, hμ, rfl⟩) (hK_Y _ ⟨μ, hμ, rfl⟩)
    _ = ε := ENNReal.add_halves _

/-- **Weak convergence implies tightness of the range** (Prohorov converse, sequence form).

If a sequence of probability measures `μ n` on a Polish space converges weakly to a
probability measure `ν`, then the set `{μ n | n ∈ ℕ}` is tight.

Proof: lift to `ProbabilityMeasure`, get `Tendsto` in the weak topology, observe that
`insert Pν (Set.range P)` is compact (convergent sequence + limit), take the closure
(closed subset of compact = compact), and apply Mathlib's
`isTightMeasureSet_of_isCompact_closure`. -/
theorem weakConverges_range_tight
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [BorelSpace E]
    [CompleteSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (h_weak : WeakConverges μ ν) :
    IsTightMeasureSet (Set.range μ) := by
  let P : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, inferInstance⟩
  let Pν : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have h_tendsto : Tendsto P atTop (𝓝 Pν) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr h_weak
  have h_insert_compact : IsCompact (insert Pν (Set.range P)) :=
    h_tendsto.isCompact_insert_range
  have h_insert_closed : IsClosed (insert Pν (Set.range P)) := h_insert_compact.isClosed
  have h_closure_compact : IsCompact (closure (insert Pν (Set.range P))) := by
    rw [h_insert_closed.closure_eq]; exact h_insert_compact
  have h_tight_insert :=
    MeasureTheory.isTightMeasureSet_of_isCompact_closure h_closure_compact
  refine h_tight_insert.subset ?_
  rintro ρ ⟨n, rfl⟩
  exact ⟨P n, Set.mem_insert_of_mem _ ⟨n, rfl⟩, rfl⟩

/-- **Prohorov: tight ⇒ sequentially compact for weak convergence** (Polish case).

If the range `{μ n | n : ℕ}` is a tight set of probability measures on a Polish space
`E`, there exists a strictly monotone subsequence extractor `φ` and a probability measure
`μ_lim` such that `μ (φ k)` converges weakly to `μ_lim`.

Proof: lift `μ n` to `ProbabilityMeasure E`; the range is tight, so its closure is
compact (Mathlib `isCompact_closure_of_isTightMeasureSet`). `ProbabilityMeasure E` is
metrizable for Polish `E`, hence first-countable, so the compact closure is sequentially
compact; extract a subsequence converging in the weak topology. Translate back to our
test-function-based `WeakConverges` via `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`. -/
theorem extract_weak_subseq
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (h_tight : IsTightMeasureSet (Set.range μ)) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (μ_lim : Measure E) (_ : IsProbabilityMeasure μ_lim),
      WeakConverges (fun k => μ (φ k)) μ_lim := by
  -- Lift to `ProbabilityMeasure E`.
  set P : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, inferInstance⟩ with hP_def
  -- The set `{(P n : Measure E) | n : ℕ}` is tight — equal to `Set.range μ` by construction.
  have h_tight_P :
      IsTightMeasureSet {(↑(ν : ProbabilityMeasure E) : Measure E) | ν ∈ Set.range P} := by
    have : {(↑(ν : ProbabilityMeasure E) : Measure E) | ν ∈ Set.range P} = Set.range μ := by
      ext ρ
      constructor
      · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨P n, ⟨n, rfl⟩, rfl⟩
    rw [this]
    exact h_tight
  -- Its closure is compact (Prokhorov).
  have h_compact : IsCompact (closure (Set.range P)) :=
    isCompact_closure_of_isTightMeasureSet h_tight_P
  -- P takes values in `closure (Set.range P)`.
  have h_P_in : ∀ n, P n ∈ closure (Set.range P) :=
    fun n => subset_closure ⟨n, rfl⟩
  -- Compact + first-countable (metrizable since E is Polish) ⇒ sequentially compact.
  have h_seqcompact : IsSeqCompact (closure (Set.range P)) := h_compact.isSeqCompact
  obtain ⟨P_lim, _hP_lim_in, φ, hφ_mono, hφ_conv⟩ := h_seqcompact h_P_in
  -- Repackage into our `WeakConverges` predicate.
  refine ⟨φ, hφ_mono, (P_lim : Measure E), inferInstance, ?_⟩
  intro f
  have h_int :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hφ_conv) f
  exact h_int

/-- A single sequence of probability measures is tight iff its range (as a set) is
tight. Convenience wrapper matching the hypothesis shape used by `extract_weak_subseq`. -/
theorem isTightMeasureSet_range_iff_singleton_tight
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (μ : ℕ → Measure E) :
    IsTightMeasureSet (Set.range μ) ↔ ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ K, IsCompact K ∧ ∀ n, (μ n) Kᶜ ≤ ε := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  constructor
  · intro h ε hε
    obtain ⟨K, hK_compact, hK⟩ := h ε hε
    exact ⟨K, hK_compact, fun n => hK (μ n) ⟨n, rfl⟩⟩
  · intro h ε hε
    obtain ⟨K, hK_compact, hK⟩ := h ε hε
    refine ⟨K, hK_compact, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hK n

end Prohorov
end AsymptoticStatistics
