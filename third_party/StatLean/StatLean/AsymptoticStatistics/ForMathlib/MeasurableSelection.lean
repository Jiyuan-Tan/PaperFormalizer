module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.Kernel.Disintegration.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import StatLean.AsymptoticStatistics.ForMathlib.AnalyticSetCapacitability

@[expose] public section

/-!
# Measurable selection of approximate ε-minimisers

Measurable selection of approximate ε-minimisers from a jointly measurable
function on a Polish target space, via the Aumann / Jankov-von Neumann
construction. The principal results are:

* `analytic_projection_aeMeasurable` — analytic projection of a Borel
  level set is m-a.e. measurable (Suslin / Choquet capacitability).
* `exists_measurable_approx_argmin` — abstract ε-approximate argmin
  selector for a jointly measurable `f : α × β → ℝ≥0∞` on Polish `β`.
* `exists_measurable_approx_argmin_lintegral` — form
  specialised to the Bayes-risk integrand
  `(x, b) ↦ ∫⁻ θ, ℓ θ b ∂(posterior x)`.

The construction uses standard-Borel structure on Polish `β` plus
Aumann-style projection measurability; it does NOT depend on lower
semicontinuity of `ℓ` in the second factor.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace AsymptoticStatistics
namespace MeasurableSelection

/-- **Sub-lemma 1 — analytic projection is m-a.e. measurable**.

For `f : α × β → ℝ≥0∞` jointly measurable on a Polish-target second factor,
the level-set projection `{x : α | ∃ b : β, f (x, b) < c}` corresponds to an
analytic set in α. Under σ-finite m, the projection is m-a.e. measurable
via Choquet capacitability of analytic sets (Suslin's theorem).

Concretely: for fixed `c : ℝ≥0∞`, the projection is the image of the Borel
set `{(x, b) | f (x, b) < c}` under the Borel projection `α × β → α`.
Mathlib's `MeasurableSet.analyticSet_image` plus Choquet capacitability
give this projection's m-a.e. measurability.

The hypotheses:
- `f`, `c`, `m` — the integrand, threshold, and σ-finite measure (vdV §8.5).
- `hf` — joint measurability of the integrand.
- `[StandardBorelSpace α]` — needed for `MeasurableSet.analyticSet_image`;
  Polish spaces are automatically standard Borel.
- `[TopologicalSpace β] [PolishSpace β] [BorelSpace β]` — Polish
  target gives second-countable Borel structure required by the analytic-image
  theorem.
- `[SFinite m]` — regularity for the null-measurable conclusion.

Proof: `MeasurableSet.analyticSet_image` gives an analytic projection; the project
theorem `AnalyticSet.statLean_nullMeasurableSet`, proved by Choquet capacitability, then gives
null-measurability for the s-finite measure `m`. -/
theorem analytic_projection_aeMeasurable
    {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [PolishSpace β] [BorelSpace β]
    (f : α × β → ℝ≥0∞) (hf : Measurable f) (c : ℝ≥0∞)
    (m : Measure α) [SFinite m] :
    NullMeasurableSet {x : α | ∃ b : β, f (x, b) < c} m := by
  classical
  -- Endow α with a compatible Polish topology so that we can speak of
  -- analytic subsets of α.
  letI := upgradeStandardBorel α
  -- The Borel level set `S := {(x, b) | f (x, b) < c}` is measurable.
  set S : Set (α × β) := f ⁻¹' Set.Iio c with hSdef
  have hS_meas : MeasurableSet S := hf measurableSet_Iio
  -- The level set `{x | ∃ b, f (x, b) < c}` is exactly the image of `S`
  -- under the first projection `Prod.fst : α × β → α`.
  have hset_eq : {x : α | ∃ b : β, f (x, b) < c} = Prod.fst '' S := by
    ext x
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨(x, b), hb, rfl⟩
    · rintro ⟨⟨x', b⟩, hxb, rfl⟩
      exact ⟨b, hxb⟩
  -- The image of a measurable set in the standard Borel space `α × β` under
  -- the measurable map `Prod.fst : α × β → α` is analytic.
  have hAnalytic : MeasureTheory.AnalyticSet (Prod.fst '' S : Set α) :=
    hS_meas.analyticSet_image measurable_fst
  -- Suslin / Choquet capacitability: an analytic set in a Polish space is
  -- `NullMeasurableSet` for any s-finite Borel measure.
  have hNMS : NullMeasurableSet (Prod.fst '' S) m :=
    hAnalytic.statLean_nullMeasurableSet m
  -- Transport the conclusion across the set equality.
  rw [hset_eq]
  exact hNMS

/-- **Borel-measurability of the ε-argmin graph**.

For jointly measurable `f : α × β → ℝ≥0∞` on standard-Borel α and a
Polish-target β, and `ε > 0`, the graph
`G := {(x, b) | f (x, b) ≤ (⨅ b', f (x, b')) + ε}`
is **null-measurable** in the product σ-algebra of `α × β` w.r.t. any
σ-finite measure on `α`.

Why null-measurable, not Borel-measurable: φ x := ⨅ b', f (x, b') is
only **m-a.e.**-measurable in α (`analytic_projection_aeMeasurable`):
its level sets are analytic, and Choquet capacitability gives only
universal measurability, not Borel measurability.

Sketch: write `G = (f).preimage(level)` ∩ `(φ ∘ Prod.fst).preimage(level)`.
Both factors are jointly null-measurable once φ is m-a.e.-measurable on α;
the intersection is null-measurable on α × β.

The proof reduces null-measurability of the graph to (i) a.e.-measurability
of `φ x := ⨅ b', f (x, b')` on `m`, obtained from
`analytic_projection_aeMeasurable` plus
`ENNReal.aemeasurable_of_exist_almost_disjoint_supersets`, and (ii) the
fact that the graph defined with the measurable representative
`φ' := AEMeasurable.mk φ` is Borel-measurable, while the difference with
the original graph lies in the **vertical strip** `N × β` with
`N := {x | φ x ≠ φ' x}` an m-null set.

The output is a Borel representative `G' : Set (α × β)` and an m-null
witness `N : Set α` such that on the m-conull complement `Nᶜ`, the fibers of
the original graph and `G'` coincide. -/
private theorem nullMeasurableSet_approx_argmin_graph
    {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [PolishSpace β] [BorelSpace β]
    [Nonempty β]
    (f : α × β → ℝ≥0∞) (hf : Measurable f) (ε : ℝ≥0∞)
    (m : Measure α) [SFinite m] :
    ∃ G' : Set (α × β), MeasurableSet G' ∧
      ∃ N : Set α, MeasurableSet N ∧ m N = 0 ∧
        ∀ x ∉ N, ∀ b : β,
          (f (x, b) ≤ (⨅ b' : β, f (x, b')) + ε ↔ (x, b) ∈ G') := by
  classical
  -- analytic-projection null-measurability of sub-level sets, plus
  -- `ENNReal.aemeasurable_of_exist_almost_disjoint_supersets`. Once φ is
  -- a.e.-measurable on α, replace it with its measurable representative
  -- φ' = AEMeasurable.mk; then the graph G' = {p | f p ≤ φ' p.1 + ε} is
  -- Borel-measurable, and the difference between the original graph and G'
  -- is contained in the vertical strip N × β where N := {x | φ x ≠ φ' x}
  -- is m-null. We expose N (and the Borel set hosting it) as the witness.
  set φ : α → ℝ≥0∞ := fun x => ⨅ b' : β, f (x, b') with hφ_def
  -- For every `c : ℝ≥0∞`, `{x | φ x < c}` is null-measurable on `m`.
  have h_phi_lt_NMS : ∀ c : ℝ≥0∞,
      NullMeasurableSet {x : α | φ x < c} m := by
    intro c
    have hset_eq : {x : α | φ x < c} = {x : α | ∃ b : β, f (x, b) < c} := by
      ext x; simp [φ, iInf_lt_iff]
    rw [hset_eq]
    exact analytic_projection_aeMeasurable f hf c m
  -- Hence φ is `AEMeasurable m` via `aemeasurable_of_exist_almost_disjoint_supersets`.
  have hφ_aemeas : AEMeasurable φ m := by
    refine ENNReal.aemeasurable_of_exist_almost_disjoint_supersets m φ ?_
    intro p q hpq
    -- Both sub/super-level sets are null-measurable; take measurable supersets.
    obtain ⟨U, hU_sub, hU_meas, hU_eq⟩ :=
      NullMeasurableSet.exists_measurable_superset_ae_eq (h_phi_lt_NMS (p : ℝ≥0∞))
    -- For the upper-level set we use the complement of `{φ ≤ q}`. We prove
    -- `{φ ≤ q}` null-measurable as a countable intersection.
    have h_phi_le : NullMeasurableSet {x : α | φ x ≤ (q : ℝ≥0∞)} m := by
      have hset_eq : {x : α | φ x ≤ (q : ℝ≥0∞)}
          = ⋂ n : ℕ, {x : α | φ x < (q : ℝ≥0∞) + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        refine ⟨?_, ?_⟩
        · intro hx n
          have hpos : (0 : ℝ≥0∞) < ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
            rw [ENNReal.inv_pos]; exact ENNReal.natCast_ne_top _
          have hqne : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
          exact lt_of_le_of_lt hx (ENNReal.lt_add_right hqne hpos.ne')
        · intro hx
          by_contra hcontra
          rw [not_le] at hcontra
          have hsub_pos : 0 < φ x - (q : ℝ≥0∞) := tsub_pos_of_lt hcontra
          obtain ⟨n, hn⟩ : ∃ n : ℕ,
              ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ < φ x - (q : ℝ≥0∞) := by
            rcases ENNReal.exists_inv_nat_lt hsub_pos.ne' with ⟨k, hk⟩
            refine ⟨k, ?_⟩
            calc ((k + 1 : ℕ) : ℝ≥0∞)⁻¹
                ≤ (k : ℝ≥0∞)⁻¹ := by
                    apply ENNReal.inv_le_inv.mpr
                    exact_mod_cast Nat.le_succ k
              _ < φ x - (q : ℝ≥0∞) := hk
          have hxn := hx n
          have hqne : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
          have h1 : (q : ℝ≥0∞) + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
              < (q : ℝ≥0∞) + (φ x - (q : ℝ≥0∞)) :=
            (ENNReal.add_lt_add_iff_left hqne).mpr hn
          rw [add_tsub_cancel_of_le hcontra.le] at h1
          exact (lt_irrefl _ (hxn.trans h1)).elim
      rw [hset_eq]
      exact NullMeasurableSet.iInter (fun n => h_phi_lt_NMS _)
    have h_phi_gt : NullMeasurableSet {x : α | (q : ℝ≥0∞) < φ x} m := by
      have hcompl : {x : α | (q : ℝ≥0∞) < φ x}
          = {x : α | φ x ≤ (q : ℝ≥0∞)}ᶜ := by ext x; simp [not_le]
      rw [hcompl]
      exact h_phi_le.compl
    obtain ⟨V, hV_sub, hV_meas, hV_eq⟩ :=
      NullMeasurableSet.exists_measurable_superset_ae_eq h_phi_gt
    refine ⟨U, V, hU_meas, hV_meas, hU_sub, hV_sub, ?_⟩
    -- m (U ∩ V) = 0: U =ᵐ {φ < p} and V =ᵐ {q < φ}; their intersection is empty when p < q.
    set Sp : Set α := {x : α | φ x < (p : ℝ≥0∞)}
    set Sq : Set α := {x : α | (q : ℝ≥0∞) < φ x}
    have hUV_eq : (U ∩ V : Set α) =ᵐ[m] (Sp ∩ Sq : Set α) :=
      hU_eq.inter hV_eq
    have hempty : (Sp ∩ Sq : Set α) = (∅ : Set α) := by
      ext x
      simp only [Sp, Sq, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and, not_lt]
      intro hxp
      -- hxp : φ x < p; goal: φ x ≤ q.
      have hpq' : (p : ℝ≥0∞) < (q : ℝ≥0∞) := by exact_mod_cast hpq
      exact (hxp.trans hpq').le
    have hzero : m (U ∩ V) = m ((∅ : Set α)) := by
      rw [← hempty]; exact measure_congr hUV_eq
    simp [hzero]
  -- Choose a measurable representative φ' = AEMeasurable.mk φ.
  set φ' : α → ℝ≥0∞ := hφ_aemeas.mk φ with hφ'_def
  have hφ'_meas : Measurable φ' := hφ_aemeas.measurable_mk
  have hφ'_ae : φ =ᵐ[m] φ' := hφ_aemeas.ae_eq_mk
  -- Define the auxiliary "Borel" graph G' built with φ'.
  set G' : Set (α × β) := {p : α × β | f p ≤ φ' p.1 + ε} with hG'_def
  have hG'_meas : MeasurableSet G' := by
    -- G' is the preimage of `{(u, v) | u ≤ v}` under
    -- `(x, b) ↦ (f (x, b), φ' x + ε)`, a measurable map.
    have h_map : Measurable (fun p : α × β => (f p, φ' p.1 + ε)) := by
      refine Measurable.prodMk hf ?_
      exact (hφ'_meas.comp measurable_fst).add measurable_const
    exact h_map measurableSet_le'
  -- Build the vertical-strip null witness.
  -- The equality `hφ'_ae : φ =ᵐ[m] φ'` provides an m-null exceptional set;
  -- a measurable representative of that null set. Use
  -- `ae_iff` + measurability of `{x | φ x ≠ φ' x}` is NOT immediate (φ
  -- is only a.e.-measurable). Instead, use `ae_eq_iff_exists_mem`-style
  -- lift: since `hφ'_ae : φ =ᵐ[m] φ'`, the set `{x | φ x ≠ φ' x}` is
  -- contained in some MEASURABLE m-null set N₀.
  -- Extract a measurable null witness: `Filter.EventuallyEq` on `MeasureTheory.ae m`
  -- gives `m {x | φ x ≠ φ' x} = 0`, but for `MeasurableSet N` we take a
  -- measurable superset via `Measure.measurableSet_toMeasurable`-style lift.
  set Nraw : Set α := {x : α | φ x ≠ φ' x} with hNraw_def
  have hNraw_null : m Nraw = 0 := hφ'_ae
  -- Take a measurable superset of `Nraw` with the same measure (zero).
  set N : Set α := MeasureTheory.toMeasurable m Nraw with hN_def
  have hN_meas : MeasurableSet N := MeasureTheory.measurableSet_toMeasurable m Nraw
  have hN_null : m N = 0 := by
    rw [hN_def]
    exact (MeasureTheory.measure_toMeasurable Nraw).trans hNraw_null
  have hNraw_subset_N : Nraw ⊆ N := MeasureTheory.subset_toMeasurable m Nraw
  -- Package the witnesses.
  refine ⟨G', hG'_meas, N, hN_meas, hN_null, ?_⟩
  intro x hxN b
  -- For x ∉ N, in particular x ∉ Nraw, so φ x = φ' x; thus the two
  -- inequalities are equivalent.
  have hx_eq : φ x = φ' x := by
    by_contra h
    exact hxN (hNraw_subset_N h)
  -- Goal: f (x, b) ≤ φ x + ε ↔ (x, b) ∈ G'.
  -- (x, b) ∈ G' unfolds to f (x, b) ≤ φ' x + ε.
  change f (x, b) ≤ φ x + ε ↔ f (x, b) ≤ φ' x + ε
  rw [hx_eq]

/-- **Analytic-image null-measurability of the basis-ball preimage**.

For a Borel set `G' ⊆ α × β` (α standard-Borel, β Polish) and a Borel set
`U ⊆ β`, the projection `{x : α | ∃ b ∈ U, (x, b) ∈ G'}` is the image of the
Borel set `G' ∩ (univ ×ˢ U)` under `Prod.fst`. This image is **analytic** by
`MeasurableSet.analyticSet_image`, hence `NullMeasurableSet m` for any `[SFinite m]`
by `AnalyticSet.statLean_nullMeasurableSet` (after `letI := upgradeStandardBorel α`
to endow `α` with a Polish topology).

This is the per-level building block for the Suslin scheme below. -/
private theorem nullMeasurableSet_proj_of_borel_basis
    {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [PolishSpace β] [BorelSpace β]
    (G' : Set (α × β)) (hG'_meas : MeasurableSet G')
    (U : Set β) (hU_meas : MeasurableSet U)
    (m : Measure α) [SFinite m] :
    NullMeasurableSet {x : α | ∃ b ∈ U, (x, b) ∈ G'} m := by
  classical
  letI := upgradeStandardBorel α
  -- Identify the projection set with `Prod.fst '' (G' ∩ (univ ×ˢ U))`.
  set S : Set (α × β) := G' ∩ (Set.univ ×ˢ U) with hSdef
  have hS_meas : MeasurableSet S :=
    hG'_meas.inter (MeasurableSet.univ.prod hU_meas)
  have hset_eq : {x : α | ∃ b ∈ U, (x, b) ∈ G'} = Prod.fst '' S := by
    ext x
    constructor
    · rintro ⟨b, hbU, hxb⟩
      exact ⟨(x, b), ⟨hxb, Set.mem_prod.mpr ⟨Set.mem_univ _, hbU⟩⟩, rfl⟩
    · rintro ⟨⟨x', b⟩, hxb, rfl⟩
      exact ⟨b, hxb.2.2, hxb.1⟩
  -- The image of a Borel set under measurable Prod.fst is analytic.
  have hAnalytic : MeasureTheory.AnalyticSet (Prod.fst '' S : Set α) :=
    hS_meas.analyticSet_image measurable_fst
  have hNMS : NullMeasurableSet (Prod.fst '' S) m :=
    hAnalytic.statLean_nullMeasurableSet m
  rw [hset_eq]
  exact hNMS

/-- **Cauchy nested-ball selector core** (inner step).

The recursive index construction for the closed-graph Aumann selector. Given a
metric Polish target `β` and a Borel graph `F ⊆ α × β` with non-empty fibers
off an m-null set `N`, this lemma produces:

* a measurable sequence `b : ℕ → α → β` taking values in the dense range
  `Set.range (TopologicalSpace.denseSeq β)`,
* a measurable m-null superset `N₀ ⊇ N`,

such that off `N₀`, the sequence `b k x` is Cauchy with successive distances
controlled by `2^{-k}`, and each ball `closedBall (b k x) 2^{-k}` meets the
fiber `F_x := {b : β | (x, b) ∈ F}`.

**Construction**: by recursion on `k`. At level 0, take any dense point witnessing
non-emptiness of `F_x` (m-a.e.). At level `k+1`, refine: pick the least
`u (idx i)` of the dense sequence that lies in `closedBall (b k x) 2^{-k}` AND
whose `2^{-(k+1)}`-ball still meets `F_x`. The latter predicate is
null-measurable via `nullMeasurableSet_proj_of_borel_basis` (the basis-ball
preimage). `Nat.find` packages the choice measurably; the null sets accumulate
across levels into one measurable witness.

This is the recursive null-set bookkeeping (`MeasureTheory.toMeasurable` +
`Nat.find` measurability + per-level null-superset extraction), separated from
the limit argument that closes the outer `aumann_selector_closed_graph_polish`. -/
private theorem cauchy_selector_inductive_step
    {α β : Type*}
    [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    [MetricSpace β] [CompleteSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] [Nonempty β]
    (F : Set (α × β)) (hF_meas : MeasurableSet F)
    (m : Measure α) [SFinite m]
    (N : Set α) (hN_meas : MeasurableSet N) (hN_null : m N = 0)
    (hF_ne_offN : ∀ x ∉ N, ∃ b : β, (x, b) ∈ F) :
    ∃ (N₀ : Set α) (b : ℕ → α → β),
      MeasurableSet N₀ ∧ m N₀ = 0 ∧ N ⊆ N₀ ∧
      (∀ k, Measurable (b k)) ∧
      (∀ x ∉ N₀, ∀ k, dist (b k x) (b (k+1) x) ≤ (1 / 2 : ℝ)^k) ∧
      (∀ x ∉ N₀, ∀ k, ∃ b' : β, dist b' (b k x) ≤ (1 / 2 : ℝ)^k ∧ (x, b') ∈ F) := by
  classical
  -- `SeparableSpace β` is automatic from `SecondCountableTopology β`; combined with
  -- `MetricSpace + CompleteSpace + SecondCountableTopology` we get `PolishSpace β`.
  haveI : SeparableSpace β := inferInstance
  haveI : PolishSpace β := inferInstance
  -- The dense sequence in `β`.
  set d : ℕ → β := TopologicalSpace.denseSeq β with hd_def
  have hd_dense : DenseRange d := TopologicalSpace.denseRange_denseSeq β
  -- Radius schedule: `δ k := (1/2)^k`. The "fiber-witness slack" at level `k`
  -- is `δ (k+1) = (1/2)^(k+1) = δ k / 2`, half of the conclusion's `(1/2)^k`.
  -- This strictness gives the existence proof at the next level enough room.
  set δ : ℕ → ℝ := fun k => (1 / 2 : ℝ)^k with hδ_def
  have hδ_pos : ∀ k, 0 < δ k := fun k => by
    change (0 : ℝ) < (1 / 2 : ℝ)^k; positivity
  -- A default value in β.
  let b₀ : β := Classical.arbitrary β
  ----------------------------------------------------------------------------
  -- Per-level/index building block: the fiber-witness predicate as
  -- a measurable subset of `α` (modulo a null set).
  --
  -- For each pair `(k, i)`, define
  --   `W k i = {x | ∃ w ∈ closedBall (d i) (δ (k+1)), (x, w) ∈ F}`.
  -- This is null-measurable in `α` by `nullMeasurableSet_proj_of_borel_basis`.
  ----------------------------------------------------------------------------
  let W : ℕ → ℕ → Set α := fun k i =>
    {x : α | ∃ w ∈ Metric.closedBall (d i) (δ (k+1)), (x, w) ∈ F}
  have hW_NMS : ∀ k i, NullMeasurableSet (W k i) m := by
    intro k i
    have hball_meas : MeasurableSet (Metric.closedBall (d i) (δ (k+1))) :=
      (Metric.isClosed_closedBall (x := d i) (ε := δ (k+1))).measurableSet
    exact nullMeasurableSet_proj_of_borel_basis F hF_meas
      (Metric.closedBall (d i) (δ (k+1))) hball_meas m
  -- Replace each `W k i` with a measurable superset `W' k i ⊇ W k i`,
  -- `W' k i =ᵐ[m] W k i`.
  choose W' hW'_sub hW'_meas hW'_ae using
    fun (k i : ℕ) =>
      NullMeasurableSet.exists_measurable_superset_ae_eq (hW_NMS k i)
  -- The level-k exception set `E k := ⋃ i, (W' k i \ W k i)`: a measurable
  -- null set capturing all per-index slack from the `W ⇒ W'` lift.
  let E : ℕ → Set α := fun k => ⋃ i, W' k i \ W k i
  have hE_null : ∀ k, m (E k) = 0 := by
    intro k
    refine measure_iUnion_null fun i => ?_
    -- (W' k i \ W k i) is null because W' k i =ᵐ[m] W k i.
    have hae_mem : ∀ᵐ x ∂m, x ∈ W' k i ↔ x ∈ W k i :=
      (hW'_ae k i).mem_iff
    have hdiff : (W' k i \ W k i) =ᵐ[m] (∅ : Set α) := by
      refine Filter.eventuallyEq_set.mpr ?_
      filter_upwards [hae_mem] with x hx
      constructor
      · rintro ⟨hxW', hxnW⟩
        exact (hxnW (hx.mp hxW')).elim
      · intro hxE
        exact hxE.elim
    calc m (W' k i \ W k i) = m (∅ : Set α) := measure_congr hdiff
      _ = 0 := measure_empty
  ----------------------------------------------------------------------------
  -- Build `b : ℕ → α → β` by recursion, together with measurable index
  -- functions `idx k : α → ℕ` with `b k x = d (idx k x)`.
  --
  -- Augment with a guaranteed-existence fallback at i = 0 so `Nat.find` is
  -- total. At level 0: `idx0 x := Nat.find` over `Q0 x i`.
  -- At level k+1: `idxStep k y x := Nat.find` over `R k y x i`, with
  -- previous value `y := b k x`.
  ----------------------------------------------------------------------------
  let Q0 : α → ℕ → Prop := fun x i => x ∈ W' 0 i ∨ (i = 0 ∧ ∀ j, x ∉ W' 0 j)
  have hQ0_ex : ∀ x, ∃ i, Q0 x i := by
    intro x
    by_cases h : ∃ j, x ∈ W' 0 j
    · obtain ⟨j, hj⟩ := h; exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr ⟨rfl, fun j hxj => h ⟨j, hxj⟩⟩⟩
  have hQ0_meas : ∀ i, MeasurableSet {x | Q0 x i} := by
    intro i
    by_cases hi : i = 0
    · subst hi
      have : {x | Q0 x 0} = W' 0 0 ∪ (⋂ j, (W' 0 j)ᶜ) := by
        ext x; simp [Q0]
      rw [this]
      exact (hW'_meas 0 0).union (MeasurableSet.iInter fun j => (hW'_meas 0 j).compl)
    · have : {x | Q0 x i} = W' 0 i := by
        ext x; simp [Q0, hi]
      rw [this]; exact hW'_meas 0 i
  let idx0 : α → ℕ := fun x => Nat.find (hQ0_ex x)
  have hidx0_meas : Measurable idx0 := measurable_find hQ0_ex hQ0_meas
  -- denseSeq is measurable as a function from ℕ (discrete) into β.
  have hd_meas : Measurable d := measurable_from_nat
  let b0 : α → β := fun x => d (idx0 x)
  have hb0_meas : Measurable b0 := hd_meas.comp hidx0_meas
  -- Step predicate at level `k+1` given previous value `y : β` and index `i`.
  let R : ℕ → β → α → ℕ → Prop := fun k y x i =>
    (dist (d i) y ≤ δ k ∧ x ∈ W' (k+1) i) ∨
      (i = 0 ∧ ∀ j, ¬ (dist (d j) y ≤ δ k ∧ x ∈ W' (k+1) j))
  have hR_ex : ∀ k y x, ∃ i, R k y x i := by
    intro k y x
    by_cases h : ∃ j, dist (d j) y ≤ δ k ∧ x ∈ W' (k+1) j
    · obtain ⟨j, hj⟩ := h; exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr ⟨rfl, fun j hj => h ⟨j, hj⟩⟩⟩
  -- Joint measurability of `R k` in `(y, x)` for each `i`.
  have hR_meas_joint : ∀ k i,
      MeasurableSet {p : β × α | R k p.1 p.2 i} := by
    intro k i
    -- Helper: for any j, the set `{p | dist (d j) p.1 ≤ δ k ∧ p.2 ∈ W' (k+1) j}`
    -- is measurable in (β × α).
    have hAB : ∀ j, MeasurableSet
        {p : β × α | dist (d j) p.1 ≤ δ k ∧ p.2 ∈ W' (k+1) j} := by
      intro j
      have hdist : Measurable (fun p : β × α => dist (d j) p.1) :=
        (measurable_const.dist measurable_id).comp measurable_fst
      have h_le : MeasurableSet {p : β × α | dist (d j) p.1 ≤ δ k} :=
        hdist measurableSet_Iic
      have hW'_pull : MeasurableSet {p : β × α | p.2 ∈ W' (k+1) j} :=
        measurable_snd (hW'_meas (k+1) j)
      exact h_le.inter hW'_pull
    by_cases hi : i = 0
    · subst hi
      have : {p : β × α | R k p.1 p.2 0}
          = {p : β × α | dist (d 0) p.1 ≤ δ k ∧ p.2 ∈ W' (k+1) 0} ∪
            (⋂ j, ({p : β × α | dist (d j) p.1 ≤ δ k ∧ p.2 ∈ W' (k+1) j})ᶜ) := by
        ext p; simp [R]
      rw [this]
      exact (hAB 0).union (MeasurableSet.iInter fun j => (hAB j).compl)
    · have : {p : β × α | R k p.1 p.2 i}
          = {p : β × α | dist (d i) p.1 ≤ δ k ∧ p.2 ∈ W' (k+1) i} := by
        ext p; simp [R, hi]
      rw [this]; exact hAB i
  let idxStep : ℕ → β → α → ℕ := fun k y x => Nat.find (hR_ex k y x)
  have hidxStep_meas : ∀ k, Measurable (fun p : β × α => idxStep k p.1 p.2) := by
    intro k
    exact measurable_find (fun p : β × α => hR_ex k p.1 p.2)
      (fun i => hR_meas_joint k i)
  -- Recursive definition of `b`.
  let b : ℕ → α → β := fun k => Nat.rec (motive := fun _ => α → β)
      b0 (fun k bk x => d (idxStep k (bk x) x)) k
  have hb_meas : ∀ k, Measurable (b k) := by
    intro k
    induction k with
    | zero => exact hb0_meas
    | succ k ih =>
      change Measurable (fun x => d (idxStep k (b k x) x))
      refine hd_meas.comp ?_
      have h_pair : Measurable (fun x : α => (b k x, x)) := ih.prodMk measurable_id
      exact (hidxStep_meas k).comp h_pair
  ----------------------------------------------------------------------------
  -- The null exception set `N₀ := N ∪ E*`, where `E* := toMeasurable m
  -- (⋃ k, E k)` is a measurable null superset of the per-level slack union.
  ----------------------------------------------------------------------------
  -- The "raw" slack union (not necessarily measurable, since W k i isn't).
  let Eraw : Set α := ⋃ k, E k
  have hEraw_null : m Eraw = 0 := by
    refine measure_iUnion_null fun k => hE_null k
  let E_star : Set α := MeasureTheory.toMeasurable m Eraw
  have hE_star_meas : MeasurableSet E_star :=
    MeasureTheory.measurableSet_toMeasurable m Eraw
  have hE_star_null : m E_star = 0 :=
    (MeasureTheory.measure_toMeasurable Eraw).trans hEraw_null
  have hEraw_sub : Eraw ⊆ E_star := MeasureTheory.subset_toMeasurable m Eraw
  let N₀ : Set α := N ∪ E_star
  have hN₀_meas : MeasurableSet N₀ := hN_meas.union hE_star_meas
  have hN₀_null : m N₀ = 0 := by
    refine le_antisymm ?_ (zero_le)
    calc m N₀ ≤ m N + m E_star := measure_union_le _ _
      _ = 0 + 0 := by rw [hN_null, hE_star_null]
      _ = 0 := by simp
  have hN_subset_N₀ : N ⊆ N₀ := Set.subset_union_left
  ----------------------------------------------------------------------------
  -- Off `N₀`, prove existence of fiber witnesses at every level.
  --
  -- This is an induction on k: at level 0, x ∉ N gives `∃ w ∈ F_x`, then
  -- density gives `j` with `dist w (d j) < δ 1`, so `x ∈ W 0 j ⊆ W' 0 j`. At
  -- level k+1, the invariant `x ∈ W k (idx k x)` (which means a fiber witness
  -- `w_k` of `(x, ·) ∈ F` lies within `δ (k+1)` of `b k x`) gives, by density,
  -- some `j` with `dist w_k (d j) < δ (k+2)`; this `j` satisfies the R-predicate
  -- with `y = b k x`.
  ----------------------------------------------------------------------------
  -- Auxiliary: for x ∉ N₀, x ∉ Eraw, hence x ∉ E k for all k. Hence
  -- for any i with `x ∈ W' k i`, we also have `x ∈ W k i`.
  have h_strip_E : ∀ x, x ∉ N₀ → ∀ k i, x ∈ W' k i → x ∈ W k i := by
    intro x hxN₀ k i hxW'
    have hxEraw : x ∉ Eraw := fun h => hxN₀ (Set.mem_union_right _ (hEraw_sub h))
    have hxE_k : x ∉ E k := fun h =>
      hxEraw (Set.mem_iUnion.mpr ⟨k, h⟩)
    by_contra hxW
    exact hxE_k (Set.mem_iUnion.mpr ⟨i, ⟨hxW', hxW⟩⟩)
  -- Useful: density of `d` at radius `r > 0`.
  have hd_dense_rad : ∀ (w : β) (r : ℝ), 0 < r → ∃ j, dist w (d j) < r := by
    intro w r hr
    exact Metric.denseRange_iff.mp hd_dense w r hr
  ----------------------------------------------------------------------------
  -- The invariant: at every level k, for x ∉ N₀,
  --   `x ∈ W' k (idx k x)` where `idx k x` is the index at level `k`.
  -- (Concretely, `idx 0 x = idx0 x` and `idx (k+1) x = idxStep k (b k x) x`.)
  ----------------------------------------------------------------------------
  -- Verify base case k = 0: x ∉ N₀ ⇒ x ∈ W' 0 (idx0 x).
  have h_base : ∀ x, x ∉ N₀ → x ∈ W' 0 (idx0 x) := by
    intro x hxN₀
    -- x ∉ N: get a witness in F_x.
    have hxN : x ∉ N := fun h => hxN₀ (Set.mem_union_left _ h)
    obtain ⟨w, hxw⟩ := hF_ne_offN x hxN
    -- Density: pick j with dist (d j) w < δ 1.
    obtain ⟨j, hj⟩ := hd_dense_rad w (δ 1) (hδ_pos 1)
    -- This shows x ∈ W 0 j: take w ∈ closedBall (d j) (δ 1) and (x, w) ∈ F.
    have hxWj : x ∈ W 0 j := by
      refine ⟨w, ?_, hxw⟩
      rw [Metric.mem_closedBall]
      exact hj.le
    have hxW'j : x ∈ W' 0 j := hW'_sub 0 j hxWj
    -- Hence Q0 x j holds via Or.inl.
    have hQ0j : Q0 x j := Or.inl hxW'j
    -- Goal: x ∈ W' 0 (idx0 x). Use Nat.find_spec.
    -- Since `idx0 x = Nat.find (hQ0_ex x)`, split cases to establish `Q0 x (idx0 x)`.
    have h_spec : Q0 x (idx0 x) := Nat.find_spec (hQ0_ex x)
    rcases h_spec with h_left | ⟨_, h_no⟩
    · exact h_left
    · exact absurd hxW'j (h_no j)
  -- Recursive step: invariant at level k ⇒ invariant at level k+1.
  -- For x ∉ N₀, x ∈ W' k (idx k x) (with idx interpreted recursively).
  -- Define `idx k x` recursively.
  let idx : ℕ → α → ℕ := fun k => Nat.rec (motive := fun _ => α → ℕ)
      idx0 (fun k _ x => idxStep k (b k x) x) k
  -- The b function equals d ∘ idx.
  have hb_eq_d_idx : ∀ k x, b k x = d (idx k x) := by
    intro k x
    induction k with
    | zero => rfl
    | succ k _ => rfl
  -- Invariant: for x ∉ N₀, x ∈ W' k (idx k x).
  have h_inv : ∀ k x, x ∉ N₀ → x ∈ W' k (idx k x) := by
    intro k x hxN₀
    induction k with
    | zero => exact h_base x hxN₀
    | succ k ih =>
      -- We have x ∈ W k (idx k x) (using h_strip_E + ih), hence a witness
      -- w_k ∈ closedBall (d (idx k x)) (δ (k+1)) with (x, w_k) ∈ F.
      have hxW_k : x ∈ W k (idx k x) := h_strip_E x hxN₀ k (idx k x) ih
      obtain ⟨w_k, hw_k_ball, hxw_k⟩ := hxW_k
      have hw_k_dist : dist w_k (d (idx k x)) ≤ δ (k+1) := by
        rw [Metric.mem_closedBall] at hw_k_ball
        exact hw_k_ball
      -- Density: pick j with dist w_k (d j) < δ (k+2).
      obtain ⟨j, hj⟩ := hd_dense_rad w_k (δ (k+2)) (hδ_pos _)
      have hj' : dist (d j) w_k < δ (k+2) := by rw [dist_comm]; exact hj
      -- Verify j satisfies the R predicate (with y = b k x = d (idx k x)).
      -- (a) dist (d j) (b k x) ≤ δ k.
      have hdj_dist : dist (d j) (b k x) ≤ δ k := by
        rw [hb_eq_d_idx k x]
        calc dist (d j) (d (idx k x))
            ≤ dist (d j) w_k + dist w_k (d (idx k x)) := dist_triangle _ _ _
          _ ≤ δ (k+2) + δ (k+1) := add_le_add hj'.le hw_k_dist
          _ ≤ δ k := by
              change (1 / 2 : ℝ)^(k+2) + (1 / 2 : ℝ)^(k+1) ≤ (1 / 2 : ℝ)^k
              -- (1/2)^(k+2) + (1/2)^(k+1) = (1/2)^k · (1/4 + 1/2) = 3/4 · (1/2)^k
              have hk : (0 : ℝ) ≤ (1 / 2 : ℝ)^k := pow_nonneg (by norm_num) _
              have h1 : (1 / 2 : ℝ)^(k+2) = (1 / 2)^k * (1/4) := by
                rw [pow_add]; ring
              have h2 : (1 / 2 : ℝ)^(k+1) = (1 / 2)^k * (1/2) := by
                rw [pow_add]; ring
              rw [h1, h2]
              nlinarith [hk]
      -- (b) x ∈ W' (k+1) j: w_k is a witness with dist w_k (d j) ≤ δ (k+2),
      --     which is the radius for level k+1's W definition.
      have hxWk1_j : x ∈ W (k+1) j := by
        refine ⟨w_k, ?_, hxw_k⟩
        rw [Metric.mem_closedBall]
        exact hj.le
      have hxW'k1_j : x ∈ W' (k+1) j := hW'_sub (k+1) j hxWk1_j
      -- Hence R k (b k x) x j holds via Or.inl.
      have hRj : R k (b k x) x j := Or.inl ⟨hdj_dist, hxW'k1_j⟩
      -- Goal: x ∈ W' (k+1) (idxStep k (b k x) x).
      change x ∈ W' (k+1) (idxStep k (b k x) x)
      have h_spec : R k (b k x) x (idxStep k (b k x) x) :=
        Nat.find_spec (hR_ex k (b k x) x)
      rcases h_spec with ⟨_, h_W'⟩ | ⟨_, h_no⟩
      · exact h_W'
      · exact absurd ⟨hdj_dist, hxW'k1_j⟩ (h_no j)
  ----------------------------------------------------------------------------
  -- Establish the geometric bounds and assemble the selector.
  ----------------------------------------------------------------------------
  -- For x ∉ N₀, the fiber witness at level k satisfies dist b' (b k x) ≤ (1/2)^k.
  have h_witness : ∀ x, x ∉ N₀ → ∀ k, ∃ b' : β, dist b' (b k x) ≤ (1/2 : ℝ)^k ∧ (x, b') ∈ F := by
    intro x hxN₀ k
    -- x ∈ W' k (idx k x) ⇒ x ∈ W k (idx k x) (since x ∉ E k).
    have hxW' : x ∈ W' k (idx k x) := h_inv k x hxN₀
    have hxW : x ∈ W k (idx k x) := h_strip_E x hxN₀ k (idx k x) hxW'
    obtain ⟨w, hw_ball, hxw⟩ := hxW
    refine ⟨w, ?_, hxw⟩
    rw [Metric.mem_closedBall] at hw_ball
    rw [hb_eq_d_idx k x]
    -- dist w (d (idx k x)) ≤ δ (k+1) = (1/2)^(k+1) ≤ (1/2)^k.
    calc dist w (d (idx k x)) ≤ δ (k+1) := hw_ball
      _ ≤ δ k := by
          change (1 / 2 : ℝ)^(k+1) ≤ (1 / 2 : ℝ)^k
          have : (1 / 2 : ℝ)^(k+1) = (1/2)^k * (1/2) := by rw [pow_add]; ring
          rw [this]
          have hk : (0 : ℝ) ≤ (1 / 2 : ℝ)^k := pow_nonneg (by norm_num) _
          nlinarith
  -- For x ∉ N₀, consecutive distance bound: dist (b k x) (b (k+1) x) ≤ (1/2)^k.
  have h_consecutive : ∀ x, x ∉ N₀ → ∀ k,
      dist (b k x) (b (k+1) x) ≤ (1/2 : ℝ)^k := by
    intro x hxN₀ k
    -- b (k+1) x = d (idxStep k (b k x) x); the R predicate at that index gives
    -- dist (d (idxStep …)) (b k x) ≤ δ k OR the no-existence branch.
    have h_spec : R k (b k x) x (idxStep k (b k x) x) :=
      Nat.find_spec (hR_ex k (b k x) x)
    -- The invariant at level k+1 says R has a real witness, so the no-existence
    -- branch can't be active. Use this to extract the inequality.
    have hxW'k1 : x ∈ W' (k+1) (idx (k+1) x) := h_inv (k+1) x hxN₀
    -- idx (k+1) x = idxStep k (b k x) x (by Nat.rec definition).
    have h_idx_step : idx (k+1) x = idxStep k (b k x) x := rfl
    rcases h_spec with ⟨h_dist, _⟩ | ⟨_, h_no⟩
    · -- d (idxStep …) is close to b k x by δ k.
      change dist (b k x) (d (idxStep k (b k x) x)) ≤ δ k
      rw [dist_comm]; exact h_dist
    · -- Contradiction: h_no says no j satisfies R's left disjunct, but we
      -- proved one in the invariant (via h_inv).
      -- Concretely: from the invariant we know x ∈ W' (k+1) j for some j; but
      -- more carefully, h_inv's induction gave a specific j (via density).
      -- The R predicate's left disjunct at *that* j holds.
      --
      -- Re-derive the witness from the invariant at level k.
      exfalso
      -- Get the W k witness w_k from invariant at level k.
      have hxW_k : x ∈ W k (idx k x) :=
        h_strip_E x hxN₀ k (idx k x) (h_inv k x hxN₀)
      obtain ⟨w_k, hw_k_ball, hxw_k⟩ := hxW_k
      have hw_k_dist : dist w_k (d (idx k x)) ≤ δ (k+1) := by
        rw [Metric.mem_closedBall] at hw_k_ball; exact hw_k_ball
      obtain ⟨j, hj⟩ := hd_dense_rad w_k (δ (k+2)) (hδ_pos _)
      have hj' : dist (d j) w_k < δ (k+2) := by rw [dist_comm]; exact hj
      have hdj_dist : dist (d j) (b k x) ≤ δ k := by
        rw [hb_eq_d_idx k x]
        calc dist (d j) (d (idx k x))
            ≤ dist (d j) w_k + dist w_k (d (idx k x)) := dist_triangle _ _ _
          _ ≤ δ (k+2) + δ (k+1) := add_le_add hj'.le hw_k_dist
          _ ≤ δ k := by
              change (1 / 2 : ℝ)^(k+2) + (1 / 2 : ℝ)^(k+1) ≤ (1 / 2 : ℝ)^k
              have hk : (0 : ℝ) ≤ (1 / 2 : ℝ)^k := pow_nonneg (by norm_num) _
              have h1 : (1 / 2 : ℝ)^(k+2) = (1 / 2)^k * (1/4) := by rw [pow_add]; ring
              have h2 : (1 / 2 : ℝ)^(k+1) = (1 / 2)^k * (1/2) := by rw [pow_add]; ring
              rw [h1, h2]; nlinarith [hk]
      have hxWk1_j : x ∈ W (k+1) j := by
        refine ⟨w_k, ?_, hxw_k⟩
        rw [Metric.mem_closedBall]; exact hj.le
      have hxW'k1_j : x ∈ W' (k+1) j := hW'_sub (k+1) j hxWk1_j
      exact h_no j ⟨hdj_dist, hxW'k1_j⟩
  ----------------------------------------------------------------------------
  -- ASSEMBLY
  ----------------------------------------------------------------------------
  refine ⟨N₀, b, hN₀_meas, hN₀_null, hN_subset_N₀, hb_meas, h_consecutive, h_witness⟩

/-- **Closed-graph Cauchy selector core**.

The Cauchy nested-ball construction at the heart of the Jankov-von Neumann /
Aumann measurable selection theorem, specialised to the case where the graph
`F` is **closed** (not just Borel) in `α × β` with respect to a given Polish
topology on `β`. Given non-empty fibers off an m-null set `N`, this lemma
produces a measurable selector `s : α → β` with `(x, s x) ∈ F` for every
`x` outside a measurable m-null superset `N₀ ⊇ N`.

**Construction (Kechris §18.A nested-ball Cauchy)**:
the recursive index construction is lifted as `cauchy_selector_inductive_step`
(above). The body of this lemma is the limit + closedness argument: extract
the Cauchy sequence from the sub-step, take its limit via metric completeness,
and use `IsClosed F` to conclude that the limit `(x, s x)` lies in `F`.

The hypotheses:
- `F`, `m`, `N`, `hF_closed`, `hN_meas`, `hN_null`, `hF_ne_offN` —
  closed Borel graph in `α × β` plus per-x non-emptiness off `N`.
- structural typeclasses: `α` and `β` are both Polish with the
  Borel measurable structure (so `IsClosed F` is well-formed and Borel
  measurability of the constructed selector is meaningful). -/
private theorem aumann_selector_closed_graph_polish
    {α β : Type*}
    [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    [Nonempty β]
    (F : Set (α × β)) (hF_meas : MeasurableSet F) (hF_closed : IsClosed F)
    (m : Measure α) [SFinite m]
    (N : Set α) (hN_meas : MeasurableSet N) (hN_null : m N = 0)
    (hF_ne_offN : ∀ x ∉ N, ∃ b : β, (x, b) ∈ F) :
    ∃ N₀ : Set α, MeasurableSet N₀ ∧ m N₀ = 0 ∧ N ⊆ N₀ ∧
      ∃ s : α → β, Measurable s ∧ ∀ x ∉ N₀, (x, s x) ∈ F := by
  classical
  -- Endow β with a complete metric compatible with its Polish topology.
  letI := upgradeIsCompletelyMetrizable β
  -- Invoke the recursive Cauchy-index sub-step to obtain a measurable sequence
  -- `b k : α → β` whose values are 2⁻ᵏ-close to the fiber `F_x` and Cauchy
  -- with rate 2⁻ᵏ off a measurable m-null set `N₀ ⊇ N`.
  obtain ⟨N₀, b, hN₀_meas, hN₀_null, hN_sub, hb_meas, hb_cauchy, hb_witness⟩ :=
    cauchy_selector_inductive_step F hF_meas m N hN_meas hN_null hF_ne_offN
  -- The arbitrary fallback value on `N₀`: pick any element of `β`.
  let b₀ : β := Classical.arbitrary β
  -- Off `N₀`, the sequence `(b k x)` is Cauchy by `hb_cauchy` with summable
  -- geometric rate `(1/2)^k`. Define `s x` as its limit (using a measurable
  -- limit construction); on `N₀` fall back to `b₀`.
  -- We use `cauchySeq_tendsto_of_complete` after extracting cauchy-ness.
  have hb_isCauchy_off : ∀ x ∉ N₀, CauchySeq (fun k => b k x) := by
    intro x hxN₀
    refine Metric.cauchySeq_iff'.2 ?_
    intro ε hε
    -- Geometric series: pick K with (1/2)^K ≤ ε/2 (so the tail telescoping
    -- sums to ≤ (1/2)^K * 2 ≤ ε).
    obtain ⟨K, hK⟩ : ∃ K : ℕ, (1 / 2 : ℝ) ^ K < ε / 2 := by
      have htd : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hpos : (0 : ℝ) < ε / 2 := by positivity
      rw [Metric.tendsto_atTop] at htd
      obtain ⟨K, hK⟩ := htd (ε / 2) hpos
      refine ⟨K, ?_⟩
      have := hK K (le_refl K)
      simpa [Real.dist_eq, abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) K)]
        using this
    refine ⟨K, fun n hn => ?_⟩
    -- Telescoping: dist (b K x) (b n x) ≤ Σ_{k=K}^{n-1} dist (b k x) (b (k+1) x)
    -- ≤ Σ_{k=K}^{n-1} (1/2)^k ≤ 2 · (1/2)^K.
    have h_tel : dist (b K x) (b n x) ≤ ∑ k ∈ Finset.Ico K n, (1 / 2 : ℝ) ^ k := by
      have := dist_le_Ico_sum_dist (f := fun k => b k x) (m := K) (n := n) hn
      refine this.trans ?_
      apply Finset.sum_le_sum
      intro k _
      exact hb_cauchy x hxN₀ k
    have h_geom : ∑ k ∈ Finset.Ico K n, (1 / 2 : ℝ) ^ k
        ≤ 2 * (1 / 2 : ℝ) ^ K := by
      -- Use `geom_series_def` style: Σ_{k=K}^{n-1} r^k ≤ r^K / (1 - r) for r=1/2.
      have hr : (1 / 2 : ℝ) < 1 := by norm_num
      have hrnn : (0 : ℝ) ≤ 1 / 2 := by norm_num
      -- Shift index: Σ_{k=K}^{n-1} (1/2)^k = (1/2)^K · Σ_{j=0}^{n-K-1} (1/2)^j
      -- and Σ_{j=0}^{n-K-1} (1/2)^j ≤ 2.
      have hshift :
          ∑ k ∈ Finset.Ico K n, (1 / 2 : ℝ) ^ k
            = (1 / 2 : ℝ) ^ K *
              ∑ j ∈ Finset.range (n - K), (1 / 2 : ℝ) ^ j := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [pow_add, mul_comm]
      rw [hshift]
      have hsum_le : ∑ j ∈ Finset.range (n - K), (1 / 2 : ℝ) ^ j ≤ 2 := by
        have hgeom : ∑ j ∈ Finset.range (n - K), (1 / 2 : ℝ) ^ j
            = (1 - (1 / 2 : ℝ) ^ (n - K)) / (1 - 1 / 2) := by
          rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
          field_simp; ring
        rw [hgeom]
        have hpos_pow : 0 ≤ (1 / 2 : ℝ) ^ (n - K) := pow_nonneg hrnn _
        have hle_pow : (1 / 2 : ℝ) ^ (n - K) ≤ 1 :=
          pow_le_one₀ hrnn (le_of_lt hr)
        have h2 : (0 : ℝ) < 1 - 1 / 2 := by norm_num
        rw [div_le_iff₀ h2]
        linarith
      have hpos_powK : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := pow_nonneg hrnn _
      nlinarith [hpos_powK]
    have h1 : dist (b K x) (b n x) ≤ 2 * (1 / 2 : ℝ) ^ K := h_tel.trans h_geom
    have h2 : 2 * (1 / 2 : ℝ) ^ K < ε := by linarith
    rw [dist_comm]
    exact h1.trans_lt h2
  -- Define `s x` as `Classical.epsilon` of the limit predicate; on `N₀` fall
  -- back to `b₀`. Measurability of the limit comes from
  -- `measurable_of_tendsto_metrizable` on the modified sequence.
  -- Modify `b k` to converge everywhere: replace `b k x` with `b₀` on `N₀`.
  set b' : ℕ → α → β := fun k x => if x ∈ N₀ then b₀ else b k x with hb'_def
  have hb'_meas : ∀ k, Measurable (b' k) := by
    intro k
    refine Measurable.ite hN₀_meas measurable_const (hb_meas k)
  have hb'_cauchy : ∀ x, CauchySeq (fun k => b' k x) := by
    intro x
    by_cases hx : x ∈ N₀
    · -- On N₀, the sequence is constant b₀.
      have : (fun k => b' k x) = fun _ => b₀ := by
        funext k; simp [b', hx]
      rw [this]
      exact cauchySeq_const _
    · have : (fun k => b' k x) = fun k => b k x := by
        funext k; simp [b', hx]
      rw [this]
      exact hb_isCauchy_off x hx
  -- Define `s` as the limit.
  set s : α → β := fun x => Classical.choose (cauchySeq_tendsto_of_complete (hb'_cauchy x))
    with hs_def
  have hs_lim : ∀ x, Filter.Tendsto (fun k => b' k x) Filter.atTop (nhds (s x)) := by
    intro x
    exact Classical.choose_spec (cauchySeq_tendsto_of_complete (hb'_cauchy x))
  have hs_meas : Measurable s := by
    refine measurable_of_tendsto_metrizable (f := b') (g := s) hb'_meas ?_
    exact tendsto_pi_nhds.mpr hs_lim
  -- Closedness of F: for x ∉ N₀, the witnesses b' k x have b''_k close to F_x,
  -- and the limit lies in F_x.
  refine ⟨N₀, hN₀_meas, hN₀_null, hN_sub, s, hs_meas, ?_⟩
  intro x hxN₀
  -- Construct a sequence of actual F-points converging to s x.
  -- For each k, pick b'' k x ∈ ball (b k x) (1/2)^k with (x, b'' k x) ∈ F
  -- (from `hb_witness`).
  choose b'' hb''_dist hb''_inF using hb_witness x hxN₀
  -- The sequence (b'' k x) also converges to s x because
  -- dist (b'' k x) (s x) ≤ dist (b'' k x) (b k x) + dist (b k x) (s x).
  have hb_tendsto : Filter.Tendsto (fun k => b k x) Filter.atTop (nhds (s x)) := by
    have := hs_lim x
    have heq : (fun k => b' k x) = fun k => b k x := by
      funext k; simp [b', hxN₀]
    rw [heq] at this
    exact this
  have hb''_tendsto : Filter.Tendsto (fun k => b'' k) Filter.atTop (nhds (s x)) := by
    rw [Metric.tendsto_atTop] at hb_tendsto ⊢
    intro ε hε
    -- pick K so (1/2)^K ≤ ε/2 and dist (b k x) (s x) ≤ ε/2 for k ≥ K'.
    obtain ⟨K₁, hK₁⟩ := hb_tendsto (ε / 2) (by linarith)
    have hpow_tendsto : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    rw [Metric.tendsto_atTop] at hpow_tendsto
    obtain ⟨K₂, hK₂⟩ := hpow_tendsto (ε / 2) (by linarith)
    refine ⟨max K₁ K₂, fun n hn => ?_⟩
    have hn1 : K₁ ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : K₂ ≤ n := le_trans (le_max_right _ _) hn
    have h1 : dist (b n x) (s x) < ε / 2 := hK₁ n hn1
    have h2 : dist (b'' n) (b n x) ≤ (1 / 2 : ℝ) ^ n := hb''_dist n
    have h2' : (1 / 2 : ℝ) ^ n < ε / 2 := by
      have := hK₂ n hn2
      have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n :=
        pow_nonneg (by norm_num) _
      simpa [Real.dist_eq, abs_of_nonneg hpos] using this
    calc dist (b'' n) (s x)
        ≤ dist (b'' n) (b n x) + dist (b n x) (s x) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  -- Since F is closed and each (x, b'' k) ∈ F, the limit (x, s x) ∈ F.
  have hpair_tendsto :
      Filter.Tendsto (fun k => (x, b'' k)) Filter.atTop (nhds (x, s x)) := by
    refine Filter.Tendsto.prodMk_nhds tendsto_const_nhds hb''_tendsto
  have : (x, s x) ∈ closure F :=
    mem_closure_of_tendsto hpair_tendsto (Filter.Eventually.of_forall (fun k => hb''_inF k))
  rwa [hF_closed.closure_eq] at this

/-! ### Single-space refinement on α × β

Closing an arbitrary Borel graph cannot be done by *factor-wise* Polish
refinement (a Cantor off-diagonal counter-example obstructs it). The approach
here refines the topology on the **product** `α × β` directly as a single
Polish space, lifts the closed-graph Aumann selector inside that refined
topology, then projects back to `α` via an m.a.e. fiber identity.

The chain consists of:

* `polishRefinement_of_measurable_singleSpace` — single-space Polish
  refinement on `α × β` making a Borel set `G'` clopen while preserving the
  Borel σ-algebra, by `MeasurableSet.isClopenable`.
* `aumann_suslin_scheme_cauchy` — composition of the single-space refinement,
  the closed-graph selector, and the fiber identity.
* `aumann_selector_closed_graph_polish_singleSpace` — closed-graph
  Aumann selection where the **graph lives in α × γ** and γ = α × β is
  treated as a single Polish target, with **m.a.e. fiber identity** on
  the first coordinate.
* `cauchy_selector_inductive_step_singleSpace` — inner nested-ball
  recursion when the target is a single Polish space γ (no factor split).
* `proj_identity_mae_of_closed_graph` — given a measurable selector
  `t : α → α × β` whose graph lies in a closed graph `Ĝ ⊆ α × (α × β)`
  whose fibers over `x ∈ α` are contained in `{x} × β`, the
  first-coordinate projection `(t x).1 = x` holds m-a.e.
* `nullMeasurableSet_image_fst_of_borel` — analytic-projection bridge:
  `Prod.fst '' G'` is null-measurable in α for Borel `G' ⊆ α × β`
  (specialisation of `analyticSet_image` + Choquet).
* `coordProj_snd_measurable_singleSpace` — second-coordinate-projection
  measurability: the second factor of a measurable map into `α × β` is
  itself measurable.

The supporting facts: `MeasurableSet.isClopenable` works on a single Polish
space (no factor structure needed); the m.a.e. fiber identity is provable from
analytic-set bookkeeping; and the first-coordinate projection of a measurable
map into `α × β` remains measurable, so the `α → β` selector falls out by
composing `t : α → α × β` with `Prod.snd`.
-/

/-- **Single-space Polish refinement closing a Borel graph**.

Given a Borel set `G' ⊆ α × β` (both α and β Polish, with their Borel
σ-algebras), there exists a Polish topology `τ'` on **the product** `α × β`
(treated as a single space) such that:

* `τ'` is finer than the original product topology `tα.prod tβ`;
* The Borel σ-algebra under `τ'` coincides with the original product
  measurable structure on `α × β`;
* `G'` is **clopen** under `τ'`.

This follows by applying Mathlib's `MeasurableSet.isClopenable` to the single
Polish space `α × β` (a product of Polish spaces is Polish
automatically; product `BorelSpace` instance is auto-derived in Mathlib).

Doing this **factor-wise** would be false for arbitrary Borel `G'` (Cantor
off-diagonal counter-example). The single-space version is correct via
`MeasurableSet.isClopenable` directly.

The hypotheses:
- `G'`, `hG'_meas` — the Borel graph and its measurability.
- structural typeclasses on `α` and `β` (Polish + Borel) —
  needed for the Polish-product instance and to invoke `MeasurableSet.isClopenable`. -/
private theorem polishRefinement_of_measurable_singleSpace
    {α β : Type*}
    [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    (G' : Set (α × β)) (hG'_meas : MeasurableSet G') :
    ∃ τ' : TopologicalSpace (α × β),
      τ' ≤ (instTopologicalSpaceProd : TopologicalSpace (α × β)) ∧
      @PolishSpace (α × β) τ' ∧
      @borel (α × β) τ' = (Prod.instMeasurableSpace : MeasurableSpace (α × β)) ∧
      @IsClosed (α × β) τ' G' ∧
      @IsOpen (α × β) τ' G' := by
  -- Apply `MeasurableSet.isClopenable` on the single Polish space `α × β`
  -- (Polish-product is Polish; product `BorelSpace` is auto-derived from
  -- second-countability of Polish factors). Gives a finer Polish topology `τ'`
  -- making `G'` clopen.
  -- `Prod.borelSpace` fires because Polish implies `SecondCountableTopology` on
  -- each factor, supplying `SecondCountableTopologyEither α β`.
  haveI hBorel : BorelSpace (α × β) := Prod.borelSpace
  -- Capture the original PolishSpace instance BEFORE `obtain` introduces `τ'`
  -- into the context — otherwise `inferInstance` for `PolishSpace (α × β)`
  -- would resolve to `τ'_polish` (closest-binder shadowing).
  have hOrigPolish : @PolishSpace (α × β) instTopologicalSpaceProd := inferInstance
  obtain ⟨τ', τ'_le, τ'_polish, hclosed, hopen⟩ := hG'_meas.isClopenable
  refine ⟨τ', τ'_le, τ'_polish, ?_, hclosed, hopen⟩
  -- Borel preservation: `borel τ' = borel (instTopologicalSpaceProd)
  -- = Prod.instMeasurableSpace`. First equality from `borel_eq_borel_of_le`,
  -- second from `BorelSpace.measurable_eq`.
  have hborel_eq : @borel (α × β) τ' = @borel (α × β) instTopologicalSpaceProd :=
    MeasureTheory.borel_eq_borel_of_le (γ := α × β) τ'_polish hOrigPolish τ'_le
  exact hborel_eq.trans hBorel.measurable_eq.symm

/-- **Analytic-image null-measurability of the first projection**.

For a Borel set `G' ⊆ α × β` on standard-Borel α and Polish β,
`Prod.fst '' G'` is `NullMeasurableSet` for any σ-finite measure on α via
analytic-image (`MeasurableSet.analyticSet_image`) + Choquet capacitability
(`AnalyticSet.statLean_nullMeasurableSet`).

The hypotheses:
- `G'`, `hG'_meas`, `m` — the Borel graph, measure, and reference.
- standard-Borel α + Polish β — required to use
  `MeasurableSet.analyticSet_image`. -/
private theorem nullMeasurableSet_image_fst_of_borel
    {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [PolishSpace β] [BorelSpace β]
    (G' : Set (α × β)) (hG'_meas : MeasurableSet G')
    (m : Measure α) [SFinite m] :
    NullMeasurableSet (Prod.fst '' G') m := by
  -- Endow `α` with the canonical Polish topology compatible with its
  -- standard-Borel structure. This gives `TopologicalSpace α`, `PolishSpace α`,
  -- `BorelSpace α` (hence `OpensMeasurableSpace α`) and `SecondCountableTopology α`.
  letI : UpgradedStandardBorel α := upgradeStandardBorel α
  -- `Prod.fst : α × β → α` is measurable, so the image of the measurable set
  -- `G'` under it is an analytic subset of `α`.
  have hAnalytic : AnalyticSet (Prod.fst '' G') :=
    hG'_meas.analyticSet_image measurable_fst
  -- Analytic sets in a Polish space are null-measurable for any `SFinite` measure
  -- (Choquet capacitability, `AnalyticSet.statLean_nullMeasurableSet`).
  exact hAnalytic.statLean_nullMeasurableSet m

/-- **Second-coordinate projection of a measurable map into α × β is measurable**.

Given a measurable `t : α → α × β`, the composition `fun x => (t x).2` is a
measurable map `α → β`, via `measurable_snd.comp t_meas`. -/
private theorem coordProj_snd_measurable_singleSpace
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (t : α → α × β) (ht : Measurable t) :
    Measurable (fun x => (t x).2) :=
  measurable_snd.comp ht

/-- **Cauchy nested-ball selector for a single Polish target γ**.

The single-space analogue of `cauchy_selector_inductive_step`. Given a Borel
graph `Ĝ ⊆ α × γ` whose fibers over `α \ N` are non-empty, this produces:
* a measurable sequence `b : ℕ → α → γ` taking values in the dense range
  of `denseSeq γ`,
* a measurable m-null superset `N₀ ⊇ N`,

such that off `N₀`, the sequence `b k x` is Cauchy with successive distances
controlled by `2^{-k}`, and each ball `closedBall (b k x) 2^{-k}` meets the
fiber `Ĝ_x := {c : γ | (x, c) ∈ Ĝ}`.

Difference from `cauchy_selector_inductive_step`: the target type `γ` is
a single Polish space (no factor split), and the resulting selector takes
values in `γ` (e.g. `α × β` when γ = α × β).

The hypotheses:
- `Ĝ`, `hĜ_meas`, `m`, `N`, `hN_meas`, `hN_null`, `hĜ_ne_offN`.
- structural typeclasses: `α` Polish, `γ` complete metric +
  second-countable + Polish. -/
private theorem cauchy_selector_inductive_step_singleSpace
    {α γ : Type*}
    [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    [MetricSpace γ] [CompleteSpace γ] [SecondCountableTopology γ]
    [MeasurableSpace γ] [BorelSpace γ] [Nonempty γ]
    (Ĝ : Set (α × γ)) (hĜ_meas : MeasurableSet Ĝ)
    (m : Measure α) [SFinite m]
    (N : Set α) (hN_meas : MeasurableSet N) (hN_null : m N = 0)
    (hĜ_ne_offN : ∀ x ∉ N, ∃ c : γ, (x, c) ∈ Ĝ) :
    ∃ (N₀ : Set α) (b : ℕ → α → γ),
      MeasurableSet N₀ ∧ m N₀ = 0 ∧ N ⊆ N₀ ∧
      (∀ k, Measurable (b k)) ∧
      (∀ x ∉ N₀, ∀ k, dist (b k x) (b (k+1) x) ≤ (1 / 2 : ℝ)^k) ∧
      (∀ x ∉ N₀, ∀ k, ∃ c' : γ, dist c' (b k x) ≤ (1 / 2 : ℝ)^k ∧ (x, c') ∈ Ĝ) := by
  classical
  -- `SeparableSpace γ` is automatic from `SecondCountableTopology γ`; combined with
  -- `MetricSpace + CompleteSpace + SecondCountableTopology` we get `PolishSpace γ`.
  haveI : SeparableSpace γ := inferInstance
  haveI : PolishSpace γ := inferInstance
  -- The dense sequence in `γ`.
  set d : ℕ → γ := TopologicalSpace.denseSeq γ with hd_def
  have hd_dense : DenseRange d := TopologicalSpace.denseRange_denseSeq γ
  -- Radius schedule: `δ k := (1/2)^k`. The "fiber-witness slack" at level `k`
  -- is `δ (k+1) = (1/2)^(k+1) = δ k / 2`, half of the conclusion's `(1/2)^k`.
  set δ : ℕ → ℝ := fun k => (1 / 2 : ℝ)^k with hδ_def
  have hδ_pos : ∀ k, 0 < δ k := fun k => by
    change (0 : ℝ) < (1 / 2 : ℝ)^k; positivity
  -- A default value in γ.
  let c₀ : γ := Classical.arbitrary γ
  ----------------------------------------------------------------------------
  -- Per-level/index building block: the fiber-witness predicate as
  -- a measurable subset of `α` (modulo a null set).
  --
  -- For each pair `(k, i)`, define
  --   `W k i = {x | ∃ w ∈ closedBall (d i) (δ (k+1)), (x, w) ∈ Ĝ}`.
  -- This is null-measurable in `α` by `nullMeasurableSet_proj_of_borel_basis`
  -- (since `[PolishSpace α]` + `[BorelSpace α]` auto-derives `[StandardBorelSpace α]`).
  ----------------------------------------------------------------------------
  let W : ℕ → ℕ → Set α := fun k i =>
    {x : α | ∃ w ∈ Metric.closedBall (d i) (δ (k+1)), (x, w) ∈ Ĝ}
  have hW_NMS : ∀ k i, NullMeasurableSet (W k i) m := by
    intro k i
    have hball_meas : MeasurableSet (Metric.closedBall (d i) (δ (k+1))) :=
      (Metric.isClosed_closedBall (x := d i) (ε := δ (k+1))).measurableSet
    exact nullMeasurableSet_proj_of_borel_basis Ĝ hĜ_meas
      (Metric.closedBall (d i) (δ (k+1))) hball_meas m
  -- Replace each `W k i` with a measurable superset `W' k i ⊇ W k i`,
  -- `W' k i =ᵐ[m] W k i`.
  choose W' hW'_sub hW'_meas hW'_ae using
    fun (k i : ℕ) =>
      NullMeasurableSet.exists_measurable_superset_ae_eq (hW_NMS k i)
  -- The level-k exception set `E k := ⋃ i, (W' k i \ W k i)`.
  let E : ℕ → Set α := fun k => ⋃ i, W' k i \ W k i
  have hE_null : ∀ k, m (E k) = 0 := by
    intro k
    refine measure_iUnion_null fun i => ?_
    have hae_mem : ∀ᵐ x ∂m, x ∈ W' k i ↔ x ∈ W k i :=
      (hW'_ae k i).mem_iff
    have hdiff : (W' k i \ W k i) =ᵐ[m] (∅ : Set α) := by
      refine Filter.eventuallyEq_set.mpr ?_
      filter_upwards [hae_mem] with x hx
      constructor
      · rintro ⟨hxW', hxnW⟩
        exact (hxnW (hx.mp hxW')).elim
      · intro hxE
        exact hxE.elim
    calc m (W' k i \ W k i) = m (∅ : Set α) := measure_congr hdiff
      _ = 0 := measure_empty
  ----------------------------------------------------------------------------
  -- Build `b : ℕ → α → γ` by recursion, together with measurable index
  -- functions `idx k : α → ℕ` with `b k x = d (idx k x)`.
  ----------------------------------------------------------------------------
  let Q0 : α → ℕ → Prop := fun x i => x ∈ W' 0 i ∨ (i = 0 ∧ ∀ j, x ∉ W' 0 j)
  have hQ0_ex : ∀ x, ∃ i, Q0 x i := by
    intro x
    by_cases h : ∃ j, x ∈ W' 0 j
    · obtain ⟨j, hj⟩ := h; exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr ⟨rfl, fun j hxj => h ⟨j, hxj⟩⟩⟩
  have hQ0_meas : ∀ i, MeasurableSet {x | Q0 x i} := by
    intro i
    by_cases hi : i = 0
    · subst hi
      have : {x | Q0 x 0} = W' 0 0 ∪ (⋂ j, (W' 0 j)ᶜ) := by
        ext x; simp [Q0]
      rw [this]
      exact (hW'_meas 0 0).union (MeasurableSet.iInter fun j => (hW'_meas 0 j).compl)
    · have : {x | Q0 x i} = W' 0 i := by
        ext x; simp [Q0, hi]
      rw [this]; exact hW'_meas 0 i
  let idx0 : α → ℕ := fun x => Nat.find (hQ0_ex x)
  have hidx0_meas : Measurable idx0 := measurable_find hQ0_ex hQ0_meas
  -- denseSeq is measurable as a function from ℕ (discrete) into γ.
  have hd_meas : Measurable d := measurable_from_nat
  let b0 : α → γ := fun x => d (idx0 x)
  have hb0_meas : Measurable b0 := hd_meas.comp hidx0_meas
  -- Step predicate at level `k+1` given previous value `y : γ` and index `i`.
  let R : ℕ → γ → α → ℕ → Prop := fun k y x i =>
    (dist (d i) y ≤ δ k ∧ x ∈ W' (k+1) i) ∨
      (i = 0 ∧ ∀ j, ¬ (dist (d j) y ≤ δ k ∧ x ∈ W' (k+1) j))
  have hR_ex : ∀ k y x, ∃ i, R k y x i := by
    intro k y x
    by_cases h : ∃ j, dist (d j) y ≤ δ k ∧ x ∈ W' (k+1) j
    · obtain ⟨j, hj⟩ := h; exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr ⟨rfl, fun j hj => h ⟨j, hj⟩⟩⟩
  -- Joint measurability of `R k` in `(y, x)` for each `i`.
  have hR_meas_joint : ∀ k i,
      MeasurableSet {p : γ × α | R k p.1 p.2 i} := by
    intro k i
    have hAB : ∀ j, MeasurableSet
        {p : γ × α | dist (d j) p.1 ≤ δ k ∧ p.2 ∈ W' (k+1) j} := by
      intro j
      have hdist : Measurable (fun p : γ × α => dist (d j) p.1) :=
        (measurable_const.dist measurable_id).comp measurable_fst
      have h_le : MeasurableSet {p : γ × α | dist (d j) p.1 ≤ δ k} :=
        hdist measurableSet_Iic
      have hW'_pull : MeasurableSet {p : γ × α | p.2 ∈ W' (k+1) j} :=
        measurable_snd (hW'_meas (k+1) j)
      exact h_le.inter hW'_pull
    by_cases hi : i = 0
    · subst hi
      have : {p : γ × α | R k p.1 p.2 0}
          = {p : γ × α | dist (d 0) p.1 ≤ δ k ∧ p.2 ∈ W' (k+1) 0} ∪
            (⋂ j, ({p : γ × α | dist (d j) p.1 ≤ δ k ∧ p.2 ∈ W' (k+1) j})ᶜ) := by
        ext p; simp [R]
      rw [this]
      exact (hAB 0).union (MeasurableSet.iInter fun j => (hAB j).compl)
    · have : {p : γ × α | R k p.1 p.2 i}
          = {p : γ × α | dist (d i) p.1 ≤ δ k ∧ p.2 ∈ W' (k+1) i} := by
        ext p; simp [R, hi]
      rw [this]; exact hAB i
  let idxStep : ℕ → γ → α → ℕ := fun k y x => Nat.find (hR_ex k y x)
  have hidxStep_meas : ∀ k, Measurable (fun p : γ × α => idxStep k p.1 p.2) := by
    intro k
    exact measurable_find (fun p : γ × α => hR_ex k p.1 p.2)
      (fun i => hR_meas_joint k i)
  -- Recursive definition of `b`.
  let b : ℕ → α → γ := fun k => Nat.rec (motive := fun _ => α → γ)
      b0 (fun k bk x => d (idxStep k (bk x) x)) k
  have hb_meas : ∀ k, Measurable (b k) := by
    intro k
    induction k with
    | zero => exact hb0_meas
    | succ k ih =>
      change Measurable (fun x => d (idxStep k (b k x) x))
      refine hd_meas.comp ?_
      have h_pair : Measurable (fun x : α => (b k x, x)) := ih.prodMk measurable_id
      exact (hidxStep_meas k).comp h_pair
  ----------------------------------------------------------------------------
  -- The null exception set is `N₀ := N ∪ E*`.
  ----------------------------------------------------------------------------
  let Eraw : Set α := ⋃ k, E k
  have hEraw_null : m Eraw = 0 := by
    refine measure_iUnion_null fun k => hE_null k
  let E_star : Set α := MeasureTheory.toMeasurable m Eraw
  have hE_star_meas : MeasurableSet E_star :=
    MeasureTheory.measurableSet_toMeasurable m Eraw
  have hE_star_null : m E_star = 0 :=
    (MeasureTheory.measure_toMeasurable Eraw).trans hEraw_null
  have hEraw_sub : Eraw ⊆ E_star := MeasureTheory.subset_toMeasurable m Eraw
  let N₀ : Set α := N ∪ E_star
  have hN₀_meas : MeasurableSet N₀ := hN_meas.union hE_star_meas
  have hN₀_null : m N₀ = 0 := by
    refine le_antisymm ?_ (zero_le)
    calc m N₀ ≤ m N + m E_star := measure_union_le _ _
      _ = 0 + 0 := by rw [hN_null, hE_star_null]
      _ = 0 := by simp
  have hN_subset_N₀ : N ⊆ N₀ := Set.subset_union_left
  ----------------------------------------------------------------------------
  -- Off `N₀`, prove existence of fiber witnesses at every level.
  ----------------------------------------------------------------------------
  have h_strip_E : ∀ x, x ∉ N₀ → ∀ k i, x ∈ W' k i → x ∈ W k i := by
    intro x hxN₀ k i hxW'
    have hxEraw : x ∉ Eraw := fun h => hxN₀ (Set.mem_union_right _ (hEraw_sub h))
    have hxE_k : x ∉ E k := fun h =>
      hxEraw (Set.mem_iUnion.mpr ⟨k, h⟩)
    by_contra hxW
    exact hxE_k (Set.mem_iUnion.mpr ⟨i, ⟨hxW', hxW⟩⟩)
  have hd_dense_rad : ∀ (w : γ) (r : ℝ), 0 < r → ∃ j, dist w (d j) < r := by
    intro w r hr
    exact Metric.denseRange_iff.mp hd_dense w r hr
  ----------------------------------------------------------------------------
  -- The invariant: at every level k, for x ∉ N₀, `x ∈ W' k (idx k x)`.
  ----------------------------------------------------------------------------
  have h_base : ∀ x, x ∉ N₀ → x ∈ W' 0 (idx0 x) := by
    intro x hxN₀
    have hxN : x ∉ N := fun h => hxN₀ (Set.mem_union_left _ h)
    obtain ⟨w, hxw⟩ := hĜ_ne_offN x hxN
    obtain ⟨j, hj⟩ := hd_dense_rad w (δ 1) (hδ_pos 1)
    have hxWj : x ∈ W 0 j := by
      refine ⟨w, ?_, hxw⟩
      rw [Metric.mem_closedBall]
      exact hj.le
    have hxW'j : x ∈ W' 0 j := hW'_sub 0 j hxWj
    have hQ0j : Q0 x j := Or.inl hxW'j
    have h_spec : Q0 x (idx0 x) := Nat.find_spec (hQ0_ex x)
    rcases h_spec with h_left | ⟨_, h_no⟩
    · exact h_left
    · exact absurd hxW'j (h_no j)
  let idx : ℕ → α → ℕ := fun k => Nat.rec (motive := fun _ => α → ℕ)
      idx0 (fun k _ x => idxStep k (b k x) x) k
  have hb_eq_d_idx : ∀ k x, b k x = d (idx k x) := by
    intro k x
    induction k with
    | zero => rfl
    | succ k _ => rfl
  have h_inv : ∀ k x, x ∉ N₀ → x ∈ W' k (idx k x) := by
    intro k x hxN₀
    induction k with
    | zero => exact h_base x hxN₀
    | succ k ih =>
      have hxW_k : x ∈ W k (idx k x) := h_strip_E x hxN₀ k (idx k x) ih
      obtain ⟨w_k, hw_k_ball, hxw_k⟩ := hxW_k
      have hw_k_dist : dist w_k (d (idx k x)) ≤ δ (k+1) := by
        rw [Metric.mem_closedBall] at hw_k_ball
        exact hw_k_ball
      obtain ⟨j, hj⟩ := hd_dense_rad w_k (δ (k+2)) (hδ_pos _)
      have hj' : dist (d j) w_k < δ (k+2) := by rw [dist_comm]; exact hj
      have hdj_dist : dist (d j) (b k x) ≤ δ k := by
        rw [hb_eq_d_idx k x]
        calc dist (d j) (d (idx k x))
            ≤ dist (d j) w_k + dist w_k (d (idx k x)) := dist_triangle _ _ _
          _ ≤ δ (k+2) + δ (k+1) := add_le_add hj'.le hw_k_dist
          _ ≤ δ k := by
              change (1 / 2 : ℝ)^(k+2) + (1 / 2 : ℝ)^(k+1) ≤ (1 / 2 : ℝ)^k
              have hk : (0 : ℝ) ≤ (1 / 2 : ℝ)^k := pow_nonneg (by norm_num) _
              have h1 : (1 / 2 : ℝ)^(k+2) = (1 / 2)^k * (1/4) := by
                rw [pow_add]; ring
              have h2 : (1 / 2 : ℝ)^(k+1) = (1 / 2)^k * (1/2) := by
                rw [pow_add]; ring
              rw [h1, h2]
              nlinarith [hk]
      have hxWk1_j : x ∈ W (k+1) j := by
        refine ⟨w_k, ?_, hxw_k⟩
        rw [Metric.mem_closedBall]
        exact hj.le
      have hxW'k1_j : x ∈ W' (k+1) j := hW'_sub (k+1) j hxWk1_j
      have hRj : R k (b k x) x j := Or.inl ⟨hdj_dist, hxW'k1_j⟩
      change x ∈ W' (k+1) (idxStep k (b k x) x)
      have h_spec : R k (b k x) x (idxStep k (b k x) x) :=
        Nat.find_spec (hR_ex k (b k x) x)
      rcases h_spec with ⟨_, h_W'⟩ | ⟨_, h_no⟩
      · exact h_W'
      · exact absurd ⟨hdj_dist, hxW'k1_j⟩ (h_no j)
  ----------------------------------------------------------------------------
  -- Establish the geometric bounds and assemble the selector.
  ----------------------------------------------------------------------------
  have h_witness : ∀ x, x ∉ N₀ → ∀ k, ∃ c' : γ, dist c' (b k x) ≤ (1/2 : ℝ)^k ∧ (x, c') ∈ Ĝ := by
    intro x hxN₀ k
    have hxW' : x ∈ W' k (idx k x) := h_inv k x hxN₀
    have hxW : x ∈ W k (idx k x) := h_strip_E x hxN₀ k (idx k x) hxW'
    obtain ⟨w, hw_ball, hxw⟩ := hxW
    refine ⟨w, ?_, hxw⟩
    rw [Metric.mem_closedBall] at hw_ball
    rw [hb_eq_d_idx k x]
    calc dist w (d (idx k x)) ≤ δ (k+1) := hw_ball
      _ ≤ δ k := by
          change (1 / 2 : ℝ)^(k+1) ≤ (1 / 2 : ℝ)^k
          have : (1 / 2 : ℝ)^(k+1) = (1/2)^k * (1/2) := by rw [pow_add]; ring
          rw [this]
          have hk : (0 : ℝ) ≤ (1 / 2 : ℝ)^k := pow_nonneg (by norm_num) _
          nlinarith
  have h_consecutive : ∀ x, x ∉ N₀ → ∀ k,
      dist (b k x) (b (k+1) x) ≤ (1/2 : ℝ)^k := by
    intro x hxN₀ k
    have h_spec : R k (b k x) x (idxStep k (b k x) x) :=
      Nat.find_spec (hR_ex k (b k x) x)
    have hxW'k1 : x ∈ W' (k+1) (idx (k+1) x) := h_inv (k+1) x hxN₀
    have h_idx_step : idx (k+1) x = idxStep k (b k x) x := rfl
    rcases h_spec with ⟨h_dist, _⟩ | ⟨_, h_no⟩
    · change dist (b k x) (d (idxStep k (b k x) x)) ≤ δ k
      rw [dist_comm]; exact h_dist
    · exfalso
      have hxW_k : x ∈ W k (idx k x) :=
        h_strip_E x hxN₀ k (idx k x) (h_inv k x hxN₀)
      obtain ⟨w_k, hw_k_ball, hxw_k⟩ := hxW_k
      have hw_k_dist : dist w_k (d (idx k x)) ≤ δ (k+1) := by
        rw [Metric.mem_closedBall] at hw_k_ball; exact hw_k_ball
      obtain ⟨j, hj⟩ := hd_dense_rad w_k (δ (k+2)) (hδ_pos _)
      have hj' : dist (d j) w_k < δ (k+2) := by rw [dist_comm]; exact hj
      have hdj_dist : dist (d j) (b k x) ≤ δ k := by
        rw [hb_eq_d_idx k x]
        calc dist (d j) (d (idx k x))
            ≤ dist (d j) w_k + dist w_k (d (idx k x)) := dist_triangle _ _ _
          _ ≤ δ (k+2) + δ (k+1) := add_le_add hj'.le hw_k_dist
          _ ≤ δ k := by
              change (1 / 2 : ℝ)^(k+2) + (1 / 2 : ℝ)^(k+1) ≤ (1 / 2 : ℝ)^k
              have hk : (0 : ℝ) ≤ (1 / 2 : ℝ)^k := pow_nonneg (by norm_num) _
              have h1 : (1 / 2 : ℝ)^(k+2) = (1 / 2)^k * (1/4) := by rw [pow_add]; ring
              have h2 : (1 / 2 : ℝ)^(k+1) = (1 / 2)^k * (1/2) := by rw [pow_add]; ring
              rw [h1, h2]; nlinarith [hk]
      have hxWk1_j : x ∈ W (k+1) j := by
        refine ⟨w_k, ?_, hxw_k⟩
        rw [Metric.mem_closedBall]; exact hj.le
      have hxW'k1_j : x ∈ W' (k+1) j := hW'_sub (k+1) j hxWk1_j
      exact h_no j ⟨hdj_dist, hxW'k1_j⟩
  ----------------------------------------------------------------------------
  -- ASSEMBLY
  ----------------------------------------------------------------------------
  refine ⟨N₀, b, hN₀_meas, hN₀_null, hN_subset_N₀, hb_meas, h_consecutive, h_witness⟩

/-- **Closed-graph Aumann selector for a single Polish target γ with
m.a.e. fiber identity**.

Given a Borel graph `Ĝ ⊆ α × γ` that is **closed** in a Polish refinement on
γ, with non-empty fibers over `α \ N`, produces a measurable selector
`t : α → γ` and a measurable m-null exceptional set `N₀ ⊇ N` such that
`(x, t x) ∈ Ĝ` for every `x ∉ N₀`.

Specialisation: when `γ = α × β` and the graph `Ĝ` encodes a "lifted" Borel
set `G' ⊆ α × β` via `Ĝ := {(x, (y, b)) | x = y ∧ (y, b) ∈ G'}`, the resulting
selector `t : α → α × β` satisfies `(t x).1 = x` m-a.e. (by
`proj_identity_mae_of_closed_graph`) and `(t x).2 ∈ G'_x` m-a.e. (by composing
this conclusion with the fiber projection). The closed-graph hypothesis
`hĜ_closed` is supplied by `polishRefinement_of_measurable_singleSpace`.

The hypotheses:
- `Ĝ`, `m`, `N`, `hĜ_meas`, `hĜ_closed`, `hN_meas`, `hN_null`,
  `hĜ_ne_offN` — the closed graph in single-space γ, measure, m-null
  exceptional set, and per-x non-emptiness.
- structural typeclasses: `α` Polish + Borel; `γ` Polish +
  Borel + Nonempty + MetricSpace (the metric is required for the
  Cauchy nested-ball construction). -/
private theorem aumann_selector_closed_graph_polish_singleSpace
    {α γ : Type*}
    [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    [Nonempty γ]
    (Ĝ : Set (α × γ)) (hĜ_meas : MeasurableSet Ĝ) (hĜ_closed : IsClosed Ĝ)
    (m : Measure α) [SFinite m]
    (N : Set α) (hN_meas : MeasurableSet N) (hN_null : m N = 0)
    (hĜ_ne_offN : ∀ x ∉ N, ∃ c : γ, (x, c) ∈ Ĝ) :
    ∃ N₀ : Set α, MeasurableSet N₀ ∧ m N₀ = 0 ∧ N ⊆ N₀ ∧
      ∃ t : α → γ, Measurable t ∧ ∀ x ∉ N₀, (x, t x) ∈ Ĝ := by
  -- Specialised to the single-space target type γ: only the inner Cauchy-step
  -- brick differs (`..._singleSpace`); the outer Cauchy-limit + closedness
  -- argument is structurally identical to `aumann_selector_closed_graph_polish`.
  classical
  -- Endow γ with a complete metric compatible with its Polish topology.
  letI := upgradeIsCompletelyMetrizable γ
  -- Invoke the recursive Cauchy-index sub-step (single-space form) to obtain a
  -- measurable sequence `b k : α → γ` whose values are 2⁻ᵏ-close to the fiber
  -- `Ĝ_x` and Cauchy with rate 2⁻ᵏ off a measurable m-null set `N₀ ⊇ N`.
  obtain ⟨N₀, b, hN₀_meas, hN₀_null, hN_sub, hb_meas, hb_cauchy, hb_witness⟩ :=
    cauchy_selector_inductive_step_singleSpace Ĝ hĜ_meas m N hN_meas hN_null hĜ_ne_offN
  -- The arbitrary fallback value on `N₀`: pick any element of `γ`.
  let b₀ : γ := Classical.arbitrary γ
  -- Off `N₀`, the sequence `(b k x)` is Cauchy by `hb_cauchy` with summable
  -- geometric rate `(1/2)^k`.
  have hb_isCauchy_off : ∀ x ∉ N₀, CauchySeq (fun k => b k x) := by
    intro x hxN₀
    refine Metric.cauchySeq_iff'.2 ?_
    intro ε hε
    obtain ⟨K, hK⟩ : ∃ K : ℕ, (1 / 2 : ℝ) ^ K < ε / 2 := by
      have htd : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hpos : (0 : ℝ) < ε / 2 := by positivity
      rw [Metric.tendsto_atTop] at htd
      obtain ⟨K, hK⟩ := htd (ε / 2) hpos
      refine ⟨K, ?_⟩
      have := hK K (le_refl K)
      simpa [Real.dist_eq, abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) K)]
        using this
    refine ⟨K, fun n hn => ?_⟩
    have h_tel : dist (b K x) (b n x) ≤ ∑ k ∈ Finset.Ico K n, (1 / 2 : ℝ) ^ k := by
      have := dist_le_Ico_sum_dist (f := fun k => b k x) (m := K) (n := n) hn
      refine this.trans ?_
      apply Finset.sum_le_sum
      intro k _
      exact hb_cauchy x hxN₀ k
    have h_geom : ∑ k ∈ Finset.Ico K n, (1 / 2 : ℝ) ^ k
        ≤ 2 * (1 / 2 : ℝ) ^ K := by
      have hr : (1 / 2 : ℝ) < 1 := by norm_num
      have hrnn : (0 : ℝ) ≤ 1 / 2 := by norm_num
      have hshift :
          ∑ k ∈ Finset.Ico K n, (1 / 2 : ℝ) ^ k
            = (1 / 2 : ℝ) ^ K *
              ∑ j ∈ Finset.range (n - K), (1 / 2 : ℝ) ^ j := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [pow_add, mul_comm]
      rw [hshift]
      have hsum_le : ∑ j ∈ Finset.range (n - K), (1 / 2 : ℝ) ^ j ≤ 2 := by
        have hgeom : ∑ j ∈ Finset.range (n - K), (1 / 2 : ℝ) ^ j
            = (1 - (1 / 2 : ℝ) ^ (n - K)) / (1 - 1 / 2) := by
          rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
          field_simp; ring
        rw [hgeom]
        have hpos_pow : 0 ≤ (1 / 2 : ℝ) ^ (n - K) := pow_nonneg hrnn _
        have hle_pow : (1 / 2 : ℝ) ^ (n - K) ≤ 1 :=
          pow_le_one₀ hrnn (le_of_lt hr)
        have h2 : (0 : ℝ) < 1 - 1 / 2 := by norm_num
        rw [div_le_iff₀ h2]
        linarith
      have hpos_powK : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := pow_nonneg hrnn _
      nlinarith [hpos_powK]
    have h1 : dist (b K x) (b n x) ≤ 2 * (1 / 2 : ℝ) ^ K := h_tel.trans h_geom
    have h2 : 2 * (1 / 2 : ℝ) ^ K < ε := by linarith
    rw [dist_comm]
    exact h1.trans_lt h2
  -- Modify `b k` to converge everywhere: replace `b k x` with `b₀` on `N₀`.
  set b' : ℕ → α → γ := fun k x => if x ∈ N₀ then b₀ else b k x with hb'_def
  have hb'_meas : ∀ k, Measurable (b' k) := by
    intro k
    refine Measurable.ite hN₀_meas measurable_const (hb_meas k)
  have hb'_cauchy : ∀ x, CauchySeq (fun k => b' k x) := by
    intro x
    by_cases hx : x ∈ N₀
    · have : (fun k => b' k x) = fun _ => b₀ := by
        funext k; simp [b', hx]
      rw [this]
      exact cauchySeq_const _
    · have : (fun k => b' k x) = fun k => b k x := by
        funext k; simp [b', hx]
      rw [this]
      exact hb_isCauchy_off x hx
  -- Define `t` as the limit.
  set t : α → γ := fun x => Classical.choose (cauchySeq_tendsto_of_complete (hb'_cauchy x))
    with ht_def
  have ht_lim : ∀ x, Filter.Tendsto (fun k => b' k x) Filter.atTop (nhds (t x)) := by
    intro x
    exact Classical.choose_spec (cauchySeq_tendsto_of_complete (hb'_cauchy x))
  have ht_meas : Measurable t := by
    refine measurable_of_tendsto_metrizable (f := b') (g := t) hb'_meas ?_
    exact tendsto_pi_nhds.mpr ht_lim
  -- Closedness of Ĝ: for x ∉ N₀, the witnesses b'' k x have b''_k close to Ĝ_x,
  -- and the limit lies in Ĝ_x.
  refine ⟨N₀, hN₀_meas, hN₀_null, hN_sub, t, ht_meas, ?_⟩
  intro x hxN₀
  -- Construct a sequence of actual Ĝ-points converging to t x.
  choose b'' hb''_dist hb''_inĜ using hb_witness x hxN₀
  have hb_tendsto : Filter.Tendsto (fun k => b k x) Filter.atTop (nhds (t x)) := by
    have := ht_lim x
    have heq : (fun k => b' k x) = fun k => b k x := by
      funext k; simp [b', hxN₀]
    rw [heq] at this
    exact this
  have hb''_tendsto : Filter.Tendsto (fun k => b'' k) Filter.atTop (nhds (t x)) := by
    rw [Metric.tendsto_atTop] at hb_tendsto ⊢
    intro ε hε
    obtain ⟨K₁, hK₁⟩ := hb_tendsto (ε / 2) (by linarith)
    have hpow_tendsto : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    rw [Metric.tendsto_atTop] at hpow_tendsto
    obtain ⟨K₂, hK₂⟩ := hpow_tendsto (ε / 2) (by linarith)
    refine ⟨max K₁ K₂, fun n hn => ?_⟩
    have hn1 : K₁ ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : K₂ ≤ n := le_trans (le_max_right _ _) hn
    have h1 : dist (b n x) (t x) < ε / 2 := hK₁ n hn1
    have h2 : dist (b'' n) (b n x) ≤ (1 / 2 : ℝ) ^ n := hb''_dist n
    have h2' : (1 / 2 : ℝ) ^ n < ε / 2 := by
      have := hK₂ n hn2
      have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n :=
        pow_nonneg (by norm_num) _
      simpa [Real.dist_eq, abs_of_nonneg hpos] using this
    calc dist (b'' n) (t x)
        ≤ dist (b'' n) (b n x) + dist (b n x) (t x) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  -- Since Ĝ is closed and each (x, b'' k) ∈ Ĝ, the limit (x, t x) ∈ Ĝ.
  have hpair_tendsto :
      Filter.Tendsto (fun k => (x, b'' k)) Filter.atTop (nhds (x, t x)) := by
    refine Filter.Tendsto.prodMk_nhds tendsto_const_nhds hb''_tendsto
  have : (x, t x) ∈ closure Ĝ :=
    mem_closure_of_tendsto hpair_tendsto (Filter.Eventually.of_forall (fun k => hb''_inĜ k))
  rwa [hĜ_closed.closure_eq] at this

/-- **m.a.e. fiber identity from a graph with diagonal-fibered structure**.

Given:
* a measurable selector `t : α → α × β`,
* a Borel set `Ĝ ⊆ α × (α × β)` (with `[StandardBorelSpace α]` + Polish β)
  whose fiber over each `x ∈ α` is contained in the *singleton-prefix slice*
  `{x} × β` (i.e. `(x, (y, b)) ∈ Ĝ ⇒ y = x`),
* `(x, t x) ∈ Ĝ` for `x ∉` an m-null set,

the first-coordinate projection `(t x).1 = x` holds m-a.e.

**Proof**: pointwise on the m-conull set `{x | (x, t x) ∈ Ĝ}` (witnessed by
`hĜ_t_ae`), `hĜ_diag` applied at `(x, t x)` yields `(t x).1 = x`. The
diagonal-fiber containment is supplied by the caller's construction of `Ĝ`
(e.g. `Ĝ := {(x, (y, b)) | x = y ∧ (y, b) ∈ G'}`), so no analytic-image
bookkeeping is needed at this lemma.

Composing `aumann_selector_closed_graph_polish_singleSpace` with this lemma
gives a selector `α → β` (the form expected by
`aumann_measurable_selection_of_borel_graph_minus_null`): extract
`Prod.snd ∘ t : α → β` (`coordProj_snd_measurable_singleSpace`) and the m.a.e.
fiber identity gives `(x, (Prod.snd ∘ t) x) ∈ G'` m-a.e.

The hypotheses:
- `Ĝ`, `t`, `ht_meas`, `hĜ_diag`, `hĜ_t_ae` — the lifted graph,
  selector, its measurability, the diagonal-fiber containment, and the
  selector-membership m.a.e. property.
- standard-Borel α + Polish β. -/
private theorem proj_identity_mae_of_closed_graph
    {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [PolishSpace β] [BorelSpace β]
    (Ĝ : Set (α × (α × β))) (_hĜ_meas : MeasurableSet Ĝ)
    (hĜ_diag : ∀ x : α, ∀ p : α × β, (x, p) ∈ Ĝ → p.1 = x)
    (t : α → α × β) (ht_meas : Measurable t)
    (m : Measure α) [SFinite m]
    (hĜ_t_ae : ∀ᵐ x ∂m, (x, t x) ∈ Ĝ) :
    ∀ᵐ x ∂m, (t x).1 = x := by
  filter_upwards [hĜ_t_ae] with x hx
  exact hĜ_diag x (t x) hx


/-- **Suslin-scheme Cauchy sequence**.

Internal recursive construction supporting `aumann_measurable_selection_of_borel_graph_minus_null`.
For each Borel set `G' ⊆ α × β` with a Polish target `β`, this lemma exposes a
measurable selector `s : α → β` and a measurable m-null exceptional set `N₀ ⊇ N`
such that on `N₀ᶜ` the pointwise conclusion `(x, s x) ∈ G'` holds.

**Subtlety (Borel-not-just-closed `G'`)**: a naive Cauchy-limit argument only
produces a selector in `closure(G'_x)`, not in `G'_x`. The Kechris (§18.A) fix
uses a Polish refinement of the topology on the product `α × β` (treated as
a single Polish space via `MeasurableSet.isClopenable`) so that `G'` becomes
**closed** in the refined topology; then the closed-graph Cauchy construction
(via `aumann_selector_closed_graph_polish_singleSpace`) applies. Borel
structures under the refined topology coincide with the original
(`borel_eq_borel_of_le`), so the selector is measurable in the original Borel
sense as well.

The proof uses the following single-space Polish refinement chain:

- `polishRefinement_of_measurable_singleSpace`: Polish refinement on
  the product `α × β` directly (single space), making `G'` clopen.
- `aumann_selector_closed_graph_polish_singleSpace`: closed-graph
  selector on the lifted graph `Ĝ ⊆ α × (α × β)`, returning `t : α → α × β`.
- `proj_identity_mae_of_closed_graph`: m.a.e. fiber identity
  `(t x).1 = x` from the diagonal-fibered structure of `Ĝ`.
- `coordProj_snd_measurable_singleSpace`: extract `s := fun x => (t x).2`
  measurably.
- `nullMeasurableSet_image_fst_of_borel`: null-measurability of
  the first projection used in the analytic-image bookkeeping.

The hypotheses:
- `G'`, `m`, `N`, `hG'_meas`, `hN_meas`, `hN_null`, `hΓ_ne_offN` —
  the graph, measure, exceptional set, and their regularity properties.
- the stated structural typeclasses. -/
private theorem aumann_suslin_scheme_cauchy
    {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [PolishSpace β] [BorelSpace β]
    [Nonempty β]
    (G' : Set (α × β)) (hG'_meas : MeasurableSet G')
    (m : Measure α) [SFinite m]
    (N : Set α) (hN_meas : MeasurableSet N) (hN_null : m N = 0)
    (hΓ_ne_offN : ∀ x ∉ N, ∃ b : β, (x, b) ∈ G') :
    ∃ N₀ : Set α, MeasurableSet N₀ ∧ m N₀ = 0 ∧ N ⊆ N₀ ∧
      ∃ s : α → β, Measurable s ∧ ∀ x ∉ N₀, (x, s x) ∈ G' := by
  -- Strategy: compose the single-space Polish refinement chain.
  -- 1. Upgrade `α` to a Polish topology (`upgradeStandardBorel`).
  -- 2. Lift `G'` to a "diagonal-fibered" graph `Ĝ ⊆ α × (α × β)` defined by
  --    `Ĝ := {(x, p) | (p.1, p.2) ∈ G' ∧ p.1 = x}`. The fibers of `Ĝ` over
  --    `x ∈ α` are then `{(x, b) : b ∈ G'_x}` — non-empty wherever G'_x is.
  -- 3. Apply `polishRefinement_of_measurable_singleSpace` to (a Borel
  --    image of) `G'` to obtain a Polish refinement on `α × β` making `G'`
  --    closed in the single-space topology. Transport to `Ĝ` via the
  --    appropriate Borel-preserving topology on `α × (α × β)`.
  -- 4. Apply `aumann_selector_closed_graph_polish_singleSpace` with γ = α × β
  --    to obtain a measurable selector `t : α → α × β` and measurable m-null
  --    set `N₀ ⊇ N` with `(x, t x) ∈ Ĝ` for `x ∉ N₀`.
  -- 5. Apply `proj_identity_mae_of_closed_graph` to get `(t x).1 = x`
  --    m-a.e., and extract `s := fun x => (t x).2` via
  --    `coordProj_snd_measurable_singleSpace`.
  -- 6. Conclude `(x, s x) ∈ G'` for `x ∉ N₀` (after possibly enlarging
  --    `N₀` by the m-null projection exception set).
  classical
  -- First handle `IsEmpty α`: the conclusion is vacuous off any null
  -- set, so we take `N₀ := N`, `s := fun _ => Classical.arbitrary β`.
  rcases isEmpty_or_nonempty α with hα_empty | hα_ne
  · refine ⟨N, hN_meas, hN_null, le_refl _, fun _ => Classical.arbitrary β,
      measurable_const, ?_⟩
    intro x _
    exact hα_empty.elim x
  -- Endow `α` with a compatible Polish topology and Borel structure.
  letI := upgradeStandardBorel α
  -- Obtain a Polish refinement τ' on `α × β` making `G'` clopen, together with
  -- Borel-preservation `@borel (α × β) τ' = Prod.instMeasurableSpace`.
  obtain ⟨τ', _τ'_le, τ'_polish, hτ'_borel, hG'_closed_τ', _hG'_open_τ'⟩ :=
    polishRefinement_of_measurable_singleSpace G' hG'_meas
  -- Install τ' as the topology on `α × β`. Construct `BorelSpace`
  -- instance under τ' from `hτ'_borel`.
  letI : TopologicalSpace (α × β) := τ'
  haveI : PolishSpace (α × β) := τ'_polish
  haveI : BorelSpace (α × β) := ⟨hτ'_borel.symm⟩
  -- Build the lifted closed graph `Ĝ ⊆ α × (α × β)`:
  --   `Ĝ := {q | q.2.1 = q.1 ∧ q.2 ∈ G'}`.
  -- Its fiber over `x` is `{(y, b) | y = x ∧ (y, b) ∈ G'} = {(x, b) | (x, b) ∈ G'}`.
  set Ĝ : Set (α × (α × β)) := {q : α × (α × β) | q.2.1 = q.1 ∧ q.2 ∈ G'}
    with hĜ_def
  -- Ĝ is measurable in the original product σ-algebra.
  have hĜ_meas : MeasurableSet Ĝ := by
    have h_diag : MeasurableSet {q : α × (α × β) | q.2.1 = q.1} := by
      have hf : Measurable (fun q : α × (α × β) => q.2.1) :=
        measurable_fst.comp measurable_snd
      have hg : Measurable (fun q : α × (α × β) => q.1) := measurable_fst
      exact measurableSet_eq_fun hf hg
    have h_proj : MeasurableSet {q : α × (α × β) | q.2 ∈ G'} :=
      measurable_snd hG'_meas
    exact h_diag.inter h_proj
  -- Ĝ is closed in the product topology on `α × (α × β)` (α with upgrade
  -- topology, α × β with τ').
  have hĜ_closed : IsClosed Ĝ := by
    -- Continuity of needed projections, all w.r.t. the auto-derived product
    -- topology on `α × (α × β)` (using α's upgrade + τ' on α × β).
    have h_snd : Continuous (Prod.snd : α × (α × β) → α × β) := continuous_snd
    have h_fst_outer : Continuous (Prod.fst : α × (α × β) → α) := continuous_fst
    -- `Prod.fst : α × β → α` under τ': τ'-open preimages of α-opens are
    -- pre-images under `id : (α × β, τ') → (α × β, instTopologicalSpaceProd)`
    -- (continuous since τ' ≤ instTopologicalSpaceProd) followed by the
    -- standard `Prod.fst` (continuous under `instTopologicalSpaceProd`).
    -- Hand-build continuity via `continuous_def`.
    have h_fst_inner_τ' : @Continuous (α × β) α _ _ Prod.fst := by
      rw [continuous_def]
      intro s hs
      -- `s ⊆ α` is open; want its preimage under `Prod.fst` to be τ'-open.
      have hs_pre_orig : @IsOpen (α × β) instTopologicalSpaceProd (Prod.fst ⁻¹' s) := by
        have : @Continuous (α × β) α instTopologicalSpaceProd _ Prod.fst := continuous_fst
        exact (continuous_def.mp this) s hs
      -- τ' ≤ instTopologicalSpaceProd, so any instTopologicalSpaceProd-open is τ'-open.
      exact _τ'_le _ hs_pre_orig
    have h_snd_fst : Continuous (fun q : α × (α × β) => q.2.1) :=
      h_fst_inner_τ'.comp h_snd
    have h_diag_cl : IsClosed {q : α × (α × β) | q.2.1 = q.1} :=
      isClosed_eq h_snd_fst h_fst_outer
    have h_proj_cl : IsClosed {q : α × (α × β) | q.2 ∈ G'} :=
      hG'_closed_τ'.preimage h_snd
    exact h_diag_cl.inter h_proj_cl
  -- Non-emptiness of Ĝ-fibers off N.
  have hĜ_ne_offN : ∀ x ∉ N, ∃ p : α × β, (x, p) ∈ Ĝ := by
    intro x hxN
    obtain ⟨b, hxb⟩ := hΓ_ne_offN x hxN
    refine ⟨(x, b), ?_, hxb⟩
    rfl
  -- The hypotheses supply `Nonempty α` and `Nonempty β`, hence `Nonempty (α × β)`.
  haveI : Nonempty (α × β) := ⟨(Classical.arbitrary α, Classical.arbitrary β)⟩
  -- Invoke the closed-graph selector with γ := α × β (under τ').
  obtain ⟨N₀, hN₀_meas, hN₀_null, hN_sub_N₀, t, ht_meas, ht_inĜ⟩ :=
    aumann_selector_closed_graph_polish_singleSpace
      Ĝ hĜ_meas hĜ_closed m N hN_meas hN_null hĜ_ne_offN
  -- Extract `(t x).1 = x` m-a.e. from the diagonal-fiber identity.
  have hĜ_diag : ∀ x : α, ∀ p : α × β, (x, p) ∈ Ĝ → p.1 = x := by
    intro x p hxp
    exact hxp.1
  have hĜ_t_ae : ∀ᵐ x ∂m, (x, t x) ∈ Ĝ := by
    rw [Filter.eventually_iff, MeasureTheory.mem_ae_iff]
    refine measure_mono_null ?_ hN₀_null
    intro x hx
    by_contra hxN₀
    exact hx (ht_inĜ x hxN₀)
  have h_proj_ae : ∀ᵐ x ∂m, (t x).1 = x :=
    proj_identity_mae_of_closed_graph Ĝ hĜ_meas hĜ_diag t ht_meas m hĜ_t_ae
  -- Enlarge `N₀` by the m-null exception set where `(t x).1 ≠ x`.
  set E : Set α := {x : α | (t x).1 ≠ x} with hE_def
  have hE_meas : MeasurableSet E := by
    have hf : Measurable (fun x : α => (t x).1) := measurable_fst.comp ht_meas
    have hne : MeasurableSet {x : α | (t x).1 ≠ x} := by
      have : {x : α | (t x).1 ≠ x} = {x : α | (t x).1 = x}ᶜ := by
        ext x; simp [Set.mem_compl_iff, Set.mem_setOf_eq, Ne]
      rw [this]
      exact (measurableSet_eq_fun hf measurable_id).compl
    exact hne
  have hE_null : m E = 0 := by
    rw [Filter.eventually_iff, MeasureTheory.mem_ae_iff] at h_proj_ae
    -- `{x | (t x).1 = x}ᶜ` has m-measure 0; this is exactly `E`.
    have : E = {x : α | (t x).1 = x}ᶜ := by
      ext x; simp [E, Set.mem_compl_iff, Set.mem_setOf_eq, Ne]
    rw [this]; exact h_proj_ae
  set N₁ : Set α := N₀ ∪ E with hN₁_def
  have hN₁_meas : MeasurableSet N₁ := hN₀_meas.union hE_meas
  have hN₁_null : m N₁ = 0 := by
    refine le_antisymm ?_ (zero_le)
    calc m N₁ ≤ m N₀ + m E := measure_union_le _ _
      _ = 0 + 0 := by rw [hN₀_null, hE_null]
      _ = 0 := by simp
  have hN_sub_N₁ : N ⊆ N₁ := Set.Subset.trans hN_sub_N₀ Set.subset_union_left
  -- Extract `s := fun x => (t x).2` via `coordProj_snd_measurable_singleSpace`.
  refine ⟨N₁, hN₁_meas, hN₁_null, hN_sub_N₁,
    fun x => (t x).2, coordProj_snd_measurable_singleSpace t ht_meas, ?_⟩
  intro x hxN₁
  -- For `x ∉ N₁ = N₀ ∪ E`: `x ∉ N₀` gives `(x, t x) ∈ Ĝ`; `x ∉ E` gives `(t x).1 = x`.
  have hxN₀ : x ∉ N₀ := fun h => hxN₁ (Set.mem_union_left _ h)
  have hxE : x ∉ E := fun h => hxN₁ (Set.mem_union_right _ h)
  have h_proj : (t x).1 = x := by
    have : ¬ (t x).1 ≠ x := hxE
    exact not_not.mp this
  have h_inĜ : (x, t x) ∈ Ĝ := ht_inĜ x hxN₀
  -- From Ĝ-membership: `t x ∈ G'`.
  have h_t_in_G' : t x ∈ G' := h_inĜ.2
  -- `(x, (t x).2) = ((t x).1, (t x).2) = t x` via Prod.ext + h_proj.
  have h_pair : (x, (t x).2) = t x := by
    apply Prod.ext
    · simp [h_proj]
    · rfl
  rw [h_pair]
  exact h_t_in_G'

/-- **Measurable selection from a Borel multifunction**.

Given a Borel set `G' ⊆ α × β` whose vertical fibers `G'_x := {b | (x, b) ∈ G'}`
are non-empty for every `x` (using `[Nonempty β]` on the empty fibers as
fallback if a m-null exception set is allowed), produces a **measurable**
selector `s : α → β` with `(x, s x) ∈ G'` for every `x` outside an m-null
exceptional set.

This is the standard Jankov-von Neumann measurable selection theorem on the
**Borel-graph form** (Bogachev *Measure Theory* Vol. II, Theorem 6.9.6;
Aliprantis-Border *Infinite Dimensional Analysis*, Theorem 18.19; Kechris,
*Classical Descriptive Set Theory*, §18). The "m-a.e." weakening (rather
than everywhere) is the universally-measurable version one gets from
Choquet capacitability of analytic sets via
`MeasureTheory.AnalyticSet.statLean_nullMeasurableSet`.

The input is a Borel `G'` plus an m-null `N`: a `(m.prod dirac)`-null
hypothesis would only constrain the default-β slice of the graph, not the
whole graph (a Vitali counter-example shows the original graph can be highly
non-measurable while satisfying it). Instead the input takes the
**vertical-strip null** form (a Borel representative `G'` and an m-null
exceptional set `N` such that on `Nᶜ`, the original graph and `G'` agree
fiber-wise), and JvN selection operates on the Borel set `G'` directly.

The hypotheses:
- `G'`, `m`, `N`, `hG'_meas`, `hN_meas`, `hN_null`, `hΓ_ne_offN` —
  the Borel graph, reference measure, m-null exceptional set, and
  per-x non-emptiness condition off the exceptional set.
- `[StandardBorelSpace α]` — Suslin/Choquet analytic-projection
  hypothesis (matches `MeasurableSet.analyticSet_image`'s source).
- `[TopologicalSpace β] [PolishSpace β] [BorelSpace β]
  [Nonempty β]` — Polish + Nonempty target for the countable-basis
  Suslin scheme + default fallback on the m-null residual.
- `[SFinite m]` — regularity for the m-a.e. conclusion.

The proof delegates to the Suslin-scheme sub-lemma `aumann_suslin_scheme_cauchy`
above, which carries the recursive measurable construction that produces the
selector + a measurable m-null witness `N₀ ⊇ N`. -/
private theorem aumann_measurable_selection_of_borel_graph_minus_null
    {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [PolishSpace β] [BorelSpace β]
    [Nonempty β]
    (G' : Set (α × β)) (hG'_meas : MeasurableSet G')
    (m : Measure α) [SFinite m]
    (N : Set α) (hN_meas : MeasurableSet N) (hN_null : m N = 0)
    (hΓ_ne_offN : ∀ x ∉ N, ∃ b : β, (x, b) ∈ G') :
    ∃ s : α → β, Measurable s ∧ ∀ᵐ x ∂m, (x, s x) ∈ G' := by
  classical
  -- Invoke the Suslin-scheme sub-lemma to get the measurable selector `s` and
  -- the (m-null) exceptional set `N₀ ⊇ N` on whose complement `(x, s x) ∈ G'`
  -- holds pointwise.
  obtain ⟨N₀, hN₀_meas, hN₀_null, _hN_sub_N₀, s, hs_meas, hs_off_N₀⟩ :=
    aumann_suslin_scheme_cauchy G' hG'_meas m N hN_meas hN_null hΓ_ne_offN
  refine ⟨s, hs_meas, ?_⟩
  -- Convert the everywhere-off-N₀ conclusion to an m-a.e. statement.
  rw [Filter.eventually_iff, MeasureTheory.mem_ae_iff]
  -- {x | (x, s x) ∈ G'}ᶜ ⊆ N₀, and m N₀ = 0.
  have h_sub : {x : α | (x, s x) ∈ G'}ᶜ ⊆ N₀ := by
    intro x hx
    by_contra hxN₀
    exact hx (hs_off_N₀ x hxN₀)
  exact measure_mono_null h_sub hN₀_null

/-- **Sub-lemma 2 — ε-approximate argmin selector**.

Given a jointly measurable `f : α × β → ℝ≥0∞` on Polish-target `β` and
`ε > 0`, construct a **measurable** function `s : α → β` such that
`f (x, s x) ≤ (⨅ b, f (x, b)) + ε` for **m-a.e.** `x`.

**Strategy (Aumann/Jankov-von Neumann)**: define the multifunction
`Γ x := {b : β | f (x, b) ≤ (⨅ b', f (x, b')) + ε}`. Two ingredients:

1. **`Γ x ≠ ∅` for every `x`**. If `⨅ b', f (x, b') = ∞` then any
   `b ∈ β` (using `[Nonempty β]`) satisfies the bound trivially. If
   `⨅ b', f (x, b') < ∞` then by definition of `iInf` and `ε > 0`
   there is a `b` with `f (x, b) ≤ ⨅ b', f (x, b') + ε`.
2. **Graph of `Γ` is null-measurable** in `α × β` (w.r.t. the product
   `m × Measure.dirac default`). The graph is
   `{(x, b) : f (x, b) ≤ φ x + ε}` where `φ x := ⨅ b', f (x, b')`. The
   graph is the preimage of the closed set `{(u, v) : u ≤ v + ε}`
   under the jointly null-measurable map `(x, b) ↦ (f (x, b), φ x)`.
   Joint measurability of `f` is given; m-a.e.-measurability of `φ`
   is `analytic_projection_aeMeasurable` via Choquet
   capacitability of analytic projections. The graph's
   null-measurability is `nullMeasurableSet_approx_argmin_graph` above.

JvN selection (the `aumann_measurable_selection_of_borel_graph_minus_null`
core) then yields a measurable `s : α → β` with `s x ∈ Γ x` m-a.e., i.e.
exactly the claimed bound m-a.e. The "null-measurable graph" form is
sufficient for the m-a.e. selector conclusion (vs the "analytic graph" form,
which requires choosing a Polish topology on `α` via `upgradeStandardBorel α`).

**Why a dense-seq partition fails**: take `β = ℝ`, `f x b := 𝟙[b ≠ 0]` (so
`⨅_b f (x, b) = 0` but `f (x, b_n) = 1` whenever `b_n ≠ 0`). For `ε < 1`,
the candidate sets `A_n := {x | f (x, b_n) ≤ ⨅ + ε} = ∅`, so the
union doesn't cover `α`. The dense-seq partition tacitly assumes
`f` is lower semicontinuous in `b` (so `denseSeq` could attain the
infimum to within ε); without this, the ε-slack alone is **not** enough,
and Aumann/JvN's analytic-graph selection is the correct tool.

The hypotheses:
- `f`, `m`, `ε`, `hε` — the integrand, σ-finite reference
  measure, approximation slack.
- `hf` — joint measurability of the integrand.
- `[StandardBorelSpace α]` — analytic projection on the source side.
- `[TopologicalSpace β] [PolishSpace β] [BorelSpace β]
  [Nonempty β]` — Polish + Nonempty target so JvN's countable-basis
  Suslin scheme applies and a default fallback exists on the m-null
  residual.
- `[SFinite m]` — regularity for the m-a.e. conclusion.

The proof delegates to two helpers above:
- `nullMeasurableSet_approx_argmin_graph` — vertical-strip null structure
  of the graph.
- `aumann_measurable_selection_of_borel_graph_minus_null` — the JvN core
  on the Borel-graph form. -/
theorem exists_measurable_approx_argmin
    {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [PolishSpace β] [BorelSpace β]
    [Nonempty β]
    (f : α × β → ℝ≥0∞) (hf : Measurable f)
    (m : Measure α) [SFinite m]
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ s : α → β, Measurable s ∧
      ∀ᵐ x ∂m, f (x, s x) ≤ (⨅ b : β, f (x, b)) + ε := by
  classical
  -- Define the per-x infimum and the selection multifunction.
  set φ : α → ℝ≥0∞ := fun x => ⨅ b : β, f (x, b) with hφ_def
  set Γ : α → Set β := fun x => {b : β | f (x, b) ≤ φ x + ε} with hΓ_def
  -- (1) Γ x is nonempty for every x.
  have hΓ_ne : ∀ x, (Γ x).Nonempty := by
    intro x
    -- Case φ x = ∞ vs φ x < ∞.
    by_cases hφtop : φ x = ⊤
    · -- Any b works: φ x + ε = ⊤, so f (x, b) ≤ ⊤ trivially.
      refine ⟨Classical.arbitrary β, ?_⟩
      simp [Γ, hφtop, le_top]
    · -- φ x < ∞: by definition of iInf, choose b with f (x, b) ≤ φ x + ε.
      have hφlt : φ x < φ x + ε := by
        have hφne : φ x ≠ ⊤ := hφtop
        exact ENNReal.lt_add_right hφne hε.ne'
      -- iInf strictly below φ x + ε: pick a witness.
      have : ∃ b : β, f (x, b) < φ x + ε := by
        have h := (iInf_lt_iff (a := φ x + ε) (f := fun b : β => f (x, b))).mp
          (lt_of_le_of_lt (by simp [φ]) hφlt)
        exact h
      rcases this with ⟨b, hb⟩
      exact ⟨b, hb.le⟩
  -- (2) Extract the Borel representative G' and m-null witness N from the
  -- vertical-strip null structure of the graph.
  obtain ⟨G', hG'_meas, N, hN_meas, hN_null, hGG'_eq⟩ :=
    nullMeasurableSet_approx_argmin_graph (α := α) (β := β) f hf ε m
  -- (3) Per-x non-emptiness of G''s fiber off N: for x ∉ N, the fiber-equiv
  -- with Γ x (which is non-empty everywhere) gives a witness in G'_x.
  have hΓ'_ne_offN : ∀ x ∉ N, ∃ b : β, (x, b) ∈ G' := by
    intro x hxN
    obtain ⟨b, hb⟩ := hΓ_ne x
    exact ⟨b, ((hGG'_eq x hxN b).mp hb)⟩
  -- (4) Apply the (refactored) JvN core to G' and N.
  obtain ⟨s, hs_meas, hs_ae⟩ :=
    aumann_measurable_selection_of_borel_graph_minus_null
      G' hG'_meas m N hN_meas hN_null hΓ'_ne_offN
  refine ⟨s, hs_meas, ?_⟩
  -- hs_ae : ∀ᵐ x ∂m, (x, s x) ∈ G'.
  -- We want: ∀ᵐ x ∂m, f (x, s x) ≤ φ x + ε, i.e. s x ∈ Γ x.
  -- Off N (m-conull) we have the fiber-equivalence (x, s x) ∈ G' ↔ s x ∈ Γ x.
  have hN_ae : ∀ᵐ x ∂m, x ∉ N := by
    rw [Filter.eventually_iff, MeasureTheory.mem_ae_iff]
    -- {x | x ∉ N}ᶜ = N
    have hcompl : ({x | x ∉ N})ᶜ = N := by
      ext x; simp
    rw [hcompl]; exact hN_null
  filter_upwards [hs_ae, hN_ae] with x hx hxN
  -- hx : (x, s x) ∈ G'; hxN : x ∉ N; goal: f (x, s x) ≤ φ x + ε.
  exact (hGG'_eq x hxN (s x)).mpr hx

/-- **Bayes-risk ε-approximate selector.**
Specialises `exists_measurable_approx_argmin` to the joint integrand
`(x, b) ↦ ∫⁻ θ, ℓ θ b ∂(posterior x)` on a Polish 𝓨 target (e.g.
`EuclideanSpace ℝ (Fin d)`, Polish via metric + second-countable instances).

The `∫⁻ x ∂m, ⨅_b ... + ε` bound follows from the a.e. bound of
`exists_measurable_approx_argmin` plus `lintegral_mono_ae` + `lintegral_const`.
The `m univ = 0` corner case gives the bound trivially via `ENNReal.le_add_right`.

The hypotheses:
- `ℓ`, `posterior`, `m`, `ε`, `hε` — standard Bayes-risk data
  (loss, posterior disintegration kernel, data marginal, slack).
- `hℓ` — joint measurability of the loss `(θ, b) ↦ ℓ θ b` (vdV §8.5).
- `[StandardBorelSpace 𝓧]` — required for analytic projection on the
  data-space side; `EuclideanSpace ℝ (Fin n)` (or a product of Polish
  spaces) is standard-Borel automatically.
- `[TopologicalSpace 𝓨] [PolishSpace 𝓨] [BorelSpace 𝓨] [Nonempty 𝓨]`
  — Polish + Nonempty estimator-space target.
- `[IsSFiniteKernel posterior]`, `[IsFiniteMeasure m]` — regularity.
  `[IsFiniteMeasure m]` auto-derives `[SFinite m]` via
  `IsFiniteMeasure.toSigmaFinite`. The conclusion `+ ε` requires
  `m univ < ∞` so the slack `ε' := ε / (m univ + 1)` satisfies
  `ε' * m univ ≤ ε`; under `[SFinite m]` alone `m univ` can be `∞`,
  breaking absorption. A probability measure satisfies
  `[IsFiniteMeasure m]` automatically.

Proof: compose the above:
1. Define `φ (x, b) := ∫⁻ θ, ℓ θ b ∂(posterior x)`.
2. Prove `φ` jointly measurable via `Measurable.lintegral_kernel_prod_right'`
   on the comapped kernel `posterior.comap Prod.fst measurable_fst`.
3. Apply `exists_measurable_approx_argmin` to `φ` with slack
   `ε' := (ε : ℝ≥0∞) / (m univ + 1)`.
4. Conclude the lintegral bound from the a.e. bound via `lintegral_mono_ae`,
   `lintegral_add_right`, `lintegral_const`, plus arithmetic. -/
theorem exists_measurable_approx_argmin_lintegral
    {𝓧 Θ 𝓨 : Type*}
    [MeasurableSpace 𝓧] [StandardBorelSpace 𝓧]
    [MeasurableSpace Θ]
    [MeasurableSpace 𝓨] [TopologicalSpace 𝓨] [PolishSpace 𝓨]
    [BorelSpace 𝓨] [Nonempty 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞)
    (hℓ : Measurable (Function.uncurry ℓ))
    (posterior : ProbabilityTheory.Kernel 𝓧 Θ)
    [ProbabilityTheory.IsSFiniteKernel posterior]
    (m : Measure 𝓧) [IsFiniteMeasure m]
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ f : 𝓧 → 𝓨, Measurable f ∧
      ∫⁻ x, ∫⁻ θ, ℓ θ (f x) ∂(posterior x) ∂m
        ≤ (∫⁻ x, ⨅ b : 𝓨, ∫⁻ θ, ℓ θ b ∂(posterior x) ∂m) + ε := by
  classical
  -- Joint integrand `φ (x, b) := ∫⁻ θ, ℓ θ b ∂(posterior x)`.
  set φ : 𝓧 × 𝓨 → ℝ≥0∞ := fun p => ∫⁻ θ, ℓ θ p.2 ∂(posterior p.1) with hφ_def
  -- The integrand φ is jointly measurable.
  -- Use `Measurable.lintegral_kernel_prod_right'` on the comapped kernel
  -- `posterior' := posterior.comap Prod.fst measurable_fst : Kernel (𝓧 × 𝓨) Θ`,
  -- with integrand `(p, θ) ↦ ℓ θ p.2`.
  have hφ_meas : Measurable φ := by
    let posterior' : ProbabilityTheory.Kernel (𝓧 × 𝓨) Θ :=
      posterior.comap Prod.fst measurable_fst
    have h_uncurry : Measurable
        (fun (q : (𝓧 × 𝓨) × Θ) => ℓ q.2 q.1.2) := by
      have : Measurable (Function.uncurry ℓ) := hℓ
      -- (q : (𝓧 × 𝓨) × Θ) ↦ (q.2, q.1.2) is measurable, then compose with
      -- uncurry ℓ : Θ × 𝓨 → ℝ≥0∞.
      exact this.comp (measurable_snd.prodMk
        (measurable_snd.comp measurable_fst))
    have hmeas := Measurable.lintegral_kernel_prod_right'
      (κ := posterior') (f := fun (q : (𝓧 × 𝓨) × Θ) => ℓ q.2 q.1.2) h_uncurry
    -- Identify the comapped integral with the original.
    have hsimp : (fun p : 𝓧 × 𝓨 => ∫⁻ θ, ℓ θ p.2 ∂(posterior' p))
        = fun p : 𝓧 × 𝓨 => ∫⁻ θ, ℓ θ p.2 ∂(posterior p.1) := by
      funext p
      simp [posterior', ProbabilityTheory.Kernel.comap_apply]
    rw [hsimp] at hmeas
    exact hmeas
  -- The slack `ε' := (ε : ℝ≥0∞) / (m univ + 1)` is positive.
  set ε' : ℝ≥0∞ := (ε : ℝ≥0∞) / (m univ + 1) with hε'_def
  have hm_univ_lt_top : m univ < ⊤ := IsFiniteMeasure.measure_univ_lt_top
  have hm_univ_ne_top : m univ ≠ ⊤ := hm_univ_lt_top.ne
  have hden_ne_top : m univ + 1 ≠ ⊤ := by
    simp [ENNReal.add_eq_top, hm_univ_ne_top]
  have hden_pos : 0 < m univ + 1 := by
    exact lt_of_lt_of_le zero_lt_one (le_add_self)
  have hε_pos : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by exact_mod_cast hε
  have hε_ne_top : (ε : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hε'_pos : 0 < ε' := by
    rw [hε'_def]
    exact ENNReal.div_pos hε_pos.ne' hden_ne_top
  -- Apply `exists_measurable_approx_argmin`.
  obtain ⟨f, hf_meas, hf_ae⟩ :=
    exists_measurable_approx_argmin (α := 𝓧) (β := 𝓨) φ hφ_meas m ε' hε'_pos
  refine ⟨f, hf_meas, ?_⟩
  -- hf_ae : ∀ᵐ x ∂m, φ (x, f x) ≤ (⨅ b, φ (x, b)) + ε'.
  -- Integrate.
  have hkey :
      ∫⁻ x, φ (x, f x) ∂m
        ≤ ∫⁻ x, (⨅ b : 𝓨, φ (x, b)) + ε' ∂m :=
    lintegral_mono_ae hf_ae
  -- Expand RHS via `lintegral_add_right` (only needs `g` measurable; here
  -- `g = fun _ => ε'` is constant) and `lintegral_const`.
  have hrw_add :
      ∫⁻ x, (⨅ b : 𝓨, φ (x, b)) + ε' ∂m
        = (∫⁻ x, ⨅ b : 𝓨, φ (x, b) ∂m) + ε' * m univ := by
    rw [lintegral_add_right _ measurable_const, lintegral_const]
  rw [hrw_add] at hkey
  -- ε' * m univ ≤ ε.
  -- Use `m univ ≤ m univ + 1` and `(ε / (m univ + 1)) * (m univ + 1) = ε`.
  have hε'_bound : ε' * m univ ≤ (ε : ℝ≥0∞) := by
    have h_mono : ε' * m univ ≤ ε' * (m univ + 1) := by
      gcongr
      exact le_self_add
    have h_cancel : ε' * (m univ + 1) = (ε : ℝ≥0∞) := by
      rw [hε'_def]
      exact ENNReal.div_mul_cancel hden_pos.ne' hden_ne_top
    exact h_mono.trans h_cancel.le
  -- Chain.
  calc ∫⁻ x, ∫⁻ θ, ℓ θ (f x) ∂(posterior x) ∂m
      = ∫⁻ x, φ (x, f x) ∂m := by rfl
    _ ≤ (∫⁻ x, ⨅ b : 𝓨, φ (x, b) ∂m) + ε' * m univ := hkey
    _ ≤ (∫⁻ x, ⨅ b : 𝓨, φ (x, b) ∂m) + ε := by
          gcongr
    _ = (∫⁻ x, ⨅ b : 𝓨, ∫⁻ θ, ℓ θ b ∂(posterior x) ∂m) + ε := by rfl

end MeasurableSelection
end AsymptoticStatistics
