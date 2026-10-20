module
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Decision.Risk.Defs
public import Mathlib.Probability.Decision.Risk.Basic
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.Prohorov

@[expose] public section

/-!
# Markov-kernel-level Prohorov tightness and sub-sequence extraction

Kernel-level adaptation of Mathlib's measure-level Prohorov theorem, for
per-input weak convergence of Markov-kernel sequences. Theorem-agnostic
infrastructure parallel to `Contiguity.lean` and `Prohorov.lean`.

Main declarations:

* `WeakConvergesKernel` — per-input weak convergence of a kernel sequence:
  for every input `a`, the output measures `(κ_n a)` converge weakly.
* `kernelProhorov_subseq_extraction` — for a per-input-tight Markov-kernel
  sequence `(κ_n)` on a Polish output space, extract a strictly monotone
  sub-sequence `φ`, a countable dense input set `D`, and a limit Markov
  kernel `κ_lim` with `(κ_{φ n} a) ⇒ κ_lim a` weakly for every `a ∈ D`.
* `tightness_from_avgRisk_coercive` — for a coercive bowl-shaped loss `L`
  and a uniformly-bounded average-risk sequence, the per-input output
  measures of the Markov-kernel family are tight.

`WeakConvergesKernel` reuses the project's `WeakConverges` (per-input
weak convergence on `ProbabilityMeasure` semantics).
-/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-! ### Per-input weak convergence of Markov kernels -/

/-- **Per-input weak convergence of a kernel sequence**.

A sequence of kernels `κ_n : Kernel Ω 𝓨` is said to weakly converge to a
limit kernel `κ_lim : Kernel Ω 𝓨` if, for every input `a : Ω`, the sequence
of output measures `(κ_n a)` weakly converges (in `WeakConverges`) to
`κ_lim a`.

This is the appropriate convergence notion for kernel-level Prohorov:
the joint (input × output) law typically does not converge weakly, but the
per-input output laws do (with input held fixed). Composing along a
fixed input measure on `Ω` recovers the bind-level weak convergence
(`WeakConverges.bind_kernel` if available).

Kernel weak convergence is the natural sub-sequential limit on the limit
side of the LAN/Gaussian-shift contiguity argument (vdV §8.5; cf. Mathlib
`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`).

**Edge behavior**: trivially satisfied if `κ_n = κ_lim` for every `n`
(constant sequence is its own limit). If `κ_n a` are not probability
measures for some `a`, the definition still makes sense but the
"Markov-kernel" qualifier from the surrounding theorems may fail. -/
def WeakConvergesKernel {Ω 𝓨 : Type*}
    [MeasurableSpace Ω] [MeasurableSpace 𝓨] [TopologicalSpace 𝓨]
    (κ_n : ℕ → Kernel Ω 𝓨) (κ_lim : Kernel Ω 𝓨) : Prop :=
  ∀ a : Ω, WeakConverges (fun n => κ_n n a) (κ_lim a)

/-! ### Kernel-level Prohorov and sub-sequence extraction

The main statement `kernelProhorov_subseq_extraction` rests on two sub-lemmas:

* `cantor_diagonal_extract_on_countable` — Cantor-diagonal extraction over a
  countable input set, packaging a per-input weak limit on the entire
  countable index set into a single sub-sequence.
* `measurable_kernel_lift_from_dense` — measurable kernel-lift extension from
  a per-input limit defined on a countable subset of `Ω`. -/

/-- **Cantor diagonal extraction over a countable index set**.

For a Markov-kernel sequence `(κ_n)` with per-input tightness on a countable
set `D ⊆ Ω`, extract a single sub-sequence `φ : ℕ → ℕ` and per-input limit
measures `μ_lim_D : Ω → Measure 𝓨` such that `(κ_{φ j} a) ⇒ μ_lim_D a` weakly
for every `a ∈ D`.

**Construction**:
1. Enumerate `D` as a sequence (using `Set.Countable`).
2. For each enumerated `a_k`, by `extract_weak_subseq` + nested-subsequence
   diagonal trick, extract finer and finer sub-sequences.
3. The diagonal sub-sequence `φ : ℕ → ℕ` works for every `a_k` simultaneously.

Uses `AsymptoticStatistics.Prohorov.extract_weak_subseq`,
`Set.Countable.exists_eq_range`, and the standard Cantor diagonal. -/
theorem cantor_diagonal_extract_on_countable
    {Ω 𝓨 : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [MeasurableSpace 𝓨] [TopologicalSpace 𝓨]
    [PolishSpace 𝓨] [BorelSpace 𝓨]
    {D : Set Ω} (hD_count : D.Countable)
    (κ_n : ℕ → Kernel Ω 𝓨)
    (hMarkov : ∀ n, IsMarkovKernel (κ_n n))
    (h_tight_on_D : ∀ a ∈ D,
      MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ => (κ_n n a : Measure 𝓨)))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ μ_lim_D : Ω → Measure 𝓨,
        (∀ a ∈ D, IsProbabilityMeasure (μ_lim_D a)) ∧
        ∀ a ∈ D, WeakConverges (fun j => κ_n (φ j) a) (μ_lim_D a) := by
  classical
  -- Trivial case: D is empty.  Use φ := id and μ_lim_D := 0; both conclusions
  -- are vacuous on D = ∅.
  by_cases hD_empty : D = ∅
  · refine ⟨id, strictMono_id, fun _ => (0 : Measure 𝓨), ?_, ?_⟩
    · intro a ha; rw [hD_empty] at ha; exact absurd ha (Set.notMem_empty a)
    · intro a ha; rw [hD_empty] at ha; exact absurd ha (Set.notMem_empty a)
  -- Non-empty case.  Enumerate D = range g for some g : ℕ → Ω with g k ∈ D for all k.
  have hD_ne : D.Nonempty := Set.nonempty_iff_ne_empty.mpr hD_empty
  obtain ⟨g, hg_eq⟩ := hD_count.exists_eq_range hD_ne
  -- Each `g k` lies in D.
  have hg_mem : ∀ k, g k ∈ D := by
    intro k; rw [hg_eq]; exact ⟨k, rfl⟩
  -- For each `a ∈ D`, the singleton `{(κ_n n a)_n}` is tight as a sub-range.
  -- Sub-sequence tightness is inherited via `IsTightMeasureSet.subset` plus
  -- `Set.range_comp_subset_range`.
  -- Build the chain inductively.
  --
  -- `Step k` produces a triple `⟨ψ_k, hψ_k_mono, μ_k⟩`:
  -- * `ψ_k : ℕ → ℕ` is StrictMono;
  -- * `(κ_n (ψ_k j) (g i)) ⇒ μ_i` weakly for every `i ≤ k`.
  -- We package the whole chain `k ↦ (ψ_k, μ_k)` via a recursive definition.
  --
  -- We use a Σ-type to bundle `(ψ : ℕ → ℕ, hψ : StrictMono ψ, μ : Measure 𝓨,
  -- hμ_prob : IsProbabilityMeasure μ, h_conv : WeakConverges _ μ)`.
  -- The recursion at step k+1 uses `extract_weak_subseq` applied to
  -- the sequence `(κ_n (ψ_k j) (g (k+1)))_j`.
  -- Predicate carried at level k.
  let P : ℕ → (ℕ → ℕ) → Prop := fun k ψ =>
    StrictMono ψ ∧
    ∀ i, i ≤ k → ∃ μ : Measure 𝓨, IsProbabilityMeasure μ ∧
      WeakConverges (fun j => κ_n (ψ j) (g i)) μ
  -- Step 0: extract a sub-sequence at `g 0`.
  have hStep0 : ∃ ψ : ℕ → ℕ, P 0 ψ := by
    have hMarkov0 : ∀ n, IsProbabilityMeasure ((κ_n n) (g 0)) :=
      fun n => (hMarkov n).is_probability_measure' (g 0)
    have h_tight0 := h_tight_on_D (g 0) (hg_mem 0)
    obtain ⟨φ, hφ_mono, μ_lim, hμ_lim_prob, hφ_conv⟩ :=
      AsymptoticStatistics.Prohorov.extract_weak_subseq
        (fun n => (κ_n n) (g 0)) h_tight0
    refine ⟨φ, hφ_mono, ?_⟩
    intro i hi
    interval_cases i
    exact ⟨μ_lim, hμ_lim_prob, hφ_conv⟩
  -- Inductive step: given `ψ_k` with `P k ψ_k`, produce `ψ_{k+1}` with `P (k+1) ψ_{k+1}`.
  have hStep : ∀ k (ψ : ℕ → ℕ), P k ψ →
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ P (k+1) (ψ ∘ ρ) := by
    intro k ψ hψ
    obtain ⟨hψ_mono, hψ_conv⟩ := hψ
    -- Apply `extract_weak_subseq` to the sub-sequence `(κ_n (ψ j) (g (k+1)))_j`.
    have hMarkov_sub : ∀ j, IsProbabilityMeasure ((κ_n (ψ j)) (g (k+1))) :=
      fun j => (hMarkov (ψ j)).is_probability_measure' (g (k+1))
    -- Tightness of the sub-sequence: subset of the full tight range.
    have h_tight_full := h_tight_on_D (g (k+1)) (hg_mem (k+1))
    have h_tight_sub :
        MeasureTheory.IsTightMeasureSet
          (Set.range (fun j : ℕ => ((κ_n (ψ j)) (g (k+1)) : Measure 𝓨))) := by
      refine h_tight_full.subset ?_
      rintro μ ⟨j, rfl⟩
      exact ⟨ψ j, rfl⟩
    obtain ⟨ρ, hρ_mono, μ_new, hμ_new_prob, hρ_conv⟩ :=
      AsymptoticStatistics.Prohorov.extract_weak_subseq
        (fun j => (κ_n (ψ j)) (g (k+1))) h_tight_sub
    refine ⟨ρ, hρ_mono, hψ_mono.comp hρ_mono, ?_⟩
    intro i hi
    rcases Nat.lt_or_ge i (k+1) with hlt | hge
    · -- For i ≤ k, inherit from ψ_k by composing with strict-mono ρ.
      have hi_le : i ≤ k := Nat.lt_succ_iff.mp hlt
      obtain ⟨μ_i, hμ_i_prob, hψ_conv_i⟩ := hψ_conv i hi_le
      exact ⟨μ_i, hμ_i_prob, hψ_conv_i.comp hρ_mono⟩
    · -- For i = k+1: this is the new convergence.
      have hi_eq : i = k + 1 := le_antisymm hi hge
      rw [hi_eq]
      exact ⟨μ_new, hμ_new_prob, hρ_conv⟩
  -- Build the chain `Ψ : ℕ → {ψ : ℕ → ℕ // P k ψ}`. To carry the `P k`
  -- predicate through the recursion, package it in a Σ-type.
  let Q : ℕ → Type _ := fun k => { ψ : ℕ → ℕ // P k ψ }
  -- Choose Q 0 from hStep0.
  let chain : ∀ k, Q k :=
    Nat.rec
      (motive := Q)
      ⟨Classical.choose hStep0, Classical.choose_spec hStep0⟩
      (fun k qk =>
        let extr := Classical.choose (hStep k qk.val qk.property)
        let extr_spec := Classical.choose_spec (hStep k qk.val qk.property)
        ⟨qk.val ∘ extr, extr_spec.2⟩)
  -- Diagonal sub-sequence: `φ k := (chain k).val k`.
  let φ : ℕ → ℕ := fun k => (chain k).val k
  -- Each chain.val is StrictMono.
  have hψ_mono : ∀ k, StrictMono (chain k).val := fun k => (chain k).property.1
  -- Recursive structure: chain (k+1).val = (chain k).val ∘ ρ_k for some
  -- StrictMono ρ_k with chain (k+1).val matching the chain definition.
  -- We extract the witness ρ_k from the recursion.
  -- Key fact: for every j, j ≤ extr j (StrictMono.id_le on Nat), so
  -- (chain (k+1)).val (k+1) ≥ (chain k).val (k+1) > (chain k).val k = φ k.
  have hChain_succ : ∀ k, ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      (chain (k+1)).val = (chain k).val ∘ ρ := by
    intro k
    let extr := Classical.choose (hStep k (chain k).val (chain k).property)
    let extr_spec := Classical.choose_spec (hStep k (chain k).val (chain k).property)
    refine ⟨extr, extr_spec.1, ?_⟩
    -- By definition of `chain`, `chain (k+1).val = (chain k).val ∘ extr`.
    rfl
  -- φ is StrictMono.
  have hφ_mono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ ?_
    intro k
    obtain ⟨ρ, hρ_mono, hcomp⟩ := hChain_succ k
    -- φ (k+1) = (chain (k+1)).val (k+1) = (chain k).val (ρ (k+1))
    --        ≥ (chain k).val (k+1) > (chain k).val k = φ k.
    have h₁ : φ (k+1) = (chain k).val (ρ (k+1)) := by
      simp [φ, hcomp, Function.comp]
    have hρ_id : k + 1 ≤ ρ (k+1) := hρ_mono.id_le (k+1)
    have h₂ : (chain k).val (k+1) ≤ (chain k).val (ρ (k+1)) :=
      (hψ_mono k).monotone hρ_id
    have h₃ : (chain k).val k < (chain k).val (k+1) :=
      (hψ_mono k) (Nat.lt_succ_self k)
    -- φ k = (chain k).val k.
    have hφ_k : φ k = (chain k).val k := rfl
    rw [h₁, hφ_k]
    exact lt_of_lt_of_le h₃ h₂
  -- Per-input limit measures: pick `μ_at i` from the predicate at level i.
  -- (chain i).property.2 i (le_refl i) gives ∃ μ_i, ...
  have hμ_at : ∀ i, ∃ μ : Measure 𝓨, IsProbabilityMeasure μ ∧
      WeakConverges (fun j => κ_n ((chain i).val j) (g i)) μ := by
    intro i
    exact (chain i).property.2 i (le_refl i)
  let μ_at : ℕ → Measure 𝓨 := fun i => Classical.choose (hμ_at i)
  have hμ_at_spec : ∀ i, IsProbabilityMeasure (μ_at i) ∧
      WeakConverges (fun j => κ_n ((chain i).val j) (g i)) (μ_at i) :=
    fun i => Classical.choose_spec (hμ_at i)
  -- For each `i`, the diagonal `(κ_n (φ j) (g i))_j` weakly converges to `μ_at i`.
  -- Strategy: show that for `j ≥ i`, `φ j` is in `range ((chain i).val)`, and
  -- the function `fun j => (chain i).val ⁻¹ (φ j)` (restricted to `j ≥ i`) is
  -- StrictMono.  Then `(κ_n (φ (j+i)) (g i))_j = (κ_n ((chain i).val (η j)) (g i))_j`
  -- with `η : ℕ → ℕ` StrictMono, and the latter weakly converges.
  --
  -- We package this via the chain decomposition: for j ≥ i,
  -- (chain j).val = (chain i).val ∘ θ_{i,j}, so φ j = (chain i).val (θ_{i,j} j).
  -- Then j ↦ θ_{i,j} j (for j ≥ i) is strict mono since φ is strict mono.
  -- Chain factorisation: for `i ≤ j`, `(chain j).val = (chain i).val ∘ η`
  -- for some StrictMono `η : ℕ → ℕ`.
  have hChain_factor : ∀ i j, i ≤ j → ∃ η : ℕ → ℕ, StrictMono η ∧
      (chain j).val = (chain i).val ∘ η := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, rfl⟩
    | succ j hij ih =>
      obtain ⟨η, hη_mono, hη_eq⟩ := ih
      obtain ⟨ρ, hρ_mono, hρ_eq⟩ := hChain_succ j
      refine ⟨η ∘ ρ, hη_mono.comp hρ_mono, ?_⟩
      rw [hρ_eq, hη_eq]
      rfl
  -- Build per-i convergence of the diagonal.
  have hDiag_conv : ∀ i, WeakConverges (fun j => κ_n (φ j) (g i)) (μ_at i) := by
    intro i
    -- Define the index function `η_idx : ℕ → ℕ` such that φ (j + i) = (chain i).val (η_idx j).
    -- Use Classical.choose at each j on hChain_factor i (j+i) (Nat.le_add_left i j).
    -- We need η_idx StrictMono on ℕ.
    -- Cleaner: define η_idx j := the inverse-image of φ (j+i) under (chain i).val.
    -- Use injectivity of (chain i).val (StrictMono ⇒ Injective) to define η_idx well.
    have hψi_inj : Function.Injective (chain i).val := (hψ_mono i).injective
    -- For each j : ℕ, j+i is ≥ i, and (chain (j+i)).val factors through (chain i).val.
    have hExists : ∀ j : ℕ, ∃ m : ℕ, φ (j + i) = (chain i).val m := by
      intro j
      obtain ⟨η, _hη_mono, hη_eq⟩ := hChain_factor i (j + i) (Nat.le_add_left i j)
      refine ⟨η (j + i), ?_⟩
      have : φ (j + i) = (chain (j + i)).val (j + i) := rfl
      rw [this, hη_eq]
      rfl
    let η_idx : ℕ → ℕ := fun j => Classical.choose (hExists j)
    have hη_idx_eq : ∀ j, φ (j + i) = (chain i).val (η_idx j) :=
      fun j => Classical.choose_spec (hExists j)
    -- StrictMono of η_idx: φ is StrictMono and (chain i).val is StrictMono ⇒ injective.
    have hη_idx_mono : StrictMono η_idx := by
      intro a b hab
      have hφ_lt : φ (a + i) < φ (b + i) := hφ_mono (Nat.add_lt_add_right hab i)
      rw [hη_idx_eq, hη_idx_eq] at hφ_lt
      exact (hψ_mono i).lt_iff_lt.mp hφ_lt
    -- Tendsto on shifted: (κ_n (φ (j+i)) (g i)) = (κ_n ((chain i).val (η_idx j)) (g i)) → μ_at i.
    have hShift_conv :
        WeakConverges (fun j => κ_n (φ (j + i)) (g i)) (μ_at i) := by
      have h_eq : (fun j => κ_n (φ (j + i)) (g i)) =
                  (fun j => κ_n ((chain i).val (η_idx j)) (g i)) := by
        funext j
        rw [hη_idx_eq j]
      rw [h_eq]
      exact (hμ_at_spec i).2.comp hη_idx_mono
    -- Lift back to `(κ_n (φ j) (g i))_j → μ_at i` using shift invariance.
    -- The two sequences differ only on indices `j < i` (finitely many).
    intro f
    have h1 := hShift_conv f
    -- `Tendsto atTop (𝓝 _)` on a shift = same on original sequence.
    -- We have `Tendsto (fun j => g j) atTop l` iff `Tendsto (fun j => g (j+i)) atTop l`.
    have h_shift : Tendsto (fun j : ℕ => j + i) Filter.atTop Filter.atTop :=
      Filter.tendsto_add_atTop_nat i
    -- Tendsto of `fun j => ∫ f d(κ_n (φ j) (g i))` along shifted sequence equals
    -- the original sequence's tendsto, by tail-equivalence.
    -- Direction needed: original tendsto from shifted tendsto.
    -- Use that shift is cofinal but we need the other direction: tendsto on shifted
    -- ⇒ tendsto on the original (since the shifted sequence achieves all sufficiently
    -- large arguments). Use `Filter.tendsto_atTop_iff_eventually` characterisation.
    -- Alternative: shifted = original ∘ (·+i); tendsto along (·+i) of (∫ f d(κ_n (φ ·) (g i)))
    -- equals tendsto of (∫ f d(κ_n (φ ·) (g i))) along atTop.map (·+i), which is atTop.
    -- Direct: by tendsto_iff_seq_tendsto or just tail equality.
    -- Use `Filter.tendsto_iff_eventually` form via `Filter.tendsto_atTop_atTop`...
    -- Cleanest: tendsto_atTop_iff_eventually_atTop_le on shifted vs unshifted.
    -- Use: `(fun j => F (j + i))` has tendsto iff `F` does.  Standard.
    have h_iff : Tendsto (fun j : ℕ => ∫ x, f x ∂(κ_n (φ (j + i)) (g i))) Filter.atTop
                  (𝓝 (∫ x, f x ∂(μ_at i))) ↔
                 Tendsto (fun j : ℕ => ∫ x, f x ∂(κ_n (φ j) (g i))) Filter.atTop
                  (𝓝 (∫ x, f x ∂(μ_at i))) := by
      constructor
      · intro h
        -- `F ∘ (·+i)` tends to L ⇒ `F` tends to L.  Use `Filter.tendsto_iff_seq_tendsto`-flavoured;
        -- direct via `Filter.tendsto_atTop` characterisation (eventually within ε).
        rw [Metric.tendsto_atTop] at h ⊢
        intro ε hε_pos
        obtain ⟨N, hN⟩ := h ε hε_pos
        refine ⟨N + i, fun j hj => ?_⟩
        -- j ≥ N + i ⇒ j - i ≥ N (and j ≥ i, so j - i + i = j).
        have hji : j ≥ i := by linarith
        have hsub : j - i ≥ N := by omega
        have hadd : j - i + i = j := Nat.sub_add_cancel hji
        have := hN (j - i) hsub
        rwa [hadd] at this
      · intro h
        exact h.comp h_shift
    exact h_iff.mp h1
  -- Now build μ_lim_D : Ω → Measure 𝓨.
  -- For `a ∈ D`, `a = g k` for some k.  Define μ_lim_D a := μ_at k for the
  -- smallest such k.  For `a ∉ D`, use `0 : Measure 𝓨` (irrelevant).
  -- Use `Classical.choose` on D-membership existential.
  have hD_choice : ∀ a ∈ D, ∃ k : ℕ, g k = a := by
    intro a ha
    rw [hg_eq] at ha
    obtain ⟨k, hk⟩ := ha
    exact ⟨k, hk⟩
  let μ_lim_D : Ω → Measure 𝓨 := fun a =>
    if h : a ∈ D then μ_at (Classical.choose (hD_choice a h)) else 0
  refine ⟨φ, hφ_mono, μ_lim_D, ?_, ?_⟩
  · intro a ha
    simp only [μ_lim_D, dif_pos ha]
    exact (hμ_at_spec _).1
  · intro a ha
    simp only [μ_lim_D, dif_pos ha]
    -- Need: WeakConverges (fun j => κ_n (φ j) a) (μ_at k) where g k = a.
    set k : ℕ := Classical.choose (hD_choice a ha) with hk_def
    have hk_eq : g k = a := Classical.choose_spec (hD_choice a ha)
    -- Rewrite a → g k using hk_eq (motive friendly).
    have h_target : WeakConverges (fun j => κ_n (φ j) (g k)) (μ_at k) :=
      hDiag_conv k
    -- Convert: (fun j => κ_n (φ j) a) = (fun j => κ_n (φ j) (g k)).
    have h_funeq : (fun j => κ_n (φ j) a) = (fun j => κ_n (φ j) (g k)) := by
      funext j; rw [hk_eq]
    rw [h_funeq]
    exact h_target

/-- **Measurable kernel lift from a dense per-input family**.

Given a per-input probability-measure family `μ_lim_D : Ω → Measure 𝓨` defined
(at least) for `a` in a countable set `D ⊆ Ω`, lift it to a measurable kernel
`κ_lim : Kernel Ω 𝓨` that agrees with `μ_lim_D` on `D`.

**Construction strategy**:
* Off-`D` extension is arbitrary measurable (e.g. fixed `Measure.dirac y₀` for
  some chosen `y₀ : 𝓨`, extracting a probability measure from `[Nonempty 𝓨]`).
* Measurability of the resulting `Ω → Measure 𝓨` follows from the dichotomy
  "in `D`" (countable, hence measurable) `vs.` "off `D`".

**Markov property**: the caller's `μ_lim_D a` are probability measures on `D`,
and the off-`D` extension is also a probability measure, so the resulting
kernel is Markov. -/
theorem measurable_kernel_lift_from_dense
    {Ω 𝓨 : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace 𝓨] [TopologicalSpace 𝓨]
    [PolishSpace 𝓨] [BorelSpace 𝓨] [Nonempty 𝓨]
    {D : Set Ω} (hD_count : D.Countable)
    (μ_lim_D : Ω → Measure 𝓨)
    (hμ_lim_D_prob : ∀ a ∈ D, IsProbabilityMeasure (μ_lim_D a)) :
    ∃ κ_lim : Kernel Ω 𝓨, IsMarkovKernel κ_lim ∧
      ∀ a ∈ D, κ_lim a = μ_lim_D a := by
  classical
  -- Pick a default probability measure from `[Nonempty 𝓨]`.
  let y₀ : 𝓨 := Classical.arbitrary 𝓨
  let default_meas : Measure 𝓨 := Measure.dirac y₀
  have h_default_prob : IsProbabilityMeasure default_meas :=
    MeasureTheory.Measure.dirac.isProbabilityMeasure
  -- The lifted function: in `D` use `μ_lim_D a`, otherwise use `default_meas`.
  let f : Ω → Measure 𝓨 := fun a => if a ∈ D then μ_lim_D a else default_meas
  -- Measurability of `f`.  Use that `f` and the constant `default_meas` differ
  -- only on the countable set `D`.
  have h_const_meas : Measurable (fun _ : Ω => default_meas) := measurable_const
  have h_diff : { a : Ω | (fun _ => default_meas) a ≠ f a } ⊆ D := by
    intro a ha
    by_contra haD
    simp [f, haD] at ha
  have h_diff_count : Set.Countable { a : Ω | (fun _ => default_meas) a ≠ f a } :=
    hD_count.mono h_diff
  have h_f_meas : Measurable f :=
    h_const_meas.measurable_of_countable_ne h_diff_count
  -- Build the Kernel.
  refine ⟨⟨f, h_f_meas⟩, ?_, ?_⟩
  · -- IsMarkovKernel: every `f a` is a probability measure.
    refine ⟨fun a => ?_⟩
    change IsProbabilityMeasure (f a)
    by_cases ha : a ∈ D
    · simp only [f, if_pos ha]
      exact hμ_lim_D_prob a ha
    · simp only [f, if_neg ha]
      exact h_default_prob
  · -- Equality on D.
    intro a ha
    change f a = μ_lim_D a
    simp only [f, if_pos ha]

/-- **Kernel-level Prokhorov tightness and sub-sequence extraction**.

For a per-input-tight sequence of Markov kernels `(κ_n : ℕ → Kernel Ω 𝓨)`
on a complete second-countable pseudo-metric output space `𝓨`, there exists
a sub-sequence `φ : ℕ → ℕ` (strictly monotone), a countable dense set
`D ⊆ Ω`, and a limit Markov kernel `κ_lim : Kernel Ω 𝓨` such that
`(κ_{φ n} a) ⇒ κ_lim a` weakly for every `a ∈ D`.

**Construction**:

1. **Diagonal extraction over a countable dense subset of `Ω`**: if `Ω` is
   separable, pick a dense countable `D ⊆ Ω`. Apply
   `cantor_diagonal_extract_on_countable` to extract a sub-sequence `φ` such
   that for every `a ∈ D`, `(κ_{φ n} a)` converges weakly to some
   `μ_lim_D a : Measure 𝓨`.
2. **Lift `μ_lim_D` to a kernel**: by `measurable_kernel_lift_from_dense`,
   package `μ_lim_D` into a measurable Markov kernel `κ_lim : Kernel Ω 𝓨`.

Uses `MeasureTheory.Measure.Prokhorov.isCompact_closure_of_isTightMeasureSet`,
`MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`, and
`MeasureTheory.IsTightMeasureSet`. Polish `𝓨` is sufficient here; the standard
Euclidean-space typeclasses (`PolishSpace + BorelSpace`) discharge the `𝓨`
regularity.

The conclusion is per-dense-input rather than per-input: the "for all `a : Ω`"
form is *false* without extra continuity in `a` (kernel outputs need not vary
continuously in the input). `[SeparableSpace Ω]` ensures a countable dense set
`D ⊆ Ω` exists, and `[Nonempty 𝓨]` is needed for the off-`D` kernel extension. -/
theorem kernelProhorov_subseq_extraction
    {Ω 𝓨 : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [SeparableSpace Ω]
    [MeasurableSingletonClass Ω]
    [MeasurableSpace 𝓨] [TopologicalSpace 𝓨]
    [PolishSpace 𝓨] [BorelSpace 𝓨] [Nonempty 𝓨]
    (κ_n : ℕ → Kernel Ω 𝓨)
    -- Markov property feeds the Prokhorov compactness step and ensures the
    -- weak limit is a probability measure (closure under weak convergence).
    (hMarkov : ∀ n, IsMarkovKernel (κ_n n))
    -- Per-input tightness, dischargeable via `tightness_from_avgRisk_coercive`.
    (h_pointwise_tight : ∀ a : Ω,
      MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ => (κ_n n a : Measure 𝓨)))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ D : Set Ω, D.Countable ∧ Dense D ∧
      ∃ κ_lim : Kernel Ω 𝓨, IsMarkovKernel κ_lim ∧
        ∀ a ∈ D, WeakConverges (fun j => κ_n (φ j) a) (κ_lim a) := by
  -- Decompose into Cantor-diagonal extraction on a countable dense set
  -- + measurable kernel-lift extension.
  -- Step 1: pick a countable dense set `D` in `Ω`.
  obtain ⟨D, hD_count, hD_dense⟩ := exists_countable_dense Ω
  -- Step 2: Cantor-diagonal extraction over D using `extract_weak_subseq`
  --   on each `a ∈ D`. This gives a single sub-sequence `φ` working for
  --   every `a ∈ D`, with per-input limits `μ_lim_D : D → Measure 𝓨`.
  obtain ⟨φ, hφ_mono, μ_lim_D, hμ_lim_D_prob, hμ_lim_D_conv⟩ :=
    cantor_diagonal_extract_on_countable
      (D := D) hD_count κ_n hMarkov
      (fun a _ => h_pointwise_tight a)
  -- Step 3: lift `μ_lim_D` to a measurable kernel `κ_lim : Kernel Ω 𝓨` that
  --   agrees with `μ_lim_D` on `D`. Off-`D` extension is arbitrary measurable
  --   (e.g. constant probability measure); the conclusion only constrains
  --   behaviour on `D`.
  obtain ⟨κ_lim, hκ_lim_markov, hκ_lim_eq⟩ :=
    measurable_kernel_lift_from_dense
      (D := D) hD_count μ_lim_D hμ_lim_D_prob
  refine ⟨φ, hφ_mono, D, hD_count, hD_dense, κ_lim, hκ_lim_markov, ?_⟩
  intro a ha
  -- Rewrite `κ_lim a = μ_lim_D a` for `a ∈ D` and apply per-input convergence.
  rw [hκ_lim_eq a ha]
  exact hμ_lim_D_conv a ha

/-- **Per-input tightness from a coercive-loss bounded average risk**.

For a Markov-kernel sequence `(κ_n : ℕ → Kernel Ω 𝓨)` and a coercive
bowl-shaped loss `L : 𝓨 → ℝ≥0∞`, if the average risk under a fixed prior
`π` is uniformly bounded, then the per-input output measures
`Set.range (fun n => κ_n n a)` are tight.

**Construction**:

1. **Coercive ⇒ Chebyshev-tail control**: by `hL_coercive`, for every level
   `M < ⊤` the sublevel set `{y | L y < M}` is contained in a ball of some
   radius `R(M)` (depending on `M`). Equivalently, for every `R`, eventually
   `L y > M` outside ball-`R` (modulo dropping a small mass).
2. **Bounded avgRisk ⇒ tightness**: by Markov's inequality applied to the
   loss `L` against `κ_n n a` (composed with the input prior `π`), the
   measure of `{y | L y > M}` is bounded by `avgRisk / M`. As `M → ∞`, this
   forces the tail of `κ_n n a` to vanish uniformly in `n`, giving
   tightness in the Prokhorov sense (Mathlib `IsTightMeasureSet`).
3. **Output: tight kernel range per-input**: the resulting per-input
   `Set.range (fun n => κ_n n a)` is tight as a Set of measures on `𝓨`.

Uses `MeasureTheory.IsTightMeasureSet`,
`MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le`, and
the Markov inequality for `ℝ≥0∞` integrals.

**Why a finite-prior version (not pointwise)**: tightness inherits from
"bounded average risk under finite π" because
`avgRisk = ∫⁻ π, ∫⁻ y, L (y - …) ∂κ_n` controls the tail at every `a` in the
support of `π`. When the prior is a finite-support discretization, the
"per-input" version follows immediately.

**On the signature**: returns a tight per-input range for *every* `a : Ω`,
not just `a ∈ supp π`. Off-support behaviour is uncontrolled by average risk
alone, so the caller must restrict attention to a fixed input in the prior's
support before invoking the kernel-Prohorov extraction. -/
theorem tightness_from_avgRisk_coercive
    {Ω 𝓨 : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [MeasurableSpace 𝓨] [NormedAddCommGroup 𝓨]
    [BorelSpace 𝓨] [SecondCountableTopology 𝓨]
    -- `ProperSpace` (holds for `EuclideanSpace ℝ (Fin d)`) is required by
    -- `isTightMeasureSet_of_tendsto_measure_norm_gt`, the path from
    -- "norm-tail vanishes" to `IsTightMeasureSet`.
    [ProperSpace 𝓨]
    -- The loss `L` is stated abstractly on a normed space; the typical
    -- specialization is `𝓨 := EuclideanSpace ℝ (Fin d)`.
    (L : 𝓨 → ℝ≥0∞) (hL_meas : Measurable L)
    (hL_coercive : ∀ M : ℝ≥0∞, M < ⊤ →
      ∃ R : ℝ, 0 < R ∧ ∀ y : 𝓨, M ≤ L y ∨ ‖y‖ ≤ R)
    (κ_n : ℕ → Kernel Ω 𝓨)
    (_hMarkov : ∀ n, IsMarkovKernel (κ_n n))
    -- `B` is the uniform bound on the average risk (a finite bayesRisk on a
    -- finite prior, for the single-output loss `L`).
    (B : ℝ≥0∞) (hB_lt_top : B < ⊤)
    (h_pointwise_bdd : ∀ a : Ω, ∀ n, ∫⁻ y, L y ∂(κ_n n a) ≤ B) :
    ∀ a : Ω,
      MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ => (κ_n n a : Measure 𝓨))) := by
  intro a
  -- Apply the Mathlib brick: `IsTightMeasureSet` from norm-tail tending to 0.
  refine MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  -- Reduce `Tendsto _ atTop (𝓝 0)` on `ℝ≥0∞`-valued function to ε-δ form.
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε_pos
  -- Trivial branch: ε = ⊤.
  by_cases hε_top : ε = ⊤
  · refine ⟨0, fun r _ => ?_⟩
    rw [hε_top]
    exact le_top
  -- Pick `M := B/ε + 1`. Then `M ≠ 0`, `M < ⊤`, and `B/M ≤ ε`.
  set M : ℝ≥0∞ := B / ε + 1 with hM_def
  have hM_pos : (0 : ℝ≥0∞) < M := by
    have : (0 : ℝ≥0∞) < 1 := one_pos
    exact lt_of_lt_of_le this (le_add_self)
  have hM_ne_zero : M ≠ 0 := hM_pos.ne'
  have hε_ne_zero : ε ≠ 0 := hε_pos.ne'
  have hB_div_lt_top : B / ε < ⊤ := ENNReal.div_lt_top hB_lt_top.ne hε_ne_zero
  have hM_lt_top : M < ⊤ := by
    exact ENNReal.add_lt_top.mpr ⟨hB_div_lt_top, ENNReal.one_lt_top⟩
  have hM_ne_top : M ≠ ⊤ := hM_lt_top.ne
  -- Key bound: `B / M ≤ ε`. Since `M ≥ B/ε`, this is `B/(B/ε) ≤ ε`.
  have hBM : B / M ≤ ε := by
    -- Use `div_le_of_le_mul'` with `B ≤ M * ε`.
    refine ENNReal.div_le_of_le_mul' ?_
    -- `M * ε = (B/ε + 1) * ε = (B/ε) * ε + ε ≥ B + ε ≥ B`.
    have hcalc : M * ε = (B / ε) * ε + ε := by
      rw [hM_def, add_mul, one_mul]
    rw [hcalc]
    -- `(B/ε) * ε = B` when `ε ≠ 0`, `ε ≠ ⊤`.
    have h_div_mul : (B / ε) * ε = B := by
      rw [ENNReal.div_mul_cancel hε_ne_zero hε_top]
    rw [h_div_mul]
    exact le_self_add
  -- Apply coercivity at level `M` to get a radius `R`.
  obtain ⟨R, _hR_pos, hR⟩ := hL_coercive M hM_lt_top
  refine ⟨R, fun r hr => ?_⟩
  -- Goal: `⨆ μ ∈ Set.range _, μ {y | r < ‖y‖} ≤ ε`.
  rw [iSup_le_iff]
  intro μ
  rw [iSup_le_iff]
  rintro ⟨n, rfl⟩
  -- For each `n`: `(κ_n n a) {y | r < ‖y‖} ≤ (κ_n n a) {y | M ≤ L y} ≤ B/M ≤ ε`.
  -- Inclusion: if `r < ‖y‖` and `r ≥ R`, then `R < ‖y‖`, so `¬(‖y‖ ≤ R)`,
  -- hence by `hR y`: `M ≤ L y`.
  have h_subset : {y : 𝓨 | r < ‖y‖} ⊆ {y : 𝓨 | M ≤ L y} := by
    intro y hy
    have h_norm : R < ‖y‖ := lt_of_le_of_lt hr hy
    have h_not_le : ¬ ‖y‖ ≤ R := not_le.mpr h_norm
    exact (hR y).resolve_right h_not_le
  -- Markov inequality: `(κ_n n a) {y | M ≤ L y} ≤ (∫⁻ y, L y) / M`.
  have h_markov : (κ_n n a) {y : 𝓨 | M ≤ L y} ≤ (∫⁻ y, L y ∂(κ_n n a)) / M :=
    MeasureTheory.meas_ge_le_lintegral_div hL_meas.aemeasurable hM_ne_zero hM_ne_top
  calc (κ_n n a) {y : 𝓨 | r < ‖y‖}
      ≤ (κ_n n a) {y : 𝓨 | M ≤ L y} := measure_mono h_subset
    _ ≤ (∫⁻ y, L y ∂(κ_n n a)) / M := h_markov
    _ ≤ B / M := by
        apply ENNReal.div_le_div_right
        exact h_pointwise_bdd a n
    _ ≤ ε := hBM

end AsymptoticStatistics
