module
/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file
LICENSES/formal-learning-theory-kernel-Apache-2.0.txt.
Authors: Dhruv Gupta

This file adapts and splits the analytic-capacitability portion of
FLT_Proofs/PureMath/ChoquetCapacity.lean at commit
b1b9d16a552e3e09bfbb8151fe6aa14c805d7979.
-/
public import StatLean.AsymptoticStatistics.ForMathlib.ChoquetCapacity.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Metrizable.Basic

@[expose] public section

/-!
# Choquet capacitability of analytic sets

This file develops the Baire-space cylinder algebra and the Choquet capacitability
theorem for analytic subsets of Polish spaces.

The declarations are adapted from Dhruv Gupta's *Formal Learning Theory Kernel*,
pinned at commit `b1b9d16a552e3e09bfbb8151fe6aa14c805d7979` (Apache-2.0).

## Main declarations

* `MeasureTheory.AnalyticSet.cap_eq_iSup_isCompact`
* `MeasureTheory.AnalyticSet.compactCap_eq`
-/

open MeasureTheory Set Filter Topology

/-- Rewrite `compactCap` as an indexed supremum over compact subsets. -/
private lemma compactCap_eq_iSup_isCompact
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (s : Set α) :
    MeasureTheory.compactCap μ s =
      ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ s), μ K := by
  unfold MeasureTheory.compactCap
  apply le_antisymm
  · apply sSup_le
    rintro r ⟨K, hKc, hKs, rfl⟩
    exact le_iSup_of_le K (le_iSup_of_le hKc (le_iSup_of_le hKs le_rfl))
  · apply iSup_le
    intro K
    apply iSup_le
    intro hKc
    apply iSup_le
    intro hKs
    apply le_csSup
    · exact ⟨μ Set.univ, fun _ ⟨_, _, _, hr⟩ =>
        hr ▸ measure_mono (Set.subset_univ _)⟩
    · exact ⟨K, hKc, hKs, rfl⟩

/-- Cylinder set `{g | ∀ i ≤ n, g i ≤ N i}`. -/
private abbrev Cyl (N : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  {g | ∀ i, i ≤ n → g i ≤ N i}

/-- Bounded-functions set `{g | ∀ i, g i ≤ N i}`. -/
private abbrev Bnd (N : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {g | ∀ i, g i ≤ N i}

/-- The coordinatewise bounded Baire-space set is compact. -/
private lemma isCompact_bnd (N : ℕ → ℕ) : IsCompact (Bnd N) := by
  have : Bnd N = Set.pi Set.univ (fun i => Set.Iic (N i)) := by
    ext g
    simp only [Bnd, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic]
  rw [this]
  exact isCompact_univ_pi fun i => (Set.finite_Iic (N i)).isCompact

/-- A bounded function belongs to every finite cylinder. -/
private lemma bnd_subset_cyl (N : ℕ → ℕ) (n : ℕ) : Bnd N ⊆ Cyl N n := by
  exact fun _ hg i _ => hg i

/-- Split a cylinder by the next-coordinate bound. -/
private lemma cyl_succ_eq (N : ℕ → ℕ) (n : ℕ) :
    Cyl N n = ⋃ k : ℕ, (Cyl N n ∩ {g | g (n + 1) ≤ k}) := by
  ext g
  simp only [Cyl, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
  exact ⟨fun h => ⟨g (n + 1), h, le_refl _⟩, fun ⟨_, h, _⟩ => h⟩

/-- The next-coordinate cylinder split is monotone in its bound. -/
private lemma monotone_cyl_split (N : ℕ → ℕ) (n : ℕ) :
    Monotone (fun k => Cyl N n ∩ {g : ℕ → ℕ | g (n + 1) ≤ k}) := by
  intro a b hab x ⟨hx1, hx2⟩
  exact ⟨hx1, le_trans hx2 hab⟩

/-- Updating the next coordinate converts a split cylinder to a longer cylinder. -/
private lemma cyl_inter_eq_cyl_update (N : ℕ → ℕ) (n k : ℕ) :
    Cyl N n ∩ {g : ℕ → ℕ | g (n + 1) ≤ k} =
      Cyl (Function.update N (n + 1) k) (n + 1) := by
  ext g
  simp only [Cyl, Set.mem_inter_iff, Set.mem_setOf_eq, Function.update]
  constructor
  · rintro ⟨hg, hgk⟩ i hi
    by_cases heq : i = n + 1
    · subst heq
      simp [hgk]
    · have : i ≤ n := by omega
      simp [heq, hg i this]
  · intro hg
    constructor
    · intro i hi
      have hne : i ≠ n + 1 := by omega
      simpa [hne] using hg i (by omega)
    · specialize hg (n + 1) (le_refl _)
      simpa using hg

/-- Cylinder bounds depend only on coordinates at most the cylinder level. -/
private lemma cyl_ext (N N' : ℕ → ℕ) (n : ℕ) (h : ∀ i, i ≤ n → N i = N' i) :
    Cyl N n = Cyl N' n := by
  ext g
  simp only [Cyl, Set.mem_setOf_eq]
  exact ⟨fun hg i hi => h i hi ▸ hg i hi, fun hg i hi => (h i hi).symm ▸ hg i hi⟩

/-- Coordinatewise truncation into `Bnd N`.

Edge behavior is literal coordinatewise `min`; there is no exceptional or
degenerate branch. -/
private noncomputable def truncate (N : ℕ → ℕ) (g : ℕ → ℕ) : ℕ → ℕ := by
  exact fun i => min (g i) (N i)

/-- Truncation belongs to the coordinatewise bounded set. -/
private lemma truncate_mem_bnd (N : ℕ → ℕ) (g : ℕ → ℕ) : truncate N g ∈ Bnd N := by
  exact fun _ => min_le_right _ _

/-- Truncation agrees with a function on coordinates controlled by a cylinder. -/
private lemma truncate_agree_on_cyl (N : ℕ → ℕ) (n : ℕ) (g : ℕ → ℕ)
    (hg : g ∈ Cyl N n) :
    ∀ i, i ≤ n → truncate N g i = g i := by
  intro i hi
  simp only [truncate, min_eq_left (hg i hi)]

/-- The intersection of closures of cylinder images equals the image of the compact
bounded-functions set. -/
private lemma iInter_closure_image_cyl_eq
    {α : Type*} [TopologicalSpace α] [PolishSpace α]
    {f : (ℕ → ℕ) → α} (hf : Continuous f) (N : ℕ → ℕ) :
    ⋂ n, closure (f '' Cyl N n) = f '' Bnd N := by
  haveI : T2Space α := inferInstance
  apply Set.Subset.antisymm
  · letI := TopologicalSpace.upgradeIsCompletelyMetrizable α
    intro y hy
    simp only [Set.mem_iInter] at hy
    have : ∀ n, ∃ g ∈ Cyl N n, dist (f g) y < 1 / (↑n + 1) := by
      intro n
      have hn : y ∈ closure (f '' Cyl N n) := hy n
      rw [Metric.mem_closure_iff] at hn
      obtain ⟨z, hz, hd⟩ := hn (1 / (↑n + 1)) (by positivity)
      obtain ⟨g, hg, hfg⟩ := hz
      exact ⟨g, hg, by rw [hfg, dist_comm]; exact hd⟩
    choose g hg_cyl hg_dist using this
    let g' : ℕ → (ℕ → ℕ) := fun n => truncate N (g n)
    have hg'_bnd : ∀ n, g' n ∈ Bnd N := fun n => truncate_mem_bnd N (g n)
    have hg'_agree : ∀ n i, i ≤ n → g' n i = g n i :=
      fun n => truncate_agree_on_cyl N n (g n) (hg_cyl n)
    have hBnd_seq := (isCompact_bnd N).isSeqCompact
    obtain ⟨g_star, hg_star_bnd, φ, hφ_strict, hg'_conv⟩ :=
      hBnd_seq (fun n => hg'_bnd n)
    have hg_conv : Tendsto (fun n => g (φ n)) atTop (𝓝 g_star) := by
      rw [tendsto_pi_nhds]
      intro i
      simp only [nhds_discrete, Filter.tendsto_pure]
      have hg'_ev : ∀ᶠ n in atTop, g' (φ n) i = g_star i := by
        rw [tendsto_pi_nhds] at hg'_conv
        have h := hg'_conv i
        simp only [nhds_discrete, Filter.tendsto_pure] at h
        exact h
      have hφ_ev : ∀ᶠ n in atTop, i ≤ φ n :=
        (hφ_strict.tendsto_atTop).eventually (Filter.eventually_ge_atTop i)
      filter_upwards [hg'_ev, hφ_ev] with n h1 h2
      rw [← h1, hg'_agree (φ n) i h2]
    have hf_conv : Tendsto (fun n => f (g (φ n))) atTop (𝓝 (f g_star)) :=
      hf.continuousAt.tendsto.comp hg_conv
    have hfy : Tendsto (fun n => f (g (φ n))) atTop (𝓝 y) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have h1div : Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h_comp : Tendsto (fun n => (1 : ℝ) / (↑(φ n) + 1)) atTop (𝓝 0) :=
        h1div.comp hφ_strict.tendsto_atTop
      obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp h_comp) ε hε
      use M
      intro n hn
      have hsmall : (1 : ℝ) / (↑(φ n) + 1) < ε := by
        have h := hM n hn
        rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at h
        exact h
      exact lt_trans (hg_dist (φ n)) hsmall
    have hfg_star : f g_star = y := tendsto_nhds_unique hf_conv hfy
    exact ⟨g_star, hg_star_bnd, hfg_star⟩
  · intro y hy
    simp only [Set.mem_iInter]
    intro n
    apply subset_closure
    obtain ⟨g, hg, hfg⟩ := hy
    exact ⟨g, bnd_subset_cyl N n hg, hfg⟩

/-- Choquet capacitability: on an analytic set, a Choquet capacity is the supremum of
its values on compact subsets.

Polish/Borel structure is the theorem's mathematical scope. -/
theorem MeasureTheory.AnalyticSet.cap_eq_iSup_isCompact
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {cap : Set α → ENNReal}
    (hcap : MeasureTheory.IsChoquetCapacity cap)
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    cap s = ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ s), cap K := by
  apply le_antisymm
  · rw [AnalyticSet] at hs
    rcases hs with rfl | ⟨f, hf_cont, hf_range⟩
    · exact le_iSup_of_le ∅ (le_iSup_of_le isCompact_empty
        (le_iSup_of_le (Set.empty_subset _) le_rfl))
    · subst hf_range
      apply le_of_forall_lt_imp_le_of_dense
      intro t ht
      have hrange_union : range f = ⋃ k, f '' {g : ℕ → ℕ | g 0 ≤ k} := by
        rw [← Set.image_univ,
          show (Set.univ : Set (ℕ → ℕ)) = ⋃ k, {g : ℕ → ℕ | g 0 ≤ k} from by
            ext g
            simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
            exact ⟨g 0, le_refl _⟩,
          Set.image_iUnion]
      have hmono_base : Monotone (fun k => f '' {g : ℕ → ℕ | g 0 ≤ k}) := by
        intro a b hab
        apply Set.image_mono
        intro x (hx : x 0 ≤ a)
        exact le_trans hx hab
      rw [hrange_union, hcap.iUnion_nat _ hmono_base] at ht
      obtain ⟨k₀, hk₀⟩ := lt_iSup_iff.mp ht
      have hcyl0 : f '' {g : ℕ → ℕ | g 0 ≤ k₀} = f '' Cyl (fun _ => k₀) 0 := by
        congr 1
        ext g
        simp [Cyl]
      have rec_step : ∀ (M : ℕ → ℕ) (n : ℕ), t < cap (f '' Cyl M n) →
          ∃ k, t < cap (f '' Cyl (Function.update M (n + 1) k) (n + 1)) := by
        intro M n hlt_M
        have hsplit : cap (f '' Cyl M n) =
            ⨆ k, cap (f '' (Cyl M n ∩ {g | g (n + 1) ≤ k})) := by
          conv_lhs => rw [cyl_succ_eq M n, Set.image_iUnion]
          exact hcap.iUnion_nat _
            (fun a b h => Set.image_mono (monotone_cyl_split M n h))
        rw [hsplit] at hlt_M
        obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt_M
        exact ⟨k, by rwa [cyl_inter_eq_cyl_update] at hk⟩
      let build : (n : ℕ) → { M : ℕ → ℕ // t < cap (f '' Cyl M n) } :=
        fun n => Nat.rec
          ⟨fun _ => k₀, hcyl0 ▸ hk₀⟩
          (fun m ⟨M_prev, hM_prev⟩ =>
            ⟨Function.update M_prev (m + 1)
              (Classical.choose (rec_step M_prev m hM_prev)),
             Classical.choose_spec (rec_step M_prev m hM_prev)⟩)
          n
      let N_seq : ℕ → (ℕ → ℕ) := fun n => (build n).val
      have hN_seq_prop : ∀ n, t < cap (f '' Cyl (N_seq n) n) :=
        fun n => (build n).property
      have hN_seq_consistent : ∀ n i, i ≤ n → N_seq (n + 1) i = N_seq n i := by
        intro n i hi
        change (Function.update (N_seq n) (n + 1) _) i = N_seq n i
        exact Function.update_of_ne (by omega) ..
      let N : ℕ → ℕ := fun i => N_seq i i
      have hN_agree : ∀ n i, i ≤ n → N i = N_seq n i := by
        intro n
        induction n with
        | zero =>
            intro i hi
            simp only [Nat.le_zero] at hi
            subst hi
            rfl
        | succ m ih =>
            intro i hi
            by_cases heq : i = m + 1
            · subst heq
              rfl
            · have him : i ≤ m := by omega
              change N_seq i i = N_seq (m + 1) i
              rw [hN_seq_consistent m i him]
              exact ih i him
      have hcyl_eq : ∀ n, Cyl N n = Cyl (N_seq n) n :=
        fun n => cyl_ext N (N_seq n) n (hN_agree n)
      have hcap_bound : ∀ n, t < cap (f '' Cyl N n) :=
        fun n => hcyl_eq n ▸ hN_seq_prop n
      set E := fun n => closure (f '' Cyl N n) with hE_def
      have hE_closed : ∀ n, IsClosed (E n) := fun _ => isClosed_closure
      have hE_anti : Antitone E := by
        intro m n hmn
        apply closure_mono
        apply Set.image_mono
        intro x (hx : ∀ i, i ≤ n → x i ≤ N i) i hi
        exact hx i (le_trans hi hmn)
      have hE_cap : ∀ n, t < cap (E n) := by
        intro n
        exact lt_of_lt_of_le (hcap_bound n) (hcap.mono subset_closure)
      have hE_inter_cap : cap (⋂ n, E n) = ⨅ n, cap (E n) :=
        hcap.iInter_closed E hE_anti hE_closed
      have ht_le : t ≤ cap (⋂ n, E n) := by
        rw [hE_inter_cap]
        exact le_iInf fun n => le_of_lt (hE_cap n)
      have hkey : ⋂ n, E n = f '' Bnd N :=
        iInter_closure_image_cyl_eq hf_cont N
      have hK_compact : IsCompact (f '' Bnd N) := (isCompact_bnd N).image hf_cont
      have hK_sub : f '' Bnd N ⊆ range f := Set.image_subset_range f _
      calc
        t ≤ cap (⋂ n, E n) := ht_le
        _ = cap (f '' Bnd N) := by rw [hkey]
        _ ≤ ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ range f), cap K :=
          le_iSup_of_le _ (le_iSup_of_le hK_compact (le_iSup_of_le hK_sub le_rfl))
  · exact iSup_le fun K => iSup_le fun _ => iSup_le fun hKs => hcap.mono hKs

/-- For an analytic set and a finite Borel measure, compact capacity equals measure.

Finite-measure and Polish/Borel assumptions state the mathematical scope. -/
theorem MeasureTheory.AnalyticSet.compactCap_eq
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    MeasureTheory.compactCap μ s = μ s := by
  rw [compactCap_eq_iSup_isCompact]
  exact (hs.cap_eq_iSup_isCompact (measure_isChoquetCapacity μ)).symm
