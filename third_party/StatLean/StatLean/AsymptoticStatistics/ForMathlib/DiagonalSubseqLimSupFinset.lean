module
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Bases

@[expose] public section

/-!
# Diagonal-attaining sub-sequence on a monotone finite-index chain

This file provides the **diagonal-attaining `Tendsto` form** of the Cantor-diagonal
sub-sequence extraction on a monotone finite-index chain: given a monotone chain of
finsets `I k` and a doubly-indexed family `a n h`, one can extract a diagonal
sub-sequence `φ` along which `⨆ h ∈ I k, a (φ k) h` converges to
`⨆ k, liminf_n ⨆ h ∈ I k, a n h`.

The headline declaration is `diagonal_subseq_attaining_lim_sup_finset`. It pairs
naturally with `exists_strictMono_tendsto_liminf_ennreal` for extracting a diagonal
sub-sequence attaining the `⨆_k liminf_n` of a per-finset-sup quantity.
-/

open Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace AsymptoticStatistics
namespace Prohorov

/-! ### Helpers: ENNReal cluster-point liminf-attainer

Two lemmas about ENNReal-valued sequences, used to build
`diagonal_subseq_attaining_lim_sup_finset` and reusable on their own.
-/

/-- In `ℝ≥0∞`, every open neighbourhood of `Filter.liminf u atTop` is
frequently hit by `u`. This is the cluster-point property of `liminf`,
specialised to ENNReal (where `IsBounded` side-conditions are automatic).

Paired with `exists_strictMono_tendsto_liminf_ennreal`, which packages this fact
into the diagonal-extraction form `∃ ψ, u ∘ ψ ⟶ liminf u`. -/
lemma frequently_mem_nhds_liminf_ennreal
    (u : ℕ → ℝ≥0∞) {s : Set ℝ≥0∞} (hs : s ∈ 𝓝 (Filter.liminf u Filter.atTop)) :
    ∃ᶠ n in Filter.atTop, u n ∈ s := by
  set L : ℝ≥0∞ := Filter.liminf u Filter.atTop with hL_def
  by_cases hL_top : L = ⊤
  · rw [hL_top] at hs
    obtain ⟨r, hr_lt, hr_sub⟩ := (ENNReal.nhds_top_basis).mem_iff.mp hs
    have h_ev : ∀ᶠ n in Filter.atTop, r < u n := by
      have h_lt : r < L := by rw [hL_top]; exact hr_lt
      exact eventually_lt_of_lt_liminf (u := u) (f := Filter.atTop) (b := r) h_lt
    exact h_ev.frequently.mono (fun n hn => hr_sub hn)
  · have hL_lt_top : L < ⊤ := lt_top_iff_ne_top.mpr hL_top
    by_cases hL_zero : L = 0
    · rw [hL_zero] at hs
      obtain ⟨ε, hε_pos, hε_sub⟩ := ENNReal.nhds_zero_basis_Iic.mem_iff.mp hs
      have h_freq : ∃ᶠ n in Filter.atTop, u n < ε := by
        have h_lt : Filter.liminf u Filter.atTop < ε := by
          rw [← hL_def, hL_zero]; exact hε_pos
        refine frequently_lt_of_liminf_lt (u := u) (f := Filter.atTop) (b := ε)
          ?_ h_lt
        -- IsCoboundedUnder (· ≥ ·) atTop u: for ENNReal use isCobounded_ge_of_top
        -- (which gives IsCobounded (· ≥ ·) (map u atTop), unfolding to IsCoboundedUnder).
        exact isCobounded_ge_of_top
      exact h_freq.mono (fun n hn => hε_sub (le_of_lt hn))
    · have hL_pos : 0 < L := pos_iff_ne_zero.mpr hL_zero
      obtain ⟨l, u', ⟨hl_lt_L, hL_lt_u'⟩, hIoo_sub⟩ :=
        (mem_nhds_iff_exists_Ioo_subset' ⟨0, hL_pos⟩ ⟨⊤, hL_lt_top⟩).mp hs
      have h_ev_lower : ∀ᶠ n in Filter.atTop, l < u n := by
        have h_lt : l < L := hl_lt_L
        exact eventually_lt_of_lt_liminf (u := u) (f := Filter.atTop) (b := l) h_lt
      have h_freq_upper : ∃ᶠ n in Filter.atTop, u n < u' := by
        have h_lt : Filter.liminf u Filter.atTop < u' := by
          rw [← hL_def]; exact hL_lt_u'
        refine frequently_lt_of_liminf_lt (u := u) (f := Filter.atTop) (b := u')
          ?_ h_lt
        exact isCobounded_ge_of_top
      refine (h_freq_upper.and_eventually h_ev_lower).mono ?_
      rintro n ⟨hnu, hnl⟩
      exact hIoo_sub ⟨hnl, hnu⟩

/-- For each sequence `u : ℕ → ℝ≥0∞`, there exists a strictly monotone
extraction `ψ : ℕ → ℕ` along which `u ∘ ψ` converges to `Filter.liminf u atTop`.

Combines `frequently_mem_nhds_liminf_ennreal` (cluster-point property) with
`TopologicalSpace.FirstCountableTopology.tendsto_subseq`. -/
lemma exists_strictMono_tendsto_liminf_ennreal (u : ℕ → ℝ≥0∞) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Filter.Tendsto (u ∘ ψ) Filter.atTop
        (𝓝 (Filter.liminf u Filter.atTop)) := by
  have hCluster :
      MapClusterPt (Filter.liminf u Filter.atTop) Filter.atTop u := by
    rw [mapClusterPt_iff_frequently]
    intro s hs
    exact frequently_mem_nhds_liminf_ennreal u hs
  exact TopologicalSpace.FirstCountableTopology.tendsto_subseq hCluster

/-! ### Main theorem: diagonal Cantor extraction on a monotone finset chain -/

/-- **Cantor-diagonal sub-sequence attaining `⨆_k liminf_n ⨆_{h ∈ I k} a_n h`**
on a monotone finite-index chain. See the module docstring for the precise
mathematical content. -/
theorem diagonal_subseq_attaining_lim_sup_finset
    {α : Type*} (I : ℕ → Finset α)
    (h_mono : ∀ k, I k ⊆ I (k + 1))
    (a : ℕ → α → ℝ≥0∞) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun k => ⨆ h ∈ I k, a (φ k) h) Filter.atTop
        (𝓝 (⨆ k, Filter.liminf (fun n => ⨆ h ∈ I k, a n h) Filter.atTop)) := by
  classical
  set b : ℕ → ℕ → ℝ≥0∞ := fun k n => ⨆ h ∈ I k, a n h with hb_def
  set L : ℕ → ℝ≥0∞ := fun k => Filter.liminf (fun n => b k n) Filter.atTop with hL_def
  set R : ℝ≥0∞ := ⨆ k, L k with hR_def
  -- Monotonicity facts.
  have h_b_mono_k : ∀ n, Monotone (fun k => b k n) := by
    intro n
    refine monotone_nat_of_le_succ (fun k => ?_)
    refine iSup₂_le (fun h hh => ?_)
    exact le_iSup₂ (f := fun h _ => a n h) h (h_mono k hh)
  have hL_mono : Monotone L := by
    intro k k' hkk'
    refine Filter.liminf_le_liminf ?_
    exact Filter.Eventually.of_forall (fun n => h_b_mono_k n hkk')
  have hL_tendsto_R : Filter.Tendsto L Filter.atTop (𝓝 R) :=
    tendsto_atTop_iSup hL_mono
  -- Per-k subseq tending to L k.
  have hExtract : ∀ k, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Filter.Tendsto ((b k) ∘ ψ) Filter.atTop (𝓝 (L k)) := by
    intro k; exact exists_strictMono_tendsto_liminf_ennreal (b k)
  choose ψ hψ_mono hψ_tendsto using hExtract
  -- ε k := (k+1 : ℝ≥0∞)⁻¹, tending to 0.
  set ε : ℕ → ℝ≥0∞ := fun k => ((k : ℝ≥0∞) + 1)⁻¹ with hε_def
  have h_kp1_lt_top : ∀ k : ℕ, ((k : ℝ≥0∞) + 1) < ⊤ := by
    intro k
    refine ENNReal.add_lt_top.mpr ⟨?_, ENNReal.one_lt_top⟩
    exact lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top k)
  have h_kp1_ne_top : ∀ k : ℕ, ((k : ℝ≥0∞) + 1) ≠ ⊤ :=
    fun k => (h_kp1_lt_top k).ne
  have h_kp1_ne_zero : ∀ k : ℕ, ((k : ℝ≥0∞) + 1) ≠ 0 := by
    intro k
    have h1 : (1 : ℝ≥0∞) ≤ (k : ℝ≥0∞) + 1 := le_add_self
    have hpos : (0 : ℝ≥0∞) < 1 := by exact one_pos
    exact (lt_of_lt_of_le hpos h1).ne'
  have hε_pos : ∀ k, 0 < ε k := by
    intro k; rw [hε_def]; exact ENNReal.inv_pos.mpr (h_kp1_ne_top k)
  have hε_ne_top : ∀ k, ε k ≠ ⊤ := by
    intro k; rw [hε_def]; exact ENNReal.inv_ne_top.mpr (h_kp1_ne_zero k)
  have hε_tendsto : Filter.Tendsto ε Filter.atTop (𝓝 0) := by
    have h_nat_top : Filter.Tendsto (fun k : ℕ => (k : ℝ≥0∞)) Filter.atTop (𝓝 ⊤) :=
      ENNReal.tendsto_nat_nhds_top
    have h_top : Filter.Tendsto (fun k : ℕ => (k : ℝ≥0∞) + 1) Filter.atTop (𝓝 ⊤) := by
      have h1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) Filter.atTop (𝓝 1) :=
        tendsto_const_nhds
      have := h_nat_top.add h1
      simpa using this
    have h_inv : Filter.Tendsto (fun x : ℝ≥0∞ => x⁻¹) (𝓝 ⊤) (𝓝 0) := by
      have hc : Continuous (fun x : ℝ≥0∞ => x⁻¹) := continuous_inv
      have := hc.tendsto ⊤
      simpa [ENNReal.inv_top] using this
    have : Filter.Tendsto (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) Filter.atTop (𝓝 0) :=
      h_inv.comp h_top
    exact this
  -- T k := L k ⊓ (k + 1) — a finite "trimmed" target that → R.
  set T : ℕ → ℝ≥0∞ := fun k => L k ⊓ ((k : ℝ≥0∞) + 1) with hT_def
  have hT_le_L : ∀ k, T k ≤ L k := fun k => inf_le_left
  have hT_le_kp1 : ∀ k, T k ≤ (k : ℝ≥0∞) + 1 := fun k => inf_le_right
  have hT_lt_top : ∀ k, T k < ⊤ :=
    fun k => lt_of_le_of_lt (hT_le_kp1 k) (h_kp1_lt_top k)
  have hT_ne_top : ∀ k, T k ≠ ⊤ := fun k => (hT_lt_top k).ne
  have h_kp1_to_top : Filter.Tendsto (fun k : ℕ => (k : ℝ≥0∞) + 1) Filter.atTop (𝓝 ⊤) := by
    have h_nat_top : Filter.Tendsto (fun k : ℕ => (k : ℝ≥0∞)) Filter.atTop (𝓝 ⊤) :=
      ENNReal.tendsto_nat_nhds_top
    have h1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) Filter.atTop (𝓝 1) :=
      tendsto_const_nhds
    have := h_nat_top.add h1
    simpa using this
  have hT_tendsto_R : Filter.Tendsto T Filter.atTop (𝓝 R) := by
    -- inf is continuous on ℝ≥0∞ × ℝ≥0∞ (LinearOrder + OrderTopology → TopologicalLattice).
    have h_inf := Filter.Tendsto.inf_nhds hL_tendsto_R h_kp1_to_top
    -- R ⊓ ⊤ = R since R ≤ ⊤.
    have hRtop : R ⊓ (⊤ : ℝ≥0∞) = R := inf_top_eq R
    simpa [hRtop] using h_inf
  -- Aux existential.
  have hAux : ∀ k N, ∃ m : ℕ,
      ψ k m > N ∧
      (T k - ε k : ℝ≥0∞) < b k (ψ k m) + ε k ∧
      b k (ψ k m) ≤ L k + ε k := by
    intro k N
    have h_psi_grow : ∀ᶠ m in Filter.atTop, ψ k m > N := by
      have h_ge : ∀ m, m ≤ ψ k m := fun m => (hψ_mono k).id_le m
      refine Filter.eventually_atTop.mpr ⟨N + 1, fun m hm => ?_⟩
      have hle : N + 1 ≤ ψ k m := le_trans hm (h_ge m)
      omega
    -- Lower bound: T k - ε k < b k (ψ k m) + ε k eventually.
    have h_lower : ∀ᶠ m in Filter.atTop, (T k - ε k : ℝ≥0∞) < b k (ψ k m) + ε k := by
      by_cases hcase : T k ≤ ε k
      · have hTeps : (T k - ε k : ℝ≥0∞) = 0 := tsub_eq_zero_of_le hcase
        refine Filter.Eventually.of_forall (fun m => ?_)
        rw [hTeps]
        calc (0 : ℝ≥0∞) < ε k := hε_pos k
          _ ≤ b k (ψ k m) + ε k := le_add_self
      · push Not at hcase
        have hT_pos : 0 < T k := lt_of_le_of_lt (zero_le) hcase
        have hT_sub_lt : (T k - ε k : ℝ≥0∞) < T k :=
          ENNReal.sub_lt_self (hT_ne_top k) hT_pos.ne' (hε_pos k).ne'
        have hT_sub_lt_L : (T k - ε k : ℝ≥0∞) < L k :=
          lt_of_lt_of_le hT_sub_lt (hT_le_L k)
        have h_open : Ioi (T k - ε k) ∈ 𝓝 (L k) :=
          IsOpen.mem_nhds isOpen_Ioi hT_sub_lt_L
        have h_ev_gt := (hψ_tendsto k).eventually h_open
        refine h_ev_gt.mono (fun m hm => ?_)
        have hbk : (b k ∘ ψ k) m = b k (ψ k m) := rfl
        rw [hbk] at hm
        calc (T k - ε k : ℝ≥0∞) < b k (ψ k m) := hm
          _ ≤ b k (ψ k m) + ε k := le_self_add
    -- Upper bound: b k (ψ k m) ≤ L k + ε k.
    have h_upper : ∀ᶠ m in Filter.atTop, b k (ψ k m) ≤ L k + ε k := by
      by_cases hL_top_k : L k = ⊤
      · refine Filter.Eventually.of_forall (fun m => ?_)
        rw [hL_top_k]; simp
      · have h_R_in_nhds : Iio (L k + ε k) ∈ 𝓝 (L k) := by
          refine IsOpen.mem_nhds isOpen_Iio ?_
          exact ENNReal.lt_add_right hL_top_k (hε_pos k).ne'
        have h_ev := (hψ_tendsto k).eventually h_R_in_nhds
        refine h_ev.mono (fun m hm => ?_)
        have hbk : (b k ∘ ψ k) m = b k (ψ k m) := rfl
        rw [hbk] at hm
        exact le_of_lt hm
    obtain ⟨m, hm⟩ := (h_psi_grow.and (h_lower.and h_upper)).exists
    exact ⟨m, hm.1, hm.2.1, hm.2.2⟩
  -- Build m : ℕ → ℕ via Nat.rec.
  let m : ℕ → ℕ := fun k =>
    Nat.rec (Classical.choose (hAux 0 0))
      (fun k' m_k' => Classical.choose (hAux (k' + 1) (ψ k' m_k'))) k
  have hm_zero : m 0 = Classical.choose (hAux 0 0) := rfl
  have hm_succ : ∀ k, m (k + 1) = Classical.choose (hAux (k + 1) (ψ k (m k))) :=
    fun _ => rfl
  have hm_spec : ∀ k,
      ψ k (m k) > (if k = 0 then 0 else ψ (k - 1) (m (k - 1))) ∧
      (T k - ε k : ℝ≥0∞) < b k (ψ k (m k)) + ε k ∧
      b k (ψ k (m k)) ≤ L k + ε k := by
    intro k
    induction k with
    | zero =>
      simp only [if_true]
      rw [hm_zero]
      exact Classical.choose_spec (hAux 0 0)
    | succ k _ih =>
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      rw [hm_succ]
      exact Classical.choose_spec (hAux (k + 1) (ψ k (m k)))
  let φ : ℕ → ℕ := fun k => ψ k (m k)
  have hφ_mono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ (fun k => ?_)
    have hspec := (hm_spec (k + 1)).1
    simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one] at hspec
    exact hspec
  refine ⟨φ, hφ_mono, ?_⟩
  change Filter.Tendsto (fun k => b k (φ k)) Filter.atTop (𝓝 R)
  have h_lower_bound : ∀ k, (T k - ε k : ℝ≥0∞) ≤ b k (φ k) + ε k :=
    fun k => le_of_lt (hm_spec k).2.1
  have h_upper_bound : ∀ k, b k (φ k) ≤ L k + ε k :=
    fun k => (hm_spec k).2.2
  -- 2 ε k → 0.
  have h_2ε_tendsto : Filter.Tendsto (fun k => 2 * ε k) Filter.atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hε_tendsto
      (by right; exact ENNReal.ofNat_ne_top)
    simpa using this
  -- T k - 2 ε k → R.
  have h_lower_lim : Filter.Tendsto (fun k => (T k - 2 * ε k : ℝ≥0∞))
      Filter.atTop (𝓝 R) := by
    have h_sub :=
      ENNReal.Tendsto.sub hT_tendsto_R h_2ε_tendsto
        (Or.inr (by norm_num : (0 : ℝ≥0∞) ≠ ⊤))
    simpa using h_sub
  -- L k + ε k → R + 0 = R.
  have h_upper_lim : Filter.Tendsto (fun k => L k + ε k) Filter.atTop (𝓝 R) := by
    have := hL_tendsto_R.add hε_tendsto
    simpa using this
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro y hy_lt_R
    have h_ev_y : ∀ᶠ k in Filter.atTop, y < (T k - 2 * ε k : ℝ≥0∞) :=
      h_lower_lim.eventually (eventually_gt_nhds hy_lt_R)
    filter_upwards [h_ev_y] with k hk
    have h_rec : (T k - ε k : ℝ≥0∞) ≤ b k (φ k) + ε k := h_lower_bound k
    have hb_ge_sub : (T k - 2 * ε k : ℝ≥0∞) ≤ b k (φ k) := by
      have h_two_eps : (2 * ε k : ℝ≥0∞) = ε k + ε k := by ring
      rw [h_two_eps, ← tsub_tsub]
      exact tsub_le_iff_right.mpr h_rec
    exact lt_of_lt_of_le hk hb_ge_sub
  · intro y hy_gt_R
    have h_ev : ∀ᶠ k in Filter.atTop, L k + ε k < y :=
      h_upper_lim.eventually (eventually_lt_nhds hy_gt_R)
    filter_upwards [h_ev] with k hk
    exact lt_of_le_of_lt (h_upper_bound k) hk

end Prohorov
end AsymptoticStatistics
