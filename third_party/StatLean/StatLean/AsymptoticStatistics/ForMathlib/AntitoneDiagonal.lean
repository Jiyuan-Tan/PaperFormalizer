module
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace AsymptoticStatistics.ForMathlib

open Filter Topology
open scoped ENNReal

/-- If every positive antitone null diagonal makes a two-parameter family vanish,
then some fixed positive scale is eventually below any prescribed positive bound. -/
theorem exists_pos_fixed_scale_eventually_lt_of_antitone_diagonal
    (L : ℕ → ℝ → ℝ≥0∞)
    (hL : ∀ δ, (∀ n, 0 < δ n) → Antitone δ → Tendsto δ atTop (𝓝 0) →
      Tendsto (fun n => L n (δ n)) atTop (𝓝 0))
    {c : ℝ≥0∞} (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, L n r < c := by
  classical
  by_contra! hfixed
  let q : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hq_pos (m : ℕ) : 0 < q m := by
    dsimp [q]
    positivity
  have hq_antitone : Antitone q := by
    intro m n hmn
    dsimp [q]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hq_tendsto : Tendsto q atTop (𝓝 0) := by
    simpa [q] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hbad (m K : ℕ) :
      ∃ n : ℕ, K ≤ n ∧ c ≤ L n (q m) := by
    obtain ⟨n, hn, hLn⟩ :=
      (frequently_iff.1 (hfixed (q m) (hq_pos m))) (eventually_ge_atTop K)
    exact ⟨n, hn, hLn⟩
  choose pick hpick_ge hpick_bad using hbad
  let N : ℕ → ℕ := Nat.rec (pick 0 0) fun m n => pick (m + 1) (n + 1)
  have hN_succ (m : ℕ) : N m < N (m + 1) := by
    dsimp [N]
    exact hpick_ge (m + 1) (N m + 1)
  have hN_strict : StrictMono N := strictMono_nat_of_lt_succ hN_succ
  have hN_bad (m : ℕ) : c ≤ L (N m) (q m) := by
    cases m with
    | zero =>
        simpa [N] using hpick_bad 0 0
    | succ m =>
        simpa [N] using hpick_bad (m + 1) (N m + 1)
  let M : ℕ → ℕ := fun n =>
    @Nat.findGreatest (fun m => N m ≤ n) (Classical.decPred _) n
  have hM_mono : Monotone M := by
    intro m n hmn
    dsimp [M]
    exact @Nat.findGreatest_mono m
      (fun k => N k ≤ m) (fun k => N k ≤ n) (Classical.decPred _) n
      (Classical.decPred _) (fun _ hk => hk.trans hmn) hmn
  have hM_tendsto : Tendsto M atTop atTop := by
    refine tendsto_atTop.2 fun m => eventually_atTop.2 ⟨N m, ?_⟩
    intro n hn
    change m ≤ @Nat.findGreatest (fun k => N k ≤ n) (Classical.decPred _) n
    exact @Nat.le_findGreatest m (fun k => N k ≤ n) (Classical.decPred _) n
      (hN_strict.le_apply.trans hn) hn
  have hM_at_N (m : ℕ) : M (N m) = m := by
    apply le_antisymm
    · have hspec : N (M (N m)) ≤ N m := by
        dsimp [M]
        exact @Nat.findGreatest_spec 0 (fun k => N k ≤ N m)
          (Classical.decPred _) (N m)
          (Nat.zero_le (N m))
          (hN_strict.monotone (Nat.zero_le m))
      exact hN_strict.le_iff_le.mp hspec
    · dsimp [M]
      exact @Nat.le_findGreatest m (fun k => N k ≤ N m)
        (Classical.decPred _) (N m) hN_strict.le_apply le_rfl
  let δ : ℕ → ℝ := q ∘ M
  have hδ_pos (n : ℕ) : 0 < δ n := by
    simpa [δ] using hq_pos (M n)
  have hδ_antitone : Antitone δ := by
    simpa [δ] using hq_antitone.comp_monotone hM_mono
  have hδ_tendsto : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using hq_tendsto.comp hM_tendsto
  have hdiag := hL δ hδ_pos hδ_antitone hδ_tendsto
  have hevent : ∀ᶠ n in atTop, L n (δ n) < c :=
    (tendsto_order.1 hdiag).2 c hc
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  have hlt : L (N K) (δ (N K)) < c := hK (N K) hN_strict.le_apply
  have hge : c ≤ L (N K) (δ (N K)) := by
    simpa [δ, hM_at_N] using hN_bad K
  exact (not_le_of_gt hlt) hge

end AsymptoticStatistics.ForMathlib
