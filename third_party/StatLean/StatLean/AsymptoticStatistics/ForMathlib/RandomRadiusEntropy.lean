module
public import StatLean.AsymptoticStatistics.ForMathlib.AntitoneLintegral
public import Mathlib.Data.Nat.Find
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace AsymptoticStatistics.ForMathlib

open Filter MeasureTheory Topology
open scoped ENNReal

theorem exists_pos_antitone_scale_tendsto_zero_div
    (b : ℕ → ℝ≥0∞)
    (hb : Tendsto b atTop (𝓝 0)) :
    ∃ a : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      Antitone a ∧
      Tendsto a atTop (𝓝 0) ∧
      Tendsto (fun n => b n / ENNReal.ofReal (a n)) atTop (𝓝 0) := by
  let q : ℕ → ℝ := fun n => Real.sqrt (b n).toReal
  let r : ℕ → ℝ := fun n => q n + 1 / ((n : ℝ) + 1)
  let a : ℕ → ℝ := fun n => sSup (r '' Set.Ici n)
  have hq : Tendsto q atTop (𝓝 0) := by
    have htoReal : Tendsto (fun n => (b n).toReal) atTop (𝓝 0) := by
      simpa using! (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hb
    simpa [q] using! Real.continuous_sqrt.continuousAt.tendsto.comp htoReal
  have hr : Tendsto r atTop (𝓝 0) := by
    simpa [r] using hq.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hr_bdd : BddAbove (Set.range r) := hr.bddAbove_range
  have htail_bdd (n : ℕ) : BddAbove (r '' Set.Ici n) := by
    exact hr_bdd.mono (Set.image_subset_range r (Set.Ici n))
  have htail_ne (n : ℕ) : (r '' Set.Ici n).Nonempty :=
    ⟨r n, n, Set.mem_Ici.mpr le_rfl, rfl⟩
  have hr_pos (n : ℕ) : 0 < r n := by
    dsimp [r, q]
    positivity
  have hr_le_a (n : ℕ) : r n ≤ a n := by
    exact le_csSup (htail_bdd n) ⟨n, Set.mem_Ici.mpr le_rfl, rfl⟩
  have ha_pos (n : ℕ) : 0 < a n := (hr_pos n).trans_le (hr_le_a n)
  have ha_antitone : Antitone a := by
    intro m n hmn
    exact csSup_le_csSup (htail_bdd m) (htail_ne n)
      (Set.image_mono (Set.Ici_subset_Ici.mpr hmn))
  have ha_tendsto : Tendsto a atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hr) (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have ha_le : a n ≤ ε / 2 := by
      apply csSup_le (htail_ne n)
      intro y hy
      obtain ⟨k, hk, rfl⟩ := hy
      have hNk : N ≤ k := hn.trans hk
      have hk' := hN k hNk
      simpa [Real.dist_eq, abs_of_nonneg (hr_pos k).le] using hk'.le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha_pos n).le]
    exact ha_le.trans_lt (half_lt_self hε)
  have hq_le_a (n : ℕ) : q n ≤ a n := by
    exact (le_add_of_nonneg_right (by positivity : 0 ≤ 1 / ((n : ℝ) + 1))).trans
      (hr_le_a n)
  have hratio_le :
      ∀ᶠ n in atTop, b n / ENNReal.ofReal (a n) ≤ ENNReal.ofReal (q n) := by
    filter_upwards [hb.eventually_ne ENNReal.zero_ne_top] with n hbn
    have hq0 : 0 ≤ q n := by simp [q]
    have hbq : b n = ENNReal.ofReal ((q n) ^ 2) := by
      rw [← ENNReal.ofReal_toReal hbn]
      congr 1
      simp [q, Real.sq_sqrt ENNReal.toReal_nonneg]
    calc
      b n / ENNReal.ofReal (a n) =
          ENNReal.ofReal ((q n) ^ 2 / a n) := by
        rw [hbq, ENNReal.ofReal_div_of_pos (ha_pos n)]
      _ ≤ ENNReal.ofReal (q n) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_iff₀ (ha_pos n)]
        simpa [pow_two] using mul_le_mul_of_nonneg_left (hq_le_a n) hq0
  have hofReal_q : Tendsto (fun n => ENNReal.ofReal (q n)) atTop (𝓝 0) := by
    simpa using! (ENNReal.continuous_ofReal.tendsto 0).comp hq
  refine ⟨a, ha_pos, ha_antitone, ha_tendsto, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hofReal_q (Eventually.of_forall fun _ => zero_le) hratio_le

theorem exists_pos_antitone_scale_tendsto_zero_diagonal
    (T : ℕ → ℝ → ℝ≥0∞)
    (hT : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => T n ε) atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ,
      (∀ n, 0 < ε n) ∧
      Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun n => T n (ε n)) atTop (𝓝 0) := by
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
  have htail (m : ℕ) :
      ∃ N : ℕ, ∀ n, N ≤ n →
        T n (q m) ≤ ENNReal.ofReal (q m) := by
    have hevent : ∀ᶠ n in atTop, T n (q m) < ENNReal.ofReal (q m) :=
      (tendsto_order.1 (hT (q m) (hq_pos m))).2 _
        (ENNReal.ofReal_pos.mpr (hq_pos m))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    exact ⟨N, fun n hn => (hN n hn).le⟩
  choose N hN using htail
  let N' : ℕ → ℕ := fun m => max m (N m)
  let M : ℕ → ℕ := fun n =>
    Nat.findGreatest (fun m => N' m ≤ n) n
  have hM_mono : Monotone M := by
    intro m n hmn
    dsimp [M]
    exact Nat.findGreatest_mono (fun _ hk => hk.trans hmn) hmn
  have hM_tendsto : Tendsto M atTop atTop := by
    refine tendsto_atTop.2 fun m => eventually_atTop.2 ⟨N' m, ?_⟩
    intro n hn
    change m ≤ Nat.findGreatest (fun k => N' k ≤ n) n
    apply Nat.le_findGreatest
    · exact (by simp [N'] : m ≤ N' m).trans hn
    · exact hn
  let ε : ℕ → ℝ := q ∘ M
  have hε_pos (n : ℕ) : 0 < ε n := by
    simpa [ε] using hq_pos (M n)
  have hε_antitone : Antitone ε := by
    simpa [ε] using hq_antitone.comp_monotone hM_mono
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using hq_tendsto.comp hM_tendsto
  have hdiag :
      ∀ᶠ n in atTop, T n (ε n) ≤ ENNReal.ofReal (ε n) := by
    refine eventually_atTop.2 ⟨N' 0, ?_⟩
    intro n hn
    have hM_spec : N' (M n) ≤ n := by
      dsimp [M]
      exact Nat.findGreatest_spec (P := fun m => N' m ≤ n) (m := 0)
        (zero_le (a := n)) hn
    have hNM : N (M n) ≤ n :=
      (by simp [N'] : N (M n) ≤ N' (M n)).trans hM_spec
    simpa [ε] using hN (M n) n hNM
  have hofReal_ε :
      Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    simpa using! (ENNReal.continuous_ofReal.tendsto 0).comp hε_tendsto
  refine ⟨ε, hε_pos, hε_antitone, hε_tendsto, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hofReal_ε (Eventually.of_forall fun _ => zero_le) hdiag

theorem randomRadiusEntropy_lintegral_tendsto_zero_of_scale
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ)
    (D R : ℕ → Ξ → ℝ≥0∞)
    (θ : ℕ → Ξ → ℝ)
    (g : ℕ → ℝ → ℝ≥0∞)
    (a : ℕ → ℝ)
    (hg : ∀ n, Antitone (g n))
    (ha : ∀ n, 0 < a n)
    (hD_meas : ∀ n, AEMeasurable (D n) μ)
    (hD_bdd : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ n, (∫⁻ ξ, D n ξ ∂μ) ≤ C)
    (hDθ : ∀ n ξ,
      D n ξ * ENNReal.ofReal (θ n ξ) ≤ R n ξ)
    (hJ : Tendsto
      (fun n => ∫⁻ ε in Set.Ioc 0 (a n), g n ε ∂volume)
      atTop (𝓝 0))
    (hR_scale : Tendsto
      (fun n => (∫⁻ ξ, R n ξ ∂μ) / ENNReal.ofReal (a n))
      atTop (𝓝 0)) :
    Tendsto
      (fun n => ∫⁻ ξ,
        D n ξ * (∫⁻ ε in Set.Ioc 0 (θ n ξ), g n ε ∂volume) ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hDC⟩ := hD_bdd
  let J : ℕ → ℝ≥0∞ := fun n => ∫⁻ ε in Set.Ioc 0 (a n), g n ε ∂volume
  let S : ℕ → ℝ≥0∞ := fun n => (∫⁻ ξ, R n ξ ∂μ) / ENNReal.ofReal (a n)
  have hJ' : Tendsto J atTop (𝓝 0) := by simpa [J] using hJ
  have hS' : Tendsto S atTop (𝓝 0) := by simpa [S] using hR_scale
  have hJ_ne_top : ∀ᶠ n in atTop, J n ≠ ⊤ :=
    hJ'.eventually_ne ENNReal.zero_ne_top
  have hpoint (n : ℕ) (ξ : Ξ) :
      D n ξ * (∫⁻ ε in Set.Ioc 0 (θ n ξ), g n ε ∂volume) ≤
        D n ξ * J n + (R n ξ / ENNReal.ofReal (a n)) * J n := by
    have hratio : D n ξ * ENNReal.ofReal (θ n ξ / a n) ≤
        R n ξ / ENNReal.ofReal (a n) := by
      rw [ENNReal.ofReal_div_of_pos (ha n), ← mul_div_assoc]
      exact ENNReal.div_le_div_right (hDθ n ξ) _
    calc
      D n ξ * (∫⁻ ε in Set.Ioc 0 (θ n ξ), g n ε ∂volume) ≤
          D n ξ * (J n + ENNReal.ofReal (θ n ξ / a n) * J n) :=
        mul_le_mul_right (setLIntegral_Ioc_le_initial_add_ratio_mul_initial_of_antitone
          (g n) (hg n) (ha n)) _
      _ = D n ξ * J n + (D n ξ * ENNReal.ofReal (θ n ξ / a n)) * J n := by
        rw [mul_add, mul_assoc]
      _ ≤ D n ξ * J n + (R n ξ / ENNReal.ofReal (a n)) * J n :=
        by
          simpa [add_comm, mul_comm] using
            (add_le_add_left (mul_le_mul_right hratio (J n)) (D n ξ * J n))
  have hbound : ∀ᶠ n in atTop,
      (∫⁻ ξ, D n ξ * (∫⁻ ε in Set.Ioc 0 (θ n ξ), g n ε ∂volume) ∂μ) ≤
        J n * C + J n * S n := by
    filter_upwards [hJ_ne_top] with n hn
    have ha0 : ENNReal.ofReal (a n) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (ha n)
    calc
      (∫⁻ ξ, D n ξ * (∫⁻ ε in Set.Ioc 0 (θ n ξ), g n ε ∂volume) ∂μ) ≤
          ∫⁻ ξ, D n ξ * J n + (R n ξ / ENNReal.ofReal (a n)) * J n ∂μ :=
        lintegral_mono (hpoint n)
      _ = (∫⁻ ξ, D n ξ ∂μ) * J n +
          (∫⁻ ξ, R n ξ / ENNReal.ofReal (a n) ∂μ) * J n := by
        rw [lintegral_add_left' ((hD_meas n).mul_const _),
          lintegral_mul_const' _ _ hn, lintegral_mul_const' _ _ hn]
      _ = (∫⁻ ξ, D n ξ ∂μ) * J n + S n * J n := by
        simp only [S, div_eq_mul_inv]
        rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr ha0)]
      _ ≤ J n * C + J n * S n := by
        simpa [mul_comm] using add_le_add (mul_le_mul_right (hDC n) (J n)) le_rfl
  have hupper : Tendsto (fun n => J n * C + J n * S n) atTop (𝓝 0) := by
    have hJC : Tendsto (fun n => J n * C) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hJ' (Or.inr hC.ne)
    have hJS : Tendsto (fun n => J n * S n) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul hJ' (Or.inr ENNReal.zero_ne_top) hS'
        (Or.inr ENNReal.zero_ne_top)
    simpa using hJC.add hJS
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper (Eventually.of_forall fun _ => zero_le) hbound

theorem randomRadiusEntropy_lintegral_tendsto_zero
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ)
    (D R : ℕ → Ξ → ℝ≥0∞)
    (θ : ℕ → Ξ → ℝ)
    (g : ℕ → ℝ → ℝ≥0∞)
    (hg : ∀ n, Antitone (g n))
    (hD_meas : ∀ n, AEMeasurable (D n) μ)
    (hD_bdd : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, (∫⁻ ξ, D n ξ ∂μ) ≤ C)
    (hDθ : ∀ n ξ, D n ξ * ENNReal.ofReal (θ n ξ) ≤ R n ξ)
    (hR : Tendsto (fun n => ∫⁻ ξ, R n ξ ∂μ) atTop (𝓝 0))
    (hJ_diagonal :
      ∀ a : ℕ → ℝ,
        (∀ n, 0 < a n) → Antitone a → Tendsto a atTop (𝓝 0) →
        Tendsto (fun n => ∫⁻ ε in Set.Ioc 0 (a n), g n ε ∂volume)
          atTop (𝓝 0)) :
    Tendsto
      (fun n => ∫⁻ ξ,
        D n ξ * (∫⁻ ε in Set.Ioc 0 (θ n ξ), g n ε ∂volume) ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨a, ha, ha_antitone, ha_tendsto, hR_scale⟩ :=
    exists_pos_antitone_scale_tendsto_zero_div
      (fun n => ∫⁻ ξ, R n ξ ∂μ) hR
  exact randomRadiusEntropy_lintegral_tendsto_zero_of_scale
    μ D R θ g a hg ha hD_meas hD_bdd hDθ
      (hJ_diagonal a ha ha_antitone ha_tendsto) hR_scale

end AsymptoticStatistics.ForMathlib
