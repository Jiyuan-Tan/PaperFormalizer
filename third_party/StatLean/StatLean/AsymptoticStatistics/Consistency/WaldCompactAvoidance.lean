module
public import StatLean.AsymptoticStatistics.ForMathlib.IidOneSidedLLN
public import StatLean.AsymptoticStatistics.ForMathlib.UpperSemicontinuousEnvelope

@[expose] public section

/-!
# Wald compact avoidance

The finite-subcover argument in the proof of vdV Theorem 5.14.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace AsymptoticStatistics.Consistency

private lemma extendedExpectation_congr_ae {X : Type*} [MeasurableSpace X]
    (Q : Measure X) {f g : X → EReal} (hfg : f =ᵐ[Q] g) :
    extendedExpectation Q f = extendedExpectation Q g := by
  unfold extendedExpectation
  rw [lintegral_congr_ae (hfg.mono fun _ h => congrArg EReal.toENNReal h),
    lintegral_congr_ae (hfg.mono fun _ h => congrArg (fun z => (-z).toENNReal) h)]

private lemma extendedEmpiricalAvg_mono {X : Type*} {f g : X → EReal}
    (n : ℕ) (s : Fin n → X) (hfg : ∀ i, f (s i) ≤ g (s i)) :
    extendedEmpiricalAvg f n s ≤ extendedEmpiricalAvg g n s := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [extendedEmpiricalAvg]
  rw [extendedEmpiricalAvg, if_neg hn, extendedEmpiricalAvg, if_neg hn]
  apply EReal.sub_le_sub
  · norm_cast
    gcongr with i
    exact EReal.toENNReal_le_toENNReal (hfg i)
  · norm_cast
    gcongr with i
    exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hfg i))

/-- A compact set disjoint from the population argmax set is visited by a
near-maximizing iid empirical criterion with probability tending to zero.
This is the compact finite-cover core of vdV Theorem 5.14, p.48. -/
theorem wald_avoids_compact_disjoint
    {X Ω Θ : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MetricSpace Θ]
    (Q : Measure X) [IsProbabilityMeasure Q]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (Xs : ℕ → Ω → X) (m : Θ → X → EReal) (θ₀ : Θ)
    (θhat : ℕ → Ω → Θ) (R : ℕ → Ω → ℝ)
    -- vdV's codomain `[-∞,∞)` excludes pointwise `⊤`.
    (hm_top : ∀ θ x, m θ x ≠ ⊤)
    -- vdV (5.12), retaining θ-dependent exceptional sets.
    (husc : ∀ θ, ∀ᵐ x ∂Q, UpperSemicontinuousAt (fun η => m η x) θ)
    -- local measurability and finite positive part in vdV (5.13).
    (hlocal : ∀ θ, ∃ ρ > 0, ∀ r, 0 < r → r ≤ ρ →
      Measurable (localCriterionSup m θ r) ∧
      (∫⁻ x, (localCriterionSup m θ r x).toENNReal ∂Q) ≠ ∞)
    -- the chosen comparison point belongs to vdV's nonempty argmax set.
    (hmax : θ₀ ∈ {θ | ∀ η,
      extendedExpectation Q (m η) ≤ extendedExpectation Q (m θ)})
    -- vdV p.48 requires at least one maximizing expectation finite.
    (hfinite : ∃ a : ℝ, extendedExpectation Q (m θ₀) = (a : EReal))
    -- single-base measurable iid sample encoding of a random sample.
    (hXs_meas : ∀ i, Measurable (Xs i))
    (hXs_indep : ProbabilityTheory.iIndepFun Xs ℙ)
    (hXs_id : ∀ i, ProbabilityTheory.IdentDistrib (Xs i) (Xs 0) ℙ ℙ)
    (hXs_law : ℙ.map (Xs 0) = Q)
    -- vdV near-maximizer inequality with a real `oₚ(1)` remainder.
    (hnear : ∀ n ω,
      extendedEmpiricalAvg (m θ₀) n (fun i : Fin n => Xs i.val ω) - (R n ω : EReal) ≤
      extendedEmpiricalAvg (m (θhat n ω)) n (fun i : Fin n => Xs i.val ω))
    (hR : TendstoInMeasure ℙ R atTop (fun _ => 0))
    (B : Set Θ) (hB_compact : IsCompact B)
    (hB_disjoint : Disjoint B
      {θ | ∀ η, extendedExpectation Q (m η) ≤ extendedExpectation Q (m θ)}) :
    Tendsto (fun n => ℙ {ω | θhat n ω ∈ B}) atTop (𝓝 0) := by
  classical
  rcases hfinite with ⟨a₀, ha₀⟩
  by_cases hB : B = ∅
  · simp [hB]
  have hseq (θ : Θ) : ∃ N : ℕ,
      (∀ k, Measurable (localCriterionSup m θ ((((k + N : ℕ) : ℝ) + 1)⁻¹))) ∧
      (∀ᵐ x ∂Q, Antitone (fun k =>
        localCriterionSup m θ ((((k + N : ℕ) : ℝ) + 1)⁻¹) x)) ∧
      (∀ᵐ x ∂Q, Tendsto (fun k =>
        localCriterionSup m θ ((((k + N : ℕ) : ℝ) + 1)⁻¹) x)
          atTop (𝓝 (m θ x))) ∧
      ∀ k, (∫⁻ x, (localCriterionSup m θ ((((k + N : ℕ) : ℝ) + 1)⁻¹) x).toENNReal ∂Q) ≠ ∞ := by
    obtain ⟨ρ, hρ, hloc⟩ := hlocal θ
    obtain ⟨N, hN⟩ := exists_nat_gt ρ⁻¹
    have hNρ : (((N : ℝ) + 1)⁻¹) ≤ ρ :=
      by simpa only [Nat.cast_add, Nat.cast_one] using
        (inv_le_comm₀ (by positivity : (0 : ℝ) < (N + 1 : ℕ)) hρ).2
          ((le_of_lt hN).trans (by exact_mod_cast Nat.le_succ N))
    have hr (k : ℕ) : 0 < ((((k + N : ℕ) : ℝ) + 1)⁻¹) := by positivity
    have hrρ (k : ℕ) : ((((k + N : ℕ) : ℝ) + 1)⁻¹) ≤ ρ := by
      exact ((inv_le_inv₀ (by positivity) (by positivity)).2 <| by
        exact_mod_cast (by omega : N + 1 ≤ k + N + 1)).trans hNρ
    have henv := iInf_localCriterionSup_eq Q m husc θ
    refine ⟨N, (fun k => (hloc _ (hr k) (hrρ k)).1), ?_, ?_,
      (fun k => (hloc _ (hr k) (hrρ k)).2)⟩
    · filter_upwards [henv] with x hx
      intro k l hkl
      exact hx.1 (Nat.add_le_add_right hkl N)
    · filter_upwards [henv] with x hx
      exact hx.2.1.comp (tendsto_add_atTop_nat N)
  have hball (θ : B) : ∃ r c : ℝ, 0 < r ∧
      extendedExpectation Q (localCriterionSup m θ.1 r) < (c : EReal) ∧ c < a₀ ∧
      Measurable (localCriterionSup m θ.1 r) ∧
      (∫⁻ x, (localCriterionSup m θ.1 r x).toENNReal ∂Q) ≠ ∞ := by
    have hnot : θ.1 ∉ {η | ∀ ζ,
        extendedExpectation Q (m ζ) ≤ extendedExpectation Q (m η)} :=
      fun h => Set.disjoint_left.1 hB_disjoint θ.2 h
    obtain ⟨η, hη⟩ := not_forall.mp hnot
    have hθ : extendedExpectation Q (m θ.1) < (a₀ : EReal) :=
      (lt_of_not_ge hη).trans_le <| by simpa [ha₀] using hmax η
    obtain ⟨c, hθc, hc⟩ := EReal.exists_between_coe_real hθ
    obtain ⟨N, hmeas, hanti, hlim, hpos⟩ := hseq θ.1
    have ht := extendedExpectation_tendsto_of_antitone Q
      (fun k => localCriterionSup m θ.1 ((((k + N : ℕ) : ℝ) + 1)⁻¹)) (m θ.1)
      hmeas hanti hlim (hpos 0)
    obtain ⟨k, hk⟩ := (ht.eventually (Iio_mem_nhds hθc)).exists
    refine ⟨((((k + N : ℕ) : ℝ) + 1)⁻¹), c, by positivity, hk, ?_, hmeas k, ?_⟩
    · exact EReal.coe_lt_coe_iff.mp hc
    · exact hpos k
  choose r c hrc using hball
  let e : B → X → EReal := fun θ => localCriterionSup m θ.1 (r θ)
  have hcover : B ⊆ ⋃ θ : B, Metric.ball θ.1 (r θ) := by
    intro θ hθ
    exact mem_iUnion.2 ⟨⟨θ, hθ⟩, Metric.mem_ball_self (hrc ⟨θ, hθ⟩).1⟩
  obtain ⟨t, ht⟩ := hB_compact.elim_finite_subcover
    (fun θ : B => Metric.ball θ.1 (r θ)) (fun _ => Metric.isOpen_ball) hcover
  have htne : t.Nonempty := by
    obtain ⟨θ, hθ⟩ := Set.nonempty_iff_ne_empty.2 hB
    rcases mem_iUnion.1 (ht hθ) with ⟨i, hi⟩
    rcases mem_iUnion.1 hi with ⟨hit, _⟩
    exact ⟨i, hit⟩
  let gaps : Finset ℝ := t.image fun θ => (a₀ - c θ) / 3
  have hgaps : gaps.Nonempty := htne.image _
  let δ : ℝ := gaps.min' hgaps
  have hδmem : δ ∈ gaps := Finset.min'_mem _ _
  obtain ⟨iδ, hiδ, hδeq⟩ := Finset.mem_image.mp hδmem
  have hδ : 0 < δ := by rw [← hδeq]; linarith [(hrc iδ).2.2.1]
  have hgap (i : B) (hi : i ∈ t) : c i ≤ a₀ - 3 * δ := by
    have := Finset.min'_le gaps ((a₀ - c i) / 3) (Finset.mem_image.2 ⟨i, hi, rfl⟩)
    change δ ≤ (a₀ - c i) / 3 at this; linarith
  let g : B → X → EReal := fun i x => if e i x = ⊤ then 0 else e i x
  have heq (i : B) : g i =ᵐ[Q] e i := by
    have hlt := ae_lt_top ((hrc i).2.2.2.1.ereal_toENNReal) (hrc i).2.2.2.2
    filter_upwards [hlt] with x hx
    have hne : e i x ≠ ⊤ := EReal.toENNReal_ne_top_iff.mp hx.ne
    simp only [g, if_neg hne]
  have hgmeas (i : B) : Measurable (g i) :=
    Measurable.ite ((hrc i).2.2.2.1 (measurableSet_singleton ⊤)) measurable_const
      (hrc i).2.2.2.1
  have hgtop (i : B) (x : X) : g i x ≠ ⊤ := by simp [g]; split <;> simp_all
  have hgpos (i : B) : (∫⁻ x, (g i x).toENNReal ∂Q) ≠ ∞ := by
    rw [lintegral_congr_ae ((heq i).mono fun _ h => congrArg EReal.toENNReal h)]
    exact (hrc i).2.2.2.2
  obtain ⟨N₀, hmseq, _, hmlim, _⟩ := hseq θ₀
  have hm0ae : AEMeasurable (m θ₀) Q :=
    aemeasurable_of_tendsto_metrizable_ae' (fun k => (hmseq k).aemeasurable) hmlim
  let m₀' := hm0ae.mk (m θ₀)
  let f₀ : X → EReal := fun x => if m₀' x = ⊤ then 0 else m₀' x
  have hf0eq : f₀ =ᵐ[Q] m θ₀ := by
    filter_upwards [hm0ae.ae_eq_mk] with x hx
    have hne : m₀' x ≠ ⊤ := by
      change hm0ae.mk (m θ₀) x ≠ ⊤
      rw [← hx]
      exact hm_top θ₀ x
    simpa only [f₀, if_neg hne] using hx.symm
  have hf0meas : Measurable f₀ := by
    apply Measurable.ite (hm0ae.measurable_mk (measurableSet_singleton ⊤))
    · exact measurable_const
    · exact hm0ae.measurable_mk
  have hf0top (x : X) : f₀ x ≠ ⊤ := by simp [f₀]; split <;> simp_all
  have hf0exp : extendedExpectation Q f₀ = (a₀ : EReal) :=
    (extendedExpectation_congr_ae Q hf0eq).trans ha₀
  have hu (i : B) (hi : i ∈ t) := iid_extendedEmpiricalAvg_upper_tail Q ℙ Xs (g i)
    (hgmeas i) (hgtop i) (hgpos i) hXs_meas hXs_indep hXs_id hXs_law
      (a₀ - 3 * δ) ((extendedExpectation_congr_ae Q (heq i)).trans_lt
        ((hrc i).2.1.trans_le (EReal.coe_le_coe_iff.mpr (hgap i hi))))
  have hzero := iid_extendedEmpiricalAvg_tendsto_finite Q ℙ Xs f₀ a₀ hf0meas hf0top
    hf0exp hXs_meas hXs_indep hXs_id hXs_law δ hδ
  have hrem := tendstoInMeasure_iff_norm.mp hR δ hδ
  let U (n : ℕ) := ⋃ i ∈ t, {ω | ((a₀ - 3 * δ : ℝ) : EReal) ≤
    extendedEmpiricalAvg (g i) n (fun j : Fin n => Xs j.val ω)}
  let L (n : ℕ) := {ω | extendedEmpiricalAvg f₀ n (fun j : Fin n => Xs j.val ω) <
    ((a₀ - δ : ℝ) : EReal) ∨ ((a₀ + δ : ℝ) : EReal) <
      extendedEmpiricalAvg f₀ n (fun j : Fin n => Xs j.val ω)}
  let D (n : ℕ) := {ω | δ ≤ ‖R n ω - 0‖}
  have hmap (j : ℕ) : MeasurePreserving (Xs j) ℙ Q :=
    ⟨hXs_meas j, by rw [(hXs_id j).map_eq, hXs_law]⟩
  have havg_eq {u v : X → EReal} (huv : u =ᵐ[Q] v) (n : ℕ) :
      ∀ᵐ ω ∂ℙ, extendedEmpiricalAvg u n (fun j : Fin n => Xs j.val ω) =
        extendedEmpiricalAvg v n (fun j : Fin n => Xs j.val ω) := by
    have hs : ∀ᵐ ω ∂ℙ, ∀ j : Fin n, u (Xs j.val ω) = v (Xs j.val ω) := by
      rw [ae_all_iff]; intro j
      exact (hmap j.val).quasiMeasurePreserving.ae_eq huv
    filter_upwards [hs] with ω hω
    unfold extendedEmpiricalAvg
    simp_rw [hω]
  have hsub (n : ℕ) : {ω | θhat n ω ∈ B} ≤ᵐ[ℙ]
      Set.union (Set.union (U n) (L n)) (D n) := by
    filter_upwards [havg_eq hf0eq n,
      t.eventually_all.2 (fun i _ => havg_eq (heq i) n)] with ω h0 hall
    intro hθ
    rcases mem_iUnion.1 (ht hθ) with ⟨i, hi⟩
    rcases mem_iUnion.1 hi with ⟨hit, hballi⟩
    by_cases hU : ω ∈ U n
    · exact Or.inl (Or.inl hU)
    by_cases hL : ω ∈ L n
    · exact Or.inl (Or.inr hL)
    by_cases hD : ω ∈ D n
    · exact Or.inr hD
    exfalso
    have hupp : extendedEmpiricalAvg (e i) n (fun j : Fin n => Xs j.val ω) <
        ((a₀ - 3 * δ : ℝ) : EReal) := by
      rw [← hall i hit]
      exact not_le.mp (fun h => hU <| mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hit, h⟩⟩)
    have hmono : extendedEmpiricalAvg (m (θhat n ω)) n (fun j : Fin n => Xs j.val ω) ≤
        extendedEmpiricalAvg (e i) n (fun j : Fin n => Xs j.val ω) := by
      apply extendedEmpiricalAvg_mono
      intro j
      unfold e localCriterionSup
      exact le_iSup_of_le ⟨θhat n ω, hballi⟩ le_rfl
    have hlo : ((a₀ - δ : ℝ) : EReal) ≤
        extendedEmpiricalAvg (m θ₀) n (fun j : Fin n => Xs j.val ω) := by
      rw [← h0]
      exact not_lt.mp fun h => hL (Or.inl h)
    have hrlt : R n ω < δ := (le_abs_self (R n ω)).trans_lt <| by
      exact not_le.mp (by simpa [D] using hD)
    have hstep : ((a₀ - 2 * δ : ℝ) : EReal) <
        extendedEmpiricalAvg (m θ₀) n (fun j : Fin n => Xs j.val ω) - (R n ω : EReal) :=
      (by norm_cast; linarith : ((a₀ - 2 * δ : ℝ) : EReal) <
        ((a₀ - δ : ℝ) : EReal) - (R n ω : EReal)).trans_le
          (EReal.sub_le_sub hlo le_rfl)
    have := hstep.trans_le ((hnear n ω).trans hmono) |>.trans hupp
    norm_cast at this
    linarith
  have hsum : Tendsto (fun n => ∑ i ∈ t, ℙ {ω | ((a₀ - 3 * δ : ℝ) : EReal) ≤
      extendedEmpiricalAvg (g i) n (fun j : Fin n => Xs j.val ω)}) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum t (fun i hi => hu i hi)
  have hbound (n : ℕ) : ℙ {ω | θhat n ω ∈ B} ≤
      (∑ i ∈ t, ℙ {ω | ((a₀ - 3 * δ : ℝ) : EReal) ≤
        extendedEmpiricalAvg (g i) n (fun j : Fin n => Xs j.val ω)}) + ℙ (L n) + ℙ (D n) :=
    (measure_mono_ae (hsub n)).trans <| (measure_union_le _ _).trans <|
      add_le_add (measure_union_le _ _ |>.trans <| add_le_add_left
        (by exact measure_biUnion_finset_le (μ := ℙ) t (fun i => {ω |
          ((a₀ - 3 * δ : ℝ) : EReal) ≤ extendedEmpiricalAvg (g i) n
            (fun j : Fin n => Xs j.val ω)})) _) le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa [L, D] using (hsum.add hzero).add hrem)
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall hbound)

end AsymptoticStatistics.Consistency
