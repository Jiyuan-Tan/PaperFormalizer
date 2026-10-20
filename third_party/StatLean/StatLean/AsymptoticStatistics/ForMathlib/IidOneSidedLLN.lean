module
public import StatLean.AsymptoticStatistics.ForMathlib.IidWLLN
public import StatLean.AsymptoticStatistics.ForMathlib.OneSidedExpectation

@[expose] public section

/-!
# I.i.d. one-sided laws of large numbers

Single-base i.i.d. LLN consequences for the extended-real empirical average.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics

private lemma extendedEmpiricalAvg_le_truncatedNegative {X : Type*}
    (f : X → EReal) (n C : ℕ) (s : Fin n → X) (htop : ∀ x, f x ≠ ⊤) :
    extendedEmpiricalAvg f n s ≤
      (EmpiricalProcess.empiricalAvg (fun x =>
        (f x).toENNReal.toReal - (min (-f x).toENNReal (C : ENNReal)).toReal) n s : EReal) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [extendedEmpiricalAvg]
  rw [extendedEmpiricalAvg, if_neg hn, EmpiricalProcess.empiricalAvg]
  have hp : (∑ i, (f (s i)).toENNReal) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun i _ => EReal.toENNReal_ne_top_iff.mpr (htop _)
  have hc : (∑ i, min (-f (s i)).toENNReal (C : ENNReal)) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun i _ =>
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top C) (min_le_right _ _)
  have hp' : (n : ENNReal)⁻¹ * ∑ i, (f (s i)).toENNReal ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (by simp [hn])) hp
  have hc' : (n : ENNReal)⁻¹ * ∑ i, min (-f (s i)).toENNReal (C : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (by simp [hn])) hc
  calc
    _ ≤ (↑((n : ENNReal)⁻¹ * ∑ i, (f (s i)).toENNReal) : EReal) -
        ↑((n : ENNReal)⁻¹ * ∑ i, min (-f (s i)).toENNReal (C : ENNReal)) := by
      apply EReal.sub_le_sub le_rfl
      norm_cast
      gcongr with i hi
      exact min_le_left _ _
    _ = _ := by
      rw [← EReal.coe_ennreal_toReal hp', ← EReal.coe_ennreal_toReal hc', ← EReal.coe_sub]
      congr 1
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sum, ENNReal.toReal_sum]
      · rw [← mul_sub, ← Finset.sum_sub_distrib]
        simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
      · exact fun i _ => ne_top_of_le_ne_top (ENNReal.natCast_ne_top C) (min_le_right _ _)
      · exact fun i _ => EReal.toENNReal_ne_top_iff.mpr (htop _)
/-- Upper-tail LLN for an `EReal` criterion with finite positive part.  No
absolute-integrability assumption is made: an infinite negative part is
allowed, as required by vdV Theorem 5.14. -/
theorem iid_extendedEmpiricalAvg_upper_tail
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (Q : Measure X) [IsProbabilityMeasure Q]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (Xs : ℕ → Ω → X) (f : X → EReal)
    -- measurability needed for the one-sided LLN.
    (hf_meas : Measurable f)
    -- vdV criteria take values in `[-∞,∞)`, excluding `⊤`.
    (hf_top : ∀ x, f x ≠ ⊤)
    -- finite positive part, the content of vdV (5.13).
    (hf_pos : (∫⁻ x, (f x).toENNReal ∂Q) ≠ ∞)
    -- single-base measurable iid sample encoding.
    (hXs_meas : ∀ i, Measurable (Xs i))
    (hXs_indep : ProbabilityTheory.iIndepFun Xs ℙ)
    (hXs_id : ∀ i, ProbabilityTheory.IdentDistrib (Xs i) (Xs 0) ℙ ℙ)
    (hXs_law : ℙ.map (Xs 0) = Q) :
    ∀ a : ℝ, extendedExpectation Q f < (a : EReal) →
      Tendsto (fun n => ℙ {ω |
        (a : EReal) ≤ extendedEmpiricalAvg f n
          (fun i : Fin n => Xs i.val ω)}) atTop (𝓝 0) := by
  classical
  intro a ha; let p : X → ENNReal := fun x => (f x).toENNReal
  let q : X → ENNReal := fun x => (-f x).toENNReal
  let L : ℕ → ENNReal := fun C => ∫⁻ x, min (q x) (C : ENNReal) ∂Q
  have hp_meas : Measurable p := hf_meas.ereal_toENNReal
  have hq_meas : Measurable q := hf_meas.neg.ereal_toENNReal
  have hL_fin (C : ℕ) : L C ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.natCast_ne_top C)
    calc L C ≤ ∫⁻ _ : X, (C : ENNReal) ∂Q := lintegral_mono fun x => min_le_right _ _
      _ = C := by simp
  have hL_lim : Tendsto L atTop (𝓝 (∫⁻ x, q x ∂Q)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · exact fun C => (hq_meas.min measurable_const).aemeasurable
    · filter_upwards [] with x
      intro i j hij
      exact min_le_min le_rfl (by exact_mod_cast hij)
    · filter_upwards [] with x
      simpa using (tendsto_const_nhds.min ENNReal.tendsto_nat_nhds_top)
  have hC : ∃ C : ℕ, (∫⁻ x, p x ∂Q).toReal - (L C).toReal < a := by
    by_cases hq : (∫⁻ x, q x ∂Q) = ∞
    · have htop : Tendsto L atTop (𝓝 ∞) := by simpa [hq] using hL_lim
      obtain ⟨k, hk⟩ := exists_nat_gt ((∫⁻ x, p x ∂Q).toReal - a)
      obtain ⟨C, hC⟩ := (ENNReal.tendsto_nhds_top_iff_nat.mp htop k).exists
      refine ⟨C, ?_⟩
      have hkr : (k : ℝ) < (L C).toReal :=
        (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top k) (hL_fin C)).2 hC
      linarith
    · have hreal : Tendsto (fun C => (L C).toReal) atTop
          (𝓝 (∫⁻ x, q x ∂Q).toReal) := (ENNReal.tendsto_toReal_iff hL_fin hq).2 hL_lim
      have hlt : (∫⁻ x, p x ∂Q).toReal - (∫⁻ x, q x ∂Q).toReal < a := by
        unfold extendedExpectation at ha
        rw [← EReal.coe_ennreal_toReal hf_pos, ← EReal.coe_ennreal_toReal hq,
          ← EReal.coe_sub] at ha
        exact EReal.coe_lt_coe_iff.mp ha
      exact ((tendsto_const_nhds.sub hreal).eventually (Iio_mem_nhds hlt)).exists
  obtain ⟨C, hC⟩ := hC
  let g : X → ℝ := fun x => (p x).toReal - (min (q x) (C : ENNReal)).toReal
  have hp_int : Integrable (fun x => (p x).toReal) Q :=
    integrable_toReal_of_lintegral_ne_top hp_meas.aemeasurable (by simpa [p] using hf_pos)
  have hqc_meas : Measurable fun x => min (q x) (C : ENNReal) := hq_meas.min measurable_const
  have hqc_int : Integrable (fun x => (min (q x) (C : ENNReal)).toReal) Q :=
    integrable_toReal_of_lintegral_ne_top hqc_meas.aemeasurable (hL_fin C)
  have hg_int : Integrable g Q := hp_int.sub hqc_int
  have hg_meas : Measurable g := hp_meas.ennreal_toReal.sub hqc_meas.ennreal_toReal
  have hp_ae : ∀ᵐ x ∂Q, p x < ∞ := Eventually.of_forall fun x =>
    lt_top_iff_ne_top.2 (EReal.toENNReal_ne_top_iff.mpr (hf_top x))
  have hqc_ae : ∀ᵐ x ∂Q, min (q x) (C : ENNReal) < ∞ := Eventually.of_forall fun x =>
    lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (ENNReal.natCast_ne_top C) (min_le_right _ _))
  have hmean : ∫ x, g x ∂Q = (∫⁻ x, p x ∂Q).toReal - (L C).toReal := by
    rw [integral_sub hp_int hqc_int, integral_toReal hp_meas.aemeasurable hp_ae,
      integral_toReal hqc_meas.aemeasurable hqc_ae]
  have hlln := iid_lln_in_prob_seq Q g hg_meas hg_int ℙ Xs hXs_meas hXs_indep hXs_id hXs_law
  have hgap : 0 < a - ∫ x, g x ∂Q := by rw [hmean]; linarith
  have hreal := hlln (a - ∫ x, g x ∂Q) hgap
  have henn : Tendsto (fun n => ℙ {ω |
      a - ∫ x, g x ∂Q ≤ ‖EmpiricalProcess.empiricalAvg g n
        (fun i : Fin n => Xs i.val ω) - ∫ x, g x ∂Q‖}) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp (by
      simpa [measureReal_def] using hreal)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds henn
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => measure_mono ?_)
  intro ω hω
  have haw : a ≤ EmpiricalProcess.empiricalAvg g n (fun i : Fin n => Xs i.val ω) :=
    EReal.coe_le_coe_iff.mp (hω.trans (extendedEmpiricalAvg_le_truncatedNegative f n C _ hf_top))
  simpa [Real.norm_eq_abs] using (sub_le_sub_right haw _).trans (le_abs_self _)

/-- If the one-sided expectation is finite real, the extended empirical
average converges to it in measure. -/
theorem iid_extendedEmpiricalAvg_tendsto_finite
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (Q : Measure X) [IsProbabilityMeasure Q]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (Xs : ℕ → Ω → X) (f : X → EReal) (a : ℝ)
    -- measurability needed for the iid LLN.
    (hf_meas : Measurable f)
    -- vdV criteria take values in `[-∞,∞)`, excluding `⊤`.
    (hf_top : ∀ x, f x ≠ ⊤)
    -- the selected maximizer has finite expectation (vdV p.48).
    (hf_finite : extendedExpectation Q f = (a : EReal))
    -- single-base measurable iid sample encoding.
    (hXs_meas : ∀ i, Measurable (Xs i))
    (hXs_indep : ProbabilityTheory.iIndepFun Xs ℙ)
    (hXs_id : ∀ i, ProbabilityTheory.IdentDistrib (Xs i) (Xs 0) ℙ ℙ)
    (hXs_law : ℙ.map (Xs 0) = Q) :
    ∀ ε > 0, Tendsto (fun n => ℙ {ω |
      extendedEmpiricalAvg f n (fun i : Fin n => Xs i.val ω) < ((a - ε : ℝ) : EReal) ∨
      ((a + ε : ℝ) : EReal) <
        extendedEmpiricalAvg f n (fun i : Fin n => Xs i.val ω)}) atTop (𝓝 0) := by
  classical
  let p : X → ENNReal := fun x => (f x).toENNReal
  let q : X → ENNReal := fun x => (-f x).toENNReal
  have hp_meas : Measurable p := hf_meas.ereal_toENNReal
  have hq_meas : Measurable q := hf_meas.neg.ereal_toENNReal
  have hq : (∫⁻ x, q x ∂Q) ≠ ∞ := by
    intro h
    unfold extendedExpectation at hf_finite
    rw [show (∫⁻ x, (-f x).toENNReal ∂Q) = ∞ by simpa [q] using h] at hf_finite
    simp at hf_finite
  have hp : (∫⁻ x, p x ∂Q) ≠ ∞ := by
    intro h
    unfold extendedExpectation at hf_finite
    rw [show (∫⁻ x, (f x).toENNReal ∂Q) = ∞ by simpa [p] using h] at hf_finite
    simp [show (∫⁻ x, (-f x).toENNReal ∂Q) ≠ ∞ by simpa [q] using hq] at hf_finite
  have hqae : ∀ᵐ x ∂Q, q x ≠ ∞ := (ae_lt_top hq_meas hq).mono fun _ h => h.ne
  let f' : X → EReal := fun x => ((f x).toReal : ℝ)
  have hf'_meas : Measurable f' := by fun_prop
  have hff' : f' =ᵐ[Q] f := by
    filter_upwards [hqae] with x hx
    exact EReal.coe_toReal (hf_top x) (by simpa [q] using hx)
  have hf'_exp : extendedExpectation Q f' = (a : EReal) := by
    unfold extendedExpectation
    rw [show (∫⁻ x, (f' x).toENNReal ∂Q) = ∫⁻ x, (f x).toENNReal ∂Q from
          lintegral_congr_ae (hff'.mono fun _ hx => congrArg EReal.toENNReal hx),
      show (∫⁻ x, (-f' x).toENNReal ∂Q) = ∫⁻ x, (-f x).toENNReal ∂Q from
          lintegral_congr_ae (hff'.mono fun _ hx => congrArg (fun z => (-z).toENNReal) hx)]
    exact hf_finite
  have hf'_pos : (∫⁻ x, (f' x).toENNReal ∂Q) ≠ ∞ := by
    rw [lintegral_congr_ae (hff'.mono fun _ hx => congrArg EReal.toENNReal hx)]
    simpa [p] using hp
  have hneg_pos : (∫⁻ x, (-f' x).toENNReal ∂Q) ≠ ∞ := by
    rw [lintegral_congr_ae (hff'.mono fun _ hx => congrArg (fun z => (-z).toENNReal) hx)]
    simpa [q] using hq
  have hneg_exp : extendedExpectation Q (-f') = ((-a : ℝ) : EReal) := by
    unfold extendedExpectation at hf'_exp ⊢
    simp only [Pi.neg_apply, neg_neg] at hf'_exp ⊢
    let A : EReal := ↑(∫⁻ x, (f' x).toENNReal ∂Q)
    let B : EReal := ↑(∫⁻ x, (-f' x).toENNReal ∂Q)
    calc B - A = -A + B := by rw [sub_eq_add_neg, add_comm]
      _ = -(A - B) := (EReal.neg_sub (.inl (EReal.coe_ennreal_ne_bot _))
        (.inl (EReal.coe_ennreal_eq_top_iff.not.mpr hf'_pos))).symm
      _ = -((a : ℝ) : EReal) := by rw [hf'_exp]
      _ = ((-a : ℝ) : EReal) := by norm_cast
  have hnegAvg (n : ℕ) (s : Fin n → X) :
      extendedEmpiricalAvg (-f') n s = -extendedEmpiricalAvg f' n s := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [extendedEmpiricalAvg]
    rw [extendedEmpiricalAvg, if_neg hn, extendedEmpiricalAvg, if_neg hn]
    simp only [Pi.neg_apply, neg_neg]
    have hA : (n : ENNReal)⁻¹ * ∑ i, (f' (s i)).toENNReal ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (by simp [hn])) <|
        ENNReal.sum_ne_top.2 fun i _ => by simp [f']
    calc
      _ = -(↑((n : ENNReal)⁻¹ * ∑ i, (f' (s i)).toENNReal) : EReal) +
          ↑((n : ENNReal)⁻¹ * ∑ i, (-f' (s i)).toENNReal) := by rw [sub_eq_add_neg, add_comm]
      _ = _ := (EReal.neg_sub (.inl (EReal.coe_ennreal_ne_bot _))
        (.inl (EReal.coe_ennreal_eq_top_iff.not.mpr hA))).symm
  have hgood (n : ℕ) : ∀ᵐ ω ∂ℙ, ∀ i : Fin n, f (Xs i.val ω) ≠ ⊥ := by
    rw [ae_all_iff]
    intro i
    have hmap : MeasurePreserving (Xs i.val) ℙ Q :=
      ⟨hXs_meas i.val, by rw [(hXs_id i.val).map_eq, hXs_law]⟩
    exact (hmap.quasiMeasurePreserving.ae hqae).mono fun ω hω hfbot =>
      hω (EReal.toENNReal_eq_top_iff.mpr (by simpa [q] using congrArg Neg.neg hfbot))
  intro ε hε
  have hu := iid_extendedEmpiricalAvg_upper_tail Q ℙ Xs f' hf'_meas (by simp [f'])
    hf'_pos hXs_meas hXs_indep hXs_id hXs_law (a + ε) (by rw [hf'_exp]; norm_cast; linarith)
  have hl := iid_extendedEmpiricalAvg_upper_tail Q ℙ Xs (-f') hf'_meas.neg (by simp [f'])
    hneg_pos hXs_meas hXs_indep hXs_id hXs_law (-a + ε)
    (by rw [hneg_exp]; norm_cast; linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hl.add hu)
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => ?_)
  calc
    ℙ {ω | extendedEmpiricalAvg f n (fun i : Fin n => Xs i.val ω) < ((a - ε : ℝ) : EReal) ∨
        ((a + ε : ℝ) : EReal) < extendedEmpiricalAvg f n (fun i : Fin n => Xs i.val ω)}
      ≤ ℙ ({ω | ((-a + ε : ℝ) : EReal) ≤ extendedEmpiricalAvg (-f') n
          (fun i : Fin n => Xs i.val ω)} ∪ {ω | ((a + ε : ℝ) : EReal) ≤
          extendedEmpiricalAvg f' n (fun i : Fin n => Xs i.val ω)}) := measure_mono_ae <| by
        filter_upwards [hgood n] with ω hω
        intro h
        change extendedEmpiricalAvg f n (fun i : Fin n => Xs i.val ω) < ((a - ε : ℝ) : EReal) ∨
          ((a + ε : ℝ) : EReal) < extendedEmpiricalAvg f n (fun i : Fin n => Xs i.val ω) at h
        change ((-a + ε : ℝ) : EReal) ≤ extendedEmpiricalAvg (-f') n
            (fun i : Fin n => Xs i.val ω) ∨ ((a + ε : ℝ) : EReal) ≤
            extendedEmpiricalAvg f' n (fun i : Fin n => Xs i.val ω)
        have hx (i : Fin n) : f' (Xs i.val ω) = f (Xs i.val ω) :=
          EReal.coe_toReal (hf_top _) (hω i)
        have havg : extendedEmpiricalAvg f' n (fun i : Fin n => Xs i.val ω) =
            extendedEmpiricalAvg f n (fun i : Fin n => Xs i.val ω) := by
          unfold extendedEmpiricalAvg
          simp_rw [hx]
        rcases h with h | h
        · left
          change ((-a + ε : ℝ) : EReal) ≤ extendedEmpiricalAvg (-f') n
            (fun i : Fin n => Xs i.val ω)
          rw [hnegAvg, havg]
          rw [show -a + ε = -(a - ε) by ring, EReal.coe_neg]
          exact EReal.neg_le_neg_iff.mpr h.le
        · right; simpa [havg] using h.le
    _ ≤ _ := by simpa using measure_union_le _ _

end AsymptoticStatistics
