module
public import StatLean.StatisticalLearning.Core.SampleLaw
public import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
public import StatLean.ConcentrationInequalities.SubGaussian.Bounded

@[expose] public section

/-!
# Finite classes have the uniform convergence property

SSBD §4.2: for a finite hypothesis class and a loss with range in `[0,1]`,
Hoeffding's inequality for each fixed hypothesis (SSBD Eq. (4.2), tail
`2 exp(−2nε²)`) plus a union bound (SSBD Eq. (4.1)) gives
`P(∃ h ∈ 𝓗, |L_S(h) − L_D(h)| > ε) ≤ 2|𝓗| exp(−2nε²)`, hence the uniform
convergence property with `m^{UC}(ε,δ) ≤ ⌈log(2|𝓗|/δ)/(2ε²)⌉`
(SSBD Corollary 4.6, first half — exact constants frozen).

**Reference.** SSBD §4.2, Lemma 4.5, Corollary 4.6. Transcriptions:
`notes/statistical_learning/book_statements/ch2-5.md`.

**Formalization notes.** The per-hypothesis tail is assembled from the
project's `hoeffding` (`ConcentrationInequalities/SubGaussian/Hoeffding.lean`,
sub-Gaussian sum tail `exp(−n t²/(2σ²))`) with proxy `σ² = 1/4` from
`isSubGaussian_of_mem_Icc` on `[0,1]` — recovering the book's `exp(−2nε²)`
exactly — applied to the coordinate stream of `sampleLaw`
(`iIndepFun_eval_sampleLaw`, `measurePreserving_eval_sampleLaw`), on both the
variables and their negations for the two-sided form. The class is a `Finset H`
so `|𝓗|` is `𝓗.card`.
-/

open MeasureTheory ProbabilityTheory StatLean.ConcentrationInequalities
open scoped ENNReal NNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {n : ℕ} {ℓ : H → Z → ℝ}

/-- **Per-hypothesis two-sided Hoeffding deviation** (SSBD Eq. (4.2)): for a
fixed `h` with loss range in `[0,1]`,
`P_{S∼Dⁿ}(|L_S(h) − L_D(h)| > ε) ≤ 2 exp(−2nε²)`. -/
theorem measure_empRisk_deviation_le {h : H} {ε : ℝ}
    -- USER-INPUT: loss range in `[0,1]`; SSBD Cor. 4.6 hypothesis
    (hrange : ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: measurability of the loss of `h`; SSBD Remark 3.1
    (hmeas : Measurable (ℓ h))
    -- USER-INPUT: at least one example; SSBD §4.2 (implicit)
    (hn : 1 ≤ n)
    -- USER-INPUT: `ε > 0`; SSBD Lemma 4.5
    (hε : 0 < ε) :
    sampleLaw D n {s | ε < |empRisk ℓ s h - risk D ℓ h|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * n * ε ^ 2)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hint : Integrable (ℓ h) D :=
    Integrable.mono' (integrable_const 1) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hrange z).1]; exact (hrange z).2)
  set μ : Measure (Sample Z n) := sampleLaw D n with hμ
  set r : ℝ := risk D ℓ h with hr
  -- each coordinate has mean `r`
  have hmean : ∀ i : Fin n, ∫ s : Sample Z n, ℓ h (s i) ∂μ = r := by
    intro i
    have hmap := (measurePreserving_eval_sampleLaw (D := D) (n := n) i).map_eq
    have : ∫ z, ℓ h z ∂D = ∫ s : Sample Z n, ℓ h (s i) ∂μ := by
      conv_lhs => rw [← hmap]
      exact integral_map (measurable_pi_apply i).aemeasurable
        (by rw [hmap]; exact hint.1)
    exact this.symm
  -- each centered coordinate is sub-Gaussian with proxy 1/4
  have hprox : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) = (4⁻¹ : ℝ≥0) := by
    norm_num
  have hsub : ∀ i : Fin n,
      HasSubgaussianMGF (fun s : Sample Z n => ℓ h (s i) - r) (4⁻¹ : ℝ≥0) μ := by
    intro i
    have := isSubGaussian_of_mem_Icc (μ := μ) (X := fun s : Sample Z n => ℓ h (s i))
      (a := 0) (b := 1) (hmeas.comp (measurable_pi_apply i)).aemeasurable
      (Filter.Eventually.of_forall fun s => hrange (s i))
    rw [hprox] at this
    have h2 := isSubGaussian_iff.mp this
    rwa [hmean i] at h2
  -- the centered coordinates are independent
  have hindep : iIndepFun (fun (i : Fin n) (s : Sample Z n) => ℓ h (s i) - r) μ := by
    have := (iIndepFun_eval_sampleLaw (D := D) (n := n)).comp
      (fun _ : Fin n => fun z : Z => ℓ h z - r) (fun _ => hmeas.sub_const r)
    simpa [Function.comp] using! this
  -- one-sided Hoeffding tail, for any independent sub-Gaussian family
  have key : ∀ Y : Fin n → Sample Z n → ℝ, iIndepFun Y μ →
      (∀ i, HasSubgaussianMGF (Y i) (4⁻¹ : ℝ≥0) μ) →
      μ {s | (n : ℝ) * ε ≤ ∑ i, Y i s} ≤
        ENNReal.ofReal (Real.exp (-2 * n * ε ^ 2)) := by
    intro Y hY hYsub
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY
      (c := fun _ : Fin n => (4⁻¹ : ℝ≥0)) (s := Finset.univ)
      (fun i _ => hYsub i) (ε := (n : ℝ) * ε) (by positivity)
    have hc : ((∑ _i : Fin n, (4⁻¹ : ℝ≥0) : ℝ≥0) : ℝ) = (n : ℝ) / 4 := by
      push_cast [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
      ring
    rw [hc] at h
    have hexp : -((n : ℝ) * ε) ^ 2 / (2 * ((n : ℝ) / 4)) = -2 * n * ε ^ 2 := by
      field_simp
      ring
    rw [hexp] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal h
  -- the deviation event splits into the two one-sided tails
  have hincl : {s : Sample Z n | ε < |empRisk ℓ s h - r|} ⊆
      {s : Sample Z n | (n : ℝ) * ε ≤ ∑ i, (ℓ h (s i) - r)} ∪
        {s : Sample Z n | (n : ℝ) * ε ≤ ∑ i, -(ℓ h (s i) - r)} := by
    intro s hs
    have hs' : ε < |empRisk ℓ s h - r| := hs
    have hsum : ∑ i, (ℓ h (s i) - r) = (n : ℝ) * (empRisk ℓ s h - r) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, empRisk]
      field_simp
    have hlt : (n : ℝ) * ε < |∑ i, (ℓ h (s i) - r)| := by
      rw [hsum, abs_mul, abs_of_pos hnR]
      exact mul_lt_mul_of_pos_left hs' hnR
    have hneg : ∑ i, -(ℓ h (s i) - r) = -∑ i, (ℓ h (s i) - r) := by
      rw [Finset.sum_neg_distrib]
    rcases lt_abs.mp hlt with hcase | hcase
    · exact Or.inl hcase.le
    · refine Or.inr ?_
      change (n : ℝ) * ε ≤ ∑ i, -(ℓ h (s i) - r)
      rw [hneg]
      exact hcase.le
  calc μ {s | ε < |empRisk ℓ s h - r|}
      ≤ μ ({s : Sample Z n | (n : ℝ) * ε ≤ ∑ i, (ℓ h (s i) - r)} ∪
        {s : Sample Z n | (n : ℝ) * ε ≤ ∑ i, -(ℓ h (s i) - r)}) := measure_mono hincl
    _ ≤ μ {s : Sample Z n | (n : ℝ) * ε ≤ ∑ i, (ℓ h (s i) - r)} +
        μ {s : Sample Z n | (n : ℝ) * ε ≤ ∑ i, -(ℓ h (s i) - r)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-2 * n * ε ^ 2)) +
        ENNReal.ofReal (Real.exp (-2 * n * ε ^ 2)) := by
        gcongr
        · exact key _ hindep hsub
        · exact key _ (hindep.comp (fun _ => fun x : ℝ => -x) fun _ => measurable_neg)
            fun i => (hsub i).neg
    _ = ENNReal.ofReal (2 * Real.exp (-2 * n * ε ^ 2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
        ring_nf

/-- **Finite-class uniform deviation bound** (SSBD Eq. (4.1) + (4.2)): for a
finite class with `[0,1]`-valued loss,
`P(∃ h ∈ 𝓗, |L_S(h) − L_D(h)| > ε) ≤ 2|𝓗| exp(−2nε²)`. -/
theorem finiteClass_measure_uniformDeviation_le (𝓗 : Finset H) {ε : ℝ}
    -- USER-INPUT: loss range in `[0,1]` on the class; SSBD Cor. 4.6
    (hrange : ∀ h ∈ 𝓗, ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: measurability of each loss; SSBD Remark 3.1
    (hmeas : ∀ h ∈ 𝓗, Measurable (ℓ h))
    -- USER-INPUT: at least one example; SSBD §4.2 (implicit)
    (hn : 1 ≤ n)
    -- USER-INPUT: `ε > 0`; SSBD Lemma 4.5
    (hε : 0 < ε) :
    sampleLaw D n {s | ∃ h ∈ 𝓗, ε < |empRisk ℓ s h - risk D ℓ h|} ≤
      ENNReal.ofReal (2 * 𝓗.card * Real.exp (-2 * n * ε ^ 2)) := by
  classical
  have hset : {s : Sample Z n | ∃ h ∈ 𝓗, ε < |empRisk ℓ s h - risk D ℓ h|} =
      ⋃ h ∈ 𝓗, {s : Sample Z n | ε < |empRisk ℓ s h - risk D ℓ h|} := by
    ext s; simp
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun h hh =>
    measure_empRisk_deviation_le (hrange h hh) (hmeas h hh) hn hε)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  ring_nf
  exact le_refl _

/-- **SSBD Corollary 4.6, uniform-convergence half**: a finite class with
`[0,1]`-valued loss has the uniform convergence property with
`m^{UC}(ε,δ) = ⌈log(2|𝓗|/δ)/(2ε²)⌉` (exact book constant). -/
theorem finiteClass_hasUniformConvergenceWith (𝓗 : Finset H)
    -- USER-INPUT: nonempty class; SSBD §4.2 (implicit — else vacuous)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: loss range in `[0,1]` on the class; SSBD Cor. 4.6
    (hrange : ∀ h ∈ 𝓗, ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: measurability of each loss; SSBD Remark 3.1
    (hmeas : ∀ h ∈ 𝓗, Measurable (ℓ h)) :
    HasUniformConvergenceWith (↑𝓗 : Set H) ℓ
      (fun ε δ => ⌈Real.log (2 * 𝓗.card / δ) / (2 * ε ^ 2)⌉₊) := by
  intro D hD ε δ hε hδ hδ1 n hn
  haveI := hD
  have hN1 : (1 : ℝ) ≤ (𝓗.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr h𝓗
  have hlogpos : 0 < Real.log (2 * 𝓗.card / δ) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hδ]
    nlinarith
  have hquot : 0 < Real.log (2 * 𝓗.card / δ) / (2 * ε ^ 2) := by positivity
  -- the sample size is at least one
  have hn1 : 1 ≤ n := le_trans (Nat.ceil_pos.mpr hquot) hn
  -- the book's arithmetic: `2 N e^{-2 n ε²} ≤ δ`
  have hnR : Real.log (2 * 𝓗.card / δ) / (2 * ε ^ 2) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hlog_le : Real.log (2 * 𝓗.card / δ) ≤ 2 * n * ε ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hnR
    nlinarith
  have hinv : (2 * (𝓗.card : ℝ) / δ)⁻¹ = Real.exp (-Real.log (2 * 𝓗.card / δ)) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
  have hexp : Real.exp (-2 * n * ε ^ 2) ≤ (2 * (𝓗.card : ℝ) / δ)⁻¹ := by
    rw [hinv]
    exact Real.exp_le_exp.mpr (by linarith)
  have hbound : 2 * (𝓗.card : ℝ) * Real.exp (-2 * n * ε ^ 2) ≤ δ := by
    have h2N : (0 : ℝ) < 2 * (𝓗.card : ℝ) := by linarith
    calc 2 * (𝓗.card : ℝ) * Real.exp (-2 * n * ε ^ 2)
        ≤ 2 * (𝓗.card : ℝ) * (2 * (𝓗.card : ℝ) / δ)⁻¹ :=
          mul_le_mul_of_nonneg_left hexp h2N.le
      _ = δ := by field_simp
  -- the bad event
  have hbad : sampleLaw D n {s | ∃ h ∈ 𝓗, ε < |empRisk ℓ s h - risk D ℓ h|} ≤
      ENNReal.ofReal δ := by
    refine (finiteClass_measure_uniformDeviation_le 𝓗 hrange hmeas hn1 hε).trans ?_
    exact ENNReal.ofReal_le_ofReal hbound
  have hcompl : {s : Sample Z n | UniformDeviationLE D (↑𝓗 : Set H) ℓ s ε}ᶜ ⊆
      {s : Sample Z n | ∃ h ∈ 𝓗, ε < |empRisk ℓ s h - risk D ℓ h|} := by
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, UniformDeviationLE, not_forall,
      Finset.mem_coe, not_le] at hs
    obtain ⟨h, hh, hlt⟩ := hs
    exact ⟨h, hh, hlt⟩
  have hcover : (1 : ℝ≥0∞) ≤
      sampleLaw D n {s : Sample Z n | UniformDeviationLE D (↑𝓗 : Set H) ℓ s ε} +
        sampleLaw D n {s : Sample Z n | UniformDeviationLE D (↑𝓗 : Set H) ℓ s ε}ᶜ := by
    have h := measure_union_le (μ := sampleLaw D n)
      {s : Sample Z n | UniformDeviationLE D (↑𝓗 : Set H) ℓ s ε}
      {s : Sample Z n | UniformDeviationLE D (↑𝓗 : Set H) ℓ s ε}ᶜ
    rwa [Set.union_compl_self, measure_univ] at h
  rw [ENNReal.ofReal_sub 1 hδ.le, ENNReal.ofReal_one]
  refine tsub_le_iff_right.mpr ?_
  refine hcover.trans ?_
  gcongr
  exact (measure_mono hcompl).trans hbad

end StatLean.StatisticalLearning
