module
public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.StrongLaw
public import StatLean.AsymptoticStatistics.EmpiricalProcess.VCSharpPacking

@[expose] public section

/-!
# Sharp finite `Lʳ` packings for VC-subgraph classes

This file proves the finite-packing step of the Chazelle--Haussler/layer-cake
argument in van der Vaart Lemma 19.15. The result is stated for finite
subfamilies and arbitrary probability laws.  The original envelope need not
be measurable.

Reference: van der Vaart, *Asymptotic Statistics*, Lemma 19.15, pp.275--276.
-/

namespace AsymptoticStatistics.EmpiricalProcess

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology symmDiff

universe u v

open UniformEntropyStructural

private noncomputable def pullbackSetFamily (x : β → α)
    (𝒜 : Set (Set α)) : Set (Set β) :=
  {B | ∃ A ∈ 𝒜, B = x ⁻¹' A}

/-- Pullback along an arbitrary map cannot increase the book VC index. -/
private theorem vcIndexLE_pullbackSetFamily
    (x : β → α) (𝒜 : Set (Set α)) (V : ℕ)
    (hVC : VCIndexLE 𝒜 V) :
    VCIndexLE (pullbackSetFamily x 𝒜) V := by
  classical
  intro s hs hsh
  have hinj : Set.InjOn x (s : Set β) := by
    intro i hi j hj hij
    by_contra hne
    have hsingle : ({i} : Finset β) ⊆ s := by
      simpa only [Finset.singleton_subset_iff] using! hi
    obtain ⟨B, ⟨A, hA, rfl⟩, hB⟩ := hsh {i} hsingle
    have hii : i ∈ x ⁻¹' A := (hB i hi).mp (by simp)
    have hji : j ∉ x ⁻¹' A := by
      intro hjA
      have : j ∈ ({i} : Finset β) := (hB j hj).mpr hjA
      exact hne (Finset.mem_singleton.mp this |>.symm)
    exact hji (by simpa only [Set.mem_preimage, hij] using hii)
  apply hVC (s.image x)
  · rw [Finset.card_image_iff.mpr hinj]
    exact hs
  · intro t ht
    let u := s.filter fun i ↦ x i ∈ t
    have hus : u ⊆ s := Finset.filter_subset _ _
    obtain ⟨B, ⟨A, hA, rfl⟩, hB⟩ := hsh u hus
    refine ⟨A, hA, fun y hy ↦ ?_⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    simpa only [u, Finset.mem_filter, hi, true_and, Set.mem_preimage]
      using hB i hi

private noncomputable def sampleTrace (z : α → β) (S : Set β) [Fintype α] : Finset α := by
  classical
  exact Finset.univ.filter fun i ↦ z i ∈ S

private theorem coe_sampleTrace (z : α → β) (S : Set β) [Fintype α] :
    (sampleTrace z S : Set α) = z ⁻¹' S := by
  classical
  ext i
  simp [sampleTrace]

private theorem sampleTrace_symmDiff_card
    (z : α → β) (S T : Set β) [Fintype α] :
    finsetHammingDistance (sampleTrace z S) (sampleTrace z T) =
      (sampleTrace z (S ∆ T)).card := by
  classical
  unfold finsetHammingDistance sampleTrace
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, true_and, Set.mem_symmDiff]

private noncomputable def symmetricUnitInterval : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)

private instance : IsProbabilityMeasure symmetricUnitInterval := by
  rw [isProbabilityMeasure_iff]
  change ((2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)) Set.univ = 1
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc]
  convert ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) using 1
  norm_num

private theorem symmetricUnitInterval_Iio_symmDiff
    {a b : ℝ} (ha₀ : -1 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : -1 ≤ b) (hb₁ : b ≤ 1) :
    symmetricUnitInterval (Set.Iio a ∆ Set.Iio b) =
      ENNReal.ofReal |a - b| / 2 := by
  rw [symmetricUnitInterval, Measure.smul_apply]
  by_cases hab : a ≤ b
  · have hset : (Set.Iio a ∆ Set.Iio b) ∩ Set.Icc (-1 : ℝ) 1 = Set.Ico a b := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_symmDiff, Set.mem_Iio, Set.mem_Icc,
        Set.mem_Ico]
      constructor
      · rintro ⟨(hx | hx), _, _⟩
        · exact (hx.2 (lt_of_lt_of_le hx.1 hab)).elim
        · exact ⟨le_of_not_gt hx.2, hx.1⟩
      · rintro ⟨hax, hxb⟩
        exact ⟨Or.inr ⟨hxb, not_lt_of_ge hax⟩, ha₀.trans hax, hxb.le.trans hb₁⟩
    rw [Measure.restrict_apply (measurableSet_Iio.symmDiff measurableSet_Iio),
      hset, Real.volume_Ico]
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    change (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (b - a) =
      ENNReal.ofReal (-(a - b)) * (2 : ℝ≥0∞)⁻¹
    rw [show b - a = -(a - b) by ring]
    ac_rfl
  · have hba : b ≤ a := le_of_not_ge hab
    have hset : (Set.Iio a ∆ Set.Iio b) ∩ Set.Icc (-1 : ℝ) 1 = Set.Ico b a := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_symmDiff, Set.mem_Iio, Set.mem_Icc,
        Set.mem_Ico]
      constructor
      · rintro ⟨(hx | hx), _, _⟩
        · exact ⟨le_of_not_gt hx.2, hx.1⟩
        · exact (hx.2 (lt_of_lt_of_le hx.1 hba)).elim
      · rintro ⟨hbx, hxa⟩
        exact ⟨Or.inl ⟨hxa, not_lt_of_ge hbx⟩, hb₀.trans hbx, hxa.le.trans ha₁⟩
    rw [Measure.restrict_apply (measurableSet_Iio.symmDiff measurableSet_Iio),
      hset, Real.volume_Ico, abs_of_nonneg (sub_nonneg.mpr hba)]
    change (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (a - b) =
      ENNReal.ofReal (a - b) * (2 : ℝ≥0∞)⁻¹
    ac_rfl

private theorem measurableSet_strictSubgraph [MeasurableSpace Ω]
    {f : Ω → ℝ} (hf : Measurable f) :
    MeasurableSet (strictSubgraph f) := by
  exact measurableSet_lt measurable_snd (hf.comp measurable_fst)

private theorem prod_symmetricUnitInterval_strictSubgraph_symmDiff
    [MeasurableSpace Ω] (Q : Measure Ω) (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf₀ : ∀ x, -1 ≤ f x) (hf₁ : ∀ x, f x ≤ 1)
    (hg₀ : ∀ x, -1 ≤ g x) (hg₁ : ∀ x, g x ≤ 1) :
    (Q.prod symmetricUnitInterval) (strictSubgraph f ∆ strictSubgraph g) =
      ∫⁻ x, ENNReal.ofReal |f x - g x| / 2 ∂Q := by
  rw [Measure.prod_apply
    ((measurableSet_strictSubgraph hf).symmDiff (measurableSet_strictSubgraph hg))]
  apply lintegral_congr
  intro x
  change symmetricUnitInterval (Set.Iio (f x) ∆ Set.Iio (g x)) = _
  exact symmetricUnitInterval_Iio_symmDiff (hf₀ x) (hf₁ x) (hg₀ x) (hg₁ x)

private theorem outerLpNorm_mono_abs
    [MeasurableSpace Ω] (Q : Measure Ω) (f g : Ω → ℝ) (r : ℝ) (hr : 0 < r)
    (hfg : ∀ x, |f x| ≤ |g x|) :
    outerLpNorm Q f r ≤ outerLpNorm Q g r := by
  unfold outerLpNorm
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply outerExpectation_mono
  intro x
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hfg x)) hr.le

private theorem outerLpNorm_rpow_eq_lintegral
    [MeasurableSpace Ω] (Q : Measure Ω) (f : Ω → ℝ) (r : ℝ) (hr : 0 < r)
    (hf : Measurable f) :
    outerLpNorm Q f r ^ r = ∫⁻ x, ENNReal.ofReal |f x| ^ r ∂Q := by
  unfold outerLpNorm
  rw [outerExpectation_eq_lintegral (by fun_prop), ← ENNReal.rpow_mul,
    inv_mul_cancel₀ hr.ne', ENNReal.rpow_one]

private noncomputable def normalizedBy (H f : Ω → ℝ) : Ω → ℝ :=
  fun x ↦ if H x = 0 then 0 else f x / H x

private theorem measurable_normalizedBy [MeasurableSpace Ω]
    {H f : Ω → ℝ} (hH : Measurable H) (hf : Measurable f) :
    Measurable (normalizedBy H f) := by
  unfold normalizedBy
  exact Measurable.ite (hH (measurableSet_singleton (0 : ℝ))) measurable_const (hf.div hH)

private theorem abs_normalizedBy_le_one
    {H f : Ω → ℝ} (hH₀ : ∀ x, 0 ≤ H x)
    (hfH : ∀ x, |f x| ≤ H x) :
    ∀ x, |normalizedBy H f x| ≤ 1 := by
  intro x
  rw [normalizedBy]
  split_ifs with hx
  · simp
  · rw [abs_div, abs_of_nonneg (hH₀ x), div_le_one (lt_of_le_of_ne (hH₀ x) (Ne.symm hx))]
    exact hfH x

private theorem normalizedBy_sub
    {H f g : Ω → ℝ} :
    ∀ x, normalizedBy H f x - normalizedBy H g x =
      if H x = 0 then 0 else (f x - g x) / H x := by
  intro x
  by_cases hx : H x = 0
  · simp [normalizedBy, hx]
  · simp [normalizedBy, hx, sub_div]

mutual

/-- Weighted layer-cake transfer for a finite measurable family.  The finite
envelope is part of the input, so no measurability of an ambient envelope is
used. -/
private theorem finite_lp_packing_of_integral_separation
    {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (A : Finset (Ω → ℝ)) (F : Set (Ω → ℝ)) (H : Ω → ℝ)
    (V : ℕ) (r η : ℝ)
    (hA : ∀ f ∈ A, f ∈ F)
    (hFm : ∀ f ∈ A, Measurable f)
    (hVC : VCIndexLE (strictSubgraphFamily F) V)
    (hHm : Measurable H) (hH₀ : ∀ x, 0 ≤ H x)
    (hAH : ∀ f ∈ A, ∀ x, |f x| ≤ H x)
    (hr : 1 ≤ r) (hη₀ : 0 < η) (hη₁ : η < 1)
    (hI₀ : 0 < ∫⁻ x, ENNReal.ofReal (H x) ^ r ∂Q)
    (hItop : (∫⁻ x, ENNReal.ofReal (H x) ^ r ∂Q) < ⊤)
    (hsep : ∀ f ∈ A, ∀ g ∈ A, f ≠ g →
      ENNReal.ofReal (2 * η) ^ r * (∫⁻ x, ENNReal.ofReal (H x) ^ r ∂Q) <
        ∫⁻ x, ENNReal.ofReal |f x - g x| ^ r ∂Q) :
    (A.card : ℝ) ≤
      (1 / (2 * Real.sqrt (Real.exp 1))) * V * (4 * Real.exp 1) ^ V *
        (η ^ r) ^ (-((V - 1 : ℕ) : ℝ)) := by
  classical
  let I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (H x) ^ r ∂Q
  let qDensity : Ω → ℝ≥0∞ := fun x ↦ I⁻¹ * ENNReal.ofReal (H x) ^ r
  let QH : Measure Ω := Q.withDensity qDensity
  have hqd : Measurable qDensity := by
    exact measurable_const.mul
      (ENNReal.continuous_rpow_const.measurable.comp hHm.ennreal_ofReal)
  have hHpowm : Measurable fun x ↦ ENNReal.ofReal (H x) ^ r :=
    ENNReal.continuous_rpow_const.measurable.comp hHm.ennreal_ofReal
  have hI₀' : I ≠ 0 := by simpa only [I] using hI₀.ne'
  have hItop' : I ≠ ⊤ := by simpa only [I] using hItop.ne
  have hQH : IsProbabilityMeasure QH := by
    rw [isProbabilityMeasure_iff]
    change Q.withDensity qDensity Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    change (∫⁻ x, I⁻¹ * ENNReal.ofReal (H x) ^ r ∂Q) = 1
    calc
      _ = I⁻¹ * (∫⁻ x, ENNReal.ofReal (H x) ^ r ∂Q) := by
        simpa only [Function.comp_apply] using
          (lintegral_const_mul (μ := Q) I⁻¹ hHpowm)
      _ = 1 := by simpa only [I] using ENNReal.inv_mul_cancel hI₀' hItop'
  letI : IsProbabilityMeasure QH := hQH
  let N (f : Ω → ℝ) : Ω → ℝ := normalizedBy H f
  let φ : Ω × ℝ → Ω × ℝ := fun p ↦
    (p.1, if H p.1 = 0 then p.2 else H p.1 * p.2)
  have hNm (f : Ω → ℝ) (hf : f ∈ A) : Measurable (N f) := by
    exact measurable_normalizedBy hHm (hFm f hf)
  have hNabs (f : Ω → ℝ) (hf : f ∈ A) : ∀ x, |N f x| ≤ 1 := by
    exact abs_normalizedBy_le_one hH₀ (hAH f hf)
  have hgraph (f : Ω → ℝ) (hf : f ∈ A) :
      strictSubgraph (N f) = φ ⁻¹' strictSubgraph f := by
    ext p
    change p.2 < normalizedBy H f p.1 ↔
      (if H p.1 = 0 then p.2 else H p.1 * p.2) < f p.1
    by_cases hx : H p.1 = 0
    · have hfx : f p.1 = 0 := by
        apply abs_eq_zero.mp
        exact le_antisymm ((hAH f hf p.1).trans_eq hx) (abs_nonneg _)
      simp [normalizedBy, hx, hfx]
    · have hHx : 0 < H p.1 := lt_of_le_of_ne (hH₀ p.1) (Ne.symm hx)
      simp only [normalizedBy, hx, if_false]
      simpa only [mul_comm] using (lt_div_iff₀ hHx)
  have hVCpull : VCIndexLE
      (pullbackSetFamily φ (strictSubgraphFamily F)) V :=
    vcIndexLE_pullbackSetFamily φ (strictSubgraphFamily F) V hVC
  have hset (f : Ω → ℝ) (hf : f ∈ A) :
      strictSubgraph (N f) ∈ pullbackSetFamily φ (strictSubgraphFamily F) := by
    exact ⟨strictSubgraph f, ⟨f, hA f hf, rfl⟩, hgraph f hf⟩
  have hsepGraph : ∀ f ∈ A, ∀ g ∈ A, f ≠ g →
      ENNReal.ofReal (η ^ r) <
        (QH.prod symmetricUnitInterval) (strictSubgraph (N f) ∆ strictSubgraph (N g)) := by
    intro f hf g hg hfg
    let J : ℝ≥0∞ := ∫⁻ x,
      ENNReal.ofReal (H x) ^ r * (ENNReal.ofReal |N f x - N g x| / 2) ∂Q
    have hNdistm : Measurable fun x ↦ ENNReal.ofReal |N f x - N g x| :=
      (by
        simpa only [Real.norm_eq_abs] using!
          (((hNm f hf).sub (hNm g hg)).norm.ennreal_ofReal))
    have hJm : Measurable fun x ↦
        ENNReal.ofReal (H x) ^ r * (ENNReal.ofReal |N f x - N g x| / 2) :=
      hHpowm.mul (hNdistm.div_const 2)
    have hdist :
        (QH.prod symmetricUnitInterval) (strictSubgraph (N f) ∆ strictSubgraph (N g)) =
          I⁻¹ * J := by
      rw [prod_symmetricUnitInterval_strictSubgraph_symmDiff QH (N f) (N g)
        (hNm f hf) (hNm g hg)
        (fun x ↦ (neg_le_of_abs_le (hNabs f hf x)))
        (fun x ↦ (le_abs_self _).trans (hNabs f hf x))
        (fun x ↦ (neg_le_of_abs_le (hNabs g hg x)))
        (fun x ↦ (le_abs_self _).trans (hNabs g hg x))]
      change (∫⁻ x, ENNReal.ofReal |N f x - N g x| / 2 ∂Q.withDensity qDensity) = _
      rw [lintegral_withDensity_eq_lintegral_mul Q hqd (hNdistm.div_const 2)]
      simp only [Pi.mul_apply, qDensity, J, mul_assoc]
      rw [lintegral_const_mul _ hJm]
    have hpoint : ∀ x,
        ENNReal.ofReal |f x - g x| ^ r ≤
          (2 : ℝ≥0∞) ^ r *
            (ENNReal.ofReal (H x) ^ r * (ENNReal.ofReal |N f x - N g x| / 2)) := by
      intro x
      by_cases hx : H x = 0
      · have hfx : f x = 0 := by
          apply abs_eq_zero.mp
          exact le_antisymm ((hAH f hf x).trans_eq hx) (abs_nonneg _)
        have hgx : g x = 0 := by
          apply abs_eq_zero.mp
          exact le_antisymm ((hAH g hg x).trans_eq hx) (abs_nonneg _)
        simp [hx, hfx, hgx, ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hr)]
      · have hHx : 0 < H x := lt_of_le_of_ne (hH₀ x) (Ne.symm hx)
        let u : ℝ≥0∞ := ENNReal.ofReal |N f x - N g x|
        have hu₂ : u ≤ 2 := by
          change ENNReal.ofReal |N f x - N g x| ≤ 2
          calc
            ENNReal.ofReal |N f x - N g x| ≤ ENNReal.ofReal (2 : ℝ) := by
              apply ENNReal.ofReal_le_ofReal
              calc
                |N f x - N g x| ≤ |N f x| + |N g x| := abs_sub _ _
                _ ≤ 1 + 1 := add_le_add (hNabs f hf x) (hNabs g hg x)
                _ = 2 := by norm_num
            _ = 2 := by norm_num
        have huhalf : u / 2 ≤ 1 :=
          (ENNReal.div_le_iff_le_mul (by norm_num) (by norm_num)).2 (by simpa using hu₂)
        have hur : (u / 2) ^ r ≤ u / 2 :=
          ENNReal.rpow_le_self_of_le_one huhalf hr
        have hdreal : |f x - g x| = H x * |N f x - N g x| := by
          change |f x - g x| = H x * |normalizedBy H f x - normalizedBy H g x|
          rw [normalizedBy_sub x, if_neg hx,
            abs_div, abs_of_nonneg (hH₀ x)]
          exact (mul_div_cancel₀ _ hx).symm
        have hdu : ENNReal.ofReal |f x - g x| = ENNReal.ofReal (H x) * u := by
          rw [hdreal, ENNReal.ofReal_mul (hH₀ x)]
        calc
          ENNReal.ofReal |f x - g x| ^ r =
              (ENNReal.ofReal (H x) * u) ^ r := by rw [hdu]
          _ = ENNReal.ofReal (H x) ^ r * u ^ r :=
            ENNReal.mul_rpow_of_nonneg _ _ (le_trans (by norm_num) hr)
          _ = ENNReal.ofReal (H x) ^ r * ((2 : ℝ≥0∞) * (u / 2)) ^ r := by
            rw [ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)]
          _ = ENNReal.ofReal (H x) ^ r * ((2 : ℝ≥0∞) ^ r * (u / 2) ^ r) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (le_trans (by norm_num) hr)]
          _ ≤ ENNReal.ofReal (H x) ^ r * ((2 : ℝ≥0∞) ^ r * (u / 2)) := by
            gcongr
          _ = (2 : ℝ≥0∞) ^ r *
              (ENNReal.ofReal (H x) ^ r * (ENNReal.ofReal |N f x - N g x| / 2)) := by
            simp only [u]
            ac_rfl
    have hDJ : (∫⁻ x, ENNReal.ofReal |f x - g x| ^ r ∂Q) ≤
        (2 : ℝ≥0∞) ^ r * J := by
      calc
        (∫⁻ x, ENNReal.ofReal |f x - g x| ^ r ∂Q) ≤
            ∫⁻ x, (2 : ℝ≥0∞) ^ r *
              (ENNReal.ofReal (H x) ^ r * (ENNReal.ofReal |N f x - N g x| / 2)) ∂Q :=
          lintegral_mono hpoint
        _ = (2 : ℝ≥0∞) ^ r * J := by
          rw [lintegral_const_mul _ hJm]
    have hscaled : (2 : ℝ≥0∞) ^ r * (ENNReal.ofReal η ^ r * I) <
        (2 : ℝ≥0∞) ^ r * J := by
      refine lt_of_lt_of_le ?_ hDJ
      simpa only [I, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
        ENNReal.mul_rpow_of_nonneg _ _ (le_trans (by norm_num) hr), mul_assoc]
        using hsep f hf g hg hfg
    have hηIJ : ENNReal.ofReal η ^ r * I < J := by
      exact (ENNReal.mul_lt_mul_iff_right
        ((ENNReal.rpow_eq_zero_iff_of_pos (lt_of_lt_of_le zero_lt_one hr)).not.mpr (by norm_num))
        (ENNReal.rpow_ne_top_of_nonneg (le_trans (by norm_num) hr) (by norm_num))).mp hscaled
    have hinv : ENNReal.ofReal η ^ r < I⁻¹ * J := by
      have := ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.mpr hItop')
        (ENNReal.inv_ne_top.mpr hI₀') hηIJ
      simpa only [mul_assoc, ENNReal.mul_inv_cancel hI₀' hItop', mul_one,
        mul_comm J I⁻¹] using this
    rw [hdist]
    simpa only [ENNReal.ofReal_rpow_of_pos hη₀] using hinv
  exact finite_measure_packing (QH.prod symmetricUnitInterval) A
    (fun f ↦ strictSubgraph (N f))
    (pullbackSetFamily φ (strictSubgraphFamily F)) V (η ^ r)
    hset (fun f hf ↦ measurableSet_strictSubgraph (hNm f hf)) hVCpull
    (Real.rpow_pos_of_pos hη₀ r) (Real.rpow_le_one hη₀.le hη₁.le (le_trans (by norm_num) hr))
    hsepGraph

/-- A finite probability-measure packing is witnessed by one finite empirical
trace, so the finite Chazelle--Haussler bound applies. Repeated sample
points are retained as distinct coordinates; pullback VC monotonicity handles
them without a finite-support assumption on the original law. -/
private theorem finite_measure_packing
    {α ι : Type u} [MeasurableSpace α]
    (P : Measure α) [IsProbabilityMeasure P]
    (I : Finset ι) (S : ι → Set α) (𝒜 : Set (Set α))
    (V : ℕ) (δ : ℝ)
    (hS : ∀ i ∈ I, S i ∈ 𝒜)
    (hSm : ∀ i ∈ I, MeasurableSet (S i))
    (hVC : VCIndexLE 𝒜 V)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ENNReal.ofReal δ < P (S i ∆ S j)) :
    (I.card : ℝ) ≤
      (1 / (2 * Real.sqrt (Real.exp 1))) * V * (4 * Real.exp 1) ^ V *
        δ ^ (-((V - 1 : ℕ) : ℝ)) := by
  classical
  obtain ⟨Ξ, mΞ, R, X, hXm, hXlaw, hXind, hR⟩ := exists_iid ℕ P
  letI : MeasurableSpace Ξ := mΞ
  letI : IsProbabilityMeasure R := hR
  let Y (i j : ↥I) (n : ℕ) (ξ : Ξ) : ℝ :=
    (S i.1 ∆ S j.1).indicator 1 (X n ξ)
  have hYm (i j : ↥I) (n : ℕ) : Measurable (Y i j n) := by
    exact (measurable_const.indicator
      ((hSm i.1 i.2).symmDiff (hSm j.1 j.2))).comp (hXm n)
  have hYint (i j : ↥I) : Integrable (Y i j 0) R := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (hYm i j 0).aestronglyMeasurable (Eventually.of_forall fun ξ ↦ ?_)
    simp only [Y]
    by_cases h : X 0 ξ ∈ (S i.1 ∆ S j.1) <;> simp [h]
  have hYind (i j : ↥I) : Pairwise fun n m ↦ Y i j n ⟂ᵢ[R] Y i j m := by
    intro n m hnm
    have hφ : Measurable ((S i.1 ∆ S j.1).indicator (fun _ ↦ (1 : ℝ))) :=
      measurable_const.indicator ((hSm i.1 i.2).symmDiff (hSm j.1 j.2))
    exact (hXind.indepFun hnm).comp hφ hφ
  have hYident (i j : ↥I) : ∀ n, IdentDistrib (Y i j n) (Y i j 0) R R := by
    intro n
    have hφ : Measurable ((S i.1 ∆ S j.1).indicator (fun _ ↦ (1 : ℝ))) :=
      measurable_const.indicator ((hSm i.1 i.2).symmDiff (hSm j.1 j.2))
    simpa only [Y, Function.comp_apply] using!
      ((hXlaw n).identDistrib (hXlaw 0)).comp hφ
  have hYmean (i j : ↥I) : R[Y i j 0] = (P (S i.1 ∆ S j.1)).toReal := by
    have hφ : AEStronglyMeasurable
        ((S i.1 ∆ S j.1).indicator (fun _ ↦ (1 : ℝ))) P :=
      (measurable_const.indicator
        ((hSm i.1 i.2).symmDiff (hSm j.1 j.2))).aestronglyMeasurable
    rw [show Y i j 0 =
        ((S i.1 ∆ S j.1).indicator (fun _ ↦ (1 : ℝ))) ∘ X 0 by rfl,
      (hXlaw 0).integral_comp hφ]
    simpa only [measureReal_def] using!
      (integral_indicator_one (μ := P)
        ((hSm i.1 i.2).symmDiff (hSm j.1 j.2)))
  have hae : ∀ᵐ ξ ∂R, ∀ i j : ↥I,
      Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.range n, Y i j k ξ) / n)
        atTop (nhds (P (S i.1 ∆ S j.1)).toReal) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    simpa only [hYmean i j] using
      strong_law_ae_real (Y i j) (hYint i j) (hYind i j) (hYident i j)
  obtain ⟨ξ, hξ⟩ := hae.exists
  have hpairs : ∀ i j : ↥I, ∀ᶠ n : ℕ in atTop, i ≠ j →
      δ < (∑ k ∈ Finset.range n, Y i j k ξ) / n := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ hnij ↦ (hnij hij).elim
    · have hijval : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
      have hp := hsep i.1 i.2 j.1 j.2 hijval
      rw [ENNReal.ofReal_lt_iff_lt_toReal hδ0.le (measure_ne_top P _)] at hp
      exact (((tendsto_order.1 (hξ i j)).1 δ hp).mono fun _ h _ ↦ h)
  have hevent : ∀ᶠ n : ℕ in atTop, 0 < n ∧
      ∀ i j : ↥I, i ≠ j →
        δ < (∑ k ∈ Finset.range n, Y i j k ξ) / n := by
    filter_upwards [eventually_gt_atTop 0,
      (eventually_all.2 fun i : ↥I ↦ eventually_all.2 fun j : ↥I ↦ hpairs i j)] with n hn hall
    exact ⟨hn, fun i j hij ↦ hall i j hij⟩
  obtain ⟨n, hn, hnavg⟩ := hevent.exists
  let z : Fin n → α := fun k ↦ X k.1 ξ
  let 𝒟 : Finset (Finset (Fin n)) := I.image fun i ↦ sampleTrace z (S i)
  have himage : Set.InjOn (fun i ↦ sampleTrace z (S i)) (I : Set ι) := by
    intro i hi j hj hij
    change sampleTrace z (S i) = sampleTrace z (S j) at hij
    by_contra hne
    have havg := hnavg ⟨i, hi⟩ ⟨j, hj⟩ (by simpa using hne)
    have hsum : (∑ k ∈ Finset.range n, Y ⟨i, hi⟩ ⟨j, hj⟩ k ξ) =
        ((sampleTrace z (S i ∆ S j)).card : ℝ) := by
      rw [← Fin.sum_univ_eq_sum_range]
      change (∑ k : Fin n, if z k ∈ S i ∆ S j then (1 : ℝ) else 0) = _
      simpa only [sampleTrace] using
        (Finset.sum_boole (R := ℝ) (fun k : Fin n ↦ z k ∈ S i ∆ S j) Finset.univ)
    rw [hsum] at havg
    have hzero : (sampleTrace z (S i ∆ S j)).card = 0 := by
      rw [← sampleTrace_symmDiff_card z (S i) (S j), hij]
      simp [finsetHammingDistance]
    simp only [hzero, Nat.cast_zero, zero_div] at havg
    exact (not_lt_of_ge hδ0.le) havg
  have hcard𝒟 : 𝒟.card = I.card := by
    exact Finset.card_image_of_injOn himage
  have hsupp : ∀ A ∈ 𝒟, A ⊆ (Finset.univ : Finset (Fin n)) := by
    exact fun A _ ↦ Finset.subset_univ A
  have hVCpull := vcIndexLE_pullbackSetFamily z 𝒜 V hVC
  have hVC𝒟 : VCIndexLE (finsetSetFamily 𝒟) V := by
    intro t ht hsh
    apply hVCpull t ht
    intro q hqt
    obtain ⟨B, ⟨C, hC, rfl⟩, hB⟩ := hsh q hqt
    simp only [𝒟, Finset.mem_image] at hC
    obtain ⟨i, hi, rfl⟩ := hC
    refine ⟨z ⁻¹' S i, ⟨S i, hS i hi, rfl⟩, ?_⟩
    simpa only [coe_sampleTrace] using hB
  have hsep𝒟 : ∀ A ∈ 𝒟, ∀ B ∈ 𝒟, A ≠ B →
      δ * (Finset.univ : Finset (Fin n)).card < finsetHammingDistance A B := by
    intro A hA B hB hAB
    simp only [𝒟, Finset.mem_image] at hA hB
    obtain ⟨i, hi, rfl⟩ := hA
    obtain ⟨j, hj, rfl⟩ := hB
    have hij : i ≠ j := fun h ↦ hAB (congrArg (fun k ↦ sampleTrace z (S k)) h)
    have havg := hnavg ⟨i, hi⟩ ⟨j, hj⟩ (by simpa using hij)
    have hsum : (∑ k ∈ Finset.range n, Y ⟨i, hi⟩ ⟨j, hj⟩ k ξ) =
        ((sampleTrace z (S i ∆ S j)).card : ℝ) := by
      rw [← Fin.sum_univ_eq_sum_range]
      change (∑ k : Fin n, if z k ∈ S i ∆ S j then (1 : ℝ) else 0) = _
      simpa only [sampleTrace] using
        (Finset.sum_boole (R := ℝ) (fun k : Fin n ↦ z k ∈ S i ∆ S j) Finset.univ)
    rw [hsum] at havg
    rw [sampleTrace_symmDiff_card]
    simp only [Finset.card_univ, Fintype.card_fin]
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    exact (lt_div_iff₀ hnreal).mp havg
  rw [← hcard𝒟]
  exact finite_chazelleHaussler_packing 𝒟 Finset.univ V δ hsupp hVC𝒟 hδ0 hδ1 hsep𝒟

end

/-- One universal constant for finite `Lʳ(Q)` packings of VC-subgraph
classes.  The strict separation scale is exactly `2 * η`. -/
def IsUniversalVCFiniteLpPackingConstant (K₀ : ℝ) : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω)
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (V : ℕ)
    (Q : Measure Ω) (A : Finset (Ω → ℝ)) (r η : ℝ),
    @IsVCSubgraphClass Ω mΩ F V →
    @UniformEntropyStructural.IsEnvelope Ω F G →
    IsProbabilityMeasure Q → outerLpNorm Q G r < ⊤ →
    (∀ f ∈ A, f ∈ F) → 1 ≤ r → 0 < η → η < 1 →
    (∀ f ∈ A, ∀ g ∈ A, f ≠ g →
      ENNReal.ofReal (2 * η) * outerLpNorm Q G r <
        outerLpNorm Q (f - g) r) →
    (A.card : ℝ) ≤ K₀ * V * (16 * Real.exp 1) ^ V *
      (1 / η) ^ (r * (V - 1 : ℕ))

/-- Existence of the universal finite `Lʳ` packing constant. -/
theorem exists_universalVCFiniteLpPackingConstant :
    ∃ K₀ : ℝ, 0 < K₀ ∧ IsUniversalVCFiniteLpPackingConstant.{u} K₀ := by
  refine ⟨1, one_pos, ?_⟩
  intro Ω mΩ F G V Q A r η hVC hG hQ hGfin hA hr hη₀ hη₁ hsep
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure Q := hQ
  classical
  have hr₀ : 0 < r := lt_of_lt_of_le zero_lt_one hr
  by_cases hsmall : A.card ≤ 1
  · by_cases hAempty : A.card = 0
    · simp only [hAempty, Nat.cast_zero]
      positivity
    · have hApos : 0 < A.card := Nat.pos_of_ne_zero hAempty
      have hAone : A.card = 1 := Nat.le_antisymm hsmall hApos
      obtain ⟨f, hf⟩ := Finset.card_pos.mp hApos
      have hV : 1 ≤ V := by
        by_contra hVnot
        have hV₀ : V = 0 := Nat.eq_zero_of_not_pos hVnot
        have hsh : SetFamilyShatters (strictSubgraphFamily F) (∅ : Finset (Ω × ℝ)) := by
          intro t ht
          have ht₀ : t = ∅ := Finset.subset_empty.mp ht
          subst t
          exact ⟨strictSubgraph f, ⟨f, hA f hf, rfl⟩, by simp⟩
        exact (hVC.2 (∅ : Finset (Ω × ℝ)) (by simp [hV₀])) hsh
      have hbase : 1 ≤ 16 * Real.exp 1 := by
        have he := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
        nlinarith
      have hbasepow : 1 ≤ (16 * Real.exp 1) ^ V := one_le_pow₀ hbase
      have hηbase : 1 ≤ 1 / η := (le_div_iff₀ hη₀).2 (by simpa using hη₁.le)
      have hexp₀ : 0 ≤ r * (V - 1 : ℕ) := mul_nonneg hr₀.le (Nat.cast_nonneg _)
      have hηpow : 1 ≤ (1 / η) ^ (r * (V - 1 : ℕ)) :=
        Real.one_le_rpow hηbase hexp₀
      have hVreal : (1 : ℝ) ≤ V := by exact_mod_cast hV
      rw [hAone, Nat.cast_one]
      calc
        (1 : ℝ) ≤ (V : ℝ) := hVreal
        _ ≤ V * (16 * Real.exp 1) ^ V :=
          le_mul_of_one_le_right (Nat.cast_nonneg V) hbasepow
        _ ≤ V * (16 * Real.exp 1) ^ V *
            (1 / η) ^ (r * (V - 1 : ℕ)) :=
          le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg V) (by positivity)) hηpow
        _ = 1 * V * (16 * Real.exp 1) ^ V *
            (1 / η) ^ (r * (V - 1 : ℕ)) := by ring
  · have hcard : 1 < A.card := lt_of_not_ge hsmall
    have hAne : A.Nonempty := Finset.card_pos.mp (lt_trans Nat.zero_lt_one hcard)
    let H : Ω → ℝ := A.sup' hAne fun f x ↦ |f x|
    have hFm : ∀ f ∈ A, Measurable f := fun f hf ↦ hVC.1 f (hA f hf)
    have hHm : Measurable H := by
      dsimp only [H]
      exact Finset.measurable_sup' hAne fun f hf ↦ by
        simpa only [Real.norm_eq_abs] using (hFm f hf).norm
    have hAH : ∀ f ∈ A, ∀ x, |f x| ≤ H x := by
      intro f hf x
      exact (Finset.le_sup' (fun g x ↦ |g x|) hf) x
    have hH₀ : ∀ x, 0 ≤ H x := by
      intro x
      obtain ⟨f, hf⟩ := hAne
      exact (abs_nonneg (f x)).trans (hAH f hf x)
    have hHG : ∀ x, H x ≤ G x := by
      intro x
      exact (Finset.sup'_le hAne (fun f x ↦ |f x|)
        fun f hf x ↦ hG.2 f (hA f hf) x) x
    have hnormHG : outerLpNorm Q H r ≤ outerLpNorm Q G r := by
      apply outerLpNorm_mono_abs Q H G r hr₀
      intro x
      simpa only [abs_of_nonneg (hH₀ x), abs_of_nonneg (hG.1 x)] using hHG x
    have hHfin : outerLpNorm Q H r < ⊤ := hnormHG.trans_lt hGfin
    have hItop : (∫⁻ x, ENNReal.ofReal (H x) ^ r ∂Q) < ⊤ := by
      have hnormpow := outerLpNorm_rpow_eq_lintegral Q H r hr₀ hHm
      simp_rw [abs_of_nonneg (hH₀ _)] at hnormpow
      rw [← hnormpow]
      exact ENNReal.rpow_lt_top_of_nonneg hr₀.le hHfin.ne
    have hsepI : ∀ f ∈ A, ∀ g ∈ A, f ≠ g →
        ENNReal.ofReal (2 * η) ^ r * (∫⁻ x, ENNReal.ofReal (H x) ^ r ∂Q) <
          ∫⁻ x, ENNReal.ofReal |f x - g x| ^ r ∂Q := by
      intro f hf g hg hfg
      have hnorm : ENNReal.ofReal (2 * η) * outerLpNorm Q H r <
          outerLpNorm Q (f - g) r :=
        lt_of_le_of_lt (mul_le_mul_right hnormHG _) (hsep f hf g hg hfg)
      have hrpow := ENNReal.rpow_lt_rpow hnorm hr₀
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr₀.le,
        outerLpNorm_rpow_eq_lintegral Q H r hr₀ hHm,
        outerLpNorm_rpow_eq_lintegral Q (f - g) r hr₀ ((hFm f hf).sub (hFm g hg))]
        at hrpow
      simp_rw [abs_of_nonneg (hH₀ _)] at hrpow
      simpa only [Pi.sub_apply] using hrpow
    have hI₀ : 0 < ∫⁻ x, ENNReal.ofReal (H x) ^ r ∂Q := by
      obtain ⟨f, hf, g, hg, hfg⟩ := Finset.one_lt_card.mp hcard
      by_contra hInot
      have hIz : (∫⁻ x, ENNReal.ofReal (H x) ^ r ∂Q) = 0 :=
        nonpos_iff_eq_zero.mp (le_of_not_gt hInot)
      have hpoint : ∀ x, ENNReal.ofReal |f x - g x| ^ r ≤
          (2 : ℝ≥0∞) ^ r * ENNReal.ofReal (H x) ^ r := by
        intro x
        have hd : |f x - g x| ≤ 2 * H x := by
          calc
            |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
            _ ≤ H x + H x := add_le_add (hAH f hf x) (hAH g hg x)
            _ = 2 * H x := by ring
        calc
          ENNReal.ofReal |f x - g x| ^ r ≤ ENNReal.ofReal (2 * H x) ^ r :=
            ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hd) hr₀.le
          _ = (2 : ℝ≥0∞) ^ r * ENNReal.ofReal (H x) ^ r := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
              ENNReal.mul_rpow_of_nonneg _ _ hr₀.le]
      have hD₀ : (∫⁻ x, ENNReal.ofReal |f x - g x| ^ r ∂Q) = 0 := by
        apply nonpos_iff_eq_zero.mp
        calc
          (∫⁻ x, ENNReal.ofReal |f x - g x| ^ r ∂Q) ≤
              ∫⁻ x, (2 : ℝ≥0∞) ^ r * ENNReal.ofReal (H x) ^ r ∂Q :=
            lintegral_mono hpoint
          _ = (2 : ℝ≥0∞) ^ r *
              (∫⁻ x, ENNReal.ofReal (H x) ^ r ∂Q) := by
            simpa only [Function.comp_apply] using
              (lintegral_const_mul (μ := Q) ((2 : ℝ≥0∞) ^ r)
                (ENNReal.continuous_rpow_const.measurable.comp hHm.ennreal_ofReal))
          _ = 0 := by rw [hIz, mul_zero]
      have := hsepI f hf g hg hfg
      rw [hIz, mul_zero, hD₀] at this
      exact (lt_irrefl 0 this).elim
    have hsharp := finite_lp_packing_of_integral_separation Q A F H V r η
      hA hFm hVC.2 hHm hH₀ hAH hr hη₀ hη₁ hI₀ hItop hsepI
    have hpow : (η ^ r) ^ (-((V - 1 : ℕ) : ℝ)) =
        (1 / η) ^ (r * (V - 1 : ℕ)) := by
      rw [← Real.rpow_mul hη₀.le, one_div, ← Real.rpow_neg_eq_inv_rpow]
      congr 1
      ring
    have hsqrt : 1 ≤ Real.sqrt (Real.exp 1) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (Real.one_le_exp (by norm_num))
    have hc : 1 / (2 * Real.sqrt (Real.exp 1)) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hbase : 4 * Real.exp 1 ≤ 16 * Real.exp 1 := by
      have he := Real.exp_pos 1
      nlinarith
    calc
      (A.card : ℝ) ≤ (1 / (2 * Real.sqrt (Real.exp 1))) * V *
          (4 * Real.exp 1) ^ V * (η ^ r) ^ (-((V - 1 : ℕ) : ℝ)) := hsharp
      _ ≤ 1 * V * (16 * Real.exp 1) ^ V *
          (η ^ r) ^ (-((V - 1 : ℕ) : ℝ)) := by
        gcongr
      _ = 1 * V * (16 * Real.exp 1) ^ V *
          (1 / η) ^ (r * (V - 1 : ℕ)) := by rw [hpow]

end

end AsymptoticStatistics.EmpiricalProcess
