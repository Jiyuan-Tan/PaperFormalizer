module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedClass
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringBook

@[expose] public section

/-!
# Minimal all-probability normalized covers

This file extracts an achieving finite cover from the book-layer normalized
covering number for one probability measure.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open Filter
open scoped ENNReal NNReal Topology

/-- A finite all-probability normalized covering number with nonzero envelope
seminorm is achieved by an admissible ambient-center finite cover. -/
theorem exists_minimal_allProbabilityNormalizedL2Cover
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω)
    (F : Set (Ω → ℝ))
    (Φ : Ω → ℝ)
    (ε : ℝ)
    (hΦ : eLpNorm Φ 2 (Q : Measure Ω) ≠ 0)
    (hN : allProbabilityNormalizedL2CoveringNumber Q F Φ ε ≠ ⊤) :
    ∃ S : Finset (Ω → ℝ),
      (∀ g ∈ S,
        Measurable g ∧ MemLp g 2 (Q : Measure Ω)) ∧
      (∀ f ∈ F, ∃ g ∈ S,
        eLpNorm (f - g) 2 (Q : Measure Ω) <
          ENNReal.ofReal ε * eLpNorm Φ 2 (Q : Measure Ω)) ∧
      (S.card : ℕ∞) =
        allProbabilityNormalizedL2CoveringNumber Q F Φ ε := by
  classical
  let Covers : Finset (Ω → ℝ) → Prop := fun S =>
    (∀ g ∈ S, Measurable g ∧ MemLp g 2 (Q : Measure Ω)) ∧
      ∀ f ∈ F, ∃ g ∈ S,
        eLpNorm (f - g) 2 (Q : Measure Ω) <
          ENNReal.ofReal ε * eLpNorm Φ 2 (Q : Measure Ω)
  obtain ⟨S, hS⟩ := ENat.exists_eq_iInf
    (fun S : Finset (Ω → ℝ) => ⨅ (_ : Covers S), (S.card : ℕ∞))
  have hN_eq : allProbabilityNormalizedL2CoveringNumber Q F Φ ε =
      ⨅ S : Finset (Ω → ℝ), ⨅ (_ : Covers S), (S.card : ℕ∞) := by
    simp [allProbabilityNormalizedL2CoveringNumber, hΦ, Covers]
  have hCovers : Covers S := by
    by_contra h
    have htop : (⨅ (_ : Covers S), (S.card : ℕ∞)) = ⊤ := by
      simp [h]
    apply hN
    rw [hN_eq, ← hS, htop]
  refine ⟨S, hCovers.1, hCovers.2, ?_⟩
  rw [hN_eq, ← hS]
  simp [hCovers]

/-- A concrete admissible cover of `F` induces an admissible cover of its
difference class, with the doubled envelope and at most squared cardinality. -/
theorem exists_differenceClass_allProbabilityL2Cover
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω)
    (F : Set (Ω → ℝ))
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ)
    (ε : ℝ)
    (S : Finset (Ω → ℝ))
    (hS_center : ∀ g ∈ S,
      Measurable g ∧ MemLp g 2 (Q : Measure Ω))
    (hS_cover : ∀ f ∈ F, ∃ g ∈ S,
      eLpNorm (f - g) 2 (Q : Measure Ω) <
        ENNReal.ofReal ε * eLpNorm Φ 2 (Q : Measure Ω)) :
    ∃ T : Finset (Ω → ℝ),
      (∀ k ∈ T,
        Measurable k ∧ MemLp k 2 (Q : Measure Ω)) ∧
      (∀ h ∈ differenceClass F, ∃ k ∈ T,
        eLpNorm (h - k) 2 (Q : Measure Ω) <
          ENNReal.ofReal ε *
            eLpNorm (fun x => 2 * Φ x) 2
              (Q : Measure Ω)) ∧
      (T.card : ℕ∞) ≤ (S.card : ℕ∞) ^ 2 := by
  classical
  let centerDiff : ((Ω → ℝ) × (Ω → ℝ)) → (Ω → ℝ) :=
    fun p x => p.1 x - p.2 x
  let T := (S.product S).image centerDiff
  refine ⟨T, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hk
    have haS : a ∈ S := (Finset.mem_product.mp hab).1
    have hbS : b ∈ S := (Finset.mem_product.mp hab).2
    exact ⟨(hS_center a haS).1.sub (hS_center b hbS).1,
      (hS_center a haS).2.sub (hS_center b hbS).2⟩
  · rintro h ⟨f, g, hf, hg, rfl⟩
    obtain ⟨a, haS, hfa⟩ := hS_cover f hf
    obtain ⟨b, hbS, hgb⟩ := hS_cover g hg
    refine ⟨centerDiff (a, b), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨haS, hbS⟩, rfl⟩
    · have hfa_meas : AEStronglyMeasurable (f - a) (Q : Measure Ω) :=
        ((hF_meas f hf).sub (hS_center a haS).1).aestronglyMeasurable
      have hgb_meas : AEStronglyMeasurable (g - b) (Q : Measure Ω) :=
        ((hF_meas g hg).sub (hS_center b hbS).1).aestronglyMeasurable
      have htriangle :
          eLpNorm ((f - g) - centerDiff (a, b)) 2 (Q : Measure Ω) ≤
            eLpNorm (f - a) 2 (Q : Measure Ω) +
              eLpNorm (g - b) 2 (Q : Measure Ω) := by
        rw [show (f - g) - centerDiff (a, b) = (f - a) - (g - b) by
          funext x
          simp [centerDiff]
          ring]
        exact MeasureTheory.eLpNorm_sub_le hfa_meas hgb_meas (by norm_num)
      refine lt_of_le_of_lt htriangle ?_
      calc
        eLpNorm (f - a) 2 (Q : Measure Ω) +
              eLpNorm (g - b) 2 (Q : Measure Ω) <
            (ENNReal.ofReal ε * eLpNorm Φ 2 (Q : Measure Ω)) +
              (ENNReal.ofReal ε * eLpNorm Φ 2 (Q : Measure Ω)) :=
          ENNReal.add_lt_add hfa hgb
        _ = ENNReal.ofReal ε *
              eLpNorm (fun x => 2 * Φ x) 2 (Q : Measure Ω) := by
          rw [show (fun x => 2 * Φ x) = (2 : ℝ) • Φ by
            funext x
            simp]
          rw [MeasureTheory.eLpNorm_const_smul]
          have htwo : ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) := by
            norm_num [Real.enorm_eq_ofReal_abs]
          rw [htwo]
          ring
  · calc
      (T.card : ℕ∞) ≤ ((S.product S).card : ℕ∞) := by
        exact_mod_cast Finset.card_image_le
      _ = (S.card : ℕ∞) ^ 2 := by
        rw [show (S.product S).card = S.card * S.card from
          Finset.card_product S S]
        norm_num [pow_two]

/-- The normalized all-probability covering number of the difference class,
with doubled envelope, is at most the square of the original covering number. -/
theorem allProbabilityNormalizedL2CoveringNumber_differenceClass_le_sq
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω)
    (F : Set (Ω → ℝ))
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ)
    (ε : ℝ) :
    allProbabilityNormalizedL2CoveringNumber Q
        (differenceClass F) (fun x => 2 * Φ x) ε ≤
      (allProbabilityNormalizedL2CoveringNumber Q F Φ ε) ^ 2 := by
  classical
  have hnorm_two :
      eLpNorm (fun x => 2 * Φ x) 2 (Q : Measure Ω) =
        (2 : ℝ≥0∞) * eLpNorm Φ 2 (Q : Measure Ω) := by
    rw [show (fun x => 2 * Φ x) = (2 : ℝ) • Φ by
      funext x
      simp]
    rw [MeasureTheory.eLpNorm_const_smul]
    norm_num [Real.enorm_eq_ofReal_abs]
  by_cases hΦ : eLpNorm Φ 2 (Q : Measure Ω) = 0
  · have htwoΦ : eLpNorm (fun x => 2 * Φ x) 2 (Q : Measure Ω) = 0 := by
      rw [hnorm_two, hΦ]
      simp
    simp [allProbabilityNormalizedL2CoveringNumber, hΦ, htwoΦ]
  · have htwoΦ : eLpNorm (fun x => 2 * Φ x) 2 (Q : Measure Ω) ≠ 0 := by
      rw [hnorm_two]
      simp [hΦ]
    by_cases hN : allProbabilityNormalizedL2CoveringNumber Q F Φ ε = ⊤
    · simp [hN]
    · obtain ⟨S, hS_center, hS_cover, hScard⟩ :=
        exists_minimal_allProbabilityNormalizedL2Cover Q F Φ ε hΦ hN
      obtain ⟨T, hT_center, hT_cover, hTcard⟩ :=
        exists_differenceClass_allProbabilityL2Cover
          Q F hF_meas Φ ε S hS_center hS_cover
      have hcover :
          allProbabilityNormalizedL2CoveringNumber Q
              (differenceClass F) (fun x => 2 * Φ x) ε ≤
            (T.card : ℕ∞) := by
        rw [allProbabilityNormalizedL2CoveringNumber, if_neg htwoΦ]
        exact iInf_le_of_le T
          (iInf_le_of_le ⟨hT_center, hT_cover⟩ le_rfl)
      calc
        allProbabilityNormalizedL2CoveringNumber Q
              (differenceClass F) (fun x => 2 * Φ x) ε ≤
            (T.card : ℕ∞) := hcover
        _ ≤ (S.card : ℕ∞) ^ 2 := hTcard
        _ = (allProbabilityNormalizedL2CoveringNumber Q F Φ ε) ^ 2 := by
          rw [hScard]

/-- The uniform all-probability covering number of the difference class,
with doubled envelope, is at most the square of the original uniform number. -/
theorem allProbabilityUniformL2CoveringNumber_differenceClass_le_sq
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Set (Ω → ℝ))
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ)
    (ε : ℝ) :
    allProbabilityUniformL2CoveringNumber
        (differenceClass F) (fun x => 2 * Φ x) ε ≤
      (allProbabilityUniformL2CoveringNumber F Φ ε) ^ 2 := by
  unfold allProbabilityUniformL2CoveringNumber
  refine iSup_le fun Q => ?_
  exact
    (allProbabilityNormalizedL2CoveringNumber_differenceClass_le_sq
      Q F hF_meas Φ ε).trans
      (pow_le_pow_left₀ bot_le
        (le_iSup (fun Q' : ProbabilityMeasure Ω =>
          allProbabilityNormalizedL2CoveringNumber Q' F Φ ε) Q) 2)

/-- Normalized all-probability covering numbers are monotone in the class. -/
theorem allProbabilityNormalizedL2CoveringNumber_mono_class
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) {F G : Set (Ω → ℝ)}
    (hFG : F ⊆ G) (Φ : Ω → ℝ) (ε : ℝ) :
    allProbabilityNormalizedL2CoveringNumber Q F Φ ε ≤
      allProbabilityNormalizedL2CoveringNumber Q G Φ ε := by
  by_cases hΦ : eLpNorm Φ 2 (Q : Measure Ω) = 0
  · simp [allProbabilityNormalizedL2CoveringNumber, hΦ]
  unfold allProbabilityNormalizedL2CoveringNumber
  rw [if_neg hΦ, if_neg hΦ]
  refine iInf_mono fun S => iInf_mono' fun hSG => ?_
  exact ⟨⟨hSG.1, fun f hf => hSG.2 f (hFG hf)⟩, le_rfl⟩

/-- Uniform all-probability covering numbers are monotone in the class. -/
theorem allProbabilityUniformL2CoveringNumber_mono_class
    {Ω : Type*} [MeasurableSpace Ω] {F G : Set (Ω → ℝ)}
    (hFG : F ⊆ G) (Φ : Ω → ℝ) (ε : ℝ) :
    allProbabilityUniformL2CoveringNumber F Φ ε ≤
      allProbabilityUniformL2CoveringNumber G Φ ε := by
  unfold allProbabilityUniformL2CoveringNumber
  exact iSup_mono fun Q =>
    allProbabilityNormalizedL2CoveringNumber_mono_class Q hFG Φ ε

/-- Book uniform covering entropy integrals are monotone in the class. -/
theorem bookUniformCoveringEntropyIntegral_mono_class
    {Ω : Type*} [MeasurableSpace Ω] {F G : Set (Ω → ℝ)}
    (hFG : F ⊆ G) (Φ : Ω → ℝ) (δ : ℝ) :
    bookUniformCoveringEntropyIntegral δ F Φ ≤
      bookUniformCoveringEntropyIntegral δ G Φ := by
  unfold bookUniformCoveringEntropyIntegral
  exact lintegral_mono fun ε => bookEntropyWeight_mono
    (allProbabilityUniformL2CoveringNumber_mono_class hFG Φ ε)

/-- Squaring an extended covering number costs at most a factor `sqrt 2` in
the book entropy weight. -/
theorem bookEntropyWeight_sq_le (N : ℕ∞) :
    bookEntropyWeight (N ^ 2) ≤
      ENNReal.ofReal (Real.sqrt 2) * bookEntropyWeight N := by
  rcases eq_or_ne N ⊤ with rfl | hN
  · simp [bookEntropyWeight]
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hN
  by_cases hn : n = 0
  · subst n
    simp
  rw [show (n : ℕ∞) ^ 2 = (n ^ 2 : ℕ) by norm_num]
  rw [bookEntropyWeight_coe, bookEntropyWeight_coe,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
  apply ENNReal.ofReal_le_ofReal
  rw [Nat.cast_pow, Real.log_pow]
  norm_num

/-- Passing to the difference class costs at most a factor `sqrt 2` in the
book uniform covering entropy integral. -/
theorem bookUniformCoveringEntropyIntegral_differenceClass_le_sqrtTwo_mul
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Set (Ω → ℝ))
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (δ : ℝ) :
    bookUniformCoveringEntropyIntegral δ
        (differenceClass F) (fun x => 2 * Φ x) ≤
      ENNReal.ofReal (Real.sqrt 2) *
        bookUniformCoveringEntropyIntegral δ F Φ := by
  unfold bookUniformCoveringEntropyIntegral
  calc
    (∫⁻ ε in Set.Ioc 0 δ,
        bookEntropyWeight
          (allProbabilityUniformL2CoveringNumber
            (differenceClass F) (fun x => 2 * Φ x) ε) ∂volume) ≤
        ∫⁻ ε in Set.Ioc 0 δ,
          ENNReal.ofReal (Real.sqrt 2) *
            bookEntropyWeight
              (allProbabilityUniformL2CoveringNumber F Φ ε) ∂volume := by
      refine lintegral_mono fun ε => ?_
      exact (bookEntropyWeight_mono
        (allProbabilityUniformL2CoveringNumber_differenceClass_le_sq
          F hF_meas Φ ε)).trans (bookEntropyWeight_sq_le _)
    _ = ENNReal.ofReal (Real.sqrt 2) *
        ∫⁻ ε in Set.Ioc 0 δ,
          bookEntropyWeight
            (allProbabilityUniformL2CoveringNumber F Φ ε) ∂volume := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Difference-class book entropy integrals tend to zero whenever the
original class integrals do. -/
theorem tendsto_bookUniformCoveringEntropyIntegral_differenceClass_zero
    {Ω ι : Type*} [MeasurableSpace Ω]
    {l : Filter ι}
    (F : ι → Set (Ω → ℝ))
    (hF_meas : ∀ i f, f ∈ F i → Measurable f)
    (Φ : ι → Ω → ℝ)
    (δ : ι → ℝ)
    (hJ : Tendsto
      (fun i => bookUniformCoveringEntropyIntegral (δ i) (F i) (Φ i))
      l (𝓝 0)) :
    Tendsto
      (fun i => bookUniformCoveringEntropyIntegral
        (δ i) (differenceClass (F i)) (fun x => 2 * Φ i x))
      l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (by
      have hscaled := ENNReal.Tendsto.const_mul hJ
        (Or.inr (ENNReal.ofReal_ne_top (r := Real.sqrt 2)))
      simpa using hscaled)
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun i =>
      bookUniformCoveringEntropyIntegral_differenceClass_le_sqrtTwo_mul
        (F i) (hF_meas i) (Φ i) (δ i))

end AsymptoticStatistics.EmpiricalProcess
