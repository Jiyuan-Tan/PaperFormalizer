module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedRelativeRadius
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringRademacherContraction
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringSymmetrization

@[expose] public section

/-!
# Empirical square-radius tails

Elementary pointwise and measurability facts for splitting a square into its
clipped part and the remaining envelope-controlled tail.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The part of `f²` left after clipping at squared radius `K²`.

Edge behavior: the threshold depends on `K` only through `K²`, so negative
radii agree with their absolute values and radius zero leaves the whole square.
-/
def squareTail {Ω : Type*} (K : ℝ) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => f x ^ 2 - clippedSquare K (f x)

/-- The square-envelope tail above the strict absolute threshold `|K|`.

Edge behavior: equality at the threshold is excluded; negative `K` has the
same threshold as `|K|`, and a negative envelope value can never enter the
tail unless its absolute value exceeds `|K|`.
-/
def squareTailEnvelope {Ω : Type*} (K : ℝ) (Φ : Ω → ℝ) : Ω → ℝ :=
  fun x => if |K| < |Φ x| then Φ x ^ 2 else 0

/-- The largest empirical second moment over a function class. -/
noncomputable def empiricalSquareRadius {Ω : Type*} [MeasurableSpace Ω]
    (F : Set (Ω → ℝ)) (n : ℕ) (X : Fin n → Ω) : ℝ≥0∞ :=
  ⨆ f ∈ F, ENNReal.ofReal (empiricalAvg (fun x => f x ^ 2) n X)

/-- The largest population second moment over a function class. -/
noncomputable def populationSquareRadius {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Set (Ω → ℝ)) : ℝ≥0∞ :=
  ⨆ f ∈ F, ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P

@[simp] theorem empiricalSquareRadius_zero {Ω : Type*} [MeasurableSpace Ω]
    (F : Set (Ω → ℝ)) (X : Fin 0 → Ω) : empiricalSquareRadius F 0 X = 0 := by
  simp [empiricalSquareRadius]

@[simp] theorem empiricalSquareRadius_empty {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (X : Fin n → Ω) : empiricalSquareRadius (∅ : Set (Ω → ℝ)) n X = 0 := by
  simp [empiricalSquareRadius]

@[simp] theorem populationSquareRadius_empty {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) : populationSquareRadius P (∅ : Set (Ω → ℝ)) = 0 := by
  simp [populationSquareRadius]

theorem sq_eq_clippedSquare_add_squareTail {Ω : Type*} (K : ℝ) (f : Ω → ℝ) (x : Ω) :
    f x ^ 2 = clippedSquare K (f x) + squareTail K f x := by
  simp [squareTail]

theorem squareTail_nonneg {Ω : Type*} (K : ℝ) (f : Ω → ℝ) (x : Ω) :
    0 ≤ squareTail K f x := by
  exact sub_nonneg.mpr (min_le_left _ _)

theorem squareTail_le_sq {Ω : Type*} (K : ℝ) (f : Ω → ℝ) (x : Ω) :
    squareTail K f x ≤ f x ^ 2 := by
  apply sub_le_self
  exact le_min (sq_nonneg _) (sq_nonneg _)

theorem squareTailEnvelope_nonneg {Ω : Type*} (K : ℝ) (Φ : Ω → ℝ) (x : Ω) :
    0 ≤ squareTailEnvelope K Φ x := by
  simp only [squareTailEnvelope]
  split <;> positivity

theorem squareTailEnvelope_two_mul_eq
    {Ω : Type*}
    (K : ℝ) (hK : 0 ≤ K)
    (Φ : Ω → ℝ) (x : Ω) :
    squareTailEnvelope K (fun y => 2 * Φ y) x =
      if K < 2 * |Φ x| then 4 * Φ x ^ 2 else 0 := by
  unfold squareTailEnvelope
  rw [abs_of_nonneg hK, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  split_ifs <;> ring

theorem lintegral_squareTailEnvelope_two_mul_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (K : ℝ) (hK : 0 ≤ K)
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ) :
    (∫⁻ x, ENNReal.ofReal
      (squareTailEnvelope K (fun y => 2 * Φ y) x) ∂P) =
      4 * ∫⁻ x in {x | K < 2 * |Φ x|},
        ENNReal.ofReal (Φ x ^ 2) ∂P := by
  let A : Set Ω := {x | K < 2 * |Φ x|}
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const (measurable_const.mul hΦ_meas.abs)
  have hpoint (x : Ω) :
      ENNReal.ofReal (squareTailEnvelope K (fun y => 2 * Φ y) x) =
        A.indicator (fun y => 4 * ENNReal.ofReal (Φ y ^ 2)) x := by
    rw [squareTailEnvelope_two_mul_eq K hK Φ x]
    by_cases hx : K < 2 * |Φ x|
    · rw [if_pos hx, Set.indicator_of_mem (show x ∈ A from hx)]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    · rw [if_neg hx, Set.indicator_of_notMem (show x ∉ A from hx)]
      simp
  calc
    (∫⁻ x, ENNReal.ofReal
        (squareTailEnvelope K (fun y => 2 * Φ y) x) ∂P) =
        ∫⁻ x, A.indicator
          (fun y => 4 * ENNReal.ofReal (Φ y ^ 2)) x ∂P :=
      lintegral_congr hpoint
    _ = ∫⁻ x in A, 4 * ENNReal.ofReal (Φ x ^ 2) ∂P :=
      lintegral_indicator hA (fun y => 4 * ENNReal.ofReal (Φ y ^ 2))
    _ = 4 * ∫⁻ x in A, ENNReal.ofReal (Φ x ^ 2) ∂P := by
      rw [lintegral_const_mul' 4 _ (by norm_num)]
    _ = 4 * ∫⁻ x in {x | K < 2 * |Φ x|},
          ENNReal.ofReal (Φ x ^ 2) ∂P := rfl

theorem squareTail_le_squareTailEnvelope
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    (hΦ : IsEnvelope F Φ) {f : Ω → ℝ} (hf : f ∈ F)
    (K : ℝ) (x : Ω) :
    squareTail K f x ≤ squareTailEnvelope K Φ x := by
  have hfΦ : |f x| ≤ Φ x := hΦ f hf x
  by_cases hKΦ : |K| < |Φ x|
  · rw [squareTailEnvelope]
    simp only [if_pos hKΦ]
    refine (squareTail_le_sq K f x).trans ?_
    exact sq_le_sq.mpr (hfΦ.trans (le_abs_self _))
  · have hfk : |f x| ≤ |K| :=
      hfΦ.trans ((le_abs_self _).trans (le_of_not_gt hKΦ))
    have hsq : f x ^ 2 ≤ K ^ 2 := sq_le_sq.mpr hfk
    simp [squareTailEnvelope, hKΦ, squareTail, clippedSquare, min_eq_left hsq]

theorem measurable_squareTail {Ω : Type*} [MeasurableSpace Ω]
    (K : ℝ) {f : Ω → ℝ} (hf : Measurable f) : Measurable (squareTail K f) := by
  exact (hf.pow_const 2).sub ((hf.pow_const 2).min measurable_const)

theorem measurable_squareTailEnvelope {Ω : Type*} [MeasurableSpace Ω]
    (K : ℝ) {Φ : Ω → ℝ} (hΦ : Measurable Φ) : Measurable (squareTailEnvelope K Φ) := by
  exact Measurable.ite (measurableSet_lt measurable_const hΦ.abs)
    (hΦ.pow_const 2) measurable_const

/-- Pointwise density is preserved by applying the clipped-square map. -/
theorem EmpProcPointwiseDense_image_clippedSquare
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set (Ω → ℝ)}
    (hDense : EmpProcPointwiseDense F P) (K : ℝ) :
    EmpProcPointwiseDense
      ((fun f : Ω → ℝ => fun x => clippedSquare K (f x)) '' F) P := by
  obtain ⟨F', hF'sub, hF'ct, hApprox, Φ, hΦint, hΦdom⟩ := hDense
  refine ⟨(fun f : Ω → ℝ => fun x => clippedSquare K (f x)) '' F', ?_,
    hF'ct.image _, ?_, fun x => (2 * |K|) * Φ x, hΦint.const_mul _, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨f, hF'sub hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨φ, hφmem, hφlim⟩ := hApprox f hf
    refine ⟨fun m x => clippedSquare K (φ m x), ?_, ?_⟩
    · intro m
      exact ⟨φ m, hφmem m, rfl⟩
    · intro x
      simpa only [clippedSquare] using!
        (((continuous_id.pow 2).min continuous_const).tendsto (f x)).comp (hφlim x)
  · rintro _ ⟨f, hf, rfl⟩ x
    calc
      |clippedSquare K (f x)| = |clippedSquare K (f x) - clippedSquare K 0| := by
        rw [clippedSquare_zero, sub_zero]
      _ ≤ (2 * |K|) * |f x - 0| := clippedSquare_lipschitz K (f x) 0
      _ ≤ (2 * |K|) * Φ x := by
        simpa using mul_le_mul_of_nonneg_left (hΦdom f hf x) (by positivity)

/-- The canonical expected empirical average of a nonnegative measurable
function is bounded by its population `lintegral`. -/
theorem lintegral_canonical_empiricalAvg_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Ψ : Ω → ℝ) (hΨ_meas : Measurable Ψ)
    (hΨ_nonneg : ∀ x, 0 ≤ Ψ x) (n : ℕ) :
    (∫⁻ X : Fin n → Ω,
      ENNReal.ofReal (empiricalAvg Ψ n X)
      ∂Measure.pi (fun _ : Fin n => P)) ≤
      ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
  cases n with
  | zero => simp
  | succ k =>
      let ν : Measure (Fin (k + 1) → Ω) :=
        Measure.pi (fun _ : Fin (k + 1) => P)
      calc
        (∫⁻ X : Fin (k + 1) → Ω,
          ENNReal.ofReal (empiricalAvg Ψ (k + 1) X) ∂ν) =
            ∫⁻ X : Fin (k + 1) → Ω,
              ENNReal.ofReal ((k + 1 : ℝ)⁻¹) *
                ∑ i : Fin (k + 1), ENNReal.ofReal (Ψ (X i)) ∂ν := by
          congr 1
          funext X
          rw [empiricalAvg,
            show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by norm_num,
            ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity)),
            ENNReal.ofReal_sum_of_nonneg]
          exact fun i hi => hΨ_nonneg (X i)
        _ = ENNReal.ofReal ((k + 1 : ℝ)⁻¹) *
            ∑ i : Fin (k + 1),
              ∫⁻ X, ENNReal.ofReal (Ψ (X i)) ∂ν := by
          rw [lintegral_const_mul]
          · rw [lintegral_finset_sum]
            intro i hi
            exact (hΨ_meas.comp (measurable_pi_apply i)).ennreal_ofReal
          · exact Finset.measurable_sum Finset.univ fun i _ =>
              (hΨ_meas.comp (measurable_pi_apply i)).ennreal_ofReal
        _ = ENNReal.ofReal ((k + 1 : ℝ)⁻¹) *
            ∑ i : Fin (k + 1), ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
          congr 2 with i
          exact (measurePreserving_eval
            (fun _ : Fin (k + 1) => P) i).lintegral_comp
              hΨ_meas.ennreal_ofReal
        _ = ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            ENNReal.ofReal_inv_of_pos (by positivity)]
          simp only [nsmul_eq_mul]
          rw [show ENNReal.ofReal ((k : ℝ) + 1) =
              (k : ℝ≥0∞) + 1 by
                rw [ENNReal.ofReal_add (by positivity) (by positivity)]
                simp,
            show ((k + 1 : ℕ) : ℝ≥0∞) = (k : ℝ≥0∞) + 1 by norm_num,
            ← mul_assoc, ENNReal.inv_mul_cancel]
          · simp
          · positivity
          · finiteness
        _ ≤ ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := le_rfl

/-- Canonical clipped-square empirical processes are controlled by the
conditional Rademacher average of the original class. -/
theorem lintegral_canonical_clippedSquareProcess_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (K : ℝ) (hK : 0 ≤ K) (n : ℕ) :
    (∫⁻ x : Fin n → Ω,
      supNormOver
        ((fun f : Ω → ℝ => fun y => clippedSquare K (f y)) '' F)
        (empiricalProcess P n x)
        ∂Measure.pi (fun _ : Fin n => P)) ≤
      ENNReal.ofReal (8 * K) *
        ∫⁻ x : Fin n → Ω, conditionalRademacherSup F n x
          ∂Measure.pi (fun _ : Fin n => P) := by
  let Fclip : Set (Ω → ℝ) :=
    (fun f : Ω → ℝ => fun y => clippedSquare K (f y)) '' F
  have hClipDense : EmpProcPointwiseDense Fclip P := by
    exact EmpProcPointwiseDense_image_clippedSquare hDense K
  have hClipMeas : ∀ g ∈ Fclip, Measurable g := by
    rintro g ⟨f, hf, rfl⟩
    exact (hF_meas f hf).pow_const 2 |>.min measurable_const
  calc
    (∫⁻ x : Fin n → Ω,
      supNormOver Fclip (empiricalProcess P n x)
        ∂Measure.pi (fun _ : Fin n => P)) ≤
        2 * ∫⁻ x : Fin n → Ω, conditionalRademacherSup Fclip n x
          ∂Measure.pi (fun _ : Fin n => P) :=
      canonical_symmetrization_empiricalProcess P Fclip hClipDense hClipMeas n
    _ ≤ 2 * ∫⁻ x : Fin n → Ω,
          ENNReal.ofReal (4 * K) * conditionalRademacherSup F n x
          ∂Measure.pi (fun _ : Fin n => P) := by
      gcongr with x
      exact conditionalRademacherSup_image_clippedSquare_le F n x K hK
    _ = 2 * (ENNReal.ofReal (4 * K) *
          ∫⁻ x : Fin n → Ω, conditionalRademacherSup F n x
            ∂Measure.pi (fun _ : Fin n => P)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (8 * K) *
          ∫⁻ x : Fin n → Ω, conditionalRademacherSup F n x
            ∂Measure.pi (fun _ : Fin n => P) := by
      have hconst : (2 : ℝ≥0∞) * ENNReal.ofReal (4 * K) =
          ENNReal.ofReal (8 * K) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring_nf
      rw [← mul_assoc, hconst]

theorem empiricalSquareRadius_le_population_add_clippedProcess_add_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (hΦ : IsEnvelope F Φ)
    (K : ℝ) (n : ℕ) (X : Fin n → Ω) :
    empiricalSquareRadius F n X ≤
      populationSquareRadius P F +
        ENNReal.ofReal ((Real.sqrt n)⁻¹) *
          supNormOver ((fun f : Ω → ℝ => fun x => clippedSquare K (f x)) '' F)
            (empiricalProcess P n X) +
        ENNReal.ofReal (empiricalAvg (squareTailEnvelope K Φ) n X) := by
  classical
  cases n with
  | zero => simp
  | succ m =>
      unfold empiricalSquareRadius
      refine iSup_le fun f => iSup_le fun hf => ?_
      let g : Ω → ℝ := fun x => clippedSquare K (f x)
      let t : Ω → ℝ := squareTail K f
      have hsqrt : Real.sqrt (m + 1) ≠ 0 := by positivity
      have hsqrt_nonneg : 0 ≤ Real.sqrt (m + 1) := Real.sqrt_nonneg _
      have havg_decomp :
          empiricalAvg (fun x => f x ^ 2) (m + 1) X =
            empiricalAvg g (m + 1) X + empiricalAvg t (m + 1) X := by
        rw [← empiricalAvg_add]
        congr 1
        funext x
        exact sq_eq_clippedSquare_add_squareTail K f x
      have havg_g :
          empiricalAvg g (m + 1) X =
            ∫ x, g x ∂P + (Real.sqrt (m + 1))⁻¹ *
              empiricalProcess P (m + 1) X g := by
        unfold empiricalProcess
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        ring
      have ht_le : empiricalAvg t (m + 1) X ≤
          empiricalAvg (squareTailEnvelope K Φ) (m + 1) X := by
        unfold empiricalAvg
        gcongr with i
        exact squareTail_le_squareTailEnvelope hΦ hf K (X i)
      have hreal : empiricalAvg (fun x => f x ^ 2) (m + 1) X ≤
          ∫ x, g x ∂P + (Real.sqrt (m + 1))⁻¹ *
              |empiricalProcess P (m + 1) X g| +
            empiricalAvg (squareTailEnvelope K Φ) (m + 1) X := by
        rw [havg_decomp, havg_g]
        gcongr
        exact le_abs_self _
      calc
        ENNReal.ofReal (empiricalAvg (fun x => f x ^ 2) (m + 1) X) ≤
            ENNReal.ofReal
              ((∫ x, g x ∂P) + (Real.sqrt (m + 1))⁻¹ *
                |empiricalProcess P (m + 1) X g| +
                empiricalAvg (squareTailEnvelope K Φ) (m + 1) X) :=
          ENNReal.ofReal_le_ofReal hreal
        _ ≤ ENNReal.ofReal (∫ x, g x ∂P) +
              ENNReal.ofReal ((Real.sqrt (m + 1))⁻¹ *
                |empiricalProcess P (m + 1) X g|) +
              ENNReal.ofReal (empiricalAvg (squareTailEnvelope K Φ) (m + 1) X) := by
          refine (ENNReal.ofReal_add_le).trans ?_
          gcongr
          exact ENNReal.ofReal_add_le
        _ = ENNReal.ofReal (∫ x, g x ∂P) +
              ENNReal.ofReal ((Real.sqrt (m + 1))⁻¹) *
                ENNReal.ofReal |empiricalProcess P (m + 1) X g| +
              ENNReal.ofReal (empiricalAvg (squareTailEnvelope K Φ) (m + 1) X) := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr hsqrt_nonneg)]
        _ ≤ populationSquareRadius P F +
              ENNReal.ofReal ((Real.sqrt (m + 1))⁻¹) *
                supNormOver
                  ((fun f : Ω → ℝ => fun x => clippedSquare K (f x)) '' F)
                  (empiricalProcess P (m + 1) X) +
              ENNReal.ofReal (empiricalAvg (squareTailEnvelope K Φ) (m + 1) X) := by
          gcongr
          · refine (show ENNReal.ofReal (∫ x, g x ∂P) ≤ _ from ?_).trans
              (le_iSup₂ f hf)
            calc
              ENNReal.ofReal (∫ x, g x ∂P) ≤ ‖∫ x, g x ∂P‖ₑ := by
                rw [Real.enorm_eq_ofReal_abs]
                exact ENNReal.ofReal_le_ofReal (le_abs_self _)
              _ ≤ ∫⁻ x, ‖g x‖ₑ ∂P := enorm_integral_le_lintegral_enorm g
              _ ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P := by
                apply lintegral_mono
                intro x
                simp only [g, Real.enorm_eq_ofReal_abs]
                rw [abs_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
                exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
          · refine le_supNormOver (f := g) ?_
            exact ⟨f, hf, rfl⟩
        _ = populationSquareRadius P F +
              ENNReal.ofReal ((Real.sqrt (Nat.succ m))⁻¹) *
                supNormOver
                  ((fun f : Ω → ℝ => fun x => clippedSquare K (f x)) '' F)
                  (empiricalProcess P (Nat.succ m) X) +
              ENNReal.ofReal (empiricalAvg (squareTailEnvelope K Φ) (Nat.succ m) X) := by
          norm_num [Nat.cast_add, Nat.cast_one]

/-- The canonical expected empirical square radius is bounded by its
population radius, a clipped Rademacher term, and the envelope tail. -/
theorem lintegral_canonical_empiricalSquareRadius_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ)
    (K : ℝ) (hK : 0 ≤ K) (n : ℕ) :
    (∫⁻ X : Fin n → Ω, empiricalSquareRadius F n X
      ∂Measure.pi (fun _ : Fin n => P)) ≤
      populationSquareRadius P F +
        ENNReal.ofReal (8 * K * (Real.sqrt n)⁻¹) *
          ∫⁻ X : Fin n → Ω,
            conditionalRademacherSup F n X
            ∂Measure.pi (fun _ : Fin n => P) +
        ∫⁻ x, ENNReal.ofReal (squareTailEnvelope K Φ x) ∂P := by
  let ν : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => P)
  let Fclip : Set (Ω → ℝ) :=
    (fun f : Ω → ℝ => fun x => clippedSquare K (f x)) '' F
  let A : ℝ≥0∞ := populationSquareRadius P F
  let c : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt n)⁻¹)
  let S : (Fin n → Ω) → ℝ≥0∞ := fun X =>
    supNormOver Fclip (empiricalProcess P n X)
  let T : (Fin n → Ω) → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (empiricalAvg (squareTailEnvelope K Φ) n X)
  let I : ℝ≥0∞ := ∫⁻ X : Fin n → Ω,
    conditionalRademacherSup F n X ∂ν
  let Tail : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (squareTailEnvelope K Φ x) ∂P
  have hClipDense : EmpProcPointwiseDense Fclip P := by
    exact EmpProcPointwiseDense_image_clippedSquare hDense K
  have hClipMeas : ∀ g ∈ Fclip, Measurable g := by
    rintro g ⟨f, hf, rfl⟩
    exact (hF_meas f hf).pow_const 2 |>.min measurable_const
  have hS_meas : Measurable S := by
    exact measurable_canonicalEmpiricalProcessSup_dense
      P Fclip hClipDense hClipMeas n
  have hleft_meas : Measurable (fun X => A + c * S X) :=
    measurable_const.add (measurable_const.mul hS_meas)
  have hpoint (X : Fin n → Ω) :
      empiricalSquareRadius F n X ≤ A + c * S X + T X := by
    simpa only [A, c, S, T, Fclip] using
      empiricalSquareRadius_le_population_add_clippedProcess_add_tail
        P F Φ hΦ K n X
  have hsplit :
      (∫⁻ X, A + c * S X + T X ∂ν) =
        A + c * (∫⁻ X, S X ∂ν) + ∫⁻ X, T X ∂ν := by
    rw [lintegral_add_left' hleft_meas.aemeasurable,
      lintegral_add_left' measurable_const.aemeasurable,
      lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' c S ENNReal.ofReal_ne_top]
  have hclip :
      (∫⁻ X, S X ∂ν) ≤ ENNReal.ofReal (8 * K) * I := by
    simpa only [S, Fclip, I, ν] using
      lintegral_canonical_clippedSquareProcess_le
        P F hDense hF_meas K hK n
  have htail : (∫⁻ X, T X ∂ν) ≤ Tail := by
    simpa only [T, Tail, ν] using
      lintegral_canonical_empiricalAvg_le P (squareTailEnvelope K Φ)
        (measurable_squareTailEnvelope K hΦ_meas)
        (squareTailEnvelope_nonneg K Φ) n
  calc
    (∫⁻ X : Fin n → Ω, empiricalSquareRadius F n X ∂ν) ≤
        ∫⁻ X, A + c * S X + T X ∂ν := lintegral_mono hpoint
    _ = A + c * (∫⁻ X, S X ∂ν) + ∫⁻ X, T X ∂ν := hsplit
    _ ≤ A + c * (ENNReal.ofReal (8 * K) * I) + Tail :=
      add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hclip (zero_le (a := c))))
        htail
    _ = populationSquareRadius P F +
          ENNReal.ofReal (8 * K * (Real.sqrt n)⁻¹) *
            (∫⁻ X : Fin n → Ω, conditionalRademacherSup F n X ∂ν) +
          ∫⁻ x, ENNReal.ofReal (squareTailEnvelope K Φ x) ∂P := by
      dsimp only [A, c, I, Tail]
      rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hK)]
      ring

end

end AsymptoticStatistics.EmpiricalProcess
