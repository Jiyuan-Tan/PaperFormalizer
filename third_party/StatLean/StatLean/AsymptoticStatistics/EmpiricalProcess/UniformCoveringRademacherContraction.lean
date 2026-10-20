module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringRademacher
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.RademacherClippedSquare
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Order.CompleteLattice.Finset

@[expose] public section

/-!
# Clipped-square contraction for normalized Rademacher averages

This file transports the raw Rademacher contraction inequality through the
common empirical-process normalization.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory

set_option linter.unusedFintypeInType false in
theorem integral_iSup_abs_rademacherAverage_clippedSquare_le
    {Ω ι : Type*} [Fintype ι]
    (n : ℕ) (X : Fin n → Ω) (u : ι → Ω → ℝ)
    (K : ℝ) (hK : 0 ≤ K) :
    ∫ ε, ⨆ j, |rademacherAverage n X ε (fun x => clippedSquare K (u j x))|
      ∂rademacherCube n ≤
      4*K * ∫ ε, ⨆ j, |rademacherAverage n X ε (u j)| ∂rademacherCube n := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI : IsEmpty ι := hι
      simp
  | inr hι =>
      letI : Nonempty ι := hι
      cases n with
      | zero => simp
      | succ m =>
          let c : ℝ := (Real.sqrt (m + 1))⁻¹
          have hc : 0 ≤ c := inv_nonneg.mpr (Real.sqrt_nonneg _)
          have haverage (v : ι → Ω → ℝ) (ε : Fin (m + 1) → Bool) (j : ι) :
              rademacherAverage (m + 1) X ε (v j) =
                c * rademacherSum (fun k => v j (X k)) ε := by
            simp [rademacherAverage, rademacherSum, c, mul_comm]
          have hscale (b : ι → ℝ) :
              (⨆ j, |c * b j|) = c * (⨆ j, |b j|) := by
            simp_rw [abs_mul, abs_of_nonneg hc]
            obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i => |b i|)
            rw [← hj]
            apply le_antisymm
            · apply ciSup_le
              intro i
              apply mul_le_mul_of_nonneg_left _ hc
              rw [hj]
              exact le_ciSup (Set.finite_range (fun q => |b q|)).bddAbove i
            · exact le_ciSup
                (Set.finite_range (fun i => c * |b i|)).bddAbove j
          have hsup (v : ι → Ω → ℝ) (ε : Fin (m + 1) → Bool) :
              (⨆ j, |rademacherAverage (m + 1) X ε (v j)|) =
                c * (⨆ j, |rademacherSum (fun k => v j (X k)) ε|) := by
            simp_rw [haverage v ε]
            exact hscale (fun j => rademacherSum (fun k => v j (X k)) ε)
          have hintegral (v : ι → Ω → ℝ) :
              ∫ ε, ⨆ j, |rademacherAverage (m + 1) X ε (v j)|
                  ∂rademacherCube (m + 1) =
                c * ∫ ε, ⨆ j, |rademacherSum (fun k => v j (X k)) ε|
                  ∂rademacherCube (m + 1) := by
            calc
              _ = ∫ ε, c * (⨆ j, |rademacherSum (fun k => v j (X k)) ε|)
                    ∂rademacherCube (m + 1) :=
                integral_congr_ae (Filter.Eventually.of_forall (hsup v))
              _ = _ := integral_const_mul _ _
          rw [hintegral (fun j x => clippedSquare K (u j x)), hintegral u]
          calc
            c * ∫ ε, ⨆ j,
                |rademacherSum (fun k => clippedSquare K (u j (X k))) ε|
                ∂rademacherCube (m + 1) ≤
                c * (4 * K * ∫ ε, ⨆ j,
                  |rademacherSum (fun k => u j (X k)) ε|
                  ∂rademacherCube (m + 1)) :=
              mul_le_mul_of_nonneg_left
                (integral_iSup_abs_rademacherSum_clippedSquare_le
                  (fun j k => u j (X k)) K hK) hc
            _ = 4 * K * (c * ∫ ε, ⨆ j,
                  |rademacherSum (fun k => u j (X k)) ε|
                  ∂rademacherCube (m + 1)) := by ring

set_option linter.unusedFintypeInType false in
theorem lintegral_iSup_ofReal_abs_rademacherAverage_clippedSquare_le
    {Ω ι : Type*} [Fintype ι]
    (n : ℕ) (X : Fin n → Ω) (u : ι → Ω → ℝ)
    (K : ℝ) (hK : 0 ≤ K) :
    ∫⁻ ε, ENNReal.ofReal
        (⨆ j, |rademacherAverage n X ε
          (fun x => clippedSquare K (u j x))|)
      ∂rademacherCube n ≤
      ENNReal.ofReal (4 * K) *
        ∫⁻ ε, ENNReal.ofReal
          (⨆ j, |rademacherAverage n X ε (u j)|)
        ∂rademacherCube n := by
  classical
  have hleft_int : Integrable
      (fun ε : Fin n → Bool => ⨆ j, |rademacherAverage n X ε
        (fun x => clippedSquare K (u j x))|)
      (rademacherCube n) := Integrable.of_finite
  have hright_int : Integrable
      (fun ε : Fin n → Bool => ⨆ j, |rademacherAverage n X ε (u j)|)
      (rademacherCube n) := Integrable.of_finite
  have hleft_nonneg : ∀ ε : Fin n → Bool,
      0 ≤ ⨆ j, |rademacherAverage n X ε
        (fun x => clippedSquare K (u j x))| :=
    fun ε => Real.iSup_nonneg fun j => abs_nonneg _
  have hright_nonneg : ∀ ε : Fin n → Bool,
      0 ≤ ⨆ j, |rademacherAverage n X ε (u j)| :=
    fun ε => Real.iSup_nonneg fun j => abs_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hleft_int
      (Filter.Eventually.of_forall hleft_nonneg),
    ← ofReal_integral_eq_lintegral_ofReal hright_int
      (Filter.Eventually.of_forall hright_nonneg),
    ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hK)]
  exact ENNReal.ofReal_le_ofReal
    (integral_iSup_abs_rademacherAverage_clippedSquare_le n X u K hK)

set_option linter.unusedFintypeInType false in
theorem rademacherSup_range_eq_ofReal_iSup
    {Ω ι : Type*} [Fintype ι]
    (u : ι → Ω → ℝ) (n : ℕ) (X : Fin n → Ω)
    (ε : Fin n → Bool) :
    rademacherSup (Set.range u) n X ε =
      ENNReal.ofReal
        (⨆ j, |rademacherAverage n X ε (u j)|) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI : IsEmpty ι := hι
      simp [rademacherSup, supNormOver]
  | inr hι =>
      letI : Nonempty ι := hι
      unfold rademacherSup supNormOver
      apply le_antisymm
      · refine iSup_le fun f => iSup_le fun hf => ?_
        obtain ⟨j, rfl⟩ := hf
        exact ENNReal.ofReal_le_ofReal
          (le_ciSup (Finite.bddAbove_range
            (fun j => |rademacherAverage n X ε (u j)|)) j)
      · obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite
          (f := fun j => |rademacherAverage n X ε (u j)|)
        rw [← hj]
        exact le_iSup_of_le (u j) (le_iSup_of_le ⟨j, rfl⟩ le_rfl)

set_option linter.unusedFintypeInType false in
theorem conditionalRademacherSup_range_clippedSquare_le
    {Ω ι : Type*} [Fintype ι]
    (u : ι → Ω → ℝ) (n : ℕ) (X : Fin n → Ω)
    (K : ℝ) (hK : 0 ≤ K) :
    conditionalRademacherSup
        (Set.range (fun j x => clippedSquare K (u j x)))
        n X ≤
      ENNReal.ofReal (4 * K) *
        conditionalRademacherSup (Set.range u) n X := by
  unfold conditionalRademacherSup
  simp_rw [rademacherSup_range_eq_ofReal_iSup]
  exact lintegral_iSup_ofReal_abs_rademacherAverage_clippedSquare_le
    n X u K hK

theorem conditionalRademacherSup_range_eq_iSup_finset
    {Ω ι : Type*} (u : ι → Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) :
    conditionalRademacherSup (Set.range u) n X =
      ⨆ S : Finset ι,
        conditionalRademacherSup
          (Set.range (fun j : S => u j)) n X := by
  classical
  have hmono {S T : Finset ι} (hST : S ⊆ T) (ε : Fin n → Bool) :
      rademacherSup (Set.range (fun j : S => u j)) n X ε ≤
        rademacherSup (Set.range (fun j : T => u j)) n X ε := by
    unfold rademacherSup
    apply supNormOver_mono
    rintro f ⟨j, rfl⟩
    exact ⟨⟨j, hST j.property⟩, rfl⟩
  have hpoint (ε : Fin n → Bool) :
      rademacherSup (Set.range u) n X ε =
        ⨆ S : Finset ι,
          rademacherSup (Set.range (fun j : S => u j)) n X ε := by
    apply le_antisymm
    · change supNormOver (Set.range u) _ ≤ _
      refine iSup_le fun f => iSup_le fun hf => ?_
      obtain ⟨j, rfl⟩ := hf
      refine le_iSup_of_le {j} ?_
      apply le_supNormOver
      exact ⟨⟨j, Finset.mem_singleton_self j⟩, rfl⟩
    · refine iSup_le fun S => ?_
      unfold rademacherSup
      apply supNormOver_mono
      rintro f ⟨j, rfl⟩
      exact ⟨j, rfl⟩
  unfold conditionalRademacherSup
  rw [lintegral_fintype]
  simp_rw [hpoint, ENNReal.iSup_mul]
  rw [ENNReal.finsetSum_iSup]
  · simp_rw [← lintegral_fintype]
  · intro S T
    refine ⟨S ∪ T, fun ε => ⟨?_, ?_⟩⟩
    · gcongr
      exact hmono Finset.subset_union_left ε
    · gcongr
      exact hmono Finset.subset_union_right ε

theorem conditionalRademacherSup_image_clippedSquare_le
    {Ω : Type*} (F : Set (Ω → ℝ))
    (n : ℕ) (X : Fin n → Ω)
    (K : ℝ) (hK : 0 ≤ K) :
    conditionalRademacherSup
        ((fun f : Ω → ℝ => fun x => clippedSquare K (f x)) '' F) n X ≤
      ENNReal.ofReal (4 * K) * conditionalRademacherSup F n X := by
  classical
  have himage :
      ((fun f : Ω → ℝ => fun x => clippedSquare K (f x)) '' F) =
        Set.range (fun f : F => fun x => clippedSquare K (f.1 x)) := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨f, f.property, rfl⟩
  rw [himage, conditionalRademacherSup_range_eq_iSup_finset]
  refine iSup_le fun S => ?_
  have hfinite := conditionalRademacherSup_range_clippedSquare_le
    (fun j : S => (j.1.1 : Ω → ℝ)) n X K hK
  have hsub : Set.range (fun j : S => (j.1.1 : Ω → ℝ)) ⊆ F := by
    rintro f ⟨j, rfl⟩
    exact j.1.2
  have hmono :
      conditionalRademacherSup
          (Set.range (fun j : S => (j.1.1 : Ω → ℝ))) n X ≤
        conditionalRademacherSup F n X := by
    unfold conditionalRademacherSup rademacherSup
    exact lintegral_mono fun ε => supNormOver_mono hsub _
  exact hfinite.trans (by gcongr)

end AsymptoticStatistics.EmpiricalProcess
