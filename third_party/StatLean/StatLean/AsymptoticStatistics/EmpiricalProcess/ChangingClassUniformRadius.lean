module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChangingClassUniform
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedEmpiricalSquareRadius

@[expose] public section
/-! # Strict localization for changing classes -/
namespace AsymptoticStatistics.EmpiricalProcess
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option linter.style.longLine false in
/-- A strict population square-radius bound localizes every row increment. -/
theorem changingLocalDifferenceClass_subset_strictLocalizedDifferenceClass_of_populationSquareRadius_lt
    {Ω T : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    (f : ℕ → T → Ω → ℝ) (P : Measure Ω)
    (n : ℕ) (δ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hRadius : populationSquareRadius P
      (changingLocalDifferenceClass f n δ) < ENNReal.ofReal ε) :
    changingLocalDifferenceClass f n δ ⊆
      strictLocalizedDifferenceClass (Set.range (f n)) P (Real.sqrt ε) := by
  rintro h ⟨s, t, hst, rfl⟩
  refine ⟨f n s, ⟨s, rfl⟩, f n t, ⟨t, rfl⟩, rfl, ?_⟩
  have hmem : (fun x => f n s x - f n t x) ∈
      changingLocalDifferenceClass f n δ := ⟨s, t, hst, rfl⟩
  have hmoment_lt :
      (∫⁻ x, ENNReal.ofReal ((f n s x - f n t x) ^ 2) ∂P) <
        ENNReal.ofReal ε := by
    refine lt_of_le_of_lt ?_ hRadius
    unfold populationSquareRadius
    exact le_iSup₂
      (f := fun g : Ω → ℝ => fun _ : g ∈ changingLocalDifferenceClass f n δ =>
        ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂P)
      (fun x => f n s x - f n t x) hmem
  have hnorm_sq :
      eLpNorm (fun x => f n s x - f n t x) 2 P ^ (2 : ℕ) =
        ∫⁻ x, ENNReal.ofReal ((f n s x - f n t x) ^ 2) ∂P := by
    calc
      eLpNorm (fun x => f n s x - f n t x) 2 P ^ (2 : ℕ) =
          eLpNorm (fun x => f n s x - f n t x) 2 P ^ (2 : ℝ) :=
        (ENNReal.rpow_natCast _ 2).symm
      _ = ∫⁻ x, ‖f n s x - f n t x‖ₑ ^ (2 : ℝ) ∂P := by
        simpa using eLpNorm_nnreal_pow_eq_lintegral
          (f := fun x => f n s x - f n t x) (μ := P)
          (p := (2 : NNReal)) (by norm_num : (2 : NNReal) ≠ 0)
      _ = ∫⁻ x, ENNReal.ofReal ((f n s x - f n t x) ^ 2) ∂P := by
        refine lintegral_congr fun x => ?_
        calc
          ‖f n s x - f n t x‖ₑ ^ (2 : ℝ) =
              ‖f n s x - f n t x‖ₑ ^ (2 : ℕ) := ENNReal.rpow_natCast _ 2
          _ = ENNReal.ofReal ((f n s x - f n t x) ^ 2) := by
            rw [Real.enorm_eq_ofReal_abs,
              ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_pos hε, one_div]
  refine (ENNReal.lt_rpow_inv_iff (z := (2 : ℝ)) (by norm_num)).2 ?_
  calc
    eLpNorm (fun x => f n s x - f n t x) 2 P ^ (2 : ℝ) =
        eLpNorm (fun x => f n s x - f n t x) 2 P ^ (2 : ℕ) :=
      ENNReal.rpow_natCast _ 2
    _ < ENNReal.ofReal ε := hnorm_sq.trans_lt hmoment_lt

end

end AsymptoticStatistics.EmpiricalProcess
