module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace AsymptoticStatistics.ForMathlib

open MeasureTheory
open scoped ENNReal

theorem setLIntegral_Ioc_le_initial_add_ratio_mul_initial_of_antitone
    (g : ℝ → ℝ≥0∞)
    (hg : Antitone g)
    {a t : ℝ}
    (ha : 0 < a) :
    (∫⁻ ε in Set.Ioc 0 t, g ε ∂volume) ≤
      (∫⁻ ε in Set.Ioc 0 a, g ε ∂volume) +
        ENNReal.ofReal (t / a) *
          (∫⁻ ε in Set.Ioc 0 a, g ε ∂volume) := by
  by_cases hta : t ≤ a
  · calc
      (∫⁻ ε in Set.Ioc 0 t, g ε ∂volume) ≤
          ∫⁻ ε in Set.Ioc 0 a, g ε ∂volume :=
        lintegral_mono_set (Set.Ioc_subset_Ioc_right hta)
      _ ≤ (∫⁻ ε in Set.Ioc 0 a, g ε ∂volume) +
          ENNReal.ofReal (t / a) *
            (∫⁻ ε in Set.Ioc 0 a, g ε ∂volume) :=
        le_add_of_nonneg_right (zero_le)
  · have hat : a < t := lt_of_not_ge hta
    have ht0 : 0 ≤ t := (ha.trans hat).le
    have hlower :
        ENNReal.ofReal a * g a ≤ ∫⁻ ε in Set.Ioc 0 a, g ε ∂volume := by
      calc
        ENNReal.ofReal a * g a =
            ∫⁻ _ε in Set.Ioc 0 a, g a ∂volume := by
          rw [setLIntegral_const, Real.volume_Ioc]
          simp [mul_comm]
        _ ≤ ∫⁻ ε in Set.Ioc 0 a, g ε ∂volume :=
          setLIntegral_mono' measurableSet_Ioc (fun ε hε => hg hε.2)
    have htail :
        (∫⁻ ε in Set.Ioc a t, g ε ∂volume) ≤
          g a * ENNReal.ofReal (t - a) := by
      calc
        (∫⁻ ε in Set.Ioc a t, g ε ∂volume) ≤
            ∫⁻ _ε in Set.Ioc a t, g a ∂volume :=
          setLIntegral_mono' measurableSet_Ioc (fun ε hε => hg hε.1.le)
        _ = g a * ENNReal.ofReal (t - a) := by
          rw [setLIntegral_const, Real.volume_Ioc]
    have hcoeff :
        ENNReal.ofReal t = ENNReal.ofReal (t / a) * ENNReal.ofReal a := by
      rw [← ENNReal.ofReal_mul (div_nonneg ht0 ha.le), div_mul_cancel₀ t ha.ne']
    have htail' :
        (∫⁻ ε in Set.Ioc a t, g ε ∂volume) ≤
          ENNReal.ofReal (t / a) *
            (∫⁻ ε in Set.Ioc 0 a, g ε ∂volume) := by
      calc
        (∫⁻ ε in Set.Ioc a t, g ε ∂volume) ≤
            g a * ENNReal.ofReal (t - a) := htail
        _ ≤ g a * ENNReal.ofReal t :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal (by linarith)) _
        _ = ENNReal.ofReal (t / a) * (ENNReal.ofReal a * g a) := by
          rw [hcoeff]
          ac_rfl
        _ ≤ ENNReal.ofReal (t / a) *
            (∫⁻ ε in Set.Ioc 0 a, g ε ∂volume) :=
          mul_le_mul_right hlower _
    rw [← Set.Ioc_union_Ioc_eq_Ioc ha.le hat.le,
      lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
    exact add_le_add_right htail' _

end AsymptoticStatistics.ForMathlib
