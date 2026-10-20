module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterTightness

@[expose] public section

/-!
# Continuous mapping for weak convergence in outer expectation

The continuous mapping theorem for possibly nonmeasurable random maps. The
only measurability used is that of the continuous map between Borel-compatible
spaces; the random maps themselves remain arbitrary.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-- Changing from the norm of a composed bounded continuous function to the
norm of the original test function does not change its shifted outer readout.
-/
private theorem outerReadout_compContinuous_eq {Ω D E : Type*}
    [MeasurableSpace Ω] [TopologicalSpace D] [TopologicalSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : E →ᵇ ℝ) (g : C(D, E))
    (X : Ω → D) :
    (outerExpectation μ
        (fun ω => ENNReal.ofReal (f (g (X ω)) + ‖f‖))).toReal
          - ‖f‖ * (μ Set.univ).toReal =
      (outerExpectation μ (fun ω => ENNReal.ofReal
        ((f.compContinuous g) (X ω) + ‖f.compContinuous g‖))).toReal
          - ‖f.compContinuous g‖ * (μ Set.univ).toReal := by
  have hnorm : ‖f.compContinuous g‖ ≤ ‖f‖ := f.norm_compContinuous_le g
  have hbase_nonneg : ∀ ω,
      0 ≤ (f.compContinuous g) (X ω) + ‖f.compContinuous g‖ := by
    intro ω
    have h := (abs_le.1 ((f.compContinuous g).norm_coe_le_norm (X ω))).1
    linarith
  have hsplit :
      (fun ω => ENNReal.ofReal (f (g (X ω)) + ‖f‖)) =
        fun ω => ENNReal.ofReal
            ((f.compContinuous g) (X ω) + ‖f.compContinuous g‖) +
          ENNReal.ofReal (‖f‖ - ‖f.compContinuous g‖) := by
    funext ω
    calc
      ENNReal.ofReal (f (g (X ω)) + ‖f‖) =
          ENNReal.ofReal (((f.compContinuous g) (X ω) + ‖f.compContinuous g‖) +
            (‖f‖ - ‖f.compContinuous g‖)) := by
              congr 1
              rw [compContinuous_apply]
              ring
      _ = ENNReal.ofReal
            ((f.compContinuous g) (X ω) + ‖f.compContinuous g‖) +
          ENNReal.ofReal (‖f‖ - ‖f.compContinuous g‖) :=
        ENNReal.ofReal_add (hbase_nonneg ω) (sub_nonneg.mpr hnorm)
  have hbase_le :
      outerExpectation μ (fun ω => ENNReal.ofReal
          ((f.compContinuous g) (X ω) + ‖f.compContinuous g‖))
        ≤ ENNReal.ofReal (2 * ‖f.compContinuous g‖) := by
    calc
      outerExpectation μ (fun ω => ENNReal.ofReal
          ((f.compContinuous g) (X ω) + ‖f.compContinuous g‖))
          ≤ outerExpectation μ (fun _ => ENNReal.ofReal (2 * ‖f.compContinuous g‖)) :=
        outerExpectation_mono fun ω => ENNReal.ofReal_le_ofReal (by
          have h := (abs_le.1 ((f.compContinuous g).norm_coe_le_norm (X ω))).2
          linarith)
      _ = ENNReal.ofReal (2 * ‖f.compContinuous g‖) := by
        rw [outerExpectation_const]
        simp
  have hbase_ne_top :
      outerExpectation μ (fun ω => ENNReal.ofReal
          ((f.compContinuous g) (X ω) + ‖f.compContinuous g‖)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbase_le
  rw [hsplit, outerExpectation_add_const _ _ ENNReal.ofReal_ne_top]
  simp only [measure_univ, ENNReal.toReal_one, mul_one]
  rw [ENNReal.toReal_add hbase_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hnorm)]
  ring

/-- **Continuous mapping theorem for outer weak convergence.** A continuous
image of a sequence converging weakly in outer expectation converges to the
pushforward of the limit law. No measurability of the random maps is required.
-/
theorem WeakConvergesOuter.continuous_comp {Ω D E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace D] [PseudoMetricSpace D]
    [MeasurableSpace E] [PseudoMetricSpace E] [OpensMeasurableSpace D]
    [BorelSpace E] {μ : ℕ → Measure Ω} {X : ℕ → Ω → D} {ν : Measure D}
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (h : WeakConvergesOuter μ X ν) {g : D → E} (hg : Continuous g) :
    WeakConvergesOuter μ (fun n => g ∘ X n) (ν.map g) := by
  let gc : C(D, E) := ⟨g, hg⟩
  have hg_meas : Measurable g := hg.measurable
  intro f
  have hcomp := h (f.compContinuous gc)
  have hreadout :
      (fun n => (outerExpectation (μ n)
          (fun ω => ENNReal.ofReal (f ((fun n => g ∘ X n) n ω) + ‖f‖))).toReal
            - ‖f‖ * (μ n Set.univ).toReal) =
        fun n => (outerExpectation (μ n) (fun ω => ENNReal.ofReal
          ((f.compContinuous gc) (X n ω) + ‖f.compContinuous gc‖))).toReal
            - ‖f.compContinuous gc‖ * (μ n Set.univ).toReal := by
    funext n
    exact outerReadout_compContinuous_eq (μ n) f gc (X n)
  have hlimit :
      ∫ y, f y ∂ν.map g = ∫ x, (f.compContinuous gc) x ∂ν := by
    rw [integral_map hg_meas.aemeasurable f.continuous.measurable.aestronglyMeasurable]
    rfl
  rw [hreadout, hlimit]
  exact hcomp

end AsymptoticStatistics
