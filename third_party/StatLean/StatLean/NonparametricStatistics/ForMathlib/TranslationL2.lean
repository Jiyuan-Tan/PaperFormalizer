module
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

/-!
# Continuity of translation in L²(ℝ)

For `f ∈ L²(ℝ)`: `∫ (f(x + t) − f(x))² dx → 0` as `t → 0`.

This is the sole analytic input through which the exact asymptotic mean integrated squared
error of kernel density estimators acquires its `o(1)`: the difference between the bias
integrand and its small-bandwidth limit is controlled by `L²`-moduli of translates of the
(weak) second derivative.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Appendix, Lemma A.2 ($L^2$-continuity of translation).

**Proof formalization notes.** Stated with the lower Lebesgue integral (no integrability side
conditions; the hypothesis `MemLp f 2` makes the value finite). Proof route: density of
continuous compactly supported functions in `L²`
(`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` or the
`ContinuousMap`-density theorems), uniform continuity on compacts for the smooth
approximation, and a `3ε` argument; translation invariance of Lebesgue measure
(`Real.map_volume_add_left` / `lintegral_add_right_eq_self`) equates the translated norms.
An alternative route is via the Fourier–Plancherel isometry if available on the pin.

**Bibliographic comments.** Classical; see e.g. E. M. Stein and G. Weiss, *Introduction to
Fourier Analysis on Euclidean Spaces* (Princeton, 1971), Ch. I.
-/

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace StatLean.NonparametricStatistics

/-- `‖r‖ₑ ^ 2 = ofReal (r ^ 2)`, the bridge between the `enorm`-squared and `ofReal`-squared
integrands. -/
private lemma enorm_rpow_two (r : ℝ) : ‖r‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (r ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg r) (by norm_num),
    Real.rpow_two, sq_abs]

/-- Continuity of translation for a *continuous, compactly supported* function, in `L²`:
`eLpNorm (φ(· + t) − φ) 2 → 0` as `t → 0`. -/
private lemma tendsto_eLpNorm_translate_sub {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => φ (x + t) - φ x) 2 volume) (𝓝 0) (𝓝 0) := by
  have hφuc : UniformContinuous φ := hφs.uniformContinuous_of_continuous hφc
  have hK : IsCompact (tsupport φ) := hφs
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  set K' : Set ℝ := closedBall (0 : ℝ) (R + 1) with hK'def
  have hK'meas : MeasurableSet K' := measurableSet_closedBall
  have hK'fin : volume K' ≠ ⊤ := measure_closedBall_lt_top.ne
  set V : ℝ≥0∞ := volume K' ^ (1 / 2 : ℝ) with hVdef
  have hVne : V ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK'fin).ne
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with hηtop | hηtop
  · exact Eventually.of_forall fun t => hηtop ▸ le_top
  · have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
    set C : ℝ := η.toReal / (V.toReal + 1) with hC
    have hC0 : 0 < C := by rw [hC]; positivity
    obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.1 hφuc C hC0
    filter_upwards [ball_mem_nhds (0 : ℝ) (lt_min hδ0 one_pos)] with t ht
    rw [mem_ball, Real.dist_eq, sub_zero] at ht
    have htδ : |t| < δ := lt_of_lt_of_le ht (min_le_left _ _)
    have ht1 : |t| < 1 := lt_of_lt_of_le ht (min_le_right _ _)
    -- pointwise domination by the constant `C` on the fixed compact `K'`
    have hpt : ∀ x, ‖φ (x + t) - φ x‖ ≤ ‖K'.indicator (fun _ => C) x‖ := by
      intro x
      by_cases hx : x ∈ K'
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC0.le]
        have hdist : dist (φ (x + t)) (φ x) < C := hδ (by rw [Real.dist_eq, add_sub_cancel_left]; exact htδ)
        rw [Real.dist_eq] at hdist
        exact hdist.le
      · have hxabs : R + 1 < |x| := by
          rw [hK'def, mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx; exact hx
        have hout : φ (x + t) = 0 := by
          refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
          have : |x + t| ≤ R := by
            have := hR hmem; rw [mem_closedBall, Real.dist_eq, sub_zero] at this; exact this
          have hab : |x| ≤ |x + t| + |t| := by
            have := abs_add_le (x + t) (-t); simpa [abs_neg] using this
          linarith
        have hx0 : φ x = 0 := by
          refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
          have := hR hmem; rw [mem_closedBall, Real.dist_eq, sub_zero] at this; linarith
        rw [Set.indicator_of_notMem hx, hout, hx0]; simp
    calc eLpNorm (fun x => φ (x + t) - φ x) 2 volume
        ≤ eLpNorm (K'.indicator (fun _ => C)) 2 volume := eLpNorm_mono hpt
      _ = ‖C‖ₑ * volume K' ^ (1 / (2 : ℝ≥0∞).toReal) :=
          eLpNorm_indicator_const hK'meas (by norm_num) (by norm_num)
      _ = ENNReal.ofReal C * V := by
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC0.le]; norm_num [hVdef]
      _ ≤ η := by
          rw [show V = ENNReal.ofReal V.toReal from (ENNReal.ofReal_toReal hVne).symm,
            ← ENNReal.ofReal_mul hC0.le, ← ENNReal.ofReal_toReal hηtop]
          apply ENNReal.ofReal_le_ofReal
          rw [hC, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [ENNReal.toReal_nonneg (a := V), hηr.le]

/-- **Continuity of translation in `L²(ℝ)`**: for square-integrable `f`,
`∫⁻ (f(x+t) − f(x))² dx → 0` as `t → 0`. -/
theorem tendsto_lintegral_sq_sub_translate {f : ℝ → ℝ}
    -- LEAN-ONLY: measurability of `f`; standard regularity
    (hf : Measurable f)
    -- USER-INPUT: square integrability of `f`; classical hypothesis of the translation lemma
    (hf2 : MemLp f 2 volume) :
    Tendsto (fun t : ℝ => ∫⁻ x, ENNReal.ofReal ((f (x + t) - f x) ^ 2))
      (𝓝 0) (𝓝 0) := by
  have haf : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  -- `N t := eLpNorm (f(·+t) − f) 2` tends to `0`.
  have hN : Tendsto (fun t : ℝ => eLpNorm (fun x => f (x + t) - f x) 2 volume) (𝓝 0) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨φ, hφsupp, hφsub, hφc, hφmem⟩ :=
      MemLp.exists_hasCompactSupport_eLpNorm_sub_le (μ := volume) (p := 2) (ε := ε / 3)
        (by norm_num) hf2 (ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top).ne'
    have haφ : AEStronglyMeasurable φ volume := hφc.aestronglyMeasurable
    have hmid := tendsto_eLpNorm_translate_sub hφc hφsupp
    rw [ENNReal.tendsto_nhds_zero] at hmid
    have h3 : ε / 3 + ε / 3 + ε / 3 = ε := by
      rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, show ε + ε + ε = 3 * ε by ring,
        mul_div_assoc, ENNReal.mul_div_cancel (by norm_num) ENNReal.ofNat_ne_top]
    filter_upwards [hmid (ε / 3) (ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top)] with t ht
    have haft : AEStronglyMeasurable (fun x => f (x + t)) volume :=
      (hf.comp (measurable_id.add_const t)).aestronglyMeasurable
    have haφt : AEStronglyMeasurable (fun x => φ (x + t)) volume :=
      (hφc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    have hA : AEStronglyMeasurable (fun x => f (x + t) - φ (x + t)) volume := haft.sub haφt
    have hB : AEStronglyMeasurable (fun x => φ (x + t) - φ x) volume := haφt.sub haφ
    have hC : AEStronglyMeasurable (fun x => φ x - f x) volume := haφ.sub haf
    have hsum : (fun x => f (x + t) - f x) = (fun x => f (x + t) - φ (x + t))
        + ((fun x => φ (x + t) - φ x) + (fun x => φ x - f x)) := by
      funext x; simp only [Pi.add_apply]; ring
    have hAeq : eLpNorm (fun x => f (x + t) - φ (x + t)) 2 volume = eLpNorm (f - φ) 2 volume := by
      have := eLpNorm_comp_measurePreserving (g := f - φ) (p := (2 : ℝ≥0∞))
        (haf.sub haφ) (measurePreserving_add_right volume t)
      simpa [Function.comp, Pi.sub_apply] using! this
    have hCeq : eLpNorm (fun x => φ x - f x) 2 volume = eLpNorm (f - φ) 2 volume :=
      eLpNorm_sub_comm φ f 2 volume
    rw [hsum]
    calc eLpNorm ((fun x => f (x + t) - φ (x + t))
            + ((fun x => φ (x + t) - φ x) + (fun x => φ x - f x))) 2 volume
        ≤ eLpNorm (fun x => f (x + t) - φ (x + t)) 2 volume
            + eLpNorm ((fun x => φ (x + t) - φ x) + (fun x => φ x - f x)) 2 volume :=
          eLpNorm_add_le hA (hB.add hC) one_le_two
      _ ≤ eLpNorm (fun x => f (x + t) - φ (x + t)) 2 volume
            + (eLpNorm (fun x => φ (x + t) - φ x) 2 volume
              + eLpNorm (fun x => φ x - f x) 2 volume) :=
          add_le_add (le_refl _) (eLpNorm_add_le hB hC one_le_two)
      _ = eLpNorm (f - φ) 2 volume
            + (eLpNorm (fun x => φ (x + t) - φ x) 2 volume + eLpNorm (f - φ) 2 volume) := by
          rw [hAeq, hCeq]
      _ ≤ ε / 3 + (ε / 3 + ε / 3) := add_le_add hφsub (add_le_add ht hφsub)
      _ = ε := by rw [← add_assoc]; exact h3
  -- Transfer `N t → 0` to the stated lintegral via `∫ ofReal(g²) = (eLpNorm g 2)²`.
  have hEq : ∀ t : ℝ, (∫⁻ x, ENNReal.ofReal ((f (x + t) - f x) ^ 2))
      = (eLpNorm (fun x => f (x + t) - f x) 2 volume) ^ (2 : ℝ) := by
    intro t
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    exact lintegral_congr fun x => (enorm_rpow_two _).symm
  have hFtendsto :
      Tendsto (fun t : ℝ => (eLpNorm (fun x => f (x + t) - f x) 2 volume) ^ (2 : ℝ))
        (𝓝 0) (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto (0 : ℝ≥0∞)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    exact h.comp hN
  simpa only [hEq] using hFtendsto

end StatLean.NonparametricStatistics
