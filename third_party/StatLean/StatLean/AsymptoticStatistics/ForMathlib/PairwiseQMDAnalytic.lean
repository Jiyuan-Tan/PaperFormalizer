module
public import StatLean.AsymptoticStatistics.Core.Hilbert
public import StatLean.AsymptoticStatistics.ForMathlib.QMDAnalytic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
# One-sided pairwise quadratic-mean differentiability

The square-root comparison is made against the canonical pairwise dominator
`P + Q`; hence no single measure must dominate an entire curve.  This is the
nondominated reading of van der Vaart (25.13).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic

open AsymptoticStatistics.Core.Hilbert

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The canonical finite dominator of a pair of measures.  Edge behavior: if
one measure is zero this is the other measure. -/
noncomputable def canonicalDominator (P Q : Measure Ω) : Measure Ω := P + Q

/-- Square-root QMD residual for `P` versus `Q`, represented under `μ`.
The definition is meaningful without domination, but its invariance theorem
assumes both measures are absolutely continuous with respect to `μ`. -/
noncomputable def residualAgainst (P Q μ : Measure Ω) (g : Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  fun ω => Real.sqrt (Q.rnDeriv μ ω).toReal
    - Real.sqrt (P.rnDeriv μ ω).toReal
    - (t / 2) * g ω * Real.sqrt (P.rnDeriv μ ω).toReal

/-- Right-sided nondominated QMD at zero, using the canonical pairwise
dominator separately for every `t`.  The ENNReal quotient prevents a
non-`L²` residual from being hidden by `toReal`. -/
def IsRightQMD (P : Measure Ω) (curve : ℝ → Measure Ω) (g : Ω → ℝ) : Prop :=
  Tendsto
    (fun t => eLpNorm
      (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
      2 (canonicalDominator P (curve t)) / ENNReal.ofReal t)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : ℝ≥0∞))

/-- The weighted `L²` change-of-dominator identity used below. -/
private lemma eLpNorm_sqrt_rnDeriv_mul_eq
    {ν ξ : Measure Ω} [SigmaFinite ν] [SigmaFinite ξ]
    (hνξ : ν ≪ ξ) (h : Ω → ℝ) :
    eLpNorm (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal * h ω) 2 ξ =
      eLpNorm h 2 ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  congr 1
  have h_ae : (fun ω => ‖Real.sqrt (ν.rnDeriv ξ ω).toReal * h ω‖ₑ ^ (2 : ℝ))
      =ᵐ[ξ] (fun ω => ν.rnDeriv ξ ω * ‖h ω‖ₑ ^ (2 : ℝ)) := by
    filter_upwards [Measure.rnDeriv_lt_top ν ξ] with ω hω
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      Real.enorm_of_nonneg (Real.sqrt_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, Real.sq_sqrt ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hω.ne]
  rw [lintegral_congr_ae h_ae]
  calc
    ∫⁻ ω, ν.rnDeriv ξ ω * ‖h ω‖ₑ ^ (2 : ℝ) ∂ξ =
        ∫⁻ ω, ‖h ω‖ₑ ^ (2 : ℝ) ∂ξ.withDensity (ν.rnDeriv ξ) :=
      (lintegral_withDensity_eq_lintegral_mul_non_measurable ξ
        (Measure.measurable_rnDeriv ν ξ) (Measure.rnDeriv_lt_top ν ξ) _).symm
    _ = ∫⁻ ω, ‖h ω‖ₑ ^ (2 : ℝ) ∂ν := by
      rw [Measure.withDensity_rnDeriv_eq ν ξ hνξ]

/-- Pairwise square-root residual norms do not depend on the chosen common
dominator.

Proof idea: rewrite both RN derivatives through `μ`, split where the
canonical density vanishes, and apply the with-density `eLpNorm` identity.

Joint witness: `P=Q=μ` and `g=0`. -/
theorem eLpNorm_residualAgainst_change_dominator
    (P Q μ : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [SigmaFinite μ] (hP : P ≪ μ) (hQ : Q ≪ μ)
    (g : Ω → ℝ) (t : ℝ) :
    eLpNorm (residualAgainst P Q (canonicalDominator P Q) g t)
        2 (canonicalDominator P Q) =
      eLpNorm (residualAgainst P Q μ g t) 2 μ := by
  let ν := canonicalDominator P Q
  letI : IsFiniteMeasure ν := by
    dsimp [ν, canonicalDominator]
    infer_instance
  have hνμ : ν ≪ μ := Measure.AbsolutelyContinuous.add_left hP hQ
  have hPν : P ≪ ν :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hQν : Q ≪ ν :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hfac : residualAgainst P Q μ g t =ᵐ[μ] fun ω =>
      Real.sqrt (ν.rnDeriv μ ω).toReal * residualAgainst P Q ν g t ω := by
    have hPchain := Measure.rnDeriv_mul_rnDeriv hPν (κ := μ)
    have hQchain := Measure.rnDeriv_mul_rnDeriv hQν (κ := μ)
    filter_upwards [hPchain, hQchain] with ω hPω hQω
    have hsP : Real.sqrt (P.rnDeriv μ ω).toReal =
        Real.sqrt (P.rnDeriv ν ω).toReal * Real.sqrt (ν.rnDeriv μ ω).toReal := by
      rw [← hPω, Pi.mul_apply, ENNReal.toReal_mul,
        Real.sqrt_mul ENNReal.toReal_nonneg]
    have hsQ : Real.sqrt (Q.rnDeriv μ ω).toReal =
        Real.sqrt (Q.rnDeriv ν ω).toReal * Real.sqrt (ν.rnDeriv μ ω).toReal := by
      rw [← hQω, Pi.mul_apply, ENNReal.toReal_mul,
        Real.sqrt_mul ENNReal.toReal_nonneg]
    simp only [residualAgainst, hsP, hsQ]
    ring
  rw [eLpNorm_congr_ae hfac]
  exact (eLpNorm_sqrt_rnDeriv_mul_eq hνμ _).symm

/-- A right-QMD remainder already forces square-integrability of the score. -/
private lemma memLp_score_of_rightQMD
    (P : Measure Ω) [IsProbabilityMeasure P]
    (curve : ℝ → Measure Ω)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (curve t))
    (g : Ω → ℝ) (hg : Measurable g) (hqmd : IsRightQMD P curve g) :
    MemLp g 2 P := by
  obtain ⟨t, ht, hlt⟩ : ∃ t : ℝ, 0 < t ∧
      eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
          2 (canonicalDominator P (curve t)) < ENNReal.ofReal t := by
    have hsmall : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
        eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
          2 (canonicalDominator P (curve t)) / ENNReal.ofReal t < 1 :=
      hqmd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
    have hboth : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), 0 < t ∧
        eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
          2 (canonicalDominator P (curve t)) < ENNReal.ofReal t := by
      filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hlt
      refine ⟨ht, ?_⟩
      calc
        eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
            2 (canonicalDominator P (curve t)) =
            (eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
              2 (canonicalDominator P (curve t)) / ENNReal.ofReal t) * ENNReal.ofReal t := by
                rw [ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top]
        _ < 1 * ENNReal.ofReal t :=
          ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr ht).ne'
            ENNReal.ofReal_ne_top hlt
        _ = ENNReal.ofReal t := one_mul _
    exact hboth.exists
  let ν := canonicalDominator P (curve t)
  letI : IsProbabilityMeasure (curve t) := hprob t ht.le
  letI : IsFiniteMeasure ν := by
    dsimp [ν, canonicalDominator]
    infer_instance
  have hPν : P ≪ ν :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hQν : curve t ≪ ν :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hp : MemLp (fun ω => Real.sqrt (P.rnDeriv ν ω).toReal) 2 ν :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv hPν
  have hq : MemLp (fun ω => Real.sqrt ((curve t).rnDeriv ν ω).toReal) 2 ν :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv hQν
  have hr : MemLp (residualAgainst P (curve t) ν g t) 2 ν := by
    refine ⟨?_, lt_trans hlt ENNReal.ofReal_lt_top⟩
    exact (((Measure.measurable_rnDeriv (curve t) ν).ennreal_toReal.sqrt.sub
      (Measure.measurable_rnDeriv P ν).ennreal_toReal.sqrt).sub
      ((measurable_const.mul hg).mul
        (Measure.measurable_rnDeriv P ν).ennreal_toReal.sqrt)).aestronglyMeasurable
  have hscaled : MemLp
      (fun ω => (t / 2) * (g ω * Real.sqrt (P.rnDeriv ν ω).toReal)) 2 ν := by
    convert (hq.sub hp).sub hr using 1
    funext ω
    change (t / 2) * (g ω * Real.sqrt (P.rnDeriv ν ω).toReal) =
      (Real.sqrt ((curve t).rnDeriv ν ω).toReal -
        Real.sqrt (P.rnDeriv ν ω).toReal) - residualAgainst P (curve t) ν g t ω
    simp only [residualAgainst]
    ring
  have hgsqrt : MemLp (fun ω => g ω * Real.sqrt (P.rnDeriv ν ω).toReal) 2 ν := by
    convert hscaled.const_mul (2 / t) using 1
    funext ω
    field_simp
  exact AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_two_of_memLp_two_mul_sqrt_rnDeriv
    hPν hg.aestronglyMeasurable hgsqrt

set_option maxHeartbeats 3000000 in
-- The one-sided unit-norm argument expands several measure-valued L² identities.
/-- Analytic part of Lemma 25.14 for one-sided pairwise QMD: the bare score
has an `L²₀(P)` representative.

Proof idea: obtain `L²` from one positive parameter, then differentiate the
unit-mass identity from the right to prove mean zero.

Joint witness: the constant path with bare score zero. -/
theorem rightQMD_score_in_L2ZeroMean
    (P : Measure Ω) [IsProbabilityMeasure P]
    (curve : ℝ → Measure Ω)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (curve t))
    (hzero : curve 0 = P) (g : Ω → ℝ) (hg : Measurable g)
    (hqmd : IsRightQMD P curve g) :
    ∃ g' : ↥(L2ZeroMean P), g =ᵐ[P] (g' : Ω → ℝ) := by
  letI : IsProbabilityMeasure (curve 0) := hprob 0 le_rfl
  have hqmd0 : IsRightQMD (curve 0) curve g := by simpa [hzero] using hqmd
  have hgL20 : MemLp g 2 (curve 0) :=
    memLp_score_of_rightQMD (curve 0) curve hprob g hg hqmd0
  have hgL2 : MemLp g 2 P := by simpa [hzero] using hgL20
  let I : ℝ := ∫ ω, g ω ∂P
  let G : ℝ := (eLpNorm g 2 P).toReal
  let ν : ℝ → Measure Ω := fun t => canonicalDominator P (curve t)
  let r : ℝ → Ω → ℝ := fun t => residualAgainst P (curve t) (ν t) g t
  let R : ℝ → ℝ := fun t => (eLpNorm (r t) 2 (ν t)).toReal
  let H : ℝ → ℝ := fun t => (eLpNorm (fun ω =>
    Real.sqrt ((curve t).rnDeriv (ν t) ω).toReal -
      Real.sqrt (P.rnDeriv (ν t) ω).toReal) 2 (ν t)).toReal
  let C : ℝ → ℝ := fun t => ∫ ω, r t ω *
    Real.sqrt (P.rnDeriv (ν t) ω).toReal ∂(ν t)
  have hRratio : Tendsto (fun t => R t / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hreal := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp hqmd
    apply hreal.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change (eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
      2 (canonicalDominator P (curve t)) / ENNReal.ofReal t).toReal = _
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal ht.le]
  have ht0 : Tendsto (fun t : ℝ => t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hbound_zero : Tendsto
      (fun t => t / 2 * (G / 2 + R t / t) ^ 2 + R t / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc : Tendsto (fun _ : ℝ => G / 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (G / 2)) := tendsto_const_nhds
    have hsum : Tendsto (fun t => G / 2 + R t / t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (G / 2)) := by
      simpa using hc.add hRratio
    have hprod := (ht0.div_const 2).mul (hsum.pow 2)
    simpa using hprod.add hRratio
  have hsmall : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      eLpNorm (r t) 2 (ν t) / ENNReal.ofReal t < 1 := by
    simpa [IsRightQMD, r, ν] using
      hqmd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  have hmain : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      |I| / 2 ≤ t / 2 * (G / 2 + R t / t) ^ 2 + R t / t := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hlt
    have htpos : 0 < t := ht
    letI : IsProbabilityMeasure (curve t) := hprob t htpos.le
    letI : IsFiniteMeasure (ν t) := by
      dsimp [ν, canonicalDominator]
      infer_instance
    have hPν : P ≪ ν t :=
      Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
    have hQν : curve t ≪ ν t :=
      Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
    let p : Ω → ℝ := fun ω => Real.sqrt (P.rnDeriv (ν t) ω).toReal
    let q : Ω → ℝ := fun ω => Real.sqrt ((curve t).rnDeriv (ν t) ω).toReal
    have hp : MemLp p 2 (ν t) :=
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv hPν
    have hq : MemLp q 2 (ν t) :=
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv hQν
    have hrlt : eLpNorm (r t) 2 (ν t) < ENNReal.ofReal t := by
      calc
        eLpNorm (r t) 2 (ν t) =
            (eLpNorm (r t) 2 (ν t) / ENNReal.ofReal t) * ENNReal.ofReal t := by
              rw [ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr ht).ne'
                ENNReal.ofReal_ne_top]
        _ < 1 * ENNReal.ofReal t := ENNReal.mul_lt_mul_left
          (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top hlt
        _ = ENNReal.ofReal t := one_mul _
    have hr : MemLp (r t) 2 (ν t) := by
      refine ⟨?_, lt_trans hrlt ENNReal.ofReal_lt_top⟩
      exact (((Measure.measurable_rnDeriv (curve t) (ν t)).ennreal_toReal.sqrt.sub
        (Measure.measurable_rnDeriv P (ν t)).ennreal_toReal.sqrt).sub
        ((measurable_const.mul hg).mul
          (Measure.measurable_rnDeriv P (ν t)).ennreal_toReal.sqrt)).aestronglyMeasurable
    have hgp : MemLp (fun ω => g ω * p ω) 2 (ν t) := by
      refine ⟨(hg.mul (Measure.measurable_rnDeriv P (ν t)).ennreal_toReal.sqrt)
        |>.aestronglyMeasurable, ?_⟩
      rw [show (fun ω => g ω * p ω) = fun ω => p ω * g ω by
        funext ω; ring]
      rw [eLpNorm_sqrt_rnDeriv_mul_eq hPν g]
      exact hgL2.2
    have hgpNorm : eLpNorm (fun ω => g ω * p ω) 2 (ν t) = eLpNorm g 2 P := by
      rw [show (fun ω => g ω * p ω) = fun ω => p ω * g ω by
        funext ω; ring]
      exact eLpNorm_sqrt_rnDeriv_mul_eq hPν g
    have hdiff : MemLp (fun ω => q ω - p ω) 2 (ν t) := hq.sub hp
    have hfun : (fun ω => q ω - p ω) =
        (t / 2) • (fun ω => g ω * p ω) + r t := by
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, p, q, r, residualAgainst]
      ring
    have htriE : eLpNorm (fun ω => q ω - p ω) 2 (ν t) ≤
        ‖t / 2‖ₑ * eLpNorm (fun ω => g ω * p ω) 2 (ν t) +
          eLpNorm (r t) 2 (ν t) := by
      calc
        eLpNorm (fun ω => q ω - p ω) 2 (ν t) =
            eLpNorm ((t / 2) • (fun ω => g ω * p ω) + r t) 2 (ν t) :=
          congrArg (fun f => eLpNorm f 2 (ν t)) hfun
        _ ≤ eLpNorm ((t / 2) • (fun ω => g ω * p ω)) 2 (ν t) +
            eLpNorm (r t) 2 (ν t) :=
          eLpNorm_add_le (hgp.1.const_smul (t / 2)) hr.1 (by norm_num)
        _ = ‖t / 2‖ₑ * eLpNorm (fun ω => g ω * p ω) 2 (ν t) +
            eLpNorm (r t) 2 (ν t) := by rw [eLpNorm_const_smul]
    have htri : H t ≤ t / 2 * G + R t := by
      have ha : ‖t / 2‖ₑ * eLpNorm (fun ω => g ω * p ω) 2 (ν t) ≠ ∞ :=
        ENNReal.mul_ne_top (by simp) hgp.2.ne
      have htop : ‖t / 2‖ₑ * eLpNorm (fun ω => g ω * p ω) 2 (ν t) +
          eLpNorm (r t) 2 (ν t) ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ha, hr.2.ne⟩
      have hle := ENNReal.toReal_mono htop htriE
      rw [ENNReal.toReal_add ha hr.2.ne, ENNReal.toReal_mul, hgpNorm] at hle
      simpa [H, p, q, G, R, Real.enorm_eq_ofReal, abs_of_pos htpos]
        using hle
    have hpSq : ∫ ω, p ω ^ 2 ∂(ν t) = 1 := by
      simpa [p] using
        (AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_sqrt_rnDeriv_sq hPν)
    have hqSq : ∫ ω, q ω ^ 2 ∂(ν t) = 1 := by
      simpa [q] using
        (AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_sqrt_rnDeriv_sq hQν)
    have hCbound : |C t| ≤ R t := by
      have hcs := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
        (ν t) hr hp
      rw [AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal hr,
        hpSq, Real.sqrt_one, mul_one] at hcs
      simpa [C, R, p] using hcs
    let A : ℝ := ∫ ω, q ω * p ω ∂(ν t)
    have hgpSq : ∫ ω, g ω * p ω ^ 2 ∂(ν t) = I := by
      have hpoint : (fun ω => g ω * p ω ^ 2) =
          fun ω => g ω * (P.rnDeriv (ν t) ω).toReal := by
        funext ω
        simp only [p, Real.sq_sqrt ENNReal.toReal_nonneg]
      rw [hpoint,
        ← AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
          hPν g]
    have hCeq : C t = A - 1 - (t / 2) * I := by
      have hqp := AsymptoticStatistics.L2Utils.integrable_mul_of_memLp_two (ν t) hq hp
      have hp2 := hp.integrable_sq
      have hgpp := AsymptoticStatistics.L2Utils.integrable_mul_of_memLp_two (ν t) hgp hp
      have hgp2 : Integrable (fun ω => g ω * p ω ^ 2) (ν t) := by
        convert hgpp using 1
        funext ω
        ring
      change ∫ ω, r t ω * p ω ∂(ν t) = _
      have heq : (fun ω => r t ω * p ω) =
          (fun ω => q ω * p ω) -
            ((fun ω => p ω ^ 2) + fun ω => (t / 2) * (g ω * p ω ^ 2)) := by
        funext ω
        simp only [Pi.sub_apply, Pi.add_apply, r, residualAgainst, p, q]
        ring
      rw [heq]
      calc
        integral (ν t) ((fun ω => q ω * p ω) -
            ((fun ω => p ω ^ 2) + fun ω => (t / 2) * (g ω * p ω ^ 2))) =
            ∫ ω, q ω * p ω ∂(ν t) -
              ∫ ω, p ω ^ 2 + (t / 2) * (g ω * p ω ^ 2) ∂(ν t) :=
          integral_sub hqp (hp2.add (hgp2.const_mul _))
        _ = A - 1 - (t / 2) * I := by
          rw [integral_add hp2 (hgp2.const_mul _), integral_const_mul, hpSq, hgpSq]
          dsimp [A]
          ring
    have hHsq : H t ^ 2 = 2 - 2 * A := by
      have hdiffSq := hdiff.integrable_sq
      have hqp := AsymptoticStatistics.L2Utils.integrable_mul_of_memLp_two (ν t) hq hp
      have hq2 := hq.integrable_sq
      have hp2 := hp.integrable_sq
      have heq : (fun ω => (q ω - p ω) ^ 2) =
          ((fun ω => q ω ^ 2) + fun ω => p ω ^ 2) -
            fun ω => 2 * (q ω * p ω) := by
        funext ω
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      have hint : ∫ ω, (q ω - p ω) ^ 2 ∂(ν t) = 2 - 2 * A := by
        rw [heq]
        calc
          integral (ν t) (((fun ω => q ω ^ 2) + fun ω => p ω ^ 2) -
              fun ω => 2 * (q ω * p ω)) =
              ∫ ω, q ω ^ 2 + p ω ^ 2 ∂(ν t) -
                ∫ ω, 2 * (q ω * p ω) ∂(ν t) :=
            integral_sub (hq2.add hp2) (hqp.const_mul _)
          _ = 2 - 2 * A := by
            rw [integral_add hq2 hp2, integral_const_mul, hqSq, hpSq]
            dsimp [A]
            ring
      have hsqrt :=
        AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal hdiff
      have hnn : 0 ≤ ∫ ω, (q ω - p ω) ^ 2 ∂(ν t) :=
        integral_nonneg fun _ => sq_nonneg _
      have hsquare : H t ^ 2 = ∫ ω, (q ω - p ω) ^ 2 ∂(ν t) := by
        change (eLpNorm (fun ω => q ω - p ω) 2 (ν t)).toReal ^ 2 = _
        rw [← hsqrt, Real.sq_sqrt hnn]
      rw [hsquare, hint]
    have hid : (t / 2) * I = -(H t ^ 2) / 2 - C t := by
      rw [hCeq, hHsq]
      ring
    have hraw : |I| / 2 ≤ H t ^ 2 / (2 * t) + |C t| / t := by
      have habs : |(t / 2) * I| ≤ H t ^ 2 / 2 + |C t| := by
        rw [hid]
        calc
          |-(H t ^ 2) / 2 - C t| ≤ |-(H t ^ 2) / 2| + |C t| := abs_sub _ _
          _ = H t ^ 2 / 2 + |C t| := by
            rw [abs_div, abs_neg, abs_sq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have := (div_le_div_iff_of_pos_right ht).mpr habs
      have hleft : |(t / 2) * I| / t = |I| / 2 := by
        rw [abs_mul, abs_of_pos (half_pos htpos)]
        field_simp [htpos.ne']
      have hright : (H t ^ 2 / 2 + |C t|) / t =
          H t ^ 2 / (2 * t) + |C t| / t := by ring
      rwa [hleft, hright] at this
    have hHnonneg : 0 ≤ H t := ENNReal.toReal_nonneg
    have hRnonneg : 0 ≤ R t := ENNReal.toReal_nonneg
    have hGnonneg : 0 ≤ G := ENNReal.toReal_nonneg
    calc
      |I| / 2 ≤ H t ^ 2 / (2 * t) + |C t| / t := hraw
      _ ≤ (t / 2 * G + R t) ^ 2 / (2 * t) + R t / t := by
        gcongr
      _ = t / 2 * (G / 2 + R t / t) ^ 2 + R t / t := by
        field_simp [htpos.ne']
  have hIle : |I| / 2 ≤ 0 := ge_of_tendsto hbound_zero hmain
  have hI : I = 0 := by
    have : |I| = 0 := by linarith [abs_nonneg I]
    exact abs_eq_zero.mp this
  have hmeanP : ∫ ω, g ω ∂P = 0 := by simpa [I] using hI
  let F : Lp ℝ 2 P := hgL2.toLp g
  have hF : F ∈ L2ZeroMean P := by
    change integralL2 P F = 0
    change @inner ℝ (Lp ℝ 2 P) _ (oneL2 P) F = 0
    rw [MeasureTheory.L2.inner_def]
    have h_one : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    have h_g : (F : Ω → ℝ) =ᵐ[P] g := MemLp.coeFn_toLp hgL2
    calc
      ∫ ω, @inner ℝ ℝ _ (((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω)
          ((F : Ω → ℝ) ω) ∂P =
          ∫ ω, g ω ∂P := by
        apply integral_congr_ae
        filter_upwards [h_one, h_g] with ω h1 hg'
        rw [h1, hg']
        change g ω * 1 = g ω
        exact mul_one _
      _ = 0 := hmeanP
  exact ⟨⟨F, hF⟩, (MemLp.coeFn_toLp hgL2).symm⟩

end AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic
