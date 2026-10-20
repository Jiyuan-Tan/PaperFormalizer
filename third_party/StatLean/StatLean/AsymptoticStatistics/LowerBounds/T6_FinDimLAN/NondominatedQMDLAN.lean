module
public import StatLean.AsymptoticStatistics.Core.NondominatedQMDProductComparison
public import StatLean.AsymptoticStatistics.ForMathlib.IidWLLN
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.Abstract1DLAN

@[expose] public section

/-! # Literal LAN from nondominated one-sided QMD (vdV Lemma 25.14) -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLAN

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.NondominatedQMDPath
open AsymptoticStatistics.Core.NondominatedQMDPath.NondominatedQMDPath
open AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The baseline-AC square-root residual is controlled by the canonical
pairwise residual.  The canonical norm additionally sees the singular part,
so only this direction is available without domination. -/
private theorem baseline_actualResidual_sq_le
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, (2 * (Real.sqrt ((γ.curve t).rnDeriv P ω).toReal - 1)
          - t * (γ.score : Ω → ℝ) ω) ^ 2 ∂P ≤
      4 * (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t))).toReal ^ 2 := by
  letI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  let μ := canonicalDominator P (γ.curve t)
  letI : SigmaFinite μ := by
    dsimp only [μ, canonicalDominator]
    infer_instance
  let p : Ω → ℝ≥0∞ := P.rnDeriv μ
  let q : Ω → ℝ≥0∞ := (γ.curve t).rnDeriv μ
  let L : Ω → ℝ≥0∞ := (γ.curve t).rnDeriv P
  let r : Ω → ℝ := γ.comparisonResidual t
  let D : Ω → ℝ := fun ω =>
    2 * (Real.sqrt (L ω).toReal - 1) - t * (γ.score : Ω → ℝ) ω
  have hPμ : P ≪ μ :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hscore_meas : Measurable (γ.score : Ω → ℝ) :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P)).measurable
  have hp : MemLp (fun ω => Real.sqrt (p ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv hPμ
  have hq : MemLp (fun ω => Real.sqrt (q ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
      (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))
  have hscore_weighted : MemLp
      (fun ω => (γ.score : Ω → ℝ) ω * Real.sqrt (p ω).toReal) 2 μ := by
    have hsquare : Integrable (fun ω => (γ.score : Ω → ℝ) ω ^ 2) P :=
      (Lp.memLp (γ.score : Lp ℝ 2 P)).integrable_sq
    have hprod : AEStronglyMeasurable
        (fun ω => (γ.score : Ω → ℝ) ω * Real.sqrt (p ω).toReal) μ :=
      hscore_meas.aestronglyMeasurable.mul
        (Measure.measurable_rnDeriv P μ).ennreal_toReal.sqrt.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hprod]
    have hP : P = μ.withDensity (P.rnDeriv μ) :=
      (Measure.withDensity_rnDeriv_eq P μ hPμ).symm
    have hi := MeasureTheory.integrable_withDensity_iff
      (Measure.measurable_rnDeriv P μ) (Measure.rnDeriv_lt_top P μ)
      (g := fun ω => (γ.score : Ω → ℝ) ω ^ 2)
    rw [← hP] at hi
    convert hi.mp hsquare using 1
    funext ω
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hr : MemLp r 2 μ := by
    change MemLp (fun ω => Real.sqrt (q ω).toReal - Real.sqrt (p ω).toReal -
      (t / 2) * (γ.score : Ω → ℝ) ω * Real.sqrt (p ω).toReal) 2 μ
    have hscaled := hscore_weighted.const_mul (t / 2)
    apply (hq.sub hp).sub
    exact MemLp.ae_eq (Filter.Eventually.of_forall fun ω => by ring) hscaled
  have hchainP : L * p =ᵐ[P] q := by
    simpa only [L, p, q] using
      (Measure.rnDeriv_mul_rnDeriv' (μ := γ.curve t) (ν := P) (κ := μ) hPμ)
  have hP_eq : μ.withDensity (P.rnDeriv μ) = P :=
    Measure.withDensity_rnDeriv_eq P μ hPμ
  have hchain : ∀ᵐ ω ∂μ, p ω ≠ 0 → L ω * p ω = q ω := by
    have h' : L * p =ᵐ[μ.withDensity (P.rnDeriv μ)] q := by
      simpa only [hP_eq] using hchainP
    simpa only [p] using!
      (ae_withDensity_iff (Measure.measurable_rnDeriv P μ)).mp h'
  have hLfinP : ∀ᵐ ω ∂P, L ω ≠ ⊤ := by
    simpa only [L] using Measure.rnDeriv_ne_top (γ.curve t) P
  have hLfin : ∀ᵐ ω ∂μ, p ω ≠ 0 → L ω ≠ ⊤ := by
    have h' : ∀ᵐ ω ∂(μ.withDensity (P.rnDeriv μ)), L ω ≠ ⊤ := by
      simpa only [hP_eq] using hLfinP
    simpa only [p] using
      (ae_withDensity_iff (Measure.measurable_rnDeriv P μ)).mp h'
  have hpoint : (fun ω => D ω ^ 2 * (p ω).toReal) ≤ᵐ[μ]
      fun ω => 4 * r ω ^ 2 := by
    filter_upwards [hchain, hLfin, Measure.rnDeriv_ne_top P μ,
      Measure.rnDeriv_ne_top (γ.curve t) μ] with ω hchainω hLω hpω hqω
    by_cases hp0 : p ω = 0
    · simp only [hp0, ENNReal.toReal_zero, mul_zero]
      positivity
    · have hprod : (q ω).toReal = (L ω).toReal * (p ω).toReal := by
        rw [← hchainω hp0, ENNReal.toReal_mul]
      have hsqrt : Real.sqrt (q ω).toReal =
          Real.sqrt (L ω).toReal * Real.sqrt (p ω).toReal := by
        rw [hprod, Real.sqrt_mul ENNReal.toReal_nonneg]
      have hrid : r ω = Real.sqrt (p ω).toReal *
          (Real.sqrt (L ω).toReal - 1 - (t / 2) * (γ.score : Ω → ℝ) ω) := by
        change Real.sqrt (q ω).toReal - Real.sqrt (p ω).toReal -
          (t / 2) * (γ.score : Ω → ℝ) ω * Real.sqrt (p ω).toReal = _
        rw [hsqrt]
        ring
      have hDid : D ω = 2 *
          (Real.sqrt (L ω).toReal - 1 - (t / 2) * (γ.score : Ω → ℝ) ω) := by
        simp only [D]
        ring
      have hpsq : Real.sqrt (p ω).toReal ^ 2 = (p ω).toReal :=
        Real.sq_sqrt ENNReal.toReal_nonneg
      rw [hrid, hDid]
      nlinarith [hpsq]
  rw [AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
    hPμ (fun ω => D ω ^ 2)]
  change (∫ ω, D ω ^ 2 * (p ω).toReal ∂μ) ≤ _
  calc
    (∫ ω, D ω ^ 2 * (p ω).toReal ∂μ) ≤ ∫ ω, 4 * r ω ^ 2 ∂μ :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)
        (hr.integrable_sq.const_mul 4) hpoint
    _ = 4 * ∫ ω, r ω ^ 2 ∂μ := integral_const_mul 4 (fun ω => r ω ^ 2)
    _ = _ := by
      have hsqrt :=
        AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal hr
      have hnonneg : 0 ≤ ∫ ω, r ω ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
      rw [← Real.sq_sqrt hnonneg, hsqrt]

private theorem baseline_actualResidual_memLp
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) :
    MemLp (fun ω =>
      2 * (Real.sqrt ((γ.curve t).rnDeriv P ω).toReal - 1)
        - t * (γ.score : Ω → ℝ) ω) 2 P := by
  letI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  have hsqrt : MemLp
      (fun ω => Real.sqrt ((γ.curve t).rnDeriv P ω).toReal) 2 P := by
    have hmeas : AEStronglyMeasurable
        (fun ω => Real.sqrt ((γ.curve t).rnDeriv P ω).toReal) P :=
      (Measure.measurable_rnDeriv
        (γ.curve t) P).ennreal_toReal.sqrt.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    convert Measure.integrable_toReal_rnDeriv (μ := γ.curve t) (ν := P) using 1
    funext ω
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hone : MemLp (fun _ : Ω => (1 : ℝ)) 2 P := memLp_const 1
  have hW : MemLp
      (fun ω => 2 * (Real.sqrt ((γ.curve t).rnDeriv P ω).toReal - 1)) 2 P :=
    (hsqrt.sub hone).const_mul 2
  have hg : MemLp (fun ω => t * (γ.score : Ω → ℝ) ω) 2 P :=
    (Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul t
  exact hW.sub hg

private theorem baseline_actualResidual_sq_isLittleO
    (γ : NondominatedQMDPath P) :
    (fun t : ℝ => ∫ ω,
      (2 * (Real.sqrt ((γ.curve t).rnDeriv P ω).toReal - 1)
        - t * (γ.score : Ω → ℝ) ω) ^ 2 ∂P)
      =o[nhdsWithin 0 (Set.Ioi 0)] (fun t => t ^ 2) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hqmd_real : Tendsto (fun t : ℝ =>
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal)
      l (nhds 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp γ.qmd_limit
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hqmd_bound : ∀ᶠ t : ℝ in l,
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal ^ 2 ≤
          c / 4 := by
    have hsqrt : 0 < Real.sqrt (c / 4) := Real.sqrt_pos.mpr (by positivity)
    have hevent := hqmd_real.eventually (Iio_mem_nhds hsqrt)
    filter_upwards [hevent] with t ht
    have hnonneg : 0 ≤
        (eLpNorm (γ.comparisonResidual t) 2
          (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal :=
      ENNReal.toReal_nonneg
    nlinarith [Real.sq_sqrt (show 0 ≤ c / 4 by positivity)]
  have hqmd_lt : ∀ᶠ t : ℝ in l,
      eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t < 1 :=
    γ.qmd_limit.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [self_mem_nhdsWithin, hqmd_bound, hqmd_lt] with t ht hbound hlt
  have htpos : 0 < t := ht
  have hnorm_fin : eLpNorm (γ.comparisonResidual t) 2
      (canonicalDominator P (γ.curve t)) ≠ ⊤ := by
    intro htop
    have hfalse : (⊤ : ℝ≥0∞) < 1 := by
      simpa only [htop, ENNReal.top_div, if_neg ENNReal.ofReal_ne_top] using hlt
    exact (not_lt_of_ge le_top hfalse).elim
  have hquot_eq :
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal =
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t))).toReal / t := by
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal htpos.le]
  rw [hquot_eq, div_pow] at hbound
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
  have hscaled := (div_le_iff₀ ht2).mp hbound
  rw [Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (baseline_actualResidual_sq_le γ t htpos.le).trans (by
    nlinarith [sq_nonneg
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t))).toReal])

private theorem integral_score_sq_eq_norm_sq (γ : NondominatedQMDPath P) :
    ∫ x, (γ.score : Ω → ℝ) x ^ 2 ∂P = ‖γ.score‖ ^ 2 := by
  have hself :
      (⟪(γ.score : Lp ℝ 2 P), (γ.score : Lp ℝ 2 P)⟫_ℝ : ℝ) =
        ‖(γ.score : Lp ℝ 2 P)‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [MeasureTheory.L2.inner_def] at hself
  have hpoint :
      (fun x => ⟪(γ.score : Ω → ℝ) x, (γ.score : Ω → ℝ) x⟫_ℝ) =ᵐ[P]
        fun x => (γ.score : Ω → ℝ) x ^ 2 := by
    filter_upwards with x
    change (γ.score : Ω → ℝ) x * (γ.score : Ω → ℝ) x = _
    ring
  rw [integral_congr_ae hpoint] at hself
  exact hself

/-- LAN for the logarithm of the actual baseline RN product likelihood.

Proof idea: at each `a≥0`, truncate the square-root likelihood expansion,
use the distinct baseline-zero-likelihood rate to justify `log`, and apply
iid LLN to the quadratic term; split `a=0` at the base point. No MGF or
uniform-integrability assumption is required. -/
theorem log_acProductLikelihood_lan_tendstoInMeasure
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X | ε ≤ |Real.log
              (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal
            - (a * (Real.sqrt n)⁻¹ *
                ∑ i : Fin n, (γ.score : Ω → ℝ) (X i)
              - (a ^ 2 / 2 : ℝ) * ‖γ.score‖ ^ 2)|})
      atTop (nhds 0) := by
  classical
  rcases ha.eq_or_lt with rfl | ha
  · intro ε hε
    have hzero : ∀ n : ℕ,
        (Measure.pi (fun _ : Fin n => P))
          {X | ε ≤ |Real.log (γ.acProductLikelihood 0 n X).toReal|} = 0 := by
      intro n
      have hpi : (fun (X : Fin n → Ω) i => (P.rnDeriv P (X i)).toReal) =ᵐ[
          Measure.pi (fun _ : Fin n => P)] fun _ _ => (1 : ℝ) := by
        exact Measure.ae_eq_pi (μ := fun _ : Fin n => P)
          (f := fun _ ω => (P.rnDeriv P ω).toReal)
          (f' := fun _ _ => (1 : ℝ)) (fun _ => by
            filter_upwards [Measure.rnDeriv_self P] with ω hω
            simp [hω])
      have hset : {X : Fin n → Ω |
          ε ≤ |Real.log (γ.acProductLikelihood 0 n X).toReal|} =ᵐ[
            Measure.pi (fun _ : Fin n => P)] (∅ : Set (Fin n → Ω)) := by
        filter_upwards [hpi] with X hX
        change (ε ≤ |Real.log (γ.acProductLikelihood 0 n X).toReal|) = False
        simp only [acProductLikelihood, curve_at_zero, ENNReal.toReal_prod]
        rw [show (∏ i : Fin n, (P.rnDeriv P (X i)).toReal) = 1 by
          simp [hX]]
        simp [not_le.mpr hε]
      simpa using measure_congr hset
    simp [hzero]
  · let u : ℕ → ℝ := fun n => a * (Real.sqrt n)⁻¹
    let W : ℕ → Ω → ℝ := fun n ω =>
      2 * (Real.sqrt ((γ.curve (u n)).rnDeriv P ω).toReal - 1)
    let D : ℕ → Ω → ℝ := fun n ω => W n ω - u n * (γ.score : Ω → ℝ) ω
    let I : ℝ := ∫ ω, (γ.score : Ω → ℝ) ω ^ 2 ∂P
    have hu_zero : Tendsto u atTop (nhds 0) := by
      have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      simpa only [u, mul_zero] using
        (tendsto_const_nhds.mul hsqrt.inv_tendsto_atTop :
          Tendsto (fun n : ℕ => a * (Real.sqrt n)⁻¹) atTop (nhds (a * 0)))
    have hu_pos : ∀ᶠ n : ℕ in atTop, 0 < u n := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact mul_pos ha (inv_pos.mpr (Real.sqrt_pos.mpr (by
        exact_mod_cast (show 0 < n by omega))))
    have hu_right : Tendsto u atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hu_zero, hu_pos⟩
    have hscale : ∀ᶠ n : ℕ in atTop, (n : ℝ) * u n ^ 2 = a ^ 2 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      dsimp only [u]
      rw [mul_pow]
      calc
        (n : ℝ) * (a ^ 2 * (Real.sqrt n)⁻¹ ^ 2) =
            a ^ 2 * ((n : ℝ) * (Real.sqrt n)⁻¹ ^ 2) := by ring
        _ = a ^ 2 := by
          rw [inv_pow, ← div_eq_mul_inv, Real.sq_sqrt hnpos.le, div_self hnpos.ne',
            mul_one]
    have hDsqO : (fun n => ∫ ω, D n ω ^ 2 ∂P) =o[atTop] fun n => u n ^ 2 := by
      simpa only [Function.comp_apply, D, W] using!
        (baseline_actualResidual_sq_isLittleO γ).comp_tendsto hu_right
    have hDscaled : Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, D n ω ^ 2 ∂P)
        atTop (nhds 0) := by
      have hmul : (fun n : ℕ => (n : ℝ) * ∫ ω, D n ω ^ 2 ∂P) =o[atTop]
          (fun n : ℕ => (n : ℝ) * u n ^ 2) :=
        (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO hDsqO
      have hscaleO : (fun n : ℕ => (n : ℝ) * u n ^ 2) =O[atTop]
          (fun _ : ℕ => (1 : ℝ)) :=
        (Filter.EventuallyEq.isBigO hscale).trans
          (Asymptotics.isBigO_const_one ℝ (a ^ 2) atTop)
      exact (Asymptotics.isLittleO_one_iff ℝ).mp (hmul.trans_isBigO hscaleO)
    have hW_mem : ∀ n, MemLp (W n) 2 P := by
      intro n
      have hu_nn : 0 ≤ u n := mul_nonneg ha.le (inv_nonneg.mpr (Real.sqrt_nonneg _))
      have hD := baseline_actualResidual_memLp γ (u n) hu_nn
      have hg := (Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul (u n)
      have hsum := hD.add hg
      convert hsum using 1
      funext ω
      simp only [Pi.add_apply]
      ring
    have hD_mem : ∀ n, MemLp (D n) 2 P := by
      intro n
      exact (hW_mem n).sub ((Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul (u n))
    have hFsq : Tendsto (fun n : ℕ => ∫ ω,
        (Real.sqrt n * W n ω - a * (γ.score : Ω → ℝ) ω) ^ 2 ∂P)
        atTop (nhds 0) := by
      apply hDscaled.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
      have hsu : Real.sqrt n * u n = a := by
        dsimp only [u]
        calc
          Real.sqrt n * (a * (Real.sqrt n)⁻¹) =
              a * (Real.sqrt n * (Real.sqrt n)⁻¹) := by ring
          _ = a := by rw [mul_inv_cancel₀ hsqrtpos.ne', mul_one]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      have hsquare : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
      calc
        (n : ℝ) * D n ω ^ 2 = Real.sqrt n ^ 2 * D n ω ^ 2 := by rw [hsquare]
        _ = (Real.sqrt n * D n ω) ^ 2 := by ring
        _ = (Real.sqrt n * W n ω - a * (γ.score : Ω → ℝ) ω) ^ 2 := by
          congr 1
          simp only [D]
          calc
            Real.sqrt n * (W n ω - u n * (γ.score : Ω → ℝ) ω) =
                Real.sqrt n * W n ω -
                  (Real.sqrt n * u n) * (γ.score : Ω → ℝ) ω := by ring
            _ = _ := by rw [hsu]
    have hgscaled : MemLp (fun ω => a * (γ.score : Ω → ℝ) ω) 2 P :=
      (Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul a
    have hFmem : ∀ n : ℕ, MemLp
        (fun ω => Real.sqrt n * W n ω - a * (γ.score : Ω → ℝ) ω) 2 P :=
      fun n => (hW_mem n).const_mul (Real.sqrt n) |>.sub hgscaled
    have hnsqW : Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, W n ω ^ 2 ∂P)
        atTop (nhds (a ^ 2 * I)) := by
      have hsquares := AsymptoticStatistics.L2Utils.tendsto_integral_sq_of_tendsto_integral_diff_sq
        P hgscaled (Filter.Eventually.of_forall hFmem) hFsq
      have htarget : ∫ ω, (a * (γ.score : Ω → ℝ) ω) ^ 2 ∂P = a ^ 2 * I := by
        simp only [mul_pow, I]
        rw [integral_const_mul]
      rw [htarget] at hsquares
      apply hsquares.congr'
      filter_upwards with n
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    have hmeanW : Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, W n ω ∂P)
        atTop (nhds (-(a ^ 2 / 4) * I)) := by
      have hsing := γ.singular_mass_localScale_tendsto a ha.le
      have hsing_real : Tendsto
          (fun n : ℕ => (n : ℝ) * (γ.singularMass (u n)).toReal) atTop (nhds 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsing
        convert this using 1
        · funext n
          simp only [Function.comp_apply, ENNReal.toReal_mul, ENNReal.toReal_natCast, u]
        · simp
      have hidentity : ∀ n : ℕ,
          ∫ ω, W n ω ∂P =
            -(1 / 4 : ℝ) * ∫ ω, W n ω ^ 2 ∂P - (γ.singularMass (u n)).toReal := by
        intro n
        letI : IsProbabilityMeasure (γ.curve (u n)) := γ.curve_isProbability (u n)
          (mul_nonneg ha.le (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        have hL_int : Integrable
            (fun ω => ((γ.curve (u n)).rnDeriv P ω).toReal) P :=
          Measure.integrable_toReal_rnDeriv
        have hW_int := (hW_mem n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        have hWsq_int := (hW_mem n).integrable_sq
        have hpoint : ∀ ω, W n ω = -(1 / 4 : ℝ) * W n ω ^ 2 +
            ((γ.curve (u n)).rnDeriv P ω).toReal - 1 := by
          intro ω
          have hs := Real.sq_sqrt
            (show 0 ≤ ((γ.curve (u n)).rnDeriv P ω).toReal from ENNReal.toReal_nonneg)
          dsimp only [W]
          nlinarith
        calc
          ∫ ω, W n ω ∂P = ∫ ω, (-(1 / 4 : ℝ) * W n ω ^ 2 +
              ((γ.curve (u n)).rnDeriv P ω).toReal - 1) ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall hpoint)
          _ = -(1 / 4 : ℝ) * ∫ ω, W n ω ^ 2 ∂P +
              ∫ ω, ((γ.curve (u n)).rnDeriv P ω).toReal ∂P - 1 := by
            calc
              ∫ ω, (-(1 / 4 : ℝ) * W n ω ^ 2 +
                  ((γ.curve (u n)).rnDeriv P ω).toReal - 1) ∂P =
                  (∫ ω, (-(1 / 4 : ℝ) * W n ω ^ 2 +
                    ((γ.curve (u n)).rnDeriv P ω).toReal) ∂P) -
                    ∫ _ : Ω, (1 : ℝ) ∂P :=
                integral_sub ((hWsq_int.const_mul _).add hL_int) (integrable_const 1)
              _ = (∫ ω, -(1 / 4 : ℝ) * W n ω ^ 2 ∂P) +
                    ∫ ω, ((γ.curve (u n)).rnDeriv P ω).toReal ∂P -
                    ∫ _ : Ω, (1 : ℝ) ∂P := by
                rw [integral_add (hWsq_int.const_mul _) hL_int]
              _ = _ := by
                rw [integral_const_mul, integral_const]
                simp
          _ = _ := by
            rw [show ∫ ω, ((γ.curve (u n)).rnDeriv P ω).toReal ∂P =
                1 - (γ.singularMass (u n)).toReal by
              simpa only [singularMass, singularPart, measureReal_def, measure_univ,
                ENNReal.toReal_one] using
                (Measure.integral_toReal_rnDeriv' (μ := γ.curve (u n)) (ν := P))]
            ring
      have hmain := (hnsqW.const_mul (-(1 / 4 : ℝ))).sub hsing_real
      convert hmain using 1
      · funext n
        rw [hidentity]
        ring
      · ring_nf
    let A : ∀ n : ℕ, (Fin n → Ω) → ℝ := fun n X =>
      (∑ i : Fin n, D n (X i)) - (n : ℝ) * ∫ ω, D n ω ∂P
    have hA : ∀ ε > 0, Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
          {X | ε ≤ |A n X|}) atTop (nhds 0) := by
      intro ε hε
      have hmem : ∀ n, MemLp (A n) 2 (Measure.pi (fun _ : Fin n => P)) := by
        intro n
        have hcoord : ∀ i : Fin n, MemLp (fun X : Fin n → Ω => D n (X i)) 2
            (Measure.pi (fun _ : Fin n => P)) := fun i =>
          (hD_mem n).comp_measurePreserving (measurePreserving_eval _ i)
        have hsum : MemLp (fun X : Fin n → Ω => ∑ i : Fin n, D n (X i)) 2
            (Measure.pi (fun _ : Fin n => P)) := by
          simpa only using MeasureTheory.memLp_finset_sum Finset.univ fun i _ => hcoord i
        exact hsum.sub (memLp_const _)
      have hmean : ∀ n, ∫ X, A n X ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
        intro n
        have hDint := (hD_mem n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        have hcoordint : ∀ i : Fin n, Integrable
            (fun X : Fin n → Ω => D n (X i)) (Measure.pi (fun _ : Fin n => P)) :=
          fun i => MeasureTheory.integrable_comp_eval hDint
        have hcoordval : ∀ i : Fin n,
            ∫ X : Fin n → Ω, D n (X i) ∂(Measure.pi (fun _ : Fin n => P)) =
              ∫ ω, D n ω ∂P := fun i =>
          MeasureTheory.integral_comp_eval (μ := fun _ : Fin n => P) (i := i)
            (hD_mem n).aestronglyMeasurable
        dsimp only [A]
        rw [integral_sub (integrable_finset_sum Finset.univ fun i _ => hcoordint i)
          (integrable_const _), integral_finset_sum _ fun i _ => hcoordint i]
        simp_rw [hcoordval]
        simp [integral_const]
      have hvarle : ∀ n, variance (A n) (Measure.pi (fun _ : Fin n => P)) ≤
          (n : ℝ) * ∫ ω, D n ω ^ 2 ∂P := by
        intro n
        have hsum_meas : AEStronglyMeasurable
            (fun X : Fin n → Ω => ∑ i : Fin n, D n (X i))
            (Measure.pi (fun _ : Fin n => P)) := by
          exact Finset.aestronglyMeasurable_fun_sum Finset.univ
            (fun i _ => ((hD_mem n).comp_measurePreserving
              (measurePreserving_eval _ i)).aestronglyMeasurable)
        rw [show A n = fun X => (∑ i : Fin n, D n (X i)) -
            (n : ℝ) * ∫ ω, D n ω ∂P by rfl,
          variance_sub_const hsum_meas]
        rw [show (fun X : Fin n → Ω => ∑ i : Fin n, D n (X i)) =
            ∑ i : Fin n, fun X => D n (X i) by funext X; simp [Finset.sum_apply],
          variance_sum_pi (fun _ : Fin n => hD_mem n)]
        have hv : variance (D n) P ≤ ∫ ω, D n ω ^ 2 ∂P :=
          variance_le_expectation_sq (hD_mem n).aestronglyMeasurable
        simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using
          mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg n)
      have hbound : Tendsto (fun n : ℕ => ENNReal.ofReal
          (((n : ℝ) * ∫ ω, D n ω ^ 2 ∂P) / ε ^ 2)) atTop (nhds 0) := by
        have hr := (hDscaled.div_const (ε ^ 2))
        have hr' : Tendsto
            (fun n : ℕ => ((n : ℝ) * ∫ ω, D n ω ^ 2 ∂P) / ε ^ 2)
            atTop (nhds 0) := by simpa using hr
        have hc := (ENNReal.continuous_ofReal.tendsto 0).comp hr'
        simpa using! hc
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hbound (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards with n
      have hc := meas_ge_le_variance_div_sq (hmem n) hε
      rw [hmean n] at hc
      have hc' : (Measure.pi (fun _ : Fin n => P)) {X | ε ≤ |A n X|} ≤
          ENNReal.ofReal (variance (A n) (Measure.pi (fun _ : Fin n => P)) / ε ^ 2) := by
        simpa only [sub_zero, Real.norm_eq_abs] using hc
      exact hc'.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (hvarle n) (sq_nonneg _)))
    let F : ℕ → Ω → ℝ := fun n ω =>
      Real.sqrt n * W n ω - a * (γ.score : Ω → ℝ) ω
    let G : ℕ → Ω → ℝ := fun n ω =>
      Real.sqrt n * W n ω + a * (γ.score : Ω → ℝ) ω
    have hGmem : ∀ n, MemLp (G n) 2 P := fun n =>
      ((hW_mem n).const_mul (Real.sqrt n)).add hgscaled
    have hGsqBound : ∀ n, ∫ ω, G n ω ^ 2 ∂P ≤
        2 * ∫ ω, F n ω ^ 2 ∂P + 8 * a ^ 2 * I := by
      intro n
      have hmajor : Integrable (fun ω => 2 * F n ω ^ 2 +
          8 * (a * (γ.score : Ω → ℝ) ω) ^ 2) P :=
        ((hFmem n).integrable_sq.const_mul 2).add (hgscaled.integrable_sq.const_mul 8)
      have hle : (∫ ω, G n ω ^ 2 ∂P) ≤
          ∫ ω, 2 * F n ω ^ 2 + 8 * (a * (γ.score : Ω → ℝ) ω) ^ 2 ∂P :=
        integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        hmajor (Filter.Eventually.of_forall fun ω => by
          have hrel : G n ω = F n ω + 2 * (a * (γ.score : Ω → ℝ) ω) := by
            dsimp only [F, G]
            ring
          change G n ω ^ 2 ≤
            2 * F n ω ^ 2 + 8 * (a * (γ.score : Ω → ℝ) ω) ^ 2
          rw [hrel]
          nlinarith [sq_nonneg
            (F n ω - 2 * (a * (γ.score : Ω → ℝ) ω))])
      calc
        ∫ ω, G n ω ^ 2 ∂P ≤
            ∫ ω, 2 * F n ω ^ 2 + 8 * (a * (γ.score : Ω → ℝ) ω) ^ 2 ∂P := hle
        _ = 2 * ∫ ω, F n ω ^ 2 ∂P + 8 * a ^ 2 * I := by
          rw [integral_add ((hFmem n).integrable_sq.const_mul 2)
            (hgscaled.integrable_sq.const_mul 8), integral_const_mul,
            integral_const_mul]
          simp only [mul_pow, I]
          rw [integral_const_mul]
          ring
    have hL1 : Tendsto (fun n : ℕ => ∫ ω,
        |(n : ℝ) * W n ω ^ 2 - a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2| ∂P)
        atTop (nhds 0) := by
      have hFsqF : Tendsto (fun n => ∫ ω, F n ω ^ 2 ∂P) atTop (nhds 0) := by
        simpa only [F] using hFsq
      have hFroot : Tendsto (fun n => Real.sqrt (∫ ω, F n ω ^ 2 ∂P))
          atTop (nhds 0) := by
        simpa only [Real.sqrt_zero] using! (Real.continuous_sqrt.tendsto 0).comp hFsqF
      have hGbd : ∀ᶠ n : ℕ in atTop, ∫ ω, G n ω ^ 2 ∂P ≤ 2 + 8 * a ^ 2 * I := by
        have hev := hFsqF.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
        filter_upwards [hev] with n hn
        exact (hGsqBound n).trans (by linarith)
      have hGroot_bd : ∀ᶠ n : ℕ in atTop,
          Real.sqrt (∫ ω, G n ω ^ 2 ∂P) ≤
            Real.sqrt (2 + 8 * a ^ 2 * I) := by
        filter_upwards [hGbd] with n hn
        exact Real.sqrt_le_sqrt hn
      have hprod : Tendsto (fun n =>
          Real.sqrt (∫ ω, F n ω ^ 2 ∂P) * Real.sqrt (∫ ω, G n ω ^ 2 ∂P))
          atTop (nhds 0) := by
        refine squeeze_zero'
          (g := fun n => Real.sqrt (∫ ω, F n ω ^ 2 ∂P) *
            Real.sqrt (2 + 8 * a ^ 2 * I)) ?_ ?_ ?_
        · filter_upwards with n
          exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · filter_upwards [hGroot_bd] with n hn
          exact mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)
        · simpa only [zero_mul] using
            hFroot.mul_const (Real.sqrt (2 + 8 * a ^ 2 * I))
      refine squeeze_zero'
        (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
        ?_ hprod
      filter_upwards with n
      have hcs := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq P
        (hFmem n).norm (hGmem n).norm
      have hpoint : (fun ω => |F n ω| * |G n ω|) =
          fun ω => |(n : ℝ) * W n ω ^ 2 -
            a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2| := by
        funext ω
        rw [← abs_mul]
        have hsquare : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
        dsimp only [F, G]
        congr 1
        nlinarith
      rw [← hpoint]
      have hnonneg : 0 ≤ ∫ ω, |F n ω| * |G n ω| ∂P :=
        integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hcs' : ∫ ω, |F n ω| * |G n ω| ∂P ≤
          Real.sqrt (∫ ω, F n ω ^ 2 ∂P) *
            Real.sqrt (∫ ω, G n ω ^ 2 ∂P) := by
        rw [← abs_of_nonneg hnonneg]
        simpa only [Real.norm_eq_abs, abs_abs, sq_abs] using hcs
      exact hcs'
    let Δ : ℕ → Ω → ℝ := fun n ω =>
      (n : ℝ) * W n ω ^ 2 - a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2
    have hΔint : ∀ n, Integrable (Δ n) P := by
      intro n
      exact ((hW_mem n).integrable_sq.const_mul (n : ℝ)).sub
        ((Lp.memLp (γ.score : Lp ℝ 2 P)).integrable_sq.const_mul (a ^ 2))
    let E : ∀ n : ℕ, (Fin n → Ω) → ℝ := fun n X =>
      (n : ℝ)⁻¹ * ∑ i : Fin n, Δ n (X i)
    have hEint : ∀ n, Integrable (E n) (Measure.pi (fun _ : Fin n => P)) := by
      intro n
      exact (integrable_finset_sum Finset.univ fun i _ =>
        MeasureTheory.integrable_comp_eval (hΔint n)).const_mul _
    have hEabs : ∀ n, ∫ X, |E n X| ∂(Measure.pi (fun _ : Fin n => P)) ≤
        ∫ ω, |Δ n ω| ∂P := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [E, Nat.cast_zero, inv_zero, zero_mul, Finset.univ_eq_empty,
          Finset.sum_empty, abs_zero, integral_zero]
        exact integral_nonneg fun _ => abs_nonneg _
      · have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
        have hpoint : ∀ X : Fin n → Ω,
            |E n X| ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, |Δ n (X i)| := by
          intro X
          dsimp only [E]
          rw [abs_mul, abs_of_pos (inv_pos.mpr hnR)]
          exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
            (inv_nonneg.mpr hnR.le)
        have hsumabs : Integrable (fun X : Fin n → Ω =>
            ∑ i : Fin n, |Δ n (X i)|) (Measure.pi (fun _ : Fin n => P)) :=
          integrable_finset_sum Finset.univ fun i _ =>
            MeasureTheory.integrable_comp_eval (μ := fun _ : Fin n => P) (i := i)
              (hΔint n).abs
        calc
          ∫ X, |E n X| ∂(Measure.pi (fun _ : Fin n => P)) ≤
              ∫ X, (n : ℝ)⁻¹ * ∑ i : Fin n, |Δ n (X i)|
                ∂(Measure.pi (fun _ : Fin n => P)) :=
            integral_mono (hEint n).abs (hsumabs.const_mul _) hpoint
          _ = (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, |Δ n ω| ∂P := by
            rw [integral_const_mul]
            congr 1
            calc
              ∫ X : Fin n → Ω, ∑ i : Fin n, |Δ n (X i)|
                  ∂(Measure.pi (fun _ : Fin n => P)) =
                  ∑ i : Fin n, ∫ X : Fin n → Ω, |Δ n (X i)|
                    ∂(Measure.pi (fun _ : Fin n => P)) :=
                integral_finset_sum Finset.univ fun i _ =>
                  MeasureTheory.integrable_comp_eval (μ := fun _ : Fin n => P) (i := i)
                    (hΔint n).abs
              _ = ∑ i : Fin n, ∫ ω, |Δ n ω| ∂P := by
                apply Finset.sum_congr rfl
                intro i hi
                exact MeasureTheory.integral_comp_eval (μ := fun _ : Fin n => P) (i := i)
                  (hΔint n).abs.aestronglyMeasurable
          _ = ∫ ω, |Δ n ω| ∂P := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, ← mul_assoc,
              inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_mul]
    have hE : ∀ ε > 0, Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)) {X | ε ≤ |E n X|})
        atTop (nhds 0) := by
      intro ε hε
      have hupper : Tendsto (fun n : ℕ => ENNReal.ofReal
          ((∫ ω, |Δ n ω| ∂P) / ε)) atTop (nhds 0) := by
        have hr : Tendsto (fun n : ℕ => (∫ ω, |Δ n ω| ∂P) / ε)
            atTop (nhds 0) := by
          simpa only [Δ, zero_div] using hL1.div_const ε
        simpa using! (ENNReal.continuous_ofReal.tendsto 0).comp hr
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
        (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards with n
      have hmark := mul_meas_ge_le_integral_of_nonneg
        (μ := Measure.pi (fun _ : Fin n => P)) (f := fun X => |E n X|)
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hEint n).abs ε
      have hreal : (Measure.pi (fun _ : Fin n => P)).real {X | ε ≤ |E n X|} ≤
          (∫ ω, |Δ n ω| ∂P) / ε := by
        apply (le_div_iff₀' hε).2
        exact hmark.trans (hEabs n)
      rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _)
        ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal]
      · exact hreal
      · exact div_nonneg (integral_nonneg fun _ => abs_nonneg _) hε.le
    have hscore2int : Integrable
        (fun ω => a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2) P :=
      (Lp.memLp (γ.score : Lp ℝ 2 P)).integrable_sq.const_mul _
    have hLLN := AsymptoticStatistics.iid_lln_in_prob_l1
      (P := P) (fun ω => a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2) hscore2int
    have hmeanScore2 : ∫ ω, a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2 ∂P =
        a ^ 2 * I := by rw [integral_const_mul]
    have hB : ∀ ε > 0, Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
          {X | ε ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|})
        atTop (nhds 0) := by
      intro ε hε
      let δ := ε / 2
      have hδ : 0 < δ := by dsimp only [δ]; positivity
      have hlln := hLLN δ hδ
      rw [hmeanScore2] at hlln
      have herr := hE δ hδ
      have hsum : Tendsto (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P))
              {X | δ ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n,
                a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 - a ^ 2 * I|} +
            (Measure.pi (fun _ : Fin n => P)) {X | δ ≤ |E n X|})
          atTop (nhds 0) := by
        simpa using hlln.add herr
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hsum (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hdecomp : ∀ X : Fin n → Ω,
          ∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I =
            ((n : ℝ)⁻¹ * ∑ i : Fin n,
                a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 - a ^ 2 * I) + E n X := by
        intro X
        dsimp only [E, Δ]
        have hpt : ∀ i : Fin n,
            a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 +
              ((n : ℝ) * W n (X i) ^ 2 -
                a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2) =
              (n : ℝ) * W n (X i) ^ 2 := by intro i; ring
        calc
          ∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I =
              ((n : ℝ)⁻¹ * ∑ i : Fin n,
                a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 +
                (n : ℝ)⁻¹ * ∑ i : Fin n,
                  ((n : ℝ) * W n (X i) ^ 2 -
                    a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2)) - a ^ 2 * I := by
            congr 1
            rw [← mul_add, ← Finset.sum_add_distrib]
            simp_rw [hpt]
            rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hnpos.ne', one_mul]
          _ = _ := by ring
      have hincl : {X : Fin n → Ω |
          ε ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|} ⊆
          {X | δ ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n,
            a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 - a ^ 2 * I|} ∪
          {X | δ ≤ |E n X|} := by
        intro X hX
        rw [Set.mem_union]
        by_contra hnot
        rw [not_or] at hnot
        have h1 : |(n : ℝ)⁻¹ * ∑ i : Fin n,
            a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 - a ^ 2 * I| < δ := by
          simpa only [Set.mem_setOf_eq, not_le] using hnot.1
        have h2 : |E n X| < δ := by
          simpa only [Set.mem_setOf_eq, not_le] using hnot.2
        rw [Set.mem_setOf_eq, hdecomp X] at hX
        have ht := abs_add_le
          ((n : ℝ)⁻¹ * ∑ i : Fin n,
            a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 - a ^ 2 * I) (E n X)
        dsimp only [δ] at h1 h2
        linarith
      exact (measure_mono hincl).trans (measure_union_le _ _)
    have hW_meas : ∀ n, Measurable (W n) := by
      intro n
      exact measurable_const.mul
        ((Measure.measurable_rnDeriv (γ.curve (u n)) P).ennreal_toReal.sqrt.sub
          measurable_const)
    have hI_nonneg : 0 ≤ I := integral_nonneg fun _ => sq_nonneg _
    have hDsq0 : Tendsto (fun n => ∫ ω, D n ω ^ 2 ∂P) atTop (nhds 0) := by
      have hu2 : Tendsto (fun n => u n ^ 2) atTop (nhds 0) := by
        convert hu_zero.pow 2 using 1
        norm_num
      exact hDsqO.isBigO.trans_tendsto hu2
    have hWsq0 : Tendsto (fun n => ∫ ω, W n ω ^ 2 ∂P) atTop (nhds 0) := by
      have hupper : Tendsto (fun n =>
          2 * ∫ ω, D n ω ^ 2 ∂P + 2 * u n ^ 2 * I) atTop (nhds 0) := by
        have hu2 := hu_zero.pow 2
        simpa [mul_assoc] using
          (hDsq0.const_mul 2).add ((hu2.const_mul 2).mul_const I)
      refine squeeze_zero' (g := fun n =>
          2 * ∫ ω, D n ω ^ 2 ∂P + 2 * u n ^ 2 * I)
        (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_ hupper
      filter_upwards with n
      have hmajor : Integrable (fun ω =>
          2 * D n ω ^ 2 + 2 * (u n * (γ.score : Ω → ℝ) ω) ^ 2) P :=
        ((hD_mem n).integrable_sq.const_mul 2).add
          (((Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul (u n)).integrable_sq.const_mul 2)
      calc
        ∫ ω, W n ω ^ 2 ∂P ≤
            ∫ ω, 2 * D n ω ^ 2 +
              2 * (u n * (γ.score : Ω → ℝ) ω) ^ 2 ∂P := by
          apply integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => sq_nonneg _) hmajor
          filter_upwards with ω
          have hrel : W n ω = D n ω + u n * (γ.score : Ω → ℝ) ω := by
            dsimp only [D]
            ring
          rw [hrel]
          nlinarith [sq_nonneg (D n ω - u n * (γ.score : Ω → ℝ) ω)]
        _ = 2 * ∫ ω, D n ω ^ 2 ∂P + 2 * u n ^ 2 * I := by
          rw [integral_add ((hD_mem n).integrable_sq.const_mul 2)
            (((Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul (u n)).integrable_sq.const_mul 2),
            integral_const_mul, integral_const_mul]
          simp only [mul_pow, I, integral_const_mul]
          ring
    have htailO : ∀ δ > 0,
        (fun n : ℕ => P.real {ω | δ ≤ |W n ω|}) =o[atTop] (fun n => u n ^ 2) := by
      intro δ hδ
      have hpack := AsymptoticStatistics.L2Utils.l2_tail_controls_of_approx
        atTop P W D (fun n ω => u n * (γ.score : Ω → ℝ) ω) u
        (fun ω => (γ.score : Ω → ℝ) ω ^ 2)
        hW_meas (Filter.Eventually.of_forall hW_mem) hWsq0
        (Filter.Eventually.of_forall hD_mem) hDsqO
        (Lp.memLp (γ.score : Lp ℝ 2 P)).integrable_sq
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (fun n => mul_nonneg ha.le (inv_nonneg.mpr (Real.sqrt_nonneg n)))
        (fun n ω => by dsimp only [D]; ring)
        (fun n ω => by simp only [mul_pow]; exact le_rfl)
        (fun _ => (0 : ℝ)) MemLp.zero δ hδ
      exact hpack.2.2.1
    have htailScaled : ∀ δ > 0, Tendsto
        (fun n : ℕ => (n : ℝ) * P.real {ω | δ ≤ |W n ω|})
        atTop (nhds 0) := by
      intro δ hδ
      have hmul : (fun n : ℕ => (n : ℝ) * P.real {ω | δ ≤ |W n ω|})
          =o[atTop] (fun n => (n : ℝ) * u n ^ 2) :=
        (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO
          (htailO δ hδ)
      have hscaleO : (fun n : ℕ => (n : ℝ) * u n ^ 2) =O[atTop]
          (fun _ : ℕ => (1 : ℝ)) :=
        (Filter.EventuallyEq.isBigO hscale).trans
          (Asymptotics.isBigO_const_one ℝ (a ^ 2) atTop)
      exact (Asymptotics.isLittleO_one_iff ℝ).mp (hmul.trans_isBigO hscaleO)
    have hMax : ∀ δ > 0, Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
          (⋃ i ∈ (Finset.univ : Finset (Fin n)), {X | δ ≤ |W n (X i)|}))
        atTop (nhds 0) := by
      intro δ hδ
      have hsingle : Tendsto (fun n : ℕ => ENNReal.ofReal
          ((n : ℝ) * P.real {ω | δ ≤ |W n ω|})) atTop (nhds 0) := by
        simpa only [Function.comp_apply, ENNReal.ofReal_zero] using!
          (ENNReal.continuous_ofReal.tendsto 0).comp (htailScaled δ hδ)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hsingle (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards with n
      have hset : MeasurableSet {ω | δ ≤ |W n ω|} :=
        measurableSet_le measurable_const ((hW_meas n).abs)
      have heach : ∀ i : Fin n,
          (Measure.pi (fun _ : Fin n => P)) {X | δ ≤ |W n (X i)|} =
            P {ω | δ ≤ |W n ω|} := by
        intro i
        rw [show {X : Fin n → Ω | δ ≤ |W n (X i)|} =
            (fun X : Fin n → Ω => X i) ⁻¹' {ω | δ ≤ |W n ω|} by rfl,
          ← Measure.map_apply (measurable_pi_apply i) hset,
          (measurePreserving_eval (fun _ : Fin n => P) i).map_eq]
      calc
        (Measure.pi (fun _ : Fin n => P))
            (⋃ i ∈ (Finset.univ : Finset (Fin n)), {X | δ ≤ |W n (X i)|}) ≤
            ∑ i ∈ (Finset.univ : Finset (Fin n)),
              (Measure.pi (fun _ : Fin n => P)) {X | δ ≤ |W n (X i)|} :=
          measure_biUnion_finset_le _ _
        _ = (n : ℕ) • P {ω | δ ≤ |W n ω|} := by simp only [heach,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ = ENNReal.ofReal ((n : ℝ) * P.real {ω | δ ≤ |W n ω|}) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_toReal (measure_ne_top P _),
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
          rfl
    let R : ℝ → ℝ := AsymptoticStatistics.ForMathlib.logTaylorRemainder
    have hC : ∀ ε > 0, Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
          {X | ε ≤ |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))|})
        atTop (nhds 0) := by
      intro ε hε
      let Mbd : ℝ := a ^ 2 * I + 1
      have hMbd : 0 < Mbd := by dsimp only [Mbd]; positivity
      let ε' : ℝ := ε / (2 * Mbd)
      have hε' : 0 < ε' := by dsimp only [ε']; positivity
      obtain ⟨η, hη, hR⟩ := Metric.tendsto_nhds_nhds.mp
        AsymptoticStatistics.ForMathlib.logTaylorRemainder_tendsto_zero ε' hε'
      have hηtwo : 0 < η / 2 := by positivity
      have hmax := hMax (η / 2) hηtwo
      have hb := hB 1 one_pos
      have hsum : Tendsto (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P))
              (⋃ i ∈ (Finset.univ : Finset (Fin n)), {ω | η / 2 ≤ |W n (ω i)|}) +
            (Measure.pi (fun _ : Fin n => P))
              {X | 1 ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|})
          atTop (nhds 0) := by
        simpa using hmax.add hb
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hsum (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards with n
      have hincl : {X : Fin n → Ω |
          ε ≤ |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))|} ⊆
          (⋃ i ∈ (Finset.univ : Finset (Fin n)), {X | η / 2 ≤ |W n (X i)|}) ∪
            {X | 1 ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|} := by
        intro X hX
        rw [Set.mem_union]
        by_contra hnot
        rw [not_or] at hnot
        have hsmall : ∀ i : Fin n, |W n (X i)| < η / 2 := by
          intro i
          have hi : ¬ X ∈ {X : Fin n → Ω | η / 2 ≤ |W n (X i)|} := by
            intro hi
            exact hnot.1 (Set.mem_biUnion (Finset.mem_univ i) hi)
          simpa only [Set.mem_setOf_eq, not_le] using hi
        have hBlt : ∑ i : Fin n, W n (X i) ^ 2 < Mbd := by
          have hb' : |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I| < 1 := by
            simpa only [Set.mem_setOf_eq, not_le] using hnot.2
          have hab := abs_lt.mp hb'
          dsimp only [Mbd]
          linarith [hab.2]
        have hRsmall : ∀ i : Fin n, |R (W n (X i))| < ε' := by
          intro i
          have hw : |W n (X i)| < η := lt_trans (hsmall i) (by linarith)
          have hd : dist (W n (X i)) (0 : ℝ) < η := by
            simpa only [dist_zero_right, Real.norm_eq_abs] using hw
          have := hR hd
          simpa only [R, dist_zero_right, Real.norm_eq_abs] using this
        have hsummand : ∀ i : Fin n,
            |W n (X i) ^ 2 * R (W n (X i))| ≤ W n (X i) ^ 2 * ε' := by
          intro i
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          exact mul_le_mul_of_nonneg_left (hRsmall i).le (sq_nonneg _)
        have habssum := Finset.abs_sum_le_sum_abs
          (fun i : Fin n => W n (X i) ^ 2 * R (W n (X i))) Finset.univ
        have hsumle : ∑ i : Fin n, |W n (X i) ^ 2 * R (W n (X i))| ≤
            ε' * ∑ i : Fin n, W n (X i) ^ 2 := by
          calc
            ∑ i : Fin n, |W n (X i) ^ 2 * R (W n (X i))| ≤
                ∑ i : Fin n, W n (X i) ^ 2 * ε' :=
              Finset.sum_le_sum fun i _ => hsummand i
            _ = _ := by rw [← Finset.sum_mul, mul_comm]
        have hfinal : |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))| < ε := by
          have heq : ε' * Mbd = ε / 2 := by dsimp only [ε']; field_simp
          calc
            |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))| ≤
                ∑ i : Fin n, |W n (X i) ^ 2 * R (W n (X i))| := habssum
            _ ≤ ε' * ∑ i : Fin n, W n (X i) ^ 2 := hsumle
            _ < ε' * Mbd := mul_lt_mul_of_pos_left hBlt hε'
            _ = ε / 2 := heq
            _ < ε := by linarith
        exact (not_lt_of_ge hX) hfinal
      exact (measure_mono hincl).trans (measure_union_le _ _)
    have hzero : Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
          (⋃ i ∈ (Finset.univ : Finset (Fin n)),
            {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}))
        atTop (nhds 0) := by
      have hlocal := γ.base_zeroLikelihood_localScale_tendsto a ha.le
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hlocal (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards with n
      have hset : MeasurableSet
          {ω | ((γ.curve (u n)).rnDeriv P ω).toReal = 0} :=
        (Measure.measurable_rnDeriv (γ.curve (u n)) P).ennreal_toReal
          (measurableSet_singleton 0)
      have heach : ∀ i : Fin n,
          (Measure.pi (fun _ : Fin n => P))
              {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0} =
            γ.baseZeroLikelihoodMass (u n) := by
        intro i
        rw [show {X : Fin n → Ω | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0} =
            (fun X : Fin n → Ω => X i) ⁻¹'
              {ω | ((γ.curve (u n)).rnDeriv P ω).toReal = 0} by rfl,
          ← Measure.map_apply (measurable_pi_apply i) hset,
          (measurePreserving_eval (fun _ : Fin n => P) i).map_eq]
        rfl
      calc
        (Measure.pi (fun _ : Fin n => P))
            (⋃ i ∈ (Finset.univ : Finset (Fin n)),
              {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}) ≤
            ∑ i ∈ (Finset.univ : Finset (Fin n)),
              (Measure.pi (fun _ : Fin n => P))
                {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0} :=
          measure_biUnion_finset_le _ _
        _ = (n : ℕ) • γ.baseZeroLikelihoodMass (u n) := by
          simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ = (n : ℝ≥0∞) * γ.baseZeroLikelihoodMass
              (a * (Real.sqrt n)⁻¹) := by
          rw [nsmul_eq_mul]
    have hscoreMean : ∫ ω, (γ.score : Ω → ℝ) ω ∂P = 0 := by
      have hmem : (γ.score : Lp ℝ 2 P) ∈ L2ZeroMean P := γ.score.2
      change (γ.score : Lp ℝ 2 P) ∈
        LinearMap.ker (integralL2 P).toLinearMap at hmem
      rw [LinearMap.mem_ker] at hmem
      have hinner : ⟪oneL2 P, (γ.score : Lp ℝ 2 P)⟫_ℝ = 0 := hmem
      rw [MeasureTheory.L2.inner_def] at hinner
      have hone : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
        MemLp.coeFn_toLp (memLp_const (1 : ℝ))
      have heq : ∫ ω, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω,
            ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ ∂P =
          ∫ ω, (γ.score : Ω → ℝ) ω ∂P := by
        apply integral_congr_ae
        filter_upwards [hone] with ω hω
        rw [show ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω,
            ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ =
              (γ.score : Ω → ℝ) ω * (oneL2 P : Ω → ℝ) ω by rfl,
          hω, mul_one]
      rw [heq] at hinner
      exact hinner
    have hDmean : ∀ n, ∫ ω, D n ω ∂P = ∫ ω, W n ω ∂P := by
      intro n
      have hWint := (hW_mem n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hgint := (Lp.memLp (γ.score : Lp ℝ 2 P)).integrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hscaled : ∫ ω, u n * (γ.score : Ω → ℝ) ω ∂P =
          u n * ∫ ω, (γ.score : Ω → ℝ) ω ∂P :=
        integral_const_mul (u n) (γ.score : Ω → ℝ)
      change (∫ ω, W n ω - u n * (γ.score : Ω → ℝ) ω ∂P) = _
      rw [integral_sub hWint (hgint.const_mul _), hscaled, hscoreMean,
        mul_zero, sub_zero]
    have hAid : ∀ n (X : Fin n → Ω), A n X =
        ∑ i : Fin n, W n (X i) - u n * ∑ i : Fin n, (γ.score : Ω → ℝ) (X i) -
          (n : ℝ) * ∫ ω, W n ω ∂P := by
      intro n X
      change (∑ i : Fin n,
          (W n (X i) - u n * (γ.score : Ω → ℝ) (X i))) -
          (n : ℝ) * ∫ ω, D n ω ∂P = _
      rw [hDmean]
      have hscaled : ∑ i : Fin n, u n * (γ.score : Ω → ℝ) (X i) =
          u n * ∑ i : Fin n, (γ.score : Ω → ℝ) (X i) := by
        rw [Finset.mul_sum]
      rw [Finset.sum_sub_distrib, hscaled]
    have hmeanDet : Tendsto (fun n : ℕ =>
        (n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I) atTop (nhds 0) := by
      convert hmeanW.add_const (a ^ 2 / 4 * I) using 1
      ring_nf
    have hnormI : I = ‖γ.score‖ ^ 2 := integral_score_sq_eq_norm_sq γ
    let Z : ∀ n : ℕ, (Fin n → Ω) → ℝ := fun n X =>
      Real.log (γ.acProductLikelihood (u n) n X).toReal -
        (u n * ∑ i : Fin n, (γ.score : Ω → ℝ) (X i) -
          a ^ 2 / 2 * ‖γ.score‖ ^ 2)
    have hdecomp : ∀ n (X : Fin n → Ω),
        X ∉ (⋃ i ∈ (Finset.univ : Finset (Fin n)),
          {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}) →
        Z n X =
          ((A n X + ((n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I)) +
            (-(1 / 4 : ℝ) * (∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I))) +
            (1 / 2 : ℝ) * ∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i)) := by
      intro n X hnonzero
      have hfac : ∀ i : Fin n, ((γ.curve (u n)).rnDeriv P (X i)).toReal ≠ 0 := by
        intro i hi
        exact hnonzero (Set.mem_biUnion (Finset.mem_univ i) hi)
      have hlog : Real.log (γ.acProductLikelihood (u n) n X).toReal =
          ∑ i : Fin n, Real.log (((γ.curve (u n)).rnDeriv P (X i)).toReal) := by
        simp only [acProductLikelihood, ENNReal.toReal_prod]
        exact Real.log_prod fun i _ => hfac i
      have htaylor : ∀ i : Fin n,
          Real.log (((γ.curve (u n)).rnDeriv P (X i)).toReal) =
            W n (X i) - W n (X i) ^ 2 / 4 +
              W n (X i) ^ 2 / 2 * R (W n (X i)) := by
        intro i
        have ht := AsymptoticStatistics.ForMathlib.log_div_nonneg_eq_sqrt_taylor
          (a := ((γ.curve (u n)).rnDeriv P (X i)).toReal) (b := 1)
          ENNReal.toReal_nonneg zero_le_one
        simpa only [div_one, W, R] using ht
      dsimp only [Z]
      rw [hlog]
      rw [Finset.sum_congr rfl fun i _ => htaylor i]
      have hsplit : ∑ i : Fin n,
          (W n (X i) - W n (X i) ^ 2 / 4 +
            W n (X i) ^ 2 / 2 * R (W n (X i))) =
          (∑ i : Fin n, W n (X i)) -
            (1 / 4 : ℝ) * ∑ i : Fin n, W n (X i) ^ 2 +
            (1 / 2 : ℝ) * ∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsplit, hAid, hnormI]
      ring
    intro ε hε
    let δ : ℝ := ε / 5
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    have hAδ := hA δ hδ
    have hBδ := hB (4 * δ) (mul_pos (by norm_num) hδ)
    have hCδ := hC (2 * δ) (mul_pos (by norm_num) hδ)
    have hdet : Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X | δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|})
        atTop (nhds 0) := by
      have hev := hmeanDet.eventually (Metric.ball_mem_nhds (0 : ℝ) hδ)
      have heq : (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P))
            {X | δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|}) =ᶠ[atTop]
          (fun _ => (0 : ℝ≥0∞)) := by
        filter_upwards [hev] with n hn
        rw [show {X : Fin n → Ω |
            δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|} = ∅ by
          ext X
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
          simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, iff_false] using
            (not_le.mpr hn), measure_empty]
      exact (tendsto_congr' heq).mpr tendsto_const_nhds
    have hsum : Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
            (⋃ i ∈ (Finset.univ : Finset (Fin n)),
              {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}) +
          ((Measure.pi (fun _ : Fin n => P)) {X | δ ≤ |A n X|} +
          ((Measure.pi (fun _ : Fin n => P))
            {X | δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|} +
          ((Measure.pi (fun _ : Fin n => P))
            {X | 4 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|} +
          (Measure.pi (fun _ : Fin n => P))
            {X | 2 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))|}))))
        atTop (nhds 0) := by
      simpa using hzero.add (hAδ.add (hdet.add (hBδ.add hCδ)))
    have hbound : ∀ n,
        (Measure.pi (fun _ : Fin n => P)) {X | ε ≤ |Z n X|} ≤
          (Measure.pi (fun _ : Fin n => P))
              (⋃ i ∈ (Finset.univ : Finset (Fin n)),
                {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}) +
            ((Measure.pi (fun _ : Fin n => P)) {X | δ ≤ |A n X|} +
            ((Measure.pi (fun _ : Fin n => P))
              {X | δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|} +
            ((Measure.pi (fun _ : Fin n => P))
              {X | 4 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|} +
            (Measure.pi (fun _ : Fin n => P))
              {X | 2 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))|}))) := by
      intro n
      let Z0 : Set (Fin n → Ω) :=
        ⋃ i ∈ (Finset.univ : Finset (Fin n)),
          {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}
      let EA : Set (Fin n → Ω) := {X | δ ≤ |A n X|}
      let ED : Set (Fin n → Ω) :=
        {X | δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|}
      let EB : Set (Fin n → Ω) :=
        {X | 4 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|}
      let EC : Set (Fin n → Ω) :=
        {X | 2 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))|}
      have hincl : {X : Fin n → Ω | ε ≤ |Z n X|} ⊆
          Z0 ∪ (EA ∪ (ED ∪ (EB ∪ EC))) := by
        intro X hX
        by_contra hnot
        simp only [Set.mem_union, not_or] at hnot
        obtain ⟨hz, hA', hD', hB', hC'⟩ := hnot
        have hdec := hdecomp n X hz
        have ha' : |A n X| < δ := by simpa only [EA, Set.mem_setOf_eq, not_le] using hA'
        have hd' : |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I| < δ := by
          simpa only [ED, Set.mem_setOf_eq, not_le] using hD'
        have hb' : |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I| < 4 * δ := by
          simpa only [EB, Set.mem_setOf_eq, not_le] using hB'
        have hc' : |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))| < 2 * δ := by
          simpa only [EC, Set.mem_setOf_eq, not_le] using hC'
        rw [Set.mem_setOf_eq, hdec] at hX
        have htri1 := abs_add_le (A n X)
          ((n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I)
        have htri2 := abs_add_le
          (A n X + ((n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I))
          (-(1 / 4 : ℝ) * (∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I))
        have htri3 := abs_add_le
          ((A n X + ((n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I)) +
            (-(1 / 4 : ℝ) * (∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I)))
          ((1 / 2 : ℝ) * ∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i)))
        have hquarter : |-(1 / 4 : ℝ) *
            (∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I)| =
              (1 / 4 : ℝ) * |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I| := by
          rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        have hhalf : |(1 / 2 : ℝ) *
            ∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))| =
              (1 / 2 : ℝ) * |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        rw [hquarter] at htri2
        rw [hhalf] at htri3
        dsimp only [δ] at ha' hd' hb' hc'
        linarith
      calc
        (Measure.pi (fun _ : Fin n => P)) {X | ε ≤ |Z n X|} ≤
            (Measure.pi (fun _ : Fin n => P)) (Z0 ∪ (EA ∪ (ED ∪ (EB ∪ EC)))) :=
          measure_mono hincl
        _ ≤ (Measure.pi (fun _ : Fin n => P)) Z0 +
            ((Measure.pi (fun _ : Fin n => P)) EA +
              ((Measure.pi (fun _ : Fin n => P)) ED +
                ((Measure.pi (fun _ : Fin n => P)) EB +
                  (Measure.pi (fun _ : Fin n => P)) EC))) := by
          have h4 : (Measure.pi (fun _ : Fin n => P)) (EB ∪ EC) ≤
              (Measure.pi (fun _ : Fin n => P)) EB +
                (Measure.pi (fun _ : Fin n => P)) EC := measure_union_le _ _
          have h3 : (Measure.pi (fun _ : Fin n => P)) (ED ∪ (EB ∪ EC)) ≤
              (Measure.pi (fun _ : Fin n => P)) ED +
                ((Measure.pi (fun _ : Fin n => P)) EB +
                  (Measure.pi (fun _ : Fin n => P)) EC) :=
            (measure_union_le _ _).trans (add_le_add_right h4 _)
          have h2 : (Measure.pi (fun _ : Fin n => P)) (EA ∪ (ED ∪ (EB ∪ EC))) ≤
              (Measure.pi (fun _ : Fin n => P)) EA +
                ((Measure.pi (fun _ : Fin n => P)) ED +
                  ((Measure.pi (fun _ : Fin n => P)) EB +
                    (Measure.pi (fun _ : Fin n => P)) EC)) :=
            (measure_union_le _ _).trans (add_le_add_right h3 _)
          exact (measure_union_le _ _).trans (add_le_add_right h2 _)
    have hZ : Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P)) {X | ε ≤ |Z n X|}) atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
        (Filter.Eventually.of_forall fun _ => bot_le)
        (Filter.Eventually.of_forall hbound)
    simpa only [Z, u] using hZ

/-- Full nondominated form of vdV Lemma 25.14: a measurable bare right-QMD
score is mean zero and square integrable, and generates the literal actual-RN
LAN expansion at `1/sqrt n`.

Proof idea: construct a `NondominatedQMDPath` from the bare score, invoke the
actual-likelihood LAN theorem, and transport all terms across the `P`-a.e.
representative. -/
theorem qmd_score_mean_integrable_and_lan_nondominated
    (P : Measure Ω) [IsProbabilityMeasure P]
    (curve : ℝ → Measure Ω)
    -- USER-INPUT: a one-sided probability path through `P`; vdV Lemma 25.14.
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (curve t))
    (hzero : curve 0 = P)
    (g : Ω → ℝ)
    -- LEAN-ONLY: measurability of the score representative.
    (hg : Measurable g)
    -- USER-INPUT: right differentiability in quadratic mean with score `g`;
    -- vdV Lemma 25.14.
    (hqmd : IsRightQMD P curve g)
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω' → Ω)
    -- LEAN-ONLY: measurability of each sample coordinate.
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: iid observations with common law `P`; vdV Lemma 25.14.
    (hindep : ProbabilityTheory.iIndepFun X P')
    (hident : ∀ i, IdentDistrib (X i) (X 0) P' P')
    (hlaw : Measure.map (X 0) P' = P) :
    (∫ ω, g ω ∂P = 0) ∧ Integrable (fun ω => g ω ^ 2) P ∧
      TendstoInMeasure P'
        (fun n ω =>
          (∑ i ∈ Finset.range n,
            Real.log (((curve ((Real.sqrt n)⁻¹)).rnDeriv P (X i ω)).toReal))
            - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)
            + (1 / 2 : ℝ) * ∫ x, g x ^ 2 ∂P)
        atTop (fun _ => (0 : ℝ)) := by
  classical
  obtain ⟨γ, hγcurve, hgscore⟩ :=
    exists_nondominatedQMDPath_of_bare_qmd P curve hprob hzero g hg hqmd
  have hscoreMean : ∫ ω, (γ.score : Ω → ℝ) ω ∂P = 0 := by
    have hmem : (γ.score : Lp ℝ 2 P) ∈ L2ZeroMean P := γ.score.2
    change (γ.score : Lp ℝ 2 P) ∈
      LinearMap.ker (integralL2 P).toLinearMap at hmem
    rw [LinearMap.mem_ker] at hmem
    have hinner : ⟪oneL2 P, (γ.score : Lp ℝ 2 P)⟫_ℝ = 0 := hmem
    rw [MeasureTheory.L2.inner_def] at hinner
    have hone : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    have heq : ∫ ω, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω,
          ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ ∂P =
        ∫ ω, (γ.score : Ω → ℝ) ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hone] with ω hω
      rw [show ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω,
          ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ =
            (γ.score : Ω → ℝ) ω * (oneL2 P : Ω → ℝ) ω by rfl,
        hω, mul_one]
    rw [heq] at hinner
    exact hinner
  have hmean : ∫ ω, g ω ∂P = 0 := by
    rw [integral_congr_ae hgscore]
    exact hscoreMean
  have hgmem : MemLp g 2 P :=
    (memLp_congr_ae hgscore).mpr (Lp.memLp (γ.score : Lp ℝ 2 P))
  have hgsq : Integrable (fun ω => g ω ^ 2) P := hgmem.integrable_sq
  refine ⟨hmean, hgsq, ?_⟩
  have hI : ∫ ω, g ω ^ 2 ∂P = ‖γ.score‖ ^ 2 := by
    have hpow : (fun ω => g ω ^ 2) =ᵐ[P]
        fun ω => (γ.score : Ω → ℝ) ω ^ 2 := by
      filter_upwards [hgscore] with ω hω
      rw [hω]
    rw [integral_congr_ae hpow]
    exact integral_score_sq_eq_norm_sq γ
  let T : ∀ n : ℕ, (Fin n → Ω) → ℝ := fun n Y =>
    Real.log (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n Y).toReal -
      ((Real.sqrt n)⁻¹ * ∑ i : Fin n, (γ.score : Ω → ℝ) (Y i) -
        (1 / 2 : ℝ) * ‖γ.score‖ ^ 2)
  let S : ∀ n : ℕ, (Fin n → Ω) → ℝ := fun n Y =>
    (∑ i : Fin n,
      Real.log (((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal)) -
      (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (Y i) +
      (1 / 2 : ℝ) * ∫ x, g x ^ 2 ∂P
  have hLAN : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)) {Y | ε ≤ |T n Y|})
      atTop (nhds 0) := by
    intro ε hε
    simpa only [T, one_mul, one_pow] using
      log_acProductLikelihood_lan_tendstoInMeasure γ 1 zero_le_one ε hε
  have hzeroProd : Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        (⋃ i ∈ (Finset.univ : Finset (Fin n)),
          {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0}))
      atTop (nhds 0) := by
    have hlocal := γ.base_zeroLikelihood_localScale_tendsto 1 zero_le_one
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hlocal (Filter.Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards with n
    have hset : MeasurableSet
        {ω | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P ω).toReal = 0} :=
      (Measure.measurable_rnDeriv (γ.curve ((Real.sqrt n)⁻¹)) P).ennreal_toReal
        (measurableSet_singleton 0)
    have heach : ∀ i : Fin n,
        (Measure.pi (fun _ : Fin n => P))
            {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0} =
          γ.baseZeroLikelihoodMass ((Real.sqrt n)⁻¹) := by
      intro i
      rw [show {Y : Fin n → Ω |
          ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0} =
          (fun Y : Fin n → Ω => Y i) ⁻¹'
            {ω | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P ω).toReal = 0} by rfl,
        ← Measure.map_apply (measurable_pi_apply i) hset,
        (measurePreserving_eval (fun _ : Fin n => P) i).map_eq]
      rfl
    calc
      (Measure.pi (fun _ : Fin n => P))
          (⋃ i ∈ (Finset.univ : Finset (Fin n)),
            {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0}) ≤
          ∑ i ∈ (Finset.univ : Finset (Fin n)),
            (Measure.pi (fun _ : Fin n => P))
              {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0} :=
        measure_biUnion_finset_le _ _
      _ = (n : ℕ) • γ.baseZeroLikelihoodMass ((Real.sqrt n)⁻¹) := by
        simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = (n : ℝ≥0∞) * γ.baseZeroLikelihoodMass
          (1 * (Real.sqrt n)⁻¹) := by rw [nsmul_eq_mul, one_mul]
  have hsumLAN : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)) {Y | ε ≤ |S n Y|})
      atTop (nhds 0) := by
    intro ε hε
    have hupper : Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
            (⋃ i ∈ (Finset.univ : Finset (Fin n)),
              {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0}) +
          (Measure.pi (fun _ : Fin n => P)) {Y | ε ≤ |T n Y|})
        atTop (nhds 0) := by
      simpa using hzeroProd.add (hLAN ε hε)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper (Filter.Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards with n
    have hgpi : (fun (Y : Fin n → Ω) i => g (Y i)) =ᵐ[
        Measure.pi (fun _ : Fin n => P)]
          fun Y i => (γ.score : Ω → ℝ) (Y i) :=
      Measure.ae_eq_pi (μ := fun _ : Fin n => P)
        (f := fun _ ω => g ω)
        (f' := fun _ ω => (γ.score : Ω → ℝ) ω) (fun _ => hgscore)
    have hincl : ∀ᵐ Y ∂(Measure.pi (fun _ : Fin n => P)),
        Y ∈ {Y : Fin n → Ω | ε ≤ |S n Y|} →
          Y ∈ ((⋃ i ∈ (Finset.univ : Finset (Fin n)),
            {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0}) ∪
            {Y | ε ≤ |T n Y|}) := by
      filter_upwards [hgpi] with Y hY
      intro hbad
      by_cases hz : Y ∈ (⋃ i ∈ (Finset.univ : Finset (Fin n)),
          {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0})
      · exact Or.inl hz
      · apply Or.inr
        have hfac : ∀ i : Fin n,
            ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal ≠ 0 := by
          intro i hi
          exact hz (Set.mem_biUnion (Finset.mem_univ i) hi)
        have hlog : Real.log
              (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n Y).toReal =
            ∑ i : Fin n,
              Real.log (((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal) := by
          simp only [acProductLikelihood, ENNReal.toReal_prod]
          exact Real.log_prod fun i _ => hfac i
        have hsumg : ∑ i : Fin n, g (Y i) =
            ∑ i : Fin n, (γ.score : Ω → ℝ) (Y i) := by
          rw [hY]
        have hST : S n Y = T n Y := by
          dsimp only [S, T]
          rw [hlog, hsumg, hI]
          ring
        rwa [hST] at hbad
    exact (measure_mono_ae hincl).trans (measure_union_le _ _)
  let Y : ∀ n : ℕ, Ω' → (Fin n → Ω) := fun n ω i => X i.val ω
  have hYmeas : ∀ n, Measurable (Y n) := by
    intro n
    exact measurable_pi_lambda _ fun i => hX_meas i.val
  have hjoint : ∀ n, Measure.map (Y n) P' =
      Measure.pi (fun _ : Fin n => P) := by
    intro n
    have hfin : iIndepFun (fun i : Fin n => X i.val) P' :=
      ProbabilityTheory.iIndepFun.precomp Fin.val_injective hindep
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (hX_meas i.val).aemeasurable)).mp hfin
    calc
      Measure.map (Y n) P' =
          Measure.pi (fun i : Fin n => Measure.map (X i.val) P') := hmap
      _ = Measure.pi (fun _ : Fin n => P) := by
        congr 1
        funext i
        rw [(hident i.val).map_eq, hlaw]
  have hSmeas : ∀ n, Measurable (S n) := by
    intro n
    dsimp only [S]
    have hlogmeas : Measurable (fun Y : Fin n → Ω =>
        ∑ i : Fin n,
          Real.log (((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal)) :=
      Finset.measurable_sum _ fun i _ =>
        ((Measure.measurable_rnDeriv (γ.curve ((Real.sqrt n)⁻¹)) P).comp
          (measurable_pi_apply i)).ennreal_toReal.log
    have hgmeas : Measurable (fun Y : Fin n → Ω =>
        ∑ i : Fin n, g (Y i)) :=
      Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i)
    exact (hlogmeas.sub (hgmeas.const_mul _)).add_const _
  rw [MeasureTheory.tendstoInMeasure_iff_norm]
  intro ε hε
  have hp := hsumLAN ε hε
  convert hp using 1
  funext n
  have hset : MeasurableSet {Z : Fin n → Ω | ε ≤ |S n Z|} :=
    measurableSet_le measurable_const (hSmeas n).abs
  have hstat : ∀ ω : Ω',
      ((∑ i ∈ Finset.range n,
          Real.log (((curve ((Real.sqrt n)⁻¹)).rnDeriv P (X i ω)).toReal))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)
        + (1 / 2 : ℝ) * ∫ x, g x ^ 2 ∂P) = S n (Y n ω) := by
    intro ω
    dsimp only [S, Y]
    rw [hγcurve]
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  calc
    P' {ω |
        ε ≤
          ‖((∑ i ∈ Finset.range n,
              Real.log (((curve ((Real.sqrt n)⁻¹)).rnDeriv P (X i ω)).toReal))
            - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)
            + (1 / 2 : ℝ) * ∫ x, g x ^ 2 ∂P) - 0‖} =
        P' ((Y n) ⁻¹' {Z : Fin n → Ω | ε ≤ |S n Z|}) := by
      congr 1
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, sub_zero, Real.norm_eq_abs]
      rw [hstat]
    _ = Measure.map (Y n) P' {Z : Fin n → Ω | ε ≤ |S n Z|} := by
      rw [Measure.map_apply (hYmeas n) hset]
    _ = (Measure.pi (fun _ : Fin n => P)) {Z : Fin n → Ω | ε ≤ |S n Z|} := by
      rw [hjoint]

end AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLAN
