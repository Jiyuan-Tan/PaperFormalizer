module
public import StatLean.AsymptoticStatistics.Core.NondominatedQMDPath
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct
public import StatLean.AsymptoticStatistics.ForMathlib.L2Tail
public import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity

@[expose] public section

/-! # Actual-likelihood product comparison for nondominated QMD paths -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace AsymptoticStatistics.Core.NondominatedQMDPath

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.ForMathlib.HellingerProduct
open AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic

set_option linter.dupNamespace false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

namespace NondominatedQMDPath

/-- Baseline-absolutely-continuous part of a path law. -/
noncomputable def acPart (γ : NondominatedQMDPath P) (t : ℝ) : Measure Ω :=
  P.withDensity ((γ.curve t).rnDeriv P)

/-- Singular part of a path law relative to `P`; it may be nonzero. -/
noncomputable def singularPart (γ : NondominatedQMDPath P) (t : ℝ) : Measure Ω :=
  (γ.curve t).singularPart P

/-- Total singular mass; it is zero for a baseline-AC perturbation. -/
noncomputable def singularMass (γ : NondominatedQMDPath P) (t : ℝ) : ℝ≥0∞ :=
  γ.singularPart t Set.univ

/-- Baseline mass of the zero actual-likelihood event.  This is distinct
from `singularMass`, which measures a defect under the perturbed law. -/
noncomputable def baseZeroLikelihoodMass
    (γ : NondominatedQMDPath P) (t : ℝ) : ℝ≥0∞ :=
  P {ω | ((γ.curve t).rnDeriv P ω).toReal = 0}

/-- Actual RN likelihood of the all-AC part of the local product law. -/
noncomputable def acProductLikelihood
    (γ : NondominatedQMDPath P) (t : ℝ) (n : ℕ) : (Fin n → Ω) → ℝ≥0∞ :=
  fun X => ∏ i : Fin n, (γ.curve t).rnDeriv P (X i)

/-- Canonical-pairwise square-root QMD residual. -/
noncomputable def comparisonResidual
    (γ : NondominatedQMDPath P) (t : ℝ) : Ω → ℝ :=
  residualAgainst P (γ.curve t) (canonicalDominator P (γ.curve t))
    (γ.score : Ω → ℝ) t

/-- Lebesgue decomposition of a path law into singular and baseline-AC parts.

The proof uses Mathlib's Lebesgue decomposition with the probability-provided
sigma-finiteness instances. -/
theorem curve_eq_singularPart_add_acPart
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) :
    γ.curve t = γ.singularPart t + γ.acPart t := by
  letI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  exact Measure.haveLebesgueDecomposition_add (γ.curve t) P

/-- Singular mass is bounded by the squared canonical QMD residual norm.

On the zero-baseline-density set the score and baseline-root
terms vanish, leaving the perturbed square root. -/
theorem singularMass_le_residual_sq
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) :
    γ.singularMass t ≤
      eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) ^ 2 := by
  letI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  let μ := canonicalDominator P (γ.curve t)
  letI : SigmaFinite μ := by
    dsimp only [μ, canonicalDominator]
    infer_instance
  let hsing := Measure.mutuallySingular_singularPart (γ.curve t) P
  let s := hsing.nullSetᶜ
  have hs : MeasurableSet s := hsing.measurableSet_nullSet.compl
  have hS : (γ.curve t).singularPart P = (γ.curve t).restrict s := by
    apply Measure.singularPart_eq_restrict
    · simpa only [s, compl_compl] using hsing.measure_nullSet
    · exact hsing.measure_compl_nullSet
  have hPμ : P ≪ μ := by
    exact (Measure.le_add_right le_rfl).absolutelyContinuous
  have hQμ : γ.curve t ≪ μ := by
    exact (Measure.le_add_left le_rfl).absolutelyContinuous
  have hPzero : P s = 0 := hsing.measure_compl_nullSet
  have hPint : ∫⁻ ω in s, P.rnDeriv μ ω ∂μ = 0 := by
    rw [Measure.setLIntegral_rnDeriv hPμ s, hPzero]
  have hpzero : P.rnDeriv μ =ᵐ[μ.restrict s] 0 := by
    exact (lintegral_eq_zero_iff'
      (Measure.measurable_rnDeriv P μ).aemeasurable.restrict).mp hPint
  have hpoint : ∀ᵐ ω ∂(μ.restrict s),
      (γ.curve t).rnDeriv μ ω ≤ ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hpzero,
      ae_restrict_of_ae (Measure.rnDeriv_ne_top (γ.curve t) μ)] with ω hp hq
    simp only [Pi.zero_apply] at hp
    have hp' : P.rnDeriv (canonicalDominator P (γ.curve t)) ω = 0 := by
      simpa only [μ] using hp
    have hq' : (γ.curve t).rnDeriv (canonicalDominator P (γ.curve t)) ω ≠ ⊤ := by
      simpa only [μ] using hq
    change (γ.curve t).rnDeriv (canonicalDominator P (γ.curve t)) ω ≤
      ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ)
    rw [comparisonResidual, residualAgainst, hp', ENNReal.toReal_zero,
      Real.sqrt_zero, mul_zero]
    simp only [sub_zero]
    rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hq']
  have hlin : γ.singularMass t ≤
      ∫⁻ ω, ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ∂μ := by
    rw [singularMass, singularPart, hS,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ← Measure.setLIntegral_rnDeriv hQμ s]
    exact (lintegral_mono_ae hpoint).trans (setLIntegral_le_lintegral s _)
  have hlin' : γ.singularMass t ≤
      ∫⁻ ω, ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ)
        ∂(canonicalDominator P (γ.curve t)) := by
    simpa only [μ] using hlin
  convert hlin' using 1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- QMD makes perturbed-law singular mass negligible at root-`n` scale.

The proof combines `singularMass_le_residual_sq` with `qmd_limit`. -/
theorem singular_mass_localScale_tendsto
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (n : ℝ≥0∞) *
      γ.singularMass (a * (Real.sqrt n)⁻¹)) atTop (nhds 0) := by
  rcases ha.eq_or_lt with rfl | ha
  · have hz : (fun n : ℕ => (n : ℝ≥0∞) *
        γ.singularMass (0 * (Real.sqrt n)⁻¹)) = fun _ => 0 := by
      funext n
      simp [singularMass, singularPart, curve_at_zero]
    rw [hz]
    exact tendsto_const_nhds
  let u : ℕ → ℝ := fun n => a * (Real.sqrt n)⁻¹
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
  let r : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (γ.comparisonResidual (u n)) 2
      (canonicalDominator P (γ.curve (u n)))
  have hquot : Tendsto (fun n => r n / ENNReal.ofReal (u n))
      atTop (nhds 0) := by
    simpa only [IsRightQMD, comparisonResidual, Function.comp_apply, r] using!
      γ.qmd_limit.comp hu_right
  have henvelope : Tendsto
      (fun n => ENNReal.ofReal a ^ 2 *
        (r n / ENNReal.ofReal (u n)) ^ 2) atTop (nhds 0) := by
    have hsq : Tendsto (fun n =>
        (r n / ENNReal.ofReal (u n)) * (r n / ENNReal.ofReal (u n)))
        atTop (nhds 0) := by
      simpa only [zero_mul] using
        ENNReal.Tendsto.mul hquot (Or.inr ENNReal.zero_ne_top) hquot
          (Or.inr ENNReal.zero_ne_top)
    simpa only [pow_two, mul_zero] using ENNReal.Tendsto.const_mul hsq
      (Or.inr (by simp : ENNReal.ofReal a ^ 2 ≠ ⊤))
  have hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ≥0∞) * ENNReal.ofReal (u n) ^ 2 = ENNReal.ofReal a ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := by omega
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos_nat
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hreal : (n : ℝ) * (u n) ^ 2 = a ^ 2 := by
      dsimp only [u]
      rw [mul_pow]
      calc
        (n : ℝ) * (a ^ 2 * (Real.sqrt n)⁻¹ ^ 2) =
            a ^ 2 * ((n : ℝ) * (Real.sqrt n)⁻¹ ^ 2) := by ring
        _ = a ^ 2 := by
          have hfactor : (n : ℝ) * (Real.sqrt n)⁻¹ ^ 2 = 1 := by
            calc
              (n : ℝ) * (Real.sqrt n)⁻¹ ^ 2 =
                  (n : ℝ) / Real.sqrt n ^ 2 := by
                    rw [inv_pow, div_eq_mul_inv]
              _ = (n : ℝ) / n := by rw [Real.sq_sqrt hnpos.le]
              _ = 1 := div_self hnpos.ne'
          rw [hfactor, mul_one]
    calc
      (n : ℝ≥0∞) * ENNReal.ofReal (u n) ^ 2 =
          ENNReal.ofReal ((n : ℝ) * (u n) ^ 2) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
              ENNReal.ofReal_pow (show 0 ≤ u n by positivity)]
      _ = ENNReal.ofReal (a ^ 2) := by rw [hreal]
      _ = ENNReal.ofReal a ^ 2 := ENNReal.ofReal_pow ha.le 2
  have hupper : ∀ᶠ n : ℕ in atTop,
      (n : ℝ≥0∞) * γ.singularMass (u n) ≤
        ENNReal.ofReal a ^ 2 * (r n / ENNReal.ofReal (u n)) ^ 2 := by
    filter_upwards [eventually_ge_atTop 1, hscale] with n hn hscale_n
    have hupos : 0 < u n := mul_pos ha (inv_pos.mpr
      (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))))
    have hd_ne : ENNReal.ofReal (u n) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hupos
    have hd_top : ENNReal.ofReal (u n) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      (n : ℝ≥0∞) * γ.singularMass (u n) ≤
          (n : ℝ≥0∞) * r n ^ 2 :=
        mul_le_mul_right (γ.singularMass_le_residual_sq (u n) hupos.le) _
      _ = ((n : ℝ≥0∞) * ENNReal.ofReal (u n) ^ 2) *
          (r n / ENNReal.ofReal (u n)) ^ 2 := by
        have hcancel : ENNReal.ofReal (u n) ^ 2 *
            (r n / ENNReal.ofReal (u n)) ^ 2 = r n ^ 2 := by
          rw [← mul_pow, ENNReal.mul_div_cancel hd_ne hd_top]
        calc
          (n : ℝ≥0∞) * r n ^ 2 =
              (n : ℝ≥0∞) * (ENNReal.ofReal (u n) ^ 2 *
                (r n / ENNReal.ofReal (u n)) ^ 2) := by rw [hcancel]
          _ = ((n : ℝ≥0∞) * ENNReal.ofReal (u n) ^ 2) *
              (r n / ENNReal.ofReal (u n)) ^ 2 := by
                rw [mul_assoc]
      _ = ENNReal.ofReal a ^ 2 *
          (r n / ENNReal.ofReal (u n)) ^ 2 := by rw [hscale_n]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds henvelope
    (Filter.Eventually.of_forall fun n => bot_le)
    hupper

/-- The baseline zero-likelihood mass is `o(t²)` from the right.

The proof uses the one-observation Hellinger/QMD inequality on the event where
the actual RN derivative vanishes. This estimate is distinct from
the singular-mass estimate. -/
theorem baseZeroLikelihoodMass_isLittleO
    (γ : NondominatedQMDPath P) :
    (fun t : ℝ => (γ.baseZeroLikelihoodMass t).toReal)
      =o[nhdsWithin 0 (Set.Ioi 0)] (fun t : ℝ => t ^ 2) := by
  classical
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  let g : Ω → ℝ := γ.score
  have hg_meas : Measurable g :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P)).measurable
  have hg_mem : MemLp g 2 P := Lp.memLp _
  have hg_sq : Integrable (fun ω => g ω ^ 2) P := hg_mem.integrable_sq
  have ht_zero : Tendsto (fun t : ℝ => t) l (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have htail : (fun t : ℝ => P.real {ω | 1 ≤ |t * g ω|})
      =o[l] (fun t : ℝ => t ^ 2) := by
    let W : ℝ → Ω → ℝ := fun t ω => t * g ω
    have hW_meas : ∀ t, Measurable (W t) :=
      fun _ => measurable_const.mul hg_meas
    have hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P :=
      Filter.Eventually.of_forall fun t => hg_mem.const_mul t
    have hW_sq_zero : Tendsto (fun t => ∫ ω, W t ω ^ 2 ∂P) l (nhds 0) := by
      have hmain := (ht_zero.pow 2).mul_const (∫ ω, g ω ^ 2 ∂P)
      have hint : (fun t : ℝ => ∫ ω, W t ω ^ 2 ∂P) =
          fun t => t ^ 2 * ∫ ω, g ω ^ 2 ∂P := by
        funext t
        simp only [W, mul_pow, MeasureTheory.integral_const_mul]
      rw [hint]
      simpa using hmain
    have hqO : (fun t : ℝ => ∫ ω, (0 : ℝ) ^ 2 ∂P)
        =o[l] (fun t => |t| ^ 2) := by
      simp
    have hpack := AsymptoticStatistics.L2Utils.l2_tail_controls_of_approx
      l P W (fun _ _ => 0) W (fun t => |t|) (fun ω => g ω ^ 2)
      hW_meas hW_mem hW_sq_zero
      (Filter.Eventually.of_forall fun _ => MemLp.zero)
      hqO
      hg_sq (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (fun _ => abs_nonneg _) (fun _ _ => by simp)
      (fun t ω => by
        change (t * g ω) ^ 2 ≤ |t| ^ 2 * g ω ^ 2
        rw [mul_pow, sq_abs])
      (fun _ => 0) MemLp.zero 1 zero_lt_one
    simpa only [W, l, sq_abs] using hpack.2.2.1
  have hmass : ∀ t : ℝ, 0 < t →
      γ.baseZeroLikelihoodMass t ≤
        P {ω | 1 ≤ |t * g ω|} +
          4 * eLpNorm (γ.comparisonResidual t) 2
            (canonicalDominator P (γ.curve t)) ^ 2 := by
    intro t ht
    letI : IsProbabilityMeasure (γ.curve t) :=
      γ.curve_isProbability t ht.le
    let μ := canonicalDominator P (γ.curve t)
    let p : Ω → ℝ≥0∞ := P.rnDeriv μ
    let qP : Ω → ℝ≥0∞ := (γ.curve t).rnDeriv P
    let q : Ω → ℝ≥0∞ := (γ.curve t).rnDeriv μ
    let Z : Set Ω := {ω | (qP ω).toReal = 0}
    let B : Set Ω := {ω | 1 ≤ |t * g ω|}
    let A : Set Ω := Z \ B
    letI : SigmaFinite μ := by
      dsimp only [μ, canonicalDominator]
      infer_instance
    have hPμ : P ≪ μ := by
      exact (Measure.le_add_right le_rfl).absolutelyContinuous
    have hZ : MeasurableSet Z := by
      change MeasurableSet ((fun ω => ((γ.curve t).rnDeriv P ω).toReal) ⁻¹' {0})
      exact (Measure.measurable_rnDeriv (γ.curve t) P).ennreal_toReal
        (measurableSet_singleton 0)
    have hB : MeasurableSet B := by
      exact measurableSet_le measurable_const ((measurable_const.mul hg_meas).abs)
    have hA : MeasurableSet A := hZ.diff hB
    have hchainP :
        (γ.curve t).rnDeriv P * P.rnDeriv μ
          =ᵐ[P] (γ.curve t).rnDeriv μ :=
      Measure.rnDeriv_mul_rnDeriv' (μ := γ.curve t) (ν := P)
        (κ := μ) hPμ
    have hP_eq : μ.withDensity (P.rnDeriv μ) = P :=
      Measure.withDensity_rnDeriv_eq P μ hPμ
    have hchainP' :
        (γ.curve t).rnDeriv P * P.rnDeriv μ
          =ᵐ[μ.withDensity (P.rnDeriv μ)] (γ.curve t).rnDeriv μ := by
      simpa only [hP_eq] using hchainP
    have hchainμ : ∀ᵐ ω ∂μ, p ω ≠ 0 →
        qP ω * p ω = q ω := by
      simpa only [p, qP, q] using!
        (ae_withDensity_iff (Measure.measurable_rnDeriv P μ)).mp hchainP'
    have hqPfinP : ∀ᵐ ω ∂P, qP ω ≠ ⊤ := by
      simpa only [qP] using Measure.rnDeriv_ne_top (γ.curve t) P
    have hqPfinP' : ∀ᵐ ω ∂(μ.withDensity (P.rnDeriv μ)), qP ω ≠ ⊤ := by
      simpa only [hP_eq] using hqPfinP
    have hqPfinμ : ∀ᵐ ω ∂μ, p ω ≠ 0 → qP ω ≠ ⊤ := by
      simpa only [p] using
        (ae_withDensity_iff (Measure.measurable_rnDeriv P μ)).mp hqPfinP'
    have hpfin : ∀ᵐ ω ∂μ, p ω ≠ ⊤ := by
      simpa only [p] using Measure.rnDeriv_ne_top P μ
    have hpoint : ∀ᵐ ω ∂(μ.restrict A),
        p ω ≤ 4 * ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) := by
      filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae hchainμ,
        ae_restrict_of_ae hqPfinμ, ae_restrict_of_ae hpfin] with
        ω hω hchain hqPfin hpfinω
      by_cases hpzero : p ω = 0
      · simp [hpzero]
      have hqPzero : qP ω = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff (qP ω)).mp hω.1 with hzero | htop
        · exact hzero
        · exact (hqPfin hpzero htop).elim
      have hqzero : q ω = 0 := by
        have hc := hchain hpzero
        simpa only [hqPzero, zero_mul] using hc.symm
      have hgood : |t * g ω| < 1 := lt_of_not_ge hω.2
      have hcoef : (1 / 2 : ℝ) ≤ 1 + t * g ω / 2 := by
        rw [abs_lt] at hgood
        linarith
      have hres : γ.comparisonResidual t ω =
          -(1 + t * g ω / 2) * Real.sqrt (p ω).toReal := by
        simp only [comparisonResidual, residualAgainst, q, p] at hqzero ⊢
        rw [hqzero, ENNReal.toReal_zero, Real.sqrt_zero, zero_sub]
        ring
      have hreal : (p ω).toReal ≤
          4 * (γ.comparisonResidual t ω) ^ 2 := by
        rw [hres]
        have hsqrt := Real.sqrt_nonneg (p ω).toReal
        have hsquare : Real.sqrt (p ω).toReal ^ 2 = (p ω).toReal :=
          Real.sq_sqrt ENNReal.toReal_nonneg
        have hcoef_nonneg : 0 ≤ 1 + t * g ω / 2 := by linarith
        have hmul : (1 / 2 : ℝ) * Real.sqrt (p ω).toReal ≤
            (1 + t * g ω / 2) * Real.sqrt (p ω).toReal :=
          mul_le_mul_of_nonneg_right hcoef hsqrt
        have hsqmul : ((1 / 2 : ℝ) * Real.sqrt (p ω).toReal) ^ 2 ≤
            ((1 + t * g ω / 2) * Real.sqrt (p ω).toReal) ^ 2 :=
          (sq_le_sq₀ (mul_nonneg (by norm_num) hsqrt)
            (mul_nonneg hcoef_nonneg hsqrt)).2 hmul
        nlinarith
      have hrespow : ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
        rw [ENNReal.rpow_two]
        simpa only [pow_two] using
          ENNReal.mul_ne_top (enorm_ne_top :
            ‖γ.comparisonResidual t ω‖ₑ ≠ ⊤) enorm_ne_top
      have hfour : (4 : ℝ≥0∞) *
          ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) hrespow
      rw [← ENNReal.toReal_le_toReal hpfinω hfour]
      simpa only [ENNReal.rpow_two, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
        ENNReal.toReal_pow, toReal_enorm, Real.norm_eq_abs, sq_abs] using hreal
    have hnormsq :
        eLpNorm (γ.comparisonResidual t) 2 μ ^ 2 =
          ∫⁻ ω, ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ∂μ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    have hPA : P A ≤ 4 *
        eLpNorm (γ.comparisonResidual t) 2 μ ^ 2 := by
      rw [← Measure.setLIntegral_rnDeriv hPμ A]
      calc
        (∫⁻ ω in A, p ω ∂μ) ≤
            ∫⁻ ω in A, 4 * ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ∂μ :=
          lintegral_mono_ae hpoint
        _ = 4 * ∫⁻ ω in A,
            ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ∂μ := by
              rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
        _ ≤ 4 * ∫⁻ ω,
            ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ∂μ :=
          mul_le_mul_right (setLIntegral_le_lintegral A _) _
        _ = 4 * eLpNorm (γ.comparisonResidual t) 2 μ ^ 2 := by
          rw [hnormsq]
    have hZA : P Z ≤ P B + P A := by
      calc
        P Z ≤ P (B ∪ A) := measure_mono (by
          intro ω hω
          by_cases hωB : ω ∈ B
          · exact Set.mem_union_left A hωB
          · exact Set.mem_union_right B ⟨hω, hωB⟩)
        _ ≤ P B + P A := measure_union_le B A
    have hZA' : P Z ≤ P B + 4 *
        eLpNorm (γ.comparisonResidual t) 2 μ ^ 2 :=
      hZA.trans (by gcongr)
    simpa only [baseZeroLikelihoodMass, Z, qP, B, g, μ] using hZA'
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have htail_bound := (Asymptotics.isLittleO_iff.mp htail) (half_pos hc)
  have hqmd := γ.qmd_limit
  have hqmd_real :
      Tendsto (fun t : ℝ =>
        (eLpNorm (γ.comparisonResidual t) 2
          (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal)
        l (nhds 0) := by
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hqmd
  have hqmd_bound : ∀ᶠ t : ℝ in l,
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal ^ 2 ≤
          c / 8 := by
    have hsqrt : 0 < Real.sqrt (c / 8) := Real.sqrt_pos.mpr (by positivity)
    have hevent := hqmd_real.eventually (Iio_mem_nhds hsqrt)
    filter_upwards [hevent] with t ht
    have hnonneg : 0 ≤
        (eLpNorm (γ.comparisonResidual t) 2
          (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal :=
      ENNReal.toReal_nonneg
    nlinarith [Real.sq_sqrt (show 0 ≤ c / 8 by positivity)]
  have hqmd_lt : ∀ᶠ t : ℝ in l,
      eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t < 1 :=
    hqmd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [self_mem_nhdsWithin, htail_bound, hqmd_bound, hqmd_lt] with
      t ht htail_t hqmd_t hqmd_lt_t
  have htpos : 0 < t := ht
  have hmass_t := hmass t htpos
  have hnorm_fin : eLpNorm (γ.comparisonResidual t) 2
      (canonicalDominator P (γ.curve t)) ≠ ⊤ := by
    intro htop
    have hden_top : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
    have hfalse : (⊤ : ℝ≥0∞) < 1 := by
      simpa only [htop, ENNReal.top_div, if_neg hden_top] using hqmd_lt_t
    exact (not_lt_of_ge le_top hfalse).elim
  have hmass_real : (γ.baseZeroLikelihoodMass t).toReal ≤
      (P {ω | 1 ≤ |t * g ω|}).toReal +
        4 * (eLpNorm (γ.comparisonResidual t) 2
          (canonicalDominator P (γ.curve t))).toReal ^ 2 := by
    have hnormpow : eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) ^ 2 ≠ ⊤ := by
      simpa only [pow_two] using ENNReal.mul_ne_top hnorm_fin hnorm_fin
    have hfour : (4 : ℝ≥0∞) * eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) ^ 2 ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hnormpow
    have hrhs : P {ω | 1 ≤ |t * g ω|} +
        4 * eLpNorm (γ.comparisonResidual t) 2
          (canonicalDominator P (γ.curve t)) ^ 2 ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, hfour⟩
    have hmono := ENNReal.toReal_mono hrhs hmass_t
    rw [ENNReal.toReal_add (measure_ne_top _ _) hfour,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_pow] at hmono
    exact hmono
  have hquot_eq :
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal =
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t))).toReal / t := by
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal htpos.le]
  rw [hquot_eq] at hqmd_t
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at htail_t
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  have hres_bound : 4 *
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t))).toReal ^ 2 ≤
      c / 2 * t ^ 2 := by
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
    rw [div_pow] at hqmd_t
    have hscaled := (div_le_iff₀ ht2).mp hqmd_t
    nlinarith
  calc
    (γ.baseZeroLikelihoodMass t).toReal ≤
        (P {ω | 1 ≤ |t * g ω|}).toReal +
          4 * (eLpNorm (γ.comparisonResidual t) 2
            (canonicalDominator P (γ.curve t))).toReal ^ 2 := hmass_real
    _ ≤ c / 2 * t ^ 2 + c / 2 * t ^ 2 :=
      add_le_add htail_t hres_bound
    _ = c * t ^ 2 := by ring

/-- Consequently an `n`-sample has vanishing baseline probability of any
zero local likelihood factor.

For `a > 0`, specialize `baseZeroLikelihoodMass_isLittleO` at
`a/sqrt n` and multiply by `n`; the case `a = 0` follows from `curve_at_zero`. -/
theorem base_zeroLikelihood_localScale_tendsto
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (n : ℝ≥0∞) *
      γ.baseZeroLikelihoodMass (a * (Real.sqrt n)⁻¹)) atTop (nhds 0) := by
  rcases ha.eq_or_lt with rfl | ha
  · have hmass0 : γ.baseZeroLikelihoodMass 0 = 0 := by
      rw [baseZeroLikelihoodMass, curve_at_zero]
      have hset :
          {ω | (P.rnDeriv P ω).toReal = 0} =ᵐ[P] (∅ : Set Ω) := by
        filter_upwards [Measure.rnDeriv_self P] with ω hω
        change ((P.rnDeriv P ω).toReal = 0) = False
        rw [hω]
        norm_num
      simpa using measure_congr hset
    simp only [zero_mul, hmass0, mul_zero]
    exact tendsto_const_nhds
  let u : ℕ → ℝ := fun n => a * (Real.sqrt n)⁻¹
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
  have hsmall : (fun n => (γ.baseZeroLikelihoodMass (u n)).toReal)
      =o[atTop] (fun n => u n ^ 2) := by
    simpa only [Function.comp_apply] using!
      γ.baseZeroLikelihoodMass_isLittleO.comp_tendsto hu_right
  have hmul : (fun n : ℕ => (n : ℝ) *
      (γ.baseZeroLikelihoodMass (u n)).toReal)
      =o[atTop] (fun n => (n : ℝ) * u n ^ 2) :=
    (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO hsmall
  have hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * u n ^ 2 = a ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := by omega
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos_nat
    dsimp only [u]
    rw [mul_pow]
    calc
      (n : ℝ) * (a ^ 2 * (Real.sqrt n)⁻¹ ^ 2) =
          a ^ 2 * ((n : ℝ) * (Real.sqrt n)⁻¹ ^ 2) := by ring
      _ = a ^ 2 := by
        have hfactor : (n : ℝ) * (Real.sqrt n)⁻¹ ^ 2 = 1 := by
          calc
            (n : ℝ) * (Real.sqrt n)⁻¹ ^ 2 =
                (n : ℝ) / Real.sqrt n ^ 2 := by
                  rw [inv_pow, div_eq_mul_inv]
            _ = (n : ℝ) / n := by rw [Real.sq_sqrt hnpos.le]
            _ = 1 := div_self hnpos.ne'
        rw [hfactor, mul_one]
  have hscaleO : (fun n : ℕ => (n : ℝ) * u n ^ 2)
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    (Filter.EventuallyEq.isBigO hscale).trans
      (Asymptotics.isBigO_const_one ℝ (a ^ 2) atTop)
  have hreal : Tendsto (fun n : ℕ => (n : ℝ) *
      (γ.baseZeroLikelihoodMass (u n)).toReal) atTop (nhds 0) := by
    exact (Asymptotics.isLittleO_one_iff ℝ).mp
      (hmul.trans_isBigO hscaleO)
  apply (ENNReal.tendsto_toReal_zero_iff (fun n => by
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n)
      (measure_ne_top P _))).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, u] using hreal

/-- At a nonnegative path parameter, the product of AC parts is the baseline
product weighted by the actual product likelihood.

The proof uses `ht` to obtain the path-law probability/sigma-finiteness
instance, then apply finite-product induction and `withDensity` Fubini.

The side condition is internal and essential: a one-sided path imposes no
condition at negative parameters. -/
theorem pi_acPart_eq_withDensity_acProductLikelihood
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Measure.pi (fun _ : Fin n => γ.acPart t) =
      (Measure.pi (fun _ : Fin n => P)).withDensity
        (γ.acProductLikelihood t n) := by
  letI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  simpa only [acPart, acProductLikelihood] using!
    (MeasureTheory.pi_withDensity_prod (fun _ : Fin n =>
      Measure.measurable_rnDeriv (γ.curve t) P)).symm

/-- Exact integrability and normalization of the actual product likelihood.
The integral is `(1-singularMass)^n`, not one.

The proof passes `ht` to the product AC identity, integrates coordinatewise,
and uses the Lebesgue decomposition. -/
theorem integrable_acProductLikelihood_and_integral
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Integrable (fun X => (γ.acProductLikelihood t n X).toReal)
        (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ X, (γ.acProductLikelihood t n X).toReal
          ∂(Measure.pi (fun _ : Fin n => P)) =
        (1 - (γ.singularMass t).toReal) ^ n := by
  letI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  have h_one : Integrable (fun ω => ((γ.curve t).rnDeriv P ω).toReal) P := by
    simpa only [integrableOn_univ] using
      (Measure.integrableOn_toReal_rnDeriv
        (s := Set.univ) (measure_ne_top (γ.curve t) Set.univ))
  have h_int : ∫ ω, ((γ.curve t).rnDeriv P ω).toReal ∂P =
      1 - (γ.singularMass t).toReal := by
    simpa only [singularMass, singularPart, measureReal_def, measure_univ,
      ENNReal.toReal_one] using
      (Measure.integral_toReal_rnDeriv' (μ := γ.curve t) (ν := P))
  constructor
  · simpa only [acProductLikelihood, ENNReal.toReal_prod] using
      (Integrable.fintype_prod (fun _ : Fin n => h_one))
  · simpa only [acProductLikelihood, ENNReal.toReal_prod, h_int,
      Fintype.card_fin] using
      (MeasureTheory.integral_fintype_prod_eq_pow
        (fun ω => ((γ.curve t).rnDeriv P ω).toReal)
        (ι := Fin n) (μ := P))

/-- Bounded expectations under the full local product law are asymptotically
equal to baseline expectations weighted by the actual RN product likelihood.

The proof expands `(singularPart+acPart)^n`, bounds all terms with a singular
coordinate, and identifies the all-AC term by the product AC identity at the
nonnegative parameter supplied by `ha`; no MGF, uniform-integrability,
absolute-continuity, or normalization assumption is used. -/
theorem product_integral_comparison
    (γ : NondominatedQMDPath P) (a C : ℝ) (ha : 0 ≤ a)
    (f : ∀ n : ℕ, (Fin n → Ω) → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_bound : ∀ n X, |f n X| ≤ C) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧ ∀ n,
      |(∫ X, f n X ∂(Measure.pi (fun _ : Fin n =>
            γ.curve (a * (Real.sqrt n)⁻¹))))
        - ∫ X, f n X *
            (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal
            ∂(Measure.pi (fun _ : Fin n => P))| ≤ error n := by
  classical
  have hC : 0 ≤ C := by
    exact (abs_nonneg (f 0 (fun i => Fin.elim0 i))).trans
      (hf_bound 0 (fun i => Fin.elim0 i))
  let u : ℕ → ℝ := fun n => a * (Real.sqrt n)⁻¹
  let error : ℕ → ℝ := fun n =>
    C * ((n : ℝ≥0∞) * γ.singularMass (u n)).toReal
  refine ⟨error, ?_, ?_⟩
  · have hs := γ.singular_mass_localScale_tendsto a ha
    have hsreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hs
    convert! hsreal.const_mul C using 1
    all_goals simp only [ENNReal.toReal_zero, mul_zero]
  intro n
  have hut : 0 ≤ u n :=
    mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _))
  letI : IsProbabilityMeasure (γ.curve (u n)) :=
    γ.curve_isProbability (u n) hut
  let Q : Measure Ω := γ.curve (u n)
  let A : Measure Ω := γ.acPart (u n)
  let ν : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => Q)
  let ρ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => A)
  let Pn : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => P)
  let L : (Fin n → Ω) → ℝ≥0∞ := γ.acProductLikelihood (u n) n
  have hAQ : A ≤ Q := by
    simpa only [A, Q, acPart] using
      Measure.withDensity_rnDeriv_le (γ.curve (u n)) P
  letI : IsFiniteMeasure A := isFiniteMeasure_of_le Q hAQ
  have hAac : A ≪ Q := hAQ.absolutelyContinuous
  have hρν : ρ ≤ ν := by
    let D : (Fin n → Ω) → ℝ≥0∞ :=
      fun X => ∏ i : Fin n, A.rnDeriv Q (X i)
    have hcoord : ∀ i : Fin n, A.rnDeriv Q ≤ᵐ[Q] 1 :=
      fun _ => Measure.rnDeriv_le_one_of_le hAQ
    have hall : (fun X : Fin n → Ω => fun i => A.rnDeriv Q (X i))
        ≤ᵐ[ν] (fun _ => fun _ : Fin n => (1 : ℝ≥0∞)) := by
      simpa only [ν] using! Measure.ae_le_pi hcoord
    have hDle : D ≤ᵐ[ν] 1 := by
      filter_upwards [hall] with X hX
      dsimp only [D]
      exact Finset.prod_le_one (fun _ _ => zero_le)
        (fun i _ => hX i)
    have htilt : ν.withDensity D = ρ := by
      have hcoordtilt : Q.withDensity (A.rnDeriv Q) = A :=
        Measure.withDensity_rnDeriv_eq A Q hAac
      calc
        ν.withDensity D =
            Measure.pi (fun _ : Fin n => Q.withDensity (A.rnDeriv Q)) := by
          simpa only [ν, D] using
            MeasureTheory.pi_withDensity_prod
              (fun _ : Fin n => Measure.measurable_rnDeriv A Q)
        _ = ρ := by simp only [hcoordtilt, ρ]
    rw [← htilt]
    simpa using withDensity_mono hDle
  let R : Measure (Fin n → Ω) := ν - ρ
  have hRρ : R + ρ = ν := by
    exact Measure.sub_add_cancel_of_le hρν
  have hνprob : IsProbabilityMeasure ν := by
    dsimp only [ν, Q]
    infer_instance
  letI : IsProbabilityMeasure ν := hνprob
  have hfν : Integrable (f n) ν := by
    refine Integrable.of_bound (hf_meas n).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun X => by
      simpa only [Real.norm_eq_abs] using hf_bound n X
  have hfρ : Integrable (f n) ρ := hfν.mono_measure hρν
  have hRν : R ≤ ν := Measure.sub_le
  have hfR : Integrable (f n) R := hfν.mono_measure hRν
  have hfull : ∫ X, f n X ∂ν =
      (∫ X, f n X ∂R) + ∫ X, f n X ∂ρ := by
    rw [← hRρ, integral_add_measure hfR hfρ]
  have hρbase : ρ = Pn.withDensity L := by
    simpa only [ρ, Pn, L, A, u] using
      γ.pi_acPart_eq_withDensity_acProductLikelihood (u n) hut n
  have hLmeas : Measurable L := by
    dsimp only [L, acProductLikelihood]
    exact Finset.measurable_prod _ fun i _ =>
      (Measure.measurable_rnDeriv (γ.curve (u n)) P).comp
        (measurable_pi_apply i)
  have hLfin : ∀ᵐ X ∂Pn, L X < ⊤ := by
    have hcoordfin : ∀ i : Fin n,
        (fun _ : Ω => True) ≤ᵐ[P]
          (fun ω => (γ.curve (u n)).rnDeriv P ω ≠ ⊤) := by
      intro i
      filter_upwards [Measure.rnDeriv_ne_top (γ.curve (u n)) P] with ω hω
      exact fun _ => hω
    have hall : (fun X : Fin n → Ω => fun _ : Fin n => True)
        ≤ᵐ[Pn] (fun X i => (γ.curve (u n)).rnDeriv P (X i) ≠ ⊤) := by
      simpa only [Pn] using Measure.ae_le_pi hcoordfin
    filter_upwards [hall] with X hX
    exact lt_top_iff_ne_top.mpr (by
      dsimp only [L, acProductLikelihood]
      exact ENNReal.prod_ne_top fun i _ => hX i trivial)
  have hweighted : ∫ X, f n X * (L X).toReal ∂Pn =
      ∫ X, f n X ∂ρ := by
    rw [hρbase,
      integral_withDensity_eq_integral_toReal_smul hLmeas hLfin (f n)]
    apply integral_congr_ae
    filter_upwards with X
    simp only [smul_eq_mul, mul_comm]
  have hdiff :
      (∫ X, f n X ∂ν) - ∫ X, f n X * (L X).toReal ∂Pn =
        ∫ X, f n X ∂R := by
    rw [hweighted, hfull]
    ring
  have hboundR : |∫ X, f n X ∂R| ≤ C * R.real Set.univ := by
    have hb := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := R) (f := f n) (C := C)
      (Filter.Eventually.of_forall fun X => by
        simpa only [Real.norm_eq_abs] using hf_bound n X)
    simpa only [Real.norm_eq_abs] using hb
  have hsfin : γ.singularMass (u n) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top (γ.curve (u n)) _)
      (Measure.singularPart_le (γ.curve (u n)) P Set.univ)
  have hsing_le_one : (γ.singularMass (u n)).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    apply (ENNReal.toReal_le_toReal hsfin ENNReal.one_ne_top).2
    calc
      γ.singularMass (u n) ≤ γ.curve (u n) Set.univ :=
        Measure.singularPart_le (γ.curve (u n)) P Set.univ
      _ = 1 := measure_univ
  have hA_mass : (A Set.univ).toReal =
      1 - (γ.singularMass (u n)).toReal := by
    have hdec := γ.curve_eq_singularPart_add_acPart (u n) hut
    have happ := congrArg (fun M : Measure Ω => M Set.univ) hdec
    have hAfin : A Set.univ ≠ ⊤ := measure_ne_top _ _
    have happ' : (1 : ℝ≥0∞) =
        γ.singularMass (u n) + A Set.univ := by
      simpa only [Measure.add_apply, measure_univ, singularMass, singularPart,
        acPart, A] using happ
    have hreal := congrArg ENNReal.toReal happ'
    rw [ENNReal.toReal_one, ENNReal.toReal_add hsfin hAfin] at hreal
    linarith
  have hρ_mass : ρ.real Set.univ =
      (1 - (γ.singularMass (u n)).toReal) ^ n := by
    simp only [ρ, measureReal_def, Measure.pi_univ, Finset.prod_const,
      ENNReal.toReal_pow, hA_mass]
    rw [Finset.card_univ, Fintype.card_fin]
  have hR_mass : R.real Set.univ =
      1 - (1 - (γ.singularMass (u n)).toReal) ^ n := by
    change ((ν - ρ) Set.univ).toReal =
      1 - (1 - (γ.singularMass (u n)).toReal) ^ n
    rw [Measure.sub_apply MeasurableSet.univ hρν,
      ENNReal.toReal_sub_of_le (hρν Set.univ) (measure_ne_top ν Set.univ)]
    have hρ_mass' : (ρ Set.univ).toReal =
        (1 - (γ.singularMass (u n)).toReal) ^ n := by
      simpa only [measureReal_def] using hρ_mass
    rw [measure_univ, ENNReal.toReal_one, hρ_mass']
  have hmissing : R.real Set.univ ≤
      (n : ℝ) * (γ.singularMass (u n)).toReal := by
    rw [hR_mass]
    have hsnonneg : 0 ≤ (γ.singularMass (u n)).toReal :=
      ENNReal.toReal_nonneg
    simpa only [sub_sub_cancel] using
      (one_sub_pow_le_nsmul_one_sub
        (x := 1 - (γ.singularMass (u n)).toReal)
        (by linarith [hsing_le_one]) (by linarith [hsnonneg]) n)
  rw [show (a * (Real.sqrt n)⁻¹) = u n from rfl]
  change |(∫ X, f n X ∂ν) - ∫ X, f n X * (L X).toReal ∂Pn| ≤ error n
  rw [hdiff]
  calc
    |∫ X, f n X ∂R| ≤ C * R.real Set.univ := hboundR
    _ ≤ C * ((n : ℝ) * (γ.singularMass (u n)).toReal) :=
      mul_le_mul_of_nonneg_left hmissing hC
    _ = error n := by
      simp only [error, ENNReal.toReal_mul, ENNReal.toReal_natCast]

end NondominatedQMDPath
end AsymptoticStatistics.Core.NondominatedQMDPath
