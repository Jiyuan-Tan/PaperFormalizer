module
public import StatLean.AsymptoticStatistics.DQM.Properties
public import StatLean.AsymptoticStatistics.DQM.SqrtDensityRatio

@[expose] public section

/-!
# Zero-density mass under DQM

DQM controls, under the true law, the mass on which a nearby density vanishes.
These statements use the full neighbourhood filter and its fixed local-scale
specialization.  They require neither strict positivity nor sigma-finiteness.
-/

namespace AsymptoticStatistics

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Under DQM, the true-law mass of the zero set of a nearby density is
`o(‖θ-θ₀‖²)` on the full neighbourhood of `θ₀`. -/
lemma dqm_zeroDensity_mass_isLittleO
    {𝒳 : Type*} [MeasurableSpace 𝒳] {k : ℕ}
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝒳) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin k))
    -- The model consists of probability densities.
    (hPDF : IsPDFOf M μ)
    -- Differentiability in quadratic mean at the truth.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) :
    (fun θ =>
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)).real
        {x | M.density θ x = 0})
      =o[𝓝 θ₀] (fun θ => ‖θ - θ₀‖ ^ 2) := by
  classical
  let P₀ := μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)
  let W := fun θ : EuclideanSpace ℝ (Fin k) => M.sqrtDensityRatio θ₀ θ
  letI : IsFiniteMeasure P₀ :=
    isFiniteMeasure_withDensity_ofReal
      (hPDF.density_integrable θ₀).hasFiniteIntegral
  have htail : (fun θ => P₀.real {x | 1 ≤ |W θ x|}) =o[𝓝 θ₀]
      (fun θ => ‖θ - θ₀‖ ^ 2) := by
    simpa only [P₀, W] using
      (dqm_sqrtDensityRatio_tail_controls M μ θ₀ ℓ hPDF hDQM
        (fun _ => (0 : ℝ)) MemLp.zero 1 zero_lt_one).2.2.1
  have hsub (θ : EuclideanSpace ℝ (Fin k)) :
      {x | M.density θ x = 0} ⊆ {x | 1 ≤ |W θ x|} := by
    intro x hx
    change M.density θ x = 0 at hx
    dsimp only [W, ParametricFamily.sqrtDensityRatio]
    change 1 ≤ |2 * (Real.sqrt (M.density θ x / M.density θ₀ x) - 1)|
    rw [hx]
    norm_num
  have hdom : (fun θ => P₀.real {x | M.density θ x = 0}) =O[𝓝 θ₀]
      (fun θ => P₀.real {x | 1 ≤ |W θ x|}) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with θ
    simpa only [one_mul, Real.norm_of_nonneg measureReal_nonneg] using
      measureReal_mono (hsub θ) (measure_ne_top P₀ _)
  simpa only [P₀] using hdom.trans_isLittleO htail

/-- Fixed local scales inherit the DQM zero-density estimate after multiplication
by the sample size. -/
lemma dqm_zeroDensity_localScale_tendsto
    {𝒳 : Type*} [MeasurableSpace 𝒳] {k : ℕ}
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝒳) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin k))
    -- The model consists of probability densities.
    (hPDF : IsPDFOf M μ)
    -- Differentiability in quadratic mean at the truth.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (a : EuclideanSpace ℝ (Fin k)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)).real
            {x | M.density
              (θ₀ + (Real.sqrt n)⁻¹ • a) x = 0})
      atTop (𝓝 0) := by
  let θn : ℕ → EuclideanSpace ℝ (Fin k) := fun n =>
    θ₀ + (Real.sqrt n)⁻¹ • a
  have hinvSqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa using! hsqrt.inv_tendsto_atTop
  have hθn : Tendsto θn atTop (𝓝 θ₀) := by
    simpa only [θn, zero_smul, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => θ₀) atTop (𝓝 θ₀)).add
        (hinvSqrt.smul_const a)
  have hsmall :
      (fun n =>
        (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)).real
          {x | M.density (θn n) x = 0}) =o[atTop]
        (fun n => ‖θn n - θ₀‖ ^ 2) := by
    simpa only [Function.comp_apply] using!
      (dqm_zeroDensity_mass_isLittleO M μ θ₀ ℓ hPDF hDQM).comp_tendsto hθn
  have hmul :
      (fun n : ℕ =>
        (n : ℝ) *
          (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)).real
            {x | M.density (θn n) x = 0}) =o[atTop]
        (fun n => (n : ℝ) * ‖θn n - θ₀‖ ^ 2) :=
    (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO hsmall
  have hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * ‖θn n - θ₀‖ ^ 2 = ‖a‖ ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := by omega
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos_nat
    rw [show θn n - θ₀ = (Real.sqrt n)⁻¹ • a by simp [θn]]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow]
    have hfactor :
        (n : ℝ) * (Real.sqrt n)⁻¹ ^ 2 = 1 := by
      calc
        (n : ℝ) * (Real.sqrt n)⁻¹ ^ 2 =
            Real.sqrt n ^ 2 * (Real.sqrt n)⁻¹ ^ 2 := by
          congr 1
          exact (Real.sq_sqrt hnpos.le).symm
        _ = 1 := by simp [hnpos.ne']
    calc
      (n : ℝ) * ((Real.sqrt n)⁻¹ ^ 2 * ‖a‖ ^ 2) =
          ((n : ℝ) * (Real.sqrt n)⁻¹ ^ 2) * ‖a‖ ^ 2 := by ring
      _ = ‖a‖ ^ 2 := by rw [hfactor, one_mul]
  have hscaleO :
      (fun n : ℕ => (n : ℝ) * ‖θn n - θ₀‖ ^ 2) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    (Filter.EventuallyEq.isBigO hscale).trans
      (Asymptotics.isBigO_const_one ℝ (‖a‖ ^ 2) atTop)
  simpa only [θn] using
    (Asymptotics.isLittleO_one_iff ℝ).mp (hmul.trans_isBigO hscaleO)

end AsymptoticStatistics
