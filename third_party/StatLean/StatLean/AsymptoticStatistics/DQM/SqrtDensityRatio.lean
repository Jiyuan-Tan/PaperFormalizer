module
public import StatLean.AsymptoticStatistics.DQM.Properties
public import StatLean.AsymptoticStatistics.ForMathlib.L2Tail
public import StatLean.AsymptoticStatistics.ParametricFamily.FisherInformation
public import StatLean.AsymptoticStatistics.ParametricFamily.SqrtDensityRatio

@[expose] public section

/-!
# DQM expansions in square-root density-ratio coordinates

Named deterministic cores for the population Taylor expansion in van der
Vaart, Theorem 5.39.  They expose the L² linearization, mean, second moment,
and uniform-integrability tails of `Wθ = 2(√(pθ/p₀)-1)`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal RealInnerProductSpace

namespace AsymptoticStatistics

/-- DQM makes the square-root density ratio L²-linear with derivative
`x ↦ ⟨θ-θ₀, ℓ(x)⟩` under the true law. -/
lemma dqm_sqrtDensityRatio_l2_linearization
    {𝒳 : Type*} [MeasurableSpace 𝒳] {k : ℕ}
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝒳) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin k))
    -- Normalized model densities, as in vdV Theorem 5.39.
    (hPDF : IsPDFOf M μ)
    -- DQM at the true parameter, as in vdV Theorem 5.39.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) :
    (∀ᶠ θ in 𝓝 θ₀, MemLp
      (fun x => M.sqrtDensityRatio θ₀ θ x - ⟪θ - θ₀, ℓ x⟫) 2
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))) ∧
    (fun θ => ∫ x, (M.sqrtDensityRatio θ₀ θ x - ⟪θ - θ₀, ℓ x⟫) ^ 2
        ∂(μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
      =o[𝓝 θ₀] (fun θ => ‖θ - θ₀‖ ^ 2) := by
  classical
  let p : 𝒳 → ℝ := M.density θ₀
  let s : EuclideanSpace ℝ (Fin k) → ℝ := fun θ => ‖θ - θ₀‖
  let z : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x => ⟪θ - θ₀, ℓ x⟫
  let W : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ =>
    M.sqrtDensityRatio θ₀ θ
  let r : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x =>
    M.sqrtDensity (θ₀ + (θ - θ₀)) x - M.sqrtDensity θ₀ x
      - (1 / 2 : ℝ) * z θ x * M.sqrtDensity θ₀ x
  have hshift : Tendsto (fun θ : EuclideanSpace ℝ (Fin k) => θ - θ₀)
      (𝓝 θ₀) (𝓝 0) := by
    simpa using! (continuous_id.sub
      (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin k) => θ₀))).tendsto θ₀
  have hrO : (fun θ => ∫ x, r θ x ^ 2 ∂μ) =o[𝓝 θ₀] (fun θ => s θ ^ 2) := by
    simpa only [Function.comp_apply, r, s, z] using!
      hDQM.isLittleO.comp_tendsto hshift
  have hrmem : ∀ᶠ θ in 𝓝 θ₀, MemLp (r θ) 2 μ := by
    simpa only [Function.comp_apply, r, z] using hshift.eventually hDQM.mem
  let score : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x =>
    z θ x * M.sqrtDensity θ₀ x
  have hscore_mem (θ : EuclideanSpace ℝ (Fin k)) : MemLp (score θ) 2 μ := by
    simpa [score, z] using dqm_score_memLp_two M μ θ₀ ℓ
      (hPDF.density_integrable θ₀) hDQM (θ - θ₀)
      (fun t => hPDF.density_integrable _)
  have hW_meas (θ : EuclideanSpace ℝ (Fin k)) : Measurable (W θ) := by
    exact (((M.density_meas θ).div (M.density_meas θ₀)).sqrt.sub_const 1).const_mul 2
  let q : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x =>
    W θ x * M.sqrtDensity θ₀ x - score θ x
  have hq_eq (θ : EuclideanSpace ℝ (Fin k)) :
      q θ = fun x => ({x | p x ≠ 0}.indicator (fun x => 2 * r θ x)) x := by
    funext x
    by_cases hp0 : p x = 0
    · have hs0 : M.sqrtDensity θ₀ x = 0 := by
        simp [ParametricFamily.sqrtDensity, p, hp0]
      rw [Set.indicator_of_notMem (by simpa using hp0)]
      simp [q, score, hs0]
    · have hp : 0 < p x := lt_of_le_of_ne (M.density_nonneg θ₀ x) (Ne.symm hp0)
      have hsqrt_mul : Real.sqrt (M.density θ x / p x) * M.sqrtDensity θ₀ x =
          M.sqrtDensity θ x := by
        rw [show M.sqrtDensity θ₀ x = Real.sqrt (p x) from rfl,
          ← Real.sqrt_mul (div_nonneg (M.density_nonneg θ x) hp.le),
          div_mul_cancel₀ _ hp0]
        rfl
      rw [Set.indicator_of_mem hp0]
      simp only [q, score, W, ParametricFamily.sqrtDensityRatio, r, z]
      rw [show θ₀ + (θ - θ₀) = θ by abel]
      rw [show 2 * (Real.sqrt (M.density θ x / p x) - 1) * M.sqrtDensity θ₀ x =
        2 * (Real.sqrt (M.density θ x / p x) * M.sqrtDensity θ₀ x -
          M.sqrtDensity θ₀ x) by ring, hsqrt_mul]
      ring
  have hqmem : ∀ᶠ θ in 𝓝 θ₀, MemLp (q θ) 2 μ := by
    filter_upwards [hrmem] with θ hmem
    rw [hq_eq θ]
    exact (hmem.const_mul 2).indicator
      (measurableSet_eq_fun (M.density_meas θ₀) measurable_const).compl
  have hqO : (fun θ => ∫ x, q θ x ^ 2 ∂μ) =o[𝓝 θ₀] (fun θ => s θ ^ 2) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hb := (Asymptotics.isLittleO_iff.mp hrO) (show 0 < c / 4 by positivity)
    filter_upwards [hb, hqmem, hrmem] with θ hb hqm hrm
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hb ⊢
    have hle : ∫ x, q θ x ^ 2 ∂μ ≤ 4 * ∫ x, r θ x ^ 2 ∂μ := by
      calc
        ∫ x, q θ x ^ 2 ∂μ ≤ ∫ x, (2 * r θ x) ^ 2 ∂μ :=
          integral_mono hqm.integrable_sq (hrm.const_mul 2).integrable_sq (fun x => by
            rw [hq_eq θ]
            by_cases hx : p x ≠ 0 <;> simp [hx, sq_nonneg])
        _ = 4 * ∫ x, r θ x ^ 2 ∂μ := by
          simp_rw [mul_pow]
          rw [integral_const_mul]
          ring
    exact hle.trans (by nlinarith)
  let P₀ : Measure 𝒳 := μ.withDensity fun x => ENNReal.ofReal (p x)
  letI : IsFiniteMeasure P₀ :=
    isFiniteMeasure_withDensity_ofReal (hPDF.density_integrable θ₀).hasFiniteIntegral
  let qp : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x => W θ x - z θ x
  have hWmem : ∀ᶠ θ in 𝓝 θ₀, MemLp (W θ) 2 P₀ := by
    filter_upwards [hqmem] with θ hqm
    refine (memLp_two_iff_integrable_sq (hW_meas θ).aestronglyMeasurable).2 ?_
    change Integrable (fun x => W θ x ^ 2)
      (μ.withDensity fun x => ENNReal.ofReal (p x))
    rw [integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal (by simp)]
    have hi : Integrable (fun x => (q θ x + score θ x) ^ 2) μ :=
      (hqm.add (hscore_mem θ)).integrable_sq
    refine hi.congr ?_
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x)]
    simp only [q, score]
    rw [← M.sqrtDensity_sq θ₀ x]
    ring
  have hbase_pos : ∀ᵐ x ∂P₀, 0 < M.sqrtDensity θ₀ x := by
    change ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (p x)),
      0 < M.sqrtDensity θ₀ x
    rw [ae_withDensity_iff (M.density_meas θ₀).ennreal_ofReal]
    filter_upwards with x
    intro hx
    have hofpos : 0 < ENNReal.ofReal (M.density θ₀ x) :=
      bot_lt_iff_ne_bot.mpr hx
    exact Real.sqrt_pos.mpr (ENNReal.ofReal_pos.mp hofpos)
  have hqpmem : ∀ᶠ θ in 𝓝 θ₀, MemLp (qp θ) 2 P₀ := by
    filter_upwards [hWmem] with θ hwm
    have hdiv_meas : AEStronglyMeasurable
        (fun x => score θ x / M.sqrtDensity θ₀ x) P₀ :=
      (((hscore_mem θ).1.mul (M.sqrtDensity_meas θ₀).inv.aestronglyMeasurable).mono_ac
        (withDensity_absolutelyContinuous _ _))
    have hzeq : (fun x => score θ x / M.sqrtDensity θ₀ x) =ᵐ[P₀] z θ := by
      filter_upwards [hbase_pos] with x hx
      simp only [score]
      field_simp [hx.ne']
    have hzmem : MemLp (z θ) 2 P₀ := by
      refine (memLp_two_iff_integrable_sq (hdiv_meas.congr hzeq)).2 ?_
      change Integrable (fun x => z θ x ^ 2)
        (μ.withDensity fun x => ENNReal.ofReal (p x))
      rw [integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal (by simp)]
      refine (hscore_mem θ).integrable_sq.congr ?_
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x),
        ← M.sqrtDensity_sq θ₀ x]
      simp only [score]
      ring
    exact hwm.sub hzmem
  have hqpSq (θ : EuclideanSpace ℝ (Fin k)) :
      ∫ x, qp θ x ^ 2 ∂P₀ = ∫ x, q θ x ^ 2 ∂μ := by
    change (∫ x, qp θ x ^ 2 ∂μ.withDensity (fun x => ENNReal.ofReal (p x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul
      (M.density_meas θ₀).ennreal_ofReal (by simp)]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x),
      ← M.sqrtDensity_sq θ₀ x]
    simp only [qp, q, score, smul_eq_mul]
    ring
  have hqpO : (fun θ => ∫ x, qp θ x ^ 2 ∂P₀) =o[𝓝 θ₀]
      (fun θ => s θ ^ 2) := by
    convert hqO using 1
    funext θ
    exact hqpSq θ
  simpa only [qp, W, z, P₀, p, s] using And.intro hqpmem hqpO

/-- The mean of the square-root density ratio is minus the Hellinger
distance, hence has leading term `-I(θ-θ₀)/4`. -/
lemma dqm_sqrtDensityRatio_mean_expansion
    {𝒳 : Type*} [MeasurableSpace 𝒳] {k : ℕ}
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝒳) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin k))
    -- Normalized model densities, as in vdV Theorem 5.39.
    (hPDF : IsPDFOf M μ)
    -- DQM at the true parameter, as in vdV Theorem 5.39.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) :
    (fun θ =>
      (∫ x, M.sqrtDensityRatio θ₀ θ x
        ∂(μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
        + (1 / 4 : ℝ) * fisherInformation M μ θ₀ ℓ (θ - θ₀) (θ - θ₀))
      =o[𝓝 θ₀] (fun θ => ‖θ - θ₀‖ ^ 2) := by
  classical
  let p : 𝒳 → ℝ := M.density θ₀
  let s : EuclideanSpace ℝ (Fin k) → ℝ := fun θ => ‖θ - θ₀‖
  let z : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x => ⟪θ - θ₀, ℓ x⟫
  let score : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x =>
    z θ x * M.sqrtDensity θ₀ x
  let r : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x =>
    M.sqrtDensity (θ₀ + (θ - θ₀)) x - M.sqrtDensity θ₀ x
      - (1 / 2 : ℝ) * z θ x * M.sqrtDensity θ₀ x
  have hshift : Tendsto (fun θ : EuclideanSpace ℝ (Fin k) => θ - θ₀)
      (𝓝 θ₀) (𝓝 0) := by
    simpa using! (continuous_id.sub
      (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin k) => θ₀))).tendsto θ₀
  have hrO : (fun θ => ∫ x, r θ x ^ 2 ∂μ) =o[𝓝 θ₀] (fun θ => s θ ^ 2) := by
    simpa only [Function.comp_apply, r, score, z, s] using!
      hDQM.isLittleO.comp_tendsto hshift
  have hrmem : ∀ᶠ θ in 𝓝 θ₀, MemLp (r θ) 2 μ := by
    simpa only [Function.comp_apply, r, score, z] using hshift.eventually hDQM.mem
  have hscore_mem (θ : EuclideanSpace ℝ (Fin k)) : MemLp (score θ) 2 μ := by
    simpa [score, z] using dqm_score_memLp_two M μ θ₀ ℓ
      (hPDF.density_integrable θ₀) hDQM (θ - θ₀)
      (fun t => hPDF.density_integrable _)
  let J : EuclideanSpace ℝ (Fin k) → ℝ := fun θ =>
    ∫ x, z θ x ^ 2 * p x ∂μ
  have hJint (θ : EuclideanSpace ℝ (Fin k)) :
      Integrable (fun x => z θ x ^ 2 * p x) μ :=
    dqm_fisher_integrable M μ θ₀ ℓ (hPDF.density_integrable θ₀) hDQM (θ - θ₀)
      (fun t => hPDF.density_integrable _)
  have hnormint : Integrable (fun x => ‖ℓ x‖ ^ 2 * p x) μ :=
    dqm_norm_sq_score_integrable M μ θ₀ ℓ (hPDF.density_integrable θ₀) hDQM
      (fun _ _ => hPDF.density_integrable _)
  let C : ℝ := ∫ x, ‖ℓ x‖ ^ 2 * p x ∂μ
  have hJbd (θ : EuclideanSpace ℝ (Fin k)) : J θ ≤ C * s θ ^ 2 := by
    calc
      J θ ≤ ∫ x, s θ ^ 2 * (‖ℓ x‖ ^ 2 * p x) ∂μ := by
        apply integral_mono (hJint θ) (hnormint.const_mul _)
        intro x
        have hi := real_inner_mul_inner_self_le (θ - θ₀) (ℓ x)
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← sq] at hi
        simpa only [z, p, s, mul_assoc] using
          mul_le_mul_of_nonneg_right hi (M.density_nonneg θ₀ x)
      _ = C * s θ ^ 2 := by rw [integral_const_mul]; ring
  have hJO : J =O[𝓝 θ₀] (fun θ => s θ ^ 2) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, Filter.Eventually.of_forall fun θ => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (M.density_nonneg θ₀ x)), Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact hJbd θ
  have hJfisher (θ : EuclideanSpace ℝ (Fin k)) :
      J θ = fisherInformation M μ θ₀ ℓ (θ - θ₀) (θ - θ₀) := by
    simp [J, z, p, fisherInformation, pow_two]
  have hscoreSq (θ : EuclideanSpace ℝ (Fin k)) :
      ∫ x, score θ x ^ 2 ∂μ = J θ := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [score, z, p, mul_pow, M.sqrtDensity_sq]
  have hscoreO : (fun θ => ∫ x, score θ x ^ 2 ∂μ) =O[𝓝 θ₀]
      (fun θ => s θ ^ 2) := by
    convert hJO using 1
    funext θ
    exact hscoreSq θ
  have hrscoreO : (fun θ => ∫ x, r θ x * score θ x ∂μ) =o[𝓝 θ₀]
      (fun θ => s θ ^ 2) :=
    L2Utils.integral_mul_isLittleO_of_sq (𝓝 θ₀) μ r score (fun θ => s θ ^ 2)
      hrmem (fun θ => hscore_mem θ) (Eventually.of_forall fun θ => sq_nonneg (s θ))
      hrO hscoreO
  let H : EuclideanSpace ℝ (Fin k) → ℝ := fun θ =>
    ∫ x, (M.sqrtDensity θ x - M.sqrtDensity θ₀ x) ^ 2 ∂μ
  have hHcore : (fun θ => H θ - (1 / 4 : ℝ) * J θ) =o[𝓝 θ₀]
      (fun θ => s θ ^ 2) := by
    apply EventuallyEq.trans_isLittleO _ (hrO.add hrscoreO)
    filter_upwards [hrmem] with θ hrm
    have hs2 : Integrable (fun x => score θ x ^ 2) μ := (hscore_mem θ).integrable_sq
    have hrs : Integrable (fun x => r θ x * score θ x) μ :=
      hrm.integrable_mul (hscore_mem θ)
    have hH : H θ = ∫ x, (r θ x ^ 2 + r θ x * score θ x) +
        (1 / 4 : ℝ) * score θ x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [r, score]
      rw [show θ₀ + (θ - θ₀) = θ by abel]
      ring
    have hsplit₁ : (∫ x, (r θ x ^ 2 + r θ x * score θ x) +
        (1 / 4 : ℝ) * score θ x ^ 2 ∂μ) =
        (∫ x, r θ x ^ 2 + r θ x * score θ x ∂μ) +
          ∫ x, (1 / 4 : ℝ) * score θ x ^ 2 ∂μ :=
      integral_add (hrm.integrable_sq.add hrs) (hs2.const_mul (1 / 4 : ℝ))
    have hsplit₂ : (∫ x, r θ x ^ 2 + r θ x * score θ x ∂μ) =
        (∫ x, r θ x ^ 2 ∂μ) + ∫ x, r θ x * score θ x ∂μ :=
      integral_add hrm.integrable_sq hrs
    rw [hH, hsplit₁, hsplit₂, integral_const_mul, hscoreSq θ]
    ring
  let P₀ : Measure 𝒳 := μ.withDensity fun x => ENNReal.ofReal (p x)
  let W : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ => M.sqrtDensityRatio θ₀ θ
  let EW : EuclideanSpace ℝ (Fin k) → ℝ := fun θ => ∫ x, W θ x ∂P₀
  have hEW (θ : EuclideanSpace ℝ (Fin k)) : EW θ = -H θ := by
    have hdint := hPDF.density_integrable θ
    have hpint := hPDF.density_integrable θ₀
    have hHint : Integrable
        (fun x => (M.sqrtDensity θ x - M.sqrtDensity θ₀ x) ^ 2) μ :=
      ((M.sqrtDensity_memLp_two μ θ hdint).sub
        (M.sqrtDensity_memLp_two μ θ₀ hpint)).integrable_sq
    have hpt (x : 𝒳) : W θ x * p x = M.density θ x - p x -
        (M.sqrtDensity θ x - M.sqrtDensity θ₀ x) ^ 2 := by
      by_cases hp0 : p x = 0
      · have hs0 : M.sqrtDensity θ₀ x = 0 := by
          simp [ParametricFamily.sqrtDensity, p, hp0]
        simp [W, ParametricFamily.sqrtDensityRatio, hp0, hs0, M.sqrtDensity_sq]
      · have hp : 0 < p x := lt_of_le_of_ne (M.density_nonneg θ₀ x) (Ne.symm hp0)
        have hsqrt_mul : Real.sqrt (M.density θ x / p x) * M.sqrtDensity θ₀ x =
            M.sqrtDensity θ x := by
          rw [show M.sqrtDensity θ₀ x = Real.sqrt (p x) from rfl,
            ← Real.sqrt_mul (div_nonneg (M.density_nonneg θ x) hp.le),
            div_mul_cancel₀ _ hp0]
          rfl
        rw [← M.sqrtDensity_sq θ x,
          show p x = M.sqrtDensity θ₀ x ^ 2 from (M.sqrtDensity_sq θ₀ x).symm]
        simp only [W, ParametricFamily.sqrtDensityRatio]
        rw [show 2 * (Real.sqrt (M.density θ x / p x) - 1) *
          M.sqrtDensity θ₀ x ^ 2 = 2 *
            (Real.sqrt (M.density θ x / p x) * M.sqrtDensity θ₀ x -
              M.sqrtDensity θ₀ x) * M.sqrtDensity θ₀ x by ring, hsqrt_mul]
        ring
    change (∫ x, W θ x ∂μ.withDensity (fun x => ENNReal.ofReal (p x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul
      (M.density_meas θ₀).ennreal_ofReal (by simp)]
    have heq : (∫ x, (ENNReal.ofReal (p x)).toReal • W θ x ∂μ) =
        ∫ x, M.density θ x - p x -
          (M.sqrtDensity θ x - M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x), smul_eq_mul, mul_comm]
      exact hpt x
    have hpint' : Integrable p μ := by simpa [p] using hpint
    have hsplit₁ : (∫ x, M.density θ x - p x -
        (M.sqrtDensity θ x - M.sqrtDensity θ₀ x) ^ 2 ∂μ) =
        (∫ x, M.density θ x - p x ∂μ) -
          ∫ x, (M.sqrtDensity θ x - M.sqrtDensity θ₀ x) ^ 2 ∂μ :=
      integral_sub (hdint.sub hpint') hHint
    have hsplit₂ : (∫ x, M.density θ x - p x ∂μ) =
        (∫ x, M.density θ x ∂μ) - ∫ x, p x ∂μ :=
      integral_sub hdint hpint'
    rw [heq, hsplit₁, hsplit₂, hPDF.density_integral_eq_one]
    simp [p, hPDF.density_integral_eq_one, H]
  have hEWcore : (fun θ => EW θ + (1 / 4 : ℝ) * J θ) =o[𝓝 θ₀]
      (fun θ => s θ ^ 2) := by
    apply EventuallyEq.trans_isLittleO _ (hHcore.const_mul_left (-1))
    filter_upwards with θ
    rw [hEW θ]
    ring
  simpa only [EW, W, P₀, p, J, hJfisher, s] using hEWcore

/-- The second moment of the square-root density ratio has leading term the
Fisher quadratic form. -/
lemma dqm_sqrtDensityRatio_sq_expansion
    {𝒳 : Type*} [MeasurableSpace 𝒳] {k : ℕ}
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝒳) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin k))
    -- Normalized model densities, as in vdV Theorem 5.39.
    (hPDF : IsPDFOf M μ)
    -- DQM at the true parameter, as in vdV Theorem 5.39.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) :
    (fun θ =>
      (∫ x, M.sqrtDensityRatio θ₀ θ x ^ 2
        ∂(μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
        - fisherInformation M μ θ₀ ℓ (θ - θ₀) (θ - θ₀))
      =o[𝓝 θ₀] (fun θ => ‖θ - θ₀‖ ^ 2) := by
  classical
  let p : 𝒳 → ℝ := M.density θ₀
  let P₀ : Measure 𝒳 := μ.withDensity fun x => ENNReal.ofReal (p x)
  let s : EuclideanSpace ℝ (Fin k) → ℝ := fun θ => ‖θ - θ₀‖
  let z : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x => ⟪θ - θ₀, ℓ x⟫
  let W : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ =>
    M.sqrtDensityRatio θ₀ θ
  let q : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x => W θ x - z θ x
  have hlinear := dqm_sqrtDensityRatio_l2_linearization M μ θ₀ ℓ hPDF hDQM
  have hqmem : ∀ᶠ θ in 𝓝 θ₀, MemLp (q θ) 2 P₀ := by
    simpa only [q, W, z, P₀, p] using hlinear.1
  have hqO : (fun θ => ∫ x, q θ x ^ 2 ∂P₀) =o[𝓝 θ₀]
      (fun θ => s θ ^ 2) := by
    simpa only [q, W, z, P₀, p, s] using hlinear.2
  let score : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x =>
    z θ x * M.sqrtDensity θ₀ x
  have hscore_mem (θ : EuclideanSpace ℝ (Fin k)) : MemLp (score θ) 2 μ := by
    simpa [score, z] using dqm_score_memLp_two M μ θ₀ ℓ
      (hPDF.density_integrable θ₀) hDQM (θ - θ₀)
      (fun _ => hPDF.density_integrable _)
  have hbase_pos : ∀ᵐ x ∂P₀, 0 < M.sqrtDensity θ₀ x := by
    change ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (p x)),
      0 < M.sqrtDensity θ₀ x
    rw [ae_withDensity_iff (M.density_meas θ₀).ennreal_ofReal]
    filter_upwards with x
    intro hx
    have hofpos : 0 < ENNReal.ofReal (M.density θ₀ x) :=
      bot_lt_iff_ne_bot.mpr hx
    exact Real.sqrt_pos.mpr (ENNReal.ofReal_pos.mp hofpos)
  have hzmem (θ : EuclideanSpace ℝ (Fin k)) : MemLp (z θ) 2 P₀ := by
    have hdiv_meas : AEStronglyMeasurable
        (fun x => score θ x / M.sqrtDensity θ₀ x) P₀ :=
      (((hscore_mem θ).1.mul (M.sqrtDensity_meas θ₀).inv.aestronglyMeasurable).mono_ac
        (withDensity_absolutelyContinuous _ _))
    have hzeq : (fun x => score θ x / M.sqrtDensity θ₀ x) =ᵐ[P₀] z θ := by
      filter_upwards [hbase_pos] with x hx
      simp only [score]
      field_simp [hx.ne']
    refine (memLp_two_iff_integrable_sq (hdiv_meas.congr hzeq)).2 ?_
    change Integrable (fun x => z θ x ^ 2)
      (μ.withDensity fun x => ENNReal.ofReal (p x))
    rw [integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal (by simp)]
    refine (hscore_mem θ).integrable_sq.congr ?_
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x),
      ← M.sqrtDensity_sq θ₀ x]
    simp only [score]
    ring
  let J : EuclideanSpace ℝ (Fin k) → ℝ := fun θ =>
    ∫ x, z θ x ^ 2 * p x ∂μ
  have hJint (θ : EuclideanSpace ℝ (Fin k)) :
      Integrable (fun x => z θ x ^ 2 * p x) μ :=
    dqm_fisher_integrable M μ θ₀ ℓ (hPDF.density_integrable θ₀) hDQM (θ - θ₀)
      (fun _ => hPDF.density_integrable _)
  have hnormint : Integrable (fun x => ‖ℓ x‖ ^ 2 * p x) μ :=
    dqm_norm_sq_score_integrable M μ θ₀ ℓ (hPDF.density_integrable θ₀) hDQM
      (fun _ _ => hPDF.density_integrable _)
  let C : ℝ := ∫ x, ‖ℓ x‖ ^ 2 * p x ∂μ
  have hJbd (θ : EuclideanSpace ℝ (Fin k)) : J θ ≤ C * s θ ^ 2 := by
    calc
      J θ ≤ ∫ x, s θ ^ 2 * (‖ℓ x‖ ^ 2 * p x) ∂μ := by
        apply integral_mono (hJint θ) (hnormint.const_mul _)
        intro x
        have hi := real_inner_mul_inner_self_le (θ - θ₀) (ℓ x)
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← sq] at hi
        simpa only [z, p, s, mul_assoc] using
          mul_le_mul_of_nonneg_right hi (M.density_nonneg θ₀ x)
      _ = C * s θ ^ 2 := by rw [integral_const_mul]; ring
  have hJO : J =O[𝓝 θ₀] (fun θ => s θ ^ 2) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, Filter.Eventually.of_forall fun θ => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (M.density_nonneg θ₀ x)), Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact hJbd θ
  have hJfisher (θ : EuclideanSpace ℝ (Fin k)) :
      J θ = fisherInformation M μ θ₀ ℓ (θ - θ₀) (θ - θ₀) := by
    simp [J, z, p, fisherInformation, pow_two]
  have hzSq (θ : EuclideanSpace ℝ (Fin k)) :
      ∫ x, z θ x ^ 2 ∂P₀ = J θ := by
    change (∫ x, z θ x ^ 2
      ∂μ.withDensity (fun x => ENNReal.ofReal (p x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul
      (M.density_meas θ₀).ennreal_ofReal (by simp)]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x)]
    simp only [smul_eq_mul, p]
    ring
  have hzO : (fun θ => ∫ x, z θ x ^ 2 ∂P₀) =O[𝓝 θ₀]
      (fun θ => s θ ^ 2) := by
    convert hJO using 1
    funext θ
    exact hzSq θ
  have hqzO : (fun θ => ∫ x, q θ x * z θ x ∂P₀) =o[𝓝 θ₀]
      (fun θ => s θ ^ 2) :=
    L2Utils.integral_mul_isLittleO_of_sq (𝓝 θ₀) P₀ q z (fun θ => s θ ^ 2)
      hqmem hzmem (Eventually.of_forall fun θ => sq_nonneg (s θ)) hqO hzO
  have hsum := hqO.add (hqzO.const_mul_left 2)
  apply EventuallyEq.trans_isLittleO _ hsum
  filter_upwards [hqmem] with θ hqm
  have hzint : Integrable (fun x => z θ x ^ 2) P₀ := (hzmem θ).integrable_sq
  have hqzint : Integrable (fun x => q θ x * z θ x) P₀ :=
    hqm.integrable_mul (hzmem θ)
  have hW : (∫ x, W θ x ^ 2 ∂P₀) =
      ∫ x, (q θ x ^ 2 + 2 * (q θ x * z θ x)) + z θ x ^ 2 ∂P₀ := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [q]
    ring
  have hsplit₁ : (∫ x,
      (q θ x ^ 2 + 2 * (q θ x * z θ x)) + z θ x ^ 2 ∂P₀) =
      (∫ x, q θ x ^ 2 + 2 * (q θ x * z θ x) ∂P₀) +
        ∫ x, z θ x ^ 2 ∂P₀ :=
    integral_add (hqm.integrable_sq.add (hqzint.const_mul 2)) hzint
  have hsplit₂ : (∫ x, q θ x ^ 2 + 2 * (q θ x * z θ x) ∂P₀) =
      (∫ x, q θ x ^ 2 ∂P₀) + ∫ x, 2 * (q θ x * z θ x) ∂P₀ :=
    integral_add hqm.integrable_sq (hqzint.const_mul 2)
  rw [hW, hsplit₁, hsplit₂, integral_const_mul, hzSq θ, hJfisher θ]
  ring

/-- The five explicit tail controls required by the integrated log-Taylor
remainder.  They follow from DQM linearization and an arbitrary L² envelope;
no positivity or sigma-finiteness assumption is needed. -/
lemma dqm_sqrtDensityRatio_tail_controls
    {𝒳 : Type*} [MeasurableSpace 𝒳] {k : ℕ}
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝒳) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin k))
    -- Normalized model densities, as in vdV Theorem 5.39.
    (hPDF : IsPDFOf M μ)
    -- DQM at the true parameter, as in vdV Theorem 5.39.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (m : 𝒳 → ℝ)
    -- The `L²` local log-Lipschitz envelope from vdV Theorem 5.39.
    (hm : MemLp m 2
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    (delta : ℝ) (hdelta : 0 < delta) :
    let P₀ := μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)
    let W := fun θ => M.sqrtDensityRatio θ₀ θ
    Tendsto (fun θ => P₀ {x | delta ≤ |W θ x|}) (𝓝 θ₀) (𝓝 0) ∧
      (fun θ => ∫ x in {x | delta ≤ |W θ x|}, W θ x ^ 2 ∂P₀)
        =o[𝓝 θ₀] (fun θ => ‖θ - θ₀‖ ^ 2) ∧
      (fun θ => P₀.real {x | delta ≤ |W θ x|})
        =o[𝓝 θ₀] (fun θ => ‖θ - θ₀‖ ^ 2) ∧
      (fun θ => ‖θ - θ₀‖ * ∫ x in {x | delta ≤ |W θ x|}, |m x| ∂P₀)
        =o[𝓝 θ₀] (fun θ => ‖θ - θ₀‖ ^ 2) ∧
      (fun θ => ∫ x in {x | delta ≤ |W θ x|}, |W θ x| ∂P₀)
        =o[𝓝 θ₀] (fun θ => ‖θ - θ₀‖ ^ 2) := by
  classical
  let p : 𝒳 → ℝ := M.density θ₀
  let P₀ : Measure 𝒳 := μ.withDensity fun x => ENNReal.ofReal (p x)
  let W : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ =>
    M.sqrtDensityRatio θ₀ θ
  let z : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x => ⟪θ - θ₀, ℓ x⟫
  let q : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x => W θ x - z θ x
  let s : EuclideanSpace ℝ (Fin k) → ℝ := fun θ => ‖θ - θ₀‖
  let g : 𝒳 → ℝ := fun x => ‖ℓ x‖ ^ 2
  letI : IsFiniteMeasure P₀ :=
    isFiniteMeasure_withDensity_ofReal (hPDF.density_integrable θ₀).hasFiniteIntegral
  have hW_meas (θ : EuclideanSpace ℝ (Fin k)) : Measurable (W θ) := by
    exact (((M.density_meas θ).div (M.density_meas θ₀)).sqrt.sub_const 1).const_mul 2
  have hlinear := dqm_sqrtDensityRatio_l2_linearization M μ θ₀ ℓ hPDF hDQM
  have hqmem : ∀ᶠ θ in 𝓝 θ₀, MemLp (q θ) 2 P₀ := by
    simpa only [q, W, z, P₀, p] using hlinear.1
  have hqO : (fun θ => ∫ x, q θ x ^ 2 ∂P₀) =o[𝓝 θ₀]
      (fun θ => s θ ^ 2) := by
    simpa only [q, W, z, P₀, p, s] using hlinear.2
  let score : EuclideanSpace ℝ (Fin k) → 𝒳 → ℝ := fun θ x =>
    z θ x * M.sqrtDensity θ₀ x
  have hscore_mem (θ : EuclideanSpace ℝ (Fin k)) : MemLp (score θ) 2 μ := by
    simpa [score, z] using dqm_score_memLp_two M μ θ₀ ℓ
      (hPDF.density_integrable θ₀) hDQM (θ - θ₀)
      (fun _ => hPDF.density_integrable _)
  have hbase_pos : ∀ᵐ x ∂P₀, 0 < M.sqrtDensity θ₀ x := by
    change ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (p x)),
      0 < M.sqrtDensity θ₀ x
    rw [ae_withDensity_iff (M.density_meas θ₀).ennreal_ofReal]
    filter_upwards with x
    intro hx
    have hofpos : 0 < ENNReal.ofReal (M.density θ₀ x) :=
      bot_lt_iff_ne_bot.mpr hx
    exact Real.sqrt_pos.mpr (ENNReal.ofReal_pos.mp hofpos)
  have hzmem (θ : EuclideanSpace ℝ (Fin k)) : MemLp (z θ) 2 P₀ := by
    have hdiv_meas : AEStronglyMeasurable
        (fun x => score θ x / M.sqrtDensity θ₀ x) P₀ :=
      (((hscore_mem θ).1.mul (M.sqrtDensity_meas θ₀).inv.aestronglyMeasurable).mono_ac
        (withDensity_absolutelyContinuous _ _))
    have hzeq : (fun x => score θ x / M.sqrtDensity θ₀ x) =ᵐ[P₀] z θ := by
      filter_upwards [hbase_pos] with x hx
      simp only [score]
      field_simp [hx.ne']
    refine (memLp_two_iff_integrable_sq (hdiv_meas.congr hzeq)).2 ?_
    change Integrable (fun x => z θ x ^ 2)
      (μ.withDensity fun x => ENNReal.ofReal (p x))
    rw [integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal (by simp)]
    refine (hscore_mem θ).integrable_sq.congr ?_
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x),
      ← M.sqrtDensity_sq θ₀ x]
    simp only [score]
    ring
  have hWmem : ∀ᶠ θ in 𝓝 θ₀, MemLp (W θ) 2 P₀ := by
    filter_upwards [hqmem] with θ hqm
    convert hqm.add (hzmem θ) using 1
    funext x
    simp [q]
  have hs0 : Tendsto (fun θ => s θ ^ 2) (𝓝 θ₀) (𝓝 0) := by
    have hs : Tendsto s (𝓝 θ₀) (𝓝 0) := by
      simpa [s] using! (continuous_norm.comp
        (continuous_id.sub
          (continuous_const : Continuous
            (fun _ : EuclideanSpace ℝ (Fin k) => θ₀)))).tendsto θ₀
    simpa using hs.pow 2
  have hsqrem := dqm_sqrtDensityRatio_sq_expansion M μ θ₀ ℓ hPDF hDQM
  have hrem0 : Tendsto
      (fun θ => (∫ x, W θ x ^ 2 ∂P₀) -
        fisherInformation M μ θ₀ ℓ (θ - θ₀) (θ - θ₀))
      (𝓝 θ₀) (𝓝 0) := by
    apply (show (fun θ => (∫ x, W θ x ^ 2 ∂P₀) -
      fisherInformation M μ θ₀ ℓ (θ - θ₀) (θ - θ₀)) =o[𝓝 θ₀]
        (fun θ => s θ ^ 2) by
          simpa only [W, P₀, p, s] using hsqrem).trans_tendsto hs0
  have hshift : Tendsto (fun θ : EuclideanSpace ℝ (Fin k) => θ - θ₀)
      (𝓝 θ₀) (𝓝 0) := by
    simpa using! (continuous_id.sub
      (continuous_const : Continuous
        (fun _ : EuclideanSpace ℝ (Fin k) => θ₀))).tendsto θ₀
  have hfisher0 : Tendsto
      (fun θ => fisherInformation M μ θ₀ ℓ (θ - θ₀) (θ - θ₀))
      (𝓝 θ₀) (𝓝 0) := by
    simpa [fisherInformation, pow_two] using!
      (dqm_fisher_cont M μ θ₀ ℓ (hPDF.density_integrable θ₀) hDQM
        (fun _ _ => hPDF.density_integrable _)).comp hshift
  have hWsq0 : Tendsto (fun θ => ∫ x, W θ x ^ 2 ∂P₀) (𝓝 θ₀) (𝓝 0) := by
    simpa only [sub_add_cancel, zero_add] using hrem0.add hfisher0
  have hnormint : Integrable (fun x => ‖ℓ x‖ ^ 2 * p x) μ :=
    dqm_norm_sq_score_integrable M μ θ₀ ℓ (hPDF.density_integrable θ₀) hDQM
      (fun _ _ => hPDF.density_integrable _)
  have hg : Integrable g P₀ := by
    change Integrable g (μ.withDensity fun x => ENNReal.ofReal (p x))
    rw [integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal (by simp)]
    refine hnormint.congr ?_
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x)]
  have hz_sq_le (θ : EuclideanSpace ℝ (Fin k)) (x : 𝒳) :
      z θ x ^ 2 ≤ s θ ^ 2 * g x := by
    have hi := real_inner_mul_inner_self_le (θ - θ₀) (ℓ x)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← sq] at hi
    simpa only [z, s, g] using hi
  simpa only [P₀, W, p, s] using
    L2Utils.l2_tail_controls_of_approx (𝓝 θ₀) P₀ W q z s g hW_meas hWmem hWsq0
      hqmem hqO hg (Eventually.of_forall fun x => sq_nonneg ‖ℓ x‖)
      (fun _ => norm_nonneg _) (fun _ _ => (sub_add_cancel _ _).symm) hz_sq_le m hm delta hdelta

end AsymptoticStatistics
