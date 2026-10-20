module
public import StatLean.AsymptoticStatistics.DQM.LogDensity
public import StatLean.AsymptoticStatistics.DQM.SqrtDensityRatio
public import StatLean.AsymptoticStatistics.ForMathlib.LogTaylorIntegral
public import StatLean.AsymptoticStatistics.ParametricFamily.FisherInformation

@[expose] public section

/-!
# Population Taylor expansion for a DQM log-density

This module reserves the deterministic population-expansion core in van der Vaart,
*Asymptotic Statistics*, Theorem 5.39 (pp. 65--66). For the true law
`P₀ = p_{θ₀} · μ`, DQM and the local `L²(P₀)` log-Lipschitz envelope give

`P₀ (log p_θ - log p_{θ₀}) = -1/2 I_{θ₀}(θ-θ₀, θ-θ₀) + o(‖θ-θ₀‖²)`.

The proof combines three ingredients:

1. the full-filter Hellinger/`W` mean expansion;
2. the full-filter `W²` expansion identifying the Fisher quadratic form;
3. uniform-integrability control of the logarithmic Taylor remainder;
4. the zero-density adapter from `Real.log (p_θ / p_{θ₀})` to the difference of
   `logDensity` values.

The fourth core is where Mathlib's convention `Real.log 0 = 0` must be handled. DQM controls
the nearby zero-set mass; no strict-positivity or sigma-finiteness assumption is reserved.
-/

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace AsymptoticStatistics

/-- **Population quadratic expansion for the log-density criterion (vdV Theorem 5.39).**

At a finite-dimensional DQM point `θ₀`, the expected log-density increment under the true
law has quadratic term `-I_{θ₀}/2`. The conclusion is stated on the full neighborhood filter,
not merely along perturbations of the form `θ₀ + h / √n`.

The local domination premise is the base-point consequence of vdV's pairwise local
log-Lipschitz condition. Its `L²(P₀)` envelope is necessary because it controls the criterion on
nearby density-zero sets without assuming that nearby densities are strictly positive.
-/
theorem dqm_logDensity_populationTaylor
    {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝓧)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- `M` consists of probability densities, as assumed in vdV Theorem 5.39.
    (hPDF : IsPDFOf M μ)
    -- Differentiability in quadratic mean at `θ₀`, as in vdV Theorem 5.39.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (menv : 𝓧 → ℝ)
    -- A square-integrable local log-Lipschitz envelope under the true law;
    -- vdV Theorem 5.39, p. 65.
    (hmenv : MemLp menv 2
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    (ρ : ℝ)
    -- The log-Lipschitz condition holds on a nontrivial neighborhood of `θ₀`.
    (hρ : 0 < ρ)
    -- Base-point form of vdV's local pairwise log-Lipschitz condition.
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ x,
      |M.logDensity θ x - M.logDensity θ₀ x| ≤ ‖menv x‖ * ‖θ - θ₀‖) :
    Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ =>
        (∫ x, (M.logDensity θ x - M.logDensity θ₀ x)
          ∂(μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
          + (1 / 2 : ℝ) * fisherInformation M μ θ₀ ℓ (θ - θ₀) (θ - θ₀))
      (fun θ => ‖θ - θ₀‖ ^ 2) := by
  classical
  let P₀ : Measure 𝓧 :=
    μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)
  let W : EuclideanSpace ℝ (Fin k) → 𝓧 → ℝ := fun θ =>
    M.sqrtDensityRatio θ₀ θ
  let L : EuclideanSpace ℝ (Fin k) → 𝓧 → ℝ := fun θ x =>
    M.logDensity θ x - M.logDensity θ₀ x
  let s : EuclideanSpace ℝ (Fin k) → ℝ := fun θ => ‖θ - θ₀‖
  let I : EuclideanSpace ℝ (Fin k) → ℝ := fun θ =>
    fisherInformation M μ θ₀ ℓ (θ - θ₀) (θ - θ₀)
  letI : IsFiniteMeasure P₀ :=
    isFiniteMeasure_withDensity_ofReal (hPDF.density_integrable θ₀).hasFiniteIntegral
  have hlinear := dqm_sqrtDensityRatio_l2_linearization M μ θ₀ ℓ hPDF hDQM
  let z : EuclideanSpace ℝ (Fin k) → 𝓧 → ℝ := fun θ x => ⟪θ - θ₀, ℓ x⟫
  let score : EuclideanSpace ℝ (Fin k) → 𝓧 → ℝ := fun θ x =>
    z θ x * M.sqrtDensity θ₀ x
  have hscore_mem (θ : EuclideanSpace ℝ (Fin k)) : MemLp (score θ) 2 μ := by
    simpa [score, z] using dqm_score_memLp_two M μ θ₀ ℓ
      (hPDF.density_integrable θ₀) hDQM (θ - θ₀)
      (fun _ => hPDF.density_integrable _)
  have hbase_pos : ∀ᵐ x ∂P₀, 0 < M.sqrtDensity θ₀ x := by
    change ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (M.density θ₀ x)),
      0 < M.sqrtDensity θ₀ x
    rw [ae_withDensity_iff (M.density_meas θ₀).ennreal_ofReal]
    filter_upwards with x
    intro hx
    exact Real.sqrt_pos.mpr (ENNReal.ofReal_pos.mp (bot_lt_iff_ne_bot.mpr hx))
  have hzmem (θ : EuclideanSpace ℝ (Fin k)) : MemLp (z θ) 2 P₀ := by
    have hdiv_meas : AEStronglyMeasurable
        (fun x => score θ x / M.sqrtDensity θ₀ x) P₀ :=
      (((hscore_mem θ).1.mul
        (M.sqrtDensity_meas θ₀).inv.aestronglyMeasurable).mono_ac
          (withDensity_absolutelyContinuous _ _))
    have hzeq : (fun x => score θ x / M.sqrtDensity θ₀ x) =ᵐ[P₀] z θ := by
      filter_upwards [hbase_pos] with x hx
      simp only [score]
      field_simp [hx.ne']
    refine (memLp_two_iff_integrable_sq (hdiv_meas.congr hzeq)).2 ?_
    change Integrable (fun x => z θ x ^ 2)
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
    rw [integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal (by simp)]
    refine (hscore_mem θ).integrable_sq.congr ?_
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x),
      ← M.sqrtDensity_sq θ₀ x]
    simp only [score]
    ring
  have hWmem : ∀ᶠ θ in 𝓝 θ₀, MemLp (W θ) 2 P₀ := by
    filter_upwards [hlinear.1] with θ hq
    have := hq.add (hzmem θ)
    convert this using 1
    funext x
    simp only [Pi.add_apply, W, z]
    ring
  have hmean : (fun θ => (∫ x, W θ x ∂P₀) + (1 / 4 : ℝ) * I θ)
      =o[𝓝 θ₀] (fun θ => s θ ^ 2) := by
    simpa only [W, P₀, I, s] using
      dqm_sqrtDensityRatio_mean_expansion M μ θ₀ ℓ hPDF hDQM
  have hsquare : (fun θ => (∫ x, W θ x ^ 2 ∂P₀) - I θ)
      =o[𝓝 θ₀] (fun θ => s θ ^ 2) := by
    simpa only [W, P₀, I, s] using
      dqm_sqrtDensityRatio_sq_expansion M μ θ₀ ℓ hPDF hDQM
  have hnormint : Integrable
      (fun x => ‖ℓ x‖ ^ 2 * M.density θ₀ x) μ :=
    dqm_norm_sq_score_integrable M μ θ₀ ℓ (hPDF.density_integrable θ₀) hDQM
      (fun _ _ => hPDF.density_integrable _)
  let C : ℝ := ∫ x, ‖ℓ x‖ ^ 2 * M.density θ₀ x ∂μ
  have hI_le (θ : EuclideanSpace ℝ (Fin k)) : I θ ≤ C * s θ ^ 2 := by
    dsimp only [I, fisherInformation]
    calc
      (∫ x, (⟪θ - θ₀, ℓ x⟫ * ⟪θ - θ₀, ℓ x⟫) * M.density θ₀ x ∂μ) ≤
          ∫ x, s θ ^ 2 * (‖ℓ x‖ ^ 2 * M.density θ₀ x) ∂μ := by
        apply integral_mono
          (by
            simpa [pow_two] using
              (dqm_fisher_integrable M μ θ₀ ℓ (hPDF.density_integrable θ₀)
                hDQM (θ - θ₀) (fun _ => hPDF.density_integrable _)))
          (hnormint.const_mul (s θ ^ 2))
        intro x
        have hi := real_inner_mul_inner_self_le (θ - θ₀) (ℓ x)
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← sq] at hi
        simpa only [s, pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right hi (M.density_nonneg θ₀ x)
      _ = C * s θ ^ 2 := by rw [integral_const_mul]; ring
  have hI_nonneg (θ : EuclideanSpace ℝ (Fin k)) : 0 ≤ I θ := by
    dsimp only [I, fisherInformation]
    exact integral_nonneg fun x =>
      mul_nonneg (mul_self_nonneg _) (M.density_nonneg θ₀ x)
  have hIO : I =O[𝓝 θ₀] (fun θ => s θ ^ 2) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, Filter.Eventually.of_forall fun θ => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hI_nonneg θ), Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact hI_le θ
  have hWsqO : (fun θ => ∫ x, W θ x ^ 2 ∂P₀)
      =O[𝓝 θ₀] (fun θ => s θ ^ 2) := by
    have hsum := hsquare.isBigO.add hIO
    convert! hsum using 1
    funext θ
    ring
  have hL_meas (θ : EuclideanSpace ℝ (Fin k)) : Measurable (L θ) :=
    (M.density_meas θ).log.sub (M.density_meas θ₀).log
  have hball : ∀ᶠ θ in 𝓝 θ₀, θ ∈ Metric.closedBall θ₀ ρ :=
    Metric.closedBall_mem_nhds θ₀ hρ
  have hLbound : ∀ᶠ θ in 𝓝 θ₀, ∀ x, |L θ x| ≤ s θ * |menv x| := by
    filter_upwards [hball] with θ hθ
    intro x
    simpa only [L, s, Real.norm_eq_abs, mul_comm] using hLip θ hθ x
  have hLint : ∀ᶠ θ in 𝓝 θ₀, Integrable (L θ) P₀ := by
    filter_upwards [hLbound] with θ hbound
    exact Integrable.mono' ((hmenv.integrable one_le_two).norm.const_mul (s θ))
      (hL_meas θ).aestronglyMeasurable (Eventually.of_forall (hbound))
  have hTaylor : ∀ᶠ θ in 𝓝 θ₀, ∀ᵐ x ∂P₀, |W θ x| < 1 →
      L θ x - W θ x + W θ x ^ 2 / 4 =
        W θ x ^ 2 / 2 * ForMathlib.logTaylorRemainder (W θ x) := by
    filter_upwards with θ
    filter_upwards [hbase_pos] with x hx
    intro hWlt
    have hp : 0 < M.density θ₀ x := Real.sqrt_pos.mp hx
    have ht : 0 < M.density θ x := by
      refine lt_of_le_of_ne (M.density_nonneg θ x) ?_
      intro hzero
      have : W θ x = -2 := by
        dsimp only [W, ParametricFamily.sqrtDensityRatio]
        rw [← hzero]
        norm_num
      rw [this] at hWlt
      norm_num at hWlt
    have hratio : L θ x = Real.log (M.density θ x / M.density θ₀ x) := by
      simp only [L, ParametricFamily.logDensity]
      rw [Real.log_div ht.ne' hp.ne']
    rw [hratio, M.log_density_ratio_taylor θ₀ θ x]
    ring
  have htails := fun delta hdelta =>
    dqm_sqrtDensityRatio_tail_controls M μ θ₀ ℓ hPDF hDQM menv hmenv delta hdelta
  have hrem : (fun θ => ∫ x, (L θ x - W θ x + W θ x ^ 2 / 4) ∂P₀)
      =o[𝓝 θ₀] (fun θ => s θ ^ 2) :=
    ForMathlib.integral_logTaylorRemainder_isLittleO (𝓝 θ₀) P₀ W L s menv
      (fun θ => M.sqrtDensityRatio_measurable θ₀ θ) hWmem hLint hmenv
      (fun _ => norm_nonneg _) hLbound hTaylor hWsqO
      (fun delta hdelta => (htails delta hdelta).2.1)
      (fun delta hdelta => (htails delta hdelta).2.2.2.1)
      (fun delta hdelta => (htails delta hdelta).2.2.2.2)
  have hcomb := (hrem.add hmean).add (hsquare.const_mul_left (-1 / 4 : ℝ))
  apply EventuallyEq.trans_isLittleO _ hcomb
  filter_upwards [hLint, hWmem] with θ hli hwm
  have hw := hwm.integrable one_le_two
  have hw2 := hwm.integrable_sq
  have hquarter : Integrable (fun x => W θ x ^ 2 / 4) P₀ := by
    simpa [div_eq_mul_inv, mul_comm] using hw2.const_mul (4 : ℝ)⁻¹
  have hquarter_eq : (∫ x, W θ x ^ 2 / 4 ∂P₀) =
      (1 / 4 : ℝ) * ∫ x, W θ x ^ 2 ∂P₀ := by
    simp_rw [div_eq_mul_inv, mul_comm]
    rw [integral_const_mul]
    ring
  have hsplit : (∫ x, (L θ x - W θ x) + W θ x ^ 2 / 4 ∂P₀) =
      (∫ x, L θ x - W θ x ∂P₀) + ∫ x, W θ x ^ 2 / 4 ∂P₀ :=
    integral_add (hli.sub hw) hquarter
  have hsub : (∫ x, L θ x - W θ x ∂P₀) =
      (∫ x, L θ x ∂P₀) - ∫ x, W θ x ∂P₀ := integral_sub hli hw
  change (∫ x, L θ x ∂P₀) + (1 / 2 : ℝ) * I θ = _
  rw [hsplit, hsub, hquarter_eq]
  ring

end AsymptoticStatistics
