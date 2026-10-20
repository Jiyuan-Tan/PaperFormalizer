module
public import StatLean.AsymptoticStatistics.MEstimator.Rate
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LinearizationEquicontinuity

@[expose] public section

/-!
# M-estimator asymptotic normality — vdV Theorem 5.23

Under the differentiability, local Lipschitz, quadratic-expansion, near-maximization, and
consistency assumptions of vdV Theorem 5.23, `m_estimator_normality` proves

    √n(θ̂ₙ − θ₀) = −V⁻¹ 𝔾ₙṁ_{θ₀} + o_P(1)

and the resulting Gaussian weak limit. The proof first obtains the `√n` rate, expands the
criterion at both the estimator and the quadratic maximizer `−V⁻¹𝔾ₙṁ`, and then applies
the argmax localization result.

The empirical supremum is assumed bounded above for every sample. This ensures that the
supremum formulation of near-maximality represents a finite value. The first-order
condition `Pṁ_{θ₀}=0`, nonsingularity of `V`, and square-integrability of the score are all
derived from the stated assumptions.
-/

namespace AsymptoticStatistics.MEstimator

open MeasureTheory Filter ProbabilityTheory EmpiricalProcess
open scoped ENNReal Topology RealInnerProductSpace Matrix ProbabilityTheory

/-! ### Little-o Taylor expansion in bounded remainder form -/

/-- **Taylor remainder in bounded form** for `mEstimator_sqrtn_rate`.

The theorem carries the second-order population Taylor expansion as an
`Asymptotics.IsLittleO`; `mEstimator_sqrtn_rate` instead consumes the concrete
localized bound `|remainder| ≤ (c/4)·‖θ−θ₀‖²` on a ball. This is the standard
`isLittleO_iff` unpacking at `ε := c/4`. Derived, not assumed. -/
theorem taylorBoundedForm_of_littleO
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (V : Matrix (Fin d) (Fin d) ℝ) {c : ℝ} (hc : 0 < c)
    (hTaylor : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < ρ →
      |(∫ x, (m θ x - m θ₀ x) ∂P)
          - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫|
        ≤ (c / 4) * ‖θ - θ₀‖ ^ 2 := by
  have hc4 : (0 : ℝ) < c / 4 := by positivity
  have h := (Asymptotics.isLittleO_iff.mp hTaylor) hc4
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ρ, hρ, hb⟩ := h
  refine ⟨ρ, hρ, fun θ hθ => ?_⟩
  have hbb := hb (show dist θ θ₀ < ρ by rwa [dist_eq_norm])
  simp only [Real.norm_eq_abs] at hbb
  rwa [abs_of_nonneg (sq_nonneg ‖θ - θ₀‖)] at hbb

/-! ### Complete-the-square identity for `hExpB` -/

/-- **`hExpB` complete-the-square identity** (reuses ArgmaxLocalization `complete_the_square`).

With `hB = −V⁻¹G` (`G = 𝔾ₙṁ`), the local quadratic `q(hB) = ½⟪hB,V hB⟫ + ⟪hB,G⟫`
collapses to `−½⟪G, V⁻¹G⟫`. This is `complete_the_square` evaluated at the vertex
`x = −V⁻¹G`, where the second square `½⟪x+V⁻¹G, V(x+V⁻¹G)⟫` vanishes. This
gives the form expected by `mEstimator_normality_of_expansion`. -/
theorem mEstimator_hExpB_completeSquare {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ)
    (hVunit : IsUnit V.det) (hVsymm : V.IsHermitian) (G : EuclideanSpace ℝ (Fin d)) :
    (1 / 2) * ⟪- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ G,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V
          (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ G)⟫
      + ⟪- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ G, G⟫
      = - (1 / 2) * ⟪G, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ G⟫ := by
  have h := complete_the_square V hVunit hVsymm
    (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ G) G
  simp only [neg_add_cancel, map_zero, inner_zero_right, mul_zero] at h
  linarith [h]

/-! ### First-order condition `Pṁ_{θ₀} = 0` -/

/-- **First-order condition** `∫ ṁ_{θ₀} dP = 0`.

At the population maximum `θ₀` the gradient of `θ ↦ Pm_θ` vanishes. Differentiating under
the integral (`hderiv` a.e. + the Lipschitz `L²` envelope for domination) gives
`∇(Pm_θ)|_{θ₀} = ∫ ṁ_{θ₀} dP`; the second-order Taylor `hTaylor` has **no linear term**,
so the gradient is `0`. Book-forced (not assumed): `Pṁ_{θ₀} = 0` is the stationarity
condition. The theorem `hasFDerivAt_integral_of_dominated_loc_of_lip`
gives `∇(Pm_θ)|_{θ₀} = ∫ innerSL(ṁ)`; `hTaylor` (little-o `‖·‖²`, no linear term) forces that
gradient to `0` by `HasFDerivAt.unique`; `innerSL` injectivity + coordinate projection then
read off `Pṁ_i = 0`. -/
theorem firstOrder_condition_Pmdot_zero
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (V : Matrix (Fin d) (Fin d) ℝ)
    (hmdot_meas : ∀ i, Measurable (mdot i))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hderiv : ∀ᵐ ω ∂P, HasFDerivAt (fun θ => m θ ω)
      (innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) θ₀)
    (hTaylor : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2)) :
    ∀ i, ∫ x, mdot i x ∂P = 0 := by
  classical
  set Vc := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V with hVcdef
  -- The bundled score `ω ↦ ṁ_{θ₀}(ω)` and its measurability.
  have hpsiVec_meas :
      Measurable (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp (measurable_pi_iff.mpr hmdot_meas)
  have hF'_meas : AEStronglyMeasurable
      (fun ω => innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) P :=
    (innerSL ℝ).continuous.comp_aestronglyMeasurable hpsiVec_meas.aestronglyMeasurable
  -- Lipschitz-with-`|menv|` on the ball for a.e. `ω`, for the *difference* `m_θ − m_{θ₀}`
  -- (subtracting the constant `m_{θ₀} ω` preserves the Lipschitz constant).
  have h_lip : ∀ᵐ ω ∂P, LipschitzOnWith (Real.nnabs (menv ω))
      (fun θ => m θ ω - m θ₀ ω) (Metric.closedBall θ₀ ρ) := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro θ₁ hθ₁ θ₂ hθ₂
    rw [Real.dist_eq, dist_eq_norm, Real.coe_nnabs,
      show (m θ₁ ω - m θ₀ ω) - (m θ₂ ω - m θ₀ ω) = m θ₁ ω - m θ₂ ω from by ring]
    calc |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖ := hLip θ₁ hθ₁ θ₂ hθ₂ ω
      _ ≤ |menv ω| * ‖θ₁ - θ₂‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  -- Differentiation under the integral, applied to the difference `F θ ω = m θ ω − m θ₀ ω`.
  -- At the base point `F θ₀ = 0`, so its integrability is automatic:
  -- `∇(θ ↦ P(m_θ − m_{θ₀}))|_{θ₀} = P ṁ_{θ₀} = ∫ innerSL(ṁ)` (subtracting the constant
  -- `m_{θ₀}` does not change the derivative).
  obtain ⟨hF'_int, hFderiv⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := P) (F := fun θ ω => m θ ω - m θ₀ ω)
    (F' := fun ω => innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω))
    (bound := menv) (x₀ := θ₀) (s := Metric.closedBall θ₀ ρ) (Metric.closedBall_mem_nhds θ₀ hρ)
    (Filter.Eventually.of_forall (fun θ => ((hm_meas θ).sub (hm_meas θ₀)).aestronglyMeasurable))
    (by simp)
    hF'_meas h_lip (hmenv.integrable one_le_two)
    (hderiv.mono (fun ω hd => hd.sub_const (m θ₀ ω)))
  -- The second-order Taylor with no linear term forces the population gradient to `0`.
  have hsq : (fun θ => ‖θ - θ₀‖ ^ 2) =o[𝓝 θ₀] (fun θ : EuclideanSpace ℝ (Fin d) => θ - θ₀) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hev : ∀ᶠ θ in 𝓝 θ₀, ‖θ - θ₀‖ < c := by
      rw [Metric.eventually_nhds_iff]
      exact ⟨c, hc, fun θ hθ => by rwa [dist_eq_norm] at hθ⟩
    filter_upwards [hev] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (le_of_lt hθ) (norm_nonneg _)
  have isBigO_Q : (fun θ => (1 / 2) * ⟪θ - θ₀, Vc (θ - θ₀)⟫)
      =O[𝓝 θ₀] (fun θ => ‖θ - θ₀‖ ^ 2) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨(1 / 2) * ‖Vc‖, Filter.Eventually.of_forall (fun θ => ?_)⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖θ - θ₀‖), abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc (1 / 2) * |⟪θ - θ₀, Vc (θ - θ₀)⟫|
        ≤ (1 / 2) * (‖θ - θ₀‖ * ‖Vc (θ - θ₀)‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ (1 / 2) * (‖θ - θ₀‖ * (‖Vc‖ * ‖θ - θ₀‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Vc.le_opNorm _) (norm_nonneg _)) (by norm_num)
      _ = (1 / 2) * ‖Vc‖ * ‖θ - θ₀‖ ^ 2 := by ring
  have hR : (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪θ - θ₀, Vc (θ - θ₀)⟫)
      =o[𝓝 θ₀] (fun θ : EuclideanSpace ℝ (Fin d) => θ - θ₀) := hTaylor.trans hsq
  have hQ : (fun θ => (1 / 2) * ⟪θ - θ₀, Vc (θ - θ₀)⟫)
      =o[𝓝 θ₀] (fun θ : EuclideanSpace ℝ (Fin d) => θ - θ₀) := isBigO_Q.trans_isLittleO hsq
  have hLittleO : (fun θ => ∫ ω, (m θ ω - m θ₀ ω) ∂P)
      =o[𝓝 θ₀] (fun θ : EuclideanSpace ℝ (Fin d) => θ - θ₀) := by
    have hfun : (fun θ => ∫ ω, (m θ ω - m θ₀ ω) ∂P)
        = (fun θ => ((∫ x, (m θ x - m θ₀ x) ∂P)
            - (1 / 2) * ⟪θ - θ₀, Vc (θ - θ₀)⟫) + (1 / 2) * ⟪θ - θ₀, Vc (θ - θ₀)⟫) := by
      funext θ; ring
    rw [hfun]
    exact hR.add hQ
  have hzero_deriv : HasFDerivAt (fun θ => ∫ ω, (m θ ω - m θ₀ ω) ∂P)
      (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) θ₀ := by
    rw [hasFDerivAt_iff_isLittleO]
    simpa using hLittleO
  -- Uniqueness of the derivative: `∫ innerSL(ṁ) = 0`.
  have hFint_zero :
      (∫ ω, innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω) ∂P) = 0 :=
    hFderiv.unique hzero_deriv
  -- The bundled score is integrable (`innerSL` is norm-preserving, so `hF'_int` transfers).
  have hpsi_int : Integrable (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) P := by
    refine ⟨hpsiVec_meas.aestronglyMeasurable, ?_⟩
    have hn : (fun ω => ‖innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)‖ₑ)
        = (fun ω => ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖ₑ) := by
      funext ω; simp only [enorm]; norm_cast; exact Subtype.ext (innerSL_apply_norm ℝ _)
    have hfin := hF'_int.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at hfin ⊢
    rwa [hn] at hfin
  -- `innerSL (P ṁ) = ∫ innerSL(ṁ) = 0`, and `innerSL` is injective, so `P ṁ = 0`.
  have hpsi_zero :
      (∫ ω, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω ∂P) = 0 := by
    have hz : innerSL ℝ (∫ ω, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω ∂P) = 0 :=
      (ContinuousLinearMap.integral_comp_comm (innerSL ℝ) hpsi_int).symm.trans hFint_zero
    have hself := congrArg (fun L => L
      (∫ ω, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω ∂P)) hz
    simp only [innerSL_apply_apply, ContinuousLinearMap.zero_apply] at hself
    exact inner_self_eq_zero.mp hself
  -- Extract each coordinate `P ṁ_i = 0` via the coordinate projection CLM.
  intro i
  calc ∫ x, mdot i x ∂P
      = ∫ ω, (EuclideanSpace.proj i)
          (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω) ∂P := rfl
    _ = (EuclideanSpace.proj i)
          (∫ ω, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω ∂P) :=
        ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i) hpsi_int
    _ = (EuclideanSpace.proj i) 0 := by rw [hpsi_zero]
    _ = 0 := map_zero _

/-! ### Generic empirical-process linear representation to normality. -/

/-- A measurable statistic with an asymptotically linear representation
`Yₙ = A 𝔾ₙψ + o_P(1)` is asymptotically Gaussian with covariance
`A * psiCov * Aᵀ`.

The empirical-process CLT assumptions use the covariance constructed above;
covariance and weak convergence are not separate assumptions. -/
theorem asymptoticNormality_of_empiricalProcess_linearRepresentation
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (A : Matrix (Fin k) (Fin k) ℝ)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    -- Measurability of the sample maps.
    (hX_meas : ∀ i, Measurable (X i))
    -- Independence of the sample coordinates.
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    -- Identical distribution of the sample coordinates.
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    -- Identification of the common sample law with `P`.
    (hX_law : μ.map (X 0) = P)
    -- Measurable score coordinates at the truth.
    (hψθ₀_meas : ∀ i, Measurable (ψ θ₀ i))
    -- Square-integrability of the bundled score.
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    -- Centering of every score coordinate.
    (hPθ₀_zero : ∀ i, ∫ x, ψ θ₀ i x ∂P = 0)
    (T : ℕ → Ξ → EuclideanSpace ℝ (Fin k))
    -- Almost-everywhere measurability required for pushforward laws and Slutsky's theorem.
    (hT_meas : ∀ n, AEMeasurable (T n) μ)
    -- The asymptotic linear representation.
    (hlinear : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      T n ξ + Matrix.toEuclideanCLM (𝕜 := ℝ) A
        (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))) :
    WeakConverges (fun n => μ.map (T n))
      (multivariateGaussian 0 (A * psiCov P ψ θ₀ * Aᵀ)) := by
  classical
  have hCLT := empiricalProcessVec_weakConverges P ψ θ₀ μ X hX_meas hX_indep hX_id hX_law
    hψθ₀_meas hψ_L2 hPθ₀_zero
  have hPSD := psiCov_posSemidef P ψ θ₀ hψ_L2
  have hG_meas : ∀ n, Measurable (fun ξ : Ξ =>
      empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)) := by
    intro n
    have hpi : Measurable (fun ξ : Ξ =>
        (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h) : Fin k → ℝ)) := by
      refine measurable_pi_iff.mpr (fun h => ?_)
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun i _ => (hψθ₀_meas h).comp (hX_meas i.val))
    exact (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp hpi
  set g : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (-A) with hg_def
  have hgauss_map :
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (psiCov P ψ θ₀)).map g
        = multivariateGaussian 0 (A * psiCov P ψ θ₀ * Aᵀ) := by
    have hmean : (Matrix.toEuclideanCLM (𝕜 := ℝ) (-A))
        (0 : EuclideanSpace ℝ (Fin k)) = 0 := map_zero _
    have hcov : (-A) * psiCov P ψ θ₀ * (-A)ᴴ = A * psiCov P ψ θ₀ * Aᵀ := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_neg,
        neg_mul, neg_mul_neg]
    rw [hg_def, multivariateGaussian_map_toEuclideanCLM (-A) 0 hPSD, hmean, hcov]
  have hCmap := hCLT.map g.continuous g.continuous.measurable
  rw [hgauss_map] at hCmap
  have hX_weak : WeakConverges (fun n => μ.map (fun ξ : Ξ =>
      g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))))
      (multivariateGaussian 0 (A * psiCov P ψ θ₀ * Aᵀ)) := by
    have hfam : (fun n => μ.map (fun ξ : Ξ =>
          g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))))
        = (fun n => (μ.map (fun ξ : Ξ =>
          empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))).map g) := by
      funext n
      rw [Measure.map_map g.continuous.measurable (hG_meas n)]
      rfl
    rw [hfam]
    exact hCmap
  have hpt : ∀ (n : ℕ) (ξ : Ξ),
      dist (g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))) (T n ξ)
        = ‖T n ξ + Matrix.toEuclideanCLM (𝕜 := ℝ) A
            (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))‖ := by
    intro n ξ
    set e := empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)
    have hgapply : g e = -(Matrix.toEuclideanCLM (𝕜 := ℝ) A e) := by
      rw [hg_def, map_neg, ContinuousLinearMap.neg_apply]
    rw [dist_eq_norm, hgapply,
      show -(Matrix.toEuclideanCLM (𝕜 := ℝ) A e) - T n ξ
          = -(T n ξ + Matrix.toEuclideanCLM (𝕜 := ℝ) A e) from by abel,
      norm_neg]
  have hDist : ∀ ε > 0, Tendsto (fun n => μ.real {ξ |
      ε ≤ dist (g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))) (T n ξ)})
      atTop (𝓝 0) := by
    intro ε hε
    have hfam : (fun n => μ.real {ξ |
        ε ≤ dist (g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))) (T n ξ)})
        = (fun n => μ.real {ξ | ε ≤ ‖T n ξ + Matrix.toEuclideanCLM (𝕜 := ℝ) A
            (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))‖}) := by
      funext n
      congr 1
      ext ξ
      simp only [Set.mem_setOf_eq, hpt n ξ]
    rw [hfam]
    exact hlinear ε hε
  exact WeakConverges.slutsky_of_tendstoInMeasure_dist
    (fun n => (g.continuous.measurable.comp (hG_meas n)).aemeasurable)
    hT_meas hX_weak hDist

/-! ### `hB = −V⁻¹𝔾ₙṁ` is `O_P(1)` -/

/-- **Comparison direction boundedness** `−V⁻¹𝔾ₙṁ = O_P(1)`.

`𝔾ₙṁ_{θ₀} = empiricalProcessVec P (fun _ => mdot) θ₀ n Xs ⇝ N(0, psiCov)`
(`empiricalProcessVec_weakConverges`), so its continuous-linear image
`−V⁻¹𝔾ₙṁ ⇝ N(0, V⁻¹ psiCov (V⁻¹)ᵀ)`; a weakly-convergent pushforward family is bounded in
probability (`isBoundedInProb_of_weakConverges`). Map the CLT through `toEuclideanCLM (-V⁻¹)`
via `WeakConverges.map` and `multivariateGaussian_map_toEuclideanCLM`, then apply
`isBoundedInProb_of_weakConverges`. -/
theorem mEstimator_hB_boundedInProb
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d))
    (V : Matrix (Fin d) (Fin d) ℝ)
    (hmdot_meas : ∀ i, Measurable (mdot i))
    (hψ_L2 : MemLp (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) 2 P)
    (hPmdot_zero : ∀ i, ∫ x, mdot i x ∂P = 0)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ =>
      - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
          (empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
            (fun i : Fin n => X i.val ξ))) := by
  classical
  have hPSD := psiCov_posSemidef P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ hψ_L2
  -- CLT: `𝔾ₙṁ ⇝ N(0, psiCov)`.
  have hCLT := empiricalProcessVec_weakConverges P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀
    μ X hX_meas hX_indep hX_id hX_law hmdot_meas hψ_L2 hPmdot_zero
  -- Measurability of the vector empirical process `𝔾ₙṁ`.
  have hG_meas : ∀ n, Measurable (fun ξ : Ξ =>
      empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
        (fun i : Fin n => X i.val ξ)) := by
    intro n
    have hcoord : ∀ h : Fin d, Measurable
        (fun ξ : Ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) (mdot h)) := by
      intro h
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun i _ => (hmdot_meas h).comp (hX_meas i.val))
    exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp (measurable_pi_iff.mpr hcoord)
  -- Push the CLT through the continuous linear map `-V⁻¹`.
  have hmap := WeakConverges.map hCLT
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)).continuous
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)).continuous.measurable
  rw [multivariateGaussian_map_toEuclideanCLM (-V⁻¹) 0 hPSD, map_zero] at hmap
  -- `(μ.map 𝔾ₙṁ).map (-V⁻¹) = μ.map ((-V⁻¹) ∘ 𝔾ₙṁ)`.
  have hfun : (fun n => (μ.map (fun ξ : Ξ =>
        empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
          (fun i : Fin n => X i.val ξ))).map
            (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)))
      = (fun n => μ.map (fun ξ : Ξ =>
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)
            (empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
              (fun i : Fin n => X i.val ξ)))) := by
    funext n
    exact Measure.map_map
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)).continuous.measurable (hG_meas n)
  rw [hfun] at hmap
  haveI : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      ((-V⁻¹) * psiCov P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ * (-V⁻¹)ᴴ)) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  have hfG_meas : ∀ n, Measurable (fun ξ : Ξ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)
        (empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
          (fun i : Fin n => X i.val ξ))) :=
    fun n => (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)).continuous.measurable.comp
      (hG_meas n)
  have hbdd := isBoundedInProb_of_weakConverges (P := fun _ : ℕ => μ) hfG_meas hmap
  -- `(-V⁻¹) applied = -(V⁻¹ applied)`.
  have hneg : (fun n (ξ : Ξ) => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)
        (empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
          (fun i : Fin n => X i.val ξ)))
      = (fun n (ξ : Ξ) => - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
          (empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
            (fun i : Fin n => X i.val ξ))) := by
    funext n ξ
    rw [map_neg, ContinuousLinearMap.neg_apply]
  rw [hneg] at hbdd
  exact hbdd

/-! ### Near-maximality through `BddAbove` -/

/-- **Near-maximality in θ₀-form.**

The main near-maximality assumption is stated in **sup-form**
`n·max0(⨆_θ ℙₙm_θ − ℙₙm_{θ̂}) →ₚ 0`; `mEstimator_sqrtn_rate` consumes the **θ₀-form**
`n·max0(ℙₙm_{θ₀} − ℙₙm_{θ̂}) →ₚ 0`. Since `ℙₙm_{θ₀} ≤ ⨆_θ ℙₙm_θ` (`le_ciSup hBdd`), the
θ₀-slack is dominated by the sup-slack, so `tendstoInProbZero_of_norm_le` transports the
limit by `le_ciSup hBdd` and monotonicity. -/
theorem nearMaxTheta0_of_sup
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hBdd : ∀ (n : ℕ) (ξ : Ξ), BddAbove (Set.range (fun θ : EuclideanSpace ℝ (Fin d) =>
      empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ))))
    (hNearMax : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * max 0 ((⨆ θ : EuclideanSpace ℝ (Fin d),
          empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ))
        - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
            (fun i : Fin n => X i.val ξ)))) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * max 0 (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ)
        - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
            (fun i : Fin n => X i.val ξ))) := by
  refine tendstoInProbZero_of_norm_le (fun n ξ => ?_) hNearMax
  have has : empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ)
      ≤ ⨆ θ : EuclideanSpace ℝ (Fin d),
          empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ) :=
    le_ciSup (hBdd n ξ) θ₀
  rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (le_max_left _ _)),
      Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (le_max_left _ _))]
  exact mul_le_mul_of_nonneg_left (max_le_max (le_refl 0) (sub_le_sub_right has _))
    (Nat.cast_nonneg n)

/-- **Near-maximality for the two localized criteria.**

The theorem `mEstimator_normality_of_expansion` uses near-maximality in the form
`max0(B − A) →ₚ 0`, where (with `hA := √n(θ̂−θ₀)`, `hB := −V⁻¹𝔾ₙṁ`)
`A = n·(ℙₙm_{θ̂} − ℙₙm_{θ₀})` and `B = n·(ℙₙm_{θ_B} − ℙₙm_{θ₀})` are the two localized
increments, so `B − A = n·(ℙₙm_{θ_B} − ℙₙm_{θ̂})`. Since `ℙₙm_{θ_B} ≤ ⨆_θ ℙₙm_θ`
(`le_ciSup hBdd`), `max0(B − A) ≤ n·max0(⨆ − ℙₙm_{θ̂}) →ₚ 0`
(`tendstoInProbZero_of_norm_le`). The identity for `A` uses
`θ₀ + (√n)⁻¹•(√n•(θ̂−θ₀)) = θ̂` (`n ≥ 1`) and `empiricalAvg` sub-additivity. -/
theorem nearMaxGlue_of_sup
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (V : Matrix (Fin d) (Fin d) ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hBdd : ∀ (n : ℕ) (ξ : Ξ), BddAbove (Set.range (fun θ : EuclideanSpace ℝ (Fin d) =>
      empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ))))
    (hNearMax : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * max 0 ((⨆ θ : EuclideanSpace ℝ (Fin d),
          empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ))
        - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
            (fun i : Fin n => X i.val ξ)))) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      max 0 ((n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
              (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                  (empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                    (fun i : Fin n => X i.val ξ)))) ω - m θ₀ ω) n (fun i : Fin n => X i.val ξ)
        - (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
              (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))) ω - m θ₀ ω) n
              (fun i : Fin n => X i.val ξ))) := by
  refine tendstoInProbZero_of_norm_le (fun n ξ => ?_) hNearMax
  rw [Real.norm_of_nonneg (le_max_left _ _),
      Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (le_max_left _ _))]
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp
  · -- `n ≥ 1`: the `A`-slot reparametrization collapses to `θ̂`.
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
    have hθA : θ₀ + (Real.sqrt n)⁻¹ •
          (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
        = θ_hat n (fun i : Fin n => X i.val ξ) := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hsqrt_pos), one_smul]; abel
    rw [hθA]
    -- `empiricalAvg` splits over the subtraction inside each localized increment.
    have eavg_sub : ∀ (f g : Ω → ℝ),
        empiricalAvg (fun ω => f ω - g ω) n (fun i : Fin n => X i.val ξ)
          = empiricalAvg f n (fun i : Fin n => X i.val ξ)
            - empiricalAvg g n (fun i : Fin n => X i.val ξ) := by
      intro f g
      simp only [empiricalAvg, Finset.sum_sub_distrib, mul_sub]
    simp only [eavg_sub]
    -- `ℙₙm_{θ_B} ≤ ⨆_θ ℙₙm_θ`.
    have hle_sup : empiricalAvg (m (θ₀ + (Real.sqrt n)⁻¹ •
            (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                (empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                  (fun i : Fin n => X i.val ξ))))) n (fun i : Fin n => X i.val ξ)
        ≤ ⨆ θ : EuclideanSpace ℝ (Fin d),
            empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ) :=
      le_ciSup (hBdd n ξ) _
    set B := empiricalAvg (m (θ₀ + (Real.sqrt n)⁻¹ •
        (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
            (empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
              (fun i : Fin n => X i.val ξ))))) n (fun i : Fin n => X i.val ξ) with hBdef
    set A := empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
        (fun i : Fin n => X i.val ξ) with hAdef
    set C := empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ) with hCdef
    set S := ⨆ θ : EuclideanSpace ℝ (Fin d),
        empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ) with hSdef
    refine max_le (mul_nonneg (Nat.cast_nonneg n) (le_max_left _ _)) ?_
    calc (n : ℝ) * (B - C) - (n : ℝ) * (A - C)
        = (n : ℝ) * (B - A) := by ring
      _ ≤ (n : ℝ) * (S - A) :=
          mul_le_mul_of_nonneg_left (by linarith [hle_sup]) (Nat.cast_nonneg n)
      _ ≤ (n : ℝ) * max 0 (S - A) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg n)

/-! ### vdV Theorem 5.23 -/

/-- **M-estimator asymptotic normality — vdV Theorem 5.23** (§5.3, book p.53–54).

For each `θ` in an
open subset of Euclidean space let `x ↦ m_θ(x)` be measurable with `θ ↦ m_θ(x)`
differentiable at `θ₀` `P`-a.e. with derivative `ṁ_{θ₀}` (`hderiv`), Lipschitz
`|m_{θ₁}−m_{θ₂}| ≤ ṁ·‖θ₁−θ₂‖` with `Pṁ² < ∞` (`hLip`, `hmenv`). Assume `θ ↦ Pm_θ` admits
a second-order Taylor expansion at the maximum `θ₀` with symmetric negative-definite `V`
(`hTaylor` little-o, `hVsymm`/`hVneg`). If `θ̂ₙ` near-maximizes the empirical criterion,
`ℙₙm_{θ̂ₙ} ≥ sup_θ ℙₙm_θ − o_P(n⁻¹)` (`hNearMax`), and `θ̂ₙ →ₚ θ₀` (`hConsistent`), then
(vdV 5.23's primary displayed result, plus the "in particular" normality)

    √n(θ̂ₙ − θ₀) = −V⁻¹ 𝔾ₙṁ_{θ₀} + o_P(1)   and   √n(θ̂ₙ − θ₀) ⇝ N(0, V⁻¹ P[ṁṁᵀ] (V⁻¹)ᵀ).

Three facts vdV states as consequences are derived from the hypotheses:
* `Pṁ_{θ₀} = 0`, the first-order condition (`firstOrder_condition_Pmdot_zero`);
* `IsUnit V.det` (nonsingularity of `V`), from `hVneg` + `c > 0`: `toEuclideanCLM V` is
  coercive hence a unit CLM (`ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map`),
  transported to `V.det` via `MulEquiv.isUnit_map` + `Matrix.isUnit_iff_isUnit_det`;
* `ṁ_{θ₀} ∈ L²`, from the `L²` envelope: `‖ṁ_{θ₀}‖ ≤ |menv|` a.e. by
  `HasFDerivAt.le_of_lipschitzOn` + `innerSL_apply_norm`, then `MemLp` by domination.

The additional condition `hBdd` states that `⨆_θ ℙₙm_θ` is finite for every sample,
which makes the supremum formulation of near-maximality meaningful. Both conclusions follow
from the same two quadratic expansions and the comparison of localized criteria. -/
theorem m_estimator_normality
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (V : Matrix (Fin d) (Fin d) ℝ)
    -- USER-INPUT: symmetric uniformly negative curvature of the population criterion;
    -- vdV Theorem 5.23.
    (hVsymm : V.IsHermitian)
    {c : ℝ} (hc : 0 < c)
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ - c * ‖x‖ ^ 2)
    -- USER-INPUT: measurable criterion functions and derivative coordinates;
    -- vdV Theorem 5.23.
    (hm_meas : ∀ θ, Measurable (m θ)) (hmdot_meas : ∀ i, Measurable (mdot i))
    -- USER-INPUT: almost-everywhere differentiability at the true parameter;
    -- vdV Theorem 5.23.
    (hderiv : ∀ᵐ ω ∂P, HasFDerivAt (fun θ => m θ ω)
      (innerSL ℝ (psiVec (fun _ => mdot) θ₀ ω)) θ₀)
    -- USER-INPUT: a measurable square-integrable local Lipschitz envelope on a
    -- nontrivial neighborhood; vdV Theorem 5.23.
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    -- USER-INPUT: the second-order population-criterion expansion at its maximum;
    -- vdV Theorem 5.23.
    (hTaylor : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2))
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    -- LEAN-ONLY: an explicit measurable independent identically distributed sequence
    -- realizing the abstract sample with law P.
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    -- LEAN-ONLY: measurability of the estimator as a random vector.
    (hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    -- USER-INPUT: near-maximization of the empirical criterion at the required rate;
    -- vdV Theorem 5.23.
    (hNearMax : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * max 0 ((⨆ θ : EuclideanSpace ℝ (Fin d),
          empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ))
        - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
            (fun i : Fin n => X i.val ξ))))
    -- USER-INPUT: consistency for the true parameter; vdV Theorem 5.23.
    (hConsistent : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    -- LEAN-ONLY: boundedness above makes the real-valued empirical supremum explicit.
    (hBdd : ∀ (n : ℕ) (ξ : Ξ), BddAbove (Set.range (fun θ : EuclideanSpace ℝ (Fin d) =>
      empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ)))) :
    (TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ))))
    ∧ WeakConverges
        (fun n => μ.map (fun ξ =>
          Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
        (multivariateGaussian 0 (V⁻¹ * psiCov P (fun _ => mdot) θ₀ * (V⁻¹)ᵀ)) := by
  classical
  -- Nonsingularity of `V` and square-integrability of the score follow from
  -- negative-definiteness of
  -- `V` and the `L²` envelope, respectively.
  -- `IsUnit V.det` follows from `hVneg` (`c > 0`): `toEuclideanCLM V` is coercive, hence a
  -- unit CLM (`isUnit_of_forall_le_norm_inner_map`), transported to `V` (`MulEquiv.isUnit_map`)
  -- and to `V.det` (`Matrix.isUnit_iff_isUnit_det`).
  have hVunit : IsUnit V.det := by
    have hVc_unit : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V) := by
      refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _
        (c := c.toNNReal) (Real.toNNReal_pos.mpr hc) (fun x => ?_)
      rw [Real.coe_toNNReal c hc.le, Real.norm_eq_abs,
        real_inner_comm x (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x)]
      have hnonpos : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ 0 :=
        le_trans (hVneg x) (by nlinarith [mul_nonneg hc.le (sq_nonneg ‖x‖)])
      rw [abs_of_nonpos hnonpos]
      nlinarith [hVneg x]
    exact (Matrix.isUnit_iff_isUnit_det V).mp
      ((MulEquiv.isUnit_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d))).mp hVc_unit)
  -- `ṁ_{θ₀} ∈ L²` follows from the `L²` envelope. For a.e. `ω`, `hderiv` gives the
  -- derivative `innerSL (ṁ_{θ₀} ω)`, whose operator norm is `≤ |menv ω|` by the local
  -- Lipschitz bound (`HasFDerivAt.le_of_lipschitzOn`); `‖innerSL v‖ = ‖v‖`, so
  -- `‖ṁ_{θ₀} ω‖ ≤ ‖menv ω‖`, and `MemLp` follows by domination against `hmenv`.
  have hpsiVec_meas :
      Measurable (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp (measurable_pi_iff.mpr hmdot_meas)
  have hψ_L2 : MemLp (psiVec (fun _ => mdot) θ₀) 2 P := by
    refine hmenv.norm.mono' hpsiVec_meas.aestronglyMeasurable ?_
    filter_upwards [hderiv] with ω hd
    have hlipω : LipschitzOnWith (Real.nnabs (menv ω))
        (fun θ => m θ ω) (Metric.closedBall θ₀ ρ) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro θ₁ hθ₁ θ₂ hθ₂
      rw [Real.dist_eq, dist_eq_norm, Real.coe_nnabs]
      calc |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖ := hLip θ₁ hθ₁ θ₂ hθ₂ ω
        _ ≤ |menv ω| * ‖θ₁ - θ₂‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    have hnorm_le := hd.le_of_lipschitzOn (Metric.closedBall_mem_nhds θ₀ hρ) hlipω
    rw [innerSL_apply_norm] at hnorm_le
    rwa [Real.coe_nnabs, ← Real.norm_eq_abs] at hnorm_le
  -- Score in `L²` per coordinate (from the bundled `hψ_L2`).
  have hmdot_L2 : ∀ i, MemLp (mdot i) 2 P := fun i => hψ_L2.eval_piLp i
  -- First-order condition `Pṁ_{θ₀} = 0`.
  have hPmdot_zero : ∀ i, ∫ x, mdot i x ∂P = 0 :=
    firstOrder_condition_Pmdot_zero P m mdot θ₀ V hmdot_meas hmdot_L2 hm_meas menv hmenv ρ hρ
      hLip hderiv hTaylor
  -- Bounded form of the curvature Taylor expansion.
  obtain ⟨ρT, hρT, hTb⟩ := taylorBoundedForm_of_littleO P m θ₀ V hc hTaylor
  -- `hA := √n(θ̂−θ₀)` and its measurability.
  have hA_meas : ∀ (n : ℕ), Measurable
      (fun ξ : Ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :=
    fun n => ((hθhat_meas n).sub measurable_const).const_smul (Real.sqrt n)
  -- `hA = √n(θ̂−θ₀) = O_P(1)` via the `√n` rate.
  have hA_bdd : IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :=
    mEstimator_sqrtn_rate_of_tendstoInProbZero P m θ₀ V hc hVneg hm_meas menv hmenv
      hmenv_meas ρ hρ hLip
      ⟨ρT, hρT, hTb⟩ θ_hat μ X hX_meas hX_indep hX_id hX_law
      (nearMaxTheta0_of_sup P m θ₀ θ_hat μ X hBdd hNearMax) hConsistent hθhat_meas
  -- Quadratic expansion at `hA`.
  have hExpA := mEstimator_quadratic_expansion P m mdot θ₀ V hm_meas hmdot_meas hmdot_L2
    menv hmenv hmenv_meas ρ hρ hLip hderiv hTaylor μ X hX_meas hX_indep hX_id hX_law
    (fun n ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) hA_meas hA_bdd
  -- `hB := −V⁻¹𝔾ₙṁ`, its measurability, and `O_P(1)`.
  have hG_meas : ∀ n, Measurable (fun ξ : Ξ =>
      empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)) := by
    intro n
    have hcoord : ∀ h : Fin d, Measurable
        (fun ξ : Ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) (mdot h)) := by
      intro h
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun i _ => (hmdot_meas h).comp (hX_meas i.val))
    exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp (measurable_pi_iff.mpr hcoord)
  have hB_meas : ∀ n, Measurable (fun ξ : Ξ =>
      - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
          (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))) :=
    fun n => ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹).continuous.measurable.comp
      (hG_meas n)).neg
  have hB_bdd := mEstimator_hB_boundedInProb P mdot θ₀ V hmdot_meas hψ_L2 hPmdot_zero
    μ X hX_meas hX_indep hX_id hX_law
  -- Quadratic expansion at `hB`, reshaped by completing the square.
  have hExpB1 := mEstimator_quadratic_expansion P m mdot θ₀ V hm_meas hmdot_meas hmdot_L2
    menv hmenv hmenv_meas ρ hρ hLip hderiv hTaylor μ X hX_meas hX_indep hX_id hX_law
    (fun n ξ => - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
        (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))
    hB_meas hB_bdd
  have hExpB : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
            (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))) ω
          - m θ₀ ω) n (fun i : Fin n => X i.val ξ)
        - (- (1 / 2) * ⟪empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ),
            Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))⟫)) := by
    have hcongr : (fun (n : ℕ) (ξ : Ξ) =>
          (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
                (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                    (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))) ω
              - m θ₀ ω) n (fun i : Fin n => X i.val ξ)
            - ((1 / 2) * ⟪- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                    (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)),
                  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V
                    (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                        (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))⟫
                + ⟪- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                    (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)),
                  empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)⟫))
        = (fun (n : ℕ) (ξ : Ξ) =>
          (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
                (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                    (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))) ω
              - m θ₀ ω) n (fun i : Fin n => X i.val ξ)
            - (- (1 / 2) * ⟪empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ),
                Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                  (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))⟫)) := by
      funext n ξ
      congr 1
      exact mEstimator_hExpB_completeSquare V hVunit hVsymm
        (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))
    rw [← hcongr]; exact hExpB1
  -- Glue-form near-max.
  have hNearMaxGlue := nearMaxGlue_of_sup P m θ₀ V mdot θ_hat μ X hBdd hNearMax
  refine ⟨?_, ?_⟩
  · -- vdV Theorem 5.23's primary displayed conclusion, the linear representation
    -- `√n(θ̂ₙ − θ₀) = −V⁻¹𝔾ₙṁ_{θ₀} + o_P(1)` from `mEstimator_linear_representation`, fed
    -- the SAME two expansions + glue near-max as the normality branch below.
    exact mEstimator_linear_representation P mdot θ₀ V hVunit hVsymm hc hVneg θ_hat μ X
      (fun (n : ℕ) (ξ : Ξ) => (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
          (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))) ω - m θ₀ ω) n
          (fun i : Fin n => X i.val ξ))
      (fun (n : ℕ) (ξ : Ξ) => (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
          (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))) ω
          - m θ₀ ω) n (fun i : Fin n => X i.val ξ))
      hExpA hExpB hNearMaxGlue
  · -- The "in particular" normality `⇝ N(0, Σ)` via the CLT and Slutsky's theorem.
    exact mEstimator_normality_of_expansion P mdot θ₀ V hVunit hVsymm hc hVneg hmdot_meas hψ_L2
      hPmdot_zero θ_hat μ X hX_meas hX_indep hX_id hX_law
      (fun (n : ℕ) (ξ : Ξ) => (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
          (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))) ω - m θ₀ ω) n
          (fun i : Fin n => X i.val ξ))
      (fun (n : ℕ) (ξ : Ξ) => (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
          (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))) ω
          - m θ₀ ω) n (fun i : Fin n => X i.val ξ))
      hExpA hExpB hNearMaxGlue hθhat_meas

/-- **Fixed-direction `L²` form** used for vdV Theorem 5.39.

This has the same estimator/sample data and the same representation-and-normality
conclusion as `m_estimator_normality`.  It replaces pointwise-a.e. differentiability by
the three facts the MLE route derives honestly: bundled score `L²`, zero score mean, and
fixed-direction `distL2` linearization. -/
theorem m_estimator_normality_of_distL2
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (V : Matrix (Fin d) (Fin d) ℝ)
    -- Symmetric population Hessian, as in vdV Theorem 5.23.
    (hVsymm : V.IsHermitian)
    {c : ℝ}
    -- Positive coercivity constant for negative definiteness.
    (hc : 0 < c)
    -- Uniform negative definiteness of the population Hessian.
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ - c * ‖x‖ ^ 2)
    -- Measurable criterion sections.
    (hm_meas : ∀ θ, Measurable (m θ))
    -- Measurable score coordinates.
    (hmdot_meas : ∀ i, Measurable (mdot i))
    -- Bundled score `L²`, derived in the specialization to Theorem 5.39.
    (hψ_L2 : MemLp (psiVec (fun _ => mdot) θ₀) 2 P)
    -- Zero score mean, derived from quadratic-mean differentiability in Theorem 5.39.
    (hPmdot_zero : ∀ i, ∫ x, mdot i x ∂P = 0)
    (menv : Ω → ℝ)
    -- vdV's common local Lipschitz envelope belongs to `L²(P)`.
    (hmenv : MemLp menv 2 P)
    -- Measurability of the empirical-process envelope.
    (hmenv_meas : Measurable menv)
    (ρ : ℝ)
    -- Positive radius of the local Lipschitz neighborhood.
    (hρ : 0 < ρ)
    -- vdV's local Lipschitz domination.
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    -- Fixed-direction `L²` linearization, derived from
    -- probability differentiability plus the common envelope in the 5.39 route.
    (hd : ∀ h : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ => distL2 P
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
      atTop (𝓝 0))
    -- Second-order population Taylor expansion at `θ₀`.
    (hTaylor : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2))
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    -- Measurability of the sample maps.
    (hX_meas : ∀ i, Measurable (X i))
    -- Independence of the sample coordinates.
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    -- Identical distribution of the sample coordinates.
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    -- Identification of the common sample law with `P`.
    (hX_law : μ.map (X 0) = P)
    -- Estimator measurability needed for pushforward laws and rate events.
    (hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    -- Empirical near-maximization at `o_P(n⁻¹)` scale.
    (hNearMax : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * max 0 ((⨆ θ : EuclideanSpace ℝ (Fin d),
          empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ))
        - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
            (fun i : Fin n => X i.val ξ))))
    -- Consistency of the estimator; the MLE specialization derives it from Theorem 5.35.
    (hConsistent : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    -- Boundedness above of the empirical criterion.
    (hBdd : ∀ (n : ℕ) (ξ : Ξ), BddAbove (Set.range
      (fun θ : EuclideanSpace ℝ (Fin d) =>
        empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ)))) :
    (TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ))))
    ∧ WeakConverges
        (fun n => μ.map (fun ξ =>
          Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
        (multivariateGaussian 0 (V⁻¹ * psiCov P (fun _ => mdot) θ₀ * (V⁻¹)ᵀ)) := by
  classical
  have hVunit : IsUnit V.det := by
    have hVc_unit : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V) := by
      refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _
        (c := c.toNNReal) (Real.toNNReal_pos.mpr hc) (fun x => ?_)
      rw [Real.coe_toNNReal c hc.le, Real.norm_eq_abs,
        real_inner_comm x (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x)]
      have hnonpos : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ 0 :=
        le_trans (hVneg x) (by nlinarith [mul_nonneg hc.le (sq_nonneg ‖x‖)])
      rw [abs_of_nonpos hnonpos]
      nlinarith [hVneg x]
    exact (Matrix.isUnit_iff_isUnit_det V).mp
      ((MulEquiv.isUnit_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d))).mp hVc_unit)
  have hmdot_L2 : ∀ i, MemLp (mdot i) 2 P := fun i => hψ_L2.eval_piLp i
  obtain ⟨ρT, hρT, hTb⟩ := taylorBoundedForm_of_littleO P m θ₀ V hc hTaylor
  have hA_meas : ∀ (n : ℕ), Measurable
      (fun ξ : Ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :=
    fun n => ((hθhat_meas n).sub measurable_const).const_smul (Real.sqrt n)
  have hA_bdd : IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :=
    mEstimator_sqrtn_rate_of_tendstoInProbZero P m θ₀ V hc hVneg hm_meas menv hmenv
      hmenv_meas ρ hρ hLip
      ⟨ρT, hρT, hTb⟩ θ_hat μ X hX_meas hX_indep hX_id hX_law
      (nearMaxTheta0_of_sup P m θ₀ θ_hat μ X hBdd hNearMax) hConsistent hθhat_meas
  have hExpA := mEstimator_quadratic_expansion_of_distL2 P m mdot θ₀ V hm_meas hmdot_meas
    hmdot_L2 menv hmenv hmenv_meas ρ hρ hLip hd hTaylor μ X hX_meas hX_indep hX_id hX_law
    (fun n ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) hA_meas hA_bdd
  have hG_meas : ∀ n, Measurable (fun ξ : Ξ =>
      empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)) := by
    intro n
    have hcoord : ∀ h : Fin d, Measurable
        (fun ξ : Ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) (mdot h)) := by
      intro h
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun i _ => (hmdot_meas h).comp (hX_meas i.val))
    exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp (measurable_pi_iff.mpr hcoord)
  have hB_meas : ∀ n, Measurable (fun ξ : Ξ =>
      - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
          (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))) :=
    fun n => ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹).continuous.measurable.comp
      (hG_meas n)).neg
  have hB_bdd := mEstimator_hB_boundedInProb P mdot θ₀ V hmdot_meas hψ_L2 hPmdot_zero
    μ X hX_meas hX_indep hX_id hX_law
  have hExpB1 := mEstimator_quadratic_expansion_of_distL2 P m mdot θ₀ V hm_meas hmdot_meas
    hmdot_L2 menv hmenv hmenv_meas ρ hρ hLip hd hTaylor μ X hX_meas hX_indep hX_id hX_law
    (fun n ξ => - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
        (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))
    hB_meas hB_bdd
  have hExpB : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
            (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))) ω
          - m θ₀ ω) n (fun i : Fin n => X i.val ξ)
        - (- (1 / 2) * ⟪empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ),
            Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))⟫)) := by
    have hcongr : (fun (n : ℕ) (ξ : Ξ) =>
          (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
                (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                    (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))) ω
              - m θ₀ ω) n (fun i : Fin n => X i.val ξ)
            - ((1 / 2) * ⟪- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                    (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)),
                  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V
                    (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                        (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))⟫
                + ⟪- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                    (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)),
                  empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)⟫))
        = (fun (n : ℕ) (ξ : Ξ) =>
          (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
                (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                    (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))) ω
              - m θ₀ ω) n (fun i : Fin n => X i.val ξ)
            - (- (1 / 2) * ⟪empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ),
                Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
                  (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))⟫)) := by
      funext n ξ
      congr 1
      exact mEstimator_hExpB_completeSquare V hVunit hVsymm
        (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))
    rw [← hcongr]
    exact hExpB1
  have hNearMaxGlue := nearMaxGlue_of_sup P m θ₀ V mdot θ_hat μ X hBdd hNearMax
  refine ⟨?_, ?_⟩
  · exact mEstimator_linear_representation P mdot θ₀ V hVunit hVsymm hc hVneg θ_hat μ X
      (fun (n : ℕ) (ξ : Ξ) => (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
          (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))) ω - m θ₀ ω) n
          (fun i : Fin n => X i.val ξ))
      (fun (n : ℕ) (ξ : Ξ) => (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
          (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))) ω
          - m θ₀ ω) n (fun i : Fin n => X i.val ξ))
      hExpA hExpB hNearMaxGlue
  · exact mEstimator_normality_of_expansion P mdot θ₀ V hVunit hVsymm hc hVneg hmdot_meas hψ_L2
      hPmdot_zero θ_hat μ X hX_meas hX_indep hX_id hX_law
      (fun (n : ℕ) (ξ : Ξ) => (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
          (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))) ω - m θ₀ ω) n
          (fun i : Fin n => X i.val ξ))
      (fun (n : ℕ) (ξ : Ξ) => (n : ℝ) * empiricalAvg (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ •
          (- Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))) ω
          - m θ₀ ω) n (fun i : Fin n => X i.val ξ))
      hExpA hExpB hNearMaxGlue hθhat_meas

/-- **Fixed-comparison `L²` form.**

Assume near-maximality through comparisons with every fixed local direction.
The comparison at `a = 0` gives the rate bound;
`argmax_localization_of_fixed_comparisons` gives the linear representation,
whose Gaussian limit then follows from the empirical-process central limit
theorem. -/
theorem m_estimator_normality_of_distL2_fixed_comparisons
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (V : Matrix (Fin d) (Fin d) ℝ)
    -- Symmetric population Hessian, as in vdV Theorem 5.23.
    (hVsymm : V.IsHermitian) {c : ℝ}
    -- Positive coercivity constant for negative definiteness.
    (hc : 0 < c)
    -- Uniform negative definiteness of the population Hessian.
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ -c * ‖x‖ ^ 2)
    -- Measurable criterion sections.
    (hm_meas : ∀ θ, Measurable (m θ))
    -- Measurable score coordinates.
    (hmdot_meas : ∀ i, Measurable (mdot i))
    -- Square-integrability of the bundled score.
    (hψ_L2 : MemLp (psiVec (fun _ => mdot) θ₀) 2 P)
    -- Coordinatewise zero score mean.
    (hPmdot_zero : ∀ i, ∫ x, mdot i x ∂P = 0)
    (menv : Ω → ℝ)
    -- Common local Lipschitz envelope in `L²(P)`.
    (hmenv : MemLp menv 2 P)
    -- Measurable envelope.
    (hmenv_meas : Measurable menv)
    (ρ : ℝ)
    -- Positive local-neighborhood radius.
    (hρ : 0 < ρ)
    -- Local pairwise Lipschitz domination.
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
      |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    -- Fixed-direction `L²` linearization.
    (hd : ∀ h : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ => distL2 P
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
      atTop (𝓝 0))
    -- Second-order population Taylor expansion.
    (hTaylor : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P) -
        (1 / 2) * ⟪θ - θ₀,
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2))
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    -- Measurability of the sample maps.
    (hX_meas : ∀ i, Measurable (X i))
    -- Independence of the sample coordinates.
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    -- Identical distribution of the sample coordinates.
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    -- Identification of the common sample law with `P`.
    (hX_law : μ.map (X 0) = P)
    -- Estimator measurability needed for pushforward laws and rate events.
    (hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    -- Near-maximality against every fixed local comparison.
    (hFixedComparison : ∀ a : EuclideanSpace ℝ (Fin d),
      TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
        (n : ℝ) * max 0
          (empiricalAvg (m (θ₀ + (Real.sqrt n)⁻¹ • a)) n
              (fun i : Fin n => X i.val ξ) -
            empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
              (fun i : Fin n => X i.val ξ))))
    -- Consistency, derived internally in the MLE specialization.
    (hConsistent : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) +
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
            (empiricalProcessVec P (fun _ => mdot) θ₀ n
              (fun i : Fin n => X i.val ξ))) ∧
      WeakConverges
        (fun n => μ.map (fun ξ =>
          Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
        (multivariateGaussian 0
          (V⁻¹ * psiCov P (fun _ => mdot) θ₀ * (V⁻¹)ᵀ)) := by
  classical
  have hVunit : IsUnit V.det := by
    have hVc_unit : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V) := by
      refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _
        (c := c.toNNReal) (Real.toNNReal_pos.mpr hc) (fun x => ?_)
      rw [Real.coe_toNNReal c hc.le, Real.norm_eq_abs,
        real_inner_comm x (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x)]
      have hnonpos : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ 0 :=
        le_trans (hVneg x) (by nlinarith [mul_nonneg hc.le (sq_nonneg ‖x‖)])
      rw [abs_of_nonpos hnonpos]
      nlinarith [hVneg x]
    exact (Matrix.isUnit_iff_isUnit_det V).mp
      ((MulEquiv.isUnit_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d))).mp hVc_unit)
  have hmdot_L2 : ∀ i, MemLp (mdot i) 2 P := fun i => hψ_L2.eval_piLp i
  obtain ⟨ρT, hρT, hTb⟩ := taylorBoundedForm_of_littleO P m θ₀ V hc hTaylor
  let hA : ℕ → Ξ → EuclideanSpace ℝ (Fin d) := fun n ξ =>
    Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
  let G : ℕ → Ξ → EuclideanSpace ℝ (Fin d) := fun n ξ =>
    empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)
  let A : ℕ → Ξ → ℝ := fun n ξ =>
    (n : ℝ) * empiricalAvg
      (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • hA n ξ) ω - m θ₀ ω) n
      (fun i : Fin n => X i.val ξ)
  let B : EuclideanSpace ℝ (Fin d) → ℕ → Ξ → ℝ := fun a n ξ =>
    (n : ℝ) * empiricalAvg
      (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • a) ω - m θ₀ ω) n
      (fun i : Fin n => X i.val ξ)
  have hA_meas : ∀ n, Measurable (hA n) := fun n =>
    ((hθhat_meas n).sub measurable_const).const_smul (Real.sqrt n)
  have hRateNear : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * max 0 (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ) -
        empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
          (fun i : Fin n => X i.val ξ))) := by
    simpa only [smul_zero, add_zero] using
      (hFixedComparison (0 : EuclideanSpace ℝ (Fin d)))
  have hA_bdd : IsBoundedInProb (fun _ : ℕ => μ) hA := by
    simpa only [hA] using
      (mEstimator_sqrtn_rate_of_tendstoInProbZero P m θ₀ V hc hVneg hm_meas menv hmenv
        hmenv_meas ρ hρ hLip
        ⟨ρT, hρT, hTb⟩ θ_hat μ X hX_meas hX_indep hX_id hX_law hRateNear
        hConsistent hθhat_meas)
  have hG_meas : ∀ n, Measurable (G n) := by
    intro n
    have hcoord : ∀ j : Fin d, Measurable
        (fun ξ : Ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) (mdot j)) := by
      intro j
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun i _ => (hmdot_meas j).comp (hX_meas i.val))
    simpa only [G] using!
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp (measurable_pi_iff.mpr hcoord)
  haveI : IsProbabilityMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
        (psiCov P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀)) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  have hG_weak := empiricalProcessVec_weakConverges P
    (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ μ X hX_meas hX_indep hX_id hX_law
    hmdot_meas hψ_L2 hPmdot_zero
  have hG_bdd : IsBoundedInProb (fun _ : ℕ => μ) G :=
    isBoundedInProb_of_weakConverges hG_meas hG_weak
  have hExpA : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => A n ξ -
      ((1 / 2) * ⟪hA n ξ, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (hA n ξ)⟫ +
        ⟪hA n ξ, G n ξ⟫)) := by
    simpa only [A, G] using
      (mEstimator_quadratic_expansion_of_distL2 P m mdot θ₀ V hm_meas hmdot_meas
        hmdot_L2 menv hmenv hmenv_meas ρ hρ hLip hd hTaylor μ X hX_meas hX_indep
        hX_id hX_law hA hA_meas hA_bdd)
  have hconst_bdd (a : EuclideanSpace ℝ (Fin d)) :
      IsBoundedInProb (fun _ : ℕ => μ) (fun _ _ => a) := by
    intro ε hε
    refine ⟨‖a‖, fun n => ?_⟩
    simp [hε.le]
  have hExpB : ∀ a : EuclideanSpace ℝ (Fin d),
      TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => B a n ξ -
        ((1 / 2) * ⟪a, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V a⟫ + ⟪a, G n ξ⟫)) := by
    intro a
    simpa only [B, G] using
      (mEstimator_quadratic_expansion_of_distL2 P m mdot θ₀ V hm_meas hmdot_meas
        hmdot_L2 menv hmenv hmenv_meas ρ hρ hLip hd hTaylor μ X hX_meas hX_indep
        hX_id hX_law (fun _ _ => a) (fun _ => measurable_const) (hconst_bdd a))
  have hNearMax : ∀ a : EuclideanSpace ℝ (Fin d),
      TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => max 0 (B a n ξ - A n ξ)) := by
    intro a
    have hfun : (fun n ξ => max 0 (B a n ξ - A n ξ)) = (fun (n : ℕ) (ξ : Ξ) =>
        (n : ℝ) * max 0
          (empiricalAvg (m (θ₀ + (Real.sqrt n)⁻¹ • a)) n
              (fun i : Fin n => X i.val ξ) -
            empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
              (fun i : Fin n => X i.val ξ))) := by
      funext n ξ
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [A, B]
      · have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
        have hθA : θ₀ + (Real.sqrt n)⁻¹ • hA n ξ =
            θ_hat n (fun i : Fin n => X i.val ξ) := by
          simp only [hA, smul_smul, inv_mul_cancel₀ (ne_of_gt hsqrt_pos), one_smul]
          abel
        have eavg_sub : ∀ (f g : Ω → ℝ),
            empiricalAvg (fun ω => f ω - g ω) n (fun i : Fin n => X i.val ξ) =
              empiricalAvg f n (fun i : Fin n => X i.val ξ) -
                empiricalAvg g n (fun i : Fin n => X i.val ξ) := by
          intro f g
          simp only [empiricalAvg, Finset.sum_sub_distrib, mul_sub]
        rw [mul_max_of_nonneg 0 _ (Nat.cast_nonneg n)]
        simp only [mul_zero]
        congr 1
        simp only [A, B, hθA, eavg_sub]
        ring
    rw [hfun]
    exact hFixedComparison a
  have hlinear : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      hA n ξ + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ (G n ξ)) :=
    argmax_localization_of_fixed_comparisons V hVunit hVsymm hc hVneg hA G A B
      hA_bdd hG_bdd hExpA hExpB hNearMax
  refine ⟨?_, ?_⟩
  · simpa only [hA, G] using hlinear
  · simpa only [hA] using
      (asymptoticNormality_of_empiricalProcess_linearRepresentation P
        (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ V⁻¹ μ X hX_meas hX_indep hX_id
        hX_law hmdot_meas hψ_L2 hPmdot_zero hA (fun n => (hA_meas n).aemeasurable)
        hlinear)

/-- **Exact-maximizer form** used for vdV Theorem 5.39.

This has the same analytic prefix and paired conclusion as
`m_estimator_normality_of_distL2`, but an exact pointwise maximizer supplies
all fixed deterministic comparisons directly.  Consequently neither the
supremum encoding nor its `BddAbove` guard appears. -/
theorem m_estimator_normality_of_distL2_fixed_maximizer
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (V : Matrix (Fin d) (Fin d) ℝ)
    -- Symmetric population Hessian, as in vdV Theorem 5.23.
    (hVsymm : V.IsHermitian)
    {c : ℝ}
    -- Positive coercivity constant for negative definiteness.
    (hc : 0 < c)
    -- Uniform negative definiteness of the population Hessian.
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ - c * ‖x‖ ^ 2)
    -- Measurable criterion sections.
    (hm_meas : ∀ θ, Measurable (m θ))
    -- Measurable score coordinates.
    (hmdot_meas : ∀ i, Measurable (mdot i))
    -- Square-integrability of the bundled score.
    (hψ_L2 : MemLp (psiVec (fun _ => mdot) θ₀) 2 P)
    -- Coordinatewise zero score mean.
    (hPmdot_zero : ∀ i, ∫ x, mdot i x ∂P = 0)
    (menv : Ω → ℝ)
    -- Common local Lipschitz envelope in `L²(P)`.
    (hmenv : MemLp menv 2 P)
    -- Measurable envelope.
    (hmenv_meas : Measurable menv)
    (ρ : ℝ)
    -- Positive local-neighborhood radius.
    (hρ : 0 < ρ)
    -- Local pairwise Lipschitz domination.
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    -- Fixed-direction `L²` linearization.
    (hd : ∀ h : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ => distL2 P
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
      atTop (𝓝 0))
    -- Second-order population Taylor expansion.
    (hTaylor : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2))
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    -- Measurability of the sample maps.
    (hX_meas : ∀ i, Measurable (X i))
    -- Independence of the sample coordinates.
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    -- Identical distribution of the sample coordinates.
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    -- Identification of the common sample law with `P`.
    (hX_law : μ.map (X 0) = P)
    -- Estimator measurability needed for pushforward laws and rate events.
    (hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    -- Exact pointwise empirical maximization.
    (hMax : ∀ n ξ θ,
      empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ) ≤
        empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
          (fun i : Fin n => X i.val ξ))
    -- Consistency, derived internally in the MLE specialization.
    (hConsistent : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :
    (TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ))))
    ∧ WeakConverges
        (fun n => μ.map (fun ξ =>
          Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
        (multivariateGaussian 0 (V⁻¹ * psiCov P (fun _ => mdot) θ₀ * (V⁻¹)ᵀ)) := by
  classical
  have hBdd : ∀ (n : ℕ) (ξ : Ξ), BddAbove (Set.range
      (fun θ : EuclideanSpace ℝ (Fin d) =>
        empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ))) := by
    intro n ξ
    refine ⟨empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
      (fun i : Fin n => X i.val ξ), ?_⟩
    rintro y ⟨θ, rfl⟩
    exact hMax n ξ θ
  have hSup : ∀ (n : ℕ) (ξ : Ξ),
      (⨆ θ : EuclideanSpace ℝ (Fin d),
        empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ)) =
          empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
            (fun i : Fin n => X i.val ξ) := by
    intro n ξ
    apply le_antisymm
    · exact ciSup_le (fun θ => hMax n ξ θ)
    · exact le_ciSup (hBdd n ξ) (θ_hat n (fun i : Fin n => X i.val ξ))
  have hNearMax : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * max 0 ((⨆ θ : EuclideanSpace ℝ (Fin d),
          empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ))
        - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
            (fun i : Fin n => X i.val ξ))) := by
    intro ε hε
    simp only [hSup]
    simp [not_le.mpr hε]
  exact m_estimator_normality_of_distL2 P m mdot θ₀ V hVsymm hc hVneg hm_meas
    hmdot_meas hψ_L2 hPmdot_zero menv hmenv hmenv_meas ρ hρ hLip hd hTaylor θ_hat μ X
    hX_meas hX_indep hX_id hX_law hθhat_meas hNearMax hConsistent hBdd

end AsymptoticStatistics.MEstimator
