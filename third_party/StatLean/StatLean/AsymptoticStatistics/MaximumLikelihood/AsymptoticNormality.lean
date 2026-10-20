module
public import StatLean.AsymptoticStatistics.DQM.LogDensityPopulationTaylor
public import StatLean.AsymptoticStatistics.MaximumLikelihood.Consistency
public import StatLean.AsymptoticStatistics.MaximumLikelihood.FisherAdapters
public import StatLean.AsymptoticStatistics.MaximumLikelihood.ProductComparisons
public import StatLean.AsymptoticStatistics.MEstimator.DifferentiabilityInProbability
public import StatLean.AsymptoticStatistics.MEstimator.AsymptoticNormality

@[expose] public section

/-!
# Maximum-likelihood asymptotic normality

Formalization of van der Vaart, *Asymptotic Statistics*, Theorem 5.39
(pp. 65--66). The first theorem assumes consistency as in
the text.  A companion corollary derives consistency through the stabilized
Kullback--Leibler/T4 route.  Both derive the score and Taylor inputs from DQM
and apply the fixed-comparison M-estimator theorem, without pointwise
log-density derivatives, strict positivity, or additional equalities relating
the score definitions.
-/

namespace AsymptoticStatistics.MaximumLikelihood

open MeasureTheory Filter ProbabilityTheory EmpiricalProcess
open scoped ENNReal Topology RealInnerProductSpace Matrix ProbabilityTheory

set_option maxHeartbeats 800000 in
-- This specialization derives the M-estimator linearization and Gaussian limit under consistency.
/-- **Maximum-likelihood asymptotic normality (vdV Theorem 5.39).**

For a consistent exact MLE in a DQM model with a measurable local
square-integrable log-Lipschitz envelope and positive-definite Fisher
information, the estimator has the inverse-Fisher asymptotic linear
representation and is asymptotically `N(0, I⁻¹)`. -/
theorem mle_asymptotic_normality_of_consistent
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    -- the model consists of probability densities.
    (hPDF : IsPDFOf M μ)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (X : ℕ → Ξ → Ω)
    (ℓ : Ω → EuclideanSpace ℝ (Fin d))
    -- Measurability of the score, as required in vdV Theorem 5.39.
    (hℓ : Measurable ℓ)
    -- differentiability in quadratic mean at `θ₀`.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (menv : Ω → ℝ)
    -- vdV's local envelope is square-integrable under `P₀`.
    (hmenv : MemLp menv 2
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- measurable representative for the envelope.
    (hmenv_meas : Measurable menv)
    (ρ : ℝ)
    -- the Lipschitz neighborhood is nontrivial.
    (hρ : 0 < ρ)
    -- vdV's pairwise local log-likelihood Lipschitz condition.
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ,
      ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ x,
        |M.logDensity θ₁ x - M.logDensity θ₂ x| ≤
          menv x * ‖θ₁ - θ₂‖)
    -- nonsingular Fisher information, encoded equivalently as PosDef.
    (hI : (fisherInformationMatrix M μ θ₀ ℓ).PosDef)
    -- measurable sample-map encoding of the iid experiment.
    (hX_meas : ∀ i, Measurable (X i))
    -- independence component of the iid sample encoding.
    (hX_indep : ProbabilityTheory.iIndepFun X ν)
    -- identical-distribution component of the iid sample encoding.
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) ν ν)
    -- identifies the common sample law with the true model law.
    (hX_law : ν.map (X 0) =
      μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
    -- estimator measurability needed for pushforward laws and rate events.
    (hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    -- consistency of the MLE, as assumed in vdV Theorem 5.39.
    (hConsistent : TendstoInProbZero (fun _ => ν)
      (fun n ξ => θ_hat n (fun i => X i.val ξ) - θ₀))
    -- exact product-likelihood maximum-likelihood property.
    (hMLE : IsMaximumLikelihoodEstimator M θ_hat) :
    TendstoInProbZero (fun _ : ℕ => ν) (fun n ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
            (fisherInformationMatrix M μ θ₀ ℓ)⁻¹
            (empiricalProcessVec
              (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
              (fun _ i x => ℓ x i) θ₀ n
              (fun i : Fin n => X i.val ξ))) ∧
      WeakConverges
        (fun n => ν.map (fun ξ =>
          Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
        (multivariateGaussian 0
          (fisherInformationMatrix M μ θ₀ ℓ)⁻¹) := by
  letI : IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) :=
    withDensity_density_isProbabilityMeasure M μ hPDF θ₀
  have hm_meas : ∀ θ, Measurable (M.logDensity θ) := by
    intro θ
    exact (M.density_meas θ).log
  have hmdot_meas : ∀ i : Fin d, Measurable (fun x => ℓ x i) :=
    fun i => (measurable_pi_apply i).comp
      ((WithLp.measurable_ofLp 2 (Fin d → ℝ)).comp hℓ)
  have hψ_L2 : MemLp (psiVec (fun _ i x => ℓ x i) θ₀) 2
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) :=
    dqm_scoreVector_memLp_two M μ θ₀ ℓ hℓ hPDF hDQM
  have hPmdot_zero : ∀ i : Fin d,
      ∫ x, ℓ x i ∂(μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) = 0 :=
    fun i => dqm_scoreCoordinate_mean_zero M μ θ₀ ℓ hℓ hPDF hDQM i
  have hdiff₀ := dqm_logDensity_differentiableInProbabilityAt M μ θ₀ ℓ hPDF hDQM
  have hdiff : DifferentiableInProbabilityAt
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
      (fun θ => M.logDensity θ)
      (MEstimator.mdotProbabilityDerivative (fun i x => ℓ x i) θ₀) θ₀ := by
    simpa only [MEstimator.mdotProbabilityDerivative, psiVec_score_eq] using! hdiff₀
  have hLip₀ : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ x,
      |M.logDensity θ x - M.logDensity θ₀ x| ≤
        ‖menv x‖ * ‖θ - θ₀‖ := by
    intro θ hθ x
    exact (hLip θ hθ θ₀ (Metric.mem_closedBall_self hρ.le) x).trans
      (by simpa only [Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (le_abs_self (menv x)) (norm_nonneg (θ - θ₀)))
  have hd : ∀ h : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ =>
      distL2 (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
        (fun x => Real.sqrt n *
          (M.logDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.logDensity θ₀ x))
        (fun x => ⟪h, psiVec
          (fun _ : EuclideanSpace ℝ (Fin d) => fun i x => ℓ x i) θ₀ x⟫))
      atTop (nhds 0) := by
    intro h
    exact MEstimator.distL2_localScale_mdot_of_differentiableInProbabilityAt
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
      (fun θ => M.logDensity θ) (fun i x => ℓ x i) θ₀ hdiff
      (fun θ => (hm_meas θ).aestronglyMeasurable) menv hmenv ρ hρ hLip₀ h
  have hFisher : ∀ u : EuclideanSpace ℝ (Fin d),
      Integrable (fun x => ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) μ := by
    intro u
    exact dqm_fisher_integrable M μ θ₀ ℓ (hPDF.density_integrable θ₀) hDQM u
      (fun t => hPDF.density_integrable (θ₀ + t • u))
  have hTaylor₀ := dqm_logDensity_populationTaylor M μ θ₀ ℓ hPDF hDQM
    menv hmenv ρ hρ hLip₀
  have hTaylor : Asymptotics.IsLittleO (nhds θ₀)
      (fun θ => (∫ x, (M.logDensity θ x - M.logDensity θ₀ x)
          ∂(μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))) -
        (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (-(fisherInformationMatrix M μ θ₀ ℓ)) (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2) := by
    convert hTaylor₀ using 1
    funext θ
    rw [fisherInformation_eq_inner_fisherInformationMatrix M μ θ₀ ℓ hFisher]
    simp only [map_neg, ContinuousLinearMap.neg_apply, inner_neg_right]
    ring
  obtain ⟨c, hc, hVsymm, _, hVneg⟩ :=
    neg_posDef_as_mEstimator_curvature (I := fisherInformationMatrix M μ θ₀ ℓ) hI
  have hFixedComparison : ∀ a : EuclideanSpace ℝ (Fin d),
      TendstoInProbZero (fun _ : ℕ => ν) (fun n ξ =>
        (n : ℝ) * max 0
          (empiricalAvg
              (M.logDensity (θ₀ + (Real.sqrt n)⁻¹ • a)) n
              (fun i : Fin n => X i.val ξ) -
            empiricalAvg
              (M.logDensity (θ_hat n (fun i : Fin n => X i.val ξ))) n
              (fun i : Fin n => X i.val ξ))) := by
    intro a
    exact mle_logDensity_fixedComparison_tendstoInProbZero M μ θ₀ ℓ hPDF hDQM
      θ_hat ν X hX_meas hX_id hX_law hMLE a
  have hT8 := MEstimator.m_estimator_normality_of_distL2_fixed_comparisons
    (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
    (fun θ => M.logDensity θ) (fun i x => ℓ x i) θ₀
    (-(fisherInformationMatrix M μ θ₀ ℓ)) hVsymm hc hVneg hm_meas
    hmdot_meas hψ_L2 hPmdot_zero menv hmenv hmenv_meas ρ hρ hLip hd hTaylor
    θ_hat ν X hX_meas hX_indep hX_id hX_law hθhat_meas hFixedComparison hConsistent
  have hIdet : IsUnit (fisherInformationMatrix M μ θ₀ ℓ).det :=
    (Matrix.isUnit_iff_isUnit_det (fisherInformationMatrix M μ θ₀ ℓ)).mp hI.isUnit
  have hInvNeg : (-(fisherInformationMatrix M μ θ₀ ℓ))⁻¹ =
      -(fisherInformationMatrix M μ θ₀ ℓ)⁻¹ := by
    simpa using
      Matrix.inv_smul' (fisherInformationMatrix M μ θ₀ ℓ) (-1 : ℝˣ) hIdet
  refine ⟨?_, ?_⟩
  · simpa only [hInvNeg, map_neg, ContinuousLinearMap.neg_apply, sub_eq_add_neg] using hT8.1
  · rw [psiCov_score_eq_fisherInformationMatrix M μ θ₀ ℓ,
      mEstimator_fisher_covariance_collapse
        (fisherInformationMatrix M μ θ₀ ℓ) hI] at hT8
    exact hT8.2

set_option maxHeartbeats 800000 in
-- This specialization derives consistency from the KL conditions before applying normality.
/-- **Maximum-likelihood asymptotic normality from KL-identifiable consistency.**

For a DQM model with a measurable local square-integrable log-Lipschitz
envelope, positive-definite Fisher information, and an exact empirical MLE,
the estimator has the inverse-Fisher asymptotic linear representation and is
asymptotically `N(0, I⁻¹)`.  This corollary supplies the consistency hypothesis
of vdV Theorem 5.39 from the stabilized KL/T4 conditions; the score, Fisher,
and Taylor adapters are also derived internally. -/
theorem mle_asymptotic_normality
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: the model is a family of probability densities; vdV Section 5.5.
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: identifiability at the true parameter; vdV Lemma 5.35.
    (hident : ∀ θ,
      parametricMeasure M μ θ = parametricMeasure M μ θ₀ → θ = θ₀)
    -- USER-INPUT: upper semicontinuity of the population criterion for the
    -- consistency argument; vdV Section 5.2.
    (husc : UpperSemicontinuous (stabilizedPopulationCriterion M μ θ₀))
    -- USER-INPUT: a compact superlevel below the maximum for the consistency
    -- argument; vdV Section 5.2.
    (hcompact : ∃ c : ℝ,
      c < stabilizedPopulationCriterion M μ θ₀ θ₀ ∧
        IsCompact {θ | c ≤ stabilizedPopulationCriterion M μ θ₀ θ})
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (X : ℕ → Ξ → Ω) (U : ℕ → Ξ → ℝ)
    -- LEAN-ONLY: a measurable envelope encoding uniform convergence of the
    -- empirical criterion in the internal consistency argument.
    (hU_dom : ∀ n ξ θ,
      |empiricalAvg (stabilizedLogCriterion M θ₀ θ) n
          (fun i : Fin n => X i.val ξ) -
        stabilizedPopulationCriterion M μ θ₀ θ| ≤ U n ξ)
    -- convergence of the measurable T4 envelope.
    (hU_conv : TendstoInMeasure ν U atTop (fun _ => (0 : ℝ)))
    (ℓ : Ω → EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: a measurable score representative; vdV Theorem 5.39.
    (hℓ : Measurable ℓ)
    -- USER-INPUT: differentiability in quadratic mean at the true parameter;
    -- vdV Theorem 5.39.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: a square-integrable local log-likelihood Lipschitz envelope
    -- on a nontrivial neighborhood; vdV Theorem 5.39.
    (menv : Ω → ℝ)
    (hmenv : MemLp menv 2
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- LEAN-ONLY: measurability of the chosen envelope representative.
    (hmenv_meas : Measurable menv)
    (ρ : ℝ)
    -- the Lipschitz neighborhood is nontrivial.
    (hρ : 0 < ρ)
    -- vdV's pairwise local log-likelihood Lipschitz condition.
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ,
      ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ x,
        |M.logDensity θ₁ x - M.logDensity θ₂ x| ≤
          menv x * ‖θ₁ - θ₂‖)
    -- USER-INPUT: nonsingular Fisher information, encoded as positive definiteness;
    -- vdV Theorem 5.39.
    (hI : (fisherInformationMatrix M μ θ₀ ℓ).PosDef)
    -- LEAN-ONLY: an explicit measurable independent identically distributed sequence
    -- realizing the abstract sample under the true model law.
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X ν)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) ν ν)
    (hX_law : ν.map (X 0) =
      μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
    -- LEAN-ONLY: measurability of the estimator as a random vector.
    (hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    -- USER-INPUT: exact maximization of the product likelihood; vdV Section 5.5.
    (hMLE : IsMaximumLikelihoodEstimator M θ_hat) :
    TendstoInProbZero (fun _ : ℕ => ν) (fun n ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
            (fisherInformationMatrix M μ θ₀ ℓ)⁻¹
            (empiricalProcessVec
              (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
              (fun _ i x => ℓ x i) θ₀ n
              (fun i : Fin n => X i.val ξ))) ∧
      WeakConverges
        (fun n => ν.map (fun ξ =>
          Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
        (multivariateGaussian 0
          (fisherInformationMatrix M μ θ₀ ℓ)⁻¹) := by
  letI : IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) :=
    withDensity_density_isProbabilityMeasure M μ hPDF θ₀
  have hConsistent : TendstoInProbZero (fun _ : ℕ => ν)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) :=
    mle_consistentInProb_of_kl_identifiable M μ θ₀ hPDF hident husc hcompact
      θ_hat ν X U hU_dom hU_conv hX_meas hX_id hX_law hMLE
  exact mle_asymptotic_normality_of_consistent M μ θ₀ hPDF θ_hat ν X ℓ hℓ hDQM
    menv hmenv hmenv_meas ρ hρ hLip hI hX_meas hX_indep hX_id hX_law
    hθhat_meas hConsistent hMLE

end AsymptoticStatistics.MaximumLikelihood
