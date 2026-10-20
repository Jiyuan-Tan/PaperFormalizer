module
public import StatLean.AsymptoticStatistics.MaximumLikelihood.AsymptoticNormality
public import StatLean.AsymptoticStatistics.MaximumLikelihood.ParameterSubset

@[expose] public section

/-!
# Maximum-likelihood asymptotic normality on a parameter subset

This file states van der Vaart, Theorem 5.39 for a model indexed by an
arbitrary set `Θ ⊆ ℝᵈ`, with the true parameter an interior point.  The
existing full-Euclidean-space theorem remains available as a specialization.
-/

namespace AsymptoticStatistics.MaximumLikelihood

open MeasureTheory Filter ProbabilityTheory EmpiricalProcess
open scoped ENNReal Topology RealInnerProductSpace Matrix ProbabilityTheory

/-- **Maximum-likelihood asymptotic normality on a parameter subset
(vdV Theorem 5.39).**

For a consistent exact MLE in a DQM model indexed by `Θ ⊆ ℝᵈ`, with the
truth an interior point, a measurable local square-integrable log-Lipschitz
envelope, and nonsingular Fisher information, the estimator has the
inverse-Fisher asymptotic linear representation and is asymptotically
`N(0, I⁻¹)`. -/
theorem mle_asymptotic_normality_on_of_consistent
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Θ : Set (EuclideanSpace ℝ (Fin d))}
    (M : ParametricFamily Ω Θ) (μ : Measure Ω) (θ₀ : Θ)
    -- USER-INPUT: the truth is an interior point of the parameter set;
    -- vdV Theorem 5.39.
    (hθ₀int : (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ interior Θ)
    -- USER-INPUT: the model is a family of probability densities; vdV Section 5.5.
    (hPDF : IsPDFOf M μ)
    (θ_hat : ∀ n, (Fin n → Ω) → Θ)
    {Ξ : Type} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (X : ℕ → Ξ → Ω)
    (ℓ : Ω → EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: a measurable score representative; vdV Theorem 5.39.
    (hℓ : Measurable ℓ)
    -- USER-INPUT: differentiability in quadratic mean at the true parameter within
    -- the parameter set; vdV Theorem 5.39.
    (hDQM : DifferentiableQuadraticMeanOn M μ θ₀ ℓ)
    -- USER-INPUT: a square-integrable local log-likelihood Lipschitz envelope on a
    -- nontrivial neighborhood; vdV Theorem 5.39.
    (menv : Ω → ℝ)
    (hmenv : MemLp menv 2
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- LEAN-ONLY: measurability of the chosen envelope representative.
    (hmenv_meas : Measurable menv)
    (ρ : ℝ)
    -- The supplied likelihood neighborhood is nontrivial.
    (hρ : 0 < ρ)
    -- Theorem 5.39's pairwise local log-likelihood Lipschitz condition on `Θ`.
    (hLip : ∀ θ₁ : Θ,
      (θ₁ : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (θ₀ : EuclideanSpace ℝ (Fin d)) ρ →
      ∀ θ₂ : Θ,
        (θ₂ : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (θ₀ : EuclideanSpace ℝ (Fin d)) ρ →
        ∀ x,
          |M.logDensity θ₁ x - M.logDensity θ₂ x| ≤
            menv x * ‖(θ₁ : EuclideanSpace ℝ (Fin d)) - (θ₂ : EuclideanSpace ℝ (Fin d))‖)
    -- USER-INPUT: nonsingular Fisher information, encoded as positive definiteness;
    -- vdV Theorem 5.39.
    (hI : (fisherInformationMatrixOn M μ θ₀ ℓ).PosDef)
    -- LEAN-ONLY: an explicit measurable independent identically distributed sequence
    -- realizing the abstract sample under the true model law.
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X ν)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) ν ν)
    (hX_law : ν.map (X 0) =
      μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
    -- LEAN-ONLY: measurability after coercion to the ambient Euclidean space.
    (hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => (θ_hat n (fun i : Fin n => X i.val ξ) :
        EuclideanSpace ℝ (Fin d))))
    -- USER-INPUT: consistency for the true parameter; vdV Theorem 5.39.
    (hConsistent : TendstoInProbZero (fun _ => ν) (fun n ξ =>
      (θ_hat n (fun i : Fin n => X i.val ξ) : EuclideanSpace ℝ (Fin d)) -
        (θ₀ : EuclideanSpace ℝ (Fin d))))
    -- USER-INPUT: exact maximization of the product likelihood over the parameter set;
    -- vdV Section 5.5.
    (hMLE : IsMaximumLikelihoodEstimator M θ_hat) :
    TendstoInProbZero (fun _ : ℕ => ν) (fun n ξ =>
        Real.sqrt n •
            ((θ_hat n (fun i : Fin n => X i.val ξ) : EuclideanSpace ℝ (Fin d)) -
              (θ₀ : EuclideanSpace ℝ (Fin d))) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
            (fisherInformationMatrixOn M μ θ₀ ℓ)⁻¹
            (empiricalProcessVec
              (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
              (fun _ i x => ℓ x i) (θ₀ : EuclideanSpace ℝ (Fin d)) n
              (fun i : Fin n => X i.val ξ))) ∧
      WeakConverges
        (fun n => ν.map (fun ξ =>
          Real.sqrt n •
            ((θ_hat n (fun i : Fin n => X i.val ξ) : EuclideanSpace ℝ (Fin d)) -
              (θ₀ : EuclideanSpace ℝ (Fin d)))))
        (multivariateGaussian 0
          (fisherInformationMatrixOn M μ θ₀ ℓ)⁻¹) := by
  let Mext := M.extendFromSetAt θ₀
  let θhatExt := liftEstimatorFromSet θ_hat
  have hPDFext : IsPDFOf Mext μ := by
    exact ParametricFamily.isPDFOf_extendFromSetAt M μ θ₀ hPDF
  have hDQMext : DifferentiableQuadraticMean Mext μ
      (θ₀ : EuclideanSpace ℝ (Fin d)) ℓ := by
    exact (differentiableQuadraticMeanOn_iff_extendFromSetAt M μ θ₀ ℓ).mp hDQM
  obtain ⟨r, hr, _, hLipExt⟩ :=
    exists_radius_extendFromSetAt_logDensity_lipschitz M θ₀ menv ρ
      hθ₀int hρ hLip
  have hmenvExt : MemLp menv 2
      (μ.withDensity fun x => ENNReal.ofReal
        (Mext.density (θ₀ : EuclideanSpace ℝ (Fin d)) x)) := by
    simpa only [Mext, ParametricFamily.extendFromSetAt_density_coe] using hmenv
  have hIext : (fisherInformationMatrix Mext μ
      (θ₀ : EuclideanSpace ℝ (Fin d)) ℓ).PosDef := by
    rw [← fisherInformationMatrixOn_eq M μ θ₀ ℓ]
    exact hI
  have hX_lawExt : ν.map (X 0) =
      μ.withDensity fun x => ENNReal.ofReal
        (Mext.density (θ₀ : EuclideanSpace ℝ (Fin d)) x) := by
    simpa only [Mext, ParametricFamily.extendFromSetAt_density_coe] using hX_law
  have hθhat_measExt : ∀ n, Measurable
      (fun ξ : Ξ => θhatExt n (fun i : Fin n => X i.val ξ)) := by
    intro n
    simpa only [θhatExt, liftEstimatorFromSet_apply] using hθhat_meas n
  have hConsistentExt : TendstoInProbZero (fun _ => ν) (fun n ξ =>
      θhatExt n (fun i : Fin n => X i.val ξ) -
        (θ₀ : EuclideanSpace ℝ (Fin d))) := by
    simpa only [θhatExt, liftEstimatorFromSet_apply] using hConsistent
  have hMLEext : IsMaximumLikelihoodEstimator Mext θhatExt := by
    exact isMaximumLikelihoodEstimator_extendFromSetAt M θ₀ θ_hat hMLE
  have hresult := mle_asymptotic_normality_of_consistent Mext μ
    (θ₀ : EuclideanSpace ℝ (Fin d)) hPDFext θhatExt ν X ℓ hℓ hDQMext
    menv hmenvExt hmenv_meas r hr hLipExt hIext hX_meas hX_indep hX_id
    hX_lawExt hθhat_measExt hConsistentExt hMLEext
  simpa only [Mext, θhatExt, liftEstimatorFromSet_apply,
    ParametricFamily.extendFromSetAt_density_coe,
    ← fisherInformationMatrixOn_eq M μ θ₀ ℓ] using hresult

/-- Maximum-likelihood asymptotic normality on `Θ` when consistency is
derived from the stabilized KL/T4 conditions.  Its conclusion is the same as
the direct form of Theorem 5.39. -/
theorem mle_asymptotic_normality_on
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Θ : Set (EuclideanSpace ℝ (Fin d))}
    (M : ParametricFamily Ω Θ) (μ : Measure Ω) (θ₀ : Θ)
    -- The truth is an inner point of `Θ`.
    (hθ₀int : (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ interior Θ)
    -- The model consists of probability densities.
    (hPDF : IsPDFOf M μ)
    -- Identifiable parametrization at the truth.
    (hident : ∀ θ,
      parametricMeasure M μ θ = parametricMeasure M μ θ₀ → θ = θ₀)
    -- Upper semicontinuity for the consistency route.
    (husc : UpperSemicontinuous (stabilizedPopulationCriterion M μ θ₀))
    -- A compact superlevel strictly below the maximum.
    (hcompact : ∃ c : ℝ,
      c < stabilizedPopulationCriterion M μ θ₀ θ₀ ∧
        IsCompact {θ | c ≤ stabilizedPopulationCriterion M μ θ₀ θ})
    (θ_hat : ∀ n, (Fin n → Ω) → Θ)
    {Ξ : Type} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (X : ℕ → Ξ → Ω) (U : ℕ → Ξ → ℝ)
    -- Measurable-envelope form of T4 uniform convergence.
    (hU_dom : ∀ n ξ θ,
      |empiricalAvg (stabilizedLogCriterion M θ₀ θ) n
          (fun i : Fin n => X i.val ξ) -
        stabilizedPopulationCriterion M μ θ₀ θ| ≤ U n ξ)
    -- Convergence of the measurable T4 envelope.
    (hU_conv : TendstoInMeasure ν U atTop (fun _ => (0 : ℝ)))
    (ℓ : Ω → EuclideanSpace ℝ (Fin d))
    -- Measurability of the DQM score.
    (hℓ : Measurable ℓ)
    -- Differentiability in quadratic mean at `θ₀` within `Θ`.
    (hDQM : DifferentiableQuadraticMeanOn M μ θ₀ ℓ)
    (menv : Ω → ℝ)
    -- The local envelope is square-integrable under the true law.
    (hmenv : MemLp menv 2
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- Measurable representative for the envelope.
    (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    -- Pairwise local log-likelihood Lipschitz condition within `Θ`.
    (hLip : ∀ θ₁ : Θ,
      (θ₁ : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (θ₀ : EuclideanSpace ℝ (Fin d)) ρ →
      ∀ θ₂ : Θ,
        (θ₂ : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (θ₀ : EuclideanSpace ℝ (Fin d)) ρ →
        ∀ x,
          |M.logDensity θ₁ x - M.logDensity θ₂ x| ≤
            menv x * ‖(θ₁ : EuclideanSpace ℝ (Fin d)) - (θ₂ : EuclideanSpace ℝ (Fin d))‖)
    -- Nonsingular Fisher information.
    (hI : (fisherInformationMatrixOn M μ θ₀ ℓ).PosDef)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X ν)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) ν ν)
    (hX_law : ν.map (X 0) =
      μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
    (hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => (θ_hat n (fun i : Fin n => X i.val ξ) :
        EuclideanSpace ℝ (Fin d))))
    -- Exact product-likelihood maximization over `Θ`.
    (hMLE : IsMaximumLikelihoodEstimator M θ_hat) :
    TendstoInProbZero (fun _ : ℕ => ν) (fun n ξ =>
        Real.sqrt n •
            ((θ_hat n (fun i : Fin n => X i.val ξ) : EuclideanSpace ℝ (Fin d)) -
              (θ₀ : EuclideanSpace ℝ (Fin d))) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
            (fisherInformationMatrixOn M μ θ₀ ℓ)⁻¹
            (empiricalProcessVec
              (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
              (fun _ i x => ℓ x i) (θ₀ : EuclideanSpace ℝ (Fin d)) n
              (fun i : Fin n => X i.val ξ))) ∧
      WeakConverges
        (fun n => ν.map (fun ξ =>
          Real.sqrt n •
            ((θ_hat n (fun i : Fin n => X i.val ξ) : EuclideanSpace ℝ (Fin d)) -
              (θ₀ : EuclideanSpace ℝ (Fin d)))))
        (multivariateGaussian 0
          (fisherInformationMatrixOn M μ θ₀ ℓ)⁻¹) := by
  have hsub_mass : ∀ θ, (∫ x, M.density θ x ∂μ) ≤ 1 := by
    intro θ
    rw [hPDF.density_integral_eq_one θ]
  have htrue_mass : (∫ x, M.density θ₀ x ∂μ) = 1 :=
    hPDF.density_integral_eq_one θ₀
  have hunique : ∀ θ, θ ≠ θ₀ →
      stabilizedPopulationCriterion M μ θ₀ θ <
        stabilizedPopulationCriterion M μ θ₀ θ₀ := by
    intro θ hθ
    exact stabilized_populationCriterion_uniquely_maximized_at_truth M μ θ₀
      hPDF.density_integrable hsub_mass htrue_mass hident θ hθ
  have hsep :=
    ForMathlib.wellSeparated_of_uniqueMax_upperSemicontinuous_compactSuperlevel
      (stabilizedPopulationCriterion M μ θ₀) θ₀ hunique husc hcompact
  let θhatΞ : ℕ → Ξ → Θ :=
    fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ)
  have hnear : ∀ n, ∀ᵐ ξ ∂ν,
      empiricalAvg (stabilizedLogCriterion M θ₀ θ₀) n
          (fun i : Fin n => X i.val ξ) ≤
        empiricalAvg (stabilizedLogCriterion M θ₀ (θhatΞ n ξ)) n
          (fun i : Fin n => X i.val ξ) := by
    simpa only [θhatΞ] using stabilized_empirical_nearmax_ae_of_mle
      M μ θ₀ θ_hat ν X hX_meas hX_id hX_law hMLE
  have hcons : ∀ ε > (0 : ℝ),
      Tendsto (fun n => ν {ξ | ε ≤ dist (θhatΞ n ξ) θ₀}) atTop (nhds 0) := by
    exact Consistency.mEstimator_consistent_ae_nearmax
      (Mn := fun n ξ θ => empiricalAvg (stabilizedLogCriterion M θ₀ θ) n
        (fun i : Fin n => X i.val ξ))
      (M := stabilizedPopulationCriterion M μ θ₀) (θ₀ := θ₀)
      (θhat := θhatΞ) (U := U) hU_dom hU_conv hsep hnear
  have hConsistent : TendstoInProbZero (fun _ : ℕ => ν) (fun n ξ =>
      (θ_hat n (fun i : Fin n => X i.val ξ) : EuclideanSpace ℝ (Fin d)) -
        (θ₀ : EuclideanSpace ℝ (Fin d))) := by
    unfold TendstoInProbZero
    intro ε hε
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcons ε hε)
    simpa only [measureReal_def, ENNReal.toReal_zero, θhatΞ, Subtype.dist_eq,
      dist_eq_norm] using! h
  exact mle_asymptotic_normality_on_of_consistent M μ θ₀ hθ₀int hPDF
    θ_hat ν X ℓ hℓ hDQM menv hmenv hmenv_meas ρ hρ hLip hI hX_meas
    hX_indep hX_id hX_law hθhat_meas hConsistent hMLE

end AsymptoticStatistics.MaximumLikelihood
