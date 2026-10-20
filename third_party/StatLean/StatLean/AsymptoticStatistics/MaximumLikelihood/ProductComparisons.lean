module
public import StatLean.AsymptoticStatistics.DQM.LogDensity
public import StatLean.AsymptoticStatistics.DQM.ZeroDensity
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalMeasure
public import StatLean.AsymptoticStatistics.ForMathlib.InProbability
public import StatLean.AsymptoticStatistics.MaximumLikelihood.Likelihood

@[expose] public section

/-!
# Product-likelihood comparisons

These adapters transfer exact product maximization to empirical log-likelihood
comparisons without assuming positivity.  The only failure event is that the
fixed comparator density vanishes at some sampled coordinate.
-/

namespace AsymptoticStatistics.MaximumLikelihood

open MeasureTheory Filter ProbabilityTheory EmpiricalProcess
open scoped ENNReal Topology ProbabilityTheory

/-- The probability that a fixed comparator has zero product likelihood is at
most `n` times its one-observation zero-density probability. -/
theorem sampleLikelihood_zero_probability_le
    {X Θ : Type*} [MeasurableSpace X]
    (M : ParametricFamily X Θ) (P₀ : Measure X)
    (θ : Θ) (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xs : ℕ → Ω → X)
    -- Measurability of sample coordinates and the failure event.
    (hXs_meas : ∀ i, Measurable (Xs i))
    -- Identical-distribution component of the sample encoding.
    (hXs_id : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
    -- Identifies the common observation law with `P₀`.
    (hXs_law : P.map (Xs 0) = P₀) :
    P.real {ω | sampleLikelihood M θ n (fun i : Fin n => Xs i.val ω) = 0} ≤
      (n : ℝ) * P₀.real {x | M.density θ x = 0} := by
  classical
  let Z : Set X := {x | M.density θ x = 0}
  let E : Fin n → Set Ω := fun i => Xs i.val ⁻¹' Z
  have hZ_meas : MeasurableSet Z := by
    exact measurableSet_eq_fun (M.density_meas θ) measurable_const
  have hzero :
      {ω | sampleLikelihood M θ n (fun i : Fin n => Xs i.val ω) = 0} =
        ⋃ i : Fin n, E i := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E, Z, Set.mem_preimage]
    simp [sampleLikelihood, Finset.prod_eq_zero_iff]
  have hcoord (i : Fin n) : P.real (E i) = P₀.real Z := by
    calc
      P.real (E i) = (P.map (Xs i.val)).real Z := by
        symm
        exact map_measureReal_apply (hXs_meas i.val) hZ_meas
      _ = (P.map (Xs 0)).real Z := by rw [(hXs_id i.val).map_eq]
      _ = P₀.real Z := by rw [hXs_law]
  rw [hzero]
  calc
    P.real (⋃ i : Fin n, E i) ≤ ∑ i : Fin n, P.real (E i) :=
      measureReal_iUnion_fintype_le E
    _ = ∑ _i : Fin n, P₀.real Z := by simp only [hcoord]
    _ = (n : ℝ) * P₀.real Z := by simp

/-- At every fixed local direction, an exact product MLE is an empirical
log-likelihood near-maximizer in probability.  DQM makes the probability of a
zero comparator product vanish at the required `n⁻¹` scale. -/
theorem mle_logDensity_fixedComparison_tendstoInProbZero
    {d : ℕ} {X : Type*} [MeasurableSpace X]
    (M : ParametricFamily X (EuclideanSpace ℝ (Fin d)))
    (μ : Measure X) (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : X → EuclideanSpace ℝ (Fin d))
    -- The model consists of probability densities.
    (hPDF : IsPDFOf M μ)
    -- Differentiability in quadratic mean at the truth.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (θhat : ∀ n, (Fin n → X) → EuclideanSpace ℝ (Fin d))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xs : ℕ → Ω → X)
    -- Measurable sample-map encoding.
    (hXs_meas : ∀ i, Measurable (Xs i))
    -- Identical-distribution component of the iid sample encoding.
    (hXs_id : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
    -- Identifies the common sample law with the true model law.
    (hXs_law : P.map (Xs 0) =
      μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
    -- Exact product-likelihood maximization.
    (hMLE : IsMaximumLikelihoodEstimator M θhat)
    (a : EuclideanSpace ℝ (Fin d)) :
    TendstoInProbZero (fun _ : ℕ => P) (fun n ω =>
      (n : ℝ) * max 0
        (empiricalAvg
            (M.logDensity (θ₀ + (Real.sqrt n)⁻¹ • a)) n
            (fun i : Fin n => Xs i.val ω) -
          empiricalAvg
            (M.logDensity (θhat n (fun i : Fin n => Xs i.val ω))) n
            (fun i : Fin n => Xs i.val ω))) := by
  let θn : ℕ → EuclideanSpace ℝ (Fin d) := fun n =>
    θ₀ + (Real.sqrt n)⁻¹ • a
  let P₀ : Measure X :=
    μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)
  intro ε hε
  have hsub (n : ℕ) :
      {ω | ε ≤ ‖(n : ℝ) * max 0
        (empiricalAvg (M.logDensity (θn n)) n
            (fun i : Fin n => Xs i.val ω) -
          empiricalAvg
            (M.logDensity (θhat n (fun i : Fin n => Xs i.val ω))) n
            (fun i : Fin n => Xs i.val ω))‖} ⊆
        {ω | sampleLikelihood M (θn n) n
          (fun i : Fin n => Xs i.val ω) = 0} := by
    intro ω hω
    by_contra hprod
    have hprod_nonneg :
        0 ≤ sampleLikelihood M (θn n) n
          (fun i : Fin n => Xs i.val ω) := by
      simp only [sampleLikelihood]
      exact Finset.prod_nonneg fun i _ => M.density_nonneg (θn n) (Xs i.val ω)
    have hprod_pos :
        0 < sampleLikelihood M (θn n) n
          (fun i : Fin n => Xs i.val ω) :=
      lt_of_le_of_ne hprod_nonneg (Ne.symm hprod)
    have havg_le :
        empiricalAvg (M.logDensity (θn n)) n
            (fun i : Fin n => Xs i.val ω) ≤
          empiricalAvg
            (M.logDensity (θhat n (fun i : Fin n => Xs i.val ω))) n
            (fun i : Fin n => Xs i.val ω) :=
      empiricalAvg_logDensity_le_of_sampleLikelihood_le M hprod_pos
        (hMLE n (fun i : Fin n => Xs i.val ω) (θn n))
    have hmax : max 0
        (empiricalAvg (M.logDensity (θn n)) n
            (fun i : Fin n => Xs i.val ω) -
          empiricalAvg
            (M.logDensity (θhat n (fun i : Fin n => Xs i.val ω))) n
            (fun i : Fin n => Xs i.val ω)) = 0 := by
      exact max_eq_left (sub_nonpos.mpr havg_le)
    simp only [Set.mem_setOf_eq] at hω
    rw [hmax, mul_zero, norm_zero] at hω
    exact (not_le_of_gt hε) hω
  have hle (n : ℕ) :
      P.real {ω | ε ≤ ‖(n : ℝ) * max 0
        (empiricalAvg (M.logDensity (θn n)) n
            (fun i : Fin n => Xs i.val ω) -
          empiricalAvg
            (M.logDensity (θhat n (fun i : Fin n => Xs i.val ω))) n
            (fun i : Fin n => Xs i.val ω))‖} ≤
        (n : ℝ) * P₀.real {x | M.density (θn n) x = 0} :=
    (measureReal_mono (hsub n)).trans
      (sampleLikelihood_zero_probability_le M P₀ (θn n) n P Xs
        hXs_meas hXs_id hXs_law)
  have hzero : Tendsto
      (fun n : ℕ => (n : ℝ) * P₀.real {x | M.density (θn n) x = 0})
      atTop (𝓝 0) := by
    simpa only [P₀, θn] using
      dqm_zeroDensity_localScale_tendsto M μ θ₀ ℓ hPDF hDQM a
  simpa only [θn] using
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
      (Eventually.of_forall fun _ => measureReal_nonneg)
      (Eventually.of_forall hle)

end AsymptoticStatistics.MaximumLikelihood
