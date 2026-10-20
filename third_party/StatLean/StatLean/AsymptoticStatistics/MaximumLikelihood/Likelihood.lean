module
public import StatLean.AsymptoticStatistics.DQM.LogDensity
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalMeasure

@[expose] public section

/-!
# Likelihood of a finite sample

This file records the product likelihood used by maximum-likelihood estimators.
The definition is valid at `n = 0`, where the empty product is `1`.
-/

namespace AsymptoticStatistics.MaximumLikelihood

/-- The likelihood of a parameter at a finite sample is the product of its
density values.  At the empty sample this is the empty product `1`. -/
noncomputable def sampleLikelihood
    {X Θ : Type*} [MeasurableSpace X] (M : ParametricFamily X Θ)
    (θ : Θ) (n : ℕ) (x : Fin n → X) : ℝ :=
  ∏ i, M.density θ (x i)

/-- An exact maximum-likelihood estimator maximizes the product likelihood on
every finite sample. -/
def IsMaximumLikelihoodEstimator
    {X Θ : Type*} [MeasurableSpace X] (M : ParametricFamily X Θ)
    (θhat : ∀ n, (Fin n → X) → Θ) : Prop :=
  ∀ n x θ, sampleLikelihood M θ n x ≤ sampleLikelihood M (θhat n x) n x

/-- A likelihood comparison whose fixed comparator product is positive gives
the corresponding empirical log-density comparison.  Positivity is on the
left-hand comparator; no converse is claimed because `Real.log 0 = 0`. -/
theorem empiricalAvg_logDensity_le_of_sampleLikelihood_le
    {X Θ : Type*} [MeasurableSpace X] (M : ParametricFamily X Θ)
    {θ η : Θ} {n : ℕ} {x : Fin n → X}
    -- Positivity of the fixed comparator likelihood.
    (hpos : 0 < sampleLikelihood M θ n x)
    -- The product-likelihood comparison.
    (hle : sampleLikelihood M θ n x ≤ sampleLikelihood M η n x) :
    EmpiricalProcess.empiricalAvg (M.logDensity θ) n x ≤
      EmpiricalProcess.empiricalAvg (M.logDensity η) n x := by
  have hθprod_pos : 0 < ∏ i : Fin n, M.density θ (x i) := by
    simpa [sampleLikelihood] using hpos
  have hprod_le :
      (∏ i : Fin n, M.density θ (x i)) ≤ ∏ i : Fin n, M.density η (x i) := by
    simpa [sampleLikelihood] using hle
  have hηprod_pos : 0 < ∏ i : Fin n, M.density η (x i) :=
    lt_of_lt_of_le hθprod_pos hprod_le
  have hθ_ne (i : Fin n) : M.density θ (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hθprod_pos.ne') i (Finset.mem_univ i)
  have hη_ne (i : Fin n) : M.density η (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hηprod_pos.ne') i (Finset.mem_univ i)
  have hθ_pos (i : Fin n) : 0 < M.density θ (x i) :=
    lt_of_le_of_ne (M.density_nonneg θ (x i)) (hθ_ne i).symm
  have hη_pos (i : Fin n) : 0 < M.density η (x i) :=
    lt_of_le_of_ne (M.density_nonneg η (x i)) (hη_ne i).symm
  have hsum_le :
      (∑ i : Fin n, Real.log (M.density θ (x i))) ≤
        ∑ i : Fin n, Real.log (M.density η (x i)) := by
    calc
      ∑ i : Fin n, Real.log (M.density θ (x i)) =
          Real.log (∏ i : Fin n, M.density θ (x i)) := by
        symm
        simpa using (Real.log_prod (s := Finset.univ)
          (f := fun i : Fin n => M.density θ (x i)) (fun i _ => (hθ_pos i).ne'))
      _ ≤ Real.log (∏ i : Fin n, M.density η (x i)) :=
        Real.log_le_log hθprod_pos hprod_le
      _ = ∑ i : Fin n, Real.log (M.density η (x i)) := by
        simpa using (Real.log_prod (s := Finset.univ)
          (f := fun i : Fin n => M.density η (x i)) (fun i _ => (hη_pos i).ne'))
  have hn_inv_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  simpa [EmpiricalProcess.empiricalAvg, ParametricFamily.logDensity] using
    mul_le_mul_of_nonneg_left hsum_le hn_inv_nonneg

end AsymptoticStatistics.MaximumLikelihood
