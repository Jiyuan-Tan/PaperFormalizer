module
public import StatLean.AsymptoticStatistics.ForMathlib.InProbability
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# Random finite matrices in probability

Finite-dimensional probability results for inversion near a nonsingular
deterministic matrix and for applying a vanishing random matrix to an `O_P(1)` vector.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace AsymptoticStatistics

/-!
## Proof outline

Matrix inversion follows from continuity of inversion at a nonsingular limit.
For matrix-vector products, split according to a tightness threshold for the
vector and use the `L²` operator-norm bound off the tail event.
-/

/-- Matrix inversion preserves convergence in probability at a nonsingular deterministic
matrix. The inverse is Mathlib's total `Matrix.inv`; the nonsingularity assumption excludes
its singular fallback only at the limit matrix. -/
theorem matrixInv_tendstoInProb_of_det_ne_zero
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    {k : ℕ} (Vhat : ℕ → Ξ → Matrix (Fin k) (Fin k) ℝ)
    (V0 : Matrix (Fin k) (Fin k) ℝ)
    -- vdV 5.45/5.48 assume the deterministic limit matrix is nonsingular.
    (hV0 : V0.det ≠ 0)
    -- needed for measurable pushforward/event manipulations.
    (hVhat_meas : ∀ n i j, Measurable (fun ξ => Vhat n ξ i j))
    -- convergence in probability of the estimated matrix.
    (hVhat : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => Vhat n ξ - V0)) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => (Vhat n ξ)⁻¹ - V0⁻¹) := by
  intro ε hε
  have hinv : ContinuousAt Inv.inv V0 :=
    continuousAt_matrix_inv V0 (by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hV0)
  obtain ⟨δ, hδ, h_inv⟩ := (Metric.continuousAt_iff.mp hinv) ε hε
  have hsub : ∀ n, {ξ | ε ≤ ‖(Vhat n ξ)⁻¹ - V0⁻¹‖}
      ⊆ {ξ | δ ≤ ‖Vhat n ξ - V0‖} := by
    intro n ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    by_contra hsmall
    have hdist : dist (Vhat n ξ) V0 < δ := by
      simpa only [dist_eq_norm] using (not_le.mp hsmall)
    have hout : dist (Vhat n ξ)⁻¹ V0⁻¹ < ε := h_inv hdist
    have hnorm : ‖(Vhat n ξ)⁻¹ - V0⁻¹‖ < ε := by
      simpa only [dist_eq_norm] using hout
    exact (not_lt_of_ge hξ) hnorm
  have hVhat_coords : ∀ n, Measurable (fun ξ => Matrix.of.symm (Vhat n ξ)) := by
    intro n
    exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hVhat_meas n i j
  have hnorm_cont : Continuous (fun W : Fin k → Fin k → ℝ => ‖Matrix.of W - V0‖) := by
    apply Continuous.norm
    refine continuous_matrix fun i j => ?_
    change Continuous (fun W : Fin k → Fin k → ℝ => W i j - V0 i j)
    fun_prop
  have hnorm_meas : ∀ n, Measurable (fun ξ => ‖Vhat n ξ - V0‖) := by
    intro n
    exact hnorm_cont.measurable.comp (hVhat_coords n)
  have hsource_meas : ∀ n, MeasurableSet {ξ | δ ≤ ‖Vhat n ξ - V0‖} :=
    fun n => measurableSet_le measurable_const (hnorm_meas n)
  have hsource : Tendsto (fun n =>
      (μ.restrict {ξ | δ ≤ ‖Vhat n ξ - V0‖}).real
        {ξ | δ ≤ ‖Vhat n ξ - V0‖}) atTop (𝓝 0) := by
    convert hVhat δ hδ using 1
    funext n
    rw [measureReal_restrict_apply' (hsource_meas n), Set.inter_self]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    hsource (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun n => by
      calc
        μ.real {ξ | ε ≤ ‖(Vhat n ξ)⁻¹ - V0⁻¹‖}
            ≤ μ.real {ξ | δ ≤ ‖Vhat n ξ - V0‖} := measureReal_mono (hsub n)
        _ = (μ.restrict {ξ | δ ≤ ‖Vhat n ξ - V0‖}).real
              {ξ | δ ≤ ‖Vhat n ξ - V0‖} := by
          rw [measureReal_restrict_apply' (hsource_meas n), Set.inter_self])

/-- A random matrix converging to zero in probability, applied to a vector bounded in
probability, converges to zero in probability. -/
theorem matrixApply_oP_of_tendstoInProbZero_isBoundedInProb
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    {k : ℕ} (A : ℕ → Ξ → Matrix (Fin k) (Fin k) ℝ)
    (X : ℕ → Ξ → EuclideanSpace ℝ (Fin k))
    -- the random matrix is `o_P(1)`.
    (hA : TendstoInProbZero (fun _ : ℕ => μ) A)
    -- the random vector is `O_P(1)`.
    (hX : IsBoundedInProb (fun _ : ℕ => μ) X) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (A n ξ) (X n ξ)) := by
  intro ε hε
  refine Metric.tendsto_atTop.mpr fun η hη => ?_
  obtain ⟨M, hM⟩ := hX (η / 2) (by positivity)
  set K : ℝ := max M 1 with hK_def
  have hK_pos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hMK : M ≤ K := le_max_left M 1
  have hlevel_pos : (0 : ℝ) < ε / K := div_pos hε hK_pos
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp (hA (ε / K) hlevel_pos) (η / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hsub : {ξ | ε ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (A n ξ) (X n ξ)‖}
      ⊆ {ξ | M < ‖X n ξ‖} ∪ {ξ | ε / K ≤ ‖A n ξ‖} := by
    intro ξ hξ
    by_cases hXbig : M < ‖X n ξ‖
    · exact Or.inl hXbig
    · refine Or.inr ?_
      simp only [Set.mem_setOf_eq] at hξ ⊢
      have hXK : ‖X n ξ‖ ≤ K := (not_lt.mp hXbig).trans hMK
      have happ :
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (A n ξ) (X n ξ)‖
            ≤ ‖A n ξ‖ * ‖X n ξ‖ := by
        calc
          _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (A n ξ)‖ * ‖X n ξ‖ :=
            (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (A n ξ)).le_opNorm _
          _ = ‖A n ξ‖ * ‖X n ξ‖ := by
            rw [Matrix.l2_opNorm_toEuclideanCLM]
      rw [div_le_iff₀ hK_pos]
      exact hξ.trans (happ.trans (mul_le_mul_of_nonneg_left hXK (norm_nonneg _)))
  have hsplit : μ.real {ξ | ε ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (A n ξ) (X n ξ)‖}
      ≤ μ.real {ξ | M < ‖X n ξ‖} + μ.real {ξ | ε / K ≤ ‖A n ξ‖} :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hA_small : μ.real {ξ | ε / K ≤ ‖A n ξ‖} < η / 2 := by
    have := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith [hM n]

end AsymptoticStatistics
