module
public import StatLean.AsymptoticStatistics.ForMathlib.MatrixInProbability
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LinearizationEquicontinuity

@[expose] public section

/-!
# Linearization for one-step estimators

Definitions and the common expansion core behind vdV Theorems 5.45 and 5.48.
-/

open MeasureTheory
open scoped Topology Matrix.Norms.L2Operator

namespace AsymptoticStatistics.OneStepEstimator

/-- The finite-dimensional parameter and estimating-equation space used in vdV §5.7. -/
abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The scaled estimating-equation residual in conditions (5.44) and (5.47):
`√n(Ψₙ(θ)-Ψₙ(θ₀)) - V₀(√n(θ-θ₀))`.

Edge behavior: at `n = 0`, `Real.sqrt n = 0`, so both scaled terms vanish. -/
noncomputable def oneStepResidual {k : ℕ} (Ψ : ℕ → Ξ → E k → E k) (θ0 : E k)
    (V0 : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) (ξ : Ξ) (θ : E k) : E k :=
  Real.sqrt n • (Ψ n ξ θ - Ψ n ξ θ0) -
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0 (Real.sqrt n • (θ - θ0))

/-- The modified Newton--Raphson one-step update of vdV §5.7:
`preₙ - Vhatₙ⁻¹ Ψₙ(preₙ)`.

Edge behavior: Mathlib's totalized `Matrix.inv` is the zero matrix on a singular
`Vhatₙ`. Hence the correction term is zero and the update equals the preliminary
estimator at that realization; no per-sample invertibility is imposed. -/
noncomputable def oneStepUpdate {k : ℕ} (Ψ : ℕ → Ξ → E k → E k) (pre : ℕ → Ξ → E k)
    (Vhat : ℕ → Ξ → Matrix (Fin k) (Fin k) ℝ) (n : ℕ) (ξ : Ξ) : E k :=
  pre n ξ - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vhat n ξ)⁻¹
    (Ψ n ξ (pre n ξ))

/-- Common algebraic/probabilistic core for vdV Theorems 5.45 and 5.48. It consumes the
leading `O_P(1)` fact, matrix convergence, preliminary root-`n` boundedness, and the
already-evaluated named linearization lemma; it does not assume a final expansion. -/
theorem oneStep_linearExpansion_core
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    {k : ℕ} (Ψ : ℕ → Ξ → E k → E k) (pre : ℕ → Ξ → E k)
    (Vhat : ℕ → Ξ → Matrix (Fin k) (Fin k) ℝ) (θ0 : E k)
    (V0 : Matrix (Fin k) (Fin k) ℝ)
    -- nonsingularity of the deterministic derivative matrix.
    (hV0 : V0.det ≠ 0)
    -- matrix inversion/convergence requires measurable random matrices.
    (hVhat_meas : ∀ n i j, Measurable (fun ξ => Vhat n ξ i j))
    -- `Vhatₙ →ₚ V₀`.
    (hVhat : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => Vhat n ξ - V0))
    -- the leading estimating-equation term is `O_P(1)`.
    (hLeading : IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n • Ψ n ξ θ0))
    -- the preliminary estimator is root-`n` bounded.
    (hpre : IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n • (pre n ξ - θ0)))
    -- The evaluated residual satisfies the applicable condition (5.44) or (5.47).
    (hResidual : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => oneStepResidual Ψ θ0 V0 n ξ (pre n ξ))) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      Real.sqrt n • (oneStepUpdate Ψ pre Vhat n ξ - θ0)
        + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0⁻¹
            (Real.sqrt n • Ψ n ξ θ0)) := by
  let L : ℕ → Ξ → E k := fun n ξ => Real.sqrt n • Ψ n ξ θ0
  let p : ℕ → Ξ → E k := fun n ξ => Real.sqrt n • (pre n ξ - θ0)
  let R : ℕ → Ξ → E k := fun n ξ => oneStepResidual Ψ θ0 V0 n ξ (pre n ξ)
  let A : ℕ → Ξ → Matrix (Fin k) (Fin k) ℝ := fun n ξ => (Vhat n ξ)⁻¹ - V0⁻¹
  have hA : TendstoInProbZero (fun _ : ℕ => μ) A :=
    matrixInv_tendstoInProb_of_det_ne_zero μ Vhat V0 hV0 hVhat_meas hVhat
  have hAL := matrixApply_oP_of_tendstoInProbZero_isBoundedInProb μ A L hA hLeading
  have hVp : IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0 (p n ξ)) := by
    intro ε hε
    obtain ⟨M, hM⟩ := hpre ε hε
    refine ⟨max (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0‖ * M) 0, fun n => ?_⟩
    refine (measureReal_mono (fun ξ hξ => ?_)).trans (hM n)
    have hnorm := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0).le_opNorm (p n ξ)
    simp only [Set.mem_setOf_eq] at hξ ⊢
    by_contra hnot
    have hpM : ‖p n ξ‖ ≤ M := not_lt.mp hnot
    have hop_nonneg : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0‖ := norm_nonneg _
    have := mul_le_mul_of_nonneg_left hpM hop_nonneg
    linarith [le_max_left (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0‖ * M) 0]
  have hAVp := matrixApply_oP_of_tendstoInProbZero_isBoundedInProb μ A
    (fun n ξ => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0 (p n ξ)) hA hVp
  have hV0R := tendstoInProbZero_clm μ
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0⁻¹) hResidual
  have hAR : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (A n ξ) (R n ξ)) := by
    intro ε hε
    have hsub : ∀ n, {ξ | ε ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
        (A n ξ) (R n ξ)‖} ⊆ {ξ | 1 ≤ ‖A n ξ‖} ∪ {ξ | ε ≤ ‖R n ξ‖} := by
      intro n ξ hξ
      by_contra hnot
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnot
      have hbound := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (A n ξ)).le_opNorm
        (R n ξ)
      have hprod : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (A n ξ) (R n ξ)‖
          < ε := lt_of_le_of_lt hbound <| lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right hnot.1.le (norm_nonneg _)) (by simpa using hnot.2)
      exact (not_lt_of_ge hξ) hprod
    have hsum : Filter.Tendsto (fun n => μ.real {ξ | 1 ≤ ‖A n ξ‖} +
        μ.real {ξ | ε ≤ ‖R n ξ‖}) Filter.atTop (nhds 0) := by
      simpa only [R, add_zero] using (hA 1 zero_lt_one).add (hResidual ε hε)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
      (Filter.Eventually.of_forall fun n =>
        (measureReal_mono (hsub n)).trans (measureReal_union_le _ _))
  have hadd : ∀ {Z W : ℕ → Ξ → E k},
      TendstoInProbZero (fun _ : ℕ => μ) Z →
      TendstoInProbZero (fun _ : ℕ => μ) W →
      TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => Z n ξ + W n ξ) := by
    intro Z W hZ hW ε hε
    have hsub : ∀ n, {ξ | ε ≤ ‖Z n ξ + W n ξ‖} ⊆
        {ξ | ε / 2 ≤ ‖Z n ξ‖} ∪ {ξ | ε / 2 ≤ ‖W n ξ‖} := by
      intro n ξ hξ
      by_contra hnot
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnot
      simp only [Set.mem_setOf_eq] at hξ
      linarith [norm_add_le (Z n ξ) (W n ξ)]
    have hsum : Filter.Tendsto (fun n => μ.real {ξ | ε / 2 ≤ ‖Z n ξ‖} +
        μ.real {ξ | ε / 2 ≤ ‖W n ξ‖}) Filter.atTop (nhds 0) := by
      simpa using (hZ (ε / 2) (half_pos hε)).add (hW (ε / 2) (half_pos hε))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
      (Filter.Eventually.of_forall fun n =>
        (measureReal_mono (hsub n)).trans (measureReal_union_le _ _))
  have hneg : ∀ {Z : ℕ → Ξ → E k}, TendstoInProbZero (fun _ : ℕ => μ) Z →
      TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => -Z n ξ) := by
    intro Z hZ ε hε
    simpa only [norm_neg] using hZ ε hε
  have hpieces := hadd (hadd (hadd hAL hAVp) hAR) hV0R
  have hunit : IsUnit V0.det := isUnit_iff_ne_zero.mpr hV0
  have htarget : (fun (n : ℕ) (ξ : Ξ) =>
      Real.sqrt n • (oneStepUpdate Ψ pre Vhat n ξ - θ0)
        + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0⁻¹
            (Real.sqrt n • Ψ n ξ θ0)) =
      (fun (n : ℕ) (ξ : Ξ) => -(((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
          (A n ξ) (L n ξ) +
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (A n ξ)
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0 (p n ξ))) +
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (A n ξ) (R n ξ)) +
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0⁻¹ (R n ξ))) := by
    funext n ξ
    have hVinv : ∀ x : E k, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0⁻¹
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0 x) = x := by
      intro x
      have hmul : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0⁻¹ *
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0 = 1 := by
        rw [← map_mul, Matrix.nonsing_inv_mul V0 hunit, map_one]
      calc
        _ = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0⁻¹ *
            Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0) x :=
          (ContinuousLinearMap.mul_apply _ _ x).symm
        _ = x := by rw [hmul, ContinuousLinearMap.one_apply]
    simp only [A, L, p, R, oneStepUpdate, oneStepResidual, smul_sub, map_sub, map_smul,
      ContinuousLinearMap.sub_apply]
    rw [hVinv, hVinv]
    module
  rw [htarget]
  exact hneg hpieces

/-- Condition (5.44), evaluated at a measurable root-`n` bounded preliminary estimator.
The book takes the supremum over `√n * ‖θ-θ₀‖ ≤ M`, whereas this Lean signature uses
`√n * ‖θ-θ₀‖ < M`. These are equivalent only because the condition is quantified over
every `M > 0`: the strict ball is contained in the closed ball at the same `M`, and the
closed ball at `M` is contained in the strict ball at `M + 1`. Because the outer-sup
predicate has a fixed index type, the actual vector residual norm is set to zero outside
the strict ball. This introduces no additional measurability or compactness assumption. -/
theorem uniformLinearization_at_preliminary
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    {k : ℕ} (Ψ : ℕ → Ξ → E k → E k) (pre : ℕ → Ξ → E k)
    (θ0 : E k) (V0 : Matrix (Fin k) (Fin k) ℝ)
    -- vdV condition (5.44), expanded over its local parameter set.
    (h44 : ∀ M : ℝ, 0 < M →
      EmpiricalProcess.TendstoZeroInOuterProbSup μ (fun n ξ (θ : E k) =>
        if Real.sqrt n * ‖θ - θ0‖ < M then ‖oneStepResidual Ψ θ0 V0 n ξ θ‖ else 0))
    -- root-`n` boundedness of the preliminary estimator.
    (hpre : IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n • (pre n ξ - θ0)))
    -- Measurability needed to evaluate the outer-probability supremum on the ball.
    (hpre_meas : ∀ n : ℕ, Measurable (fun ξ => Real.sqrt n • (pre n ξ - θ0))) :
    TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => oneStepResidual Ψ θ0 V0 n ξ (pre n ξ)) := by
  let h : ℕ → Ξ → E k := fun n ξ => Real.sqrt n • (pre n ξ - θ0)
  let θ : ℕ → E k → E k := fun n z => θ0 + (Real.sqrt n)⁻¹ • z
  let D : ℕ → Ξ → E k → ℝ := fun n ξ z => ‖oneStepResidual Ψ θ0 V0 n ξ (θ n z)‖
  have hsup : ∀ M : ℝ, 0 ≤ M →
      EmpiricalProcess.TendstoZeroInOuterProbSup μ
        (fun n ξ (z : {z : E k // ‖z‖ ≤ M}) => D n ξ z.1) := by
    intro M hM
    have hfull := h44 (M + 1) (by linarith)
    intro ε hε
    have hsub : ∀ n, {ξ | ∃ z : {z : E k // ‖z‖ ≤ M}, ε < |D n ξ z.1|} ⊆
        {ξ | ∃ t : E k, ε <
          |if Real.sqrt n * ‖t - θ0‖ < M + 1
            then ‖oneStepResidual Ψ θ0 V0 n ξ t‖ else 0|} := by
      intro n ξ hξ
      obtain ⟨z, hz⟩ := hξ
      have hlocal : Real.sqrt n * ‖θ n z.1 - θ0‖ < M + 1 := by
        by_cases hn : n = 0
        · subst n
          simp only [θ, Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_smul, add_zero,
            sub_self, norm_zero, zero_mul]
          linarith
        · have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)
          simp only [θ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hsqrt)]
          rw [← mul_assoc, mul_inv_cancel₀ hsqrt.ne', one_mul]
          exact lt_of_le_of_lt z.2 (lt_add_one M)
      refine ⟨θ n z.1, ?_⟩
      rw [if_pos hlocal]
      simpa only [D, abs_norm] using hz
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hfull ε hε)
      (Filter.Eventually.of_forall fun _ => zero_le)
      (Filter.Eventually.of_forall fun n =>
        EmpiricalProcess.outerMeasureStar_mono μ (hsub n))
  have hcollapse := EmpiricalProcess.tendstoInProbZero_of_ball_outerProbSup
    μ D h hpre_meas hsup hpre
  have heval : ∀ n ξ, D n ξ (h n ξ) = ‖oneStepResidual Ψ θ0 V0 n ξ (pre n ξ)‖ := by
    intro n ξ
    by_cases hn : n = 0
    · subst n
      simp only [D, h, θ, Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_smul, add_zero,
        oneStepResidual, map_zero, sub_self, norm_zero]
    · have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)
      simp only [D, h, θ, smul_smul]
      rw [inv_mul_cancel₀ hsqrt.ne', one_smul]
      simp only [add_sub_cancel]
  intro ε hε
  simpa only [heval, Real.norm_eq_abs, abs_norm] using hcollapse ε hε

end AsymptoticStatistics.OneStepEstimator
