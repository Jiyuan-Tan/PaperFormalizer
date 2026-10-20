module
public import StatLean.AsymptoticStatistics.Asymptotics.ZEstimatorVec
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperational
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScoreVec

@[expose] public section

/-!
# Z-estimator semiparametric efficiency for vector parameters

This file proves the vector-parameter (`θ ∈ ℝᵈ`) form of van der Vaart,
Theorem 25.54.

## Multivariate formulation

The theorem `ZEstimatorVecNative.mle_asympLinear_of_nativeTaylorCore_vec`
derives the vector residual directly through the `d × d` identity
`√n·Ĩ·(θ̂−θ₀) = 𝔾ₙℓ̃ + o_P` and then applies `Ĩ⁻¹`, so the influence is
`Ĩ⁻¹ℓ̃ = candidateVecEIF`. This is valid for arbitrary non-diagonal `Ĩ`.
Its vector and matrix regularity assumptions are recorded by
`ZEstimatorTaylorCoreNative_vec` (`hPD`, the vector estimating equation
`score_eq_vec`, the matrix Bartlett identity `matrix_bartlett`, and the matrix
DQM-Taylor remainder `matrix_taylor`).

## Coordinatewise reduction

The **vector→coordinatewise reduction**
`asymptoticallyLinearAt_vec_of_forall_coord` states that a vector estimator
`T_n : (Fin n → Ω) → EuclideanSpace ℝ (Fin d)`
is asymptotically linear with influence tuple `φ` and vector centering `c`
if for every coordinate `j`, the scalar coordinate `T_n · j` is
asymptotically linear with scalar influence function `φ j` and scalar
centering `c j`. This is a pure measure-theoretic union/coordinate bound:
vector norm convergence in `Pⁿ`-probability follows from the `d`
coordinatewise scalar convergences (`EuclideanSpace.norm_eq` +
Cauchy-Schwarz over coordinates). The `j`-th coordinate of the vector
residual `√n·(T_n X − c) − (√n)⁻¹·Σᵢ tupleEval P φ (Xᵢ)` equals the scalar
residual `√n·((T_n X) j − c j) − (√n)⁻¹·Σᵢ (φ j)(Xᵢ)`
(`vec_residual_coord`), so the reduction is literal coordinatewise.

Reference: vdV §25.5, thm:25.54 (vector form); §25.11 thm:25.77.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative

variable {Ω : Type} [MeasurableSpace Ω]
variable {d : ℕ}

/-! ### Coordinate lemmas for `EuclideanSpace ℝ (Fin d)` -/

/-- A single coordinate of a Euclidean vector is bounded by its norm. -/
private lemma abs_coord_le_norm (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    |x j| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (abs_nonneg (x.ofLp j))]
  apply Real.sqrt_le_sqrt
  rw [sq_abs]
  exact (Finset.single_le_sum (f := fun i => ‖x.ofLp i‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ j)).trans_eq'
    (by rw [Real.norm_eq_abs, sq_abs])

/-- If every coordinate is strictly below `ε / √d`, the Euclidean norm is
strictly below `ε` (needs `d > 0` and `ε > 0`). -/
private lemma norm_lt_of_forall_coord_lt (x : EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (hd : 0 < d) (hε : 0 < ε) (h : ∀ j, |x j| < ε / Real.sqrt d) : ‖x‖ < ε := by
  rw [EuclideanSpace.norm_eq]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [show ε = Real.sqrt (ε ^ 2) by rw [Real.sqrt_sq hε.le]]
  apply Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => by positivity))
  calc ∑ i, ‖x.ofLp i‖ ^ 2 < ∑ _i : Fin d, (ε / Real.sqrt d) ^ 2 := by
        apply Finset.sum_lt_sum_of_nonempty
          (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd))
        intro i _
        rw [Real.norm_eq_abs, sq_abs]
        have hi := abs_lt.mp (h i)
        exact sq_lt_sq' hi.1 hi.2
    _ = ε ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          div_pow, Real.sq_sqrt hdR.le]
        field_simp

/-- The `j`-th coordinate of the vector AL residual equals the scalar AL
residual of the `j`-th coordinate estimator, centering, and influence
function. -/
private lemma vec_residual_coord
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (φ : Fin d → ↥(L2ZeroMean P)) (c : EuclideanSpace ℝ (Fin d))
    (n : ℕ) (X : Fin n → Ω) (j : Fin d) :
    (Real.sqrt n • (T_n n X - c)
        - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P φ (X i))) j
      = Real.sqrt n * (T_n n X j - c j)
        - (Real.sqrt n)⁻¹
          * (∑ i, ((φ j : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)) := by
  have h_te : ∀ i, tupleEval P φ (X i) j
      = ((φ j : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i) := fun i => rfl
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  rw [show (∑ i, tupleEval P φ (X i)).ofLp j
        = ∑ i, (tupleEval P φ (X i)).ofLp j by
      simp only [WithLp.ofLp_sum, Finset.sum_apply]]
  congr 2

/-- **Vector→coordinatewise reduction (sufficiency direction).**

If, for every coordinate `j`, the scalar coordinate estimator
`fun n X => T_n n X j` is asymptotically linear at `P` with scalar
influence function `φ j` and scalar centering `c j`, then the vector
estimator `T_n` is asymptotically linear at `P` with influence tuple `φ`
and vector centering `c`.

The vector residual's norm `≥ ε` event is contained (for `d > 0`) in the
union over `j` of the coordinate events `|residual j| ≥ ε/√d`
(`norm_lt_of_forall_coord_lt`); the measure is bounded by the finite sum
of coordinate measures, each → 0 at threshold `ε/√d`. The `d = 0` case is
vacuous (`EuclideanSpace ℝ (Fin 0)` has norm 0). -/
theorem asymptoticallyLinearAt_vec_of_forall_coord
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : Fin d → ↥(L2ZeroMean P)) (c : EuclideanSpace ℝ (Fin d))
    (h : ∀ j, AsymptoticallyLinearAt (fun n X => T_n n X j) P (φ j) (c j)) :
    AsymptoticallyLinearAt_vec T_n P φ c := by
  intro ε hε
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: the residual lives in `EuclideanSpace ℝ (Fin 0)`, norm = 0 < ε.
    subst hd0
    have h_set_empty : ∀ n : ℕ,
        {X : Fin n → Ω |
          ε ≤ ‖Real.sqrt n • (T_n n X - c)
                - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P φ (X i))‖} = ∅ := by
      intro n
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have : ‖Real.sqrt n • (T_n n X - c)
              - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P φ (X i))‖ = 0 := by
        rw [EuclideanSpace.norm_eq]
        simp
      rw [this]; exact hε
    simp only [h_set_empty, measure_empty]
    exact tendsto_const_nhds
  · -- d > 0: union bound over coordinates.
    have hsqrtd_pos : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hdpos)
    have hεd_pos : (0 : ℝ) < ε / Real.sqrt d := div_pos hε hsqrtd_pos
    -- Each coordinate measure → 0 at threshold ε/√d.
    have h_coord : ∀ j, Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε / Real.sqrt d ≤ |Real.sqrt n * (T_n n X j - c j)
                  - (Real.sqrt n)⁻¹
                    * (∑ i, ((φ j : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i))|})
        atTop (𝓝 0) := fun j => h j (ε / Real.sqrt d) hεd_pos
    -- Squeeze the vector measure between 0 and the sum of coordinate measures.
    rw [show (0 : ℝ≥0∞) = ∑ _j : Fin d, (0 : ℝ≥0∞) by simp]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_finset_sum (Finset.univ : Finset (Fin d)) (fun j _ => h_coord j))
    · exact Filter.Eventually.of_forall (fun _ => by simp)
    · refine Filter.Eventually.of_forall (fun n => ?_)
      refine le_trans (measure_mono ?_) (measure_iUnion_fintype_le _ _)
      intro X hX
      simp only [Set.mem_setOf_eq] at hX
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      by_contra hc
      push Not at hc
      -- All coordinates < ε/√d ⇒ norm < ε ⇒ contradiction with hX.
      have h_all : ∀ j, |(Real.sqrt n • (T_n n X - c)
            - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P φ (X i))) j| < ε / Real.sqrt d := by
        intro j
        rw [vec_residual_coord]
        exact hc j
      have := norm_lt_of_forall_coord_lt _ ε hdpos hε h_all
      exact absurd hX (not_le.mpr this)

/-! ### Vector Taylor theorem -/

open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
variable {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
variable [T_nuis.HasOrthogonalProjection] {e : Fin d → Θ}
variable {estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
variable {score_func_seq : ∀ n, (Fin n → Ω) → (Ω → EuclideanSpace ℝ (Fin d))}
variable {score_l_dot : Matrix (Fin d) (Fin d) (Lp ℝ 2 P)}
variable {θ₀ : EuclideanSpace ℝ (Fin d)}

/-- **vdV Theorem 25.54 (vector form): asymptotic linearity.**

From the vector and matrix assumptions
`ZEstimatorTaylorCoreNative_vec` (`hPD`, the vector estimating equation
`score_eq_vec`, the matrix Bartlett identity `matrix_bartlett`, the matrix
DQM-Taylor remainder `matrix_taylor`), the vector Z-estimator is
asymptotically linear at `P` with influence tuple `candidateVecEIF S_θ T_nuis e`
and vector centering `θ₀`. The proof uses the matrix identity
`√n·Ĩ·(θ̂−θ₀) = 𝔾ₙℓ̃ + o_P` and therefore permits arbitrary
non-diagonal information matrices.

Reference: vdV §25.5, thm:25.54 (vector form); §25.11 thm:25.77. -/
theorem zEstimator_asympLinear_of_taylor_vec
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) :
    AsymptoticallyLinearAt_vec estimator P
      (candidateVecEIF S_θ T_nuis e) θ₀ :=
  mle_asympLinear_of_nativeTaylorCore_vec h

/-- Construct `EfficientScoreEqAssumptions_vec` from the vector Taylor assumptions.

The vector Taylor conclusion and the EIF characterization
(`h_mem`, `h_Dψ`) yield `EfficientScoreEqAssumptions_vec`, so
`zEstimator_semiparametricallyEfficient_vec` follows from the proved
asymptotic-linear expansion.

Reference: vdV §25.5, thm:25.54 (vector form). -/
def toEfficientScoreEqAssumptions_vec
    {T : Submodule ℝ ↥(L2ZeroMean P)}
    {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀)
    (h_mem : ∀ j, candidateVecEIF S_θ T_nuis e j ∈ T)
    (h_Dψ : ∀ (j : Fin d) (g : T),
      (EuclideanSpace.proj j ∘L Dψ) g
        = ⟪candidateVecEIF S_θ T_nuis e j, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    AsymptoticStatistics.Asymptotics.ZEstimatorVec.EfficientScoreEqAssumptions_vec
      P Θ S_θ T_nuis e T Dψ estimator θ₀ where
  hPD := h.hPD
  h_mem := h_mem
  h_Dψ := h_Dψ
  asympLinear_25_54_vec := zEstimator_asympLinear_of_taylor_vec h

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVec
