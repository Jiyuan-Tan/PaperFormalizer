module
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVec

@[expose] public section

/-!
# Z-estimator bias-residual expansion (vector θ) — coordinatewise discharge

Vector-parameter (`θ ∈ ℝᵈ`) discharge layer for the bundled
`asympLinear_25_59_vec` field of
`EfficientScoreEqBiasResidualAssumptions_vec`, mirroring the scalar
`Discharge/ZEstimatorBiasResidual.lean`.

As in the scalar layer, the Taylor route's algebraic identity already
absorbs vdV's explicit bias term `√n · P_{θ̂_n,η} ℓ̃_{θ̂_n,η̂_n}` into the
asymptotic-linear conclusion (the estimating-equation rate is retained in
each per-coordinate `ZEstimatorTaylorCore`), so the natural specialization
of thm:25.59 in this setup has identically-zero bias. The bias=0
bias-residual expansion is then literally the vector AL expansion
(`asympLinearWithBiasAt_vec_zero_iff_asympLinearAt_vec`), discharged by the
vector Z-estimator Taylor theorem `zEstimator_asympLinear_of_taylor_vec`.

Reference: vdV §25.5, thm:25.59 (vector form).
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative

variable {Ω : Type} [MeasurableSpace Ω]
variable {d : ℕ}
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
variable {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
variable [T_nuis.HasOrthogonalProjection] {e : Fin d → Θ}
variable {estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
variable {score_func_seq : ∀ n, (Fin n → Ω) → (Ω → EuclideanSpace ℝ (Fin d))}
variable {score_l_dot : Matrix (Fin d) (Fin d) (Lp ℝ 2 P)}
variable {θ₀ : EuclideanSpace ℝ (Fin d)}

/-- *vdV thm:25.59 (vector form) — discharge of `asympLinear_25_59_vec`, native route.*

From the vector/matrix primitive bundle `ZEstimatorTaylorCoreNative_vec`,
whose interface does not include the no-bias condition, the vector
Z-estimator satisfies the vector bias-residual
asymptotic-linear expansion with influence tuple `candidateVecEIF S_θ T_nuis e`,
vector centering `θ₀`, and identically-zero bias-residual sequence.

**Proof.** The bias=0 vector bias-residual predicate is literally the
vector AL predicate (`asympLinearWithBiasAt_vec_zero_iff_asympLinearAt_vec`);
discharge it via `zEstimator_asympLinear_of_taylor_vec`.

Reference: vdV §25.5, thm:25.59 (vector form); §25.11 thm:25.77. -/
theorem zEstimator_biasResidual_asympLinear_of_taylor_vec
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) :
    AsymptoticallyLinearWithBiasAt_vec estimator P
      (candidateVecEIF S_θ T_nuis e) θ₀ (fun _ _ => 0) :=
  (asympLinearWithBiasAt_vec_zero_iff_asympLinearAt_vec _ _ _ _).mpr
    (zEstimator_asympLinear_of_taylor_vec h)

/-- **Zero-residual vector Taylor assumptions as a bias-residual bundle.**

Constructs `EfficientScoreEqBiasResidualAssumptions_vec` from
`ZEstimatorTaylorCoreNative_vec` and the EIF-construction inputs `h_mem` and `h_Dψ`, with
residual `(fun _ _ => 0)`. Positive definiteness is inherited from `h.hPD`, and
`asympLinear_25_59_vec` is supplied by
`zEstimator_biasResidual_asympLinear_of_taylor_vec`.

Reference: vdV §25.5, Theorem 25.59 (vector form). -/
def toEfficientScoreEqBiasResidualAssumptions_vec
    {T : Submodule ℝ ↥(L2ZeroMean P)}
    {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀)
    (h_mem : ∀ j, candidateVecEIF S_θ T_nuis e j ∈ T)
    (h_Dψ : ∀ (j : Fin d) (g : T),
      (EuclideanSpace.proj j ∘L Dψ) g
        = ⟪candidateVecEIF S_θ T_nuis e j, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    AsymptoticStatistics.Asymptotics.ZEstimatorVec.EfficientScoreEqBiasResidualAssumptions_vec
      P Θ S_θ T_nuis e T Dψ estimator (fun _ _ => 0) θ₀ where
  hPD := h.hPD
  h_mem := h_mem
  h_Dψ := h_Dψ
  asympLinear_25_59_vec := zEstimator_biasResidual_asympLinear_of_taylor_vec h

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVec
