module
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.LeastFavorableVec

@[expose] public section

/-!
# Scalar specialization of the approximate least-favorable theorem

The scalar statements are the `Fin 1` specializations of the native vector
result. Reference: van der Vaart, §25.11, Theorem 25.77, p. 409.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.Discharge.LeastFavorable

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasExpansionVec
open AsymptoticStatistics.Asymptotics.Discharge.LeastFavorableVec

variable {Omega : Type} [MeasurableSpace Omega]
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {Theta : Type*} [NormedAddCommGroup Theta] [InnerProductSpace Real Theta]
  [CompleteSpace Theta]
variable {S_theta : OrdinaryScore P Theta} {T_nuis : NuisanceTangentSpace P}
  [proj : T_nuis.HasOrthogonalProjection] {e : Fin 1 -> Theta}
variable {H : Type*}
variable {M : QMDModel (Omega := Omega) P 1}
variable {modelLaw : EuclideanSpace Real (Fin 1) -> H -> Measure Omega}
variable {nuisancePath : EuclideanSpace Real (Fin 1) -> H ->
  EuclideanSpace Real (Fin 1) -> H}
variable {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin 1)}
variable {nuisanceEstimator : forall n, (Fin n -> Omega) -> H}
variable {theta0 : EuclideanSpace Real (Fin 1)} {eta0 : H}
variable {F : Fin 1 -> Set (Omega -> Real)} {envelope : Omega -> Real}

local instance scalarProjection2577 : T_nuis.HasOrthogonalProjection := proj

/-- Scalar asymptotic linearity obtained by evaluating the native vector
Theorem 25.77 conclusion at the sole coordinate. -/
theorem mle_asympLinear_2577_native
    (h : @ApproxLeastFavorable2577NativeHyp_vec Omega _ 1 P _ Theta _ _ _
      S_theta T_nuis proj e H M modelLaw nuisancePath estimator nuisanceEstimator
      theta0 eta0 F envelope) :
    AsymptoticallyLinearAt (fun n X => estimator n X 0) P
      (@candidateVecEIF Omega _ P _ Theta _ _ _ 1 S_theta T_nuis proj e 0)
      (theta0 0) := by
  have hv := @ApproxLeastFavorable2577NativeHyp_vec.asympLinear_2577
    Omega _ 1 P _ Theta _ _ _ S_theta T_nuis proj e H M modelLaw nuisancePath
    estimator nuisanceEstimator theta0 eta0 F envelope h
  exact asymptoticallyLinearAt_vec_fin_one_iff.mp hv

/-- Scalar semiparametric efficiency as a `Fin 1` specialization of the
native proper-submodel theorem. -/
theorem mle_semiparametricallyEfficient_2577_native
    -- USER-INPUT: the approximate least-favorable submodel hypotheses;
    -- vdV Theorem 25.77.
    (h : @ApproxLeastFavorable2577NativeHyp_vec Omega _ 1 P _ Theta _ _ _
      S_theta T_nuis proj e H M modelLaw nuisancePath estimator nuisanceEstimator
      theta0 eta0 F envelope)
    {T : Submodule Real ↥(L2ZeroMean P)} {dpsi : T →L[Real] Real}
    -- USER-INPUT: the candidate lies in the tangent space and represents the
    -- pathwise derivative; vdV Theorem 25.77.
    (h_mem : @candidateVecEIF Omega _ P _ Theta _ _ _ 1
      S_theta T_nuis proj e 0 ∈ T)
    (h_dpsi : forall g : T, dpsi g = inner Real
      (@candidateVecEIF Omega _ P _ Theta _ _ _ 1 S_theta T_nuis proj e 0)
      (g : ↥(L2ZeroMean P)))
    -- USER-INPUT: the target functional has truth value `theta0 0`.
    {psi : Measure Omega -> Real} (hpsi : psi P = theta0 0) :
    SemiparametricallyEfficientAt (fun n X => estimator n X 0) psi P T := by
  have hEIF : IsEfficientInfluenceFunction P T dpsi
      (@candidateVecEIF Omega _ P _ Theta _ _ _ 1 S_theta T_nuis proj e 0) := by
    refine ⟨?_, h_mem⟩
    intro g
    exact (h_dpsi g).symm
  have hAL : AsymptoticallyLinearAt (fun n X => estimator n X 0) P
      (@candidateVecEIF Omega _ P _ Theta _ _ _ 1 S_theta T_nuis proj e 0)
      (psi P) := by
    rw [hpsi]
    exact mle_asympLinear_2577_native h
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif hEIF hAL

end AsymptoticStatistics.Asymptotics.Discharge.LeastFavorable
