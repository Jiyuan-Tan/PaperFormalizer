module
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasExpansionVec
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative

@[expose] public section

/-!
# Approximate least-favorable proper submodels

This file proves the native vector form of van der Vaart, Theorem 25.77
(§25.11, p. 409). The fitted score is the derivative of a proper nuisance
submodel whose likelihood is the Radon--Nikodym density of its model law.
Equations (25.75) and (25.76), Donsker localization, parametric MLE
consistency, and local MLE maximality imply the first-order moving-bias
expansion of Theorem 25.54. The inverse of the full efficient-information
matrix then gives the efficient influence function.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.Discharge.LeastFavorableVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasExpansionVec
open AsymptoticStatistics.EmpiricalProcess

/-- The `j`th coordinate direction in the native Euclidean parameter. -/
noncomputable def coordinateDirection2577_vec {d : Nat} (j : Fin d) :
    EuclideanSpace Real (Fin d) :=
  PiLp.single (β := fun _ : Fin d => Real) 2 j 1

/-- The canonical density of a model law relative to the QMD dominating
measure. -/
noncomputable def modelDensity2577_vec
    {Omega H : Type*} [MeasurableSpace Omega] {d : Nat}
    {P : Measure Omega} [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (modelLaw : EuclideanSpace Real (Fin d) -> H -> Measure Omega)
    (theta : EuclideanSpace Real (Fin d)) (eta : H) (omega : Omega) : Real :=
  ((modelLaw theta eta).rnDeriv M.dominating omega).toReal

/-- Log density along the vector proper nuisance submodel through
`(theta, eta)`. -/
noncomputable def properSubmodelLogLikelihood2577_vec
    {Omega H : Type*} [MeasurableSpace Omega] {d : Nat}
    {P : Measure Omega} [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (modelLaw : EuclideanSpace Real (Fin d) -> H -> Measure Omega)
    (nuisancePath : EuclideanSpace Real (Fin d) -> H ->
      EuclideanSpace Real (Fin d) -> H)
    (theta : EuclideanSpace Real (Fin d)) (eta : H)
    (delta : EuclideanSpace Real (Fin d)) (omega : Omega) : Real :=
  Real.log (modelDensity2577_vec M modelLaw (theta + delta)
    (nuisancePath theta eta delta) omega)

/-- Vector proper-submodel score. Its `j`th coordinate is the derivative
along `delta = t e_j`. -/
noncomputable def properSubmodelScore2577_vec
    {Omega H : Type*} [MeasurableSpace Omega] {d : Nat}
    {P : Measure Omega} [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (modelLaw : EuclideanSpace Real (Fin d) -> H -> Measure Omega)
    (nuisancePath : EuclideanSpace Real (Fin d) -> H ->
      EuclideanSpace Real (Fin d) -> H)
    (theta : EuclideanSpace Real (Fin d)) (eta : H) (omega : Omega) :
    EuclideanSpace Real (Fin d) :=
  WithLp.toLp 2 (fun j => deriv
    (fun t : Real => properSubmodelLogLikelihood2577_vec M modelLaw nuisancePath
      theta eta (t • coordinateDirection2577_vec j) omega) 0)

/-- The proper-submodel score evaluated at the joint MLE. -/
noncomputable def fittedProperSubmodelScore2577_vec
    {Omega H : Type*} [MeasurableSpace Omega] {d : Nat}
    {P : Measure Omega} [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (modelLaw : EuclideanSpace Real (Fin d) -> H -> Measure Omega)
    (nuisancePath : EuclideanSpace Real (Fin d) -> H ->
      EuclideanSpace Real (Fin d) -> H)
    (estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d))
    (nuisanceEstimator : forall n, (Fin n -> Omega) -> H)
    (n : Nat) (X : Fin n -> Omega) : Omega -> EuclideanSpace Real (Fin d) :=
  properSubmodelScore2577_vec M modelLaw nuisancePath
    (estimator n X) (nuisanceEstimator n X)

/-- The literal extended `L²` norm. Unlike a real Bochner integral outside
`L²`, this value records nonintegrability as `infinity`. -/
noncomputable def extendedL2Norm2577
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    (mu : Measure Omega) (f : Omega -> E) : ENNReal :=
  (∫⁻ omega, ‖f omega‖ₑ ^ (2 : Real) ∂mu) ^ (1 / 2 : Real)

/-- Efficient-score tuple with the projection witness passed explicitly. -/
noncomputable def efficientScoreTuple2577_vec
    {Omega Theta : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    [NormedAddCommGroup Theta] [InnerProductSpace Real Theta] [CompleteSpace Theta]
    {d : Nat} (S_theta : OrdinaryScore P Theta)
    (T_nuis : NuisanceTangentSpace P)
    (proj : T_nuis.HasOrthogonalProjection) (e : Fin d -> Theta) :
    Omega -> EuclideanSpace Real (Fin d) :=
  tupleEval P (fun j => @efficientScore Omega _ P _ Theta _ _ _
    S_theta T_nuis proj (e j))

/-- Efficient-information matrix with the projection witness passed explicitly. -/
noncomputable def efficientInformation2577_vec
    {Omega Theta : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    [NormedAddCommGroup Theta] [InnerProductSpace Real Theta] [CompleteSpace Theta]
    {d : Nat} (S_theta : OrdinaryScore P Theta)
    (T_nuis : NuisanceTangentSpace P)
    (proj : T_nuis.HasOrthogonalProjection) (e : Fin d -> Theta) :
    Matrix (Fin d) (Fin d) Real :=
  @efficientInformationMatrix Omega _ P _ Theta _ _ _ d
    S_theta T_nuis proj e

/-- The common fitted-score localization event. -/
def fittedScoreGood2577_vec
    {Omega H : Type*} [MeasurableSpace Omega] {d : Nat}
    {P : Measure Omega} [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (modelLaw : EuclideanSpace Real (Fin d) -> H -> Measure Omega)
    (nuisancePath : EuclideanSpace Real (Fin d) -> H ->
      EuclideanSpace Real (Fin d) -> H)
    (estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d))
    (nuisanceEstimator : forall n, (Fin n -> Omega) -> H)
    (F : Fin d -> Set (Omega -> Real)) (n : Nat) (X : Fin n -> Omega) : Prop :=
  forall j, (fun omega => fittedProperSubmodelScore2577_vec M modelLaw nuisancePath
    estimator nuisanceEstimator n X omega j) ∈ F j

/-- Zero localization of the fitted score off the common good event. -/
noncomputable def localizedFittedScore2577_vec
    {Omega H : Type*} [MeasurableSpace Omega] {d : Nat}
    {P : Measure Omega} [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (modelLaw : EuclideanSpace Real (Fin d) -> H -> Measure Omega)
    (nuisancePath : EuclideanSpace Real (Fin d) -> H ->
      EuclideanSpace Real (Fin d) -> H)
    (estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d))
    (nuisanceEstimator : forall n, (Fin n -> Omega) -> H)
    (F : Fin d -> Set (Omega -> Real)) (n : Nat) (X : Fin n -> Omega) :
    Omega -> EuclideanSpace Real (Fin d) := fun omega => by
  classical
  exact if fittedScoreGood2577_vec M modelLaw nuisancePath estimator nuisanceEstimator F n X
      then fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator n X omega
      else 0

/-- Vector hypotheses for van der Vaart, Theorem 25.77. The QMD
curve is the fixed-nuisance law `P_{theta0+delta,eta0}`; the proper-submodel
likelihood and score are generated canonically from the model laws. -/
structure ApproxLeastFavorable2577NativeHyp_vec
    {Omega : Type} [MeasurableSpace Omega] {d : Nat}
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Theta : Type*) [NormedAddCommGroup Theta] [InnerProductSpace Real Theta]
    [CompleteSpace Theta]
    (S_theta : OrdinaryScore P Theta) (T_nuis : NuisanceTangentSpace P)
    [proj : T_nuis.HasOrthogonalProjection] (e : Fin d -> Theta)
    (H : Type*)
    (M : QMDModel (Omega := Omega) P d)
    (modelLaw : EuclideanSpace Real (Fin d) -> H -> Measure Omega)
    (nuisancePath : EuclideanSpace Real (Fin d) -> H ->
      EuclideanSpace Real (Fin d) -> H)
    (estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d))
    (nuisanceEstimator : forall n, (Fin n -> Omega) -> H)
    (theta0 : EuclideanSpace Real (Fin d)) (eta0 : H)
    (F : Fin d -> Set (Omega -> Real)) (envelope : Omega -> Real) : Prop where
  modelLaw_isProbability : forall theta eta, IsProbabilityMeasure (modelLaw theta eta)
  modelLaw_absContinuous : forall theta eta, modelLaw theta eta ≪ M.dominating
  fixed_nuisance_model : forall delta,
    M.curve delta = modelLaw (theta0 + delta) eta0
  nuisancePath_zero : forall theta eta, nuisancePath theta eta 0 = eta
  proper_score_hasDeriv : forall theta eta j omega,
    0 < modelDensity2577_vec M modelLaw theta eta omega ->
    HasDerivAt
      (fun t : Real => properSubmodelLogLikelihood2577_vec M modelLaw nuisancePath
        theta eta (t • coordinateDirection2577_vec j) omega)
      (properSubmodelScore2577_vec M modelLaw nuisancePath theta eta omega j) 0
  qmd_score_eq_ordinary : M.score =ᵐ[P]
    tupleEval P (fun j => S_theta (e j))
  truth_proper_score_eq_efficient :
    properSubmodelScore2577_vec M modelLaw nuisancePath theta0 eta0 =ᵐ[P]
      efficientScoreTuple2577_vec S_theta T_nuis proj e
  information_det_isUnit : IsUnit
    (efficientInformation2577_vec S_theta T_nuis proj e).det
  is_donsker : forall j, IsPDonsker (F j) P
  envelope_memLp : MemLp envelope 2 P
  envelope_bound : forall j f, f ∈ F j -> forall omega,
    |f omega| <= envelope omega
  fitted_score_measurable : forall n, Measurable (fun p :
    (Fin n -> Omega) × Omega =>
      fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator n p.1 p.2)
  fitted_score_bad_measurable : forall n, MeasurableSet
    {X : Fin n -> Omega | ¬ fittedScoreGood2577_vec M modelLaw nuisancePath
      estimator nuisanceEstimator F n X}
  fitted_score_mem_wpa : Tendsto (fun n =>
    (Measure.pi (fun _ : Fin n => P))
      {X | ¬ fittedScoreGood2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X}) atTop (nhds 0)
  /-- Square-integrability of the fitted-score representative on the common
  good event under the moving law in (25.76b). -/
  fitted_score_memLp_moving_on_good : forall n X,
    fittedScoreGood2577_vec M modelLaw nuisancePath estimator nuisanceEstimator F n X ->
    MemLp (fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator n X) 2 (modelLaw (estimator n X) eta0)
  /-- Equation (25.76a), as an extended-`L²(P0)` tail statement. -/
  score_l2_truth : forall epsilon : Real, 0 < epsilon -> Tendsto (fun n =>
    (Measure.pi (fun _ : Fin n => P)) {X |
      ENNReal.ofReal epsilon <= extendedL2Norm2577 P (fun omega =>
        fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
            nuisanceEstimator n X omega -
          properSubmodelScore2577_vec M modelLaw nuisancePath theta0 eta0 omega)})
    atTop (nhds 0)
  /-- Equation (25.76b), as uniform extended-`L²(P_{thetaHat,eta0})`
  tightness. Infinite energy remains in every finite tail. -/
  score_energy_moving_tight : forall epsilon : Real, 0 < epsilon ->
    exists R : Real, 0 <= R ∧ forall n,
      (Measure.pi (fun _ : Fin n => P)).real {X |
        ENNReal.ofReal R < extendedL2Norm2577
          (modelLaw (estimator n X) eta0)
          (fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
            nuisanceEstimator n X)} <= epsilon
  estimator_consistency : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => estimator n X - theta0)
  estimator_measurable : forall n, Measurable (estimator n)
  /-- Vector local maximality of the joint MLE and strict positivity of every
  fitted-path sample density throughout the same interior ball. -/
  mle_local_max_interior : forall n X, exists radius : Real, 0 < radius ∧
    forall delta, ‖delta‖ < radius ->
      (forall i : Fin n, 0 < modelDensity2577_vec M modelLaw
        (estimator n X + delta)
        (nuisancePath (estimator n X) (nuisanceEstimator n X) delta) (X i)) ∧
      (∑ i : Fin n, properSubmodelLogLikelihood2577_vec M modelLaw nuisancePath
        (estimator n X) (nuisanceEstimator n X) delta (X i)) <=
      ∑ i : Fin n, properSubmodelLogLikelihood2577_vec M modelLaw nuisancePath
        (estimator n X) (nuisanceEstimator n X) 0 (X i)
  /-- Equation (25.75), with moving law `P_{thetaHat,eta0}`. -/
  moving_bias_2575 : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X =>
      (1 + ‖Real.sqrt n • (estimator n X - theta0)‖)⁻¹ •
        (Real.sqrt n • ∫ omega,
          fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
            nuisanceEstimator n X omega ∂(modelLaw (estimator n X) eta0)))

namespace ApproxLeastFavorable2577NativeHyp_vec

variable {Omega : Type} [MeasurableSpace Omega] {d : Nat}
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {Theta : Type*} [NormedAddCommGroup Theta] [InnerProductSpace Real Theta]
  [CompleteSpace Theta]
variable {S_theta : OrdinaryScore P Theta} {T_nuis : NuisanceTangentSpace P}
  [proj : T_nuis.HasOrthogonalProjection] {e : Fin d -> Theta}
variable {H : Type*}
variable {M : QMDModel (Omega := Omega) P d}
variable {modelLaw : EuclideanSpace Real (Fin d) -> H -> Measure Omega}
variable {nuisancePath : EuclideanSpace Real (Fin d) -> H ->
  EuclideanSpace Real (Fin d) -> H}
variable {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
variable {nuisanceEstimator : forall n, (Fin n -> Omega) -> H}
variable {theta0 : EuclideanSpace Real (Fin d)} {eta0 : H}
variable {F : Fin d -> Set (Omega -> Real)} {envelope : Omega -> Real}

local instance projection2577 : T_nuis.HasOrthogonalProjection := proj

variable (h : ApproxLeastFavorable2577NativeHyp_vec P Theta S_theta T_nuis e H M
  modelLaw nuisancePath estimator nuisanceEstimator theta0 eta0 F envelope)

include h

/-- At zero displacement the proper path returns to its base nuisance value,
so its likelihood is the canonical log density of the base model law. -/
theorem properSubmodelLogLikelihood_zero
    (theta : EuclideanSpace Real (Fin d)) (eta : H) (omega : Omega) :
    properSubmodelLogLikelihood2577_vec M modelLaw nuisancePath theta eta 0 omega =
      Real.log (modelDensity2577_vec M modelLaw theta eta omega) := by
  simp [properSubmodelLogLikelihood2577_vec, h.nuisancePath_zero]

omit [IsProbabilityMeasure P] [NormedAddCommGroup Theta]
    [InnerProductSpace Real Theta] [CompleteSpace Theta] proj h in
/-- The public lintegral spelling agrees with Mathlib's extended seminorm. -/
theorem extendedL2Norm_eq_eLpNorm2577
    {E : Type*} [NormedAddCommGroup E] (mu : Measure Omega) (f : Omega -> E) :
    extendedL2Norm2577 mu f = eLpNorm f 2 mu := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num [extendedL2Norm2577]

omit [IsProbabilityMeasure P] [NormedAddCommGroup Theta]
    [InnerProductSpace Real Theta] [CompleteSpace Theta] proj h in
/-- For an honest `L²` representative, the extended norm agrees with the
real square-root energy used by the first-order QMD engine. -/
theorem sqrt_integral_norm_sq_eq_extendedL2Norm2577
    {E : Type*} [NormedAddCommGroup E] {mu : Measure Omega} {f : Omega -> E}
    (hf : MemLp f 2 mu) :
    Real.sqrt (∫ omega, ‖f omega‖ ^ 2 ∂mu) = (extendedL2Norm2577 mu f).toReal := by
  rw [extendedL2Norm_eq_eLpNorm2577]
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num
  have hnonneg : 0 <= ∫ omega, ‖f omega‖ ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
  norm_num [Real.sqrt_eq_rpow]

/-- Positive definiteness is derived from Gram positive semidefiniteness and
the book-level determinant condition. -/
theorem information_posDef :
    (efficientInformation2577_vec S_theta T_nuis proj e).PosDef := by
  have hpsd : (efficientInformation2577_vec S_theta T_nuis proj e).PosSemidef := by
    simpa [efficientInformation2577_vec] using
      (@efficientInformationMatrix_posSemidef Omega _ P _ Theta _ _ _ d
        S_theta T_nuis proj e)
  exact hpsd.posDef_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr h.information_det_isUnit)

omit h in
/-- The efficient-score tuple is square-integrable under truth. -/
theorem efficientScoreTuple_memLp :
    MemLp (efficientScoreTuple2577_vec S_theta T_nuis proj e) 2 P := by
  rw [efficientScoreTuple2577_vec]
  apply MemLp.of_eval_piLp
  intro j
  exact Lp.memLp _

/-- Approximate least favorability identifies the truth proper score with the
efficient score, hence the truth proper score is square-integrable. -/
theorem truthProperSubmodelScore_memLp :
    MemLp (properSubmodelScore2577_vec M modelLaw nuisancePath theta0 eta0) 2 P :=
  MemLp.ae_eq h.truth_proper_score_eq_efficient.symm
    (efficientScoreTuple_memLp (S_theta := S_theta) (T_nuis := T_nuis)
      (proj := proj) (e := e))

/-- W.p.a.1 membership makes every coordinate class nonempty. -/
theorem class_nonempty (j : Fin d) : (F j).Nonempty := by
  by_contra hempty
  have hbad : forall n,
      {X : Fin n -> Omega | ¬ fittedScoreGood2577_vec M modelLaw nuisancePath
        estimator nuisanceEstimator F n X} = Set.univ := by
    intro n
    apply Set.eq_univ_of_forall
    intro X hgood
    exact hempty ⟨_, hgood j⟩
  have ht := h.fitted_score_mem_wpa
  simp_rw [hbad, measure_univ] at ht
  have hone : Tendsto (fun _ : Nat => (1 : ENNReal)) atTop (nhds 0) := ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hone)

/-- An in-class localization anchor derived from w.p.a.1 membership. -/
noncomputable def classAnchor2577_vec : Omega -> EuclideanSpace Real (Fin d) :=
  fun omega => WithLp.toLp 2 (fun j => Classical.choose (h.class_nonempty j) omega)

theorem classAnchor_mem (j : Fin d) :
    (fun omega => h.classAnchor2577_vec omega j) ∈ F j := by
  simpa [classAnchor2577_vec] using Classical.choose_spec (h.class_nonempty j)

theorem movingLaw_eq_fixedNuisance (n : Nat) (X : Fin n -> Omega) :
    M.curve (estimator n X - theta0) = modelLaw (estimator n X) eta0 := by
  rw [h.fixed_nuisance_model]
  congr 2
  abel

/-- The canonical density represents each supplied model law. -/
theorem modelLaw_eq_withDensity (theta : EuclideanSpace Real (Fin d)) (eta : H) :
    M.dominating.withDensity ((modelLaw theta eta).rnDeriv M.dominating) =
      modelLaw theta eta := by
  letI := h.modelLaw_isProbability theta eta
  exact Measure.withDensity_rnDeriv_eq _ _ (h.modelLaw_absContinuous theta eta)

/-- On the common good event, the class envelope gives `L²(P0)` membership. -/
theorem fittedScore_memLp_truth_on_good (n : Nat) (X : Fin n -> Omega)
    (hgood : fittedScoreGood2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator F n X) :
    MemLp (fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator n X) 2 P := by
  apply MemLp.of_eval_piLp
  intro j
  refine h.envelope_memLp.of_le ?_ (Filter.Eventually.of_forall fun omega => ?_)
  · have hv := (h.fitted_score_measurable n).comp
        (measurable_prodMk_left : Measurable (fun omega : Omega => (X, omega)))
    exact ((PiLp.proj (𝕜 := Real) (p := 2)
      (β := fun _ : Fin d => Real) j).continuous.measurable.comp hv).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact (h.envelope_bound j _ (hgood j) omega).trans (le_abs_self _)

theorem localizedScore_memLp_truth (n : Nat) (X : Fin n -> Omega) :
    MemLp (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator F n X) 2 P := by
  classical
  by_cases hgood : fittedScoreGood2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator F n X
  · rw [show localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X =
        fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator n X by
      funext omega
      simp [localizedFittedScore2577_vec, hgood]]
    exact h.fittedScore_memLp_truth_on_good n X hgood
  · rw [show localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X = 0 by
      funext omega
      simp [localizedFittedScore2577_vec, hgood]]
    exact MemLp.zero

theorem localizedScore_memLp_moving (n : Nat) (X : Fin n -> Omega) :
    MemLp (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator F n X) 2 (M.curve (estimator n X - theta0)) := by
  classical
  rw [h.movingLaw_eq_fixedNuisance]
  by_cases hgood : fittedScoreGood2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator F n X
  · rw [show localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X =
        fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator n X by
      funext omega
      simp [localizedFittedScore2577_vec, hgood]]
    exact h.fitted_score_memLp_moving_on_good n X hgood
  · rw [show localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X = 0 by
      funext omega
      simp [localizedFittedScore2577_vec, hgood]]
    exact MemLp.zero

theorem localizedScore_measurable (n : Nat) : Measurable (fun p :
    (Fin n -> Omega) × Omega =>
      localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n p.1 p.2) := by
  classical
  have hset : MeasurableSet {p : (Fin n -> Omega) × Omega |
      fittedScoreGood2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n p.1} := by
    convert (h.fitted_score_bad_measurable n).compl.preimage measurable_fst using 1
    ext p
    simp
  have hz : Measurable (fun _ : (Fin n -> Omega) × Omega =>
      (0 : EuclideanSpace Real (Fin d))) := measurable_const
  change Measurable (fun p : (Fin n -> Omega) × Omega =>
    if fittedScoreGood2577_vec M modelLaw nuisancePath estimator nuisanceEstimator F n p.1
      then fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator n p.1 p.2
      else 0)
  exact (h.fitted_score_measurable n).ite hset hz

/-- The model-law and probability fields make the canonical RN likelihood
an actual likelihood, not a free objective. -/
theorem modelDensity_lintegral_eq_one
    (theta : EuclideanSpace Real (Fin d)) (eta : H) :
    ∫⁻ omega, ENNReal.ofReal (modelDensity2577_vec M modelLaw theta eta omega)
      ∂M.dominating = 1 := by
  letI := h.modelLaw_isProbability theta eta
  have hfin : ∀ᵐ omega ∂M.dominating,
      (modelLaw theta eta).rnDeriv M.dominating omega ≠ ∞ :=
    Measure.rnDeriv_ne_top _ _
  calc
    _ = ∫⁻ omega, (modelLaw theta eta).rnDeriv M.dominating omega
        ∂M.dominating := by
      apply lintegral_congr_ae
      filter_upwards [hfin] with omega homega
      simp [modelDensity2577_vec, ENNReal.ofReal_toReal homega]
    _ = modelLaw theta eta Set.univ :=
      Measure.lintegral_rnDeriv (h.modelLaw_absContinuous theta eta)
    _ = 1 := measure_univ

/-- Positivity holds throughout the same ball as fitted-path maximality. -/
theorem fittedPathDensity_pos (n : Nat) (X : Fin n -> Omega) :
    exists radius : Real, 0 < radius ∧ forall delta,
      ‖delta‖ < radius -> forall i : Fin n,
        0 < modelDensity2577_vec M modelLaw (estimator n X + delta)
          (nuisancePath (estimator n X) (nuisanceEstimator n X) delta) (X i) := by
  obtain ⟨r, hr, hlocal⟩ := h.mle_local_max_interior n X
  exact ⟨r, hr, fun delta hdelta => (hlocal delta hdelta).1⟩

/-- Vector local maximality and differentiability of the canonical proper
submodel imply exact empirical stationarity. -/
theorem fittedScore_stationary (n : Nat) (X : Fin n -> Omega) :
    ∑ i : Fin n, fittedProperSubmodelScore2577_vec M modelLaw nuisancePath
      estimator nuisanceEstimator n X (X i) = 0 := by
  ext j
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.zero_apply]
  let f : Real -> Real := fun t =>
    ∑ i : Fin n, properSubmodelLogLikelihood2577_vec M modelLaw nuisancePath
      (estimator n X) (nuisanceEstimator n X)
      (t • coordinateDirection2577_vec j) (X i)
  obtain ⟨radius, hradius, hmax⟩ := h.mle_local_max_interior n X
  have hlocal : IsLocalMax f 0 := by
    change ∀ᶠ t in nhds 0, f t <= f 0
    filter_upwards [Metric.ball_mem_nhds (0 : Real) hradius] with t ht
    have ht' : ‖t • coordinateDirection2577_vec j‖ < radius := by
      have hcoord : ‖coordinateDirection2577_vec j‖ = 1 := by
        simp [coordinateDirection2577_vec]
      simpa [norm_smul, Real.norm_eq_abs, hcoord, Metric.mem_ball, Real.dist_eq] using ht
    simpa [f] using (hmax _ ht').2
  have hderiv : HasDerivAt f
      (∑ i : Fin n, fittedProperSubmodelScore2577_vec M modelLaw nuisancePath
        estimator nuisanceEstimator n X (X i) j) 0 := by
    have hs := HasDerivAt.sum (u := Finset.univ)
      (A := fun i t => properSubmodelLogLikelihood2577_vec M modelLaw nuisancePath
        (estimator n X) (nuisanceEstimator n X)
        (t • coordinateDirection2577_vec j) (X i))
      (A' := fun i => fittedProperSubmodelScore2577_vec M modelLaw nuisancePath
        estimator nuisanceEstimator n X (X i) j)
      (fun i _ => by
        have hzero : ‖(0 : EuclideanSpace Real (Fin d))‖ < radius := by
          simpa using hradius
        have hpos := (hmax 0 hzero).1 i
        have hpos_base : 0 < modelDensity2577_vec M modelLaw
            (estimator n X) (nuisanceEstimator n X) (X i) := by
          simpa [h.nuisancePath_zero] using hpos
        exact h.proper_score_hasDeriv
          (estimator n X) (nuisanceEstimator n X) j (X i) hpos_base)
    dsimp only [f]
    convert! hs using 1
    funext t
    simp only [Finset.sum_apply]
  rw [← hderiv.deriv]
  exact hlocal.deriv_eq_zero

/-- Zero localization preserves exact stationarity. -/
theorem localizedScore_stationary (n : Nat) (X : Fin n -> Omega) :
    ∑ i : Fin n, localizedFittedScore2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator F n X (X i) = 0 := by
  classical
  by_cases hgood : fittedScoreGood2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator F n X
  · simpa [localizedFittedScore2577_vec, hgood] using h.fittedScore_stationary n X
  · simp [localizedFittedScore2577_vec, hgood]

theorem localizedScore_equation : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => (Real.sqrt n)⁻¹ •
      ∑ i : Fin n, localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X (X i)) := by
  intro epsilon hepsilon
  simp only [h.localizedScore_stationary, smul_zero, norm_zero,
    not_le.mpr hepsilon, Set.setOf_false, measureReal_empty]
  exact tendsto_const_nhds

/-- The DQM/ordinary-score identity and efficient-score orthogonality yield
the full efficient-information cross moment. -/
theorem crossMoment_eq_information :
    qmdCrossMoment P M (efficientScoreTuple2577_vec S_theta T_nuis proj e) =
      efficientInformation2577_vec S_theta T_nuis proj e := by
  ext j k
  change (∫ omega,
      (((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj (e j) :
        ↥(L2ZeroMean P)) : Lp Real 2 P) : Omega -> Real) omega *
        M.score omega k ∂P) = _
  calc
    _ = ∫ omega,
        (((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj (e j) :
          ↥(L2ZeroMean P)) : Lp Real 2 P) : Omega -> Real) omega *
        (((S_theta (e k) : ↥(L2ZeroMean P)) :
          Lp Real 2 P) : Omega -> Real) omega ∂P := by
      apply integral_congr_ae
      filter_upwards [h.qmd_score_eq_ordinary] with omega homega
      rw [congrArg (fun z => z k) homega]
      simp [tupleEval]
    _ = inner Real
        ((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj (e j) :
          ↥(L2ZeroMean P)) : Lp Real 2 P)
        ((S_theta (e k) : ↥(L2ZeroMean P)) : Lp Real 2 P) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => mul_comm _ _
    _ = inner Real
        ((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj (e j) :
          ↥(L2ZeroMean P)) : Lp Real 2 P)
        ((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj (e k) :
          ↥(L2ZeroMean P)) : Lp Real 2 P) :=
      @efficientScore_inner_ordinary_eq_self Omega _ P _ Theta _ _ _
        S_theta T_nuis proj (e j) (e k)
    _ = efficientInformation2577_vec S_theta T_nuis proj e j k := by
      simp only [efficientInformation2577_vec]
      exact (@efficientInformationMatrix_apply Omega _ P _ Theta _ _ _ d
        S_theta T_nuis proj e j k).symm

private theorem localized_bad_measure_tendsto : Tendsto (fun n =>
    (Measure.pi (fun _ : Fin n => P)).real
      {X | ¬ fittedScoreGood2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X}) atTop (nhds 0) := by
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h.fitted_score_mem_wpa

omit h in
theorem efficientScoreTuple_measurable :
    Measurable (efficientScoreTuple2577_vec S_theta T_nuis proj e) := by
  apply (WithLp.measurable_toLp 2 (Fin d -> Real)).comp
  rw [measurable_pi_iff]
  intro j
  exact (Lp.stronglyMeasurable
    ((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj (e j) :
      ↥(L2ZeroMean P)) : Lp Real 2 P)).measurable

/-- Equation (25.76a) gives real `L²(P0)` convergence for the internal
zero-localized score. -/
theorem localized_score_l2_truth : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => Real.sqrt (∫ omega,
      ‖localizedFittedScore2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X omega -
        efficientScoreTuple2577_vec S_theta T_nuis proj e omega‖ ^ 2 ∂P)) := by
  intro epsilon hepsilon
  have htailR := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (h.score_l2_truth epsilon hepsilon)
  have hsum : Tendsto (fun n =>
      (Measure.pi (fun _ : Fin n => P)).real {X |
        ENNReal.ofReal epsilon <= extendedL2Norm2577 P (fun omega =>
          fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
              nuisanceEstimator n X omega -
            properSubmodelScore2577_vec M modelLaw nuisancePath theta0 eta0 omega)} +
      (Measure.pi (fun _ : Fin n => P)).real {X |
        ¬ fittedScoreGood2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X}) atTop (nhds 0) := by
    simpa using! htailR.add h.localized_bad_measure_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    (Filter.Eventually.of_forall fun n => ?_)
  let Q := Measure.pi (fun _ : Fin n => P)
  calc
    Q.real {X | epsilon <= ‖Real.sqrt (∫ omega,
        ‖localizedFittedScore2577_vec M modelLaw nuisancePath estimator
            nuisanceEstimator F n X omega -
          efficientScoreTuple2577_vec S_theta T_nuis proj e omega‖ ^ 2 ∂P)‖}
        <= Q.real ({X | ENNReal.ofReal epsilon <= extendedL2Norm2577 P (fun omega =>
            fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
                nuisanceEstimator n X omega -
              properSubmodelScore2577_vec M modelLaw nuisancePath theta0 eta0 omega)} ∪
          {X | ¬ fittedScoreGood2577_vec M modelLaw nuisancePath estimator
            nuisanceEstimator F n X}) := measureReal_mono (by
          intro X hX
          by_cases hgood : fittedScoreGood2577_vec M modelLaw nuisancePath estimator
              nuisanceEstimator F n X
          · left
            have hmem : MemLp (fun omega =>
                fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
                    nuisanceEstimator n X omega -
                  properSubmodelScore2577_vec M modelLaw nuisancePath theta0 eta0 omega) 2 P :=
              (h.fittedScore_memLp_truth_on_good n X hgood).sub
                h.truthProperSubmodelScore_memLp
            have henergy : (∫ omega,
                ‖fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
                    nuisanceEstimator n X omega -
                  properSubmodelScore2577_vec M modelLaw nuisancePath theta0 eta0 omega‖ ^ 2 ∂P) =
                ∫ omega,
                ‖fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
                    nuisanceEstimator n X omega -
                  efficientScoreTuple2577_vec S_theta T_nuis proj e omega‖ ^ 2 ∂P := by
              apply integral_congr_ae
              filter_upwards [h.truth_proper_score_eq_efficient] with omega homega
              rw [homega]
            have hsqrt := sqrt_integral_norm_sq_eq_extendedL2Norm2577 hmem
            have hfinite : extendedL2Norm2577 P (fun omega =>
                fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
                    nuisanceEstimator n X omega -
                  properSubmodelScore2577_vec M modelLaw nuisancePath theta0 eta0 omega) ≠ ∞ := by
              rw [extendedL2Norm_eq_eLpNorm2577]
              exact hmem.eLpNorm_lt_top.ne
            have hX' : epsilon <= Real.sqrt (∫ omega,
                ‖fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
                    nuisanceEstimator n X omega -
                  properSubmodelScore2577_vec M modelLaw nuisancePath theta0 eta0
                    omega‖ ^ 2 ∂P) := by
              rw [henergy]
              simpa [localizedFittedScore2577_vec, hgood, Real.norm_eq_abs,
                abs_of_nonneg (Real.sqrt_nonneg _)] using hX
            rw [hsqrt] at hX'
            exact (ENNReal.ofReal_le_iff_le_toReal hfinite).2 hX'
          · exact Or.inr hgood)
    _ <= Q.real {X | ENNReal.ofReal epsilon <= extendedL2Norm2577 P (fun omega =>
          fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
              nuisanceEstimator n X omega -
            properSubmodelScore2577_vec M modelLaw nuisancePath theta0 eta0 omega)} +
        Q.real {X | ¬ fittedScoreGood2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X} := measureReal_union_le _ _

theorem localized_score_l2_truth_measurable (n : Nat) : Measurable (fun X =>
    Real.sqrt (∫ omega,
      ‖localizedFittedScore2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X omega -
        efficientScoreTuple2577_vec S_theta T_nuis proj e omega‖ ^ 2 ∂P)) := by
  exact (((h.localizedScore_measurable n).sub
      ((efficientScoreTuple_measurable (S_theta := S_theta) (T_nuis := T_nuis)
        (proj := proj) (e := e)).comp measurable_snd)).norm.pow_const 2
    |>.stronglyMeasurable.integral_prod_right').measurable.sqrt

/-- Equation (25.76b) gives real moving-law tightness for the internal
zero-localized score. -/
theorem localized_score_energy_moving_tight : IsBoundedInProb
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => Real.sqrt (∫ omega,
      ‖localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X omega‖ ^ 2
      ∂(M.curve (estimator n X - theta0)))) := by
  intro epsilon hepsilon
  obtain ⟨R, hR, hbound⟩ := h.score_energy_moving_tight epsilon hepsilon
  refine ⟨R, fun n => (measureReal_mono ?_).trans (hbound n)⟩
  intro X hX
  change R < ‖Real.sqrt (∫ omega,
      ‖localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X omega‖ ^ 2
      ∂(M.curve (estimator n X - theta0)))‖ at hX
  by_cases hgood : fittedScoreGood2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator F n X
  · have hmem := h.localizedScore_memLp_moving n X
    have hsqrt := sqrt_integral_norm_sq_eq_extendedL2Norm2577 hmem
    have hfinite : extendedL2Norm2577 (M.curve (estimator n X - theta0))
        (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X) ≠ ∞ := by
      rw [extendedL2Norm_eq_eLpNorm2577]
      exact hmem.eLpNorm_lt_top.ne
    have hX' : R < (extendedL2Norm2577 (M.curve (estimator n X - theta0))
        (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X)).toReal := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hsqrt] at hX
      exact hX
    have hENN := (ENNReal.ofReal_lt_iff_lt_toReal hR hfinite).2 hX'
    have hloc : localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X =
        fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator n X := by
      funext omega
      simp [localizedFittedScore2577_vec, hgood]
    rw [h.movingLaw_eq_fixedNuisance n X, hloc] at hENN
    exact hENN
  · have hzero : localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X = 0 := by
      funext omega
      simp [localizedFittedScore2577_vec, hgood]
    rw [hzero] at hX
    have hXzero : R < 0 := by simpa using hX
    exact False.elim ((not_lt_of_ge hR) hXzero)

omit [MeasurableSpace Omega] [IsProbabilityMeasure P]
    [NormedAddCommGroup Theta] [InnerProductSpace Real Theta]
    [CompleteSpace Theta] proj h in
private theorem tendstoInProbZero_mono2577
    {G K : Type*} [NormedAddCommGroup G] [NormedAddCommGroup K]
    {Omega' : Nat -> Type*} [forall n, MeasurableSpace (Omega' n)]
    {Q : forall n, Measure (Omega' n)} [forall n, IsProbabilityMeasure (Q n)]
    {Z : forall n, Omega' n -> G} {W : forall n, Omega' n -> K}
    (hle : forall n omega, ‖Z n omega‖ <= ‖W n omega‖)
    (hW : TendstoInProbZero Q W) : TendstoInProbZero Q Z := by
  intro epsilon hepsilon
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hW epsilon hepsilon) (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    (Filter.Eventually.of_forall fun n =>
      measureReal_mono fun _ homega => homega.trans (hle _ _))

/-- Coordinate `L²(P0)` convergence for the localized score. -/
theorem localized_score_l2_coord (j : Fin d) : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => Real.sqrt (∫ omega,
      (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X omega j -
        efficientScoreTuple2577_vec S_theta T_nuis proj e omega j) ^ 2 ∂P)) := by
  refine tendstoInProbZero_mono2577 (fun n X => ?_) h.localized_score_l2_truth
  let diff : Omega -> EuclideanSpace Real (Fin d) := fun omega =>
    localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X omega -
      efficientScoreTuple2577_vec S_theta T_nuis proj e omega
  have hdiff : MemLp diff 2 P :=
    (h.localizedScore_memLp_truth n X).sub
      (efficientScoreTuple_memLp (S_theta := S_theta) (T_nuis := T_nuis)
        (proj := proj) (e := e))
  have hcoord : MemLp (fun omega => diff omega j) 2 P := hdiff.eval_piLp j
  have hiCoord : Integrable (fun omega => (diff omega j) ^ 2) P := by
    simpa [Real.norm_eq_abs, sq_abs] using hcoord.integrable_norm_pow (by norm_num)
  have hiVec : Integrable (fun omega => ‖diff omega‖ ^ 2) P :=
    hdiff.integrable_norm_pow (by norm_num)
  have hInt : (∫ omega, (diff omega j) ^ 2 ∂P) <=
      ∫ omega, ‖diff omega‖ ^ 2 ∂P := by
    apply integral_mono_ae hiCoord hiVec
    exact Filter.Eventually.of_forall fun omega => by
      have hc := PiLp.norm_apply_le (diff omega) j
      rw [Real.norm_eq_abs] at hc
      simpa [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (diff omega j)) (norm_nonneg (diff omega))).2 hc
  have hsqrt := Real.sqrt_le_sqrt hInt
  simpa only [diff, PiLp.sub_apply, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt

/-- Scalar tail form of localized equation (25.76a). -/
theorem localized_score_l2_coord_tail (j : Fin d) (delta : Real)
    (hdelta : 0 < delta) : Tendsto (fun n =>
      (Measure.pi (fun _ : Fin n => P)) {X | delta ^ 2 <= ∫ omega,
        (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
            nuisanceEstimator F n X omega j -
          efficientScoreTuple2577_vec S_theta T_nuis proj e omega j) ^ 2 ∂P})
      atTop (nhds 0) := by
  rw [← ENNReal.tendsto_toReal_zero_iff
    (fun n => measure_ne_top (Measure.pi (fun _ : Fin n => P)) _)]
  apply (h.localized_score_l2_coord j delta hdelta).congr'
  filter_upwards [] with n
  rw [measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [] with X
  let A : Real := ∫ omega,
    (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X omega j -
      efficientScoreTuple2577_vec S_theta T_nuis proj e omega j) ^ 2 ∂P
  have hA : 0 <= A := integral_nonneg fun _ => sq_nonneg _
  have hsqrt : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
  change (delta <= ‖Real.sqrt A‖) = (delta ^ 2 <= A)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply propext
  constructor <;> intro hx
  · nlinarith
  · nlinarith [Real.sqrt_nonneg A]

theorem localized_coord_bad_measurable (n : Nat) (j : Fin d) : MeasurableSet
    {X : Fin n -> Omega |
      (fun omega => localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X omega j) ∉ F j} := by
  classical
  by_cases hz : (0 : Omega -> Real) ∈ F j
  · have hempty : {X : Fin n -> Omega |
        (fun omega => localizedFittedScore2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X omega j) ∉ F j} = ∅ := by
      ext X
      by_cases hgood : fittedScoreGood2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X
      · simp [localizedFittedScore2577_vec, hgood, hgood j]
      · have hzero : (fun omega => localizedFittedScore2577_vec M modelLaw nuisancePath
            estimator nuisanceEstimator F n X omega j) = 0 := by
          funext omega
          simp [localizedFittedScore2577_vec, hgood]
        change ((fun omega => localizedFittedScore2577_vec M modelLaw nuisancePath
          estimator nuisanceEstimator F n X omega j) ∉ F j) ↔ False
        rw [hzero]
        simp [hz]
    rw [hempty]
    exact MeasurableSet.empty
  · have heq : {X : Fin n -> Omega |
        (fun omega => localizedFittedScore2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X omega j) ∉ F j} =
        {X | ¬ fittedScoreGood2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X} := by
      ext X
      by_cases hgood : fittedScoreGood2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X
      · simp [localizedFittedScore2577_vec, hgood, hgood j]
      · have hzero : (fun omega => localizedFittedScore2577_vec M modelLaw nuisancePath
            estimator nuisanceEstimator F n X omega j) = 0 := by
          funext omega
          simp [localizedFittedScore2577_vec, hgood]
        change ((fun omega => localizedFittedScore2577_vec M modelLaw nuisancePath
          estimator nuisanceEstimator F n X omega j) ∉ F j) ↔
          ¬ fittedScoreGood2577_vec M modelLaw nuisancePath estimator
            nuisanceEstimator F n X
        rw [hzero]
        simp [hz, hgood]
    rw [heq]
    exact h.fitted_score_bad_measurable n

theorem localized_coord_mem_wpa (j : Fin d) : Tendsto (fun n =>
    (Measure.pi (fun _ : Fin n => P)) {X |
      (fun omega => localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F n X omega j) ∉ F j}) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    h.fitted_score_mem_wpa (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun n => measure_mono ?_)
  intro X hX hgood
  apply hX
  have heq : (fun omega => localizedFittedScore2577_vec M modelLaw nuisancePath
      estimator nuisanceEstimator F n X omega j) =
      fun omega => fittedProperSubmodelScore2577_vec M modelLaw nuisancePath
        estimator nuisanceEstimator n X omega j := by
    funext omega
    simp [localizedFittedScore2577_vec, hgood]
  rw [heq]
  exact hgood j

/-- The book hypotheses instantiate w.p.a.1 random-index replacement for the
internal localized score. -/
theorem empiricalReplacementHyp : RandomIndexScoreReplacementWPAHyp_vec P d
    (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator F)
    (efficientScoreTuple2577_vec S_theta T_nuis proj e)
    h.classAnchor2577_vec F := by
  refine ⟨fun j => ?_, h.localizedScore_memLp_truth,
    efficientScoreTuple_memLp (S_theta := S_theta) (T_nuis := T_nuis)
      (proj := proj) (e := e)⟩
  refine ⟨?_, ((efficientScoreTuple_memLp (S_theta := S_theta)
    (T_nuis := T_nuis) (proj := proj) (e := e)).eval_piLp j), h.is_donsker j,
    ?_, (fun n => h.localized_coord_bad_measurable n j), h.localized_coord_mem_wpa j,
    h.classAnchor_mem j, h.localized_score_l2_coord_tail j⟩
  · exact (PiLp.proj (𝕜 := Real) (p := 2)
      (β := fun _ : Fin d => Real) j).continuous.measurable.comp
        (efficientScoreTuple_measurable (S_theta := S_theta) (T_nuis := T_nuis)
          (proj := proj) (e := e))
  · intro n
    exact (PiLp.proj (𝕜 := Real) (p := 2)
      (β := fun _ : Fin d => Real) j).continuous.measurable.comp
        (h.localizedScore_measurable n)

theorem firstOrderTransportHyp : FirstOrder2576ScoreTransportHypVec P M
    estimator theta0
    (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
      nuisanceEstimator F)
    (efficientScoreTuple2577_vec S_theta T_nuis proj e) := by
  exact ⟨h.localizedScore_measurable, h.localizedScore_memLp_truth,
    h.localizedScore_memLp_moving,
    efficientScoreTuple_memLp (S_theta := S_theta) (T_nuis := T_nuis)
      (proj := proj) (e := e),
    h.localized_score_l2_truth, h.localized_score_l2_truth_measurable,
    h.localized_score_energy_moving_tight, h.estimator_consistency⟩

private theorem moving_bias_localization_transfer : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X =>
      (1 + ‖Real.sqrt n • (estimator n X - theta0)‖)⁻¹ •
        rawMovingBias_vec M estimator theta0
          (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
            nuisanceEstimator F) n X) := by
  intro epsilon hepsilon
  have hsum : Tendsto (fun n =>
      (Measure.pi (fun _ : Fin n => P)).real {X | epsilon <= ‖
        (1 + ‖Real.sqrt n • (estimator n X - theta0)‖)⁻¹ •
          (Real.sqrt n • ∫ omega,
            fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
              nuisanceEstimator n X omega ∂(modelLaw (estimator n X) eta0))‖} +
      (Measure.pi (fun _ : Fin n => P)).real {X |
        ¬ fittedScoreGood2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X}) atTop (nhds 0) := by
    simpa using (h.moving_bias_2575 epsilon hepsilon).add
      h.localized_bad_measure_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    (Filter.Eventually.of_forall fun n => ?_)
  let Q := Measure.pi (fun _ : Fin n => P)
  calc
    Q.real {X | epsilon <= ‖
        (1 + ‖Real.sqrt n • (estimator n X - theta0)‖)⁻¹ •
          rawMovingBias_vec M estimator theta0
            (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
              nuisanceEstimator F) n X‖}
      <= Q.real ({X | epsilon <= ‖
          (1 + ‖Real.sqrt n • (estimator n X - theta0)‖)⁻¹ •
            (Real.sqrt n • ∫ omega,
              fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
                nuisanceEstimator n X omega ∂(modelLaw (estimator n X) eta0))‖} ∪
        {X | ¬ fittedScoreGood2577_vec M modelLaw nuisancePath estimator
          nuisanceEstimator F n X}) := measureReal_mono (by
            intro X hX
            by_cases hgood : fittedScoreGood2577_vec M modelLaw nuisancePath estimator
                nuisanceEstimator F n X
            · left
              have hloc : localizedFittedScore2577_vec M modelLaw nuisancePath estimator
                  nuisanceEstimator F n X =
                  fittedProperSubmodelScore2577_vec M modelLaw nuisancePath estimator
                    nuisanceEstimator n X := by
                funext omega
                simp [localizedFittedScore2577_vec, hgood]
              simpa [rawMovingBias_vec, h.movingLaw_eq_fixedNuisance n X, hloc] using hX
            · exact Or.inr hgood)
    _ <= _ := measureReal_union_le _ _

/-- Native moving-bias identity derived from the hypotheses of the theorem. -/
theorem normalized_master_identity : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X =>
      let Delta := Real.sqrt n • (estimator n X - theta0)
      (1 + ‖Delta‖)⁻¹ •
        (Delta
          - Matrix.toEuclideanCLM (𝕜 := Real)
              (efficientInformation2577_vec S_theta T_nuis proj e)⁻¹
              ((Real.sqrt n)⁻¹ • ∑ i : Fin n,
                efficientScoreTuple2577_vec S_theta T_nuis proj e (X i))
          - Matrix.toEuclideanCLM (𝕜 := Real)
              (efficientInformation2577_vec S_theta T_nuis proj e)⁻¹
              (rawMovingBias_vec M estimator theta0
                (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
                  nuisanceEstimator F) n X))) := by
  let score0 : Fin d -> ↥(L2ZeroMean P) := fun j =>
    @efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj (e j)
  apply normalizedMovingBias_expansion_vec (score0 := score0)
    h.localizedScore_equation
    (fun n X => (h.localizedScore_memLp_truth n X).integrable (by norm_num))
    (efficientScoreTuple_memLp (S_theta := S_theta) (T_nuis := T_nuis)
      (proj := proj) (e := e))
    (fun j => (efficientScoreTuple_memLp (S_theta := S_theta)
      (T_nuis := T_nuis) (proj := proj) (e := e)).eval_piLp j)
  · simpa [score0, efficientScoreTuple2577_vec] using
      randomIndex_empiricalScoreReplacement_oP_wpa_vec h.empiricalReplacementHyp
  · simpa [score0, efficientScoreTuple2577_vec] using
      qmdModel_modelShift_normalized_oP_of_2576 h.firstOrderTransportHyp
  · simpa [score0, efficientScoreTuple2577_vec] using h.crossMoment_eq_information
  · exact h.information_posDef

/-- Native vector asymptotic linearity in van der Vaart, Theorem 25.77. -/
theorem asympLinear_2577 : AsymptoticallyLinearAt_vec estimator P
    (@candidateVecEIF Omega _ P _ Theta _ _ _ d S_theta T_nuis proj e) theta0 := by
  let score0 : Fin d -> ↥(L2ZeroMean P) := fun j =>
    @efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj (e j)
  have hAL := asympLinear_of_normalizedExpansion_2554_vec
    (score0 := score0) (I := efficientInformation2577_vec S_theta T_nuis proj e)
    (B := rawMovingBias_vec M estimator theta0
      (localizedFittedScore2577_vec M modelLaw nuisancePath estimator
        nuisanceEstimator F))
    (fun j => (efficientScoreTuple_memLp (S_theta := S_theta)
      (T_nuis := T_nuis) (proj := proj) (e := e)).eval_piLp j)
    h.estimator_measurable h.normalized_master_identity h.moving_bias_localization_transfer
  simpa [score0, candidateVecEIF, efficientInformation2577_vec] using! hAL

end ApproxLeastFavorable2577NativeHyp_vec

variable {Omega : Type} [MeasurableSpace Omega]
variable {d : Nat}
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {Theta : Type*} [NormedAddCommGroup Theta] [InnerProductSpace Real Theta]
  [CompleteSpace Theta]
variable {S_theta : OrdinaryScore P Theta} {T_nuis : NuisanceTangentSpace P}
variable [proj : T_nuis.HasOrthogonalProjection] {e : Fin d -> Theta}
variable {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
variable {theta0 : EuclideanSpace Real (Fin d)}
variable {H : Type*}
variable {M : QMDModel (Omega := Omega) P d}
variable {modelLaw : EuclideanSpace Real (Fin d) -> H -> Measure Omega}
variable {nuisancePath : EuclideanSpace Real (Fin d) -> H ->
  EuclideanSpace Real (Fin d) -> H}
variable {nuisanceEstimator : forall n, (Fin n -> Omega) -> H}
variable {eta0 : H}
variable {F : Fin d -> Set (Omega -> Real)} {envelope : Omega -> Real}

local instance headlineProjection2577 : T_nuis.HasOrthogonalProjection := proj

/-- van der Vaart, Theorem 25.77: native vector asymptotic linearity from an
approximately least-favorable proper nuisance submodel. -/
theorem mle_asympLinear_2577_native_vec
    (h : ApproxLeastFavorable2577NativeHyp_vec P Theta S_theta T_nuis e H M
      modelLaw nuisancePath estimator nuisanceEstimator theta0 eta0 F envelope) :
    AsymptoticallyLinearAt_vec estimator P
      (@candidateVecEIF Omega _ P _ Theta _ _ _ d S_theta T_nuis proj e) theta0 :=
  h.asympLinear_2577

/-- van der Vaart, Theorem 25.77: native vector semiparametric efficiency. -/
theorem mle_semiparametricallyEfficient_2577_native_vec
    -- USER-INPUT: the approximate least-favorable submodel hypotheses;
    -- vdV Theorem 25.77.
    (h : ApproxLeastFavorable2577NativeHyp_vec P Theta S_theta T_nuis e H M
      modelLaw nuisancePath estimator nuisanceEstimator theta0 eta0 F envelope)
    {T : Submodule Real ↥(L2ZeroMean P)}
    {Dpsi : T →L[Real] EuclideanSpace Real (Fin d)}
    -- USER-INPUT: the candidate coordinates lie in the tangent space and
    -- represent the pathwise derivative; vdV Theorem 25.77.
    (h_mem : forall j,
      @candidateVecEIF Omega _ P _ Theta _ _ _ d S_theta T_nuis proj e j ∈ T)
    (h_Dpsi : forall (j : Fin d) (g : T),
      ((EuclideanSpace.proj j) ∘L Dpsi) g = inner Real
        (@candidateVecEIF Omega _ P _ Theta _ _ _ d S_theta T_nuis proj e j)
        (g : ↥(L2ZeroMean P)))
    -- USER-INPUT: the target functional is centered at `theta0`.
    {psi : Measure Omega -> EuclideanSpace Real (Fin d)} (hpsi : psi P = theta0) :
    SemiparametricallyEfficientAt_vec estimator psi P T := by
  have hPD : (@efficientInformationMatrix Omega _ P _ Theta _ _ _ d
      S_theta T_nuis proj e).PosDef := by
    simpa [efficientInformation2577_vec] using h.information_posDef
  have hEIF : IsEfficientInfluenceFunction_vec Dpsi
      (@candidateVecEIF Omega _ P _ Theta _ _ _ d S_theta T_nuis proj e) :=
    @eif_from_efficientScore_vec Omega _ P _ Theta _ _ _ d S_theta T_nuis proj e
      T Dpsi hPD h_mem h_Dpsi
  have hAL : AsymptoticallyLinearAt_vec estimator P
      (@candidateVecEIF Omega _ P _ Theta _ _ _ d S_theta T_nuis proj e) (psi P) := by
    rw [hpsi]
    exact h.asympLinear_2577
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif_vec hEIF hAL

/-! ## Finite-dimensional non-diagonal checks -/

/-- A positive-definite non-diagonal information matrix. -/
def nonDiagonalInformation2577 : Matrix (Fin 2) (Fin 2) Real :=
  fun i j => if i = j then 2 else 1

/-- A score vector concentrated in the first coordinate. -/
def nonDiagonalScore2577 : Fin 2 -> Real := fun j => if j = 0 then 1 else 0

private noncomputable def nonDiagonalInformationInverse2577 : Matrix (Fin 2) (Fin 2) Real :=
  fun i j => if i = j then (2 / 3 : Real) else (-1 / 3 : Real)

/-- Full inversion of a non-diagonal information matrix mixes coordinates. -/
theorem nonDiagonalInformation2577_inverse_mix :
    Matrix.mulVec nonDiagonalInformation2577⁻¹ nonDiagonalScore2577 =
      fun j => if j = 0 then (2 / 3 : Real) else (-1 / 3 : Real) := by
  have hleft : nonDiagonalInformationInverse2577 * nonDiagonalInformation2577 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [nonDiagonalInformationInverse2577, nonDiagonalInformation2577,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.inv_eq_left_inv hleft]
  funext j
  fin_cases j <;>
    norm_num [nonDiagonalInformationInverse2577, nonDiagonalScore2577,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Reciprocal-diagonal scaling fails for the same information matrix. -/
theorem nonDiagonalInformation2577_diagonal_scaling_fails :
    Matrix.mulVec nonDiagonalInformation2577⁻¹ nonDiagonalScore2577 ≠
      fun j => (nonDiagonalInformation2577 j j)⁻¹ * nonDiagonalScore2577 j := by
  intro heq
  have hcoord := congrFun heq (1 : Fin 2)
  rw [nonDiagonalInformation2577_inverse_mix] at hcoord
  norm_num [nonDiagonalInformation2577, nonDiagonalScore2577] at hcoord

/-- Algebraic nuisance direction used in the explicit moment witness. -/
def nonDiagonalNuisanceDirection2577 : Fin 3 -> Real :=
  ![0, 0, 1]

/-- Ordinary score coefficient vectors `b1=(1,0,1)` and `b2=(1,1,1)`. -/
def nonDiagonalOrdinaryCoefficients2577 : Fin 2 -> Fin 3 -> Real :=
  ![![1, 0, 1], ![1, 1, 1]]

/-- Efficient score coefficient vectors `(1,0,0)` and `(1,1,0)`. -/
def nonDiagonalEfficientCoefficients2577 : Fin 2 -> Fin 3 -> Real :=
  ![![1, 0, 0], ![1, 1, 0]]

/-- Covariance/moment pairing for independent unit-variance coordinates. -/
def standardMoment2577 (u v : Fin 3 -> Real) : Real :=
  ∑ k : Fin 3, u k * v k

/-- Removing the nuisance direction `a=(0,0,1)` from each ordinary score
gives the displayed efficient scores. -/
theorem nonDiagonal2577_ordinary_sub_nuisance_eq_efficient :
    (fun j k => nonDiagonalOrdinaryCoefficients2577 j k -
      nonDiagonalNuisanceDirection2577 k) =
      nonDiagonalEfficientCoefficients2577 := by
  funext j k
  fin_cases j <;> fin_cases k <;>
    norm_num [nonDiagonalOrdinaryCoefficients2577,
      nonDiagonalNuisanceDirection2577, nonDiagonalEfficientCoefficients2577]

/-- The ordinary and efficient scores in the witness are genuinely distinct. -/
theorem nonDiagonal2577_ordinary_ne_efficient :
    nonDiagonalOrdinaryCoefficients2577 ≠ nonDiagonalEfficientCoefficients2577 := by
  intro heq
  have hcoord := congrFun (congrFun heq (0 : Fin 2)) (2 : Fin 3)
  change (1 : Real) = 0 at hcoord
  norm_num at hcoord

/-- Efficient-by-ordinary cross moments equal the non-diagonal efficient
Gram matrix `[[1,1],[1,2]]`. -/
theorem nonDiagonal2577_cross_identity :
    (fun i j => standardMoment2577 (nonDiagonalEfficientCoefficients2577 i)
      (nonDiagonalOrdinaryCoefficients2577 j)) =
      fun i j => if i = 0 then 1 else if j = 0 then 1 else 2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [standardMoment2577, nonDiagonalEfficientCoefficients2577,
      nonDiagonalOrdinaryCoefficients2577, nonDiagonalNuisanceDirection2577,
      Fin.sum_univ_succ]

/-- The efficient Gram moments give the same non-diagonal matrix. -/
theorem nonDiagonal2577_efficient_gram :
    (fun i j => standardMoment2577 (nonDiagonalEfficientCoefficients2577 i)
      (nonDiagonalEfficientCoefficients2577 j)) =
      fun i j => if i = 0 then 1 else if j = 0 then 1 else 2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [standardMoment2577, nonDiagonalEfficientCoefficients2577,
      nonDiagonalOrdinaryCoefficients2577, nonDiagonalNuisanceDirection2577,
      Fin.sum_univ_succ]

/-- Algebraic nuisance path shift `eta-delta1-delta2`. -/
def nonDiagonalNuisancePath2577 (eta : Real) (delta : Fin 2 -> Real) : Real :=
  eta - delta 0 - delta 1

theorem nonDiagonalNuisancePath2577_zero (eta : Real) :
    nonDiagonalNuisancePath2577 eta 0 = eta := by
  simp [nonDiagonalNuisancePath2577]

noncomputable def nonDiagonalCrossInformation2577 : Matrix (Fin 2) (Fin 2) Real :=
  fun i j => if i = 0 then 1 else if j = 0 then 1 else 2

private noncomputable def nonDiagonalCrossInformationInverse2577 :
    Matrix (Fin 2) (Fin 2) Real := fun i j =>
  if i = 0 then (if j = 0 then 2 else -1) else (if j = 0 then -1 else 1)

/-- Full inversion for the explicit ordinary/efficient moment witness mixes
the two coordinates. -/
theorem nonDiagonal2577_cross_inverse_mix :
    Matrix.mulVec nonDiagonalCrossInformation2577⁻¹ nonDiagonalScore2577 =
      fun j => if j = 0 then (2 : Real) else -1 := by
  have hleft : nonDiagonalCrossInformationInverse2577 *
      nonDiagonalCrossInformation2577 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [nonDiagonalCrossInformationInverse2577,
        nonDiagonalCrossInformation2577, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.inv_eq_left_inv hleft]
  funext j
  fin_cases j <;>
    norm_num [nonDiagonalCrossInformationInverse2577,
      nonDiagonalScore2577, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end AsymptoticStatistics.Asymptotics.Discharge.LeastFavorableVec
