module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterFiniteProduct

@[expose] public section

/-!
# Uniqueness of tight measures from finite coordinate laws

A structural determining-class result for probability measures on a normed
space.  A separating family of continuous linear coordinates determines a
tight Borel probability measure once all finite coordinate-vector laws agree.
-/

namespace AsymptoticStatistics

open MeasureTheory
open scoped ENNReal

/-- Package finitely many continuous linear coordinates as a Euclidean-valued
continuous linear map.

Edge behavior: for `m = 0` this is the unique map to the zero-dimensional
Euclidean space. -/
noncomputable def finiteCoordinateCLM
    {D ι : Type*} [SeminormedAddCommGroup D] [NormedSpace ℝ D]
    {m : ℕ} (eval : ι → D →L[ℝ] ℝ) (a : Fin m → ι) :
    D →L[ℝ] EuclideanSpace ℝ (Fin m) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun r ↦ eval (a r))

/-- Tight Borel probability measures on a normed space are equal when every
finite vector from a point-separating family of continuous linear coordinates
has the same pushforward law.

The tightness hypotheses are essential in the possibly nonseparable carrier;
finite-dimensional marginal equality alone is not silently promoted to
path-space equality. -/
theorem tightMeasure_eq_of_finiteCoordinate_laws
    {D ι : Type*} [SeminormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasurableSpace D] [BorelSpace D]
    (eval : ι → D →L[ℝ] ℝ)
    (hsep : ∀ x y : D, (∀ i, eval i x = eval i y) → x = y)
    {ν κ : Measure D}
    -- explicit evidence avoids installing local typeclass instances.
    (hνprob : IsProbabilityMeasure ν)
    -- explicit evidence avoids installing local typeclass instances.
    (hκprob : IsProbabilityMeasure κ)
    (hνtight : IsTightMeasureSet ({ν} : Set (Measure D)))
    (hκtight : IsTightMeasureSet ({κ} : Set (Measure D)))
    (hlaw : ∀ (m : ℕ) (a : Fin m → ι),
      ν.map (finiteCoordinateCLM eval a) =
        κ.map (finiteCoordinateCLM eval a)) :
    ν = κ := by
  classical
  let coord : D → (ι → ℝ) := fun x i ↦ eval i x
  have hcoord_cont : Continuous coord := continuous_pi fun i ↦ (eval i).continuous
  have hcoord_inj : Function.Injective coord := by
    intro x y hxy
    exact hsep x y fun i ↦ congrFun hxy i
  letI : T2Space D := T2Space.of_injective_continuous hcoord_inj hcoord_cont
  let E0 := EuclideanSpace ℝ (Fin 0)
  let embed0 : D →L[ℝ] D × E0 := ContinuousLinearMap.inl ℝ D E0
  let fst0 : (D × E0) →L[ℝ] D := ContinuousLinearMap.fst ℝ D E0
  let ν0 : Measure (D × E0) := ν.map embed0
  let κ0 : Measure (D × E0) := κ.map embed0
  letI : IsProbabilityMeasure ν := hνprob
  letI : IsProbabilityMeasure κ := hκprob
  letI : IsProbabilityMeasure ν0 :=
    Measure.isProbabilityMeasure_map embed0.continuous.aemeasurable
  letI : IsProbabilityMeasure κ0 :=
    Measure.isProbabilityMeasure_map embed0.continuous.aemeasurable
  have hν0tight : IsTightMeasureSet ({ν0} : Set (Measure (D × E0))) := by
    simpa only [ν0, Set.image_singleton] using hνtight.map embed0.continuous
  have hκ0tight : IsTightMeasureSet ({κ0} : Set (Measure (D × E0))) := by
    simpa only [κ0, Set.image_singleton] using hκtight.map embed0.continuous
  have hself : WeakConvergesOuter (fun _ : ℕ ↦ ν) (fun _ x ↦ embed0 x) ν0 := by
    apply (weakConvergesOuter_of_measurable (fun _ ↦ embed0.continuous.measurable)).2
    intro f
    simpa only [ν0] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ ∫ y, f y ∂ν0)
        Filter.atTop (nhds (∫ y, f y ∂ν0)))
  have htight : IsAsymptoticallyTight (fun _ : ℕ ↦ ν) (fun _ x ↦ embed0 x) :=
    isAsymptoticallyTight_of_weakConvergesOuter hself hν0tight
  have hmixed : ∀ (m : ℕ) (a : Fin m → Sum ι (Fin 0)),
      WeakConvergesOuter (fun _ : ℕ ↦ ν)
        (fun _ x ↦ mixedEvalCLM eval a (embed0 x))
        (κ0.map (mixedEvalCLM eval a)) := by
    intro m a
    let aD : Fin m → ι := fun r ↦ match a r with
      | Sum.inl i => i
      | Sum.inr j => Fin.elim0 j
    let T : (D × E0) →L[ℝ] EuclideanSpace ℝ (Fin m) := mixedEvalCLM eval a
    have hcomp : ∀ x, T (embed0 x) = finiteCoordinateCLM eval aD x := by
      intro x
      apply PiLp.ext
      intro r
      rcases har : a r with i | j
      · simp [T, embed0, aD, mixedEvalCLM, finiteCoordinateCLM, har]
      · exact Fin.elim0 j
    have hmixlaw : ν.map (fun x ↦ T (embed0 x)) = κ0.map T := by
      calc
        ν.map (fun x ↦ T (embed0 x)) = ν.map (finiteCoordinateCLM eval aD) := by
          congr 1
          funext x
          exact hcomp x
        _ = κ.map (finiteCoordinateCLM eval aD) := hlaw m aD
        _ = κ.map (fun x ↦ T (embed0 x)) := by
          congr 1
          funext x
          exact (hcomp x).symm
        _ = κ0.map T := by
          change κ.map (fun x ↦ T (embed0 x)) = (κ.map embed0).map T
          rw [Measure.map_map T.continuous.measurable embed0.continuous.measurable]
          rfl
    apply (weakConvergesOuter_of_measurable
      (fun _ ↦ T.continuous.measurable.comp embed0.continuous.measurable)).2
    change WeakConverges (fun _ : ℕ ↦ ν.map (fun x ↦ T (embed0 x))) (κ0.map T)
    rw [hmixlaw]
    exact fun _ ↦ tendsto_const_nhds
  have hprod : WeakConvergesOuter (fun _ : ℕ ↦ ν) (fun _ x ↦ embed0 x) κ0 :=
    weakConvergesOuter_prod_of_tight_mixedEval eval hsep htight hκ0tight hmixed
  have hpweak : WeakConverges (fun _ : ℕ ↦ ν0) κ0 := by
    have h := (weakConvergesOuter_of_measurable
      (fun _ ↦ embed0.continuous.measurable)).1 hprod
    simpa only [ν0] using h
  have hselfweak : WeakConverges (fun _ : ℕ ↦ ν0) ν0 :=
    fun _ ↦ tendsto_const_nhds
  have hpush : ν0 = κ0 := hselfweak.unique hpweak
  have hmaps := congrArg (fun p : Measure (D × E0) ↦ p.map fst0) hpush
  change (ν.map embed0).map fst0 = (κ.map embed0).map fst0 at hmaps
  rw [Measure.map_map fst0.continuous.measurable embed0.continuous.measurable,
    Measure.map_map fst0.continuous.measurable embed0.continuous.measurable] at hmaps
  simpa [embed0, fst0, Function.comp_def] using hmaps

end AsymptoticStatistics
