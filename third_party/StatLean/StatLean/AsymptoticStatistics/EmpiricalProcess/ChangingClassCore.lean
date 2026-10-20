module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.Outer
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
# The common carrier for changing-class empirical processes

This file supplies the bounded-path carrier and the finite-coordinate linear maps used in the
finite-partition formulation of asymptotic equicontinuity. No topology or countability assumption
is imposed on the index type.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

/-- **Constitutive (vdV Theorem 18.14 and §19.5):** the bounded-path carrier `ℓ∞(T)`. -/
abbrev LinfT (T : Type*) : Type _ := lp (fun _ : T => ℝ) ∞

/-- The Borel measurable space on the sup-norm carrier `LinfT T`. -/
noncomputable instance instMeasurableSpaceLinfT (T : Type*) :
    MeasurableSpace (LinfT T) := borel _

instance instBorelSpaceLinfT (T : Type*) : BorelSpace (LinfT T) := ⟨rfl⟩

/-- **Constitutive (vdV Theorem 18.14):** a finite partition of the index set together with one
representative per cell. The zero-cell case is retained. -/
structure FiniteApproximation (T : Type*) where
  k : ℕ
  cell : T → Fin k
  rep : Fin k → T

/-- **Evaluation at one bounded-path coordinate** (vdV Theorem 18.14), bundled as
a continuous linear map of norm at most one. -/
noncomputable def changingClassLinfEvalCLM {T : Type*} (t : T) : LinfT T →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun x => x t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun x => by
      simpa using! lp.norm_apply_le_norm ENNReal.top_ne_zero x t

/-- **Constitutive (vdV Theorem 18.14):** restrict a bounded path to a finite ordered family of
coordinates. This also covers the zero-dimensional coordinate space. -/
noncomputable def finiteCoordinateProjection {T : Type*} {k : ℕ} (t : Fin k → T) :
    LinfT T →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => changingClassLinfEvalCLM (t i))

/-- **Constitutive (vdV Theorem 18.14):** reconstruct a bounded path by making it constant on each
cell of a finite approximation. -/
noncomputable def finiteReconstruction {T : Type*} (a : FiniteApproximation T) :
    EuclideanSpace ℝ (Fin a.k) →L[ℝ] LinfT T := by
  let L : EuclideanSpace ℝ (Fin a.k) →ₗ[ℝ] LinfT T :=
    { toFun := fun y =>
        ⟨fun s => y (a.cell s), memℓp_infty ⟨‖y‖, by
          rintro _ ⟨s, rfl⟩
          exact PiLp.norm_apply_le y (a.cell s)⟩⟩
      map_add' := by
        intro y z
        apply lp.ext
        funext s
        rfl
      map_smul' := by
        intro c y
        apply lp.ext
        funext s
        rfl }
  exact LinearMap.mkContinuous L 1 fun y => by
    simp only [one_mul]
    apply lp.norm_le_of_forall_le (norm_nonneg y)
    intro s
    exact PiLp.norm_apply_le y (a.cell s)

namespace FiniteApproximation

/-- **Constitutive (vdV Theorem 18.14):** project a bounded path to representative coordinates and
then reconstruct it as a path constant on each cell. -/
noncomputable def project {T : Type*} (a : FiniteApproximation T) : LinfT T →L[ℝ] LinfT T :=
  finiteReconstruction a ∘L finiteCoordinateProjection a.rep

@[simp] theorem project_apply {T : Type*} (a : FiniteApproximation T)
    (z : LinfT T) (t : T) :
    a.project z t = z (a.rep (a.cell t)) := by
  rfl

end FiniteApproximation

/-- **DERIVED criterion (vdV Theorem 18.14):** eventual approximation in outer probability by
one finite partition projection. Both tolerances are strictly positive; the finite approximation
is allowed to have zero cells. -/
def PartitionAEC {Ξ T : Type*} [MeasurableSpace Ξ]
    (μ : ℕ → Measure Ξ) (X : ℕ → Ξ → LinfT T) : Prop :=
  ∀ ε η, 0 < ε → 0 < η → ∃ a : FiniteApproximation T, ∀ᶠ n in Filter.atTop,
    (μ n).outerMeasureStar {ξ | η < ‖X n ξ - a.project (X n ξ)‖} < ENNReal.ofReal ε

/-- **Constitutive (vdV Theorem 18.14):** the covariance matrix cut out by a finite ordered
family of indices. The definition is total in dimension zero. -/
def finiteCovariance {T : Type*} (C : T → T → ℝ) {k : ℕ} (t : Fin k → T) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => C (t i) (t j)

/-- **DERIVED predicate (vdV Theorem 18.14):** ordinary convergence in distribution of every
finite coordinate projection to its centered, possibly singular multivariate Gaussian law. The
zero-dimensional projection is included. -/
def FDDConverges {Ξ T : Type*} [MeasurableSpace Ξ]
    (μ : ℕ → Measure Ξ) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ℕ → Ξ → LinfT T) (C : T → T → ℝ) : Prop :=
  ∀ {k : ℕ} (t : Fin k → T),
    TendstoInDistribution (fun n ξ => finiteCoordinateProjection t (X n ξ))
      Filter.atTop id μ (multivariateGaussian 0 (finiteCovariance C t))

/-- **Constitutive covariance condition (vdV Theorem 18.14):** every finite covariance cut is
positive semidefinite, including the zero-dimensional cut. -/
def KernelPosSemidef {T : Type*} (C : T → T → ℝ) : Prop :=
  ∀ {k : ℕ} (t : Fin k → T), (finiteCovariance C t).PosSemidef

/-- **Constitutive (vdV Theorem 18.14):** a proposed centered Gaussian limit law is a
probability measure, is tight as a singleton family, and has every prescribed finite Gaussian
coordinate law. The zero-dimensional finite law is included; no countability assumption on `T`
or existence certificate is stored. -/
structure TightCenteredGaussianLaw {T : Type*} (C : T → T → ℝ)
    (ν : Measure (LinfT T)) : Prop where
  prob : IsProbabilityMeasure ν
  tight : IsTightMeasureSet ({ν} : Set (Measure (LinfT T)))
  finiteLaw : ∀ {k : ℕ} (t : Fin k → T),
    ν.map (finiteCoordinateProjection t) =
      multivariateGaussian 0 (finiteCovariance C t)

end AsymptoticStatistics.EmpiricalProcess
