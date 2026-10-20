module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.DonskerProcessData
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperationalVec

@[expose] public section

/-!
# Coordinates for joint Brownian-bridge and influence-function limits

This module defines the continuous finite-coordinate readouts, measurable
influence representatives, covariance kernel, and joint-law assumptions in the
structural form of van der Vaart Theorem 19.23.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperationalVec

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Continuous evaluation of a bounded `F`-indexed path at the coordinate `f`. -/
noncomputable def linfEvalCLM (F : Set (Ω → ℝ)) (f : ↥F) :
    LinfF F →L[ℝ] ℝ := by
  let L : LinfF F →ₗ[ℝ] ℝ :=
    { toFun := fun z => z f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine L.mkContinuous 1 (fun z => ?_)
  simpa only [one_mul] using! lp.norm_apply_le_norm ENNReal.top_ne_zero z f

/-- A measurable pointwise representative chosen from the `L²(P)` equivalence
class of the `j`th influence coordinate. -/
noncomputable def influenceFunction
    {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) (j : Fin k) : Ω → ℝ :=
  (Lp.aestronglyMeasurable (ψ j : Lp ℝ 2 P)).mk
    (((ψ j : Lp ℝ 2 P) : Ω → ℝ))

/-- The chosen measurable influence representative agrees `P`-almost everywhere
with its underlying `L²(P)` element. -/
theorem influenceFunction_ae_eq
    {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) (j : Fin k) :
    (((ψ j : Lp ℝ 2 P) : Ω → ℝ)) =ᵐ[P] influenceFunction ψ j :=
  (Lp.aestronglyMeasurable (ψ j : Lp ℝ 2 P)).ae_eq_mk

/-- The coordinate indexed by either `f ∈ F` or an influence component.
Edge behavior: for `k = 0`, only the `F` branch can be inhabited. -/
noncomputable def jointIndexFunction
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) : Sum ↥F (Fin k) → Ω → ℝ := by
  intro a
  cases a with
  | inl f => exact (f : Ω → ℝ)
  | inr j => exact influenceFunction ψ j

/-- Evaluation of a joint path `(G, Z) ∈ ℓ∞(F) × ℝᵏ` on either an `F`
coordinate or an influence coordinate. -/
noncomputable def jointEval {F : Set (Ω → ℝ)} {k : ℕ}
    (w : LinfF F × EuclideanSpace ℝ (Fin k)) :
    Sum ↥F (Fin k) → ℝ := by
  intro a
  cases a with
  | inl f => exact w.1 f
  | inr j => exact w.2.ofLp j

/-- Covariance of two coordinates in the joint Brownian-bridge/influence
Gaussian limit. It is the covariance under `P` of the corresponding raw
functions, hence includes the bridge centering on the `F` branch.

Edge behavior: Bochner integrals retain Mathlib's standard value on
nonintegrable inputs; the existence theorem below explicitly assumes `L²` for
`F`, while influence coordinates carry it constitutively. -/
noncomputable def jointCov
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P))
    (a b : Sum ↥F (Fin k)) : ℝ := by
  exact (∫ x, jointIndexFunction ψ a x * jointIndexFunction ψ b x ∂P)
    - (∫ x, jointIndexFunction ψ a x ∂P)
      * (∫ x, jointIndexFunction ψ b x ∂P)

/-- A tight centered Gaussian law jointly coupling a `P`-Brownian bridge on
`F` and the finite influence-function vector, with the correct mixed
covariances. -/
structure IsJointBridgeInfluence
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (ψ : Fin k → ↥(L2ZeroMean P))
    (ν : Measure (LinfF F))
    (κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))) : Prop where
  /-- Constitutive (vdV Theorem 19.23 p.279): `κ` is a probability law. -/
  isProbabilityMeasure : IsProbabilityMeasure κ
  /-- Constitutive (vdV Theorem 19.23 p.279): the first marginal is the
  supplied `P`-Brownian bridge law. -/
  firstMarginal : κ.map Prod.fst = ν
  /-- Constitutive (vdV Theorem 19.23 p.279): all finite mixed coordinate
  tuples are jointly Gaussian. -/
  gaussianFDD : ∀ (m : ℕ) (a : Fin m → Sum ↥F (Fin k)),
    HasGaussianLaw
      (fun w : LinfF F × EuclideanSpace ℝ (Fin k) =>
        (fun i => jointEval w (a i))) κ
  /-- Constitutive (vdV Theorem 19.23 p.279): the joint process is centered. -/
  mean : ∀ a : Sum ↥F (Fin k),
    ∫ w, jointEval w a ∂κ = 0
  /-- Constitutive (vdV Theorem 19.23 p.279): mixed second moments have the
  covariance inherited from the common empirical process. -/
  covariance : ∀ a b : Sum ↥F (Fin k),
    ∫ w, jointEval w a * jointEval w b ∂κ = jointCov P ψ a b
  /-- Constitutive (vdV Theorem 19.23 p.279): the joint Borel limit law is
  tight, as required for path-space weak convergence. -/
  tight : IsTightMeasureSet
    ({κ} : Set (Measure (LinfF F × EuclideanSpace ℝ (Fin k))))


end AsymptoticStatistics.EmpiricalProcess
