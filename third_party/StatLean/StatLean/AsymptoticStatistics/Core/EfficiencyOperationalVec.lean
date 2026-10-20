module
public import StatLean.AsymptoticStatistics.Core.EIFVec
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperational
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Operational semiparametric efficiency — vector parameter

Vector-valued (`θ ∈ ℝᵈ`) counterparts of the scalar predicates in
`AsymptoticStatistics.Core.EfficiencyOperational`: asymptotic linearity,
the bias-residual variant, and the operational form of semiparametric
efficiency, all for an estimator sequence
`T_n : (Fin n → Ω) → EuclideanSpace ℝ (Fin d)`.

The codomain is `EuclideanSpace ℝ (Fin d)`; the influence function is a
*tuple* `φ : Fin d → ↥(L²₀(P))` (component `φ j` is the influence
function of the `j`-th coordinate functional); the deviation is the
Euclidean norm `‖·‖`. The efficiency clause uses
`IsEfficientInfluenceFunction_vec` from `Core.EIFVec`.

This layer is **additive** over the scalar layer: the scalar
declarations are unchanged. The `d = 1` case recovers the scalar
predicates (up to the `EuclideanSpace ℝ (Fin 1) ≃ ℝ` identification).

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998),
§25.5 — the vector parameter form of asymptotic linearity (eq:25.22)
and operational efficiency (lem:25.23).
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.EfficiencyOperationalVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EIFVec

variable {Ω : Type*} [MeasurableSpace Ω]
variable {d : ℕ}

/-- The `EuclideanSpace ℝ (Fin d)`-valued evaluation of an influence
function tuple `φ : Fin d → ↥(L²₀(P))` at a sample point `x : Ω`:
the vector whose `j`-th coordinate is `(φ j)(x)`. -/
noncomputable def tupleEval
    (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : Fin d → ↥(L2ZeroMean P)) (x : Ω) : EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm
    (fun j => ((φ j : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x)

/-- An estimator sequence `T_n : (Fin n → Ω) → EuclideanSpace ℝ (Fin d)`
is *asymptotically linear* at a probability measure `P` with influence
function tuple `φ : Fin d → ↥(L²₀(P))` and centering
`c : EuclideanSpace ℝ (Fin d)`, iff for every `ε > 0` the `Pⁿ`-probability
that the Euclidean norm of the residual
`√n · (T_n X − c) − (1/√n) · Σᵢ (φ(Xᵢ))` exceeds `ε` tends to zero.

This is the vector form of
`AsymptoticStatistics.Core.EfficiencyOperational.AsymptoticallyLinearAt`:
the absolute value `|·|` is replaced by the Euclidean norm `‖·‖`, the
scalar influence function by the tuple `φ`, and the scalar centering by
the vector `c`.

Reference: vdV §25.5, eq:25.22 (vector form). -/
def AsymptoticallyLinearAt_vec
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : Fin d → ↥(L2ZeroMean P)) (c : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ ε > 0, Tendsto (fun n : ℕ =>
    (MeasureTheory.Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ ‖Real.sqrt n • (T_n n X - c)
              - (Real.sqrt n)⁻¹
                • (∑ i, tupleEval P φ (X i))‖})
    atTop (nhds 0)

/-- *Bias-residual variant of vector asymptotic linearity (vdV §25.5,
thm:25.59, vector form).*

`T_n` is asymptotically linear at `P` with influence tuple `φ`, vector
centering `c`, and bias-residual sequence
`bias : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)`, iff for every
`ε > 0` the `Pⁿ`-probability that
`‖√n · (T_n X − c) − (1/√n) · Σᵢ φ(Xᵢ) − bias n X‖ ≥ ε` tends to zero.

Edge behavior: when `bias = (fun _ _ => 0)`, the predicate is literally
`AsymptoticallyLinearAt_vec T_n P φ c` (see
`asympLinearWithBiasAt_vec_zero_iff_asympLinearAt_vec`). -/
def AsymptoticallyLinearWithBiasAt_vec
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : Fin d → ↥(L2ZeroMean P)) (c : EuclideanSpace ℝ (Fin d))
    (bias : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ ε > 0, Tendsto (fun n : ℕ =>
    (MeasureTheory.Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ ‖Real.sqrt n • (T_n n X - c)
              - (Real.sqrt n)⁻¹
                • (∑ i, tupleEval P φ (X i))
              - bias n X‖})
    atTop (nhds 0)

/-- *Reduction: vector thm:25.54 = vector thm:25.59 with vanishing
bias.* The bias-residual predicate at the constantly-zero bias sequence
is literally `AsymptoticallyLinearAt_vec`.

Reference: vdV §25.5, the (25.52)-collapse step, vector form. -/
theorem asympLinearWithBiasAt_vec_zero_iff_asympLinearAt_vec
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : Fin d → ↥(L2ZeroMean P)) (c : EuclideanSpace ℝ (Fin d)) :
    AsymptoticallyLinearWithBiasAt_vec T_n P φ c (fun _ _ => 0)
      ↔ AsymptoticallyLinearAt_vec T_n P φ c := by
  simp only [AsymptoticallyLinearWithBiasAt_vec, AsymptoticallyLinearAt_vec,
    sub_zero]

/-- An estimator sequence `T_n` is *semiparametrically efficient* at `P`
relative to a tangent space `T` for the vector functional
`ψ : Measure Ω → EuclideanSpace ℝ (Fin d)`, iff there exists an
efficient influence function tuple `φ : Fin d → ↥(L²₀(P))` and a vector
derivative `Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)` such that `φ` is the
vector EIF for `Dψ` and `T_n` is asymptotically linear at `P` with
influence tuple `φ` and centering `ψ P`.

This is the vector form of
`AsymptoticStatistics.Core.EfficiencyOperational.SemiparametricallyEfficientAt`,
with `IsEfficientInfluenceFunction` replaced by the componentwise
`IsEfficientInfluenceFunction_vec`.

Reference: vdV §25.5 (operational form, vector parameter). -/
def SemiparametricallyEfficientAt_vec
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin d))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Submodule ℝ ↥(L2ZeroMean P)) : Prop :=
  ∃ (φ : Fin d → ↥(L2ZeroMean P)) (Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)),
    IsEfficientInfluenceFunction_vec Dψ φ ∧
    AsymptoticallyLinearAt_vec T_n P φ (ψ P)

/-- *Operational form of vdV lem:25.23 (vector parameter).* If the tuple
`φ` is a vector EIF for `Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)` at `P`
relative to `T`, and `T_n` is asymptotically linear at `P` with influence
tuple `φ` and centering `ψ P`, then `T_n` is semiparametrically efficient
at `P` relative to `T` for `ψ`.

Reference: vdV §25.5, lem:25.23 (operational form, vector). The proof is
the And-intro under existential witnesses — definitional. -/
theorem estimator_semiparametricallyEfficient_of_asympLinear_eif_vec
    {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Submodule ℝ ↥(L2ZeroMean P)}
    {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)} {φ : Fin d → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec Dψ φ)
    (hAL : AsymptoticallyLinearAt_vec T_n P φ (ψ P)) :
    SemiparametricallyEfficientAt_vec T_n ψ P T :=
  ⟨φ, Dψ, hEIF, hAL⟩

end AsymptoticStatistics.Core.EfficiencyOperationalVec
