module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
public import StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

/-!
# The affine-transformed empirical process and its per-index measurability

The chaining decomposition's right-hand side is a sum of `∫⁻` terms whose
B-link / TRUNC / raw integrands carry a supremum `⨆ f ∈ S` of
`ξ ↦ |𝔾ₙ(φ f)(ξ)|` over a sub-collection `S ⊆ F`, for a **pointwise-affine**
transform `φ f = (f − a) · b` with a fixed subtract `a : Ω → ℝ` and a fixed
multiplier `b : Ω → ℝ`.  All three shapes (raw: `a = 0, b = 1`; TRUNC:
`a = 0, b = 1{tail}`; B-link: `a = π_q i, b = 1{chainB i}`) are the same
functional `f ↦ |𝔾ₙ((f − a)·b)|`.

This file hosts the common functional itself together with its **per-index**
measurability leaf:

* `transformedEmpProcess` — the affine-transformed empirical process
  `f ↦ 𝔾ₙ((f − a)·b)`.
* `measurable_ofReal_abs_transformedEmpProcess` — for fixed `f`, the map
  `ξ ↦ ofReal|𝔾ₙ((f − a)·b)(ξ)|` is measurable in the sample randomness `ξ`
  whenever `f`, `a`, `b` are measurable.

The countable-supremum **bridges** that turn an `⨆ f ∈ S` into a measurable
function live in `PointwiseDense.lean`, built on the *satisfiable* VW
pointwise-measurable predicate `EmpProcPointwiseDense` (a countable
pointwise-dense `F' ⊆ F` with an integrable envelope) via dominated
convergence.  Those bridges consume `transformedEmpProcess` and
`measurable_ofReal_abs_transformedEmpProcess` from this file.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §2.3.3
(measurability of suprema, `E*`); van der Vaart & Wellner, *Weak Convergence
and Empirical Processes* (Springer, 1996), §2.3.3 (pointwise-measurable class).
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **affine-transformed empirical process**
`f ↦ 𝔾ₙ((f − a) · b) = empiricalProcess P n Y ((f − a) · b)`, the common
functional of all three chaining suprema (raw: `a = 0, b = 1`; TRUNC:
`a = 0, b = 1{tail}`; B-link: `a = π_q i, b = 1{chainB i}`).

`a` (the subtract) and `b` (the multiplier) are *fixed* functions of the
sample point; the only varying argument is the index `f ∈ F`. -/
noncomputable def transformedEmpProcess
    (P : Measure Ω) (n : ℕ) (Y : Fin n → Ω) (a b : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  empiricalProcess P n Y (fun x => (f x - a x) * b x)

/-! ### Per-index measurability of the transformed empirical process

The transformed empirical process `ξ ↦ 𝔾ₙ((f − a)·b)(ξ)` is measurable in the
sample randomness `ξ` whenever `f`, `a`, `b` are measurable. This is the leaf
the countable-supremum bridges in `PointwiseDense.lean` feed into. -/

variable {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ω}

/-- `ξ ↦ ofReal|𝔾ₙ((f − a)·b)(ξ)|` is measurable when `f`, `a`, `b` are
measurable.  The composed multiplier `(f − a)·b` is measurable, then the
empirical process is a finite linear combination of measurable sample
evaluations (`empiricalAvg`) minus a constant (`∫ · dP`), scaled by `√n`. -/
lemma measurable_ofReal_abs_transformedEmpProcess
    {X : ℕ → Ξ → Ω} (hX_meas : ∀ i, Measurable (X i))
    (n : ℕ) {a b f : Ω → ℝ} (hf : Measurable f) (ha : Measurable a)
    (hb : Measurable b) :
    Measurable (fun ξ : Ξ =>
      ENNReal.ofReal
        |transformedEmpProcess P n (fun i : Fin n => X i.val ξ) a b f|) := by
  have hg : Measurable (fun x => (f x - a x) * b x) :=
    ((hf.sub ha).mul hb)
  have hE : Measurable (fun ξ : Ξ =>
      transformedEmpProcess P n (fun i : Fin n => X i.val ξ) a b f) := by
    unfold transformedEmpProcess empiricalProcess empiricalAvg
    refine Measurable.const_mul (Measurable.sub ?_ measurable_const) _
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum Finset.univ
      (fun i _ => hg.comp (hX_meas i.val))
  have habs : (fun ξ : Ξ =>
        |transformedEmpProcess P n (fun i : Fin n => X i.val ξ) a b f|)
      = (fun ξ : Ξ =>
        ‖transformedEmpProcess P n (fun i : Fin n => X i.val ξ) a b f‖) := by
    funext ξ; exact (Real.norm_eq_abs _).symm
  exact Measurable.ennreal_ofReal (habs ▸ hE.norm)

end AsymptoticStatistics.EmpiricalProcess
