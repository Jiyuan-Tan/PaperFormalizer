module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Empirical averages of finite samples

The empirical average of a real-valued function over a sample indexed by `Fin n`,
with its elementary additive and scalar-multiplication identities. This definition
is independent of measure theory and is shared by the probability and empirical-
process layers.
-/

namespace AsymptoticStatistics.EmpiricalProcess

variable {Ω : Type*}

/-- The **empirical average** of `f` on the sample `X`:
`empiricalAvg f n X = (1/n) · Σᵢ f (X i)`.

Edge: for `n = 0`, the sum is empty and the prefactor `(0 : ℝ)⁻¹ = 0`
in Lean's convention, so the whole expression is `0`.

This is the real-valued shorthand for integration against an empirical measure,
in the form used in the proof of vdV Theorem 19.4. -/
noncomputable def empiricalAvg (f : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (X i)

@[simp] lemma empiricalAvg_zero (f : Ω → ℝ) (X : Fin 0 → Ω) :
    empiricalAvg f 0 X = 0 := by
  simp [empiricalAvg]

@[simp] lemma empiricalAvg_const_zero (n : ℕ) (X : Fin n → Ω) :
    empiricalAvg (fun _ => (0 : ℝ)) n X = 0 := by
  simp [empiricalAvg]

lemma empiricalAvg_add (f g : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) :
    empiricalAvg (fun x => f x + g x) n X = empiricalAvg f n X + empiricalAvg g n X := by
  unfold empiricalAvg
  rw [Finset.sum_add_distrib, mul_add]

lemma empiricalAvg_smul (c : ℝ) (f : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) :
    empiricalAvg (fun x => c * f x) n X = c * empiricalAvg f n X := by
  unfold empiricalAvg
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (n : ℝ)⁻¹ c, mul_assoc]

end AsymptoticStatistics.EmpiricalProcess
