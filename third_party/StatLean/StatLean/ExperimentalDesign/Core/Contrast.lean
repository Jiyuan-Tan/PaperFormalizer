module
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Treatment contrasts

A **contrast** among `t` treatments is a coefficient vector `l : T → ℝ` with
`∑ⱼ lⱼ = 0`; the associated treatment comparison is `L = ∑ⱼ lⱼ μⱼ` for treatment
means (or effects) `μ`.  The zero-sum constraint is exactly what makes comparisons
insensitive to the overall level: `∑ⱼ lⱼ (μⱼ + a) = ∑ⱼ lⱼ μⱼ`.  Two contrasts are
**orthogonal** when `∑ⱼ lⱼ l'ⱼ = 0`; orthogonal contrasts carry independent pieces of
the treatment variation.

This tiny abstraction is reused by pairwise treatment comparisons, ANOVA component
sums of squares, and (via the `±1` characters of `Factorial/TwoLevel`) all factorial
main effects and interactions.

## Main results

* `Contrast` — the structure; `Contrast.eval` — the comparison `∑ⱼ lⱼ μⱼ`.
* `eval_const`, `eval_add_const` — insensitivity to the overall level.
* `eval_add`, `eval_smul` — linearity in the treatment means.
* `Contrast.add`, `Contrast.neg`, `Contrast.smul`, `Contrast.zero` — the coefficient
  algebra.
* `Contrast.IsOrthogonal` — orthogonality of comparisons.
* `pairwiseContrast`, `eval_pairwiseContrast` — the elementary comparison `μ₁ − μ₂`.

**Reference.** R. Mead, *The Design of Experiments*, Cambridge University Press,
1988, §4.7 (contrasts, treatment comparisons and component sums of squares): the
zero-sum definition `L_k = ∑_j l_{kj} t_j`, `∑_j l_{kj} = 0`, the observation that the
least-squares estimate `∑_j l_{kj} ȳ_{.j}` is unchanged by the overall mean because
the coefficients sum to zero, and the orthogonality condition `∑_j l_{kj} l_{k'j} = 0`.
(`Mead §4.7`.)

**Proof formalization notes.**
* The zero-sum condition is a structure field (constitutive: without it the object is
  not Mead's contrast and level-insensitivity fails).
* No `Fintype T` degeneracy issues: over an empty treatment set every coefficient
  vector is a contrast and every evaluation is `0`.
* Scale is deliberately unconstrained (`Mead §4.7`: "there are no restrictions on the
  size of coefficients"), so contrasts form an `ℝ`-module, not a normalised family.
-/

namespace StatLean.ExperimentalDesign

variable {T : Type*} [Fintype T]

/-- A **treatment contrast**: a coefficient vector on the treatments summing to zero
(`Mead §4.7`). -/
structure Contrast (T : Type*) [Fintype T] where
  /-- The comparison coefficients `l : T → ℝ`. -/
  coeff : T → ℝ
  /-- Constitutive (Mead §4.7): the coefficients sum to zero — this is what makes the
  comparison insensitive to the overall treatment level. -/
  sum_coeff_eq_zero : ∑ t, coeff t = 0

namespace Contrast

/-- The **treatment comparison** `L = ∑ⱼ lⱼ μⱼ` evaluated at treatment means `μ`
(`Mead §4.7`). -/
noncomputable def eval (c : Contrast T) (μ : T → ℝ) : ℝ :=
  ∑ t, c.coeff t * μ t

/-- A contrast annihilates constants. -/
theorem eval_const (c : Contrast T) (a : ℝ) : c.eval (fun _ => a) = 0 := by
  rw [eval, ← Finset.sum_mul, c.sum_coeff_eq_zero, zero_mul]

/-- A contrast is insensitive to a shift of the overall level (`Mead §4.7`). -/
theorem eval_add_const (c : Contrast T) (μ : T → ℝ) (a : ℝ) :
    c.eval (fun t => μ t + a) = c.eval μ := by
  simp only [eval, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, c.sum_coeff_eq_zero,
    zero_mul, add_zero]

/-- Additivity of the comparison in the treatment means. -/
theorem eval_add (c : Contrast T) (μ ν : T → ℝ) :
    c.eval (fun t => μ t + ν t) = c.eval μ + c.eval ν := by
  simp only [eval, mul_add, Finset.sum_add_distrib]

/-- Homogeneity of the comparison in the treatment means. -/
theorem eval_smul (c : Contrast T) (b : ℝ) (μ : T → ℝ) :
    c.eval (fun t => b * μ t) = b * c.eval μ := by
  simp only [eval, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- The zero contrast. -/
noncomputable def zero : Contrast T :=
  ⟨fun _ => 0, by simp⟩

/-- The sum of two contrasts. -/
noncomputable def add (c d : Contrast T) : Contrast T :=
  ⟨fun t => c.coeff t + d.coeff t, by
    rw [Finset.sum_add_distrib, c.sum_coeff_eq_zero, d.sum_coeff_eq_zero, add_zero]⟩

/-- The negation of a contrast. -/
noncomputable def neg (c : Contrast T) : Contrast T :=
  ⟨fun t => -c.coeff t, by rw [Finset.sum_neg_distrib, c.sum_coeff_eq_zero, neg_zero]⟩

/-- A scalar multiple of a contrast (`Mead §4.7`: comparisons are scale-free). -/
noncomputable def smul (b : ℝ) (c : Contrast T) : Contrast T :=
  ⟨fun t => b * c.coeff t, by rw [← Finset.mul_sum, c.sum_coeff_eq_zero, mul_zero]⟩

/-- Evaluation is additive in the contrast. -/
theorem add_eval (c d : Contrast T) (μ : T → ℝ) :
    (c.add d).eval μ = c.eval μ + d.eval μ := by
  simp only [eval, add, add_mul, Finset.sum_add_distrib]

/-- Evaluation is homogeneous in the contrast. -/
theorem smul_eval (b : ℝ) (c : Contrast T) (μ : T → ℝ) :
    (c.smul b).eval μ = b * c.eval μ := by
  simp only [eval, smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **Orthogonality** of two treatment comparisons: `∑ⱼ lⱼ l'ⱼ = 0` (`Mead §4.7`). -/
def IsOrthogonal (c d : Contrast T) : Prop :=
  ∑ t, c.coeff t * d.coeff t = 0

/-- Orthogonality is symmetric. -/
theorem IsOrthogonal.symm {c d : Contrast T} (h : c.IsOrthogonal d) :
    d.IsOrthogonal c := by
  rw [IsOrthogonal, ← h]
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

end Contrast

section Pairwise

variable [DecidableEq T]

/-- The **pairwise contrast** comparing treatments `t₁` and `t₂`: coefficients `+1`
at `t₁`, `−1` at `t₂`, `0` elsewhere (`Mead §4.7`, the simple comparison
`t₁ − t₂`). -/
noncomputable def pairwiseContrast (t₁ t₂ : T)
    -- LEAN-ONLY: distinct treatments; for `t₁ = t₂` the coefficients cancel to the
    -- zero contrast and the evaluation lemma below would still hold trivially
    (h : t₁ ≠ t₂) : Contrast T :=
  ⟨fun t => (if t = t₁ then (1 : ℝ) else 0) - (if t = t₂ then (1 : ℝ) else 0),
    by rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ t₁ (fun _ => (1 : ℝ)),
      Finset.sum_ite_eq' Finset.univ t₂ (fun _ => (1 : ℝ))]; simp⟩

/-- The pairwise contrast evaluates to the difference of the two treatment means. -/
theorem eval_pairwiseContrast (t₁ t₂ : T) (h : t₁ ≠ t₂) (μ : T → ℝ) :
    (pairwiseContrast t₁ t₂ h).eval μ = μ t₁ - μ t₂ := by
  simp only [Contrast.eval, pairwiseContrast, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_pos]

end Pairwise

end StatLean.ExperimentalDesign
