module
public import StatLean.ConcentrationInequalities.Orlicz.Defs
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

/-!
# Orlicz generators ψ₂, ψ₁ — analytic side conditions

Analytic facts about the two canonical Orlicz generators
$$ \psi_2(x) = e^{x^2} - 1, \qquad \psi_1(x) = e^{x} - 1 : $$
value at zero, nonnegativity, monotonicity on $[0,\infty)$, convexity on
$[0,\infty)$, continuity, measurability, and divergence at $+\infty$. Every
general Luxemburg-norm lemma in this cluster (attainment, definiteness,
triangle, domination) takes these as hypotheses on an abstract `ψ`; this file
discharges them for `psiTwo` and `psiOne`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §2.6 (Definition 2.6.4), §2.8 (Definition 2.8.4),
and Exercises 2.42–2.43 (the properties an Orlicz function must satisfy).

**Proof formalization notes.** ψ-generator properties enter downstream lemmas
as *hypotheses*, never as a bundled Orlicz-function structure: the general
norm has no book-numbered definition (HDP Remark 2.8.9 / Exercises 2.42–2.43),
so nothing is constitutive. `psiTwo`/`psiOne` are fresh definitions in this
area: `StatLean.AsymptoticStatistics.EmpiricalProcess` has its own `psi_1`/
`psi_2` in a *concept* layer of another area, and importing it would invert
the area DAG (project charter §3 allows only cross-area `ForMathlib` imports);
the ≈60-line duplication is deliberate, with laptop-side unification deferred.
Convexity of `psiTwo` on `[0,∞)` is `ConvexOn.comp` of `exp` after `x ↦ x²`
(it fails on all of ℝ only in the sense that the book never needs it there);
all other proofs are one-step compositions.

**Bibliographic comments.** The requirements on an Orlicz function (convex,
increasing, ψ(0)=0, ψ(∞)=∞) go back to W. Orlicz (1932) and W. A. J. Luxemburg
(1955); see Buldygin–Kozachenko, AMS 2000, for the ψ₂/ψ₁ specializations.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

@[simp] lemma psiTwo_zero : psiTwo 0 = 0 := by simp [psiTwo]

@[simp] lemma psiOne_zero : psiOne 0 = 0 := by simp [psiOne]

/-- `ψ₂ ≥ 0` everywhere (`exp(x²) ≥ 1` for all `x`). -/
lemma psiTwo_nonneg (x : ℝ) : 0 ≤ psiTwo x := by
  simp only [psiTwo_apply]
  linarith [Real.add_one_le_exp (x ^ 2), sq_nonneg x]

/-- `ψ₁ ≥ 0` on `[0, ∞)`. -/
lemma psiOne_nonneg {x : ℝ}
    -- LEAN-ONLY: ψ₁ is negative on x < 0; the norm only evaluates ψ₁ at |X|/K ≥ 0
    (hx : 0 ≤ x) :
    0 ≤ psiOne x := by
  simp only [psiOne_apply]
  linarith [Real.add_one_le_exp x]

lemma psiOne_monotone : Monotone psiOne := by
  intro a b hab
  simp only [psiOne_apply]
  exact sub_le_sub_right (Real.exp_le_exp.mpr hab) 1

lemma psiTwo_monotoneOn : MonotoneOn psiTwo (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [psiTwo_apply]
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := le_trans ha' hab
  have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith [mul_le_mul hab hab ha' hb']
  exact sub_le_sub_right (Real.exp_le_exp.mpr hsq) 1

/-- Convexity of `ψ₁` on `[0, ∞)` (HDP Exercise 2.42 ingredient). -/
lemma psiOne_convexOn : ConvexOn ℝ (Set.Ici 0) psiOne := by
  have hexp : ConvexOn ℝ (Set.Ici (0 : ℝ)) Real.exp :=
    convexOn_exp.subset (Set.subset_univ _) (convex_Ici 0)
  have hfun : psiOne = fun x => Real.exp x + (-1) := by
    ext x; simp only [psiOne_apply]; ring
  rw [hfun]; exact hexp.add_const (-1)

/-- Convexity of `ψ₂` on `[0, ∞)` (HDP Exercise 2.42 ingredient;
`ConvexOn.comp` of `exp` after `x ↦ x²`). -/
lemma psiTwo_convexOn : ConvexOn ℝ (Set.Ici 0) psiTwo := by
  have hset : (fun x : ℝ => x ^ 2) '' Set.Ici 0 = Set.Ici 0 := by
    ext y; constructor
    · rintro ⟨x, _, rfl⟩; exact sq_nonneg x
    · intro hy; exact ⟨Real.sqrt y, Real.sqrt_nonneg y, Real.sq_sqrt hy⟩
  have hgexp : ConvexOn ℝ ((fun x : ℝ => x ^ 2) '' Set.Ici 0) Real.exp := by
    rw [hset]; exact convexOn_exp.subset (Set.subset_univ _) (convex_Ici 0)
  have hgmono : MonotoneOn Real.exp ((fun x : ℝ => x ^ 2) '' Set.Ici 0) :=
    Real.exp_monotone.monotoneOn _
  have hcomp : ConvexOn ℝ (Set.Ici 0) (Real.exp ∘ fun x : ℝ => x ^ 2) :=
    hgexp.comp (convexOn_pow 2) hgmono
  have hfun : psiTwo = fun x => (Real.exp ∘ fun x : ℝ => x ^ 2) x + (-1) := by
    ext x; simp only [psiTwo_apply, Function.comp_apply]; ring
  rw [hfun]; exact hcomp.add_const (-1)

/-- Continuity of `ψ₂` (side condition of the attainment lemma). -/
lemma psiTwo_continuous : Continuous psiTwo := by
  unfold psiTwo; fun_prop

/-- Continuity of `ψ₁` (side condition of the attainment lemma). -/
lemma psiOne_continuous : Continuous psiOne := by
  unfold psiOne; fun_prop

/-- Measurability of `ψ₂` (side condition of the triangle inequality). -/
lemma psiTwo_measurable : Measurable psiTwo := psiTwo_continuous.measurable

/-- Measurability of `ψ₁` (side condition of the triangle inequality). -/
lemma psiOne_measurable : Measurable psiOne := psiOne_continuous.measurable

/-- `ψ₂ → ∞` at `∞` (norm-definiteness ingredient). -/
lemma psiTwo_tendsto_atTop : Filter.Tendsto psiTwo Filter.atTop Filter.atTop := by
  have h2 : Filter.Tendsto (fun x : ℝ => Real.exp (x ^ 2)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp (Filter.tendsto_pow_atTop two_ne_zero)
  have h3 := Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) h2
  exact h3.congr (fun x => by rw [psiTwo_apply]; ring)

/-- `ψ₁ → ∞` at `∞` (norm-definiteness ingredient). -/
lemma psiOne_tendsto_atTop : Filter.Tendsto psiOne Filter.atTop Filter.atTop := by
  have h3 := Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) Real.tendsto_exp_atTop
  exact h3.congr (fun x => by rw [psiOne_apply]; ring)

end StatLean.ConcentrationInequalities
