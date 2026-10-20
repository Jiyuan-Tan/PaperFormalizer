module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
# Truncated binomial sum bound `∑_{k ≤ d} C(n,k) ≤ (en/d)^d`

For natural numbers $1 \le d \le n$,
$$ \sum_{k=0}^{d} \binom{n}{k} \;\le\; \Bigl(\frac{e\,n}{d}\Bigr)^{d}. $$
This is the classical closed-form bound on the truncated binomial sum that
turns the Sauer–Shelah counting lemma into the polynomial growth bound used
throughout VC theory.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Exercise 0.6 (used in §8.3.3, Lemma 8.3.9,
second inequality).

**Proof formalization notes.** Absent from Mathlib (brick check). Proof plan:
multiply by $(d/n)^d \le (d/n)^k$ (for $k \le d$, since $d/n \le 1$), bound
the resulting sum by the full binomial expansion of $(1 + d/n)^n$ via
`add_pow` + `Finset.sum_le_sum_of_subset_of_nonneg`, then
$(1 + d/n)^n \le e^d$ from `Real.add_one_le_exp`. The constant is exactly
the book's $e = $ `Real.exp 1`; no numeric slack is taken here. Edge
behavior: the hypothesis `1 ≤ d` rules out the degenerate `0^0` division;
`d ≤ n` is the book's stated regime (the bound is false for `d > n` as
stated, e.g. `n = 1, d = 2`). Pure real algebra, zero probability content;
candidate upstream. Named-sorry fallback of this work item:
`sum_choose_le_exp_mul_pow` (already in final consumable form).

**Bibliographic comments.** The bound is folklore in combinatorics and
statistical learning theory; it appears as the standard companion to the
Sauer–Shelah lemma (N. Sauer, *J. Combin. Theory Ser. A* 13 (1972), 145–147;
S. Shelah, *Pacific J. Math.* 41 (1972), 247–261).
-/

open Finset

namespace StatLean.ConcentrationInequalities

/-- Truncated binomial theorem: for `0 ≤ x`, the sum of the first `d + 1`
terms of the binomial expansion of `(1 + x)^n` is at most the whole
expansion. -/
lemma sum_choose_mul_pow_le_one_add_pow {n d : ℕ}
    -- LEAN-ONLY: truncation range fits inside the expansion range; pure
    -- algebra, no book content.
    (hdn : d ≤ n) {x : ℝ}
    -- LEAN-ONLY: nonnegativity so dropped binomial terms are nonnegative.
    (hx0 : 0 ≤ x) :
    ∑ k ∈ Finset.Iic d, (n.choose k : ℝ) * x ^ k ≤ (1 + x) ^ n := by
  have hpow : (1 + x) ^ n
      = ∑ k ∈ Finset.range (n + 1), x ^ k * (n.choose k : ℝ) := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one]
  have hcomm : ∑ k ∈ Finset.Iic d, (n.choose k : ℝ) * x ^ k
      = ∑ k ∈ Finset.Iic d, x ^ k * (n.choose k : ℝ) := by
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  rw [hcomm, hpow]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro k hk
    simp only [Finset.mem_Iic] at hk
    simp only [Finset.mem_range]
    omega
  · intro k _ _
    positivity

/-- `(1 + d/n)^n ≤ e^d`, from `Real.add_one_le_exp` applied at `d/n`. -/
lemma one_add_div_pow_le_exp {n d : ℕ}
    -- LEAN-ONLY: positivity of the denominator; pure algebra.
    (hn : 0 < n) :
    ((1 : ℝ) + (d : ℝ) / (n : ℝ)) ^ n ≤ Real.exp d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (1 : ℝ) + (d : ℝ) / (n : ℝ) ≤ Real.exp ((d : ℝ) / (n : ℝ)) := by
    have := Real.add_one_le_exp ((d : ℝ) / (n : ℝ))
    linarith
  calc ((1 : ℝ) + (d : ℝ) / (n : ℝ)) ^ n
      ≤ (Real.exp ((d : ℝ) / (n : ℝ))) ^ n :=
        pow_le_pow_left₀ (by positivity) h1 n
    _ = Real.exp ((n : ℝ) * ((d : ℝ) / (n : ℝ))) := by rw [Real.exp_nat_mul]
    _ = Real.exp d := by congr 1; field_simp

/-- **Truncated binomial sum bound** (HDP Exercise 0.6; used in §8.3.3,
Lemma 8.3.9): for `1 ≤ d ≤ n`,
`∑_{k ≤ d} C(n,k) ≤ (e·n/d)^d` with `e = Real.exp 1`. -/
theorem sum_choose_le_exp_mul_pow {n d : ℕ}
    -- USER-INPUT: 1 ≤ d (nondegenerate dimension); HDP Exercise 0.6.
    (hd1 : 1 ≤ d)
    -- USER-INPUT: d ≤ n (the book's stated regime; the bound fails above the
    -- diagonal); HDP Exercise 0.6.
    (hdn : d ≤ n) :
    (∑ k ∈ Finset.Iic d, (n.choose k : ℝ)) ≤ (Real.exp 1 * n / d) ^ d := by
  have hnN : 0 < n := lt_of_lt_of_le hd1 hdn
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnN
  set r : ℝ := (d : ℝ) / (n : ℝ) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hn0]; exact_mod_cast hdn
  have hrd0 : 0 < r ^ d := pow_pos hr0 d
  -- Key: `(∑ C(n,k)) · rᵈ ≤ eᵈ`.
  have hkey : (∑ k ∈ Finset.Iic d, (n.choose k : ℝ)) * r ^ d ≤ Real.exp d := by
    rw [Finset.sum_mul]
    have step2 : ∑ k ∈ Finset.Iic d, (n.choose k : ℝ) * r ^ d
        ≤ ∑ k ∈ Finset.Iic d, (n.choose k : ℝ) * r ^ k := by
      refine Finset.sum_le_sum fun k hk => ?_
      simp only [Finset.mem_Iic] at hk
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr0.le hr1 hk) (Nat.cast_nonneg _)
    refine step2.trans ?_
    refine (sum_choose_mul_pow_le_one_add_pow hdn hr0.le).trans ?_
    rw [hr]
    exact one_add_div_pow_le_exp hnN
  -- `RHSᵈ · rᵈ = eᵈ`, so cancel the positive factor `rᵈ`.
  have hrhs : (Real.exp 1 * n / d) ^ d * r ^ d = Real.exp d := by
    rw [hr, ← mul_pow]
    have hcollapse : Real.exp 1 * (n : ℝ) / (d : ℝ) * ((d : ℝ) / (n : ℝ))
        = Real.exp 1 := by field_simp
    rw [hcollapse, ← Real.exp_nat_mul, mul_one]
  refine le_of_mul_le_mul_right ?_ hrd0
  rw [hrhs]
  exact hkey

end StatLean.ConcentrationInequalities
