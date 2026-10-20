module
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# Binomial ratio inequality — `ForMathlib` layer

A pure finite-sum inequality (no probability), used by the knock-off initial bound
`E[V₊(0)/(1+V₋(0))] ≤ 1` where `V₊(0) ~ Binomial(N, ½)` and `V₋(0) = N − V₊(0)`:

`∑_{k=0}^{N} C(N,k)/2^N · k/(1 + (N−k)) ≤ 1`.

The sum equals exactly `1 − 2^{-N}`; the proof telescopes each term as
`C(N+1,k)/2^N − C(N,k)/2^N` (via `Nat.choose_mul_succ_eq`) and sums the two binomial rows. Not
packaged in Mathlib; theorem-agnostic.
-/

open Finset

namespace StatLean.MultipleTesting

/-- Per-term identity: `C(N,k)/2^N · k/(1+(N−k)) = C(N+1,k)/2^N − C(N,k)/2^N` for `k ≤ N`. Follows
from `Nat.choose_mul_succ_eq N k : C(N,k)·(N+1) = C(N+1,k)·(N+1−k)`. -/
private lemma binom_ratio_term_eq (N k : ℕ) (hkN : k ≤ N) :
    (N.choose k : ℝ) / 2 ^ N * ((k : ℝ) / (1 + ((N : ℝ) - (k : ℝ)))) =
    (N + 1).choose k / 2 ^ N - N.choose k / 2 ^ N := by
  have h2N : (2 : ℝ) ^ N ≠ 0 := by positivity
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hd_pos : (0 : ℝ) < 1 + ((N : ℝ) - k) := by linarith
  have hkN1 : k ≤ N + 1 := Nat.le_succ_of_le hkN
  have hR : (N.choose k : ℝ) * ((N : ℝ) + 1) =
      ((N + 1).choose k : ℝ) * (1 + ((N : ℝ) - k)) :=
    calc (N.choose k : ℝ) * ((N : ℝ) + 1)
        = ((N.choose k * (N + 1) : ℕ) : ℝ) := by push_cast; ring
      _ = (((N + 1).choose k * (N + 1 - k) : ℕ) : ℝ) := by
            exact_mod_cast Nat.choose_mul_succ_eq N k
      _ = ((N + 1).choose k : ℝ) * ((N + 1 - k : ℕ) : ℝ) := by push_cast; ring
      _ = ((N + 1).choose k : ℝ) * (1 + ((N : ℝ) - k)) := by
            congr 1; rw [Nat.cast_sub hkN1]; push_cast; ring
  field_simp [h2N, hd_pos.ne']
  linear_combination hR

/-- `∑_{k=0}^N C(N,k)/2^N · k/(1+(N−k)) = 1 − 1/2^N ≤ 1`. The finite-sum inequality behind the
knock-off initial bound `E[V₊(0)/(1+V₋(0))] ≤ 1` (`V₊(0) ~ Binomial(N, ½)`). -/
theorem binom_ratio_sum_le_one (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      (N.choose k : ℝ) / 2 ^ N * ((k : ℝ) / (1 + ((N : ℝ) - (k : ℝ))))) ≤ 1 := by
  have h2N_pos : (0 : ℝ) < 2 ^ N := by positivity
  suffices h : ∑ k ∈ Finset.range (N + 1),
      (N.choose k : ℝ) / 2 ^ N * ((k : ℝ) / (1 + ((N : ℝ) - (k : ℝ)))) = 1 - 1 / 2 ^ N by
    linarith [div_pos one_pos h2N_pos]
  rw [Finset.sum_congr rfl fun k hk =>
    binom_ratio_term_eq N k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [Finset.sum_sub_distrib]
  have hN : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) / 2 ^ N = 1 := by
    rw [← Finset.sum_div]
    have : (∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ)) = 2 ^ N := by
      exact_mod_cast Nat.sum_range_choose N
    rw [this, div_self h2N_pos.ne']
  have hN1 : ∑ k ∈ Finset.range (N + 1), ((N + 1).choose k : ℝ) / 2 ^ N = 2 - 1 / 2 ^ N := by
    rw [← Finset.sum_div]
    have hpartial : ∑ k ∈ Finset.range (N + 1), (N + 1).choose k = 2 ^ (N + 1) - 1 := by
      have h := Nat.sum_range_choose (N + 1)
      rw [Finset.sum_range_succ, Nat.choose_self] at h
      omega
    have hcastsum : (∑ k ∈ Finset.range (N + 1), ((N + 1).choose k : ℝ)) =
        (2 : ℝ) ^ (N + 1) - 1 := by
      have h1 : 1 ≤ 2 ^ (N + 1) := Nat.one_le_two_pow
      calc (∑ k ∈ Finset.range (N + 1), ((N + 1).choose k : ℝ))
          = ((∑ k ∈ Finset.range (N + 1), (N + 1).choose k : ℕ) : ℝ) := by norm_cast
        _ = ((2 ^ (N + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hpartial
        _ = (2 : ℝ) ^ (N + 1) - 1 := by rw [Nat.cast_sub h1]; push_cast; ring
    rw [hcastsum]
    have h2N1 : (2 : ℝ) ^ (N + 1) = 2 * 2 ^ N := by ring
    rw [h2N1]
    field_simp
  linarith [hN, hN1]

/-- **Knock-off supermartingale step** (the finite core, Lu, *Big Data Analysis*, Springer Nature
Switzerland, 2025 (ISBN 978-3-032-03160-0), Ch. 21 (Knock-Off) §21.3, Theorem 21.2 (Knock-Off) /
Barber–Candès): with null
positive/negative counts `a, b` among the remaining nulls (`k = a+b`), revealing the next removed
sign uniformly (`+` w.p. `a/k`, `−` w.p. `b/k`) does not increase the ratio `a/(1+b)`:
`(a/k)·(a−1)/(1+b) + (b/k)·(a/b) ≤ a/(1+b)`. Equality for `b ≥ 1`; strict at `b = 0` (`a−1 ≤ a`).
Division uses Lean's `x/0 = 0` convention. This is the finite inequality the one-step
conditional-expectation bound `step_condExp_le` reduces to (see `notes/.../construction_audit.md`). -/
lemma step_ratio_le (a b : ℕ) :
    (a : ℝ) / (a + b) * (((a : ℝ) - 1) / (1 + b)) +
      (b : ℝ) / (a + b) * ((a : ℝ) / b) ≤ (a : ℝ) / (1 + b) := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · -- b = 0: the `−` branch vanishes, leaving `a − 1 ≤ a`.
    subst hb
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; norm_num
    · have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
      simp only [Nat.cast_zero, add_zero, div_one, zero_div, zero_mul, mul_zero]
      rw [div_self ha0, one_mul]
      linarith
  · -- b ≥ 1: equality (martingale).
    have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    have hab0 : (a : ℝ) + b ≠ 0 := by positivity
    have h1b0 : (1 : ℝ) + b ≠ 0 := by positivity
    apply le_of_eq
    field_simp
    ring

end StatLean.MultipleTesting
