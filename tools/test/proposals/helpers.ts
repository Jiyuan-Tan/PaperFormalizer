// Shared fixtures for the promotion-round tests (not a test file itself).

/** A paper module for the round-B move tests: a definition, helpers, column-0 equations, a headline. */
export const PAPER_MAIN = `module

public import Mathlib.Tactic.Ring

/-!
# Fixture
-/

@[expose] public section

namespace Papers.Fix

open Nat

variable (k : ℕ) {m : ℕ} (P : Papers.Fix.Setup)

/-- The sum of a number with itself. -/
def twice (n : ℕ) : ℕ := n + n

/-- Adding a number to itself is multiplying it by two. -/
@[simp]
theorem twice_eq_two_mul (n : ℕ) : twice n = 2 * n := by
  unfold twice; ring

theorem uses_k : k ≤ k + 1 := Nat.le_succ k

open Finset in
theorem sq_le_sq_of_le {a b : ℕ} (h : a ≤ b) : a * a ≤ b * b :=
  Nat.mul_le_mul h h

def f : ℕ → ℕ
| 0 => 1
| n + 1 => twice (f n)

/-- Headline. -/
theorem main_result {a b : ℕ} (h : a ≤ b) : twice (a * a) ≤ 2 * (b * b) := by
  rw [twice_eq_two_mul]
  exact Nat.mul_le_mul_left 2 (Papers.Fix.sq_le_sq_of_le h)

end Papers.Fix
`;
