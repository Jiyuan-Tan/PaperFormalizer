import Mathlib

/-!
# Schur's inequality

Classical polynomial inequalities for nonnegative reals.
-/

namespace Toolkit.Foundations.Algebra

/-- **Schur's inequality** (exponent 1). For all real numbers `a, b, c ≥ 0`,
`a(a-b)(a-c) + b(b-a)(b-c) + c(c-a)(c-b) ≥ 0`.
Hardy, Littlewood and Pólya, *Inequalities*, Theorem 1. -/
theorem schur_inequality {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac <;>
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc,
      mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hbc), mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hac),
      mul_nonneg (sub_nonneg.2 hbc) (sub_nonneg.2 hac)]

end Toolkit.Foundations.Algebra
