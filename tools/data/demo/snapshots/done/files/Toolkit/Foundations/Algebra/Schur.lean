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

/-- A cubic inequality from Schur's inequality. For all real numbers `a, b, c ≥ 0`,
`(a+b+c)^3 + 9abc ≥ 4(a+b+c)(ab+bc+ca)`. -/
theorem cubic_ge_of_schur {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    4 * (a + b + c) * (a * b + b * c + c * a) ≤ (a + b + c) ^ 3 + 9 * a * b * c := by
  nlinarith [schur_inequality ha hb hc]

end Toolkit.Foundations.Algebra
