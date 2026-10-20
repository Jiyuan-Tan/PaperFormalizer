module
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.RademacherContraction

@[expose] public section

/-!
# Rademacher contraction for clipped squares

The square map clipped at radius `K` is `2 * |K|`-Lipschitz.  Applying the
absolute-supremum Rademacher contraction inequality gives the corresponding
factor-four integral bound for nonnegative radii.
-/

namespace ProbabilityTheory

open MeasureTheory

/-- The square of `x`, clipped at the squared radius `K ^ 2`.

Edge behavior: the radius enters only through its square, so negative radii
give the same function as their absolute values.
-/
def clippedSquare (K x : ℝ) : ℝ := min (x ^ 2) (K ^ 2)

@[simp] theorem clippedSquare_zero (K : ℝ) : clippedSquare K 0 = 0 := by
  rw [clippedSquare, zero_pow (by norm_num : 2 ≠ 0),
    min_eq_left (sq_nonneg K)]

@[simp] theorem clippedSquare_zero_radius (x : ℝ) : clippedSquare 0 x = 0 := by
  rw [clippedSquare, zero_pow (by norm_num : 2 ≠ 0),
    min_eq_right (sq_nonneg x)]

theorem clippedSquare_lipschitz (K x y : ℝ) :
    |clippedSquare K x - clippedSquare K y| ≤ (2 * |K|) * |x - y| := by
  have hrepr (z : ℝ) :
      clippedSquare K z = (min |z| |K|) ^ 2 := by
    by_cases hz : |z| ≤ |K|
    · rw [clippedSquare, min_eq_left hz]
      rw [min_eq_left (sq_le_sq.mpr hz)]
      exact (sq_abs z).symm
    · have hKz : |K| ≤ |z| := le_of_not_ge hz
      rw [clippedSquare, min_eq_right hKz]
      rw [min_eq_right (sq_le_sq.mpr hKz)]
      exact (sq_abs K).symm
  let u := min |x| |K|
  let v := min |y| |K|
  have hu : 0 ≤ u := le_min (abs_nonneg x) (abs_nonneg K)
  have hv : 0 ≤ v := le_min (abs_nonneg y) (abs_nonneg K)
  have huK : u ≤ |K| := min_le_right _ _
  have hvK : v ≤ |K| := min_le_right _ _
  have huv : |u - v| ≤ |(|x| - |y|)| := by
    simpa [u, v] using
      (abs_min_sub_min_le_max |x| |K| |y| |K|)
  have hsum : |u + v| ≤ 2 * |K| := by
    rw [abs_of_nonneg (add_nonneg hu hv)]
    linarith
  rw [hrepr x, hrepr y]
  change |u ^ 2 - v ^ 2| ≤ _
  calc
    |u ^ 2 - v ^ 2| = |u - v| * |u + v| := by
      rw [show u ^ 2 - v ^ 2 = (u - v) * (u + v) by ring, abs_mul]
    _ ≤ |(|x| - |y|)| * (2 * |K|) :=
      mul_le_mul huv hsum (abs_nonneg _) (abs_nonneg _)
    _ ≤ |x - y| * (2 * |K|) :=
      mul_le_mul_of_nonneg_right (abs_abs_sub_abs_le_abs_sub x y) (by positivity)
    _ = (2 * |K|) * |x - y| := by ring

set_option linter.unusedFintypeInType false in
theorem integral_iSup_abs_rademacherSum_clippedSquare_le
    {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → Fin n → ℝ) (K : ℝ) (hK : 0 ≤ K) :
    ∫ ε, ⨆ j, |rademacherSum (fun k => clippedSquare K (a j k)) ε|
        ∂rademacherCube n ≤
      4 * K * ∫ ε, ⨆ j, |rademacherSum (a j) ε| ∂rademacherCube n := by
  calc
    _ ≤ 2 * (2 * |K|) *
        ∫ ε, ⨆ j, |rademacherSum (a j) ε| ∂rademacherCube n :=
      integral_iSup_abs_rademacherSum_comp_le a
        (fun _ => clippedSquare K) (2 * |K|)
        (fun _ => clippedSquare_zero K)
        (fun _ => clippedSquare_lipschitz K)
    _ = 4 * K * ∫ ε, ⨆ j, |rademacherSum (a j) ε| ∂rademacherCube n := by
      rw [abs_of_nonneg hK]
      ring

end ProbabilityTheory
