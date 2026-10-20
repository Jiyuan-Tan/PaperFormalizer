module
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-!
# Tail bounds for p-series

Summability and an explicit tail estimate for `∑_{m ≥ n} m^{−s}`, `s > 1`:
$$ \sum_{m \ge n} m^{-s} \;\le\; \frac{s}{s-1}\,(n-1)^{1-s} \qquad (n \ge 2). $$

Used to bound the aliasing residual of trigonometric coefficient estimates over Sobolev
ellipsoids (Cauchy–Schwarz turns an ellipsoid membership into a weighted tail `∑ a_m^{-2}`).

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.7.2 ($p$-series tail bounds used in Lemma 1.8
and Theorem 1.9).

**Proof formalization notes.** Standard integral test: `m^{-s} ≤ ∫_{m-1}^m x^{-s} dx` and
summation (`AntitoneOn.sum_le_integral`-style comparison, or directly via Mathlib's
`sum_rpow`-comparison lemmas if present on the pin); the stated constant `s/(s−1)` is
deliberately generous (the sharp integral-test constant is `1/(s−1)`).

**Bibliographic comments.** Classical (Euler; Maclaurin–Cauchy integral test).
-/

open MeasureTheory Set intervalIntegral

namespace StatLean.NonparametricStatistics

/-- Summability of the shifted p-series `m ↦ (n + m)^{−s}` for `s > 1`. -/
theorem summable_nat_add_rpow_neg {s : ℝ} (hs : 1 < s) (n : ℕ) :
    Summable fun m : ℕ => ((n + m : ℕ) : ℝ) ^ (-s) := by
  have hb : Summable (fun m : ℕ => (m : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  refine ((summable_nat_add_iff n).mpr hb).congr (fun m => ?_)
  rw [Nat.add_comm m n]

/-- **Tail estimate for p-series**: for `s > 1` and `n ≥ 2`,
`∑_{m≥n} m^{−s} = ∑_{k:ℕ} (n+k)^{−s} ≤ (s/(s−1))·(n−1)^{1−s}`. -/
theorem tsum_nat_add_rpow_neg_le {s : ℝ} (hs : 1 < s) {n : ℕ}
    -- LEAN-ONLY: `n ≥ 2` keeps `(n−1)^{1−s}` a genuine positive power; consumers apply this
    -- with large `n`
    (hn : 2 ≤ n) :
    (∑' m : ℕ, ((n + m : ℕ) : ℝ) ^ (-s)) ≤ s / (s - 1) * ((n : ℝ) - 1) ^ (1 - s) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  -- abbreviations for the two boundary powers
  set A : ℝ := ((n : ℝ) - 1) ^ (1 - s) with hA
  have hAnn : 0 ≤ A := Real.rpow_nonneg hpos.le _
  refine Real.tsum_le_of_sum_range_le
    (fun m => Real.rpow_nonneg (by positivity) _) (fun M => ?_)
  -- antitonicity of `x ↦ x^(-s)` on the relevant interval
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Icc ((n : ℝ) - 1) ((n : ℝ) - 1 + M)) := by
    intro x hx y _ hxy
    have hx0 : 0 < x := lt_of_lt_of_le hpos hx.1
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hsum := hanti.sum_le_integral
  -- rewrite the summand into the target `(n+i)^(-s)` shape
  have hLHS : (∑ i ∈ Finset.range M, (fun x : ℝ => x ^ (-s)) ((n : ℝ) - 1 + ((i + 1 : ℕ) : ℝ)))
      = ∑ i ∈ Finset.range M, ((n + i : ℕ) : ℝ) ^ (-s) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : ((n : ℝ) - 1 + ((i + 1 : ℕ) : ℝ)) = ((n + i : ℕ) : ℝ) := by push_cast; ring
    simp only [this]
  rw [hLHS] at hsum
  -- evaluate the comparison integral in closed form
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  set B : ℝ := ((n : ℝ) - 1 + (M : ℝ)) ^ (1 - s) with hB
  have hBnn : 0 ≤ B := Real.rpow_nonneg (by linarith) _
  have hint : (∫ x in ((n : ℝ) - 1)..((n : ℝ) - 1 + M), x ^ (-s)) = (B - A) / (1 - s) := by
    rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
    · simp only [neg_add_eq_sub]; rw [← hA, ← hB]
    · -- `0 ∉ [[n-1, n-1+M]]`
      simp only [Set.uIcc_of_le (by linarith :
        (n : ℝ) - 1 ≤ (n : ℝ) - 1 + M), Set.mem_Icc, not_and, not_le]
      intro _; linarith
  refine hsum.trans ?_
  rw [hint]
  -- `(B - A)/(1 - s) ≤ s/(s-1) * A`
  have hrw : (B - A) / (1 - s) = (A - B) / (s - 1) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  rw [hrw]
  have h1 : (A - B) / (s - 1) ≤ A / (s - 1) :=
    (div_le_div_iff_of_pos_right hs1).mpr (by linarith)
  refine h1.trans ?_
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hs1).mpr (by nlinarith)

end StatLean.NonparametricStatistics
