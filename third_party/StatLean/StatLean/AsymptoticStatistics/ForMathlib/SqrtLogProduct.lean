module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

/-!
# Entropy bookkeeping for the chaining argument: product-salvage and dyadic rearrangement

Two purely analytic facts used in van der Vaart, *Asymptotic Statistics*,
§19.6 p.286-287 (proof of Lemma 19.34), where the nested-partition
construction blows the level-`q` cell count up to a product
`N_q ≤ ∏_{p ∈ [q₀, q]} N_p`. The textbook salvages the entropy bookkeeping
through two moves:

1. **Product-salvage** (`Real.sqrt_log_prod_le_sum`, `Real.sqrt_log_prod_le_sum_one_add`):
   `√(log (∏ N_p)) ≤ ∑ √(log N_p)`, and the `1 +`-regularized variant
   `√(log (1 + ∏ N_p)) ≤ ∑ √(log (1 + N_p))` matching the `1 +` entropy weight.
   This is subadditivity of `t ↦ √t` on a finite sum of nonnegative logarithms,
   after `Real.log_prod` turns the log of a product into a sum of logs (and, for
   the `1 +` form, `1 + ∏ N_p ≤ ∏ (1 + N_p)` via `one_add_prod_le_prod_one_add`).
   The edge case `N_p = 0` holds with no positivity hypothesis: the bare form has
   `log 0 = 0` so the LHS `= 0`; the `1 +` form is regularized to `log 1 = 0`.

2. **Dyadic rearrangement** (`ENNReal.tsum_pow_half_sum_Icc_le`): in `ℝ≥0∞`,
   `∑'_q (2⁻¹)^q · (∑_{p ∈ [q₀, q]} a_p) ≤ 2 · ∑'_p (2⁻¹)^p · a_p`. vdV's
   "rearranging the sums" step: swap the order of summation (`ENNReal.tsum_comm`),
   then bound the inner geometric tail `∑_{q ≥ p} (2⁻¹)^q = 2 · (2⁻¹)^p`. The
   constant `2` is exact (equality on a point mass `a = δ_{p₀}`).

These sit between `NestedBracketPartition.card_le`
(`StatLean/AsymptoticStatistics/EmpiricalProcess/NestedPartition.lean`) and the dyadic
entropy series of `StatLean/AsymptoticStatistics/EmpiricalProcess/Bracketing.lean`.

Reference: vdV §19.6 p.286-287.
-/

open scoped BigOperators ENNReal

namespace AsymptoticStatistics.ForMathlib

/-! ## Two-term and finite-sum subadditivity of `√` -/

/-- Subadditivity of `√` on two nonnegative reals: `√(a + b) ≤ √a + √b`.
(`Real.sqrt_add_le_sqrt_add_sqrt` does not exist in Mathlib; we prove it inline
by squaring.) -/
theorem Real.sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsum : (0 : ℝ) ≤ Real.sqrt a + Real.sqrt b :=
    add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  rw [show a + b = Real.sqrt a ^ 2 + Real.sqrt b ^ 2 by
        rw [Real.sq_sqrt ha, Real.sq_sqrt hb]]
  -- `√(x² + y²) ≤ √((x + y)²) = x + y`
  calc Real.sqrt (Real.sqrt a ^ 2 + Real.sqrt b ^ 2)
      ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq hsum

/-- Subadditivity of `√` over a finite sum of nonnegative reals:
`√(∑ f i) ≤ ∑ √(f i)`. -/
theorem Real.sqrt_sum_le {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have ha0 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hs0 : 0 ≤ ∑ i ∈ s, f i :=
        Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
      refine (Real.sqrt_add_le ha0 hs0).trans ?_
      gcongr
      exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

/-! ## Product-salvage: `√(log (∏ N_p)) ≤ ∑ √(log N_p)` -/

/-- **Product-salvage (real form).** For naturals `N : ι → ℕ` with `1 ≤ N i`
on `s` (so each `log (N i) ≥ 0`),
`√(log (∏_{i ∈ s} N i)) ≤ ∑_{i ∈ s} √(log (N i))`.

vdV §19.6 p.286: the entropy salvage `(∑ log N_p)^{1/2} ≤ ∑ (log N_p)^{1/2}`. -/
theorem Real.sqrt_log_prod_le_sum {ι : Type*} (s : Finset ι) {N : ι → ℕ}
    (hN : ∀ i ∈ s, 1 ≤ N i) :
    Real.sqrt (Real.log (∏ i ∈ s, (N i : ℝ)))
      ≤ ∑ i ∈ s, Real.sqrt (Real.log (N i : ℝ)) := by
  have hlog : Real.log (∏ i ∈ s, (N i : ℝ)) = ∑ i ∈ s, Real.log (N i : ℝ) := by
    apply Real.log_prod
    intro i hi
    have : (1 : ℝ) ≤ (N i : ℝ) := by exact_mod_cast hN i hi
    positivity
  rw [hlog]
  apply Real.sqrt_sum_le
  intro i hi
  apply Real.log_nonneg
  exact_mod_cast hN i hi

/-- **Product-salvage, `N i ≠ 0` form.** The same bound stated with the
nonvanishing hypothesis `N i ≠ 0` (equivalent to `1 ≤ N i` for naturals),
which is the shape the chaining caller has on hand: per-level cover
cardinalities are `≥ 1` whenever `F` is nonempty. -/
theorem Real.sqrt_log_prod_le_sum' {ι : Type*} (s : Finset ι) {N : ι → ℕ}
    (hN : ∀ i ∈ s, N i ≠ 0) :
    Real.sqrt (Real.log (∏ i ∈ s, (N i : ℝ)))
      ≤ ∑ i ∈ s, Real.sqrt (Real.log (N i : ℝ)) :=
  Real.sqrt_log_prod_le_sum s fun i hi => Nat.one_le_iff_ne_zero.mpr (hN i hi)

/-- **`1 +`-regularized product bound.** `1 + ∏_{p ∈ s} N_p ≤ ∏_{p ∈ s} (1 + N_p)`
for nonnegative reals `N_p` over a **nonempty** `s`. Expanding the right product
gives `1 + ∏ N_p` plus a sum of nonnegative cross terms, so the inequality is an
instance of "dropping the extra nonnegative mass". Proved by induction on a
nonempty `Finset` (`Finset.Nonempty.cons_induction`): the base singleton is an
equality `1 + N a = 1 + N a`, and the inductive step uses
`(1 + a)(1 + ∏) = 1 + ∏ + a + a·∏ ≥ 1 + a·∏`.

The nonemptiness is essential: on `s = ∅` both products are `1`, giving the false
`2 ≤ 1`. All chaining callers use `s = Icc q₀ q` with `q₀ ≤ q`, hence nonempty. -/
theorem one_add_prod_le_prod_one_add {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {N : ι → ℝ} (hN : ∀ i ∈ s, 0 ≤ N i) :
    1 + ∏ i ∈ s, N i ≤ ∏ i ∈ s, (1 + N i) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
      rw [Finset.prod_cons, Finset.prod_cons]
      have ha0 : 0 ≤ N a := hN a (Finset.mem_cons_self a s)
      have hprod_nonneg : 0 ≤ ∏ i ∈ s, N i :=
        Finset.prod_nonneg fun i hi => hN i (Finset.mem_cons.mpr (Or.inr hi))
      have hih : 1 + ∏ i ∈ s, N i ≤ ∏ i ∈ s, (1 + N i) :=
        ih fun i hi => hN i (Finset.mem_cons.mpr (Or.inr hi))
      -- `1 + N a * ∏ N ≤ (1 + N a) * (1 + ∏ N) ≤ (1 + N a) * ∏ (1 + N)`
      calc 1 + N a * ∏ i ∈ s, N i
          ≤ (1 + N a) * (1 + ∏ i ∈ s, N i) := by nlinarith [hprod_nonneg, ha0]
        _ ≤ (1 + N a) * ∏ i ∈ s, (1 + N i) := by
            apply mul_le_mul_of_nonneg_left hih (by linarith)

/-- **`1 +`-regularized product-salvage.** For naturals `N : ι → ℕ` over a
**nonempty** `s`, `√(log (1 + ∏_{i ∈ s} N i)) ≤ ∑_{i ∈ s} √(log (1 + N i))`. This
is the regularized form of `Real.sqrt_log_prod_le_sum` matching the `1 +` entropy
weight `entropyWeight N = √(log (1 + N))`.

Proof: `1 + ∏ N_p ≤ ∏ (1 + N_p)` (`one_add_prod_le_prod_one_add`, needs `s`
nonempty), then `log` monotone (both sides `≥ 1`), then
`log (∏ (1 + N_p)) = ∑ log (1 + N_p)` (`Real.log_prod`, each factor `≥ 1 > 0`),
then `√` subadditive over the finite sum (`Real.sqrt_sum_le`, each summand
`log (1 + N_p) ≥ 0`).

The nonemptiness is essential (on `s = ∅` the LHS is `√(log 2) > 0` but the RHS is
`0`). All chaining callers index over `Icc q₀ q` with `q₀ ≤ q`, hence nonempty.

vdV §19.6 p.286-287: the entropy salvage with the Lemma 19.33 `1 +` regularizer. -/
theorem Real.sqrt_log_prod_le_sum_one_add {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) (N : ι → ℕ) :
    Real.sqrt (Real.log (1 + ∏ i ∈ s, (N i : ℝ)))
      ≤ ∑ i ∈ s, Real.sqrt (Real.log (1 + (N i : ℝ))) := by
  have hN_nonneg : ∀ i ∈ s, (0 : ℝ) ≤ (N i : ℝ) := fun i _ => Nat.cast_nonneg _
  -- Step 1: `1 + ∏ N_p ≤ ∏ (1 + N_p)`, then `log` is monotone.
  have hprod_le : 1 + ∏ i ∈ s, (N i : ℝ) ≤ ∏ i ∈ s, (1 + (N i : ℝ)) :=
    one_add_prod_le_prod_one_add hs hN_nonneg
  have hprod_pos : (0 : ℝ) < 1 + ∏ i ∈ s, (N i : ℝ) := by
    have : (0 : ℝ) ≤ ∏ i ∈ s, (N i : ℝ) := Finset.prod_nonneg hN_nonneg
    linarith
  have hlog_le : Real.log (1 + ∏ i ∈ s, (N i : ℝ))
      ≤ Real.log (∏ i ∈ s, (1 + (N i : ℝ))) := Real.log_le_log hprod_pos hprod_le
  refine (Real.sqrt_le_sqrt hlog_le).trans ?_
  -- Step 2: `log (∏ (1 + N_p)) = ∑ log (1 + N_p)`.
  have hlog_prod : Real.log (∏ i ∈ s, (1 + (N i : ℝ)))
      = ∑ i ∈ s, Real.log (1 + (N i : ℝ)) := by
    apply Real.log_prod
    intro i _
    have : (0 : ℝ) ≤ (N i : ℝ) := Nat.cast_nonneg _
    positivity
  rw [hlog_prod]
  -- Step 3: `√` subadditive over the finite sum (each summand `≥ 0`).
  apply Real.sqrt_sum_le
  intro i _
  apply Real.log_nonneg
  have : (0 : ℝ) ≤ (N i : ℝ) := Nat.cast_nonneg _
  linarith

/-! ## Dyadic rearrangement in `ℝ≥0∞` -/

/-- The geometric tail `∑'_{q} (2⁻¹)^q · ⟦p ∈ Icc q₀ q⟧` collapses, for
`q₀ ≤ p`, to `2 · (2⁻¹)^p`: the indicator is `1` exactly when `q ≥ p`, and
`∑_{q ≥ p} (2⁻¹)^q = (2⁻¹)^p · ∑_{j} (2⁻¹)^j = 2 · (2⁻¹)^p`. We only need the
`≤` direction. -/
private lemma tsum_half_pow_indicator_le {q₀ p : ℕ} :
    (∑' q : ℕ, if p ∈ Finset.Icc q₀ q then (2⁻¹ : ℝ≥0∞) ^ q else 0)
      ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ p := by
  -- Drop the lower bound `q₀ ≤ p` from the indicator (it only shrinks the sum).
  have hdrop : (∑' q : ℕ, if p ∈ Finset.Icc q₀ q then (2⁻¹ : ℝ≥0∞) ^ q else 0)
      ≤ ∑' q : ℕ, if p ≤ q then (2⁻¹ : ℝ≥0∞) ^ q else 0 := by
    apply ENNReal.tsum_le_tsum
    intro q
    by_cases hmem : p ∈ Finset.Icc q₀ q
    · rw [if_pos hmem, if_pos (Finset.mem_Icc.mp hmem).2]
    · rw [if_neg hmem]; positivity
  refine hdrop.trans ?_
  -- Reindex `q = p + j`: `∑_{q ≥ p} (2⁻¹)^q = ∑_j (2⁻¹)^{p + j}`.
  have hinj : Function.Injective (fun j : ℕ => p + j) := fun a b h => by
    simpa using Nat.add_left_cancel h
  have hsupp : (Function.support fun q => if p ≤ q then (2⁻¹ : ℝ≥0∞) ^ q else 0)
      ⊆ Set.range (fun j : ℕ => p + j) := by
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    by_cases hpq : p ≤ q
    · exact ⟨q - p, Nat.add_sub_cancel' hpq⟩
    · rw [if_neg hpq] at hq; exact absurd rfl hq
  have hreindex : (∑' q : ℕ, if p ≤ q then (2⁻¹ : ℝ≥0∞) ^ q else 0)
      = ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (p + j) := by
    rw [← hinj.tsum_eq hsupp]
    refine tsum_congr fun j => ?_
    rw [if_pos (Nat.le_add_right p j)]
  rw [hreindex]
  -- `∑_j (2⁻¹)^{p+j} = (2⁻¹)^p · ∑_j (2⁻¹)^j = (2⁻¹)^p · 2`.
  simp_rw [pow_add]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two, mul_comm]

/-- **Dyadic rearrangement (vdV "rearranging the sums").** In `ℝ≥0∞`, for any
`a : ℕ → ℝ≥0∞` and any `q₀`,
`∑'_q (2⁻¹)^q · (∑_{p ∈ [q₀, q]} a_p) ≤ 2 · ∑'_p (2⁻¹)^p · a_p`.

The constant `2` is exact: equality holds on a point mass `a = δ_{p₀}` with
`q₀ ≤ p₀`. Proof: push `(2⁻¹)^q` into the inner finite sum, swap the order of
summation, and collapse the inner geometric tail (`tsum_half_pow_indicator_le`).

vdV §19.6 p.286-287. -/
theorem ENNReal.tsum_pow_half_sum_Icc_le (q₀ : ℕ) (a : ℕ → ℝ≥0∞) :
    (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc q₀ q, a p))
      ≤ 2 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by
  -- Rewrite each term as a double sum over all `p`, with an `Icc` indicator.
  have hterm : ∀ q : ℕ,
      (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc q₀ q, a p)
        = ∑' p : ℕ, (if p ∈ Finset.Icc q₀ q then (2⁻¹ : ℝ≥0∞) ^ q else 0) * a p := by
    intro q
    rw [Finset.mul_sum, sum_eq_tsum_indicator]
    refine tsum_congr fun p => ?_
    rw [Set.indicator_apply]
    by_cases hp : p ∈ (Finset.Icc q₀ q : Set ℕ)
    · rw [if_pos hp, if_pos (by simpa using hp)]
    · rw [if_neg hp, if_neg (by simpa using hp), zero_mul]
  simp_rw [hterm]
  -- Swap the order of summation.
  rw [ENNReal.tsum_comm]
  -- Now bound the inner `q`-tail for each `p`.
  calc (∑' p : ℕ, ∑' q : ℕ,
          (if p ∈ Finset.Icc q₀ q then (2⁻¹ : ℝ≥0∞) ^ q else 0) * a p)
      = ∑' p : ℕ,
          (∑' q : ℕ, if p ∈ Finset.Icc q₀ q then (2⁻¹ : ℝ≥0∞) ^ q else 0) * a p := by
        refine tsum_congr fun p => ?_
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∑' p : ℕ, (2 * (2⁻¹ : ℝ≥0∞) ^ p) * a p := by
        apply ENNReal.tsum_le_tsum
        intro p
        gcongr
        exact tsum_half_pow_indicator_le
    _ = 2 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun p => ?_
        ring

end AsymptoticStatistics.ForMathlib
