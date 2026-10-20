module
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Order statistics of a finite real tuple — `ForMathlib` layer

Theorem-agnostic bricks (pure math, Mathlib-only) used by the Benjamini–Hochberg and Holm
assembly files: the order statistics `v₍₀₎ ≤ v₍₁₎ ≤ ⋯` of a tuple `v : Fin n → ℝ`, built from
Mathlib's `Tuple.sort` (the permutation that sorts `v`).

`orderStat v i = v (Tuple.sort v i)` is the `i`-th smallest entry; `orderStat_monotone` records
that `i ↦ orderStat v i` is monotone. These let the assembly files write the BH cutoff
`p₍ᵢ₎ ≤ iα/N` and the Holm step-down cutoffs against sorted p-values.
-/

namespace StatLean.MultipleTesting

variable {n : ℕ}

/-- The `i`-th order statistic (i.e. `i`-th smallest entry) of a real tuple `v : Fin n → ℝ`,
defined as `v` precomposed with the sorting permutation `Tuple.sort v`. -/
noncomputable def orderStat (v : Fin n → ℝ) (i : Fin n) : ℝ := v (Tuple.sort v i)

/-- The map `i ↦ orderStat v i` is monotone: `orderStat` lists the entries in non-decreasing
order. -/
theorem orderStat_monotone (v : Fin n → ℝ) : Monotone (orderStat v) := by
  unfold orderStat
  exact Tuple.monotone_sort v

end StatLean.MultipleTesting
