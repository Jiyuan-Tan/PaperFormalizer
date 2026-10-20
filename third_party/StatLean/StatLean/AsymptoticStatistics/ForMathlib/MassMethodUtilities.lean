module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

/-!
Pure-`ℝ` and pure-topology utilities for the mass-method
(point-mass) verification entry point.

These three lemmas isolate the algebraic and filter-arithmetic
content out of `Core/MassMethod.lean`'s measure-theoretic units, so
that Lemma 1's QMD construction and Theorem 1's bridge proof do not
have to fight `ENNReal.ofReal` non-negativity gymnastics or filter
hierarchy bookkeeping inline.

The three lemmas:
- `ENNReal_ofReal_mixture` — `1 + t·g = (1−t) + t·(1+g)` lifted to
  `ENNReal` with the appropriate non-negativity side conditions.
- `dqm_integrand_bound` — absolute-value bound
  `|√(1+tu) − 1 − (t/2)u| ≤ t² u² / 2` from the conjugate identity.
- `nhdsWithin_Ioi_le_compl_zero` — `𝓝[>] 0 ≤ 𝓝[≠] 0` for filter
  alignment between QMD-curve and mixture-Gâteaux Tendsto.
-/

open Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.ForMathlib.MassMethodUtilities

/-! ## ENNReal mixture decomposition -/

/-- Algebraic-quarantine lemma: `1 + t·g = (1−t) + t·(1+g)` lifted to
`ENNReal` via `ofReal`, with the non-negativity side conditions made
explicit (`0 ≤ t ≤ 1`, `g ≥ -1`) so `ENNReal.ofReal_add` /
`ENNReal.ofReal_mul` apply directly without negative-part splitting. -/
lemma ENNReal_ofReal_mixture {t g : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hg : -1 ≤ g) :
    ENNReal.ofReal (1 + t * g) =
      ENNReal.ofReal (1 - t) + ENNReal.ofReal t * ENNReal.ofReal (1 + g) := by
  have h_split : (1 + t * g : ℝ) = (1 - t) + t * (1 + g) := by ring
  have h_nonneg₁ : 0 ≤ 1 - t := by linarith
  have h_nonneg₂ : 0 ≤ 1 + g := by linarith
  have h_nonneg₃ : 0 ≤ t * (1 + g) := mul_nonneg ht₀ h_nonneg₂
  rw [h_split, ENNReal.ofReal_add h_nonneg₁ h_nonneg₃,
      ENNReal.ofReal_mul ht₀]

/-! ## DQM-integrand absolute-value bound -/

/-- Pure-`ℝ` algebraic Lipschitz bound for the DQM integrand:
`|√(1+t·u) − 1 − (t/2)·u| ≤ t²·u² / 2` for `t ∈ Ioo 0 1` and `u ≥ -1`.

Proof: the conjugate identity
`√(1+tu) − 1 = tu / (√(1+tu) + 1)` rearranges
`√(1+tu) − 1 − (t/2)u = -t²u² / [2 (√(1+tu)+1)²]`,
and the denominator is at least `2`, giving the absolute-value bound.

This is the "absolute pointwise bound" form (mass-method plan,
Risk-1 mitigation): scaling linearly in `t²` rather than using a
squared bound. Integrating against `P` then yields
`eLpNorm² LSE 2 P ≤ t⁴·M⁴/4`, hence `eLpNorm² LSE 2 P / t² → 0`,
satisfying the QMD condition. -/
lemma dqm_integrand_bound {t u : ℝ}
    (ht_pos : 0 < t) (ht_lt : t < 1) (hu : -1 ≤ u) :
    |Real.sqrt (1 + t * u) - 1 - (t / 2) * u| ≤ t ^ 2 * u ^ 2 / 2 := by
  -- Set `s := √(1+t·u)`. Then `s² = 1+t·u`, so `t·u = s² - 1`.
  -- Algebraic key fact:
  --   `s - 1 - (t/2)·u = s - 1 - (s²-1)/2 = -(s-1)²/2`.
  -- Bound:
  --   `|LHS| = (s-1)²/2`. We need `(s-1)² ≤ t²u² = (s²-1)² = (s-1)²·(s+1)²`.
  -- This holds iff `(s+1)² ≥ 1`, which holds since `s ≥ 0` ⇒ `s+1 ≥ 1`.
  have h_pos : 0 < 1 + t * u := by nlinarith
  have h_nonneg : 0 ≤ 1 + t * u := le_of_lt h_pos
  set s := Real.sqrt (1 + t * u) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s * s = 1 + t * u := Real.mul_self_sqrt h_nonneg
  -- Identity: s - 1 - (t/2)·u = -(s-1)²/2.
  have h_lhs_eq : s - 1 - (t / 2) * u = -((s - 1) ^ 2) / 2 := by
    have h_tu : t * u = s * s - 1 := by linarith [hs_sq]
    nlinarith [h_tu, sq_nonneg (s - 1)]
  rw [h_lhs_eq]
  -- Goal: |-(s-1)²/2| ≤ t²u²/2.
  rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (sq_nonneg _)]
  -- Goal: (s-1)²/2 ≤ t²u²/2.
  -- Multiply by 2: (s-1)² ≤ t²u².
  have h_step : (s - 1) ^ 2 ≤ t ^ 2 * u ^ 2 := by
    -- t²u² = (tu)² = (s² - 1)² = ((s-1)(s+1))² = (s-1)²·(s+1)².
    have h_tu_sq : t ^ 2 * u ^ 2 = (s - 1) ^ 2 * (s + 1) ^ 2 := by
      have h_tu : t * u = s * s - 1 := by linarith [hs_sq]
      have : (s * s - 1) = (s - 1) * (s + 1) := by ring
      nlinarith [h_tu, this, sq_nonneg ((s - 1) * (s + 1))]
    rw [h_tu_sq]
    have h_splus_one : (1 : ℝ) ≤ (s + 1) ^ 2 := by nlinarith [hs_nonneg]
    have h_lhs_nn : 0 ≤ (s - 1) ^ 2 := sq_nonneg _
    nlinarith [h_lhs_nn, h_splus_one]
  linarith [h_step]

/-! ## Filter alignment -/

/-- `𝓝[>] 0 ≤ 𝓝[≠] 0` as filters on `ℝ`. Used to convert a Tendsto
on the QMD-curve filter `nhdsWithin 0 ({0}ᶜ)` to a Tendsto on the
mixture-Gâteaux filter `nhdsWithin 0 (Set.Ioi 0)`. -/
lemma nhdsWithin_Ioi_le_compl_zero :
    nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin 0 ({0}ᶜ) :=
  nhdsWithin_mono 0 (fun _ ht => ne_of_gt ht)

end AsymptoticStatistics.ForMathlib.MassMethodUtilities
