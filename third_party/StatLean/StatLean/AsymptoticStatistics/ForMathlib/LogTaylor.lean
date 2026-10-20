module
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

/-!
Asymptotic Statistics — Taylor remainder for `log(1 + x)` around `0`.

Provides a concrete remainder function `logTaylorRemainder` with

  `Real.log (1 + x) = x − x²/2 + x² · logTaylorRemainder (2 · x)`  (for `x > −1`)

and `logTaylorRemainder → 0` as `u → 0`. This is the form used in the vdV proof
of Theorem 7.2 Step 5, where the `2·x` shift matches the substitution
`x = W_n/2`.

## Contents

* `logTaylorRemainder` — the explicit remainder function.
* `log_one_add_eq_taylor` — the identity.
* `logTaylorRemainder_tendsto_zero` — the rate: `R(u) → 0` as `u → 0`.
-/

open Filter Topology Asymptotics

namespace AsymptoticStatistics
namespace ForMathlib

/-- Explicit second-order Taylor remainder of `log(1 + x)` at `0`, parameterised
so that the identity `log(1 + x) = x − x²/2 + x² · logTaylorRemainder (2 · x)`
holds (for `x > −1`).  Equal to `0` at the origin; elsewhere, the obvious
quotient expression. -/
noncomputable def logTaylorRemainder (u : ℝ) : ℝ :=
  if u = 0 then 0
  else 4 * (Real.log (1 + u / 2) - u / 2 + u ^ 2 / 8) / u ^ 2

@[simp] lemma logTaylorRemainder_zero : logTaylorRemainder 0 = 0 := by
  unfold logTaylorRemainder; simp

/-- **Taylor expansion identity for `log(1 + x)`.**

For every `x > −1`,
  `log(1 + x) = x − x²/2 + x² · logTaylorRemainder (2 · x)`.
(Holds by definition of `logTaylorRemainder`; `x > −1` is needed so `log(1+x)`
is the honest logarithm and not the Mathlib `0`-convention.) -/
lemma log_one_add_eq_taylor {x : ℝ} (hx : -1 < x) :
    Real.log (1 + x) = x - (1 / 2) * x ^ 2 + x ^ 2 * logTaylorRemainder (2 * x) := by
  by_cases hx0 : x = 0
  · subst hx0; simp
  · have h2x_ne : (2 : ℝ) * x ≠ 0 := mul_ne_zero two_ne_zero hx0
    have hx_sq_ne : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
    -- Unfold the remainder at `2 * x`.
    have h_unfold : logTaylorRemainder (2 * x) =
        4 * (Real.log (1 + x) - x + (2 * x) ^ 2 / 8) / (2 * x) ^ 2 := by
      unfold logTaylorRemainder
      rw [if_neg h2x_ne]
      have h_div : (2 * x) / 2 = x := by ring
      rw [h_div]
    rw [h_unfold]
    -- Algebraic identity:
    --   x^2 * (4 * (log(1+x) - x + (2x)²/8) / (2x)²)
    --   = 4 x² (log(1+x) - x + x²/2) / (4 x²)
    --   = log(1+x) - x + x²/2.
    have h_rhs : x ^ 2 * (4 * (Real.log (1 + x) - x + (2 * x) ^ 2 / 8) / (2 * x) ^ 2)
        = Real.log (1 + x) - x + x ^ 2 / 2 := by
      field_simp
      ring
    linarith [h_rhs]

/-- Taylor identity for the logarithm of a nonnegative ratio, written through
the square-root ratio `w = 2 * (√(a / b) - 1)`.  Mathlib's totalized division
and convention `Real.log 0 = 0` make the identity valid also when `a / b = 0`;
then `w = -2` and the explicit remainder supplies the boundary value. -/
lemma log_div_nonneg_eq_sqrt_taylor {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let w := 2 * (Real.sqrt (a / b) - 1)
    Real.log (a / b) = w - w ^ 2 / 4 + w ^ 2 / 2 * logTaylorRemainder w := by
  dsimp only
  have hratio : 0 ≤ a / b := div_nonneg ha hb
  let y := Real.sqrt (a / b)
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = a / b := by
    rw [show y = Real.sqrt (a / b) by rfl, Real.sq_sqrt hratio]
  rcases hy.lt_or_eq with hy_pos | hy_zero
  · have hlog : Real.log (a / b) = 2 * Real.log y := by
      rw [← hy_sq, Real.log_pow]
      ring
    have htaylor := log_one_add_eq_taylor (show -1 < y - 1 by linarith)
    have hone : (1 : ℝ) + (y - 1) = y := by ring
    rw [hone] at htaylor
    rw [hlog, htaylor]
    ring
  · have hy_eq : y = 0 := hy_zero.symm
    have hratio_zero : a / b = 0 := by rw [← hy_sq, hy_eq]; ring
    have hrem : logTaylorRemainder (-2) = 3 / 2 := by
      unfold logTaylorRemainder
      rw [if_neg (by norm_num : (-2 : ℝ) ≠ 0)]
      norm_num [Real.log_zero]
    rw [hratio_zero, Real.log_zero, show Real.sqrt 0 = 0 by simp]
    norm_num [hrem]

/-- **Remainder rate.** `logTaylorRemainder u → 0` as `u → 0`.

Proof uses `Real.abs_log_sub_add_sum_range_le` with `n = 2` and substitution
`x ↦ −u/2`, which gives `|log(1 + u/2) − u/2 + u²/8| ≤ |u/2|³ / (1 − |u/2|)`
for `|u/2| < 1`, i.e. `|u| < 2`.  Dividing by `|u|²/4` yields
`|logTaylorRemainder u| ≤ |u| / (2 − |u|)`, which is bounded by `|u|` for
`|u| ≤ 1` and hence tends to `0`. -/
lemma logTaylorRemainder_tendsto_zero :
    Tendsto logTaylorRemainder (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Choose δ := min ε 1. For |u| < δ, prove |R u| < ε via |R u| ≤ |u|.
  refine Metric.eventually_nhds_iff.mpr ⟨min ε 1, lt_min hε one_pos, fun u hu => ?_⟩
  rw [Real.dist_eq, sub_zero] at hu
  have hu_abs_lt : |u| < ε ∧ |u| < 1 := ⟨lt_of_lt_of_le hu (min_le_left _ _),
    lt_of_lt_of_le hu (min_le_right _ _)⟩
  rw [Real.dist_eq, sub_zero]
  -- Main bound: |R u| ≤ |u|.
  suffices hbd : |logTaylorRemainder u| ≤ |u| from lt_of_le_of_lt hbd hu_abs_lt.1
  by_cases hu0 : u = 0
  · subst hu0; simp
  -- For u ≠ 0: unfold and bound using `abs_log_sub_add_sum_range_le`.
  have h_half_abs : |u / 2| < 1 := by
    rw [abs_div]; simp only [abs_two]; linarith [hu_abs_lt.2]
  -- Mathlib's bound, with x = -(u/2) and n = 2:
  --   |((-u/2) + (-u/2)²/2) + log(1 - (-u/2))| ≤ |u/2|³ / (1 - |u/2|)
  -- i.e. |−u/2 + u²/8 + log(1+u/2)| ≤ |u/2|³ / (1 - |u/2|).
  have h_mathlib := Real.abs_log_sub_add_sum_range_le (x := -(u / 2)) (by rwa [abs_neg]) 2
  -- Unpack the sum and rewrite log(1 - (-u/2)) = log(1 + u/2).
  have h_sum : ∑ i ∈ Finset.range 2, (-(u / 2)) ^ (i + 1) / ((i : ℝ) + 1) =
      -(u / 2) + u ^ 2 / 8 := by
    simp [Finset.sum_range_succ]
    ring
  have h_log : Real.log (1 - -(u / 2)) = Real.log (1 + u / 2) := by ring_nf
  rw [h_sum, h_log] at h_mathlib
  -- h_mathlib : |−(u/2) + u²/8 + log(1 + u/2)| ≤ |u/2|³ / (1 − |u/2|)
  have h_pow : |(-(u / 2))| ^ (2 + 1) = |u| ^ 3 / 8 := by
    rw [abs_neg, abs_div]; simp only [abs_two]; ring
  rw [h_pow] at h_mathlib
  -- Rewrite 1 - |-(u/2)| = 1 - |u|/2 = (2 - |u|)/2.
  have h_denom : 1 - |(-(u / 2))| = (2 - |u|) / 2 := by
    rw [abs_neg, abs_div]; simp only [abs_two]
    ring
  rw [h_denom] at h_mathlib
  -- Rearrange LHS: |−u/2 + u²/8 + log(1+u/2)| = |log(1+u/2) − u/2 + u²/8|.
  have h_lhs_eq :
      |-(u / 2) + u ^ 2 / 8 + Real.log (1 + u / 2)|
        = |Real.log (1 + u / 2) - u / 2 + u ^ 2 / 8| := by
    congr 1; ring
  rw [h_lhs_eq] at h_mathlib
  -- Now bound |R u| = 4 * |log(1+u/2) - u/2 + u²/8| / u².
  unfold logTaylorRemainder
  rw [if_neg hu0]
  have hu_sq_pos : 0 < u ^ 2 := by positivity
  have hu_sq_abs : |u ^ 2| = u ^ 2 := abs_of_pos hu_sq_pos
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), hu_sq_abs]
  -- Goal: 4 * |log(1+u/2) - u/2 + u²/8| / u² ≤ |u|.
  -- Use h_mathlib.
  have h_two_sub_pos : 0 < 2 - |u| := by linarith [hu_abs_lt.2]
  rw [div_le_iff₀ hu_sq_pos]
  calc 4 * |Real.log (1 + u / 2) - u / 2 + u ^ 2 / 8|
      ≤ 4 * (|u| ^ 3 / 8 / ((2 - |u|) / 2)) :=
        mul_le_mul_of_nonneg_left h_mathlib (by norm_num)
    _ = |u| ^ 3 / (2 - |u|) := by field_simp; ring
    _ ≤ |u| ^ 3 / 1 := by
        apply div_le_div_of_nonneg_left (by positivity) one_pos
        linarith [hu_abs_lt.2]
    _ = |u| ^ 3 := by ring
    _ = |u| * |u| ^ 2 := by ring
    _ = |u| * u ^ 2 := by rw [sq_abs]

/-- **Asymptotic form** of the Taylor expansion: the residue
`log(1 + x) − x + x²/2` is `o(x²)` near `0`.

Equivalent to `logTaylorRemainder_tendsto_zero` (and proven from it), but in
the Mathlib-idiomatic `IsLittleO` form. Useful when downstream code needs to
chain asymptotic facts without unpacking the explicit remainder. -/
lemma log_one_add_sub_taylor_isLittleO :
    (fun x : ℝ => Real.log (1 + x) - x + (1 / 2) * x ^ 2) =o[𝓝 (0 : ℝ)]
      (fun x => x ^ 2) := by
  -- Step 1: rewrite the residue as `x² · logTaylorRemainder (2 * x)` near 0.
  have h_eq : (fun x : ℝ => Real.log (1 + x) - x + (1 / 2) * x ^ 2)
                =ᶠ[𝓝 (0 : ℝ)] (fun x => logTaylorRemainder (2 * x) * x ^ 2) := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
    have h := log_one_add_eq_taylor hx
    linarith
  -- Step 2: `logTaylorRemainder (2·) → 0` at `0`.
  have h_smul_tendsto : Tendsto (fun x : ℝ => 2 * x) (𝓝 0) (𝓝 0) := by
    simpa using! (continuous_const.mul continuous_id).tendsto (0 : ℝ)
  have h_R_tendsto :
      Tendsto (fun x : ℝ => logTaylorRemainder (2 * x)) (𝓝 0) (𝓝 0) :=
    logTaylorRemainder_tendsto_zero.comp h_smul_tendsto
  -- Step 3: turn into `=o[𝓝 0] (fun _ => 1)` and multiply by `x²`.
  have h_R_isLittleO :
      (fun x : ℝ => logTaylorRemainder (2 * x)) =o[𝓝 (0 : ℝ)]
        (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_const_iff (by norm_num : (1 : ℝ) ≠ 0)).mpr h_R_tendsto
  have h_sq_isBigO :
      (fun x : ℝ => x ^ 2) =O[𝓝 (0 : ℝ)] (fun x => x ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have h_prod : (fun x : ℝ => logTaylorRemainder (2 * x) * x ^ 2)
      =o[𝓝 (0 : ℝ)] (fun x : ℝ => (1 : ℝ) * x ^ 2) :=
    h_R_isLittleO.mul_isBigO h_sq_isBigO
  have h_simp :
      (fun x : ℝ => (1 : ℝ) * x ^ 2) = (fun x => x ^ 2) := by funext x; ring
  rw [h_simp] at h_prod
  exact h_eq.trans_isLittleO h_prod

end ForMathlib
end AsymptoticStatistics
