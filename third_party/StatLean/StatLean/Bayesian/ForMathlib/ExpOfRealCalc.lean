module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

/-!
# `ENNReal`-valued exponential calculus and a Gaussian-type series bound

Elementary `ℝ≥0∞` book-keeping for the term `ENNReal.ofReal (Real.exp ·)` —
positivity, finiteness, monotonicity, the additive law for products, and division
by an exponential — together with the two analytic facts the DL series endgame
needs:

* `tsum_ofReal_exp_neg_sq_le` — a Gaussian-type tail series
  `∑_{j≥0} exp(−c(M+j)²K)` is dominated by twice its first term, once the first
  inter-term gap forces the ratio below `1/2`.
* `tendsto_ofReal_exp_neg` — `ofReal (exp (−εₙ)) → 0` whenever `εₙ → ∞`.

**Reference.** Mathlib-level bricks (no book statement of their own) consumed by the
Dirichlet–Laplace posterior-contraction proof (Bhattacharya–Pati–Pillai–Dunson,
*Dirichlet–Laplace priors for optimal shrinkage*, JASA 2015 / arXiv:1401.5398;
tag `BPPD §X.Y`): they carry the `ℝ≥0∞` ratio algebra and the shell-sum bookkeeping
`∑_S ∑_{j≥M} ∑_i (1+β) exp(−j²r²/12) → 0` of Theorems 3.1 / 3.4 (§6).

**Proof formalization notes.** The five algebra lemmas are short consequences of
`ENNReal.ofReal_mul` / `ENNReal.ofReal_lt_top` / `ENNReal.ofReal_le_ofReal_iff`
together with `Real.exp_add` / `Real.exp_pos`; `tsum_ofReal_exp_neg_sq_le`
geometric-dominates the summand by comparing consecutive terms — the gap
`(M+j+1)² − (M+j)² ≥ 2M+1` gives ratio `≤ exp(−cK(2M+1)) ≤ 1/2` — and sums the
resulting geometric series (`ENNReal.tsum_geometric`); `tendsto_ofReal_exp_neg`
composes `Real.tendsto_exp_atBot` with the continuity of `ENNReal.ofReal` at `0`.

**Bibliographic comments.** Geometric domination of a Gaussian tail sum by its
leading term is standard elementary analysis.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- `ENNReal.ofReal (Real.exp x)` is strictly positive (the exponential is). -/
lemma ofReal_exp_pos (x : ℝ) : 0 < ENNReal.ofReal (Real.exp x) :=
  ENNReal.ofReal_pos.mpr (Real.exp_pos x)

/-- `ENNReal.ofReal (Real.exp x)` is finite (it is the image of a real under
`ENNReal.ofReal`). -/
lemma ofReal_exp_ne_top (x : ℝ) : ENNReal.ofReal (Real.exp x) ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- Monotonicity transfer: `ofReal (exp x) ≤ ofReal (exp y) ↔ x ≤ y` (exponentials
are positive, so `ENNReal.ofReal` neither clamps nor loses order). -/
lemma ofReal_exp_le_iff (x y : ℝ) :
    ENNReal.ofReal (Real.exp x) ≤ ENNReal.ofReal (Real.exp y) ↔ x ≤ y := by
  rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos y).le, Real.exp_le_exp]

/-- The additive law for a product of exponentials in `ℝ≥0∞`:
`ofReal (exp x) * ofReal (exp y) = ofReal (exp (x + y))`. -/
lemma ofReal_exp_mul (x y : ℝ) :
    ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (Real.exp y)
      = ENNReal.ofReal (Real.exp (x + y)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos x).le, ← Real.exp_add]

/-- Division by an exponential is multiplication by its reciprocal exponential:
`a / ofReal (exp x) = a * ofReal (exp (−x))`. -/
lemma div_ofReal_exp_neg (a : ℝ≥0∞) (x : ℝ) :
    a / ENNReal.ofReal (Real.exp x) = a * ENNReal.ofReal (Real.exp (-x)) := by
  rw [ENNReal.div_eq_inv_mul, Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos x),
    mul_comm]

/-- **Gaussian-type tail series, dominated by twice its leading term.** For
`c, K` with positive curvature `c` and the first inter-term gap large enough
(`1 ≤ c(2M+1)K`, forcing the consecutive ratio below `1/2`),
`∑_{j≥0} exp(−c(M+j)²K) ≤ 2 · exp(−cM²K)`. -/
theorem tsum_ofReal_exp_neg_sq_le (c K : ℝ) (M : ℕ)
    -- LEAN-ONLY: positive curvature so the summand decays; genuine caller input
    (hc : 0 < c)
    -- LEAN-ONLY: first gap forces the consecutive ratio ≤ 1/2 (geometric domination); caller input
    (h : 1 ≤ c * (2 * M + 1) * K) :
    (∑' j : ℕ, ENNReal.ofReal (Real.exp (-c * ((M + j : ℕ) : ℝ) ^ 2 * K)))
      ≤ 2 * ENNReal.ofReal (Real.exp (-c * (M : ℝ) ^ 2 * K)) := by
  -- `K > 0` from the gap hypothesis `1 ≤ c(2M+1)K` (`c(2M+1) > 0`).
  have hK : 0 < K := by
    by_contra hle
    push_neg at hle
    nlinarith [h, mul_nonneg (mul_pos hc (by positivity : (0:ℝ) < 2 * (M:ℝ) + 1)).le
      (neg_nonneg.mpr hle)]
  have hcK : 0 ≤ c * K := (mul_pos hc hK).le
  -- Term-by-term geometric domination: `exp(-c(M+j)²K) ≤ exp(-cM²K)·r^j`.
  have hterm : ∀ j : ℕ,
      ENNReal.ofReal (Real.exp (-c * ((M + j : ℕ) : ℝ) ^ 2 * K))
        ≤ ENNReal.ofReal (Real.exp (-c * (M:ℝ)^2 * K))
          * ENNReal.ofReal (Real.exp (-c * (2 * (M:ℝ) + 1) * K)) ^ j := by
    intro j
    have hexp : Real.exp (-c * ((M + j : ℕ):ℝ)^2 * K)
        ≤ Real.exp (-c * (M:ℝ)^2 * K) * Real.exp (-c * (2 * (M:ℝ) + 1) * K) ^ j := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      have hjsq : (j:ℝ) ≤ (j:ℝ)^2 := by
        exact_mod_cast Nat.le_self_pow (by norm_num) j
      nlinarith [mul_nonneg hcK (sub_nonneg.mpr hjsq)]
    calc ENNReal.ofReal (Real.exp (-c * ((M + j : ℕ):ℝ)^2 * K))
        ≤ ENNReal.ofReal (Real.exp (-c * (M:ℝ)^2 * K)
            * Real.exp (-c * (2 * (M:ℝ) + 1) * K) ^ j) := ENNReal.ofReal_le_ofReal hexp
      _ = ENNReal.ofReal (Real.exp (-c * (M:ℝ)^2 * K))
            * ENNReal.ofReal (Real.exp (-c * (2 * (M:ℝ) + 1) * K)) ^ j := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
            ENNReal.ofReal_pow (Real.exp_pos _).le]
  -- The ratio `r = exp(-c(2M+1)K) ≤ exp(-1) ≤ 1/2`.
  have he2 : -c * (2 * (M:ℝ) + 1) * K ≤ -1 := by nlinarith [h]
  have he1 : (2:ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hexpm1 : Real.exp (-1) ≤ 1/2 := by
    have hpos := Real.exp_pos 1
    have hprodone : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    nlinarith [hprodone, hpos, he1, Real.exp_pos (-1)]
  have hofhalf : ENNReal.ofReal (1/2 : ℝ) = 2⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hRhalf : ENNReal.ofReal (Real.exp (-c * (2 * (M:ℝ) + 1) * K)) ≤ 2⁻¹ := by
    rw [← hofhalf]
    exact ENNReal.ofReal_le_ofReal (le_trans (Real.exp_le_exp.mpr he2) hexpm1)
  have hhalf : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
    rw [ENNReal.sub_eq_of_eq_add (by simp) (ENNReal.inv_two_add_inv_two).symm]
  have hR12 : (2 : ℝ≥0∞)⁻¹ ≤ 1 - ENNReal.ofReal (Real.exp (-c * (2 * (M:ℝ) + 1) * K)) :=
    hhalf ▸ tsub_le_tsub_left hRhalf 1
  have hinv : (1 - ENNReal.ofReal (Real.exp (-c * (2 * (M:ℝ) + 1) * K)))⁻¹ ≤ 2 := by
    calc (1 - ENNReal.ofReal (Real.exp (-c * (2 * (M:ℝ) + 1) * K)))⁻¹
        ≤ ((2:ℝ≥0∞)⁻¹)⁻¹ := ENNReal.inv_le_inv.mpr hR12
      _ = 2 := inv_inv 2
  calc (∑' j : ℕ, ENNReal.ofReal (Real.exp (-c * ((M + j : ℕ):ℝ)^2 * K)))
      ≤ ∑' j : ℕ, ENNReal.ofReal (Real.exp (-c * (M:ℝ)^2 * K))
          * ENNReal.ofReal (Real.exp (-c * (2 * (M:ℝ) + 1) * K)) ^ j :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (Real.exp (-c * (M:ℝ)^2 * K))
          * ∑' j : ℕ, ENNReal.ofReal (Real.exp (-c * (2 * (M:ℝ) + 1) * K)) ^ j :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (Real.exp (-c * (M:ℝ)^2 * K))
          * (1 - ENNReal.ofReal (Real.exp (-c * (2 * (M:ℝ) + 1) * K)))⁻¹ := by
        rw [ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (Real.exp (-c * (M:ℝ)^2 * K)) * 2 := mul_le_mul_right hinv _
    _ = 2 * ENNReal.ofReal (Real.exp (-c * (M:ℝ)^2 * K)) := mul_comm _ _

/-- **Series endgame.** If the real exponent diverges (`εₙ → ∞`) then
`ofReal (exp (−εₙ)) → 0` in `ℝ≥0∞`. -/
theorem tendsto_ofReal_exp_neg {ε : ℕ → ℝ}
    -- LEAN-ONLY: the exponent diverges (drives the contraction to 0); genuine caller input
    (h : Filter.Tendsto ε Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => ENNReal.ofReal (Real.exp (-(ε n))))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hreal : Filter.Tendsto (fun n => Real.exp (-(ε n))) Filter.atTop (nhds (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atBot_iff.mpr h)
  have := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  simpa [ENNReal.ofReal_zero, Function.comp] using! this

end StatLean.Bayesian
