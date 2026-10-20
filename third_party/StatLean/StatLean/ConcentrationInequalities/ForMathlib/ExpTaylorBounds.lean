module
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

/-!
# Exponential Taylor bounds — elementary numeric bricks

Elementary inequalities between polynomials, factorials, and the real
exponential, used throughout the Orlicz cluster:
$$ y \le e^{y/2} \ (y \ge 0), \qquad y^2 \le e^{y} \ (y \ge 0), \qquad
   e^{x} \le 1 + x + \tfrac{x^2}{2}\,e^{|x|}, $$
$$ \frac{x^n}{n!} \le e^{x} \ (x \ge 0), \qquad
   \Bigl(\frac{n}{e}\Bigr)^{n} \le n!. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability: An Introduction
with Applications in Data Science*, 2nd ed., Cambridge University Press. These
are the unnamed numeric steps inside Proposition 2.6.1 ((iii)⇒(iv), (iii)⇒(ii),
(ii)⇒(iii)), Proposition 2.8.1 ((iii)⇒(iv)), and Lemma 1.7.8 ($(n/e)^n \le n!$).

**Proof formalization notes.** Pure real analysis, probability-free
(Mathlib-candidate; this file creates the area's `ForMathlib/` layer, precedent
`HighDimensionalStatistics/ForMathlib/`). All constants are exact — no frozen
numerals. The Taylor–Lagrange bound `exp_le_one_add_add_sq_half_mul_exp_abs`
splits into a series-comparison branch for `x ≥ 0` (via
`Real.sum_le_exp_of_nonneg`) and the alternating-series/convexity branch
`exp_le_one_add_add_sq_half_of_nonpos` for `x ≤ 0`; the latter is this work
item's designated named-sorry fallback. `(n/e)^n ≤ n!` follows from
`x^n/n! ≤ e^x` at `x = n` (backup brick: `Stirling.le_factorial_stirling`).

**Bibliographic comments.** Taylor–Lagrange bounds on the exponential are
classical (Euler). Their systematic use to convert Orlicz-moment conditions
into MGF bounds follows Buldygin–Kozachenko, *Metric Characterization of
Random Variables and Random Processes*, AMS 2000.
-/

namespace StatLean.ConcentrationInequalities

/-- Single-term series bound `x^n / n! ≤ e^x` for `x ≥ 0` (HDP §2.6.1
(iii)⇒(ii) even-moment bound; from `Real.sum_le_exp_of_nonneg`). -/
theorem pow_div_factorial_le_exp {x : ℝ}
    -- LEAN-ONLY: nonnegativity of the argument; numeric brick, no book scope
    (hx : 0 ≤ x) (n : ℕ) :
    x ^ n / (n.factorial : ℝ) ≤ Real.exp x := by
  have hsum := Real.sum_le_exp_of_nonneg hx (n + 1)
  refine le_trans ?_ hsum
  refine Finset.single_le_sum (f := fun i => x ^ i / (i.factorial : ℝ)) ?_
    (Finset.self_mem_range_succ n)
  intro i _
  exact div_nonneg (pow_nonneg hx i) (by positivity)

/-- `y ≤ e^{y/2}` for `y ≥ 0` (HDP §2.6.1 proof step "x² ≤ e^{x²}",
square-root form). -/
theorem le_exp_half {y : ℝ}
    -- LEAN-ONLY: nonnegativity of the argument; numeric brick, no book scope
    (hy : 0 ≤ y) :
    y ≤ Real.exp (y / 2) := by
  have hu : (0 : ℝ) ≤ y / 2 := by linarith
  have h3 : 1 + (y / 2) + (y / 2) ^ 2 / 2 ≤ Real.exp (y / 2) := by
    have hs := Real.sum_le_exp_of_nonneg hu 3
    have heq : ∑ i ∈ Finset.range 3, (y / 2) ^ i / (i.factorial : ℝ)
        = 1 + (y / 2) + (y / 2) ^ 2 / 2 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
        Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat,
        pow_zero, pow_one, zero_add]
      ring
    rwa [heq] at hs
  nlinarith [h3, sq_nonneg (y - 2)]

/-- `y² ≤ e^{y}` for `y ≥ 0` (HDP §2.8.1 proof step "x² ≤ 4e^{|x|/2}",
normalized form; square of `le_exp_half`). -/
theorem sq_le_exp {y : ℝ}
    -- LEAN-ONLY: nonnegativity of the argument; numeric brick, no book scope
    (hy : 0 ≤ y) :
    y ^ 2 ≤ Real.exp y := by
  have h := le_exp_half hy
  have hexp : Real.exp (y / 2) * Real.exp (y / 2) = Real.exp y := by
    rw [← Real.exp_add]; congr 1; ring
  nlinarith [h, hy, Real.exp_pos (y / 2), hexp]

/-- Nonpositive branch `e^x ≤ 1 + x + x²/2` for `x ≤ 0` (alternating-series /
convexity argument; helper for `exp_le_one_add_add_sq_half_mul_exp_abs`). -/
theorem exp_le_one_add_add_sq_half_of_nonpos {x : ℝ}
    -- LEAN-ONLY: branch condition of the two-sided Taylor bound; no book scope
    (hx : x ≤ 0) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  -- `f s = 1 + s + s²/2 − eˢ` has `f' s = 1 + s − eˢ ≤ 0` (since `1 + s ≤ eˢ`),
  -- so `f` is antitone; `x ≤ 0` gives `f 0 ≤ f x`, i.e. `0 ≤ f x`.
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun s => 1 + s + s ^ 2 / 2 - Real.exp s) (1 + s - Real.exp s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => 1 + s + s ^ 2 / 2) (1 + s) s := by
      have hpow : HasDerivAt (fun s : ℝ => s ^ 2 / 2) ((2 : ℝ) * s ^ (2 - 1) / 2) s :=
        (hasDerivAt_pow 2 s).div_const 2
      have := ((hasDerivAt_const s (1 : ℝ)).add (hasDerivAt_id s)).add hpow
      convert! this using 1
      ring
    exact h1.sub (Real.hasDerivAt_exp s)
  have hdiff : Differentiable ℝ (fun s => 1 + s + s ^ 2 / 2 - Real.exp s) :=
    fun s => (hderiv s).differentiableAt
  have hanti : AntitoneOn (fun s => 1 + s + s ^ 2 / 2 - Real.exp s) (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn
    intro s _
    rw [(hderiv s).deriv]
    have := Real.add_one_le_exp s
    linarith
  have hmem0 : (0 : ℝ) ∈ Set.Iic (0 : ℝ) := Set.mem_Iic.mpr le_rfl
  have hmemx : x ∈ Set.Iic (0 : ℝ) := Set.mem_Iic.mpr hx
  have hmono := hanti hmemx hmem0 hx
  simp only at hmono
  have hf0 : Real.exp 0 = 1 := Real.exp_zero
  nlinarith [hmono, hf0]

/-- Nonnegative branch of the two-sided Taylor bound: `e^x ≤ 1 + x +
(x²/2)·e^x` for `x ≥ 0`, via the integral comparison
`e^x - 1 - x = ∫₀ˣ (e^t - 1) dt ≤ ∫₀ˣ t·e^x dt = (x²/2)·e^x`. -/
private theorem exp_le_one_add_add_sq_half_mul_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 * Real.exp x := by
  have hii1 : IntervalIntegrable (fun t => Real.exp t - 1) MeasureTheory.volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hii2 : IntervalIntegrable (fun t => t * Real.exp x) MeasureTheory.volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  -- FTC: ∫₀ˣ (e^t − 1) dt = e^x − x − 1.
  have hFTC : ∫ t in (0 : ℝ)..x, (Real.exp t - 1) = Real.exp x - x - 1 := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) x,
        HasDerivAt (fun s => Real.exp s - s) (Real.exp t - 1) t := by
      intro t _
      simpa using! (Real.hasDerivAt_exp t).sub (hasDerivAt_id t)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii1]
    simp
  -- Pointwise comparison on [0, x].
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) x, Real.exp t - 1 ≤ t * Real.exp x := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have htx : t ≤ x := ht.2
    have hmul : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have hexp1 : Real.exp t - 1 ≤ t * Real.exp t := by
      nlinarith [mul_nonneg (Real.exp_pos t).le (sub_nonneg.mpr (Real.add_one_le_exp (-t))), hmul]
    have hmono2 : t * Real.exp t ≤ t * Real.exp x :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htx) ht0
    linarith
  have hmono := intervalIntegral.integral_mono_on hx hii1 hii2 hpt
  have hval : ∫ t in (0 : ℝ)..x, t * Real.exp x = x ^ 2 / 2 * Real.exp x := by
    rw [intervalIntegral.integral_mul_const, integral_id]; ring
  rw [hFTC, hval] at hmono
  linarith

/-- Two-sided Taylor–Lagrange bound `e^x ≤ 1 + x + (x²/2)·e^{|x|}` (HDP
§2.6.1 (iii)⇒(iv) and §2.8.1 (iii)⇒(iv): the split `E e^{λX} ≤ 1 + λEX +
(λ²/2)E X²e^{|λX|}`). For `x ≥ 0` by series comparison
(`Real.sum_le_exp_of_nonneg`); for `x < 0` via
`exp_le_one_add_add_sq_half_of_nonpos`. -/
theorem exp_le_one_add_add_sq_half_mul_exp_abs (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 * Real.exp |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact exp_le_one_add_add_sq_half_mul_exp_of_nonneg hx
  · have hx0 : x ≤ 0 := le_of_lt hx
    rw [abs_of_neg hx]
    have hbrick := exp_le_one_add_add_sq_half_of_nonpos hx0
    have h1 : (1 : ℝ) ≤ Real.exp (-x) := by
      have := Real.add_one_le_exp (-x); linarith
    nlinarith [hbrick, h1, sq_nonneg x]

/-- `(n/e)^n ≤ n!` (HDP Lemma 1.7.8; used in Prop 2.6.1 (ii)⇒(iii)).
Follows from `pow_div_factorial_le_exp` at `x = n`; backup:
`Stirling.le_factorial_stirling`. -/
theorem pow_div_exp_pow_le_factorial (n : ℕ) :
    ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  have hx : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpe := pow_div_factorial_le_exp hx n
  have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hen : Real.exp 1 ^ n = Real.exp (n : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
  rw [div_pow, hen, div_le_iff₀ (Real.exp_pos _)]
  rw [div_le_iff₀ hfacpos] at hpe
  nlinarith [hpe]

end StatLean.ConcentrationInequalities
