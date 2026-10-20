module
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

public import Mathlib.Probability.Independence.CharacteristicFunction

@[expose] public section

/-!
# The Lindeberg central limit theorem for triangular arrays

Mathlib's central limit theorem
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`) covers a *single* i.i.d.
sequence. The asymptotics of permutation, randomization and bootstrap distributions all
need the strictly more general **triangular-array** form: for each `n` a finite row
`X n 0, …, X n (m n − 1)` of independent, centered, square-integrable variables whose
variances add up to `1` in the limit and which satisfy the **Lindeberg condition**
$$\sum_i \mathbb E\bigl[X_{n,i}^2\,\mathbf 1\{|X_{n,i}| > \varepsilon\}\bigr] \to 0
  \qquad (\forall\,\varepsilon > 0),$$
the row sums `∑ᵢ Xₙ,ᵢ` converge in distribution to the standard normal law. Rows are
unrelated to each other (no nesting, no common marginal), which is exactly what the
downstream applications need: after conditioning on the data, a permutation statistic is a
row of independent summands whose law changes with `n`.

## Main results

* `lindeberg_clt` — the triangular-array CLT under the Lindeberg condition.
* `lindeberg_clt_of_bounded` — the uniformly-bounded corollary (`|Xₙ,ᵢ| ≤ cₙ`, `cₙ → 0`),
  which is the form most often applied.
* `weighted_iid_clt` — weighted sums `∑ᵢ wₙ,ᵢ Yᵢ` of an i.i.d. sequence, under the
  negligibility condition `maxᵢ wₙ,ᵢ² / ∑ⱼ wₙ,ⱼ² → 0`.
* `triangular_wlln_of_L1` — the companion weak law: row-i.i.d. arrays whose row laws
  converge weakly *and* whose first absolute moments converge have row averages converging
  in probability to the limiting mean. **The frozen form of this statement was false** (the
  `L¹` hypothesis was vacuous for non-integrable rows, because the Bochner integral takes its
  junk value there); it carries one added hypothesis, `∀ n, Integrable id (G n)`, and is
  proved. See its docstring for the counterexample and the repair.

Convergence in distribution is stated with Mathlib's `MeasureTheory.TendstoInDistribution`
(random-variable form, constant family of underlying spaces `fun _ => P`), which is the
convention already used by the multivariate CLT elsewhere in the project; convergence in
probability with `MeasureTheory.TendstoInMeasure`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 11 (Basic Large-Sample
Theory), §11.2 (Weak Convergence and Central Limit Theorems), **Theorem 11.2.5** (Lindeberg Central
Limit Theorem) for triangular arrays. (`TSH4 §11.2 Thm 11.2.5`.)

**Proof formalization notes.**
* Route: characteristic functions. Lindeberg's swapping/telescoping argument bounds
  `|∏ᵢ φₙ,ᵢ(t) − exp(−t²/2)|` by a sum of third-order remainders split at the level `ε`;
  Lévy continuity (`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`) then
  converts pointwise `charFun` convergence into weak convergence, exactly as in the
  project's multivariate CLT.
* The variance normalisation is stated as `∑ᵢ Var[Xₙ,ᵢ] → 1` rather than the textbook's
  exact `= 1`; this is strictly more general (rescaling a row by `sₙ` is not always
  available downstream) and is what the swapping argument actually consumes.
* The Lindeberg sums are stated with the *open* truncation set `{ε < |Xₙ,ᵢ|}`. Quantified
  over all `ε > 0` this is equivalent to the closed-set version, and it is the weaker
  hypothesis at each fixed `ε`.
* `lindeberg_clt_of_bounded` does not carry an `MemLp _ 2` hypothesis: a bounded
  measurable function on a probability space is automatically square-integrable, so
  demanding it would be laundering.
* In `weighted_iid_clt` the negligibility condition is written in `∀ ε > 0, ∀ᶠ n` form
  rather than as `Tendsto (fun n => ⨆ i, …) atTop (𝓝 0)`: for an empty row `Fin 0` a real
  `⨆` collapses to the junk value `0`, so the `iSup` spelling would silently weaken the
  hypothesis; the two agree on nonempty rows.

**Bibliographic comments.** The condition and the theorem are due to J. W. Lindeberg
("Eine neue Herleitung des Exponentialgesetzes in der Wahrscheinlichkeitsrechnung,"
*Math. Z.* **15** (1922), 211–225); the triangular-array formulation and the converse
(necessity of the condition under uniform asymptotic negligibility) are due to W. Feller
("Über den zentralen Grenzwertsatz der Wahrscheinlichkeitsrechnung," *Math. Z.* **40**
(1935), 521–559). The characteristic-function continuity theorem that closes the argument
is P. Lévy, *Calcul des probabilités*, Gauthier-Villars, 1925.
-/

open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped Topology ENNReal NNReal

namespace StatLean.HypothesisTesting

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

open Complex in
/-- **Uniform third-order remainder bound for `e^{iy}`.** The pointwise estimate driving
Lindeberg's swapping argument:
`‖exp (I y) − (1 + I y − y²/2)‖ ≤ min (|y|³/6) (y²)`.
Both bounds are elementary: the cubic half comes from integrating the exponential's remainder
three times, the quadratic half from `‖exp (I y) − 1 − I y‖ ≤ y²/2` and the triangle
inequality. Mathlib only provides the non-uniform `taylor_charFun_two`, so this is proved from
scratch here. -/
private lemma norm_cexp_sub_taylor_le (y : ℝ) :
    ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2)‖ ≤ min (|y| ^ 3 / 6) (y ^ 2) := by
  -- Derivative of `u ↦ exp (I u)` (as a function of a real variable).
  have he : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w))
      (Complex.exp (I * ↑u) * I) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using (h1.cexp).comp_ofReal
  -- `|exp (I u)| = 1`.
  have hnorme : ∀ u : ℝ, ‖Complex.exp (I * ↑u)‖ = 1 := by
    intro u; rw [Complex.norm_exp]; simp
  -- Derivative of `u ↦ I u`.
  have hIu : ∀ u : ℝ, HasDerivAt (fun w : ℝ => I * ↑w) I u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using h1.comp_ofReal
  -- Continuity of the three integrands.
  have hcontI : Continuous (fun u : ℝ => Complex.exp (I * ↑u) * I) := by fun_prop
  have hcont1 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1) * I) := by fun_prop
  have hcont2 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1 - I * ↑u) * I) := by fun_prop
  -- Level 0: `‖exp (I z) − 1‖ ≤ z` for `z ≥ 0`.
  have hL0 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1‖ ≤ z := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I) = Complex.exp (I * ↑z) - 1 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => he u)
        (hcontI.intervalIntegrable 0 z)]
      simp
    rw [← hInt]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := z)
      (C := 1) (f := fun u => Complex.exp (I * ↑u) * I)
      (fun u _ => by rw [norm_mul, Complex.norm_I, mul_one]; exact le_of_eq (hnorme u))
    calc ‖∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I‖ ≤ 1 * |z - 0| := hbnd
      _ = z := by rw [sub_zero, abs_of_nonneg hz, one_mul]
  -- Derivative of `A₁ w = exp (I w) − 1 − I w`.
  have hd1 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w)
      ((Complex.exp (I * ↑u) - 1) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1) * I = Complex.exp (I * ↑u) * I - 0 - I := by ring
    rw [heq]
    exact ((he u).sub (hasDerivAt_const u (1 : ℂ))).sub (hIu u)
  -- Level 1: `‖exp (I z) − 1 − I z‖ ≤ z²/2` for `z ≥ 0`.
  have hL1 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ z ^ 2 / 2 := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1) * I)
        = Complex.exp (I * ↑z) - 1 - I * ↑z := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd1 u)
        (hcont1.intervalIntegrable 0 z)]
      simp
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ ∫ u in (0:ℝ)..z, u := by
      rw [← hInt]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        (continuous_id.intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL0 u hu.1.le
    rw [integral_id] at hb
    simpa using hb
  -- Derivative of `w ↦ w²/2` (written `w * w / 2`).
  have hsq : ∀ u : ℝ, HasDerivAt (fun w : ℝ => (↑w * ↑w / 2 : ℂ)) (↑u : ℂ) u := by
    intro u
    have hof : HasDerivAt (fun w : ℝ => (↑w : ℂ)) 1 u := by
      simpa using (hasDerivAt_id (↑u : ℂ)).comp_ofReal
    have heq : (↑u : ℂ) = (1 * ↑u + ↑u * 1) / 2 := by ring
    rw [heq]
    exact (hof.mul hof).div_const 2
  -- Derivative of `A₂ w = exp (I w) − 1 − I w + w²/2`.
  have hd2 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w + ↑w * ↑w / 2)
      ((Complex.exp (I * ↑u) - 1 - I * ↑u) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1 - I * ↑u) * I
        = (Complex.exp (I * ↑u) - 1) * I + ↑u := by
      have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
      linear_combination (-(↑u : ℂ)) * hI2
    rw [heq]
    exact (hd1 u).add (hsq u)
  -- `A₂ z` as an integral of `A₁ · I`.
  have hA2z : ∀ z : ℝ, (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1 - I * ↑u) * I)
      = Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2 := by
    intro z
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd2 u)
      (hcont2.intervalIntegrable 0 z)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  -- The `y ≥ 0` case of the goal (with `|y| = y`).
  have key : ∀ z : ℝ, 0 ≤ z →
      ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖ ≤ min (z ^ 3 / 6) (z ^ 2) := by
    intro z hz
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖
        ≤ ∫ u in (0:ℝ)..z, u ^ 2 / 2 := by
      rw [← hA2z z]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 / 2)).intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL1 u hu.1.le
    have hintval : (∫ u in (0:ℝ)..z, u ^ 2 / 2) = z ^ 3 / 6 := by
      rw [intervalIntegral.integral_div, integral_pow]; push_cast; ring
    refine le_min (hb.trans (le_of_eq hintval)) ?_
    have h1 := hL1 z hz
    have hcast : (↑z * ↑z / 2 : ℂ) = ((z * z / 2 : ℝ) : ℂ) := by push_cast; ring
    have hz2 : ‖(↑z * ↑z / 2 : ℂ)‖ = z ^ 2 / 2 := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    have hsplit : Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2
        = (Complex.exp (I * ↑z) - 1 - I * ↑z) + ↑z * ↑z / 2 := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [hz2]; linarith
  -- Reduce the goal to `A₂`.
  have hEq : Complex.exp (I * ↑y) - (1 + I * ↑y - (↑y : ℂ) ^ 2 / 2)
      = Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2 := by ring
  rw [hEq]
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact key y hy
  · -- Reflect to `−y ≥ 0` via conjugation.
    have hz : (0:ℝ) ≤ -y := by linarith
    have hexp : (starRingEnd ℂ) (Complex.exp (I * ↑y)) = Complex.exp (I * ↑(-y)) := by
      rw [← Complex.exp_conj]; congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
    have hconj : (starRingEnd ℂ) (Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2)
        = Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2 := by
      simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
        Complex.conj_ofReal, hexp, Complex.ofReal_neg]
      ring
    have hnn : ‖Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2‖
        = ‖Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2‖ := by
      rw [← hconj, Complex.norm_conj]
    rw [hnn, abs_of_neg hy, show (y : ℝ) ^ 2 = (-y) ^ 2 from by ring]
    exact key (-y) hz

-- H1: telescoping product bound.
private lemma norm_prod_sub_prod_le {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] (s : Finset ι)
    (f g : ι → 𝕜) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    have key : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
        = f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [key]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hpg : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one (fun i _ => norm_nonneg _) hg'
    have h1 : ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ :=
      calc ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖
            ≤ 1 * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ :=
              mul_le_mul_of_nonneg_right hfa (norm_nonneg _)
        _ = ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ := one_mul _
        _ ≤ ∑ i ∈ s, ‖f i - g i‖ := ih hf' hg'
    have h2 : ‖f a - g a‖ * ‖∏ i ∈ s, g i‖ ≤ ‖f a - g a‖ :=
      calc ‖f a - g a‖ * ‖∏ i ∈ s, g i‖
            ≤ ‖f a - g a‖ * 1 := mul_le_mul_of_nonneg_left hpg (norm_nonneg _)
        _ = ‖f a - g a‖ := mul_one _
    linarith

-- H2: real quadratic remainder for `exp (-u)`.
private lemma abs_exp_neg_sub_one_sub_le {u : ℝ} (hu : |u| ≤ 1) :
    |Real.exp (-u) - (1 - u)| ≤ (3 / 4) * u ^ 2 := by
  have h := Real.exp_bound (x := -u) (by rwa [abs_neg]) (n := 2) (by norm_num)
  have hs : ∑ m ∈ Finset.range 2, (-u) ^ m / (m.factorial : ℝ) = 1 - u := by
    simp [Finset.sum_range_succ]; ring
  rw [hs, abs_neg, sq_abs] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]
  ring

-- H3: diagonal tendsto-to-zero.
private lemma tendsto_zero_of_eventually_le {F : ℕ → ℝ}
    (hF : ∀ᶠ n in atTop, 0 ≤ F n) (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, F n ≤ δ) :
    Tendsto F atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hF] with n hn using lt_of_lt_of_le hb hn
  · filter_upwards [h (b / 2) (by linarith)] with n hn using lt_of_le_of_lt hn (by linarith)

open Complex in
/-- **The analytic core of the Lindeberg CLT.** Under the Lindeberg hypotheses the product
of the row characteristic functions converges pointwise to the standard-normal
characteristic function `t ↦ exp(−t²/2)`. This is the content of Lindeberg's
swapping/telescoping estimate; `lindeberg_clt` merely feeds this pointwise statement through
Lévy's continuity theorem.

Lindeberg's swapping/telescoping estimate, assembled on top of the uniform remainder
bound `norm_cexp_sub_taylor_le`: telescope the two products, bound each factor's
difference by `E[min(|t Xₙᵢ|³/6, t² Xₙᵢ²)]`, split at the level `ε` (the large part is
the Lindeberg sum killed by `hlin`), and match `∏ᵢ (1 − t²σₙᵢ²/2) → exp(−t²/2)`. -/
private lemma tendsto_prod_charFun_lindeberg
    {m : ℕ → ℕ} {X : (n : ℕ) → Fin (m n) → Ω → ℝ}
    (hmeas : ∀ n i, Measurable (X n i))
    (hindep : ∀ n, iIndepFun (X n) P)
    (hL2 : ∀ n i, MemLp (X n i) 2 P)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hvar : Tendsto (fun n => ∑ i, Var[X n i; P]) atTop (𝓝 1))
    (hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => ∏ i, charFun (P.map (X n i)) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) := by
  -- The `t = 0` case is `∏ 1 → 1`; handle it first, then assume `t ≠ 0`.
  rcases eq_or_ne t 0 with rfl | ht
  · have hone : ∀ n i, charFun (P.map (X n i)) 0 = 1 := by
      intro n i
      haveI : IsProbabilityMeasure (P.map (X n i)) :=
        Measure.isProbabilityMeasure_map (hmeas n i).aemeasurable
      rw [charFun_zero, probReal_univ, Complex.ofReal_one]
    have hR : charFun (gaussianReal 0 1) 0 = 1 := by
      rw [charFun_zero, probReal_univ, Complex.ofReal_one]
    simp only [hone, Finset.prod_const_one, hR]
    exact tendsto_const_nhds
  -- Basic facts about the row entries.
  have hvnn : ∀ n i, (0:ℝ) ≤ Var[X n i; P] := fun n i => variance_nonneg _ _
  have hunn : ∀ n i, (0:ℝ) ≤ t ^ 2 * Var[X n i; P] / 2 :=
    fun n i => div_nonneg (mul_nonneg (sq_nonneg t) (hvnn n i)) (by norm_num)
  have hI2 : ∀ n i, Integrable (fun ω => (X n i ω) ^ 2) P := fun n i => (hL2 n i).integrable_sq
  have hI1 : ∀ n i, Integrable (X n i) P := fun n i => (hL2 n i).integrable one_le_two
  have hVeq : ∀ n i, Var[X n i; P] = ∫ ω, (X n i ω) ^ 2 ∂P :=
    fun n i => variance_of_integral_eq_zero (hmeas n i).aemeasurable (hmean n i)
  -- The RHS constant as a genuine exponential.
  have hc : charFun (gaussianReal 0 1) t = Complex.exp (-(↑t ^ 2 / 2)) := by
    rw [charFun_gaussianReal]; push_cast; ring_nf
  -- Measurability of the truncation sets.
  have hset : ∀ ε n i, MeasurableSet {ω | ε < |X n i ω|} := fun ε n i =>
    measurableSet_lt measurable_const (hmeas n i).abs
  -- Nonnegativity of the Lindeberg terms.
  have hLnn : ∀ ε n i, 0 ≤ ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P :=
    fun ε n i => setIntegral_nonneg (hset ε n i) fun ω _ => sq_nonneg _
  -- CENTRAL per-term estimate (crux of the swapping argument).
  have hterm : ∀ ε : ℝ, 0 < ε → ∀ n i,
      ‖charFun (P.map (X n i)) t - ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ)‖
        ≤ |t| ^ 3 * ε / 6 * Var[X n i; P]
          + t ^ 2 * ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P := by
    intro ε hε n i
    have hsm := hset ε n i
    -- Integrability of the integrand pieces.
    have hIsecond : Integrable (fun ω => Complex.I * (↑(t * X n i ω) : ℂ)) P :=
      (((hI1 n i).const_mul t).ofReal).const_mul Complex.I
    have hIrp : Integrable (fun ω => ((1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) : ℂ)) P :=
      ((integrable_const (1 : ℝ)).sub (((hI2 n i).const_mul (t ^ 2)).div_const 2)).ofReal
    have hItX2 : Integrable (fun ω => (t * X n i ω) ^ 2) P := by
      simpa [mul_pow] using (hI2 n i).const_mul (t ^ 2)
    have hIthird : Integrable (fun ω => ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) P := by
      have he : (fun ω => ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)
          = fun ω => (↑((t * X n i ω) ^ 2) : ℂ) / 2 := by ext ω; rw [← Complex.ofReal_pow]
      rw [he]; exact (hItX2.ofReal).div_const (2 : ℂ)
    have hFmeas : Measurable (fun ω => Complex.exp (Complex.I * ↑(t * X n i ω))) :=
      Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.comp ((hmeas n i).const_mul t)).const_mul Complex.I)
    have hIF : Integrable (fun ω => Complex.exp (Complex.I * ↑(t * X n i ω))) P :=
      (integrable_const (1 : ℝ)).mono' hFmeas.aestronglyMeasurable
        (ae_of_all _ fun ω => le_of_eq (by rw [Complex.norm_exp]; simp))
    have hIG : Integrable (fun ω => 1 + Complex.I * ↑(t * X n i ω)
        - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) P :=
      ((integrable_const (1 : ℂ)).add hIsecond).sub hIthird
    -- `charFun = ∫ exp`.
    have hFcf : charFun (P.map (X n i)) t
        = ∫ ω, Complex.exp (Complex.I * ↑(t * X n i ω)) ∂P := by
      rw [charFun_apply_real, integral_map (hmeas n i).aemeasurable
        (Continuous.aestronglyMeasurable (by fun_prop))]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      congr 1; push_cast; ring
    -- The real (variance) part and the vanishing imaginary part.
    have hRp : ∫ ω, (1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) ∂P = 1 - t ^ 2 * Var[X n i; P] / 2 := by
      rw [integral_sub (integrable_const 1) (((hI2 n i).const_mul (t ^ 2)).div_const 2),
        integral_const, probReal_univ, smul_eq_mul, mul_one, integral_div]
      simp only [integral_const_mul]
      rw [← hVeq n i]
    have hTX : ∫ ω, t * X n i ω ∂P = 0 := by
      rw [integral_const_mul t (X n i), hmean n i, mul_zero]
    have hImC : ∫ ω, Complex.I * ((t * X n i ω : ℝ) : ℂ) ∂P = 0 := by
      have key : ∫ ω, Complex.I * ((t * X n i ω : ℝ) : ℂ) ∂P
          = Complex.I * ∫ ω, ((t * X n i ω : ℝ) : ℂ) ∂P := integral_const_mul _ _
      rw [key, integral_complex_ofReal, hTX, Complex.ofReal_zero, mul_zero]
    -- `∫ G = 1 - t²σ²/2`.
    have hGint : ∫ ω, (1 + Complex.I * ↑(t * X n i ω)
        - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) ∂P = ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ) := by
      have hEq : (fun ω => 1 + Complex.I * (↑(t * X n i ω) : ℂ) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)
          = fun ω => ((1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) : ℂ)
              + Complex.I * ((t * X n i ω : ℝ) : ℂ) := by
        ext ω; push_cast; ring
      rw [hEq, integral_add hIrp hIsecond, integral_complex_ofReal, hRp, hImC, add_zero]
    -- Assemble the difference as one integral.
    have hab : charFun (P.map (X n i)) t - ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ)
        = ∫ ω, (Complex.exp (Complex.I * ↑(t * X n i ω))
            - (1 + Complex.I * ↑(t * X n i ω) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)) ∂P := by
      rw [integral_sub hIF hIG, ← hFcf, hGint]
    -- Pointwise remainder bound.
    set g : Ω → ℝ := fun ω => |t| ^ 3 * ε / 6 * (X n i ω) ^ 2
        + t ^ 2 * Set.indicator {ω | ε < |X n i ω|} (fun ω => (X n i ω) ^ 2) ω with hgdef
    have hbound : ∀ ω, ‖Complex.exp (Complex.I * ↑(t * X n i ω))
        - (1 + Complex.I * ↑(t * X n i ω) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)‖ ≤ g ω := by
      intro ω
      refine (norm_cexp_sub_taylor_le (t * X n i ω)).trans ?_
      have hnn0 : (0:ℝ) ≤ |t| ^ 3 * ε / 6 * (X n i ω) ^ 2 :=
        mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) 3) hε.le) (by norm_num))
          (sq_nonneg _)
      by_cases hω : ε < |X n i ω|
      · have hωm : ω ∈ {ω | ε < |X n i ω|} := hω
        simp only [hgdef, Set.indicator_of_mem hωm]
        refine (min_le_right _ _).trans ?_
        have h2 : (t * X n i ω) ^ 2 = t ^ 2 * (X n i ω) ^ 2 := by ring
        rw [h2]; linarith [hnn0]
      · have hωm : ω ∉ {ω | ε < |X n i ω|} := hω
        simp only [hgdef, Set.indicator_of_notMem hωm, mul_zero, add_zero]
        refine (min_le_left _ _).trans ?_
        have habs : |t * X n i ω| ^ 3 = |t| ^ 3 * |X n i ω| ^ 3 := by rw [abs_mul, mul_pow]
        have hcube : |X n i ω| ^ 3 ≤ ε * (X n i ω) ^ 2 := by
          have he : |X n i ω| ^ 3 = |X n i ω| * (X n i ω) ^ 2 := by rw [← sq_abs]; ring
          rw [he]; exact mul_le_mul_of_nonneg_right (not_lt.1 hω) (sq_nonneg _)
        rw [habs]; nlinarith [hcube, pow_nonneg (abs_nonneg t) 3]
    have hbint : Integrable g P := by
      rw [hgdef]
      exact ((hI2 n i).const_mul _).add (((hI2 n i).indicator hsm).const_mul _)
    have hg_int : ∫ ω, g ω ∂P
        = |t| ^ 3 * ε / 6 * Var[X n i; P]
          + t ^ 2 * ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P := by
      rw [hgdef, integral_add ((hI2 n i).const_mul _) (((hI2 n i).indicator hsm).const_mul _)]
      simp only [integral_const_mul, integral_indicator hsm]
      rw [← hVeq n i]
    rw [hab]
    exact (norm_integral_le_of_norm_le hbint (ae_of_all _ hbound)).trans (le_of_eq hg_int)
  -- Uniform asymptotic negligibility of the row variances.
  have hsmall : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, ∀ i, Var[X n i; P] ≤ c := by
    intro c hc
    have hεpos : (0:ℝ) < Real.sqrt (c / 2) := Real.sqrt_pos.2 (by linarith)
    have hε2 : Real.sqrt (c / 2) ^ 2 = c / 2 := Real.sq_sqrt (by linarith)
    set ε := Real.sqrt (c / 2) with hεdef
    have hSlt : ∀ᶠ n in atTop,
        ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P ≤ c / 2 :=
      (hlin ε hεpos).eventually_le_const (show (0:ℝ) < c / 2 by linarith)
    filter_upwards [hSlt] with n hn i
    have hsm := hset ε n i
    have hdecomp : Var[X n i; P]
        = ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P
          + ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂P := by
      rw [hVeq n i]; exact (integral_add_compl hsm (hI2 n i)).symm
    have hpart1 : ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P ≤ c / 2 :=
      le_trans (Finset.single_le_sum (fun j _ => hLnn ε n j) (Finset.mem_univ i)) hn
    have hpart2 : ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂P ≤ c / 2 := by
      rw [← hε2]
      calc ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂P
          ≤ ∫ ω in {ω | ε < |X n i ω|}ᶜ, ε ^ 2 ∂P := by
            refine setIntegral_mono_on ((hI2 n i).integrableOn) integrableOn_const hsm.compl
              (fun ω hω => ?_)
            simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
            rw [← sq_abs (X n i ω)]
            exact pow_le_pow_left₀ (abs_nonneg _) hω 2
        _ ≤ ∫ _ω, ε ^ 2 ∂P :=
            setIntegral_le_integral (integrable_const _) (ae_of_all _ fun _ => by positivity)
        _ = ε ^ 2 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hdecomp]; linarith
  have ht2 : (0:ℝ) < t ^ 2 := by positivity
  -- Eventually every row term satisfies `uᵢ = t²σᵢ²/2 ≤ 1`.
  have hev1 : ∀ᶠ n in atTop, ∀ i, t ^ 2 * Var[X n i; P] / 2 ≤ 1 := by
    filter_upwards [hsmall (2 / t ^ 2) (by positivity)] with n hn i
    have hb := (le_div_iff₀ ht2).1 (hn i)
    have hcomm : t ^ 2 * Var[X n i; P] = Var[X n i; P] * t ^ 2 := mul_comm _ _
    linarith
  -- Abbreviations for the two products (`A` characteristic, `B` its quadratic surrogate).
  set A : ℕ → ℂ := fun n => ∏ i, charFun (P.map (X n i)) t with hA
  set B : ℕ → ℂ := fun n => ∏ i, ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ) with hB
  -- `∑ᵢ uᵢ → t²/2`.
  have hsum : Tendsto (fun n => ∑ i, t ^ 2 * Var[X n i; P] / 2) atTop (𝓝 (t ^ 2 / 2)) := by
    have h := hvar.const_mul (t ^ 2 / 2)
    have he : ∀ n, ∑ i, t ^ 2 * Var[X n i; P] / 2 = t ^ 2 / 2 * ∑ i, Var[X n i; P] := by
      intro n; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    simpa [he, mul_one] using h
  ------------------------------------------------------------------
  -- Claim G : `∑ᵢ uᵢ² → 0`.
  ------------------------------------------------------------------
  have hGsq : Tendsto (fun n => ∑ i, (t ^ 2 * Var[X n i; P] / 2) ^ 2) atTop (𝓝 0) := by
    refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n =>
      Finset.sum_nonneg fun i _ => sq_nonneg _) (fun δ hδ => ?_)
    set M : ℝ := δ / (t ^ 2 / 2 + 2) with hMdef
    have hMpos : 0 < M := by rw [hMdef]; exact div_pos hδ (by positivity)
    have hsmallM := hsmall (2 * M / t ^ 2) (div_pos (mul_pos (by norm_num) hMpos) ht2)
    have hsumlt : ∀ᶠ n in atTop, ∑ i, t ^ 2 * Var[X n i; P] / 2 < t ^ 2 / 2 + 1 :=
      hsum.eventually_lt_const (by linarith)
    filter_upwards [hsmallM, hsumlt] with n hnM hnsum
    have huM : ∀ i, t ^ 2 * Var[X n i; P] / 2 ≤ M := by
      intro i
      have hb := (le_div_iff₀ ht2).1 (hnM i)
      have hcomm : t ^ 2 * Var[X n i; P] = Var[X n i; P] * t ^ 2 := mul_comm _ _
      linarith
    calc ∑ i, (t ^ 2 * Var[X n i; P] / 2) ^ 2
        ≤ ∑ i, M * (t ^ 2 * Var[X n i; P] / 2) := by
          apply Finset.sum_le_sum; intro i _
          rw [sq]; exact mul_le_mul_of_nonneg_right (huM i) (hunn n i)
      _ = M * ∑ i, t ^ 2 * Var[X n i; P] / 2 := by rw [Finset.mul_sum]
      _ ≤ M * (t ^ 2 / 2 + 1) := by
          apply mul_le_mul_of_nonneg_left hnsum.le hMpos.le
      _ ≤ δ := by
          rw [hMdef]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith [hδ.le]
  ------------------------------------------------------------------
  -- T2 : `B n → charFun gaussian`.
  ------------------------------------------------------------------
  have T2 : Tendsto B atTop (𝓝 (charFun (gaussianReal 0 1) t)) := by
    rw [hc, hB]
    -- Reduce to a real product.
    have hLC : Complex.exp (-(↑t ^ 2 / 2)) = ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    have hBreal : (fun n => ∏ i, ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ))
        = fun n => ((∏ i, (1 - t ^ 2 * Var[X n i; P] / 2) : ℝ) : ℂ) := by
      ext n; rw [Complex.ofReal_prod]
    rw [hLC, hBreal]
    -- Now prove the real limit and lift by `ofReal`.
    refine (Complex.continuous_ofReal.tendsto _).comp ?_
    -- Real statement: `∏ (1 - uᵢ) → exp(-t²/2)`.
    have hprodexp : ∀ n, ∏ i, Real.exp (-(t ^ 2 * Var[X n i; P] / 2))
        = Real.exp (-(∑ i, t ^ 2 * Var[X n i; P] / 2)) := by
      intro n; rw [← Real.exp_sum]; rw [← Finset.sum_neg_distrib]
    have hEprod : Tendsto (fun n => ∏ i, Real.exp (-(t ^ 2 * Var[X n i; P] / 2))) atTop
        (𝓝 (Real.exp (-(t ^ 2 / 2)))) := by
      simp_rw [hprodexp]
      exact (Real.continuous_exp.tendsto _).comp hsum.neg
    have hdiff : Tendsto (fun n => (∏ i, (1 - t ^ 2 * Var[X n i; P] / 2))
        - ∏ i, Real.exp (-(t ^ 2 * Var[X n i; P] / 2))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n => norm_nonneg _)
        (fun δ hδ => ?_)
      have hsqlt : ∀ᶠ n in atTop, (3 / 4) * ∑ i, (t ^ 2 * Var[X n i; P] / 2) ^ 2 < δ := by
        have hlim : Tendsto (fun n => (3 / 4) * ∑ i, (t ^ 2 * Var[X n i; P] / 2) ^ 2) atTop
            (𝓝 0) := by simpa using hGsq.const_mul (3 / 4)
        exact hlim.eventually_lt_const (by linarith)
      filter_upwards [hev1, hsqlt] with n hn1 hn2
      have htel := norm_prod_sub_prod_le (𝕜 := ℝ) Finset.univ
        (fun i => 1 - t ^ 2 * Var[X n i; P] / 2)
        (fun i => Real.exp (-(t ^ 2 * Var[X n i; P] / 2)))
        (fun i _ => by
          rw [Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [hn1 i, hunn n i], by linarith [hunn n i]⟩)
        (fun i _ => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact (Real.exp_le_one_iff).2 (by linarith [hunn n i]))
      refine htel.trans (le_of_lt (lt_of_le_of_lt ?_ hn2))
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h2 := abs_exp_neg_sub_one_sub_le (u := t ^ 2 * Var[X n i; P] / 2)
        (by rw [abs_le]; exact ⟨by linarith [hunn n i], hn1 i⟩)
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact h2
    have hRealP1 : Tendsto (fun n => ∏ i, (1 - t ^ 2 * Var[X n i; P] / 2)) atTop
        (𝓝 (Real.exp (-(t ^ 2 / 2)))) := by
      have := hdiff.add hEprod
      simpa using this
    exact hRealP1
  ------------------------------------------------------------------
  -- T1 : `A n - B n → 0`.
  ------------------------------------------------------------------
  have T1 : Tendsto (fun n => A n - B n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n => norm_nonneg _)
      (fun δ hδ => ?_)
    set ε : ℝ := δ / (|t| ^ 3 + 1) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; exact div_pos hδ (by positivity)
    have hle : |t| ^ 3 * ε ≤ δ := by
      have h0 : (0:ℝ) < |t| ^ 3 + 1 := by positivity
      rw [hεdef, ← mul_div_assoc, div_le_iff₀ h0]; nlinarith [abs_nonneg t, hδ.le]
    have hVarlt : ∀ᶠ n in atTop, ∑ i, Var[X n i; P] ≤ 2 :=
      (hvar.eventually_lt_const (by norm_num : (1:ℝ) < 2)).mono fun n h => h.le
    have hLinlt : ∀ᶠ n in atTop,
        t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P < δ / 3 := by
      have hlim : Tendsto (fun n => t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P)
          atTop (𝓝 0) := by simpa using (hlin ε hεpos).const_mul (t ^ 2)
      exact hlim.eventually_lt_const (by linarith)
    filter_upwards [hev1, hVarlt, hLinlt] with n hn1 hn2 hn3
    -- telescoping
    have hpm : ∀ i, IsProbabilityMeasure (P.map (X n i)) := fun i =>
      Measure.isProbabilityMeasure_map (hmeas n i).aemeasurable
    have htel := norm_prod_sub_prod_le (𝕜 := ℂ) Finset.univ
      (fun i => charFun (P.map (X n i)) t)
      (fun i => ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ))
      (fun i _ => norm_charFun_le_one _)
      (fun i _ => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hn1 i], by linarith [hunn n i]⟩)
    refine htel.trans ?_
    -- sum of per-term bounds
    have hsum2 : ∑ i, ‖charFun (P.map (X n i)) t - ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ)‖
        ≤ |t| ^ 3 * ε / 6 * ∑ i, Var[X n i; P]
          + t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => hterm ε hεpos n i
    refine hsum2.trans ?_
    have hterm1 : |t| ^ 3 * ε / 6 * ∑ i, Var[X n i; P] ≤ δ / 3 := by
      have hnn : (0:ℝ) ≤ |t| ^ 3 * ε / 6 := by positivity
      calc |t| ^ 3 * ε / 6 * ∑ i, Var[X n i; P]
          ≤ |t| ^ 3 * ε / 6 * 2 := by apply mul_le_mul_of_nonneg_left hn2 hnn
        _ ≤ δ / 3 := by nlinarith [hle, hεpos.le, abs_nonneg t]
    linarith [hn3]
  ------------------------------------------------------------------
  -- Combine.
  ------------------------------------------------------------------
  have hcomb := T1.add T2
  simpa using hcomb

/-- **Lindeberg's central limit theorem for triangular arrays.**

For each `n` the row `(X n i)_{i < m n}` consists of independent, centered,
square-integrable random variables; the row variances converge to `1` and the Lindeberg
condition holds. Then the row sums converge in distribution to the standard normal law.

The row sizes `m n` are arbitrary (they need not tend to infinity, and rows are unrelated
across `n`). -/
theorem lindeberg_clt {m : ℕ → ℕ} {X : (n : ℕ) → Fin (m n) → Ω → ℝ} {Z : Ω' → ℝ}
    -- USER-INPUT: every array entry is measurable (data regularity).
    (hmeas : ∀ n i, Measurable (X n i))
    -- USER-INPUT: entries inside a row are jointly independent (rows are unconstrained).
    (hindep : ∀ n, iIndepFun (X n) P)
    -- USER-INPUT: entries are square-integrable, so the row variances are finite.
    (hL2 : ∀ n i, MemLp (X n i) 2 P)
    -- USER-INPUT: entries are centered.
    (hmean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    -- USER-INPUT: the row variances add up to 1 in the limit (normalisation).
    (hvar : Tendsto (fun n => ∑ i, Var[X n i; P]) atTop (𝓝 1))
    -- USER-INPUT: the Lindeberg condition.
    (hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P) atTop (𝓝 0))
    -- USER-INPUT: `Z` realises the standard normal law on the limit space.
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω => ∑ i, X n i ω) atTop Z (fun _ => P) P' where
  forall_aemeasurable n :=
    Finset.aemeasurable_fun_sum _ fun i _ => (hmeas n i).aemeasurable
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    rw! [hZ.map_eq]
    have hcf : ∀ n, charFun (P.map (fun ω => ∑ i, X n i ω)) t
        = ∏ i, charFun (P.map (X n i)) t := fun n => by
      rw [iIndepFun.charFun_map_fun_sum_eq_prod (fun i => (hmeas n i).aemeasurable) (hindep n),
        Finset.prod_apply]
    simpa [hcf] using tendsto_prod_charFun_lindeberg hmeas hindep hL2 hmean hvar hlin t

/-- **Uniformly bounded rows.**

If the entries of the `n`-th row are bounded by a constant `c n` tending to `0`, the
Lindeberg condition is automatic (for `ε > 0` the truncation sets are eventually empty), so
the row sums are asymptotically standard normal as soon as the row variances converge
to `1`. This is the form used for randomization and permutation statistics, where the
summands are explicit bounded functions of the data.

No square-integrability hypothesis is needed: a bounded measurable function on a
probability space lies in `L²`. -/
theorem lindeberg_clt_of_bounded {m : ℕ → ℕ} {X : (n : ℕ) → Fin (m n) → Ω → ℝ}
    {c : ℕ → ℝ} {Z : Ω' → ℝ}
    -- USER-INPUT: every array entry is measurable (data regularity).
    (hmeas : ∀ n i, Measurable (X n i))
    -- USER-INPUT: entries inside a row are jointly independent.
    (hindep : ∀ n, iIndepFun (X n) P)
    -- USER-INPUT: entries are centered.
    (hmean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    -- USER-INPUT: the row variances add up to 1 in the limit (normalisation).
    (hvar : Tendsto (fun n => ∑ i, Var[X n i; P]) atTop (𝓝 1))
    -- USER-INPUT: the `n`-th row is bounded by `c n`.
    (hbdd : ∀ n i ω, |X n i ω| ≤ c n)
    -- USER-INPUT: the bounds are asymptotically negligible.
    (hc : Tendsto c atTop (𝓝 0))
    -- USER-INPUT: `Z` realises the standard normal law on the limit space.
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω => ∑ i, X n i ω) atTop Z (fun _ => P) P' := by
  -- Bounded measurable ⇒ `L²`.
  have hL2 : ∀ n i, MemLp (X n i) 2 P := fun n i =>
    MemLp.of_bound (hmeas n i).aestronglyMeasurable (c n)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hbdd n i ω)
  -- Lindeberg condition: for `ε > 0` the truncation sets are eventually empty (`c n < ε`).
  have hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    intro ε hε
    have key : ∀ᶠ n in atTop,
        (∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P) = 0 := by
      filter_upwards [hc.eventually (eventually_lt_nhds hε)] with n hn
      refine Finset.sum_eq_zero fun i _ => ?_
      have hempty : {ω | ε < |X n i ω|} = (∅ : Set Ω) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact le_trans (hbdd n i ω) hn.le
      rw [hempty]; simp
    exact tendsto_const_nhds.congr' (key.mono fun n hn => hn.symm)
  exact lindeberg_clt hmeas hindep hL2 hmean hvar hlin hZ

/-- **Central limit theorem for weighted sums of an i.i.d. sequence.**

Let `Y₀, Y₁, …` be i.i.d. with mean `0` and variance `σ² > 0`, and let `wₙ,ᵢ` be triangular
weights whose squares are individually negligible relative to their sum,
`maxᵢ wₙ,ᵢ² / ∑ⱼ wₙ,ⱼ² → 0`. Then
$$\frac{\sum_i w_{n,i} Y_i}{\sigma\,\bigl(\sum_i w_{n,i}^2\bigr)^{1/2}}
  \;\rightsquigarrow\; N(0,1).$$

This is `lindeberg_clt` applied to the row `Xₙ,ᵢ := wₙ,ᵢ Yᵢ / (σ (∑ⱼ wₙ,ⱼ²)^{1/2})`, whose
variances sum to `1` exactly and whose Lindeberg sums are controlled by the negligibility
condition together with the single square-integrable law of `Y₀`.

The negligibility hypothesis is spelled `∀ ε > 0, ∀ᶠ n, ∀ i, wₙ,ᵢ² ≤ ε ∑ⱼ wₙ,ⱼ²` — the
`iSup`-free form of `maxᵢ wₙ,ᵢ² / ∑ⱼ wₙ,ⱼ² → 0`. -/
theorem weighted_iid_clt {m : ℕ → ℕ} {Y : ℕ → Ω → ℝ} {w : (n : ℕ) → Fin (m n) → ℝ}
    {σ : ℝ} {Z : Ω' → ℝ}
    -- USER-INPUT: the sampled variables are measurable (data regularity).
    (hmeas : ∀ i, Measurable (Y i))
    -- USER-INPUT: the sample is jointly independent.
    (hindep : iIndepFun Y P)
    -- USER-INPUT: the sample is identically distributed.
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    -- USER-INPUT: square-integrable sampling law.
    (hL2 : MemLp (Y 0) 2 P)
    -- USER-INPUT: the sampling law is centered.
    (hmean : ∫ ω, Y 0 ω ∂P = 0)
    -- USER-INPUT: the scale parameter is positive (nondegenerate sampling law).
    (hσ : 0 < σ)
    -- USER-INPUT: the sampling variance is `σ²`.
    (hvar : Var[Y 0; P] = σ ^ 2)
    -- USER-INPUT: the `n`-th row of weights is not identically zero.
    (hw : ∀ n, 0 < ∑ i, (w n i) ^ 2)
    -- USER-INPUT: individual weights are asymptotically negligible.
    (hneg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i, (w n i) ^ 2 ≤ ε * ∑ j, (w n j) ^ 2)
    -- USER-INPUT: `Z` realises the standard normal law on the limit space.
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution
      (fun n ω => (σ * Real.sqrt (∑ i, (w n i) ^ 2))⁻¹ * ∑ i, w n i * Y (i : ℕ) ω)
      atTop Z (fun _ => P) P' := by
  -- Abbreviations for the weight-square sum `S n`, the normalising scale `s n = σ √(S n)`,
  -- and the normalised row `X n i = (s n)⁻¹ · wₙ,ᵢ · Yᵢ`.
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℝ, S = fun n => ∑ i, (w n i) ^ 2 := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → ℝ, s = fun n => σ * Real.sqrt (S n) := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : (n : ℕ) → Fin (m n) → Ω → ℝ,
      X = fun n i ω => (s n)⁻¹ * w n i * Y (i : ℕ) ω := ⟨_, rfl⟩
  have hσ2 : (0 : ℝ) < σ ^ 2 := pow_pos hσ 2
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hSpos : ∀ n, 0 < S n := by intro n; rw [hSdef]; exact hw n
  have hspos : ∀ n, 0 < s n := by
    intro n; simp only [hsdef]; exact mul_pos hσ (Real.sqrt_pos.2 (hSpos n))
  have hsn2 : ∀ n, (s n) ^ 2 = σ ^ 2 * ∑ i, (w n i) ^ 2 := by
    intro n; simp only [hsdef, hSdef]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  -- The normalised weight squares sum to `1/σ²` on every row.
  have hasum : ∀ n, ∑ i, ((s n)⁻¹ * w n i) ^ 2 = (σ ^ 2)⁻¹ := by
    intro n
    have e : ∑ i, ((s n)⁻¹ * w n i) ^ 2 = (∑ i, (w n i) ^ 2) * ((s n) ^ 2)⁻¹ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, inv_pow, mul_comm]
    rw [e, hsn2 n, mul_inv, mul_comm ((σ ^ 2)⁻¹) ((∑ i, (w n i) ^ 2)⁻¹), ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt (hw n)), one_mul]
  -- Row regularity: measurable, `L²`, centered, independent.
  have hmeas' : ∀ n i, Measurable (X n i) := by
    intro n i; simp only [hXdef]; exact (hmeas ↑i).const_mul _
  have hL2' : ∀ n i, MemLp (X n i) 2 P := by
    intro n i; simp only [hXdef]; exact ((hident ↑i).symm.memLp_snd hL2).const_mul _
  have hmean' : ∀ n i, ∫ ω, X n i ω ∂P = 0 := by
    intro n i; simp only [hXdef]
    rw [integral_const_mul, ((hident ↑i).integral_eq).trans hmean, mul_zero]
  have hindep' : ∀ n, iIndepFun (X n) P := by
    intro n
    have h1 : iIndepFun (fun i : Fin (m n) => Y (↑i : ℕ)) P :=
      iIndepFun.precomp Fin.val_injective hindep
    have h2 := h1.comp (fun i : Fin (m n) => fun y : ℝ => (s n)⁻¹ * w n i * y)
      (fun i => measurable_id.const_mul _)
    refine (iIndepFun_congr (fun i => ?_)).2 h2
    filter_upwards with ω; simp only [hXdef, Function.comp]
  -- Row variances sum to `1`, hence trivially tend to `1`.
  have hvarval : ∀ n, ∑ i, Var[X n i; P] = 1 := by
    intro n
    have hVi : ∀ i, Var[X n i; P] = ((s n)⁻¹ * w n i) ^ 2 * σ ^ 2 := by
      intro i; simp only [hXdef]
      rw [variance_const_mul, (hident ↑i).variance_eq, hvar]
    simp_rw [hVi]
    rw [← Finset.sum_mul, hasum n, inv_mul_cancel₀ (ne_of_gt hσ2)]
  have hvar' : Tendsto (fun n => ∑ i, Var[X n i; P]) atTop (𝓝 1) := by
    have hcongr : (fun n => ∑ i, Var[X n i; P]) = fun _ => (1 : ℝ) := funext hvarval
    rw [hcongr]; exact tendsto_const_nhds
  -- The `L²`-tail of the sampling law vanishes: `∫_{K < |Y₀|} Y₀² → 0` as `K → ∞`.
  have hsq0 : Integrable (fun ω => (Y 0 ω) ^ 2) P := hL2.integrable_sq
  obtain ⟨tail, htaildef⟩ : ∃ tail : ℕ → ℝ,
      tail = fun (K : ℕ) => ∫ ω in {ω | (K : ℝ) < |Y 0 ω|}, (Y 0 ω) ^ 2 ∂P := ⟨_, rfl⟩
  have htail0 : Tendsto tail atTop (𝓝 0) := by
    simp only [htaildef]
    have hsm : ∀ K : ℕ, MeasurableSet {ω | (K : ℝ) < |Y 0 ω|} := fun K =>
      measurableSet_lt measurable_const (hmeas 0).abs
    have hanti : Antitone fun K : ℕ => {ω | (K : ℝ) < |Y 0 ω|} := by
      intro a b hab ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      exact lt_of_le_of_lt (by exact_mod_cast hab) hω
    have hint : ∃ K : ℕ, IntegrableOn (fun ω => (Y 0 ω) ^ 2) {ω | (K : ℝ) < |Y 0 ω|} P :=
      ⟨0, hsq0.integrableOn⟩
    have hlim := tendsto_setIntegral_of_antitone hsm hanti hint
    have hempty : ⋂ K : ℕ, {ω | (K : ℝ) < |Y 0 ω|} = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_lt]
      obtain ⟨K, hK⟩ := exists_nat_gt |Y 0 ω|
      exact ⟨K, hK.le⟩
    rw [hempty] at hlim
    simpa using hlim
  -- Identically-distributed rows share the same tail integral.
  have htaileq : ∀ (i K : ℕ),
      ∫ ω in {ω | (K : ℝ) < |Y i ω|}, (Y i ω) ^ 2 ∂P = tail K := by
    intro i K
    have hset : ∀ j : ℕ, MeasurableSet {ω | (K : ℝ) < |Y j ω|} := fun j =>
      measurableSet_lt measurable_const (hmeas j).abs
    have hg : Measurable fun y : ℝ => if (K : ℝ) < |y| then y ^ 2 else 0 :=
      Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
        (measurable_id.pow_const 2) measurable_const
    have hcomp : ∀ j : ℕ, ∫ ω, (if (K : ℝ) < |Y j ω| then (Y j ω) ^ 2 else 0) ∂P
        = ∫ ω in {ω | (K : ℝ) < |Y j ω|}, (Y j ω) ^ 2 ∂P := by
      intro j
      rw [← integral_indicator (hset j)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases h : (K : ℝ) < |Y j ω| <;> simp [Set.indicator, h]
    simp only [htaildef]
    rw [← hcomp i, ← hcomp 0]
    simpa [Function.comp] using ((hident i).comp hg).integral_eq
  -- Lindeberg's condition for the normalised row, from weight negligibility.
  have hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    intro ε hε
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · -- Each Lindeberg sum is nonnegative.
      refine Eventually.of_forall fun n => hb.trans_le (Finset.sum_nonneg fun i _ => ?_)
      exact setIntegral_nonneg (measurableSet_lt measurable_const (hmeas' n i).abs)
        fun ω _ => sq_nonneg _
    · -- Upper bound: pick a tail level `K` making `tail K < σ² b`, then use negligibility.
      obtain ⟨K, hKtail, hK1⟩ :=
        (((tendsto_order.1 htail0).2 (σ ^ 2 * b) (mul_pos hσ2 hb)).and
          (eventually_ge_atTop 1)).exists
      have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
      filter_upwards [hneg (σ ^ 2 * (ε / K) ^ 2) (by positivity)] with n hn
      -- Uniform bound on the normalised weights from negligibility.
      have haik : ∀ i, |(s n)⁻¹ * w n i| ≤ ε / K := by
        intro i
        have hsq : ((s n)⁻¹ * w n i) ^ 2 ≤ (ε / K) ^ 2 := by
          have e1 : ((s n)⁻¹ * w n i) ^ 2 = (w n i) ^ 2 / (s n) ^ 2 := by
            rw [mul_pow, inv_pow]; ring
          rw [e1, hsn2 n, div_le_iff₀ (mul_pos hσ2 (hw n))]
          calc (w n i) ^ 2 ≤ σ ^ 2 * (ε / K) ^ 2 * ∑ i, (w n i) ^ 2 := hn i
            _ = (ε / K) ^ 2 * (σ ^ 2 * ∑ i, (w n i) ^ 2) := by ring
        calc |(s n)⁻¹ * w n i| = Real.sqrt (((s n)⁻¹ * w n i) ^ 2) :=
              (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt ((ε / K) ^ 2) := Real.sqrt_le_sqrt hsq
          _ = ε / K := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      -- Per-entry bound of the truncated second moment by the shared tail.
      have hterm : ∀ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P
          ≤ ((s n)⁻¹ * w n i) ^ 2 * tail K := by
        intro i
        have hXsq : ∀ ω, (X n i ω) ^ 2 = ((s n)⁻¹ * w n i) ^ 2 * (Y (↑i : ℕ) ω) ^ 2 := by
          intro ω; simp only [hXdef]; rw [mul_pow]
        rw [setIntegral_congr_fun (measurableSet_lt measurable_const (hmeas' n i).abs)
              (fun ω _ => hXsq ω), integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [← htaileq (↑i) K]
        refine setIntegral_mono_set (((hident ↑i).symm.memLp_snd hL2).integrable_sq).integrableOn
          (Eventually.of_forall fun ω => sq_nonneg _) (Eventually.of_forall fun ω hω => ?_)
        -- `{ε < |X n i|} ⊆ {K < |Y i|}`.
        have h1 : ε < |(s n)⁻¹ * w n i| * |Y (↑i : ℕ) ω| := by
          rw [← abs_mul]; simpa only [hXdef] using! hω
        have h3 : ε < (ε / K) * |Y (↑i : ℕ) ω| :=
          lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_right (haik i) (abs_nonneg _))
        show (K : ℝ) < |Y (↑i : ℕ) ω|
        by_contra hcon
        push_neg at hcon
        have hle : (ε / K) * |Y (↑i : ℕ) ω| ≤ (ε / K) * K :=
          mul_le_mul_of_nonneg_left hcon (by positivity)
        rw [div_mul_cancel₀ ε (ne_of_gt hKpos)] at hle
        exact absurd (lt_of_lt_of_le h3 hle) (lt_irrefl ε)
      -- Sum the per-entry bounds and conclude.
      calc ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P
          ≤ ∑ i, ((s n)⁻¹ * w n i) ^ 2 * tail K := Finset.sum_le_sum fun i _ => hterm i
        _ = (σ ^ 2)⁻¹ * tail K := by rw [← Finset.sum_mul, hasum n]
        _ < b := by
            have hlt : (σ ^ 2)⁻¹ * tail K < (σ ^ 2)⁻¹ * (σ ^ 2 * b) :=
              mul_lt_mul_of_pos_left hKtail (inv_pos.2 hσ2)
            rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hσ2), one_mul] at hlt
  -- Assemble: rewrite the target row sum and apply the triangular-array CLT.
  have hgoaleq : (fun n ω => (σ * Real.sqrt (∑ i, (w n i) ^ 2))⁻¹ * ∑ i, w n i * Y (↑i : ℕ) ω)
      = fun n ω => ∑ i, X n i ω := by
    funext n ω
    simp only [hXdef, hsdef, hSdef]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hgoaleq]
  exact lindeberg_clt hmeas' hindep' hL2' hmean' hvar' hlin hZ

/-! ### Truncation bricks for the triangular weak law

The weak law below is proved by a *fixed-level* truncation (not the textbook `n`-dependent
one): the excess `(|y| − K)⁺` has an integral that converges along the rows because both
`∫|y| dGₙ → ∫|y| dν` (the `L¹` hypothesis) and `∫ (|y| ∧ K) dGₙ → ∫ (|y| ∧ K) dν` (weak
convergence against a *bounded continuous* test function) hold. That is exactly the amount of
uniform integrability the argument needs, and it is obtained without any separate uniform
integrability development. -/

/-- Package a bounded continuous real function on the line as an element of `ℝ →ᵇ ℝ`. -/
private noncomputable def wllnBcf (f : ℝ → ℝ) (hf : Continuous f) {C : ℝ}
    (hC : ∀ y, |f y| ≤ C) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * C) fun x y => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    have h1 := hC x
    have h2 := hC y
    have h3 : |f x - f y| ≤ |f x| + |f y| := by
      have hx := le_abs_self (f x)
      have hx' := neg_abs_le (f x)
      have hy := le_abs_self (f y)
      have hy' := neg_abs_le (f y)
      rw [abs_le]
      constructor <;> linarith
    linarith

@[simp]
private lemma wllnBcf_apply (f : ℝ → ℝ) (hf : Continuous f) {C : ℝ} (hC : ∀ y, |f y| ≤ C)
    (y : ℝ) : wllnBcf f hf hC y = f y := rfl

/-- The two-sided truncation of the identity at level `K`. -/
private noncomputable def wllnTrunc (K : ℝ) (y : ℝ) : ℝ := max (-K) (min K y)

private lemma continuous_wllnTrunc (K : ℝ) : Continuous (wllnTrunc K) := by
  unfold wllnTrunc; fun_prop

private lemma abs_wllnTrunc_le {K : ℝ} (hK : 0 ≤ K) (y : ℝ) : |wllnTrunc K y| ≤ K :=
  abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- The truncation error is the excess `(|y| − K)⁺`. -/
private lemma wllnTrunc_sub {K : ℝ} (hK : 0 ≤ K) (y : ℝ) :
    |y - wllnTrunc K y| = max (|y| - K) 0 := by
  unfold wllnTrunc
  rcases le_total y (-K) with h1 | h1
  · have hyK : y ≤ K := h1.trans (by linarith)
    rw [min_eq_right hyK, max_eq_left h1, abs_of_nonpos (by linarith : y - -K ≤ 0),
      abs_of_nonpos (by linarith : y ≤ 0), max_eq_left (by linarith)]
    ring
  · rcases le_total y K with h2 | h2
    · have habs : |y| ≤ K := abs_le.mpr ⟨by linarith, h2⟩
      rw [min_eq_right h2, max_eq_right h1, sub_self, abs_zero,
        max_eq_right (by linarith)]
    · rw [min_eq_left h2, max_eq_right (by linarith : -K ≤ K),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - K),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ y), max_eq_left (by linarith)]

/-- The excess is the difference between `|y|` and its own truncation `|y| ∧ K`. -/
private lemma wlln_excess_eq {K : ℝ} (hK : 0 ≤ K) (y : ℝ) :
    max (|y| - K) 0 = |y| - min |y| K := by
  rcases le_total |y| K with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]

/-- `y ↦ |y| ∧ K` is a bounded continuous test function. -/
private noncomputable def wllnAbsMin (K : ℝ) (hK : 0 ≤ K) : ℝ →ᵇ ℝ :=
  wllnBcf (fun y => min |y| K) (by fun_prop) (C := K) fun y =>
    abs_le.mpr ⟨by
        have : (0 : ℝ) ≤ min |y| K := le_min (abs_nonneg y) hK
        linarith, min_le_right _ _⟩

/-- The excess integral is finite and computed by subtraction, on any probability measure with
an integrable identity. -/
private lemma wlln_integral_excess {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {K : ℝ} (hK : 0 ≤ K) :
    ∫ y, max (|y| - K) 0 ∂μ = (∫ y, |y| ∂μ) - ∫ y, min |y| K ∂μ := by
  have habs : Integrable (fun y : ℝ => |y|) μ := hμ.abs
  have hmin : Integrable (fun y : ℝ => min |y| K) μ := by
    refine Integrable.mono' (integrable_const K) (by fun_prop) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg y) hK)]
    exact min_le_right _ _
  rw [← integral_sub habs hmin]
  exact integral_congr_ae (.of_forall fun y => wlln_excess_eq hK y)

/-- **Excess integrals converge along the rows.** This is the uniform-integrability input of
the weak law, obtained from weak convergence plus convergence of first absolute moments. -/
private lemma wlln_tendsto_excess {G : ℕ → Measure ℝ} {ν : Measure ℝ}
    [∀ n, IsProbabilityMeasure (G n)] [IsProbabilityMeasure ν]
    (hGint : ∀ n, Integrable id (G n)) (hν : Integrable id ν)
    (hweak : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ y, f y ∂(G n)) atTop (𝓝 (∫ y, f y ∂ν)))
    (hL1 : Tendsto (fun n => ∫ y, |y| ∂(G n)) atTop (𝓝 (∫ y, |y| ∂ν)))
    {K : ℝ} (hK : 0 ≤ K) :
    Tendsto (fun n => ∫ y, max (|y| - K) 0 ∂(G n)) atTop
      (𝓝 (∫ y, max (|y| - K) 0 ∂ν)) := by
  have hmin := hweak (wllnAbsMin K hK)
  simp only [wllnAbsMin, wllnBcf_apply] at hmin
  have hlim := hL1.sub hmin
  rw [← wlln_integral_excess hν hK] at hlim
  refine hlim.congr fun n => ?_
  rw [← wlln_integral_excess (hGint n) hK]

/-- The excess integral of the limit law tends to `0` as the truncation level grows. -/
private lemma wlln_excess_tendsto_zero {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : Integrable id ν) :
    Tendsto (fun K : ℕ => ∫ y, max (|y| - (K : ℝ)) 0 ∂ν) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun (K : ℕ) (y : ℝ) => max (|y| - (K : ℝ)) 0) (f := fun _ : ℝ => (0 : ℝ))
    (bound := fun y : ℝ => |y|) (fun K => by fun_prop) hν.abs
    (fun K => .of_forall fun y => by
      have hK : (0 : ℝ) ≤ (K : ℕ) := Nat.cast_nonneg K
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith) (abs_nonneg y))
    (.of_forall fun y => by
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge |y|
      filter_upwards [eventually_ge_atTop N] with K hK
      have : |y| - (K : ℝ) ≤ 0 := by
        have : ((N : ℕ) : ℝ) ≤ (K : ℝ) := Nat.cast_le.mpr hK
        linarith
      rw [max_eq_right this])
  simpa using h

/-- **The per-row estimate of the weak law.** With a truncation at a fixed level `K` whose
centring error is already smaller than `ε/3`, the deviation probability splits into a
Chebyshev term for the truncated average and a Markov term for the excess. -/
private lemma wlln_row_bound {n : ℕ} (hn : 0 < n) {Yn : Fin n → Ω → ℝ} {Gn : Measure ℝ}
    [IsProbabilityMeasure Gn] (hmeas : ∀ i, Measurable (Yn i)) (hindep : iIndepFun Yn P)
    (hlaw : ∀ i, P.map (Yn i) = Gn) (hGint : Integrable id Gn) {K : ℝ} (hK : 0 ≤ K)
    {ε : ℝ} (hε : 0 < ε) {m : ℝ} (ham : |(∫ y, wllnTrunc K y ∂Gn) - m| < ε / 3) :
    P {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i, Yn i ω - m|}
      ≤ ENNReal.ofReal (9 * K ^ 2 / (n * ε ^ 2))
        + ENNReal.ofReal (3 * (∫ y, max (|y| - K) 0 ∂Gn) / ε) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set Z : Fin n → Ω → ℝ := fun i ω => wllnTrunc K (Yn i ω) with hZdef
  set a : ℝ := ∫ y, wllnTrunc K y ∂Gn with hadef
  have hZmeas : ∀ i, Measurable (Z i) := fun i =>
    (continuous_wllnTrunc K).measurable.comp (hmeas i)
  have hZbdd : ∀ i ω, |Z i ω| ≤ K := fun i ω => abs_wllnTrunc_le hK _
  have hZmem : ∀ i, MemLp (Z i) 2 P := fun i =>
    MemLp.of_bound (hZmeas i).aestronglyMeasurable K
      (.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hZbdd i ω)
  have hZmean : ∀ i, ∫ ω, Z i ω ∂P = a := by
    intro i
    rw [hadef, ← hlaw i,
      integral_map (hmeas i).aemeasurable (continuous_wllnTrunc K).aestronglyMeasurable]
  -- the truncated average
  set S : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i, Z i ω with hSdef
  have hSmem : MemLp S 2 P :=
    (memLp_finset_sum (μ := P) (p := 2) Finset.univ fun i _ => hZmem i).const_mul _
  have hSmean : ∫ ω, S ω ∂P = a := by
    have hint : ∀ i : Fin n, Integrable (Z i) P := fun i => (hZmem i).integrable one_le_two
    rw [hSdef]
    rw [integral_const_mul, integral_finset_sum _ fun i _ => hint i]
    simp only [hZmean]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      inv_mul_cancel_left₀ hnR.ne']
  -- variance of the truncated average
  have hvarZ : ∀ i, variance (Z i) P ≤ K ^ 2 := by
    intro i
    refine (variance_le_expectation_sq (hZmeas i).aestronglyMeasurable).trans ?_
    have hsq : Integrable (fun ω => Z i ω ^ 2) P := (hZmem i).integrable_sq
    have : ∫ ω, Z i ω ^ 2 ∂P ≤ ∫ _ω, K ^ 2 ∂P :=
      integral_mono hsq (integrable_const _) fun ω => by
        have := hZbdd i ω
        nlinarith [abs_nonneg (Z i ω), sq_abs (Z i ω)]
    simpa using this
  have hSvar : variance S P ≤ K ^ 2 / n := by
    have hindepZ : iIndepFun Z P := by
      have := hindep.comp (fun _ : Fin n => wllnTrunc K)
        (fun _ => (continuous_wllnTrunc K).measurable)
      exact this
    have hfun : (fun ω => ∑ i, Z i ω) = ∑ i : Fin n, Z i := by
      funext ω; simp
    have h2 : variance (fun ω => ∑ i, Z i ω) P = ∑ i, variance (Z i) P := by
      rw [hfun]
      exact IndepFun.variance_sum (fun i _ => hZmem i)
        fun i _ j _ hij => hindepZ.indepFun hij
    have h3 : ∑ i, variance (Z i) P ≤ (n : ℝ) * K ^ 2 := by
      calc ∑ i, variance (Z i) P ≤ ∑ _i : Fin n, K ^ 2 := Finset.sum_le_sum fun i _ => hvarZ i
        _ = (n : ℝ) * K ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hSdef, variance_const_mul, h2]
    calc ((n : ℝ)⁻¹) ^ 2 * ∑ i, variance (Z i) P
        ≤ ((n : ℝ)⁻¹) ^ 2 * ((n : ℝ) * K ^ 2) := by
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = K ^ 2 / n := by field_simp
  -- the excess average
  set W : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i, |Yn i ω - Z i ω| with hWdef
  have hYint : ∀ i, Integrable (Yn i) P := by
    intro i
    have h := hGint
    rw [← hlaw i] at h
    exact (integrable_map_measure aestronglyMeasurable_id (hmeas i).aemeasurable).mp h
  have hWterm : ∀ i : Fin n, Integrable (fun ω => |Yn i ω - Z i ω|) P :=
    fun i => ((hYint i).sub ((hZmem i).integrable one_le_two)).abs
  have hWint : Integrable W P := by
    refine Integrable.const_mul ?_ _
    exact integrable_finset_sum _ fun i _ => hWterm i
  have hWnn : ∀ ω, 0 ≤ W ω := by
    intro ω
    have : (0 : ℝ) ≤ ∑ i, |Yn i ω - Z i ω| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    positivity
  have hWmean : ∫ ω, W ω ∂P = ∫ y, max (|y| - K) 0 ∂Gn := by
    have hterm : ∀ i : Fin n,
        ∫ ω, |Yn i ω - Z i ω| ∂P = ∫ y, max (|y| - K) 0 ∂Gn := by
      intro i
      have h1 : (fun ω => |Yn i ω - Z i ω|) = fun ω => max (|Yn i ω| - K) 0 := by
        funext ω; exact wllnTrunc_sub hK _
      rw [h1, ← hlaw i,
        integral_map (hmeas i).aemeasurable (by fun_prop)]
    rw [hWdef, integral_const_mul, integral_finset_sum _ fun i _ => hWterm i]
    simp only [hterm]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      inv_mul_cancel_left₀ hnR.ne']
  -- the deviation event is covered by the two elementary events
  have hsub : {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i, Yn i ω - m|}
      ⊆ {ω | ε / 3 ≤ |S ω - a|} ∪ {ω | ε / 3 ≤ W ω} := by
    intro ω hω
    by_cases h1 : ε / 3 ≤ |S ω - a|
    · exact Or.inl h1
    by_cases h2 : ε / 3 ≤ W ω
    · exact Or.inr h2
    exfalso
    push_neg at h1 h2
    have hgap : |(n : ℝ)⁻¹ * ∑ i, Yn i ω - S ω| ≤ W ω := by
      have hrw : (n : ℝ)⁻¹ * ∑ i, Yn i ω - S ω
          = (n : ℝ)⁻¹ * ∑ i, (Yn i ω - Z i ω) := by
        rw [hSdef]; simp [Finset.sum_sub_distrib, mul_sub]
      rw [hrw, hWdef, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hnR))]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (le_of_lt (inv_pos.mpr hnR))
    have hchain : |(n : ℝ)⁻¹ * ∑ i, Yn i ω - m|
        ≤ |(n : ℝ)⁻¹ * ∑ i, Yn i ω - S ω| + |S ω - a| + |a - m| := by
      have h3 := abs_sub_le ((n : ℝ)⁻¹ * ∑ i, Yn i ω) (S ω) m
      have h4 := abs_sub_le (S ω) a m
      linarith
    have hmem : ε ≤ |(n : ℝ)⁻¹ * ∑ i, Yn i ω - m| := hω
    have ham' : |a - m| < ε / 3 := ham
    linarith
  -- Chebyshev and Markov
  have hcheb : P {ω | ε / 3 ≤ |S ω - a|} ≤ ENNReal.ofReal (9 * K ^ 2 / (n * ε ^ 2)) := by
    have h := meas_ge_le_variance_div_sq (μ := P) hSmem (by linarith : (0 : ℝ) < ε / 3)
    rw [hSmean] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hpos : (0 : ℝ) < (ε / 3) ^ 2 := by positivity
    rw [div_le_div_iff₀ hpos (by positivity)]
    have hv := hSvar
    have hK2 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have : variance S P * (n * ε ^ 2) ≤ K ^ 2 / n * (n * ε ^ 2) := by
      exact mul_le_mul_of_nonneg_right hv (by positivity)
    calc variance S P * (n * ε ^ 2) ≤ K ^ 2 / n * (n * ε ^ 2) := this
      _ = 9 * K ^ 2 * (ε / 3) ^ 2 := by field_simp; ring
  have hmark : P {ω | ε / 3 ≤ W ω}
      ≤ ENNReal.ofReal (3 * (∫ y, max (|y| - K) 0 ∂Gn) / ε) := by
    have h := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := W)
      (.of_forall hWnn) hWint (ε / 3)
    rw [hWmean] at h
    have hb : P.real {ω | ε / 3 ≤ W ω} ≤ 3 * (∫ y, max (|y| - K) 0 ∂Gn) / ε := by
      rw [le_div_iff₀ hε]
      linarith [h]
    have hnn : (0 : ℝ) ≤ 3 * (∫ y, max (|y| - K) 0 ∂Gn) / ε := by
      have hint0 : (0 : ℝ) ≤ ∫ y, max (|y| - K) 0 ∂Gn :=
        integral_nonneg fun y => le_max_right _ _
      positivity
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top P _) hnn).mpr hb
  calc P {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i, Yn i ω - m|}
      ≤ P ({ω | ε / 3 ≤ |S ω - a|} ∪ {ω | ε / 3 ≤ W ω}) := measure_mono hsub
    _ ≤ P {ω | ε / 3 ≤ |S ω - a|} + P {ω | ε / 3 ≤ W ω} := measure_union_le _ _
    _ ≤ _ := add_le_add hcheb hmark

/-- **Weak law of large numbers for a triangular array** (first-absolute-moment form).

Let the `n`-th row `Yₙ,₀, …, Yₙ,ₙ₋₁` consist of independent variables with common law `Gₙ`.
If `Gₙ` converges weakly to `ν` and the first absolute moments converge,
`∫ |y| dGₙ → ∫ |y| dν < ∞`, then the row averages converge in probability to the limiting
mean:
$$\bar Y_n = n^{-1}\sum_{i<n} Y_{n,i} \;\xrightarrow{\;P\;}\; \int y \,\mathrm d\nu .$$

Weak convergence of the row laws alone is *not* enough (mass can escape to infinity); the
convergence of first absolute moments is exactly the uniform-integrability substitute that
makes the truncation argument work, and it is what the bootstrap applications can verify.

Convergence of the row laws is stated on `ProbabilityMeasure ℝ`, since the rows carry no
common random-variable representation.

## ⚠ THE FROZEN STATEMENT WAS **FALSE** — repaired below, counterexample retained

The frozen hypothesis `hL1` is stated with the **Bochner** integral `∫ y, |y| ∂(G n)`, which is
the
junk value `0` whenever `|·|` is *not* `G n`-integrable (`MeasureTheory.integral_undef`).
Consequently `hL1` says nothing at all about rows with an infinite first absolute moment: it
is satisfied *vacuously* by any sequence of non-integrable `Gₙ` as soon as the limit has
`∫|y| dν = 0`. That loophole destroys the conclusion.

**Counterexample.** Let `μₙ` be any probability measure supported in `[n³, ∞)` with
`∫ |y| dμₙ = ∞` (e.g. the law of `n³ / U` with `U` uniform on `(0,1)`, a Pareto law of index
`1`), and put
`Gₙ = (1 − 1/n) · δ₀ + (1/n) · μₙ`, `ν = δ₀`.
All hypotheses hold:

* `IsProbabilityMeasure (Gₙ)`, `IsProbabilityMeasure ν`;
* `hweak`: for bounded continuous `f`, `∫ f dGₙ = (1 − 1/n) f(0) + (1/n) ∫ f dμₙ → f(0)`,
  since `|∫ f dμₙ| ≤ ‖f‖∞`; so `Gₙ ⇒ δ₀ = ν`;
* `hL1`: `|·|` is not `Gₙ`-integrable (`(1/n) ∫|y| dμₙ = ∞`), so the Bochner integral takes
  its junk value: `∫ |y| dGₙ = 0` for every `n`, and `∫ |y| dν = 0`. The sequence is
  constantly `0` and converges to `0`;
* `hν`: `Integrable id δ₀`, and `∫ y dν = 0`.

But the conclusion fails. Let `Nₙ` be the number of row entries that are nonzero; `Nₙ` is
`Binomial(n, 1/n)`, so `P(Nₙ ≥ 1) = 1 − (1 − 1/n)ⁿ → 1 − e⁻¹ ≈ 0.632`. On `{Nₙ ≥ 1}` every
nonzero entry is `≥ n³`, hence
`n⁻¹ ∑_{i<n} Yₙ,ᵢ ≥ n⁻¹ · n³ = n² ≥ 1`,
so `P{ω | 1 ≤ |n⁻¹ ∑ᵢ Yₙ,ᵢ − 0|} ≥ 1 − (1 − 1/n)ⁿ ↛ 0`: `TendstoInMeasure` fails at `ε = 1`.

(The proof note that used to sit in the body asserted the opposite — that a heavy-tailed
`Gₙ = (1−1/n)δ₀ + (1/n)·Cauchy` still concentrates. That happens to be true for the *fixed*
Cauchy tail, because `n⁻¹ × O_P(1)` many Cauchy draws is `O_P(1/n)`; it is not true once the
escaping mass is placed at height `n³`, which the hypotheses permit.)

**Repair (minimal, documented).** Exactly one hypothesis is added,

`(hGint : ∀ n, Integrable id (G n))`,

which closes the junk-value loophole and nothing else: it is precisely what makes `hL1` say
what it reads as saying. (The equivalent alternative is to restate `hL1` with the lower
Lebesgue integral `∫⁻ y, ‖y‖₊ ∂(G n)` in `ℝ≥0∞`; the added hypothesis is the less invasive of
the two, since every downstream row law is an image measure of an integrable variable.) No
other hypothesis is touched, and the conclusion is unchanged. The counterexample above is
killed immediately: its `Gₙ` has `∫⁻|y| dGₙ = ∞`, so `id` is not `Gₙ`-integrable.

**Proof (as formalised).** Not the textbook `n`-dependent truncation, but a cheaper
*fixed-level* one, which avoids developing uniform integrability as a separate notion. Fix
`K ≥ 0` and split `Y = τ_K(Y) + (Y − τ_K(Y))` with `τ_K y = max (−K) (min K y)`:

* the truncated average is an average of `n` independent variables bounded by `K`, so
  `Var[n⁻¹∑ τ_K(Yₙ,ᵢ)] ≤ K²/n` and Chebyshev gives `9K²/(nε²)`;
* the excess average is controlled by Markov, `E|n⁻¹∑ (Yₙ,ᵢ − τ_K(Yₙ,ᵢ))| ≤ ∫ (|y|−K)⁺ dGₙ`;
* the centring `∫ τ_K dGₙ` converges to `∫ τ_K dν` because `τ_K` is *bounded continuous*
  (`hweak`), and `|∫ τ_K dν − ∫ y dν| ≤ ∫ (|y|−K)⁺ dν`.

The single quantitative input is that the excess integrals converge,
`∫ (|y|−K)⁺ dGₙ → ∫ (|y|−K)⁺ dν` (`wlln_tendsto_excess`), which follows from `hL1` **plus**
weak convergence against the bounded continuous `y ↦ |y| ∧ K`, using `hGint` to split
`(|y|−K)⁺ = |y| − (|y| ∧ K)` under the Bochner integral. Letting `K → ∞` afterwards
(`wlln_excess_tendsto_zero`, dominated convergence under `hν`) makes both `ν`-side errors as
small as desired. -/
theorem triangular_wlln_of_L1 {Y : (n : ℕ) → Fin n → Ω → ℝ} {G : ℕ → Measure ℝ}
    {ν : Measure ℝ} [∀ n, IsProbabilityMeasure (G n)] [IsProbabilityMeasure ν]
    -- USER-INPUT: every array entry is measurable (data regularity).
    (hmeas : ∀ n i, Measurable (Y n i))
    -- USER-INPUT: entries inside a row are jointly independent.
    (hindep : ∀ n, iIndepFun (Y n) P)
    -- USER-INPUT: the `n`-th row is identically distributed with law `G n`.
    (hlaw : ∀ n (i : Fin n), P.map (Y n i) = G n)
    -- USER-INPUT (REPAIR): every row law has a finite first absolute moment.  Without this the
    -- statement is FALSE: see the counterexample in the docstring, where `hL1` holds only
    -- because the Bochner integral `∫ y, |y| ∂(G n)` takes its junk value `0`.
    (hGint : ∀ n, Integrable id (G n))
    -- USER-INPUT: the row laws converge weakly to `ν` (portmanteau form: integration against
    -- bounded continuous test functions; matches the convention used elsewhere in the library).
    (hweak : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ y, f y ∂(G n)) atTop (𝓝 (∫ y, f y ∂ν)))
    -- USER-INPUT: the limit law has a finite first moment.
    (hν : Integrable id ν)
    -- USER-INPUT: the first absolute moments converge.
    (hL1 : Tendsto (fun n => ∫ y, |y| ∂(G n)) atTop (𝓝 (∫ y, |y| ∂ν))) :
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i, Y n i ω) atTop
      (fun _ => ∫ y, y ∂ν) := by
  -- Fixed-level truncation.  See the docstring for the counterexample that forces `hGint`.
  refine tendstoInMeasure_of_ne_top ?_
  intro e he hetop
  -- work with the real deviation level `ε = e.toReal`
  set ε : ℝ := e.toReal with hεdef
  have hε : (0 : ℝ) < ε := ENNReal.toReal_pos he.ne' hetop
  have hset : ∀ n : ℕ,
      {ω | e ≤ edist ((n : ℝ)⁻¹ * ∑ i, Y n i ω) (∫ y, y ∂ν)}
        = {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i, Y n i ω - ∫ y, y ∂ν|} := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq, edist_dist, Real.dist_eq]
    exact ENNReal.le_ofReal_iff_toReal_le hetop (abs_nonneg _)
  simp only [hset]
  rw [ENNReal.tendsto_nhds_zero]
  intro ρ hρ
  -- replace the `ℝ≥0∞` tolerance by a real one
  obtain ⟨δ, hδ0, hδρ⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ρ := by
    rcases eq_top_or_lt_top ρ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨ρ.toReal, ENNReal.toReal_pos hρ.ne' h.ne, by rw [ENNReal.ofReal_toReal h.ne]⟩
  set m : ℝ := ∫ y, y ∂ν with hmdef
  -- choose the truncation level: the limiting excess integral must beat both budgets
  obtain ⟨Kn, hKn⟩ : ∃ Kn : ℕ,
      ∫ y, max (|y| - (Kn : ℝ)) 0 ∂ν < min (ε / 6) (δ * ε / 12) :=
    ((wlln_excess_tendsto_zero hν).eventually
      (gt_mem_nhds (lt_min (by linarith) (by positivity)))).exists
  set K : ℝ := (Kn : ℝ) with hKdef
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hνy : Integrable (fun y : ℝ => y) ν := hν
  have hti : Integrable (fun y : ℝ => wllnTrunc K y) ν :=
    Integrable.mono' (integrable_const K) (continuous_wllnTrunc K).aestronglyMeasurable
      (.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_wllnTrunc_le hK y)
  -- the two convergent sequences of the argument
  have hexc := wlln_tendsto_excess hGint hν hweak hL1 hK
  have htr : Tendsto (fun n => ∫ y, wllnTrunc K y ∂(G n)) atTop
      (𝓝 (∫ y, wllnTrunc K y ∂ν)) := by
    have h := hweak (wllnBcf (wllnTrunc K) (continuous_wllnTrunc K) (abs_wllnTrunc_le hK))
    simpa using h
  -- the centring error of the truncation on the limit law is the limiting excess
  have hcent : |(∫ y, wllnTrunc K y ∂ν) - m| ≤ ∫ y, max (|y| - K) 0 ∂ν := by
    rw [hmdef]
    calc |(∫ y, wllnTrunc K y ∂ν) - ∫ y, y ∂ν|
        = |∫ y, (wllnTrunc K y - y) ∂ν| := by rw [integral_sub hti hνy]
      _ ≤ ∫ y, |wllnTrunc K y - y| ∂ν := by
          simpa only [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := ν) fun y => wllnTrunc K y - y
      _ = ∫ y, max (|y| - K) 0 ∂ν := by
          refine integral_congr_ae (.of_forall fun y => ?_)
          have hy := wllnTrunc_sub hK y
          rw [abs_sub_comm] at hy
          exact hy
  -- eventually the centring is accurate to `ε/3`
  have hev1 : ∀ᶠ n in atTop, |(∫ y, wllnTrunc K y ∂(G n)) - m| < ε / 3 := by
    have hc : |(∫ y, wllnTrunc K y ∂ν) - m| < ε / 6 :=
      lt_of_le_of_lt hcent (lt_of_lt_of_le hKn (min_le_left _ _))
    filter_upwards [htr.eventually
      (eventually_abs_sub_lt (∫ y, wllnTrunc K y ∂ν) (by linarith : (0 : ℝ) < ε / 6))] with n hn
    have h2 := abs_sub_le (∫ y, wllnTrunc K y ∂(G n)) (∫ y, wllnTrunc K y ∂ν) m
    linarith
  -- eventually the Markov term is at most `δ/2`
  have hev2 : ∀ᶠ n in atTop, 3 * (∫ y, max (|y| - K) 0 ∂(G n)) / ε ≤ δ / 2 := by
    have hr2 : ∫ y, max (|y| - K) 0 ∂ν < δ * ε / 12 :=
      lt_of_lt_of_le hKn (min_le_right _ _)
    filter_upwards [hexc.eventually (eventually_abs_sub_lt (∫ y, max (|y| - K) 0 ∂ν)
      (by positivity : (0 : ℝ) < δ * ε / 12))] with n hn
    have hb : ∫ y, max (|y| - K) 0 ∂(G n) < δ * ε / 6 := by
      have h3 := abs_lt.mp hn
      linarith [h3.2]
    rw [div_le_iff₀ hε]
    linarith
  -- eventually the Chebyshev term is at most `δ/2`
  have hev3 : ∀ᶠ n : ℕ in atTop, 9 * K ^ 2 / ((n : ℝ) * ε ^ 2) ≤ δ / 2 := by
    obtain ⟨N, hN⟩ := exists_nat_ge (18 * K ^ 2 / (δ * ε ^ 2))
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
    have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left N 1) hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have h1 : 18 * K ^ 2 / (δ * ε ^ 2) ≤ (n : ℝ) := hN.trans hnN
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ * ε ^ 2)] at h1
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * ε ^ 2)]
    nlinarith [h1]
  -- assemble
  filter_upwards [hev1, hev2, hev3, eventually_gt_atTop 0] with n h1 h2 h3 hn
  calc P {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i, Y n i ω - m|}
      ≤ ENNReal.ofReal (9 * K ^ 2 / ((n : ℝ) * ε ^ 2))
          + ENNReal.ofReal (3 * (∫ y, max (|y| - K) 0 ∂(G n)) / ε) :=
        wlln_row_bound hn (fun i => hmeas n i) (hindep n) (fun i => hlaw n i) (hGint n) hK hε h1
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
        add_le_add (ENNReal.ofReal_le_ofReal h3) (ENNReal.ofReal_le_ofReal h2)
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring
    _ ≤ ρ := hδρ

end StatLean.HypothesisTesting
