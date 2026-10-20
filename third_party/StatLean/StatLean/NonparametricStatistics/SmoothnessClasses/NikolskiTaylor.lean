module
public import StatLean.NonparametricStatistics.SmoothnessClasses.Defs
public import StatLean.NonparametricStatistics.ForMathlib.TaylorIntegralRemainder
public import StatLean.NonparametricStatistics.ForMathlib.MinkowskiIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

/-!
# Taylor remainder bounds over Nikol'skii classes (L² form)

The `L²` analogue of the Hölder–Taylor bound, driving the *integrated* bias analysis: for `f`
in the Nikol'skii class `H(β, L)` and `ℓ = holderIndex β`,
$$ \Bigl\|\,f(\cdot+t) - \sum_{j=0}^{\ell} \frac{f^{(j)}(\cdot)}{j!}t^j\,\Bigr\|_{L^2(dx)}
   \;\le\; \frac{L}{\ell!}\,|t|^{\beta}. $$

* `taylor_integral_remainder_sub` — the centered integral-remainder identity: subtracting the
  full order-`ℓ` polynomial leaves
  `t^ℓ/(ℓ−1)!·∫₀¹(1−τ)^{ℓ−1}(f^{(ℓ)}(x+τt) − f^{(ℓ)}(x))dτ`
  (the `ℓ`-th Taylor term is absorbed because `∫₀¹(1−τ)^{ℓ−1}dτ = 1/ℓ`).
* `MemNikolski.lintegral_sq_remainder_le` — the squared-`L²` bound, via the generalized
  Minkowski inequality and the Nikol'skii translate condition.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.3 (integrated Taylor-remainder control on
the Nikol'skii class $\mathcal{H}(\beta, L)$, as used in the proof of Proposition 1.5).

**Proof formalization notes.** For `ℓ = 0` the identity degenerates and the bound is the
Nikol'skii condition itself. For `ℓ ≥ 1`: `taylor_integral_remainder` plus linearity of the
`τ`-integral gives the identity; then `lintegral_lintegral_sq_rpow_le` (with `μ` the restricted
Lebesgue measure on `[0,1]` in the `τ` variable) pulls the `L²(dx)`-norm inside, and
`(1−τ)^{ℓ−1}·(τ|t|)^{β−ℓ} ≤ (1−τ)^{ℓ−1}` integrates to `1/ℓ`, upgrading `1/(ℓ−1)!` to `1/ℓ!`.

**Bibliographic comments.** The `L²`-modulus route to integrated bias is the classical
mean-integrated-squared-error computation of kernel density estimation; cf. M. Rosenblatt,
*Ann. Math. Statist.* **27** (1956), 832–837, and S. M. Nikol'skii, *Approximation of
Functions of Several Variables and Imbedding Theorems*, Springer, 1975.
-/

open MeasureTheory
open scoped ENNReal Nat

namespace StatLean.NonparametricStatistics

/-- **Centered integral-remainder identity**: for `C^ℓ` `f` (`ℓ ≥ 1`), subtracting the full
order-`ℓ` Taylor polynomial leaves the centered kernel-form remainder:
`f(x+t) − ∑_{j≤ℓ} f⁽ʲ⁾(x)tʲ/j!
  = t^ℓ/(ℓ−1)!·∫₀¹ (1−τ)^{ℓ−1}·(f⁽ℓ⁾(x+τt) − f⁽ℓ⁾(x)) dτ`. -/
theorem taylor_integral_remainder_sub {f : ℝ → ℝ} {ℓ : ℕ}
    -- LEAN-ONLY: order at least one; the `ℓ = 0` case is treated separately by consumers
    (hℓ : 1 ≤ ℓ)
    -- USER-INPUT: `f` is `ℓ` times continuously differentiable; classical Taylor input
    (hf : ContDiff ℝ ℓ f)
    (x t : ℝ) :
    f (x + t) - ∑ j ∈ Finset.range (ℓ + 1),
        iteratedDeriv j f x * t ^ j / (Nat.factorial j : ℝ)
      = t ^ ℓ / (Nat.factorial (ℓ - 1) : ℝ)
        * ∫ τ in (0 : ℝ)..1,
            (1 - τ) ^ (ℓ - 1) * (iteratedDeriv ℓ f (x + τ * t) - iteratedDeriv ℓ f x) := by
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, (Nat.succ_pred_eq_of_pos hℓ).symm⟩
  have hm0 : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hcontD : Continuous (fun τ : ℝ => iteratedDeriv (m + 1) f (x + τ * t)) :=
    (hf.continuous_iteratedDeriv' (m + 1)).comp (by fun_prop)
  have hpow : Continuous (fun τ : ℝ => (1 - τ) ^ m) :=
    (continuous_const.sub continuous_id).pow m
  have hintA : IntervalIntegrable
      (fun τ : ℝ => (1 - τ) ^ m * iteratedDeriv (m + 1) f (x + τ * t)) volume 0 1 :=
    (hpow.mul hcontD).intervalIntegrable 0 1
  have hintB : IntervalIntegrable
      (fun τ : ℝ => iteratedDeriv (m + 1) f x * (1 - τ) ^ m) volume 0 1 :=
    (continuous_const.mul hpow).intervalIntegrable 0 1
  -- Split the centered integral and evaluate `∫₀¹ (1−τ)^m = 1/(m+1)`.
  have hIsub : (∫ τ in (0 : ℝ)..1,
        (1 - τ) ^ m * (iteratedDeriv (m + 1) f (x + τ * t) - iteratedDeriv (m + 1) f x))
      = (∫ τ in (0 : ℝ)..1, (1 - τ) ^ m * iteratedDeriv (m + 1) f (x + τ * t))
        - iteratedDeriv (m + 1) f x * ∫ τ in (0 : ℝ)..1, (1 - τ) ^ m := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hintA hintB]
    exact intervalIntegral.integral_congr (fun τ _ => by ring)
  have hI1 : (∫ τ in (0 : ℝ)..1, (1 - τ) ^ m) = 1 / ((m : ℝ) + 1) := by
    have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s => -(1 - s) ^ (m + 1) / ((m : ℝ) + 1)) ((1 - τ) ^ m) τ := by
      intro τ _
      have hw := ((hasDerivAt_id τ).const_sub (1 : ℝ)).pow (m + 1)
      simp only [id_eq] at hw
      have h3 := hw.neg.div_const ((m : ℝ) + 1)
      convert! h3 using 1
      rw [Nat.add_sub_cancel]; push_cast; field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hpow.intervalIntegrable 0 1)]
    simp only [sub_self, sub_zero, one_pow, zero_pow (Nat.succ_ne_zero m), neg_zero, zero_div]
    ring
  have hfs : (Nat.factorial (m + 1) : ℝ) = ((m : ℝ) + 1) * Nat.factorial m := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [Finset.sum_range_succ, taylor_integral_remainder hℓ hf x t]
  simp only [Nat.add_sub_cancel]
  rw [hIsub, hI1, hfs]
  set S := ∑ j ∈ Finset.range (m + 1), iteratedDeriv j f x * t ^ j / (Nat.factorial j : ℝ)
  field_simp
  ring

/-- Helper: `(ENNReal.ofReal (u^2))^(1/2) = ENNReal.ofReal u` for `0 ≤ u`. -/
private lemma ofReal_sq_rpow_half {u : ℝ} (hu : 0 ≤ u) :
    (ENNReal.ofReal (u ^ 2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal u := by
  rw [ENNReal.ofReal_pow hu, ← ENNReal.rpow_natCast (ENNReal.ofReal u) 2, ← ENNReal.rpow_mul]
  norm_num

/-- **Squared-`L²` Taylor remainder bound over a Nikol'skii class**: for `f ∈ H(β, L)` and
`ℓ = holderIndex β`,
`∫ (f(x+t) − ∑_{j≤ℓ} f⁽ʲ⁾(x)tʲ/j!)² dx ≤ ((L/ℓ!)·|t|^β)²`. -/
theorem MemNikolski.lintegral_sq_remainder_le {β L : ℝ}
    -- USER-INPUT: positive smoothness and Nikol'skii constant; classical class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    {f : ℝ → ℝ} (hf : MemNikolski β L f) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal ((f (x + t) - ∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x * t ^ j / (Nat.factorial j : ℝ)) ^ 2)
      ≤ ENNReal.ofReal ((L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β) ^ 2) := by
  rcases eq_or_ne t 0 with ht0 | ht0
  · -- t = 0: the remainder vanishes pointwise, so the LHS is 0.
    subst ht0
    have hz : ∀ x, f (x + 0) - ∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x * (0 : ℝ) ^ j / (Nat.factorial j : ℝ) = 0 := by
      intro x
      rw [Finset.sum_range_succ']
      simp
    have hz2 : ∀ x, ENNReal.ofReal ((f (x + 0) - ∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x * (0 : ℝ) ^ j / (Nat.factorial j : ℝ)) ^ 2) = 0 := by
      intro x; rw [hz x]; norm_num
    rw [lintegral_congr (fun x => hz2 x)]
    simp only [MeasureTheory.lintegral_zero]
    exact zero_le
  rcases Nat.eq_zero_or_pos (holderIndex β) with hℓ0 | hℓpos
  · -- ℓ = 0: reduces to the Nikol'skii translate condition at shift `t`.
    have hnik := hf.translate_sq_le t
    rw [hℓ0] at hnik ⊢
    simp only [zero_add, Finset.sum_range_one, iteratedDeriv_zero, pow_zero, Nat.cast_zero,
      sub_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one] at hnik ⊢
    exact hnik
  · -- ℓ ≥ 1.
    obtain ⟨m, hm⟩ : ∃ m, holderIndex β = m + 1 :=
      ⟨holderIndex β - 1, (Nat.succ_pred_eq_of_pos hℓpos).symm⟩
    -- `ℓ < β`, so the Hölder exponent `β − ℓ` is nonnegative.
    have hcast : ((holderIndex β : ℝ)) = (⌈β⌉₊ : ℝ) - 1 := by
      have h1 : 1 ≤ ⌈β⌉₊ := by
        have := hℓpos; rw [holderIndex] at this; omega
      rw [holderIndex, Nat.cast_sub h1]; norm_num
    have hβℓ : 0 ≤ β - (holderIndex β : ℝ) := by
      have h := Nat.ceil_lt_add_one hβ.le
      rw [hcast]; linarith
    set ℓ := holderIndex β with hℓdef
    -- Abbreviations.
    set Δ : ℝ → ℝ → ℝ := fun τ x =>
      iteratedDeriv ℓ f (x + τ * t) - iteratedDeriv ℓ f x with hΔdef
    set c : ℝ := t ^ ℓ / (Nat.factorial (ℓ - 1) : ℝ) with hcdef
    set I : ℝ → ℝ := fun x => ∫ τ in (0 : ℝ)..1, (1 - τ) ^ (ℓ - 1) * Δ τ x with hIdef
    -- Continuity / measurability of the top derivative.
    have hcont : Continuous (iteratedDeriv ℓ f) :=
      ContDiff.continuous_iteratedDeriv' ℓ hf.contDiff
    -- Step 1: rewrite the integrand pointwise via the Taylor identity.
    have hstep1 : ∀ x, f (x + t) - ∑ j ∈ Finset.range (ℓ + 1),
          iteratedDeriv j f x * t ^ j / (Nat.factorial j : ℝ) = c * I x := by
      intro x
      have := taylor_integral_remainder_sub hℓpos hf.contDiff x t
      simpa [hcdef, hIdef, hΔdef] using this
    rw [lintegral_congr (fun x => by rw [hstep1 x])]
    -- The integrand kernel `g τ x = ofReal |(1−τ)^(ℓ−1) · Δ τ x|`.
    set g : ℝ → ℝ → ℝ≥0∞ := fun τ x =>
      ENNReal.ofReal |(1 - τ) ^ (ℓ - 1) * Δ τ x| with hgdef
    -- Joint measurability of `g`.
    have hΔcont : Continuous (Function.uncurry Δ) := by
      have h1 : Continuous fun p : ℝ × ℝ => iteratedDeriv ℓ f (p.2 + p.1 * t) :=
        hcont.comp (by fun_prop)
      have h2 : Continuous fun p : ℝ × ℝ => iteratedDeriv ℓ f p.2 := hcont.comp (by fun_prop)
      simpa [Function.uncurry, hΔdef] using! h1.sub h2
    have hgmeas : Measurable (Function.uncurry g) := by
      have hcw : Continuous fun p : ℝ × ℝ => (1 - p.1) ^ (ℓ - 1) := by fun_prop
      have : Continuous fun p : ℝ × ℝ => |(1 - p.1) ^ (ℓ - 1) * Δ p.1 p.2| :=
        (hcw.mul hΔcont).abs
      exact (this.measurable).ennreal_ofReal
    -- Continuity in τ for fixed x, for interval integrability.
    have hτcont : ∀ x, Continuous fun τ : ℝ => (1 - τ) ^ (ℓ - 1) * Δ τ x := by
      intro x
      have : Continuous fun τ : ℝ => Δ τ x :=
        hΔcont.comp (by fun_prop : Continuous fun τ : ℝ => (τ, x))
      exact (Continuous.pow (by fun_prop) _).mul this
    -- Step 3: pointwise `ofReal((I x)^2) ≤ (∫⁻ τ in Icc 0 1, g τ x)^2`.
    have hpt : ∀ x, ENNReal.ofReal ((I x) ^ 2)
        ≤ (∫⁻ τ in Set.Icc (0 : ℝ) 1, g τ x) ^ 2 := by
      intro x
      have habs : |I x| ≤ ∫ τ in (0 : ℝ)..1, |(1 - τ) ^ (ℓ - 1) * Δ τ x| := by
        rw [hIdef]
        simpa [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (a := (0:ℝ)) (b := 1)
            (μ := volume) (f := fun τ => (1 - τ) ^ (ℓ - 1) * Δ τ x) (by norm_num)
      have hnn : 0 ≤ ∫ τ in (0 : ℝ)..1, |(1 - τ) ^ (ℓ - 1) * Δ τ x| :=
        le_trans (abs_nonneg _) habs
      have hbridge : ENNReal.ofReal (∫ τ in (0 : ℝ)..1, |(1 - τ) ^ (ℓ - 1) * Δ τ x|)
          = ∫⁻ τ in Set.Icc (0 : ℝ) 1, g τ x := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
          ← MeasureTheory.integral_Icc_eq_integral_Ioc]
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          ((hτcont x).abs.integrableOn_Icc)
          (Filter.Eventually.of_forall fun τ => abs_nonneg _)]
      have hle : ENNReal.ofReal (|I x|) ≤ ∫⁻ τ in Set.Icc (0 : ℝ) 1, g τ x := by
        rw [← hbridge]; exact ENNReal.ofReal_le_ofReal habs
      calc ENNReal.ofReal ((I x) ^ 2)
          = (ENNReal.ofReal (|I x|)) ^ 2 := by
            rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
        _ ≤ (∫⁻ τ in Set.Icc (0 : ℝ) 1, g τ x) ^ 2 := by
            gcongr
    -- Step 5: per-`τ` bound on the inner `L²(dx)` norm.
    have hpertau : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        (∫⁻ x, (g τ x) ^ 2) ^ (1 / 2 : ℝ)
          ≤ ENNReal.ofReal ((1 - τ) ^ (ℓ - 1) * (L * |t| ^ (β - (ℓ : ℝ)))) := by
      intro τ hτ
      obtain ⟨hτ0, hτ1⟩ := hτ
      have h1τ : (0 : ℝ) ≤ 1 - τ := by linarith
      have hw : (0 : ℝ) ≤ (1 - τ) ^ (ℓ - 1) := by positivity
      -- Pull the `(1−τ)^(ℓ−1)` constant out of the `dx`-integral.
      have hconst : (∫⁻ x, (g τ x) ^ 2)
          = ENNReal.ofReal (((1 - τ) ^ (ℓ - 1)) ^ 2)
            * ∫⁻ x, ENNReal.ofReal ((Δ τ x) ^ 2) := by
        rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        rw [hgdef]
        rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, mul_pow,
          ENNReal.ofReal_mul (by positivity)]
      -- Nikol'skii translate condition at shift `τ·t`.
      have hnik := hf.translate_sq_le (τ * t)
      rw [← hℓdef] at hnik
      have hΔeq : (∫⁻ x, ENNReal.ofReal ((Δ τ x) ^ 2))
          = ∫⁻ x, ENNReal.ofReal ((iteratedDeriv ℓ f (x + τ * t)
              - iteratedDeriv ℓ f x) ^ 2) := by
        refine lintegral_congr fun x => ?_; rw [hΔdef]
      rw [hΔeq] at hconst
      have hbnd : (∫⁻ x, (g τ x) ^ 2)
          ≤ ENNReal.ofReal (((1 - τ) ^ (ℓ - 1)) ^ 2)
            * ENNReal.ofReal ((L * |τ * t| ^ (β - (ℓ : ℝ))) ^ 2) := by
        rw [hconst]; gcongr
      -- Take square roots.
      calc (∫⁻ x, (g τ x) ^ 2) ^ (1 / 2 : ℝ)
          ≤ (ENNReal.ofReal (((1 - τ) ^ (ℓ - 1)) ^ 2)
              * ENNReal.ofReal ((L * |τ * t| ^ (β - (ℓ : ℝ))) ^ 2)) ^ (1 / 2 : ℝ) := by
            gcongr
        _ = ENNReal.ofReal ((1 - τ) ^ (ℓ - 1))
              * ENNReal.ofReal (L * |τ * t| ^ (β - (ℓ : ℝ))) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
              ofReal_sq_rpow_half hw,
              ofReal_sq_rpow_half (by positivity)]
        _ ≤ ENNReal.ofReal ((1 - τ) ^ (ℓ - 1) * (L * |t| ^ (β - (ℓ : ℝ)))) := by
            rw [ENNReal.ofReal_mul hw]
            have hreal : L * |τ * t| ^ (β - (ℓ : ℝ)) ≤ L * |t| ^ (β - (ℓ : ℝ)) := by
              rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
              have hτabs : |τ| ^ (β - (ℓ : ℝ)) ≤ 1 :=
                Real.rpow_le_one (abs_nonneg _) (by rw [abs_of_nonneg hτ0]; exact hτ1) hβℓ
              have hstep : |τ| ^ (β - (ℓ : ℝ)) * |t| ^ (β - (ℓ : ℝ)) ≤ |t| ^ (β - (ℓ : ℝ)) := by
                nlinarith [Real.rpow_nonneg (abs_nonneg t) (β - (ℓ : ℝ)), hτabs]
              nlinarith [hstep, hL, Real.rpow_nonneg (abs_nonneg t) (β - (ℓ : ℝ))]
            gcongr
    -- Step 6: integrate the per-`τ` bound; `∫₀¹ (1−τ)^{ℓ−1} dτ = 1/ℓ`.
    have hℓm : ℓ - 1 = m := by omega
    have hI1 : (∫ τ in (0 : ℝ)..1, (1 - τ) ^ (ℓ - 1)) = 1 / (ℓ : ℝ) := by
      rw [hℓm]
      have hℓn : (ℓ : ℝ) = (m : ℝ) + 1 := by rw [hm]; push_cast; ring
      have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun s => -(1 - s) ^ (m + 1) / ((m : ℝ) + 1)) ((1 - τ) ^ m) τ := by
        intro τ _
        have hw := ((hasDerivAt_id τ).const_sub (1 : ℝ)).pow (m + 1)
        simp only [id_eq] at hw
        have h3 := hw.neg.div_const ((m : ℝ) + 1)
        convert! h3 using 1
        rw [Nat.add_sub_cancel]; push_cast; field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (((continuous_const.sub continuous_id).pow m).intervalIntegrable 0 1)]
      simp only [sub_self, sub_zero, one_pow, zero_pow (Nat.succ_ne_zero m), neg_zero, zero_div]
      rw [hℓn]; ring
    have hℓpos' : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓpos
    have hnnae : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
        fun τ => (1 - τ) ^ (ℓ - 1) := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2
        (Filter.Eventually.of_forall fun τ hτ => ?_)
      have : (0 : ℝ) ≤ 1 - τ := by exact sub_nonneg.2 hτ.2
      positivity
    have hcontpow : Continuous fun τ : ℝ => (1 - τ) ^ (ℓ - 1) := by fun_prop
    have hIicc : (∫⁻ τ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - τ) ^ (ℓ - 1)))
        = ENNReal.ofReal (1 / (ℓ : ℝ)) := by
      rw [← hI1, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc,
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcontpow.integrableOn_Icc hnnae]
    -- Assemble.
    set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμdef
    have hmink := lintegral_lintegral_sq_rpow_le μ volume (g := g) hgmeas
    -- Pull `∫⁻ ∂μ = ∫⁻ in Icc 0 1`.
    have hμeq : ∀ h : ℝ → ℝ≥0∞, (∫⁻ τ, h τ ∂μ) = ∫⁻ τ in Set.Icc (0 : ℝ) 1, h τ := by
      intro h; rw [hμdef]
    -- Step 2: pull the `c²` constant.
    have hc2 : (∫⁻ x, ENNReal.ofReal ((c * I x) ^ 2))
        = ENNReal.ofReal (c ^ 2) * ∫⁻ x, ENNReal.ofReal ((I x) ^ 2) := by
      rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x => ?_
      rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    -- The `τ`-integral bound.
    have hτint : (∫⁻ τ in Set.Icc (0 : ℝ) 1, (∫⁻ x, (g τ x) ^ 2) ^ (1 / 2 : ℝ))
        ≤ ENNReal.ofReal (L * |t| ^ (β - (ℓ : ℝ))) * ENNReal.ofReal (1 / (ℓ : ℝ)) := by
      calc (∫⁻ τ in Set.Icc (0 : ℝ) 1, (∫⁻ x, (g τ x) ^ 2) ^ (1 / 2 : ℝ))
          ≤ ∫⁻ τ in Set.Icc (0 : ℝ) 1,
              ENNReal.ofReal ((1 - τ) ^ (ℓ - 1) * (L * |t| ^ (β - (ℓ : ℝ)))) := by
            refine MeasureTheory.setLIntegral_mono_ae ?_ ?_
            · refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
              fun_prop
            · exact Filter.Eventually.of_forall fun τ hτ => hpertau τ hτ
        _ = ENNReal.ofReal (L * |t| ^ (β - (ℓ : ℝ)))
              * ∫⁻ τ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - τ) ^ (ℓ - 1)) := by
            rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun τ => ?_
            rw [← ENNReal.ofReal_mul (by positivity), mul_comm ((1 - τ) ^ (ℓ - 1))]
        _ = ENNReal.ofReal (L * |t| ^ (β - (ℓ : ℝ))) * ENNReal.ofReal (1 / (ℓ : ℝ)) := by
            rw [hIicc]
    -- Combine Step 3 and Minkowski.
    set A : ℝ≥0∞ := ∫⁻ x, (∫⁻ τ in Set.Icc (0 : ℝ) 1, g τ x) ^ 2 with hAdef
    have hIA : (∫⁻ x, ENNReal.ofReal ((I x) ^ 2)) ≤ A := lintegral_mono hpt
    have hAmink : A ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (L * |t| ^ (β - (ℓ : ℝ))) * ENNReal.ofReal (1 / (ℓ : ℝ)) := by
      refine le_trans ?_ hτint
      simpa [hAdef, hμeq] using hmink
    have hAle : A ≤ (ENNReal.ofReal (L * |t| ^ (β - (ℓ : ℝ)))
        * ENNReal.ofReal (1 / (ℓ : ℝ))) ^ 2 := by
      have hAeq : A = (A ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [← ENNReal.rpow_natCast (A ^ (1/2:ℝ)) 2, ← ENNReal.rpow_mul]
        norm_num
      rw [hAeq]; gcongr
    -- Assemble constants.
    rw [hc2]
    refine le_trans (mul_le_mul' (le_refl (ENNReal.ofReal (c ^ 2)))
      (le_trans hIA hAle)) ?_
    -- Reduce to a real identity: collapse the LHS product into one `ofReal`.
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ L * |t| ^ (β - (ℓ:ℝ))),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [le_iff_eq_or_lt]; left
    -- The real identity `c² · (L|t|^{β−ℓ})² · (1/ℓ)² = (L/ℓ! · |t|^β)²`.
    have hcval : c = t ^ ℓ / (Nat.factorial (ℓ - 1) : ℝ) := rfl
    -- Key: `(t^ℓ)² · (|t|^{β−ℓ})² = (|t|^β)²`.
    have hkeyid : (t ^ ℓ) ^ 2 * (|t| ^ (β - (ℓ : ℝ))) ^ 2 = (|t| ^ β) ^ 2 := by
      have hℓsq : (t ^ ℓ) ^ 2 = (|t| ^ (ℓ : ℝ)) ^ 2 := by
        rw [Real.rpow_natCast, ← abs_pow, sq_abs]
      rw [hℓsq, ← mul_pow, ← Real.rpow_add (abs_pos.2 ht0)]
      ring_nf
    have hfact : (Nat.factorial ℓ : ℝ) = (Nat.factorial (ℓ - 1) : ℝ) * (ℓ : ℝ) := by
      rw [hℓm, hm, Nat.factorial_succ]; push_cast; ring
    have hfne : (Nat.factorial (ℓ - 1) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hℓne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓpos'
    rw [hcval, hfact]
    field_simp
    nlinarith [hkeyid, sq_nonneg (t ^ ℓ), sq_nonneg (|t| ^ (β - (ℓ:ℝ)))]

end StatLean.NonparametricStatistics
