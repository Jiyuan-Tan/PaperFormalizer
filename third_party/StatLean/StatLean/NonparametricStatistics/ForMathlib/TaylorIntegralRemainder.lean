module
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# Taylor's theorem with integral remainder

For a globally `C^ℓ` function `f : ℝ → ℝ` (`ℓ ≥ 1`), the order-`ℓ` expansion with the exact
integral form of the remainder, for increments of either sign:
$$ f(x_0 + t) = \sum_{j=0}^{\ell-1} \frac{f^{(j)}(x_0)}{j!} t^j
   + \frac{t^\ell}{(\ell-1)!} \int_0^1 (1-\tau)^{\ell-1} f^{(\ell)}(x_0 + \tau t)\,d\tau. $$

This is the remainder form consumed by the *integrated* bias analysis of kernel smoothers over
Nikol'skii classes: unlike the Lagrange form it is linear in `f^{(ℓ)}` along the segment, so
`L²`-moduli of continuity can be pulled through by the generalized Minkowski inequality.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.3 (integral-remainder Taylor tooling for the
integrated bias bound of Proposition 1.5).

**Proof formalization notes.** Not available in Mathlib in this form (Mathlib's
`Mathlib.Analysis.Calculus.Taylor` provides mean-value-type remainders). Proof: induction on
`ℓ` with integration by parts in `τ`
(`intervalIntegral.integral_mul_deriv_eq_deriv_mul` or `integral_deriv_smul_eq_sub`), with the
fundamental theorem of calculus (`intervalIntegral.integral_deriv_eq_sub`) as the base case
`ℓ = 1`; continuity of `iteratedDeriv ℓ f` supplies all integrability side conditions.

**Bibliographic comments.** The integral remainder is classical (A.-L. Cauchy, *Résumé des
leçons sur le calcul infinitésimal*, Paris, 1823).
-/

open scoped Nat

namespace StatLean.NonparametricStatistics

/-- Auxiliary form of the integral-remainder Taylor expansion, phrased with `ℓ = m + 1` to avoid
truncated subtraction, and proved by induction on `m` (over all functions simultaneously). -/
private lemma taylor_integral_aux :
    ∀ (m : ℕ) {f : ℝ → ℝ}, ContDiff ℝ (m + 1) f → ∀ (x₀ t : ℝ),
      f (x₀ + t)
        = (∑ j ∈ Finset.range (m + 1), iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ))
          + t ^ (m + 1) / (Nat.factorial m : ℝ)
            * ∫ τ in (0 : ℝ)..1, (1 - τ) ^ m * iteratedDeriv (m + 1) f (x₀ + τ * t) := by
  intro m
  induction m with
  | zero =>
    intro f hf x₀ t
    have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s => f (x₀ + s * t)) (iteratedDeriv 1 f (x₀ + τ * t) * t) τ := by
      intro τ _
      have hin : HasDerivAt (fun s : ℝ => x₀ + s * t) t τ := by
        simpa using ((hasDerivAt_id τ).mul_const t).const_add x₀
      have hout : HasDerivAt f (iteratedDeriv 1 f (x₀ + τ * t)) (x₀ + τ * t) := by
        rw [iteratedDeriv_one]
        exact (hf.differentiable (by norm_num) (x₀ + τ * t)).hasDerivAt
      exact hout.comp τ hin
    have hcont : Continuous (fun τ : ℝ => iteratedDeriv 1 f (x₀ + τ * t) * t) :=
      ((hf.continuous_iteratedDeriv 1 (by norm_num)).comp (by fun_prop)).mul continuous_const
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable 0 1)
    rw [intervalIntegral.integral_mul_const] at hFTC
    simp only [one_mul, zero_mul, add_zero] at hFTC
    simp only [zero_add, Finset.sum_range_one, iteratedDeriv_zero, pow_zero, pow_one,
      Nat.factorial_zero, Nat.cast_one, div_one, mul_one, one_mul]
    rw [mul_comm t]
    linarith [hFTC]
  | succ m ih =>
    intro f hf x₀ t
    -- Derivative of `u τ = f⁽ᵐ⁺¹⁾(x₀ + τ t)`.
    have hu : ∀ τ : ℝ, HasDerivAt (fun s => iteratedDeriv (m + 1) f (x₀ + s * t))
        (t * iteratedDeriv (m + 1 + 1) f (x₀ + τ * t)) τ := by
      intro τ
      have hin : HasDerivAt (fun s : ℝ => x₀ + s * t) t τ := by
        simpa using ((hasDerivAt_id τ).mul_const t).const_add x₀
      have hout : HasDerivAt (iteratedDeriv (m + 1) f)
          (iteratedDeriv (m + 1 + 1) f (x₀ + τ * t)) (x₀ + τ * t) := by
        have hd := (hf.differentiable_iteratedDeriv (m + 1)
          (by exact_mod_cast Nat.lt_succ_self (m + 1))) (x₀ + τ * t)
        have := hd.hasDerivAt
        rwa [← iteratedDeriv_succ] at this
      simpa [mul_comm] using! hout.comp τ hin
    -- Derivative of `v τ = -(1-τ)^(m+1)/(m+1)`.
    have hv : ∀ τ : ℝ,
        HasDerivAt (fun s => -(1 - s) ^ (m + 1) / (↑(m + 1) : ℝ)) ((1 - τ) ^ m) τ := by
      intro τ
      have hw := ((hasDerivAt_id τ).const_sub (1 : ℝ)).pow (m + 1)
      simp only [id_eq] at hw
      have h3 := hw.neg.div_const (↑(m + 1) : ℝ)
      convert! h3 using 1
      rw [Nat.add_sub_cancel]
      have hne : (↑(m + 1) : ℝ) ≠ 0 := by positivity
      field_simp
    -- Integrability of the two factors.
    have hu' : IntervalIntegrable
        (fun τ => t * iteratedDeriv (m + 1 + 1) f (x₀ + τ * t)) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      exact continuous_const.mul
        ((hf.continuous_iteratedDeriv (m + 1 + 1) (by norm_num)).comp (by fun_prop))
    have hv' : IntervalIntegrable (fun τ : ℝ => (1 - τ) ^ m) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun τ _ => hu τ) (fun τ _ => hv τ) hu' hv'
    -- Pull the constant out of the boundary integral.
    have hlast :
        (∫ τ in (0 : ℝ)..1, t * iteratedDeriv (m + 1 + 1) f (x₀ + τ * t)
            * (-(1 - τ) ^ (m + 1) / (↑(m + 1) : ℝ)))
          = (-(t / (↑(m + 1) : ℝ)))
            * ∫ τ in (0 : ℝ)..1, (1 - τ) ^ (m + 1) * iteratedDeriv (m + 1 + 1) f (x₀ + τ * t) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun τ _ => by ring)
    -- Integration-by-parts identity for the order-`m` remainder integral.
    have hJm :
        (∫ τ in (0 : ℝ)..1, (1 - τ) ^ m * iteratedDeriv (m + 1) f (x₀ + τ * t))
          = iteratedDeriv (m + 1) f x₀ / (↑(m + 1) : ℝ)
            + (t / (↑(m + 1) : ℝ))
              * ∫ τ in (0 : ℝ)..1,
                  (1 - τ) ^ (m + 1) * iteratedDeriv (m + 1 + 1) f (x₀ + τ * t) := by
      have hcomm :
          (∫ τ in (0 : ℝ)..1, (1 - τ) ^ m * iteratedDeriv (m + 1) f (x₀ + τ * t))
            = ∫ τ in (0 : ℝ)..1, iteratedDeriv (m + 1) f (x₀ + τ * t) * (1 - τ) ^ m :=
        intervalIntegral.integral_congr (fun τ _ => mul_comm _ _)
      rw [hcomm, hIBP, hlast]
      simp only [one_mul, zero_mul, add_zero, sub_zero, sub_self, one_pow,
        zero_pow (Nat.succ_ne_zero m), neg_zero, zero_div, mul_zero]
      ring
    have hm : (↑((m + 1).factorial) : ℝ) = ↑(m + 1) * ↑m.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h1 : (↑(m + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    have h2 : (↑m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    rw [Finset.sum_range_succ, ih hf.of_succ x₀ t, hJm, hm]
    simp only [pow_succ]
    field_simp
    ring

/-- **Taylor's theorem with integral remainder** (global, two-sided). If `f` is `C^ℓ` on `ℝ`
with `ℓ ≥ 1`, then for every `x₀ t`:
`f (x₀ + t) = ∑_{j<ℓ} f⁽ʲ⁾(x₀)·tʲ/j! + (tℓ/(ℓ−1)!)·∫₀¹ (1−τ)^{ℓ−1} f⁽ℓ⁾(x₀ + τ·t) dτ`. -/
theorem taylor_integral_remainder {f : ℝ → ℝ} {ℓ : ℕ}
    -- LEAN-ONLY: order at least one so the remainder integrand is a genuine derivative
    (hℓ : 1 ≤ ℓ)
    -- USER-INPUT: `f` is `ℓ` times continuously differentiable on `ℝ`; classical smoothness
    -- input of Taylor's theorem
    (hf : ContDiff ℝ ℓ f)
    (x₀ t : ℝ) :
    f (x₀ + t)
      = (∑ j ∈ Finset.range ℓ, iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ))
        + t ^ ℓ / (Nat.factorial (ℓ - 1) : ℝ)
          * ∫ τ in (0 : ℝ)..1, (1 - τ) ^ (ℓ - 1) * iteratedDeriv ℓ f (x₀ + τ * t) := by
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, (Nat.succ_pred_eq_of_pos hℓ).symm⟩
  simpa using taylor_integral_aux m hf x₀ t

end StatLean.NonparametricStatistics
