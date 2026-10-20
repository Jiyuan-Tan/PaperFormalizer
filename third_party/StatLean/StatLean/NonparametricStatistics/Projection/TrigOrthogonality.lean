module
public import StatLean.NonparametricStatistics.Projection.Defs
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Orthonormality of the trigonometric system on [0, 1]

`∫₀¹ φⱼ(x)·φ_k(x) dx = δ_{jk}` for `j, k ≥ 1`, and the uniform bound `|φⱼ| ≤ √2`.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.7.1–1.7.2 (the trigonometric Fourier basis and
its $L^2[0,1]$ orthonormality).

**Proof formalization notes.** Case-split on the parities and frequencies: the products reduce
by the product-to-sum identities (`Real.cos_mul_cos`-style, or directly
`2·cos a·cos b = cos(a−b) + cos(a+b)` etc.) to integrals of `cos(2πmx)` and `sin(2πmx)` over
`[0,1]`, which vanish for `m ≠ 0` (`integral_cos`, `integral_sin` with the `2πm` period) and
give the normalization `∫ cos² = ∫ sin² = 1/2` for equal frequencies (`integral_cos_sq`,
`integral_sin_sq`). The frequency arithmetic (`j/2 ± k/2 = 0` iff same-parity equal indices)
is the only bookkeeping.

**Bibliographic comments.** Classical Fourier analysis (J. Fourier, *Théorie analytique de la
chaleur*, 1822); the role of the trigonometric system in orthogonal series estimation goes
back to N. N. Čencov, *Soviet Math. Dokl.* **3** (1962), 1559–1562.
-/

open MeasureTheory intervalIntegral

namespace StatLean.NonparametricStatistics

/-- Uniform bound on the trigonometric system: `|φⱼ(x)| ≤ √2` for every `j` and `x`. -/
theorem trigBasis_abs_le (j : ℕ) (x : ℝ) : |trigBasis j x| ≤ Real.sqrt 2 := by
  have h0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  unfold trigBasis
  split_ifs
  · rw [abs_zero]; exact h0
  · rw [abs_one]; exact h1
  · rw [abs_mul, abs_of_nonneg h0]
    calc Real.sqrt 2 * |Real.cos (2 * Real.pi * ((j / 2 : ℕ) : ℝ) * x)|
          ≤ Real.sqrt 2 * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) h0
      _ = Real.sqrt 2 := mul_one _
  · rw [abs_mul, abs_of_nonneg h0]
    calc Real.sqrt 2 * |Real.sin (2 * Real.pi * ((j / 2 : ℕ) : ℝ) * x)|
          ≤ Real.sqrt 2 * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) h0
      _ = Real.sqrt 2 := mul_one _

/-- The trigonometric system is measurable in `x` for each index. -/
theorem trigBasis_measurable (j : ℕ) : Measurable (trigBasis j) := by
  unfold trigBasis
  split_ifs
  · exact measurable_const
  · exact measurable_const
  · fun_prop
  · fun_prop

/-! ### Normal forms for the trigonometric system -/

private lemma trigBasis_one (x : ℝ) : trigBasis 1 x = 1 := by
  simp [trigBasis]

private lemma trigBasis_even {q : ℕ} (hq : 1 ≤ q) (x : ℝ) :
    trigBasis (2 * q) x = Real.sqrt 2 * Real.cos (2 * Real.pi * (q : ℝ) * x) := by
  have h2 : (2 * q) / 2 = q := by omega
  unfold trigBasis
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), h2]

private lemma trigBasis_odd {q : ℕ} (hq : 1 ≤ q) (x : ℝ) :
    trigBasis (2 * q + 1) x = Real.sqrt 2 * Real.sin (2 * Real.pi * (q : ℝ) * x) := by
  have h2 : (2 * q + 1) / 2 = q := by omega
  unfold trigBasis
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), h2]

private lemma trig_index_cases {j : ℕ} (hj : 1 ≤ j) :
    j = 1 ∨ (∃ p, 1 ≤ p ∧ j = 2 * p) ∨ (∃ p, 1 ≤ p ∧ j = 2 * p + 1) := by
  rcases Nat.lt_or_ge j 2 with h | h
  · left; omega
  · rcases Nat.even_or_odd j with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact Or.inr (Or.inl ⟨p, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨p, by omega, by omega⟩)

/-! ### Single-frequency integrals over `[0,1]` -/

private lemma intCosZ (c : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * (c : ℝ) * x) = if c = 0 then 1 else 0 := by
  by_cases hc : c = 0
  · subst hc; simp
  · rw [if_neg hc]
    have hA : (2 * Real.pi * (c : ℝ)) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨two_ne_zero, Real.pi_ne_zero⟩, Int.cast_ne_zero.mpr hc⟩
    have hkey := intervalIntegral.mul_integral_comp_mul_left (a := 0) (b := 1)
      (f := Real.cos) (2 * Real.pi * (c : ℝ))
    rw [mul_zero, mul_one, integral_cos] at hkey
    have hsin : Real.sin (2 * Real.pi * (c : ℝ)) = 0 := by
      have he : 2 * Real.pi * (c : ℝ) = ((2 * c : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [he, Real.sin_int_mul_pi]
    rw [hsin, Real.sin_zero, sub_zero] at hkey
    exact (mul_eq_zero.mp hkey).resolve_left hA

private lemma intSinZ (c : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (c : ℝ) * x) = 0 := by
  by_cases hc : c = 0
  · subst hc; simp
  · have hA : (2 * Real.pi * (c : ℝ)) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨two_ne_zero, Real.pi_ne_zero⟩, Int.cast_ne_zero.mpr hc⟩
    have hkey := intervalIntegral.mul_integral_comp_mul_left (a := 0) (b := 1)
      (f := Real.sin) (2 * Real.pi * (c : ℝ))
    rw [mul_zero, mul_one, integral_sin] at hkey
    have hcos : Real.cos (2 * Real.pi * (c : ℝ)) = 1 := by
      have he : 2 * Real.pi * (c : ℝ) = (c : ℝ) * (2 * Real.pi) := by ring
      rw [he, Real.cos_int_mul_two_pi]
    rw [Real.cos_zero, hcos, sub_self] at hkey
    exact (mul_eq_zero.mp hkey).resolve_left hA

private lemma cos_intervalIntegrable (c : ℤ) :
    IntervalIntegrable (fun x => Real.cos (2 * Real.pi * (c : ℝ) * x)) volume 0 1 := by
  apply Continuous.intervalIntegrable; fun_prop

private lemma sin_intervalIntegrable (c : ℤ) :
    IntervalIntegrable (fun x => Real.sin (2 * Real.pi * (c : ℝ) * x)) volume 0 1 := by
  apply Continuous.intervalIntegrable; fun_prop

/-! ### Product integrals over `[0,1]` (product-to-sum) -/

private lemma intCosCosZ (p q : ℤ) (hpq : p + q ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x)
      = if p = q then (1 : ℝ) / 2 else 0 := by
  have key : ∀ x, Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x)
      = (Real.cos (2 * Real.pi * ((p - q : ℤ) : ℝ) * x)
          + Real.cos (2 * Real.pi * ((p + q : ℤ) : ℝ) * x)) / 2 := by
    intro x
    have e1 : 2 * Real.pi * ((p - q : ℤ) : ℝ) * x
        = 2 * Real.pi * (p : ℝ) * x - 2 * Real.pi * (q : ℝ) * x := by push_cast; ring
    have e2 : 2 * Real.pi * ((p + q : ℤ) : ℝ) * x
        = 2 * Real.pi * (p : ℝ) * x + 2 * Real.pi * (q : ℝ) * x := by push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
  rw [intervalIntegral.integral_congr (fun x _ => key x), intervalIntegral.integral_div,
      intervalIntegral.integral_add (cos_intervalIntegrable _) (cos_intervalIntegrable _),
      intCosZ, intCosZ, if_neg hpq]
  by_cases hpeq : p = q
  · rw [if_pos hpeq, if_pos (sub_eq_zero.mpr hpeq)]; norm_num
  · rw [if_neg hpeq, if_neg (sub_ne_zero.mpr hpeq)]; norm_num

private lemma intSinSinZ (p q : ℤ) (hpq : p + q ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x)
      = if p = q then (1 : ℝ) / 2 else 0 := by
  have key : ∀ x, Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x)
      = (Real.cos (2 * Real.pi * ((p - q : ℤ) : ℝ) * x)
          - Real.cos (2 * Real.pi * ((p + q : ℤ) : ℝ) * x)) / 2 := by
    intro x
    have e1 : 2 * Real.pi * ((p - q : ℤ) : ℝ) * x
        = 2 * Real.pi * (p : ℝ) * x - 2 * Real.pi * (q : ℝ) * x := by push_cast; ring
    have e2 : 2 * Real.pi * ((p + q : ℤ) : ℝ) * x
        = 2 * Real.pi * (p : ℝ) * x + 2 * Real.pi * (q : ℝ) * x := by push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
  rw [intervalIntegral.integral_congr (fun x _ => key x), intervalIntegral.integral_div,
      intervalIntegral.integral_sub (cos_intervalIntegrable _) (cos_intervalIntegrable _),
      intCosZ, intCosZ, if_neg hpq]
  by_cases hpeq : p = q
  · rw [if_pos hpeq, if_pos (sub_eq_zero.mpr hpeq)]; norm_num
  · rw [if_neg hpeq, if_neg (sub_ne_zero.mpr hpeq)]; norm_num

private lemma intCosSinZ (p q : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x)
      = 0 := by
  have key : ∀ x, Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x)
      = (Real.sin (2 * Real.pi * ((p + q : ℤ) : ℝ) * x)
          - Real.sin (2 * Real.pi * ((p - q : ℤ) : ℝ) * x)) / 2 := by
    intro x
    have e1 : 2 * Real.pi * ((p + q : ℤ) : ℝ) * x
        = 2 * Real.pi * (p : ℝ) * x + 2 * Real.pi * (q : ℝ) * x := by push_cast; ring
    have e2 : 2 * Real.pi * ((p - q : ℤ) : ℝ) * x
        = 2 * Real.pi * (p : ℝ) * x - 2 * Real.pi * (q : ℝ) * x := by push_cast; ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]; ring
  rw [intervalIntegral.integral_congr (fun x _ => key x), intervalIntegral.integral_div,
      intervalIntegral.integral_sub (sin_intervalIntegrable _) (sin_intervalIntegrable _),
      intSinZ, intSinZ]
  norm_num

private lemma intSinCosZ (p q : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x)
      = 0 := by
  have key : ∀ x, Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x)
      = (Real.sin (2 * Real.pi * ((p + q : ℤ) : ℝ) * x)
          + Real.sin (2 * Real.pi * ((p - q : ℤ) : ℝ) * x)) / 2 := by
    intro x
    have e1 : 2 * Real.pi * ((p + q : ℤ) : ℝ) * x
        = 2 * Real.pi * (p : ℝ) * x + 2 * Real.pi * (q : ℝ) * x := by push_cast; ring
    have e2 : 2 * Real.pi * ((p - q : ℤ) : ℝ) * x
        = 2 * Real.pi * (p : ℝ) * x - 2 * Real.pi * (q : ℝ) * x := by push_cast; ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]; ring
  rw [intervalIntegral.integral_congr (fun x _ => key x), intervalIntegral.integral_div,
      intervalIntegral.integral_add (sin_intervalIntegrable _) (sin_intervalIntegrable _),
      intSinZ, intSinZ]
  norm_num

/-! ### ℕ-frequency wrappers -/

private lemma intCosN {q : ℕ} (hq : q ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * (q : ℝ) * x) = 0 := by
  have h := intCosZ (q : ℤ)
  rw [if_neg (by exact_mod_cast hq)] at h
  simpa using h

private lemma intSinN (q : ℕ) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (q : ℝ) * x) = 0 := by
  simpa using intSinZ (q : ℤ)

private lemma intCosCos {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x)
      = if p = q then (1 : ℝ) / 2 else 0 := by
  have h := intCosCosZ (p : ℤ) (q : ℤ) (by omega)
  simpa using h

private lemma intSinSin {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x)
      = if p = q then (1 : ℝ) / 2 else 0 := by
  have h := intSinSinZ (p : ℤ) (q : ℤ) (by omega)
  simpa using h

private lemma intCosSin (p q : ℕ) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x)
      = 0 := by
  simpa using intCosSinZ (p : ℤ) (q : ℤ)

private lemma intSinCos (p q : ℕ) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x)
      = 0 := by
  simpa using intSinCosZ (p : ℤ) (q : ℤ)

/-- **Orthonormality of the trigonometric system on `[0,1]`**:
`∫₀¹ φⱼ·φ_k = 1` if `j = k` and `0` otherwise (indices `≥ 1`). -/
theorem trigBasis_orthonormal {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..1, trigBasis j x * trigBasis k x = if j = k then 1 else 0 := by
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rcases trig_index_cases hj with hj1 | ⟨p, hp, hjp⟩ | ⟨p, hp, hjp⟩ <;>
    rcases trig_index_cases hk with hk1 | ⟨q, hq, hkq⟩ | ⟨q, hq, hkq⟩
  -- j = 1, k = 1
  · subst hj1; subst hk1
    rw [if_pos rfl]
    have hfun : ∀ x, trigBasis 1 x * trigBasis 1 x = (1 : ℝ) := by
      intro x; rw [trigBasis_one]; ring
    rw [intervalIntegral.integral_congr (fun x _ => hfun x)]; simp
  -- j = 1, k = 2q
  · subst hj1; subst hkq
    rw [if_neg (by omega)]
    have hfun : ∀ x, trigBasis 1 x * trigBasis (2 * q) x
        = Real.sqrt 2 * Real.cos (2 * Real.pi * (q : ℝ) * x) := by
      intro x; rw [trigBasis_one, trigBasis_even hq, one_mul]
    rw [intervalIntegral.integral_congr (fun x _ => hfun x), intervalIntegral.integral_const_mul,
        intCosN (by omega), mul_zero]
  -- j = 1, k = 2q+1
  · subst hj1; subst hkq
    rw [if_neg (by omega)]
    have hfun : ∀ x, trigBasis 1 x * trigBasis (2 * q + 1) x
        = Real.sqrt 2 * Real.sin (2 * Real.pi * (q : ℝ) * x) := by
      intro x; rw [trigBasis_one, trigBasis_odd hq, one_mul]
    rw [intervalIntegral.integral_congr (fun x _ => hfun x), intervalIntegral.integral_const_mul,
        intSinN, mul_zero]
  -- j = 2p, k = 1
  · subst hjp; subst hk1
    rw [if_neg (by omega)]
    have hfun : ∀ x, trigBasis (2 * p) x * trigBasis 1 x
        = Real.sqrt 2 * Real.cos (2 * Real.pi * (p : ℝ) * x) := by
      intro x; rw [trigBasis_even hp, trigBasis_one, mul_one]
    rw [intervalIntegral.integral_congr (fun x _ => hfun x), intervalIntegral.integral_const_mul,
        intCosN (by omega), mul_zero]
  -- j = 2p, k = 2q
  · subst hjp; subst hkq
    have hfun : ∀ x, trigBasis (2 * p) x * trigBasis (2 * q) x
        = 2 * (Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x)) := by
      intro x
      rw [trigBasis_even hp, trigBasis_even hq]
      rw [show Real.sqrt 2 * Real.cos (2 * Real.pi * (p : ℝ) * x)
              * (Real.sqrt 2 * Real.cos (2 * Real.pi * (q : ℝ) * x))
            = (Real.sqrt 2 * Real.sqrt 2)
              * (Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x))
            from by ring, hsqrt]
    rw [intervalIntegral.integral_congr (fun x _ => hfun x), intervalIntegral.integral_const_mul,
        intCosCos hp hq]
    rcases eq_or_ne p q with h | h
    · subst h; rw [if_pos rfl, if_pos rfl]; norm_num
    · rw [if_neg h, if_neg (by omega), mul_zero]
  -- j = 2p, k = 2q+1
  · subst hjp; subst hkq
    rw [if_neg (by omega)]
    have hfun : ∀ x, trigBasis (2 * p) x * trigBasis (2 * q + 1) x
        = 2 * (Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x)) := by
      intro x
      rw [trigBasis_even hp, trigBasis_odd hq]
      rw [show Real.sqrt 2 * Real.cos (2 * Real.pi * (p : ℝ) * x)
              * (Real.sqrt 2 * Real.sin (2 * Real.pi * (q : ℝ) * x))
            = (Real.sqrt 2 * Real.sqrt 2)
              * (Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x))
            from by ring, hsqrt]
    rw [intervalIntegral.integral_congr (fun x _ => hfun x), intervalIntegral.integral_const_mul,
        intCosSin, mul_zero]
  -- j = 2p+1, k = 1
  · subst hjp; subst hk1
    rw [if_neg (by omega)]
    have hfun : ∀ x, trigBasis (2 * p + 1) x * trigBasis 1 x
        = Real.sqrt 2 * Real.sin (2 * Real.pi * (p : ℝ) * x) := by
      intro x; rw [trigBasis_odd hp, trigBasis_one, mul_one]
    rw [intervalIntegral.integral_congr (fun x _ => hfun x), intervalIntegral.integral_const_mul,
        intSinN, mul_zero]
  -- j = 2p+1, k = 2q
  · subst hjp; subst hkq
    rw [if_neg (by omega)]
    have hfun : ∀ x, trigBasis (2 * p + 1) x * trigBasis (2 * q) x
        = 2 * (Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x)) := by
      intro x
      rw [trigBasis_odd hp, trigBasis_even hq]
      rw [show Real.sqrt 2 * Real.sin (2 * Real.pi * (p : ℝ) * x)
              * (Real.sqrt 2 * Real.cos (2 * Real.pi * (q : ℝ) * x))
            = (Real.sqrt 2 * Real.sqrt 2)
              * (Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x))
            from by ring, hsqrt]
    rw [intervalIntegral.integral_congr (fun x _ => hfun x), intervalIntegral.integral_const_mul,
        intSinCos, mul_zero]
  -- j = 2p+1, k = 2q+1
  · subst hjp; subst hkq
    have hfun : ∀ x, trigBasis (2 * p + 1) x * trigBasis (2 * q + 1) x
        = 2 * (Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x)) := by
      intro x
      rw [trigBasis_odd hp, trigBasis_odd hq]
      rw [show Real.sqrt 2 * Real.sin (2 * Real.pi * (p : ℝ) * x)
              * (Real.sqrt 2 * Real.sin (2 * Real.pi * (q : ℝ) * x))
            = (Real.sqrt 2 * Real.sqrt 2)
              * (Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x))
            from by ring, hsqrt]
    rw [intervalIntegral.integral_congr (fun x _ => hfun x), intervalIntegral.integral_const_mul,
        intSinSin hp hq]
    rcases eq_or_ne p q with h | h
    · subst h; rw [if_pos rfl, if_pos rfl]; norm_num
    · rw [if_neg h, if_neg (by omega), mul_zero]

end StatLean.NonparametricStatistics
