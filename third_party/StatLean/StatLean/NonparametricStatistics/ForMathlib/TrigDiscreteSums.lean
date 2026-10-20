module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Algebra.Field.GeomSum

@[expose] public section

/-!
# Discrete sums of cosines and sines at rational frequencies

The exact values of `∑_{s=1}^{n} cos(2πms/n)` and `∑_{s=1}^{n} sin(2πms/n)`:
both vanish when `n ∤ m`; the cosine sum equals `n` (and the sine sum `0`) when `n ∣ m`.

These are the arithmetic engine behind the discrete orthonormality of the trigonometric system
at the regular design — the fact that makes coefficient estimates at design points behave like
genuine Fourier coefficients.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.7.2 (roots-of-unity sums behind the discrete
orthogonality of Lemma 1.7).

**Proof formalization notes.** Pass to the complex exponential: the sums are the real and
imaginary parts of the geometric sum `∑_{s=1}^n ζ^s` with `ζ = exp(2πi·m/n)`. For `n ∤ m` one
has `ζ ≠ 1` and `ζ^n = 1`, so `∑_{s=0}^{n-1} ζ^s = (ζ^n − 1)/(ζ − 1) = 0`
(`Finset.geom_sum_eq`), and the `1..n` sum is `ζ` times the `0..n−1` sum. For `n ∣ m`, every
term is `1` (resp. `0`). Key Mathlib pieces: `Complex.exp_int_mul_two_pi_mul_I`,
`Complex.exp_re`/`exp_ofReal_mul_I_re`, `Finset.geom_sum_eq`.

**Bibliographic comments.** Classical roots-of-unity identities (Gauss).
-/

open scoped Real

namespace StatLean.NonparametricStatistics

/-- The `(s+1)`-th power of `ζ = exp(2πi·m/n)` is `exp(i·2πm(s+1)/n)`, the complex exponential
whose real/imaginary parts are the cosine/sine terms of the discrete sums. -/
private lemma trig_exp_pow_eq (n m s : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I * m / n)) ^ (s + 1)
      = Complex.exp (((2 * Real.pi * m * (s + 1) / n : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The complex geometric sum `∑_{s=0}^{n-1} ζ^{s+1} = 0` when `n ∤ m` (so `ζ ≠ 1`, `ζ^n = 1`). -/
private lemma trig_geomSum_eq_zero {n m : ℕ} (hm : ¬ (n : ℤ) ∣ (m : ℤ)) :
    ∑ s ∈ Finset.range n, (Complex.exp (2 * Real.pi * Complex.I * m / n)) ^ (s + 1) = 0 := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    set ζ := Complex.exp (2 * Real.pi * Complex.I * m / n) with hζdef
    have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hζ1 : ζ ≠ 1 := by
      rw [hζdef, Ne, Complex.exp_eq_one_iff]
      rintro ⟨k, hk⟩
      rw [div_eq_iff hn'] at hk
      apply hm
      set c := (2 * (Real.pi : ℂ) * Complex.I) with hcdef
      have hmk : c * m = c * (k * n) := by rw [hcdef, hk]; ring
      have hmkn : (m : ℂ) = k * n := mul_left_cancel₀ hc hmk
      have : ((m : ℤ) : ℂ) = ((n * k : ℤ) : ℂ) := by push_cast; rw [hmkn]; ring
      exact ⟨k, by exact_mod_cast this⟩
    have hζn : ζ ^ n = 1 := by
      rw [hζdef, ← Complex.exp_nat_mul]
      have : (n : ℂ) * (2 * Real.pi * Complex.I * m / n) = m * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [this, Complex.exp_nat_mul_two_pi_mul_I]
    have hsplit : ∑ s ∈ Finset.range n, ζ ^ (s + 1) = ζ * ∑ s ∈ Finset.range n, ζ ^ s := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; rw [pow_succ]; ring
    rw [hsplit, geom_sum_eq hζ1, hζn]
    simp

/-- `∑_{s=1}^{n} cos(2π·m·s/n) = 0` when `n ∤ m`. -/
theorem sum_cos_two_pi_mul_div_eq_zero {n m : ℕ} (hm : ¬ (n : ℤ) ∣ (m : ℤ)) :
    ∑ s ∈ Finset.range n, Real.cos (2 * Real.pi * m * (s + 1) / n) = 0 := by
  have h : ∑ s ∈ Finset.range n, Real.cos (2 * Real.pi * m * (s + 1) / n)
      = (∑ s ∈ Finset.range n, (Complex.exp (2 * Real.pi * Complex.I * m / n)) ^ (s + 1)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro s _
    rw [trig_exp_pow_eq, Complex.exp_ofReal_mul_I_re]
  rw [h, trig_geomSum_eq_zero hm, Complex.zero_re]

/-- `∑_{s=1}^{n} sin(2π·m·s/n) = 0` when `n ∤ m`. -/
theorem sum_sin_two_pi_mul_div_eq_zero {n m : ℕ} (hm : ¬ (n : ℤ) ∣ (m : ℤ)) :
    ∑ s ∈ Finset.range n, Real.sin (2 * Real.pi * m * (s + 1) / n) = 0 := by
  have h : ∑ s ∈ Finset.range n, Real.sin (2 * Real.pi * m * (s + 1) / n)
      = (∑ s ∈ Finset.range n, (Complex.exp (2 * Real.pi * Complex.I * m / n)) ^ (s + 1)).im := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl; intro s _
    rw [trig_exp_pow_eq, Complex.exp_ofReal_mul_I_im]
  rw [h, trig_geomSum_eq_zero hm, Complex.zero_im]

/-- `∑_{s=1}^{n} cos(2π·m·s/n) = n` when `n ∣ m` (every angle is a multiple of `2π`). -/
theorem sum_cos_two_pi_mul_div_of_dvd {n m : ℕ} (hm : (n : ℤ) ∣ (m : ℤ)) :
    ∑ s ∈ Finset.range n, Real.cos (2 * Real.pi * m * (s + 1) / n) = n := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    obtain ⟨t, ht⟩ := Int.natCast_dvd_natCast.mp hm
    have hterm : ∀ s ∈ Finset.range n,
        Real.cos (2 * Real.pi * m * (s + 1) / n) = 1 := by
      intro s _
      have he : 2 * Real.pi * (m : ℝ) * (s + 1) / n = (↑(t * (s + 1)) : ℝ) * (2 * Real.pi) := by
        rw [ht]; push_cast; field_simp
      rw [he, Real.cos_nat_mul_two_pi]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- `∑_{s=1}^{n} sin(2π·m·s/n) = 0` when `n ∣ m` (every angle is a multiple of `2π`). -/
theorem sum_sin_two_pi_mul_div_of_dvd {n m : ℕ} (hm : (n : ℤ) ∣ (m : ℤ)) :
    ∑ s ∈ Finset.range n, Real.sin (2 * Real.pi * m * (s + 1) / n) = 0 := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    obtain ⟨t, ht⟩ := Int.natCast_dvd_natCast.mp hm
    have hterm : ∀ s ∈ Finset.range n,
        Real.sin (2 * Real.pi * m * (s + 1) / n) = 0 := by
      intro s _
      have he : 2 * Real.pi * (m : ℝ) * (s + 1) / n = (↑(2 * (t * (s + 1))) : ℝ) * Real.pi := by
        rw [ht]; push_cast; field_simp
      rw [he, Real.sin_nat_mul_pi]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_zero]

end StatLean.NonparametricStatistics
