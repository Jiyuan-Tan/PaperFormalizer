module
public import StatLean.TimeSeries.ForMathlib.PosSemidefSequence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Fejér–Cesàro sums of a sequence

For `γ : ℤ → ℝ` and `n : ℕ`, the **Fejér–Cesàro sum**
`fejerSum γ n ω = (2πn)⁻¹ Σ_{j,k<n} γ(j−k) e^{−iω(j−k)}
              = (2π)⁻¹ Σ_{|m|<n} (1 − |m|/n) γ(m) e^{−iωm}`
is the density (in `ω ∈ [−π, π]`) of the approximating spectral measures in the proof of
the Herglotz theorem (FY §2.7.4). Key facts stated here:

* the diagonal-collection identity (double sum = Fejér-weighted single sum);
* for even `γ` the sum is real; for positive semidefinite `γ` it is nonnegative — the
  probabilistic positivity `f_n(ω) = Var(Σⱼ e^{−iωj} X_j)/(2πn γ(0)) ≥ 0` of the book,
  obtained here directly from `IsPosSemidefSeq.complex_sum_re_nonneg` with the
  coefficient vector `cⱼ = e^{−iωj}`;
* the trigonometric-moment identity (FY eq. (2.71)):
  `∫_{−π}^{π} e^{ijω} fejerSum γ n ω dω = (1 − |j|/n) γ(j)` for `|j| < n`, `0` otherwise,
  via the basic orthogonality `∫_{−π}^{π} e^{imω} dω = 0` for `m ≠ 0`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.7.4
(pp. 80–81), supporting Theorem 2.10; the same Fejér weights appear in the in-text proof
of Theorem 2.11 (p. 52). (`FY §2.7.4, eq. (2.71)`.)

**Proof formalization notes.** `fejerSum γ 0 ω = 0` by the `(0 : ℝ)⁻¹ = 0` junk
convention (the `n = 0` case never occurs in use). The nonnegativity route deliberately
avoids constructing the random variable `ξ` of the book's proof: positive
semidefiniteness of `γ` is exactly what the variance computation extracts, so we take it
as the hypothesis.

**Bibliographic comments.** Fejér's kernel and the Cesàro summation of Fourier series are
L. Fejér, "Untersuchungen über Fouriersche Reihen", *Math. Ann.* **58** (1904), 51–69.
Their use to prove Herglotz's theorem is classical; the book follows Brockwell & Davis
(1991), pp. 118–119.
-/

open scoped Real
open Finset

namespace StatLean.TimeSeries

/-- The **Fejér–Cesàro sum** `(2πn)⁻¹ Σ_{j,k<n} γ(j−k) e^{−iω(j−k)}` (FY §2.7.4).
Junk value `0` at `n = 0`. -/
noncomputable def fejerSum (γ : ℤ → ℝ) (n : ℕ) (ω : ℝ) : ℂ :=
  (((2 * π * n)⁻¹ : ℝ) : ℂ) * ∑ j ∈ range n, ∑ k ∈ range n,
    (γ ((j : ℤ) - (k : ℤ)) : ℂ) *
      Complex.exp (-(Complex.I * (ω : ℂ) * (((j : ℤ) - (k : ℤ) : ℤ) : ℂ)))

/-- The diagonal `{(j, k) ∈ [0,n)² : j − k = m}` is parametrized by `i ↦ (i + a, i + b)`
where `(a, b)` is `(m, 0)` for `m ≥ 0` and `(0, −m)` for `m ≤ 0`; it therefore has
`n − (a + b) = n − |m|` elements. -/
private lemma card_fiber_sub (n a b : ℕ) (m : ℤ) (hab : a = 0 ∨ b = 0)
    (hm : (a : ℤ) - (b : ℤ) = m) :
    #({p ∈ Finset.range n ×ˢ Finset.range n | (p.1 : ℤ) - (p.2 : ℤ) = m}) = n - (a + b) := by
  rw [show n - (a + b) = #(Finset.range (n - (a + b))) from (Finset.card_range _).symm]
  refine Finset.card_nbij' (fun p => p.1 - a) (fun i => (i + a, i + b)) ?_ ?_ ?_ ?_ <;>
    intro p hp <;>
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
      Finset.mem_range, Finset.coe_range, Set.mem_Iio, Prod.ext_iff] at hp ⊢ <;>
    omega

/-- Diagonal collection for an arbitrary summand: `Σ_{j,k<n} F(j−k) = Σ_{|m|<n} (n−|m|) F(m)`. -/
private lemma sum_range_sub_eq_weighted (F : ℤ → ℂ) (n : ℕ) :
    ∑ j ∈ range n, ∑ k ∈ range n, F ((j : ℤ) - (k : ℤ))
      = ∑ m ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1), ((((n : ℤ) - |m|) : ℤ) : ℂ) * F m := by
  have hmaps : ∀ p ∈ Finset.range n ×ˢ Finset.range n,
      ((p.1 : ℤ) - (p.2 : ℤ)) ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_Icc]
    omega
  rw [← Finset.sum_product', ← Finset.sum_fiberwise_of_maps_to' hmaps F]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_Icc] at hm
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  by_cases h0 : 0 ≤ m
  · obtain ⟨c, rfl⟩ : ∃ c : ℕ, m = (c : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg h0).symm⟩
    have hcn : c ≤ n := by omega
    rw [card_fiber_sub n c 0 _ (Or.inr rfl) (by push_cast; ring), add_zero,
      Nat.cast_sub hcn, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (c : ℤ))]
    push_cast
    ring
  · obtain ⟨c, rfl⟩ : ∃ c : ℕ, m = -(c : ℤ) := ⟨(-m).toNat, by omega⟩
    have hcn : c ≤ n := by omega
    rw [card_fiber_sub n 0 c _ (Or.inl rfl) (by push_cast; ring), zero_add,
      Nat.cast_sub hcn, abs_of_nonpos (by omega : -(c : ℤ) ≤ 0)]
    push_cast
    ring

/-- Diagonal collection: the Fejér double sum equals the weighted single sum
`(2πn)⁻¹ Σ_{|m|<n} (n − |m|) γ(m) e^{−iωm}` (the display below FY eq. (2.71)). -/
theorem fejerSum_eq_weighted (γ : ℤ → ℝ) (n : ℕ) (ω : ℝ) :
    fejerSum γ n ω = (((2 * π * n)⁻¹ : ℝ) : ℂ) *
      ∑ m ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1),
        ((((n : ℤ) - |m|) : ℤ) : ℂ) * (γ m : ℂ) *
          Complex.exp (-(Complex.I * (ω : ℂ) * (m : ℂ))) := by
  rw [fejerSum, sum_range_sub_eq_weighted
    (fun m => (γ m : ℂ) * Complex.exp (-(Complex.I * (ω : ℂ) * (m : ℂ)))) n]
  congr 1
  exact Finset.sum_congr rfl fun m _ => (mul_assoc _ _ _).symm

/-- The Fejér double sum *is* the Hermitian quadratic form of `γ` at the time points
`t j = j` with the coefficient vector `c j = e^{−iωj}` — the algebraic content of the
book's variance computation. -/
private theorem fejerSum_eq_hermitian (γ : ℤ → ℝ) (n : ℕ) (ω : ℝ) :
    fejerSum γ n ω = (((2 * π * n)⁻¹ : ℝ) : ℂ) *
      ∑ i : Fin n, ∑ j : Fin n,
        Complex.exp (-(Complex.I * (ω : ℂ) * ((i : ℕ) : ℂ))) *
            (starRingEnd ℂ) (Complex.exp (-(Complex.I * (ω : ℂ) * ((j : ℕ) : ℂ)))) *
          (γ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) : ℂ) := by
  rw [fejerSum]
  congr 1
  simp only [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hconj : (starRingEnd ℂ) (Complex.exp (-(Complex.I * (ω : ℂ) * ((j : ℕ) : ℂ))))
      = Complex.exp (Complex.I * (ω : ℂ) * ((j : ℕ) : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  rw [hconj, ← Complex.exp_add]
  have hexp : Complex.exp (-(Complex.I * (ω : ℂ) * ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : ℂ)))
      = Complex.exp (-(Complex.I * (ω : ℂ) * ((i : ℕ) : ℂ)) + Complex.I * (ω : ℂ) * ((j : ℕ) : ℂ))
      := by
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- For even `γ` the Fejér sum is real. -/
theorem fejerSum_im (γ : ℤ → ℝ) (heven : ∀ k, γ (-k) = γ k) (n : ℕ) (ω : ℝ) :
    (fejerSum γ n ω).im = 0 := by
  rw [fejerSum, Complex.im_ofReal_mul]
  -- the double sum is fixed by conjugation: conjugating swaps `j` and `k`, and evenness
  -- of `γ` together with `e^{iωm} = conj (e^{−iωm})` restores the summand
  have hstar : (starRingEnd ℂ) (∑ j ∈ range n, ∑ k ∈ range n,
        (γ ((j : ℤ) - (k : ℤ)) : ℂ) *
          Complex.exp (-(Complex.I * (ω : ℂ) * (((j : ℤ) - (k : ℤ) : ℤ) : ℂ))))
      = ∑ j ∈ range n, ∑ k ∈ range n,
        (γ ((j : ℤ) - (k : ℤ)) : ℂ) *
          Complex.exp (-(Complex.I * (ω : ℂ) * (((j : ℤ) - (k : ℤ) : ℤ) : ℂ))) := by
    simp only [map_sum, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have hsym : γ ((k : ℤ) - (j : ℤ)) = γ ((j : ℤ) - (k : ℤ)) := by rw [← neg_sub, heven]
    rw [hsym]
    congr 1
    push_cast
    simp only [map_neg, map_mul, map_sub, map_natCast, Complex.conj_I, Complex.conj_ofReal]
    ring_nf
  rw [Complex.conj_eq_iff_im.mp hstar, mul_zero]

/-- **Fejér positivity**: for an even positive semidefinite `γ`, the Fejér sum is
nonnegative (FY §2.7.4: `f_n(ω) = Var(ξ) ≥ 0`). -/
theorem fejerSum_re_nonneg (γ : ℤ → ℝ) (h : IsPosSemidefSeq γ)
    (heven : ∀ k, γ (-k) = γ k) (n : ℕ) (ω : ℝ) :
    0 ≤ (fejerSum γ n ω).re := by
  rw [fejerSum_eq_hermitian, Complex.re_ofReal_mul]
  refine mul_nonneg (by positivity) ?_
  exact h.complex_sum_re_nonneg heven (fun i => ((i : ℕ) : ℤ))
    (fun i => Complex.exp (-(Complex.I * (ω : ℂ) * ((i : ℕ) : ℂ))))

/-- Basic orthogonality on `[−π, π]`: `∫_{−π}^{π} e^{imω} dω = 0` for a nonzero integer
`m` (the engine of FY eq. (2.71) and of the inversion computations of §2.3.2). -/
theorem integral_exp_int_mul_I_eq_zero {m : ℤ} (hm : m ≠ 0) :
    ∫ ω in (-π : ℝ)..π, Complex.exp (Complex.I * (ω : ℂ) * (m : ℂ)) = 0 := by
  have hmC : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hc : Complex.I * (m : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hmC
  have hrw : ∀ ω : ℝ, Complex.exp (Complex.I * (ω : ℂ) * (m : ℂ))
      = Complex.exp (Complex.I * (m : ℂ) * (ω : ℂ)) := by
    intro ω; ring_nf
  simp_rw [hrw]
  rw [integral_exp_mul_complex hc]
  have hper : Complex.exp (Complex.I * (m : ℂ) * ((π : ℝ) : ℂ))
      = Complex.exp (Complex.I * (m : ℂ) * (((-π : ℝ)) : ℂ)) := by
    have hsplit : Complex.I * (m : ℂ) * ((π : ℝ) : ℂ)
        = Complex.I * (m : ℂ) * (((-π : ℝ)) : ℂ) + (m : ℂ) * (2 * (π : ℝ) * Complex.I) := by
      push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hper, sub_self, zero_div]

/-- Term-by-term integration of the weighted Fejér sum against `e^{ijω}`: only the
`m = j` slot survives the orthogonality `∫_{−π}^{π} e^{iω(j−m)} dω = 0`. -/
private lemma integral_fejerSum_mul_exp (γ : ℤ → ℝ) (n : ℕ) (j : ℤ) :
    ∫ ω in (-π : ℝ)..π,
        fejerSum γ n ω * Complex.exp (Complex.I * (ω : ℂ) * (j : ℂ))
      = ∑ m ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1),
          (if m = j then
            (((2 * π * n)⁻¹ : ℝ) : ℂ) * ((((n : ℤ) - |m|) : ℤ) : ℂ) * (γ m : ℂ) *
              ((2 * π : ℝ) : ℂ)
          else 0) := by
  have hint : ∀ ω : ℝ, fejerSum γ n ω * Complex.exp (Complex.I * (ω : ℂ) * (j : ℂ))
      = ∑ m ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1),
          ((((2 * π * n)⁻¹ : ℝ) : ℂ) * ((((n : ℤ) - |m|) : ℤ) : ℂ) * (γ m : ℂ)) *
            Complex.exp (Complex.I * (ω : ℂ) * (((j - m : ℤ) : ℤ) : ℂ)) := by
    intro ω
    rw [fejerSum_eq_weighted, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hexp : Complex.exp (-(Complex.I * (ω : ℂ) * (m : ℂ))) *
          Complex.exp (Complex.I * (ω : ℂ) * (j : ℂ))
        = Complex.exp (Complex.I * (ω : ℂ) * (((j - m : ℤ) : ℤ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hexp]
    ring
  simp_rw [hint]
  rw [intervalIntegral.integral_finset_sum
    (fun m _ => (Continuous.intervalIntegrable (by fun_prop) _ _))]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hcm : ∀ (r : ℂ) (m' : ℤ),
      (∫ ω in (-π : ℝ)..π, r * Complex.exp (Complex.I * (ω : ℂ) * (m' : ℂ)))
        = r * ∫ ω in (-π : ℝ)..π, Complex.exp (Complex.I * (ω : ℂ) * (m' : ℂ)) :=
    fun r m' => intervalIntegral.integral_const_mul r _
  rw [hcm]
  by_cases h : m = j
  · subst h
    have hconst : (∫ _ω in (-π : ℝ)..π,
          Complex.exp (Complex.I * ((_ω : ℝ) : ℂ) * (((m - m : ℤ) : ℤ) : ℂ)))
        = ((2 * π : ℝ) : ℂ) := by
      simp only [sub_self, Int.cast_zero, mul_zero, Complex.exp_zero]
      rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) from by norm_num, intervalIntegral.integral_ofReal,
        intervalIntegral.integral_const, smul_eq_mul]
      push_cast
      ring
    rw [if_pos rfl, hconst]
  · rw [if_neg h,
      integral_exp_int_mul_I_eq_zero (sub_ne_zero.mpr fun hc => h hc.symm), mul_zero]

/-- Trigonometric moments of the Fejér sum, in-range case (FY eq. (2.71)):
`∫_{−π}^{π} e^{ijω} fejerSum γ n ω dω = ((n − |j|)/n) γ(j)` for `|j| < n`. -/
theorem integral_fejerSum_mul_exp_of_lt (γ : ℤ → ℝ) {n : ℕ} {j : ℤ} (hj : |j| < (n : ℤ)) :
    ∫ ω in (-π : ℝ)..π,
        fejerSum γ n ω * Complex.exp (Complex.I * (ω : ℂ) * (j : ℂ))
      = (((((n : ℤ) - |j|) : ℤ) : ℂ) / (n : ℂ)) * (γ j : ℂ) := by
  obtain ⟨hj1, hj2⟩ := abs_lt.mp hj
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hπC : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [integral_fejerSum_mul_exp, Finset.sum_eq_single j]
  · rw [if_pos rfl]
    push_cast
    field_simp
  · intro m _ hm
    rw [if_neg hm]
  · intro hmem
    exact absurd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) hmem

/-- Trigonometric moments of the Fejér sum, out-of-range case (FY eq. (2.71)):
the integral vanishes for `|j| ≥ n`. -/
theorem integral_fejerSum_mul_exp_of_le (γ : ℤ → ℝ) {n : ℕ} {j : ℤ}
    (hj : (n : ℤ) ≤ |j|) :
    ∫ ω in (-π : ℝ)..π,
        fejerSum γ n ω * Complex.exp (Complex.I * (ω : ℂ) * (j : ℂ)) = 0 := by
  rw [integral_fejerSum_mul_exp]
  refine Finset.sum_eq_zero fun m hm => ?_
  simp only [Finset.mem_Icc] at hm
  have hne : m ≠ j := by
    rcases abs_cases j with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hj <;> omega
  rw [if_neg hne]

end StatLean.TimeSeries
