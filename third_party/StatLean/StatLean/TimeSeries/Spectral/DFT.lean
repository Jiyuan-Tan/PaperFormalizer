module
public import StatLean.TimeSeries.Process.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# The discrete Fourier transform of a data vector (FY §2.4.1)

Fourier frequencies `ω_k = 2πk/T`, the unitary DFT
`α_k = T^{-1/2} Σ_{t=1}^{T} x_t e^{−itω_k}` (FY eqs. (2.49)–(2.51); we index data by
`Fin T` with `t + 1` playing the book's `t ∈ {1, …, T}`), the orthonormality of the
harmonic vectors (in-text proof: geometric sums of roots of unity — the same engine as
`NonparametricStatistics/ForMathlib/TrigDiscreteSums.lean`), and the discrete Parseval
identity (FY eq. (2.52)).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.4.1
(pp. 60–62, eqs. (2.49)–(2.54)). (`FY §2.4.1`.)

**Proof formalization notes.** The DFT is defined for `k : ℤ` (it is `T`-periodic in
`k`; FY's index window `−[(T−1)/2] ≤ k ≤ [T/2]` is a choice of representatives).
Orthonormality is stated as the inner-product identity for the exponential vectors;
Parseval sums `|α_k|²` over any window of `T` consecutive `k`s — we state it over
`k ∈ Finset.range T`, equivalent by periodicity.

**Bibliographic comments.** The finite Fourier analysis of time series goes back to
A. Schuster's periodogram (1898); the unitary normalization follows FY.
-/

open Finset
open scoped Real

namespace StatLean.TimeSeries

/-- The **Fourier frequency** `ω_k = 2πk/T` (FY §2.4.1). -/
noncomputable def fourierFreq (T : ℕ) (k : ℤ) : ℝ := 2 * π * k / T

/-- The **unitary DFT** of a data vector (FY eq. (2.51)):
`α_k = T^{-1/2} Σ_{t=1}^{T} x_t e^{−itω_k}`. -/
noncomputable def dft {T : ℕ} (x : Fin T → ℝ) (k : ℤ) : ℂ :=
  ((Real.sqrt T)⁻¹ : ℝ) * ∑ t : Fin T, (x t : ℂ) *
    Complex.exp (-(Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ) * (fourierFreq T k : ℂ)))

/-! ### The roots-of-unity engine

All the discrete orthogonality sums below are geometric sums of the root of unity
`ζ_{T,m} = e^{2πim/T}`; the proof pattern is the one of
`NonparametricStatistics/ForMathlib/TrigDiscreteSums.lean`. -/

/-- The root of unity `ζ_{T,m} = e^{2πim/T}`. Junk value `1` when `T = 0`. -/
private noncomputable def rootU (T : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (Complex.I * ((2 * π * (m : ℝ) / (T : ℝ) : ℝ) : ℂ))

/-- `ζ_{T,m}^T = e^{2πim} = 1`. -/
private lemma rootU_pow_self {T : ℕ} (hT : 0 < T) (m : ℤ) : rootU T m ^ T = 1 := by
  have hTC : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  rw [rootU, ← Complex.exp_nat_mul]
  have h : (T : ℂ) * (Complex.I * ((2 * π * (m : ℝ) / (T : ℝ) : ℝ) : ℂ))
      = ((m : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- `ζ_{T,m} ≠ 1` exactly when `T ∤ m`. -/
private lemma rootU_ne_one {T : ℕ} (hT : 0 < T) {m : ℤ} (hm : ¬ ((T : ℤ) ∣ m)) :
    rootU T m ≠ 1 := by
  have hTR : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  rw [rootU, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  apply hm
  have h1 : ((2 * π * (m : ℝ) / (T : ℝ) : ℝ) : ℂ) * Complex.I
      = ((2 * π * (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast at hn ⊢
    linear_combination hn
  have h2 : (2 * π * (m : ℝ) / (T : ℝ) : ℝ) = 2 * π * (n : ℝ) := by
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h1
  field_simp at h2
  refine ⟨n, ?_⟩
  have h4 : ((m : ℤ) : ℝ) = ((T * n : ℤ) : ℝ) := by push_cast; linarith [h2]
  exact_mod_cast h4

/-- The full geometric sum of a nontrivial root of unity vanishes. -/
private lemma sum_rootU_pow {T : ℕ} {m : ℤ} (hm : ¬ ((T : ℤ) ∣ m)) :
    ∑ j ∈ Finset.range T, rootU T m ^ j = 0 := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp
  · rw [geom_sum_eq (rootU_ne_one hT hm), rootU_pow_self hT m, sub_self, zero_div]

/-- The `1`-shifted geometric sum (the book's `t = 1, …, T`) also vanishes. -/
private lemma sum_rootU_pow_succ {T : ℕ} {m : ℤ} (hm : ¬ ((T : ℤ) ∣ m)) :
    ∑ t : Fin T, rootU T m ^ ((t : ℕ) + 1) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun n => rootU T m ^ (n + 1)) T]
  have : ∑ n ∈ Finset.range T, rootU T m ^ (n + 1)
      = rootU T m * ∑ n ∈ Finset.range T, rootU T m ^ n := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [pow_succ]; ring
  rw [this, sum_rootU_pow hm, mul_zero]

/-- `e^{imω_k} = ζ_{T,m}^k`: the exponential at a Fourier frequency is a power of the
root of unity. -/
private lemma exp_fourierFreq_eq_rootU_pow (T : ℕ) (m : ℤ) (k : ℕ) :
    Complex.exp (Complex.I * (m : ℂ) * ((fourierFreq T (k : ℤ) : ℝ) : ℂ)) = rootU T m ^ k := by
  rw [rootU, ← Complex.exp_nat_mul]
  congr 1
  unfold fourierFreq
  push_cast
  ring

/-- `ζ_{T,0} = 1`. -/
private lemma rootU_zero (T : ℕ) : rootU T 0 = 1 := by
  simp [rootU]

/-- The DFT is `T`-periodic in the frequency index. -/
theorem dft_periodic {T : ℕ} (x : Fin T → ℝ) (k : ℤ) :
    dft x (k + T) = dft x k := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp [dft]
  have hTR : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hfreq : fourierFreq T (k + T) = fourierFreq T k + 2 * π := by
    unfold fourierFreq
    push_cast
    field_simp
  unfold dft
  rw [hfreq]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have hsplit : -(Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ) * ((fourierFreq T k + 2 * π : ℝ) : ℂ))
      = -(Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ) * ((fourierFreq T k : ℝ) : ℂ))
        + ((-((t : ℕ) + 1 : ℕ) : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Exponential-vector orthogonality** (FY §2.4.1, in-text): for `j ≢ k (mod T)`,
`Σ_{t=1}^{T} e^{it(ω_k − ω_j)} = 0`. -/
theorem sum_exp_fourierFreq_eq_zero {T : ℕ} (hT : 0 < T) {j k : ℤ}
    (hjk : ¬ ((T : ℤ) ∣ (k - j))) :
    ∑ t : Fin T, Complex.exp
      (Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ) * ((fourierFreq T k - fourierFreq T j : ℝ) : ℂ))
      = 0 := by
  have hterm : ∀ t : Fin T,
      Complex.exp (Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ)
          * ((fourierFreq T k - fourierFreq T j : ℝ) : ℂ))
        = rootU T (k - j) ^ ((t : ℕ) + 1) := by
    intro t
    rw [rootU, ← Complex.exp_nat_mul]
    congr 1
    unfold fourierFreq
    push_cast
    ring
  rw [Finset.sum_congr rfl fun t _ => hterm t]
  exact sum_rootU_pow_succ hjk

/-- `‖z‖²`, pushed into `ℂ`, is `z · z̄`. -/
private lemma ofReal_norm_sq (z : ℂ) : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- The conjugate of the DFT flips the sign of the exponent. -/
private lemma conj_dft {T : ℕ} (x : Fin T → ℝ) (k : ℤ) :
    (starRingEnd ℂ) (dft x k) = ((Real.sqrt T)⁻¹ : ℝ) * ∑ s : Fin T, (x s : ℂ) *
      Complex.exp (Complex.I * (((s : ℕ) + 1 : ℕ) : ℂ) * (fourierFreq T k : ℂ)) := by
  rw [dft, map_mul, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast]
  ring_nf

/-- The frequency sum of `ζ_{T, s−t}^k` over a full period is `T` on the diagonal and `0`
off it: `t, s < T` forces `T ∣ s − t ↔ s = t`. -/
private lemma sum_rootU_pow_fin {T : ℕ} (t s : Fin T) :
    ∑ k ∈ Finset.range T, rootU T (((s : ℕ) : ℤ) - ((t : ℕ) : ℤ)) ^ k
      = if s = t then (T : ℂ) else 0 := by
  by_cases h : s = t
  · subst h
    simp [rootU_zero]
  · rw [if_neg h]
    refine sum_rootU_pow ?_
    intro hdvd
    exact h (Fin.ext (by
      have habs : |((s : ℕ) : ℤ) - ((t : ℕ) : ℤ)| < (T : ℤ) := by
        have hs : ((s : ℕ) : ℤ) < (T : ℤ) := by exact_mod_cast s.2
        have ht : ((t : ℕ) : ℤ) < (T : ℤ) := by exact_mod_cast t.2
        have hs0 : (0 : ℤ) ≤ ((s : ℕ) : ℤ) := Int.natCast_nonneg _
        have ht0 : (0 : ℤ) ≤ ((t : ℕ) : ℤ) := Int.natCast_nonneg _
        rw [abs_lt]; omega
      have := Int.eq_zero_of_abs_lt_dvd hdvd habs
      omega))

/-- **Discrete Parseval** (FY eq. (2.52)): `Σ_t x_t² = Σ_{k<T} |α_k|²`. -/
theorem sum_sq_eq_sum_normSq_dft {T : ℕ} (x : Fin T → ℝ) :
    ∑ t : Fin T, (x t) ^ 2 = ∑ k ∈ Finset.range T, ‖dft x (k : ℤ)‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp
  have hTR : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hTC : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hc : (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * (((Real.sqrt T)⁻¹ : ℝ) : ℂ) = ((T : ℂ))⁻¹ := by
    rw [← Complex.ofReal_mul, ← sq, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (T : ℝ))]
    push_cast
    ring
  -- expand `|α_k|²` as a double sum of roots of unity
  have hexp : ∀ k : ℕ, ((‖dft x (k : ℤ)‖ : ℝ) : ℂ) ^ 2
      = ((T : ℂ))⁻¹ * ∑ t : Fin T, ∑ s : Fin T,
          (x t : ℂ) * (x s : ℂ) * rootU T (((s : ℕ) : ℤ) - ((t : ℕ) : ℤ)) ^ k := by
    intro k
    rw [ofReal_norm_sq, conj_dft, dft, mul_mul_mul_comm, hc, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
    have hprod : Complex.exp (-(Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ) * (fourierFreq T k : ℂ)))
        * Complex.exp (Complex.I * (((s : ℕ) + 1 : ℕ) : ℂ) * (fourierFreq T k : ℂ))
        = rootU T (((s : ℕ) : ℤ) - ((t : ℕ) : ℤ)) ^ k := by
      rw [← Complex.exp_add, rootU, ← Complex.exp_nat_mul]
      congr 1
      unfold fourierFreq
      push_cast
      ring
    rw [← hprod]
    ring
  -- sum over the frequencies, swap, and collapse the diagonal
  refine Complex.ofReal_inj.mp ?_
  rw [Complex.ofReal_sum, Complex.ofReal_sum]
  have hpow : ∀ t : Fin T, ((x t ^ 2 : ℝ) : ℂ) = (x t : ℂ) * (x t : ℂ) := by
    intro t; push_cast; ring
  rw [Finset.sum_congr rfl fun t _ => hpow t]
  have hcast : ∀ k ∈ Finset.range T, ((‖dft x (k : ℤ)‖ ^ 2 : ℝ) : ℂ)
      = ((T : ℂ))⁻¹ * ∑ t : Fin T, ∑ s : Fin T,
          (x t : ℂ) * (x s : ℂ) * rootU T (((s : ℕ) : ℤ) - ((t : ℕ) : ℤ)) ^ k := by
    intro k _
    rw [Complex.ofReal_pow]
    exact hexp k
  rw [Finset.sum_congr rfl hcast, ← Finset.mul_sum]
  have hswap : ∑ k ∈ Finset.range T, ∑ t : Fin T, ∑ s : Fin T,
        (x t : ℂ) * (x s : ℂ) * rootU T (((s : ℕ) : ℤ) - ((t : ℕ) : ℤ)) ^ k
      = ∑ t : Fin T, ∑ s : Fin T, ∑ k ∈ Finset.range T,
        (x t : ℂ) * (x s : ℂ) * rootU T (((s : ℕ) : ℤ) - ((t : ℕ) : ℤ)) ^ k := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_comm
  rw [hswap]
  have hinner : ∀ t : Fin T, ∑ s : Fin T, ∑ k ∈ Finset.range T,
        (x t : ℂ) * (x s : ℂ) * rootU T (((s : ℕ) : ℤ) - ((t : ℕ) : ℤ)) ^ k
      = (T : ℂ) * ((x t : ℂ) * (x t : ℂ)) := by
    intro t
    have hs : ∀ s : Fin T, ∑ k ∈ Finset.range T,
        (x t : ℂ) * (x s : ℂ) * rootU T (((s : ℕ) : ℤ) - ((t : ℕ) : ℤ)) ^ k
        = if s = t then (T : ℂ) * ((x t : ℂ) * (x t : ℂ)) else 0 := by
      intro s
      rw [← Finset.mul_sum, sum_rootU_pow_fin t s]
      by_cases h : s = t
      · subst h; simp; ring
      · simp [h]
    rw [Finset.sum_congr rfl fun s _ => hs s, Finset.sum_ite_eq' Finset.univ t]
    simp
  rw [Finset.sum_congr rfl fun t _ => hinner t, ← Finset.mul_sum, ← mul_assoc,
    inv_mul_cancel₀ hTC, one_mul]

end StatLean.TimeSeries
