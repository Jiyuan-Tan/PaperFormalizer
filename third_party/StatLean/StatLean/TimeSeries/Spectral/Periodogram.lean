module
public import StatLean.TimeSeries.Spectral.DFT

@[expose] public section

/-!
# The periodogram (FY §2.4.2, Definition 2.8, Theorem 2.13)

`I_T(ω_k) = T⁻¹|Σ_t x_t e^{−itω_k}|² = |α_k|²` (FY Definition 2.8; no `2π` anywhere in
`I_T` — the density estimator is `I_T/2π`), the energy decomposition
`Σ_t x_t² = Σ_k I_T(ω_k)` (from discrete Parseval), and **FY Theorem 2.13** — the
deterministic identity `I_T(ω_k) = Σ_{|τ|<T} γ̂(τ) e^{−iτω_k}` for `k ≢ 0 (mod T)`,
where `γ̂` is the divisor-`T`, mean-corrected sample ACVF (FY eq. (2.23); §2.7.5 proof:
free mean-centering by root-of-unity sums, then reindex `τ = t − s`).

(FY Theorem 2.14 — the asymptotic distribution of the periodogram over a linear
process — is a batch-C target: its part (i) consumes the commissioned triangular-array
CLT; the statement will be added alongside `ForMathlib/Probability/TriangularCLT`.)

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.4.2,
Definition 2.8, Theorem 2.13 (pp. 62–63) and §2.7.5 (p. 81).
(`FY §2.4.2 Def 2.8, Thm 2.13; §2.7.5`.)

**Proof formalization notes.** Theorem 2.13 is per-data-vector (no probability); the
`k ≠ 0` hypothesis is the mod-`T` nondivisibility that kills the constant vector. The
sample-ACVF sum over `|τ| < T` is written as `τ = 0` plus two symmetric tails (our
`sampleACVF` takes `k : ℕ`; evenness of the sample ACVF is part of the statement's
bookkeeping).

**Bibliographic comments.** A. Schuster, "On the investigation of hidden periodicities"
(1898). The sample-ACVF identity is classical; FY follow Brockwell & Davis (1991),
Prop. 10.1.2.
-/

open Finset
open scoped Real

namespace StatLean.TimeSeries

/-- The **periodogram** (FY Definition 2.8): `I_T(k) = |α_k|²` at the `k`-th Fourier
frequency. -/
noncomputable def periodogram {T : ℕ} (x : Fin T → ℝ) (k : ℤ) : ℝ :=
  ‖dft x k‖ ^ 2

/-- **Energy decomposition** (FY §2.4.2, from eq. (2.52)):
`Σ_t x_t² = Σ_{k<T} I_T(k)`. -/
theorem sum_sq_eq_sum_periodogram {T : ℕ} (x : Fin T → ℝ) :
    ∑ t : Fin T, (x t) ^ 2 = ∑ k ∈ Finset.range T, periodogram x (k : ℤ) := by
  simpa only [periodogram] using sum_sq_eq_sum_normSq_dft x

/-! ### Machinery for Theorem 2.13

The mean-corrected data extended by `0` outside the observation window, the elementary
exponential `e^{imω}`, and the diagonal-collection lemma that groups a double sum over
`[0,T)²` by the lag `τ = b − a` (the template is the private `sum_range_sub_eq_weighted`
of `ForMathlib/Fourier/FejerKernel.lean`; here the coefficients are not a function of the
lag alone, so the fibers are re-indexed rather than counted). -/

/-- The mean-corrected data, extended by `0` outside the observation window. -/
private noncomputable def centered {T : ℕ} (x : Fin T → ℝ) (n : ℕ) : ℝ :=
  if h : n < T then x ⟨n, h⟩ - sampleMean x else 0

private lemma centered_of_le {T : ℕ} {x : Fin T → ℝ} {n : ℕ} (hn : T ≤ n) :
    centered x n = 0 := by
  rw [centered, dif_neg (by omega)]

/-- The sample autocovariance in terms of the extended centred data: the `dite` guard of
`sampleACVF` is exactly the vanishing of `centered` past the window. -/
private lemma sampleACVF_eq_centered {T : ℕ} (x : Fin T → ℝ) (τ : ℕ) :
    sampleACVF x τ = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, centered x t * centered x (t + τ) := by
  rw [sampleACVF, ← Fin.sum_univ_eq_sum_range
    (fun n => centered x n * centered x (n + τ)) T]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [centered, t.isLt, dif_pos, Fin.eta]
  by_cases h : (t : ℕ) + τ < T
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, mul_zero]

/-- `e^{imω}`. -/
private noncomputable def expω (ω : ℝ) (m : ℤ) : ℂ :=
  Complex.exp (Complex.I * (m : ℂ) * (ω : ℂ))

private lemma expω_zero (ω : ℝ) : expω ω 0 = 1 := by simp [expω]

/-- `e^{imω} + e^{−imω} = 2cos(mω)`. -/
private lemma expω_add_neg (ω : ℝ) (m : ℤ) :
    expω ω m + expω ω (-m) = ((2 * Real.cos ((m : ℝ) * ω) : ℝ) : ℂ) := by
  have h1 : expω ω m = Complex.exp ((((m : ℝ) * ω : ℝ) : ℂ) * Complex.I) := by
    rw [expω]; congr 1; push_cast; ring
  have h2 : expω ω (-m) = Complex.exp (-(((m : ℝ) * ω : ℝ) : ℂ) * Complex.I) := by
    rw [expω]; congr 1; push_cast; ring
  have h3 : ((2 * Real.cos ((m : ℝ) * ω) : ℝ) : ℂ)
      = 2 * ((Real.cos ((m : ℝ) * ω) : ℝ) : ℂ) := by push_cast; ring
  have hcos : ((Real.cos ((m : ℝ) * ω) : ℝ) : ℂ) = Complex.cos ((((m : ℝ) * ω : ℝ) : ℂ)) :=
    Complex.ofReal_cos _
  rw [h1, h2, h3, hcos, Complex.cos]
  ring

/-- `‖z‖²`, pushed into `ℂ`, is `z · z̄`. -/
private lemma ofReal_norm_sq (z : ℂ) : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- Conjugating a DFT-shaped sum with real coefficients flips the sign of the exponent. -/
private lemma conj_sum_exp {T : ℕ} (r : ℕ → ℂ) (hr : ∀ a, (starRingEnd ℂ) (r a) = r a)
    (ω : ℝ) :
    (starRingEnd ℂ) (∑ a ∈ Finset.range T, r a *
        Complex.exp (-(Complex.I * ((a + 1 : ℕ) : ℂ) * (ω : ℂ))))
      = ∑ a ∈ Finset.range T, r a *
        Complex.exp (Complex.I * ((a + 1 : ℕ) : ℂ) * (ω : ℂ)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, hr, ← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast]
  ring_nf

/-- **Diagonal collection.** For a coefficient sequence supported on `[0, T)`, the strict
upper triangle of the double sum is the lag sum over `τ ∈ [1, T−1]`. -/
private lemma sum_strict_upper {T : ℕ} (c : ℕ → ℂ) (hc : ∀ n, T ≤ n → c n = 0) (F : ℕ → ℂ) :
    ∑ a ∈ Finset.range T, ∑ b ∈ Finset.range T, (if a < b then c a * c b * F (b - a) else 0)
      = ∑ τ ∈ Finset.Icc 1 (T - 1), (∑ a ∈ Finset.range T, c a * c (a + τ)) * F τ := by
  have hIcc : Finset.Icc 1 (T - 1) = Finset.Ico 1 T := by
    ext τ; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hstep : ∀ a ∈ Finset.range T,
      ∑ b ∈ Finset.range T, (if a < b then c a * c b * F (b - a) else 0)
        = ∑ τ ∈ Finset.Icc 1 (T - 1), c a * c (a + τ) * F τ := by
    intro a ha
    simp only [Finset.mem_range] at ha
    rw [← Finset.sum_filter]
    have hfil : {b ∈ Finset.range T | a < b} = Finset.Ico (a + 1) T := by
      ext b; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hfil, hIcc, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hL : ∀ i : ℕ, c a * c (a + 1 + i) * F (a + 1 + i - a) = c a * c (a + (1 + i)) * F (1 + i)
        := by
      intro i
      have h2 : a + 1 + i - a = 1 + i := by omega
      have h1 : a + 1 + i = a + (1 + i) := by omega
      rw [h2, h1]
    rw [Finset.sum_congr rfl fun i _ => hL i]
    have hsub : Finset.range (T - (a + 1)) ⊆ Finset.range (T - 1) := by
      intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    refine Finset.sum_subset hsub ?_
    intro i _ hni
    simp only [Finset.mem_range, not_lt] at hni
    rw [hc (a + (1 + i)) (by omega)]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  exact Finset.sum_congr rfl fun τ _ => (Finset.sum_mul _ _ _).symm

/-- **FY Theorem 2.13** (proof §2.7.5): for a nonzero Fourier frequency, the
periodogram is the discrete Fourier transform of the sample autocovariances:
`I_T(ω_k) = γ̂(0) + Σ_{τ=1}^{T−1} γ̂(τ)·2cos(τω_k)`. (Real form of FY's
`Σ_{|τ|<T} γ̂(τ)e^{−iτω_k}`, using evenness of `γ̂`.) -/
theorem periodogram_eq_sampleACVF {T : ℕ} (hT : 0 < T) (x : Fin T → ℝ) {k : ℤ}
    -- USER-INPUT: k ≢ 0 (mod T) — FY's "k ≠ 0"; Thm 2.13 fails at the zero frequency
    (hk : ¬ ((T : ℤ) ∣ k)) :
    periodogram x k = sampleACVF x 0 +
      ∑ τ ∈ Finset.Icc 1 (T - 1), sampleACVF x τ * (2 * Real.cos (τ * fourierFreq T k)) := by
  have hTR : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hTC : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  set ω := fourierFreq T k with hωdef
  set c : ℕ → ℂ := fun a => ((centered x a : ℝ) : ℂ) with hcdef
  have hc : ∀ n, T ≤ n → c n = 0 := by
    intro n hn
    simp [hcdef, centered_of_le hn]
  -- (1) the constant vector is annihilated: mean-centering inside the DFT is free
  have hzero : ∑ t : Fin T, Complex.exp
      (-(Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ) * (ω : ℂ))) = 0 := by
    have h := sum_exp_fourierFreq_eq_zero (T := T) hT (j := k) (k := 0)
      (by simpa using hk)
    rw [← h]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    have h0 : fourierFreq T (0 : ℤ) = 0 := by simp [fourierFreq]
    rw [h0, hωdef]
    push_cast
    ring
  have hstep : ∀ t : Fin T,
      c (t : ℕ) * Complex.exp (-(Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ) * (ω : ℂ)))
        = (x t : ℂ) * Complex.exp (-(Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ) * (ω : ℂ)))
          - (sampleMean x : ℂ) *
            Complex.exp (-(Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ) * (ω : ℂ))) := by
    intro t
    simp only [hcdef, centered, t.isLt, dif_pos, Fin.eta]
    push_cast
    ring
  have hdftFin : dft x k = ((Real.sqrt T)⁻¹ : ℝ) * ∑ t : Fin T,
      c (t : ℕ) * Complex.exp (-(Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ) * (ω : ℂ))) := by
    rw [dft, ← hωdef]
    congr 1
    rw [Finset.sum_congr rfl fun t _ => hstep t, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hzero, mul_zero, sub_zero]
  have hdft : dft x k = ((Real.sqrt T)⁻¹ : ℝ) * ∑ a ∈ Finset.range T,
      c a * Complex.exp (-(Complex.I * ((a + 1 : ℕ) : ℂ) * (ω : ℂ))) := by
    rw [hdftFin, Fin.sum_univ_eq_sum_range
      (fun a => c a * Complex.exp (-(Complex.I * ((a + 1 : ℕ) : ℂ) * (ω : ℂ)))) T]
  -- (2) `|α_k|²` as the double sum of the centred data
  have hconj : (starRingEnd ℂ) (∑ a ∈ Finset.range T,
        c a * Complex.exp (-(Complex.I * ((a + 1 : ℕ) : ℂ) * (ω : ℂ))))
      = ∑ a ∈ Finset.range T,
        c a * Complex.exp (Complex.I * ((a + 1 : ℕ) : ℂ) * (ω : ℂ)) :=
    conj_sum_exp c (fun a => by simp [hcdef]) ω
  have hnorm : ((‖dft x k‖ : ℝ) : ℂ) ^ 2 = ((T : ℂ))⁻¹ *
      ∑ a ∈ Finset.range T, ∑ b ∈ Finset.range T, c a * c b * expω ω ((b : ℤ) - (a : ℤ)) := by
    rw [ofReal_norm_sq, hdft, map_mul, Complex.conj_ofReal, hconj, mul_mul_mul_comm,
      ← Complex.ofReal_mul, ← pow_two, inv_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (T : ℝ))]
    congr 1
    · push_cast; ring
    · rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have h : Complex.exp (-(Complex.I * ((a + 1 : ℕ) : ℂ) * (ω : ℂ)))
          * Complex.exp (Complex.I * ((b + 1 : ℕ) : ℂ) * (ω : ℂ))
            = expω ω ((b : ℤ) - (a : ℤ)) := by
        rw [← Complex.exp_add, expω]
        congr 1
        push_cast
        ring
      rw [← h]
      ring
  -- (3) group the double sum by the lag `τ = b − a`
  have hdiag : ∀ a b : ℕ, c a * c b * expω ω ((b : ℤ) - (a : ℤ))
      = (if a = b then c a * c a else 0)
        + (if a < b then c a * c b * expω ω ((b : ℤ) - (a : ℤ)) else 0)
        + (if b < a then c a * c b * expω ω ((b : ℤ) - (a : ℤ)) else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [if_neg h.ne, if_pos h, if_neg (by omega)]; ring
    · subst h; rw [if_pos rfl, if_neg (lt_irrefl a)]
      simp [expω_zero]
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]; ring
  have hgroup : ∑ a ∈ Finset.range T, ∑ b ∈ Finset.range T,
        c a * c b * expω ω ((b : ℤ) - (a : ℤ))
      = (∑ a ∈ Finset.range T, c a * c a)
        + ∑ τ ∈ Finset.Icc 1 (T - 1), (∑ a ∈ Finset.range T, c a * c (a + τ)) *
            ((2 * Real.cos ((τ : ℝ) * ω) : ℝ) : ℂ) := by
    have hexpand : ∀ a ∈ Finset.range T, ∑ b ∈ Finset.range T,
          c a * c b * expω ω ((b : ℤ) - (a : ℤ))
        = (∑ b ∈ Finset.range T, if a = b then c a * c a else 0)
          + (∑ b ∈ Finset.range T, if a < b then c a * c b * expω ω ((b : ℤ) - (a : ℤ)) else 0)
          + (∑ b ∈ Finset.range T, if b < a then c a * c b * expω ω ((b : ℤ) - (a : ℤ)) else 0)
          := by
      intro a _
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => hdiag a b
    rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib, Finset.sum_add_distrib]
    -- the diagonal
    have hd : ∑ a ∈ Finset.range T, (∑ b ∈ Finset.range T, if a = b then c a * c a else 0)
        = ∑ a ∈ Finset.range T, c a * c a := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.sum_ite_eq (Finset.range T) a (fun _ => c a * c a), if_pos ha]
    -- the strict upper triangle
    have hu : ∑ a ∈ Finset.range T,
          (∑ b ∈ Finset.range T, if a < b then c a * c b * expω ω ((b : ℤ) - (a : ℤ)) else 0)
        = ∑ τ ∈ Finset.Icc 1 (T - 1), (∑ a ∈ Finset.range T, c a * c (a + τ)) *
            expω ω (τ : ℤ) := by
      rw [← sum_strict_upper c hc (fun τ => expω ω (τ : ℤ))]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases h : a < b
      · rw [if_pos h, if_pos h]
        have hcast : ((b - a : ℕ) : ℤ) = (b : ℤ) - (a : ℤ) := by omega
        rw [hcast]
      · rw [if_neg h, if_neg h]
    -- the strict lower triangle
    have hl : ∑ a ∈ Finset.range T,
          (∑ b ∈ Finset.range T, if b < a then c a * c b * expω ω ((b : ℤ) - (a : ℤ)) else 0)
        = ∑ τ ∈ Finset.Icc 1 (T - 1), (∑ a ∈ Finset.range T, c a * c (a + τ)) *
            expω ω (-(τ : ℤ)) := by
      rw [Finset.sum_comm, ← sum_strict_upper c hc (fun τ => expω ω (-(τ : ℤ)))]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases h : a < b
      · rw [if_pos h, if_pos h]
        have hcast : ((b - a : ℕ) : ℤ) = (b : ℤ) - (a : ℤ) := by omega
        have hneg : -((b : ℤ) - (a : ℤ)) = (a : ℤ) - (b : ℤ) := by ring
        rw [hcast, hneg]
        ring
      · rw [if_neg h, if_neg h]
    rw [hd, hu, hl, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← mul_add, expω_add_neg]
    push_cast
    ring
  -- (4) back to ℝ
  have hA : ((sampleACVF x 0 : ℝ) : ℂ) = ((T : ℂ))⁻¹ * ∑ a ∈ Finset.range T, c a * c a := by
    rw [sampleACVF_eq_centered]
    simp only [hcdef, add_zero]
    push_cast [Complex.ofReal_sum]
    ring
  have hB : ∀ τ : ℕ, ((sampleACVF x τ * (2 * Real.cos ((τ : ℝ) * ω)) : ℝ) : ℂ)
      = ((T : ℂ))⁻¹ * ((∑ a ∈ Finset.range T, c a * c (a + τ)) *
          ((2 * Real.cos ((τ : ℝ) * ω) : ℝ) : ℂ)) := by
    intro τ
    rw [sampleACVF_eq_centered]
    simp only [hcdef]
    push_cast [Complex.ofReal_sum]
    ring
  refine Complex.ofReal_inj.mp ?_
  rw [periodogram, Complex.ofReal_pow, hnorm, hgroup, mul_add, Complex.ofReal_add,
    Complex.ofReal_sum, ← hA, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => (hB τ).symm

/-- At the zero frequency the periodogram is `T · (sample mean)²` (FY §2.7.5 remark). -/
theorem periodogram_zero {T : ℕ} (x : Fin T → ℝ) :
    periodogram x 0 = T * sampleMean x ^ 2 := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp [periodogram, dft]
  have hTR : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hfreq : fourierFreq T 0 = 0 := by simp [fourierFreq]
  have hdft : dft x 0 = (((Real.sqrt T)⁻¹ * ∑ t : Fin T, x t : ℝ) : ℂ) := by
    rw [dft, hfreq]
    push_cast
    simp
  rw [periodogram, hdft, Complex.norm_real, Real.norm_eq_abs, sq_abs, sampleMean, mul_pow,
    mul_pow, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (T : ℝ))]
  field_simp

end StatLean.TimeSeries
