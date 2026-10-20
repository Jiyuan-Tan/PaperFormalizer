module
public import StatLean.TimeSeries.Spectral.Periodogram
public import StatLean.TimeSeries.Spectral.LinearFilter
public import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
public import StatLean.TimeSeries.Models.WhiteNoise

@[expose] public section

/-!
# Periodogram asymptotics (FY §2.4.2, Theorem 2.14)

For a two-sided linear process `X_t = Σ_{j∈ℤ} a_j ε_{t−j}` with iid `(0, σ²)`
innovations and `Σ|a_j| < ∞`, writing `n = [(T−1)/2]` and, for `1 ≤ k ≤ n`,

* `ξ_{2k−1} = (2/T)^{1/2} σ⁻¹ Σ_{t=1}^T ε_t cos(t ω_k)` (`dftNoiseCos`),
* `ξ_{2k} = (2/T)^{1/2} σ⁻¹ Σ_{t=1}^T ε_t sin(t ω_k)` (`dftNoiseSin`):

**Theorem 2.14.**
(i) every fixed finite linear combination `Σ_j c_j ξ_{k_j}` (distinct indices) is
asymptotically `N(0, Σ_j c_j²)` — proved via the exact discrete trigonometric
orthogonality (variance is exactly `Σ c_j²` up to `O(1/T)`) and the double-array
Lindeberg CLT (`TriangularCLT`);
(ii) `I_T(ω_k) = 2π g(ω_k) (ξ_{2k−1}² + ξ_{2k}²)/2 + R_T(ω_k)` with
`max_{1≤k≤n} E|R_T(ω_k)| → 0` — via the DFT-of-filter factorization
`α_k = a(e^{−iω_k}) α_{k,ε} + Y_T(ω_k)` and the uniform L² edge-effect bound
(FY eq. (2.72), Cauchy–Schwarz against the `ℓ¹` tail of `a`).

Consequence recorded in FY's text (not separately stated here): the normalized
ordinates `I_T(ω_k)/(2π g(ω_k))` are asymptotically iid `Exp(1)` — this is (i) + (ii) +
continuous mapping, deferred until a consumer needs it.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.4.2,
Theorem 2.14 (p. 63); proof §2.7.6 (pp. 83–85), citing Serfling (1980) p. 31 for the
double-array CLT. (`FY §2.4.2 Thm 2.14`.)

**Proof formalization notes.**
* The frequencies use `fourierFreq T k = 2πk/T` and the time index `t = 1, …, T` as in
  `Spectral/DFT.lean` (whose exponential-orthogonality lemmas drive the exact variance
  computation in (i)).
* In (ii) the remainder bound is uniform over `k ≤ n`: stated with an explicit
  vanishing envelope sequence `b : ℕ → ℝ` rather than a `Finset.sup`, avoiding junk
  when the frequency window is empty (`T ≤ 2`).
* The spectral density `g` is `spectralDensityOf X μ` at the circle point
  `(fourierFreq T k : AddCircle (2π))`; summability of the ACVF (needed for `g` to be
  the honest density) is derived from `Σ|a_j| < ∞` via the filter theory
  (`IsFilteredBy.hasSummableACVF` with white-noise input).

**Bibliographic comments.** Theorem 2.14 descends from Brockwell & Davis (1991),
Prop 10.3.1–Thm 10.3.2; the χ²₂-limit picture of periodogram ordinates goes back to
Fisher (1929) and Bartlett (1950).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The normalized **cosine noise sum** `ξ_{2k−1}` (FY §2.7.6):
`(2/T)^{1/2} σ⁻¹ Σ_{t=1}^T ε_t cos(t ω_k)`; junk when `σ² ≤ 0` or `T = 0`. -/
noncomputable def dftNoiseCos (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (T : ℕ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (2 / T) / Real.sqrt σ2 *
    ∑ t ∈ Finset.range T, ε ((t : ℤ) + 1) ω * Real.cos (((t : ℝ) + 1) * fourierFreq T k)

/-- The normalized **sine noise sum** `ξ_{2k}` (FY §2.7.6). -/
noncomputable def dftNoiseSin (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (T : ℕ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (2 / T) / Real.sqrt σ2 *
    ∑ t ∈ Finset.range T, ε ((t : ℤ) + 1) ω * Real.sin (((t : ℝ) + 1) * fourierFreq T k)

/-- The interleaved family: `ξ-index 2k−1 ↦ cos` at frequency `k`, `2k ↦ sin` at
frequency `k` (FY's numbering; `j ≥ 1`). -/
noncomputable def dftNoiseXi (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (T : ℕ) (j : ℕ) : Ω → ℝ :=
  if j % 2 = 1 then dftNoiseCos ε σ2 T ((j + 1) / 2) else dftNoiseSin ε σ2 T (j / 2)

/-! ### Discrete trigonometric orthogonality (FY §2.4.1)

The exact variance computation behind Theorem 2.14(i) is the classical orthogonality of
the Fourier trigonometric vectors on the grid `t = 1, …, T`. Everything is derived from
`Spectral/DFT.lean`'s exponential orthogonality by taking real and imaginary parts and
by the product-to-sum identities.
-/

/-- `e^{ir} = cos r + i sin r` in the shape used below. -/
private lemma exp_I_ofReal (r : ℝ) :
    Complex.exp (Complex.I * (r : ℂ))
      = (Real.cos r : ℂ) + (Real.sin r : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The full-period exponential sum at a Fourier frequency: `Σ_{t=1}^T e^{i t ω_m}` is
`T` when `T ∣ m` and `0` otherwise. -/
private lemma sum_exp_fourierFreq_eq {T : ℕ} (hT : 0 < T) (m : ℤ) :
    ∑ t ∈ Finset.range T,
        Complex.exp (Complex.I * ((((t : ℝ) + 1) * fourierFreq T m : ℝ) : ℂ))
      = if (T : ℤ) ∣ m then (T : ℂ) else 0 := by
  by_cases hdvd : (T : ℤ) ∣ m
  · rw [if_pos hdvd]
    obtain ⟨q, rfl⟩ := hdvd
    have hTR : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
    have hfr : fourierFreq T ((T : ℤ) * q) = 2 * π * (q : ℝ) := by
      unfold fourierFreq; push_cast; field_simp
    have hterm : ∀ t ∈ Finset.range T,
        Complex.exp (Complex.I * ((((t : ℝ) + 1) * fourierFreq T ((T : ℤ) * q) : ℝ) : ℂ))
          = 1 := by
      intro t _
      rw [hfr]
      have : Complex.I * (((((t : ℝ) + 1) * (2 * π * (q : ℝ))) : ℝ) : ℂ)
          = (((((t : ℕ) : ℤ) + 1) * q : ℤ) : ℂ) * (2 * π * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [Finset.sum_congr rfl hterm]
    simp
  · rw [if_neg hdvd]
    have hfr0 : fourierFreq T (0 : ℤ) = 0 := by unfold fourierFreq; simp
    have hkey := sum_exp_fourierFreq_eq_zero hT (j := (0 : ℤ)) (k := m) (by simpa using hdvd)
    rw [← Fin.sum_univ_eq_sum_range
      (fun t : ℕ => Complex.exp (Complex.I * ((((t : ℝ) + 1) * fourierFreq T m : ℝ) : ℂ))) T]
    rw [← hkey]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hfr0]
    congr 1
    push_cast
    ring

/-- The full-period cosine sum: `T` on the diagonal `T ∣ m`, `0` off it. -/
private lemma sum_cos_fourierFreq {T : ℕ} (hT : 0 < T) (m : ℤ) :
    ∑ t ∈ Finset.range T, Real.cos (((t : ℝ) + 1) * fourierFreq T m)
      = if (T : ℤ) ∣ m then (T : ℝ) else 0 := by
  have h := congrArg Complex.re (sum_exp_fourierFreq_eq hT m)
  rw [Complex.re_sum] at h
  simp only [exp_I_ofReal, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero] at h
  rw [h]
  by_cases hdvd : (T : ℤ) ∣ m <;> simp [hdvd]

/-- The full-period sine sum always vanishes. -/
private lemma sum_sin_fourierFreq {T : ℕ} (hT : 0 < T) (m : ℤ) :
    ∑ t ∈ Finset.range T, Real.sin (((t : ℝ) + 1) * fourierFreq T m) = 0 := by
  have h := congrArg Complex.im (sum_exp_fourierFreq_eq hT m)
  rw [Complex.im_sum] at h
  simp only [exp_I_ofReal, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_add, add_zero] at h
  rw [h]
  by_cases hdvd : (T : ℤ) ∣ m <;> simp [hdvd]

section Orthogonality

variable {T k l : ℕ}

/-- Additivity of the Fourier frequency in the index. -/
private lemma fourierFreq_sub_mul (T : ℕ) (k l : ℕ) (t : ℕ) :
    ((t : ℝ) + 1) * fourierFreq T (k : ℤ) - ((t : ℝ) + 1) * fourierFreq T (l : ℤ)
      = ((t : ℝ) + 1) * fourierFreq T ((k : ℤ) - (l : ℤ)) := by
  unfold fourierFreq; push_cast; ring

private lemma fourierFreq_add_mul (T : ℕ) (k l : ℕ) (t : ℕ) :
    ((t : ℝ) + 1) * fourierFreq T (k : ℤ) + ((t : ℝ) + 1) * fourierFreq T (l : ℤ)
      = ((t : ℝ) + 1) * fourierFreq T ((k : ℤ) + (l : ℤ)) := by
  unfold fourierFreq; push_cast; ring

/-- On the window `1 ≤ k, l` and `k + l < T`, the sum frequency is never a multiple of
`T`. -/
private lemma not_dvd_add (hk : 1 ≤ k) (hkl : k + l < T) :
    ¬ ((T : ℤ) ∣ ((k : ℤ) + (l : ℤ))) := by
  intro hdvd
  have hpos : (0 : ℤ) < (k : ℤ) + (l : ℤ) := by
    have : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    have : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg _
    omega
  have hle := Int.le_of_dvd hpos hdvd
  have : ((k : ℤ) + (l : ℤ)) < (T : ℤ) := by exact_mod_cast hkl
  omega

/-- On the same window, the difference frequency is a multiple of `T` exactly on the
diagonal. -/
private lemma dvd_sub_iff (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k + l < T) :
    ((T : ℤ) ∣ ((k : ℤ) - (l : ℤ))) ↔ k = l := by
  constructor
  · intro hdvd
    have hkT : (k : ℤ) < (T : ℤ) := by
      have : k < T := by omega
      exact_mod_cast this
    have hlT : (l : ℤ) < (T : ℤ) := by
      have : l < T := by omega
      exact_mod_cast this
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
    have hl0 : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg _
    have habs : |(k : ℤ) - (l : ℤ)| < (T : ℤ) := by rw [abs_lt]; omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    have : (k : ℤ) = (l : ℤ) := by omega
    exact_mod_cast this
  · rintro rfl; simp

/-- **Cosine–cosine orthogonality**: `Σ_{t=1}^T cos(tω_k) cos(tω_l) = (T/2) δ_{kl}`. -/
private lemma sum_cos_mul_cos (hT : 0 < T) (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k + l < T) :
    ∑ t ∈ Finset.range T,
        Real.cos (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
          * Real.cos (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
      = if k = l then (T : ℝ) / 2 else 0 := by
  have hterm : ∀ t : ℕ,
      Real.cos (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
        * Real.cos (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
        = (Real.cos (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) - (l : ℤ)))
            + Real.cos (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) + (l : ℤ)))) / 2 := by
    intro t
    rw [← fourierFreq_sub_mul T k l t, ← fourierFreq_add_mul T k l t, Real.cos_sub,
      Real.cos_add]
    ring
  rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.sum_div, Finset.sum_add_distrib,
    sum_cos_fourierFreq hT, sum_cos_fourierFreq hT, if_neg (not_dvd_add hk hkl)]
  by_cases hd : k = l
  · rw [if_pos hd, if_pos ((dvd_sub_iff hk hl hkl).2 hd)]; ring
  · rw [if_neg hd, if_neg (fun h => hd ((dvd_sub_iff hk hl hkl).1 h))]; ring

/-- **Sine–sine orthogonality**: `Σ_{t=1}^T sin(tω_k) sin(tω_l) = (T/2) δ_{kl}`. -/
private lemma sum_sin_mul_sin (hT : 0 < T) (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k + l < T) :
    ∑ t ∈ Finset.range T,
        Real.sin (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
          * Real.sin (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
      = if k = l then (T : ℝ) / 2 else 0 := by
  have hterm : ∀ t : ℕ,
      Real.sin (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
        * Real.sin (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
        = (Real.cos (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) - (l : ℤ)))
            - Real.cos (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) + (l : ℤ)))) / 2 := by
    intro t
    rw [← fourierFreq_sub_mul T k l t, ← fourierFreq_add_mul T k l t, Real.cos_sub,
      Real.cos_add]
    ring
  rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.sum_div, Finset.sum_sub_distrib,
    sum_cos_fourierFreq hT, sum_cos_fourierFreq hT, if_neg (not_dvd_add hk hkl)]
  by_cases hd : k = l
  · rw [if_pos hd, if_pos ((dvd_sub_iff hk hl hkl).2 hd)]; ring
  · rw [if_neg hd, if_neg (fun h => hd ((dvd_sub_iff hk hl hkl).1 h))]; ring

/-- **Cosine–sine orthogonality**: the mixed sums vanish identically on the window. -/
private lemma sum_cos_mul_sin (hT : 0 < T) :
    ∑ t ∈ Finset.range T,
        Real.cos (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
          * Real.sin (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
      = 0 := by
  have hterm : ∀ t : ℕ,
      Real.cos (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
        * Real.sin (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
        = (Real.sin (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) + (l : ℤ)))
            - Real.sin (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) - (l : ℤ)))) / 2 := by
    intro t
    rw [← fourierFreq_sub_mul T k l t, ← fourierFreq_add_mul T k l t, Real.sin_sub,
      Real.sin_add]
    ring
  rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.sum_div, Finset.sum_sub_distrib,
    sum_sin_fourierFreq hT, sum_sin_fourierFreq hT]
  ring

end Orthogonality

/-! ### The `ξ`-family as a weighted sum of the innovations -/

/-- The frequency index carried by the `ξ`-index `j` (`2k−1 ↦ k`, `2k ↦ k`). -/
private def xiFreq (j : ℕ) : ℕ := if j % 2 = 1 then (j + 1) / 2 else j / 2

/-- The trigonometric factor carried by the `ξ`-index `j` at time `t + 1`. -/
private noncomputable def xiTrig (T j t : ℕ) : ℝ :=
  if j % 2 = 1 then Real.cos (((t : ℝ) + 1) * fourierFreq T (xiFreq j : ℤ))
  else Real.sin (((t : ℝ) + 1) * fourierFreq T (xiFreq j : ℤ))

private lemma abs_xiTrig_le_one (T j t : ℕ) : |xiTrig T j t| ≤ 1 := by
  unfold xiTrig
  split_ifs
  · exact Real.abs_cos_le_one _
  · exact Real.abs_sin_le_one _

private lemma one_le_xiFreq {j : ℕ} (hj : 1 ≤ j) : 1 ≤ xiFreq j := by
  unfold xiFreq
  split_ifs with h <;> omega

/-- `ξ`-indices with the same parity and the same frequency coincide. -/
private lemma xiFreq_inj {j j' : ℕ} (hpar : j % 2 = j' % 2) (h : xiFreq j = xiFreq j') :
    j = j' := by
  unfold xiFreq at h
  by_cases hj : j % 2 = 1
  · rw [if_pos hj, if_pos (by omega)] at h; omega
  · rw [if_neg hj, if_neg (by omega)] at h; omega

/-- **The `ξ`-trigonometric Gram matrix** on the window `κ i ≥ 1`, frequencies inside
`[1, (T−1)/2]`: orthogonal with squared norm `T/2`. -/
private lemma sum_xiTrig_mul {T j j' : ℕ} (hT : 0 < T) (hj : 1 ≤ j) (hj' : 1 ≤ j')
    (hw : xiFreq j + xiFreq j' < T) :
    ∑ t ∈ Finset.range T, xiTrig T j t * xiTrig T j' t
      = if j = j' then (T : ℝ) / 2 else 0 := by
  have hf : 1 ≤ xiFreq j := one_le_xiFreq hj
  have hf' : 1 ≤ xiFreq j' := one_le_xiFreq hj'
  unfold xiTrig
  by_cases hp : j % 2 = 1 <;> by_cases hp' : j' % 2 = 1
  · simp only [if_pos hp, if_pos hp']
    rw [sum_cos_mul_cos hT hf hf' hw]
    by_cases hd : xiFreq j = xiFreq j'
    · rw [if_pos hd, if_pos (xiFreq_inj (by omega) hd)]
    · rw [if_neg hd, if_neg (fun h => hd (by rw [h]))]
  · simp only [if_pos hp, if_neg hp']
    rw [sum_cos_mul_sin hT, if_neg (by omega)]
  · simp only [if_neg hp, if_pos hp']
    rw [if_neg (show ¬ j = j' by omega),
      ← sum_cos_mul_sin (T := T) (k := xiFreq j') (l := xiFreq j) hT]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  · simp only [if_neg hp, if_neg hp']
    rw [sum_sin_mul_sin hT hf hf' hw]
    by_cases hd : xiFreq j = xiFreq j'
    · rw [if_pos hd, if_pos (xiFreq_inj (by omega) hd)]
    · rw [if_neg hd, if_neg (fun h => hd (by rw [h]))]

omit [MeasurableSpace Ω] in
/-- The `ξ`-coordinate is the weighted innovation sum `Σ_{t<T} (A_T · trig) ε_{t+1}`. -/
private lemma dftNoiseXi_eq_sum (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (T j : ℕ) (ω : Ω) :
    dftNoiseXi ε σ2 T j ω
      = ∑ t ∈ Finset.range T,
          (Real.sqrt (2 / T) / Real.sqrt σ2 * xiTrig T j t) * ε ((t : ℤ) + 1) ω := by
  unfold dftNoiseXi xiTrig xiFreq
  by_cases h : j % 2 = 1
  · simp only [if_pos h]
    unfold dftNoiseCos
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  · simp only [if_neg h]
    unfold dftNoiseSin
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring

/-- The weight of the innovation `ε_{t+1}` in the linear combination `Σ_i c_i ξ_{κ i}`. -/
private noncomputable def xiCombWeight {m : ℕ} (c : Fin m → ℝ) (κ : Fin m → ℕ) (σ2 : ℝ)
    (T t : ℕ) : ℝ :=
  ∑ i, c i * (Real.sqrt (2 / T) / Real.sqrt σ2 * xiTrig T (κ i) t)

omit [MeasurableSpace Ω] in
private lemma sum_c_dftNoiseXi_eq {m : ℕ} (c : Fin m → ℝ) (κ : Fin m → ℕ) (ε : ℤ → Ω → ℝ)
    (σ2 : ℝ) (T : ℕ) (ω : Ω) :
    ∑ i, c i * dftNoiseXi ε σ2 T (κ i) ω
      = ∑ t ∈ Finset.range T, xiCombWeight c κ σ2 T t * ε ((t : ℤ) + 1) ω := by
  simp only [dftNoiseXi_eq_sum, Finset.mul_sum, xiCombWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by ring

omit [MeasurableSpace Ω] in
/-- **Exact row variance** (FY §2.7.6): on the window where every `ξ`-frequency involved
fits in `[1, (T−1)/2]`, the innovation-weight energy is exactly `σ⁻² Σ c²`, so the row
variances of the array equal `Σ c²` — no error term at all. -/
private lemma sum_xiCombWeight_sq {m : ℕ} (c : Fin m → ℝ) (κ : Fin m → ℕ) {σ2 : ℝ}
    (hσ : 0 < σ2) (hinj : Function.Injective κ) (h1 : ∀ i, 1 ≤ κ i)
    {T : ℕ} (hT : 0 < T) (hwin : ∀ i j, xiFreq (κ i) + xiFreq (κ j) < T) :
    σ2 * ∑ t ∈ Finset.range T, (xiCombWeight c κ σ2 T t) ^ 2 = ∑ i, c i ^ 2 := by
  have hTR : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have h2T : (0 : ℝ) ≤ 2 / (T : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg T)
  have hA2 : (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2 = 2 / ((T : ℝ) * σ2) := by
    rw [div_pow, Real.sq_sqrt h2T, Real.sq_sqrt hσ.le, div_div]
  -- Expand the square of the weight into the trigonometric Gram matrix.
  have hexp : ∀ t : ℕ, (xiCombWeight c κ σ2 T t) ^ 2
      = ∑ i, ∑ j, (c i * c j * (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2)
          * (xiTrig T (κ i) t * xiTrig T (κ j) t) := by
    intro t
    rw [xiCombWeight, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun t _ => hexp t]
  -- Swap the time sum inside.
  have hswap : ∑ t ∈ Finset.range T, ∑ i, ∑ j,
        (c i * c j * (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2)
          * (xiTrig T (κ i) t * xiTrig T (κ j) t)
      = ∑ i, ∑ j, (c i * c j * (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2)
          * ∑ t ∈ Finset.range T, xiTrig T (κ i) t * xiTrig T (κ j) t := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  rw [hswap]
  -- Orthogonality collapses the double sum to the diagonal.
  have hdiag : ∀ i j : Fin m, (∑ t ∈ Finset.range T, xiTrig T (κ i) t * xiTrig T (κ j) t)
      = if j = i then (T : ℝ) / 2 else 0 := by
    intro i j
    rw [sum_xiTrig_mul hT (h1 i) (h1 j) (hwin i j)]
    by_cases h : j = i
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun hc => h (hinj hc).symm)]
  have hrow : ∀ i : Fin m, (∑ j, (c i * c j * (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2)
        * ∑ t ∈ Finset.range T, xiTrig T (κ i) t * xiTrig T (κ j) t)
      = (c i * c i * (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2) * ((T : ℝ) / 2) := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [hdiag i i, if_pos rfl]
    · intro j _ hj; rw [hdiag i j, if_neg hj, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA2]
  field_simp

omit [MeasurableSpace Ω] in
/-- The innovation weights are uniformly `O(T^{-1/2})`: this is the negligibility feeding
the Lindeberg condition. -/
private lemma xiCombWeight_sq_le {m : ℕ} (c : Fin m → ℝ) (κ : Fin m → ℕ) {σ2 : ℝ}
    (hσ : 0 < σ2) (T t : ℕ) :
    (xiCombWeight c κ σ2 T t) ^ 2 ≤ 2 / ((T : ℝ) * σ2) * (∑ i, |c i|) ^ 2 := by
  have h2T : (0 : ℝ) ≤ 2 / (T : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg T)
  have hA : (0 : ℝ) ≤ Real.sqrt (2 / T) / Real.sqrt σ2 := by positivity
  have hA2 : (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2 = 2 / ((T : ℝ) * σ2) := by
    rw [div_pow, Real.sq_sqrt h2T, Real.sq_sqrt hσ.le, div_div]
  have habs : |xiCombWeight c κ σ2 T t|
      ≤ (Real.sqrt (2 / T) / Real.sqrt σ2) * ∑ i, |c i| := by
    rw [xiCombWeight, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg hA]
    have h1 := abs_xiTrig_le_one T (κ i) t
    have h2 : (0 : ℝ) ≤ |c i| * (Real.sqrt (2 / T) / Real.sqrt σ2) :=
      mul_nonneg (abs_nonneg _) hA
    nlinarith [mul_nonneg h2 (sub_nonneg.2 h1)]
  calc (xiCombWeight c κ σ2 T t) ^ 2 = |xiCombWeight c κ σ2 T t| ^ 2 := (sq_abs _).symm
    _ ≤ ((Real.sqrt (2 / T) / Real.sqrt σ2) * ∑ i, |c i|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = 2 / ((T : ℝ) * σ2) * (∑ i, |c i|) ^ 2 := by rw [mul_pow, hA2]

/-! ### Weighted sums of an i.i.d. sequence

The `ξ`-combination is a triangular array of *weighted* copies of one i.i.d. sequence; the
Lindeberg condition then only needs (a) the weights to be individually negligible and
(b) the common law to be square-integrable (the truncated second moment `∫_{K ≤ |Y|} Y²`
vanishes as `K → ∞` by dominated convergence). -/

/-- **CLT for weighted sums of an i.i.d. sequence** (charFun form). The rows are
`X_{n,i} = w_{n,i} Y_i`; the row-variance limit `v` and the individual negligibility of
the weights are the only inputs beyond the sampling law. -/
private lemma tendsto_charFun_weighted_iid [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {kk : ℕ → ℕ} {w : (n : ℕ) → Fin (kk n) → ℝ} {σ2 v : ℝ}
    (hmeasY : ∀ i, Measurable (Y i))
    (hindepY : iIndepFun Y μ)
    (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hL2Y : MemLp (Y 0) 2 μ)
    (hmeanY : ∫ ω, Y 0 ω ∂μ = 0)
    (hvarY : variance (Y 0) μ = σ2) (hσ2 : 0 < σ2)
    (hS : Tendsto (fun n => σ2 * ∑ i, (w n i) ^ 2) atTop (𝓝 v))
    (hneg : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, ∀ i, (w n i) ^ 2 ≤ c)
    (u : ℝ) :
    Tendsto (fun n => charFun (μ.map fun ω => ∑ i, w n i * Y (i : ℕ) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal v)) u)) := by
  obtain ⟨X, hXdef⟩ : ∃ X : (n : ℕ) → Fin (kk n) → Ω → ℝ,
      X = fun n i ω => w n i * Y (i : ℕ) ω := ⟨_, rfl⟩
  -- Row regularity.
  have hmeas' : ∀ n i, Measurable (X n i) := by
    intro n i; simp only [hXdef]; exact (hmeasY ↑i).const_mul _
  have hL2' : ∀ n i, MemLp (X n i) 2 μ := by
    intro n i; simp only [hXdef]; exact ((hidentY ↑i).symm.memLp_snd hL2Y).const_mul _
  have hmean' : ∀ n i, ∫ ω, X n i ω ∂μ = 0 := by
    intro n i; simp only [hXdef]
    rw [integral_const_mul, ((hidentY ↑i).integral_eq).trans hmeanY, mul_zero]
  have hindep' : ∀ n, iIndepFun (X n) μ := by
    intro n
    have h1 : iIndepFun (fun i : Fin (kk n) => Y (↑i : ℕ)) μ :=
      iIndepFun.precomp Fin.val_injective hindepY
    have h2 := h1.comp (fun i : Fin (kk n) => fun y : ℝ => w n i * y)
      (fun i => measurable_id.const_mul _)
    refine (iIndepFun_congr (fun i => ?_)).2 h2
    filter_upwards with ω; simp only [hXdef, Function.comp]
  -- Row variances.
  have hvar' : Tendsto (fun n => ∑ i, variance (X n i) μ) atTop (𝓝 v) := by
    have hVi : ∀ n i, variance (X n i) μ = (w n i) ^ 2 * σ2 := by
      intro n i; simp only [hXdef]
      rw [variance_const_mul, (hidentY ↑i).variance_eq, hvarY]
    have hcongr : (fun n => ∑ i, variance (X n i) μ)
        = fun n => σ2 * ∑ i, (w n i) ^ 2 := by
      funext n; simp_rw [hVi]; rw [← Finset.sum_mul]; ring
    rw [hcongr]; exact hS
  -- The `L²`-tail of the sampling law vanishes.
  have hsq0 : Integrable (fun ω => (Y 0 ω) ^ 2) μ := hL2Y.integrable_sq
  obtain ⟨tail, htaildef⟩ : ∃ tail : ℕ → ℝ,
      tail = fun (K : ℕ) => ∫ ω in {ω | (K : ℝ) ≤ |Y 0 ω|}, (Y 0 ω) ^ 2 ∂μ := ⟨_, rfl⟩
  have hsmK : ∀ (j K : ℕ), MeasurableSet {ω | (K : ℝ) ≤ |Y j ω|} := fun j K =>
    measurableSet_le measurable_const (hmeasY j).abs
  have htail0 : Tendsto tail atTop (𝓝 0) := by
    simp only [htaildef]
    have hanti : Antitone fun K : ℕ => {ω | (K : ℝ) ≤ |Y 0 ω|} := by
      intro a b hab ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      exact le_trans (by exact_mod_cast hab) hω
    have hint : ∃ K : ℕ, IntegrableOn (fun ω => (Y 0 ω) ^ 2) {ω | (K : ℝ) ≤ |Y 0 ω|} μ :=
      ⟨0, hsq0.integrableOn⟩
    have hlim := tendsto_setIntegral_of_antitone (fun K => hsmK 0 K) hanti hint
    have hempty : ⋂ K : ℕ, {ω | (K : ℝ) ≤ |Y 0 ω|} = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_le]
      obtain ⟨K, hK⟩ := exists_nat_gt |Y 0 ω|
      exact ⟨K, hK⟩
    rw [hempty] at hlim
    simpa using hlim
  -- Identically-distributed coordinates share the same tail integral.
  have htaileq : ∀ (i K : ℕ),
      ∫ ω in {ω | (K : ℝ) ≤ |Y i ω|}, (Y i ω) ^ 2 ∂μ = tail K := by
    intro i K
    have hg : Measurable fun y : ℝ => if (K : ℝ) ≤ |y| then y ^ 2 else 0 :=
      Measurable.ite (measurableSet_le measurable_const measurable_id.abs)
        (measurable_id.pow_const 2) measurable_const
    have hcomp : ∀ j : ℕ, ∫ ω, (if (K : ℝ) ≤ |Y j ω| then (Y j ω) ^ 2 else 0) ∂μ
        = ∫ ω in {ω | (K : ℝ) ≤ |Y j ω|}, (Y j ω) ^ 2 ∂μ := by
      intro j
      rw [← integral_indicator (hsmK j K)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases h : (K : ℝ) ≤ |Y j ω| <;> simp [Set.indicator, h]
    simp only [htaildef]
    rw [← hcomp i, ← hcomp 0]
    simpa [Function.comp] using ((hidentY i).comp hg).integral_eq
  -- Bounded row weight energy (from the convergent row variances).
  have henergy : ∀ᶠ n in atTop, ∑ i, (w n i) ^ 2 ≤ (|v| + 1) / σ2 := by
    filter_upwards [hS.eventually_le_const (show v < |v| + 1 by
      have := le_abs_self v; linarith)] with n hn
    rw [le_div_iff₀ hσ2, mul_comm]
    exact hn
  -- Lindeberg's condition for the (closed-set) triangular array.
  have hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    intro ε hε
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · refine Eventually.of_forall fun n => hb.trans_le (Finset.sum_nonneg fun i _ => ?_)
      exact setIntegral_nonneg (measurableSet_le measurable_const (hmeas' n i).abs)
        fun ω _ => sq_nonneg _
    · -- Pick a truncation level `K` making the shared tail small, then use negligibility.
      have hEpos : (0 : ℝ) < (|v| + 1) / σ2 + 1 := by
        have : (0 : ℝ) ≤ (|v| + 1) / σ2 := by positivity
        linarith
      obtain ⟨K, hKtail, hK1⟩ :=
        (((tendsto_order.1 htail0).2 (b / ((|v| + 1) / σ2 + 1))
          (div_pos hb hEpos)).and (eventually_ge_atTop 1)).exists
      have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
      filter_upwards [hneg ((ε / K) ^ 2) (by positivity), henergy] with n hn hnE
      have haik : ∀ i, |w n i| ≤ ε / K := by
        intro i
        calc |w n i| = Real.sqrt ((w n i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt ((ε / K) ^ 2) := Real.sqrt_le_sqrt (hn i)
          _ = ε / K := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      have hterm : ∀ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ
          ≤ (w n i) ^ 2 * tail K := by
        intro i
        have hXsq : ∀ ω, (X n i ω) ^ 2 = (w n i) ^ 2 * (Y (↑i : ℕ) ω) ^ 2 := by
          intro ω; simp only [hXdef]; rw [mul_pow]
        rw [setIntegral_congr_fun (measurableSet_le measurable_const (hmeas' n i).abs)
              (fun ω _ => hXsq ω), integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [← htaileq (↑i) K]
        refine setIntegral_mono_set
          (((hidentY ↑i).symm.memLp_snd hL2Y).integrable_sq).integrableOn
          (Eventually.of_forall fun ω => sq_nonneg _) (Eventually.of_forall fun ω hω => ?_)
        have h1 : ε ≤ |w n i| * |Y (↑i : ℕ) ω| := by
          rw [← abs_mul]; simpa only [hXdef] using! hω
        have h3 : ε ≤ (ε / K) * |Y (↑i : ℕ) ω| :=
          le_trans h1 (mul_le_mul_of_nonneg_right (haik i) (abs_nonneg _))
        change (K : ℝ) ≤ |Y (↑i : ℕ) ω|
        by_contra hcon
        have hle : (ε / K) * |Y (↑i : ℕ) ω| < (ε / K) * K :=
          mul_lt_mul_of_pos_left (not_le.1 hcon) (by positivity)
        rw [div_mul_cancel₀ ε (ne_of_gt hKpos)] at hle
        exact absurd (lt_of_le_of_lt h3 hle) (lt_irrefl ε)
      have htailnn : 0 ≤ tail K := by
        rw [htaildef]; exact setIntegral_nonneg (hsmK 0 K) fun ω _ => sq_nonneg _
      calc ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ
          ≤ ∑ i, (w n i) ^ 2 * tail K := Finset.sum_le_sum fun i _ => hterm i
        _ = (∑ i, (w n i) ^ 2) * tail K := by rw [← Finset.sum_mul]
        _ ≤ ((|v| + 1) / σ2 + 1) * tail K := by
            refine mul_le_mul_of_nonneg_right (by linarith) htailnn
        _ < b := by
            have := (mul_lt_mul_of_pos_left hKtail hEpos)
            rwa [mul_div_cancel₀ b (ne_of_gt hEpos)] at this
  have hmain :=
    tendsto_charFun_rowSum_gaussian_of_lindeberg hmeas' hindep' hmean' hL2' hvar' hlin u
  simpa only [hXdef] using hmain

/-- **FY Theorem 2.14(i)**: any fixed finite linear combination of distinct
`ξ`-coordinates is asymptotically `N(0, Σ c²)` (charFun form). The index selection
`κsel` picks `m` distinct `ξ`-indices; the indices are fixed while `T → ∞`. -/
theorem dftNoiseXi_clt [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: iid(0, σ²) innovations; FY Thm 2.14
    (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    {m : ℕ} (c : Fin m → ℝ)
    -- USER-INPUT: distinct ξ-indices, all ≥ 1; FY Thm 2.14(i)
    (κsel : Fin m → ℕ) (hinj : Function.Injective κsel) (h1 : ∀ i, 1 ≤ κsel i)
    (u : ℝ) :
    Tendsto (fun T : ℕ =>
        charFun (μ.map fun ω => ∑ i, c i * dftNoiseXi ε σ2 T (κsel i) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (∑ i, c i ^ 2))) u)) := by
  -- The innovations, reindexed by `ℕ` as `Y j = ε_{j+1}`.
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ → Ω → ℝ, Y = fun j : ℕ => ε ((j : ℤ) + 1) := ⟨_, rfl⟩
  have hYi : ∀ j : ℕ, Y j = ε ((j : ℤ) + 1) := fun j => by rw [hYdef]
  have hY0 : Y 0 = ε 1 := by rw [hYdef]; norm_num
  have hmeasY : ∀ j, Measurable (Y j) := fun j => by rw [hYi j]; exact hε.measurable _
  have hindepY : iIndepFun Y μ := by
    rw [hYdef]
    exact iIndepFun.precomp (g := fun j : ℕ => (j : ℤ) + 1)
      (fun a b hab => by exact_mod_cast (add_left_injective (1 : ℤ) hab)) hε.iIndep
  have hidentY : ∀ j, IdentDistrib (Y j) (Y 0) μ μ := by
    intro j; rw [hYi j, hY0]; exact hε.identDistrib _ 1
  have hL2Y : MemLp (Y 0) 2 μ := by
    rw [hY0]; exact (hε.identDistrib 0 1).memLp_snd hε.memLp
  have hmeanY : ∫ ω, Y 0 ω ∂μ = 0 := by
    rw [hY0]; exact ((hε.identDistrib 1 0).integral_eq).trans hε.integral_eq_zero
  have hvarY : variance (Y 0) μ = σ2 := by
    rw [hY0]; exact ((hε.identDistrib 1 0).variance_eq).trans hε.variance_eq
  -- A uniform bound on the `ξ`-frequencies involved (they are fixed while `T → ∞`).
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i, xiFreq (κsel i) ≤ M :=
    ⟨Finset.univ.sup fun i => xiFreq (κsel i),
      fun i => Finset.le_sup (f := fun i => xiFreq (κsel i)) (Finset.mem_univ i)⟩
  -- Row variances: exactly `Σ c²` once the frequency window fits.
  have hS : Tendsto
      (fun T : ℕ => σ2 * ∑ t : Fin T, (xiCombWeight c κsel σ2 T (t : ℕ)) ^ 2) atTop
      (𝓝 (∑ i, c i ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (2 * M)] with T hT'
    have hT : 0 < T := by omega
    have hwin : ∀ i j, xiFreq (κsel i) + xiFreq (κsel j) < T := by
      intro i j; have := hM i; have := hM j; omega
    rw [Fin.sum_univ_eq_sum_range
      (fun t : ℕ => (xiCombWeight c κsel σ2 T t) ^ 2) T]
    exact (sum_xiCombWeight_sq c κsel hσ hinj h1 hT hwin).symm
  -- Weight negligibility: the weights are uniformly `O(T^{-1/2})`.
  have hneg : ∀ cc : ℝ, 0 < cc → ∀ᶠ T in atTop,
      ∀ t : Fin T, (xiCombWeight c κsel σ2 T (t : ℕ)) ^ 2 ≤ cc := by
    intro cc hcc
    have heq : ∀ T : ℕ, 2 / ((T : ℝ) * σ2) * (∑ i, |c i|) ^ 2
        = (2 * (∑ i, |c i|) ^ 2 / σ2) * ((T : ℝ))⁻¹ := by
      intro T
      rcases eq_or_ne ((T : ℝ)) 0 with h | h
      · rw [h]; simp
      · field_simp
    have hinvT : Tendsto (fun T : ℕ => ((T : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hlim : Tendsto (fun T : ℕ => 2 / ((T : ℝ) * σ2) * (∑ i, |c i|) ^ 2) atTop (𝓝 0) := by
      simp only [heq]
      simpa using hinvT.const_mul (2 * (∑ i, |c i|) ^ 2 / σ2)
    filter_upwards [hlim.eventually_le_const hcc] with T hT1 t
    exact le_trans (xiCombWeight_sq_le c κsel hσ T (t : ℕ)) hT1
  have key := tendsto_charFun_weighted_iid (μ := μ) (Y := Y) (kk := fun T : ℕ => T)
    (w := fun T (t : Fin T) => xiCombWeight c κsel σ2 T (t : ℕ)) (σ2 := σ2)
    (v := ∑ i, c i ^ 2) hmeasY hindepY hidentY hL2Y hmeanY hvarY hσ hS hneg u
  refine Tendsto.congr (fun T => ?_) key
  congr 1
  refine congrArg (fun f : Ω → ℝ => μ.map f) ?_
  funext ω
  rw [sum_c_dftNoiseXi_eq c κsel ε σ2 T ω,
    ← Fin.sum_univ_eq_sum_range
      (fun t : ℕ => xiCombWeight c κsel σ2 T t * ε ((t : ℤ) + 1) ω) T]
  exact Finset.sum_congr rfl fun t _ => by rw [hYi (t : ℕ)]

/-! ### The periodogram as a squared DFT modulus (FY §2.7.6)

The identification half of Theorem 2.14(ii) is deterministic: the periodogram ordinate is
`‖α_k‖²`, the `χ²₂`-type quantity `2π g(ω_k)(ξ_{2k−1}² + ξ_{2k}²)/2` is
`‖Γ(ω_k)‖² ‖α_{k,ε}‖²`, and the two differ only through the edge effect
`α_k − Γ(ω_k) α_{k,ε}`. -/

/-- The DFT of the observed window `t = 1, …, T` of a process. -/
private noncomputable def dftSample (Z : ℤ → Ω → ℝ) (T : ℕ) (k : ℕ) (ω : Ω) : ℂ :=
  dft (fun t : Fin T => Z (((t : ℕ) : ℤ) + 1) ω) (k : ℤ)

omit [MeasurableSpace Ω] in
private lemma exp_neg_I_ofReal (r : ℝ) :
    Complex.exp (-(Complex.I * (r : ℂ)))
      = (Real.cos r : ℂ) - (Real.sin r : ℂ) * Complex.I := by
  have h := exp_I_ofReal (-r)
  rw [Real.cos_neg, Real.sin_neg] at h
  rw [show -(Complex.I * (r : ℂ)) = Complex.I * ((-r : ℝ) : ℂ) by push_cast; ring, h]
  push_cast; ring

omit [MeasurableSpace Ω] in
/-- The DFT window split into its cosine and sine real parts. -/
private lemma dftSample_eq (Z : ℤ → Ω → ℝ) (T : ℕ) (k : ℕ) (ω : Ω) :
    dftSample Z T k ω
      = ((Real.sqrt T)⁻¹ : ℝ) *
        (((∑ t ∈ Finset.range T,
              Z ((t : ℤ) + 1) ω * Real.cos (((t : ℝ) + 1) * fourierFreq T k) : ℝ) : ℂ)
          - ((∑ t ∈ Finset.range T,
              Z ((t : ℤ) + 1) ω * Real.sin (((t : ℝ) + 1) * fourierFreq T k) : ℝ) : ℂ)
            * Complex.I) := by
  rw [dftSample, dft]
  congr 1
  rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Fin.sum_univ_eq_sum_range
      (fun t : ℕ => ((Z ((t : ℤ) + 1) ω * Real.cos (((t : ℝ) + 1) * fourierFreq T k) : ℝ) : ℂ)
        - ((Z ((t : ℤ) + 1) ω * Real.sin (((t : ℝ) + 1) * fourierFreq T k) : ℝ) : ℂ)
          * Complex.I) T]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hcast : -(Complex.I * ((((t : ℕ) + 1 : ℕ) : ℂ)) * ((fourierFreq T (k : ℤ) : ℝ) : ℂ))
      = -(Complex.I * (((((t : ℕ) : ℝ) + 1) * fourierFreq T (k : ℤ) : ℝ) : ℂ)) := by
    push_cast; ring
  rw [hcast, exp_neg_I_ofReal]
  push_cast
  ring

omit [MeasurableSpace Ω] in
/-- `‖α_k‖²` in terms of the cosine and sine sums. -/
private lemma normSq_dftSample (Z : ℤ → Ω → ℝ) {T : ℕ} (hT : 0 < T) (k : ℕ) (ω : Ω) :
    ‖dftSample Z T k ω‖ ^ 2
      = (T : ℝ)⁻¹ *
        ((∑ t ∈ Finset.range T,
            Z ((t : ℤ) + 1) ω * Real.cos (((t : ℝ) + 1) * fourierFreq T k)) ^ 2
          + (∑ t ∈ Finset.range T,
            Z ((t : ℤ) + 1) ω * Real.sin (((t : ℝ) + 1) * fourierFreq T k)) ^ 2) := by
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  rw [dftSample_eq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt T)⁻¹)]
  congr 1
  · rw [inv_pow, Real.sq_sqrt hTR.le]
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, zero_sub, add_zero]
    ring

omit [MeasurableSpace Ω] in
/-- `‖α_{k,ε}‖² = (σ²/2)(ξ_{2k−1}² + ξ_{2k}²)`: the `χ²₂` normalisation of FY §2.7.6. -/
private lemma normSq_dftSample_noise (ε : ℤ → Ω → ℝ) {σ2 : ℝ} (hσ : 0 < σ2) {T : ℕ}
    (hT : 0 < T) (k : ℕ) (ω : Ω) :
    ‖dftSample ε T k ω‖ ^ 2
      = σ2 / 2 * ((dftNoiseCos ε σ2 T k ω) ^ 2 + (dftNoiseSin ε σ2 T k ω) ^ 2) := by
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have h2T : (0 : ℝ) < 2 / (T : ℝ) := by positivity
  have hA2 : (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2 = 2 / ((T : ℝ) * σ2) := by
    rw [div_pow, Real.sq_sqrt h2T.le, Real.sq_sqrt hσ.le, div_div]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ t ∈ Finset.range T,
      ε ((t : ℤ) + 1) ω * Real.cos (((t : ℝ) + 1) * fourierFreq T k) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ t ∈ Finset.range T,
      ε ((t : ℤ) + 1) ω * Real.sin (((t : ℝ) + 1) * fourierFreq T k) := ⟨_, rfl⟩
  rw [normSq_dftSample ε hT k ω, dftNoiseCos, dftNoiseSin, ← hC, ← hS, mul_pow, mul_pow, hA2]
  field_simp

/-- **White-noise spectral density** `g_ε ≡ σ²/(2π)` (FY §2.3.2), reproved here to keep
this file off the ARMA layer. -/
private lemma spectralDensityOf_whiteNoise [IsProbabilityMeasure μ] {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hε : IsWhiteNoise ε σ2 μ) (l : AddCircle (2 * π)) :
    spectralDensityOf ε μ l = σ2 / (2 * π) := by
  rw [spectralDensityOf,
    tsum_eq_single 0 (fun k hk => by rw [hε.acvf_eq k, if_neg hk, zero_mul]),
    hε.acvf_eq 0, if_pos rfl, fourier_zero, Complex.one_re, mul_one]
  ring

/-- White noise has an absolutely summable ACVF (it is finitely supported). -/
private lemma hasSummableACVF_whiteNoise [IsProbabilityMeasure μ] {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hε : IsWhiteNoise ε σ2 μ) : HasSummableACVF ε μ :=
  summable_of_ne_finset_zero (s := {0}) fun k hk => by
    rw [hε.acvf_eq k, if_neg (by simpa using hk), abs_zero]

/-- **The spectral identification** `2π g_X(λ) = σ² ‖Γ(λ)‖²` for the filtered process. -/
private lemma two_pi_spectralDensityOf_eq [IsProbabilityMeasure μ] {σ2 : ℝ} {a : ℤ → ℝ}
    {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (ha : Summable fun j : ℤ => |a j|)
    (hmeas : ∀ t, Measurable (X t)) (hfil : IsFilteredBy X ε a μ)
    (l : AddCircle (2 * π)) :
    2 * π * spectralDensityOf X μ l = σ2 * ‖transferFun a l‖ ^ 2 := by
  have hwn := hε.isWhiteNoise
  rw [hfil.spectralDensityOf_eq ha hwn.isStationary (hasSummableACVF_whiteNoise hwn)
      hε.measurable hmeas l, spectralDensityOf_whiteNoise hwn l]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp

/-- The second moment of a weighted noise sum: `E(Σ w_t ε_{t+1})² = σ² Σ w_t²`. -/
private lemma integral_sq_weighted_noise [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε σ2 μ) (T : ℕ) (w : ℕ → ℝ) :
    ∫ ω, (∑ t ∈ Finset.range T, w t * ε ((t : ℤ) + 1) ω) ^ 2 ∂μ
      = σ2 * ∑ t ∈ Finset.range T, (w t) ^ 2 := by
  have hwn := hε.isWhiteNoise
  have hmemLp : ∀ t : ℤ, MemLp (ε t) 2 μ := hwn.memLp
  have hmemW : ∀ s : ℕ, MemLp (fun ω => w s * ε ((s : ℤ) + 1) ω) 2 μ :=
    fun s => (hmemLp ((s : ℤ) + 1)).const_mul (w s)
  have hint : ∀ s t : ℕ,
      Integrable (fun ω => (w s * ε ((s : ℤ) + 1) ω) * (w t * ε ((t : ℤ) + 1) ω)) μ :=
    fun s t => (hmemW s).integrable_mul (hmemW t)
  -- The Gram matrix of the innovations.
  have hcross : ∀ s t : ℕ,
      ∫ ω, (w s * ε ((s : ℤ) + 1) ω) * (w t * ε ((t : ℤ) + 1) ω) ∂μ
        = if s = t then σ2 * (w s) ^ 2 else 0 := by
    intro s t
    have hprodint : ∫ ω, (w s * ε ((s : ℤ) + 1) ω) * (w t * ε ((t : ℤ) + 1) ω) ∂μ
        = (w s * w t) * ∫ ω, ε ((s : ℤ) + 1) ω * ε ((t : ℤ) + 1) ω ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have hmul : ∫ ω, ε ((s : ℤ) + 1) ω * ε ((t : ℤ) + 1) ω ∂μ
        = cov[ε ((s : ℤ) + 1), ε ((t : ℤ) + 1); μ] := by
      rw [covariance_eq_sub (hmemLp _) (hmemLp _), hwn.integral_eq_zero, hwn.integral_eq_zero]
      simp [Pi.mul_apply]
    rw [hprodint, hmul]
    by_cases hst : s = t
    · subst hst
      rw [if_pos rfl, covariance_self (hmemLp _).aestronglyMeasurable.aemeasurable,
        hwn.variance_eq]
      ring
    · rw [if_neg hst, hwn.uncorrelated _ _ (by
        simp only [ne_eq, add_left_inj, Nat.cast_inj]; exact hst), mul_zero]
  -- Expand the square and integrate term by term.
  have hexp : ∀ ω : Ω, (∑ t ∈ Finset.range T, w t * ε ((t : ℤ) + 1) ω) ^ 2
      = ∑ s ∈ Finset.range T, ∑ t ∈ Finset.range T,
          (w s * ε ((s : ℤ) + 1) ω) * (w t * ε ((t : ℤ) + 1) ω) := by
    intro ω; rw [sq, Finset.sum_mul_sum]
  rw [integral_congr_ae (Eventually.of_forall hexp),
    integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun t _ => hint s t))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [integral_finset_sum _ (fun t _ => hint s t),
    Finset.sum_congr rfl (fun t _ => hcross s t), Finset.sum_ite_eq, if_pos hs]

/-- The second moment of the noise DFT ordinate is exactly `σ²` on the window
`1 ≤ k ≤ [(T−1)/2]` (the discrete Pythagoras `Σ cos² = Σ sin² = T/2`). -/
private lemma integral_normSq_dftSample_noise [IsProbabilityMeasure μ] {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) {T k : ℕ} (hk : 1 ≤ k) (hkT : k + k < T) :
    ∫ ω, ‖dftSample ε T k ω‖ ^ 2 ∂μ = σ2 := by
  have hT : 0 < T := by omega
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hcos := sum_cos_mul_cos hT hk hk hkT
  have hsin := sum_sin_mul_sin hT hk hk hkT
  rw [if_pos rfl] at hcos hsin
  have hsq : ∀ (f : ℕ → ℝ), (∑ t ∈ Finset.range T, f t * f t) = ∑ t ∈ Finset.range T, (f t) ^ 2 :=
    fun f => Finset.sum_congr rfl fun t _ => (sq (f t)).symm
  rw [hsq] at hcos hsin
  have hpt : ∀ ω : Ω, ‖dftSample ε T k ω‖ ^ 2
      = (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T,
            ε ((t : ℤ) + 1) ω * Real.cos (((t : ℝ) + 1) * fourierFreq T k)) ^ 2
        + (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T,
            ε ((t : ℤ) + 1) ω * Real.sin (((t : ℝ) + 1) * fourierFreq T k)) ^ 2 := by
    intro ω; rw [normSq_dftSample ε hT k ω]; ring
  have hcomm : ∀ (g : ℕ → ℝ) (ω : Ω), (∑ t ∈ Finset.range T, ε ((t : ℤ) + 1) ω * g t)
      = ∑ t ∈ Finset.range T, g t * ε ((t : ℤ) + 1) ω :=
    fun g ω => Finset.sum_congr rfl fun t _ => mul_comm _ _
  simp only [hpt, hcomm]
  have hIc : Integrable (fun ω => (∑ t ∈ Finset.range T,
      Real.cos (((t : ℝ) + 1) * fourierFreq T k) * ε ((t : ℤ) + 1) ω) ^ 2) μ := by
    have hm : MemLp (fun ω => ∑ t ∈ Finset.range T,
        Real.cos (((t : ℝ) + 1) * fourierFreq T k) * ε ((t : ℤ) + 1) ω) 2 μ :=
      memLp_finset_sum _ (fun t _ => (hε.isWhiteNoise.memLp _).const_mul _)
    exact hm.integrable_sq
  have hIs : Integrable (fun ω => (∑ t ∈ Finset.range T,
      Real.sin (((t : ℝ) + 1) * fourierFreq T k) * ε ((t : ℤ) + 1) ω) ^ 2) μ := by
    have hm : MemLp (fun ω => ∑ t ∈ Finset.range T,
        Real.sin (((t : ℝ) + 1) * fourierFreq T k) * ε ((t : ℤ) + 1) ω) 2 μ :=
      memLp_finset_sum _ (fun t _ => (hε.isWhiteNoise.memLp _).const_mul _)
    exact hm.integrable_sq
  rw [integral_add (hIc.const_mul _) (hIs.const_mul _), integral_const_mul, integral_const_mul,
    integral_sq_weighted_noise hε T (fun t => Real.cos (((t : ℝ) + 1) * fourierFreq T k)),
    integral_sq_weighted_noise hε T (fun t => Real.sin (((t : ℝ) + 1) * fourierFreq T k)),
    hcos, hsin]
  field_simp
  ring

private instance : Fact (0 < 2 * π) := ⟨by positivity⟩

omit [MeasurableSpace Ω] in
/-- The transfer function is bounded by the `ℓ¹` norm of the filter, uniformly in the
frequency. -/
private lemma norm_transferFun_le (a : ℤ → ℝ) (ha : Summable fun j : ℤ => |a j|)
    (l : AddCircle (2 * π)) : ‖transferFun a l‖ ≤ ∑' j : ℤ, |a j| := by
  have hnorm : ∀ j : ℤ, ‖(a j : ℂ) * fourier (T := 2 * π) (-j) l‖ = |a j| := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, fourier_apply, Circle.norm_coe, mul_one]
  have hsum : Summable fun j : ℤ => ‖(a j : ℂ) * fourier (T := 2 * π) (-j) l‖ := by
    simpa only [hnorm] using ha
  rw [transferFun]
  refine (norm_tsum_le_tsum_norm hsum).trans (le_of_eq ?_)
  exact tsum_congr hnorm

/-- Square-integrability of the noise DFT ordinate. -/
private lemma integrable_normSq_dftSample_noise [IsProbabilityMeasure μ] {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) {T : ℕ} (hT : 0 < T) (k : ℕ) :
    Integrable (fun ω => ‖dftSample ε T k ω‖ ^ 2) μ := by
  have hpt : ∀ ω : Ω, ‖dftSample ε T k ω‖ ^ 2
      = (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T,
            Real.cos (((t : ℝ) + 1) * fourierFreq T k) * ε ((t : ℤ) + 1) ω) ^ 2
        + (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T,
            Real.sin (((t : ℝ) + 1) * fourierFreq T k) * ε ((t : ℤ) + 1) ω) ^ 2 := by
    intro ω
    have hc : (∑ t ∈ Finset.range T,
          ε ((t : ℤ) + 1) ω * Real.cos (((t : ℝ) + 1) * fourierFreq T k))
        = ∑ t ∈ Finset.range T,
          Real.cos (((t : ℝ) + 1) * fourierFreq T k) * ε ((t : ℤ) + 1) ω :=
      Finset.sum_congr rfl fun t _ => mul_comm _ _
    have hs : (∑ t ∈ Finset.range T,
          ε ((t : ℤ) + 1) ω * Real.sin (((t : ℝ) + 1) * fourierFreq T k))
        = ∑ t ∈ Finset.range T,
          Real.sin (((t : ℝ) + 1) * fourierFreq T k) * ε ((t : ℤ) + 1) ω :=
      Finset.sum_congr rfl fun t _ => mul_comm _ _
    rw [normSq_dftSample ε hT k ω, hc, hs]
    ring
  have hIc : Integrable (fun ω => (∑ t ∈ Finset.range T,
      Real.cos (((t : ℝ) + 1) * fourierFreq T k) * ε ((t : ℤ) + 1) ω) ^ 2) μ :=
    (memLp_finset_sum _ (fun t _ => (hε.isWhiteNoise.memLp _).const_mul _)).integrable_sq
  have hIs : Integrable (fun ω => (∑ t ∈ Finset.range T,
      Real.sin (((t : ℝ) + 1) * fourierFreq T k) * ε ((t : ℤ) + 1) ω) ^ 2) μ :=
    (memLp_finset_sum _ (fun t _ => (hε.isWhiteNoise.memLp _).const_mul _)).integrable_sq
  exact ((hIc.const_mul _).add (hIs.const_mul _)).congr
    (Filter.Eventually.of_forall fun ω => (hpt ω).symm)

/-! ### The edge effect: the four-step route of the docstring below, executed

`Step 1` is the finite rearrangement `dftSample X^N = Σ_{|j| ≤ N} a_j e^{−ijω_k} D_j`
(`dftSample_truncFilter_eq`), `Step 2` the `L²` cost of a window shift
(`integral_normSq_winSum_sub_le`), `Step 3` the `N → ∞` passage
(`eLpNorm_dft_edge_le`) and `Step 4` the uniform envelope (`tendsto_edgeEnv`). -/

private noncomputable def eePhase (T k : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (-(Complex.I * (m : ℂ) * ((fourierFreq T k : ℝ) : ℂ)))

omit [MeasurableSpace Ω] in
private lemma norm_eePhase (T k : ℕ) (m : ℤ) : ‖eePhase T k m‖ = 1 := by
  rw [eePhase, Complex.norm_exp]
  norm_num

omit [MeasurableSpace Ω] in
private lemma eePhase_add (T k : ℕ) (m n : ℤ) :
    eePhase T k (m + n) = eePhase T k m * eePhase T k n := by
  rw [eePhase, eePhase, eePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

omit [MeasurableSpace Ω] in
private lemma dftSample_eq_sum_range (Z : ℤ → Ω → ℝ) (T : ℕ) (k : ℕ) (ω : Ω) :
    dftSample Z T k ω = ((Real.sqrt T)⁻¹ : ℝ) *
      ∑ t ∈ Finset.range T, (Z ((t : ℤ) + 1) ω : ℂ) * eePhase T k ((t : ℤ) + 1) := by
  rw [dftSample, dft, Fin.sum_univ_eq_sum_range
    (fun t : ℕ => (Z ((t : ℤ) + 1) ω : ℂ) *
      Complex.exp (-(Complex.I * (((t : ℕ) + 1 : ℕ) : ℂ) * ((fourierFreq T (k : ℤ)) : ℂ)))) T]
  refine congrArg _ (Finset.sum_congr rfl fun t _ => ?_)
  rw [eePhase]
  push_cast
  ring_nf

/-- The general-index Gram identity for a weighted sum of i.i.d. innovations. -/
private lemma integral_sq_weighted_noise_gen [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε σ2 μ) (S : Finset ℤ) (w : ℤ → ℝ) :
    ∫ ω, (∑ s ∈ S, w s * ε s ω) ^ 2 ∂μ = σ2 * ∑ s ∈ S, (w s) ^ 2 := by
  classical
  have hwn := hε.isWhiteNoise
  have hmemLp : ∀ t : ℤ, MemLp (ε t) 2 μ := hwn.memLp
  have hmemW : ∀ s : ℤ, MemLp (fun ω => w s * ε s ω) 2 μ :=
    fun s => (hmemLp s).const_mul (w s)
  have hint : ∀ s t : ℤ, Integrable (fun ω => (w s * ε s ω) * (w t * ε t ω)) μ :=
    fun s t => (hmemW s).integrable_mul (hmemW t)
  have hcross : ∀ s t : ℤ, ∫ ω, (w s * ε s ω) * (w t * ε t ω) ∂μ
      = if s = t then σ2 * (w s) ^ 2 else 0 := by
    intro s t
    have hprodint : ∫ ω, (w s * ε s ω) * (w t * ε t ω) ∂μ
        = (w s * w t) * ∫ ω, ε s ω * ε t ω ∂μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have hmul : ∫ ω, ε s ω * ε t ω ∂μ = cov[ε s, ε t; μ] := by
      rw [covariance_eq_sub (hmemLp _) (hmemLp _), hwn.integral_eq_zero, hwn.integral_eq_zero]
      simp [Pi.mul_apply]
    rw [hprodint, hmul]
    by_cases hst : s = t
    · subst hst
      rw [if_pos rfl, covariance_self (hmemLp _).aestronglyMeasurable.aemeasurable,
        hwn.variance_eq]
      ring
    · rw [if_neg hst, hwn.uncorrelated _ _ hst, mul_zero]
  have hexp : ∀ ω : Ω, (∑ s ∈ S, w s * ε s ω) ^ 2
      = ∑ s ∈ S, ∑ t ∈ S, (w s * ε s ω) * (w t * ε t ω) := by
    intro ω; rw [sq, Finset.sum_mul_sum]
  rw [integral_congr_ae (Eventually.of_forall hexp),
    integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun t _ => hint s t)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [integral_finset_sum _ (fun t _ => hint s t),
    Finset.sum_congr rfl (fun t _ => hcross s t), Finset.sum_ite_eq, if_pos hs]

/-- The complex form of the Gram identity. -/
private lemma integral_normSq_weighted_noise [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε σ2 μ) (S : Finset ℤ) (c : ℤ → ℂ) :
    ∫ ω, ‖∑ s ∈ S, c s * (ε s ω : ℂ)‖ ^ 2 ∂μ = σ2 * ∑ s ∈ S, ‖c s‖ ^ 2 := by
  classical
  have hre : ∀ ω : Ω, (∑ s ∈ S, c s * (ε s ω : ℂ)).re = ∑ s ∈ S, (c s).re * ε s ω := by
    intro ω
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun s _ => by simp [Complex.mul_re]
  have him : ∀ ω : Ω, (∑ s ∈ S, c s * (ε s ω : ℂ)).im = ∑ s ∈ S, (c s).im * ε s ω := by
    intro ω
    rw [Complex.im_sum]
    exact Finset.sum_congr rfl fun s _ => by simp [Complex.mul_im]
  have hpt : ∀ ω : Ω, ‖∑ s ∈ S, c s * (ε s ω : ℂ)‖ ^ 2
      = (∑ s ∈ S, (c s).re * ε s ω) ^ 2 + (∑ s ∈ S, (c s).im * ε s ω) ^ 2 := by
    intro ω
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre ω, him ω]
    ring
  have hIre : Integrable (fun ω => (∑ s ∈ S, (c s).re * ε s ω) ^ 2) μ :=
    (memLp_finset_sum _ (fun s _ => (hε.isWhiteNoise.memLp s).const_mul _)).integrable_sq
  have hIim : Integrable (fun ω => (∑ s ∈ S, (c s).im * ε s ω) ^ 2) μ :=
    (memLp_finset_sum _ (fun s _ => (hε.isWhiteNoise.memLp s).const_mul _)).integrable_sq
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hIre hIim,
    integral_sq_weighted_noise_gen hε S (fun s => (c s).re),
    integral_sq_weighted_noise_gen hε S (fun s => (c s).im), ← mul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun s _ => ?_)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- The DFT of the noise over the window shifted by `j`. -/
private noncomputable def winSum (ε : ℤ → Ω → ℝ) (T k : ℕ) (j : ℤ) (ω : Ω) : ℂ :=
  ((Real.sqrt T)⁻¹ : ℝ) * ∑ s ∈ Finset.Icc (1 - j) ((T : ℤ) - j), (ε s ω : ℂ) * eePhase T k s

omit [MeasurableSpace Ω] in
private lemma sum_Icc_shift {M : Type*} [AddCommMonoid M] (T : ℕ) (j : ℤ) (f : ℤ → M) :
    ∑ s ∈ Finset.Icc (1 - j) ((T : ℤ) - j), f s
      = ∑ t ∈ Finset.range T, f ((t : ℤ) + 1 - j) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map,
    show (((T : ℤ) - j) + 1 - (1 - j)).toNat = T from by omega]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  simp [Nat.castEmbedding, addLeftEmbedding]
  ring

omit [MeasurableSpace Ω] in
private lemma winSum_zero (ε : ℤ → Ω → ℝ) (T k : ℕ) (ω : Ω) :
    winSum ε T k 0 ω = dftSample ε T k ω := by
  rw [winSum, dftSample_eq_sum_range, sum_Icc_shift]
  simp

/-- **Step 2**: shifting the DFT window by `j` costs at most `2 min(|j|, T)` innovations. -/
private lemma integral_normSq_winSum_sub_le [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε σ2 μ) (hσ : 0 ≤ σ2) {T : ℕ} (hT : 0 < T) (k : ℕ) (j : ℤ) :
    ∫ ω, ‖winSum ε T k j ω - winSum ε T k 0 ω‖ ^ 2 ∂μ
      ≤ σ2 * (2 * min (T : ℝ) |(j : ℝ)| / T) := by
  classical
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  set Wj : Finset ℤ := Finset.Icc (1 - j) ((T : ℤ) - j) with hWj
  set W0 : Finset ℤ := Finset.Icc (1 - (0 : ℤ)) ((T : ℤ) - 0) with hW0
  set S : Finset ℤ := Finset.Icc (1 - (j.natAbs : ℤ)) ((T : ℤ) + (j.natAbs : ℤ)) with hS
  have hWjS : Wj ⊆ S := by
    intro s hs
    simp only [hWj, hS, Finset.mem_Icc] at hs ⊢
    omega
  have hW0S : W0 ⊆ S := by
    intro s hs
    simp only [hW0, hS, Finset.mem_Icc] at hs ⊢
    omega
  set c : ℤ → ℂ := fun s => (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * eePhase T k s *
    ((if s ∈ Wj then (1 : ℂ) else 0) - (if s ∈ W0 then (1 : ℂ) else 0)) with hc
  -- the difference of the two window sums is a weighted noise sum over `S`
  have hdiff : ∀ ω : Ω, winSum ε T k j ω - winSum ε T k 0 ω = ∑ s ∈ S, c s * (ε s ω : ℂ) := by
    intro ω
    have e1 : ∑ s ∈ S, (if s ∈ Wj then (1 : ℂ) else 0) *
          ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) * eePhase T k s * (ε s ω : ℂ))
        = ∑ s ∈ Wj, (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * eePhase T k s * (ε s ω : ℂ) := by
      rw [← Finset.sum_subset hWjS (fun x _ hx => by simp [hx])]
      exact Finset.sum_congr rfl fun s hs => by simp [hs]
    have e2 : ∑ s ∈ S, (if s ∈ W0 then (1 : ℂ) else 0) *
          ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) * eePhase T k s * (ε s ω : ℂ))
        = ∑ s ∈ W0, (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * eePhase T k s * (ε s ω : ℂ) := by
      rw [← Finset.sum_subset hW0S (fun x _ hx => by simp [hx])]
      exact Finset.sum_congr rfl fun s hs => by simp [hs]
    have hsplit : ∑ s ∈ S, c s * (ε s ω : ℂ)
        = (∑ s ∈ S, (if s ∈ Wj then (1 : ℂ) else 0) *
            ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) * eePhase T k s * (ε s ω : ℂ)))
          - ∑ s ∈ S, (if s ∈ W0 then (1 : ℂ) else 0) *
            ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) * eePhase T k s * (ε s ω : ℂ)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by simp only [hc]; ring
    rw [hsplit, e1, e2, winSum, winSum, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun s _ => by ring
  have hdiff2 : ∀ ω : Ω, ‖winSum ε T k j ω - winSum ε T k 0 ω‖ ^ 2
      = ‖∑ s ∈ S, c s * (ε s ω : ℂ)‖ ^ 2 := fun ω => by rw [hdiff ω]
  rw [integral_congr_ae (Eventually.of_forall hdiff2),
    integral_normSq_weighted_noise hε S c]
  refine mul_le_mul_of_nonneg_left ?_ hσ
  -- the weight energy is `(2T − 2 #(W_j ∩ W_0))/T`
  have hnormc : ∀ s : ℤ, ‖c s‖ ^ 2 = ((T : ℝ)⁻¹) *
      ((if s ∈ Wj then (1 : ℝ) else 0) + (if s ∈ W0 then (1 : ℝ) else 0)
        - 2 * (if s ∈ Wj ∩ W0 then (1 : ℝ) else 0)) := by
    intro s
    have hs : ‖(((Real.sqrt T)⁻¹ : ℝ) : ℂ)‖ ^ 2 = (T : ℝ)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.sqrt_inv,
        Real.sq_sqrt (by positivity)]
    rw [hc]
    simp only [norm_mul, mul_pow, norm_eePhase, mul_one, hs]
    congr 1
    by_cases h1 : s ∈ Wj <;> by_cases h2 : s ∈ W0 <;>
      simp [h1, h2, Finset.mem_inter] <;> norm_num
  rw [Finset.sum_congr rfl (fun s _ => hnormc s), ← Finset.mul_sum]
  have hsum1 : ∑ s ∈ S, (if s ∈ Wj then (1 : ℝ) else 0) = (Wj.card : ℝ) := by
    rw [← Finset.sum_subset hWjS (fun x _ hx => by simp [hx])]
    simp
  have hsum2 : ∑ s ∈ S, (if s ∈ W0 then (1 : ℝ) else 0) = (W0.card : ℝ) := by
    rw [← Finset.sum_subset hW0S (fun x _ hx => by simp [hx])]
    simp
  have hsum3 : ∑ s ∈ S, (if s ∈ Wj ∩ W0 then (1 : ℝ) else 0) = ((Wj ∩ W0).card : ℝ) := by
    rw [← Finset.sum_subset (Finset.inter_subset_left.trans hWjS)
      (fun x _ hx => if_neg hx), Finset.sum_congr rfl (fun x hx => if_pos hx)]
    simp
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum1, hsum2, ← Finset.mul_sum, hsum3]
  -- the cardinal bookkeeping: `#W_j = #W_0 = T` and `#(W_j ∩ W_0) ≥ T − |j|`
  have hcardWj : Wj.card = T := by rw [hWj, Int.card_Icc]; omega
  have hcardW0 : W0.card = T := by rw [hW0, Int.card_Icc]; omega
  have hcapA : Finset.Icc (max (1 - j) 1) (min ((T : ℤ) - j) (T : ℤ)) ⊆ Wj ∩ W0 := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    simp only [hWj, hW0, Finset.mem_inter, Finset.mem_Icc]
    omega
  have hsubcard : (T : ℤ) - (j.natAbs : ℤ)
      ≤ (((Finset.Icc (max (1 - j) 1) (min ((T : ℤ) - j) (T : ℤ))).card : ℕ) : ℤ) := by
    rw [Int.card_Icc]
    rcases le_total j 0 with hj | hj
    · rw [max_eq_left (by omega : (1 : ℤ) ≤ 1 - j),
        min_eq_right (by omega : (T : ℤ) ≤ (T : ℤ) - j)]
      omega
    · rw [max_eq_right (by omega : (1 : ℤ) - j ≤ 1),
        min_eq_left (by omega : (T : ℤ) - j ≤ (T : ℤ))]
      omega
  have hcapcard : (T : ℤ) - (j.natAbs : ℤ) ≤ ((Wj ∩ W0).card : ℤ) :=
    le_trans hsubcard (by exact_mod_cast Finset.card_le_card hcapA)
  have habsj : |(j : ℝ)| = ((j.natAbs : ℕ) : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hR1 : (T : ℝ) - ((j.natAbs : ℕ) : ℝ) ≤ (((Wj ∩ W0).card : ℕ) : ℝ) := by
    exact_mod_cast hcapcard
  have hR2 : (0 : ℝ) ≤ (((Wj ∩ W0).card : ℕ) : ℝ) := by positivity
  rw [hcardWj, hcardW0, habsj, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rcases le_total (T : ℝ) ((j.natAbs : ℕ) : ℝ) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- The symmetric partial filter, as a process. -/
private noncomputable def truncFilter (a : ℤ → ℝ) (ε : ℤ → Ω → ℝ) (N : ℕ) : ℤ → Ω → ℝ :=
  fun t ω => ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a j * ε (t - j) ω

omit [MeasurableSpace Ω] in
/-- **Step 1** (deterministic, finite): the DFT of the truncated filter is the finite
combination `Σ_{|j| ≤ N} a_j e^{−ijω_k} · (DFT of the noise over the shifted window)`. -/
private lemma dftSample_truncFilter_eq (a : ℤ → ℝ) (ε : ℤ → Ω → ℝ) (N : ℕ) (T k : ℕ) (ω : Ω) :
    dftSample (truncFilter a ε N) T k ω
      = ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (a j : ℂ) * eePhase T k j * winSum ε T k j ω := by
  rw [dftSample_eq_sum_range]
  have hwin : ∀ j : ℤ, winSum ε T k j ω = ((Real.sqrt T)⁻¹ : ℝ) *
      ∑ t ∈ Finset.range T, (ε ((t : ℤ) + 1 - j) ω : ℂ) * eePhase T k ((t : ℤ) + 1 - j) := by
    intro j
    rw [winSum, sum_Icc_shift]
  simp only [hwin]
  have hswap : ∑ t ∈ Finset.range T, ((truncFilter a ε N ((t : ℤ) + 1) ω : ℝ) : ℂ) *
        eePhase T k ((t : ℤ) + 1)
      = ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j *
          ∑ t ∈ Finset.range T, (ε ((t : ℤ) + 1 - j) ω : ℂ) * eePhase T k ((t : ℤ) + 1 - j) := by
    have hpt : ∀ t : ℕ, ((truncFilter a ε N ((t : ℤ) + 1) ω : ℝ) : ℂ) * eePhase T k ((t : ℤ) + 1)
        = ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j *
            ((ε ((t : ℤ) + 1 - j) ω : ℂ) * eePhase T k ((t : ℤ) + 1 - j)) := by
      intro t
      rw [truncFilter]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show ((t : ℤ) + 1) = j + ((t : ℤ) + 1 - j) from by ring, eePhase_add]
      ring
    rw [Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  rw [hswap, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [MeasurableSpace Ω] in
/-- The Fourier character of `AddCircle (2π)` at a Fourier frequency is the DFT phase. -/
private lemma fourier_eq_eePhase (T k : ℕ) (j : ℤ) :
    (fourier (-j) ((fourierFreq T k : ℝ) : AddCircle (2 * π)) : ℂ) = eePhase T k j := by
  rw [fourier_coe_apply, eePhase]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  field_simp
  push_cast
  ring

private lemma memLp_ofReal' {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    MemLp (fun ω => (f ω : ℂ)) 2 μ := by
  refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1, ?_⟩
  rw [eLpNorm_congr_norm_ae (g := f) (Eventually.of_forall fun ω => by simp)]
  exact hf.2

private lemma toReal_eLpNorm_two_sq {f : Ω → ℂ} (hf : MemLp f 2 μ) :
    ((eLpNorm f 2 μ).toReal) ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  have hnn : (0 : ℝ) ≤ ∫ ω, ‖f ω‖ ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num)]
  have hpow : ∀ ω, ‖f ω‖ ^ ((2 : ENNReal).toReal) = ‖f ω‖ ^ 2 := by
    intro ω
    rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [integral_congr_ae (Eventually.of_forall hpow),
    show ((2 : ENNReal).toReal)⁻¹ = 1 / (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt hnn]

/-- `L²`-membership of the filtered process, read off the `L²` convergence itself. -/
private lemma memLp_of_isFilteredBy [IsProbabilityMeasure μ] {σ2 : ℝ} {a : ℤ → ℝ}
    {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hmeas : ∀ t, Measurable (X t))
    (hfil : IsFilteredBy X ε a μ) (t : ℤ) : MemLp (X t) 2 μ := by
  obtain ⟨N, hN⟩ := ((hfil t).eventually (gt_mem_nhds (show (0 : ENNReal) < 1 by norm_num))).exists
  have htr : MemLp (truncFilter a ε N t) 2 μ :=
    memLp_finset_sum _ (fun j _ => (hε.isWhiteNoise.memLp (t - j)).const_mul (a j))
  have hdiff : MemLp (fun ω => X t ω - truncFilter a ε N t ω) 2 μ :=
    ⟨(hmeas t).aestronglyMeasurable.sub htr.1, lt_of_lt_of_le hN (by norm_num)⟩
  have hsum := hdiff.add htr
  have hfun : ((fun ω => X t ω - truncFilter a ε N t ω) + truncFilter a ε N t) = X t := by
    funext ω; simp
  rw [hfun] at hsum
  exact hsum

private lemma memLp_dftSample [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hZ : ∀ t, MemLp (Z t) 2 μ) (T k : ℕ) : MemLp (fun ω => dftSample Z T k ω) 2 μ := by
  have hfun : (fun ω => dftSample Z T k ω) = fun ω => ((Real.sqrt T)⁻¹ : ℝ) *
      ∑ t ∈ Finset.range T, (Z ((t : ℤ) + 1) ω : ℂ) * eePhase T k ((t : ℤ) + 1) :=
    funext fun ω => dftSample_eq_sum_range Z T k ω
  rw [hfun]
  exact (memLp_finset_sum (Finset.range T)
    (fun (t : ℕ) (_ : t ∈ Finset.range T) =>
      (memLp_ofReal' (hZ ((t : ℤ) + 1))).mul_const (eePhase T k ((t : ℤ) + 1)))).const_mul _

private lemma memLp_winSum [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε σ2 μ) (T k : ℕ) (j : ℤ) : MemLp (fun ω => winSum ε T k j ω) 2 μ :=
  (memLp_finset_sum (Finset.Icc (1 - j) ((T : ℤ) - j))
    (fun (s : ℤ) (_ : s ∈ Finset.Icc (1 - j) ((T : ℤ) - j)) =>
      (memLp_ofReal' (hε.isWhiteNoise.memLp s)).mul_const (eePhase T k s))).const_mul _

/-- The per-lag edge weight `(2 min(|j|, T)/T)^{1/2}`. -/
private noncomputable def edgeWeight (T : ℕ) (j : ℤ) : ℝ :=
  Real.sqrt (2 * min (T : ℝ) |(j : ℝ)| / T)

/-- The edge envelope `σ √2 Σ_j |a_j| (min(|j|,T)/T)^{1/2}`, uniform in the frequency. -/
private noncomputable def edgeEnv (σ2 : ℝ) (a : ℤ → ℝ) (T : ℕ) : ℝ :=
  Real.sqrt σ2 * ∑' j : ℤ, |a j| * edgeWeight T j

private lemma edgeWeight_nonneg (T : ℕ) (j : ℤ) : 0 ≤ edgeWeight T j := Real.sqrt_nonneg _

private lemma edgeWeight_le (T : ℕ) (j : ℤ) : edgeWeight T j ≤ Real.sqrt 2 := by
  refine Real.sqrt_le_sqrt ?_
  rcases Nat.eq_zero_or_pos T with hT | hT
  · simp [hT]
  · have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    rw [div_le_iff₀ hTR]
    have : min (T : ℝ) |(j : ℝ)| ≤ (T : ℝ) := min_le_left _ _
    linarith

private lemma summable_edgeWeight {a : ℤ → ℝ} (ha : Summable fun j : ℤ => |a j|) (T : ℕ) :
    Summable fun j : ℤ => |a j| * edgeWeight T j := by
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _) (edgeWeight_nonneg T j))
    (fun j => mul_le_mul_of_nonneg_left (edgeWeight_le T j) (abs_nonneg _)) (ha.mul_right _)

private lemma edgeEnv_nonneg {σ2 : ℝ} (hσ : 0 ≤ σ2) (a : ℤ → ℝ) (T : ℕ) :
    0 ≤ edgeEnv σ2 a T :=
  mul_nonneg (Real.sqrt_nonneg _)
    (tsum_nonneg fun j => mul_nonneg (abs_nonneg _) (edgeWeight_nonneg T j))

private lemma tendsto_edgeEnv {σ2 : ℝ} {a : ℤ → ℝ} (ha : Summable fun j : ℤ => |a j|) :
    Tendsto (fun T : ℕ => edgeEnv σ2 a T) atTop (𝓝 0) := by
  have hpt : ∀ j : ℤ, Tendsto (fun T : ℕ => |a j| * edgeWeight T j) atTop (𝓝 0) := by
    intro j
    have hev : ∀ᶠ T : ℕ in atTop, |a j| * edgeWeight T j
        = |a j| * Real.sqrt (2 * |(j : ℝ)| / T) := by
      filter_upwards [eventually_ge_atTop j.natAbs] with T hT
      have habsj : |(j : ℝ)| = ((j.natAbs : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      have : |(j : ℝ)| ≤ (T : ℝ) := by
        rw [habsj]; exact_mod_cast hT
      rw [edgeWeight, min_eq_right this]
    refine Tendsto.congr' (Filter.EventuallyEq.symm hev) ?_
    have h1 : Tendsto (fun T : ℕ => 2 * |(j : ℝ)| / T) atTop (𝓝 0) := by
      simpa using tendsto_const_div_atTop_nhds_zero_nat (2 * |(j : ℝ)|)
    have h2 : Tendsto (fun T : ℕ => Real.sqrt (2 * |(j : ℝ)| / T)) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at h
      exact h
    simpa only [mul_zero] using h2.const_mul |a j|
  have hbd : ∀ᶠ T : ℕ in atTop, ∀ j : ℤ, ‖|a j| * edgeWeight T j‖ ≤ |a j| * Real.sqrt 2 := by
    filter_upwards with T j
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (edgeWeight_nonneg T j))]
    exact mul_le_mul_of_nonneg_left (edgeWeight_le T j) (abs_nonneg _)
  have := tendsto_tsum_of_dominated_convergence (f := fun (T : ℕ) (j : ℤ) =>
    |a j| * edgeWeight T j) (g := fun _ : ℤ => (0 : ℝ)) (ha.mul_right _) hpt hbd
  simp only [tsum_zero] at this
  simpa [edgeEnv] using this.const_mul (Real.sqrt σ2)

private lemma eLpNorm_two_le_of_integral_normSq_le {f : Ω → ℂ} (hf : MemLp f 2 μ)
    {C : ℝ} (hC : 0 ≤ C) (h : ∫ ω, ‖f ω‖ ^ 2 ∂μ ≤ C ^ 2) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal C := by
  have h2 : ((eLpNorm f 2 μ).toReal) ^ 2 ≤ C ^ 2 := by rw [toReal_eLpNorm_two_sq hf]; exact h
  have h3 : (eLpNorm f 2 μ).toReal ≤ C := by
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm f 2 μ)]
  exact (ENNReal.le_ofReal_iff_toReal_le hf.2.ne hC).2 h3

private lemma memLp_truncFilter [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε σ2 μ) (a : ℤ → ℝ) (N : ℕ) (t : ℤ) : MemLp (truncFilter a ε N t) 2 μ :=
  memLp_finset_sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun (j : ℤ) (_ : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) =>
      (hε.isWhiteNoise.memLp (t - j)).const_mul (a j))

/-- The symmetric windows exhaust `ℤ`. -/
private lemma tendsto_Icc_symm :
    Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun m n hmn => ?_) (fun x => ⟨x.natAbs, ?_⟩)
  · have : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    refine Finset.subset_iff.mpr fun q hq => ?_
    simp only [Finset.mem_Icc] at hq ⊢
    omega
  · simp only [Finset.mem_Icc]
    omega

/-- **The edge bound at a fixed sample size and frequency** (Steps 1–3 assembled). -/
private lemma eLpNorm_dft_edge_le [IsProbabilityMeasure μ] {σ2 : ℝ} {a : ℤ → ℝ}
    {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hσ : 0 ≤ σ2)
    (ha : Summable fun j : ℤ => |a j|)
    (hmeas : ∀ t, Measurable (X t)) (hfil : IsFilteredBy X ε a μ) {T : ℕ} (hT : 0 < T) (k : ℕ) :
    eLpNorm (fun ω => dftSample X T k ω
        - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π)) * dftSample ε T k ω) 2 μ
      ≤ ENNReal.ofReal (edgeEnv σ2 a T) := by
  classical
  have hXmem : ∀ t, MemLp (X t) 2 μ := memLp_of_isFilteredBy hε hmeas hfil
  have hEmem : ∀ t, MemLp (ε t) 2 μ := fun t => hε.isWhiteNoise.memLp t
  have hmemDE : MemLp (fun ω => dftSample ε T k ω) 2 μ := memLp_dftSample hEmem T k
  have hmemDX : MemLp (fun ω => dftSample X T k ω) 2 μ := memLp_dftSample hXmem T k
  have hmemtr : ∀ N : ℕ, MemLp (fun ω => dftSample (truncFilter a ε N) T k ω) 2 μ := fun N =>
    memLp_dftSample (fun t => memLp_truncFilter hε a N t) T k
  -- the transfer function as the limit of the symmetric partial sums
  have hsummableC : Summable (fun j : ℤ => (a j : ℂ) * eePhase T k j) := by
    refine Summable.of_norm (Summable.congr ha (fun j => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_eePhase, mul_one]
  have htf : transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))
      = ∑' j : ℤ, (a j : ℂ) * eePhase T k j := by
    rw [transferFun]
    exact tsum_congr fun j => by rw [fourier_eq_eePhase]
  have hΓN : Tendsto (fun N : ℕ =>
      ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j) atTop
      (𝓝 (transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π)))) := by
    rw [htf]
    exact hsummableC.hasSum.comp tendsto_Icc_symm
  -- the truncated edge term is uniformly bounded by the envelope
  have hFN : ∀ N : ℕ, eLpNorm (fun ω => dftSample (truncFilter a ε N) T k ω
        - (∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j)
          * dftSample ε T k ω) 2 μ ≤ ENNReal.ofReal (edgeEnv σ2 a T) := by
    intro N
    have hrw : (fun ω => dftSample (truncFilter a ε N) T k ω
          - (∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j) * dftSample ε T k ω)
        = ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            (fun ω => ((a j : ℂ) * eePhase T k j) *
              (winSum ε T k j ω - winSum ε T k 0 ω)) := by
      funext ω
      rw [Finset.sum_apply, dftSample_truncFilter_eq, ← winSum_zero ε T k ω, Finset.sum_mul,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hrw]
    refine le_trans (eLpNorm_sum_le (fun j _ =>
      (((memLp_winSum hε T k j).sub (memLp_winSum hε T k 0)).const_mul _).1) one_le_two) ?_
    have hterm : ∀ j : ℤ,
        eLpNorm (fun ω => ((a j : ℂ) * eePhase T k j) *
            (winSum ε T k j ω - winSum ε T k 0 ω)) 2 μ
          ≤ ENNReal.ofReal (|a j| * (Real.sqrt σ2 * edgeWeight T j)) := by
      intro j
      have hsmul : (fun ω => ((a j : ℂ) * eePhase T k j) *
          (winSum ε T k j ω - winSum ε T k 0 ω))
          = ((a j : ℂ) * eePhase T k j) • (fun ω => winSum ε T k j ω - winSum ε T k 0 ω) := by
        funext ω; simp [smul_eq_mul]
      rw [hsmul, eLpNorm_const_smul]
      have hnc : ‖(a j : ℂ) * eePhase T k j‖ₑ = ENNReal.ofReal |a j| := by
        rw [← ofReal_norm_eq_enorm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          norm_eePhase, mul_one]
      have hbound : eLpNorm (fun ω => winSum ε T k j ω - winSum ε T k 0 ω) 2 μ
          ≤ ENNReal.ofReal (Real.sqrt σ2 * edgeWeight T j) := by
        refine eLpNorm_two_le_of_integral_normSq_le
          ((memLp_winSum hε T k j).sub (memLp_winSum hε T k 0))
          (mul_nonneg (Real.sqrt_nonneg _) (edgeWeight_nonneg T j)) ?_
        have h := integral_normSq_winSum_sub_le hε hσ hT k j
        refine h.trans (le_of_eq ?_)
        have hminnn : (0 : ℝ) ≤ min (T : ℝ) |(j : ℝ)| :=
          le_min (by positivity) (abs_nonneg _)
        have hwnn : (0 : ℝ) ≤ 2 * min (T : ℝ) |(j : ℝ)| / (T : ℝ) :=
          div_nonneg (by linarith) (by positivity)
        rw [mul_pow, Real.sq_sqrt hσ, edgeWeight, Real.sq_sqrt hwnn]
      rw [hnc, ENNReal.ofReal_mul (abs_nonneg _)]
      exact mul_le_mul_right hbound _
    refine le_trans (Finset.sum_le_sum (fun j _ => hterm j)) ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (edgeWeight_nonneg T j)))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsum : ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a j| * (Real.sqrt σ2 * edgeWeight T j)
        = Real.sqrt σ2 * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a j| * edgeWeight T j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum, edgeEnv]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    exact (summable_edgeWeight ha T).sum_le_tsum _
      (fun j _ => mul_nonneg (abs_nonneg _) (edgeWeight_nonneg T j))
  -- the two `N → ∞` defects
  have hAN : Tendsto (fun N : ℕ =>
      eLpNorm (fun ω => dftSample X T k ω - dftSample (truncFilter a ε N) T k ω) 2 μ) atTop (𝓝 0) := by
    have hle : ∀ N : ℕ,
        eLpNorm (fun ω => dftSample X T k ω - dftSample (truncFilter a ε N) T k ω) 2 μ
          ≤ ∑ t ∈ Finset.range T, ENNReal.ofReal ((Real.sqrt T)⁻¹) *
              eLpNorm (fun ω => X ((t : ℤ) + 1) ω - truncFilter a ε N ((t : ℤ) + 1) ω) 2 μ := by
      intro N
      have hrw : (fun ω => dftSample X T k ω - dftSample (truncFilter a ε N) T k ω)
          = ∑ t ∈ Finset.range T, (fun ω => (((Real.sqrt T)⁻¹ : ℝ) : ℂ) *
              (((X ((t : ℤ) + 1) ω - truncFilter a ε N ((t : ℤ) + 1) ω : ℝ)) : ℂ) *
                eePhase T k ((t : ℤ) + 1)) := by
        funext ω
        rw [Finset.sum_apply, dftSample_eq_sum_range, dftSample_eq_sum_range, Finset.mul_sum,
          Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun t _ => by push_cast; ring
      rw [hrw]
      refine le_trans (eLpNorm_sum_le (fun t _ => ?_) one_le_two) (Finset.sum_le_sum fun t _ => ?_)
      · exact (((memLp_ofReal' ((hXmem _).sub (memLp_truncFilter hε a N _))).const_mul _).mul_const
          (eePhase T k ((t : ℤ) + 1))).1
      · have hsmul : (fun ω => (((Real.sqrt T)⁻¹ : ℝ) : ℂ) *
            (((X ((t : ℤ) + 1) ω - truncFilter a ε N ((t : ℤ) + 1) ω : ℝ)) : ℂ) *
              eePhase T k ((t : ℤ) + 1))
            = ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) * eePhase T k ((t : ℤ) + 1)) •
              (fun ω => (((X ((t : ℤ) + 1) ω - truncFilter a ε N ((t : ℤ) + 1) ω : ℝ)) : ℂ)) := by
          funext ω; simp [smul_eq_mul]; ring
        rw [hsmul, eLpNorm_const_smul]
        have hnc : ‖(((Real.sqrt T)⁻¹ : ℝ) : ℂ) * eePhase T k ((t : ℤ) + 1)‖ₑ
            = ENNReal.ofReal ((Real.sqrt T)⁻¹) := by
          rw [← ofReal_norm_eq_enorm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            norm_eePhase, mul_one, abs_of_nonneg (by positivity)]
        rw [hnc]
        refine mul_le_mul_right (le_of_eq ?_) _
        refine eLpNorm_congr_norm_ae (Eventually.of_forall fun ω => ?_)
        rw [Complex.norm_real]
    have hg : Tendsto (fun N : ℕ => ∑ t ∈ Finset.range T,
        ENNReal.ofReal ((Real.sqrt T)⁻¹) *
          eLpNorm (fun ω => X ((t : ℤ) + 1) ω - truncFilter a ε N ((t : ℤ) + 1) ω) 2 μ)
        atTop (𝓝 0) := by
      have h0 : ∀ t ∈ Finset.range T, Tendsto (fun N : ℕ => ENNReal.ofReal ((Real.sqrt T)⁻¹) *
          eLpNorm (fun ω => X ((t : ℤ) + 1) ω - truncFilter a ε N ((t : ℤ) + 1) ω) 2 μ)
          atTop (𝓝 0) := by
        intro t _
        have := ENNReal.Tendsto.const_mul (hfil ((t : ℤ) + 1))
          (Or.inr (by simp : ENNReal.ofReal ((Real.sqrt T)⁻¹) ≠ ⊤))
        simpa using! this
      have := tendsto_finset_sum (Finset.range T) h0
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
      (fun N => zero_le) hle
  have hBN : Tendsto (fun N : ℕ => eLpNorm (fun ω =>
      ((∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j)
        - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))) * dftSample ε T k ω) 2 μ)
      atTop (𝓝 0) := by
    have heq : ∀ N : ℕ, eLpNorm (fun ω =>
        ((∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j)
          - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))) * dftSample ε T k ω) 2 μ
        = ‖(∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j)
            - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))‖ₑ *
          eLpNorm (fun ω => dftSample ε T k ω) 2 μ := by
      intro N
      rw [show (fun ω => ((∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j)
          - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))) * dftSample ε T k ω)
        = ((∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j)
          - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))) •
          (fun ω => dftSample ε T k ω) from funext fun ω => by simp [smul_eq_mul]]
      exact eLpNorm_const_smul _ _ _ _
    simp only [heq]
    have hn : Tendsto (fun N : ℕ => ‖(∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (a j : ℂ) * eePhase T k j)
        - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))‖ₑ) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => ‖(∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (a j : ℂ) * eePhase T k j)
          - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))‖) atTop (𝓝 0) := by
        have h := (hΓN.sub (tendsto_const_nhds
          (x := transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))))).norm
        simpa using h
      have h2 := ENNReal.tendsto_ofReal h1
      simpa only [ofReal_norm_eq_enorm, ENNReal.ofReal_zero] using h2
    have := ENNReal.Tendsto.mul_const hn (Or.inr hmemDE.2.ne)
    simpa using this
  -- assembly
  have hlim : Tendsto (fun N : ℕ =>
      eLpNorm (fun ω => dftSample X T k ω - dftSample (truncFilter a ε N) T k ω) 2 μ
      + eLpNorm (fun ω => ((∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j)
          - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))) * dftSample ε T k ω) 2 μ
      + ENNReal.ofReal (edgeEnv σ2 a T)) atTop (𝓝 (ENNReal.ofReal (edgeEnv σ2 a T))) := by
    simpa using (hAN.add hBN).add (tendsto_const_nhds (x := ENNReal.ofReal (edgeEnv σ2 a T)))
  refine ge_of_tendsto hlim (Eventually.of_forall fun N => ?_)
  have hdec : (fun ω => dftSample X T k ω
      - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π)) * dftSample ε T k ω)
      = (fun ω => dftSample X T k ω - dftSample (truncFilter a ε N) T k ω)
        + ((fun ω => ((∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j)
            - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))) * dftSample ε T k ω)
          + (fun ω => dftSample (truncFilter a ε N) T k ω
            - (∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (a j : ℂ) * eePhase T k j)
              * dftSample ε T k ω)) := by
    funext ω; simp; ring
  rw [hdec]
  refine le_trans (eLpNorm_add_le (hmemDX.sub (hmemtr N)).1 ?_ one_le_two) ?_
  · exact (((hmemDE.const_mul _)).add ((hmemtr N).sub (hmemDE.const_mul _))).1
  · rw [add_assoc]
    refine add_le_add le_rfl (le_trans (eLpNorm_add_le (hmemDE.const_mul _).1
      ((hmemtr N).sub (hmemDE.const_mul _)).1 one_le_two) ?_)
    exact add_le_add le_rfl (hFN N)

/-- **THE EDGE-EFFECT CORE (FY eq. (2.72)) — PROVED** (wave `ts/f3-spectral-garch-finale`,
2026-08-09; it was the single open debt of this file, which is now `sorry`-free and
axiom-clean).  The four-step route recorded below was executed *verbatim*; the bricks are
in the section just above.  Two implementation notes worth keeping:

* the symmetric difference of the two windows is never formed — the weight
  `1_{W_j} − 1_{W_0}` is summed over any common superset and its energy is read off
  `#W_j + #W_0 − 2#(W_j ∩ W_0) = 2T − 2#(W_j ∩ W_0)`, which needs only the *lower* bound
  `#(W_j ∩ W_0) ≥ T − |j|` (an explicit sub-interval plus `omega`);
* step 4's `ℓ¹` split at `|j| ≤ √T` described below is **unnecessary**: Tannery's theorem
  (`tendsto_tsum_of_dominated_convergence`) applies directly, with dominating function
  `|a_j|√2` and pointwise limit `0`, which is both shorter and sharper.

`α_k = Γ(ω_k) α_{k,ε} + Y_T(ω_k)` where the edge term `Y_T` collects, for each lag `j`,
the at most `2 min(|j|, T)` innovations that the window `t = 1, …, T` shifts in or out:
`Y_T(ω_k) = T^{-1/2} Σ_j a_j e^{-ijω_k} (Σ_{s ∈ W_j} ε_s e^{-isω_k})` with `#W_j ≤
2 min(|j|,T)`. Independence gives `‖Y_T(ω_k)‖_{L²} ≤ σ (2/T)^{1/2} Σ_j |a_j| min(|j|,T)^{1/2}`,
uniformly in `k`, and the right side tends to `0` by dominated convergence on the `ℓ¹`
weight (split at `|j| ≤ T^{1/2}`).

Formalizing it needs the `L²` interchange of the (infinite) filter sum with the (finite)
DFT sum through `IsFilteredBy`.

**Route, decomposed (executed).** The trap is
that `IsFilteredBy` is stated as an `L²` limit of the *symmetric* partial sums
`Σ_{|j| ≤ N} a_j ε_{t−j}`, so the interchange must be done at finite `N`, where it is an
exact finite rearrangement, and only then passed to the limit:
1. (deterministic, finite) for `X^N_t = Σ_{|j| ≤ N} a_j ε_{t−j}`,
   `dftSample X^N T k = Σ_{|j| ≤ N} a_j e^{−ijω_k} · D_j` where
   `D_j = T^{−1/2} Σ_{t=1}^{T} ε_{t−j} e^{−i(t−j)ω_k}` is the DFT of `ε` over the shifted
   window `[1−j, T−j]` — a `Finset.sum_comm` plus `e^{−itω_k} = e^{−ijω_k}e^{−i(t−j)ω_k}`;
2. (probabilistic) `‖D_j − dftSample ε T k‖_{L²} ≤ σ (2 min(|j|,T)/T)^{1/2}`: the two
   windows differ in at most `2 min(|j|,T)` innovations and the iid orthogonality of
   `hε` makes the `L²` norm of that difference the square root of `σ²/T` times their
   count;
3. (`ℓ¹` limit) `‖dftSample X^N T k − Γ_N(ω_k) dftSample ε T k‖_{L²} ≤ e_N(T)` with
   `e_N(T) = σ√2 Σ_{|j| ≤ N} |a_j| (min(|j|,T)/T)^{1/2}`, then `N → ∞` using
   `IsFilteredBy` on the left (`dftSample` is a *finite* linear combination of the `X_t`,
   so `L²` convergence transfers) and `ha` on the right;
4. (uniformity) `e(T) = σ√2 Σ_j |a_j| (min(|j|,T)/T)^{1/2} → 0` and does not depend on
   `k`: split at `|j| ≤ √T`, where `(min(|j|,T)/T)^{1/2} ≤ T^{−1/4}`, against the `ℓ¹`
   tail `Σ_{|j| > √T} |a_j| → 0`.

Everything
downstream of it — the spectral identification `2π g = σ²‖Γ‖²`, the `χ²₂` normalisation
`‖α_{k,ε}‖² = (σ²/2)(ξ_{2k−1}² + ξ_{2k}²)`, the exact second moment `E‖α_{k,ε}‖² = σ²`
and the `L¹` assembly — is proved. -/
private lemma exists_dft_edge_L2_bound [IsProbabilityMeasure μ] {σ2 : ℝ} {a : ℤ → ℝ}
    {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (ha : Summable fun j : ℤ => |a j|)
    (hmeas : ∀ t, Measurable (X t)) (hfil : IsFilteredBy X ε a μ) :
    ∃ e : ℕ → ℝ, (∀ T, 0 ≤ e T) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ T k : ℕ, 1 ≤ k → k + k < T →
        Integrable (fun ω => ‖dftSample X T k ω
            - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))
              * dftSample ε T k ω‖ ^ 2) μ ∧
        ∫ ω, ‖dftSample X T k ω
            - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))
              * dftSample ε T k ω‖ ^ 2 ∂μ ≤ e T := by
  refine ⟨fun T => (edgeEnv σ2 a T) ^ 2, fun T => sq_nonneg _, ?_, ?_⟩
  · have := (tendsto_edgeEnv (σ2 := σ2) ha).pow 2
    simpa using this
  · intro T k hk hkT
    have hT : 0 < T := lt_of_le_of_lt (Nat.zero_le _) hkT
    have hXmem : ∀ t, MemLp (X t) 2 μ := memLp_of_isFilteredBy hε hmeas hfil
    have hmemDE : MemLp (fun ω => dftSample ε T k ω) 2 μ :=
      memLp_dftSample (fun t => hε.isWhiteNoise.memLp t) T k
    have hmemDX : MemLp (fun ω => dftSample X T k ω) 2 μ := memLp_dftSample hXmem T k
    have hmemF : MemLp (fun ω => dftSample X T k ω
        - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π)) * dftSample ε T k ω) 2 μ :=
      hmemDX.sub (hmemDE.const_mul _)
    refine ⟨hmemF.norm.integrable_sq, ?_⟩
    rw [← toReal_eLpNorm_two_sq hmemF]
    have hle := eLpNorm_dft_edge_le hε hσ.le ha hmeas hfil hT k
    have h1 : (eLpNorm (fun ω => dftSample X T k ω
        - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))
          * dftSample ε T k ω) 2 μ).toReal ≤ edgeEnv σ2 a T :=
      (ENNReal.le_ofReal_iff_toReal_le hmemF.2.ne (edgeEnv_nonneg hσ.le a T)).1 hle
    have h2 : (0 : ℝ) ≤ (eLpNorm (fun ω => dftSample X T k ω
        - transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π))
          * dftSample ε T k ω) 2 μ).toReal := ENNReal.toReal_nonneg
    nlinarith

/-- **FY Theorem 2.14(ii)**: for the two-sided linear process, uniformly over the
Fourier frequencies `1 ≤ k ≤ [(T−1)/2]`, the periodogram ordinate is the rescaled
χ²₂-type quadratic form of the noise trigonometric sums up to an `L¹`-negligible
remainder:
`E |I_T(ω_k) − 2π g(ω_k) (ξ_{2k−1}² + ξ_{2k}²)/2| ≤ b_T → 0`. -/
theorem periodogram_eq_scaled_chi2_approx [IsProbabilityMeasure μ] {σ2 : ℝ} {a : ℤ → ℝ}
    {X ε : ℤ → Ω → ℝ}
    -- USER-INPUT: iid(0, σ²) innovations; FY Thm 2.14
    (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    -- USER-INPUT: absolutely summable two-sided coefficients; FY Thm 2.14
    (ha : Summable fun j : ℤ => |a j|)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: two-sided linear representation (FY eq. (2.24), zero mean),
    -- definitionally `IsFilteredBy X ε a μ`
    (hfil : IsFilteredBy X ε a μ) :
    ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
      ∀ T k : ℕ, 1 ≤ k → k ≤ (T - 1) / 2 →
        ∫ ω, |periodogram (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) k
            - 2 * π * spectralDensityOf X μ ((fourierFreq T k : ℝ) : AddCircle (2 * π))
              * ((dftNoiseCos ε σ2 T k ω) ^ 2 + (dftNoiseSin ε σ2 T k ω) ^ 2) / 2|
          ∂μ ≤ b T := by
  obtain ⟨e, hena, he0, hedge⟩ := exists_dft_edge_L2_bound hε hσ ha hmeas hfil
  obtain ⟨Ca, hCadef⟩ : ∃ Ca : ℝ, Ca = ∑' j : ℤ, |a j| := ⟨_, rfl⟩
  have hCa0 : 0 ≤ Ca := by rw [hCadef]; exact tsum_nonneg fun j => abs_nonneg _
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℕ → ℝ,
      δ = fun T : ℕ => Real.sqrt (e T + 1 / ((T : ℝ) + 1)) := ⟨_, rfl⟩
  have hinv : ∀ T : ℕ, (0 : ℝ) < 1 / ((T : ℝ) + 1) := by
    intro T; positivity
  have hδpos : ∀ T, 0 < δ T := by
    intro T
    rw [hδdef]
    exact Real.sqrt_pos.2 (by linarith [hena T, hinv T])
  have hδsq : ∀ T, e T ≤ (δ T) ^ 2 := by
    intro T
    rw [hδdef, Real.sq_sqrt (by linarith [hena T, hinv T])]
    linarith [hinv T]
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have h2 : Tendsto (fun T : ℕ => 1 / ((T : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun T : ℕ => e T + 1 / ((T : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using he0.add h2
    rw [hδdef]
    simpa using! (Real.continuous_sqrt.tendsto 0).comp h1
  refine ⟨fun T => δ T * (Ca ^ 2 * σ2) + e T + δ T, ?_, ?_⟩
  · have := ((hδ0.mul_const (Ca ^ 2 * σ2)).add he0).add hδ0
    simpa using this
  intro T k hk1 hk2
  have hkT : k + k < T := by omega
  have hT : 0 < T := by omega
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℂ,
      Γ = transferFun a ((fourierFreq T k : ℝ) : AddCircle (2 * π)) := ⟨_, rfl⟩
  obtain ⟨hDint, hDbd⟩ := hedge T k hk1 hkT
  rw [← hΓ] at hDint hDbd
  -- The observed and the noise-driven ordinates.
  have hΓle : ‖Γ‖ ≤ Ca := by
    rw [hΓ, hCadef]; exact norm_transferFun_le a ha _
  have hInoise := integrable_normSq_dftSample_noise hε hT k
  have hCint : Integrable (fun ω => ‖Γ * dftSample ε T k ω‖ ^ 2) μ := by
    have : ∀ ω : Ω, ‖Γ * dftSample ε T k ω‖ ^ 2 = ‖Γ‖ ^ 2 * ‖dftSample ε T k ω‖ ^ 2 := by
      intro ω; rw [norm_mul, mul_pow]
    exact (hInoise.const_mul (‖Γ‖ ^ 2)).congr (Eventually.of_forall fun ω => (this ω).symm)
  have hCval : ∫ ω, ‖Γ * dftSample ε T k ω‖ ^ 2 ∂μ = ‖Γ‖ ^ 2 * σ2 := by
    have hpt : ∀ ω : Ω, ‖Γ * dftSample ε T k ω‖ ^ 2
        = ‖Γ‖ ^ 2 * ‖dftSample ε T k ω‖ ^ 2 := fun ω => by rw [norm_mul, mul_pow]
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
      integral_normSq_dftSample_noise hε hk1 hkT]
  -- Rewrite the integrand as the difference of squared moduli.
  have hpt : ∀ ω : Ω, |periodogram (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) k
        - 2 * π * spectralDensityOf X μ ((fourierFreq T k : ℝ) : AddCircle (2 * π))
          * ((dftNoiseCos ε σ2 T k ω) ^ 2 + (dftNoiseSin ε σ2 T k ω) ^ 2) / 2|
      = |‖dftSample X T k ω‖ ^ 2 - ‖Γ * dftSample ε T k ω‖ ^ 2| := by
    intro ω
    congr 1
    simp only [periodogram, dftSample]
    rw [two_pi_spectralDensityOf_eq hε ha hmeas hfil, ← hΓ, norm_mul, mul_pow]
    rw [show ‖dft (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) (k : ℤ)‖ ^ 2
        = σ2 / 2 * ((dftNoiseCos ε σ2 T k ω) ^ 2 + (dftNoiseSin ε σ2 T k ω) ^ 2) from
      normSq_dftSample_noise ε hσ hT k ω]
    ring
  simp only [hpt]
  -- Pointwise: `|‖A‖² − ‖C‖²| ≤ δ‖C‖² + (1 + δ⁻¹)‖D‖²`.
  have hbound : ∀ ω : Ω, |‖dftSample X T k ω‖ ^ 2 - ‖Γ * dftSample ε T k ω‖ ^ 2|
      ≤ δ T * ‖Γ * dftSample ε T k ω‖ ^ 2
        + (1 + (δ T)⁻¹) * ‖dftSample X T k ω - Γ * dftSample ε T k ω‖ ^ 2 := by
    intro ω
    obtain ⟨A, hAe⟩ : ∃ A : ℝ, A = ‖dftSample X T k ω‖ := ⟨_, rfl⟩
    obtain ⟨C, hCe⟩ : ∃ C : ℝ, C = ‖Γ * dftSample ε T k ω‖ := ⟨_, rfl⟩
    obtain ⟨D, hDe⟩ : ∃ D : ℝ, D = ‖dftSample X T k ω - Γ * dftSample ε T k ω‖ := ⟨_, rfl⟩
    rw [← hAe, ← hCe, ← hDe]
    have hA0 : 0 ≤ A := by rw [hAe]; exact norm_nonneg _
    have hC0 : 0 ≤ C := by rw [hCe]; exact norm_nonneg _
    have hD0 : 0 ≤ D := by rw [hDe]; exact norm_nonneg _
    have hdiff : |A - C| ≤ D := by
      rw [hAe, hCe, hDe]; exact abs_norm_sub_norm_le _ _
    have hAle : A ≤ C + D := by
      have := abs_le.1 hdiff; linarith [this.2]
    have hkey : |A ^ 2 - C ^ 2| ≤ D * (2 * C + D) := by
      have h1 : A ^ 2 - C ^ 2 = (A - C) * (A + C) := by ring
      rw [h1, abs_mul]
      have h2 : |A + C| = A + C := abs_of_nonneg (by linarith)
      rw [h2]
      have h3 : A + C ≤ 2 * C + D := by linarith
      exact mul_le_mul hdiff h3 (by linarith) hD0
    have hamgm : 2 * C * D ≤ δ T * C ^ 2 + (δ T)⁻¹ * D ^ 2 := by
      have hδ := hδpos T
      have hkeyid : δ T * (δ T * C ^ 2 + (δ T)⁻¹ * D ^ 2 - 2 * C * D)
          = (δ T * C - D) ^ 2 := by field_simp; ring
      have hZ : 0 ≤ δ T * (δ T * C ^ 2 + (δ T)⁻¹ * D ^ 2 - 2 * C * D) := by
        rw [hkeyid]; exact sq_nonneg _
      nlinarith [hZ, hδ]
    calc |A ^ 2 - C ^ 2| ≤ D * (2 * C + D) := hkey
      _ = 2 * C * D + D ^ 2 := by ring
      _ ≤ (δ T * C ^ 2 + (δ T)⁻¹ * D ^ 2) + D ^ 2 := by linarith [hamgm]
      _ = δ T * C ^ 2 + (1 + (δ T)⁻¹) * D ^ 2 := by ring
    -- (the `calc` closes the goal after unfolding the abbreviations)
  have hgint : Integrable (fun ω => δ T * ‖Γ * dftSample ε T k ω‖ ^ 2
      + (1 + (δ T)⁻¹) * ‖dftSample X T k ω - Γ * dftSample ε T k ω‖ ^ 2) μ :=
    (hCint.const_mul (δ T)).add (hDint.const_mul (1 + (δ T)⁻¹))
  have hmono := integral_mono_of_nonneg
    (Eventually.of_forall fun ω => abs_nonneg
      (‖dftSample X T k ω‖ ^ 2 - ‖Γ * dftSample ε T k ω‖ ^ 2))
    hgint (Eventually.of_forall hbound)
  refine hmono.trans ?_
  rw [integral_add (hCint.const_mul (δ T)) (hDint.const_mul (1 + (δ T)⁻¹)),
    integral_const_mul, integral_const_mul, hCval]
  have hδ := hδpos T
  have h1 : δ T * (‖Γ‖ ^ 2 * σ2) ≤ δ T * (Ca ^ 2 * σ2) := by
    have hΓ2 : ‖Γ‖ ^ 2 ≤ Ca ^ 2 := by
      have := norm_nonneg Γ
      nlinarith [hΓle]
    have : ‖Γ‖ ^ 2 * σ2 ≤ Ca ^ 2 * σ2 := by nlinarith [hσ.le]
    exact mul_le_mul_of_nonneg_left this hδ.le
  have h2 : (1 + (δ T)⁻¹) * (∫ ω, ‖dftSample X T k ω - Γ * dftSample ε T k ω‖ ^ 2 ∂μ)
      ≤ e T + δ T := by
    have hDnn : 0 ≤ ∫ ω, ‖dftSample X T k ω - Γ * dftSample ε T k ω‖ ^ 2 ∂μ :=
      integral_nonneg fun ω => by positivity
    have hstep : (1 + (δ T)⁻¹)
        * (∫ ω, ‖dftSample X T k ω - Γ * dftSample ε T k ω‖ ^ 2 ∂μ)
        ≤ (1 + (δ T)⁻¹) * e T :=
      mul_le_mul_of_nonneg_left hDbd (by positivity)
    have hlast : (δ T)⁻¹ * e T ≤ δ T := by
      rw [inv_mul_le_iff₀ hδ]
      calc e T ≤ (δ T) ^ 2 := hδsq T
        _ = δ T * δ T := sq (δ T)
    nlinarith [hstep, hlast, hena T]
  linarith [h1, h2]

end StatLean.TimeSeries
