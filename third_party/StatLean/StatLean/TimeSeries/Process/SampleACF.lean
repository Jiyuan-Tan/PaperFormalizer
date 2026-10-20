module
public import StatLean.TimeSeries.ForMathlib.PosSemidefSequence
public import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
public import StatLean.TimeSeries.Models.Linear
public import StatLean.TimeSeries.Process.Stationary
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Normed.Group.Tannery

public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-!
# Sampling theory of the ACVF/ACF (FY §2.2.2, Theorem 2.8, eqs. (2.23)–(2.27))

Deterministic and asymptotic properties of the sample autocovariance `γ̂` and sample
autocorrelation `ρ̂` (divisor-`T`, mean-corrected — FY eq. (2.23), defined in
`Process/Defs.lean`):

* the divisor-`T` sample ACVF is a **positive semidefinite sequence** (FY §2.2.2's
  "may be shown" claim; false for the `1/(T−k)` divisor);
* **FY Theorem 2.8** for two-sided linear processes (eq. (2.24)) with IID innovations —
  (i) the sample-mean CLT [ledger-(a) debt: B&D §7.3 m-dependent route]. Parts (ii) and
  (iii), and FY eq. (2.27) which was proved from (iii), have been removed; see **Removed**
  below.

**Removed (2026-08-10, user directive).** The module's two sorried declarations, the
theorem proved from one of them, and six `private` helpers left with no surviving consumer
were deleted. Everything else — the positive-semidefiniteness of the sample ACVF, the whole
(R1)–(R4) reduction ledger with its Cesàro/covariance-kernel machinery, and all the
`acvf`/`acf` identities — is untouched and remains proved.
* `sampleACVF_zero_clt_debt` — FY Theorem 2.8(ii) (B&D 1991 Prop 7.3.4): the CLT for
  `γ̂(0)`, with the corrected limiting variance `(η − 3)γ(0)² + 2 Σ_{j∈ℤ} γ(j)²`.
* `sampleACF_bartlett_clt_debt` — FY Theorem 2.8(iii): **Bartlett's formula** (eq. (2.26))
  in Cramér–Wold form, `√T Σ_i c_i (ρ̂(i) − ρ(i)) →d N(0, cᵀ W c)` with `W = bartlettW`.
* `IsMA.sampleACF_clt` (**consumer**) — **FY eq. (2.27)**: for an MA(q) process and lag
  `j > q`, `√T ρ̂(j) →d N(0, 1 + 2Σ_{t=1}^q ρ(t)²)`, the basis of the ±1.96/√T confidence
  bands and the §3.4.4 ACF order-identification rule. Its proof consumed the Bartlett debt.
* `private`, proved, left without a consumer: the whole `Degenerate`/`Degenerate2` split-off
  of the `a ≡ 0` corner — `ae_eq_zero_of_filter_zero`, `acvf_eq_zero_of_ae_zero`,
  `acf_eq_zero_of_ae_zero`, `sampleACVF_ae_eq_zero`, `acvf_zero_pos_of_ne`,
  `bartlettW_eq_zero_of_ae_zero`.

`bartlettW` itself (FY eq. (2.26)) is **kept**: it is a public definition, not a helper.

Recover from `bdc8143f`.

**Misprint corrections (stated as provable, per project policy).**
* FY eq. (2.25) prints `ν₂² = 2σ⁴ Σ_j ρ(j)²`; dimensional analysis and
  B&D (1991) Prop 7.3.4 give `ν₂² = (η − 3)γ(0)² + 2 Σ_{j∈ℤ} γ(j)²` with
  `η = Eε⁴/σ⁴` — we state the corrected form.
* FY eq. (2.27) prints `1 + 2Σ_{t=1}^q ρ(q)²`; the correct summand is `ρ(t)²`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.2.2
(pp. 41–43), Theorem 2.8, eqs. (2.23)–(2.27). (`FY §2.2.2`.)

**Bibliographic comments.** Bartlett's formula is M. S. Bartlett (1946), *On the
theoretical specification and sampling properties of autocorrelated time-series*; the
modern proofs via m-dependent truncation are Brockwell & Davis (1991), §7.2–7.3
(Props 7.3.1–7.3.4, Thm 7.2.1). The psd property of the divisor-`T` estimator and its
failure for `1/(T−k)` are discussed in B&D (1991), §7.2 and Percival–Walden (1993).

The CLT statements are phrased through pointwise characteristic-function convergence
(Lévy-equivalent to convergence in distribution), matching the batch-A/B debt
conventions. The linear-process hypothesis is spelled as an explicit two-sided `L²`
partial-sum limit — definitionally `IsFilteredBy` (`Spectral/LinearFilter.lean`), which
this Process-layer file must not import.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Positive semidefiniteness of the divisor-`T` sample ACVF

The mechanism: write `y` for the mean-corrected data zero-padded to all of `ℤ`
(`padData`). The divisor-`T` sample ACVF is exactly the (un-normalized) autocorrelation
of this compactly supported sequence, `T·γ̂(k) = Σ_s y_s y_{s+k}` at *every* lag `k ∈ ℤ`
(`sum_padData_eq_rawACVF`) — this is where the divisor `T` rather than `T − k` is used,
and where the `1/(T−k)` estimator fails. The quadratic form then collapses to a sum of
squares, `Σ_{ij} a_i a_j γ̂(t_i − t_j) = T⁻¹ Σ_s (Σ_i a_i y_{s+t_i})² ≥ 0`. -/

/-- The mean-corrected data vector as a function on `ℕ`, junk `0` outside the window. -/
private noncomputable def padNat {T : ℕ} (x : Fin T → ℝ) (n : ℕ) : ℝ :=
  if h : n < T then x ⟨n, h⟩ - sampleMean x else 0

/-- The mean-corrected data vector, zero-padded to all of `ℤ`. -/
private noncomputable def padData {T : ℕ} (x : Fin T → ℝ) (s : ℤ) : ℝ :=
  if h : 0 ≤ s ∧ s.toNat < T then x ⟨s.toNat, h.2⟩ - sampleMean x else 0

/-- The un-normalized (divisor-free) sample ACVF: the inner sum of `sampleACVF`. -/
private noncomputable def rawACVF {T : ℕ} (x : Fin T → ℝ) (k : ℕ) : ℝ :=
  ∑ t : Fin T, if h : (t : ℕ) + k < T then
    (x t - sampleMean x) * (x ⟨(t : ℕ) + k, h⟩ - sampleMean x) else 0

private lemma sampleACVF_eq_raw {T : ℕ} (x : Fin T → ℝ) (k : ℕ) :
    sampleACVF x k = (T : ℝ)⁻¹ * rawACVF x k := rfl

/-- `padData` is supported in the data window `[0, T)`. -/
private lemma padData_eq_zero {T : ℕ} (x : Fin T → ℝ) {s : ℤ}
    (hs : s ∉ Finset.Ico (0 : ℤ) (T : ℤ)) : padData x s = 0 := by
  rw [padData, dif_neg]
  simp only [Finset.mem_Ico, not_and, not_lt] at hs
  rintro ⟨h1, h2⟩
  have := hs h1
  omega

private lemma padData_of_nonneg {T : ℕ} (x : Fin T → ℝ) {s : ℤ} (hs : 0 ≤ s) :
    padData x s = padNat x s.toNat := by
  rw [padData, padNat]
  by_cases h : s.toNat < T
  · rw [dif_pos ⟨hs, h⟩, dif_pos h]
  · rw [dif_neg (fun hc => h hc.2), dif_neg h]

private lemma rawACVF_eq_range {T : ℕ} (x : Fin T → ℝ) (m : ℕ) :
    rawACVF x m = ∑ n ∈ Finset.range T, padNat x n * padNat x (n + m) := by
  rw [rawACVF, ← Fin.sum_univ_eq_sum_range (fun n => padNat x n * padNat x (n + m)) T]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : padNat x (i : ℕ) = x i - sampleMean x := by
    rw [padNat, dif_pos i.isLt]
  rw [h1, padNat]
  by_cases h2 : (i : ℕ) + m < T
  · rw [dif_pos h2, dif_pos h2]
  · rw [dif_neg h2, dif_neg h2, mul_zero]

/-- At a nonnegative lag the window sum over `[0, T)` is the raw sample ACVF. -/
private lemma sum_padData_ico {T : ℕ} (x : Fin T → ℝ) (m : ℕ) :
    ∑ s ∈ Finset.Ico (0 : ℤ) (T : ℤ), padData x s * padData x (s + (m : ℤ))
      = rawACVF x m := by
  rw [rawACVF_eq_range]
  refine Finset.sum_nbij' (fun s => s.toNat) (fun n => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_Ico] at hs; simp only [Finset.mem_range]; omega
  · intro n hn; simp only [Finset.mem_range] at hn; simp only [Finset.mem_Ico]; omega
  · intro s hs; simp only [Finset.mem_Ico] at hs; omega
  · intro n hn; simp only [Finset.mem_range] at hn; omega
  · intro s hs
    simp only [Finset.mem_Ico] at hs
    rw [padData_of_nonneg x (by omega), padData_of_nonneg x (by omega)]
    congr 2
    omega

/-- The window may be enlarged freely: the padding kills every extra term. -/
private lemma sum_padData_window {T : ℕ} (x : Fin T → ℝ) (k : ℤ) {S : Finset ℤ}
    (hS : Finset.Ico (0 : ℤ) (T : ℤ) ⊆ S) :
    ∑ s ∈ S, padData x s * padData x (s + k)
      = ∑ s ∈ Finset.Ico (0 : ℤ) (T : ℤ), padData x s * padData x (s + k) :=
  (Finset.sum_subset hS fun s _ hs => by rw [padData_eq_zero x hs, zero_mul]).symm

/-- The window sum is even in the lag (reindex by the lag, on a window large enough to
absorb the shift). -/
private lemma sum_padData_symm {T : ℕ} (x : Fin T → ℝ) (k : ℤ) :
    ∑ s ∈ Finset.Ico (0 : ℤ) (T : ℤ), padData x s * padData x (s + k)
      = ∑ s ∈ Finset.Ico (0 : ℤ) (T : ℤ), padData x s * padData x (s + -k) := by
  obtain ⟨K, hK1, hK2⟩ : ∃ K : ℤ, -K ≤ k ∧ k ≤ K := ⟨|k|, neg_abs_le k, le_abs_self k⟩
  have hsub1 : Finset.Ico (0 : ℤ) (T : ℤ) ⊆ Finset.Ico (-K) ((T : ℤ) + K) := by
    intro s hs; simp only [Finset.mem_Ico] at *; omega
  have hsub2 : Finset.Ico (0 : ℤ) (T : ℤ) ⊆ Finset.Ico (-K + k) ((T : ℤ) + K + k) := by
    intro s hs; simp only [Finset.mem_Ico] at *; omega
  rw [← sum_padData_window x k hsub1, ← sum_padData_window x (-k) hsub2]
  refine Finset.sum_nbij' (fun s => s + k) (fun u => u - k) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_Ico] at *; omega
  · intro u hu; simp only [Finset.mem_Ico] at *; omega
  · intro s _; ring
  · intro u _; ring
  · intro s _; rw [show s + k + -k = s from by ring, mul_comm]

/-- **The key deterministic identity**: at *every* integer lag, the raw divisor-`T`
sample ACVF is the window sum `Σ_s y_s y_{s+k}` of the zero-padded mean-corrected data. -/
private lemma sum_padData_eq_rawACVF {T : ℕ} (x : Fin T → ℝ) (k : ℤ) {S : Finset ℤ}
    (hS : Finset.Ico (0 : ℤ) (T : ℤ) ⊆ S) :
    ∑ s ∈ S, padData x s * padData x (s + k) = rawACVF x k.natAbs := by
  rw [sum_padData_window x k hS]
  by_cases hk : 0 ≤ k
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
    rw [show ((m : ℤ)).natAbs = m from by omega]
    exact sum_padData_ico x m
  · rw [sum_padData_symm x k]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, -k = (m : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [hm, show k.natAbs = m from by omega]
    exact sum_padData_ico x m

/-- The shifted form of `sum_padData_eq_rawACVF`, on an explicit integer window. -/
private lemma sum_padData_shift {T : ℕ} (x : Fin T → ℝ) (b k A B : ℤ)
    (hA : A + b ≤ 0) (hB : (T : ℤ) ≤ B + b) :
    ∑ s ∈ Finset.Ico A B, padData x (s + b) * padData x (s + b + k) = rawACVF x k.natAbs := by
  rw [← sum_padData_eq_rawACVF x k (S := Finset.Ico (A + b) (B + b))
      (by intro s hs; simp only [Finset.mem_Ico] at *; omega)]
  refine Finset.sum_nbij' (fun s => s + b) (fun u => u - b) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_Ico] at *; omega
  · intro u hu; simp only [Finset.mem_Ico] at *; omega
  · intro s _; ring
  · intro u _; ring
  · intro s _; rfl

/-- **FY §2.2.2 (eq. (2.23) claim)**: the divisor-`T` sample ACVF, extended evenly to
`ℤ` (it vanishes at lags `≥ T`), is a positive semidefinite sequence — the property
that fails for the `1/(T−k)` divisor. Deterministic. -/
theorem isPosSemidefSeq_sampleACVF {T : ℕ} (x : Fin T → ℝ) :
    IsPosSemidefSeq fun k : ℤ => sampleACVF x k.natAbs := by
  intro n t a
  -- a bound on the time points, giving one window `[−M, T+M)` that carries every shift
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ i, -M ≤ t i ∧ t i ≤ M := by
    refine ⟨∑ i, |t i|, fun i => ?_⟩
    have h1 : |t i| ≤ ∑ i, |t i| :=
      Finset.single_le_sum (f := fun i => |t i|) (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
    have h2 := neg_abs_le (t i)
    have h3 := le_abs_self (t i)
    omega
  -- each entry of the quadratic form is a window sum of the padded data
  have key : ∀ i j : Fin n,
      sampleACVF x (t i - t j).natAbs
        = (T : ℝ)⁻¹ * ∑ s ∈ Finset.Ico (-M) ((T : ℤ) + M),
            padData x (s + t i) * padData x (s + t j) := by
    intro i j
    rw [sampleACVF_eq_raw]
    congr 1
    rw [← sum_padData_shift x (t j) (t i - t j) (-M) ((T : ℤ) + M)
      (by have := hM j; omega) (by have := hM j; omega)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show s + t j + (t i - t j) = s + t i from by ring, mul_comm]
  -- the quadratic form is a sum of squares
  have main : (T : ℝ)⁻¹ * ∑ s ∈ Finset.Ico (-M) ((T : ℤ) + M),
        (∑ i, a i * padData x (s + t i)) ^ 2
      = ∑ i, ∑ j, a i * a j * sampleACVF x (t i - t j).natAbs := by
    have e1 : ∀ s : ℤ, (∑ i, a i * padData x (s + t i)) ^ 2
        = ∑ i, ∑ j, (a i * padData x (s + t i)) * (a j * padData x (s + t j)) := by
      intro s; rw [sq, Fintype.sum_mul_sum]
    calc (T : ℝ)⁻¹ * ∑ s ∈ Finset.Ico (-M) ((T : ℤ) + M),
            (∑ i, a i * padData x (s + t i)) ^ 2
        = (T : ℝ)⁻¹ * ∑ s ∈ Finset.Ico (-M) ((T : ℤ) + M), ∑ i, ∑ j,
            (a i * padData x (s + t i)) * (a j * padData x (s + t j)) := by
          rw [Finset.sum_congr rfl (fun s _ => e1 s)]
      _ = (T : ℝ)⁻¹ * ∑ i, ∑ j, ∑ s ∈ Finset.Ico (-M) ((T : ℤ) + M),
            (a i * padData x (s + t i)) * (a j * padData x (s + t j)) := by
          congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, a i * a j * sampleACVF x (t i - t j).natAbs := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [key i j, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
  rw [← main]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun s _ => sq_nonneg _)

/-! ### The MA(q) second-order structure

The MA(q) recurrence is a single finite lag combination `X_t = Σ_{i≤q} c_i ε_{t−i}` of the
innovations, with the coefficient vector `c = (1, a₁, …, a_q)` independent of `t`. All the
second-order facts below (stationarity, `γ(0)`) are read off the one bilinear covariance
computation `cov_eq_of_ma`, whose value depends on `(s, t)` only through `s − t`. -/

/-- Covariance only sees the a.e. class of each argument (private copy of the
`Models/Linear.lean` helper). -/
private lemma covariance_congr_ae {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIX : ∫ x, X x ∂μ = ∫ x, X' x ∂μ := integral_congr_ae hX
  have hIY : ∫ x, Y x ∂μ = ∫ x, Y' x ∂μ := integral_congr_ae hY
  simp only [covariance, hIX, hIY]
  exact integral_congr_ae (by filter_upwards [hX, hY] with ω h1 h2 using by rw [h1, h2])

/-- The MA(q) coefficient vector `(1, a₁, …, a_q)`. -/
private def maCoeff {q : ℕ} (a : Fin q → ℝ) : Fin (q + 1) → ℝ := Fin.cases 1 a

private lemma maCoeff_zero {q : ℕ} (a : Fin q → ℝ) : maCoeff a 0 = 1 := rfl

private lemma maCoeff_succ {q : ℕ} (a : Fin q → ℝ) (i : Fin q) : maCoeff a i.succ = a i := rfl

/-- The MA(q) recurrence packaged as a single lag combination with a `t`-independent
coefficient vector. -/
private lemma IsMA.rec_sum {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsMA a σ2 X ε μ) (u : ℤ) :
    X u =ᵐ[μ] fun ω => ∑ i : Fin (q + 1), maCoeff a i * ε (u - ((i : ℕ) : ℤ)) ω := by
  have hlag : ∀ i : Fin q, u - ((((i.succ : Fin (q + 1)) : ℕ) : ℤ)) = u - 1 - ((i : ℕ) : ℤ) := by
    intro i; rw [Fin.val_succ]; push_cast; ring
  filter_upwards [h.recurrence u] with ω hω
  rw [hω, Fin.sum_univ_succ]
  simp only [maCoeff_zero, maCoeff_succ, Fin.val_zero, Nat.cast_zero, sub_zero, one_mul,
    hlag, Finset.univ_eq_empty, Finset.sum_empty, zero_add]

/-- Bilinear expansion of the covariance of two finite linear combinations of white noise:
only coinciding time indices contribute, each with weight `σ²`. -/
private lemma cov_noise_comb [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hw : IsWhiteNoise ε σ2 μ) {n m : ℕ} (c : Fin n → ℝ) (d : Fin m → ℝ)
    (u : Fin n → ℤ) (v : Fin m → ℤ) :
    cov[fun ω => ∑ i, c i * ε (u i) ω, fun ω => ∑ j, d j * ε (v j) ω; μ]
      = ∑ i, ∑ j, if u i = v j then c i * d j * σ2 else 0 := by
  rw [covariance_fun_sum_fun_sum (X := fun i ω => c i * ε (u i) ω)
      (Y := fun j ω => d j * ε (v j) ω)
      (fun i => (hw.memLp (u i)).const_mul (c i))
      (fun j => (hw.memLp (v j)).const_mul (d j))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  by_cases hij : u i = v j
  · rw [if_pos hij, hij, covariance_self (hw.memLp (v j)).aestronglyMeasurable.aemeasurable,
      hw.variance_eq]
    ring
  · rw [if_neg hij, hw.uncorrelated _ _ hij]
    ring

/-- The general two-time MA(q) covariance: a finite sum over the coinciding lag pairs. -/
private lemma IsMA.cov_eq_of_ma [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) (s t : ℤ) :
    cov[X s, X t; μ]
      = ∑ i : Fin (q + 1), ∑ j : Fin (q + 1),
          if s - ((i : ℕ) : ℤ) = t - ((j : ℕ) : ℤ) then maCoeff a i * maCoeff a j * σ2 else 0 := by
  rw [covariance_congr_ae (h.rec_sum s) (h.rec_sum t)]
  exact cov_noise_comb h.whiteNoise _ _ _ _

/-- Each MA(q) marginal is in `L²`. -/
private lemma IsMA.memLp_two [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) (t : ℤ) : MemLp (X t) 2 μ :=
  MemLp.ae_eq (h.rec_sum t).symm
    (memLp_finset_sum Finset.univ fun i _ =>
      (h.whiteNoise.memLp (t - ((i : ℕ) : ℤ))).const_mul (maCoeff a i))

/-- The MA(q) mean is zero at every time. -/
private lemma IsMA.integral_eq_zero [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) (t : ℤ) : ∫ ω, X t ω ∂μ = 0 := by
  rw [integral_congr_ae (h.rec_sum t),
    integral_finset_sum (Finset.univ : Finset (Fin (q + 1))) (fun (i : Fin (q + 1)) _ =>
      ((h.whiteNoise.memLp (t - ((i : ℕ) : ℤ))).integrable one_le_two).const_mul (maCoeff a i))]
  simp [integral_const_mul, h.whiteNoise.integral_eq_zero]

/-- An MA(q) process (finite MA of white noise) is weakly stationary. (Stated here for
the (2.27) assembly; candidate for promotion to `Models/Linear.lean`.) -/
theorem IsMA.isStationary [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) (hmeas : ∀ t, Measurable (X t)) :
    IsStationary X μ := by
  refine ⟨h.memLp_two, fun s t => by rw [h.integral_eq_zero s, h.integral_eq_zero t],
    fun t k => ?_⟩
  rw [h.cov_eq_of_ma (t + k) t, h.cov_eq_of_ma k 0]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  refine if_congr ⟨fun hc => by omega, fun hc => by omega⟩ rfl rfl

/-- The MA(q) lag-0 autocovariance: `γ(0) = σ²(1 + Σ_j a_j²)` (FY eq. (2.18)
specialized; positivity of `γ(0)` for `σ² > 0` follows). -/
theorem IsMA.acvf_zero_eq [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) :
    acvf X μ 0 = σ2 * (1 + ∑ j, a j ^ 2) := by
  rw [acvf, h.cov_eq_of_ma 0 0]
  have hdiag : ∀ i j : Fin (q + 1),
      ((0 : ℤ) - ((i : ℕ) : ℤ) = 0 - ((j : ℕ) : ℤ)) ↔ i = j := by
    intro i j
    constructor
    · intro hc; exact Fin.val_injective (by omega)
    · rintro rfl; rfl
  have hinner : ∀ i : Fin (q + 1),
      (∑ j : Fin (q + 1),
        if (0 : ℤ) - ((i : ℕ) : ℤ) = 0 - ((j : ℕ) : ℤ) then maCoeff a i * maCoeff a j * σ2 else 0)
        = maCoeff a i * maCoeff a i * σ2 := by
    intro i
    rw [Finset.sum_congr rfl (fun j _ =>
      if_congr (hdiag i j) rfl rfl), Finset.sum_ite_eq Finset.univ i]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hinner i), Fin.sum_univ_succ]
  simp only [maCoeff_zero, maCoeff_succ, one_mul, mul_add, mul_one, Finset.mul_sum]
  refine congrArg (fun z => σ2 + z) (Finset.sum_congr rfl fun i _ => by ring)

/-! ## The sample-mean CLT (FY Theorem 2.8(i))

The route is the truncation route of B&D §7.3, but the m-dependent blocking step is
*unnecessary*: for a **finite** filter window the partial sum `Σ_{t≤T} Σ_{|k|≤N} a_k ε_{t−k}`
regroups (`sum_window_swap`) into `Σ_n c_{n,T} ε_{n+1−N}`, an exactly weighted sum of
**independent** innovations, so the Lindeberg triangular-array CLT applies directly. The
window coefficients equal `Σ_{|k|≤N} a_k` on the bulk and are uniformly bounded on the
`4N` boundary indices, giving the row-variance limit `σ²(Σ_{|k|≤N} a_k)²`. The truncation
level is then removed by an `L²` defect bound that is **uniform in `T`**: the `ℓ¹` energy
budget `Σ_n c_n² ≤ (max_n |c_n|)(Σ_n |c_n|) ≤ B · (T B)` converts the `ℓ¹` tail mass
`B = Σ_{|k|>N}|a_k|` of the filter into `‖·‖₂ ≤ √σ² B`, free of `T`. A three-`ε`
characteristic-function argument closes the double limit. -/

/-- The weight attached to the innovation `ε_{n+1−M}` when the window-`M` truncated
filter is summed over the data window `t = 1, …, T`. -/
private noncomputable def winCoef (b : ℤ → ℝ) (T M n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
    if 1 ≤ (n : ℤ) + 1 - (M : ℤ) + k ∧ (n : ℤ) + 1 - (M : ℤ) + k ≤ (T : ℤ) then b k else 0

/-- **The window swap**: summing a window-`M` finite filter over the data window
`t = 1, …, T` regroups it as a weighted sum of the *inputs* `F(n + 1 − M)`,
`n = 0, …, T + 2M − 1`. Deterministic; used with `F = ε · ω` and with `F = 1`. -/
private lemma sum_window_swap (b : ℤ → ℝ) (F : ℤ → ℝ) (T M : ℕ) :
    ∑ t ∈ Finset.range T, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), b k * F ((t : ℤ) + 1 - k)
      = ∑ n ∈ Finset.range (T + 2 * M), winCoef b T M n * F ((n : ℤ) + 1 - (M : ℤ)) := by
  classical
  have hR : ∀ n ∈ Finset.range (T + 2 * M),
      winCoef b T M n * F ((n : ℤ) + 1 - (M : ℤ))
        = ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            (if 1 ≤ (n : ℤ) + 1 - (M : ℤ) + k ∧ (n : ℤ) + 1 - (M : ℤ) + k ≤ (T : ℤ) then
              b k * F ((n : ℤ) + 1 - (M : ℤ)) else 0) := by
    intro n _
    rw [winCoef, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by split <;> simp
  rw [Finset.sum_congr rfl hR, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = (M : ℤ) - k := ⟨((M : ℤ) - k).toNat, by omega⟩
  have hdle : d ≤ 2 * M := by omega
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun t => t + d) (fun n => n - d) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_range] at ht
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_, ?_⟩ <;> push_cast <;> omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_range]
    have h1 : (1 : ℤ) ≤ (n : ℤ) + 1 - (M : ℤ) + k := hn.2.1
    have h2 : (n : ℤ) + 1 - (M : ℤ) + k ≤ (T : ℤ) := hn.2.2
    omega
  · intro t _; omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    have h1 : (1 : ℤ) ≤ (n : ℤ) + 1 - (M : ℤ) + k := hn.2.1
    omega
  · intro t ht
    congr 2
    push_cast
    omega

/-- Each window weight is bounded by the total mass of the filter. -/
private lemma abs_winCoef_le (b : ℤ → ℝ) (T M n : ℕ) :
    |winCoef b T M n| ≤ ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |b k| := by
  rw [winCoef]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  split
  · exact le_rfl
  · simp

/-- The window weights have total mass at most `T ·Σ|b|`: the `ℓ¹` energy budget. -/
private lemma sum_abs_winCoef_le (b : ℤ → ℝ) (T M : ℕ) :
    ∑ n ∈ Finset.range (T + 2 * M), |winCoef b T M n|
      ≤ (T : ℝ) * ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |b k| := by
  have habs : ∀ n, |winCoef b T M n| ≤ winCoef (fun k => |b k|) T M n := by
    intro n
    rw [winCoef, winCoef]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    split
    · exact le_rfl
    · simp
  have hswap := sum_window_swap (fun k => |b k|) (fun _ => (1 : ℝ)) T M
  simp only [mul_one] at hswap
  calc ∑ n ∈ Finset.range (T + 2 * M), |winCoef b T M n|
      ≤ ∑ n ∈ Finset.range (T + 2 * M), winCoef (fun k => |b k|) T M n :=
        Finset.sum_le_sum fun n _ => habs n
    _ = ∑ t ∈ Finset.range T, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |b k| := hswap.symm
    _ = (T : ℝ) * ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |b k| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- A finite weighted sum of *distinct* white-noise coordinates is in `L²`. -/
private lemma memLp_weighted_noise [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hw : IsWhiteNoise ε σ2 μ) {K : ℕ} (c : Fin K → ℝ) (g : Fin K → ℤ) :
    MemLp (fun ω => ∑ i, c i * ε (g i) ω) 2 μ :=
  memLp_finset_sum Finset.univ fun i _ => (hw.memLp (g i)).const_mul (c i)

/-- **The second-moment identity** for a weighted sum of distinct white-noise
coordinates: `E(Σ cᵢ ε_{gᵢ})² = σ² Σ cᵢ²`. -/
private lemma integral_sq_weighted_noise [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hw : IsWhiteNoise ε σ2 μ) {K : ℕ} (c : Fin K → ℝ) (g : Fin K → ℤ)
    (hg : Function.Injective g) :
    ∫ ω, (∑ i, c i * ε (g i) ω) ^ 2 ∂μ = σ2 * ∑ i, (c i) ^ 2 := by
  have hmem : MemLp (fun ω => ∑ i, c i * ε (g i) ω) 2 μ := memLp_weighted_noise hw c g
  have hmean : ∫ ω, (∑ i, c i * ε (g i) ω) ∂μ = 0 := by
    rw [integral_finset_sum Finset.univ fun i _ =>
      ((hw.memLp (g i)).integrable one_le_two).const_mul (c i)]
    simp [integral_const_mul, hw.integral_eq_zero]
  have hvar : variance (fun ω => ∑ i, c i * ε (g i) ω) μ = σ2 * ∑ i, (c i) ^ 2 := by
    rw [← covariance_self hmem.aestronglyMeasurable.aemeasurable, cov_noise_comb hw c c g g]
    have hinner : ∀ i : Fin K,
        (∑ j, if g i = g j then c i * c j * σ2 else 0) = c i * c i * σ2 := by
      intro i
      rw [Finset.sum_congr rfl (fun j _ =>
        if_congr ⟨fun hc => hg hc, fun hc => by rw [hc]⟩ rfl rfl),
        Finset.sum_ite_eq Finset.univ i]
      simp
    rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have := variance_eq_sub hmem
  rw [hvar, hmean] at this
  simp only [Pi.pow_apply] at this
  linarith [this]

/-- **CLT for weighted sums of an i.i.d. sequence** (charFun form). The rows are
`X_{n,i} = w_{n,i} Y_i`; the row-variance limit `v` and the individual negligibility of
the weights are the only inputs beyond the sampling law. -/
private lemma tendsto_charFun_weighted_iid' [IsProbabilityMeasure μ]
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

/-! ### `L²` bookkeeping and the characteristic-function comparison -/

/-- `L²` control from a second-moment bound. -/
private lemma eLpNorm_two_le_of_integral_sq_le {f : Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : MemLp f 2 μ) (h : ∫ ω, f ω ^ 2 ∂μ ≤ C ^ 2) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal C := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpow : ∀ ω, ‖f ω‖ ^ ((2 : ENNReal).toReal) = f ω ^ 2 := by
    intro ω
    rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, sq_abs]
  rw [integral_congr_ae (Eventually.of_forall hpow),
    show ((2 : ENNReal).toReal)⁻¹ = 1 / (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  calc Real.sqrt (∫ ω, f ω ^ 2 ∂μ) ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt h
    _ = C := Real.sqrt_sq hC

/-- On a probability space an `L²` bound controls the `L¹` norm. -/
private lemma integral_abs_le_of_eLpNorm_two [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : AEStronglyMeasurable f μ) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal C) :
    ∫ ω, |f ω| ∂μ ≤ C := by
  have h1 : ∫ ω, |f ω| ∂μ = (∫⁻ ω, ‖f ω‖ₑ ∂μ).toReal := by
    simpa [Real.norm_eq_abs] using integral_norm_eq_lintegral_enorm hf
  have h2 : eLpNorm f 1 μ ≤ ENNReal.ofReal C :=
    le_trans (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hf) h
  rw [eLpNorm_one_eq_lintegral_enorm] at h2
  rw [h1]
  calc (∫⁻ ω, ‖f ω‖ₑ ∂μ).toReal ≤ (ENNReal.ofReal C).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    _ = C := ENNReal.toReal_ofReal hC

/-- charFun of a pushforward, as an integral on the base space. -/
private lemma charFun_map_eq_integral' {f : Ω → ℝ} (hf : AEMeasurable f μ) (u : ℝ) :
    charFun (μ.map f) u = ∫ ω, Complex.exp (Complex.I * (u * f ω : ℝ)) ∂μ := by
  rw [charFun_apply_real, integral_map hf (by fun_prop)]
  simp only [Complex.ofReal_mul]
  congr 1 with ω
  ring_nf

private lemma integrable_cexp_mul_I' [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) :
    Integrable (fun ω => Complex.exp (Complex.I * (f ω : ℝ))) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (Complex.measurable_exp.comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with ω
  simp [Complex.norm_exp]

/-- **The `L¹` charFun comparison**: `‖E e^{iuZ} − E e^{iuW}‖ ≤ |u| E|Z − W|`. -/
private lemma norm_charFun_map_sub_le [IsProbabilityMeasure μ] {Z W : Ω → ℝ}
    (hZ : Measurable Z) (hW : Measurable W)
    (hint : Integrable (fun ω => |Z ω - W ω|) μ) (u : ℝ) :
    ‖charFun (μ.map Z) u - charFun (μ.map W) u‖ ≤ |u| * ∫ ω, |Z ω - W ω| ∂μ := by
  rw [charFun_map_eq_integral' hZ.aemeasurable u, charFun_map_eq_integral' hW.aemeasurable u,
    ← integral_sub (integrable_cexp_mul_I' (hZ.const_mul u))
      (integrable_cexp_mul_I' (hW.const_mul u))]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [show |u| * ∫ ω, |Z ω - W ω| ∂μ = ∫ ω, |u| * |Z ω - W ω| ∂μ from
    (integral_const_mul _ _).symm]
  refine integral_mono (((integrable_cexp_mul_I' (hZ.const_mul u)).sub
    (integrable_cexp_mul_I' (hW.const_mul u))).norm) (hint.const_mul _) fun ω => ?_
  have hfact : Complex.exp (Complex.I * ((u * Z ω : ℝ)))
        - Complex.exp (Complex.I * ((u * W ω : ℝ)))
      = Complex.exp (Complex.I * ((u * W ω : ℝ))) *
        (Complex.exp (Complex.I * ((u * Z ω - u * W ω : ℝ))) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hfact, norm_mul,
    show ‖Complex.exp (Complex.I * ((u * W ω : ℝ)))‖ = 1 from by simp [Complex.norm_exp], one_mul]
  refine le_trans (by simpa using
      Real.norm_exp_I_mul_ofReal_sub_one_le (x := u * Z ω - u * W ω)) ?_
  rw [show u * Z ω - u * W ω = u * (Z ω - W ω) from by ring, abs_mul]

/-! ### The truncated-filter CLT

For a *finite* filter window the partial sum over `t = 1, …, T` is, after the window swap,
an exactly weighted sum of **independent** innovations — no blocking is needed. The row
weights are `T^{-1/2}` times the window coefficients, which equal `Σ_{|k|≤N} a_k` on the
bulk `2N ≤ n < T` and are bounded by `Σ_{|k|≤N}|a_k|` on the `4N` boundary indices. -/

private lemma tendsto_charFun_truncSum [IsProbabilityMeasure μ] {a : ℤ → ℝ} {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2) (N : ℕ) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T,
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (σ2 * (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) ^ 2))) u)) := by
  classical
  have hwn := hε.isWhiteNoise
  obtain ⟨AN, hAN⟩ : ∃ x : ℝ, x = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k := ⟨_, rfl⟩
  obtain ⟨AA, hAA⟩ : ∃ x : ℝ, x = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k| := ⟨_, rfl⟩
  have hAAnn : 0 ≤ AA := by rw [hAA]; exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have hginj : Function.Injective fun n : ℕ => (n : ℤ) + 1 - (N : ℤ) := by
    intro p q hpq; simpa using hpq
  -- the innovation reindex `Y n = ε_{n+1−N}`
  have hidentY : ∀ n : ℕ, IdentDistrib (ε ((n : ℤ) + 1 - (N : ℤ)))
      (ε (((0 : ℕ) : ℤ) + 1 - (N : ℤ))) μ μ := fun n => hε.identDistrib _ _
  -- the row weights
  have hsqinv : ∀ T : ℕ, ((Real.sqrt (T : ℝ))⁻¹) ^ 2 = ((T : ℝ))⁻¹ := by
    intro T
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg T)]
  have hrow : ∀ T : ℕ,
      (∑ i : Fin (T + 2 * N), ((Real.sqrt (T : ℝ))⁻¹ * winCoef a T N (i : ℕ)) ^ 2)
        = ((T : ℝ))⁻¹ * ∑ n ∈ Finset.range (T + 2 * N), (winCoef a T N n) ^ 2 := by
    intro T
    rw [Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range
        (fun n => ((T : ℝ))⁻¹ * (winCoef a T N n) ^ 2) (T + 2 * N)]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, hsqinv T]
  -- the bulk value of the window coefficients
  have hbulk : ∀ T n : ℕ, 2 * N ≤ n → n < T → winCoef a T N n = AN := by
    intro T n h1 h2
    rw [winCoef, hAN]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    exact if_pos ⟨by omega, by omega⟩
  have hbdd : ∀ T n : ℕ, (winCoef a T N n) ^ 2 ≤ AA ^ 2 := by
    intro T n
    have h1 : |winCoef a T N n| ≤ AA := by rw [hAA]; exact abs_winCoef_le a T N n
    calc (winCoef a T N n) ^ 2 = |winCoef a T N n| ^ 2 := (sq_abs _).symm
      _ ≤ AA ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  -- the two-sided bulk/boundary estimate
  have hsand : ∀ T : ℕ, 2 * N ≤ T →
      ((T : ℝ) - 2 * N) * AN ^ 2
          ≤ ∑ n ∈ Finset.range (T + 2 * N), (winCoef a T N n) ^ 2 ∧
        ∑ n ∈ Finset.range (T + 2 * N), (winCoef a T N n) ^ 2
          ≤ ((T : ℝ) - 2 * N) * AN ^ 2 + 4 * N * AA ^ 2 := by
    intro T hT
    have hsub : Finset.Ico (2 * N) T ⊆ Finset.range (T + 2 * N) := by
      intro n hn
      simp only [Finset.mem_Ico] at hn
      simp only [Finset.mem_range]
      omega
    have hsplit := Finset.sum_sdiff (f := fun n => (winCoef a T N n) ^ 2) hsub
    have hIco : ∑ n ∈ Finset.Ico (2 * N) T, (winCoef a T N n) ^ 2
        = ((T : ℝ) - 2 * N) * AN ^ 2 := by
      rw [Finset.sum_congr rfl (fun n hn => by
          simp only [Finset.mem_Ico] at hn
          rw [hbulk T n hn.1 hn.2]), Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      congr 1
      have : ((T - 2 * N : ℕ) : ℝ) = (T : ℝ) - 2 * N := by
        push_cast [Nat.cast_sub hT]; ring
      rw [this]
    have hbdcard : (Finset.range (T + 2 * N) \ Finset.Ico (2 * N) T).card = 4 * N := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, Finset.card_range, Nat.card_Ico]
      omega
    have hbd1 : (0 : ℝ)
        ≤ ∑ n ∈ Finset.range (T + 2 * N) \ Finset.Ico (2 * N) T, (winCoef a T N n) ^ 2 :=
      Finset.sum_nonneg fun n _ => sq_nonneg _
    have hbd2 : ∑ n ∈ Finset.range (T + 2 * N) \ Finset.Ico (2 * N) T, (winCoef a T N n) ^ 2
        ≤ 4 * N * AA ^ 2 := by
      calc ∑ n ∈ Finset.range (T + 2 * N) \ Finset.Ico (2 * N) T, (winCoef a T N n) ^ 2
          ≤ ∑ _n ∈ Finset.range (T + 2 * N) \ Finset.Ico (2 * N) T, AA ^ 2 :=
            Finset.sum_le_sum fun n _ => hbdd T n
        _ = 4 * N * AA ^ 2 := by
            rw [Finset.sum_const, hbdcard, nsmul_eq_mul]
            push_cast
            ring
    exact ⟨by linarith, by linarith⟩
  -- the row-variance limit
  have hTinv : Tendsto (fun T : ℕ => ((T : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hS0 : Tendsto (fun T : ℕ =>
      ((T : ℝ))⁻¹ * ∑ n ∈ Finset.range (T + 2 * N), (winCoef a T N n) ^ 2 - AN ^ 2)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      (by simpa using hTinv.mul_const (2 * (N : ℝ) * AN ^ 2 + 4 * (N : ℝ) * AA ^ 2))
    filter_upwards [eventually_ge_atTop (max 1 (2 * N))] with T hT
    have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
    have hT2 : 2 * N ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
    have hinvnn : (0 : ℝ) ≤ ((T : ℝ))⁻¹ := by positivity
    obtain ⟨h1, h2⟩ := hsand T hT2
    have hkey : ((T : ℝ))⁻¹ * ((T : ℝ) - 2 * N) = 1 - 2 * (N : ℝ) * ((T : ℝ))⁻¹ := by
      field_simp
    have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
    have hL' : ((T : ℝ))⁻¹ * (((T : ℝ) - 2 * (N : ℝ)) * AN ^ 2)
        = AN ^ 2 - 2 * (N : ℝ) * ((T : ℝ))⁻¹ * AN ^ 2 := by field_simp
    have hU' : ((T : ℝ))⁻¹ * ((((T : ℝ) - 2 * (N : ℝ)) * AN ^ 2) + 4 * (N : ℝ) * AA ^ 2)
        = AN ^ 2 - 2 * (N : ℝ) * ((T : ℝ))⁻¹ * AN ^ 2
          + ((T : ℝ))⁻¹ * (4 * (N : ℝ) * AA ^ 2) := by field_simp
    have hR' : ((T : ℝ))⁻¹ * (2 * (N : ℝ) * AN ^ 2 + 4 * (N : ℝ) * AA ^ 2)
        = 2 * (N : ℝ) * ((T : ℝ))⁻¹ * AN ^ 2
          + ((T : ℝ))⁻¹ * (4 * (N : ℝ) * AA ^ 2) := by ring
    have hPnn : (0 : ℝ) ≤ 2 * (N : ℝ) * ((T : ℝ))⁻¹ * AN ^ 2 := by positivity
    have hQnn : (0 : ℝ) ≤ ((T : ℝ))⁻¹ * (4 * (N : ℝ) * AA ^ 2) := by positivity
    rw [Real.norm_eq_abs, abs_le]
    constructor <;>
      linarith [mul_le_mul_of_nonneg_left h1 hinvnn, mul_le_mul_of_nonneg_left h2 hinvnn]
  have hS : Tendsto (fun T : ℕ => σ2 *
      ∑ i : Fin (T + 2 * N), ((Real.sqrt (T : ℝ))⁻¹ * winCoef a T N (i : ℕ)) ^ 2)
      atTop (𝓝 (σ2 * AN ^ 2)) := by
    have h1 : Tendsto (fun T : ℕ =>
        ((T : ℝ))⁻¹ * ∑ n ∈ Finset.range (T + 2 * N), (winCoef a T N n) ^ 2)
        atTop (𝓝 (AN ^ 2)) := by
      have h := hS0.add_const (AN ^ 2)
      rw [zero_add] at h
      exact h.congr fun T => by ring
    have h2 := h1.const_mul σ2
    exact h2.congr fun T => by rw [hrow T]
  -- individual negligibility of the weights
  have hneg : ∀ c : ℝ, 0 < c → ∀ᶠ T : ℕ in atTop, ∀ i : Fin (T + 2 * N),
      ((Real.sqrt (T : ℝ))⁻¹ * winCoef a T N (i : ℕ)) ^ 2 ≤ c := by
    intro c hc
    have h0 : Tendsto (fun T : ℕ => ((T : ℝ))⁻¹ * AA ^ 2) atTop (𝓝 0) := by
      simpa using hTinv.mul_const (AA ^ 2)
    filter_upwards [h0.eventually (eventually_lt_nhds hc)] with T hT i
    have hinvnn : (0 : ℝ) ≤ ((T : ℝ))⁻¹ := by positivity
    rw [mul_pow, hsqinv T]
    nlinarith [hbdd T (i : ℕ), mul_le_mul_of_nonneg_left (hbdd T (i : ℕ)) hinvnn]
  -- the weighted-iid CLT, and the window swap turning it into the statement
  have hmain := tendsto_charFun_weighted_iid'
    (Y := fun n : ℕ => ε ((n : ℤ) + 1 - (N : ℤ)))
    (kk := fun T : ℕ => T + 2 * N)
    (w := fun (T : ℕ) (i : Fin (T + 2 * N)) => (Real.sqrt (T : ℝ))⁻¹ * winCoef a T N (i : ℕ))
    (fun n => hε.measurable _)
    (iIndepFun.precomp hginj hε.iIndep)
    hidentY (hwn.memLp _) (hwn.integral_eq_zero _) (hwn.variance_eq _) hσ hS hneg u
  rw [← hAN]
  refine hmain.congr fun T => ?_
  congr 1
  refine congrArg (fun f : Ω → ℝ => μ.map f) (funext fun ω => ?_)
  rw [sum_window_swap a (fun j => ε j ω) T N, Finset.mul_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun n => (Real.sqrt (T : ℝ))⁻¹ * (winCoef a T N n * ε ((n : ℤ) + 1 - (N : ℤ)) ω))
      (T + 2 * N)]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The `L²` defect of a truncation

For a finite filter the normalized partial sum is an `L²`-bounded weighted sum of
independent innovations, and the **`ℓ¹` energy budget** `Σ_n c_n² ≤ (max|c|)(Σ_n|c_n|)
≤ B · T B` turns the `ℓ¹` mass `B` of the filter into a `T`-free `L²` bound. -/

private lemma eLpNorm_windowSum_le [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hw : IsWhiteNoise ε σ2 μ) (hσ : 0 ≤ σ2) (b : ℤ → ℝ) {B : ℝ} (hBnn : 0 ≤ B)
    (T M : ℕ) (hT : 1 ≤ T) (hB : ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |b k| ≤ B) :
    eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), b k * ε ((t : ℤ) + 1 - k) ω) 2 μ
      ≤ ENNReal.ofReal (Real.sqrt σ2 * B) := by
  classical
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hginj : Function.Injective fun i : Fin (T + 2 * M) => ((i : ℕ) : ℤ) + 1 - (M : ℤ) := by
    intro p q hpq
    simp only at hpq
    exact Fin.ext (by omega)
  have hpt : (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), b k * ε ((t : ℤ) + 1 - k) ω)
      = fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ i : Fin (T + 2 * M),
          winCoef b T M (i : ℕ) * ε (((i : ℕ) : ℤ) + 1 - (M : ℤ)) ω := by
    funext ω
    rw [sum_window_swap b (fun j => ε j ω) T M,
      ← Fin.sum_univ_eq_sum_range
        (fun n => winCoef b T M n * ε ((n : ℤ) + 1 - (M : ℤ)) ω) (T + 2 * M)]
  rw [hpt]
  have hmemZ : MemLp (fun ω => ∑ i : Fin (T + 2 * M),
      winCoef b T M (i : ℕ) * ε (((i : ℕ) : ℤ) + 1 - (M : ℤ)) ω) 2 μ :=
    memLp_weighted_noise hw _ _
  -- the `ℓ²` energy of the window weights
  have hcsum : ∑ i : Fin (T + 2 * M), (winCoef b T M (i : ℕ)) ^ 2 ≤ (T : ℝ) * B ^ 2 := by
    have h2 : ∀ n : ℕ, (winCoef b T M n) ^ 2 ≤ B * |winCoef b T M n| := by
      intro n
      have h3 := (abs_winCoef_le b T M n).trans hB
      nlinarith [abs_nonneg (winCoef b T M n), sq_abs (winCoef b T M n)]
    calc ∑ i : Fin (T + 2 * M), (winCoef b T M (i : ℕ)) ^ 2
        = ∑ n ∈ Finset.range (T + 2 * M), (winCoef b T M n) ^ 2 :=
          Fin.sum_univ_eq_sum_range (fun n => (winCoef b T M n) ^ 2) (T + 2 * M)
      _ ≤ ∑ n ∈ Finset.range (T + 2 * M), B * |winCoef b T M n| :=
          Finset.sum_le_sum fun n _ => h2 n
      _ = B * ∑ n ∈ Finset.range (T + 2 * M), |winCoef b T M n| := by rw [Finset.mul_sum]
      _ ≤ B * ((T : ℝ) * B) :=
          mul_le_mul_of_nonneg_left
            ((sum_abs_winCoef_le b T M).trans
              (mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg T))) hBnn
      _ = (T : ℝ) * B ^ 2 := by ring
  -- the second moment of the normalized weighted sum
  have hsq : ∫ ω, ((Real.sqrt (T : ℝ))⁻¹ * ∑ i : Fin (T + 2 * M),
        winCoef b T M (i : ℕ) * ε (((i : ℕ) : ℤ) + 1 - (M : ℤ)) ω) ^ 2 ∂μ
      = ((T : ℝ))⁻¹ * (σ2 * ∑ i : Fin (T + 2 * M), (winCoef b T M (i : ℕ)) ^ 2) := by
    have h1 : ∀ ω, ((Real.sqrt (T : ℝ))⁻¹ * ∑ i : Fin (T + 2 * M),
          winCoef b T M (i : ℕ) * ε (((i : ℕ) : ℤ) + 1 - (M : ℤ)) ω) ^ 2
        = ((T : ℝ))⁻¹ * (∑ i : Fin (T + 2 * M),
            winCoef b T M (i : ℕ) * ε (((i : ℕ) : ℤ) + 1 - (M : ℤ)) ω) ^ 2 := by
      intro ω
      rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg T)]
    rw [integral_congr_ae (Eventually.of_forall h1), integral_const_mul,
      integral_sq_weighted_noise hw _ _ hginj]
  refine eLpNorm_two_le_of_integral_sq_le (by positivity) (hmemZ.const_mul _) ?_
  rw [hsq, mul_pow, Real.sq_sqrt hσ]
  have h3 : ((T : ℝ))⁻¹ * (σ2 * ∑ i : Fin (T + 2 * M), (winCoef b T M (i : ℕ)) ^ 2)
      ≤ ((T : ℝ))⁻¹ * (σ2 * ((T : ℝ) * B ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcsum hσ) (by positivity)
  have h4 : ((T : ℝ))⁻¹ * (σ2 * ((T : ℝ) * B ^ 2)) = σ2 * B ^ 2 := by
    field_simp
  linarith

/-- **The head remainder is `L²`-null**: at a *fixed* sample size `T`, the normalized
partial sum of the filter defects `X_t − m − Σ_{|k|≤M} a_k ε_{t−k}` is a finite sum of
`L²`-null terms, hence vanishes as the truncation level `M` grows. -/
private lemma tendsto_eLpNorm_headRemainder [IsProbabilityMeasure μ] {a : ℤ → ℝ} {m σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hmeas : ∀ t, Measurable (X t))
    (hfil : ∀ t : ℤ, Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => X t ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (T : ℕ) :
    Tendsto (fun M : ℕ => eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) 2 μ)
      atTop (𝓝 0) := by
  have hsmul : ∀ (c : ℝ) (g : Ω → ℝ),
      eLpNorm (fun ω => c * g ω) 2 μ = ‖c‖ₑ * eLpNorm g 2 μ := by
    intro c g
    rw [show (fun ω => c * g ω) = c • g from by funext ω; simp, eLpNorm_const_smul]
  have hbound : ∀ M : ℕ,
      eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        (X ((t : ℤ) + 1) ω - m -
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) 2 μ
        ≤ ‖(Real.sqrt (T : ℝ))⁻¹‖ₑ * ∑ t ∈ Finset.range T,
            eLpNorm (fun ω => X ((t : ℤ) + 1) ω - m -
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) 2 μ := by
    intro M
    rw [hsmul]
    gcongr
    rw [show (fun ω => ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m -
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω))
        = ∑ t ∈ Finset.range T, (fun ω => X ((t : ℤ) + 1) ω - m -
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) from by
      funext ω; simp]
    exact eLpNorm_sum_le (fun t _ =>
      (((hmeas _).sub measurable_const).sub
        (Finset.measurable_sum _ fun k _ =>
          (hε.measurable _).const_mul _)).aestronglyMeasurable) one_le_two
  have hsum0 : Tendsto (fun M : ℕ => ∑ t ∈ Finset.range T,
      eLpNorm (fun ω => X ((t : ℤ) + 1) ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) 2 μ)
      atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.range T)
      (fun t (_ : t ∈ Finset.range T) => hfil ((t : ℤ) + 1))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun M => zero_le) hbound
  have := (ENNReal.Tendsto.const_mul hsum0
    (Or.inr (enorm_ne_top (x := (Real.sqrt (T : ℝ))⁻¹))))
  simpa using this

/-! ### The truncation defect, uniformly in the sample size -/

set_option maxHeartbeats 1000000 in
-- The statement carries several nested `Finset` sums; elaboration needs the larger budget.
private lemma integral_abs_defect_le [IsProbabilityMeasure μ] {a : ℤ → ℝ} {m σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hmeas : ∀ t, Measurable (X t))
    (hfil : ∀ t : ℤ, Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => X t ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    {B : ℝ} (hBnn : 0 ≤ B) (N : ℕ)
    (hB : ∀ M : ℕ, N ≤ M →
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k| ≤ B)
    (T : ℕ) (hT : 1 ≤ T) :
    Integrable (fun ω => |(Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
        - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
            ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω|) μ ∧
    ∫ ω, |(Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
        - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
            ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω| ∂μ
      ≤ Real.sqrt σ2 * B := by
  classical
  have hwn := hε.isWhiteNoise
  obtain ⟨bco, hbco⟩ : ∃ b : ℤ → ℝ,
      b = fun k => if k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then 0 else a k := ⟨_, rfl⟩
  -- measurability of every piece
  have hmG : ∀ M : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), bco k * ε ((t : ℤ) + 1 - k) ω) := fun M =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _) _
  have hmE : ∀ M : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      (X ((t : ℤ) + 1) ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) := fun M =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      ((hmeas _).sub measurable_const).sub
        (Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _)) _
  have hmD : Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      (X ((t : ℤ) + 1) ω - m)
      - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) := by
    refine Measurable.sub (Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      (hmeas _).sub measurable_const) _) ?_
    exact Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _) _
  -- the exact splitting `D = E_M + G_M` at every truncation level `M ≥ N`
  have hsplit : ∀ M : ℕ, N ≤ M → ∀ ω,
      (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
          - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
              ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω
        = ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
            (X ((t : ℤ) + 1) ω - m -
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω))
          + ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), bco k * ε ((t : ℤ) + 1 - k) ω) := by
    intro M hNM ω
    have hsub : Finset.Icc (-(N : ℤ)) (N : ℤ) ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      intro k hk
      simp only [Finset.mem_Icc] at *
      omega
    have hkey : ∀ t : ℕ,
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω
          - ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), bco k * ε ((t : ℤ) + 1 - k) ω
        = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω := by
      intro t
      have hstep := Finset.sum_subset hsub (f := fun k =>
        if k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then a k * ε ((t : ℤ) + 1 - k) ω else 0)
        (fun k _ hk => if_neg hk)
      rw [← Finset.sum_sub_distrib,
        Finset.sum_congr rfl (fun k _ => (show
          a k * ε ((t : ℤ) + 1 - k) ω - bco k * ε ((t : ℤ) + 1 - k) ω
            = if k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then a k * ε ((t : ℤ) + 1 - k) ω else 0 from by
          simp only [hbco]
          by_cases hk : k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) <;> simp [hk])), ← hstep]
      exact Finset.sum_congr rfl fun k hk => if_pos hk
    have hA : ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
          - ∑ t ∈ Finset.range T, ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω
        = ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m -
            ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)
          + ∑ t ∈ Finset.range T,
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), bco k * ε ((t : ℤ) + 1 - k) ω := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by linarith [hkey t]
    linear_combination (Real.sqrt (T : ℝ))⁻¹ * hA
  -- the tail filter has `ℓ¹` mass at most `B`
  have hbcomass : ∀ M : ℕ, N ≤ M →
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |bco k| ≤ B := by
    intro M hNM
    have hsub : Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ)
        ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := Finset.sdiff_subset
    have heq : ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |bco k|
        = ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k| := by
      rw [← Finset.sum_subset hsub (fun k hk hk' => by
        simp only [Finset.mem_sdiff, not_and, not_not] at hk'
        rw [hbco]
        simp only [if_pos (hk' hk), abs_zero])]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_sdiff] at hk
      rw [hbco]
      simp only [if_neg hk.2]
    rw [heq]
    exact hB M hNM
  -- the tail piece is `L²`-small, uniformly in `T`
  have hGbound : ∀ M : ℕ, N ≤ M →
      eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), bco k * ε ((t : ℤ) + 1 - k) ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt σ2 * B) := fun M hNM =>
    eLpNorm_windowSum_le hwn hσ.le bco hBnn T M hT (hbcomass M hNM)
  -- the head piece vanishes as the truncation level grows
  have hE0 := tendsto_eLpNorm_headRemainder hε hmeas hfil T
  -- pass to the limit `M → ∞`
  have hDle : eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      (X ((t : ℤ) + 1) ω - m)
      - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) 2 μ
      ≤ ENNReal.ofReal (Real.sqrt σ2 * B) := by
    have hlim : Tendsto (fun M : ℕ =>
        eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
          (X ((t : ℤ) + 1) ω - m -
            ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) 2 μ
          + ENNReal.ofReal (Real.sqrt σ2 * B)) atTop
        (𝓝 (ENNReal.ofReal (Real.sqrt σ2 * B))) := by
      have := hE0.add (tendsto_const_nhds (x := ENNReal.ofReal (Real.sqrt σ2 * B)))
      simpa using this
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop N] with M hNM
    refine le_trans (le_of_eq (eLpNorm_congr_ae (Eventually.of_forall (hsplit M hNM)))) ?_
    exact le_trans (eLpNorm_add_le (hmE M).aestronglyMeasurable (hmG M).aestronglyMeasurable
      one_le_two) (add_le_add le_rfl (hGbound M hNM))
  have hmemD : MemLp (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      (X ((t : ℤ) + 1) ω - m)
      - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) 2 μ :=
    ⟨hmD.aestronglyMeasurable, lt_of_le_of_lt hDle ENNReal.ofReal_lt_top⟩
  exact ⟨(hmemD.integrable one_le_two).abs,
    integral_abs_le_of_eLpNorm_two (by positivity) hmD.aestronglyMeasurable hDle⟩

/-- **FY Theorem 2.8(i) — DEBT (ledger (a); proof route: m-dependent approximation +
iid CLT, B&D 1991 §7.3)**: sample-mean CLT for a two-sided linear process
`X_t = m + Σ_{k∈ℤ} a_k ε_{t−k}` with IID(0, σ²) innovations and `Σ_k a_k ≠ 0`:
`√T (X̄_T − m) →d N(0, σ²(Σ_k a_k)²)`. -/
theorem sampleMean_clt_debt [IsProbabilityMeasure μ] {a : ℤ → ℝ} {m σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ}
    -- USER-INPUT: IID(0, σ²) innovations; FY Thm 2.8 / eq. (2.24)
    (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    -- USER-INPUT: absolutely summable coefficients; FY Thm 2.8
    (ha : Summable fun k : ℤ => |a k|)
    -- USER-INPUT: nondegeneracy Σ_k a_k ≠ 0; FY Thm 2.8(i)
    (hane : (∑' k : ℤ, a k) ≠ 0)
    -- LEAN-ONLY: measurability of the process; implicit in FY
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: two-sided linear representation (FY eq. (2.24)) as the L² limit of
    -- symmetric partial sums (definitionally `IsFilteredBy (X · − m) ε a μ`)
    (hfil : ∀ t : ℤ, Tendsto (fun N : ℕ =>
      eLpNorm (fun ω => X t ω - m -
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, X ((t : ℤ) + 1) ω - m)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (σ2 * (∑' k : ℤ, a k) ^ 2))) u)) := by
  classical
  have hwn := hε.isWhiteNoise
  have hsa : Summable a := ha.of_abs
  obtain ⟨A, hA⟩ : ∃ x : ℝ, x = ∑' k : ℤ, a k := ⟨_, rfl⟩
  obtain ⟨Aabs, hAabs⟩ : ∃ x : ℝ, x = ∑' k : ℤ, |a k| := ⟨_, rfl⟩
  -- the symmetric windows exhaust `ℤ`
  have hmono : Monotone fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro p q hpq k hk
    simp only [Finset.mem_Icc] at *
    omega
  have hcov : ∀ k : ℤ, ∃ N : ℕ, k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := fun k =>
    ⟨k.natAbs, by simp only [Finset.mem_Icc]; omega⟩
  have hfin : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop :=
    tendsto_atTop_finset_of_monotone hmono hcov
  have hANlim : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) atTop (𝓝 A) := by
    rw [hA]; exact hsa.hasSum.comp hfin
  have hAAlim : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k|)
      atTop (𝓝 Aabs) := by
    rw [hAabs]; exact ha.hasSum.comp hfin
  -- the `ℓ¹` tail mass
  have hBNnn : ∀ N : ℕ, 0 ≤ Aabs - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k| := by
    intro N
    have h := ha.sum_le_tsum (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun k _ => abs_nonneg (a k))
    rw [hAabs]
    linarith
  have hBNlim : Tendsto
      (fun N : ℕ => Aabs - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k|) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := Aabs) (f := atTop (α := ℕ))).sub hAAlim
    simpa using h
  have hBNbound : ∀ N M : ℕ, N ≤ M →
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k|
        ≤ Aabs - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k| := by
    intro N M hNM
    have hsub : Finset.Icc (-(N : ℤ)) (N : ℤ) ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      intro k hk
      simp only [Finset.mem_Icc] at *
      omega
    have h1 := Finset.sum_sdiff (f := fun k => |a k|) hsub
    have h2 := ha.sum_le_tsum (Finset.Icc (-(M : ℤ)) (M : ℤ)) (fun k _ => abs_nonneg (a k))
    rw [hAabs]
    linarith
  -- the Gaussian limit depends continuously on the variance
  have hGcont : Continuous fun v : ℝ => charFun (gaussianReal 0 (Real.toNNReal v)) u := by
    have hEq : (fun v : ℝ => charFun (gaussianReal 0 (Real.toNNReal v)) u)
        = fun v : ℝ => Complex.exp (-(((max v 0 : ℝ)) : ℂ) * (u : ℂ) ^ 2 / 2) := by
      funext v
      rw [charFun_gaussianReal, Real.coe_toNNReal']
      push_cast
      ring_nf
    rw [hEq]
    fun_prop
  have hlimN : Tendsto (fun N : ℕ => charFun (gaussianReal 0 (Real.toNNReal
        (σ2 * (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) ^ 2))) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (σ2 * A ^ 2))) u)) :=
    (hGcont.tendsto (σ2 * A ^ 2)).comp ((hANlim.pow 2).const_mul σ2)
  -- normalization identity for the statement's random variable
  have hSSeq : ∀ (T : ℕ), 1 ≤ T → ∀ ω,
      Real.sqrt (T : ℝ) * ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, X ((t : ℤ) + 1) ω - m)
        = (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m) := by
    intro T hT ω
    have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    have hsum : ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
        = (∑ t ∈ Finset.range T, X ((t : ℤ) + 1) ω) - (T : ℝ) * m := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum]
    obtain ⟨s, hspos, hsdef⟩ : ∃ s : ℝ, 0 < s ∧ Real.sqrt (T : ℝ) = s :=
      ⟨_, Real.sqrt_pos.2 hTpos, rfl⟩
    have hs2 : s * s = (T : ℝ) := by rw [← hsdef]; exact Real.mul_self_sqrt hTpos.le
    rw [hsdef, ← hs2]
    field_simp
  -- measurability of the two comparison variables
  have hmZ : ∀ T : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)) := fun T =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      (hmeas _).sub measurable_const) _
  have hmW : ∀ N T : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) := fun N T =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _) _
  rw [← hA, Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ,
      |u| * (Real.sqrt σ2 * (Aabs - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k|)) < δ / 3 ∧
      dist (charFun (gaussianReal 0 (Real.toNNReal
          (σ2 * (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) ^ 2))) u)
        (charFun (gaussianReal 0 (Real.toNNReal (σ2 * A ^ 2))) u) < δ / 3 := by
    have h1 : Tendsto (fun N : ℕ =>
        |u| * (Real.sqrt σ2 * (Aabs - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k|)))
        atTop (𝓝 0) := by
      simpa using (hBNlim.const_mul (Real.sqrt σ2)).const_mul |u|
    have e1 := h1.eventually (eventually_lt_nhds (show (0 : ℝ) < δ / 3 by linarith))
    have e2 : ∀ᶠ N : ℕ in atTop,
        dist (charFun (gaussianReal 0 (Real.toNNReal
            (σ2 * (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) ^ 2))) u)
          (charFun (gaussianReal 0 (Real.toNNReal (σ2 * A ^ 2))) u) < δ / 3 := by
      have h := hlimN.eventually (Metric.ball_mem_nhds
        (charFun (gaussianReal 0 (Real.toNNReal (σ2 * A ^ 2))) u)
        (show (0 : ℝ) < δ / 3 by linarith))
      simpa [Metric.mem_ball] using h
    exact (e1.and e2).exists
  obtain ⟨T0, hT0⟩ := Metric.tendsto_atTop.1
    (tendsto_charFun_truncSum (a := a) hε hσ N u) (δ / 3) (by linarith)
  refine ⟨max 1 T0, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTT0 : T0 ≤ T := le_trans (le_max_right _ _) hT
  rw [show (fun ω => Real.sqrt (T : ℝ) *
        ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, X ((t : ℤ) + 1) ω - m))
      = (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)) from
    funext (hSSeq T hT1)]
  obtain ⟨hint, hbd⟩ := integral_abs_defect_le hε hσ hmeas hfil (hBNnn N) N (hBNbound N) T hT1
  have hd1 : dist (charFun (μ.map fun ω => (Real.sqrt (T : ℝ))⁻¹ *
        ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)) u)
      (charFun (μ.map fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) u) < δ / 3 := by
    rw [dist_eq_norm]
    refine lt_of_le_of_lt
      (le_trans (norm_charFun_map_sub_le (hmZ T) (hmW N T) hint u) ?_) hN1
    exact mul_le_mul_of_nonneg_left hbd (abs_nonneg u)
  have hd2 := hT0 T hTT0
  obtain ⟨P, hP⟩ : ∃ z : ℂ, z = charFun (μ.map fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)) u := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ z : ℂ, z = charFun (μ.map fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) u := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ z : ℂ, z = charFun (gaussianReal 0 (Real.toNNReal
      (σ2 * (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) ^ 2))) u := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ z : ℂ, z = charFun (gaussianReal 0 (Real.toNNReal (σ2 * A ^ 2))) u :=
    ⟨_, rfl⟩
  rw [← hP, ← hQ] at hd1
  rw [← hQ, ← hR] at hd2
  rw [← hR, ← hS] at hN2
  rw [← hP, ← hS]
  linarith [dist_triangle P Q S, dist_triangle Q R S]

/-! ### Bricks for the lag-0 and Bartlett debts

The **mean correction** in `γ̂(0)` is asymptotically negligible, and this is already a
consequence of the sample-mean layer above: the same ℓ¹ energy budget that produced the
`T`-free `L²` bound of `eLpNorm_windowSum_le` bounds the whole normalized centred partial
sum by `√σ² Σ_k|a_k|` uniformly in `T` (`eLpNorm_normalizedSum_le`), whence
`E|√T X̄_T²| ≤ σ² (Σ_k|a_k|)² / √T → 0` (`tendsto_integral_sqrt_mul_sampleMean_sq`).
So `√T (γ̂(0) − γ(0))` and `√T (T⁻¹ Σ_t X_t² − γ(0))` have the same limit law, which is
the reduction the remaining debts start from.

**Named residues of the (since removed) FY Thm 2.8(ii) debt (after this reduction).**
* (R1) the CLT for `T^{-1/2} Σ_{t≤T}(X_t² − γ(0))` at a *fixed* truncation level `N`.
  The truncated square is `2N`-dependent, so Bernstein-block `[1,T]` into big blocks of
  a fixed length `L` separated by guard blocks of length `2N`: the big-block sums are
  functions of **disjoint** innovation blocks, hence independent, and identically
  distributed because the joint law of an i.i.d. family is a product measure and so is
  shift-invariant. Constant weights `T^{-1/2}` then feed the *already present*
  `tendsto_charFun_weighted_iid` — **no new CLT engine is needed**, in contrast with the
  MDS route; `L → ∞` after `T → ∞` removes the guard-block loss.
  **Status (wave `ts/f4b-garch-last`, 2026-08-09): (R1) is the *only* item of the four
  still carrying analytic content, and it may now be proved against a known target.**
  Its second-moment side is fully supplied: `cov_sq_truncFilter` shows the truncated
  covariance depends on `(s, t)` only through the lag `s − t` (so the block scheme's
  variance bookkeeping is a one-variable computation), `tendsto_cov_sq_truncFilter` sends
  that lag kernel to `covKernel` as `N → ∞`, and `tendsto_cesaro_covKernel` evaluates the
  Cesàro mass of `covKernel` as the frozen constant. What (R1) still owes is the
  *distributional* step alone — the block construction, the independence of the
  big-block sums, and the guard-block `L²` loss.
* (R2) the fourth-moment covariance `Cov(X_s^{(N)2}, X_t^{(N)2})`, i.e. the partition
  formula for `E[ε_i ε_j ε_k ε_l]` over i.i.d. innovations (`η σ⁴` on the diagonal,
  `σ⁴` on each pairing, `0` otherwise). This was the only genuinely *missing analytic
  input* — everything else in (R1)/(R3) reuses machinery in this file. **CLOSED**
  (wave `ts/f3b-tail`, 2026-08-09): `integral_sq_mul_sq_noiseComb` and its covariance
  form `cov_sq_noiseComb`, in the `FourthMoment` section below, at arbitrary finitely
  supported weights `c`, `d` — so at *every* pair of lags `(s, t)` and every truncation
  level `N` at once, which is what the joint (Bartlett) version needs as well. Two
  corrections to the plan as stated here are worth recording. First, the *partition
  formula* is not the right intermediate object: proving it means a four-fold sum split
  over equality patterns of `(i, j, k, l)`, and the one-coordinate induction of
  `integral_sq_mul_sq_step` replaces it entirely (the pattern bookkeeping becomes a
  `ring` identity in one new innovation). Second, no third moment of `ε` is needed and
  none is available from the hypotheses of the two debts — the `A³` block is killed by
  `E Q = E R = 0` rather than by `E ε³ = 0`, and the `A¹` block by `E ε = 0`; a route
  that *did* need `E ε³` would be unprovable from `MemLp (ε 0) 4 μ` alone.
* (R3) the truncation transfer at the squared level,
  `‖T^{-1/2} Σ_t ((X_t² − EX_t²) − (X_t^{(N)2} − EX_t^{(N)2}))‖₂ → 0` as `N → ∞`,
  uniformly in `T`: factor `X² − X^{(N)2} = (X − X^{(N)})(X + X^{(N)})` and apply
  Cauchy–Schwarz against (R2) together with the ℓ¹ energy budget of
  `eLpNorm_windowSum_le` at the bilinear level.
  **Correction (wave `ts/f4b-garch-last`, 2026-08-09): (R2) as stated above is not enough
  for this, and the gap is now filled.** The factorization `(X − X^{(N)})(X + X^{(N)})`
  produces a product of two *different* linear forms, so what the second moment of
  `Σ_t (X_t² − X_t^{(N)2})` needs is `Cov(L_c L_d, L_e L_f)` at four independent weight
  vectors, and `cov_sq_noiseComb` only covers the diagonal `c = d`, `e = f`. It is a
  genuine strengthening, but a *cheap* one: bilinear polarization
  (`4 L_c L_d = L_{c+d}² − L_{c−d}²` in each slot) reduces it to four instances of the
  squared identity, with no new induction and no extra moment hypothesis. Proved as
  `integral_prod_four_noiseComb`/`cov_prod_noiseComb` (Isserlis/Wick plus the
  fourth-cumulant diagonal). What is *still* open in (R3) is only the passage from the
  finite windows to the `L²` limits `X_t` themselves — the covariance algebra is done.
* (R4) the series identity `Σ_h γ(h)² = σ⁴ Σ_h (Σ_k a_k a_{k+h})²` matching the limit
  produced by (R1)+(R2) to the frozen `(η−3)γ(0)² + 2 Σ_{j∈ℤ} γ(j)²`.
  (The frozen constant is *confirmed* against B&D (1991) Prop 7.3.4: the printed FY
  (2.25) is indeed a misprint, and the docstring's correction is the right one — no
  further amendment is called for.)
  **Its dependence input is CLOSED** (wave `ts/f3b-tail`, 2026-08-09):
  `acvf_eq_tsum_of_filter` gives `γ(h) = σ² Σ_k a_k a_{k−h}` at every lag, and at `h = 0`
  `γ(0) = σ² Σ_k a_k²`, so the frozen constant *is* the (R1)+(R2) constant term by term —
  squaring and summing the identity is all (R4) is. Three things about it are worth
  recording, because they change the ledger:
  - the identity needs **neither `hσ` nor stationarity nor a decay rate**: it comes out of
    `hfil` and `IsIIDNoise` alone, with `ha` used only to make `k ↦ a_k a_{k−h}` summable;
  - `E X_t = 0` is **derived**, not assumed (`integral_eq_zero_of_filter`), and so is
    `MemLp (X t) 2 μ` (`memLp_two_of_filter`) — the frozen statement supplies neither, and
    both are needed before `acvf` can be manipulated at all;
  - the pairing `Σ_h γ(h)² < ∞` is a *separate* step — the identity alone does not give it.
    It is **also CLOSED** (`summable_acvf_sq_of_filter`), by Young's inequality
    (`ℓ¹ * ℓ¹ ⊆ ℓ¹ ⊆ ℓ²`): the reindexing `(h, k) ↦ (k, k − h)` of `ℤ × ℤ`
    (`shiftPairEquiv`) turns the coefficient double series into a product of two copies of
    `ha`, so it is summable on `ℤ × ℤ` and its `h`-sections sum (`summable_absConv`); then
    `|Σ_k a_k a_{k−h}| ≤ Σ_k |a_k||a_{k−h}| ≤ (Σ|a|)²` upgrades `ℓ¹` to `ℓ²` in `h`
    (`summable_acvfCoeff_sq`). This is what stops the frozen `2 Σ_{j∈ℤ} γ(j)²` from being a
    junk `tsum`, and it is the only place in the whole reduction where the `ℓ¹` hypothesis
    `ha` is used for anything other than making a single series converge.
  **(R4) is now CLOSED outright** (wave `ts/f4b-garch-last`, 2026-08-09):
  `tendsto_cesaro_covKernel` (section `CesaroKernel` below). The previous reading — "the
  residual bookkeeping cannot be written down until (R1) fixes the exact shape of the
  limit it produces" — is **overturned**: the shape is forced by (R2) alone and does not
  wait on (R1). (R2)'s covariance depends on `(s, t)` only through `h = s − t`, so the
  variance of the normalized sum is `T⁻¹ Σ_{s,t<T} covKernel(s − t)`, and a Cesàro/Fejér
  limit at an absolutely summable kernel (`tendsto_cesaro_kernel`, proved there at an
  abstract `K : ℤ → ℝ`) evaluates it as `Σ_{h∈ℤ} covKernel h`, which is *exactly* the
  frozen `(η−3)γ(0)² + 2 Σ_{j∈ℤ} γ(j)²`. Two things this settled that the plan above had
  not: the `η`-block needs its own reindexing `Σ_h Σ_i a_i² a_{i−h}² = (Σ_i a_i²)²`
  (`tsum_sqConv`, Tonelli on `ℤ × ℤ` through `shiftPairEquiv`) — it is *not* a corollary
  of `summable_acvfCoeff_sq`, which only covers the `γ(h)²` block; and absolute
  summability of the kernel (`summable_abs_covKernel`) is what licenses the Fejér weights
  to be dropped, so `ha` is used here a *second* time, contradicting the reading recorded
  at `summable_acvfCoeff_sq` that Young's inequality is "the only place in the whole
  reduction where the `ℓ¹` hypothesis `ha` is used for anything other than making a single
  series converge". So (R1) may now be proved against a *known* target constant: what it
  owes is the CLT, not the variance.

**Named residue of the (since removed) Bartlett debt.** the joint (lags `0..M`) version of
(R1)–(R4) — the same blocks, assembled through the Cramér–Wold linear combination that
the frozen statement already exhibits — followed by the ratio delta method
`ρ̂(i) = γ̂(i)/γ̂(0)`. Its `bartlettW` covariance is the standard Bartlett formula; no
misprint watch fires there either.

**Update (wave `ts/f3b-tail`, 2026-08-09).** Two of the four blocks are shared with the
lag-`0` debt *at full strength*, i.e. nothing lag-`0`-specific was used in closing them:
`integral_sq_mul_sq_noiseComb`/`cov_sq_noiseComb` take **arbitrary** weight vectors
`c`, `d`, so (R2) is already the joint statement — the Cramér–Wold combination
`Σ_i c_i γ̂(i)` is again a quadratic form in the innovations and its fourth moment is the
same formula; and `acvf_eq_tsum_of_filter` is stated at an arbitrary lag `h`, so it feeds
`bartlettW`'s `acf` entries directly. What is genuinely joint, and still open, is the
lag-`0..M` version of (R1) (one Bernstein-block CLT for the *vector* of lag products,
i.e. the same blocks with the Cramér–Wold coefficient carried through) and the ratio
delta method, which additionally needs `0 < γ(0)` — available from
`acvf_eq_tsum_of_filter` at `h = 0` as `σ² Σ_k a_k² > 0`, but only once `a ≠ 0` is
assumed, which the frozen statement does *not* hypothesize. That is a genuine gap in the
frozen statement of the Bartlett debt: with `a ≡ 0` the process is `0` a.s., `ρ̂` and `ρ`
are both junk `0/0 = 0`, and the limit is `δ₀` rather than the stated Gaussian — which is
consistent only because `bartlettW` is then also `0`. So the statement survives, but the
delta method cannot be the route in that degenerate corner and must be split off.

**Executed (wave `ts/f4b-garch-last`, 2026-08-09; the two debts and the `Degenerate`
sections have since been removed).** Both debts `by_cases`d on `∀ k, a k = 0` and **proved**
the degenerate branch outright: `hfil` with `a ≡ 0` forces `eLpNorm (X t) 2 μ = 0`, so `X`
is a.e. `0`, whence `acvf`, `acf`, `sampleACVF`, `sampleACF` and `bartlettW` are all the
junk value `0` and both sides of both statements are `δ₀`'s character. In the surviving
branch `0 < γ(0)` was *supplied* rather than assumed (from `acvf_eq_tsum_of_filter` at
`h = 0` plus one nonzero coefficient), so the delta method's nondegeneracy input was no
longer part of the residue.
One correction to the reading above: `a ≡ 0` does **not** need `hσ` or any moment
hypothesis to be handled — it is a statement about `hfil` alone, and the collapse happens
already at the level of `eLpNorm`, not through the limiting variance. -/

/-- The `L²` bound implied by an `eLpNorm` bound (converse of
`eLpNorm_two_le_of_integral_sq_le`). -/
private lemma integral_sq_le_of_eLpNorm_two {f : Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : AEStronglyMeasurable f μ) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal C) :
    ∫ ω, f ω ^ 2 ∂μ ≤ C ^ 2 := by
  have hmem : MemLp f 2 μ := ⟨hf, lt_of_le_of_lt h ENNReal.ofReal_lt_top⟩
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num)] at h
  have hpow : ∀ ω, ‖f ω‖ ^ ((2 : ENNReal).toReal) = f ω ^ 2 := by
    intro ω
    rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, sq_abs]
  rw [integral_congr_ae (Eventually.of_forall hpow),
    show ((2 : ENNReal).toReal)⁻¹ = 1 / (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow] at h
  have hnn : (0 : ℝ) ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have h2 : Real.sqrt (∫ ω, f ω ^ 2 ∂μ) ≤ C := (ENNReal.ofReal_le_ofReal_iff hC).1 h
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ ω, f ω ^ 2 ∂μ)]

/-- **The `T`-free `L²` bound for the normalized centred partial sum**:
`‖T^{-1/2} Σ_{t≤T}(X_t − m)‖₂ ≤ √σ² Σ_k |a_k|`. This is the ℓ¹ energy budget of
`eLpNorm_windowSum_le` applied to the full filter, with the truncation level removed by
`tendsto_eLpNorm_headRemainder`. -/
private lemma eLpNorm_normalizedSum_le [IsProbabilityMeasure μ] {a : ℤ → ℝ} {m σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (ha : Summable fun k : ℤ => |a k|)
    (hmeas : ∀ t, Measurable (X t))
    (hfil : ∀ t : ℤ, Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => X t ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (T : ℕ) (hT : 1 ≤ T) :
    eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ *
        ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)) 2 μ
      ≤ ENNReal.ofReal (Real.sqrt σ2 * ∑' k : ℤ, |a k|) := by
  classical
  have hwn := hε.isWhiteNoise
  have hAnn : (0 : ℝ) ≤ ∑' k : ℤ, |a k| := tsum_nonneg fun k => abs_nonneg _
  have hmG : ∀ M : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) := fun M =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _) _
  have hmE : ∀ M : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      (X ((t : ℤ) + 1) ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) := fun M =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      ((hmeas _).sub measurable_const).sub
        (Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _)) _
  have hsplit : ∀ (M : ℕ) (ω : Ω),
      (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
        = ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
            (X ((t : ℤ) + 1) ω - m -
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω))
          + ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) := by
    intro M ω
    have hA : ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
        = ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m -
            ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)
          + ∑ t ∈ Finset.range T,
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    linear_combination (Real.sqrt (T : ℝ))⁻¹ * hA
  have hGbound : ∀ M : ℕ,
      eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt σ2 * ∑' k : ℤ, |a k|) := fun M =>
    eLpNorm_windowSum_le hwn hσ.le a hAnn T M hT
      (ha.sum_le_tsum (Finset.Icc (-(M : ℤ)) (M : ℤ)) (fun k _ => abs_nonneg (a k)))
  have hE0 := tendsto_eLpNorm_headRemainder hε hmeas hfil (m := m) T
  have hlim : Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        (X ((t : ℤ) + 1) ω - m -
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) 2 μ
        + ENNReal.ofReal (Real.sqrt σ2 * ∑' k : ℤ, |a k|)) atTop
      (𝓝 (ENNReal.ofReal (Real.sqrt σ2 * ∑' k : ℤ, |a k|))) := by
    have h := hE0.add
      (tendsto_const_nhds (x := ENNReal.ofReal (Real.sqrt σ2 * ∑' k : ℤ, |a k|)))
    simpa using h
  refine ge_of_tendsto hlim (Eventually.of_forall fun M => ?_)
  refine le_trans (le_of_eq (eLpNorm_congr_ae (Eventually.of_forall (hsplit M)))) ?_
  exact le_trans (eLpNorm_add_le (hmE M).aestronglyMeasurable (hmG M).aestronglyMeasurable
    one_le_two) (add_le_add le_rfl (hGbound M))

/-- **The mean correction of `γ̂(0)` is asymptotically negligible** (zero-mean case):
`E|√T X̄_T²| ≤ σ² (Σ_k |a_k|)² / √T → 0`. Hence `√T (γ̂(0) − γ(0))` and
`√T (T⁻¹ Σ_t X_t² − γ(0))` have the same limit law. -/
private lemma tendsto_integral_sqrt_mul_sampleMean_sq [IsProbabilityMeasure μ] {a : ℤ → ℝ}
    {σ2 : ℝ} {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (ha : Summable fun k : ℤ => |a k|)
    (hmeas : ∀ t, Measurable (X t))
    (hfil : ∀ t : ℤ, Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => X t ω -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun T : ℕ => ∫ ω, |Real.sqrt (T : ℝ) *
        (sampleMean fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ^ 2| ∂μ) atTop (𝓝 0) := by
  classical
  have hAnn : (0 : ℝ) ≤ ∑' k : ℤ, |a k| := tsum_nonneg fun k => abs_nonneg _
  have hfil' : ∀ t : ℤ, Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => X t ω - 0 -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0) := by
    intro t
    simpa using hfil t
  have hmZ : ∀ T : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - 0)) := fun T =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      (hmeas _).sub measurable_const) _
  -- the pointwise rewriting `√T X̄² = T^{-1/2} (T^{-1/2} Σ_t X_t)²`
  have hpt : ∀ (T : ℕ), 1 ≤ T → ∀ ω,
      |Real.sqrt (T : ℝ) * (sampleMean fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ^ 2|
        = (Real.sqrt (T : ℝ))⁻¹ *
          ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - 0)) ^ 2 := by
    intro T hT ω
    have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    obtain ⟨s, hspos, hsdef⟩ : ∃ s : ℝ, 0 < s ∧ Real.sqrt (T : ℝ) = s :=
      ⟨_, Real.sqrt_pos.2 hTpos, rfl⟩
    have hs2 : s * s = (T : ℝ) := by rw [← hsdef]; exact Real.mul_self_sqrt hTpos.le
    have hval : Real.sqrt (T : ℝ) *
          (sampleMean fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ^ 2
        = (Real.sqrt (T : ℝ))⁻¹ *
          ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - 0)) ^ 2 := by
      rw [sampleMean, Fin.sum_univ_eq_sum_range (fun t => X ((t : ℤ) + 1) ω) T, hsdef,
        ← hs2]
      simp only [sub_zero]
      field_simp
    rw [hval, abs_of_nonneg (by positivity)]
  -- the uniform second-moment bound
  have hbound : ∀ T : ℕ, 1 ≤ T →
      ∫ ω, |Real.sqrt (T : ℝ) *
          (sampleMean fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ^ 2| ∂μ
        ≤ (Real.sqrt (T : ℝ))⁻¹ * (Real.sqrt σ2 * ∑' k : ℤ, |a k|) ^ 2 := by
    intro T hT
    rw [integral_congr_ae (Eventually.of_forall (hpt T hT)), integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact integral_sq_le_of_eLpNorm_two (by positivity) (hmZ T).aestronglyMeasurable
      (eLpNorm_normalizedSum_le hε hσ ha hmeas hfil' T hT)
  -- and it tends to zero
  have hsq0 : Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹ *
      (Real.sqrt σ2 * ∑' k : ℤ, |a k|) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℕ => Real.sqrt (T : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    simpa using h2.mul_const ((Real.sqrt σ2 * ∑' k : ℤ, |a k|) ^ 2)
  refine squeeze_zero' ?_ ?_ hsq0
  · filter_upwards with T
    exact integral_nonneg fun ω => abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with T hT
    exact hbound T hT

/-! ### (R2): the fourth-moment identity for weighted sums of the innovations

This is the analytic input named as **(R2)** in the residue ledger above — the only piece
of the FY Thm 2.8(ii) reduction that was not already available in this file.
For an i.i.d. family `ε` with `E ε = 0`, `Var ε = σ²` and a finite fourth moment,
and for finitely supported weights `c`, `d`,

`E[(Σ cᵢ εᵢ)² (Σ dᵢ εᵢ)²] = (η σ⁴ − 3σ⁴) Σ cᵢ²dᵢ² + σ⁴[(Σ cᵢ²)(Σ dᵢ²) + 2(Σ cᵢdᵢ)²]`,

equivalently `Cov((Σ cᵢ εᵢ)², (Σ dᵢ εᵢ)²) = (ησ⁴ − 3σ⁴) Σ cᵢ²dᵢ² + 2σ⁴ (Σ cᵢdᵢ)²`
(`cov_sq_noiseComb`). Taking `c i = a (s − i)` and `d i = a (t − i)` on the window
`|s − i| ≤ N` this *is* `Cov(X_s^{(N)2}, X_t^{(N)2})`.

The proof is a **one-coordinate induction** on the support (`integral_sq_mul_sq_step`),
not a four-fold sum over the partition lattice: adjoining one innovation `A = ε a`,
independent of the two partial sums `Q`, `R` already built, expands the integrand as a
polynomial in `A` whose coefficients are polynomials in `(Q, R)`,

`(cA + Q)²(dA + R)² = c²d²A⁴ + A³·G₃(Q,R) + A²·G₂(Q,R) + A·G₁(Q,R) + Q²R²`,

and independence factorises each block. The odd blocks die for free — `E G₃ = 0` because
`E Q = E R = 0`, and `E A = 0` kills the `A¹` block whatever `G₁` is — so **no third
moment of `ε` is ever needed**, which is what makes a bare `MemLp (ε 0) 4` hypothesis
enough. This also explains the shape of the answer: `η` enters only through the diagonal
`A⁴` term, and the `3σ⁴` correction is the diagonal that the two `σ⁴` products
double-count.
-/

section FourthMoment

variable {ε : ℤ → Ω → ℝ} {σ2 : ℝ}

private lemma holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 :=
  ⟨by rw [← two_mul, show (4 : ENNReal) = 2 * 2 by norm_num,
      ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩

private lemma memLp_two_mul_of_memLp_four {f g : Ω → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    MemLp (fun ω => f ω * g ω) 2 μ := by
  haveI := holderTriple_four_four_two
  exact hg.mul' hf

private lemma integrable_mul_of_memLp_two {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => f ω * g ω) μ :=
  hf.integrable_mul hg

/-! #### Moments of the innovations -/

private lemma IsIIDNoise.memLp_four (hε : IsIIDNoise ε σ2 μ) (hε4 : MemLp (ε 0) 4 μ) (i : ℤ) :
    MemLp (ε i) 4 μ := (hε.identDistrib 0 i).memLp_snd hε4

private lemma IsIIDNoise.memLp_two_of_iid (hε : IsIIDNoise ε σ2 μ) (i : ℤ) : MemLp (ε i) 2 μ :=
  (hε.identDistrib 0 i).memLp_snd hε.memLp

private lemma IsIIDNoise.integral_zero' [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ) (i : ℤ) :
    ∫ ω, ε i ω ∂μ = 0 := ((hε.identDistrib i 0).integral_eq).trans hε.integral_eq_zero

private lemma IsIIDNoise.integral_sq' [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ) (i : ℤ) :
    ∫ ω, ε i ω ^ 2 ∂μ = σ2 := by
  have h0 : ∫ ω, ε 0 ω ^ 2 ∂μ = σ2 := by
    have hv := variance_eq_sub hε.memLp
    rw [hε.variance_eq, hε.integral_eq_zero] at hv
    simp only [Pi.pow_apply] at hv
    linarith
  have ht := ((hε.identDistrib i 0).comp (measurable_id.pow_const 2)).integral_eq
  simp only [Function.comp, id_eq] at ht
  rw [ht, h0]

private lemma IsIIDNoise.integral_four' [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ) (i : ℤ) :
    ∫ ω, ε i ω ^ 4 ∂μ = ∫ ω, ε 0 ω ^ 4 ∂μ := by
  have ht := ((hε.identDistrib i 0).comp (measurable_id.pow_const 4)).integral_eq
  simpa only [Function.comp, id_eq] using ht

private lemma integral_noise_mul_noise [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ) (i j : ℤ) :
    ∫ ω, ε i ω * ε j ω ∂μ = if i = j then σ2 else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, ← hε.integral_sq' i]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  · rw [if_neg h]
    have hind : IndepFun (ε i) (ε j) μ := hε.iIndep.indepFun h
    rw [hind.integral_fun_mul_eq_mul_integral (hε.measurable i).aestronglyMeasurable
      (hε.measurable j).aestronglyMeasurable, hε.integral_zero' i, zero_mul]

/-! #### Linear combinations of the innovations -/

private lemma integral_noiseComb [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ) (c : ℤ → ℝ)
    (s : Finset ℤ) : ∫ ω, ∑ i ∈ s, c i * ε i ω ∂μ = 0 := by
  rw [integral_finset_sum s
    (fun i _ => ((hε.memLp_two_of_iid i).integrable one_le_two).const_mul (c i))]
  simp only [integral_const_mul, hε.integral_zero', mul_zero, Finset.sum_const_zero]

private lemma integral_noiseComb_mul [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ) (c d : ℤ → ℝ)
    (s : Finset ℤ) :
    ∫ ω, (∑ i ∈ s, c i * ε i ω) * (∑ j ∈ s, d j * ε j ω) ∂μ = σ2 * ∑ i ∈ s, c i * d i := by
  have hI : ∀ i j : ℤ, Integrable (fun ω => (c i * d j) * (ε i ω * ε j ω)) μ :=
    fun i j => (integrable_mul_of_memLp_two (hε.memLp_two_of_iid i)
      (hε.memLp_two_of_iid j)).const_mul _
  have hpt : ∀ ω, (∑ i ∈ s, c i * ε i ω) * (∑ j ∈ s, d j * ε j ω)
      = ∑ i ∈ s, ∑ j ∈ s, (c i * d j) * (ε i ω * ε j ω) := by
    intro ω
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finset_sum s (fun i _ => integrable_finset_sum s fun j _ => hI i j)]
  have hstep : ∀ i ∈ s, ∫ ω, ∑ j ∈ s, (c i * d j) * (ε i ω * ε j ω) ∂μ
      = σ2 * (c i * d i) := by
    intro i hi
    rw [integral_finset_sum s (fun j _ => hI i j)]
    simp only [integral_const_mul, integral_noise_mul_noise hε]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq s i (fun j => c i * d j * σ2), if_pos hi]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]


/-! #### The coordinate-by-coordinate induction step -/

set_option maxHeartbeats 1000000 in
-- the nine-term expansion stresses `ring`/`integral_add` bookkeeping; the default budget
-- is not enough for the assembly `rw` chain
private lemma integral_sq_mul_sq_step [IsProbabilityMeasure μ] {A Q R : Ω → ℝ}
    {v2 v4 q r m P ca da : ℝ}
    (hA4 : MemLp A 4 μ) (hQ4 : MemLp Q 4 μ) (hR4 : MemLp R 4 μ)
    (hind : IndepFun A (fun ω => (Q ω, R ω)) μ)
    (hA1 : ∫ ω, A ω ∂μ = 0) (hA2 : ∫ ω, A ω ^ 2 ∂μ = v2) (hA4i : ∫ ω, A ω ^ 4 ∂μ = v4)
    (hQ1 : ∫ ω, Q ω ∂μ = 0) (hR1 : ∫ ω, R ω ∂μ = 0)
    (hQQ : ∫ ω, Q ω ^ 2 ∂μ = q) (hRR : ∫ ω, R ω ^ 2 ∂μ = r)
    (hQR : ∫ ω, Q ω * R ω ∂μ = m)
    (hP : ∫ ω, Q ω ^ 2 * R ω ^ 2 ∂μ = P) :
    ∫ ω, (ca * A ω + Q ω) ^ 2 * (da * A ω + R ω) ^ 2 ∂μ
      = ca ^ 2 * da ^ 2 * v4 + v2 * (ca ^ 2 * r + 4 * (ca * da) * m + da ^ 2 * q) + P := by
  have hA2' : MemLp A 2 μ := hA4.mono_exponent (by norm_num)
  have hQ2 : MemLp Q 2 μ := hQ4.mono_exponent (by norm_num)
  have hR2 : MemLp R 2 μ := hR4.mono_exponent (by norm_num)
  have hAA : MemLp (fun ω => A ω * A ω) 2 μ := memLp_two_mul_of_memLp_four hA4 hA4
  have hAQ : MemLp (fun ω => A ω * Q ω) 2 μ := memLp_two_mul_of_memLp_four hA4 hQ4
  have hAR : MemLp (fun ω => A ω * R ω) 2 μ := memLp_two_mul_of_memLp_four hA4 hR4
  have hQQm : MemLp (fun ω => Q ω * Q ω) 2 μ := memLp_two_mul_of_memLp_four hQ4 hQ4
  have hRRm : MemLp (fun ω => R ω * R ω) 2 μ := memLp_two_mul_of_memLp_four hR4 hR4
  have hQRm : MemLp (fun ω => Q ω * R ω) 2 μ := memLp_two_mul_of_memLp_four hQ4 hR4
  -- integrable squares and products
  have hIQsq : Integrable (fun ω => Q ω ^ 2) μ :=
    (integrable_mul_of_memLp_two hQ2 hQ2).congr (Eventually.of_forall fun ω => by ring)
  have hIRsq : Integrable (fun ω => R ω ^ 2) μ :=
    (integrable_mul_of_memLp_two hR2 hR2).congr (Eventually.of_forall fun ω => by ring)
  have hIQR : Integrable (fun ω => Q ω * R ω) μ := integrable_mul_of_memLp_two hQ2 hR2
  have hIA4 : Integrable (fun ω => A ω ^ 4) μ :=
    (integrable_mul_of_memLp_two hAA hAA).congr (Eventually.of_forall fun ω => by ring)
  -- the coefficient functions of the powers of `A`
  have hG3m : Measurable fun z : ℝ × ℝ => 2 * ca ^ 2 * da * z.2 + 2 * ca * da ^ 2 * z.1 := by
    fun_prop
  have hG2m : Measurable fun z : ℝ × ℝ =>
      ca ^ 2 * z.2 ^ 2 + 4 * (ca * da) * (z.1 * z.2) + da ^ 2 * z.1 ^ 2 := by fun_prop
  have hG1m : Measurable fun z : ℝ × ℝ =>
      2 * ca * (z.1 * z.2 ^ 2) + 2 * da * (z.1 ^ 2 * z.2) := by fun_prop
  have hind3 : IndepFun (fun ω => A ω ^ 3)
      (fun ω => 2 * ca ^ 2 * da * R ω + 2 * ca * da ^ 2 * Q ω) μ :=
    hind.comp (measurable_id.pow_const 3) hG3m
  have hind2 : IndepFun (fun ω => A ω ^ 2)
      (fun ω => ca ^ 2 * R ω ^ 2 + 4 * (ca * da) * (Q ω * R ω) + da ^ 2 * Q ω ^ 2) μ :=
    hind.comp (measurable_id.pow_const 2) hG2m
  have hind1 : IndepFun A
      (fun ω => 2 * ca * (Q ω * R ω ^ 2) + 2 * da * (Q ω ^ 2 * R ω)) μ :=
    hind.comp measurable_id hG1m
  -- L⁴/L² membership of the coefficient functions
  have hG3four : MemLp (fun ω => 2 * ca ^ 2 * da * R ω + 2 * ca * da ^ 2 * Q ω) 4 μ :=
    (hR4.const_mul _).add (hQ4.const_mul _)
  have hRsq2 : MemLp (fun ω => R ω ^ 2) 2 μ :=
    MemLp.ae_eq (Eventually.of_forall fun ω => (by ring : R ω * R ω = R ω ^ 2)) hRRm
  have hQsq2 : MemLp (fun ω => Q ω ^ 2) 2 μ :=
    MemLp.ae_eq (Eventually.of_forall fun ω => (by ring : Q ω * Q ω = Q ω ^ 2)) hQQm
  have hG2two : MemLp
      (fun ω => ca ^ 2 * R ω ^ 2 + 4 * (ca * da) * (Q ω * R ω) + da ^ 2 * Q ω ^ 2) 2 μ :=
    ((hRsq2.const_mul _).add (hQRm.const_mul _)).add (hQsq2.const_mul _)
  -- integrability of the five blocks
  have hIT4 : Integrable (fun ω => ca ^ 2 * da ^ 2 * A ω ^ 4) μ := hIA4.const_mul _
  have hIT3 : Integrable
      (fun ω => A ω ^ 3 * (2 * ca ^ 2 * da * R ω + 2 * ca * da ^ 2 * Q ω)) μ := by
    refine (integrable_mul_of_memLp_two hAA (memLp_two_mul_of_memLp_four hA4 hG3four)).congr
      (Eventually.of_forall fun ω => by ring)
  have hIT2 : Integrable (fun ω => A ω ^ 2 *
      (ca ^ 2 * R ω ^ 2 + 4 * (ca * da) * (Q ω * R ω) + da ^ 2 * Q ω ^ 2)) μ := by
    refine (integrable_mul_of_memLp_two hAA hG2two).congr (Eventually.of_forall fun ω => by ring)
  have hIT1 : Integrable
      (fun ω => A ω * (2 * ca * (Q ω * R ω ^ 2) + 2 * da * (Q ω ^ 2 * R ω))) μ := by
    have h1 : Integrable (fun ω => 2 * ca * ((A ω * Q ω) * (R ω * R ω))) μ :=
      (integrable_mul_of_memLp_two hAQ hRRm).const_mul _
    have h2 : Integrable (fun ω => 2 * da * ((A ω * R ω) * (Q ω * Q ω))) μ :=
      (integrable_mul_of_memLp_two hAR hQQm).const_mul _
    exact (h1.add h2).congr (Eventually.of_forall fun ω => by
      simp only [Pi.add_apply]; ring)
  have hIT0 : Integrable (fun ω => Q ω ^ 2 * R ω ^ 2) μ :=
    (integrable_mul_of_memLp_two hQRm hQRm).congr (Eventually.of_forall fun ω => by ring)
  -- the values of the five blocks
  have hIG3 : ∫ ω, (2 * ca ^ 2 * da * R ω + 2 * ca * da ^ 2 * Q ω) ∂μ = 0 := by
    rw [integral_add ((hR2.integrable one_le_two).const_mul _)
        ((hQ2.integrable one_le_two).const_mul _),
      integral_const_mul, integral_const_mul, hQ1, hR1]
    ring
  have hIG2 : ∫ ω, (ca ^ 2 * R ω ^ 2 + 4 * (ca * da) * (Q ω * R ω) + da ^ 2 * Q ω ^ 2) ∂μ
      = ca ^ 2 * r + 4 * (ca * da) * m + da ^ 2 * q := by
    have ha1 : Integrable (fun ω => ca ^ 2 * R ω ^ 2 + 4 * (ca * da) * (Q ω * R ω)) μ :=
      (hIRsq.const_mul _).add (hIQR.const_mul _)
    rw [integral_add ha1 (hIQsq.const_mul _),
      integral_add (hIRsq.const_mul _) (hIQR.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, hQQ, hRR, hQR]
  have hA3m : AEStronglyMeasurable (fun ω => A ω ^ 3) μ :=
    (hA4.aestronglyMeasurable.aemeasurable.pow_const 3).aestronglyMeasurable
  have hA2m : AEStronglyMeasurable (fun ω => A ω ^ 2) μ :=
    (hA4.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable
  have hV4 : ∫ ω, ca ^ 2 * da ^ 2 * A ω ^ 4 ∂μ = ca ^ 2 * da ^ 2 * v4 := by
    rw [integral_const_mul, hA4i]
  have hV3 : ∫ ω, A ω ^ 3 * (2 * ca ^ 2 * da * R ω + 2 * ca * da ^ 2 * Q ω) ∂μ = 0 := by
    rw [hind3.integral_fun_mul_eq_mul_integral hA3m hG3four.aestronglyMeasurable, hIG3, mul_zero]
  have hV2 : ∫ ω, A ω ^ 2 *
      (ca ^ 2 * R ω ^ 2 + 4 * (ca * da) * (Q ω * R ω) + da ^ 2 * Q ω ^ 2) ∂μ
      = v2 * (ca ^ 2 * r + 4 * (ca * da) * m + da ^ 2 * q) := by
    rw [hind2.integral_fun_mul_eq_mul_integral hA2m hG2two.aestronglyMeasurable, hIG2, hA2]
  have hV1 : ∫ ω, A ω * (2 * ca * (Q ω * R ω ^ 2) + 2 * da * (Q ω ^ 2 * R ω)) ∂μ = 0 := by
    have hQam : AEStronglyMeasurable Q μ := hQ4.aestronglyMeasurable
    have hRam : AEStronglyMeasurable R μ := hR4.aestronglyMeasurable
    have hQ2am : AEStronglyMeasurable (fun ω => Q ω ^ 2) μ :=
      (hQam.aemeasurable.pow_const 2).aestronglyMeasurable
    have hR2am : AEStronglyMeasurable (fun ω => R ω ^ 2) μ :=
      (hRam.aemeasurable.pow_const 2).aestronglyMeasurable
    have hG1am : AEStronglyMeasurable
        (fun ω => 2 * ca * (Q ω * R ω ^ 2) + 2 * da * (Q ω ^ 2 * R ω)) μ :=
      ((hQam.mul hR2am).const_mul _).add ((hQ2am.mul hRam).const_mul _)
    rw [hind1.integral_fun_mul_eq_mul_integral hA4.aestronglyMeasurable hG1am, hA1, zero_mul]
  -- assembly
  have hpt : ∀ ω, (ca * A ω + Q ω) ^ 2 * (da * A ω + R ω) ^ 2
      = (ca ^ 2 * da ^ 2 * A ω ^ 4
          + A ω ^ 3 * (2 * ca ^ 2 * da * R ω + 2 * ca * da ^ 2 * Q ω)
          + A ω ^ 2 * (ca ^ 2 * R ω ^ 2 + 4 * (ca * da) * (Q ω * R ω) + da ^ 2 * Q ω ^ 2)
          + A ω * (2 * ca * (Q ω * R ω ^ 2) + 2 * da * (Q ω ^ 2 * R ω)))
        + Q ω ^ 2 * R ω ^ 2 := fun ω => by ring
  have hb1 : Integrable (fun ω => ca ^ 2 * da ^ 2 * A ω ^ 4
      + A ω ^ 3 * (2 * ca ^ 2 * da * R ω + 2 * ca * da ^ 2 * Q ω)) μ := hIT4.add hIT3
  have hb2 : Integrable (fun ω => (ca ^ 2 * da ^ 2 * A ω ^ 4
      + A ω ^ 3 * (2 * ca ^ 2 * da * R ω + 2 * ca * da ^ 2 * Q ω))
      + A ω ^ 2 * (ca ^ 2 * R ω ^ 2 + 4 * (ca * da) * (Q ω * R ω) + da ^ 2 * Q ω ^ 2)) μ :=
    hb1.add hIT2
  have hb3 : Integrable (fun ω => ((ca ^ 2 * da ^ 2 * A ω ^ 4
      + A ω ^ 3 * (2 * ca ^ 2 * da * R ω + 2 * ca * da ^ 2 * Q ω))
      + A ω ^ 2 * (ca ^ 2 * R ω ^ 2 + 4 * (ca * da) * (Q ω * R ω) + da ^ 2 * Q ω ^ 2))
      + A ω * (2 * ca * (Q ω * R ω ^ 2) + 2 * da * (Q ω ^ 2 * R ω))) μ := hb2.add hIT1
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add hb3 hIT0, integral_add hb2 hIT1, integral_add hb1 hIT2,
    integral_add hIT4 hIT3, hV4, hV3, hV2, hV1, hP]
  ring

/-! #### The fourth-moment identity itself -/

private lemma indepFun_noise_pair [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (c d : ℤ → ℝ) {a : ℤ} {s : Finset ℤ} (ha : a ∉ s) :
    IndepFun (ε a) (fun ω => ((∑ i ∈ s, c i * ε i ω), (∑ i ∈ s, d i * ε i ω))) μ := by
  have hbig : IndepFun (ε a) (fun ω (i : s) => ε (i : ℤ) ω) μ := by
    have h := hε.iIndep.indepFun_finset ({a} : Finset ℤ) s
      (Finset.disjoint_singleton_left.2 ha) hε.measurable
    exact h.comp (measurable_pi_apply ⟨a, Finset.mem_singleton_self a⟩) measurable_id
  have hψ : Measurable
      (fun y : (i : s) → ℝ => ((∑ i : s, c i * y i), (∑ i : s, d i * y i))) := by
    refine Measurable.prodMk ?_ ?_ <;>
      exact Finset.measurable_sum Finset.univ fun i _ => (measurable_pi_apply i).const_mul _
  have h2 := hbig.comp measurable_id hψ
  refine h2.congr (Eventually.of_forall fun ω => rfl) (Eventually.of_forall fun ω => ?_)
  simp only [Function.comp_apply]
  rw [Finset.sum_coe_sort s (fun i => c i * ε i ω),
    Finset.sum_coe_sort s (fun i => d i * ε i ω)]

private theorem integral_sq_mul_sq_noiseComb [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (hε4 : MemLp (ε 0) 4 μ) (c d : ℤ → ℝ) (s : Finset ℤ) :
    ∫ ω, (∑ i ∈ s, c i * ε i ω) ^ 2 * (∑ i ∈ s, d i * ε i ω) ^ 2 ∂μ
      = ((∫ ω, ε 0 ω ^ 4 ∂μ) - 3 * σ2 ^ 2) * (∑ i ∈ s, c i ^ 2 * d i ^ 2)
        + σ2 ^ 2 * ((∑ i ∈ s, c i ^ 2) * (∑ i ∈ s, d i ^ 2)
          + 2 * (∑ i ∈ s, c i * d i) ^ 2) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hQ4 : MemLp (fun ω => ∑ i ∈ s, c i * ε i ω) 4 μ :=
      memLp_finset_sum s fun i _ => (hε.memLp_four hε4 i).const_mul (c i)
    have hR4 : MemLp (fun ω => ∑ i ∈ s, d i * ε i ω) 4 μ :=
      memLp_finset_sum s fun i _ => (hε.memLp_four hε4 i).const_mul (d i)
    have hQQ : ∫ ω, (∑ i ∈ s, c i * ε i ω) ^ 2 ∂μ = σ2 * ∑ i ∈ s, c i ^ 2 := by
      rw [show (∑ i ∈ s, c i ^ 2) = ∑ i ∈ s, c i * c i from
          Finset.sum_congr rfl fun i _ => pow_two (c i),
        ← integral_noiseComb_mul hε c c s]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have hRR : ∫ ω, (∑ i ∈ s, d i * ε i ω) ^ 2 ∂μ = σ2 * ∑ i ∈ s, d i ^ 2 := by
      rw [show (∑ i ∈ s, d i ^ 2) = ∑ i ∈ s, d i * d i from
          Finset.sum_congr rfl fun i _ => pow_two (d i),
        ← integral_noiseComb_mul hε d d s]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have hstep := integral_sq_mul_sq_step (μ := μ) (A := ε a)
      (Q := fun ω => ∑ i ∈ s, c i * ε i ω) (R := fun ω => ∑ i ∈ s, d i * ε i ω)
      (ca := c a) (da := d a) (hε.memLp_four hε4 a) hQ4 hR4
      (indepFun_noise_pair hε c d ha) (hε.integral_zero' a) (hε.integral_sq' a)
      (hε.integral_four' a) (integral_noiseComb hε c s) (integral_noiseComb hε d s) hQQ hRR
      (integral_noiseComb_mul hε c d s) ih
    simp only [Finset.sum_cons]
    rw [hstep]
    ring

/-- **(R2), covariance form.** -/
private theorem cov_sq_noiseComb [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (hε4 : MemLp (ε 0) 4 μ) (c d : ℤ → ℝ) (s : Finset ℤ) :
    cov[fun ω => (∑ i ∈ s, c i * ε i ω) ^ 2, fun ω => (∑ i ∈ s, d i * ε i ω) ^ 2; μ]
      = ((∫ ω, ε 0 ω ^ 4 ∂μ) - 3 * σ2 ^ 2) * (∑ i ∈ s, c i ^ 2 * d i ^ 2)
        + 2 * σ2 ^ 2 * (∑ i ∈ s, c i * d i) ^ 2 := by
  have hQ4 : MemLp (fun ω => ∑ i ∈ s, c i * ε i ω) 4 μ :=
    memLp_finset_sum s fun i _ => (hε.memLp_four hε4 i).const_mul (c i)
  have hR4 : MemLp (fun ω => ∑ i ∈ s, d i * ε i ω) 4 μ :=
    memLp_finset_sum s fun i _ => (hε.memLp_four hε4 i).const_mul (d i)
  have hQsq : MemLp (fun ω => (∑ i ∈ s, c i * ε i ω) ^ 2) 2 μ :=
    MemLp.ae_eq (Eventually.of_forall fun ω => (by ring :
      (∑ i ∈ s, c i * ε i ω) * (∑ i ∈ s, c i * ε i ω) = (∑ i ∈ s, c i * ε i ω) ^ 2))
      (memLp_two_mul_of_memLp_four hQ4 hQ4)
  have hRsq : MemLp (fun ω => (∑ i ∈ s, d i * ε i ω) ^ 2) 2 μ :=
    MemLp.ae_eq (Eventually.of_forall fun ω => (by ring :
      (∑ i ∈ s, d i * ε i ω) * (∑ i ∈ s, d i * ε i ω) = (∑ i ∈ s, d i * ε i ω) ^ 2))
      (memLp_two_mul_of_memLp_four hR4 hR4)
  have hQQ : ∫ ω, (∑ i ∈ s, c i * ε i ω) ^ 2 ∂μ = σ2 * ∑ i ∈ s, c i ^ 2 := by
    rw [show (∑ i ∈ s, c i ^ 2) = ∑ i ∈ s, c i * c i from
        Finset.sum_congr rfl fun i _ => pow_two (c i), ← integral_noiseComb_mul hε c c s]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  have hRR : ∫ ω, (∑ i ∈ s, d i * ε i ω) ^ 2 ∂μ = σ2 * ∑ i ∈ s, d i ^ 2 := by
    rw [show (∑ i ∈ s, d i ^ 2) = ∑ i ∈ s, d i * d i from
        Finset.sum_congr rfl fun i _ => pow_two (d i), ← integral_noiseComb_mul hε d d s]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  rw [covariance_eq_sub hQsq hRsq]
  have hprod : ∫ ω, ((fun ω => (∑ i ∈ s, c i * ε i ω) ^ 2) *
      (fun ω => (∑ i ∈ s, d i * ε i ω) ^ 2)) ω ∂μ
      = ∫ ω, (∑ i ∈ s, c i * ε i ω) ^ 2 * (∑ i ∈ s, d i * ε i ω) ^ 2 ∂μ := rfl
  simp only [hprod, integral_sq_mul_sq_noiseComb hε hε4 c d s, hQQ, hRR]
  ring


/-! #### (R2) at four linear forms

The squared identity above polarizes: `4 L_c L_d = L_{c+d}² − L_{c−d}²` in each of the two
slots turns `E[L_c L_d L_e L_f]` into an alternating sum of **four** instances of
`integral_sq_mul_sq_noiseComb`, with no new induction and no new moment hypothesis. The
answer is the Isserlis/Wick formula with the fourth-cumulant correction on the diagonal,

`E[L_c L_d L_e L_f] = (Eε⁴ − 3σ⁴) Σ c_i d_i e_i f_i
      + σ⁴[(Σcd)(Σef) + (Σce)(Σdf) + (Σcf)(Σde)]`,

and its covariance form `cov_prod_noiseComb` drops the `(Σcd)(Σef)` block. Taking
`c = d`, `e = f` recovers `integral_sq_mul_sq_noiseComb`/`cov_sq_noiseComb`, so this is a
strict generalization: it is what (R3) needs (there the object is
`Cov(U_s V_s, U_t V_t)` with `U = X − X^{(N)}`, `V = X + X^{(N)}`, a product of two
*different* linear forms) and what the joint Bartlett covariances need (products of lagged
pairs `X_t X_{t−i}`, again never a square). -/

/-- **(R2) at four linear forms**, by bilinear polarization of the squared version. -/
private theorem integral_prod_four_noiseComb [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (hε4 : MemLp (ε 0) 4 μ) (c d e f : ℤ → ℝ) (s : Finset ℤ) :
    ∫ ω, (∑ i ∈ s, c i * ε i ω) * (∑ i ∈ s, d i * ε i ω) *
        (∑ i ∈ s, e i * ε i ω) * (∑ i ∈ s, f i * ε i ω) ∂μ
      = ((∫ ω, ε 0 ω ^ 4 ∂μ) - 3 * σ2 ^ 2) * (∑ i ∈ s, c i * d i * e i * f i)
        + σ2 ^ 2 * ((∑ i ∈ s, c i * d i) * (∑ i ∈ s, e i * f i)
          + (∑ i ∈ s, c i * e i) * (∑ i ∈ s, d i * f i)
          + (∑ i ∈ s, c i * f i) * (∑ i ∈ s, d i * e i)) := by
  classical
  -- `L u` is the linear form with weights `u`
  have hL4 : ∀ u : ℤ → ℝ, MemLp (fun ω => ∑ i ∈ s, u i * ε i ω) 4 μ := fun u =>
    memLp_finset_sum s fun i _ => (hε.memLp_four hε4 i).const_mul (u i)
  have hInt : ∀ u v w z : ℤ → ℝ, Integrable (fun ω => (∑ i ∈ s, u i * ε i ω) *
      (∑ i ∈ s, v i * ε i ω) * ((∑ i ∈ s, w i * ε i ω) * (∑ i ∈ s, z i * ε i ω))) μ :=
    fun u v w z => integrable_mul_of_memLp_two
      (memLp_two_mul_of_memLp_four (hL4 u) (hL4 v)) (memLp_two_mul_of_memLp_four (hL4 w) (hL4 z))
  have hIntSq : ∀ u v : ℤ → ℝ, Integrable (fun ω =>
      (∑ i ∈ s, u i * ε i ω) ^ 2 * (∑ i ∈ s, v i * ε i ω) ^ 2) μ := by
    intro u v
    refine (hInt u u v v).congr (Eventually.of_forall fun ω => by ring)
  -- the four polarized linear forms
  have hadd : ∀ u v : ℤ → ℝ, ∀ ω, (∑ i ∈ s, (u i + v i) * ε i ω)
      = (∑ i ∈ s, u i * ε i ω) + (∑ i ∈ s, v i * ε i ω) := by
    intro u v ω
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsub : ∀ u v : ℤ → ℝ, ∀ ω, (∑ i ∈ s, (u i - v i) * ε i ω)
      = (∑ i ∈ s, u i * ε i ω) - (∑ i ∈ s, v i * ε i ω) := by
    intro u v ω
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- the pointwise polarization identity
  have hpt : ∀ ω, (16 : ℝ) * ((∑ i ∈ s, c i * ε i ω) * (∑ i ∈ s, d i * ε i ω) *
      ((∑ i ∈ s, e i * ε i ω) * (∑ i ∈ s, f i * ε i ω)))
      = (∑ i ∈ s, (c i + d i) * ε i ω) ^ 2 * (∑ i ∈ s, (e i + f i) * ε i ω) ^ 2
        - (∑ i ∈ s, (c i + d i) * ε i ω) ^ 2 * (∑ i ∈ s, (e i - f i) * ε i ω) ^ 2
        - (∑ i ∈ s, (c i - d i) * ε i ω) ^ 2 * (∑ i ∈ s, (e i + f i) * ε i ω) ^ 2
        + (∑ i ∈ s, (c i - d i) * ε i ω) ^ 2 * (∑ i ∈ s, (e i - f i) * ε i ω) ^ 2 := by
    intro ω
    rw [hadd c d ω, hadd e f ω, hsub c d ω, hsub e f ω]
    ring
  -- integrate the identity
  have hint16 : (16 : ℝ) * ∫ ω, (∑ i ∈ s, c i * ε i ω) * (∑ i ∈ s, d i * ε i ω) *
      ((∑ i ∈ s, e i * ε i ω) * (∑ i ∈ s, f i * ε i ω)) ∂μ
      = (∫ ω, (∑ i ∈ s, (c i + d i) * ε i ω) ^ 2 * (∑ i ∈ s, (e i + f i) * ε i ω) ^ 2 ∂μ)
        - (∫ ω, (∑ i ∈ s, (c i + d i) * ε i ω) ^ 2 * (∑ i ∈ s, (e i - f i) * ε i ω) ^ 2 ∂μ)
        - (∫ ω, (∑ i ∈ s, (c i - d i) * ε i ω) ^ 2 * (∑ i ∈ s, (e i + f i) * ε i ω) ^ 2 ∂μ)
        + (∫ ω, (∑ i ∈ s, (c i - d i) * ε i ω) ^ 2 * (∑ i ∈ s, (e i - f i) * ε i ω) ^ 2 ∂μ) := by
    have h0 : (16 : ℝ) * ∫ ω, (∑ i ∈ s, c i * ε i ω) * (∑ i ∈ s, d i * ε i ω) *
        ((∑ i ∈ s, e i * ε i ω) * (∑ i ∈ s, f i * ε i ω)) ∂μ
        = ∫ ω, (16 : ℝ) * ((∑ i ∈ s, c i * ε i ω) * (∑ i ∈ s, d i * ε i ω) *
          ((∑ i ∈ s, e i * ε i ω) * (∑ i ∈ s, f i * ε i ω))) ∂μ :=
      (integral_const_mul _ _).symm
    have hquad : ∀ A B C D : Ω → ℝ, Integrable A μ → Integrable B μ → Integrable C μ →
        Integrable D μ → ∫ ω, (A ω - B ω - C ω + D ω) ∂μ
          = (∫ ω, A ω ∂μ) - (∫ ω, B ω ∂μ) - (∫ ω, C ω ∂μ) + (∫ ω, D ω ∂μ) := by
      intro A B C D hA hB hC hD
      have iAB : Integrable (fun ω => A ω - B ω) μ := hA.sub hB
      have iABC : Integrable (fun ω => A ω - B ω - C ω) μ := iAB.sub hC
      rw [integral_add iABC hD, integral_sub iAB hC, integral_sub hA hB]
    rw [h0, integral_congr_ae (Eventually.of_forall hpt),
      hquad _ _ _ _ (hIntSq _ _) (hIntSq _ _) (hIntSq _ _) (hIntSq _ _)]
  rw [integral_sq_mul_sq_noiseComb hε hε4 (fun i => c i + d i) (fun i => e i + f i) s,
    integral_sq_mul_sq_noiseComb hε hε4 (fun i => c i + d i) (fun i => e i - f i) s,
    integral_sq_mul_sq_noiseComb hε hε4 (fun i => c i - d i) (fun i => e i + f i) s,
    integral_sq_mul_sq_noiseComb hε hε4 (fun i => c i - d i) (fun i => e i - f i) s] at hint16
  -- the four polarized weight vectors, in terms of the ten basic sums
  have hsqA : ∀ u v : ℤ → ℝ, ∑ i ∈ s, (u i + v i) ^ 2
      = (∑ i ∈ s, u i ^ 2) + (∑ i ∈ s, v i ^ 2) + 2 * ∑ i ∈ s, u i * v i := by
    intro u v
    have h : ∀ i, (u i + v i) ^ 2 = u i ^ 2 + v i ^ 2 + 2 * (u i * v i) := fun i => by ring
    simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsqS : ∀ u v : ℤ → ℝ, ∑ i ∈ s, (u i - v i) ^ 2
      = (∑ i ∈ s, u i ^ 2) + (∑ i ∈ s, v i ^ 2) - 2 * ∑ i ∈ s, u i * v i := by
    intro u v
    have h : ∀ i, (u i - v i) ^ 2 = u i ^ 2 + v i ^ 2 - 2 * (u i * v i) := fun i => by ring
    simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hcr : ∀ (u v w z : ℤ → ℝ), ∑ i ∈ s, (u i + v i) * (w i + z i)
      = (∑ i ∈ s, u i * w i) + (∑ i ∈ s, u i * z i)
        + (∑ i ∈ s, v i * w i) + (∑ i ∈ s, v i * z i) := by
    intro u v w z
    have h : ∀ i, (u i + v i) * (w i + z i)
        = u i * w i + u i * z i + (v i * w i + v i * z i) := fun i => by ring
    simp only [h, Finset.sum_add_distrib]
    ring
  have hcr2 : ∀ (u v w z : ℤ → ℝ), ∑ i ∈ s, (u i + v i) * (w i - z i)
      = (∑ i ∈ s, u i * w i) - (∑ i ∈ s, u i * z i)
        + (∑ i ∈ s, v i * w i) - (∑ i ∈ s, v i * z i) := by
    intro u v w z
    have h : ∀ i, (u i + v i) * (w i - z i)
        = u i * w i - u i * z i + (v i * w i - v i * z i) := fun i => by ring
    simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  have hcr3 : ∀ (u v w z : ℤ → ℝ), ∑ i ∈ s, (u i - v i) * (w i + z i)
      = (∑ i ∈ s, u i * w i) + (∑ i ∈ s, u i * z i)
        - (∑ i ∈ s, v i * w i) - (∑ i ∈ s, v i * z i) := by
    intro u v w z
    have h : ∀ i, (u i - v i) * (w i + z i)
        = u i * w i + u i * z i - (v i * w i + v i * z i) := fun i => by ring
    simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have hcr4 : ∀ (u v w z : ℤ → ℝ), ∑ i ∈ s, (u i - v i) * (w i - z i)
      = (∑ i ∈ s, u i * w i) - (∑ i ∈ s, u i * z i)
        - (∑ i ∈ s, v i * w i) + (∑ i ∈ s, v i * z i) := by
    intro u v w z
    have h : ∀ i, (u i - v i) * (w i - z i)
        = u i * w i - u i * z i - (v i * w i - v i * z i) := fun i => by ring
    simp only [h, Finset.sum_sub_distrib]
    ring
  -- the diagonal (`η`) block collapses to `16 Σ c d e f`
  have hdiag : (∑ i ∈ s, (c i + d i) ^ 2 * (e i + f i) ^ 2)
      - (∑ i ∈ s, (c i + d i) ^ 2 * (e i - f i) ^ 2)
      - (∑ i ∈ s, (c i - d i) ^ 2 * (e i + f i) ^ 2)
      + (∑ i ∈ s, (c i - d i) ^ 2 * (e i - f i) ^ 2)
      = 16 * ∑ i ∈ s, c i * d i * e i * f i := by
    have h := Finset.sum_congr (rfl : s = s) fun i (_ : i ∈ s) => (by ring :
      (c i + d i) ^ 2 * (e i + f i) ^ 2 - (c i + d i) ^ 2 * (e i - f i) ^ 2
        - (c i - d i) ^ 2 * (e i + f i) ^ 2 + (c i - d i) ^ 2 * (e i - f i) ^ 2
        = 16 * (c i * d i * e i * f i))
    simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using h
  simp only [hsqA, hsqS, hcr, hcr2, hcr3, hcr4] at hint16
  have hgoal : ∫ ω, (∑ i ∈ s, c i * ε i ω) * (∑ i ∈ s, d i * ε i ω) *
      (∑ i ∈ s, e i * ε i ω) * (∑ i ∈ s, f i * ε i ω) ∂μ
      = ∫ ω, (∑ i ∈ s, c i * ε i ω) * (∑ i ∈ s, d i * ε i ω) *
        ((∑ i ∈ s, e i * ε i ω) * (∑ i ∈ s, f i * ε i ω)) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by ring)
  rw [hgoal]
  linear_combination hint16 / 16 + ((∫ ω, ε 0 ω ^ 4 ∂μ) - 3 * σ2 ^ 2) / 16 * hdiag


/-- **(R2) at four linear forms, covariance form** — the Isserlis/Wick formula with the
fourth-cumulant correction on the diagonal. -/
private theorem cov_prod_noiseComb [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (hε4 : MemLp (ε 0) 4 μ) (c d e f : ℤ → ℝ) (s : Finset ℤ) :
    cov[fun ω => (∑ i ∈ s, c i * ε i ω) * (∑ i ∈ s, d i * ε i ω),
        fun ω => (∑ i ∈ s, e i * ε i ω) * (∑ i ∈ s, f i * ε i ω); μ]
      = ((∫ ω, ε 0 ω ^ 4 ∂μ) - 3 * σ2 ^ 2) * (∑ i ∈ s, c i * d i * e i * f i)
        + σ2 ^ 2 * ((∑ i ∈ s, c i * e i) * (∑ i ∈ s, d i * f i)
          + (∑ i ∈ s, c i * f i) * (∑ i ∈ s, d i * e i)) := by
  have hL4 : ∀ u : ℤ → ℝ, MemLp (fun ω => ∑ i ∈ s, u i * ε i ω) 4 μ := fun u =>
    memLp_finset_sum s fun i _ => (hε.memLp_four hε4 i).const_mul (u i)
  rw [covariance_eq_sub (memLp_two_mul_of_memLp_four (hL4 c) (hL4 d))
    (memLp_two_mul_of_memLp_four (hL4 e) (hL4 f))]
  have hprod : ∫ ω, ((fun ω => (∑ i ∈ s, c i * ε i ω) * (∑ i ∈ s, d i * ε i ω)) *
      (fun ω => (∑ i ∈ s, e i * ε i ω) * (∑ i ∈ s, f i * ε i ω))) ω ∂μ
      = ∫ ω, (∑ i ∈ s, c i * ε i ω) * (∑ i ∈ s, d i * ε i ω) *
        (∑ i ∈ s, e i * ε i ω) * (∑ i ∈ s, f i * ε i ω) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by simp only [Pi.mul_apply]; ring)
  rw [hprod, integral_prod_four_noiseComb hε hε4 c d e f s,
    integral_noiseComb_mul hε c d s, integral_noiseComb_mul hε e f s]
  ring

end FourthMoment

/-! ### (R4)'s dependence input: the autocovariance of the two-sided linear process

`γ(h) = σ² Σ_k a_k a_{k−h}` (`acvf_eq_tsum_of_filter`), derived from the `L²`
representation `hfil` alone — no rate on `a`, no stationarity input, and no separate
mean hypothesis (`E X_t = 0` is *derived* here, `integral_eq_zero_of_filter`). This is
the identity (R4) needs to match the limiting variance produced by (R1)+(R2) to the
frozen `(η−3)γ(0)² + 2 Σ_j γ(j)²`, and it is also what turns `bartlettW`'s `acf`
entries into the coefficient series of FY eq. (2.26).

The route: the two truncated filters have an *exact* second moment
(`integral_truncFilter_mul`, a double sum over the two windows collapsed by
`integral_noise_mul_noise` — no reindexing of the innovations is needed, the Kronecker
delta `s − k = t − l` does the bookkeeping), the bilinear form `(U, V) ↦ ∫ U V` is
`L²`-continuous (`abs_integral_mul_sub_le`, from the Cauchy–Schwarz brick
`abs_integral_mul_le_sqrt`), and the window constraint `k ∈ A ∧ k − h ∈ A` exhausts `ℤ`,
so the partial sums converge to the `tsum` (`tendsto_partial_shift`). The `ℓ¹`
hypothesis `ha` enters *only* in the last of these, and only to make
`k ↦ a_k a_{k−h}` summable — `|a_{k−h}| ≤ Σ_j |a_j|` bounds one factor.
-/

section LinearAcvf

variable {a : ℤ → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}

private lemma abs_integral_mul_le_sqrt [IsProbabilityMeasure μ] {U V : Ω → ℝ}
    (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) :
    |∫ ω, U ω * V ω ∂μ| ≤ Real.sqrt (∫ ω, U ω ^ 2 ∂μ) * Real.sqrt (∫ ω, V ω ^ 2 ∂μ) := by
  have habs : ∀ f : Ω → ℝ, MemLp f 2 μ → MemLp (fun ω => |f ω|) (ENNReal.ofReal (2 : ℝ)) μ := by
    intro f hf
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact hf.abs
  have hpt : ∀ (f : Ω → ℝ) (ω : Ω), |f ω| ^ (2 : ℝ) = f ω ^ 2 := by
    intro f ω
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun ω => abs_nonneg (U ω))
    (Filter.Eventually.of_forall fun ω => abs_nonneg (V ω)) (habs U hU) (habs V hV)
  rw [integral_congr_ae (Filter.Eventually.of_forall (hpt U)),
    integral_congr_ae (Filter.Eventually.of_forall (hpt V)),
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h2
  refine le_trans ?_ h2
  calc |∫ ω, U ω * V ω ∂μ| ≤ ∫ ω, |U ω * V ω| ∂μ := abs_integral_le_integral_abs
  _ = ∫ ω, |U ω| * |V ω| ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => abs_mul _ _)


/-- `L²`-convergence in the `eLpNorm` currency gives convergence of the root second
moments. -/
private lemma tendsto_sqrt_integral_sq_of_eLpNorm {f : ℕ → Ω → ℝ}
    (hm : ∀ N, AEStronglyMeasurable (f N) μ)
    (h : Tendsto (fun N => eLpNorm (f N) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun N => Real.sqrt (∫ ω, f N ω ^ 2 ∂μ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hev : ∀ᶠ N in atTop, eLpNorm (f N) 2 μ < ENNReal.ofReal (δ / 2) :=
    h.eventually (eventually_lt_nhds (by simpa using half_pos hδ))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨N0, fun N hN => ?_⟩
  have hb := integral_sq_le_of_eLpNorm_two (half_pos hδ).le (hm N) (hN0 N hN).le
  have hnn : (0 : ℝ) ≤ ∫ ω, f N ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have : Real.sqrt (∫ ω, f N ω ^ 2 ∂μ) ≤ δ / 2 := by
    calc Real.sqrt (∫ ω, f N ω ^ 2 ∂μ) ≤ Real.sqrt ((δ / 2) ^ 2) := Real.sqrt_le_sqrt hb
    _ = δ / 2 := Real.sqrt_sq (half_pos hδ).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)]
  linarith

section Acvf
variable {a : ℤ → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}

/-- The exact second moment of a pair of truncated filters. -/
private lemma integral_truncFilter_mul [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (A : Finset ℤ) (h : ℤ) :
    ∫ ω, (∑ k ∈ A, a k * ε (h - k) ω) * (∑ l ∈ A, a l * ε (0 - l) ω) ∂μ
      = σ2 * ∑ k ∈ A, (if k - h ∈ A then a k * a (k - h) else 0) := by
  have hI : ∀ k l : ℤ, Integrable (fun ω => (a k * a l) * (ε (h - k) ω * ε (0 - l) ω)) μ :=
    fun k l => (integrable_mul_of_memLp_two (hε.memLp_two_of_iid _)
      (hε.memLp_two_of_iid _)).const_mul _
  have hpt : ∀ ω, (∑ k ∈ A, a k * ε (h - k) ω) * (∑ l ∈ A, a l * ε (0 - l) ω)
      = ∑ k ∈ A, ∑ l ∈ A, (a k * a l) * (ε (h - k) ω * ε (0 - l) ω) := by
    intro ω
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finset_sum A (fun k _ => integrable_finset_sum A fun l _ => hI k l)]
  have hstep : ∀ k ∈ A, ∫ ω, ∑ l ∈ A, (a k * a l) * (ε (h - k) ω * ε (0 - l) ω) ∂μ
      = σ2 * (if k - h ∈ A then a k * a (k - h) else 0) := by
    intro k _
    rw [integral_finset_sum A (fun l _ => hI k l)]
    simp only [integral_const_mul, integral_noise_mul_noise hε]
    rw [Finset.sum_congr rfl (fun l _ =>
      show a k * a l * (if h - k = 0 - l then σ2 else 0)
        = a k * a l * (if k - h = l then σ2 else 0) from
      congrArg (fun z => a k * a l * z) (if_congr (by omega) rfl rfl))]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq A (k - h) (fun l => a k * a l * σ2)]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]

variable (hε : IsIIDNoise ε σ2 μ)
  (hfil : ∀ t : ℤ, Tendsto (fun N : ℕ => eLpNorm (fun ω => X t ω -
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))

include hε in
private lemma memLp_truncFilter (A : Finset ℤ) (t : ℤ) :
    MemLp (fun ω => ∑ k ∈ A, a k * ε (t - k) ω) 2 μ :=
  memLp_finset_sum A fun k _ => (hε.memLp_two_of_iid (t - k)).const_mul (a k)

include hε in
private lemma integral_truncFilter_eq_zero [IsProbabilityMeasure μ] (A : Finset ℤ) (t : ℤ) :
    ∫ ω, ∑ k ∈ A, a k * ε (t - k) ω ∂μ = 0 := by
  rw [integral_finset_sum A
    (fun k _ => ((hε.memLp_two_of_iid (t - k)).integrable one_le_two).const_mul (a k))]
  simp only [integral_const_mul, hε.integral_zero', mul_zero, Finset.sum_const_zero]

include hε hfil in
private lemma memLp_two_of_filter [IsProbabilityMeasure μ] (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    MemLp (X t) 2 μ := by
  obtain ⟨N, hN⟩ := ((hfil t).eventually_lt_const (by norm_num : (0 : ENNReal) < 1)).exists
  have hmd : AEStronglyMeasurable (fun ω => X t ω -
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) μ :=
    (((hmeas t).sub (Finset.measurable_sum _ fun k _ =>
      (hε.measurable (t - k)).const_mul (a k)))).aestronglyMeasurable
  have hd : MemLp (fun ω => X t ω -
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) 2 μ :=
    ⟨hmd, lt_of_lt_of_le hN (by norm_num)⟩
  have := hd.add (memLp_truncFilter (a := a) hε (Finset.Icc (-(N : ℤ)) (N : ℤ)) t)
  refine MemLp.ae_eq (Eventually.of_forall fun ω => ?_) this
  simp only [Pi.add_apply]
  ring

include hε hfil in
private lemma tendsto_sqrt_defect (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    Tendsto (fun N : ℕ => Real.sqrt (∫ ω, (X t ω -
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) ^ 2 ∂μ)) atTop (𝓝 0) :=
  tendsto_sqrt_integral_sq_of_eLpNorm
    (fun _ => (((hmeas t).sub (Finset.measurable_sum _ fun k _ =>
      (hε.measurable (t - k)).const_mul (a k)))).aestronglyMeasurable) (hfil t)

include hε hfil in
private lemma integral_eq_zero_of_filter [IsProbabilityMeasure μ] (hmeas : ∀ t, Measurable (X t))
    (t : ℤ) : ∫ ω, X t ω ∂μ = 0 := by
  have hXm := memLp_two_of_filter hε hfil hmeas t
  have hbound : ∀ N : ℕ, |∫ ω, X t ω ∂μ| ≤ Real.sqrt (∫ ω, (X t ω -
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) ^ 2 ∂μ) := by
    intro N
    have hd : MemLp (fun ω => X t ω -
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) 2 μ :=
      hXm.sub (memLp_truncFilter (a := a) hε (Finset.Icc (-(N : ℤ)) (N : ℤ)) t)
    have hcs := abs_integral_mul_le_sqrt hd (memLp_const (μ := μ) (1 : ℝ))
    have he1 : ∫ ω, (X t ω -
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) * (1 : ℝ) ∂μ
        = ∫ ω, X t ω ∂μ := by
      rw [integral_congr_ae (Eventually.of_forall fun ω => mul_one _),
        integral_sub (hXm.integrable one_le_two)
          ((memLp_truncFilter (a := a) hε (Finset.Icc (-(N : ℤ)) (N : ℤ)) t).integrable one_le_two),
        integral_truncFilter_eq_zero (a := a) hε (Finset.Icc (-(N : ℤ)) (N : ℤ)) t, sub_zero]
    rw [he1] at hcs
    simpa using hcs
  have := ge_of_tendsto (tendsto_sqrt_defect hε hfil hmeas t)
    (Eventually.of_forall hbound)
  exact abs_eq_zero.1 (le_antisymm this (abs_nonneg _))

end Acvf

/-- `L²` continuity of the bilinear form `(U, V) ↦ ∫ U V`. -/
private lemma abs_integral_mul_sub_le [IsProbabilityMeasure μ] {U V U' V' : Ω → ℝ}
    (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) (hU' : MemLp U' 2 μ) (hV' : MemLp V' 2 μ) :
    |∫ ω, U ω * V ω ∂μ - ∫ ω, U' ω * V' ω ∂μ|
      ≤ Real.sqrt (∫ ω, (U ω - U' ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, V ω ^ 2 ∂μ)
        + Real.sqrt (∫ ω, U ω ^ 2 ∂μ) * Real.sqrt (∫ ω, (V ω - V' ω) ^ 2 ∂μ)
        + Real.sqrt (∫ ω, (U ω - U' ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, (V ω - V' ω) ^ 2 ∂μ) := by
  have hdU : MemLp (fun ω => U ω - U' ω) 2 μ := hU.sub hU'
  have hdV : MemLp (fun ω => V ω - V' ω) 2 μ := hV.sub hV'
  have i1 : Integrable (fun ω => (U ω - U' ω) * V ω) μ := integrable_mul_of_memLp_two hdU hV
  have i2 : Integrable (fun ω => U ω * (V ω - V' ω)) μ := integrable_mul_of_memLp_two hU hdV
  have i3 : Integrable (fun ω => (U ω - U' ω) * (V ω - V' ω)) μ :=
    integrable_mul_of_memLp_two hdU hdV
  have iUV : Integrable (fun ω => U ω * V ω) μ := integrable_mul_of_memLp_two hU hV
  have iUV' : Integrable (fun ω => U' ω * V' ω) μ := integrable_mul_of_memLp_two hU' hV'
  have h12 : Integrable (fun ω => (U ω - U' ω) * V ω + U ω * (V ω - V' ω)) μ := i1.add i2
  have e : ∫ ω, U ω * V ω ∂μ - ∫ ω, U' ω * V' ω ∂μ
      = (∫ ω, (U ω - U' ω) * V ω ∂μ + ∫ ω, U ω * (V ω - V' ω) ∂μ)
        - ∫ ω, (U ω - U' ω) * (V ω - V' ω) ∂μ := by
    rw [← integral_sub iUV iUV', ← integral_add i1 i2, ← integral_sub h12 i3]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  have key : ∀ x y z : ℝ, |x + y - z| ≤ |x| + |y| + |z| := by
    intro x y z
    rw [abs_le]
    constructor
    · linarith [neg_abs_le x, neg_abs_le y, le_abs_self z]
    · linarith [le_abs_self x, le_abs_self y, neg_abs_le z]
  have t1 := abs_integral_mul_le_sqrt hdU hV
  have t2 := abs_integral_mul_le_sqrt hU hdV
  have t3 := abs_integral_mul_le_sqrt hdU hdV
  rw [e]
  linarith [key (∫ ω, (U ω - U' ω) * V ω ∂μ) (∫ ω, U ω * (V ω - V' ω) ∂μ)
    (∫ ω, (U ω - U' ω) * (V ω - V' ω) ∂μ)]


private lemma summable_acoef_shift (ha : Summable fun k : ℤ => |a k|) (h : ℤ) :
    Summable fun k : ℤ => a k * a (k - h) := by
  refine Summable.of_norm_bounded (g := fun k : ℤ => (∑' j : ℤ, |a j|) * |a k|)
    (ha.mul_left _) fun k => ?_
  have hb : |a (k - h)| ≤ ∑' j : ℤ, |a j| :=
    ha.le_tsum (k - h) (fun j _ => abs_nonneg _)
  calc ‖a k * a (k - h)‖ = |a (k - h)| * |a k| := by
        rw [Real.norm_eq_abs, abs_mul]; ring
  _ ≤ (∑' j : ℤ, |a j|) * |a k| := by
        exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)

private lemma tendsto_partial_shift (ha : Summable fun k : ℤ => |a k|) (h : ℤ) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (if k - h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then a k * a (k - h) else 0))
      atTop (𝓝 (∑' k : ℤ, a k * a (k - h))) := by
  classical
  have hF : ∀ N : ℕ, ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (if k - h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then a k * a (k - h) else 0)
      = ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
          (fun k => k - h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)), a k * a (k - h) :=
    fun N => (Finset.sum_filter _ _).symm
  simp only [hF]
  refine (summable_acoef_shift ha h).hasSum.comp (tendsto_atTop_finset_of_monotone ?_ ?_)
  · intro p q hpq k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at *
    have : (p : ℤ) ≤ (q : ℤ) := by exact_mod_cast hpq
    omega
  · intro k
    refine ⟨max k.natAbs (k - h).natAbs, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have h1 : (k.natAbs : ℤ) ≤ (max k.natAbs (k - h).natAbs : ℕ) := by
      exact_mod_cast Nat.le_max_left _ _
    have h2 : ((k - h).natAbs : ℤ) ≤ (max k.natAbs (k - h).natAbs : ℕ) := by
      exact_mod_cast Nat.le_max_right _ _
    have e1 := Int.natAbs_eq k
    have e2 := Int.natAbs_eq (k - h)
    omega

private lemma tendsto_integral_truncFilter [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (hfil : ∀ t : ℤ, Tendsto (fun N : ℕ => eLpNorm (fun ω => X t ω -
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (hmeas : ∀ t, Measurable (X t)) (h : ℤ) :
    Tendsto (fun N : ℕ => ∫ ω,
        (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (h - k) ω) *
        (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a l * ε (0 - l) ω) ∂μ)
      atTop (𝓝 (∫ ω, X h ω * X 0 ω ∂μ)) := by
  have hXh := memLp_two_of_filter hε hfil hmeas h
  have hX0 := memLp_two_of_filter hε hfil hmeas 0
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  refine squeeze_zero (g := fun N : ℕ =>
      Real.sqrt (∫ ω, (X h ω -
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (h - k) ω) ^ 2 ∂μ) *
        Real.sqrt (∫ ω, X 0 ω ^ 2 ∂μ)
      + Real.sqrt (∫ ω, X h ω ^ 2 ∂μ) *
        Real.sqrt (∫ ω, (X 0 ω -
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (0 - k) ω) ^ 2 ∂μ)
      + Real.sqrt (∫ ω, (X h ω -
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (h - k) ω) ^ 2 ∂μ) *
        Real.sqrt (∫ ω, (X 0 ω -
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (0 - k) ω) ^ 2 ∂μ))
    (fun N => dist_nonneg) (fun N => ?_) ?_
  · rw [Real.dist_eq, abs_sub_comm]
    exact abs_integral_mul_sub_le hXh hX0
      (memLp_truncFilter (a := a) hε (Finset.Icc (-(N : ℤ)) (N : ℤ)) h)
      (memLp_truncFilter (a := a) hε (Finset.Icc (-(N : ℤ)) (N : ℤ)) 0)
  · have d1 := tendsto_sqrt_defect hε hfil hmeas h
    have d0 := tendsto_sqrt_defect hε hfil hmeas 0
    have := ((d1.mul_const (Real.sqrt (∫ ω, X 0 ω ^ 2 ∂μ))).add
      ((d0.const_mul (Real.sqrt (∫ ω, X h ω ^ 2 ∂μ))))).add (d1.mul d0)
    simpa using this

private theorem acvf_eq_tsum_of_filter [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (hfil : ∀ t : ℤ, Tendsto (fun N : ℕ => eLpNorm (fun ω => X t ω -
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (ha : Summable fun k : ℤ => |a k|) (hmeas : ∀ t, Measurable (X t)) (h : ℤ) :
    acvf X μ h = σ2 * ∑' k : ℤ, a k * a (k - h) := by
  have hXh := memLp_two_of_filter hε hfil hmeas h
  have hX0 := memLp_two_of_filter hε hfil hmeas 0
  have hlim1 := tendsto_integral_truncFilter hε hfil hmeas h
  have hlim2 : Tendsto (fun N : ℕ => ∫ ω,
      (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (h - k) ω) *
      (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a l * ε (0 - l) ω) ∂μ)
      atTop (𝓝 (σ2 * ∑' k : ℤ, a k * a (k - h))) := by
    have heq : ∀ N : ℕ, ∫ ω,
        (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (h - k) ω) *
        (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a l * ε (0 - l) ω) ∂μ
        = σ2 * ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            (if k - h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then a k * a (k - h) else 0) :=
      fun N => integral_truncFilter_mul hε _ h
    simp only [heq]
    exact (tendsto_partial_shift ha h).const_mul σ2
  have hval : ∫ ω, X h ω * X 0 ω ∂μ = σ2 * ∑' k : ℤ, a k * a (k - h) :=
    tendsto_nhds_unique hlim1 hlim2
  rw [acvf, covariance_eq_sub hXh hX0, integral_eq_zero_of_filter hε hfil hmeas h,
    integral_eq_zero_of_filter hε hfil hmeas 0]
  simpa using hval

/-- The reindexing `(h, k) ↦ (k, k − h)` of `ℤ × ℤ`. -/
private def shiftPairEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun x := (x.2, x.2 - x.1)
  invFun y := (y.1 - y.2, y.1)
  left_inv x := by simp
  right_inv y := by simp

private lemma summable_absConv (ha : Summable fun k : ℤ => |a k|) :
    Summable fun x : ℤ × ℤ => |a x.2| * |a (x.2 - x.1)| := by
  have hprod : Summable fun x : ℤ × ℤ => |a x.1| * |a x.2| :=
    ha.mul_of_nonneg ha (fun k => abs_nonneg _) (fun k => abs_nonneg _)
  have := (shiftPairEquiv.summable_iff (f := fun x : ℤ × ℤ => |a x.1| * |a x.2|)).2 hprod
  simpa [Function.comp, shiftPairEquiv] using! this

/-- **Young's inequality for the autocovariance series**: the lag-`h` coefficient series of a
two-sided `ℓ¹` filter is itself `ℓ¹` in `h`, hence `ℓ²`. -/
private lemma summable_acvfCoeff_sq (ha : Summable fun k : ℤ => |a k|) :
    Summable fun h : ℤ => (∑' k : ℤ, a k * a (k - h)) ^ 2 := by
  classical
  set S : ℝ := ∑' j : ℤ, |a j| with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun j => abs_nonneg _
  have hF := summable_absConv (a := a) ha
  have hsec : ∀ h : ℤ, Summable fun k : ℤ => |a k| * |a (k - h)| := fun h => hF.prod_factor h
  have hc : Summable fun h : ℤ => ∑' k : ℤ, |a k| * |a (k - h)| := hF.prod
  have hcnn : ∀ h : ℤ, 0 ≤ ∑' k : ℤ, |a k| * |a (k - h)| :=
    fun h => tsum_nonneg fun k => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hcle : ∀ h : ℤ, (∑' k : ℤ, |a k| * |a (k - h)|) ≤ S * S := by
    intro h
    have hb : ∀ k : ℤ, |a k| * |a (k - h)| ≤ |a k| * S := by
      intro k
      exact mul_le_mul_of_nonneg_left (ha.le_tsum (k - h) fun j _ => abs_nonneg _) (abs_nonneg _)
    calc (∑' k : ℤ, |a k| * |a (k - h)|) ≤ ∑' k : ℤ, |a k| * S :=
          (hsec h).tsum_le_tsum hb (ha.mul_right S)
    _ = S * S := by rw [tsum_mul_right]
  have habs : ∀ h : ℤ, |∑' k : ℤ, a k * a (k - h)| ≤ ∑' k : ℤ, |a k| * |a (k - h)| := by
    intro h
    have hnorm : Summable fun k : ℤ => ‖a k * a (k - h)‖ := by
      simpa [Real.norm_eq_abs, abs_mul] using hsec h
    have := norm_tsum_le_tsum_norm hnorm
    simpa [Real.norm_eq_abs, abs_mul] using this
  refine Summable.of_nonneg_of_le (fun h => sq_nonneg _) (fun h => ?_) (hc.mul_left (S * S))
  have h1 := habs h
  have h2 := hcle h
  have h3 := hcnn h
  nlinarith [abs_nonneg (∑' k : ℤ, a k * a (k - h)), sq_abs (∑' k : ℤ, a k * a (k - h))]

/-- **The frozen limiting variance is not a junk `tsum`**: `Σ_h γ(h)² < ∞`. -/
private lemma summable_acvf_sq_of_filter [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (hfil : ∀ t : ℤ, Tendsto (fun N : ℕ => eLpNorm (fun ω => X t ω -
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (ha : Summable fun k : ℤ => |a k|) (hmeas : ∀ t, Measurable (X t)) :
    Summable fun h : ℤ => acvf X μ h ^ 2 := by
  refine Summable.congr ((summable_acvfCoeff_sq (a := a) ha).mul_left (σ2 ^ 2)) fun h => ?_
  rw [acvf_eq_tsum_of_filter hε hfil ha hmeas h]
  ring

end LinearAcvf

/-! ### (R4): the limiting variance the block CLT (R1) must produce

The Cesàro/Fejér brick below is the deterministic half of the lag-`0` debt's variance
identification.  (R2) (`cov_sq_noiseComb`) makes `Cov(X_s², X_t²)` a function of the lag
`h = s − t` alone — the kernel `covKernel a σ² (Eε⁴) h` — so the variance of the
normalized sum `T^{-1/2} Σ_{t<T} X_t²` is `T⁻¹ Σ_{s,t<T} covKernel (s − t)`, and
`tendsto_cesaro_covKernel` evaluates its limit as **exactly** the frozen constant
`(η − 3)γ(0)² + 2 Σ_{j∈ℤ} γ(j)²` of FY Thm 2.8(ii).

Two inputs feed it, both already available in this file: `acvf_eq_tsum_of_filter`
(`γ(h) = σ² Σ_k a_k a_{k−h}`, which turns the coefficient-level kernel into the ACVF-level
constant) and `summable_acvfCoeff_sq` (Young, which makes the `2 Σ_j γ(j)²` block a
genuine number).  The `η`-block needs one more reindexing, `tsum_sqConv`
(`Σ_h Σ_i a_i² a_{i−h}² = (Σ_i a_i²)²`, Tonelli on `ℤ × ℤ` through `shiftPairEquiv`),
which is where `(Σ_i a_i²)² = (γ(0)/σ²)²` comes from.

The triangular-weight identity and the Tannery step are re-proved here at an **abstract
kernel** `K : ℤ → ℝ`; `Mixing/LimitTheorems.lean` runs the same argument, but only at
`K = acvf X μ` and behind `private`. -/

section CesaroKernel

variable {a : ℤ → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}

/-- `{s − n : s < n} = [−n, 0)`. -/
private lemma sum_range_sub_last (f : ℤ → ℝ) (n : ℕ) :
    ∑ s ∈ Finset.range n, f ((s : ℤ) - (n : ℤ)) = ∑ k ∈ Finset.Ico (-(n : ℤ)) 0, f k := by
  have hinj : Function.Injective fun s : ℕ => (s : ℤ) - (n : ℤ) := by
    intro a b h; dsimp only at h; omega
  have hmap : (Finset.range n).map ⟨fun s : ℕ => (s : ℤ) - (n : ℤ), hinj⟩
      = Finset.Ico (-(n : ℤ)) 0 := by
    ext k
    simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · intro hk; exact ⟨(k + n).toNat, by omega, by omega⟩
  rw [← hmap, Finset.sum_map]
  rfl

/-- `{n − t : t ≤ n} = [0, n]`. -/
private lemma sum_range_last_sub (f : ℤ → ℝ) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), f ((n : ℤ) - (t : ℤ)) = ∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), f k := by
  have hinj : Function.Injective fun t : ℕ => (n : ℤ) - (t : ℤ) := by
    intro a b h; dsimp only at h; omega
  have hmap : (Finset.range (n + 1)).map ⟨fun t : ℕ => (n : ℤ) - (t : ℤ), hinj⟩
      = Finset.Icc (0 : ℤ) (n : ℤ) := by
    ext k
    simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · intro hk; exact ⟨((n : ℤ) - k).toNat, by omega, by omega⟩
  rw [← hmap, Finset.sum_map]
  rfl

/-- **Triangular-weight identity**: `∑_{s,t<n} f(s−t) = ∑_{|k|<n} (n − |k|) f(k)`. -/
private lemma sum_sub_double_eq (f : ℤ → ℝ) : ∀ n : ℕ,
    ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, f ((s : ℤ) - (t : ℤ))
      = ∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hIoo : Finset.Ioo (-((n : ℤ) + 1)) ((n : ℤ) + 1) = Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      ext k; simp only [Finset.mem_Ioo, Finset.mem_Icc]; omega
    have hsplit : Finset.Icc (-(n : ℤ)) (n : ℤ)
        = Finset.Ico (-(n : ℤ)) 0 ∪ Finset.Icc (0 : ℤ) (n : ℤ) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.Ico (-(n : ℤ)) 0) (Finset.Icc (0 : ℤ) (n : ℤ)) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_Ico] at hk
      simp only [Finset.mem_Icc] at hk'
      omega
    have hL : ∑ s ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1), f ((s : ℤ) - (t : ℤ))
        = (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, f ((s : ℤ) - (t : ℤ)))
          + ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f k := by
      rw [Finset.sum_range_succ]
      have hrow : ∀ s ∈ Finset.range n, ∑ t ∈ Finset.range (n + 1), f ((s : ℤ) - (t : ℤ))
          = (∑ t ∈ Finset.range n, f ((s : ℤ) - (t : ℤ))) + f ((s : ℤ) - (n : ℤ)) := by
        intro s _
        rw [Finset.sum_range_succ]
      rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, sum_range_sub_last,
        sum_range_last_sub, hsplit, Finset.sum_union hdisj]
      ring
    have hR : ∑ k ∈ Finset.Ioo (-((n : ℤ) + 1)) ((n : ℤ) + 1), (((n : ℝ) + 1) - |(k : ℝ)|) * f k
        = (∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k)
          + ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f k := by
      rw [hIoo]
      have hshrink : ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k
          = ∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k := by
        refine (Finset.sum_subset ?_ ?_).symm
        · intro k hk
          simp only [Finset.mem_Ioo] at hk
          simp only [Finset.mem_Icc]
          omega
        · intro k hk hk'
          simp only [Finset.mem_Icc] at hk
          simp only [Finset.mem_Ioo, not_and_or, not_lt] at hk'
          have : |(k : ℝ)| = (n : ℝ) := by
            rcases hk' with h | h
            · have : k = -(n : ℤ) := by omega
              subst this; push_cast; simp
            · have : k = (n : ℤ) := by omega
              subst this; push_cast; simp
          rw [this]; ring
      rw [← hshrink, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hL, ih]
    push_cast
    push_cast at hR
    rw [hR]

/-- **Cesàro/Fejér limit at an absolutely summable kernel.** -/
private lemma tendsto_cesaro_kernel {K : ℤ → ℝ} (hK : Summable fun k : ℤ => |K k|) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, K ((s : ℤ) - (t : ℤ)))
      atTop (𝓝 (∑' k : ℤ, K k)) := by
  classical
  set g : ℕ → ℤ → ℝ := fun n k =>
    if k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ) then (1 - |(k : ℝ)| / (n : ℝ)) * K k else 0
    with hgdef
  have hns : ∀ n : ℕ, (n : ℝ)⁻¹ *
      ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, K ((s : ℤ) - (t : ℤ)) = ∑' k : ℤ, g n k := by
    intro n
    have hz : ∑' k : ℤ, g n k = ∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), g n k :=
      tsum_eq_sum fun k hk => by simp only [hgdef, if_neg hk]
    rw [sum_sub_double_eq K n, hz]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [hgdef, if_pos hk]
      field_simp
  have hdom : Tendsto (fun n : ℕ => ∑' k : ℤ, g n k) atTop (𝓝 (∑' k : ℤ, K k)) := by
    refine tendsto_tsum_of_dominated_convergence hK (fun k => ?_) (Eventually.of_forall ?_)
    · have hk : ∀ᶠ n : ℕ in atTop, g n k = (1 - |(k : ℝ)| / (n : ℝ)) * K k := by
        filter_upwards [eventually_ge_atTop (k.natAbs + 1)] with n hn
        have hmem : k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ) := by
          simp only [Finset.mem_Ioo]
          have : (k.natAbs : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
          omega
        simp only [hgdef, if_pos hmem]
      refine Tendsto.congr' (hk.mono fun n h => h.symm) ?_
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - |(k : ℝ)| / (n : ℝ)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat |(k : ℝ)|)
      simpa using h1.mul_const (K k)
    · intro n k
      by_cases hk : k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ)
      · simp only [hgdef, if_pos hk, Real.norm_eq_abs, abs_mul]
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        simp only [Finset.mem_Ioo] at hk
        have hklt : |(k : ℝ)| < (n : ℝ) := by
          rw [abs_lt]
          exact ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩
        have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (abs_nonneg _) hklt
        have hd0 : 0 ≤ |(k : ℝ)| / (n : ℝ) := div_nonneg (abs_nonneg _) hnpos.le
        have hd1 : |(k : ℝ)| / (n : ℝ) < 1 := (div_lt_one hnpos).mpr hklt
        rw [abs_le]
        constructor <;> linarith
      · simp only [hgdef, if_neg hk, norm_zero]
        exact abs_nonneg _
  exact (Tendsto.congr (fun n => (hns n).symm) hdom)



/-- `ℓ¹ ⊆ ℓ²` for the coefficient sequence. -/
private lemma summable_sq_of_abs (ha : Summable fun k : ℤ => |a k|) :
    Summable fun k : ℤ => a k ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    (ha.mul_left (∑' j : ℤ, |a j|))
  have hb : |a k| ≤ ∑' j : ℤ, |a j| := ha.le_tsum k fun j _ => abs_nonneg _
  nlinarith [abs_nonneg (a k), sq_abs (a k)]

/-- The squared-coefficient convolution kernel is summable on `ℤ × ℤ`. -/
private lemma summable_sqConv (ha : Summable fun k : ℤ => |a k|) :
    Summable fun x : ℤ × ℤ => a x.2 ^ 2 * a (x.2 - x.1) ^ 2 := by
  have hsq := summable_sq_of_abs ha
  have hprod : Summable fun x : ℤ × ℤ => a x.1 ^ 2 * a x.2 ^ 2 :=
    hsq.mul_of_nonneg hsq (fun k => sq_nonneg _) (fun k => sq_nonneg _)
  have := (shiftPairEquiv.summable_iff (f := fun x : ℤ × ℤ => a x.1 ^ 2 * a x.2 ^ 2)).2 hprod
  simpa [Function.comp, shiftPairEquiv] using! this

/-- **The `η`-block of the limiting variance**: `Σ_h Σ_i a_i² a_{i−h}² = (Σ_i a_i²)²`. -/
private lemma tsum_sqConv (ha : Summable fun k : ℤ => |a k|) :
    (∑' h : ℤ, ∑' i : ℤ, a i ^ 2 * a (i - h) ^ 2) = (∑' i : ℤ, a i ^ 2) ^ 2 := by
  have hsq := summable_sq_of_abs ha
  have hF := summable_sqConv (a := a) ha
  have hprod : Summable fun x : ℤ × ℤ => a x.1 ^ 2 * a x.2 ^ 2 :=
    hsq.mul_of_nonneg hsq (fun k => sq_nonneg _) (fun k => sq_nonneg _)
  have e1 : (∑' x : ℤ × ℤ, a x.2 ^ 2 * a (x.2 - x.1) ^ 2)
      = ∑' x : ℤ × ℤ, a x.1 ^ 2 * a x.2 ^ 2 := by
    have := shiftPairEquiv.tsum_eq (fun x : ℤ × ℤ => a x.1 ^ 2 * a x.2 ^ 2)
    simpa [Function.comp, shiftPairEquiv] using this
  have e2 : (∑' x : ℤ × ℤ, a x.1 ^ 2 * a x.2 ^ 2) = (∑' i : ℤ, a i ^ 2) ^ 2 := by
    rw [hprod.tsum_prod]
    rw [show (∑' i : ℤ, ∑' j : ℤ, a i ^ 2 * a j ^ 2)
        = ∑' i : ℤ, a i ^ 2 * ∑' j : ℤ, a j ^ 2 from tsum_congr fun i => tsum_mul_left]
    rw [tsum_mul_right]; ring
  rw [← e2, ← e1, hF.tsum_prod]


/-- The lag-`h` covariance kernel produced by (R2) at the two-sided linear filter `a`:
`Cov(X_s², X_t²)` with `h = s − t`, in terms of the coefficient sequence alone. -/
private noncomputable def covKernel (a : ℤ → ℝ) (σ2 m4 : ℝ) (h : ℤ) : ℝ :=
  (m4 - 3 * σ2 ^ 2) * (∑' i : ℤ, a i ^ 2 * a (i - h) ^ 2)
    + 2 * σ2 ^ 2 * (∑' i : ℤ, a i * a (i - h)) ^ 2

private lemma summable_abs_covKernel (ha : Summable fun k : ℤ => |a k|) (σ2 m4 : ℝ) :
    Summable fun h : ℤ => |covKernel a σ2 m4 h| := by
  have hA : Summable fun h : ℤ => ∑' i : ℤ, a i ^ 2 * a (i - h) ^ 2 :=
    (summable_sqConv (a := a) ha).prod
  have hB : Summable fun h : ℤ => (∑' k : ℤ, a k * a (k - h)) ^ 2 :=
    summable_acvfCoeff_sq (a := a) ha
  have hAnn : ∀ h : ℤ, 0 ≤ ∑' i : ℤ, a i ^ 2 * a (i - h) ^ 2 :=
    fun h => tsum_nonneg fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  refine Summable.of_nonneg_of_le (fun h => abs_nonneg _) (fun h => ?_)
    ((hA.mul_left |m4 - 3 * σ2 ^ 2|).add (hB.mul_left |2 * σ2 ^ 2|))
  calc |covKernel a σ2 m4 h|
      ≤ |(m4 - 3 * σ2 ^ 2) * (∑' i : ℤ, a i ^ 2 * a (i - h) ^ 2)|
        + |2 * σ2 ^ 2 * (∑' i : ℤ, a i * a (i - h)) ^ 2| := abs_add_le _ _
    _ = |m4 - 3 * σ2 ^ 2| * (∑' i : ℤ, a i ^ 2 * a (i - h) ^ 2)
        + |2 * σ2 ^ 2| * (∑' k : ℤ, a k * a (k - h)) ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hAnn h),
          abs_of_nonneg (sq_nonneg (∑' k : ℤ, a k * a (k - h)))]

/-- **(R4) discharged, in the shape (R1) must produce it.** The `T`-normalized double sum
of the (R2) covariance kernel over the sampling window converges to the frozen limiting
variance of FY Thm 2.8(ii). -/
private theorem tendsto_cesaro_covKernel [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (hσ : 0 < σ2)
    (hfil : ∀ t : ℤ, Tendsto (fun N : ℕ => eLpNorm (fun ω => X t ω -
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (ha : Summable fun k : ℤ => |a k|) (hmeas : ∀ t, Measurable (X t)) :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, ∑ t ∈ Finset.range T,
        covKernel a σ2 (∫ ω, ε 0 ω ^ 4 ∂μ) ((s : ℤ) - (t : ℤ))) atTop
      (𝓝 (((∫ ω, ε 0 ω ^ 4 ∂μ) / σ2 ^ 2 - 3) * acvf X μ 0 ^ 2
        + 2 * ∑' j : ℤ, acvf X μ j ^ 2)) := by
  have hσ0 : σ2 ≠ 0 := hσ.ne'
  have hA : Summable fun h : ℤ => ∑' i : ℤ, a i ^ 2 * a (i - h) ^ 2 :=
    (summable_sqConv (a := a) ha).prod
  have hB : Summable fun h : ℤ => (∑' k : ℤ, a k * a (k - h)) ^ 2 :=
    summable_acvfCoeff_sq (a := a) ha
  -- the coefficient series in terms of the ACVF
  have hcoeff : ∀ h : ℤ, (∑' k : ℤ, a k * a (k - h)) = acvf X μ h / σ2 := by
    intro h
    rw [acvf_eq_tsum_of_filter hε hfil ha hmeas h]
    field_simp
  have hzero : (∑' i : ℤ, a i ^ 2) = acvf X μ 0 / σ2 := by
    rw [← hcoeff 0]
    exact tsum_congr fun i => by rw [sub_zero, sq]
  -- the total mass of the kernel *is* the frozen constant
  have hmass : (∑' h : ℤ, covKernel a σ2 (∫ ω, ε 0 ω ^ 4 ∂μ) h)
      = ((∫ ω, ε 0 ω ^ 4 ∂μ) / σ2 ^ 2 - 3) * acvf X μ 0 ^ 2
        + 2 * ∑' j : ℤ, acvf X μ j ^ 2 := by
    have hsplit : (∑' h : ℤ, covKernel a σ2 (∫ ω, ε 0 ω ^ 4 ∂μ) h)
        = ((∫ ω, ε 0 ω ^ 4 ∂μ) - 3 * σ2 ^ 2) * (∑' h : ℤ, ∑' i : ℤ, a i ^ 2 * a (i - h) ^ 2)
          + 2 * σ2 ^ 2 * ∑' h : ℤ, (∑' k : ℤ, a k * a (k - h)) ^ 2 := by
      rw [← tsum_mul_left, ← tsum_mul_left,
        ← (hA.mul_left _).tsum_add (hB.mul_left _)]
      rfl
    have hacvf : (∑' h : ℤ, (∑' k : ℤ, a k * a (k - h)) ^ 2)
        = (∑' j : ℤ, acvf X μ j ^ 2) / σ2 ^ 2 := by
      rw [eq_div_iff (by positivity), ← tsum_mul_right]
      exact tsum_congr fun h => by rw [hcoeff h]; field_simp
    rw [hsplit, tsum_sqConv (a := a) ha, hzero, hacvf]
    field_simp
  rw [← hmass]
  exact tendsto_cesaro_kernel (summable_abs_covKernel (a := a) ha _ _)


/-! #### The truncated covariance is a function of the lag

`cov_sq_truncFilter` is what makes (R2) and the Cesàro brick above compose: at any window
`A`, `Cov((X_u^{A})², (X_v^{A})²)` depends on `(u, v)` only through `u − v` — the change of
index `i = u − k` in `cov_sq_noiseComb`'s two coefficient sums (`sum_window_reindex`).
At `A = [−N, N]` the resulting lag kernel converges, as `N → ∞`, to `covKernel`
(`tendsto_cov_sq_truncFilter`), through the *same* window-exhaustion lemma
`tendsto_partial_shift` used for the ACVF — applied twice, once at `a` and once at `a²`
(the latter is `ℓ¹` by `summable_sq_of_abs`). -/

/-- Reindexing a window sum: `i ↦ u − i` carries `{i ∈ S : u − i ∈ A}` onto `A`. -/
private lemma sum_window_reindex {A S : Finset ℤ} {u : ℤ} (hS : ∀ k ∈ A, u - k ∈ S)
    (F : ℤ → ℝ) :
    ∑ i ∈ S, (if u - i ∈ A then F (u - i) else 0) = ∑ k ∈ A, F k := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (i := fun i => u - i) (j := fun k => u - k) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simpa using (Finset.mem_filter.1 hi).2
  · intro k hk
    exact Finset.mem_filter.2 ⟨hS k hk, by simpa using hk⟩
  · intro i _; simp
  · intro k _; simp
  · intro i _; rfl


/-- **The truncated fourth-moment covariance depends on the lag alone.** -/
private theorem cov_sq_truncFilter [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (hε4 : MemLp (ε 0) 4 μ) (A : Finset ℤ) (u v : ℤ) :
    cov[fun ω => (∑ k ∈ A, a k * ε (u - k) ω) ^ 2,
        fun ω => (∑ k ∈ A, a k * ε (v - k) ω) ^ 2; μ]
      = ((∫ ω, ε 0 ω ^ 4 ∂μ) - 3 * σ2 ^ 2) *
          (∑ k ∈ A, if k - (u - v) ∈ A then a k ^ 2 * a (k - (u - v)) ^ 2 else 0)
        + 2 * σ2 ^ 2 *
          (∑ k ∈ A, if k - (u - v) ∈ A then a k * a (k - (u - v)) else 0) ^ 2 := by
  classical
  set S : Finset ℤ := (A.image fun k => u - k) ∪ (A.image fun k => v - k) with hSdef
  set c : ℤ → ℝ := fun i => if u - i ∈ A then a (u - i) else 0 with hc
  set d : ℤ → ℝ := fun i => if v - i ∈ A then a (v - i) else 0 with hd
  have hSu : ∀ k ∈ A, u - k ∈ S := fun k hk =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hk)
  have hSv : ∀ k ∈ A, v - k ∈ S := fun k hk =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
  have hidx : ∀ i : ℤ, u - i - (u - v) = v - i := by intro i; omega
  -- the two truncated filters, as linear forms over the common index set `S`
  have hLu : ∀ ω, ∑ i ∈ S, c i * ε i ω = ∑ k ∈ A, a k * ε (u - k) ω := by
    intro ω
    rw [← sum_window_reindex hSu (fun k => a k * ε (u - k) ω)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : u - i ∈ A <;> simp [hc, h]
  have hLv : ∀ ω, ∑ i ∈ S, d i * ε i ω = ∑ k ∈ A, a k * ε (v - k) ω := by
    intro ω
    rw [← sum_window_reindex hSv (fun k => a k * ε (v - k) ω)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : v - i ∈ A <;> simp [hd, h]
  -- the two coefficient sums, reindexed to the lag `u − v`
  have hquad : ∑ i ∈ S, c i ^ 2 * d i ^ 2
      = ∑ k ∈ A, if k - (u - v) ∈ A then a k ^ 2 * a (k - (u - v)) ^ 2 else 0 := by
    rw [← sum_window_reindex hSu
      (fun k => if k - (u - v) ∈ A then a k ^ 2 * a (k - (u - v)) ^ 2 else 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hidx]
    by_cases h1 : u - i ∈ A <;> by_cases h2 : v - i ∈ A <;> simp [hc, hd, h1, h2]
  have hlin : ∑ i ∈ S, c i * d i
      = ∑ k ∈ A, if k - (u - v) ∈ A then a k * a (k - (u - v)) else 0 := by
    rw [← sum_window_reindex hSu
      (fun k => if k - (u - v) ∈ A then a k * a (k - (u - v)) else 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hidx]
    by_cases h1 : u - i ∈ A <;> by_cases h2 : v - i ∈ A <;> simp [hc, hd, h1, h2]
  have hcov := cov_sq_noiseComb hε hε4 c d S
  simp only [hLu, hLv] at hcov
  rw [hcov, hquad, hlin]


/-- **(R2) meets (R4)**: at the window `[−N, N]` the lag kernel converges to `covKernel`. -/
private lemma tendsto_cov_sq_truncFilter [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (hε4 : MemLp (ε 0) 4 μ) (ha : Summable fun k : ℤ => |a k|) (u v : ℤ) :
    Tendsto (fun N : ℕ =>
        cov[fun ω => (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (u - k) ω) ^ 2,
          fun ω => (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (v - k) ω) ^ 2; μ])
      atTop (𝓝 (covKernel a σ2 (∫ ω, ε 0 ω ^ 4 ∂μ) (u - v))) := by
  have hasq : Summable fun k : ℤ => |a k ^ 2| := by
    simpa only [abs_sq] using summable_sq_of_abs ha
  have h1 := tendsto_partial_shift (a := fun k : ℤ => a k ^ 2) hasq (u - v)
  have h2 := tendsto_partial_shift (a := a) ha (u - v)
  have := ((h1.const_mul ((∫ ω, ε 0 ω ^ 4 ∂μ) - 3 * σ2 ^ 2)).add
    ((h2.pow 2).const_mul (2 * σ2 ^ 2)))
  refine this.congr fun N => ?_
  rw [cov_sq_truncFilter hε hε4 (Finset.Icc (-(N : ℤ)) (N : ℤ)) u v]

end CesaroKernel



/-- **Bartlett's asymptotic covariance** (FY eq. (2.26)):
`w_{ij} = Σ_{k=1}^∞ [ρ(k+i) + ρ(k−i) − 2ρ(i)ρ(k)]·[ρ(k+j) + ρ(k−j) − 2ρ(j)ρ(k)]`
(the sum over `k ≥ 1` realized as a `tsum` over `ℕ` shifted by one; junk `0` when not
summable, by the `tsum` convention). -/
noncomputable def bartlettW (X : ℤ → Ω → ℝ) (μ : Measure Ω) (i j : ℕ) : ℝ :=
  ∑' k : ℕ,
    (acf X μ ((k : ℤ) + 1 + (i : ℤ)) + acf X μ ((k : ℤ) + 1 - (i : ℤ))
        - 2 * acf X μ (i : ℤ) * acf X μ ((k : ℤ) + 1)) *
      (acf X μ ((k : ℤ) + 1 + (j : ℤ)) + acf X μ ((k : ℤ) + 1 - (j : ℤ))
        - 2 * acf X μ (j : ℤ) * acf X μ ((k : ℤ) + 1))

end StatLean.TimeSeries
