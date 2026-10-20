module
public import StatLean.TimeSeries.Spectral.LinearFilter
public import StatLean.TimeSeries.Stationarity.ARMAExistence

@[expose] public section

/-!
# ARMA spectral densities (FY §2.3.3, Proposition 2.4, eqs. (2.46)–(2.48))

**FY Proposition 2.4**: a stationary causal ARMA(p, q) process with `b(z) ≠ 0` on the
closed unit disc has spectral density
`g(ω) = σ²/(2π) · |a(e^{−iω})|² / |b(e^{−iω})|²` (eq. (2.46); the rational-in-cosines
expansions (2.47)–(2.48) are this identity with `|trig poly|²` written out and are not
restated separately). The in-text proof applies Theorem 2.12 twice — once to
`b(B)X = a(B)ε` viewed as filtering `X`, once viewing it as filtering `ε` — and uses the
white-noise density `g_ε ≡ σ²/(2π)`.

Also here: **Example 2.5** (AR(1) density, eq. (2.40), in unnormalized `g`-scale) and
**Example 2.7** (AR(1) signal plus uncorrelated observation white noise: the spectrum is
`g_Z + σ_η²/(2π)`, an ARMA(1,1)-shaped rational function — FY's non-identifiability
remark: distinct (signal, noise) pairs can produce the same spectrum).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.3.3,
Proposition 2.4, eqs. (2.46)–(2.48) (pp. 58–59); Example 2.5 (p. 54, eq. (2.40));
Example 2.7 (p. 59). (`FY §2.3.3`.)

**Proof formalization notes.**
* The bridge between polynomial filters and `transferFun` is `polyFilterCoeffs`:
  the transfer function of the one-sided finite filter with coefficients of `P` is
  `P(e^{−iω})` (`transferFun_polyFilterCoeffs`), where `e^{−iω} = fourier (−1) l`.
* Summability of the output ACVF is **derived**, not assumed: causality + no-root ⇒
  exponential ACVF decay (`IsARMA.acvf_exponential_decay`) ⇒ `HasSummableACVF`
  (`IsARMA.hasSummableACVF`), per the hypothesis-discipline rule.

**Bibliographic comments.** The rational ARMA spectrum computation is classical
(Wold 1938; Doob 1953 ch. X); FY Prop 2.4 follows Brockwell & Davis (1991), Thm 4.4.2.
The signal-plus-noise non-identifiability of Example 2.7 traces to the errors-in-
variables literature (Grether & Maddala 1973).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real ENNReal

namespace StatLean.TimeSeries

private instance : Fact (0 < 2 * π) := ⟨by positivity⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The two-sided coefficient sequence of the **one-sided polynomial filter** `P(B)`:
`k ↦ coeff_k P` for `k ≥ 0` and `0` for `k < 0` (FY §2.3.3's `b(B)X`, `a(B)ε`). Finite
support, hence always `ℓ¹`. -/
noncomputable def polyFilterCoeffs (P : Polynomial ℝ) : ℤ → ℝ := fun k =>
  if 0 ≤ k then P.coeff k.toNat else 0

/-- The polynomial-filter coefficients vanish off `[0, deg P]`. -/
private theorem polyFilterCoeffs_eq_zero (P : Polynomial ℝ) {k : ℤ}
    (hk : k < 0 ∨ (P.natDegree : ℤ) < k) : polyFilterCoeffs P k = 0 := by
  rw [polyFilterCoeffs]
  by_cases h : 0 ≤ k
  · exact if_pos h ▸ Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · exact if_neg h

/-- The index set `{0, 1, …, deg P} ⊆ ℤ` carrying the polynomial filter, as the image of
`Finset.range (deg P + 1)` under `Nat.cast`. -/
private def polyFilterSupport (P : Polynomial ℝ) : Finset ℤ :=
  (Finset.range (P.natDegree + 1)).map ⟨Nat.cast, Nat.cast_injective⟩

private theorem polyFilterCoeffs_eq_zero_of_notMem (P : Polynomial ℝ) {k : ℤ}
    (hk : k ∉ polyFilterSupport P) : polyFilterCoeffs P k = 0 := by
  simp only [polyFilterSupport, Finset.mem_map, Finset.mem_range,
    Function.Embedding.coeFn_mk, not_exists, not_and] at hk
  refine polyFilterCoeffs_eq_zero P ?_
  rcases lt_or_ge k 0 with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    by_contra hle
    exact absurd (by omega : ((k.toNat : ℕ) : ℤ) = k) (hk k.toNat (by omega))

/-- A polynomial filter has finitely many nonzero coefficients, hence is `ℓ¹`. -/
theorem summable_abs_polyFilterCoeffs (P : Polynomial ℝ) :
    Summable fun k : ℤ => |polyFilterCoeffs P k| := by
  apply summable_of_ne_finset_zero (s := Finset.Icc (0 : ℤ) (P.natDegree : ℤ))
  intro k hk
  simp only [Finset.mem_Icc, not_and, not_le] at hk
  rw [polyFilterCoeffs_eq_zero P (by omega), abs_zero]

/-- `e^{−inω} = (e^{−iω})ⁿ` for `n ≥ 0`. -/
private theorem fourier_neg_natCast (n : ℕ) (l : AddCircle (2 * π)) :
    (fourier (-(n : ℤ)) l : ℂ) = (fourier (-1) l : ℂ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : (-((n + 1 : ℕ) : ℤ)) = (-(n : ℤ)) + (-1) := by push_cast; ring
      rw [h, fourier_add, ih, pow_succ]

/-- The transfer function of a polynomial filter is the polynomial evaluated at
`e^{−iω}`: `Γ(ω) = Σ_{k≥0} coeff_k P · e^{−ikω} = P(e^{−iω})` (FY §2.3.3, the
computation behind eq. (2.46)). -/
theorem transferFun_polyFilterCoeffs (P : Polynomial ℝ) (l : AddCircle (2 * π)) :
    transferFun (polyFilterCoeffs P) l = Polynomial.aeval ((fourier (-1) l : ℂ)) P := by
  rw [transferFun, tsum_eq_sum (s := polyFilterSupport P)
    fun k hk => by rw [polyFilterCoeffs_eq_zero_of_notMem P hk]; simp]
  rw [polyFilterSupport, Finset.sum_map, Polynomial.aeval_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [polyFilterCoeffs, if_pos (Int.natCast_nonneg i), Int.toNat_natCast,
    fourier_neg_natCast, Complex.real_smul]

/-- An exact a.e. finite-sum representation realizes the polynomial filter in the `L²`
sense of `IsFilteredBy` (the partial sums are eventually exact). -/
theorem isFilteredBy_of_ae_eq_polySum {X Y : ℤ → Ω → ℝ} {P : Polynomial ℝ}
    (h : ∀ t : ℤ, X t =ᵐ[μ] fun ω =>
      ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * Y (t - (k : ℕ)) ω) :
    IsFilteredBy X Y (polyFilterCoeffs P) μ := by
  intro t
  have key : ∀ N : ℕ, P.natDegree ≤ N →
      (0 : ℝ≥0∞) = eLpNorm (fun ω => X t ω -
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), polyFilterCoeffs P k * Y (t - k) ω) 2 μ := by
    intro N hN
    have hsub : polyFilterSupport P ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      intro x hx
      simp only [polyFilterSupport, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk] at hx
      obtain ⟨n, hn, rfl⟩ := hx
      simp only [Finset.mem_Icc]
      omega
    have hae : (fun ω => X t ω -
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), polyFilterCoeffs P k * Y (t - k) ω) =ᵐ[μ] 0 := by
      filter_upwards [h t] with ω hω
      simp only [Pi.zero_apply, sub_eq_zero, hω]
      rw [← Finset.sum_subset hsub
        fun x _ hxn => by rw [polyFilterCoeffs_eq_zero_of_notMem P hxn, zero_mul],
        polyFilterSupport, Finset.sum_map]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Function.Embedding.coeFn_mk]
      rw [polyFilterCoeffs, if_pos (Int.natCast_nonneg i), Int.toNat_natCast]
    rw [eLpNorm_congr_ae hae, eLpNorm_zero]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop P.natDegree] with N hN using key N hN

/-- White noise has (trivially) absolutely summable ACVF. -/
theorem IsWhiteNoise.hasSummableACVF [IsProbabilityMeasure μ] {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hε : IsWhiteNoise ε σ2 μ) :
    HasSummableACVF ε μ := by
  apply summable_of_ne_finset_zero (s := {0})
  intro k hk
  rw [hε.acvf_eq k, if_neg (by simpa using hk), abs_zero]

/-- **White-noise spectral density** (FY §2.3.2, p. 53): `g_ε(ω) ≡ σ²/(2π)` — the flat
spectrum ("white light"). -/
theorem IsWhiteNoise.spectralDensityOf_eq [IsProbabilityMeasure μ] {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hε : IsWhiteNoise ε σ2 μ) (l : AddCircle (2 * π)) :
    spectralDensityOf ε μ l = σ2 / (2 * π) := by
  rw [spectralDensityOf, tsum_eq_single 0 (fun k hk => by rw [hε.acvf_eq k, if_neg hk, zero_mul]),
    hε.acvf_eq 0, if_pos rfl, fourier_zero, Complex.one_re, mul_one]
  ring

/-! ### Coefficient bookkeeping for the lag polynomials

These mirror the (file-private) computations of `Models/Linear.lean`: `arPoly` and
`maPoly` have constant coefficient `1`, coefficient `∓bᵢ`/`aⱼ` in degree `i+1`/`j+1`, and
degree at most `p`/`q`. -/

/-- The coefficients of the AR polynomial `b(z) = 1 - b₁z - ⋯ - b_pz^p`. -/
private theorem coeff_arPoly {p : ℕ} (b : Fin p → ℝ) (m : ℕ) :
    (arPoly b).coeff m
      = (if m = 0 then (1 : ℝ) else 0) - ∑ i : Fin p, if m = (i : ℕ) + 1 then b i else 0 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

private theorem coeff_arPoly_zero {p : ℕ} (b : Fin p → ℝ) : (arPoly b).coeff 0 = 1 := by
  rw [coeff_arPoly]; simp

private theorem coeff_arPoly_succ {p : ℕ} (b : Fin p → ℝ) (j : Fin p) :
    (arPoly b).coeff ((j : ℕ) + 1) = -(b j) := by
  rw [coeff_arPoly]
  simp [Fin.val_eq_val, Finset.sum_ite_eq]

private theorem natDegree_arPoly_le {p : ℕ} (b : Fin p → ℝ) : (arPoly b).natDegree ≤ p := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [coeff_arPoly, if_neg (by omega), zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun i _ => if_neg ?_
  have := i.isLt
  omega

/-- The coefficients of the MA polynomial `a(z) = 1 + a₁z + ⋯ + a_qz^q`. -/
private theorem coeff_maPoly {q : ℕ} (a : Fin q → ℝ) (m : ℕ) :
    (maPoly a).coeff m
      = (if m = 0 then (1 : ℝ) else 0) + ∑ j : Fin q, if m = (j : ℕ) + 1 then a j else 0 := by
  simp [maPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

private theorem coeff_maPoly_zero {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  rw [coeff_maPoly]; simp

private theorem coeff_maPoly_succ {q : ℕ} (a : Fin q → ℝ) (j : Fin q) :
    (maPoly a).coeff ((j : ℕ) + 1) = a j := by
  rw [coeff_maPoly]
  simp [Fin.val_eq_val, Finset.sum_ite_eq]

private theorem natDegree_maPoly_le {q : ℕ} (a : Fin q → ℝ) : (maPoly a).natDegree ≤ q := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [coeff_maPoly, if_neg (by omega), zero_add]
  refine Finset.sum_eq_zero fun j _ => if_neg ?_
  have := j.isLt
  omega

omit [MeasurableSpace Ω] in
/-- Coefficients past the degree contribute nothing, so the defining `natDegree`-truncated
sum can be run to any larger order. -/
private theorem sum_range_coeff_extend {P : Polynomial ℝ} {n : ℕ} (hn : P.natDegree ≤ n)
    (W : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * W (t - (k : ℕ)) ω
      = ∑ k ∈ Finset.range (n + 1), P.coeff k * W (t - (k : ℕ)) ω := by
  have hsub : Finset.range (P.natDegree + 1) ⊆ Finset.range (n + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  refine Finset.sum_subset hsub fun x _ hx => ?_
  rw [Finset.mem_range, not_lt] at hx
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

omit [MeasurableSpace Ω] in
/-- The `P(B)W` sum with its degree-`0` term split off (FY's `b(B)X`, `a(B)ε` shape). -/
private theorem sum_range_split (P : Polynomial ℝ) (n : ℕ) (W : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    ∑ k ∈ Finset.range (n + 1), P.coeff k * W (t - (k : ℕ)) ω
      = P.coeff 0 * W t ω + ∑ i : Fin n, P.coeff ((i : ℕ) + 1) * W (t - 1 - (i : ℕ)) ω := by
  rw [← Fin.sum_univ_eq_sum_range (fun m => P.coeff m * W (t - (m : ℤ)) ω) (n + 1),
    Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.cast_zero, sub_zero, Fin.val_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : t - (((i : ℕ) + 1 : ℕ) : ℤ) = t - 1 - ((i : ℕ) : ℤ) := by push_cast; ring
  rw [h]

/-- **FY Proposition 2.4 (eq. (2.46))**: the spectral density of a stationary causal
ARMA(p, q) process with `b(z) ≠ 0` on the closed unit disc is
`g(ω) = σ²/(2π) · |a(e^{−iω})|²/|b(e^{−iω})|²`.

Summability of the ACVF is derived internally (causality + no-root ⇒ exponential decay),
not assumed. -/
theorem IsARMA.spectralDensityOf_eq [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ)
    -- USER-INPUT: the ARMA process is stationary; FY Prop 2.4
    (hstat : IsStationary X μ)
    -- USER-INPUT: causal MA(∞) representation with the ARMA ψ-weights; FY §2.1.3
    -- standing causality convention (the iff with `NoRootClosedDisc` is the named debt
    -- `arma_causal_of_stationary_debt`)
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    -- USER-INPUT: b(z) ≠ 0 for |z| ≤ 1; FY Prop 2.4
    (hroot : NoRootClosedDisc b)
    (hmeas : ∀ t, Measurable (X t))
    (l : AddCircle (2 * π)) :
    spectralDensityOf X μ l =
      σ2 / (2 * π) * ‖Polynomial.aeval ((fourier (-1) l : ℂ)) (maPoly a)‖ ^ 2
        / ‖Polynomial.aeval ((fourier (-1) l : ℂ)) (arPoly b)‖ ^ 2 := by
  have hεstat : IsStationary ε μ := h.whiteNoise.isStationary
  have hεsum : HasSummableACVF ε μ := h.whiteNoise.hasSummableACVF
  have hεmeas : ∀ t, Measurable (ε t) := h.whiteNoise.measurable
  have hsum : HasSummableACVF X μ := h.hasSummableACVF (h.acvf_exponential_decay hcausal hroot)
  -- the intermediate MA process `W_t = a(B) ε_t`, which is also `b(B) X_t`
  obtain ⟨W, hWdef⟩ : ∃ W : ℤ → Ω → ℝ,
      W = fun t ω => ε t ω + ∑ j : Fin q, a j * ε (t - 1 - (j : ℕ)) ω := ⟨_, rfl⟩
  have hWmeas : ∀ t, Measurable (W t) := by
    intro t
    simp only [hWdef]
    exact (hεmeas t).add (Finset.measurable_sum _ fun j _ => measurable_const.mul (hεmeas _))
  have hWa : IsFilteredBy W ε (polyFilterCoeffs (maPoly a)) μ := by
    refine isFilteredBy_of_ae_eq_polySum fun t => Filter.Eventually.of_forall fun ω => ?_
    change W t ω
      = ∑ k ∈ Finset.range ((maPoly a).natDegree + 1), (maPoly a).coeff k * ε (t - (k : ℕ)) ω
    have hs : ∑ j : Fin q, (maPoly a).coeff ((j : ℕ) + 1) * ε (t - 1 - (j : ℕ)) ω
        = ∑ j : Fin q, a j * ε (t - 1 - (j : ℕ)) ω :=
      Finset.sum_congr rfl fun j _ => by rw [coeff_maPoly_succ]
    rw [sum_range_coeff_extend (natDegree_maPoly_le a) ε t ω, sum_range_split,
      coeff_maPoly_zero, one_mul, hs]
    simp only [hWdef]
  have hWb : IsFilteredBy W X (polyFilterCoeffs (arPoly b)) μ := by
    refine isFilteredBy_of_ae_eq_polySum fun t => ?_
    filter_upwards [h.recurrence t] with ω hω
    have hs : ∑ i : Fin p, (arPoly b).coeff ((i : ℕ) + 1) * X (t - 1 - (i : ℕ)) ω
        = ∑ i : Fin p, -(b i * X (t - 1 - (i : ℕ)) ω) :=
      Finset.sum_congr rfl fun i _ => by rw [coeff_arPoly_succ]; ring
    rw [sum_range_coeff_extend (natDegree_arPoly_le b) X t ω, sum_range_split,
      coeff_arPoly_zero, one_mul, hs, Finset.sum_neg_distrib]
    simp only [hWdef]
    linarith [hω]
  -- FY Theorem 2.12 applied twice to the same `W`
  have e1 := hWa.spectralDensityOf_eq (summable_abs_polyFilterCoeffs _) hεstat hεsum hεmeas
    hWmeas l
  have e2 := hWb.spectralDensityOf_eq (summable_abs_polyFilterCoeffs _) hstat hsum hmeas hWmeas l
  rw [transferFun_polyFilterCoeffs, h.whiteNoise.spectralDensityOf_eq l] at e1
  rw [transferFun_polyFilterCoeffs] at e2
  have hz1 : ‖(fourier (-1) l : ℂ)‖ = 1 := Circle.norm_coe _
  have hA : ‖Polynomial.aeval ((fourier (-1) l : ℂ)) (arPoly b)‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (hroot _ hz1.le))
  rw [eq_div_iff hA]
  linear_combination e1 - e2

/-- For an AR(1) polynomial `b(z) = 1 − b₁z`, the condition `|b₁| < 1` is the no-root
condition on the closed unit disc. -/
private theorem noRootClosedDisc_of_abs_lt_one {b1 : ℝ} (hb : |b1| < 1) :
    NoRootClosedDisc (fun _ : Fin 1 => b1) := by
  intro z hz hcon
  have har : Polynomial.aeval z (arPoly (fun _ : Fin 1 => b1)) = 1 - (b1 : ℂ) * z := by
    simp [arPoly]
  rw [har, sub_eq_zero] at hcon
  have hnorm : (1 : ℝ) = |b1| * ‖z‖ := by
    have h2 := congrArg (fun w : ℂ => ‖w‖) hcon
    simpa using h2
  nlinarith [norm_nonneg z, abs_nonneg b1]

/-- **FY Example 2.5 (eq. (2.40))**, in unnormalized `g`-scale: a stationary causal
AR(1) process with `|b| < 1` has
`g(ω) = σ²/(2π) / (1 + b² − 2b cos ω)`. (FY prints the normalized `f = g/γ(0)`; the
`γ(0) = σ²/(1−b²)` factor converts.) -/
theorem spectralDensityOf_ar_one [IsProbabilityMeasure μ] {b1 σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ}
    (h : IsAR (fun _ : Fin 1 => b1) σ2 X ε μ)
    -- USER-INPUT: stationarity; FY Example 2.5
    (hstat : IsStationary X μ)
    -- USER-INPUT: causal representation; FY §2.1.3 convention
    (hcausal :
      IsLinearProcessOf (armaPsi (fun _ : Fin 1 => b1) (Fin.elim0 : Fin 0 → ℝ)) X ε μ)
    -- USER-INPUT: |b| < 1 (equivalent to the AR polynomial's no-root condition,
    -- derived internally); FY Example 2.5
    (hb : |b1| < 1)
    (hmeas : ∀ t, Measurable (X t))
    (l : AddCircle (2 * π)) :
    spectralDensityOf X μ l
      = σ2 / (2 * π) / (1 + b1 ^ 2 - 2 * b1 * (fourier 1 l).re) := by
  have hma : ∀ z : ℂ, Polynomial.aeval z (maPoly (Fin.elim0 : Fin 0 → ℝ)) = 1 := by
    intro z; simp [maPoly]
  have har : ∀ z : ℂ, Polynomial.aeval z (arPoly (fun _ : Fin 1 => b1)) = 1 - (b1 : ℂ) * z := by
    intro z; simp [arPoly]
  have hz1 : ‖(fourier (-1) l : ℂ)‖ = 1 := Circle.norm_coe _
  have hre : ((fourier (-1) l : ℂ)).re = ((fourier 1 l : ℂ)).re := by
    rw [fourier_neg]; simp
  have hns : ((fourier (-1) l : ℂ)).re * ((fourier (-1) l : ℂ)).re
      + ((fourier (-1) l : ℂ)).im * ((fourier (-1) l : ℂ)).im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hz1, one_pow]
  have hden : ‖(1 : ℂ) - (b1 : ℂ) * (fourier (-1) l : ℂ)‖ ^ 2
      = 1 + b1 ^ 2 - 2 * b1 * ((fourier 1 l : ℂ)).re := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← hre]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination b1 ^ 2 * hns
  rw [h.spectralDensityOf_eq hstat hcausal (noRootClosedDisc_of_abs_lt_one hb) hmeas l,
    hma, har, hden, norm_one, one_pow, mul_one]

/-- Sum of two uncorrelated weakly stationary processes: stationary again, with
additive ACVF (the covariance computation behind FY Example 2.7). -/
theorem isStationary_add_of_uncorrelated [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    (hX : IsStationary X μ) (hY : IsStationary Y μ)
    -- USER-INPUT: cross-uncorrelation at all lags; FY Example 2.7 ("independent of")
    (huncorr : ∀ s t : ℤ, cov[X s, Y t; μ] = 0) :
    IsStationary (fun t ω => X t ω + Y t ω) μ ∧
      ∀ k : ℤ, acvf (fun t ω => X t ω + Y t ω) μ k = acvf X μ k + acvf Y μ k := by
  have hcov : ∀ s t : ℤ, cov[fun ω => X s ω + Y s ω, fun ω => X t ω + Y t ω; μ]
      = cov[X s, X t; μ] + cov[Y s, Y t; μ] := by
    intro s t
    have h0 : cov[fun ω => X s ω + Y s ω, fun ω => X t ω + Y t ω; μ]
        = cov[X s + Y s, X t + Y t; μ] := rfl
    rw [h0, covariance_add_left (hX.memLp s) (hY.memLp s) ((hX.memLp t).add (hY.memLp t)),
      covariance_add_right (hX.memLp s) (hX.memLp t) (hY.memLp t),
      covariance_add_right (hY.memLp s) (hX.memLp t) (hY.memLp t),
      huncorr s t, covariance_comm (X := Y s) (Y := X t), huncorr t s]
    ring
  refine ⟨⟨fun t => (hX.memLp t).add (hY.memLp t), fun s t => ?_, fun t k => ?_⟩, fun k => ?_⟩
  · rw [integral_add ((hX.memLp s).integrable one_le_two) ((hY.memLp s).integrable one_le_two),
      integral_add ((hX.memLp t).integrable one_le_two) ((hY.memLp t).integrable one_le_two),
      hX.integral_eq s t, hY.integral_eq s t]
  · rw [hcov, hcov, hX.cov_shift t k, hY.cov_shift t k]
  · exact hcov k 0

/-- The spectral-density series converges absolutely under summable ACVF (`|Re e^{ikλ}| ≤ 1`). -/
private theorem summable_acvf_mul_fourier [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hZ : HasSummableACVF Z μ) (l : AddCircle (2 * π)) :
    Summable fun k : ℤ => acvf Z μ k * (fourier k l).re := by
  refine Summable.of_norm_bounded hZ fun k => ?_
  have h1 : |((fourier k l : ℂ)).re| ≤ 1 := by
    have h3 : ‖(fourier k l : ℂ)‖ = 1 := Circle.norm_coe _
    have h2 := Complex.abs_re_le_norm (fourier k l : ℂ)
    rwa [h3] at h2
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  nlinarith [abs_nonneg (acvf Z μ k)]

/-- Additive ACVFs give additive spectral densities. -/
private theorem spectralDensityOf_add [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    (hX : HasSummableACVF X μ) (hY : HasSummableACVF Y μ)
    (hadd : ∀ k : ℤ, acvf (fun t ω => X t ω + Y t ω) μ k = acvf X μ k + acvf Y μ k)
    (l : AddCircle (2 * π)) :
    spectralDensityOf (fun t ω => X t ω + Y t ω) μ l
      = spectralDensityOf X μ l + spectralDensityOf Y μ l := by
  rw [spectralDensityOf, spectralDensityOf, spectralDensityOf, ← mul_add,
    ← Summable.tsum_add (summable_acvf_mul_fourier hX l) (summable_acvf_mul_fourier hY l)]
  congr 1
  exact tsum_congr fun k => by rw [hadd k, add_mul]

/-- **FY Example 2.7**: AR(1) signal plus uncorrelated white observation noise has
spectral density `g_Z(ω) + σ_η²/(2π)` — an ARMA(1,1)-shaped rational spectrum. FY's
point: the sum is *not* AR(1), and distinct (signal, noise) parameter pairs can give
the same spectrum (non-identifiability). -/
theorem spectralDensityOf_ar_one_add_noise [IsProbabilityMeasure μ]
    {b1 σ2 ση2 : ℝ} {Z ε η : ℤ → Ω → ℝ}
    (hZ : IsAR (fun _ : Fin 1 => b1) σ2 Z ε μ)
    -- USER-INPUT: stationarity of the signal; FY Example 2.7
    (hstatZ : IsStationary Z μ)
    -- USER-INPUT: causal representation of the signal; FY §2.1.3 convention
    (hcausal :
      IsLinearProcessOf (armaPsi (fun _ : Fin 1 => b1) (Fin.elim0 : Fin 0 → ℝ)) Z ε μ)
    -- USER-INPUT: |b| < 1; FY Example 2.7
    (hb : |b1| < 1)
    (hmeas : ∀ t, Measurable (Z t))
    -- USER-INPUT: white observation noise; FY Example 2.7
    (hη : IsWhiteNoise η ση2 μ)
    -- USER-INPUT: noise uncorrelated with the signal at all lags; FY Example 2.7
    (huncorr : ∀ s t : ℤ, cov[Z s, η t; μ] = 0)
    (l : AddCircle (2 * π)) :
    spectralDensityOf (fun t ω => Z t ω + η t ω) μ l
      = σ2 / (2 * π) / (1 + b1 ^ 2 - 2 * b1 * (fourier 1 l).re) + ση2 / (2 * π) := by
  have hZsum : HasSummableACVF Z μ :=
    hZ.hasSummableACVF (hZ.acvf_exponential_decay hcausal (noRootClosedDisc_of_abs_lt_one hb))
  obtain ⟨-, hacvfAdd⟩ := isStationary_add_of_uncorrelated hstatZ hη.isStationary huncorr
  rw [spectralDensityOf_add hZsum hη.hasSummableACVF hacvfAdd l,
    spectralDensityOf_ar_one hZ hstatZ hcausal hb hmeas l, hη.spectralDensityOf_eq l]

end StatLean.TimeSeries
