module
public import StatLean.TimeSeries.Models.WhiteNoise

@[expose] public section

/-!
# Linear models — the chapter-1 structural claims (FY §1.3.3–§1.3.5)

The provable claims of FY ch. 1 about the linear model classes:

* **MA(q) is q-dependent in covariance** (FY §1.3.3, "obviously"): observations more
  than `q` apart share no innovations, hence are uncorrelated;
* **MA(1) inversion** (FY §1.3.3, "it can be proved"): for `|a| < 1`, the partial sums
  `Σ_{j≤N} (−a)^j X_{t−j}` recover `ε_t` in probability (the concrete instance
  `a = −0.9` is the book's display);
* **ARIMA is a (typically nonstationary) ARMA(p+d, q)** (FY §1.3.5, "easy to see";
  the book misprints the MA order as `p`): the differenced recurrence composes to the
  AR polynomial `b(z)(1−z)^d` of degree `p + d`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §1.3.3
(p. 12), §1.3.5 (pp. 13–14). (`FY §1.3.3; §1.3.5`.)

**Proof formalization notes.**
* `IsMA.cov_eq_zero` computes `cov` of the two a.e. finite innovation sums bilinearly
  against `IsWhiteNoise.uncorrelated`; the index gap `|s − t| > q` empties the diagonal.
* In `IsARIMA.satisfiesARMA` the composed AR coefficients are read off the polynomial
  `arPoly b * (1 − X)^d`; sign convention: our `SatisfiesARMA` coefficients are the
  *negatives* of that polynomial's nonconstant coefficients (the constant term is `1`).
* The MA(1) inversion is stated as convergence in probability (`TendstoInMeasure`),
  matching the book's claim; the geometric remainder bound `‖(−a)^N ε_{t−N}‖ → 0` runs
  through Chebyshev on an `L²` bound.

**Bibliographic comments.** Invertibility of moving averages and the AR(∞)
representation are due to H. Wold (1938) and were systematized by G. E. P. Box and
G. M. Jenkins (1970), where ARIMA modeling (differencing to stationarity) originates.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Covariance only sees the a.e. class of each argument. -/
private lemma covariance_congr_ae {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIX : ∫ x, X x ∂μ = ∫ x, X' x ∂μ := integral_congr_ae hX
  have hIY : ∫ x, Y x ∂μ = ∫ x, Y' x ∂μ := integral_congr_ae hY
  simp only [covariance, hIX, hIY]
  exact integral_congr_ae (by filter_upwards [hX, hY] with ω h1 h2 using by rw [h1, h2])

/-- Two finite linear combinations of white-noise coordinates taken over *disjoint* index
sets are uncorrelated. -/
private lemma cov_noise_combination_eq_zero [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hw : IsWhiteNoise ε σ2 μ) {n m : ℕ} (c : Fin n → ℝ) (d : Fin m → ℝ)
    (u : Fin n → ℤ) (v : Fin m → ℤ) (huv : ∀ i j, u i ≠ v j) :
    cov[fun ω => ∑ i, c i * ε (u i) ω, fun ω => ∑ j, d j * ε (v j) ω; μ] = 0 := by
  rw [covariance_fun_sum_fun_sum (X := fun i ω => c i * ε (u i) ω)
      (Y := fun j ω => d j * ε (v j) ω)
      (fun i => (hw.memLp (u i)).const_mul (c i))
      (fun j => (hw.memLp (v j)).const_mul (d j))]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right, hw.uncorrelated _ _ (huv i j)]
  ring

/-- The one-sided half of `IsMA.cov_eq_zero`: the MA(q) covariance vanishes once the
later time exceeds the earlier one by more than the order. -/
private lemma IsMA.cov_eq_zero_of_lt [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ}
    {σ2 : ℝ} {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) {s t : ℤ} (hgap : t + q < s) :
    cov[X s, X t; μ] = 0 := by
  -- the MA coefficient vector `(1, a₁, …, a_q)` and the lag map `u ↦ (u, u-1, …, u-q)`
  obtain ⟨c, hc0, hcs⟩ : ∃ c : Fin (q + 1) → ℝ, c 0 = 1 ∧ ∀ i : Fin q, c i.succ = a i :=
    ⟨Fin.cases 1 a, rfl, fun _ => rfl⟩
  obtain ⟨L, hL0, hLs⟩ : ∃ L : ℤ → Fin (q + 1) → ℤ,
      (∀ u, L u 0 = u) ∧ ∀ (u : ℤ) (i : Fin q), L u i.succ = u - 1 - (i : ℕ) :=
    ⟨fun u => Fin.cases u fun i => u - 1 - (i : ℕ), fun _ => rfl, fun _ _ => rfl⟩
  -- the MA(q) recurrence, packaged as a single sum
  have hrec : ∀ u : ℤ, X u =ᵐ[μ] fun ω => ∑ i, c i * ε (L u i) ω := by
    intro u
    filter_upwards [h.recurrence u] with ω hω
    rw [hω, Fin.sum_univ_succ, hc0, hL0]
    simp only [hcs, hLs]
    simp
  -- the two lag windows `[s-q, s]` and `[t-q, t]` are disjoint
  have hge : ∀ i : Fin (q + 1), s - q ≤ L s i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [hL0]; omega
    · rw [hLs]; have := k.isLt; omega
  have hle : ∀ j : Fin (q + 1), L t j ≤ t := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [hL0]
    · rw [hLs]; have := k.isLt; omega
  rw [covariance_congr_ae (hrec s) (hrec t)]
  refine cov_noise_combination_eq_zero h.whiteNoise c c (L s) (L t) fun i j => ?_
  have h1 := hge i
  have h2 := hle j
  omega

/-- **MA(q) is q-dependent** (FY §1.3.3): observations more than `q` apart are
uncorrelated. -/
theorem IsMA.cov_eq_zero [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) {s t : ℤ}
    -- USER-INPUT: the lag exceeds the MA order; FY §1.3.3
    (hgap : (q : ℤ) < |s - t|) :
    cov[X s, X t; μ] = 0 := by
  rcases lt_abs.mp hgap with hc | hc
  · exact h.cov_eq_zero_of_lt (by omega)
  · rw [covariance_comm]; exact h.cov_eq_zero_of_lt (by omega)

/-- **MA(1) inversion** (FY §1.3.3): for an MA(1) with `|a₁| < 1`, the alternating
geometric partial sums of lagged observations recover the innovation in probability:
`Σ_{j=0}^{N} (−a₁)^j X_{t−j} → ε_t`. (The book's display is the instance `a₁ = −0.9`:
`X_t + Σ_{j≥1} 0.9^j X_{t−j} = ε_t`.) -/
theorem IsMA.tendstoInMeasure_inversion [IsProbabilityMeasure μ] {a1 : ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ}
    (h : IsMA (fun _ : Fin 1 => a1) σ2 X ε μ)
    -- USER-INPUT: invertibility |a₁| < 1; FY §1.3.3
    (ha : |a1| < 1) (t : ℤ) :
    TendstoInMeasure μ
      (fun N ω => ∑ j ∈ Finset.range (N + 1), (-a1) ^ j * X (t - (j : ℕ)) ω)
      atTop (ε t) := by
  have hw := h.whiteNoise
  -- the MA(1) recurrence in cleaned-up form
  have hrec : ∀ u : ℤ, X u =ᵐ[μ] fun ω => ε u ω + a1 * ε (u - 1) ω := by
    intro u
    filter_upwards [h.recurrence u] with ω hω
    simpa using hω
  -- the telescoping identity: the partial sums are the innovation plus a geometric tail
  have key : ∀ N : ℕ, (fun ω => ∑ j ∈ Finset.range (N + 1), (-a1) ^ j * X (t - (j : ℕ)) ω)
      =ᵐ[μ] fun ω => ε t ω - (-a1) ^ (N + 1) * ε (t - (N : ℤ) - 1) ω := by
    intro N
    induction N with
    | zero =>
      filter_upwards [hrec t] with ω hω
      simp only [Finset.sum_range_one, Nat.cast_zero, sub_zero, pow_zero, one_mul,
        zero_add, pow_one, hω]
      ring
    | succ N ih =>
      have e1 : t - ((N + 1 : ℕ) : ℤ) = t - (N : ℤ) - 1 := by push_cast; ring
      have e2 : t - (N : ℤ) - 1 - 1 = t - ((N + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
      filter_upwards [ih, hrec (t - (N : ℤ) - 1)] with ω h1 h2
      rw [Finset.sum_range_succ, h1, e1, h2, e2]
      ring
  refine TendstoInMeasure.congr_left (fun N => (key N).symm) ?_
  -- the geometric tail vanishes in measure, by Chebyshev
  rw [tendstoInMeasure_iff_dist]
  intro ζ hζ
  have hbound : ∀ N : ℕ,
      μ {ω | ζ ≤ dist (ε t ω - (-a1) ^ (N + 1) * ε (t - (N : ℤ) - 1) ω) (ε t ω)}
        ≤ ENNReal.ofReal ((a1 ^ 2) ^ (N + 1) * σ2 / ζ ^ 2) := by
    intro N
    set Z : Ω → ℝ := fun ω => (-a1) ^ (N + 1) * ε (t - (N : ℤ) - 1) ω with hZdef
    have hZmem : MemLp Z 2 μ := (hw.memLp _).const_mul _
    have hZint : ∫ ω, Z ω ∂μ = 0 := by
      simp only [hZdef, integral_const_mul, hw.integral_eq_zero, mul_zero]
    have hpow : ((-a1) ^ (N + 1)) ^ 2 = (a1 ^ 2) ^ (N + 1) := by
      rw [← pow_mul, mul_comm (N + 1) 2, pow_mul, neg_sq]
    have hZvar : variance Z μ = (a1 ^ 2) ^ (N + 1) * σ2 := by
      rw [hZdef, variance_const_mul, hw.variance_eq, hpow]
    have hset : {ω | ζ ≤ dist (ε t ω - Z ω) (ε t ω)} = {ω | ζ ≤ |Z ω - ∫ ω, Z ω ∂μ|} := by
      ext ω
      simp only [Set.mem_setOf_eq, Real.dist_eq, hZint, sub_zero,
        show ε t ω - Z ω - ε t ω = -Z ω from by ring, abs_neg]
    rw [hset]
    exact (meas_ge_le_variance_div_sq hZmem hζ).trans (by rw [hZvar])
  have ha0 : (0 : ℝ) ≤ a1 ^ 2 := sq_nonneg _
  have ha1 : a1 ^ 2 < 1 := by nlinarith [abs_nonneg a1, sq_abs a1]
  have hreal : Tendsto (fun N : ℕ => (a1 ^ 2) ^ (N + 1) * σ2 / ζ ^ 2) atTop (nhds 0) := by
    have := (((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).comp
      (tendsto_add_atTop_nat 1)).mul_const σ2).div_const (ζ ^ 2)
    simpa using this
  have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal ((a1 ^ 2) ^ (N + 1) * σ2 / ζ ^ 2))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) hbound

/-! ### Lag polynomials acting on processes

The ARIMA composition is the identity `b(B)(1-B)^d Y = b(B) (1-B)^d Y` read off
coefficientwise. The bookkeeping runs through `papp P n W`, the polynomial `P`
applied to the process `W` as a lag operator with the sum truncated at order `n`
(faithful whenever `P.natDegree ≤ n`), and through the single structural step
`P (1-B) W = P (diff W)`. -/

/-- The coefficients of the AR polynomial `b(z) = 1 - b₁z - ⋯ - b_pz^p`. -/
private lemma coeff_arPoly {p : ℕ} (b : Fin p → ℝ) (m : ℕ) :
    (arPoly b).coeff m
      = (if m = 0 then (1 : ℝ) else 0) - ∑ i : Fin p, if m = (i : ℕ) + 1 then b i else 0 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

private lemma coeff_arPoly_zero {p : ℕ} (b : Fin p → ℝ) : (arPoly b).coeff 0 = 1 := by
  rw [coeff_arPoly]; simp

private lemma coeff_arPoly_succ {p : ℕ} (b : Fin p → ℝ) (j : Fin p) :
    (arPoly b).coeff ((j : ℕ) + 1) = -(b j) := by
  rw [coeff_arPoly]
  simp [Fin.val_eq_val, Finset.sum_ite_eq]

private lemma natDegree_arPoly_le {p : ℕ} (b : Fin p → ℝ) : (arPoly b).natDegree ≤ p := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [coeff_arPoly, if_neg (by omega), zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun i _ => if_neg ?_
  have := i.isLt
  omega

private lemma natDegree_one_sub_X_pow_le (d : ℕ) :
    ((1 - Polynomial.X : Polynomial ℝ) ^ d).natDegree ≤ d := by
  have h1 : (1 - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp
  simpa using Polynomial.natDegree_pow_le_of_le d h1

private lemma coeff_zero_one_sub_X_pow (d : ℕ) :
    ((1 - Polynomial.X : Polynomial ℝ) ^ d).coeff 0 = 1 := by
  simp [Polynomial.coeff_zero_eq_eval_zero]

/-- A polynomial acting on a process as a lag operator, with the sum truncated at
order `n`: `(P W)_t = Σ_{m ≤ n} P_m W_{t-m}`. -/
private noncomputable def papp (P : Polynomial ℝ) (n : ℕ) (W : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), P.coeff m * W (t - (m : ℤ)) ω

omit [MeasurableSpace Ω] in
/-- The constant term of `papp` split off. -/
private lemma papp_eq (P : Polynomial ℝ) (n : ℕ) (W : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    papp P n W t ω
      = P.coeff 0 * W t ω + ∑ i : Fin n, P.coeff ((i : ℕ) + 1) * W (t - 1 - (i : ℕ)) ω := by
  rw [papp, ← Fin.sum_univ_eq_sum_range (fun m => P.coeff m * W (t - (m : ℤ)) ω) (n + 1),
    Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.cast_zero, sub_zero, Fin.val_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : t - (((i : ℕ) + 1 : ℕ) : ℤ) = t - 1 - ((i : ℕ) : ℤ) := by push_cast; ring
  rw [h]

omit [MeasurableSpace Ω] in
/-- The structural step: multiplying the lag polynomial by `(1 - z)` is differencing
the process. -/
private lemma papp_mul_one_sub_X (P : Polynomial ℝ) {n : ℕ} (hn : P.natDegree ≤ n)
    (W : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    papp (P * (1 - Polynomial.X)) (n + 1) W t ω = papp P n (diff W) t ω := by
  have hc : ∀ k, (P * (1 - Polynomial.X)).coeff k
      = P.coeff k - (P * Polynomial.X).coeff k := by
    intro k; rw [mul_sub, mul_one, Polynomial.coeff_sub]
  have hfirst : ∑ k ∈ Finset.range (n + 1 + 1), P.coeff k * W (t - (k : ℤ)) ω
      = ∑ m ∈ Finset.range (n + 1), P.coeff m * W (t - (m : ℤ)) ω := by
    rw [Finset.sum_range_succ, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      zero_mul, add_zero]
  have hsecond : ∑ k ∈ Finset.range (n + 1 + 1), (P * Polynomial.X).coeff k * W (t - (k : ℤ)) ω
      = ∑ m ∈ Finset.range (n + 1), P.coeff m * W (t - (m : ℤ) - 1) ω := by
    rw [Finset.sum_range_succ']
    simp only [Polynomial.coeff_mul_X, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero,
      mul_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h : t - (((m : ℕ) + 1 : ℕ) : ℤ) = t - (m : ℤ) - 1 := by push_cast; ring
    rw [h]
  simp only [papp, hc, sub_mul, Finset.sum_sub_distrib]
  rw [hfirst, hsecond, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [diff]
  ring

omit [MeasurableSpace Ω] in
/-- The AR polynomial acting on a process is the ARMA left-hand side. -/
private lemma papp_arPoly {p : ℕ} (b : Fin p → ℝ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    papp (arPoly b) p Z t ω = Z t ω - ∑ i : Fin p, b i * Z (t - 1 - (i : ℕ)) ω := by
  have h : ∀ i : Fin p, (arPoly b).coeff ((i : ℕ) + 1) * Z (t - 1 - (i : ℕ)) ω
      = -(b i * Z (t - 1 - (i : ℕ)) ω) := by
    intro i; rw [coeff_arPoly_succ]; ring
  rw [papp_eq, coeff_arPoly_zero, one_mul, Finset.sum_congr rfl (fun i _ => h i),
    Finset.sum_neg_distrib]
  ring

omit [MeasurableSpace Ω] in
/-- `b(z)(1-z)^d` acting on `Y` is `b(z)` acting on the `d`-fold difference of `Y`. -/
private lemma papp_arPoly_mul {p : ℕ} (b : Fin p → ℝ) (d : ℕ) (Y : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    papp (arPoly b * (1 - Polynomial.X) ^ d) (p + d) Y t ω
      = papp (arPoly b) p (diff^[d] Y) t ω := by
  induction d generalizing Y with
  | zero => simp
  | succ d ih =>
    have hdeg : (arPoly b * (1 - Polynomial.X) ^ d).natDegree ≤ p + d :=
      Polynomial.natDegree_mul_le_of_le (natDegree_arPoly_le b) (natDegree_one_sub_X_pow_le d)
    have hpoly : (arPoly b * (1 - Polynomial.X) ^ (d + 1))
        = (arPoly b * (1 - Polynomial.X) ^ d) * (1 - Polynomial.X) := by ring
    rw [show p + (d + 1) = (p + d) + 1 from rfl, hpoly, papp_mul_one_sub_X _ hdeg, ih,
      Function.iterate_succ_apply]

/-- **ARIMA(p,d,q) satisfies an ARMA(p+d, q) recurrence** (FY §1.3.5; the book's
"ARMA(p+d, p)" is a misprint for the MA order `q`): the composed AR coefficients are
read off `b(z)(1−z)^d`. Nonstationarity of `Y` itself is the typical situation and is
not claimed here. -/
theorem IsARIMA.satisfiesARMA {p q d : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ}
    {Y ε : ℤ → Ω → ℝ} (h : IsARIMA b a d σ2 Y ε μ) :
    SatisfiesARMA
      (fun i : Fin (p + d) =>
        -((arPoly b * (1 - Polynomial.X) ^ d).coeff ((i : ℕ) + 1)))
      a Y ε μ := by
  intro t
  filter_upwards [h.isARMA.recurrence t] with ω hω
  -- the AR polynomial applied to the differenced process is the innovation side
  have hP : papp (arPoly b * (1 - Polynomial.X) ^ d) (p + d) Y t ω
      = ε t ω + ∑ j, a j * ε (t - 1 - (j : ℕ)) ω := by
    rw [papp_arPoly_mul, papp_arPoly, hω]
    ring
  rw [papp_eq, Polynomial.mul_coeff_zero, coeff_arPoly_zero, coeff_zero_one_sub_X_pow,
    one_mul, one_mul] at hP
  have hneg : ∑ i : Fin (p + d),
        -((arPoly b * (1 - Polynomial.X) ^ d).coeff ((i : ℕ) + 1)) * Y (t - 1 - (i : ℕ)) ω
      = -∑ i : Fin (p + d),
        (arPoly b * (1 - Polynomial.X) ^ d).coeff ((i : ℕ) + 1) * Y (t - 1 - (i : ℕ)) ω := by
    simp [neg_mul, Finset.sum_neg_distrib]
  rw [hneg]
  linarith [hP]

end StatLean.TimeSeries
