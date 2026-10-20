module
public import StatLean.NonparametricStatistics.LocalPolynomial.WeightBounds
public import StatLean.NonparametricStatistics.LocalPolynomial.SupNorm.Increments
public import StatLean.NonparametricStatistics.ForMathlib.MaxExpSquare
public import StatLean.NonparametricStatistics.ForMathlib.GaussianExpSq

@[expose] public section

/-!
# Sup-norm control of the stochastic term of the local polynomial estimator

Under i.i.d. centered Gaussian noise and a Lipschitz boxed kernel, the stochastic component
of LP(`ℓ`) satisfies
$$ \mathbb E\Bigl[\ \sup_{t\in[0,1]}\Bigl|\sum_i \xi_i\,W^*_i(t)\Bigr|^2\Bigr]
   \;\le\; C\,\frac{\sigma_\xi^2\,\log n}{n h}, $$
with `C = C(ℓ, K_max, λ₀, a₀, L_K)` — the `log n` being the price of the supremum.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.6.2 (the stochastic term of the sup-norm bound
of Theorem 1.8, via Lemma 1.6 and Corollary 1.3 on a grid of $M = n^4$ points).

**Proof formalization notes.** Discretize `[0,1]` on the grid `t_j = j/M`, `M = n⁴`:

1. *Grid maximum.* At each grid point, `∑ᵢ ξᵢW*ᵢ(t_j) = U(0)ᵀB_{t_j}⁻¹·η_j/√(nh)·…` where the
   coordinates of `η_j = (nh)^{-1/2}∑ᵢ ξᵢU(zᵢ)K(zᵢ)` are *linear combinations of i.i.d.
   Gaussians*, hence Gaussian with variance `≤ 2a₀K²_max·σ_ξ²`
   (`hasLaw_sum_mul_gaussianReal` + the design density bound). The inverse bound converts
   `|∑ξW*| ≤ ‖η_j‖·…/λ₀·(nh)^{-1/2}`, and `lintegral_iSup_normSq_gaussian_le` gives
   `E max_j ‖η_j‖² ≲ (ℓ+1)·vmax·log(√2·M(ℓ+1)) = O(log n)`.
2. *Increments.* Between grid points, `∑ᵢ|W*ᵢ(t) − W*ᵢ(t_j)| ≤ C_L·|t−t_j|/h³`
   (`lp_weight_lipschitz_sum`, from `SupNorm/Increments.lean`), so the continuum supremum
   exceeds the grid maximum by at most `max_i|ξ_i|·C_L·n^{-4}/h³`, whose second moment is
   `O(σ_ξ²·log n·n^{-8}/h⁶) = o(σ_ξ²·log n/(nh))` for `h ≥ 1/(2n)`.

The constant is existential with the stated dependence (by binder position before the
quantifiers over `n`, the design, the noise, and the sample space).

**Bibliographic comments.** The discretize-and-bound-the-maximum route to sup-norm rates is
classical; cf. C. J. Stone, *Ann. Statist.* **10** (1982), 1040–1053, and W. Härdle,
*Applied Nonparametric Regression* (Cambridge, 1990).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- ℓ²-sum of local polynomial weights: `∑ᵢ Wᵢ(s)² ≤ (C*)²/(nh)`. -/
private lemma lp_sum_weight_sq_le {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {Kmax lam0 a₀ h : ℝ}
    {ℓ : ℕ} (hn : 0 < n) (hh : 0 < h) (hhl : 1 / (2 * (n : ℝ)) ≤ h) (hlam : 0 < lam0)
    (ha₀ : 0 ≤ a₀) (heig : DesignEigenvalueLB xdat K h ℓ lam0) (hbox : KernelBoxed K Kmax)
    (hdens : DesignDensityBound xdat a₀) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i, (lpWeight xdat K h ℓ s i) ^ 2 ≤ (lpWeightConst Kmax lam0 a₀) ^ 2 / ((n : ℝ) * h) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnh : (0 : ℝ) < (n : ℝ) * h := mul_pos hnpos hh
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hC : (0 : ℝ) ≤ lpWeightConst Kmax lam0 a₀ := by
    unfold lpWeightConst
    exact le_trans (div_nonneg (mul_nonneg (by norm_num) hKmax) hlam.le) (le_max_left _ _)
  have hper : ∀ i, (lpWeight xdat K h ℓ s i) ^ 2
      ≤ lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) * |lpWeight xdat K h ℓ s i| := by
    intro i
    have habs := lp_weight_abs_le hn hh hlam ha₀ heig hbox hs i
    have h1 : (lpWeight xdat K h ℓ s i) ^ 2
        = |lpWeight xdat K h ℓ s i| * |lpWeight xdat K h ℓ s i| := by rw [← sq_abs]; ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right habs (abs_nonneg _)
  calc ∑ i, (lpWeight xdat K h ℓ s i) ^ 2
      ≤ ∑ i, lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) * |lpWeight xdat K h ℓ s i| :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) * ∑ i, |lpWeight xdat K h ℓ s i| := by
        rw [← Finset.mul_sum]
    _ ≤ lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) * lpWeightConst Kmax lam0 a₀ :=
        mul_le_mul_of_nonneg_left (lp_weight_sum_abs_le hn hhl hlam ha₀ heig hbox hdens hs)
          (div_nonneg hC hnh.le)
    _ = (lpWeightConst Kmax lam0 a₀) ^ 2 / ((n : ℝ) * h) := by rw [div_mul_eq_mul_div, ← pow_two]

/-- Every point of `[0,1]` lies within `1/M` of a grid point `j/M`, `j ≤ M`. -/
private lemma exists_grid_near {M : ℕ} (hM : 0 < M) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ j : Fin (M + 1), |t - (j : ℝ) / M| ≤ 1 / M := by
  have hMr : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have htM : 0 ≤ t * M := mul_nonneg ht.1 hMr.le
  have hle : t * (M : ℝ) ≤ (M : ℝ) := by nlinarith [ht.2, hMr.le]
  have hjle : Nat.floor (t * M) ≤ M := by
    calc Nat.floor (t * M) ≤ Nat.floor ((M : ℝ)) := Nat.floor_le_floor hle
      _ = M := Nat.floor_natCast M
  refine ⟨⟨Nat.floor (t * M), Nat.lt_succ_iff.mpr hjle⟩, ?_⟩
  have hflle : (Nat.floor (t * M) : ℝ) ≤ t * M := Nat.floor_le htM
  have hltfl : t * M < Nat.floor (t * M) + 1 := Nat.lt_floor_add_one _
  have hval : ((⟨Nat.floor (t * M), Nat.lt_succ_iff.mpr hjle⟩ : Fin (M + 1)) : ℝ)
      = (Nat.floor (t * M) : ℝ) := rfl
  have he : t - (Nat.floor (t * M) : ℝ) / M = (t * M - Nat.floor (t * M)) / M := by
    field_simp
  have habs1 : |t * M - (Nat.floor (t * M) : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [hflle, hltfl]
  rw [hval, he, abs_div, abs_of_pos hMr, div_le_div_iff₀ hMr hMr]
  exact mul_le_mul_of_nonneg_right habs1 hMr.le

/-- `log(√2·(n⁴+1)) ≤ 6·log n` for `n ≥ 2` (the price of the `n⁴`-point grid). -/
private lemma log_sqrt2_grid_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.sqrt 2 * ((n : ℝ) ^ 4 + 1)) ≤ 6 * Real.log n := by
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ 4 by norm_num); rwa [h4] at this
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
    have : (1 : ℕ) ≤ n ^ 4 := Nat.one_le_pow 4 n (by omega)
    exact_mod_cast this
  have hbound : Real.sqrt 2 * ((n : ℝ) ^ 4 + 1) ≤ (n : ℝ) ^ 6 := by
    have h1 : (n : ℝ) ^ 4 + 1 ≤ 2 * (n : ℝ) ^ 4 := by nlinarith [hn4]
    calc Real.sqrt 2 * ((n : ℝ) ^ 4 + 1) ≤ 2 * (2 * (n : ℝ) ^ 4) := by
          apply mul_le_mul hs2 h1 (by positivity) (by norm_num)
      _ = 4 * (n : ℝ) ^ 4 := by ring
      _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 4 := by
          have h4n : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hnr]
          nlinarith [h4n, pow_nonneg (show (0 : ℝ) ≤ (n : ℝ) by linarith) 4]
      _ = (n : ℝ) ^ 6 := by ring
  calc Real.log (Real.sqrt 2 * ((n : ℝ) ^ 4 + 1))
      ≤ Real.log ((n : ℝ) ^ 6) := Real.log_le_log (by positivity) hbound
    _ = 6 * Real.log n := by rw [Real.log_pow]; push_cast; ring

/-- Second moment of a centered Gaussian as a lower Lebesgue integral: `∫⁻ x², d𝒩(0,v) = v`. -/
private lemma gaussian_lintegral_sq (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 v) = ENNReal.ofReal (v : ℝ) := by
  have hint : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
    have hv := variance_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    rw [variance_eq_integral measurable_id.aemeasurable] at hv
    simpa [integral_id_gaussianReal] using hv
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal' 2 (by simp)).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall (fun x => sq_nonneg x)),
    hint]

/-- Second moment of the `ℓ¹`-norm of the noise vector: `E[(∑ᵢ|ξᵢ|)²] ≤ n²·v`. -/
private lemma lintegral_sum_abs_sq_le {n : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ξ : Fin n → Ω → ℝ) (v : ℝ≥0) (hξm : ∀ i, Measurable (ξ i))
    (hξlaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 v) P) :
    ∫⁻ ω, ENNReal.ofReal ((∑ i, |ξ i ω|) ^ 2) ∂P ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * v) := by
  have hcs : ∀ ω, (∑ i, |ξ i ω|) ^ 2 ≤ (n : ℝ) * ∑ i, (ξ i ω) ^ 2 := by
    intro ω
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => |ξ i ω|)
    simpa only [one_mul, one_pow, sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] using h
  calc ∫⁻ ω, ENNReal.ofReal ((∑ i, |ξ i ω|) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((n : ℝ) * ∑ i, (ξ i ω) ^ 2) ∂P :=
        lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hcs ω))
    _ = ∫⁻ ω, ENNReal.ofReal (n : ℝ) * ∑ i, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P := by
        refine lintegral_congr (fun ω => ?_)
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    _ = ENNReal.ofReal (n : ℝ) * ∑ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_finset_sum _ (fun i _ => by fun_prop)]
    _ = ENNReal.ofReal (n : ℝ) * ∑ _i : Fin n, ENNReal.ofReal (v : ℝ) := by
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [(hξlaw i).lintegral_comp (f := fun x => ENNReal.ofReal (x ^ 2)) (by fun_prop),
          gaussian_lintegral_sq]
    _ = ENNReal.ofReal (n : ℝ) * ENNReal.ofReal ((n : ℝ) * v) := by
        congr 1
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((n : ℝ) ^ 2 * v) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

set_option maxHeartbeats 2000000 in
/-- **Sup-norm stochastic bound**: there is `C = C(ℓ, K_max, λ₀, a₀, L_K)` such that under
the standing design assumptions, a Lipschitz boxed kernel, and i.i.d. `N(0, v)` noise,
`E[(sup_{t∈[0,1]} |∑ᵢ ξᵢ·W*ᵢ(t)|)²] ≤ C·v·log n/(n·h)` for all `n ≥ 2`,
`1/(2n) ≤ h ≤ 1`. -/
theorem lp_supnorm_stochastic_le {ℓ : ℕ} {K : ℝ → ℝ} {Kmax lam0 a₀ LK : ℝ}
    -- USER-INPUT: positive eigenvalue floor and nonnegative density constant; standing
    -- design assumptions
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: Lipschitz kernel; the sup-norm analysis input
    (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ}, 2 ≤ n → ∀ {h : ℝ}, 1 / (2 * (n : ℝ)) ≤ h → h ≤ 1 →
      ∀ {xdat : Fin n → ℝ}, (∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1) →
        DesignEigenvalueLB xdat K h ℓ lam0 → DesignDensityBound xdat a₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ξ : Fin n → Ω → ℝ) (v : ℝ≥0),
        (∀ i, Measurable (ξ i)) → iIndepFun ξ P →
        (∀ i, HasLaw (ξ i) (gaussianReal 0 v) P) →
        ∫⁻ ω, ENNReal.ofReal
            ((⨆ t : Set.Icc (0 : ℝ) 1, |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i|) ^ 2) ∂P
          ≤ ENNReal.ofReal (C * (v : ℝ) * Real.log n / ((n : ℝ) * h)) := by
  obtain ⟨CL, hCLpos, hCL⟩ := lp_weight_lipschitz_sum (ℓ := ℓ) hlam ha₀ hbox hKlip
  set Cst : ℝ := lpWeightConst Kmax lam0 a₀ with hCstdef
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hCstnn : 0 ≤ Cst := by
    rw [hCstdef, lpWeightConst]
    exact le_trans (div_nonneg (mul_nonneg (by norm_num) hKmax) hlam.le) (le_max_left _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨48 * Cst ^ 2 + 64 * CL ^ 2 / Real.log 2 + 1, by positivity, ?_⟩
  intro n hn h hhl hh1 xdat hx heig hdens Ω _ P _ ξ v hξm hξind hξlaw
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hh : 0 < h := lt_of_lt_of_le (div_pos one_pos (mul_pos (by norm_num) hnpos)) hhl
  have hnh : (0 : ℝ) < (n : ℝ) * h := mul_pos hnpos hh
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hRHSnn : (0 : ℝ) ≤ (48 * Cst ^ 2 + 64 * CL ^ 2 / Real.log 2 + 1)
      * (v : ℝ) * Real.log n / ((n : ℝ) * h) := by positivity
  -- degenerate case: `Cst = 0` (kernel bound `0`) forces all weights to vanish
  by_cases hCst0 : Cst = 0
  · have hzero : ∀ ω, (⨆ t : Set.Icc (0 : ℝ) 1,
        |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i|) ^ 2 = 0 := by
      intro ω
      have hval : ∀ t : Set.Icc (0 : ℝ) 1,
          |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i| = 0 := by
        intro t
        have hW : ∀ i, lpWeight xdat K h ℓ (t : ℝ) i = 0 := by
          intro i
          have hb := lp_weight_abs_le hn0 hh hlam ha₀ heig hbox t.2 i
          rw [← hCstdef, hCst0, zero_div] at hb
          exact abs_nonpos_iff.mp hb
        simp [hW]
      rw [show (⨆ t : Set.Icc (0 : ℝ) 1, |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i|)
          = 0 from by simp only [hval]; exact ciSup_const]
      norm_num
    have hL0 : ∫⁻ ω, ENNReal.ofReal ((⨆ t : Set.Icc (0 : ℝ) 1,
        |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i|) ^ 2) ∂P = 0 := by
      simp only [hzero, ENNReal.ofReal_zero, lintegral_zero]
    rw [hL0]; exact zero_le
  have hCstpos : 0 < Cst := lt_of_le_of_ne hCstnn (Ne.symm hCst0)
  -- degenerate case: `v = 0` forces the noise to vanish a.e.
  by_cases hv0 : v = 0
  · have hxi0 : ∀ i, ξ i =ᵐ[P] 0 := by
      intro i
      have hmap : P.map (ξ i) = Measure.dirac 0 := by
        rw [(hξlaw i).map_eq, hv0, gaussianReal_zero_var]
      have hne : P {ω | ξ i ω ≠ 0} = 0 := by
        have hset : {ω | ξ i ω ≠ 0} = ξ i ⁻¹' {(0 : ℝ)}ᶜ := by ext ω; simp
        rw [hset, ← Measure.map_apply (hξm i) (measurableSet_singleton (0 : ℝ)).compl, hmap,
          Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl]
        simp
      exact ae_iff.mpr hne
    have hZ0 : ∀ᵐ ω ∂P, (⨆ t : Set.Icc (0 : ℝ) 1,
        |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i|) ^ 2 = 0 := by
      have hall : ∀ᵐ ω ∂P, ∀ i, ξ i ω = 0 := (ae_all_iff).mpr hxi0
      filter_upwards [hall] with ω hω
      have : ∀ t : Set.Icc (0 : ℝ) 1, |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i| = 0 := by
        intro t; simp [hω]
      rw [show (⨆ t : Set.Icc (0 : ℝ) 1, |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i|)
          = 0 from by simp only [this]; exact ciSup_const]
      norm_num
    rw [lintegral_congr_ae (hZ0.mono (fun ω h => by rw [h, ENNReal.ofReal_zero]))]
    simp only [lintegral_zero]; exact zero_le
  -- main case: `Cst > 0` and `v > 0`
  have hvpos : 0 < v := pos_iff_ne_zero.mpr hv0
  have hvR : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr hvpos
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hCLnn : 0 ≤ CL := hCLpos.le
  set M : ℕ := n ^ 4 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hMr : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hMpos
  set s : Fin (M + 1) → ℝ := fun j => (j : ℝ) / M with hsdef
  have hs01 : ∀ j, s j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    refine ⟨by positivity, ?_⟩
    rw [hsdef, div_le_one hMr]
    exact_mod_cast Nat.lt_succ_iff.mp j.isLt
  set a : ℝ := ((n : ℝ) * h) / (4 * Cst ^ 2 * (v : ℝ)) with hadef
  have hapos : 0 < a := by rw [hadef]; positivity
  set Z : Ω → ℝ → ℝ := fun ω s => ∑ i, ξ i ω * lpWeight xdat K h ℓ s i with hZdef
  have hZapp : ∀ ω s, Z ω s = ∑ i, ξ i ω * lpWeight xdat K h ℓ s i := fun _ _ => rfl
  set E : Ω → ℝ := fun ω => (∑ i, |ξ i ω|) * (CL / ((M : ℝ) * h ^ 3)) with hEdef
  have hEapp : ∀ ω, E ω = (∑ i, |ξ i ω|) * (CL / ((M : ℝ) * h ^ 3)) := fun _ => rfl
  have hη_meas : ∀ j, Measurable (fun ω => Z ω (s j)) := by
    intro j
    simp only [hZapp]
    exact Finset.measurable_sum Finset.univ (fun i _ => (hξm i).mul_const _)
  have hbddabove : ∀ ω, BddAbove (Set.range fun t : Set.Icc (0 : ℝ) 1 => |Z ω (t : ℝ)|) := by
    intro ω
    refine ⟨(∑ i, |ξ i ω|) * Cst / ((n : ℝ) * h), ?_⟩
    rintro _ ⟨t, rfl⟩
    simp only [hZapp]
    calc |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i|
        ≤ ∑ i, |ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |ξ i ω| * |lpWeight xdat K h ℓ (t : ℝ) i| := by simp_rw [abs_mul]
      _ ≤ ∑ i, |ξ i ω| * (Cst / ((n : ℝ) * h)) := by
          refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
          rw [hCstdef]; exact lp_weight_abs_le hn0 hh hlam ha₀ heig hbox t.2 i
      _ = (∑ i, |ξ i ω|) * Cst / ((n : ℝ) * h) := by rw [← Finset.sum_mul]; ring
  -- pointwise bound
  have hpt : ∀ ω, (⨆ t : Set.Icc (0 : ℝ) 1, |Z ω (t : ℝ)|) ^ 2
      ≤ 2 * (⨆ j, (Z ω (s j)) ^ 2) + 2 * (E ω) ^ 2 := by
    intro ω
    have hbddg : BddAbove (Set.range fun j => |Z ω (s j)|) := (Set.finite_range _).bddAbove
    have hbddsq : BddAbove (Set.range fun j => (Z ω (s j)) ^ 2) := (Set.finite_range _).bddAbove
    set sgrid : ℝ := ⨆ j, (Z ω (s j)) ^ 2 with hsgrid
    have hsgrid_nn : 0 ≤ sgrid := le_trans (sq_nonneg (Z ω (s 0))) (le_ciSup hbddsq 0)
    have hgle : (⨆ j, |Z ω (s j)|) ≤ Real.sqrt sgrid := by
      apply ciSup_le; intro j
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (le_ciSup hbddsq j)
    have hgabs_nn : 0 ≤ ⨆ j, |Z ω (s j)| := le_trans (abs_nonneg _) (le_ciSup hbddg 0)
    have hgsq : (⨆ j, |Z ω (s j)|) ^ 2 ≤ sgrid := by
      calc (⨆ j, |Z ω (s j)|) ^ 2 ≤ (Real.sqrt sgrid) ^ 2 := pow_le_pow_left₀ hgabs_nn hgle 2
        _ = sgrid := Real.sq_sqrt hsgrid_nn
    have hkey : (⨆ t : Set.Icc (0 : ℝ) 1, |Z ω (t : ℝ)|) ≤ (⨆ j, |Z ω (s j)|) + E ω := by
      apply ciSup_le; intro t
      obtain ⟨j, hj⟩ := exists_grid_near hMpos t.2
      have hinc : |Z ω (t : ℝ) - Z ω (s j)| ≤ E ω := by
        have hdiff : Z ω (t : ℝ) - Z ω (s j)
            = ∑ i, ξ i ω * (lpWeight xdat K h ℓ (t : ℝ) i - lpWeight xdat K h ℓ (s j) i) := by
          rw [hZapp, hZapp, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        have hM1 : |(t : ℝ) - s j| * (M : ℝ) ≤ 1 := by
          have hh2 := mul_le_mul_of_nonneg_right hj hMr.le
          rwa [div_mul_cancel₀ _ hMr.ne'] at hh2
        rw [hdiff, hEapp]
        calc |∑ i, ξ i ω * (lpWeight xdat K h ℓ (t : ℝ) i - lpWeight xdat K h ℓ (s j) i)|
            ≤ ∑ i, |ξ i ω| * |lpWeight xdat K h ℓ (t : ℝ) i - lpWeight xdat K h ℓ (s j) i| := by
              refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
              simp_rw [abs_mul]
          _ ≤ ∑ i, |ξ i ω|
                * (∑ i', |lpWeight xdat K h ℓ (t : ℝ) i' - lpWeight xdat K h ℓ (s j) i'|) := by
              refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
              exact Finset.single_le_sum
                (f := fun i' => |lpWeight xdat K h ℓ (t : ℝ) i' - lpWeight xdat K h ℓ (s j) i'|)
                (fun i' _ => abs_nonneg _) (Finset.mem_univ i)
          _ = (∑ i, |ξ i ω|)
                * (∑ i', |lpWeight xdat K h ℓ (t : ℝ) i' - lpWeight xdat K h ℓ (s j) i'|) := by
              rw [← Finset.sum_mul]
          _ ≤ (∑ i, |ξ i ω|) * (CL * |(t : ℝ) - s j| / h ^ 3) := by
              refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg (fun i _ => abs_nonneg _))
              exact hCL hn0 hhl hh1 hx heig hdens (t : ℝ) t.2 (s j) (hs01 j)
          _ ≤ (∑ i, |ξ i ω|) * (CL / ((M : ℝ) * h ^ 3)) := by
              refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg (fun i _ => abs_nonneg _))
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM1 hCLnn)
                (pow_pos hh 3).le]
      calc |Z ω (t : ℝ)| = |Z ω (s j) + (Z ω (t : ℝ) - Z ω (s j))| := by congr 1; ring
        _ ≤ |Z ω (s j)| + |Z ω (t : ℝ) - Z ω (s j)| := abs_add_le _ _
        _ ≤ (⨆ j', |Z ω (s j')|) + E ω := add_le_add (le_ciSup hbddg j) hinc
    have hsupt_nn : 0 ≤ ⨆ t : Set.Icc (0 : ℝ) 1, |Z ω (t : ℝ)| :=
      le_trans (abs_nonneg _) (le_ciSup (hbddabove ω)
        (⟨0, Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩⟩ : Set.Icc (0 : ℝ) 1))
    calc (⨆ t : Set.Icc (0 : ℝ) 1, |Z ω (t : ℝ)|) ^ 2
        ≤ ((⨆ j, |Z ω (s j)|) + E ω) ^ 2 := pow_le_pow_left₀ hsupt_nn hkey 2
      _ ≤ 2 * (⨆ j, |Z ω (s j)|) ^ 2 + 2 * (E ω) ^ 2 := by
          nlinarith [sq_nonneg ((⨆ j, |Z ω (s j)|) - E ω)]
      _ ≤ 2 * sgrid + 2 * (E ω) ^ 2 := by nlinarith [hgsq]
  -- grid maximum bound
  have hgrid : ∫⁻ ω, ENNReal.ofReal (⨆ j, (Z ω (s j)) ^ 2) ∂P
      ≤ ENNReal.ofReal (24 * Cst ^ 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h)) := by
    have hexp : ∀ j, ∫⁻ ω, ENNReal.ofReal (Real.exp (a * (Z ω (s j)) ^ 2)) ∂P
        ≤ ENNReal.ofReal (Real.sqrt 2) := by
      intro j
      have hlaw : HasLaw (fun ω => Z ω (s j))
          (gaussianReal 0 ((∑ i, (lpWeight xdat K h ℓ (s j) i) ^ 2).toNNReal * v)) P := by
        have hL := hasLaw_sum_mul_gaussianReal (P := P)
          (fun i => lpWeight xdat K h ℓ (s j) i) hξm hξind hξlaw
        have heq : (fun ω => ∑ i, lpWeight xdat K h ℓ (s j) i * ξ i ω) = (fun ω => Z ω (s j)) := by
          funext ω; rw [hZapp]; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        rwa [heq] at hL
      rw [hlaw.lintegral_comp (f := fun x => ENNReal.ofReal (Real.exp (a * x ^ 2))) (by fun_prop)]
      apply lintegral_exp_mul_sq_gaussianReal_le
      have hσ : (((∑ i, (lpWeight xdat K h ℓ (s j) i) ^ 2).toNNReal * v : ℝ≥0) : ℝ)
          = (∑ i, (lpWeight xdat K h ℓ (s j) i) ^ 2) * (v : ℝ) := by
        rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
      rw [hσ]
      have hsw := lp_sum_weight_sq_le hn0 hh hhl hlam ha₀ heig hbox hdens (hs01 j)
      have key : a * (4 * ((∑ i, (lpWeight xdat K h ℓ (s j) i) ^ 2) * (v : ℝ)))
          = ((n : ℝ) * h) * (∑ i, (lpWeight xdat K h ℓ (s j) i) ^ 2) / Cst ^ 2 := by
        rw [hadef]; field_simp
      rw [key, div_le_one (by positivity : (0 : ℝ) < Cst ^ 2)]
      calc ((n : ℝ) * h) * (∑ i, (lpWeight xdat K h ℓ (s j) i) ^ 2)
          ≤ ((n : ℝ) * h) * (Cst ^ 2 / ((n : ℝ) * h)) := mul_le_mul_of_nonneg_left hsw hnh.le
        _ = Cst ^ 2 := by field_simp
    have hbase := lintegral_iSup_sq_le_log (P := P) (by omega : 1 ≤ M + 1) hapos hη_meas hexp
    refine le_trans hbase (ENNReal.ofReal_le_ofReal ?_)
    have hMcast : ((M + 1 : ℕ) : ℝ) = (n : ℝ) ^ 4 + 1 := by rw [hMdef]; push_cast; ring
    rw [hMcast, div_le_iff₀ hapos]
    have hrhs : 24 * Cst ^ 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h) * a = 6 * Real.log n := by
      rw [hadef]; field_simp; ring
    rw [hrhs]; exact log_sqrt2_grid_le hn
  -- increment bound
  have hincr : ∫⁻ ω, ENNReal.ofReal ((E ω) ^ 2) ∂P
      ≤ ENNReal.ofReal (32 * CL ^ 2 / Real.log 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h)) := by
    have hc0nn : (0 : ℝ) ≤ (CL / ((M : ℝ) * h ^ 3)) ^ 2 := by positivity
    have hnum : (CL / ((M : ℝ) * h ^ 3)) ^ 2 * ((n : ℝ) ^ 2 * (v : ℝ))
        ≤ 32 * CL ^ 2 / Real.log 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h) := by
      have h1 : (CL / ((M : ℝ) * h ^ 3)) ^ 2 * ((n : ℝ) ^ 2 * (v : ℝ))
          = CL ^ 2 * (v : ℝ) / ((n : ℝ) ^ 6 * h ^ 6) := by rw [hMdef]; push_cast; field_simp
      have hRHSeq : 32 * CL ^ 2 / Real.log 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h)
          = (32 * CL ^ 2 * (v : ℝ) * Real.log n) / (Real.log 2 * ((n : ℝ) * h)) := by
        field_simp
      have hnh_half : (1 : ℝ) / 2 ≤ (n : ℝ) * h := by
        have hm := mul_le_mul_of_nonneg_left hhl hnpos.le
        rw [show (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 / 2 by field_simp] at hm; linarith
      have h32 : (1 : ℝ) ≤ 32 * ((n : ℝ) * h) ^ 5 := by
        nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hnh_half 5]
      have hlogn2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnr
      have hkey5 : Real.log 2 ≤ 32 * Real.log n * ((n : ℝ) * h) ^ 5 := by
        nlinarith [mul_le_mul_of_nonneg_left h32 hlogn, hlogn2]
      rw [h1, hRHSeq, div_le_div_iff₀ (by positivity) (mul_pos hlog2 hnh)]
      nlinarith [mul_le_mul_of_nonneg_left hkey5
        (by positivity : (0 : ℝ) ≤ CL ^ 2 * (v : ℝ) * ((n : ℝ) * h))]
    calc ∫⁻ ω, ENNReal.ofReal ((E ω) ^ 2) ∂P
        = ∫⁻ ω, ENNReal.ofReal ((CL / ((M : ℝ) * h ^ 3)) ^ 2)
            * ENNReal.ofReal ((∑ i, |ξ i ω|) ^ 2) ∂P := by
          refine lintegral_congr (fun ω => ?_)
          rw [hEapp, mul_pow, mul_comm ((∑ i, |ξ i ω|) ^ 2) _, ENNReal.ofReal_mul hc0nn]
      _ = ENNReal.ofReal ((CL / ((M : ℝ) * h ^ 3)) ^ 2)
            * ∫⁻ ω, ENNReal.ofReal ((∑ i, |ξ i ω|) ^ 2) ∂P := by
          rw [lintegral_const_mul _ (by fun_prop)]
      _ ≤ ENNReal.ofReal ((CL / ((M : ℝ) * h ^ 3)) ^ 2) * ENNReal.ofReal ((n : ℝ) ^ 2 * v) :=
          mul_le_mul_right (lintegral_sum_abs_sq_le ξ v hξm hξlaw) _
      _ = ENNReal.ofReal ((CL / ((M : ℝ) * h ^ 3)) ^ 2 * ((n : ℝ) ^ 2 * v)) :=
          (ENNReal.ofReal_mul hc0nn).symm
      _ ≤ ENNReal.ofReal (32 * CL ^ 2 / Real.log 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h)) :=
          ENNReal.ofReal_le_ofReal hnum
  -- assemble
  have hsup_meas : Measurable (fun ω => ⨆ j, (Z ω (s j)) ^ 2) :=
    Measurable.iSup (fun j => (hη_meas j).pow_const 2)
  have hE_meas : Measurable E := by
    rw [hEdef]
    exact (Finset.measurable_sum Finset.univ (fun i _ => (hξm i).abs)).mul_const _
  have hdbl : ∀ y : ℝ, (2 : ℝ≥0∞) * ENNReal.ofReal y = ENNReal.ofReal (2 * y) := fun y => by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hA : ∫⁻ ω, ENNReal.ofReal (2 * (⨆ j, (Z ω (s j)) ^ 2)) ∂P
      = 2 * ∫⁻ ω, ENNReal.ofReal (⨆ j, (Z ω (s j)) ^ 2) ∂P := by
    rw [← lintegral_const_mul 2 hsup_meas.ennreal_ofReal]
    exact lintegral_congr (fun ω => (hdbl _).symm)
  have hB : ∫⁻ ω, ENNReal.ofReal (2 * (E ω) ^ 2) ∂P
      = 2 * ∫⁻ ω, ENNReal.ofReal ((E ω) ^ 2) ∂P := by
    rw [← lintegral_const_mul 2 (hE_meas.pow_const 2).ennreal_ofReal]
    exact lintegral_congr (fun ω => (hdbl _).symm)
  calc ∫⁻ ω, ENNReal.ofReal ((⨆ t : Set.Icc (0 : ℝ) 1,
        |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i|) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (2 * (⨆ j, (Z ω (s j)) ^ 2) + 2 * (E ω) ^ 2) ∂P :=
        lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hpt ω))
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (2 * (⨆ j, (Z ω (s j)) ^ 2))
          + ENNReal.ofReal (2 * (E ω) ^ 2)) ∂P :=
        lintegral_mono (fun ω => ENNReal.ofReal_add_le)
    _ = ∫⁻ ω, ENNReal.ofReal (2 * (⨆ j, (Z ω (s j)) ^ 2)) ∂P
          + ∫⁻ ω, ENNReal.ofReal (2 * (E ω) ^ 2) ∂P :=
        lintegral_add_left (by measurability) _
    _ = 2 * ∫⁻ ω, ENNReal.ofReal (⨆ j, (Z ω (s j)) ^ 2) ∂P
          + 2 * ∫⁻ ω, ENNReal.ofReal ((E ω) ^ 2) ∂P := by rw [hA, hB]
    _ ≤ 2 * ENNReal.ofReal (24 * Cst ^ 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h))
          + 2 * ENNReal.ofReal (32 * CL ^ 2 / Real.log 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h)) :=
        add_le_add (mul_le_mul_right hgrid 2) (mul_le_mul_right hincr 2)
    _ = ENNReal.ofReal (48 * Cst ^ 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h))
          + ENNReal.ofReal (64 * CL ^ 2 / Real.log 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h)) := by
        rw [hdbl, hdbl]; congr 1 <;> · congr 1; ring
    _ = ENNReal.ofReal (48 * Cst ^ 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h)
          + 64 * CL ^ 2 / Real.log 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((48 * Cst ^ 2 + 64 * CL ^ 2 / Real.log 2 + 1)
          * (v : ℝ) * Real.log n / ((n : ℝ) * h)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have heq : (48 * Cst ^ 2 + 64 * CL ^ 2 / Real.log 2 + 1) * (v : ℝ) * Real.log n
              / ((n : ℝ) * h)
            = 48 * Cst ^ 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h)
              + 64 * CL ^ 2 / Real.log 2 * (v : ℝ) * Real.log n / ((n : ℝ) * h)
              + (v : ℝ) * Real.log n / ((n : ℝ) * h) := by ring
        have hXnn : (0 : ℝ) ≤ (v : ℝ) * Real.log n / ((n : ℝ) * h) :=
          div_nonneg (mul_nonneg (NNReal.coe_nonneg v) hlogn) hnh.le
        linarith [heq, hXnn]

end StatLean.NonparametricStatistics
