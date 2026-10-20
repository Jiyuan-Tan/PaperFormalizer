module
public import StatLean.NonparametricStatistics.LocalPolynomial.WeightBounds
public import StatLean.NonparametricStatistics.LocalPolynomial.Reproduction
public import StatLean.NonparametricStatistics.SmoothnessClasses.HolderTaylor
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Pointwise risk of the local polynomial estimator

Bias and variance of LP(`ℓ`) with `ℓ = holderIndex β` over the Hölder class `Σ(β, L)` on
`[0,1]`, under the standing design/kernel assumptions and independent centered noise with
second moments bounded by `σ²_max`:
$$ |b(x_0)| \le q_1 h^{\beta}, \qquad \sigma^2(x_0) \le \frac{q_2}{nh}, \qquad
   q_1 = \frac{C^* L}{\ell!},\quad q_2 = \sigma_{\max}^2 (C^*)^2, $$
and the assembled pointwise rate with `h = α·n^{−1/(2β+1)}`:
`E[(f̂(x₀) − f(x₀))²] ≤ lpRateConst·n^{−2β/(2β+1)}` — with a fully explicit constant.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.6.1, Proposition 1.13 (LP bias and variance,
constants $q_1 = C_* L/\ell!$, $q_2 = \sigma_{\max}^2 C_*^2$) and Theorem 1.6 (pointwise rate
$n^{-2\beta/(2\beta+1)}$).

**Proof formalization notes.** *Bias* (deterministic): with `∑ W* = 1` (reproduction) and the
support/ℓ¹ weight bounds,
`|∑ f(xᵢ)W*ᵢ − f(t)| = |∑ (f(xᵢ) − Taylor_t(xᵢ))W*ᵢ| ≤ (L/ℓ!)·∑|xᵢ−t|^β|W*ᵢ|
 ≤ (L/ℓ!)·h^β·C*` — the intermediate Taylor terms of orders `1, …, ℓ` are killed by monomial
reproduction, and `|xᵢ−t| ≤ h` on the support of the weights. *Variance*: independence gives
`σ²(x₀) = ∑ (W*ᵢ)²·E ξᵢ² ≤ σ²_max·(sup|W*|)·∑|W*| ≤ σ²_max·C*²/(nh)` (noise second moments in
`∫⁻` form force genuine square-integrability). *Rate*: MSE = bias² + variance (exact under
`L²`), then substitute the bandwidth. Positive definiteness of `B_t` needed by reproduction
is derived from the eigenvalue hypothesis (`lpMatrix_posDef`).

**Bibliographic comments.** Pointwise rates for local polynomial estimators over Hölder
classes are due to C. J. Stone, *Ann. Statist.* **8** (1980), 1348–1360 (rectangular kernel)
with the general kernel treatment standard since the 1980s; see J. Fan and I. Gijbels,
*Local Polynomial Modelling and Its Applications* (1996).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

variable {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {h lam0 a₀ Kmax : ℝ}

/-- Nonnegativity of the weight constant `C*` from the boxed-kernel and design hypotheses. -/
private lemma lpWeightConst_nonneg (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀) (hbox : KernelBoxed K Kmax) :
    0 ≤ lpWeightConst Kmax lam0 a₀ := by
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  exact le_trans (div_nonneg (mul_nonneg (by norm_num) hKmax) hlam.le) (le_max_left _ _)

/-- Each noise coordinate is square-integrable (`MemLp 2`) from its `∫⁻`-moment bound. -/
private lemma lp_xi_memLp {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Fin n → Ω → ℝ} {σmax2 : ℝ} (i : Fin n)
    (hξm : Measurable (ξ i))
    (hξ2 : ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P ≤ ENNReal.ofReal σmax2) :
    MemLp (ξ i) 2 P := by
  refine (memLp_two_iff_integrable_sq hξm.aestronglyMeasurable).mpr
    ⟨(hξm.pow_const 2).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => sq_nonneg _)).mpr
    (lt_of_le_of_lt hξ2 ENNReal.ofReal_lt_top)

/-- The LP estimator on noisy data is square-integrable. -/
private lemma lp_estimator_memLp {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {h : ℝ} {ℓ : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin n → Ω → ℝ} {σmax2 : ℝ} {f : ℝ → ℝ} {t : ℝ}
    (hξm : ∀ i, Measurable (ξ i))
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P ≤ ENNReal.ofReal σmax2) :
    MemLp (fun ω => lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t) 2 P := by
  have hrw : (fun ω => lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t)
      = ∑ i : Fin n, (fun ω => (f (xdat i) + ξ i ω) * lpWeight xdat K h ℓ t i) := by
    funext ω; simp only [lpEstimator, Finset.sum_apply]
  rw [hrw]
  exact memLp_finset_sum' _ (fun i _ =>
    ((memLp_const (f (xdat i))).add (lp_xi_memLp i (hξm i) (hξ2 i))).mul_const _)

/-- Exact bias–variance decomposition of the pointwise squared error, in `∫⁻` form. -/
private lemma mse_decomp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : Ω → ℝ} (hS : MemLp S 2 P) (y : ℝ) :
    ∫⁻ ω, ENNReal.ofReal ((S ω - y) ^ 2) ∂P
      = ENNReal.ofReal (((∫ ω, S ω ∂P) - y) ^ 2)
        + ∫⁻ ω, ENNReal.ofReal ((S ω - ∫ ω', S ω' ∂P) ^ 2) ∂P := by
  have hInt2 : Integrable S P := hS.integrable (by norm_num)
  set m := ∫ ω, S ω ∂P with hm
  have hcenter : ∫ ω, (S ω - m) ∂P = 0 := by
    rw [integral_sub hInt2 (integrable_const _), integral_const, hm]; simp
  have hV : Integrable (fun ω => (S ω - m) ^ 2) P := (hS.sub (memLp_const _)).integrable_sq
  have hC : Integrable (fun ω => S ω - m) P := hInt2.sub (integrable_const _)
  have hsqint : Integrable (fun ω => (S ω - y) ^ 2) P := (hS.sub (memLp_const _)).integrable_sq
  have hexp : ∀ ω, (S ω - y) ^ 2 - (S ω - m) ^ 2 = (2 * (m - y)) * (S ω - m) + (m - y) ^ 2 :=
    fun ω => by ring
  have hstep : ∫ ω, ((S ω - y) ^ 2 - (S ω - m) ^ 2) ∂P = (m - y) ^ 2 := by
    rw [integral_congr_ae (ae_of_all _ hexp),
      integral_add (hC.const_mul (2 * (m - y))) (integrable_const _),
      integral_const_mul, hcenter, mul_zero, integral_const]
    simp
  have hkey : ∫ ω, (S ω - y) ^ 2 ∂P = (m - y) ^ 2 + ∫ ω, (S ω - m) ^ 2 ∂P := by
    rw [← hstep, integral_sub hsqint hV]; ring
  rw [← ofReal_integral_eq_lintegral_ofReal hsqint (ae_of_all _ fun ω => sq_nonneg _),
    hkey, ENNReal.ofReal_add (sq_nonneg _) (integral_nonneg fun ω => sq_nonneg _)]
  congr 1
  exact ofReal_integral_eq_lintegral_ofReal hV (ae_of_all _ fun ω => sq_nonneg _)

/-- **Deterministic bias bound of LP(`ℓ`)** over `Σ(β, L)` on `[0,1]`:
`|∑ i, f(xdat i)·W*ᵢ(t) − f(t)| ≤ q₁·h^β` with `q₁ = lpBiasConst β L Kmax lam0 a₀`. -/
theorem lp_bias_deterministic {β L : ℝ}
    -- USER-INPUT: positive smoothness and nonnegative Hölder constant; class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    -- LEAN-ONLY: nonempty sample; standard side condition
    (hn : 0 < n)
    -- USER-INPUT: bandwidth at least `1/(2n)`; classical range of the weight bounds
    (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    -- USER-INPUT: positive eigenvalue floor and nonnegative density constant; standing
    -- design assumptions
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: design points lie in `[0,1]`; the fixed-design model on the unit interval
    (hx : ∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: eigenvalue lower bound on the local design matrix; standing assumption
    (heig : DesignEigenvalueLB xdat K h (holderIndex β) lam0)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: design density bound; standing design assumption
    (hdens : DesignDensityBound xdat a₀)
    {f : ℝ → ℝ}
    -- USER-INPUT: the regression function lies in `Σ(β, L)` on `[0,1]`
    (hf : MemHolderOn β L f (Set.Icc 0 1))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |∑ i, f (xdat i) * lpWeight xdat K h (holderIndex β) t i - f t|
      ≤ lpBiasConst β L Kmax lam0 a₀ * h ^ β := by
  set ℓ := holderIndex β with hℓ
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hh : 0 < h := lt_of_lt_of_le (div_pos one_pos (mul_pos two_pos hnpos)) hhl
  have hpd : (lpMatrix xdat K h ℓ t).PosDef := lpMatrix_posDef hlam (heig t ht)
  -- within-interval Taylor polynomial of `f` at `t`
  set P : Fin n → ℝ := fun i => ∑ j ∈ Finset.range (ℓ + 1),
      iteratedDerivWithin j f (Set.Icc 0 1) t * (xdat i - t) ^ j / (Nat.factorial j : ℝ)
    with hP
  -- reproduction of the Taylor polynomial: `∑ i, P i · W*ᵢ = f t`
  have hrepro : ∑ i, P i * lpWeight xdat K h ℓ t i = f t := by
    have hc := lp_weight_reproduce_poly hpd hh.ne'
      (fun k : Fin (ℓ + 1) =>
        iteratedDerivWithin (k : ℕ) f (Set.Icc 0 1) t / (Nat.factorial (k : ℕ) : ℝ))
    simp only [Fin.val_zero, iteratedDerivWithin_zero, Nat.factorial_zero, Nat.cast_one,
      div_one] at hc
    rw [← hc]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [hP]
    rw [Fin.sum_univ_eq_sum_range (fun m =>
      iteratedDerivWithin m f (Set.Icc 0 1) t / (Nat.factorial m : ℝ) * (xdat i - t) ^ m) (ℓ + 1)]
    apply Finset.sum_congr rfl
    intro j _; ring
  -- rewrite the error as a weighted sum of Taylor remainders
  have hkeyeq : (∑ i, f (xdat i) * lpWeight xdat K h ℓ t i) - f t
      = ∑ i, (f (xdat i) - P i) * lpWeight xdat K h ℓ t i := by
    rw [← hrepro, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hkeyeq]
  -- per-term bound
  have hq : 0 ≤ L / (Nat.factorial ℓ : ℝ) := div_nonneg hL (by positivity)
  have hhβ : (0 : ℝ) ≤ h ^ β := (Real.rpow_nonneg hh.le β)
  have hterm : ∀ i, |(f (xdat i) - P i) * lpWeight xdat K h ℓ t i|
      ≤ (L / (Nat.factorial ℓ : ℝ) * h ^ β) * |lpWeight xdat K h ℓ t i| := by
    intro i
    rw [abs_mul]
    rcases lt_or_ge h |xdat i - t| with hfar | hnear
    · rw [lp_weight_eq_zero_of_far hh hbox hfar, abs_zero, mul_zero, mul_zero]
    · have htay := MemHolderOn.taylor_remainder_abs_le_Icc (a := 0) (b := 1) one_pos hβ hL hf ht
        (hx i)
      have hrem : |f (xdat i) - P i| ≤ L / (Nat.factorial ℓ : ℝ) * h ^ β := by
        refine le_trans htay ?_
        rw [hℓ]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hnear hβ.le) hq
      exact mul_le_mul_of_nonneg_right hrem (abs_nonneg _)
  calc |∑ i, (f (xdat i) - P i) * lpWeight xdat K h ℓ t i|
      ≤ ∑ i, |(f (xdat i) - P i) * lpWeight xdat K h ℓ t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (L / (Nat.factorial ℓ : ℝ) * h ^ β) * |lpWeight xdat K h ℓ t i| :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (L / (Nat.factorial ℓ : ℝ) * h ^ β) * ∑ i, |lpWeight xdat K h ℓ t i| := by
        rw [← Finset.mul_sum]
    _ ≤ (L / (Nat.factorial ℓ : ℝ) * h ^ β) * lpWeightConst Kmax lam0 a₀ := by
        apply mul_le_mul_of_nonneg_left
          (lp_weight_sum_abs_le hn hhl hlam ha₀ heig hbox hdens ht)
        exact mul_nonneg hq hhβ
    _ = lpBiasConst β L Kmax lam0 a₀ * h ^ β := by rw [lpBiasConst, hℓ]; ring

/-- **Pointwise variance bound of LP(`ℓ`)** under independent centered noise with second
moments at most `σ²_max`: `σ²(t) ≤ q₂/(n·h)` with `q₂ = lpVarConst σmax2 Kmax lam0 a₀`. -/
theorem lp_variance_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Fin n → Ω → ℝ} {σmax2 : ℝ} {ℓ : ℕ} {f : ℝ → ℝ}
    -- LEAN-ONLY: nonempty sample; standard side condition
    (hn : 0 < n)
    -- USER-INPUT: bandwidth at least `1/(2n)`; classical range of the weight bounds
    (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    -- USER-INPUT: positive eigenvalue floor and nonnegative density constant; standing
    -- design assumptions
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: eigenvalue lower bound on the local design matrix; standing assumption
    (heig : DesignEigenvalueLB xdat K h ℓ lam0)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: design density bound; standing design assumption
    (hdens : DesignDensityBound xdat a₀)
    -- LEAN-ONLY: measurability of the noise; standard regularity
    (hξm : ∀ i, Measurable (ξ i))
    -- USER-INPUT: mutually independent noise; the fixed-design regression model
    (hξi : iIndepFun ξ P)
    -- USER-INPUT: centered noise; the fixed-design regression model
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    -- USER-INPUT: noise second moments at most `σ²_max` (lower-Lebesgue form, so the bound
    -- is a genuine moment constraint); the fixed-design regression model
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P ≤ ENNReal.ofReal σmax2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫⁻ ω, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t
          - ∫ ω', lpEstimator xdat (fun i => f (xdat i) + ξ i ω') K h ℓ t ∂P) ^ 2) ∂P
      ≤ ENNReal.ofReal (lpVarConst σmax2 Kmax lam0 a₀ / ((n : ℝ) * h)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hh : 0 < h := lt_of_lt_of_le (div_pos one_pos (mul_pos two_pos hnpos)) hhl
  have hnh : (0 : ℝ) < (n : ℝ) * h := mul_pos hnpos hh
  have hCnn : 0 ≤ lpWeightConst Kmax lam0 a₀ := lpWeightConst_nonneg hlam ha₀ hbox
  -- `∑ᵢ (W*ᵢ)² ≤ (C*)²/(nh)`
  have hsumsq : ∑ i, (lpWeight xdat K h ℓ t i) ^ 2
      ≤ (lpWeightConst Kmax lam0 a₀) ^ 2 / ((n : ℝ) * h) := by
    have hb1 : ∀ i, (lpWeight xdat K h ℓ t i) ^ 2
        ≤ (lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h)) * |lpWeight xdat K h ℓ t i| := by
      intro i
      have habs := lp_weight_abs_le hn hh hlam ha₀ heig hbox ht i
      have hsq : (lpWeight xdat K h ℓ t i) ^ 2
          = |lpWeight xdat K h ℓ t i| * |lpWeight xdat K h ℓ t i| := by
        rw [← sq_abs]; ring
      rw [hsq]
      exact mul_le_mul_of_nonneg_right habs (abs_nonneg _)
    calc ∑ i, (lpWeight xdat K h ℓ t i) ^ 2
        ≤ ∑ i, (lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h)) * |lpWeight xdat K h ℓ t i| :=
          Finset.sum_le_sum (fun i _ => hb1 i)
      _ = (lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h)) * ∑ i, |lpWeight xdat K h ℓ t i| := by
          rw [← Finset.mul_sum]
      _ ≤ (lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h)) * lpWeightConst Kmax lam0 a₀ := by
          apply mul_le_mul_of_nonneg_left
            (lp_weight_sum_abs_le hn hhl hlam ha₀ heig hbox hdens ht)
          exact div_nonneg hCnn hnh.le
      _ = (lpWeightConst Kmax lam0 a₀) ^ 2 / ((n : ℝ) * h) := by ring
  rcases le_or_gt 0 σmax2 with hσ | hσneg
  · -- non-degenerate case: bound the variance
    have hMemS : MemLp (fun ω => lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t) 2 P :=
      lp_estimator_memLp hξm hξ2
    have hgoal : (∫⁻ ω, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t
          - ∫ ω', lpEstimator xdat (fun i => f (xdat i) + ξ i ω') K h ℓ t ∂P) ^ 2) ∂P)
        = evariance (fun ω => lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t) P :=
      (evariance_eq_lintegral_ofReal _ _).symm
    rw [hgoal, ← ofReal_variance hMemS]
    refine ENNReal.ofReal_le_ofReal ?_
    have hSsum : (fun ω => lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t)
        = ∑ i : Fin n, (fun ω => (f (xdat i) + ξ i ω) * lpWeight xdat K h ℓ t i) := by
      funext ω; simp only [lpEstimator, Finset.sum_apply]
    rw [hSsum]
    have hmemh : ∀ i, MemLp (fun ω => (f (xdat i) + ξ i ω) * lpWeight xdat K h ℓ t i) 2 P :=
      fun i => ((memLp_const (f (xdat i))).add (lp_xi_memLp i (hξm i) (hξ2 i))).mul_const _
    have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin n)))
        (fun i j => (fun ω => (f (xdat i) + ξ i ω) * lpWeight xdat K h ℓ t i)
          ⟂ᵢ[P] (fun ω => (f (xdat j) + ξ j ω) * lpWeight xdat K h ℓ t j)) := by
      intro i _ j _ hij
      exact (hξi.indepFun hij).comp
        ((measurable_const.add measurable_id).mul_const _)
        ((measurable_const.add measurable_id).mul_const _)
    rw [IndepFun.variance_sum (fun i _ => hmemh i) hpair]
    have hvar_i : ∀ i, variance (fun ω => (f (xdat i) + ξ i ω) * lpWeight xdat K h ℓ t i) P
        ≤ (lpWeight xdat K h ℓ t i) ^ 2 * σmax2 := by
      intro i
      have heq : (fun ω => (f (xdat i) + ξ i ω) * lpWeight xdat K h ℓ t i)
          = (fun ω => ξ i ω * lpWeight xdat K h ℓ t i
              + f (xdat i) * lpWeight xdat K h ℓ t i) := by
        funext ω; ring
      rw [heq, variance_add_const ((hξm i).aestronglyMeasurable.mul_const _) _,
        variance_mul_const]
      have hvξ : variance (ξ i) P ≤ σmax2 := by
        refine (variance_le_expectation_sq (hξm i).aestronglyMeasurable).trans ?_
        simp only [Pi.pow_apply]
        rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _)
          ((hξm i).pow_const 2).aestronglyMeasurable, ← ENNReal.toReal_ofReal hσ]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hξ2 i)
      calc variance (ξ i) P * (lpWeight xdat K h ℓ t i) ^ 2
          ≤ σmax2 * (lpWeight xdat K h ℓ t i) ^ 2 :=
            mul_le_mul_of_nonneg_right hvξ (sq_nonneg _)
        _ = (lpWeight xdat K h ℓ t i) ^ 2 * σmax2 := by ring
    calc ∑ i, variance (fun ω => (f (xdat i) + ξ i ω) * lpWeight xdat K h ℓ t i) P
        ≤ ∑ i, (lpWeight xdat K h ℓ t i) ^ 2 * σmax2 := Finset.sum_le_sum (fun i _ => hvar_i i)
      _ = σmax2 * ∑ i, (lpWeight xdat K h ℓ t i) ^ 2 := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ σmax2 * ((lpWeightConst Kmax lam0 a₀) ^ 2 / ((n : ℝ) * h)) :=
          mul_le_mul_of_nonneg_left hsumsq hσ
      _ = lpVarConst σmax2 Kmax lam0 a₀ / ((n : ℝ) * h) := by rw [lpVarConst]; ring
  · -- degenerate case `σ²_max < 0`: all noise vanishes a.e., so the LHS is `0`
    have hae : ∀ i, ξ i =ᵐ[P] 0 := by
      intro i
      have hz0 : ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P = 0 :=
        le_antisymm (by rw [← ENNReal.ofReal_of_nonpos hσneg.le]; exact hξ2 i) (zero_le)
      have hmz := (lintegral_eq_zero_iff ((hξm i).pow_const 2).ennreal_ofReal).mp hz0
      filter_upwards [hmz] with ω hω
      have h2 : (ξ i ω) ^ 2 = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hω) (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num) |>.mp h2
    have hSae : (fun ω => lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t)
        =ᵐ[P] (fun _ => ∑ i, f (xdat i) * lpWeight xdat K h ℓ t i) := by
      filter_upwards [ae_all_iff.mpr hae] with ω hω
      show lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t
          = ∑ i, f (xdat i) * lpWeight xdat K h ℓ t i
      simp only [lpEstimator]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hω i]; simp
    have hmean : (∫ ω', lpEstimator xdat (fun i => f (xdat i) + ξ i ω') K h ℓ t ∂P)
        = ∑ i, f (xdat i) * lpWeight xdat K h ℓ t i := by
      rw [integral_congr_ae hSae]; simp
    have hint0 : (fun ω => ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t
          - ∫ ω', lpEstimator xdat (fun i => f (xdat i) + ξ i ω') K h ℓ t ∂P) ^ 2)) =ᵐ[P] 0 := by
      filter_upwards [hSae] with ω hω
      rw [hω, hmean]; simp
    calc ∫⁻ ω, ENNReal.ofReal
          ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t
            - ∫ ω', lpEstimator xdat (fun i => f (xdat i) + ξ i ω') K h ℓ t ∂P) ^ 2) ∂P
        = ∫⁻ _ω, (0 : ℝ≥0∞) ∂P := lintegral_congr_ae hint0
      _ = 0 := lintegral_zero
      _ ≤ _ := zero_le

/-- **Pointwise MSE bound of LP(`ℓ`)** over `Σ(β, L)`: bias² + variance,
`E[(f̂(t) − f(t))²] ≤ q₁²·h^{2β} + q₂/(n·h)`. -/
theorem lp_mse_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Fin n → Ω → ℝ} {σmax2 : ℝ} {β L : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hL : 0 ≤ L) (hσ : 0 ≤ σmax2)
    (hn : 0 < n) (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    (hx : ∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1)
    (heig : DesignEigenvalueLB xdat K h (holderIndex β) lam0)
    (hbox : KernelBoxed K Kmax)
    (hdens : DesignDensityBound xdat a₀)
    (hf : MemHolderOn β L f (Set.Icc 0 1))
    (hξm : ∀ i, Measurable (ξ i)) (hξi : iIndepFun ξ P)
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P ≤ ENNReal.ofReal σmax2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫⁻ ω, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t - f t) ^ 2) ∂P
      ≤ ENNReal.ofReal ((lpBiasConst β L Kmax lam0 a₀) ^ 2 * h ^ (2 * β)
          + lpVarConst σmax2 Kmax lam0 a₀ / ((n : ℝ) * h)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hh : 0 < h := lt_of_lt_of_le (div_pos one_pos (mul_pos two_pos hnpos)) hhl
  have hMemS : MemLp (fun ω => lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h
      (holderIndex β) t) 2 P := lp_estimator_memLp hξm hξ2
  -- bias–variance split
  have hdecomp : ∫⁻ ω, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t - f t) ^ 2) ∂P
      = ENNReal.ofReal (((∫ ω, lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h
            (holderIndex β) t ∂P) - f t) ^ 2)
        + ∫⁻ ω, ENNReal.ofReal
            ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t
              - ∫ ω', lpEstimator xdat (fun i => f (xdat i) + ξ i ω') K h (holderIndex β) t ∂P)
              ^ 2) ∂P :=
    mse_decomp hMemS (f t)
  rw [hdecomp, ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hh.le _))
    (div_nonneg (by rw [lpVarConst]; positivity) (mul_pos hnpos hh).le)]
  refine add_le_add ?_ ?_
  · -- bias² bound
    have hint : ∀ i, Integrable
        (fun ω => (f (xdat i) + ξ i ω) * lpWeight xdat K h (holderIndex β) t i) P :=
      fun i => (((memLp_const (f (xdat i))).add (lp_xi_memLp i (hξm i) (hξ2 i))).mul_const
        _).integrable (by norm_num)
    have hmeanA : (∫ ω, lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t ∂P)
        = ∑ i, f (xdat i) * lpWeight xdat K h (holderIndex β) t i := by
      calc (∫ ω, lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t ∂P)
          = ∫ ω, ∑ i, (f (xdat i) + ξ i ω) * lpWeight xdat K h (holderIndex β) t i ∂P := by
            simp only [lpEstimator]
        _ = ∑ i, ∫ ω, (f (xdat i) + ξ i ω) * lpWeight xdat K h (holderIndex β) t i ∂P :=
            integral_finset_sum _ (fun i _ => hint i)
        _ = ∑ i, f (xdat i) * lpWeight xdat K h (holderIndex β) t i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [show (fun ω => (f (xdat i) + ξ i ω) * lpWeight xdat K h (holderIndex β) t i)
                = (fun ω => f (xdat i) * lpWeight xdat K h (holderIndex β) t i
                    + ξ i ω * lpWeight xdat K h (holderIndex β) t i) from funext fun ω => by ring,
              integral_add (integrable_const _)
                (((lp_xi_memLp i (hξm i) (hξ2 i)).integrable (by norm_num)).mul_const _),
              integral_const, integral_mul_const, hξ0 i, zero_mul, add_zero]
            simp
    have hbias := lp_bias_deterministic hβ hL hn hhl hlam ha₀ hx heig hbox hdens hf ht
    have hpow : (lpBiasConst β L Kmax lam0 a₀ * h ^ β) ^ 2
        = (lpBiasConst β L Kmax lam0 a₀) ^ 2 * h ^ (2 * β) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast (h ^ β) 2, ← Real.rpow_mul hh.le]
      congr 1; push_cast; ring
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hmeanA, ← hpow]
    exact sq_le_sq' (abs_le.mp hbias).1 (abs_le.mp hbias).2
  · -- variance bound
    exact lp_variance_le hn hhl hlam ha₀ heig hbox hdens hξm hξi hξ0 hξ2 ht

/-- **Pointwise rate of LP(`ℓ`) over `Σ(β, L)`**: with the bandwidth
`h = α·n^{−1/(2β+1)}`, uniformly over `t ∈ [0,1]` and `f ∈ Σ(β, L)`,
`E[(f̂(t) − f(t))²] ≤ lpRateConst·n^{−2β/(2β+1)}` — the constant is fully explicit. -/
theorem lp_pointwise_rate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Fin n → Ω → ℝ} {σmax2 : ℝ} {β L α : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hL : 0 ≤ L) (hα : 0 < α) (hσ : 0 ≤ σmax2)
    (hn : 0 < n)
    -- LEAN-ONLY: the bandwidth is the rate-optimal tuning; packaged as an equation so all
    -- design hypotheses are stated at this bandwidth
    (hform : h = α * (n : ℝ) ^ (-(1 / (2 * β + 1))))
    -- LEAN-ONLY: side condition `h ≥ 1/(2n)`, satisfied for all large `n`
    (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    (hx : ∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1)
    (heig : DesignEigenvalueLB xdat K h (holderIndex β) lam0)
    (hbox : KernelBoxed K Kmax)
    (hdens : DesignDensityBound xdat a₀)
    (hf : MemHolderOn β L f (Set.Icc 0 1))
    (hξm : ∀ i, Measurable (ξ i)) (hξi : iIndepFun ξ P)
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P ≤ ENNReal.ofReal σmax2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫⁻ ω, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t - f t) ^ 2) ∂P
      ≤ ENNReal.ofReal (lpRateConst β L α σmax2 Kmax lam0 a₀
          * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hp : (0 : ℝ) < 2 * β + 1 := by linarith
  have hpne : (2 * β + 1 : ℝ) ≠ 0 := ne_of_gt hp
  -- the substituted bandwidth turns the MSE bound into the rate constant exactly
  have hval : (lpBiasConst β L Kmax lam0 a₀) ^ 2 * h ^ (2 * β)
        + lpVarConst σmax2 Kmax lam0 a₀ / ((n : ℝ) * h)
      = lpRateConst β L α σmax2 Kmax lam0 a₀ * (n : ℝ) ^ (-(2 * β / (2 * β + 1))) := by
    have hh2b : h ^ (2 * β) = α ^ (2 * β) * (n : ℝ) ^ (-(2 * β / (2 * β + 1))) := by
      rw [hform, Real.mul_rpow hα.le (Real.rpow_nonneg hnpos.le _), ← Real.rpow_mul hnpos.le,
        show (-(1 / (2 * β + 1))) * (2 * β) = -(2 * β / (2 * β + 1)) from by ring]
    have hnh_eq : (n : ℝ) * h = α * (n : ℝ) ^ (2 * β / (2 * β + 1)) := by
      rw [hform,
        show (n : ℝ) * (α * (n : ℝ) ^ (-(1 / (2 * β + 1))))
            = α * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 / (2 * β + 1)))) from by
          rw [Real.rpow_one]; ring,
        ← Real.rpow_add hnpos,
        show (1 : ℝ) + -(1 / (2 * β + 1)) = 2 * β / (2 * β + 1) from by field_simp; ring]
    have hXpos : (0 : ℝ) < (n : ℝ) ^ (2 * β / (2 * β + 1)) := Real.rpow_pos_of_pos hnpos _
    have hnh_val : lpVarConst σmax2 Kmax lam0 a₀ / ((n : ℝ) * h)
        = lpVarConst σmax2 Kmax lam0 a₀ / α * (n : ℝ) ^ (-(2 * β / (2 * β + 1))) := by
      rw [hnh_eq, Real.rpow_neg hnpos.le]
      field_simp
    rw [lpRateConst, hh2b, hnh_val]; ring
  calc ∫⁻ ω, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t - f t) ^ 2) ∂P
      ≤ ENNReal.ofReal ((lpBiasConst β L Kmax lam0 a₀) ^ 2 * h ^ (2 * β)
          + lpVarConst σmax2 Kmax lam0 a₀ / ((n : ℝ) * h)) :=
        lp_mse_le hβ hL hσ hn hhl hlam ha₀ hx heig hbox hdens hf hξm hξi hξ0 hξ2 ht
    _ = ENNReal.ofReal (lpRateConst β L α σmax2 Kmax lam0 a₀
          * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))) := by rw [hval]

end StatLean.NonparametricStatistics
