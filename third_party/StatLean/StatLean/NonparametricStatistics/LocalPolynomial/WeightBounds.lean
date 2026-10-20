module
public import StatLean.NonparametricStatistics.LocalPolynomial.Quadratic
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Bounds on local polynomial weights

Under the standing assumptions (eigenvalue lower bound, design density bound, boxed kernel)
and `h ≥ 1/(2n)`, the LP(`ℓ`) weights satisfy, uniformly over `t ∈ [0,1]`:

* `|W*ᵢ(t)| ≤ C*/(n·h)`;
* `∑ i, |W*ᵢ(t)| ≤ C*`;
* `W*ᵢ(t) = 0` whenever `|xdat i − t| > h`,

with the explicit constant `C* = lpWeightConst Kmax lam0 a₀ = max{2K_max/λ₀, 4K_max·a₀/λ₀}`.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.6.1, Lemma 1.3 (bounds on the LP weights,
constant $C_* = \max\{2K_{\max}/\lambda_0,\ 4K_{\max}a_0/\lambda_0\}$).

**Proof formalization notes.** (iii) is immediate from the kernel's support. For (i):
`|W*ᵢ| ≤ (nh)⁻¹·‖B⁻¹U(zᵢ)K(zᵢ)‖ ≤ (nh)⁻¹·K_max·‖U(zᵢ)‖/λ₀` by the inverse bound
(`lpMatrix_inv_mulVec_sq_le`); on `|z| ≤ 1`, `‖U(z)‖² = ∑ (z^k/k!)² ≤ ∑ 1/k! ≤ e ≤ 4`
(`lpBasis_normSq_le`), so `‖U(zᵢ)‖ ≤ 2`. For (ii), sum (i) over the at most
`n·a₀·max(2h, 1/n) = 2a₀·n·h` indices with `|xᵢ − t| ≤ h` (design density bound, using
`h ≥ 1/(2n)` to resolve the max).

**Bibliographic comments.** These weight bounds are the standard technical core of local
polynomial risk analysis; cf. C. J. Stone, *Ann. Statist.* **8** (1980), 1348–1360, and
J. Fan and I. Gijbels, *Local Polynomial Modelling and Its Applications* (1996).
-/

open Matrix

set_option maxHeartbeats 800000

namespace StatLean.NonparametricStatistics

variable {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {h lam0 a₀ Kmax : ℝ} {ℓ : ℕ}

/-- On `|z| ≤ 1` the rescaled monomial basis vector has squared norm at most `e` (hence norm
at most `2`): `∑ k, (z^k/k!)² ≤ e`. -/
theorem lpBasis_normSq_le (ℓ : ℕ) {z : ℝ} (hz : |z| ≤ 1) :
    ∑ k, (lpBasis ℓ z k) ^ 2 ≤ Real.exp 1 := by
  have h1 : ∀ k : Fin (ℓ + 1),
      (lpBasis ℓ z k) ^ 2 ≤ 1 / (Nat.factorial (k : ℕ) : ℝ) := by
    intro k
    rw [lpBasis, div_pow]
    have hk1 : (z ^ (k : ℕ)) ^ 2 ≤ 1 := by
      have hzk : |z ^ (k : ℕ)| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg z) hz
      nlinarith [hzk, sq_abs (z ^ (k : ℕ)), abs_nonneg (z ^ (k : ℕ))]
    have hfac : (1 : ℝ) ≤ (Nat.factorial (k : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hk1, hfac]
  calc ∑ k, (lpBasis ℓ z k) ^ 2
      ≤ ∑ k : Fin (ℓ + 1), (1 : ℝ) / (Nat.factorial (k : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun k _ => h1 k)
    _ = ∑ i ∈ Finset.range (ℓ + 1), (1 : ℝ) / (Nat.factorial i : ℝ) :=
        Fin.sum_univ_eq_sum_range (fun i => (1 : ℝ) / (Nat.factorial i : ℝ)) (ℓ + 1)
    _ ≤ Real.exp 1 := by
        have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (ℓ + 1)
        simpa using this

/-- **Weight vanishing outside the bandwidth window**: `W*ᵢ(t) = 0` when `|xdat i − t| > h`
(boxed kernel, positive bandwidth). -/
theorem lp_weight_eq_zero_of_far
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    {t : ℝ} {i : Fin n} (hfar : h < |xdat i - t|) :
    lpWeight xdat K h ℓ t i = 0 := by
  have hz : 1 < |(xdat i - t) / h| := by
    rw [abs_div, abs_of_pos hh, lt_div_iff₀ hh, one_mul]; exact hfar
  have hK : K ((xdat i - t) / h) = 0 :=
    hbox.2 _ (fun hmem => absurd (abs_le.mpr (Set.mem_Icc.mp hmem)) (not_le.mpr hz))
  simp only [lpWeight, hK, mul_zero]

/-- The tight per-index weight bound on the bandwidth window (`|z| ≤ 1`):
`|W*ᵢ(t)| ≤ (2K_max/λ₀)/(nh)`. -/
private lemma lpWeight_abs_le_tight (hn : 0 < n) (hh : 0 < h) (hlam : 0 < lam0)
    (heig : DesignEigenvalueLB xdat K h ℓ lam0) (hbox : KernelBoxed K Kmax)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin n)
    (hz : |(xdat i - t) / h| ≤ 1) :
    |lpWeight xdat K h ℓ t i| ≤ (2 * Kmax / lam0) / ((n : ℝ) * h) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnh : (0 : ℝ) < (n : ℝ) * h := mul_pos hnpos hh
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hw0 : |(lpMatrix xdat K h ℓ t)⁻¹.mulVec (lpBasis ℓ ((xdat i - t) / h)) 0|
      ≤ 2 / lam0 := by
    set U := lpBasis ℓ ((xdat i - t) / h) with hU
    set w := (lpMatrix xdat K h ℓ t)⁻¹.mulVec U with hw
    have hsum : ∑ k, (w k) ^ 2 ≤ (∑ k, (U k) ^ 2) / lam0 ^ 2 :=
      lpMatrix_inv_mulVec_sq_le hlam (heig t ht) U
    have hUnorm : ∑ k, (U k) ^ 2 ≤ Real.exp 1 := lpBasis_normSq_le ℓ hz
    have hw0sq : (w 0) ^ 2 ≤ Real.exp 1 / lam0 ^ 2 := by
      calc (w 0) ^ 2 ≤ ∑ k, (w k) ^ 2 :=
            Finset.single_le_sum (fun k _ => sq_nonneg (w k)) (Finset.mem_univ 0)
        _ ≤ (∑ k, (U k) ^ 2) / lam0 ^ 2 := hsum
        _ ≤ Real.exp 1 / lam0 ^ 2 := by gcongr
    have hb : (0 : ℝ) ≤ 2 / lam0 := by positivity
    have hsq2 : (w 0) ^ 2 ≤ (2 / lam0) ^ 2 := by
      have he4 : Real.exp 1 ≤ 4 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      calc (w 0) ^ 2 ≤ Real.exp 1 / lam0 ^ 2 := hw0sq
        _ ≤ 4 / lam0 ^ 2 := by gcongr
        _ = (2 / lam0) ^ 2 := by rw [div_pow]; norm_num
    calc |w 0| = Real.sqrt ((w 0) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((2 / lam0) ^ 2) := Real.sqrt_le_sqrt hsq2
      _ = 2 / lam0 := Real.sqrt_sq hb
  have hnhinv : (0 : ℝ) ≤ ((n : ℝ) * h)⁻¹ := le_of_lt (inv_pos.mpr hnh)
  have h2lam : (0 : ℝ) ≤ 2 / lam0 := by positivity
  simp only [lpWeight]
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hnh)]
  have hlam' : lam0 ≠ 0 := hlam.ne'
  have hnh' : (n : ℝ) * h ≠ 0 := hnh.ne'
  calc ((n : ℝ) * h)⁻¹ * |(lpMatrix xdat K h ℓ t)⁻¹.mulVec (lpBasis ℓ ((xdat i - t) / h)) 0|
        * |K ((xdat i - t) / h)|
      ≤ ((n : ℝ) * h)⁻¹ * (2 / lam0) * Kmax := by
        apply mul_le_mul _ (hbox.1 _) (abs_nonneg _) (mul_nonneg hnhinv h2lam)
        exact mul_le_mul_of_nonneg_left hw0 hnhinv
    _ = (2 * Kmax / lam0) / ((n : ℝ) * h) := by field_simp

/-- **Sup-norm weight bound**: `|W*ᵢ(t)| ≤ C*/(n·h)` uniformly over `t ∈ [0,1]` and `i`. -/
theorem lp_weight_abs_le
    -- LEAN-ONLY: nonempty sample and positive bandwidth; standard side conditions
    (hn : 0 < n) (hh : 0 < h)
    -- USER-INPUT: positive eigenvalue floor; standing design assumption
    (hlam : 0 < lam0)
    -- USER-INPUT: nonnegative density constant; standing design assumption
    (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: eigenvalue lower bound on the local design matrix; standing assumption
    (heig : DesignEigenvalueLB xdat K h ℓ lam0)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    |lpWeight xdat K h ℓ t i| ≤ lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnh : (0 : ℝ) < (n : ℝ) * h := mul_pos hnpos hh
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  rcases le_or_gt |(xdat i - t) / h| 1 with hz | hz
  · calc |lpWeight xdat K h ℓ t i|
        ≤ (2 * Kmax / lam0) / ((n : ℝ) * h) :=
          lpWeight_abs_le_tight hn hh hlam heig hbox ht i hz
      _ = (2 * Kmax / lam0) * ((n : ℝ) * h)⁻¹ := div_eq_mul_inv _ _
      _ ≤ lpWeightConst Kmax lam0 a₀ * ((n : ℝ) * h)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt (inv_pos.mpr hnh))
      _ = lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) := (div_eq_mul_inv _ _).symm
  · have hfar : h < |xdat i - t| := by
      rw [abs_div, abs_of_pos hh, lt_div_iff₀ hh, one_mul] at hz; exact hz
    rw [lp_weight_eq_zero_of_far hh hbox hfar, abs_zero]
    apply div_nonneg _ (le_of_lt hnh)
    exact le_max_of_le_left (div_nonneg (mul_nonneg (by norm_num) hKmax) hlam.le)

/-- **ℓ¹ weight bound**: `∑ i, |W*ᵢ(t)| ≤ C*` uniformly over `t ∈ [0,1]`, provided
`h ≥ 1/(2n)`. -/
theorem lp_weight_sum_abs_le
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
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i, |lpWeight xdat K h ℓ t i| ≤ lpWeightConst Kmax lam0 a₀ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hh : 0 < h := lt_of_lt_of_le (div_pos one_pos (mul_pos two_pos hnpos)) hhl
  have hnh : (0 : ℝ) < (n : ℝ) * h := mul_pos hnpos hh
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hconst : (0 : ℝ) ≤ 2 * Kmax / lam0 := div_nonneg (mul_nonneg (by norm_num) hKmax) hlam.le
  have hcoef : (0 : ℝ) ≤ (2 * Kmax / lam0) / ((n : ℝ) * h) := div_nonneg hconst (le_of_lt hnh)
  -- per-index bound weighted by the window indicator
  have perterm : ∀ i, |lpWeight xdat K h ℓ t i|
      ≤ (2 * Kmax / lam0) / ((n : ℝ) * h)
        * (Set.Icc (t - h) (t + h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by
    intro i
    rcases le_or_gt |(xdat i - t) / h| 1 with hz | hz
    · have hmem : xdat i ∈ Set.Icc (t - h) (t + h) := by
        rw [abs_div, abs_of_pos hh, div_le_one hh, abs_le] at hz
        rw [Set.mem_Icc]; constructor <;> linarith [hz.1, hz.2]
      simp only [Set.indicator_of_mem hmem, mul_one]
      exact lpWeight_abs_le_tight hn hh hlam heig hbox ht i hz
    · have hfar : h < |xdat i - t| := by
        rw [abs_div, abs_of_pos hh, lt_div_iff₀ hh, one_mul] at hz; exact hz
      rw [lp_weight_eq_zero_of_far hh hbox hfar, abs_zero]
      exact mul_nonneg hcoef (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  -- resolve the design-density max to `2h`
  have hkey : (1 : ℝ) ≤ 2 * (n : ℝ) * h := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))] at hhl
    nlinarith [hhl]
  have hmax : max (t + h - (t - h)) ((n : ℝ)⁻¹) = t + h - (t - h) := by
    apply max_eq_left
    rw [show t + h - (t - h) = 2 * h by ring, inv_eq_one_div, div_le_iff₀ hnpos]
    nlinarith [hkey]
  have hSbound : ∑ i, (Set.Icc (t - h) (t + h)).indicator (fun _ => (1 : ℝ)) (xdat i)
      ≤ a₀ * (2 * h) * (n : ℝ) := by
    have hd := hdens (t - h) (t + h) (by linarith)
    rw [hmax, show t + h - (t - h) = 2 * h by ring, ← div_eq_inv_mul,
      div_le_iff₀ hnpos] at hd
    exact hd
  calc ∑ i, |lpWeight xdat K h ℓ t i|
      ≤ ∑ i, (2 * Kmax / lam0) / ((n : ℝ) * h)
          * (Set.Icc (t - h) (t + h)).indicator (fun _ => (1 : ℝ)) (xdat i) :=
        Finset.sum_le_sum (fun i _ => perterm i)
    _ = (2 * Kmax / lam0) / ((n : ℝ) * h)
          * ∑ i, (Set.Icc (t - h) (t + h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by
        rw [Finset.mul_sum]
    _ ≤ (2 * Kmax / lam0) / ((n : ℝ) * h) * (a₀ * (2 * h) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hSbound hcoef
    _ = 4 * Kmax * a₀ / lam0 := by field_simp; ring
    _ ≤ lpWeightConst Kmax lam0 a₀ := le_max_right _ _

end StatLean.NonparametricStatistics
