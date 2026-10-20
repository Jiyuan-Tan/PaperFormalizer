module
public import StatLean.NonparametricStatistics.LocalPolynomial.WeightBounds

@[expose] public section

/-!
# Lipschitz control of local polynomial weights in the evaluation point

For a Lipschitz boxed kernel, the total variation of the weight vector between two evaluation
points is controlled:
$$ \sum_i \bigl|W^*_i(t) - W^*_i(t')\bigr| \;\le\; C_L\,\frac{|t - t'|}{h^3},
   \qquad t, t' \in [0,1], $$
with `C_L = C_L(ℓ, K_max, λ₀, a₀, L_K)`. This is the grid-to-continuum step of the sup-norm
analysis: on a grid of mesh `n^{-4}` the increment is `O(n^{-4}/h³) = O(n^{-1})`.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.6.2 (Lipschitz increments of the LP weight
sums, for the discretization step of Theorem 1.8).

**Proof formalization notes.** Write the weight difference through the resolvent identity
`B_t⁻¹ − B_{t'}⁻¹ = B_t⁻¹(B_{t'} − B_t)B_{t'}⁻¹`. Each ingredient is Lipschitz in `t` with
constants polynomial in `1/h`: `‖U(zᵢ)K(zᵢ) − U(z'ᵢ)K(z'ᵢ)‖ ≤ C·|t−t'|/h` (Lipschitz kernel,
bounded basis on the support), `‖B_t − B_{t'}‖ ≤ C·|t−t'|/h` (design density bound controls
the number of active summands), and `‖B⁻¹‖ ≤ 1/λ₀`. Both `t, t'` count on the union of the
two bandwidth windows, of cardinality `≤ 4a₀nh`. The generous `h⁻³` absorbs all bookkeeping
(only upper bounds are needed; `h ≤ 1`).

**Bibliographic comments.** Standard chaining/discretization bookkeeping; folklore.
-/

open Matrix

namespace StatLean.NonparametricStatistics

/-- Basis-vector norm bound on `|z| ≤ 2`: `∑ k, (lpBasis ℓ z k)² ≤ (ℓ+1)·4^ℓ`. -/
private lemma lpBasis_normSq_le_two {ℓ : ℕ} {z : ℝ} (hz : |z| ≤ 2) :
    ∑ k, (lpBasis ℓ z k) ^ 2 ≤ ((ℓ : ℝ) + 1) * 4 ^ ℓ := by
  have hterm : ∀ k : Fin (ℓ + 1), (lpBasis ℓ z k) ^ 2 ≤ (4 : ℝ) ^ ℓ := by
    intro k
    rw [lpBasis, div_pow]
    have hzk : |z ^ (k : ℕ)| ≤ 2 ^ (k : ℕ) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg z) hz _
    have hk1 : (z ^ (k : ℕ)) ^ 2 ≤ 4 ^ ℓ := by
      have h2k : (2 : ℝ) ^ (k : ℕ) ≤ 2 ^ ℓ :=
        pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp k.isLt)
      have : (z ^ (k : ℕ)) ^ 2 ≤ (2 ^ (k : ℕ)) ^ 2 := by
        nlinarith [hzk, sq_abs (z ^ (k : ℕ)), abs_nonneg (z ^ (k : ℕ)),
          pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) (k:ℕ)]
      calc (z ^ (k : ℕ)) ^ 2 ≤ (2 ^ (k : ℕ)) ^ 2 := this
        _ = (4 : ℝ) ^ (k : ℕ) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ (4 : ℝ) ^ ℓ := pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp k.isLt)

    have hfac : (1 : ℝ) ≤ (Nat.factorial (k : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [div_le_iff₀ (by positivity)]
    have hfsq : (1 : ℝ) ≤ ((Nat.factorial (k : ℕ) : ℝ)) ^ 2 := by nlinarith [hfac]
    nlinarith [hk1, hfsq, pow_nonneg (show (0:ℝ) ≤ 4 by norm_num) ℓ]
  calc ∑ k, (lpBasis ℓ z k) ^ 2
      ≤ ∑ _k : Fin (ℓ + 1), (4 : ℝ) ^ ℓ := Finset.sum_le_sum (fun k _ => hterm k)
    _ = ((ℓ : ℝ) + 1) * 4 ^ ℓ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring

/-- Per-coordinate Lipschitz bound of the basis difference on `|z|,|z'| ≤ 2`:
`|z^k - z'^k| ≤ k·2^(k-1)·|z - z'|`, hence `≤ 2^ℓ·|z-z'|`. -/
private lemma abs_pow_sub_le {z z' : ℝ} (hz : |z| ≤ 2) (hz' : |z'| ≤ 2) (k : ℕ) :
    |z ^ k - z' ^ k| ≤ (k : ℝ) * 2 ^ k * |z - z'| := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hstep : z ^ (m + 1) - z' ^ (m + 1)
        = z * (z ^ m - z' ^ m) + z' ^ m * (z - z') := by ring
    have hzm : |z ^ m| ≤ 2 ^ m := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg z) hz _
    have hz'm : |z' ^ m| ≤ 2 ^ m := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg z') hz' _
    calc |z ^ (m + 1) - z' ^ (m + 1)|
        = |z * (z ^ m - z' ^ m) + z' ^ m * (z - z')| := by rw [hstep]
      _ ≤ |z * (z ^ m - z' ^ m)| + |z' ^ m * (z - z')| := abs_add_le _ _
      _ = |z| * |z ^ m - z' ^ m| + |z' ^ m| * |z - z'| := by rw [abs_mul, abs_mul]
      _ ≤ 2 * ((m : ℝ) * 2 ^ m * |z - z'|) + 2 ^ m * |z - z'| := by
          gcongr
      _ ≤ ((m : ℝ) + 1) * 2 ^ (m + 1) * |z - z'| := by
          have := abs_nonneg (z - z'); rw [pow_succ]; nlinarith [this,
            pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) m]
      _ = ((m : ℕ) + 1 : ℝ) * 2 ^ (m + 1) * |z - z'| := by push_cast; ring
      _ = (↑(m + 1) : ℝ) * 2 ^ (m + 1) * |z - z'| := by push_cast; ring

/-- ℓ¹→ℓ² helper: from `∑_k (v k)² ≤ M²` and `M ≥ 0`, `|v 0| ≤ M`. -/
private lemma abs_zero_le_of_sq_sum_le {ℓ : ℕ} (v : Fin (ℓ + 1) → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hsum : ∑ k, (v k) ^ 2 ≤ M ^ 2) : |v 0| ≤ M := by
  have h0 : (v 0) ^ 2 ≤ M ^ 2 :=
    le_trans (Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ 0)) hsum
  calc |v 0| = Real.sqrt ((v 0) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt h0
    _ = M := Real.sqrt_sq hM

/-- Uniform bound on a basis coordinate for `|z| ≤ 2`: `|U_k(z)| ≤ (ℓ+1)·2^ℓ`. -/
private lemma lpBasis_abs_le_two {ℓ : ℕ} {z : ℝ} (hz : |z| ≤ 2) (k : Fin (ℓ + 1)) :
    |lpBasis ℓ z k| ≤ ((ℓ : ℝ) + 1) * 2 ^ ℓ := by
  rw [lpBasis, abs_div]
  have hnum : |z ^ (k : ℕ)| ≤ 2 ^ ℓ := by
    rw [abs_pow]
    calc |z| ^ (k : ℕ) ≤ 2 ^ (k : ℕ) := pow_le_pow_left₀ (abs_nonneg z) hz _
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp k.isLt)
  have hden : (1 : ℝ) ≤ |(Nat.factorial (k : ℕ) : ℝ)| := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [div_le_iff₀ (by positivity)]
  have h1 : |z ^ (k : ℕ)| ≤ 2 ^ ℓ := hnum
  have hle1 : (1:ℝ) ≤ (ℓ:ℝ) + 1 := by have := (Nat.cast_nonneg ℓ : (0:ℝ) ≤ (ℓ:ℝ)); linarith
  have hp : (0:ℝ) ≤ (2:ℝ) ^ ℓ := pow_nonneg (by norm_num) ℓ
  calc |z ^ (k:ℕ)| ≤ 2 ^ ℓ := h1
    _ = 1 * 2 ^ ℓ * 1 := by ring
    _ ≤ ((ℓ:ℝ) + 1) * 2 ^ ℓ * |(Nat.factorial (k : ℕ) : ℝ)| := by
        gcongr

/-- Lipschitz bound on a basis coordinate difference for `|z|,|z'| ≤ 2`:
`|U_k(z) − U_k(z')| ≤ (ℓ+1)·2^ℓ·|z − z'|`. -/
private lemma lpBasis_sub_abs_le_two {ℓ : ℕ} {z z' : ℝ} (hz : |z| ≤ 2) (hz' : |z'| ≤ 2)
    (k : Fin (ℓ + 1)) :
    |lpBasis ℓ z k - lpBasis ℓ z' k| ≤ ((ℓ : ℝ) + 1) * 2 ^ ℓ * |z - z'| := by
  rw [lpBasis, lpBasis, div_sub_div_same, abs_div]
  have hnum := abs_pow_sub_le hz hz' (k : ℕ)
  have hden : (1 : ℝ) ≤ |(Nat.factorial (k : ℕ) : ℝ)| := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk2 : (k : ℝ) * 2 ^ (k : ℕ) ≤ ((ℓ : ℝ) + 1) * 2 ^ ℓ := by
    have h1 : (k : ℝ) ≤ (ℓ : ℝ) + 1 := by
      have := Nat.lt_succ_iff.mp k.isLt; exact_mod_cast Nat.le_succ_of_le this
    have h2 : (2 : ℝ) ^ (k : ℕ) ≤ 2 ^ ℓ :=
      pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp k.isLt)
    have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
    nlinarith [h1, h2, pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) (k:ℕ), (Nat.cast_nonneg ℓ : (0:ℝ) ≤ (ℓ:ℝ))]
  rw [div_le_iff₀ (by positivity)]
  have hle : |z ^ (k:ℕ) - z' ^ (k:ℕ)| ≤ ((ℓ:ℝ) + 1) * 2 ^ ℓ * |z - z'| :=
    le_trans hnum (by nlinarith [hk2, abs_nonneg (z - z')])
  nlinarith [hle, hden, abs_nonneg (z ^ (k:ℕ) - z' ^ (k:ℕ)), abs_nonneg (z - z'),
    mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ (ℓ:ℝ)+1)
      (pow_nonneg (show (0:ℝ)≤2 by norm_num) ℓ)) (abs_nonneg (z - z'))]

/-- Entry expansion of the local design matrix. -/
private lemma lpMatrix_apply {n : ℕ} (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ) (t : ℝ)
    (k j : Fin (ℓ + 1)) :
    lpMatrix xdat K h ℓ t k j = ((n : ℝ) * h)⁻¹ * ∑ i, K ((xdat i - t) / h)
      * (lpBasis ℓ ((xdat i - t) / h) k * lpBasis ℓ ((xdat i - t) / h) j) := by
  simp only [lpMatrix, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Per-summand triple-telescope Lipschitz bound with the union-window indicator. -/
private lemma lpMatrix_summand_le {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ}
    {Kmax LK h : ℝ} {ℓ : ℕ} (hh : 0 < h) (hbox : KernelBoxed K Kmax)
    (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|)
    {t t' : ℝ} (hd : |t - t'| < h) (k j : Fin (ℓ + 1)) (i : Fin n) :
    |K ((xdat i - t') / h) * (lpBasis ℓ ((xdat i - t') / h) k
        * lpBasis ℓ ((xdat i - t') / h) j)
      - K ((xdat i - t) / h) * (lpBasis ℓ ((xdat i - t) / h) k
        * lpBasis ℓ ((xdat i - t) / h) j)|
      ≤ (LK + 2 * Kmax) * (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2 * (|t - t'| / h)
        * (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by
  set B := ((ℓ : ℝ) + 1) * 2 ^ ℓ with hBdef
  have hBpos : (0 : ℝ) ≤ B := by positivity
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hLK : 0 ≤ LK := by
    have hk := hKlip 1 0
    have : |(1:ℝ) - 0| = 1 := by norm_num
    rw [this, mul_one] at hk
    exact le_trans (abs_nonneg _) hk
  set z := (xdat i - t) / h with hz
  set z' := (xdat i - t') / h with hz'
  have hzz' : |z - z'| = |t - t'| / h := by
    rw [hz, hz', div_sub_div_same, abs_div, abs_of_pos hh]
    congr 1; rw [show xdat i - t - (xdat i - t') = t' - t by ring, abs_sub_comm]
  -- if the summand is nonzero, both |z|,|z'| ≤ 2 and x_i in the union window
  by_cases hact : xdat i ∈ Set.Icc (t - 2 * h) (t + 2 * h)
  · rw [Set.indicator_of_mem hact, mul_one]
    -- We bound in all cases assuming |z|,|z'| ≤ 2. Show that.
    -- At least one K ≠ 0 forces both ≤ 2; else summand = 0.
    by_cases hboth : (z ∈ Set.Icc (-1:ℝ) 1) ∨ (z' ∈ Set.Icc (-1:ℝ) 1)
    · have hz2 : |z| ≤ 2 ∧ |z'| ≤ 2 := by
        have hdz : |z - z'| < 1 := by rw [hzz', div_lt_one hh]; exact hd
        rcases hboth with hin | hin
        · have h1 : |z| ≤ 1 := abs_le.mpr (Set.mem_Icc.mp hin)
          refine ⟨le_trans h1 (by norm_num), ?_⟩
          have hdz' : |z' - z| < 1 := by rw [abs_sub_comm]; exact hdz
          calc |z'| = |z' - z + z| := by ring_nf
            _ ≤ |z' - z| + |z| := abs_add_le _ _
            _ ≤ 2 := by linarith [hdz', h1]
        · have h1 : |z'| ≤ 1 := abs_le.mpr (Set.mem_Icc.mp hin)
          refine ⟨?_, le_trans h1 (by norm_num)⟩
          calc |z| = |z - z' + z'| := by ring_nf
            _ ≤ |z - z'| + |z'| := abs_add_le _ _
            _ ≤ 2 := by linarith [hdz, h1]
      obtain ⟨hz2, hz'2⟩ := hz2
      -- triple telescope
      have hUk := lpBasis_abs_le_two hz2 k
      have hUj := lpBasis_abs_le_two hz2 j
      have hUk' := lpBasis_abs_le_two hz'2 k
      have hUj' := lpBasis_abs_le_two hz'2 j
      have hdUk : |lpBasis ℓ z' k - lpBasis ℓ z k| ≤ B * (|t - t'| / h) := by
        have := lpBasis_sub_abs_le_two hz'2 hz2 k
        rw [abs_sub_comm z' z, hzz'] at this; exact this
      have hdUj : |lpBasis ℓ z' j - lpBasis ℓ z j| ≤ B * (|t - t'| / h) := by
        have := lpBasis_sub_abs_le_two hz'2 hz2 j
        rw [abs_sub_comm z' z, hzz'] at this; exact this
      have hdK : |K z' - K z| ≤ LK * (|t - t'| / h) := by
        have hkl := hKlip z' z
        rw [abs_sub_comm z' z, hzz'] at hkl; exact hkl
      -- telescoping identity
      set uk := lpBasis ℓ z k; set uj := lpBasis ℓ z j
      set uk' := lpBasis ℓ z' k; set uj' := lpBasis ℓ z' j
      have htel : K z' * (uk' * uj') - K z * (uk * uj)
          = (K z' - K z) * (uk' * uj') + K z * (uk' - uk) * uj'
            + K z * uk * (uj' - uj) := by ring
      calc |K z' * (uk' * uj') - K z * (uk * uj)|
          = |(K z' - K z) * (uk' * uj') + K z * (uk' - uk) * uj'
              + K z * uk * (uj' - uj)| := by rw [htel]
        _ ≤ |(K z' - K z) * (uk' * uj')| + |K z * (uk' - uk) * uj'|
              + |K z * uk * (uj' - uj)| := by
            refine le_trans (abs_add_le _ _) ?_; gcongr; exact abs_add_le _ _
        _ = |K z' - K z| * (|uk'| * |uj'|) + |K z| * |uk' - uk| * |uj'|
              + |K z| * |uk| * |uj' - uj| := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
        _ ≤ (LK * (|t-t'|/h)) * (B * B) + Kmax * (B * (|t-t'|/h)) * B
              + Kmax * B * (B * (|t-t'|/h)) := by
            have hnn : (0:ℝ) ≤ |t-t'|/h := div_nonneg (abs_nonneg _) hh.le
            gcongr <;> first
              | exact hdK | exact hbox.1 z | exact hUk' | exact hUj' | exact hUk
              | exact hdUk | exact hdUj
        _ = (LK + 2 * Kmax) * B ^ 2 * (|t - t'| / h) := by ring
    · push_neg at hboth
      have hK1 : K z = 0 := hbox.2 z hboth.1
      have hK2 : K z' = 0 := hbox.2 z' hboth.2
      simp only [hK1, hK2, zero_mul, mul_zero, sub_zero, abs_zero]
      positivity
  · -- summand = 0 since both K vanish (x_i not in window)
    rw [Set.indicator_of_notMem hact, mul_zero]
    have hz1 : z ∉ Set.Icc (-1:ℝ) 1 := by
      intro hin
      apply hact
      have : |z| ≤ 1 := abs_le.mpr (Set.mem_Icc.mp hin)
      rw [hz, abs_div, abs_of_pos hh, div_le_one hh] at this
      rw [Set.mem_Icc]; rw [abs_le] at this
      constructor <;> nlinarith [this.1, this.2, hh]
    have hz'1 : z' ∉ Set.Icc (-1:ℝ) 1 := by
      intro hin
      apply hact
      have hb : |z'| ≤ 1 := abs_le.mpr (Set.mem_Icc.mp hin)
      rw [hz', abs_div, abs_of_pos hh, div_le_one hh] at hb
      rw [abs_le] at hb
      have hd' : |t - t'| < h := hd
      rw [Set.mem_Icc]; rw [abs_lt] at hd'
      constructor <;> nlinarith [hb.1, hb.2, hd'.1, hd'.2, hh]
    have hK1 : K z = 0 := hbox.2 z hz1
    have hK2 : K z' = 0 := hbox.2 z' hz'1
    simp only [hK1, hK2, zero_mul, mul_zero, sub_zero, abs_zero, le_refl]

/-- The inverse of the (symmetric) local design matrix is symmetric. -/
private lemma lpMatrix_inv_isSymm {n : ℕ} (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ)
    (t : ℝ) : (lpMatrix xdat K h ℓ t)⁻¹.IsSymm := by
  have hs : (lpMatrix xdat K h ℓ t)ᵀ = lpMatrix xdat K h ℓ t := lpMatrix_isSymm xdat K h ℓ t
  show ((lpMatrix xdat K h ℓ t)⁻¹)ᵀ = (lpMatrix xdat K h ℓ t)⁻¹
  rw [Matrix.transpose_nonsing_inv, hs]

/-- The `0`-th coordinate of `B⁻¹ U` is the dot product with the `0`-th column of `B⁻¹`. -/
private lemma lpMatrix_inv_mulVec_zero {n : ℕ} (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ)
    (t : ℝ) (U : Fin (ℓ + 1) → ℝ) :
    (lpMatrix xdat K h ℓ t)⁻¹.mulVec U 0
      = ∑ k, (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k * U k := by
  have hs : ((lpMatrix xdat K h ℓ t)⁻¹)ᵀ = (lpMatrix xdat K h ℓ t)⁻¹ :=
    lpMatrix_inv_isSymm xdat K h ℓ t
  have hsymm : ∀ k, (lpMatrix xdat K h ℓ t)⁻¹ k 0 = (lpMatrix xdat K h ℓ t)⁻¹ 0 k := by
    intro k
    have := congrFun (congrFun hs 0) k
    simpa [Matrix.transpose_apply] using this
  have hR : ∀ k, (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
      = (lpMatrix xdat K h ℓ t)⁻¹ 0 k := by
    intro k
    have hc : (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
        = (lpMatrix xdat K h ℓ t)⁻¹ k 0 := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq]
    rw [hc, hsymm k]
  simp_rw [hR]
  simp only [Matrix.mulVec, dotProduct]

/-- Squared-ℓ² bound on the `0`-th column of `B⁻¹`: `∑ (B⁻¹ e₀)² ≤ 1/lam0²`. -/
private lemma lp_invE0_normSq_le {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {lam0 h : ℝ} {ℓ : ℕ}
    {t : ℝ} (hlam : 0 < lam0)
    (hLB : ∀ v : Fin (ℓ + 1) → ℝ,
      lam0 * ∑ k, (v k) ^ 2 ≤ ∑ k, v k * (lpMatrix xdat K h ℓ t).mulVec v k) :
    ∑ k, ((lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k) ^ 2 ≤ 1 / lam0 ^ 2 := by
  have hb := lpMatrix_inv_mulVec_sq_le hlam hLB (Pi.single (0 : Fin (ℓ + 1)) 1)
  have he0 : ∑ k, ((Pi.single (0 : Fin (ℓ + 1)) 1 : Fin (ℓ + 1) → ℝ) k) ^ 2 = 1 := by
    rw [Finset.sum_eq_single (0 : Fin (ℓ + 1))]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  rwa [he0] at hb

/-- ℓ¹ bound on the `0`-th column of `B⁻¹`: `∑ |B⁻¹ e₀| ≤ (ℓ+1)/lam0`. -/
private lemma lp_invE0_absSum_le {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {lam0 h : ℝ} {ℓ : ℕ}
    {t : ℝ} (hlam : 0 < lam0)
    (hLB : ∀ v : Fin (ℓ + 1) → ℝ,
      lam0 * ∑ k, (v k) ^ 2 ≤ ∑ k, v k * (lpMatrix xdat K h ℓ t).mulVec v k) :
    ∑ k, |(lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k| ≤ ((ℓ : ℝ) + 1) / lam0 := by
  set g := fun k => (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k with hg
  have hsq : ∑ k, (g k) ^ 2 ≤ 1 / lam0 ^ 2 := lp_invE0_normSq_le hlam hLB
  set S := ∑ k, |g k| with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hMnn : 0 ≤ ((ℓ : ℝ) + 1) / lam0 := by positivity
  have hcs : S ^ 2 ≤ (∑ k, (g k) ^ 2) * ((ℓ : ℝ) + 1) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => |g k|) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
    exact h
  have hle1 : ((ℓ : ℝ) + 1) ≤ ((ℓ : ℝ) + 1) ^ 2 := by
    nlinarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ (ℓ : ℝ))]
  have hS2 : S ^ 2 ≤ (((ℓ : ℝ) + 1) / lam0) ^ 2 := by
    have hstep : (∑ k, (g k) ^ 2) * ((ℓ : ℝ) + 1) ≤ (((ℓ : ℝ) + 1) / lam0) ^ 2 := by
      rw [div_pow]
      have h1 : (∑ k, (g k) ^ 2) * ((ℓ : ℝ) + 1) ≤ (1 / lam0 ^ 2) * ((ℓ : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
      calc (∑ k, (g k) ^ 2) * ((ℓ : ℝ) + 1) ≤ (1 / lam0 ^ 2) * ((ℓ : ℝ) + 1) := h1
        _ = ((ℓ : ℝ) + 1) / lam0 ^ 2 := by ring
        _ ≤ ((ℓ : ℝ) + 1) ^ 2 / lam0 ^ 2 := by gcongr
    exact le_trans hcs hstep
  have h1 := Real.sqrt_le_sqrt hS2
  rwa [Real.sqrt_sq hSnn, Real.sqrt_sq hMnn] at h1

/-- The weight as a dot product with the `0`-th column of `B⁻¹`. -/
private lemma lpWeight_eq_dot {n : ℕ} (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ) (t : ℝ)
    (i : Fin n) :
    lpWeight xdat K h ℓ t i
      = ((n : ℝ) * h)⁻¹ * ∑ k, (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
          * (lpBasis ℓ ((xdat i - t) / h) k * K ((xdat i - t) / h)) := by
  rw [lpWeight, lpMatrix_inv_mulVec_zero]
  rw [show (∑ k, (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
        * (lpBasis ℓ ((xdat i - t) / h) k * K ((xdat i - t) / h)))
      = (∑ k, (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
        * lpBasis ℓ ((xdat i - t) / h) k) * K ((xdat i - t) / h) from by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun k _ => by ring)]
  ring

/-- Design-density count bound on the doubled bandwidth window: `∑ᵢ 1[xᵢ∈[t−2h,t+2h]] ≤ 4a₀hn`. -/
private lemma count_active_le {n : ℕ} {xdat : Fin n → ℝ} {a₀ h : ℝ} (hn : 0 < n) (hh : 0 < h)
    (hhl : 1 / (2 * (n : ℝ)) ≤ h) (hdens : DesignDensityBound xdat a₀) (t : ℝ) :
    ∑ i, (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i)
      ≤ 4 * a₀ * h * (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hd := hdens (t - 2 * h) (t + 2 * h) (by linarith)
  have hinv : (n : ℝ)⁻¹ ≤ 4 * h := by
    have he : (n : ℝ)⁻¹ = 2 * (1 / (2 * (n : ℝ))) := by field_simp
    rw [he]; nlinarith [hhl, hh]
  have hmax : max ((t + 2 * h) - (t - 2 * h)) ((n : ℝ)⁻¹) = (t + 2 * h) - (t - 2 * h) :=
    max_eq_left (by rw [show (t + 2 * h) - (t - 2 * h) = 4 * h by ring]; exact hinv)
  rw [hmax, show (t + 2 * h) - (t - 2 * h) = 4 * h by ring] at hd
  have h2 := mul_le_mul_of_nonneg_left hd hnpos.le
  rw [← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul] at h2
  calc ∑ i, (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i)
      ≤ (n : ℝ) * (a₀ * (4 * h)) := h2
    _ = 4 * a₀ * h * (n : ℝ) := by ring

/-- Entrywise Lipschitz bound of the local design matrix in the evaluation point. -/
private lemma lpMatrix_entry_diff_le {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ}
    {Kmax a₀ LK h : ℝ} {ℓ : ℕ} (hn : 0 < n) (hh : 0 < h) (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    (hbox : KernelBoxed K Kmax) (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|)
    (hdens : DesignDensityBound xdat a₀) {t t' : ℝ} (hd : |t - t'| < h) (k j : Fin (ℓ + 1)) :
    |lpMatrix xdat K h ℓ t' k j - lpMatrix xdat K h ℓ t k j|
      ≤ 4 * a₀ * (LK + 2 * Kmax) * (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2 * (|t - t'| / h) := by
  set B := ((ℓ : ℝ) + 1) * 2 ^ ℓ with hBdef
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hLK : 0 ≤ LK := by
    have hk := hKlip 1 0; rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at hk
    exact le_trans (abs_nonneg _) hk
  have hcoef : (0 : ℝ) ≤ (LK + 2 * Kmax) * B ^ 2 * (|t - t'| / h) := by
    have : (0 : ℝ) ≤ |t - t'| / h := div_nonneg (abs_nonneg _) hh.le
    positivity
  rw [lpMatrix_apply, lpMatrix_apply, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) * h)⁻¹)]
  have hsum : |∑ i, (K ((xdat i - t') / h)
        * (lpBasis ℓ ((xdat i - t') / h) k * lpBasis ℓ ((xdat i - t') / h) j)
      - K ((xdat i - t) / h)
        * (lpBasis ℓ ((xdat i - t) / h) k * lpBasis ℓ ((xdat i - t) / h) j))|
      ≤ (LK + 2 * Kmax) * B ^ 2 * (|t - t'| / h) * (4 * a₀ * h * (n : ℝ)) := by
    calc |∑ i, _| ≤ ∑ i, |_| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (LK + 2 * Kmax) * B ^ 2 * (|t - t'| / h)
            * (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i) :=
          Finset.sum_le_sum (fun i _ => lpMatrix_summand_le hh hbox hKlip hd k j i)
      _ = (LK + 2 * Kmax) * B ^ 2 * (|t - t'| / h)
            * ∑ i, (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by
          rw [← Finset.mul_sum]
      _ ≤ (LK + 2 * Kmax) * B ^ 2 * (|t - t'| / h) * (4 * a₀ * h * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (count_active_le hn hh hhl hdens t) hcoef
  calc ((n : ℝ) * h)⁻¹ * |∑ i, _|
      ≤ ((n : ℝ) * h)⁻¹ * ((LK + 2 * Kmax) * B ^ 2 * (|t - t'| / h) * (4 * a₀ * h * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * a₀ * (LK + 2 * Kmax) * B ^ 2 * (|t - t'| / h) := by
        field_simp

/-- Resolvent identity applied to `e₀`: `A⁻¹e₀ − C⁻¹e₀ = A⁻¹(C − A)C⁻¹e₀`. -/
private lemma resolvent_e0 {ℓ : ℕ} (A C : Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ)
    (hA : IsUnit A.det) (hC : IsUnit C.det) :
    A⁻¹.mulVec (Pi.single 0 1) - C⁻¹.mulVec (Pi.single 0 1)
      = A⁻¹.mulVec ((C - A).mulVec (C⁻¹.mulVec (Pi.single 0 1))) := by
  have hCg : C.mulVec (C⁻¹.mulVec (Pi.single 0 1)) = Pi.single 0 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hC, Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, hCg, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]

/-- Cauchy–Schwarz: `(∑ |vₖ|)² ≤ (ℓ+1)·∑ vₖ²`. -/
private lemma absSum_sq_le {ℓ : ℕ} (v : Fin (ℓ + 1) → ℝ) :
    (∑ k, |v k|) ^ 2 ≤ ((ℓ : ℝ) + 1) * ∑ k, (v k) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => |v k|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  linarith [h, mul_comm (∑ k, (v k) ^ 2) ((ℓ : ℝ) + 1)]

/-- ℓ¹ bound on the difference of the two `0`-columns of the inverse design matrices
(the resolvent/`Δg` term): `∑ₖ |B_t⁻¹e₀ − B_{t'}⁻¹e₀|ₖ ≤ (ℓ+1)²·D/λ₀²·(|t−t'|/h)`,
`D = 4a₀(L_K+2K_max)((ℓ+1)2^ℓ)²`. -/
private lemma lp_gdiff_absSum_le {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ}
    {Kmax lam0 a₀ LK h : ℝ} {ℓ : ℕ} (hn : 0 < n) (hh : 0 < h) (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    (ha₀ : 0 ≤ a₀) (hlam : 0 < lam0) (hbox : KernelBoxed K Kmax)
    (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|) (hdens : DesignDensityBound xdat a₀)
    {t t' : ℝ} (hd : |t - t'| < h)
    (hLBt : ∀ v : Fin (ℓ + 1) → ℝ,
      lam0 * ∑ k, (v k) ^ 2 ≤ ∑ k, v k * (lpMatrix xdat K h ℓ t).mulVec v k)
    (hLBt' : ∀ v : Fin (ℓ + 1) → ℝ,
      lam0 * ∑ k, (v k) ^ 2 ≤ ∑ k, v k * (lpMatrix xdat K h ℓ t').mulVec v k) :
    ∑ k, |(lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
        - (lpMatrix xdat K h ℓ t')⁻¹.mulVec (Pi.single 0 1) k|
      ≤ ((ℓ : ℝ) + 1) ^ 2 * (4 * a₀ * (LK + 2 * Kmax) * (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2)
          / lam0 ^ 2 * (|t - t'| / h) := by
  classical
  set e0 : Fin (ℓ + 1) → ℝ := Pi.single 0 1 with he0
  set Bt := lpMatrix xdat K h ℓ t with hBt
  set Bt' := lpMatrix xdat K h ℓ t' with hBt'
  set d : ℝ := |t - t'| / h with hddef
  set D : ℝ := 4 * a₀ * (LK + 2 * Kmax) * (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2 with hD
  have hlne : lam0 ≠ 0 := hlam.ne'
  have hdnn : 0 ≤ d := div_nonneg (abs_nonneg _) hh.le
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hLK : 0 ≤ LK := by
    have hk := hKlip 1 0; rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at hk
    exact le_trans (abs_nonneg _) hk
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  have hdett : IsUnit Bt.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (lpMatrix_posDef hlam hLBt).isUnit
  have hdett' : IsUnit Bt'.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (lpMatrix_posDef hlam hLBt').isUnit
  set gt' := Bt'⁻¹.mulVec e0 with hgt'
  set w := (Bt' - Bt).mulVec gt' with hw
  have hres : Bt⁻¹.mulVec e0 - Bt'⁻¹.mulVec e0 = Bt⁻¹.mulVec w :=
    resolvent_e0 Bt Bt' hdett hdett'
  have hg' : ∑ j, |gt' j| ≤ ((ℓ : ℝ) + 1) / lam0 := lp_invE0_absSum_le hlam hLBt'
  have hbnd : ∀ k, |w k| ≤ D * d * (((ℓ : ℝ) + 1) / lam0) := by
    intro k
    have hwk : ((Bt' - Bt).mulVec gt') k = ∑ j, (Bt' - Bt) k j * gt' j := rfl
    rw [hw, hwk]
    calc |∑ j, (Bt' - Bt) k j * gt' j|
        ≤ ∑ j, |(Bt' - Bt) k j * gt' j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |(Bt' - Bt) k j| * |gt' j| := by simp_rw [abs_mul]
      _ ≤ ∑ j, (D * d) * |gt' j| := by
          refine Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
          rw [Matrix.sub_apply]
          have hb := lpMatrix_entry_diff_le hn hh hhl hbox hKlip hdens hd k j
          rw [← hD, ← hddef] at hb; exact hb
      _ = (D * d) * ∑ j, |gt' j| := by rw [← Finset.mul_sum]
      _ ≤ (D * d) * (((ℓ : ℝ) + 1) / lam0) := mul_le_mul_of_nonneg_left hg' (by positivity)
      _ = D * d * (((ℓ : ℝ) + 1) / lam0) := by ring
  have hwsq : ∑ k, (w k) ^ 2 ≤ ((ℓ : ℝ) + 1) * (D * d * (((ℓ : ℝ) + 1) / lam0)) ^ 2 := by
    calc ∑ k, (w k) ^ 2
        ≤ ∑ _k : Fin (ℓ + 1), (D * d * (((ℓ : ℝ) + 1) / lam0)) ^ 2 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          rw [← sq_abs (w k)]; exact pow_le_pow_left₀ (abs_nonneg _) (hbnd k) 2
      _ = ((ℓ : ℝ) + 1) * (D * d * (((ℓ : ℝ) + 1) / lam0)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring
  have hΔ : ∀ k, (Bt⁻¹.mulVec e0) k - (Bt'⁻¹.mulVec e0) k = (Bt⁻¹.mulVec w) k := by
    intro k; have := congrFun hres k; rwa [Pi.sub_apply] at this
  set S := ∑ k, |(Bt⁻¹.mulVec e0) k - (Bt'⁻¹.mulVec e0) k| with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hTnn : 0 ≤ ((ℓ : ℝ) + 1) ^ 2 * D / lam0 ^ 2 * d :=
    mul_nonneg (div_nonneg (mul_nonneg (by positivity) hDnn) (by positivity)) hdnn
  have hΔsq : ∑ k, ((Bt⁻¹.mulVec e0) k - (Bt'⁻¹.mulVec e0) k) ^ 2
      ≤ (∑ k, (w k) ^ 2) / lam0 ^ 2 := by
    have hb := lpMatrix_inv_mulVec_sq_le hlam hLBt w
    calc ∑ k, ((Bt⁻¹.mulVec e0) k - (Bt'⁻¹.mulVec e0) k) ^ 2
        = ∑ k, ((Bt⁻¹.mulVec w) k) ^ 2 :=
          Finset.sum_congr rfl (fun k _ => by rw [hΔ k])
      _ ≤ (∑ k, (w k) ^ 2) / lam0 ^ 2 := hb
  have hScs : S ^ 2 ≤ ((ℓ : ℝ) + 1)
      * ∑ k, ((Bt⁻¹.mulVec e0) k - (Bt'⁻¹.mulVec e0) k) ^ 2 :=
    absSum_sq_le (fun k => (Bt⁻¹.mulVec e0) k - (Bt'⁻¹.mulVec e0) k)
  have heq : ((ℓ : ℝ) + 1) * (((ℓ : ℝ) + 1) * (D * d * (((ℓ : ℝ) + 1) / lam0)) ^ 2 / lam0 ^ 2)
      = (((ℓ : ℝ) + 1) ^ 2 * D / lam0 ^ 2 * d) ^ 2 := by field_simp
  have hchain : S ^ 2 ≤ (((ℓ : ℝ) + 1) ^ 2 * D / lam0 ^ 2 * d) ^ 2 := by
    have h1 : S ^ 2 ≤ ((ℓ : ℝ) + 1) * ((∑ k, (w k) ^ 2) / lam0 ^ 2) :=
      le_trans hScs (mul_le_mul_of_nonneg_left hΔsq (by positivity))
    have h2 : ((ℓ : ℝ) + 1) * ((∑ k, (w k) ^ 2) / lam0 ^ 2)
        ≤ ((ℓ : ℝ) + 1)
          * (((ℓ : ℝ) + 1) * (D * d * (((ℓ : ℝ) + 1) / lam0)) ^ 2 / lam0 ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hwsq (by positivity)
    exact le_trans h1 (le_trans h2 (le_of_eq heq))
  have hfin := Real.sqrt_le_sqrt hchain
  rwa [Real.sqrt_sq hSnn, Real.sqrt_sq hTnn] at hfin

/-- Pointwise bound on a basis-times-kernel coordinate, supported in the doubled window. -/
private lemma lpV_abs_le {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {Kmax h : ℝ} {ℓ : ℕ}
    (hh : 0 < h) (hbox : KernelBoxed K Kmax) {t t' : ℝ} (hd : |t - t'| < h) (k : Fin (ℓ + 1))
    (i : Fin n) :
    |K ((xdat i - t') / h) * lpBasis ℓ ((xdat i - t') / h) k|
      ≤ Kmax * (((ℓ : ℝ) + 1) * 2 ^ ℓ)
        * (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by
  set z' := (xdat i - t') / h with hz'
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  by_cases hact : xdat i ∈ Set.Icc (t - 2 * h) (t + 2 * h)
  · rw [Set.indicator_of_mem hact, mul_one]
    by_cases hz'1 : z' ∈ Set.Icc (-1 : ℝ) 1
    · rw [abs_mul]
      have h1 : |z'| ≤ 2 := le_trans (abs_le.mpr (Set.mem_Icc.mp hz'1)) (by norm_num)
      exact mul_le_mul (hbox.1 z') (lpBasis_abs_le_two h1 k) (abs_nonneg _) hKmax
    · rw [hbox.2 z' hz'1, zero_mul, abs_zero]; positivity
  · rw [Set.indicator_of_notMem hact, mul_zero]
    have hz'1 : z' ∉ Set.Icc (-1 : ℝ) 1 := by
      intro hin
      apply hact
      have hb : |z'| ≤ 1 := abs_le.mpr (Set.mem_Icc.mp hin)
      rw [hz', abs_div, abs_of_pos hh, div_le_one hh] at hb
      rw [abs_le] at hb
      have hd' : |t - t'| < h := hd
      rw [Set.mem_Icc]; rw [abs_lt] at hd'
      constructor <;> nlinarith [hb.1, hb.2, hd'.1, hd'.2, hh]
    rw [hbox.2 z' hz'1, zero_mul, abs_zero]

/-- Term I of the weight increment: `∑ᵢ |∑ₖ (B_t⁻¹e₀)ₖ (V_i(t)−V_i(t'))ₖ|`. -/
private lemma lp_termI_sum_le {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {Kmax lam0 a₀ LK h : ℝ}
    {ℓ : ℕ} {t t' : ℝ} (hn : 0 < n) (hh : 0 < h) (hhl : 1 / (2 * (n : ℝ)) ≤ h) (hlam : 0 < lam0)
    (hbox : KernelBoxed K Kmax) (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|)
    (hdens : DesignDensityBound xdat a₀)
    (heigt : ∀ v : Fin (ℓ + 1) → ℝ,
      lam0 * ∑ k, (v k) ^ 2 ≤ ∑ k, v k * (lpMatrix xdat K h ℓ t).mulVec v k)
    (hd : |t - t'| < h) :
    ∑ i, |∑ k, (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
        * (lpBasis ℓ ((xdat i - t) / h) k * K ((xdat i - t) / h)
          - lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h))|
      ≤ ((ℓ : ℝ) + 1) / lam0
          * ((LK + 2 * Kmax) * (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2 * (|t - t'| / h)) * (4 * a₀ * h * n) := by
  set B : ℝ := ((ℓ : ℝ) + 1) * 2 ^ ℓ with hBdef
  set d : ℝ := |t - t'| / h with hddef
  set M : ℝ := (LK + 2 * Kmax) * B ^ 2 * d with hMdef
  set G := (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) with hG
  have hdnn : 0 ≤ d := div_nonneg (abs_nonneg _) hh.le
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hLK : 0 ≤ LK := by
    have hk := hKlip 1 0; rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at hk
    exact le_trans (abs_nonneg _) hk
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hg : ∑ k, |G k| ≤ ((ℓ : ℝ) + 1) / lam0 := by
    rw [hG]; exact lp_invE0_absSum_le hlam heigt
  have hVdiff : ∀ i k, |lpBasis ℓ ((xdat i - t) / h) k * K ((xdat i - t) / h)
        - lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h)|
      ≤ M * (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by
    intro i k
    have hb := lpMatrix_summand_le (xdat := xdat) hh hbox hKlip hd k 0 i
    have h0t : lpBasis ℓ ((xdat i - t) / h) 0 = 1 := by simp [lpBasis]
    have h0t' : lpBasis ℓ ((xdat i - t') / h) 0 = 1 := by simp [lpBasis]
    rw [h0t, h0t', mul_one, mul_one] at hb
    rw [mul_comm (lpBasis ℓ ((xdat i - t) / h) k) (K ((xdat i - t) / h)),
      mul_comm (lpBasis ℓ ((xdat i - t') / h) k) (K ((xdat i - t') / h)), abs_sub_comm]
    exact hb
  calc ∑ i, |∑ k, G k * (lpBasis ℓ ((xdat i - t) / h) k * K ((xdat i - t) / h)
          - lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h))|
      ≤ ∑ i, ((ℓ : ℝ) + 1) / lam0 * M
          * (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        calc |∑ k, G k * (lpBasis ℓ ((xdat i - t) / h) k * K ((xdat i - t) / h)
                - lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h))|
            ≤ ∑ k, |G k * (lpBasis ℓ ((xdat i - t) / h) k * K ((xdat i - t) / h)
                - lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k, |G k| * (M
              * (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i)) := by
              refine Finset.sum_le_sum (fun k _ => ?_)
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hVdiff i k) (abs_nonneg _)
          _ = (∑ k, |G k|) * (M
              * (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i)) := by
              rw [← Finset.sum_mul]
          _ ≤ ((ℓ : ℝ) + 1) / lam0 * (M
              * (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i)) := by
              refine mul_le_mul_of_nonneg_right hg ?_
              exact mul_nonneg hMnn (Set.indicator_nonneg (fun _ _ => by norm_num) _)
          _ = ((ℓ : ℝ) + 1) / lam0 * M
              * (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by ring
    _ = ((ℓ : ℝ) + 1) / lam0 * M
          * ∑ i, (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by
        rw [← Finset.mul_sum]
    _ ≤ ((ℓ : ℝ) + 1) / lam0 * M * (4 * a₀ * h * n) := by
        refine mul_le_mul_of_nonneg_left (count_active_le hn hh hhl hdens t) ?_
        exact mul_nonneg (div_nonneg (by positivity) hlam.le) hMnn
    _ = ((ℓ : ℝ) + 1) / lam0
          * ((LK + 2 * Kmax) * (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2 * (|t - t'| / h)) * (4 * a₀ * h * n) := by
        rw [hMdef]

/-- Term II of the weight increment: `∑ᵢ |∑ₖ (Δg)ₖ V_i(t')ₖ|`, controlled by `∑ₖ|Δg|`. -/
private lemma lp_termII_sum_le {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {Kmax a₀ h : ℝ}
    {ℓ : ℕ} {t t' : ℝ} (hn : 0 < n) (hh : 0 < h) (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    (hbox : KernelBoxed K Kmax) (hdens : DesignDensityBound xdat a₀) (hd : |t - t'| < h) :
    ∑ i, |∑ k, ((lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
        - (lpMatrix xdat K h ℓ t')⁻¹.mulVec (Pi.single 0 1) k)
        * (lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h))|
      ≤ (∑ k, |(lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
          - (lpMatrix xdat K h ℓ t')⁻¹.mulVec (Pi.single 0 1) k|)
        * (Kmax * (((ℓ : ℝ) + 1) * 2 ^ ℓ) * (4 * a₀ * h * n)) := by
  set B : ℝ := ((ℓ : ℝ) + 1) * 2 ^ ℓ with hBdef
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hsupp : ∀ k, ∑ i, |lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h)|
      ≤ Kmax * B * (4 * a₀ * h * n) := by
    intro k
    calc ∑ i, |lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h)|
        ≤ ∑ i, Kmax * B
            * (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [mul_comm (lpBasis ℓ ((xdat i - t') / h) k) (K ((xdat i - t') / h))]
          exact lpV_abs_le hh hbox hd k i
      _ = Kmax * B
            * ∑ i, (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by
          rw [← Finset.mul_sum]
      _ ≤ Kmax * B * (4 * a₀ * h * n) :=
          mul_le_mul_of_nonneg_left (count_active_le hn hh hhl hdens t) (mul_nonneg hKmax hBnn)
  calc ∑ i, |∑ k, ((lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
          - (lpMatrix xdat K h ℓ t')⁻¹.mulVec (Pi.single 0 1) k)
          * (lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h))|
      ≤ ∑ i, ∑ k, |(lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
          - (lpMatrix xdat K h ℓ t')⁻¹.mulVec (Pi.single 0 1) k|
          * |lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h)| := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun k _ => ?_))
        exact (abs_mul _ _).le
    _ = ∑ k, |(lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
          - (lpMatrix xdat K h ℓ t')⁻¹.mulVec (Pi.single 0 1) k|
          * ∑ i, |lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h)| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun k _ => by rw [← Finset.mul_sum])
    _ ≤ ∑ k, |(lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
          - (lpMatrix xdat K h ℓ t')⁻¹.mulVec (Pi.single 0 1) k| * (Kmax * B * (4 * a₀ * h * n)) := by
        refine Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hsupp k) (abs_nonneg _))
    _ = (∑ k, |(lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
          - (lpMatrix xdat K h ℓ t')⁻¹.mulVec (Pi.single 0 1) k|)
          * (Kmax * (((ℓ : ℝ) + 1) * 2 ^ ℓ) * (4 * a₀ * h * n)) := by
        rw [← Finset.sum_mul, hBdef]

/-- Split of the weight increment into the Term I (`Δ`-basis) and Term II (`Δ`-resolvent)
inner sums, scaled by `(nh)⁻¹`. -/
private lemma lp_weight_diff_eq {n : ℕ} (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ)
    (t t' : ℝ) (i : Fin n) :
    lpWeight xdat K h ℓ t i - lpWeight xdat K h ℓ t' i
      = ((n : ℝ) * h)⁻¹
        * ((∑ k, (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
              * (lpBasis ℓ ((xdat i - t) / h) k * K ((xdat i - t) / h)
                - lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h)))
          + (∑ k, ((lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
                - (lpMatrix xdat K h ℓ t')⁻¹.mulVec (Pi.single 0 1) k)
              * (lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h)))) := by
  rw [lpWeight_eq_dot, lpWeight_eq_dot, ← mul_sub]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

set_option maxHeartbeats 1600000 in
/-- **ℓ¹-Lipschitz bound of the weight vector in the evaluation point**: there is
`C_L = C_L(ℓ, K_max, λ₀, a₀, L_K)` with
`∑ i, |W*ᵢ(t) − W*ᵢ(t')| ≤ C_L·|t − t'|/h³` for all `t, t' ∈ [0,1]` under the standing
assumptions. -/
theorem lp_weight_lipschitz_sum {ℓ : ℕ} {K : ℝ → ℝ} {Kmax lam0 a₀ LK : ℝ}
    -- USER-INPUT: positive eigenvalue floor and nonnegative density constant; standing
    -- design assumptions
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: Lipschitz kernel; the sup-norm analysis input
    (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|) :
    ∃ CL : ℝ, 0 < CL ∧
      ∀ {n : ℕ}, 0 < n → ∀ {h : ℝ}, 1 / (2 * (n : ℝ)) ≤ h → h ≤ 1 →
      ∀ {xdat : Fin n → ℝ}, (∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1) →
        DesignEigenvalueLB xdat K h ℓ lam0 → DesignDensityBound xdat a₀ →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        ∑ i, |lpWeight xdat K h ℓ t i - lpWeight xdat K h ℓ t' i|
          ≤ CL * |t - t'| / h ^ 3 := by
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hLK : 0 ≤ LK := by
    have hk := hKlip 1 0; rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at hk
    exact le_trans (abs_nonneg _) hk
  have h4a : (0 : ℝ) ≤ 4 * a₀ := by linarith
  have hLKK : (0 : ℝ) ≤ LK + 2 * Kmax := by linarith
  have hP : (0 : ℝ) ≤ ((ℓ : ℝ) + 1) * 2 ^ ℓ := by positivity
  have hP2 : (0 : ℝ) ≤ (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2 := sq_nonneg _
  have hCstnn : (0 : ℝ) ≤ lpWeightConst Kmax lam0 a₀ := by
    unfold lpWeightConst
    exact le_trans (div_nonneg (mul_nonneg (by norm_num) hKmax) hlam.le) (le_max_left _ _)
  set CI : ℝ := ((ℓ : ℝ) + 1) / lam0 * ((LK + 2 * Kmax) * (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2)
      * (4 * a₀) with hCIdef
  set CII : ℝ := ((ℓ : ℝ) + 1) ^ 2 * (4 * a₀ * (LK + 2 * Kmax) * (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2)
      / lam0 ^ 2 * (Kmax * (((ℓ : ℝ) + 1) * 2 ^ ℓ) * (4 * a₀)) with hCIIdef
  have hCInn : 0 ≤ CI :=
    mul_nonneg (mul_nonneg (div_nonneg (by positivity) hlam.le) (mul_nonneg hLKK hP2)) h4a
  have hCIInn : 0 ≤ CII :=
    mul_nonneg (div_nonneg (mul_nonneg (by positivity)
        (mul_nonneg (mul_nonneg h4a hLKK) hP2)) (by positivity))
      (mul_nonneg (mul_nonneg hKmax hP) h4a)
  refine ⟨2 * lpWeightConst Kmax lam0 a₀ + CI + CII + 1, by linarith, ?_⟩
  intro n hn h hhl hh1 xdat hx heig hdens t ht t' ht'
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hh : 0 < h := lt_of_lt_of_le (div_pos one_pos (mul_pos (by norm_num) hnpos)) hhl
  have hnh : (0 : ℝ) < (n : ℝ) * h := mul_pos hnpos hh
  rcases le_or_gt h (|t - t'|) with hcase | hcase
  · -- crude case: `h ≤ |t − t'|`
    have hsum := lp_weight_sum_abs_le hn hhl hlam ha₀ heig hbox hdens ht
    have hsum' := lp_weight_sum_abs_le hn hhl hlam ha₀ heig hbox hdens ht'
    have hcrude : ∑ i, |lpWeight xdat K h ℓ t i - lpWeight xdat K h ℓ t' i|
        ≤ 2 * lpWeightConst Kmax lam0 a₀ := by
      calc ∑ i, |lpWeight xdat K h ℓ t i - lpWeight xdat K h ℓ t' i|
          ≤ ∑ i, (|lpWeight xdat K h ℓ t i| + |lpWeight xdat K h ℓ t' i|) :=
            Finset.sum_le_sum (fun i _ => by
              rw [sub_eq_add_neg]
              exact le_trans (abs_add_le _ _) (le_of_eq (by rw [abs_neg])))
        _ = ∑ i, |lpWeight xdat K h ℓ t i| + ∑ i, |lpWeight xdat K h ℓ t' i| :=
            Finset.sum_add_distrib
        _ ≤ 2 * lpWeightConst Kmax lam0 a₀ := by linarith
    refine le_trans hcrude ?_
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < h ^ 3)]
    have hh3h : h ^ 3 ≤ h := by
      have := pow_le_pow_of_le_one hh.le hh1 (by norm_num : 1 ≤ 3); simpa using this
    have hh3 : h ^ 3 ≤ |t - t'| := le_trans hh3h hcase
    nlinarith [mul_nonneg hCstnn (sub_nonneg.mpr hh3), mul_nonneg hCInn (abs_nonneg (t - t')),
      mul_nonneg hCIInn (abs_nonneg (t - t')), abs_nonneg (t - t'), hCstnn]
  · -- smooth case: `|t − t'| < h`
    have hPn : (0 : ℝ) ≤ 4 * a₀ * h * (n : ℝ) :=
      mul_nonneg (mul_nonneg h4a hh.le) (Nat.cast_nonneg n)
    have hnn : (0 : ℝ) ≤ Kmax * (((ℓ : ℝ) + 1) * 2 ^ ℓ) * (4 * a₀ * h * (n : ℝ)) :=
      mul_nonneg (mul_nonneg hKmax hP) hPn
    have hTI := lp_termI_sum_le hn hh hhl hlam hbox hKlip hdens (heig t ht) hcase
    have hgdiff := lp_gdiff_absSum_le hn hh hhl ha₀ hlam hbox hKlip hdens hcase
      (heig t ht) (heig t' ht')
    have hTII := le_trans (lp_termII_sum_le hn hh hhl hbox hdens hcase)
      (mul_le_mul_of_nonneg_right hgdiff hnn)
    have hne_n : (n : ℝ) ≠ 0 := hnpos.ne'
    calc ∑ i, |lpWeight xdat K h ℓ t i - lpWeight xdat K h ℓ t' i|
        ≤ ∑ i, ((n : ℝ) * h)⁻¹
            * (|∑ k, (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
                  * (lpBasis ℓ ((xdat i - t) / h) k * K ((xdat i - t) / h)
                    - lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h))|
              + |∑ k, ((lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
                    - (lpMatrix xdat K h ℓ t')⁻¹.mulVec (Pi.single 0 1) k)
                  * (lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h))|) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [lp_weight_diff_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) * h)⁻¹)]
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ = ((n : ℝ) * h)⁻¹
          * ((∑ i, |∑ k, (lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
                * (lpBasis ℓ ((xdat i - t) / h) k * K ((xdat i - t) / h)
                  - lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h))|)
            + ∑ i, |∑ k, ((lpMatrix xdat K h ℓ t)⁻¹.mulVec (Pi.single 0 1) k
                  - (lpMatrix xdat K h ℓ t')⁻¹.mulVec (Pi.single 0 1) k)
                * (lpBasis ℓ ((xdat i - t') / h) k * K ((xdat i - t') / h))|) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ ((n : ℝ) * h)⁻¹
          * (((ℓ : ℝ) + 1) / lam0
              * ((LK + 2 * Kmax) * (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2 * (|t - t'| / h)) * (4 * a₀ * h * n)
            + ((ℓ : ℝ) + 1) ^ 2 * (4 * a₀ * (LK + 2 * Kmax) * (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2)
                / lam0 ^ 2 * (|t - t'| / h)
              * (Kmax * (((ℓ : ℝ) + 1) * 2 ^ ℓ) * (4 * a₀ * h * n))) :=
          mul_le_mul_of_nonneg_left (add_le_add hTI hTII) (by positivity)
      _ = (CI + CII) * (|t - t'| / h) := by
          rw [hCIdef, hCIIdef, mul_add, add_mul]
          congr 1 <;> field_simp
      _ ≤ (2 * lpWeightConst Kmax lam0 a₀ + CI + CII + 1) * |t - t'| / h ^ 3 := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < h ^ 3)]
          have hexp : (CI + CII) * (|t - t'| / h) * h ^ 3 = (CI + CII) * |t - t'| * h ^ 2 := by
            field_simp
          rw [hexp]
          nlinarith [mul_nonneg (mul_nonneg (add_nonneg hCInn hCIInn) (abs_nonneg (t - t')))
              (by nlinarith [hh1, hh.le] : (0 : ℝ) ≤ 1 - h ^ 2),
            mul_nonneg hCstnn (abs_nonneg (t - t')), abs_nonneg (t - t')]

end StatLean.NonparametricStatistics
