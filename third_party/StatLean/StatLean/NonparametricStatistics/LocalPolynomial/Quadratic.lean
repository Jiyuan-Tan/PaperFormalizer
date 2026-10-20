module
public import StatLean.NonparametricStatistics.LocalPolynomial.Defs
public import StatLean.NonparametricStatistics.Regression.Defs
public import Mathlib.LinearAlgebra.Matrix.Symmetric

@[expose] public section

/-!
# The local polynomial estimator as a quadratic minimisation

The exact linear algebra of the LP(`ℓ`) criterion: symmetry and positive definiteness of the
local design matrix, the inverse bound from the eigenvalue hypothesis, normal equations,
uniqueness of the minimiser, agreement of the closed-form weights with the minimiser, and
linearity of the estimator.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.6, Proposition 1.11 (the LP estimator is
linear) with the normal equations (1.66) and the inverse bound (1.70).

**Proof formalization notes.** Expanding the square,
`lpObjective θ = ∑ Yᵢ²Kᵢ − 2·(nh)·⟨θ, a_t⟩ + (nh)·⟨θ, B_t θ⟩`; when `B_t ≻ 0` this strictly
convex quadratic has the unique stationary point `B_t θ = a_t`. `lpEstimator` is by
construction `(B_t⁻¹ a_t)₀`, hence equals `θ 0` for any minimiser `θ`. Positive definiteness
follows from the quadratic-form lower bound at positive `lam0` plus symmetry of `B_t` (a sum
of symmetric rank-one blocks `U Uᵀ`). The inverse bound is the Cauchy–Schwarz chain
`lam0·‖w‖² ≤ ⟨w, B w⟩ ≤ ‖w‖·‖B w‖` applied at `w = B⁻¹ v`.

**Bibliographic comments.** V. Ya. Katkovnik, *Soviet Automat. Control* **5** (1979), 25–34;
C. J. Stone, *Ann. Statist.* **5** (1977), 595–620.
-/

open Matrix

set_option maxHeartbeats 800000

namespace StatLean.NonparametricStatistics

variable {n : ℕ} {xdat Y : Fin n → ℝ} {K : ℝ → ℝ} {h : ℝ} {ℓ : ℕ} {t : ℝ}

/-- The local design matrix is symmetric. -/
theorem lpMatrix_isSymm (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ) (t : ℝ) :
    (lpMatrix xdat K h ℓ t).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [lpMatrix, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun r _ => by ring

/-- Expansion of a matrix-vector product for the local design matrix. -/
lemma lpMatrix_mulVec_apply (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ) (t : ℝ)
    (θ : Fin (ℓ + 1) → ℝ) (j : Fin (ℓ + 1)) :
    (lpMatrix xdat K h ℓ t).mulVec θ j
      = ((n : ℝ) * h)⁻¹ * ∑ i, K ((xdat i - t) / h) * lpBasis ℓ ((xdat i - t) / h) j
          * (∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k) := by
  simp only [lpMatrix, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- A positive uniform quadratic-form lower bound makes the local design matrix positive
definite. -/
theorem lpMatrix_posDef {lam0 : ℝ} (hlam : 0 < lam0)
    (hLB : ∀ v : Fin (ℓ + 1) → ℝ,
      lam0 * ∑ k, (v k) ^ 2 ≤ ∑ k, v k * (lpMatrix xdat K h ℓ t).mulVec v k) :
    (lpMatrix xdat K h ℓ t).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · have hsymm : (lpMatrix xdat K h ℓ t)ᴴ = lpMatrix xdat K h ℓ t := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      exact lpMatrix_isSymm xdat K h ℓ t
    exact hsymm
  · intro x hx
    simp only [dotProduct, Pi.star_apply, star_trivial]
    have hpos : 0 < ∑ k, (x k) ^ 2 := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨k, Finset.mem_univ k, ?_⟩
      exact lt_of_le_of_ne (sq_nonneg _) ((pow_ne_zero 2 hk).symm)
    calc (0 : ℝ) < lam0 * ∑ k, (x k) ^ 2 := mul_pos hlam hpos
      _ ≤ ∑ k, x k * (lpMatrix xdat K h ℓ t).mulVec x k := hLB x

/-- **Inverse bound from the eigenvalue hypothesis** (squared form):
`‖B_t⁻¹ v‖² ≤ ‖v‖²/lam0²`. -/
theorem lpMatrix_inv_mulVec_sq_le {lam0 : ℝ} (hlam : 0 < lam0)
    (hLB : ∀ v : Fin (ℓ + 1) → ℝ,
      lam0 * ∑ k, (v k) ^ 2 ≤ ∑ k, v k * (lpMatrix xdat K h ℓ t).mulVec v k)
    (v : Fin (ℓ + 1) → ℝ) :
    ∑ k, ((lpMatrix xdat K h ℓ t)⁻¹.mulVec v k) ^ 2
      ≤ (∑ k, (v k) ^ 2) / lam0 ^ 2 := by
  set B := lpMatrix xdat K h ℓ t with hB
  set w := B⁻¹.mulVec v with hw
  have hpd : B.PosDef := lpMatrix_posDef hlam hLB
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  have hBw : B.mulVec w = v := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < lam0 ^ 2)]
  have hlb : lam0 * ∑ k, (w k) ^ 2 ≤ ∑ k, w k * v k := by
    have := hLB w
    rwa [hBw] at this
  have hcs : (∑ k, w k * v k) ^ 2 ≤ (∑ k, (w k) ^ 2) * ∑ k, (v k) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w v
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun k _ => sq_nonneg (w k))) with hW | hW
  · rw [← hW, zero_mul]; positivity
  · have hP : 0 < ∑ k, w k * v k := lt_of_lt_of_le (mul_pos hlam hW) hlb
    have hsq : (lam0 * ∑ k, (w k) ^ 2) ^ 2 ≤ (∑ k, w k * v k) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt (mul_pos hlam hW)) hlb 2
    nlinarith [hsq, hcs, hW]

/-- Expansion of `lpObjective` along the coordinate direction `Pi.single j 1`. -/
private lemma lpObjective_add_single (xdat Y : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ) (t : ℝ)
    (θ : Fin (ℓ + 1) → ℝ) (j : Fin (ℓ + 1)) (s : ℝ) :
    lpObjective xdat Y K h ℓ t (θ + s • (Pi.single j (1 : ℝ) : Fin (ℓ + 1) → ℝ))
      = lpObjective xdat Y K h ℓ t θ
        + (∑ i, (lpBasis ℓ ((xdat i - t) / h) j) ^ 2 * K ((xdat i - t) / h)) * s ^ 2
        + (-2 * ∑ i, (Y i - ∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k)
            * lpBasis ℓ ((xdat i - t) / h) j * K ((xdat i - t) / h)) * s := by
  simp only [lpObjective]
  set e := (Pi.single j (1 : ℝ) : Fin (ℓ + 1) → ℝ) with he
  have key : ∀ i, (Y i - ∑ k, (θ + s • e) k * lpBasis ℓ ((xdat i - t) / h) k) ^ 2
        * K ((xdat i - t) / h)
      = (Y i - ∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k) ^ 2 * K ((xdat i - t) / h)
        + (lpBasis ℓ ((xdat i - t) / h) j) ^ 2 * K ((xdat i - t) / h) * s ^ 2
        + -2 * ((Y i - ∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k)
            * lpBasis ℓ ((xdat i - t) / h) j * K ((xdat i - t) / h)) * s := by
    intro i
    have hinner : ∑ k, (θ + s • e) k * lpBasis ℓ ((xdat i - t) / h) k
        = (∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k) + s * lpBasis ℓ ((xdat i - t) / h) j := by
      have hrw : ((θ : Fin (ℓ + 1) → ℝ) + s • e)
          = fun k => θ k + s * (if k = j then 1 else 0) := by
        funext k; simp [he, Pi.single_apply]
      rw [hrw]
      simp only [add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ j (fun k => s * lpBasis ℓ ((xdat i - t) / h) k)]
      simp
    rw [hinner]; ring
  rw [Finset.sum_congr rfl fun i _ => key i]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.mul_sum]

/-- The linear coefficient of a nonnegative-for-all-`s` quadratic in `s` vanishes. -/
private lemma linear_coeff_eq_zero {A b : ℝ} (h : ∀ s : ℝ, 0 ≤ A * s ^ 2 + b * s) : b = 0 := by
  rcases le_or_gt A 0 with hA | hA
  · have h1 := h 1
    have h2 := h (-1)
    norm_num at h1 h2
    linarith
  · have key := h (-b / (2 * A))
    have hne : (4 * A) ≠ 0 := by positivity
    have expand : A * (-b / (2 * A)) ^ 2 + b * (-b / (2 * A)) = -b ^ 2 / (4 * A) := by
      field_simp; ring
    rw [expand] at key
    have h4 : 0 < 4 * A := by linarith
    have hbb : 0 ≤ -b ^ 2 := by
      have := mul_nonneg key (le_of_lt h4)
      rwa [div_mul_cancel₀ _ hne] at this
    nlinarith [sq_nonneg b, hbb]

/-- The `→` direction of the normal equations: a minimiser satisfies `B_t θ = a_t`. This holds
without any sign hypothesis on `nh`. -/
private lemma isLPSolution_imp_normal (hpd : (lpMatrix xdat K h ℓ t).PosDef)
    {θ : Fin (ℓ + 1) → ℝ} (hθ : IsLPSolution xdat Y K h ℓ t θ) :
    (lpMatrix xdat K h ℓ t).mulVec θ = lpRhs xdat Y K h ℓ t := by
  have hnh : (n : ℝ) * h ≠ 0 := by
    intro h0
    have hx : (Pi.single (0 : Fin (ℓ + 1)) (1 : ℝ) : Fin (ℓ + 1) → ℝ) ≠ 0 := by
      intro hcon; simpa using congrFun hcon 0
    have hpos := hpd.dotProduct_mulVec_pos hx
    rw [show lpMatrix xdat K h ℓ t = 0 from by simp [lpMatrix, h0]] at hpos
    simp [Matrix.zero_mulVec] at hpos
  funext j
  have hquad : ∀ s : ℝ,
      0 ≤ (∑ i, (lpBasis ℓ ((xdat i - t) / h) j) ^ 2 * K ((xdat i - t) / h)) * s ^ 2
      + (-2 * ∑ i, (Y i - ∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k)
          * lpBasis ℓ ((xdat i - t) / h) j * K ((xdat i - t) / h)) * s := by
    intro s
    have hle := hθ (θ + s • (Pi.single j (1 : ℝ) : Fin (ℓ + 1) → ℝ))
    rw [lpObjective_add_single] at hle
    linarith
  have hb := linear_coeff_eq_zero hquad
  have hsum0 : ∑ i, (Y i - ∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k)
      * lpBasis ℓ ((xdat i - t) / h) j * K ((xdat i - t) / h) = 0 := by
    linarith
  have hexp : ∑ i, (Y i - ∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k)
        * lpBasis ℓ ((xdat i - t) / h) j * K ((xdat i - t) / h)
      = (n : ℝ) * h * lpRhs xdat Y K h ℓ t j
        - (n : ℝ) * h * (lpMatrix xdat K h ℓ t).mulVec θ j := by
    rw [lpMatrix_mulVec_apply]
    simp only [lpRhs]
    rw [mul_inv_cancel_left₀ hnh, mul_inv_cancel_left₀ hnh, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum0] at hexp
  have : (n : ℝ) * h * lpRhs xdat Y K h ℓ t j
      = (n : ℝ) * h * (lpMatrix xdat K h ℓ t).mulVec θ j := by linarith
  exact (mul_left_cancel₀ hnh this).symm

/-- Objective-difference identity used for the `←` direction of the normal equations. For all
`θ θ'`, writing `Δ := θ' − θ`, the objective gap decomposes into a quadratic form plus a
gradient term. Needs only `(n·h) ≠ 0`. -/
private lemma lpObjective_diff (xdat Y : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ) (t : ℝ)
    (hnh : (n : ℝ) * h ≠ 0) (θ θ' : Fin (ℓ + 1) → ℝ) :
    lpObjective xdat Y K h ℓ t θ' - lpObjective xdat Y K h ℓ t θ
      = (n : ℝ) * h * (∑ j, (θ' - θ) j * (lpMatrix xdat K h ℓ t).mulVec (θ' - θ) j)
        + 2 * ((n : ℝ) * h) * (∑ j, (θ' - θ) j
            * ((lpMatrix xdat K h ℓ t).mulVec θ - lpRhs xdat Y K h ℓ t) j) := by
  have hM : ∀ w : Fin (ℓ + 1) → ℝ,
      (n : ℝ) * h * (∑ j, (θ' - θ) j * (lpMatrix xdat K h ℓ t).mulVec w j)
        = ∑ i, (∑ k, (θ' - θ) k * lpBasis ℓ ((xdat i - t) / h) k)
            * (∑ k, w k * lpBasis ℓ ((xdat i - t) / h) k) * K ((xdat i - t) / h) := by
    intro w
    simp only [lpMatrix_mulVec_apply]
    rw [Finset.mul_sum, Finset.sum_congr rfl fun j _ => by
      rw [mul_left_comm, mul_inv_cancel_left₀ hnh, Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    trans (∑ j, (θ' - θ) j * lpBasis ℓ ((xdat i - t) / h) j)
        * (K ((xdat i - t) / h) * (∑ k, w k * lpBasis ℓ ((xdat i - t) / h) k))
    · rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    · ring
  have hA : (n : ℝ) * h * (∑ j, (θ' - θ) j * lpRhs xdat Y K h ℓ t j)
      = ∑ i, (∑ k, (θ' - θ) k * lpBasis ℓ ((xdat i - t) / h) k)
          * Y i * K ((xdat i - t) / h) := by
    simp only [lpRhs]
    rw [Finset.mul_sum, Finset.sum_congr rfl fun j _ => by
      rw [mul_left_comm, mul_inv_cancel_left₀ hnh, Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    trans (∑ j, (θ' - θ) j * lpBasis ℓ ((xdat i - t) / h) j)
        * (Y i * K ((xdat i - t) / h))
    · rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    · ring
  have hobj : lpObjective xdat Y K h ℓ t θ' - lpObjective xdat Y K h ℓ t θ
      = ∑ i, ((∑ k, (θ' - θ) k * lpBasis ℓ ((xdat i - t) / h) k) ^ 2
          - 2 * (Y i - ∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k)
              * (∑ k, (θ' - θ) k * lpBasis ℓ ((xdat i - t) / h) k))
          * K ((xdat i - t) / h) := by
    simp only [lpObjective]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hΔ : ∑ k, (θ' - θ) k * lpBasis ℓ ((xdat i - t) / h) k
        = (∑ k, θ' k * lpBasis ℓ ((xdat i - t) / h) k)
          - ∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k := by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [hΔ]; ring
  have hcross : (n : ℝ) * h
      * (∑ j, (θ' - θ) j * ((lpMatrix xdat K h ℓ t).mulVec θ - lpRhs xdat Y K h ℓ t) j)
      = (∑ i, (∑ k, (θ' - θ) k * lpBasis ℓ ((xdat i - t) / h) k)
            * (∑ k, θ k * lpBasis ℓ ((xdat i - t) / h) k) * K ((xdat i - t) / h))
        - ∑ i, (∑ k, (θ' - θ) k * lpBasis ℓ ((xdat i - t) / h) k) * Y i
            * K ((xdat i - t) / h) := by
    rw [← hM θ, ← hA, ← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.sub_apply]; ring
  rw [hobj, hM (θ' - θ), mul_assoc, hcross, mul_sub, Finset.mul_sum, Finset.mul_sum,
    ← add_sub_assoc, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Normal equations**: under `B_t ≻ 0` and a positive bandwidth, `θ` minimises the LP(`ℓ`)
criterion iff `B_t θ = a_t`. (The `→` direction needs no sign hypothesis; the `←` direction
does — with `n·h < 0` the objective is concave and has no minimiser even when the normal
equations hold, so `0 < h` is genuinely required.) -/
theorem isLPSolution_iff_normal
    -- LEAN-ONLY: positive bandwidth, making `n·h > 0` and the objective convex; without it
    -- the `←` direction is false (concave objective at `n·h < 0`). Standard side condition.
    (hh : 0 < h)
    (hpd : (lpMatrix xdat K h ℓ t).PosDef)
    (θ : Fin (ℓ + 1) → ℝ) :
    IsLPSolution xdat Y K h ℓ t θ
      ↔ (lpMatrix xdat K h ℓ t).mulVec θ = lpRhs xdat Y K h ℓ t := by
  have hnh : (n : ℝ) * h ≠ 0 := by
    intro h0
    have hx : (Pi.single (0 : Fin (ℓ + 1)) (1 : ℝ) : Fin (ℓ + 1) → ℝ) ≠ 0 := by
      intro hcon; simpa using congrFun hcon 0
    have hpos := hpd.dotProduct_mulVec_pos hx
    rw [show lpMatrix xdat K h ℓ t = 0 from by simp [lpMatrix, h0]] at hpos
    simp at hpos
  have hn0 : n ≠ 0 := by rintro rfl; simp at hnh
  have hnh_pos : 0 < (n : ℝ) * h :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0) hh
  constructor
  · exact isLPSolution_imp_normal hpd
  · intro hnorm θ'
    have hid := lpObjective_diff xdat Y K h ℓ t hnh θ θ'
    have hterm2 : ∑ j, (θ' - θ) j
        * ((lpMatrix xdat K h ℓ t).mulVec θ - lpRhs xdat Y K h ℓ t) j = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Pi.sub_apply, Pi.sub_apply, hnorm, sub_self, mul_zero]
    rw [hterm2, mul_zero, add_zero] at hid
    have hquad : 0 ≤ ∑ j, (θ' - θ) j * (lpMatrix xdat K h ℓ t).mulVec (θ' - θ) j := by
      rcases eq_or_ne (θ' - θ) 0 with hΔ0 | hΔ0
      · rw [hΔ0]; simp
      · refine le_of_lt ?_
        have hp := hpd.dotProduct_mulVec_pos hΔ0
        simpa [dotProduct, Pi.star_apply, star_trivial] using hp
    have := mul_nonneg hnh_pos.le hquad
    linarith [hid]

/-- Existence of the minimiser in closed form: under `B_t ≻ 0` and a positive bandwidth,
`θ̂ = B_t⁻¹ a_t` minimises the LP(`ℓ`) criterion. -/
theorem isLPSolution_inv_mulVec
    -- LEAN-ONLY: positive bandwidth; same obstruction as `isLPSolution_iff_normal` (`←`)
    (hh : 0 < h)
    (hpd : (lpMatrix xdat K h ℓ t).PosDef) :
    IsLPSolution xdat Y K h ℓ t
      ((lpMatrix xdat K h ℓ t)⁻¹.mulVec (lpRhs xdat Y K h ℓ t)) := by
  refine (isLPSolution_iff_normal hh hpd _).mpr ?_
  have hdet : IsUnit (lpMatrix xdat K h ℓ t).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- Uniqueness of the minimiser under `B_t ≻ 0`. -/
theorem isLPSolution_unique (hpd : (lpMatrix xdat K h ℓ t).PosDef)
    {θ₁ θ₂ : Fin (ℓ + 1) → ℝ}
    (h₁ : IsLPSolution xdat Y K h ℓ t θ₁) (h₂ : IsLPSolution xdat Y K h ℓ t θ₂) :
    θ₁ = θ₂ := by
  have hn1 := isLPSolution_imp_normal hpd h₁
  have hn2 := isLPSolution_imp_normal hpd h₂
  have hdet : IsUnit (lpMatrix xdat K h ℓ t).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  have hkey : (lpMatrix xdat K h ℓ t).mulVec θ₁ = (lpMatrix xdat K h ℓ t).mulVec θ₂ := by
    rw [hn1, hn2]
  calc θ₁ = (lpMatrix xdat K h ℓ t)⁻¹.mulVec ((lpMatrix xdat K h ℓ t).mulVec θ₁) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    _ = (lpMatrix xdat K h ℓ t)⁻¹.mulVec ((lpMatrix xdat K h ℓ t).mulVec θ₂) := by rw [hkey]
    _ = θ₂ := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- The closed-form estimator equals `(B_t⁻¹ a_t)₀`. -/
lemma lpEstimator_eq_invMulVec_lpRhs (xdat Y : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ)
    (t : ℝ) :
    lpEstimator xdat Y K h ℓ t = (lpMatrix xdat K h ℓ t)⁻¹.mulVec (lpRhs xdat Y K h ℓ t) 0 := by
  have hL : lpEstimator xdat Y K h ℓ t
      = ∑ i, ∑ j, Y i * ((n : ℝ) * h)⁻¹
          * ((lpMatrix xdat K h ℓ t)⁻¹ 0 j * lpBasis ℓ ((xdat i - t) / h) j)
          * K ((xdat i - t) / h) := by
    simp only [lpEstimator, lpWeight, Matrix.mulVec, dotProduct, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hR : (lpMatrix xdat K h ℓ t)⁻¹.mulVec (lpRhs xdat Y K h ℓ t) 0
      = ∑ j, ∑ i, Y i * ((n : ℝ) * h)⁻¹
          * ((lpMatrix xdat K h ℓ t)⁻¹ 0 j * lpBasis ℓ ((xdat i - t) / h) j)
          * K ((xdat i - t) / h) := by
    simp only [lpRhs, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hL, hR, Finset.sum_comm]

/-- **The closed-form estimator is the minimiser's first coordinate**: under `B_t ≻ 0`, for
any minimiser `θ`, `lpEstimator xdat Y K h ℓ t = θ 0` (the classical `f̂(t) = U(0)ᵀθ̂(t)`). -/
theorem lpEstimator_eq_isLPSolution (hpd : (lpMatrix xdat K h ℓ t).PosDef)
    {θ : Fin (ℓ + 1) → ℝ} (hθ : IsLPSolution xdat Y K h ℓ t θ) :
    lpEstimator xdat Y K h ℓ t = θ 0 := by
  have hnormal := isLPSolution_imp_normal hpd hθ
  have hdet : IsUnit (lpMatrix xdat K h ℓ t).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  rw [lpEstimator_eq_invMulVec_lpRhs, ← hnormal, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- **The LP(`ℓ`) estimator is linear** in the responses: it is given by response-free
weights (immediately from the closed weight form). -/
theorem isLinearEstimator_lpEstimator (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ) :
    IsLinearEstimator fun (Y : Fin n → ℝ) (t : ℝ) => lpEstimator xdat Y K h ℓ t :=
  ⟨fun t i => lpWeight xdat K h ℓ t i, fun Y t => rfl⟩

end StatLean.NonparametricStatistics
