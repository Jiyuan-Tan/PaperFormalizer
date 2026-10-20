module
public import StatLean.NonparametricStatistics.LocalPolynomial.Quadratic

@[expose] public section

/-!
# Polynomial reproduction by local polynomial weights

Under `B_t ≻ 0`, the LP(`ℓ`) weights reproduce every polynomial of degree at most `ℓ`
*exactly*, for any data configuration:
`∑ i, Q(xdat i)·W*ᵢ(t) = Q(t)`. Stated in the centered monomial basis `(x − t)^k` — every
polynomial of degree `≤ ℓ` is a combination `∑_k c_k (x − t)^k`, so this is equivalent to the
classical statement. In particular the weights sum to one, and their centered moments of
orders `1, …, ℓ` vanish — the cancellation mechanism of the bias analysis.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.6, Proposition 1.12 (polynomial reproduction,
Eq. (1.68)).

**Proof formalization notes.** For responses `Y i = (xdat i − t)^k`, the coefficient vector
`q` with `q_j = δ_{jk}·k!·h^k` satisfies `q ⬝ U((xᵢ−t)/h) = (xᵢ−t)^k`, so it solves the normal
equations `B_t q = a_t`; since `B_t` is invertible, `lpEstimator = (B_t⁻¹ a_t)₀ = q₀`. By
linearity of the weights, the general centered-polynomial identity follows by summation. Needs
`h ≠ 0` (so the basis change `z = (x−t)/h` is invertible).

**Bibliographic comments.** The reproduction property is the defining feature of local
polynomial smoothers; cf. J. Fan and I. Gijbels, *Local Polynomial Modelling and Its
Applications*, Chapman & Hall, 1996, §3.1, and C. J. Stone, *Ann. Statist.* **5** (1977),
595–620.
-/

open Matrix

set_option maxHeartbeats 800000

namespace StatLean.NonparametricStatistics

variable {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {h : ℝ} {ℓ : ℕ} {t : ℝ}

/-- **Centered monomial reproduction**: under `B_t ≻ 0` and `h ≠ 0`, for `k ≤ ℓ`,
`∑ i, (xdat i − t)^k·W*ᵢ(t) = δ_{k,0}` — i.e. the weights sum to `1` and their centered
moments of orders `1, …, ℓ` vanish. -/
theorem lp_weight_reproduce_monomial (hpd : (lpMatrix xdat K h ℓ t).PosDef)
    -- LEAN-ONLY: nonzero bandwidth so the centered basis change is invertible
    (hh : h ≠ 0)
    {k : ℕ} (hk : k ≤ ℓ) :
    ∑ i, (xdat i - t) ^ k * lpWeight xdat K h ℓ t i = if k = 0 then 1 else 0 := by
  have hdet : IsUnit (lpMatrix xdat K h ℓ t).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  set κ : Fin (ℓ + 1) := ⟨k, Nat.lt_succ_of_le hk⟩ with hκ
  have hκv : (κ : ℕ) = k := rfl
  set q : Fin (ℓ + 1) → ℝ := Pi.single κ ((Nat.factorial k : ℝ) * h ^ k) with hq
  -- `q` solves the normal equations for the response `Y i = (xdat i − t)^k`.
  have hBq : (lpMatrix xdat K h ℓ t).mulVec q
      = lpRhs xdat (fun i => (xdat i - t) ^ k) K h ℓ t := by
    funext m
    rw [lpMatrix_mulVec_apply]
    simp only [lpRhs]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hinner : ∑ l, q l * lpBasis ℓ ((xdat i - t) / h) l = (xdat i - t) ^ k := by
      rw [Finset.sum_eq_single_of_mem κ (Finset.mem_univ κ)
        (fun l _ hl => by rw [hq, Pi.single_eq_of_ne hl, zero_mul])]
      rw [hq, Pi.single_eq_same, lpBasis, hκv]
      rw [div_pow]
      field_simp
    rw [hinner]; ring
  -- LHS is `lpEstimator` for the response `(xdat · − t)^k`, which equals `q 0`.
  have hLHS : (∑ i, (xdat i - t) ^ k * lpWeight xdat K h ℓ t i)
      = lpEstimator xdat (fun i => (xdat i - t) ^ k) K h ℓ t := rfl
  rw [hLHS, lpEstimator_eq_invMulVec_lpRhs, ← hBq, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, hq, Pi.single_apply]
  by_cases hk0 : k = 0
  · subst hk0
    simp [hκ, Fin.ext_iff]
  · have hne : ¬ ((0 : Fin (ℓ + 1)) = κ) := by
      rw [hκ, Fin.ext_iff]
      simpa using (Ne.symm hk0)
    simp [hne, hk0]

/-- The LP(`ℓ`) weights sum to one (the `k = 0` case of monomial reproduction). -/
theorem lp_weight_sum_one (hpd : (lpMatrix xdat K h ℓ t).PosDef) (hh : h ≠ 0) :
    ∑ i, lpWeight xdat K h ℓ t i = 1 := by
  have := lp_weight_reproduce_monomial hpd hh (k := 0) (Nat.zero_le _)
  simpa using this

/-- **Polynomial reproduction** in the centered basis: under `B_t ≻ 0` and `h ≠ 0`, for any
coefficients `c : Fin (ℓ+1) → ℝ`,
`∑ i, (∑ k, c k·(xdat i − t)^k)·W*ᵢ(t) = c 0` — that is, `∑ᵢ Q(xdat i)·W*ᵢ(t) = Q(t)` for
every polynomial `Q` of degree at most `ℓ`. -/
theorem lp_weight_reproduce_poly (hpd : (lpMatrix xdat K h ℓ t).PosDef) (hh : h ≠ 0)
    (c : Fin (ℓ + 1) → ℝ) :
    ∑ i, (∑ k : Fin (ℓ + 1), c k * (xdat i - t) ^ (k : ℕ)) * lpWeight xdat K h ℓ t i
      = c 0 := by
  have key : ∀ k : Fin (ℓ + 1),
      ∑ i, (xdat i - t) ^ (k : ℕ) * lpWeight xdat K h ℓ t i = if (k : ℕ) = 0 then 1 else 0 :=
    fun k => lp_weight_reproduce_monomial hpd hh k.is_le
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, key]
  simp [Fin.val_eq_zero_iff]

end StatLean.NonparametricStatistics
