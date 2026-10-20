module
public import StatLean.NonparametricStatistics.Projection.Defs
public import StatLean.NonparametricStatistics.ForMathlib.TrigDiscreteSums

@[expose] public section

/-!
# Discrete orthonormality of the trigonometric system at the regular design

The exact discrete analogue of `L²[0,1]`-orthonormality: at the regular design
`x_s = s/n`, `s = 1, …, n`,
$$ \frac1n \sum_{s=1}^{n} \varphi_j(s/n)\,\varphi_k(s/n) \;=\; \delta_{jk},
   \qquad 1 \le j, k \le n-1. $$
This is the reason coefficient estimates at the regular design behave *exactly* like Fourier
coefficients: the empirical Gram matrix of the first `n − 1` basis functions is the identity.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.7.2, Lemma 1.7 (discrete orthonormality of the
trigonometric basis at the regular design).

**Proof formalization notes.** Product-to-sum turns each product into discrete cosine/sine
sums at frequencies `j/2 ± k/2` (ℕ-division bookkeeping); by `ForMathlib/TrigDiscreteSums`
these vanish unless the frequency is a multiple of `n`, and for `1 ≤ j, k ≤ n − 1` the
frequencies `j/2 ± k/2` lie in `(−n, n)`, so only the zero frequency survives — precisely at
same-parity equal indices, where the normalization `(√2)²·(1/2) = 1` (and `φ₁ ≡ 1`) gives the
diagonal. The frequency-range arithmetic is the delicate step; state each parity case as a
private lemma if useful.

**Bibliographic comments.** Classical discrete Fourier analysis; its use for regular-design
regression estimates appears in J. Rice, *Ann. Statist.* **12** (1984), 1215–1230, and
B. T. Polyak and A. B. Tsybakov, "Asymptotic optimality of the `C_p`-test for the orthogonal
series estimation of regression," *Theory Probab. Appl.* **35** (1990), 293–306.
-/

namespace StatLean.NonparametricStatistics

/-! ### Normal forms for the trigonometric system -/

private lemma trigBasis_one (x : ℝ) : trigBasis 1 x = 1 := by
  simp [trigBasis]

private lemma trigBasis_even {q : ℕ} (hq : 1 ≤ q) (x : ℝ) :
    trigBasis (2 * q) x = Real.sqrt 2 * Real.cos (2 * Real.pi * (q : ℝ) * x) := by
  have h2 : (2 * q) / 2 = q := by omega
  unfold trigBasis
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), h2]

private lemma trigBasis_odd {q : ℕ} (hq : 1 ≤ q) (x : ℝ) :
    trigBasis (2 * q + 1) x = Real.sqrt 2 * Real.sin (2 * Real.pi * (q : ℝ) * x) := by
  have h2 : (2 * q + 1) / 2 = q := by omega
  unfold trigBasis
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), h2]

private lemma trig_index_cases {j : ℕ} (hj : 1 ≤ j) :
    j = 1 ∨ (∃ p, 1 ≤ p ∧ j = 2 * p) ∨ (∃ p, 1 ≤ p ∧ j = 2 * p + 1) := by
  rcases Nat.lt_or_ge j 2 with h | h
  · left; omega
  · rcases Nat.even_or_odd j with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact Or.inr (Or.inl ⟨p, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨p, by omega, by omega⟩)

/-! ### Integer-frequency discrete sums -/

private lemma not_dvd_of_abs_lt {n : ℕ} {c : ℤ} (hc0 : c ≠ 0)
    (hlow : -(n : ℤ) < c) (hhigh : c < n) : ¬ (n : ℤ) ∣ c := by
  intro hdvd
  have h1 : (n : ℤ) ≤ |c| := Int.le_of_dvd (abs_pos.mpr hc0) ((dvd_abs _ _).mpr hdvd)
  have h2 : |c| < (n : ℤ) := abs_lt.mpr ⟨hlow, hhigh⟩
  omega

private lemma cast_eq_or_neg_natAbs (c : ℤ) :
    (c : ℝ) = (c.natAbs : ℝ) ∨ (c : ℝ) = -(c.natAbs : ℝ) := by
  rcases Int.natAbs_eq c with h | h
  · left; have := congrArg (fun z : ℤ => (z : ℝ)) h; simpa using this
  · right; have := congrArg (fun z : ℤ => (z : ℝ)) h; simpa using this

/-- Discrete cosine sum at an integer frequency: `n` if `n ∣ c`, else `0`. -/
private lemma sum_cosZ (n : ℕ) (c : ℤ) :
    ∑ s ∈ Finset.range n, Real.cos (2 * Real.pi * (c : ℝ) * (↑s + 1) / n)
      = if (n : ℤ) ∣ c then (n : ℝ) else 0 := by
  have hcos : ∀ s : ℕ, Real.cos (2 * Real.pi * (c : ℝ) * (↑s + 1) / n)
      = Real.cos (2 * Real.pi * (c.natAbs : ℝ) * (↑s + 1) / n) := by
    intro s
    rcases cast_eq_or_neg_natAbs c with hc | hc
    · rw [hc]
    · rw [hc, show 2 * Real.pi * (-(c.natAbs : ℝ)) * (↑s + 1) / n
            = -(2 * Real.pi * (c.natAbs : ℝ) * (↑s + 1) / n) from by ring, Real.cos_neg]
  rw [Finset.sum_congr rfl (fun s _ => hcos s)]
  by_cases hdvd : (n : ℤ) ∣ c
  · rw [if_pos hdvd]; exact sum_cos_two_pi_mul_div_of_dvd (Int.dvd_natAbs.mpr hdvd)
  · rw [if_neg hdvd]
    exact sum_cos_two_pi_mul_div_eq_zero (fun h => hdvd (Int.dvd_natAbs.mp h))

/-- Discrete sine sum at an integer frequency: always `0`. -/
private lemma sum_sinZ (n : ℕ) (c : ℤ) :
    ∑ s ∈ Finset.range n, Real.sin (2 * Real.pi * (c : ℝ) * (↑s + 1) / n) = 0 := by
  have hb : ∀ m : ℕ, ∑ s ∈ Finset.range n,
      Real.sin (2 * Real.pi * (m : ℝ) * (↑s + 1) / n) = 0 := by
    intro m
    by_cases h : (n : ℤ) ∣ (m : ℤ)
    · exact sum_sin_two_pi_mul_div_of_dvd h
    · exact sum_sin_two_pi_mul_div_eq_zero h
  rcases cast_eq_or_neg_natAbs c with hc | hc
  · have hterm : ∀ s : ℕ, Real.sin (2 * Real.pi * (c : ℝ) * (↑s + 1) / n)
        = Real.sin (2 * Real.pi * (c.natAbs : ℝ) * (↑s + 1) / n) := by
      intro s; rw [hc]
    rw [Finset.sum_congr rfl (fun s _ => hterm s), hb]
  · have hterm : ∀ s : ℕ, Real.sin (2 * Real.pi * (c : ℝ) * (↑s + 1) / n)
        = -Real.sin (2 * Real.pi * (c.natAbs : ℝ) * (↑s + 1) / n) := by
      intro s
      rw [hc, show 2 * Real.pi * (-(c.natAbs : ℝ)) * (↑s + 1) / n
            = -(2 * Real.pi * (c.natAbs : ℝ) * (↑s + 1) / n) from by ring, Real.sin_neg]
    rw [Finset.sum_congr rfl (fun s _ => hterm s), Finset.sum_neg_distrib, hb, neg_zero]

/-- **Discrete orthonormality at the regular design**: for `1 ≤ j, k ≤ n − 1`,
`n⁻¹ ∑_{s=1}^n φⱼ(s/n)·φ_k(s/n) = δ_{jk}`. -/
theorem trigBasis_discrete_orthonormal {n j k : ℕ}
    (hj : 1 ≤ j) (hj' : j ≤ n - 1) (hk : 1 ≤ k) (hk' : k ≤ n - 1) :
    (n : ℝ)⁻¹ * ∑ i : Fin n, trigBasis j (regularDesign n i) * trigBasis k (regularDesign n i)
      = if j = k then 1 else 0 := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hconv : ∑ i : Fin n,
        trigBasis j (regularDesign n i) * trigBasis k (regularDesign n i)
      = ∑ s ∈ Finset.range n,
        trigBasis j (((s : ℝ) + 1) / n) * trigBasis k (((s : ℝ) + 1) / n) :=
    Fin.sum_univ_eq_sum_range
      (fun s => trigBasis j (((s : ℝ) + 1) / n) * trigBasis k (((s : ℝ) + 1) / n)) n
  rw [hconv]
  rcases trig_index_cases hj with hj1 | ⟨p, hp, hjp⟩ | ⟨p, hp, hjp⟩ <;>
    rcases trig_index_cases hk with hk1 | ⟨q, hq, hkq⟩ | ⟨q, hq, hkq⟩
  -- j = 1, k = 1
  · subst hj1; subst hk1
    rw [if_pos rfl]
    have hterm : ∀ s : ℕ,
        trigBasis 1 (((s : ℝ) + 1) / n) * trigBasis 1 (((s : ℝ) + 1) / n) = (1 : ℝ) := by
      intro s; rw [trigBasis_one]; ring
    rw [Finset.sum_congr rfl (fun s _ => hterm s), Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, inv_mul_cancel₀ hn0]
  -- j = 1, k = 2q
  · subst hj1; subst hkq
    rw [if_neg (by omega)]
    have hterm : ∀ s : ℕ, trigBasis 1 (((s : ℝ) + 1) / n) * trigBasis (2 * q) (((s : ℝ) + 1) / n)
        = Real.sqrt 2 * Real.cos (2 * Real.pi * ((q : ℤ) : ℝ) * (↑s + 1) / n) := by
      intro s
      rw [trigBasis_one, trigBasis_even hq, one_mul,
          show 2 * Real.pi * ((q : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (q : ℝ) * (((s : ℝ) + 1) / n) from by push_cast; ring]
    rw [Finset.sum_congr rfl (fun s _ => hterm s), ← Finset.mul_sum, sum_cosZ,
        if_neg (not_dvd_of_abs_lt (by omega) (by omega) (by omega)), mul_zero, mul_zero]
  -- j = 1, k = 2q+1
  · subst hj1; subst hkq
    rw [if_neg (by omega)]
    have hterm : ∀ s : ℕ, trigBasis 1 (((s : ℝ) + 1) / n)
        * trigBasis (2 * q + 1) (((s : ℝ) + 1) / n)
        = Real.sqrt 2 * Real.sin (2 * Real.pi * ((q : ℤ) : ℝ) * (↑s + 1) / n) := by
      intro s
      rw [trigBasis_one, trigBasis_odd hq, one_mul,
          show 2 * Real.pi * ((q : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (q : ℝ) * (((s : ℝ) + 1) / n) from by push_cast; ring]
    rw [Finset.sum_congr rfl (fun s _ => hterm s), ← Finset.mul_sum, sum_sinZ, mul_zero, mul_zero]
  -- j = 2p, k = 1
  · subst hjp; subst hk1
    rw [if_neg (by omega)]
    have hterm : ∀ s : ℕ, trigBasis (2 * p) (((s : ℝ) + 1) / n) * trigBasis 1 (((s : ℝ) + 1) / n)
        = Real.sqrt 2 * Real.cos (2 * Real.pi * ((p : ℤ) : ℝ) * (↑s + 1) / n) := by
      intro s
      rw [trigBasis_even hp, trigBasis_one, mul_one,
          show 2 * Real.pi * ((p : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (p : ℝ) * (((s : ℝ) + 1) / n) from by push_cast; ring]
    rw [Finset.sum_congr rfl (fun s _ => hterm s), ← Finset.mul_sum, sum_cosZ,
        if_neg (not_dvd_of_abs_lt (by omega) (by omega) (by omega)), mul_zero, mul_zero]
  -- j = 2p, k = 2q
  · subst hjp; subst hkq
    have hterm : ∀ s : ℕ, trigBasis (2 * p) (((s : ℝ) + 1) / n)
        * trigBasis (2 * q) (((s : ℝ) + 1) / n)
        = Real.cos (2 * Real.pi * ((p - q : ℤ) : ℝ) * (↑s + 1) / n)
          + Real.cos (2 * Real.pi * ((p + q : ℤ) : ℝ) * (↑s + 1) / n) := by
      intro s
      rw [trigBasis_even hp, trigBasis_even hq]
      set x := ((s : ℝ) + 1) / n with hx
      rw [show 2 * Real.pi * ((p - q : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (p : ℝ) * x - 2 * Real.pi * (q : ℝ) * x from by
              rw [hx]; push_cast; ring,
          show 2 * Real.pi * ((p + q : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (p : ℝ) * x + 2 * Real.pi * (q : ℝ) * x from by
              rw [hx]; push_cast; ring,
          Real.cos_sub, Real.cos_add,
          show Real.sqrt 2 * Real.cos (2 * Real.pi * (p : ℝ) * x)
              * (Real.sqrt 2 * Real.cos (2 * Real.pi * (q : ℝ) * x))
            = (Real.sqrt 2 * Real.sqrt 2)
              * (Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x))
            from by ring, hsqrt]
      ring
    have hsum : ¬ (n : ℤ) ∣ ((p : ℤ) + q) := not_dvd_of_abs_lt (by omega) (by omega) (by omega)
    rw [Finset.sum_congr rfl (fun s _ => hterm s), Finset.sum_add_distrib, sum_cosZ, sum_cosZ,
        if_neg hsum, add_zero]
    rcases eq_or_ne p q with h | h
    · subst h
      rw [if_pos (by simp), if_pos (by omega), inv_mul_cancel₀ hn0]
    · have hdiff : ¬ (n : ℤ) ∣ ((p : ℤ) - q) := not_dvd_of_abs_lt (by omega) (by omega) (by omega)
      rw [if_neg hdiff, if_neg (by omega), mul_zero]
  -- j = 2p, k = 2q+1
  · subst hjp; subst hkq
    rw [if_neg (by omega)]
    have hterm : ∀ s : ℕ,
        trigBasis (2 * p) (((s : ℝ) + 1) / n) * trigBasis (2 * q + 1) (((s : ℝ) + 1) / n)
        = Real.sin (2 * Real.pi * ((p + q : ℤ) : ℝ) * (↑s + 1) / n)
          - Real.sin (2 * Real.pi * ((p - q : ℤ) : ℝ) * (↑s + 1) / n) := by
      intro s
      rw [trigBasis_even hp, trigBasis_odd hq]
      set x := ((s : ℝ) + 1) / n with hx
      rw [show 2 * Real.pi * ((p + q : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (p : ℝ) * x + 2 * Real.pi * (q : ℝ) * x from by
              rw [hx]; push_cast; ring,
          show 2 * Real.pi * ((p - q : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (p : ℝ) * x - 2 * Real.pi * (q : ℝ) * x from by
              rw [hx]; push_cast; ring,
          Real.sin_add, Real.sin_sub,
          show Real.sqrt 2 * Real.cos (2 * Real.pi * (p : ℝ) * x)
              * (Real.sqrt 2 * Real.sin (2 * Real.pi * (q : ℝ) * x))
            = (Real.sqrt 2 * Real.sqrt 2)
              * (Real.cos (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x))
            from by ring, hsqrt]
      ring
    rw [Finset.sum_congr rfl (fun s _ => hterm s), Finset.sum_sub_distrib, sum_sinZ, sum_sinZ,
        sub_zero, mul_zero]
  -- j = 2p+1, k = 1
  · subst hjp; subst hk1
    rw [if_neg (by omega)]
    have hterm : ∀ s : ℕ, trigBasis (2 * p + 1) (((s : ℝ) + 1) / n)
        * trigBasis 1 (((s : ℝ) + 1) / n)
        = Real.sqrt 2 * Real.sin (2 * Real.pi * ((p : ℤ) : ℝ) * (↑s + 1) / n) := by
      intro s
      rw [trigBasis_odd hp, trigBasis_one, mul_one,
          show 2 * Real.pi * ((p : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (p : ℝ) * (((s : ℝ) + 1) / n) from by push_cast; ring]
    rw [Finset.sum_congr rfl (fun s _ => hterm s), ← Finset.mul_sum, sum_sinZ, mul_zero, mul_zero]
  -- j = 2p+1, k = 2q
  · subst hjp; subst hkq
    rw [if_neg (by omega)]
    have hterm : ∀ s : ℕ,
        trigBasis (2 * p + 1) (((s : ℝ) + 1) / n) * trigBasis (2 * q) (((s : ℝ) + 1) / n)
        = Real.sin (2 * Real.pi * ((p + q : ℤ) : ℝ) * (↑s + 1) / n)
          + Real.sin (2 * Real.pi * ((p - q : ℤ) : ℝ) * (↑s + 1) / n) := by
      intro s
      rw [trigBasis_odd hp, trigBasis_even hq]
      set x := ((s : ℝ) + 1) / n with hx
      rw [show 2 * Real.pi * ((p + q : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (p : ℝ) * x + 2 * Real.pi * (q : ℝ) * x from by
              rw [hx]; push_cast; ring,
          show 2 * Real.pi * ((p - q : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (p : ℝ) * x - 2 * Real.pi * (q : ℝ) * x from by
              rw [hx]; push_cast; ring,
          Real.sin_add, Real.sin_sub,
          show Real.sqrt 2 * Real.sin (2 * Real.pi * (p : ℝ) * x)
              * (Real.sqrt 2 * Real.cos (2 * Real.pi * (q : ℝ) * x))
            = (Real.sqrt 2 * Real.sqrt 2)
              * (Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.cos (2 * Real.pi * (q : ℝ) * x))
            from by ring, hsqrt]
      ring
    rw [Finset.sum_congr rfl (fun s _ => hterm s), Finset.sum_add_distrib, sum_sinZ, sum_sinZ,
        add_zero, mul_zero]
  -- j = 2p+1, k = 2q+1
  · subst hjp; subst hkq
    have hterm : ∀ s : ℕ,
        trigBasis (2 * p + 1) (((s : ℝ) + 1) / n) * trigBasis (2 * q + 1) (((s : ℝ) + 1) / n)
        = Real.cos (2 * Real.pi * ((p - q : ℤ) : ℝ) * (↑s + 1) / n)
          - Real.cos (2 * Real.pi * ((p + q : ℤ) : ℝ) * (↑s + 1) / n) := by
      intro s
      rw [trigBasis_odd hp, trigBasis_odd hq]
      set x := ((s : ℝ) + 1) / n with hx
      rw [show 2 * Real.pi * ((p - q : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (p : ℝ) * x - 2 * Real.pi * (q : ℝ) * x from by
              rw [hx]; push_cast; ring,
          show 2 * Real.pi * ((p + q : ℤ) : ℝ) * ((s : ℝ) + 1) / n
            = 2 * Real.pi * (p : ℝ) * x + 2 * Real.pi * (q : ℝ) * x from by
              rw [hx]; push_cast; ring,
          Real.cos_sub, Real.cos_add,
          show Real.sqrt 2 * Real.sin (2 * Real.pi * (p : ℝ) * x)
              * (Real.sqrt 2 * Real.sin (2 * Real.pi * (q : ℝ) * x))
            = (Real.sqrt 2 * Real.sqrt 2)
              * (Real.sin (2 * Real.pi * (p : ℝ) * x) * Real.sin (2 * Real.pi * (q : ℝ) * x))
            from by ring, hsqrt]
      ring
    have hsum : ¬ (n : ℤ) ∣ ((p : ℤ) + q) := not_dvd_of_abs_lt (by omega) (by omega) (by omega)
    rw [Finset.sum_congr rfl (fun s _ => hterm s), Finset.sum_sub_distrib, sum_cosZ, sum_cosZ,
        if_neg hsum, sub_zero]
    rcases eq_or_ne p q with h | h
    · subst h
      rw [if_pos (by simp), if_pos (by omega), inv_mul_cancel₀ hn0]
    · have hdiff : ¬ (n : ℤ) ∣ ((p : ℤ) - q) := not_dvd_of_abs_lt (by omega) (by omega) (by omega)
      rw [if_neg hdiff, if_neg (by omega), mul_zero]

end StatLean.NonparametricStatistics
