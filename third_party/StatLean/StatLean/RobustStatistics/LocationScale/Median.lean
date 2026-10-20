module
public import StatLean.RobustStatistics.ForMathlib.OrderStatPerturb
public import StatLean.PointEstimation.Equivariance.Defs

@[expose] public section

/-!
# The sample median

The sample median as an order statistic: for `n = 2k+1` observations the median is the
`(k+1)`-th smallest value (`MMY §1.2, §2.3.1`). For even `n` this file adopts the *low
median* (the `⌊(n-1)/2⌋`-th order statistic, `0`-indexed), one of the two conventions the
book allows (`MMY §4.5.1`: "the median must be understood as the 'high' or 'low' median");
all headline robustness theorems are stated for odd `n`, where the conventions coincide.

* `sampleMedian` — the `⌊(n-1)/2⌋`-th order statistic (`0`-indexed); junk value `0` for
  `n = 0`.
* counting characterizations: at least half the data on each side.
* equivariance: location equivariance, and full scale equivariance `Med(cx) = c·Med(x)`
  for odd `n` (index reversal fixes the middle index).

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §1.2, §2.3.1
(eq. (2.18), (2.21): the median as the L¹ location estimate), §4.5.1 (high/low median).

**Bibliographic comments.** The median's status as the archetypal robust estimator was fixed
by J. L. Hodges, Jr. (*Proc. Fifth Berkeley Symp.*, Vol. I, 1967 — the first finite-sample
tolerance computations), F. R. Hampel ("A general qualitative definition of robustness,"
*Ann. Math. Statist.* **42** (1971), 1887–1896 — asymptotic breakdown point 1/2), and the
Princeton study (Andrews, Bickel, Hampel, Huber, Rogers and Tukey, *Robust Estimates of
Location: Survey and Advances*, Princeton Univ. Press, 1972).
-/

open StatLean.MultipleTesting Finset

namespace StatLean.RobustStatistics

variable {n : ℕ}

/-- The **sample median** (`MMY §1.2`): the `⌊(n-1)/2⌋`-th order statistic (`0`-indexed).
For odd `n = 2k+1` this is the `(k+1)`-th smallest observation; for even `n` it is the
*low* median (`MMY §4.5.1`). Junk value `0` when `n = 0`. -/
noncomputable def sampleMedian (x : Fin n → ℝ) : ℝ :=
  if h : n = 0 then 0 else orderStat x ⟨(n - 1) / 2, by omega⟩

/-- Unfolding lemma for nonempty samples. -/
theorem sampleMedian_eq_orderStat (hn : n ≠ 0) (x : Fin n → ℝ) :
    sampleMedian x = orderStat x ⟨(n - 1) / 2, by omega⟩ := by
  rw [sampleMedian, dif_neg hn]

/-- For odd `n = 2k+1` the median is the `(k+1)`-th smallest observation (index `k`,
`0`-indexed). -/
theorem sampleMedian_odd {k : ℕ} (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    sampleMedian x = orderStat x ⟨k, by omega⟩ := by
  rw [sampleMedian_eq_orderStat (by omega)]
  exact congrArg (orderStat x) (Fin.ext (show (n - 1) / 2 = k by omega))

/-- The median is one of the data values. -/
theorem sampleMedian_mem_range (hn : n ≠ 0) (x : Fin n → ℝ) :
    sampleMedian x ∈ Set.range x := by
  rw [sampleMedian_eq_orderStat hn]
  exact orderStat_mem_range x _

/-! ### Counting characterizations (`MMY §2.3.1`, eq. (2.21) context) -/

/-- At least half the observations (strictly more than `(n-1)/2`, i.e. `⌊(n-1)/2⌋ + 1`)
are `≤` the median. -/
theorem card_le_sampleMedian (hn : n ≠ 0) (x : Fin n → ℝ) :
    (n - 1) / 2 + 1 ≤ (univ.filter fun j => x j ≤ sampleMedian x).card := by
  rw [sampleMedian_eq_orderStat hn]
  exact card_le_orderStat_le x ⟨(n - 1) / 2, by omega⟩

/-- At least half the observations are `≥` the median. -/
theorem card_sampleMedian_le (hn : n ≠ 0) (x : Fin n → ℝ) :
    n - (n - 1) / 2 ≤ (univ.filter fun j => sampleMedian x ≤ x j).card := by
  rw [sampleMedian_eq_orderStat hn]
  exact card_orderStat_le x ⟨(n - 1) / 2, by omega⟩

/-! ### Equivariance -/

/-- **The sample median is location equivariant** on nonempty samples (`MMY §2.3.1`).

The nonemptiness hypothesis is not removable: at `n = 0` the junk value
`sampleMedian = 0` would force `0 = 0 + a` for every `a`, and the counterexample
`¬ IsLocEquivariant (sampleMedian (n := 0))` is machine-checked
(`intro h; have := h 1 (fun _ => 0); simp [sampleMedian] at this`). The round-1 stub
omitted the guard; repaired at wave-A merge. -/
theorem sampleMedian_locEquivariant (hn : n ≠ 0) :
    -- LEAN-ONLY: nonempty sample — the n = 0 junk median is not equivariant (see docstring)
    PointEstimation.IsLocEquivariant (sampleMedian (n := n)) := by
  intro a x
  have hx : (x + a • (1 : Fin n → ℝ)) = fun j => x j + a := by
    funext j; simp
  rw [hx, sampleMedian_eq_orderStat hn, sampleMedian_eq_orderStat hn, orderStat_add_const]

/-- For nonnegative scalars the median is scale equivariant (any `n`). -/
theorem sampleMedian_const_mul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : Fin n → ℝ) :
    sampleMedian (fun i => c * x i) = c * sampleMedian x := by
  by_cases hn : n = 0
  · subst hn; simp [sampleMedian]
  · rw [sampleMedian_eq_orderStat hn, sampleMedian_eq_orderStat hn,
      orderStat_const_mul_of_nonneg x hc]

/-- **For odd `n` the median is fully scale equivariant**, `Med(cx) = c·Med(x)` for every
`c : ℝ` (`MMY §2.3.1`): negation reverses the order statistics, and for odd `n` the middle
index is a fixed point of the reversal. -/
theorem sampleMedian_const_mul_of_odd {k : ℕ} (hn : n = 2 * k + 1) (c : ℝ)
    (x : Fin n → ℝ) :
    sampleMedian (fun i => c * x i) = c * sampleMedian x := by
  by_cases hc : 0 ≤ c
  · exact sampleMedian_const_mul_of_nonneg hc x
  replace hc : c < 0 := not_le.mp hc
  -- The middle index of an odd-length sample is fixed by the index reversal `Fin.rev`.
  have hmid : ∀ h : k < n, (⟨k, h⟩ : Fin n).rev = ⟨k, h⟩ := by
    intro h
    refine Fin.ext ?_
    rw [Fin.val_rev]
    change n - (k + 1) = k
    omega
  obtain ⟨w, hw⟩ : ∃ w : Fin n → ℝ, w = fun i => (-c) * x i := ⟨_, rfl⟩
  have hcw : (fun i => c * x i) = fun j => -w j := by
    funext i; rw [hw]; ring
  rw [sampleMedian_odd hn, sampleMedian_odd hn, hcw, orderStat_neg w, hmid, hw,
    orderStat_const_mul_of_nonneg x (by linarith : (0:ℝ) ≤ -c)]
  ring

/-- Median of a constant sample. -/
theorem sampleMedian_const (hn : n ≠ 0) (a : ℝ) :
    sampleMedian (fun _ : Fin n => a) = a := by
  rw [sampleMedian_eq_orderStat hn]
  rfl

end StatLean.RobustStatistics
