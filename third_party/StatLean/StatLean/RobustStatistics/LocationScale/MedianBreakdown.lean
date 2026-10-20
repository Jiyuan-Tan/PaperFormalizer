module
public import StatLean.RobustStatistics.LocationScale.Median
public import StatLean.RobustStatistics.Core.BreakdownPoint

@[expose] public section

/-!
# Breakdown of the sample median — the maximal-resistance theorem

The flagship finite-sample robustness contrast (`MMY §3.2.5`): for `n = 2k+1`
observations, the sample median resists `k` arbitrary replacements but breaks under
`k+1`, so its breakdown count is exactly `m* = k = ⌊(n-1)/2⌋` — the maximum possible for
any location-equivariant estimator (`MMY` eq. (3.26), `Core/BreakdownPoint.lean`) — while
the sample mean has `m* = 0` (`LocationScale/Mean.lean`).

* `sampleMedian_resists` — with at most `k` replacements, the median stays within the
  range of the original data (via the replacement-perturbation bound
  `orderStat_le_of_hammingDist`).
* `sampleMedian_breaksUnder` — `k+1` replacements placed at a common large value drag
  the median beyond any bound.
* `sampleMedian_breakdownCount` — `m*(Med, x) = k`, hence `ε*_n = k/(2k+1) → 1/2`.
* `sampleMedian_breakdownCount_eq_max` — the median attains the location-equivariant
  maximum `⌊(n-1)/2⌋`.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §3.2.5 (eq.
(3.24)–(3.26)), §3.8.2.

**Bibliographic comments.** The finite-sample computation — the median resists `k` of
`2k+1` replacements, and no location-equivariant estimator does better than `⌊(n−1)/2⌋` —
is D. L. Donoho and P. J. Huber, "The notion of breakdown point," in *A Festschrift for
Erich L. Lehmann*, Wadsworth, 1983, pp. 157–184, sharpening Hodges (1967) and Hampel's
asymptotic 1/2 (1971).
-/

open Finset

namespace StatLean.RobustStatistics

open StatLean.MultipleTesting

variable {n k : ℕ}

/-- The quantitative resistance bound, stated before `sampleMedian_resists` so that the
latter can use it (the public restatement is `sampleMedian_mem_Icc_of_hammingDist`).

With `n = 2k+1` the median is `y₍ₖ₎`; the replacement-perturbation bound
`orderStat_le_of_hammingDist` applies twice, at `0 + k ≤ k` and at `k + k ≤ 2k`, giving
`x₍₀₎ ≤ y₍ₖ₎ ≤ x₍₂ₖ₎`. -/
private theorem mem_Icc_aux (hn : n = 2 * k + 1) {x y : Fin n → ℝ}
    (h : hammingDist x y ≤ k) :
    sampleMedian y ∈ Set.Icc (⨅ i, x i) (⨆ i, x i) := by
  have h0 : 0 < n := by omega
  have hk : k < n := by omega
  have h2k : 2 * k < n := by omega
  rw [sampleMedian_odd hn, Set.mem_Icc]
  constructor
  · have hle : orderStat x ⟨0, h0⟩ ≤ orderStat y ⟨k, hk⟩ :=
      orderStat_le_of_hammingDist (m := k) h (by change 0 + k ≤ k; omega)
    obtain ⟨j, hj⟩ := orderStat_mem_range x ⟨0, h0⟩
    refine le_trans ?_ hle
    rw [← hj]
    exact ciInf_le (Set.Finite.bddBelow (Set.finite_range x)) j
  · have hle : orderStat y ⟨k, hk⟩ ≤ orderStat x ⟨2 * k, h2k⟩ :=
      orderStat_le_of_hammingDist (m := k) (hammingDist_comm x y ▸ h)
        (by change k + k ≤ 2 * k; omega)
    obtain ⟨j, hj⟩ := orderStat_mem_range x ⟨2 * k, h2k⟩
    refine le_trans hle ?_
    rw [← hj]
    exact le_ciSup (Set.Finite.bddAbove (Set.finite_range x)) j

/-- **The median resists `k` replacements** (`n = 2k+1`; `MMY §3.2.5`): however at most
`k` observations are replaced, the median of the corrupted sample stays within the range
of the original data, hence bounded. -/
theorem sampleMedian_resists (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    Resists sampleMedian x k := by
  refine ⟨max |⨅ i, x i| |⨆ i, x i|, fun y hy => ?_⟩
  have h := mem_Icc_aux hn hy
  rw [Set.mem_Icc] at h
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h1 : -|⨅ i, x i| ≤ ⨅ i, x i := neg_abs_le _
    have h2 : -max |⨅ i, x i| |⨆ i, x i| ≤ -|⨅ i, x i| := neg_le_neg (le_max_left _ _)
    linarith [h.1]
  · have h1 : (⨆ i, x i) ≤ |⨆ i, x i| := le_abs_self _
    have h2 : |⨆ i, x i| ≤ max |⨅ i, x i| |⨆ i, x i| := le_max_right _ _
    linarith [h.2]

/-- Quantitative form of the resistance: the corrupted median lies between the smallest
and largest original observations. -/
theorem sampleMedian_mem_Icc_of_hammingDist (hn : n = 2 * k + 1) {x y : Fin n → ℝ}
    (h : hammingDist x y ≤ k) :
    sampleMedian y ∈ Set.Icc (⨅ i, x i) (⨆ i, x i) :=
  mem_Icc_aux hn h

/-- **`k+1` replacements break the median** (`n = 2k+1`; `MMY §3.2.5`): placing `k+1`
observations at a common arbitrarily large value drags the median beyond any bound. -/
theorem sampleMedian_breaksUnder (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    BreaksUnder sampleMedian x (k + 1) := by
  intro M
  have hk : k < n := by omega
  have hval : ((⟨k, hk⟩ : Fin n) : ℕ) = k := rfl
  -- Move the `k+1` coordinates `Iic ⟨k, _⟩` to the common value `|M| + 1`.
  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ,
      y = fun j => if j ≤ (⟨k, hk⟩ : Fin n) then |M| + 1 else x j := ⟨_, rfl⟩
  have hbig : ∀ j : Fin n, j ≤ (⟨k, hk⟩ : Fin n) → y j = |M| + 1 := by
    intro j hj; simp [hy, hj]
  have hsame : ∀ j : Fin n, ¬j ≤ (⟨k, hk⟩ : Fin n) → y j = x j := by
    intro j hj; simp [hy, hj]
  refine ⟨y, ?_, ?_⟩
  · -- only the `k+1` coordinates of `Iic ⟨k, _⟩` were touched
    have hsub : (univ.filter fun j => x j ≠ y j) ⊆ Finset.Iic (⟨k, hk⟩ : Fin n) := by
      intro j hj
      rw [mem_filter] at hj
      rw [Finset.mem_Iic]
      by_contra hjc
      exact hj.2 (hsame j hjc).symm
    calc hammingDist x y ≤ (Finset.Iic (⟨k, hk⟩ : Fin n)).card := Finset.card_le_card hsub
      _ = k + 1 := by rw [Fin.card_Iic, hval]
  · -- `k+1` coordinates sit at `|M| + 1`, so at most `k` are below it: `y₍ₖ₎ ≥ |M| + 1`
    have hge : |M| + 1 ≤ sampleMedian y := by
      rw [sampleMedian_odd hn]
      refine le_orderStat_of_card_le y ⟨k, hk⟩ (|M| + 1) ?_
      have hsub : Finset.Iic (⟨k, hk⟩ : Fin n) ⊆ univ.filter fun j => |M| + 1 ≤ y j := by
        intro j hj
        rw [Finset.mem_Iic] at hj
        rw [mem_filter]
        exact ⟨mem_univ j, le_of_eq (hbig j hj).symm⟩
      have hcard := Finset.card_le_card hsub
      rw [Fin.card_Iic, hval] at hcard
      omega
    calc M ≤ |M| := le_abs_self M
      _ < |M| + 1 := by linarith
      _ ≤ sampleMedian y := hge
      _ ≤ |sampleMedian y| := le_abs_self _

/-- **The breakdown count of the median is exactly `k`** (`n = 2k+1`; `MMY §3.2.5`):
`m*(Med, x) = k`, so the finite-sample breakdown point is `ε*_n = k/(2k+1) → 1/2`. -/
theorem sampleMedian_breakdownCount (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    breakdownCount sampleMedian x = k :=
  breakdownCount_eq_of_resists_of_breaksUnder (by omega) (sampleMedian_resists hn x)
    (sampleMedian_breaksUnder hn x)

/-- **The median attains the maximal breakdown of location-equivariant estimators**
(`MMY` eq. (3.26)): `m*(Med, x) = ⌊(n-1)/2⌋`, the upper bound of
`locEquivariant_breakdownCount_le`. -/
theorem sampleMedian_breakdownCount_eq_max (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    breakdownCount sampleMedian x = (n - 1) / 2 := by
  rw [sampleMedian_breakdownCount hn]
  omega

/-- The finite-sample breakdown point of the median, `ε*_n = k/(2k+1)`. -/
theorem sampleMedian_breakdownPoint (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    breakdownPoint sampleMedian x = k / (2 * k + 1 : ℝ) := by
  have hnr : (n : ℝ) = 2 * k + 1 := by rw [hn]; push_cast; ring
  unfold breakdownPoint
  rw [sampleMedian_breakdownCount hn, hnr]

end StatLean.RobustStatistics
