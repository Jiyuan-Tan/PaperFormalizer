module
public import StatLean.RobustStatistics.ForMathlib.OrderStatPerturb
public import StatLean.RobustStatistics.LocationScale.Mean
public import StatLean.PointEstimation.Equivariance.Defs

@[expose] public section

/-!
# The trimmed mean

The `m`-trimmed mean discards the `m` smallest and `m` largest observations and averages
the rest (`MMY §2.4`, the α-trimmed mean with `m = [nα]`):

$$\bar x_{(m)} = \frac{1}{n-2m} \sum_{i=m}^{n-m-1} x_{(i)},$$

interpolating between the sample mean (`m = 0`) and the median (`m → ⌊(n-1)/2⌋`). Its
finite-sample robustness — resistance to `m` replacements — follows from the
replacement-perturbation bound on order statistics
(`ForMathlib/OrderStatPerturb.lean`), matching `m* = [nα]` in `MMY §3.2.5`.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.4 (trimmed
and Winsorized means), §3.2.5 (their breakdown).

**Bibliographic comments.** Trimmed means as a systematic tool begin with J. W. Tukey and
D. H. McLaughlin, "Less vulnerable confidence and significance procedures for location based
on a single sample: trimming/Winsorization 1," *Sankhyā Ser. A* **25** (1963), 331–352;
their asymptotics are P. J. Bickel, "On some robust estimates of location," *Ann. Math.
Statist.* **36** (1965), 847–858, and S. M. Stigler, "The asymptotic distribution of the
trimmed mean," *Ann. Statist.* **1** (1973), 472–477. The finite-sample breakdown count
`m* = m` at trim depth `m` is the pattern of Donoho–Huber (1983).
-/

open StatLean.MultipleTesting Finset

namespace StatLean.RobustStatistics

variable {n : ℕ}

/-- The **`m`-trimmed mean** (`MMY §2.4`): the average of the order statistics with the
`m` smallest and `m` largest observations removed. Junk value `0` when `n ≤ 2m` (empty
trimmed sum or division by `0`). -/
noncomputable def trimmedMean (m : ℕ) (x : Fin n → ℝ) : ℝ :=
  (∑ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m), orderStat x i) /
    (n - 2 * m : ℝ)

/-! ### The retained index set

The trimmed sum runs over the `n - 2m` retained ranks `m ≤ i < n - m`; the two private
lemmas below compute that cardinality (in `ℕ` and, under `2m < n`, in `ℝ`) once and for
all. -/

/-- The retained ranks are in bijection with `Ico m (n - m)`, so there are `n - 2m` of
them. -/
private theorem card_trim_filter (n m : ℕ) :
    (univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m)).card = n - 2 * m := by
  classical
  have h : (univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m)).card
      = (Finset.Ico m (n - m)).card := by
    refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      exact Finset.mem_Ico.mpr ha
    · intro a _ b _ hab
      exact Fin.val_injective hab
    · intro b hb
      rw [Finset.mem_Ico] at hb
      exact ⟨⟨b, by omega⟩, by simp only [mem_filter, mem_univ, true_and]; omega, rfl⟩
  rw [h, Nat.card_Ico]
  omega

/-- The real-valued cardinality of the retained index set, matching the denominator of
`trimmedMean`. -/
private theorem cast_card_trim {m : ℕ} (hm : 2 * m < n) :
    ((univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m)).card : ℝ)
      = (n : ℝ) - 2 * (m : ℝ) := by
  rw [card_trim_filter, Nat.cast_sub hm.le]
  push_cast
  ring

/-- The denominator of `trimmedMean` is positive when some observations are retained. -/
private theorem trim_denom_pos {m : ℕ} (hm : 2 * m < n) : (0 : ℝ) < (n : ℝ) - 2 * (m : ℝ) := by
  have h1 : ((2 * m : ℕ) : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hm
  push_cast at h1
  linarith

/-- A uniform lower bound on the retained order statistics is a lower bound for the
trimmed mean. -/
private theorem le_trimmedMean_of_forall {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) {a : ℝ}
    (ha : ∀ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m),
      a ≤ orderStat x i) :
    a ≤ trimmedMean m x := by
  have hd := trim_denom_pos (n := n) hm
  have hsum := Finset.card_nsmul_le_sum _ (orderStat x) a ha
  rw [nsmul_eq_mul, cast_card_trim hm] at hsum
  simp only [trimmedMean]
  rw [le_div_iff₀ hd]
  linarith [hsum, mul_comm ((n : ℝ) - 2 * (m : ℝ)) a]

/-- A uniform upper bound on the retained order statistics is an upper bound for the
trimmed mean. -/
private theorem trimmedMean_le_of_forall {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) {b : ℝ}
    (hb : ∀ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m),
      orderStat x i ≤ b) :
    trimmedMean m x ≤ b := by
  have hd := trim_denom_pos (n := n) hm
  have hsum := Finset.sum_le_card_nsmul _ (orderStat x) b hb
  rw [nsmul_eq_mul, cast_card_trim hm] at hsum
  simp only [trimmedMean]
  rw [div_le_iff₀ hd]
  linarith [hsum, mul_comm ((n : ℝ) - 2 * (m : ℝ)) b]

/-! ### Basic properties -/

/-- With no trimming the trimmed mean is the sample mean (`MMY §2.4`, limit case
`α = 0`). -/
theorem trimmedMean_zero (x : Fin n → ℝ) : trimmedMean 0 x = sampleMean x := by
  classical
  have hfilter : (univ.filter (fun i : Fin n => 0 ≤ (i : ℕ) ∧ (i : ℕ) < n - 0)) = univ := by
    refine Finset.filter_true_of_mem fun i _ => ⟨Nat.zero_le _, ?_⟩
    simp
  simp only [trimmedMean, sampleMean, hfilter, sum_orderStat]
  norm_num

/-- **The trimmed mean is location equivariant** (`MMY §2.4`, eq. (2.43)–(2.46): it is an
L-estimator with weights summing to one). -/
theorem trimmedMean_locEquivariant {m : ℕ} (hm : 2 * m < n) :
    PointEstimation.IsLocEquivariant (trimmedMean (n := n) m) := by
  classical
  intro a x
  have hd := trim_denom_pos (n := n) hm
  have hx : (x + a • (1 : Fin n → ℝ)) = fun j => x j + a := by funext j; simp
  -- Each retained order statistic shifts by `a`, and there are `n - 2m` of them.
  have hsum : ∑ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m),
        orderStat (fun j => x j + a) i
      = (∑ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m), orderStat x i)
        + ((n : ℝ) - 2 * (m : ℝ)) * a := by
    rw [Finset.sum_congr rfl fun i _ => orderStat_add_const x a i, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, cast_card_trim hm]
  rw [hx]
  simp only [trimmedMean]
  rw [hsum, add_div, mul_div_cancel_left₀ a hd.ne']

/-- The trimmed mean lies between the extreme retained order statistics; in particular it
lies within the range of the data. -/
theorem trimmedMean_mem_Icc {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) :
    trimmedMean m x ∈ Set.Icc (⨅ i, x i) (⨆ i, x i) := by
  classical
  have hbb : BddBelow (Set.range x) := (Set.finite_range x).bddBelow
  have hba : BddAbove (Set.range x) := (Set.finite_range x).bddAbove
  refine ⟨le_trimmedMean_of_forall hm x fun i _ => ?_, trimmedMean_le_of_forall hm x fun i _ => ?_⟩
  · obtain ⟨j, hj⟩ := orderStat_mem_range x i
    rw [← hj]
    exact ciInf_le hbb j
  · obtain ⟨j, hj⟩ := orderStat_mem_range x i
    rw [← hj]
    exact le_ciSup hba j

/-- **The trimmed mean resists `m` replacements** (`MMY §3.2.5`: `m* = [nα]` for the
α-trimmed mean): every retained order statistic of the corrupted sample stays within the
range of the original data, by the replacement-perturbation bound. -/
theorem trimmedMean_resists {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) :
    Resists (trimmedMean m) x m := by
  classical
  have hbb : BddBelow (Set.range x) := (Set.finite_range x).bddBelow
  have hba : BddAbove (Set.range x) := (Set.finite_range x).bddAbove
  refine ⟨max |⨅ i, x i| |⨆ i, x i|, fun y hy => ?_⟩
  have hy' : hammingDist y x ≤ m := by rwa [hammingDist_comm] at hy
  -- A retained rank `i` of `y` is squeezed between the ranks `i - m` and `i + m` of `x`,
  -- both of which are data values of `x`, hence inside its range.
  have hlow : ∀ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m),
      (⨅ i, x i) ≤ orderStat y i := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    have hjlt : (i : ℕ) - m < n := by omega
    have hstep : orderStat x ⟨(i : ℕ) - m, hjlt⟩ ≤ orderStat y i :=
      orderStat_le_of_hammingDist hy (by change (i : ℕ) - m + m ≤ (i : ℕ); omega)
    refine le_trans ?_ hstep
    obtain ⟨j, hj⟩ := orderStat_mem_range x ⟨(i : ℕ) - m, hjlt⟩
    rw [← hj]
    exact ciInf_le hbb j
  have hhigh : ∀ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m),
      orderStat y i ≤ ⨆ i, x i := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    have hjlt : (i : ℕ) + m < n := by omega
    have hstep : orderStat y i ≤ orderStat x ⟨(i : ℕ) + m, hjlt⟩ :=
      orderStat_le_of_hammingDist hy' (by change (i : ℕ) + m ≤ (i : ℕ) + m; omega)
    refine le_trans hstep ?_
    obtain ⟨j, hj⟩ := orderStat_mem_range x ⟨(i : ℕ) + m, hjlt⟩
    rw [← hj]
    exact le_ciSup hba j
  rw [abs_le]
  constructor
  · calc -max |⨅ i, x i| |⨆ i, x i| ≤ -|⨅ i, x i| := neg_le_neg (le_max_left _ _)
      _ ≤ ⨅ i, x i := neg_abs_le _
      _ ≤ trimmedMean m y := le_trimmedMean_of_forall hm y hlow
  · calc trimmedMean m y ≤ ⨆ i, x i := trimmedMean_le_of_forall hm y hhigh
      _ ≤ |⨆ i, x i| := le_abs_self _
      _ ≤ max |⨅ i, x i| |⨆ i, x i| := le_max_right _ _

/-- The `m + 1` lowest-indexed coordinates, the ones replaced in the breakdown witness. -/
private theorem card_le_index_filter {n m : ℕ} (hmn : m < n) :
    (univ.filter (fun i : Fin n => (i : ℕ) ≤ m)).card = m + 1 := by
  classical
  have h : (univ.filter (fun i : Fin n => (i : ℕ) ≤ m)).card = (Finset.range (m + 1)).card := by
    refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      simp only [Finset.mem_range]
      omega
    · intro a _ b _ hab
      exact Fin.val_injective hab
    · intro b hb
      rw [Finset.mem_range] at hb
      exact ⟨⟨b, by omega⟩, by simp only [mem_filter, mem_univ, true_and]; omega, rfl⟩
  rw [h, Finset.card_range]

/-- **`m+1` replacements break the `m`-trimmed mean** (`MMY §3.2.5`): one extreme value
survives the trimming. -/
theorem trimmedMean_breaksUnder {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) :
    BreaksUnder (trimmedMean m) x (m + 1) := by
  classical
  intro M
  have hmn : m < n := by omega
  have hd : (0 : ℝ) < (n : ℝ) - 2 * (m : ℝ) := trim_denom_pos hm
  have hd1 : (1 : ℝ) ≤ (n : ℝ) - 2 * (m : ℝ) := by
    have h1 : ((2 * m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (by omega)
    push_cast at h1
    linarith
  have hdn : (n : ℝ) - 2 * (m : ℝ) ≤ (n : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  -- `L ≤ 0` is a lower bound for every observation, hence (with `C ≥ 0`) for every
  -- coordinate of the corrupted sample.
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = min 0 (⨅ i, x i) := ⟨_, rfl⟩
  have hL0 : L ≤ 0 := hLdef ▸ min_le_left _ _
  have hLx : ∀ j, L ≤ x j := by
    intro j
    have hj := ciInf_le (Set.finite_range x).bddBelow j
    rw [hLdef]
    exact le_trans (min_le_right _ _) hj
  -- The common replacement value, large enough to outweigh the `n - 2m - 1` other terms.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (n : ℝ) * |M| + (n : ℝ) * |L| + 1 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]; positivity
  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun i : Fin n => if (i : ℕ) ≤ m then C else x i :=
    ⟨_, rfl⟩
  have hyi : ∀ i : Fin n, y i = if (i : ℕ) ≤ m then C else x i := by intro i; rw [hy]
  -- Only the `m + 1` coordinates with index `≤ m` are touched.
  have hdist : hammingDist x y ≤ m + 1 := by
    have hsub : hammingDist x y ≤ (univ.filter (fun i : Fin n => (i : ℕ) ≤ m)).card := by
      refine Finset.card_le_card fun i hi => ?_
      have hne : x i ≠ y i := by simpa using (Finset.mem_filter.mp hi).2
      simp only [mem_filter, mem_univ, true_and]
      by_contra hgt
      exact hne (by rw [hyi i, if_neg hgt])
    rwa [card_le_index_filter hmn] at hsub
  -- Those `m + 1` coordinates all carry the value `C`.
  have hCcount : m + 1 ≤ (univ.filter (fun j : Fin n => C ≤ y j)).card := by
    rw [← card_le_index_filter (n := n) hmn]
    refine Finset.card_le_card fun i hi => ?_
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [hyi i, if_pos hi]
  -- The retained rank `n - m - 1` therefore carries at least `C`.
  have hi0 : n - m - 1 < n := by omega
  have hi0mem : (⟨n - m - 1, hi0⟩ : Fin n)
      ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m) := by
    simp only [mem_filter, mem_univ, true_and]
    omega
  have hbig : C ≤ orderStat y ⟨n - m - 1, hi0⟩ := by
    refine le_orderStat_of_card_le y ⟨n - m - 1, hi0⟩ C ?_
    have hval : ((⟨n - m - 1, hi0⟩ : Fin n) : ℕ) = n - m - 1 := rfl
    rw [hval]
    omega
  -- Every rank of `y` is bounded below by `L`, so the remaining retained terms cannot
  -- cancel the large one.
  have hylow : ∀ i : Fin n, L ≤ orderStat y i := by
    intro i
    obtain ⟨j, hj⟩ := orderStat_mem_range y i
    rw [← hj, hyi j]
    split
    · linarith
    · exact hLx j
  have hsum : ((n : ℝ) - 2 * (m : ℝ) - 1) * L + C
      ≤ ∑ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m), orderStat y i := by
    rw [← Finset.add_sum_erase _ (orderStat y) hi0mem]
    have hcard : (((univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m)).erase
        ⟨n - m - 1, hi0⟩).card : ℝ) = (n : ℝ) - 2 * (m : ℝ) - 1 := by
      have h1 : n - 2 * m - 1 = n - (2 * m + 1) := by omega
      rw [Finset.card_erase_of_mem hi0mem, card_trim_filter, h1,
        Nat.cast_sub (by omega : 2 * m + 1 ≤ n)]
      push_cast
      ring
    have hrest := Finset.card_nsmul_le_sum
      ((univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m)).erase ⟨n - m - 1, hi0⟩)
      (orderStat y) L fun i _ => hylow i
    rw [nsmul_eq_mul, hcard] at hrest
    linarith
  refine ⟨y, hdist, lt_of_lt_of_le ?_ (le_abs_self _)⟩
  simp only [trimmedMean]
  rw [lt_div_iff₀ hd]
  nlinarith [hsum, hC, hL0, hd1, hdn, abs_nonneg M, abs_nonneg L,
    mul_nonneg (sub_nonneg.mpr (le_abs_self M)) hd.le,
    mul_nonneg (abs_nonneg M) (by linarith : (0 : ℝ) ≤ (n : ℝ) - ((n : ℝ) - 2 * (m : ℝ))),
    mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2 * (m : ℝ) - 1)
      (by linarith [neg_abs_le L] : (0 : ℝ) ≤ L + |L|),
    mul_nonneg (abs_nonneg L)
      (by linarith : (0 : ℝ) ≤ (n : ℝ) - ((n : ℝ) - 2 * (m : ℝ) - 1))]

/-- **The breakdown count of the `m`-trimmed mean is exactly `m`**
(`MMY §3.2.5`: `m* = [nα]`). -/
theorem trimmedMean_breakdownCount {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) :
    breakdownCount (trimmedMean m) x = m :=
  breakdownCount_eq_of_resists_of_breaksUnder (by omega) (trimmedMean_resists hm x)
    (trimmedMean_breaksUnder hm x)

end StatLean.RobustStatistics
