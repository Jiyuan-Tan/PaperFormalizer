module
public import StatLean.RobustStatistics.Core.BreakdownPoint
public import StatLean.RobustStatistics.LocationScale.MAD
public import StatLean.RobustStatistics.LocationScale.MedianBreakdown
public import StatLean.RobustStatistics.LocationScale.Mean

@[expose] public section

/-!
# Finite-sample breakdown of dispersion estimators — the SD implodes never but explodes
# at once; the MAD resists half

For a dispersion estimator the parameter space is `Θ = (0, ∞)`, so the finite-sample
breakdown notion (`MMY §3.2.5`, Definition (3.25)) must guard *both* boundary pieces:
a corrupted sample breaks the estimator if it can be driven to `∞` (**explosion**) *or*
to `0` (**implosion**). This file gives the dispersion analogue of Round-1's
`Resists`/`breakdownCount` lattice and the two classical verdicts (`MMY §3.2.2`,
Problem 3.3, finite-sample form):

* the sample standard deviation breaks under a **single** replacement (`ε* = 0`);
* the sample MAD (odd `n = 2k+1`, distinct data) resists `k − 1` replacements and
  implodes under `k` — duplicating `k` values at one data point collapses a majority of
  the absolute deviations to `0` — so its breakdown count is exactly `k − 1` and its
  breakdown point tends to `1/2`.

* `DispersionResists`, `DispersionBreaksUnder`, `dispersionBreakdownCount` — the
  implosion-aware lattice (mirroring `Core/BreakdownPoint`).
* `sampleSD` and `sampleSD_breaksUnder_one` / `sampleSD_dispersionBreakdownCount`.
* `sampleMAD_implodes_under` / `sampleMAD_dispersionResists` /
  `sampleMAD_dispersionBreakdownCount`.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera,
*Robust Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.)
§2.6 (the SD and the dispersion conditions (2.58)), §3.2.2 ("the BPs of the SD, the MAD
and the IQR are 0, 1/2 and 1/4", Problem 3.3), §3.2.5 (the replacement FBP (3.24)–
(3.25) and its boundary-aware reading for `Θ = (0, ∞)`); the FBP notion is from
Donoho–Huber (1983).

**Bibliographic comments.** The classical breakdown verdicts — SD `0`, MAD `1/2`, IQR
`1/4` — trace to Hampel's advocacy of the median deviation ("The influence curve and its
role in robust estimation," *J. Amer. Statist. Assoc.* **69** (1974), 383–393) and the
finite-sample framework of Donoho and Huber (1983); efficient high-breakdown alternatives
to the MAD are Rousseeuw and Croux, *J. Amer. Statist. Assoc.* **88** (1993), 1273–1283.
-/

open MeasureTheory Finset

namespace StatLean.RobustStatistics

open StatLean.MultipleTesting

variable {n : ℕ}

/-- **Dispersion resistance** (`MMY §3.2.5`, Definition (3.25) read at `Θ = (0, ∞)`):
`m` replacements cannot drive `S` to the boundary — there are `0 < lo ≤ hi` with
`S y ∈ [lo, hi]` for every `y` within Hamming distance `m` of `x`. Note `Resists` of
`Core/BreakdownPoint` guards only `∞`; a dispersion estimator must also stay away from
`0` (implosion). -/
def DispersionResists (S : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (m : ℕ) : Prop :=
  ∃ lo hi : ℝ, 0 < lo ∧
    ∀ y : Fin n → ℝ, hammingDist x y ≤ m → S y ∈ Set.Icc lo hi

/-- `m` replacements break the dispersion estimator: explosion or implosion. -/
def DispersionBreaksUnder (S : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (m : ℕ) : Prop :=
  ¬DispersionResists S x m

/-- Resistance is antitone in the contamination budget. -/
theorem DispersionResists.anti {S : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {m m' : ℕ}
    (hmm' : m ≤ m') (h : DispersionResists S x m') : DispersionResists S x m := by
  obtain ⟨lo, hi, hlo, H⟩ := h
  exact ⟨lo, hi, hlo, fun y hy => H y (hy.trans hmm')⟩

/-- Zero replacements are resisted exactly when the uncorrupted value is off the
boundary (`0 < S x`) — unlike the location lattice, this is *not* free (a constant
sample already has `MAD = 0`). -/
theorem dispersionResists_zero {S : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : 0 < S x) : DispersionResists S x 0 := by
  refine ⟨S x, S x, h, fun y hy => ?_⟩
  have hxy : x = y := hammingDist_eq_zero.mp (Nat.le_zero.mp hy)
  rw [← hxy]
  exact ⟨le_rfl, le_rfl⟩

/-- **The dispersion breakdown count** `m* = max{m ≤ n : DispersionResists S x m}`
(`MMY (3.25)`, boundary-aware form); junk value `0` when even `m = 0` is not resisted. -/
noncomputable def dispersionBreakdownCount (S : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℕ :=
  sSup {m | m ≤ n ∧ DispersionResists S x m}

/-- The two-sided characterization of the dispersion breakdown count (mirror of
Round-1's `breakdownCount_eq_of_resists_of_breaksUnder`). -/
theorem dispersionBreakdownCount_eq_of_resists_of_breaksUnder
    {S : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {m : ℕ} (hm : m ≤ n)
    (hres : DispersionResists S x m) (hbrk : DispersionBreaksUnder S x (m + 1)) :
    dispersionBreakdownCount S x = m := by
  have hne : {m | m ≤ n ∧ DispersionResists S x m}.Nonempty := ⟨m, hm, hres⟩
  have hbdd : BddAbove {m | m ≤ n ∧ DispersionResists S x m} := ⟨n, fun _ hb => hb.1⟩
  have hmem := Nat.sSup_mem hne hbdd
  refine le_antisymm ?_ (le_csSup hbdd ⟨hm, hres⟩)
  by_contra hlt
  push Not at hlt
  exact hbrk (hmem.2.anti (Nat.succ_le_of_lt hlt))

/-- **The sample standard deviation** `SD(x) = √((1/n) ∑ (xᵢ − x̄)²)` (`MMY §2.6`,
with the `1/n` normalization in place of the book's `1/(n−1)` — the breakdown
statements are unaffected by the constant factor). -/
noncomputable def sampleSD (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (sampleMean fun i => (x i - sampleMean x) ^ 2)

/-- The sample mean is (fully) scale equivariant — the companion of
`sampleMean_locEquivariant` needed for the SD's `|c|`-equivariance. -/
private theorem sampleMean_const_mul (c : ℝ) (x : Fin n → ℝ) :
    sampleMean (fun i => c * x i) = c * sampleMean x := by
  simp only [sampleMean, ← Finset.mul_sum, mul_div_assoc]

/-- The SD satisfies the dispersion conditions (`MMY (2.58)`): shift invariance and
absolute-scale equivariance. -/
theorem sampleSD_isDispersionEstimator (hn : n ≠ 0) :
    IsDispersionEstimator (sampleSD (n := n)) := by
  constructor
  · -- shift invariance: the mean shifts along, so the residuals are unchanged
    intro a x
    have hmean : sampleMean (x + a • (1 : Fin n → ℝ)) = sampleMean x + a :=
      sampleMean_locEquivariant (Nat.pos_of_ne_zero hn) a x
    have hdev : (fun i => ((x + a • (1 : Fin n → ℝ)) i
        - sampleMean (x + a • (1 : Fin n → ℝ))) ^ 2)
        = fun i => (x i - sampleMean x) ^ 2 := by
      funext i
      rw [hmean]
      have hxi : (x + a • (1 : Fin n → ℝ)) i = x i + a := by simp
      rw [hxi]
      ring_nf
    rw [sampleSD, sampleSD, hdev]
  · -- scale equivariance: `c²` comes out of the mean and `√(c² ·) = |c| √·`
    intro c x
    have hsmul : (c • x) = fun i => c * x i := by funext i; simp
    have hmean : sampleMean (c • x) = c * sampleMean x := by
      rw [hsmul]; exact sampleMean_const_mul c x
    have hdev : (fun i => ((c • x) i - sampleMean (c • x)) ^ 2)
        = fun i => c ^ 2 * (x i - sampleMean x) ^ 2 := by
      funext i
      rw [hmean, hsmul]
      ring
    rw [sampleSD, sampleSD, hdev, sampleMean_const_mul,
      Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **One replacement explodes the SD** (`MMY §3.2.2`, "the BPs of the SD … are 0",
finite-sample form): a single arbitrarily-large replacement drives the SD beyond any
bound (`n ≥ 2`, so the corrupted mean cannot chase the outlier). -/
theorem sampleSD_breaksUnder_one (hn : 2 ≤ n) (x : Fin n → ℝ) :
    DispersionBreaksUnder sampleSD x 1 := by
  classical
  rintro ⟨lo, hi, hlo, H⟩
  have hn0 : 0 < n := by omega
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  -- replace the single coordinate `i₀` by the value making its residual exactly `A`
  set S : ℝ := ∑ i ∈ Finset.univ \ {i₀}, x i with hS
  set A : ℝ := (n:ℝ) * (|hi| + 1) with hA
  set M : ℝ := ((n:ℝ) * A + S) / ((n:ℝ) - 1) with hM
  set y : Fin n → ℝ := Function.update x i₀ M with hy
  have hdist : hammingDist x y ≤ 1 := by
    refine le_trans (Finset.card_le_card (t := ({i₀} : Finset (Fin n))) fun i hi' => ?_) (by simp)
    by_cases h : i = i₀
    · simp [h]
    · exact absurd (Function.update_of_ne h M x).symm
        (by simpa [hy] using (Finset.mem_filter.mp hi').2)
  have hsum : ∑ i, y i = M + S := Finset.sum_update_of_mem (Finset.mem_univ i₀) x M
  have hmean : sampleMean y = (M + S) / n := by rw [sampleMean, hsum]
  have hMn : M * ((n:ℝ) - 1) = (n:ℝ) * A + S := by rw [hM]; field_simp
  -- with `n ≥ 2` the corrupted mean cannot chase the outlier: the residual is `A`
  have hd : y i₀ - sampleMean y = A := by
    have hyi : y i₀ = M := by simp [hy]
    rw [hyi, hmean]
    field_simp
    nlinarith [hMn]
  have hterm : (y i₀ - sampleMean y) ^ 2 ≤ ∑ i, (y i - sampleMean y) ^ 2 :=
    Finset.single_le_sum (f := fun i => (y i - sampleMean y) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
  have hvar : A ^ 2 / (n:ℝ) ≤ sampleMean fun i => (y i - sampleMean y) ^ 2 := by
    rw [sampleMean, ← hd]
    gcongr
  have ha : (0:ℝ) ≤ |hi| := abs_nonneg hi
  have hkey : |hi| ^ 2 < A ^ 2 / (n:ℝ) := by
    rw [lt_div_iff₀ hnpos, hA]
    have h1 : |hi| ^ 2 < (n:ℝ) * (|hi| + 1) ^ 2 := by nlinarith
    calc |hi| ^ 2 * (n:ℝ) < ((n:ℝ) * (|hi| + 1) ^ 2) * (n:ℝ) := by nlinarith
      _ = ((n:ℝ) * (|hi| + 1)) ^ 2 := by ring
  have hlt : |hi| < sampleSD y := by
    rw [sampleSD]
    exact (Real.lt_sqrt (abs_nonneg hi)).2 (lt_of_lt_of_le hkey hvar)
  have := (H y hdist).2
  linarith [le_abs_self hi]

/-- The SD's dispersion breakdown count is `0` (for data with `SD > 0`). -/
theorem sampleSD_dispersionBreakdownCount (hn : 2 ≤ n) {x : Fin n → ℝ}
    (hx : 0 < sampleSD x) : dispersionBreakdownCount sampleSD x = 0 :=
  dispersionBreakdownCount_eq_of_resists_of_breaksUnder (Nat.zero_le n)
    (dispersionResists_zero hx) (by simpa using sampleSD_breaksUnder_one hn x)

/-- **`k` replacements implode the MAD** (`MMY §3.2.2` + Problem 3.3, finite-sample
form, `n = 2k+1`): replacing `k` coordinates by the value of a remaining data point
creates `k + 1` copies of one value; the corrupted median is that value, a majority of
the absolute deviations vanish, and the MAD is `0`.

**Note on `hinj`.** Distinctness is *not* used by the implosion argument (duplicating
`x i₀` onto `k` coordinates collapses the MAD for arbitrary data); the hypothesis is kept
because the breakdown-count theorem pairs this verdict with
`sampleMAD_dispersionResists`, where distinctness is essential. -/
theorem sampleMAD_implodes_under {k : ℕ} (hn : n = 2 * k + 1) (hk : 1 ≤ k)
    {x : Fin n → ℝ} (hinj : Function.Injective x) :
    DispersionBreaksUnder sampleMAD x k := by
  classical
  rintro ⟨lo, hi, hlo, H⟩
  have hkn : k < n := by omega
  have hn0 : 0 < n := by omega
  set i₀ : Fin n := ⟨0, hn0⟩ with hi₀
  set K : Fin n := ⟨k, hkn⟩ with hK
  -- duplicate the value `x i₀` onto the `k` coordinates `1 ≤ j ≤ k`
  set y : Fin n → ℝ := fun j => if (j : ℕ) ≤ k then x i₀ else x j with hy
  have hcopy : ∀ j : Fin n, j ≤ K → y j = x i₀ := by
    intro j hj
    have hjk : (j : ℕ) ≤ k := hj
    simp [hy, hjk]
  have hdist : hammingDist x y ≤ k := by
    have hsub : (univ.filter fun j => x j ≠ y j) ⊆ (Finset.Iic K).erase i₀ := by
      intro j hj
      rw [mem_filter] at hj
      have hjk : (j : ℕ) ≤ k := by
        by_contra hc
        exact hj.2 (by simp [hy, hc])
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_Iic.2 hjk⟩
      intro hje
      exact hj.2 (by simp [hy, hje, hi₀])
    calc hammingDist x y ≤ ((Finset.Iic K).erase i₀).card := Finset.card_le_card hsub
      _ = k := by
          rw [Finset.card_erase_of_mem (Finset.mem_Iic.2 (by simp [hi₀, hK])), Fin.card_Iic]
          simp [hK]
  -- `k + 1` copies of `x i₀` pin the corrupted median to `x i₀`
  have hcard_le : k + 1 ≤ (univ.filter fun j => y j ≤ x i₀).card := by
    have hsub : Finset.Iic K ⊆ univ.filter fun j => y j ≤ x i₀ := fun j hj =>
      mem_filter.2 ⟨mem_univ j, le_of_eq (hcopy j (Finset.mem_Iic.1 hj))⟩
    have h2 := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h2
    simpa [hK] using h2
  have hcard_ge : n - k ≤ (univ.filter fun j => x i₀ ≤ y j).card := by
    have hsub : Finset.Iic K ⊆ univ.filter fun j => x i₀ ≤ y j := fun j hj =>
      mem_filter.2 ⟨mem_univ j, ge_of_eq (hcopy j (Finset.mem_Iic.1 hj))⟩
    have h2 := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h2
    simp only [hK] at h2
    omega
  have hmed : sampleMedian y = x i₀ := by
    rw [sampleMedian_odd hn]
    exact le_antisymm (orderStat_le_of_card_le y ⟨k, hkn⟩ (x i₀) (by simpa using hcard_le))
      (le_orderStat_of_card_le y ⟨k, hkn⟩ (x i₀) (by simpa using hcard_ge))
  -- a majority of the absolute deviations vanish, so the MAD implodes to `0`
  have hmad : sampleMAD y = 0 := by
    refine le_antisymm ?_ (sampleMAD_nonneg y)
    rw [sampleMAD, hmed, sampleMedian_odd hn]
    refine orderStat_le_of_card_le _ ⟨k, hkn⟩ 0 ?_
    have hsub : Finset.Iic K ⊆ univ.filter fun j => |y j - x i₀| ≤ 0 := by
      intro j hj
      refine mem_filter.2 ⟨mem_univ j, ?_⟩
      rw [hcopy j (Finset.mem_Iic.1 hj), sub_self, abs_zero]
    have h2 := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h2
    simpa [hK] using h2
  have hge := (H y hdist).1
  rw [hmad] at hge
  linarith

/-- **The MAD resists `k − 1` replacements** (`MMY §3.2.2` + Problem 3.3, finite-sample
form, `n = 2k+1`, distinct data): with at most `k − 1` replacements, at most `k` of the
`n` values can coincide within half the minimal gap of the original data, so the
corrupted median-of-absolute-deviations stays above `(min gap)/2 > 0`; boundedness above
follows from the Round-1 order-statistic perturbation bricks. -/
theorem sampleMAD_dispersionResists {k : ℕ} (hn : n = 2 * k + 1) (hk : 1 ≤ k)
    {x : Fin n → ℝ} (hinj : Function.Injective x) :
    DispersionResists sampleMAD x (k - 1) := by
  classical
  have hkn : k < n := by omega
  have hn0 : 0 < n := by omega
  -- the minimal gap of the (distinct) data
  set pairs : Finset (Fin n × Fin n) := univ.filter (fun p => p.1 ≠ p.2) with hpairs
  have hpne : pairs.Nonempty := by
    refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
    rw [hpairs, mem_filter]
    exact ⟨mem_univ _, by simp [Fin.ext_iff]⟩
  set g : ℝ := (pairs.image fun p => |x p.1 - x p.2|).min' (hpne.image _) with hg
  have hgmem : g ∈ pairs.image fun p => |x p.1 - x p.2| := Finset.min'_mem _ _
  have hgpos : 0 < g := by
    rw [Finset.mem_image] at hgmem
    obtain ⟨p, hp, hpg⟩ := hgmem
    rw [hpairs, mem_filter] at hp
    rw [← hpg]
    exact abs_pos.2 (sub_ne_zero.2 fun hc => hp.2 (hinj hc))
  have hgle : ∀ i j : Fin n, i ≠ j → g ≤ |x i - x j| := by
    intro i j hij
    refine Finset.min'_le _ _ (Finset.mem_image.2 ⟨(i, j), ?_, rfl⟩)
    rw [hpairs, mem_filter]
    exact ⟨mem_univ _, hij⟩
  -- the window the corrupted median lives in (Round-1 median resistance)
  set m₀ : ℝ := ⨅ i, x i with hm₀
  set M₀ : ℝ := ⨆ i, x i with hM₀
  have hxlo : ∀ j, m₀ ≤ x j := fun j => ciInf_le (Set.Finite.bddBelow (Set.finite_range x)) j
  have hxhi : ∀ j, x j ≤ M₀ := fun j => le_ciSup (Set.Finite.bddAbove (Set.finite_range x)) j
  refine ⟨g / 2, M₀ - m₀, by linarith, fun y hy => ?_⟩
  have hyk : hammingDist x y ≤ k := le_trans hy (by omega)
  set t : ℝ := sampleMedian y with ht
  have htmem : t ∈ Set.Icc m₀ M₀ := sampleMedian_mem_Icc_of_hammingDist hn hyk
  set D : Finset (Fin n) := univ.filter (fun j => x j ≠ y j) with hD
  have hDcard : D.card ≤ k - 1 := hy
  set d : Fin n → ℝ := fun j => |y j - t| with hd
  have hMAD : sampleMAD y = orderStat d ⟨k, hkn⟩ := by
    rw [sampleMAD, sampleMedian_odd hn]
  constructor
  · -- at most `k` deviations can be below `g/2`: the `≤ k−1` replaced ones plus at most
    -- ONE surviving original (two would sit within `g` of each other)
    set Bad : Finset (Fin n) := univ.filter (fun j => d j < g / 2) with hBad
    have hBadD : (Bad \ D).card ≤ 1 := by
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      rw [Finset.mem_sdiff, hBad, mem_filter, hD, mem_filter] at ha hb
      have hae : x a = y a := by by_contra hc; exact ha.2 ⟨mem_univ a, hc⟩
      have hbe : x b = y b := by by_contra hc; exact hb.2 ⟨mem_univ b, hc⟩
      by_contra hab
      have h1 : |y a - t| < g / 2 := ha.1.2
      have h2 : |y b - t| < g / 2 := hb.1.2
      have h3 : |x a - x b| < g := by
        rw [hae, hbe]
        calc |y a - y b| = |(y a - t) - (y b - t)| := by ring_nf
          _ ≤ |y a - t| + |y b - t| := abs_sub _ _
          _ < g := by linarith
      exact absurd (hgle a b hab) (not_le.2 h3)
    have hBadcard : Bad.card ≤ k := by
      have hsub : Bad ⊆ (Bad \ D) ∪ D := by
        intro a ha
        by_cases hc : a ∈ D
        · exact Finset.mem_union_right _ hc
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨ha, hc⟩)
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
    have hsplit : Bad.card + (univ.filter fun j => ¬ (d j < g / 2)).card = n := by
      rw [hBad]
      simpa using Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (Fin n))) (p := fun j => d j < g / 2)
    have hgood : n - k ≤ (univ.filter fun j => g / 2 ≤ d j).card := by
      have hcongr : (univ.filter fun j => ¬ (d j < g / 2))
          = univ.filter fun j => g / 2 ≤ d j := by
        apply Finset.filter_congr
        intro j _
        simp [not_lt]
      rw [← hcongr]
      omega
    rw [hMAD]
    exact le_orderStat_of_card_le d ⟨k, hkn⟩ (g / 2) (by simpa using hgood)
  · -- at least `k+2` deviations come from surviving data points, all `≤ M₀ − m₀`
    have hsurv : ∀ j : Fin n, j ∉ D → d j ≤ M₀ - m₀ := by
      intro j hj
      have hxy : x j = y j := by
        by_contra hc
        exact hj (by rw [hD, mem_filter]; exact ⟨mem_univ j, hc⟩)
      rw [hd]
      simp only
      rw [← hxy, abs_le]
      exact ⟨by linarith [hxlo j, htmem.2], by linarith [hxhi j, htmem.1]⟩
    have hsplit : D.card + (univ.filter fun j => ¬ (x j ≠ y j)).card = n := by
      rw [hD]
      simpa using Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (Fin n))) (p := fun j => x j ≠ y j)
    have hsub : (univ.filter fun j => ¬ (x j ≠ y j)) ⊆ univ.filter fun j => d j ≤ M₀ - m₀ := by
      intro j hj
      rw [mem_filter] at hj
      refine mem_filter.2 ⟨mem_univ j, hsurv j ?_⟩
      rw [hD, mem_filter]
      rintro ⟨-, hne⟩
      exact hj.2 hne
    have hcard := Finset.card_le_card hsub
    rw [hMAD]
    refine orderStat_le_of_card_le d ⟨k, hkn⟩ (M₀ - m₀) ?_
    simp only []
    omega

/-- **The dispersion breakdown count of the MAD is exactly `k − 1`** (`MMY §3.2.2` +
Problem 3.3, finite-sample form): `(k−1)/(2k+1) → 1/2`, the asymptotic MAD breakdown
point. Note the contrast with the median's location breakdown count `k`
(`LocationScale/MedianBreakdown.lean`): the MAD pays one replacement earlier because
implosion — impossible for a location estimator — binds first. -/
theorem sampleMAD_dispersionBreakdownCount {k : ℕ} (hn : n = 2 * k + 1) (hk : 1 ≤ k)
    {x : Fin n → ℝ} (hinj : Function.Injective x) :
    dispersionBreakdownCount sampleMAD x = k - 1 :=
  dispersionBreakdownCount_eq_of_resists_of_breaksUnder (by omega)
    (sampleMAD_dispersionResists hn hk hinj)
    (by rw [show k - 1 + 1 = k by omega]; exact sampleMAD_implodes_under hn hk hinj)

end StatLean.RobustStatistics
