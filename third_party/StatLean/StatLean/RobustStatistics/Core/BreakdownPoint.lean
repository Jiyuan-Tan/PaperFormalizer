module
public import Mathlib.InformationTheory.Hamming
public import StatLean.PointEstimation.Equivariance.Defs

@[expose] public section

/-!
# Finite-sample replacement breakdown point

The replacement finite-sample breakdown point of an estimator at a data set `x` is the
largest fraction `m*/n` of observations that can be replaced by arbitrary values while the
estimate stays bounded (`MMY §3.2.5`, eq. (3.24)–(3.25); Donoho–Huber 1983). Replacement
contamination is measured by the Hamming distance `hammingDist x y = #{i : xᵢ ≠ yᵢ}`
(Mathlib's `hammingDist`), which must not be conflated with the population ε-mixture of
`Core/Contamination.lean` — the two contamination models get separate primitives.

* `Resists T x m` — the estimate stays uniformly bounded over all `m`-replacements of `x`.
* `BreaksUnder T x m` — some `m`-replacement drives `|T|` beyond any bound.
* `breakdownCount T x` — `m* = max {m ≤ n : Resists T x m}` (`MMY` eq. (3.25)).
* `breakdownPoint T x` — `ε*_n = m*/n` (`MMY` eq. (3.24)).
* `locEquivariant_not_resists`, `locEquivariant_breakdownCount_le` — no location-equivariant
  estimator resists `⌈n/2⌉` replacements: `m* ≤ ⌊(n-1)/2⌋` (`MMY` eq. (3.26), §3.8.2).

**Scope (location parameters).** The parameter space is `ℝ`, so "breakdown" means
`|T y| → ∞`; the boundary-of-`Θ` refinement needed for scale parameters (implosion to `0`)
is deferred to the scale round.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §3.2.5 (eq.
(3.24)–(3.26)), §3.8.2.

**Bibliographic comments.** D. L. Donoho and P. J. Huber, "The notion of breakdown point,"
in *A Festschrift for Erich L. Lehmann*, Wadsworth, 1983, pp. 157–184.
-/

namespace StatLean.RobustStatistics

variable {n : ℕ} (T : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)

/-- **Resistance to `m` replacements** (`MMY §3.2.5`): the estimate stays uniformly
bounded when at most `m` observations of `x` are replaced by arbitrary values. -/
def Resists (m : ℕ) : Prop :=
  ∃ M : ℝ, ∀ y : Fin n → ℝ, hammingDist x y ≤ m → |T y| ≤ M

/-- **Breakdown under `m` replacements** (`MMY §3.2.5`): replacing at most `m`
observations can drive the estimate beyond any bound. -/
def BreaksUnder (m : ℕ) : Prop :=
  ∀ M : ℝ, ∃ y : Fin n → ℝ, hammingDist x y ≤ m ∧ M < |T y|

variable {T x}

/-- Breakdown is the negation of resistance. -/
theorem breaksUnder_iff_not_resists {m : ℕ} : BreaksUnder T x m ↔ ¬Resists T x m := by
  constructor
  · rintro h ⟨M, hM⟩
    obtain ⟨y, hy, hy'⟩ := h M
    exact absurd (hM y hy) (not_le.mpr hy')
  · intro h M
    by_contra hc
    push Not at hc
    exact h ⟨M, hc⟩

/-- Resistance is antitone in the number of allowed replacements. -/
theorem Resists.anti {m m' : ℕ} (hmm' : m ≤ m') (h : Resists T x m') : Resists T x m := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun y hy => hM y (hy.trans hmm')⟩

/-- Every estimator resists `0` replacements. -/
theorem resists_zero : Resists T x 0 := by
  refine ⟨|T x|, fun y hy => ?_⟩
  have hxy : x = y := hammingDist_eq_zero.mp (Nat.le_zero.mp hy)
  rw [← hxy]

variable (T x)

/-- The **breakdown count** `m*` (`MMY §3.2.5`, eq. (3.25)): the largest number `m ≤ n`
of replacements the estimator resists at `x`. -/
noncomputable def breakdownCount : ℕ :=
  sSup {m | m ≤ n ∧ Resists T x m}

/-- The **finite-sample replacement breakdown point** `ε*_n = m*/n`
(`MMY §3.2.5`, eq. (3.24)). Junk value `0` when `n = 0`. -/
noncomputable def breakdownPoint : ℝ :=
  breakdownCount T x / n

variable {T x}

/-- The set of resisted replacement numbers is nonempty (`0` belongs to it). -/
private theorem resistsSet_nonempty : {m | m ≤ n ∧ Resists T x m}.Nonempty :=
  ⟨0, Nat.zero_le n, resists_zero⟩

/-- The set of resisted replacement numbers is bounded above by the sample size. -/
private theorem resistsSet_bddAbove : BddAbove {m | m ≤ n ∧ Resists T x m} :=
  ⟨n, fun _ hm => hm.1⟩

/-- The estimator resists its breakdown count. -/
theorem resists_breakdownCount : Resists T x (breakdownCount T x) :=
  (Nat.sSup_mem (resistsSet_nonempty (T := T) (x := x))
    (resistsSet_bddAbove (T := T) (x := x))).2

/-- Any resisted replacement number (at most `n`) is below the breakdown count. -/
theorem le_breakdownCount {m : ℕ} (hm : m ≤ n) (h : Resists T x m) :
    m ≤ breakdownCount T x :=
  le_csSup (resistsSet_bddAbove (T := T) (x := x)) ⟨hm, h⟩

/-- The breakdown count is at most the sample size. -/
theorem breakdownCount_le_card : breakdownCount T x ≤ n :=
  csSup_le (resistsSet_nonempty (T := T) (x := x)) fun _ hb => hb.1

/-- Characterization by a witness pair: resists `m`, breaks under `m + 1`. -/
theorem breakdownCount_eq_of_resists_of_breaksUnder {m : ℕ} (hm : m ≤ n)
    (hres : Resists T x m) (hbreak : BreaksUnder T x (m + 1)) :
    breakdownCount T x = m := by
  refine le_antisymm ?_ (le_breakdownCount hm hres)
  by_contra hlt
  push Not at hlt
  exact breaksUnder_iff_not_resists.mp hbreak
    (resists_breakdownCount.anti (Nat.succ_le_of_lt hlt))

/-- Breaking under one replacement forces breakdown count `0`. -/
theorem breakdownCount_eq_zero_of_breaksUnder_one (h : BreaksUnder T x 1) :
    breakdownCount T x = 0 :=
  breakdownCount_eq_of_resists_of_breaksUnder (Nat.zero_le n) resists_zero
    (by simpa using h)

/-! ### The maximal breakdown of location-equivariant estimators (`MMY` eq. (3.26)) -/

/-- **No location-equivariant estimator resists `⌈n/2⌉` replacements** (`MMY §3.8.2`,
finite-sample form): if `n ≤ 2m`, a resisted `m`-replacement bound would contradict shift
equivariance, since a data set can be driven toward both `x` and an arbitrarily large
shift of `x` simultaneously. -/
theorem locEquivariant_not_resists (hT : PointEstimation.IsLocEquivariant T)
    (hn : 0 < n) {m : ℕ} (hm : n ≤ 2 * m) : ¬Resists T x m := by
  classical
  rintro ⟨M, hM⟩
  -- A bound on all `m`-replacements bounds `|T x|` itself, so `M ≥ 0`.
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM x (by simp))
  -- The shift used to separate the two halves of the sample.
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * M + 1 := ⟨_, rfl⟩
  -- `w` agrees with `x` on the first `m` coordinates and is shifted down elsewhere;
  -- `w + c • 1` agrees with `x` off the first `m` coordinates.
  obtain ⟨w, hwdef⟩ : ∃ w : Fin n → ℝ, w = fun i : Fin n => if (i : ℕ) < m then x i else x i - c :=
    ⟨_, rfl⟩
  have hwi : ∀ i : Fin n, w i = if (i : ℕ) < m then x i else x i - c := by
    intro i; simp only [hwdef]
  have hzi : ∀ i : Fin n, (w + c • (1 : Fin n → ℝ)) i = if (i : ℕ) < m then x i + c else x i := by
    intro i
    by_cases h : (i : ℕ) < m <;> simp [hwi i, h]
  -- Hamming distances from `x`, bounded by counting coordinates.
  have hcard : ∀ (y : Fin n → ℝ) (s : Finset (Fin n)), (∀ i, x i ≠ y i → i ∈ s) →
      hammingDist x y ≤ s.card := by
    intro y s hs
    refine Finset.card_le_card fun i hi => hs i ?_
    simpa using (Finset.mem_filter.mp hi).2
  have hdw : hammingDist x w ≤ m := by
    refine le_trans (hcard w (Finset.univ.filter fun i : Fin n => m ≤ (i : ℕ)) ?_) ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hlt
      exact hi (by simp [hwi i, Nat.lt_of_not_le hlt])
    · have hinj : (Finset.univ.filter fun i : Fin n => m ≤ (i : ℕ)).card ≤
          (Finset.Ico m n).card :=
        Finset.card_le_card_of_injOn (fun i : Fin n => (i : ℕ))
          (fun i hi => by
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi
            simp [hi, i.isLt])
          (fun i _ j _ h => Fin.val_injective h)
      simp only [Nat.card_Ico] at hinj
      omega
  have hdz : hammingDist x (w + c • (1 : Fin n → ℝ)) ≤ m := by
    refine le_trans (hcard _ (Finset.univ.filter fun i : Fin n => (i : ℕ) < m) ?_) ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hge
      exact hi (by simp [hzi i, hge])
    · have hinj : (Finset.univ.filter fun i : Fin n => (i : ℕ) < m).card ≤
          (Finset.range m).card :=
        Finset.card_le_card_of_injOn (fun i : Fin n => (i : ℕ))
          (fun i hi => by
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi
            simp [hi])
          (fun i _ j _ h => Fin.val_injective h)
      simpa using hinj
  -- Equivariance turns the two bounds into `c ≤ 2M`, contradicting `c = 2M + 1`.
  have hshift : T (w + c • (1 : Fin n → ℝ)) = T w + c := hT c w
  have hb1 : |T w| ≤ M := hM w hdw
  have hb2 : |T (w + c • (1 : Fin n → ℝ))| ≤ M := hM _ hdz
  have e1 := le_abs_self (T (w + c • (1 : Fin n → ℝ)))
  have e2 := neg_le_abs (T w)
  linarith

/-- **The maximal finite-sample breakdown bound** (`MMY §3.2.5`, eq. (3.26)): every
location-equivariant estimator has `m* ≤ ⌊(n-1)/2⌋`. The sample median attains this bound
(`LocationScale/MedianBreakdown.lean`). -/
theorem locEquivariant_breakdownCount_le (hT : PointEstimation.IsLocEquivariant T)
    (hn : 0 < n) : breakdownCount T x ≤ (n - 1) / 2 := by
  refine csSup_le (resistsSet_nonempty (T := T) (x := x)) fun b hb => ?_
  by_contra hlt
  push Not at hlt
  exact locEquivariant_not_resists hT hn (by omega) hb.2

end StatLean.RobustStatistics
