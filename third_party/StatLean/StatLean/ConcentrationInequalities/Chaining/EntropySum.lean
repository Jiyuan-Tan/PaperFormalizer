module
public import StatLean.ConcentrationInequalities.Chaining.EntropyIntegrand
public import StatLean.ConcentrationInequalities.Chaining.DyadicNets
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Dyadic entropy sum and Dudley integral carriers

The dyadic entropy sum of HDP Eq. (8.2),
$$ \Sigma(T) \;=\; \sum_{k \in \mathbb{Z}} 2^{-k}
     \sqrt{\log \mathcal{N}(T, d, 2^{-k})}, $$
and the diameter-capped Dudley entropy integral of Eq. (8.16),
$$ I(T, D) \;=\; \int_0^{D} \sqrt{\log \mathcal{N}(T, d, \varepsilon)}\,
     d\varepsilon , $$
with: summability for finite nonempty $T$ (derived, never hypothesized),
window-sum control, the one-directional comparison $\Sigma \le 2 I$ (book
p. 226), the diameter lower bounds used for term absorption
(Remark 8.1.6), and the $\mathbb{R}_{\ge 0}^\infty$ twin `dudleyLIntegral`
used solely by the countable lift.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1: Eq. (8.2) (Theorem 8.1.4's sum),
Eq. (8.16) / Remark 8.1.7 (the diameter-capped integral), p. 226 (the sum-vs-
integral comparison in the proof of Theorem 8.1.3), Remark 8.1.6.

**Proof formalization notes.** `dudleySum` is a REAL ℤ-indexed `tsum` (junk
`0` only when non-summable, ruled out for finite nonempty `T` by
`summable_dudleySummand`: terms vanish left of the coarse scale since
`𝒩 = 1` at `ε ≥ diam`, and are geometrically dominated by `2^{−k}√(log |T|)`
on the right). Proofs use finite WINDOW sums `∑ k ∈ Icc (κ+1) (κ+n)` and the
bridge `sum_window_le_dudleySum`. Only the direction `∑ ≤ 2∫` is formalized
(book p. 226: `2^{−k} = 2∫_{2^{−k−1}}^{2^{−k}} dε` + antitonicity): per
dyadic block `2^{−k−1}·f(2^{−k}) ≤ ∫_{Ioc(2^{−k−1}, 2^{−k})} f`, the blocks
are pairwise disjoint and tile inside `Ioc 0 D` — NOT via the unit-step
`AntitoneOn.sum_le_integral` family (wrong grid shape). The reverse
`∫ ≤ 2∑` (HDP Exercise 8.3) is out of scope. The cap `D` is an explicit
parameter with hypothesis `diam T ≤ D`, making Eq. (8.16) the PRIMARY
statement and Eq. (8.13)'s `∫_0^∞` a display corollary
(`dudleyIntegral_Ioi_eq`). The diameter absorption lemmas
(`diam·√log2 ≤ 4·dudleySum`, `≤ 8·dudleyIntegral`) are the only places the
book's constant-free "`𝒩 ≥ 2` below `diam/2`" step becomes a quantitative
Lean cost. Pre-agreed >300-line split plan (design risk register): if this
file exceeds ~300 lines during proof closure, split into
`Chaining/EntropySum.lean` (the ℤ-sum carrier: `dudleySummand`, `dudleySum`,
summability, window bridges, `diam ≤ 4·dudleySum`) and a new
`Chaining/DudleyIntegral.lean` (the integral carriers `dudleyIntegral` /
`dudleyLIntegral`, the `∑ ≤ 2∫` comparison, `dudleyIntegral_Ioi_eq`, and the
`diam ≤ 8·dudleyIntegral` absorption) — all `def` bodies stay byte-identical,
only lemma homes move. Named-sorry fallback of this work item:
`sum_window_le_two_mul_dudleyIntegral` (the block-tiling comparison), with
both carriers and all other lemmas proved.

**Bibliographic comments.** The entropy integral is due to R. M. Dudley,
"The sizes of compact subsets of Hilbert space and continuity of Gaussian
processes," *J. Funct. Anal.* 1 (1967), 290–330; the dyadic-sum form and the
sum/integral equivalence are standard (Talagrand, *Upper and Lower Bounds
for Stochastic Processes*, 2014, §2.3).
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {E : Type*} [PseudoMetricSpace E]

/-- **Dyadic entropy summand** (HDP §8.1, Eq. (8.2)):
`2^{−k} √(log 𝒩(T, d, 2^{−k}))` at the dyadic scale `k ∈ ℤ`. Edge behavior
inherited from `sqrtLogCov` (junk `0` at `𝒩 = ⊤`). -/
noncomputable def dudleySummand (T : Set E) (k : ℤ) : ℝ :=
  (2 : ℝ) ^ (-k) * sqrtLogCov T ((2 : ℝ) ^ (-k))

/-- **Dyadic entropy sum** (HDP §8.1, Eq. (8.2) RHS): the ℤ-indexed `tsum`
of `dudleySummand`. Edge behavior: junk `0` when non-summable — ruled out
for finite nonempty `T` by `summable_dudleySummand`, so the junk zone is
never load-bearing in the chaining theorems. -/
noncomputable def dudleySum (T : Set E) : ℝ :=
  ∑' k : ℤ, dudleySummand T k

lemma dudleySummand_nonneg (T : Set E) (k : ℤ) :
    -- LEAN-ONLY: product of nonnegatives; no book content
    0 ≤ dudleySummand T k :=
  mul_nonneg (by positivity) (sqrtLogCov_nonneg T _)

/-- Summability of the dyadic entropy sum for finite nonempty `T` (HDP §8.1,
proof Step 1): finitely many nonzero terms on the left (`𝒩 = 1` for
`2^{−k} ≥ diam T`) and a geometric tail on the right (`𝒩 ≤ |T|`). Derived,
never hypothesized. -/
lemma summable_dudleySummand {T : Set E}
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) :
    Summable (dudleySummand T) := by
  have hbd : Bornology.IsBounded T := hfin.isBounded
  apply Summable.of_nat_of_neg_add_one
  · -- Right tail (k = ↑n ≥ 0): geometric domination by `√(log|T|) · (1/2)ⁿ`.
    have hpow : ∀ n : ℕ, (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2) ^ n := by
      intro n; rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    refine Summable.of_nonneg_of_le (g := fun n : ℕ => dudleySummand T (n : ℤ))
      (f := fun n : ℕ => Real.sqrt (Real.log T.ncard) * (1 / 2) ^ n)
      (fun n => dudleySummand_nonneg T _) (fun n => ?_) ?_
    · have h1 : dudleySummand T (n : ℤ)
          ≤ (2 : ℝ) ^ (-(n : ℤ)) * Real.sqrt (Real.log T.ncard) :=
        mul_le_mul_of_nonneg_left (sqrtLogCov_le_sqrt_log_ncard hfin _) (by positivity)
      rw [hpow] at h1
      linarith [h1, mul_comm (Real.sqrt (Real.log T.ncard)) ((1 / 2 : ℝ) ^ n)]
    · exact (summable_geometric_two).mul_left _
  · -- Left tail (k = -(n+1) ≤ -1): eventually zero above the diameter scale.
    obtain ⟨m, hm⟩ := exists_nat_gt (Metric.diam T)
    have hmle : Metric.diam T ≤ (2 : ℝ) ^ (m : ℤ) := by
      rw [zpow_natCast]
      exact hm.le.trans (by exact_mod_cast Nat.lt_two_pow_self.le)
    apply summable_of_ne_finset_zero (s := Finset.range m)
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    show dudleySummand T (-((n : ℤ) + 1)) = 0
    unfold dudleySummand
    rw [neg_neg]
    have hdiam : Metric.diam T ≤ (2 : ℝ) ^ ((n : ℤ) + 1) :=
      hmle.trans (zpow_le_zpow_right₀ one_le_two (by exact_mod_cast Nat.le_succ_of_le hn))
    rw [sqrtLogCov_eq_zero_of_diam_le hne hbd (by positivity) hdiam, mul_zero]

lemma dudleySum_nonneg (T : Set E) :
    -- LEAN-ONLY: tsum of nonnegatives (junk 0 also nonneg); no book content
    0 ≤ dudleySum T :=
  tsum_nonneg (fun k => dudleySummand_nonneg T k)

/-- Finite windows are dominated by the full sum (HDP §8.1, the
Eq. (8.12) ⇒ Eq. (8.2) step): nonneg partial sums vs `tsum`. -/
lemma sum_window_le_dudleySum {T : Set E}
    -- LEAN-ONLY: T finite so the tsum is honest (summable)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) (s : Finset ℤ) :
    ∑ k ∈ s, dudleySummand T k ≤ dudleySum T :=
  Summable.sum_le_tsum s (fun i _ => dudleySummand_nonneg T i)
    (summable_dudleySummand hfin hne)

/-- **Dudley entropy integral, diameter-capped** (HDP §8.1, Eq. (8.16)):
`∫_0^D √(log 𝒩(T,d,ε)) dε` as a Bochner set integral over `Ioc 0 D` w.r.t.
`volume`. The cap `D` is explicit: `D = diam T` gives Eq. (8.16), and the
zero-extension beyond the diameter gives the `∫_0^∞` display of Theorem
8.1.3 (`dudleyIntegral_Ioi_eq`). Edge behavior: `0` for `D ≤ 0` (empty
interval) and under the `sqrtLogCov` junk zone (guarded by consumers). -/
noncomputable def dudleyIntegral (T : Set E) (D : ℝ) : ℝ :=
  ∫ ε in Set.Ioc (0 : ℝ) D, sqrtLogCov T ε

lemma dudleyIntegral_nonneg (T : Set E) (D : ℝ) :
    -- LEAN-ONLY: integral of a nonneg integrand; no book content
    0 ≤ dudleyIntegral T D :=
  setIntegral_nonneg measurableSet_Ioc (fun x _ => sqrtLogCov_nonneg T x)

/-- Monotonicity in the cap (LEAN-ONLY: nonneg integrand on a larger set). -/
lemma dudleyIntegral_mono_cap {T : Set E}
    -- LEAN-ONLY: T finite gives integrability on both intervals
    (hfin : T.Finite) {D D' : ℝ}
    -- LEAN-ONLY: cap comparison
    (h : D ≤ D') :
    dudleyIntegral T D ≤ dudleyIntegral T D' := by
  unfold dudleyIntegral
  exact setIntegral_mono_set (integrableOn_sqrtLogCov_Ioc hfin)
    (Filter.Eventually.of_forall (fun x => sqrtLogCov_nonneg T x))
    ((Set.Ioc_subset_Ioc_right h).eventuallyLE)

/-- The `∫_0^∞` display equals the capped integral (HDP §8.1, Remark 8.1.7):
the integrand vanishes on `[diam T, ∞)`; bridges Eq. (8.13)'s `∫_0^∞` to the
capped carrier. -/
lemma dudleyIntegral_Ioi_eq {T : Set E}
    -- LEAN-ONLY: T finite (integrability + the √(log|T|) bound)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {D : ℝ}
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap (the diam = 0 corner is handled by consumers)
    (hD0 : 0 < D) :
    ∫ ε in Set.Ioi (0 : ℝ), sqrtLogCov T ε = dudleyIntegral T D := by
  have hbd : Bornology.IsBounded T := hfin.isBounded
  have hzero_on : ∀ x ∈ Set.Ioi D, sqrtLogCov T x = 0 := fun x hx =>
    sqrtLogCov_eq_zero_of_diam_le hne hbd
      (le_of_lt (lt_of_le_of_lt hD0.le hx)) (le_of_lt (lt_of_le_of_lt hD hx))
  have hIoiD : MeasureTheory.IntegrableOn (sqrtLogCov T) (Set.Ioi D)
      MeasureTheory.volume :=
    integrableOn_zero.congr_fun (fun x hx => (hzero_on x hx).symm) measurableSet_Ioi
  unfold dudleyIntegral
  rw [← Set.Ioc_union_Ioi_eq_Ioi hD0.le,
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_sqrtLogCov_Ioc hfin) hIoiD,
    setIntegral_eq_zero_of_forall_eq_zero hzero_on, add_zero]

/-- **Window-sum vs integral comparison** (HDP §8.1, p. 226, proof of
Theorem 8.1.3): per dyadic block,
`2^{−k−1}·sqrtLogCov T (2^{−k}) ≤ ∫_{Ioc(2^{−k−1}, 2^{−k})} sqrtLogCov`
(constant-on-block lower bound + `sqrtLogCov_anti`); the blocks are pairwise
disjoint and tile inside `Ioc 0 D`, so any finite window sum is at most
`2 · dudleyIntegral T D`. This is the file's named-sorry fallback. -/
theorem sum_window_le_two_mul_dudleyIntegral {T : Set E}
    -- LEAN-ONLY: T finite (integrability, antitonicity below ⊤)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {s : Finset ℤ} {D : ℝ}
    -- LEAN-ONLY: the window scales fit under the cap, so the blocks tile
    -- inside Ioc 0 D
    (hs : ∀ k ∈ s, (2 : ℝ) ^ (-k) ≤ D) :
    ∑ k ∈ s, dudleySummand T k ≤ 2 * dudleyIntegral T D := by
  classical
  set B : ℤ → Set ℝ := fun k => Set.Ioc ((2 : ℝ) ^ (-(k + 1))) ((2 : ℝ) ^ (-k)) with hB
  have hcov_fin : ∀ ε : ℝ, coveringNumber T ε ≠ ⊤ := fun ε =>
    ne_top_of_le_ne_top hfin.encard_lt_top.ne (Metric.coveringNumber_le_encard_self T)
  have hIocD_int : MeasureTheory.IntegrableOn (sqrtLogCov T) (Set.Ioc 0 D)
      MeasureTheory.volume := integrableOn_sqrtLogCov_Ioc hfin
  -- Each block sits inside `Ioc 0 D`.
  have hsub : ∀ k ∈ s, B k ⊆ Set.Ioc 0 D := by
    intro k hk x hx
    exact ⟨lt_of_lt_of_le (by positivity) hx.1.le, hx.2.trans (hs k hk)⟩
  have hint_bk : ∀ k ∈ s, MeasureTheory.IntegrableOn (sqrtLogCov T) (B k)
      MeasureTheory.volume := fun k hk => hIocD_int.mono_set (hsub k hk)
  -- Key scale identity `2^{-k} = 2 · 2^{-(k+1)}`.
  have hkey : ∀ k : ℤ, (2 : ℝ) ^ (-k) = 2 * (2 : ℝ) ^ (-(k + 1)) := by
    intro k
    rw [show (-(k + 1) : ℤ) = -k - 1 from by ring, zpow_sub₀ (two_ne_zero), zpow_one]
    ring
  -- Per-block lower bound: `dudleySummand T k ≤ 2 · ∫_{B k} sqrtLogCov`.
  have hblock : ∀ k ∈ s, dudleySummand T k ≤ 2 * ∫ x in B k, sqrtLogCov T x := by
    intro k hk
    have hcle : ∀ x ∈ B k, sqrtLogCov T ((2 : ℝ) ^ (-k)) ≤ sqrtLogCov T x :=
      fun x hx => sqrtLogCov_anti hx.2 (hcov_fin x)
    have hmt : MeasureTheory.volume (B k) ≠ ∞ := by
      show MeasureTheory.volume (Set.Ioc _ _) ≠ ∞
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    have hge := setIntegral_ge_of_const_le_real (μ := MeasureTheory.volume)
      (s := B k) (f := sqrtLogCov T) (c := sqrtLogCov T ((2 : ℝ) ^ (-k)))
      measurableSet_Ioc hmt hcle (hint_bk k hk)
    have hvol : MeasureTheory.volume.real (B k) = (2 : ℝ) ^ (-(k + 1)) := by
      show MeasureTheory.volume.real (Set.Ioc _ _) = _
      rw [MeasureTheory.Measure.real, Real.volume_Ioc,
        ENNReal.toReal_ofReal
          (by rw [hkey k]; have := show (0:ℝ) < (2:ℝ) ^ (-(k + 1)) from by positivity;
              linarith)]
      rw [hkey k]; ring
    rw [hvol] at hge
    -- `dudleySummand = 2^{-k} · sqrtLogCov = 2·(2^{-(k+1)} · sqrtLogCov)`.
    have hds : dudleySummand T k
        = 2 * (sqrtLogCov T ((2 : ℝ) ^ (-k)) * (2 : ℝ) ^ (-(k + 1))) := by
      unfold dudleySummand; rw [hkey k]; ring
    rw [hds]
    linarith [hge]
  -- Blocks are pairwise disjoint.
  have hdisj : Set.Pairwise ↑s (Function.onFun Disjoint B) := by
    have key : ∀ i j : ℤ, i < j → Disjoint (B i) (B j) := by
      intro i j hij
      rw [hB, Set.disjoint_left]
      intro x hxi hxj
      have h3 : (2 : ℝ) ^ (-j) ≤ (2 : ℝ) ^ (-(i + 1)) :=
        zpow_le_zpow_right₀ one_le_two (by omega)
      have := hxi.1
      have := hxj.2
      linarith
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  -- Disjoint union of block integrals, controlled by the cap integral.
  have hunion : ∑ k ∈ s, ∫ x in B k, sqrtLogCov T x
      = ∫ x in ⋃ k ∈ s, B k, sqrtLogCov T x :=
    (integral_biUnion_finset s (fun i _ => measurableSet_Ioc) hdisj hint_bk).symm
  have hUsub : (⋃ k ∈ s, B k) ⊆ Set.Ioc 0 D := by
    simp only [Set.iUnion_subset_iff]; exact hsub
  have hfinal : ∫ x in ⋃ k ∈ s, B k, sqrtLogCov T x ≤ dudleyIntegral T D :=
    setIntegral_mono_set hIocD_int
      (Filter.Eventually.of_forall (fun x => sqrtLogCov_nonneg T x))
      hUsub.eventuallyLE
  calc ∑ k ∈ s, dudleySummand T k
      ≤ ∑ k ∈ s, 2 * ∫ x in B k, sqrtLogCov T x := Finset.sum_le_sum hblock
    _ = 2 * ∑ k ∈ s, ∫ x in B k, sqrtLogCov T x := by rw [Finset.mul_sum]
    _ = 2 * ∫ x in ⋃ k ∈ s, B k, sqrtLogCov T x := by rw [hunion]
    _ ≤ 2 * dudleyIntegral T D := by linarith [hfinal]

/-- **Sum ≤ 2·integral** (HDP §8.1, p. 226): tsum version of the window
comparison via `Summable.tsum_le_of_sum_le` (window terms above the diameter
scale vanish). -/
theorem dudleySum_le_two_mul_dudleyIntegral {T : Set E}
    -- LEAN-ONLY: T finite (summability + integrability)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {D : ℝ}
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    dudleySum T ≤ 2 * dudleyIntegral T D := by
  classical
  have hbd : Bornology.IsBounded T := hfin.isBounded
  refine Summable.tsum_le_of_sum_le (summable_dudleySummand hfin hne) (fun s => ?_)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun k => (2 : ℝ) ^ (-k) ≤ D)]
  have hz : ∑ k ∈ s.filter (fun k => ¬ (2 : ℝ) ^ (-k) ≤ D), dudleySummand T k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_filter, not_le] at hk
    unfold dudleySummand
    rw [sqrtLogCov_eq_zero_of_diam_le hne hbd (by positivity)
      (hD.trans hk.2.le), mul_zero]
  rw [hz, add_zero]
  exact sum_window_le_two_mul_dudleyIntegral hfin hne
    (fun k hk => (Finset.mem_filter.mp hk).2)

/-- Diameter lower bound on the sum (HDP §8.1, Remark 8.1.6 absorption
device): at the last scale `κ'` with `𝒩 = 1`, the `(κ'+1)`-term is
`≥ 2^{−κ'−1}·√log 2 ≥ (diam/4)·√log 2` (uses
`one_lt_coveringNumber_of_two_mul_lt_dist`). The frozen numeral `4` is the
quantitative cost of the book's constant-free "`𝒩 ≥ 2` below `diam/2`". -/
lemma diam_mul_sqrt_log_two_le_four_mul_dudleySum {T : Set E}
    -- LEAN-ONLY: T finite (summability; honest diam)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) :
    Metric.diam T * Real.sqrt (Real.log 2) ≤ 4 * dudleySum T := by
  have hbd : Bornology.IsBounded T := hfin.isBounded
  rcases eq_or_lt_of_le (Metric.diam_nonneg (s := T)) with hdiam0 | hdiam_pos
  · -- Degenerate `diam = 0`: LHS is `0`, RHS nonnegative.
    rw [← hdiam0, zero_mul]
    linarith [dudleySum_nonneg T]
  · -- Pick a dyadic scale `e = 2^{-κ}` with `diam/4 ≤ e < diam/2`.
    obtain ⟨κ, h_lo, h_hi⟩ := exists_coarse_scale (D := Metric.diam T / 4) (by linarith)
    set e : ℝ := (2 : ℝ) ^ (-κ) with he
    have h_lo' : Metric.diam T / 4 ≤ e := h_lo
    have h_hi' : e < Metric.diam T / 2 := by
      have : e < 2 * (Metric.diam T / 4) := h_hi
      linarith
    have he_pos : 0 < e := by positivity
    -- A pair of points at distance `> 2e` exists, since `2e < diam`.
    have h2e : 2 * e < Metric.diam T := by linarith
    obtain ⟨a, ha, b, hb, hab⟩ :
        ∃ a ∈ T, ∃ b ∈ T, 2 * e < dist a b := by
      by_contra h_all
      push_neg at h_all
      exact absurd (Metric.diam_le_of_forall_dist_le_of_nonempty hne h_all) (not_le.2 h2e)
    -- Hence `𝒩(T, e) ≥ 2`, giving `sqrtLogCov T e ≥ √(log 2)`.
    have hcov : 1 < coveringNumber T e :=
      one_lt_coveringNumber_of_two_mul_lt_dist he_pos.le ha hb hab
    have hcov_top : coveringNumber T e ≠ ⊤ :=
      ne_top_of_le_ne_top hfin.encard_lt_top.ne (Metric.coveringNumber_le_encard_self T)
    have h2n : 2 ≤ (coveringNumber T e).toNat := by
      have : (2 : ℕ∞) ≤ coveringNumber T e := by
        rwa [show (2 : ℕ∞) = 1 + 1 from rfl, ENat.add_one_le_iff (by simp)]
      simpa using ENat.toNat_le_toNat this hcov_top
    have hsqrt : Real.sqrt (Real.log 2) ≤ sqrtLogCov T e := by
      unfold sqrtLogCov
      apply Real.sqrt_le_sqrt
      apply Real.log_le_log (by norm_num)
      exact_mod_cast h2n
    -- The `κ`-summand dominates `(diam/4)·√(log 2)`.
    have hsummand : Metric.diam T / 4 * Real.sqrt (Real.log 2) ≤ dudleySummand T κ := by
      have : Metric.diam T / 4 * Real.sqrt (Real.log 2) ≤ e * sqrtLogCov T e :=
        mul_le_mul h_lo' hsqrt (Real.sqrt_nonneg _) he_pos.le
      simpa [dudleySummand, he] using this
    have hle : dudleySummand T κ ≤ dudleySum T := by
      have := sum_window_le_dudleySum hfin hne {κ}
      simpa using this
    have hchain : Metric.diam T / 4 * Real.sqrt (Real.log 2) ≤ dudleySum T :=
      hsummand.trans hle
    nlinarith [hchain, Real.sqrt_nonneg (Real.log 2)]

/-- Diameter lower bound on the integral (HDP §8.1, Remark 8.1.6): previous
lemma + `∑ ≤ 2∫`; frozen numeral `8 = 4 × 2`. -/
lemma diam_mul_sqrt_log_two_le_eight_mul_dudleyIntegral {T : Set E}
    -- LEAN-ONLY: T finite
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {D : ℝ}
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    Metric.diam T * Real.sqrt (Real.log 2) ≤ 8 * dudleyIntegral T D := by
  have h1 := diam_mul_sqrt_log_two_le_four_mul_dudleySum hfin hne
  have h2 := dudleySum_le_two_mul_dudleyIntegral hfin hne hD hD0
  linarith

/-- ℝ≥0∞ twin of the Dudley integral (HDP §8.1, p. 227 footnote), used
SOLELY by the countable lift `dudley_inequality_countable` so that neither
side of the lifted inequality can be junk. -/
noncomputable def dudleyLIntegral (T : Set E) (D : ℝ) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc (0 : ℝ) D, ENNReal.ofReal (sqrtLogCov T ε)

/-- The twin agrees with the Bochner carrier under integrability. -/
lemma dudleyLIntegral_eq_ofReal {T : Set E} {D : ℝ}
    -- LEAN-ONLY: integrability so `ofReal ∘ ∫ = ∫⁻ ∘ ofReal`; no book content
    (hint : MeasureTheory.IntegrableOn (sqrtLogCov T) (Set.Ioc 0 D)
      MeasureTheory.volume) :
    dudleyLIntegral T D = ENNReal.ofReal (dudleyIntegral T D) := by
  unfold dudleyLIntegral dudleyIntegral
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun x => sqrtLogCov_nonneg T x))]

/-! ### ℝ≥0∞ dyadic entropy sum (faithful infinite-`T` carriers)

For infinite totally bounded `T` the real `dudleySum` (a `tsum`) silently
junks to `0` when the dyadic entropy series diverges, so the faithful
general-`T` statements (HDP Thm 8.1.4 with E sup read per Remark 7.2.1)
carry the ℝ≥0∞ twin `dudleyLSum`, which never junks: divergence is an
honest `⊤` and the inequality is then trivially true — exactly the book's
"≤ ∞". The real lemmas above remain the finite-`T` display path. -/

/-- ℝ≥0∞ twin of the dyadic entropy sum `dudleySum` (HDP §8.1, Eq. (8.2)
RHS): `∑_{k ∈ ℤ} 2^{−k} √(log 𝒩(T, 2^{−k}))` valued in `ℝ≥0∞`, honest at
divergence (`⊤`), junk-free without any summability hypothesis. -/
noncomputable def dudleyLSum (T : Set E) : ℝ≥0∞ :=
  ∑' k : ℤ, ENNReal.ofReal (dudleySummand T k)

/-- Finite windows sit below the full ℝ≥0∞ dyadic sum — unconditionally
(the ℝ≥0∞ twin of `sum_window_le_dudleySum`, with no summability needed). -/
lemma sum_window_le_dudleyLSum {T : Set E} (s : Finset ℤ) :
    ∑ k ∈ s, ENNReal.ofReal (dudleySummand T k) ≤ dudleyLSum T :=
  ENNReal.sum_le_tsum s

/-- The ℝ≥0∞ dyadic sum agrees with the real one under summability
(`ENNReal.ofReal`-tsum bridge; the summand is nonnegative). -/
lemma dudleyLSum_eq_ofReal_of_summable {T : Set E}
    -- LEAN-ONLY: summability so the real tsum is honest; no book content
    (hS : Summable fun k : ℤ => dudleySummand T k) :
    dudleyLSum T = ENNReal.ofReal (dudleySum T) := by
  unfold dudleyLSum dudleySum
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => dudleySummand_nonneg T k) hS]

/-- Summability of the dyadic summand for finite `T` (geometric tail
`𝒩 ≤ |T|` at fine scales, zero summand beyond the diameter at coarse
scales) — extracted from the existing `summable_dudleySummand` route so the
`*_of_finite` corollaries can rebuild the real display from the ℝ≥0∞
primaries. -/
lemma summable_dudleySummand_of_finite {T : Set E}
    -- LEAN-ONLY: T finite (book WLOG); geometric-tail discharge
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) :
    Summable fun k : ℤ => dudleySummand T k :=
  summable_dudleySummand hfin hne

/-- Sum-to-integral comparison, ℝ≥0∞ twin (HDP §8.1, proof of Thm 8.1.3):
`dudleyLSum T ≤ 2 · dudleyLIntegral T D` whenever the cap dominates the
diameter. Junk-free at every entropy size: both sides are honest ℝ≥0∞. -/
lemma dudleyLSum_le_two_mul_dudleyLIntegral {T : Set E}
    -- LEAN-ONLY: finite covering numbers at positive radii (junk-guard for
    -- `sqrtLogCov`, whose `toNat` collapses at 𝒩 = ⊤); the faithful `hcov`
    -- package of the general Dudley statements
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {D : ℝ}
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    dudleyLSum T ≤ 2 * dudleyLIntegral T D := by
  classical
  have hbd : Bornology.IsBounded T := isBounded_of_coveringNumber_ne_top hcov
  set B : ℤ → Set ℝ := fun k => Set.Ioc ((2 : ℝ) ^ (-(k + 1))) ((2 : ℝ) ^ (-k)) with hB
  -- Key scale identity `2^{-k} = 2 · 2^{-(k+1)}`.
  have hkey : ∀ k : ℤ, (2 : ℝ) ^ (-k) = 2 * (2 : ℝ) ^ (-(k + 1)) := by
    intro k
    rw [show (-(k + 1) : ℤ) = -k - 1 from by ring, zpow_sub₀ (two_ne_zero), zpow_one]; ring
  -- Per-block lower bound in ℝ≥0∞ (constant-on-block + antitonicity).
  have hblock : ∀ k : ℤ, ENNReal.ofReal (dudleySummand T k)
      ≤ 2 * ∫⁻ x in B k, ENNReal.ofReal (sqrtLogCov T x) := by
    intro k
    have hds : ENNReal.ofReal (dudleySummand T k)
        = 2 * (ENNReal.ofReal (sqrtLogCov T ((2 : ℝ) ^ (-k)))
            * ENNReal.ofReal ((2 : ℝ) ^ (-(k + 1)))) := by
      have h1 : dudleySummand T k
          = sqrtLogCov T ((2 : ℝ) ^ (-k)) * (2 * (2 : ℝ) ^ (-(k + 1))) := by
        unfold dudleySummand; rw [hkey k]; ring
      rw [h1, ENNReal.ofReal_mul (sqrtLogCov_nonneg T _),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      ring
    have hc : ∫⁻ x in B k, ENNReal.ofReal (sqrtLogCov T ((2 : ℝ) ^ (-k)))
        = ENNReal.ofReal (sqrtLogCov T ((2 : ℝ) ^ (-k)))
            * ENNReal.ofReal ((2 : ℝ) ^ (-(k + 1))) := by
      rw [setLIntegral_const]
      congr 1
      show MeasureTheory.volume (Set.Ioc ((2 : ℝ) ^ (-(k + 1))) ((2 : ℝ) ^ (-k)))
          = ENNReal.ofReal ((2 : ℝ) ^ (-(k + 1)))
      rw [Real.volume_Ioc]; congr 1; rw [hkey k]; ring
    have hmono : ∫⁻ x in B k, ENNReal.ofReal (sqrtLogCov T ((2 : ℝ) ^ (-k)))
        ≤ ∫⁻ x in B k, ENNReal.ofReal (sqrtLogCov T x) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro x hx
      have hxpos : 0 < x := lt_trans (by positivity) hx.1
      exact ENNReal.ofReal_le_ofReal (sqrtLogCov_anti hx.2 (hcov x hxpos))
    calc ENNReal.ofReal (dudleySummand T k)
        = 2 * ∫⁻ x in B k, ENNReal.ofReal (sqrtLogCov T ((2 : ℝ) ^ (-k))) := by rw [hds, hc]
      _ ≤ 2 * ∫⁻ x in B k, ENNReal.ofReal (sqrtLogCov T x) := by gcongr
  -- Blocks are pairwise disjoint.
  have hdisj : Set.PairwiseDisjoint (Set.univ : Set ℤ) B := by
    have key : ∀ i j : ℤ, i < j → Disjoint (B i) (B j) := by
      intro i j hij
      rw [hB, Set.disjoint_left]
      intro x hxi hxj
      have h3 : (2 : ℝ) ^ (-j) ≤ (2 : ℝ) ^ (-(i + 1)) :=
        zpow_le_zpow_right₀ one_le_two (by omega)
      have := hxi.1
      have := hxj.2
      linarith
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  -- Pass to the tsum via finite windows.
  unfold dudleyLSum
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun s => ?_)
  -- Drop the coarse terms above the diameter scale (their summand is `0`).
  rw [← Finset.sum_filter_add_sum_filter_not s (fun k => (2 : ℝ) ^ (-k) ≤ D)]
  have hz : ∑ k ∈ s.filter (fun k => ¬ (2 : ℝ) ^ (-k) ≤ D),
      ENNReal.ofReal (dudleySummand T k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_filter, not_le] at hk
    have : dudleySummand T k = 0 := by
      unfold dudleySummand
      rw [sqrtLogCov_eq_zero_of_diam_le hne hbd (by positivity) (hD.trans hk.2.le), mul_zero]
    rw [this, ENNReal.ofReal_zero]
  rw [hz, add_zero]
  set s' := s.filter (fun k => (2 : ℝ) ^ (-k) ≤ D) with hs'def
  have hssub : ∀ k ∈ s', (2 : ℝ) ^ (-k) ≤ D := fun k hk => (Finset.mem_filter.mp hk).2
  have hsub : ∀ k ∈ s', B k ⊆ Set.Ioc 0 D := by
    intro k hk x hx
    exact ⟨lt_of_lt_of_le (by positivity) hx.1.le, hx.2.trans (hssub k hk)⟩
  have hUsub : (⋃ k ∈ s', B k) ⊆ Set.Ioc 0 D := by
    simp only [Set.iUnion_subset_iff]; exact hsub
  calc ∑ k ∈ s', ENNReal.ofReal (dudleySummand T k)
      ≤ ∑ k ∈ s', 2 * ∫⁻ x in B k, ENNReal.ofReal (sqrtLogCov T x) :=
        Finset.sum_le_sum (fun k _ => hblock k)
    _ = 2 * ∑ k ∈ s', ∫⁻ x in B k, ENNReal.ofReal (sqrtLogCov T x) := by rw [Finset.mul_sum]
    _ = 2 * ∫⁻ x in ⋃ k ∈ s', B k, ENNReal.ofReal (sqrtLogCov T x) := by
        rw [lintegral_biUnion_finset (hdisj.subset (Set.subset_univ _))
          (fun b _ => measurableSet_Ioc)]
    _ ≤ 2 * dudleyLIntegral T D := by
        gcongr
        unfold dudleyLIntegral
        exact lintegral_mono' (Measure.restrict_mono hUsub le_rfl) le_rfl

/-- Diameter absorber, ℝ≥0∞ twin (HDP §8.1, Remark 8.1.6 absorption):
`ofReal (diam T · √log 2) ≤ 4 · dudleyLSum T`. -/
lemma ofReal_diam_mul_sqrt_log_two_le_four_mul_dudleyLSum {T : Set E}
    -- LEAN-ONLY: finite covering numbers at positive radii (junk-guard)
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) :
    ENNReal.ofReal (Metric.diam T * Real.sqrt (Real.log 2))
      ≤ 4 * dudleyLSum T := by
  have hbd : Bornology.IsBounded T := isBounded_of_coveringNumber_ne_top hcov
  rcases eq_or_lt_of_le (Metric.diam_nonneg (s := T)) with hdiam0 | hdiam_pos
  · rw [← hdiam0, zero_mul, ENNReal.ofReal_zero]; exact zero_le
  · -- Pick a dyadic scale `e = 2^{-κ}` with `diam/4 ≤ e < diam/2`.
    obtain ⟨κ, h_lo, h_hi⟩ := exists_coarse_scale (D := Metric.diam T / 4) (by linarith)
    set e : ℝ := (2 : ℝ) ^ (-κ) with he
    have h_lo' : Metric.diam T / 4 ≤ e := h_lo
    have he_pos : 0 < e := by positivity
    have h_hi' : e < Metric.diam T / 2 := by
      have : e < 2 * (Metric.diam T / 4) := h_hi; linarith
    have h2e : 2 * e < Metric.diam T := by linarith
    obtain ⟨a, ha, b, hb, hab⟩ :
        ∃ a ∈ T, ∃ b ∈ T, 2 * e < dist a b := by
      by_contra h_all
      push_neg at h_all
      exact absurd (Metric.diam_le_of_forall_dist_le_of_nonempty hne h_all) (not_le.2 h2e)
    have hcov1 : 1 < coveringNumber T e :=
      one_lt_coveringNumber_of_two_mul_lt_dist he_pos.le ha hb hab
    have hcov_top : coveringNumber T e ≠ ⊤ := hcov e he_pos
    have h2n : 2 ≤ (coveringNumber T e).toNat := by
      have : (2 : ℕ∞) ≤ coveringNumber T e := by
        rwa [show (2 : ℕ∞) = 1 + 1 from rfl, ENat.add_one_le_iff (by simp)]
      simpa using ENat.toNat_le_toNat this hcov_top
    have hsqrt : Real.sqrt (Real.log 2) ≤ sqrtLogCov T e := by
      unfold sqrtLogCov
      apply Real.sqrt_le_sqrt
      apply Real.log_le_log (by norm_num)
      exact_mod_cast h2n
    have hsummand : Metric.diam T / 4 * Real.sqrt (Real.log 2) ≤ dudleySummand T κ := by
      have : Metric.diam T / 4 * Real.sqrt (Real.log 2) ≤ e * sqrtLogCov T e :=
        mul_le_mul h_lo' hsqrt (Real.sqrt_nonneg _) he_pos.le
      simpa [dudleySummand, he] using this
    calc ENNReal.ofReal (Metric.diam T * Real.sqrt (Real.log 2))
        ≤ ENNReal.ofReal (4 * dudleySummand T κ) := by
          apply ENNReal.ofReal_le_ofReal
          have heq : Metric.diam T * Real.sqrt (Real.log 2)
              = 4 * (Metric.diam T / 4 * Real.sqrt (Real.log 2)) := by ring
          rw [heq]
          exact mul_le_mul_of_nonneg_left hsummand (by norm_num)
      _ = 4 * ENNReal.ofReal (dudleySummand T κ) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
      _ ≤ 4 * dudleyLSum T := by
          gcongr
          exact ENNReal.le_tsum κ

/-- Capped-vs-`Ioi` display, ℝ≥0∞ twin (HDP §8.1, Remark 8.1.7): beyond the
diameter the integrand vanishes, so the `∫₀^∞` and capped forms agree. -/
lemma dudleyLIntegral_Ioi_eq {T : Set E}
    -- LEAN-ONLY: finite covering numbers at positive radii (junk-guard)
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {D : ℝ}
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Remark 8.1.7
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ε in Set.Ioi (0 : ℝ), ENNReal.ofReal (sqrtLogCov T ε)
      = dudleyLIntegral T D := by
  have hbd : Bornology.IsBounded T := isBounded_of_coveringNumber_ne_top hcov
  have hzero_on : ∀ x ∈ Set.Ioi D, sqrtLogCov T x = 0 := fun x hx =>
    sqrtLogCov_eq_zero_of_diam_le hne hbd
      (le_of_lt (lt_of_le_of_lt hD0.le hx)) (le_of_lt (lt_of_le_of_lt hD hx))
  unfold dudleyLIntegral
  rw [← Set.Ioc_union_Ioi_eq_Ioi hD0.le,
    lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl),
    setLIntegral_eq_zero measurableSet_Ioi (fun x hx => by rw [hzero_on x hx]; simp),
    add_zero]

end StatLean.ConcentrationInequalities
