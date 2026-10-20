module
/-
# Abstract Dudley / Gaussian-chaining for sub-Gaussian-increment processes

This is the abstract chaining argument behind the existence of the `P`-Brownian
bridge `G_P` (vdV §19.2 / §18.1; van der Vaart–Wellner §2.1).  It is
stated for a process `X : T → Ω → ℝ` over a pseudo-metric index `T`, whose
increments are sub-Gaussian with proxy variance
`K² · dist²`, has (a.s.) bounded, uniformly-continuous sample paths on a
countable dense subset.

Mathematical content.  Fix dyadic scales `2^{-j}` and a `2^{-j}`-net `T_j` of
`T` at each scale.  For a point `t`, let `π_j t` be its nearest net point.  The
telescope
`X (π_J t) - X (π_0 t) = ∑_{j<J} (X (π_{j+1} t) - X (π_j t))`
reduces the modulus of continuity to the **per-level links** `(π_j t, π_{j+1} t)`.
Each link increment is sub-Gaussian with proxy `≤ K · 3·2^{-j}` (triangle
inequality on the two net distances + the original distance), so the level
maximum over the *finite* link set is controlled by the Gaussian maximal
inequality `√(2σ² log(2·#links))`
(`ProbabilityTheory.expectation_iSup_abs_le_of_subgaussian`).  Summing a
Dudley-finite schedule and a Borel–Cantelli argument yields a.s. uniform
continuity.

The proof develops nets, nearest-point projections, and the chaining telescope.
The analytic argument runs over the `closePairs` Dudley level set
(`measure_bigOsc_le`, `summable_bigOsc`, `aeUC_via_borelCantelli`) and assembles
into `gaussianChaining_UC`.
-/
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.GaussianMaximal
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace GaussianChaining

variable {T : Type*} [PseudoMetricSpace T]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : T → Ω → ℝ} {K : ℝ}

/-! ## The dyadic-net input

The chaining input is an **explicit dyadic net family** `net : ℕ → Finset T`
together with `hnet` (each `net j` is a `2^{-j}`-net of `T`) and `hnet_mono`
(the family is nested).  Taking the net as data — rather than deriving it from a
bare ε-net total-boundedness existential via `Classical.choose` — makes the net
cardinality explicit in the `hDudley` entropy hypothesis. Total boundedness of
`T` follows from `hnet` by `gc_totallyBounded_univ`. -/

/-! ## Dyadic nets and nearest-point projection

The chaining input is an **explicit dyadic net family** `net : ℕ → Finset T`
with two properties: each `net j` is a `2^{-j}`-net of `T` (`hnet`), and the
family is nested (`hnet_mono`).  Taking the net as data (rather than deriving it
from a bare ε-net existential via `Classical.choose`) keeps the net cardinality
explicit in the `hDudley` entropy hypothesis, stated on `(net j).card`. -/

/-- **Self-projecting nearest net point.** `dyadicProj net hnet j t` is `t`
itself when `t` is already in `net j`, and otherwise *a* net point within
`2^{-j}` of `t` (the witness of `hnet`).  The self-projection branch
(`dyadicProj_self`) is what makes the chaining telescope terminate exactly at a
skeleton point. -/
noncomputable def dyadicProj
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) (t : T) :
    T := by
  classical
  exact if t ∈ net j then t else (hnet j t).choose

/-- The projection lands in the net (both branches). -/
theorem dyadicProj_mem
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) (t : T) :
    dyadicProj net hnet j t ∈ net j := by
  classical
  unfold dyadicProj
  split_ifs with h
  · exact h
  · exact (hnet j t).choose_spec.1

/-- The projection is `2^{-j}`-close to its argument (both branches). -/
theorem dyadicProj_dist_lt
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) (t : T) :
    dist t (dyadicProj net hnet j t) < (2 : ℝ) ^ (-(j : ℤ)) := by
  classical
  unfold dyadicProj
  split_ifs with h
  · rw [dist_self]; positivity
  · exact (hnet j t).choose_spec.2

/-- If `t` is already in the net, the projection is the identity. -/
theorem dyadicProj_self
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) (t : T)
    (ht : t ∈ net j) :
    dyadicProj net hnet j t = t := by
  classical
  unfold dyadicProj
  rw [if_pos ht]

/-- **Consecutive projections are close.** Successive dyadic projections of the
same point differ by at most `3·2^{-j}` (triangle inequality on the two net
distances).  This is the per-level link bound feeding the Gaussian maximal
inequality. -/
theorem dyadicProj_consecutive_close
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) (t : T) :
    dist (dyadicProj net hnet j t) (dyadicProj net hnet (j + 1) t)
      ≤ 3 * (2 : ℝ) ^ (-(j : ℤ)) := by
  have h1 : dist t (dyadicProj net hnet j t) < (2 : ℝ) ^ (-(j : ℤ)) :=
    dyadicProj_dist_lt net hnet j t
  have h2 : dist t (dyadicProj net hnet (j + 1) t) < (2 : ℝ) ^ (-((j : ℤ) + 1)) := by
    have := dyadicProj_dist_lt net hnet (j + 1) t
    simpa [Nat.cast_add, Nat.cast_one, neg_add] using this
  have h2j : (2 : ℝ) ^ (-((j : ℤ) + 1)) ≤ (2 : ℝ) ^ (-(j : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-(j : ℤ)) := by positivity
  calc dist (dyadicProj net hnet j t) (dyadicProj net hnet (j + 1) t)
      ≤ dist (dyadicProj net hnet j t) t + dist t (dyadicProj net hnet (j + 1) t) :=
        dist_triangle _ _ _
    _ = dist t (dyadicProj net hnet j t) + dist t (dyadicProj net hnet (j + 1) t) := by
        rw [dist_comm (dyadicProj net hnet j t) t]
    _ ≤ (2 : ℝ) ^ (-(j : ℤ)) + (2 : ℝ) ^ (-(j : ℤ)) :=
        add_le_add (le_of_lt h1) (le_of_lt (h2.trans_le h2j))
    _ ≤ 3 * (2 : ℝ) ^ (-(j : ℤ)) := by linarith

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **Chaining telescope.** The increment from the coarsest scale `π₀ t` to scale
`π_J t` is the telescoping sum of the per-level link increments.  Proved inline
via `Finset.sum_range_sub` (do NOT import any assembly file). -/
theorem chain_telescope_path
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (t : T) (J : ℕ) (ω : Ω) :
    X (dyadicProj net hnet J t) ω - X (dyadicProj net hnet 0 t) ω
      = ∑ j ∈ Finset.range J,
          (X (dyadicProj net hnet (j+1) t) ω - X (dyadicProj net hnet j t) ω) := by
  exact (Finset.sum_range_sub (fun j => X (dyadicProj net hnet j t) ω) J).symm

/-! ## Shared sub-Gaussian tail and summability helpers -/

/-- **One-sided sub-Gaussian tail, weakened to a uniform proxy.** If `Z` is
sub-Gaussian with proxy `c` and `0 ≤ a`, `(c : ℝ) ≤ σsq`, then the right tail
`μ {a < Z}` is bounded by `exp(-a²/(2σ²))`. Handles two regimes: `c = 0` (then
`Z =ᵐ 0` and the strict-threshold tail is null, which is `≤ anything`); and
`0 < c ≤ σsq` (Chernoff + exp-monotonicity in the denominator, using `-a² ≤ 0`;
note `0 < c ≤ σsq` already forces `0 < σsq`). -/
private theorem tail_one_sided_le {Z : Ω → ℝ} {c : ℝ≥0} {a σsq : ℝ}
    (hZ : ProbabilityTheory.HasSubgaussianMGF Z c μ)
    (ha : 0 ≤ a) (hcle : (c : ℝ) ≤ σsq) :
    μ {ω | a < Z ω} ≤ ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * σsq))) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ (c : ℝ) from c.coe_nonneg) with hc0 | hcpos
  · -- Degenerate proxy: Z =ᵐ 0, so {a < Z} ⊆ᵐ {a < 0} which is null for 0 ≤ a.
    have hc0' : c = 0 := by
      ext; simpa using hc0.symm
    subst hc0'
    have hZ0 : Z =ᵐ[μ] 0 :=
      ProbabilityTheory.HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianMGF_zero hZ
    have hnull : μ {ω | a < Z ω} = 0 := by
      have hsub2 : {ω | a < Z ω} ⊆ {ω | Z ω ≠ 0} ∪ {ω | a < (0 : ℝ)} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω
        by_cases hz : Z ω = 0
        · right; rw [Set.mem_setOf_eq]; rw [hz] at hω; exact hω
        · left; exact hz
      have hnull0 : μ {ω | a < (0 : ℝ)} = 0 := by
        have he : {ω : Ω | a < (0 : ℝ)} = ∅ := by
          ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]; exact ha
        rw [he]; exact measure_empty
      have hZnull : μ {ω | Z ω ≠ 0} = 0 := by
        have he : {ω | Z ω ≠ 0} = {ω | Z ω ≠ (0 : Ω → ℝ) ω} := by simp
        rw [he]
        exact (measure_mono_null (fun ω hω => hω) (ae_iff.mp hZ0))
      exact measure_mono_null hsub2 (by simp [measure_union_null hZnull hnull0])
    rw [hnull]; exact zero_le
  · -- Positive proxy: Chernoff + exp-monotonicity in the denominator.
    have hσpos : 0 < σsq := lt_of_lt_of_le hcpos hcle
    have hsub : {ω | a < Z ω} ⊆ {ω | a ≤ Z ω} := by
      intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; exact le_of_lt hω
    refine (measure_mono hsub).trans ?_
    have hreal := ProbabilityTheory.HasSubgaussianMGF.measure_ge_le hZ ha
    have hexp_mono : Real.exp (-a ^ 2 / (2 * (c : ℝ))) ≤ Real.exp (-a ^ 2 / (2 * σsq)) := by
      apply Real.exp_le_exp.mpr
      have hden : (0 : ℝ) < 2 * (c : ℝ) := by positivity
      have hden2 : (0 : ℝ) < 2 * σsq := by positivity
      have hden' : 2 * (c : ℝ) ≤ 2 * σsq := by linarith [hcle]
      rw [div_le_div_iff₀ hden hden2]
      nlinarith [sq_nonneg a, hden', mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hden')]
    have hbound : μ.real {ω | a ≤ Z ω} ≤ Real.exp (-a ^ 2 / (2 * σsq)) :=
      le_trans hreal hexp_mono
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hbound

/-- **Summability of `2^{-j}·√(log(j+2))`.** A super-geometric decay against a
sub-polynomial (in fact `≪ √(log)`) entropy growth: the schedule's
`log(j+2)`-correction (which makes the Borel–Cantelli masses summable) is itself
modulus-summable.  Proved by comparison with `∑ (j+2)·(1/2)^j` after the crude
bound `√(log(j+2)) ≤ √(j+2) ≤ j+2`. -/
private theorem summable_pow_neg_sqrt_log :
    Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (j + 2))) := by
  -- `2^{-j} = (1/2)^j` and `√(log(j+2)) ≤ j + 2` (a very crude bound: `log x ≤ x`
  -- so `√(log x) ≤ √x ≤ x` for `x ≥ 1`).  Then `(1/2)^j·(j+2)` is summable.
  have hcmp : ∀ j : ℕ,
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (j + 2))
        ≤ ((j : ℝ) + 2) * (1 / 2 : ℝ) ^ j := by
    intro j
    have h2 : (2 : ℝ) ^ (-(j : ℤ)) = (1 / 2 : ℝ) ^ j := by
      rw [zpow_neg, ← inv_zpow, zpow_natCast]; norm_num
    rw [h2, mul_comm]
    gcongr
    -- √(log(j+2)) ≤ j + 2
    have hlog : Real.log ((j : ℝ) + 2) ≤ (j : ℝ) + 2 := by
      nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < (j : ℝ) + 2 by positivity)]
    calc Real.sqrt (Real.log ((j : ℝ) + 2))
        ≤ Real.sqrt ((j : ℝ) + 2) := Real.sqrt_le_sqrt hlog
      _ ≤ (j : ℝ) + 2 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (j : ℝ) + 2 by positivity),
            Real.sqrt_nonneg ((j : ℝ) + 2),
            Real.one_le_sqrt.mpr (show (1 : ℝ) ≤ (j : ℝ) + 2 by
              have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j; linarith)]
  apply Summable.of_nonneg_of_le (fun j => by positivity) hcmp
  -- `∑ (j+2)·(1/2)^j` is summable: `(j+2)·r^j = j·r^j + 2·r^j`, both summable for `|r| < 1`.
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
  have h1 : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 hr).congr (fun j => by simp)
  have h2 : Summable (fun j : ℕ => (2 : ℝ) * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one hr).mul_left 2
  have := h1.add h2
  apply this.congr
  intro j; ring

/-! ## Close net-pairs and level oscillation (★ Dudley level set)

The a.s.-continuity Borel–Cantelli argument needs control of the increment
between two arbitrary close skeleton points.  The standard Dudley level set is
**all close net-pairs at each scale**: pairs `(s, t)` of net points within
`6·2^{-j}`.  The level oscillation event `bigOsc j a` collects the `ω` where some
such pair's increment exceeds `a`, and the Borel–Cantelli summability over a
Dudley-finite schedule (`summable_bigOsc`) feeds the main theorem.  The cardinality bound
here is `#closePairs ≤ #net²` (a filtered product), giving the extra
`√(log 2 + 2 log #net)` wrinkle handled below by sqrt-subadditivity. -/

/-- **All net-pairs at scale `j` within `6·2^{-j}`** (the standard Dudley level
set).  The filtered product `(net j ×ˢ net j).filter (dist ≤ 6·2^{-j})`. -/
noncomputable def closePairs
    (net : ℕ → Finset T) (j : ℕ) :
    Finset (T × T) := by
  classical
  exact ((net j) ×ˢ (net j)).filter
    (fun p => dist p.1 p.2 ≤ 6 * (2 : ℝ) ^ (-(j : ℤ)))

/-- A close pair's endpoints are within `6·2^{-j}` (the filter predicate). -/
theorem mem_closePairs_dist
    (net : ℕ → Finset T) (j : ℕ)
    {p : T × T} (hp : p ∈ closePairs net j) :
    dist p.1 p.2 ≤ 6 * (2 : ℝ) ^ (-(j : ℤ)) := by
  classical
  exact (Finset.mem_filter.mp hp).2

/-- `#closePairs ≤ #net²`: a filtered subset of the product `net ×ˢ net`. -/
theorem closePairs_card_le
    (net : ℕ → Finset T) (j : ℕ) :
    (closePairs net j).card ≤ (net j).card ^ 2 := by
  classical
  unfold closePairs
  calc ((net j ×ˢ net j).filter
          (fun p => dist p.1 p.2 ≤ 6 * (2 : ℝ) ^ (-(j : ℤ)))).card
      ≤ (net j ×ˢ net j).card := Finset.card_filter_le _ _
    _ = (net j).card * (net j).card := Finset.card_product _ _
    _ = (net j).card ^ 2 := (sq _).symm

/-- **Level oscillation event over close net-pairs.** At level `j` with threshold
`a`, `bigOsc X net j a` is the set where some close net-pair's increment exceeds
`a`: `⋃ p ∈ closePairs net j, {ω | a < |X p.2 ω − X p.1 ω|}`. -/
noncomputable def bigOsc (X : T → Ω → ℝ)
    (net : ℕ → Finset T) (j : ℕ) (a : ℝ) :
    Set Ω :=
  ⋃ p ∈ closePairs net j, {ω | a < |X p.2 ω - X p.1 ω|}

/-- **Level large-deviation bound over close pairs.** The measure of the level
oscillation event is bounded by a union bound over close pairs of the sub-Gaussian
tail with proxy `σ_j² = K²·(6·2^{-j})²`:
`μ (bigOsc net j a) ≤ #(closePairs j) · 2 · exp(−a²/(2 K²(6·2^{-j})²))`.

The per-pair distance bound is `mem_closePairs_dist` (direct, from the
`closePairs` filter predicate). -/
theorem measure_bigOsc_le
    (hK : 0 ≤ K)
    (net : ℕ → Finset T)
    (hSG : ∀ s t, ProbabilityTheory.HasSubgaussianMGF (fun ω => X s ω - X t ω)
      ⟨K ^ 2 * dist s t ^ 2, by positivity⟩ μ)
    (j : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    μ (bigOsc X net j a)
      ≤ (closePairs net j).card
          * (2 * ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * (K ^ 2 * (6 * (2 : ℝ) ^ (-(j : ℤ))) ^ 2))))) := by
  classical
  -- Abbreviations.
  set σsq : ℝ := K ^ 2 * (6 * (2 : ℝ) ^ (-(j : ℤ))) ^ 2 with hσsq
  set B : ℝ≥0∞ := 2 * ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * σsq))) with hB
  -- Per-pair two-sided sub-Gaussian tail bound, uniform over the close-pair set.
  have hpair : ∀ p ∈ closePairs net j,
      μ {ω | a < |X p.2 ω - X p.1 ω|} ≤ B := by
    intro p hp
    -- Distance bound: dist p.1 p.2 ≤ 6·2^{-j} (filter predicate).
    have hdist : dist p.1 p.2 ≤ 6 * (2 : ℝ) ^ (-(j : ℤ)) := mem_closePairs_dist net j hp
    -- Proxy weakening: K²·dist² ≤ σ_j².
    have hproxy : K ^ 2 * dist p.2 p.1 ^ 2 ≤ σsq := by
      rw [hσsq, dist_comm p.2 p.1]
      have h0 : (0 : ℝ) ≤ dist p.1 p.2 := dist_nonneg
      have hr : (0 : ℝ) ≤ 6 * (2 : ℝ) ^ (-(j : ℤ)) := by positivity
      have hsq : dist p.1 p.2 ^ 2 ≤ (6 * (2 : ℝ) ^ (-(j : ℤ))) ^ 2 := by
        apply sq_le_sq' <;> nlinarith [hdist, h0]
      nlinarith [sq_nonneg K, hsq]
    -- Sub-Gaussian one-sided tails for Y = X p.2 - X p.1 and its negation.
    have hSGp := hSG p.2 p.1
    have hSGn := hSGp.neg
    set Y : Ω → ℝ := fun ω => X p.2 ω - X p.1 ω with hY
    have htail_right : μ {ω | a < Y ω} ≤ ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * σsq))) :=
      tail_one_sided_le hSGp ha hproxy
    have htail_left : μ {ω | a < (-Y) ω} ≤ ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * σsq))) :=
      tail_one_sided_le hSGn ha hproxy
    have hcover : {ω | a < |X p.2 ω - X p.1 ω|}
        ⊆ {ω | a < Y ω} ∪ {ω | a < (-Y) ω} := by
      intro ω hω
      rw [Set.mem_setOf_eq] at hω
      rcases lt_abs.mp hω with h | h
      · left; exact h
      · right; rw [Set.mem_setOf_eq]; simpa [hY] using h
    calc μ {ω | a < |X p.2 ω - X p.1 ω|}
        ≤ μ ({ω | a < Y ω} ∪ {ω | a < (-Y) ω}) := measure_mono hcover
      _ ≤ μ {ω | a < Y ω} + μ {ω | a < (-Y) ω} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * σsq)))
            + ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * σsq))) := add_le_add htail_right htail_left
      _ = B := by rw [hB]; ring
  -- Union bound over the finite close-pair set.
  calc μ (bigOsc X net j a)
      = μ (⋃ p ∈ closePairs net j, {ω | a < |X p.2 ω - X p.1 ω|}) := rfl
    _ ≤ ∑ p ∈ closePairs net j, μ {ω | a < |X p.2 ω - X p.1 ω|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ closePairs net j, B := Finset.sum_le_sum hpair
    _ = (closePairs net j).card • B := by rw [Finset.sum_const]
    _ = (closePairs net j).card * B := by rw [nsmul_eq_mul]

/-- **Summability of the level-oscillation masses (close-pair Dudley schedule).**
For the Dudley-summable threshold schedule, the total mass
`∑' j, μ (bigOsc net j (a j))` is finite (the Borel–Cantelli hypothesis), and the
schedule is itself modulus-summable.

The schedule used is `a j = (6·K·2^{-j})·√(2·(log(2·#closePairs j) + 2·log(j+2)))`.
With `σ_j² = K²·(6·2^{-j})²` this collapses the `j`-th mass to `1/(j+2)²`.  The
card bound `#closePairs ≤ #net²` gives
`log(2·#closePairs) ≤ log 2 + 2·log(#net)` and hence
`√(log(2·#closePairs)) ≤ √(log 2) + √2·√(log(2·#net))` by sqrt-subadditivity, so
`Summable a` follows from `hDudley` + `summable_pow_neg_sqrt_log`. -/
theorem summable_bigOsc
    (hK : 0 ≤ K)
    (net : ℕ → Finset T)
    (hSG : ∀ s t, ProbabilityTheory.HasSubgaussianMGF (fun ω => X s ω - X t ω)
      ⟨K ^ 2 * dist s t ^ 2, by positivity⟩ μ)
    (hDudley : Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card)))) :
    ∃ a : ℕ → ℝ, (∀ j, 0 < a j) ∧ Summable a ∧
      (∑' j, μ (bigOsc X net j (a j))) ≠ ∞ := by
  classical
  by_cases hK0 : K = 0
  · -- Degenerate proxy: every increment is a.e. 0, so any positive summable
    -- schedule gives null level events.  Use `a j = 2^{-j}`.
    refine ⟨fun j => (2 : ℝ) ^ (-(j : ℤ)), fun j => by positivity, ?_, ?_⟩
    · have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
      apply (summable_geometric_of_norm_lt_one hr).congr
      intro j
      rw [zpow_neg, ← inv_zpow, zpow_natCast]; norm_num
    · have hzero : ∀ j : ℕ, μ (bigOsc X net j ((2 : ℝ) ^ (-(j : ℤ)))) = 0 := by
        intro j
        refine le_antisymm ?_ (zero_le)
        have hpair : ∀ p ∈ closePairs net j,
            μ {ω | (2 : ℝ) ^ (-(j : ℤ)) < |X p.2 ω - X p.1 ω|} = 0 := by
          intro p _
          have hcz : (⟨K ^ 2 * dist p.2 p.1 ^ 2, by positivity⟩ : ℝ≥0) = 0 := by
            apply Subtype.ext
            change K ^ 2 * dist p.2 p.1 ^ 2 = ((0 : ℝ≥0) : ℝ)
            simp [hK0]
          have hsg := hSG p.2 p.1
          rw [hcz] at hsg
          have hae : (fun ω => X p.2 ω - X p.1 ω) =ᵐ[μ] 0 :=
            hsg.ae_eq_zero_of_hasSubgaussianMGF_zero
          have hsub : {ω | (2 : ℝ) ^ (-(j : ℤ)) < |X p.2 ω - X p.1 ω|}
              ⊆ {ω | X p.2 ω - X p.1 ω ≠ (0 : Ω → ℝ) ω} := by
            intro ω hω
            rw [Set.mem_setOf_eq] at hω ⊢
            simp only [Pi.zero_apply]
            intro hz
            rw [hz, abs_zero] at hω
            exact absurd hω (not_lt.mpr (by positivity))
          exact measure_mono_null hsub (ae_iff.mp hae)
        calc μ (bigOsc X net j ((2 : ℝ) ^ (-(j : ℤ))))
            = μ (⋃ p ∈ closePairs net j, {ω | (2 : ℝ) ^ (-(j : ℤ)) < |X p.2 ω - X p.1 ω|}) := rfl
          _ ≤ ∑ p ∈ closePairs net j, μ {ω | (2 : ℝ) ^ (-(j : ℤ)) < |X p.2 ω - X p.1 ω|} :=
              measure_biUnion_finset_le _ _
          _ = 0 := by rw [Finset.sum_eq_zero hpair]
      have htsum : (∑' j, μ (bigOsc X net j ((2 : ℝ) ^ (-(j : ℤ))))) = 0 := by
        rw [show (fun j => μ (bigOsc X net j ((2 : ℝ) ^ (-(j : ℤ)))))
              = (fun _ : ℕ => (0 : ℝ≥0∞)) from funext hzero, tsum_zero]
      rw [htsum]; exact ENNReal.zero_ne_top
  · -- Nondegenerate proxy `0 < K`.
    have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    -- Abbreviations for the schedule.
    set Lj : ℕ → ℝ := fun j => Real.log (2 * (closePairs net j).card) with hLj
    set Mj : ℕ → ℝ := fun j => 2 * Real.log ((j : ℝ) + 2) with hMj
    set σj : ℕ → ℝ := fun j => 6 * K * (2 : ℝ) ^ (-(j : ℤ)) with hσj
    set a : ℕ → ℝ := fun j => σj j * Real.sqrt (2 * (Lj j + Mj j)) with ha
    have hσpos : ∀ j, 0 < σj j := fun j => by rw [hσj]; positivity
    have hLnn : ∀ j, 0 ≤ Lj j := by
      intro j
      simp only [hLj]
      rcases Nat.eq_zero_or_pos (closePairs net j).card with h0 | hpos
      · rw [h0]; simp
      · apply Real.log_nonneg
        have : (1 : ℝ) ≤ (closePairs net j).card := by exact_mod_cast hpos
        linarith
    have hMpos : ∀ j, 0 < Mj j := by
      intro j
      simp only [hMj]
      have h1 : (1 : ℝ) < (j : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j; linarith
      have := Real.log_pos h1
      linarith
    have hargpos : ∀ j, 0 < 2 * (Lj j + Mj j) := by
      intro j; have := hLnn j; have := hMpos j; linarith
    have hapos : ∀ j, 0 < a j := by
      intro j; rw [ha]; exact mul_pos (hσpos j) (Real.sqrt_pos.mpr (hargpos j))
    -- The denominator-half from `measure_bigOsc_le`: `D j = K²·(6·2^{-j})² = σj j²`.
    set Dj : ℕ → ℝ := fun j => K ^ 2 * (6 * (2 : ℝ) ^ (-(j : ℤ))) ^ 2 with hDj
    have hDpos : ∀ j, 0 < Dj j := fun j => by rw [hDj]; positivity
    have hσsq : ∀ j, σj j ^ 2 = Dj j := by
      intro j; rw [hσj, hDj]; ring
    -- Per-term bound: `μ (bigOsc j (a j)) ≤ ofReal (1/(j+2)²)`.
    have hterm : ∀ j, μ (bigOsc X net j (a j)) ≤ ENNReal.ofReal (1 / ((j : ℝ) + 2) ^ 2) := by
      intro j
      rcases Nat.eq_zero_or_pos (closePairs net j).card with h0 | hpos
      · -- Empty close-pair set ⟹ bigOsc is empty.
        have hempty : closePairs net j = ∅ := Finset.card_eq_zero.mp h0
        have : bigOsc X net j (a j) = ∅ := by
          rw [bigOsc, hempty]; simp
        rw [this, measure_empty]; exact zero_le
      · have hcardpos : (0 : ℝ) < (closePairs net j).card := by exact_mod_cast hpos
        have hbound := measure_bigOsc_le hK net hSG j (a := a j) (hapos j).le
        have hexparg : -(a j) ^ 2 / (2 * Dj j) = -(Lj j + Mj j) := by
          rw [ha]
          simp only
          rw [mul_pow, Real.sq_sqrt (le_of_lt (hargpos j)), hσsq j]
          rw [show Dj j * (2 * (Lj j + Mj j)) = (Lj j + Mj j) * (2 * Dj j) by ring,
            neg_div, mul_div_assoc, div_self (by positivity : (2 * Dj j) ≠ 0), mul_one]
        rw [hexparg] at hbound
        have hexp_collapse : Real.exp (-(Lj j + Mj j))
            = (1 / (2 * (closePairs net j).card)) * (1 / ((j : ℝ) + 2) ^ 2) := by
          rw [hLj, hMj]
          simp only
          rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg]
          rw [Real.exp_log (by positivity)]
          rw [show (2 : ℝ) * Real.log ((j : ℝ) + 2) = Real.log (((j : ℝ) + 2) ^ 2) by
            rw [Real.log_pow]; push_cast; ring]
          rw [Real.exp_log (by positivity)]
          rw [one_div, one_div]
        rw [hexp_collapse] at hbound
        refine hbound.trans (le_of_eq ?_)
        have hcollapse : ((closePairs net j).card : ℝ≥0∞)
            * (2 * ENNReal.ofReal (1 / (2 * (closePairs net j).card) * (1 / ((j : ℝ) + 2) ^ 2)))
            = ENNReal.ofReal (1 / ((j : ℝ) + 2) ^ 2) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_natCast (closePairs net j).card,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hcard : ((closePairs net j).card : ℝ) ≠ 0 := by positivity
          field_simp
        exact hcollapse
    refine ⟨a, hapos, ?_, ?_⟩
    · -- Summable a.  Dominate `a j ≤ σj j·√(2 Lj j) + σj j·√(2 Mj j)` (sqrt-subadditivity),
      -- and show each summand summable.  Part 1 uses the card bound `#closePairs ≤ #net²`.
      have hB1 : Summable (fun j : ℕ => σj j * Real.sqrt (2 * Lj j)) := by
        -- `√(log(2·#closePairs j)) ≤ √(log 2) + √2·√(log(2·#net j))` via `#cP ≤ #net²`.
        -- Dominate `σj j·√(2 Lj j)` by a sum of two summable series.
        -- First, the close-pair card bound and the resulting log bound.
        have hlogbnd : ∀ j, Real.log (2 * (closePairs net j).card)
            ≤ Real.log 2 + 2 * Real.log (2 * (net j).card) := by
          intro j
          -- log(2 #cP) ≤ log(2 · #net²) = log 2 + 2 log #net.
          -- and log 2 + 2 log #net ≤ log 2 + 2 log(2 #net).
          have hcard : ((closePairs net j).card : ℝ) ≤ ((net j).card : ℝ) ^ 2 := by
            have := closePairs_card_le net j
            calc ((closePairs net j).card : ℝ)
                ≤ (((net j).card ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
              _ = ((net j).card : ℝ) ^ 2 := by push_cast; ring
          rcases Nat.eq_zero_or_pos (closePairs net j).card with h0 | hcp_pos
          · -- #cP = 0 ⟹ log(2·0) = log 0 = 0 ≤ RHS (both log terms ≥ 0).
            rw [h0]; simp only [Nat.cast_zero, mul_zero, Real.log_zero]
            have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            have hnet : (0 : ℝ) ≤ Real.log (2 * (net j).card) := by
              rcases Nat.eq_zero_or_pos (net j).card with h0' | hp
              · rw [h0']; simp
              · apply Real.log_nonneg
                have : (1 : ℝ) ≤ (net j).card := by exact_mod_cast hp
                linarith
            linarith
          · -- #cP ≥ 1; then #net ≥ 1 too (since #cP ≤ #net²).
            have hcp1 : (1 : ℝ) ≤ (closePairs net j).card := by exact_mod_cast hcp_pos
            -- #net ≥ 1: since `1 ≤ #cP ≤ #net²`, `#net` cannot be `0`.
            have hnet_ne : (net j).card ≠ 0 := by
              intro hz
              rw [hz] at hcard
              simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                zero_pow] at hcard
              linarith [hcp1, hcard]
            have hnet1 : (1 : ℝ) ≤ (net j).card := by
              have : 1 ≤ (net j).card := Nat.one_le_iff_ne_zero.mpr hnet_ne
              exact_mod_cast this
            -- log(2 #cP) ≤ log(2 #net²) = log 2 + log(#net²) = log 2 + 2 log #net.
            have hstep1 : Real.log (2 * (closePairs net j).card)
                ≤ Real.log (2 * (net j).card ^ 2) := by
              apply Real.log_le_log (by positivity)
              nlinarith [hcard]
            have hstep2 : Real.log (2 * (net j).card ^ 2)
                = Real.log 2 + 2 * Real.log (net j).card := by
              rw [Real.log_mul (by norm_num)
                    (by positivity : ((net j).card : ℝ) ^ 2 ≠ 0),
                Real.log_pow]
              push_cast; ring
            have hstep3 : Real.log (net j).card
                ≤ Real.log (2 * (net j).card) := by
              apply Real.log_le_log (by linarith)
              nlinarith [hnet1]
            have hcombine : Real.log 2 + 2 * Real.log (net j).card
                ≤ Real.log 2 + 2 * Real.log (2 * (net j).card) := by
              linarith [hstep3]
            -- combine
            calc Real.log (2 * (closePairs net j).card)
                ≤ Real.log 2 + 2 * Real.log (net j).card := hstep1.trans (le_of_eq hstep2)
              _ ≤ Real.log 2 + 2 * Real.log (2 * (net j).card) := hcombine
        -- sqrt-subadditivity: √(2 Lj) ≤ √(log 2) ·? — bound √(Lj) ≤ √(log 2) + √2 √(log(2#net)).
        have hsqrtbnd : ∀ j, Real.sqrt (2 * Lj j)
            ≤ Real.sqrt 2 * (Real.sqrt (Real.log 2)
                + Real.sqrt 2 * Real.sqrt (Real.log (2 * (net j).card))) := by
          intro j
          set Nj : ℝ := Real.log (2 * (net j).card) with hNjdef
          have hL2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          have hnetnn : (0 : ℝ) ≤ Nj := by
            rw [hNjdef]
            rcases Nat.eq_zero_or_pos (net j).card with h0' | hp
            · rw [h0']; simp
            · apply Real.log_nonneg
              have : (1 : ℝ) ≤ (net j).card := by exact_mod_cast hp
              linarith
          -- √(Lj) ≤ √(log 2 + 2·Nj) ≤ √(log2) + √(2·Nj) = √(log2)+√2·√(Nj).
          have hLjbnd : Real.sqrt (Lj j)
              ≤ Real.sqrt (Real.log 2) + Real.sqrt 2 * Real.sqrt Nj := by
            have h1 : Real.sqrt (Lj j) ≤ Real.sqrt (Real.log 2 + 2 * Nj) := by
              apply Real.sqrt_le_sqrt
              simpa [hLj, hNjdef] using hlogbnd j
            refine h1.trans ?_
            -- √(x+y) ≤ √x + √y with x = log2, y = 2·Nj.
            have hx : (0 : ℝ) ≤ Real.log 2 := hL2nn
            have hy : (0 : ℝ) ≤ 2 * Nj := by linarith
            have hsub : Real.sqrt (Real.log 2 + 2 * Nj)
                ≤ Real.sqrt (Real.log 2) + Real.sqrt (2 * Nj) := by
              rw [show Real.sqrt (Real.log 2) + Real.sqrt (2 * Nj)
                    = Real.sqrt ((Real.sqrt (Real.log 2) + Real.sqrt (2 * Nj)) ^ 2) from
                (Real.sqrt_sq (by positivity)).symm]
              apply Real.sqrt_le_sqrt
              have hcross : 0 ≤ 2 * Real.sqrt (Real.log 2) * Real.sqrt (2 * Nj) := by positivity
              nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, hcross,
                Real.sqrt_nonneg (Real.log 2), Real.sqrt_nonneg (2 * Nj)]
            refine hsub.trans (le_of_eq ?_)
            rw [Real.sqrt_mul (by norm_num)]
          -- √(2 Lj) = √2·√(Lj) ≤ √2·(…).
          rw [Real.sqrt_mul (by norm_num)]
          exact mul_le_mul_of_nonneg_left hLjbnd (Real.sqrt_nonneg 2)
        -- Dominate `σj j·√(2 Lj j)` by the displayed dyadic entropy term.
        have hbound : ∀ j, σj j * Real.sqrt (2 * Lj j)
            ≤ (6 * K * Real.sqrt 2) * (Real.sqrt (Real.log 2) * (2 : ℝ) ^ (-(j : ℤ)))
              + (6 * K * Real.sqrt 2 * Real.sqrt 2)
                * ((2 : ℝ) ^ (-(j : ℤ))
                  * Real.sqrt (Real.log (2 * (net j).card))) := by
          intro j
          have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(j : ℤ)) := by positivity
          calc σj j * Real.sqrt (2 * Lj j)
              ≤ σj j * (Real.sqrt 2 * (Real.sqrt (Real.log 2)
                  + Real.sqrt 2 * Real.sqrt (Real.log (2 * (net j).card)))) :=
                mul_le_mul_of_nonneg_left (hsqrtbnd j) (hσpos j).le
            _ = (6 * K * Real.sqrt 2) * (Real.sqrt (Real.log 2) * (2 : ℝ) ^ (-(j : ℤ)))
                + (6 * K * Real.sqrt 2 * Real.sqrt 2)
                  * ((2 : ℝ) ^ (-(j : ℤ))
                    * Real.sqrt (Real.log (2 * (net j).card))) := by
                rw [hσj]; ring
        apply Summable.of_nonneg_of_le (fun j => by rw [hσj]; positivity) hbound
        -- The dominating series is a sum of two summable series.
        apply Summable.add
        · -- `∑ √(log2)·2^{-j}` is √(log2) times a geometric series, scaled.
          apply Summable.mul_left
          have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
          have hgeo : Summable (fun j : ℕ => (2 : ℝ) ^ (-(j : ℤ))) := by
            apply (summable_geometric_of_norm_lt_one hr).congr
            intro j; rw [zpow_neg, ← inv_zpow, zpow_natCast]; norm_num
          apply (hgeo.mul_left (Real.sqrt (Real.log 2))).congr
          intro j; ring
        · -- `∑ 2^{-j}·√(log(2#net j))` = `hDudley`, scaled.
          exact hDudley.mul_left _
      -- Part 2: `∑ σj j·√(2 Mj j) = ∑ 12·K·2^{-j}·√(log(j+2))`, summable.
      have hB2 : Summable (fun j : ℕ => σj j * Real.sqrt (2 * Mj j)) := by
        have heq : ∀ j, σj j * Real.sqrt (2 * Mj j)
            = (12 * K) * ((2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log ((j : ℝ) + 2))) := by
          intro j
          rw [hσj, hMj]
          simp only
          rw [show (2 : ℝ) * (2 * Real.log ((j : ℝ) + 2)) = (2 ^ 2) * Real.log ((j : ℝ) + 2) by
            ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
          ring
        apply (Summable.mul_left (12 * K) summable_pow_neg_sqrt_log).congr
        intro j; rw [heq]
      -- Combine: `a j ≤ σj j·√(2 Lj j) + σj j·√(2 Mj j)`.
      apply Summable.of_nonneg_of_le (fun j => (hapos j).le) ?_ (hB1.add hB2)
      intro j
      rw [ha]
      simp only
      rw [show (2 : ℝ) * (Lj j + Mj j) = 2 * Lj j + 2 * Mj j by ring]
      have hsub : Real.sqrt (2 * Lj j + 2 * Mj j)
          ≤ Real.sqrt (2 * Lj j) + Real.sqrt (2 * Mj j) := by
        have h2L : (0 : ℝ) ≤ 2 * Lj j := by have := hLnn j; linarith
        have h2M : (0 : ℝ) ≤ 2 * Mj j := by have := (hMpos j).le; linarith
        rw [show Real.sqrt (2 * Lj j) + Real.sqrt (2 * Mj j)
              = Real.sqrt ((Real.sqrt (2 * Lj j) + Real.sqrt (2 * Mj j)) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
        apply Real.sqrt_le_sqrt
        have hcross : 0 ≤ 2 * Real.sqrt (2 * Lj j) * Real.sqrt (2 * Mj j) := by positivity
        nlinarith [Real.sq_sqrt h2L, Real.sq_sqrt h2M, hcross,
          Real.sqrt_nonneg (2 * Lj j), Real.sqrt_nonneg (2 * Mj j)]
      calc σj j * Real.sqrt (2 * Lj j + 2 * Mj j)
          ≤ σj j * (Real.sqrt (2 * Lj j) + Real.sqrt (2 * Mj j)) := by
            apply mul_le_mul_of_nonneg_left hsub (hσpos j).le
        _ = σj j * Real.sqrt (2 * Lj j) + σj j * Real.sqrt (2 * Mj j) := by ring
    · -- ∑' μ (bigOsc) ≠ ∞.
      have hpser : Summable (fun j : ℕ => 1 / ((j : ℝ) + 2) ^ 2) := by
        have hbase : Summable (fun j : ℕ => 1 / ((j : ℝ)) ^ 2) :=
          Real.summable_one_div_nat_pow.mpr (by norm_num : (1 : ℕ) < 2)
        have := (summable_nat_add_iff 2).mpr hbase
        simpa using this
      have hfin : (∑' j : ℕ, ENNReal.ofReal (1 / ((j : ℝ) + 2) ^ 2)) ≠ ∞ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hpser]
        exact ENNReal.ofReal_ne_top
      refine ne_of_lt (lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hfin))
      exact ENNReal.tsum_le_tsum hterm

/-! ### Borel–Cantelli helpers for `aeUC_via_borelCantelli` -/

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **Consecutive projections are a close pair at the finer scale.** The link
`(π_m t, π_{m+1} t)` lives in `closePairs net (m+1)`: both endpoints are in
`net (m+1)` (`π_m t ∈ net m ⊆ net (m+1)` by nesting, `π_{m+1} t ∈ net (m+1)`)
and `dist (π_m t) (π_{m+1} t) ≤ 3·2^{-m} = 6·2^{-(m+1)}`. -/
private theorem mem_closePairs_consecutive
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (hnet_mono : Monotone net)
    (m : ℕ) (t : T) :
    (dyadicProj net hnet m t, dyadicProj net hnet (m + 1) t) ∈ closePairs net (m + 1) := by
  classical
  -- Endpoints in `net (m+1)`.
  have h1 : dyadicProj net hnet m t ∈ net (m + 1) :=
    hnet_mono (Nat.le_succ m) (dyadicProj_mem net hnet m t)
  have h2 : dyadicProj net hnet (m + 1) t ∈ net (m + 1) := dyadicProj_mem net hnet (m + 1) t
  -- Distance bound: `3·2^{-m} = 6·2^{-(m+1)}`.
  have hd : dist (dyadicProj net hnet m t) (dyadicProj net hnet (m + 1) t)
      ≤ 3 * (2 : ℝ) ^ (-(m : ℤ)) :=
    dyadicProj_consecutive_close net hnet m t
  have heq : (3 : ℝ) * (2 : ℝ) ^ (-(m : ℤ)) = 6 * (2 : ℝ) ^ (-((m : ℤ) + 1)) := by
    rw [show (-((m : ℤ) + 1)) = (-(m : ℤ)) - 1 by ring, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  refine Finset.mem_filter.mpr ⟨Finset.mk_mem_product h1 h2, ?_⟩
  have hcast : (-(((m : ℕ) + 1 : ℕ) : ℤ)) = (-((m : ℤ) + 1)) := by push_cast; ring
  calc dist (dyadicProj net hnet m t) (dyadicProj net hnet (m + 1) t)
      ≤ 3 * (2 : ℝ) ^ (-(m : ℤ)) := hd
    _ = 6 * (2 : ℝ) ^ (-((m : ℤ) + 1)) := heq
    _ = 6 * (2 : ℝ) ^ (-(((m : ℕ) + 1 : ℕ) : ℤ)) := by rw [hcast]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **Same-level projections of two nearby points are a close pair.** If
`dist s t < 2^{-J}` then `(π_J s, π_J t)` lives in `closePairs net J`:
both endpoints are in `net J` and
`dist (π_J s) (π_J t) ≤ 3·2^{-J} ≤ 6·2^{-J}`. -/
private theorem mem_closePairs_same_level
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (J : ℕ) {s t : T}
    (hst : dist s t < (2 : ℝ) ^ (-(J : ℤ))) :
    (dyadicProj net hnet J s, dyadicProj net hnet J t) ∈ closePairs net J := by
  classical
  have h1 : dyadicProj net hnet J s ∈ net J := dyadicProj_mem net hnet J s
  have h2 : dyadicProj net hnet J t ∈ net J := dyadicProj_mem net hnet J t
  refine Finset.mem_filter.mpr ⟨Finset.mk_mem_product h1 h2, ?_⟩
  -- `dist (π_J s) (π_J t) ≤ dist (π_J s) s + dist s t + dist t (π_J t) < 3·2^{-J} ≤ 6·2^{-J}`.
  have ha : dist s (dyadicProj net hnet J s) < (2 : ℝ) ^ (-(J : ℤ)) :=
    dyadicProj_dist_lt net hnet J s
  have hb : dist t (dyadicProj net hnet J t) < (2 : ℝ) ^ (-(J : ℤ)) :=
    dyadicProj_dist_lt net hnet J t
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(J : ℤ)) := by positivity
  calc dist (dyadicProj net hnet J s) (dyadicProj net hnet J t)
      ≤ dist (dyadicProj net hnet J s) s + dist s (dyadicProj net hnet J t) := dist_triangle _ _ _
    _ ≤ dist (dyadicProj net hnet J s) s + (dist s t + dist t (dyadicProj net hnet J t)) := by
        gcongr; exact dist_triangle _ _ _
    _ = dist s (dyadicProj net hnet J s) + dist s t + dist t (dyadicProj net hnet J t) := by
        rw [dist_comm (dyadicProj net hnet J s) s]; ring
    _ ≤ 6 * (2 : ℝ) ^ (-(J : ℤ)) := by linarith

/-- **Close-pair membership at a level — relaxed radius.** As
`mem_closePairs_same_level` but with the larger ball `dist s t < 2·2^{-J}` (the
projected pair is within `dist (π_J s) s + dist s t + dist t (π_J t) < 4·2^{-J}
≤ 6·2^{-J}`, the `closePairs` tolerance).  The slack `2·2^{-J}` vs `2^{-J}` is what
lets the modulus-ball transport's density limit pass a *closed* constraint
`dist f g ≤ 2^{-J}` (strictly below `2·2^{-J}`) through `le_of_tendsto`. -/
private theorem mem_closePairs_same_level'
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (J : ℕ) {s t : T}
    (hst : dist s t < 2 * (2 : ℝ) ^ (-(J : ℤ))) :
    (dyadicProj net hnet J s, dyadicProj net hnet J t) ∈ closePairs net J := by
  classical
  have h1 : dyadicProj net hnet J s ∈ net J := dyadicProj_mem net hnet J s
  have h2 : dyadicProj net hnet J t ∈ net J := dyadicProj_mem net hnet J t
  refine Finset.mem_filter.mpr ⟨Finset.mk_mem_product h1 h2, ?_⟩
  have ha : dist s (dyadicProj net hnet J s) < (2 : ℝ) ^ (-(J : ℤ)) :=
    dyadicProj_dist_lt net hnet J s
  have hb : dist t (dyadicProj net hnet J t) < (2 : ℝ) ^ (-(J : ℤ)) :=
    dyadicProj_dist_lt net hnet J t
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(J : ℤ)) := by positivity
  calc dist (dyadicProj net hnet J s) (dyadicProj net hnet J t)
      ≤ dist (dyadicProj net hnet J s) s + dist s (dyadicProj net hnet J t) := dist_triangle _ _ _
    _ ≤ dist (dyadicProj net hnet J s) s + (dist s t + dist t (dyadicProj net hnet J t)) := by
        gcongr; exact dist_triangle _ _ _
    _ = dist s (dyadicProj net hnet J s) + dist s t + dist t (dyadicProj net hnet J t) := by
        rw [dist_comm (dyadicProj net hnet J s) s]; ring
    _ ≤ 6 * (2 : ℝ) ^ (-(J : ℤ)) := by linarith

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **Vertical-leg bound.** For a skeleton point `s ∈ net jₛ`, if at
every level `m ≥ J₀` no close-pair increment exceeds `a m` (the no-`bigOsc`
condition) and `J₀ ≤ J`, then the gap between `X s ω` and `X (π_J s) ω` is
controlled by the tail of the summable schedule: `|X s ω − X (π_J s) ω| ≤ ∑' k, a (J + k)`.
The proof telescopes `X (π_{jₛ} s) − X (π_J s)` over `Ico J jₛ` (since `π_{jₛ} s = s`
by self-projection), bounds each per-level link increment by `a (m+1)` via
`mem_closePairs_consecutive`, and dominates the finite sum by the summable tail. -/
private theorem aeUC_vertical_leg
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (hnet_mono : Monotone net)
    {a : ℕ → ℝ} (ha_pos : ∀ j, 0 < a j) (ha_summable : Summable a) (ω : Ω)
    {J₀ : ℕ} (hbc : ∀ m ≥ J₀, ∀ p ∈ closePairs net m, |X p.2 ω - X p.1 ω| ≤ a m)
    {jₛ : ℕ} {s : T} (hs : s ∈ net jₛ) {J : ℕ} (hJ : J₀ ≤ J) :
    |X s ω - X (dyadicProj net hnet J s) ω| ≤ ∑' k : ℕ, a (J + k) := by
  classical
  -- Tail nonneg, summability of the shifted schedule.
  have ha_shift : Summable (fun k : ℕ => a (J + k)) := by
    have := (summable_nat_add_iff J).mpr ha_summable
    simpa [add_comm] using this
  have htail_nonneg : 0 ≤ ∑' k : ℕ, a (J + k) :=
    tsum_nonneg (fun k => (ha_pos _).le)
  rcases le_or_gt jₛ J with hle | hlt
  · -- `J ≥ jₛ`: `s ∈ net J` (nesting) ⟹ `π_J s = s`, leg is 0.
    have hsJ : s ∈ net J := hnet_mono hle hs
    rw [dyadicProj_self net hnet J s hsJ]
    simpa using htail_nonneg
  · -- `J < jₛ`: telescope over `Ico J jₛ`.
    have hJjs : J ≤ jₛ := hlt.le
    -- `π_{jₛ} s = s` by self-projection at level `jₛ`.
    have hself : dyadicProj net hnet jₛ s = s := dyadicProj_self net hnet jₛ s hs
    -- Telescope identity over `Ico J jₛ`.
    have htel : X s ω - X (dyadicProj net hnet J s) ω
        = ∑ m ∈ Finset.Ico J jₛ,
            (X (dyadicProj net hnet (m + 1) s) ω - X (dyadicProj net hnet m s) ω) := by
      have e1 := chain_telescope_path (X := X) net hnet s jₛ ω
      have e2 := chain_telescope_path (X := X) net hnet s J ω
      rw [Finset.sum_Ico_eq_sub _ hJjs, ← e1, ← e2, hself]; ring
    rw [htel]
    -- Bound `|∑| ≤ ∑ |·| ≤ ∑_{Ico J jₛ} a (m+1)`.
    calc |∑ m ∈ Finset.Ico J jₛ,
              (X (dyadicProj net hnet (m + 1) s) ω - X (dyadicProj net hnet m s) ω)|
        ≤ ∑ m ∈ Finset.Ico J jₛ,
              |X (dyadicProj net hnet (m + 1) s) ω - X (dyadicProj net hnet m s) ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ico J jₛ, a (m + 1) := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          have hmJ : J ≤ m := (Finset.mem_Ico.mp hm).1
          -- `(π_m s, π_{m+1} s) ∈ closePairs (m+1)`, and `m+1 ≥ J₀`.
          have hmem := mem_closePairs_consecutive net hnet hnet_mono m s
          have hbnd := hbc (m + 1) (by omega) _ hmem
          -- `hbnd : |X (π_{m+1} s) ω − X (π_m s) ω| ≤ a (m+1)` (p.2 = π_{m+1}, p.1 = π_m).
          simpa using hbnd
      _ = ∑ k ∈ Finset.Ico (J + 1) (jₛ + 1), a k := Finset.sum_Ico_add' a J jₛ 1
      _ ≤ ∑' k : ℕ, a (J + k) := by
          -- `Ico (J+1) (jₛ+1)` reindexes into the shifted family `fun n => a (J + n)`
          -- via `k ↦ k - J`; the map is injective there, image ⊆ ℕ, dominated by the tail.
          have hmap : ∀ k ∈ Finset.Ico (J + 1) (jₛ + 1),
              a k = (fun n : ℕ => a (J + n)) (k - J) := by
            intro k hk
            have hkJ : J + 1 ≤ k := (Finset.mem_Ico.mp hk).1
            simp only; congr 1; omega
          rw [Finset.sum_congr rfl hmap]
          have hinj : Set.InjOn (fun k => k - J) (Finset.Ico (J + 1) (jₛ + 1) : Set ℕ) := by
            intro x hx y hy hxy
            simp only [Finset.coe_Ico, Set.mem_Ico] at hx hy
            simp only at hxy
            omega
          rw [← Finset.sum_image (f := fun n : ℕ => a (J + n)) (g := fun k => k - J) hinj]
          exact Summable.sum_le_tsum _ (fun n _ => (ha_pos _).le) ha_shift

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **Deterministic-modulus telescope (the pointwise chaining bound).** Fix a
sample point `ω`.  Suppose that at every level `m ≥ J₀` the point `ω` *avoids*
the level oscillation event `bigOsc X net m (a m)` — i.e. no close net-pair at
scale `m` has an increment exceeding `a m`.  Then for any two skeleton points
`s, t ∈ T₀ = ⋃ⱼ net j` whose distance is below the dyadic scale `2^{-J}` (with
`J₀ ≤ J`), the increment `|X s ω − X t ω|` is controlled by the **deterministic
schedule** `η J = a J + 2·∑' k, a (J + k)`:

`|X s ω − X t ω| ≤ a J + 2·∑' k, a (J + k)`.

This is the pointwise crux of `aeUC_via_borelCantelli`: a triangle split into two
vertical legs (`aeUC_vertical_leg`, each `≤ ∑' k, a (J + k)`) and a horizontal
middle (`mem_closePairs_same_level`, `≤ a J`). The almost-sure statement then
follows by Borel–Cantelli; the same deterministic `η` places paths in a fixed
compact modulus ball. -/
theorem osc_le_of_avoid_bigOsc
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (hnet_mono : Monotone net)
    {a : ℕ → ℝ} (ha_pos : ∀ j, 0 < a j) (ha_summable : Summable a) (ω : Ω)
    {J₀ : ℕ} (havoid : ∀ m ≥ J₀, ω ∉ bigOsc X net m (a m))
    {J : ℕ} (hJ : J₀ ≤ J) {s t : T}
    (hs : s ∈ ⋃ j : ℕ, (↑(net j) : Set T)) (ht : t ∈ ⋃ j : ℕ, (↑(net j) : Set T))
    (hst : dist s t < (2 : ℝ) ^ (-(J : ℤ))) :
    |X s ω - X t ω| ≤ a J + 2 * ∑' k : ℕ, a (J + k) := by
  classical
  -- Convert the `bigOsc`-avoidance hypothesis into the close-pair increment bound.
  have hbound : ∀ m ≥ J₀, ∀ p ∈ closePairs net m, |X p.2 ω - X p.1 ω| ≤ a m := by
    intro m hm p hp
    have hnot := havoid m hm
    simp only [bigOsc, Set.mem_iUnion, not_exists, exists_prop, not_and] at hnot
    have := hnot p hp
    simpa [Set.mem_setOf_eq, not_lt] using this
  -- `s, t ∈ T₀`: extract their net levels.
  simp only [Set.mem_iUnion, Finset.mem_coe] at hs ht
  obtain ⟨jₛ, hsj⟩ := hs
  obtain ⟨jₜ, htj⟩ := ht
  -- Triangle split: `|X s − X t| ≤ |X s − X(π_J s)| + |X(π_J s) − X(π_J t)| + |X(π_J t) − X t|`.
  have hsplit : |X s ω - X t ω|
      ≤ |X s ω - X (dyadicProj net hnet J s) ω|
        + |X (dyadicProj net hnet J s) ω - X (dyadicProj net hnet J t) ω|
        + |X (dyadicProj net hnet J t) ω - X t ω| := by
    calc |X s ω - X t ω|
        ≤ |X s ω - X (dyadicProj net hnet J s) ω| + |X (dyadicProj net hnet J s) ω - X t ω| := by
          have := abs_sub_le (X s ω) (X (dyadicProj net hnet J s) ω) (X t ω); linarith [this]
      _ ≤ |X s ω - X (dyadicProj net hnet J s) ω|
            + (|X (dyadicProj net hnet J s) ω - X (dyadicProj net hnet J t) ω|
              + |X (dyadicProj net hnet J t) ω - X t ω|) := by
          gcongr
          exact abs_sub_le (X (dyadicProj net hnet J s) ω) (X (dyadicProj net hnet J t) ω) (X t ω)
      _ = _ := by ring
  -- Vertical legs: each ≤ ∑' k, a (J + k).
  have hleg_s : |X s ω - X (dyadicProj net hnet J s) ω| ≤ ∑' k : ℕ, a (J + k) :=
    aeUC_vertical_leg (X := X) net hnet hnet_mono ha_pos ha_summable ω hbound hsj hJ
  have hleg_t : |X (dyadicProj net hnet J t) ω - X t ω| ≤ ∑' k : ℕ, a (J + k) := by
    rw [abs_sub_comm]
    exact aeUC_vertical_leg (X := X) net hnet hnet_mono ha_pos ha_summable ω hbound htj hJ
  -- Horizontal middle: `(π_J s, π_J t) ∈ closePairs J`, increment ≤ a J.
  have hmid : |X (dyadicProj net hnet J s) ω - X (dyadicProj net hnet J t) ω| ≤ a J := by
    have hmem := mem_closePairs_same_level net hnet J hst
    have := hbound J hJ _ hmem
    rw [abs_sub_comm]
    simpa using this
  -- Combine.
  calc |X s ω - X t ω|
      ≤ |X s ω - X (dyadicProj net hnet J s) ω|
        + |X (dyadicProj net hnet J s) ω - X (dyadicProj net hnet J t) ω|
        + |X (dyadicProj net hnet J t) ω - X t ω| := hsplit
    _ ≤ (∑' k : ℕ, a (J + k)) + a J + (∑' k : ℕ, a (J + k)) := by
        gcongr
    _ = a J + 2 * ∑' k : ℕ, a (J + k) := by ring

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **Deterministic-modulus telescope — relaxed radius.** As
`osc_le_of_avoid_bigOsc`, but with the larger ball `dist s t < 2·2^{-J}` (the
horizontal close-pair tolerance `6·2^{-J}` absorbs it via
`mem_closePairs_same_level'`).  This is the form the modulus-ball `G_P`-tightness
transport consumes: its schedule constraint `dist f g ≤ 2^{-(J+k)}` is *strictly*
below `2·2^{-(J+k)}`, so the skeleton density limit passes through `le_of_tendsto`. -/
theorem osc_le_of_avoid_bigOsc'
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (hnet_mono : Monotone net)
    {a : ℕ → ℝ} (ha_pos : ∀ j, 0 < a j) (ha_summable : Summable a) (ω : Ω)
    {J₀ : ℕ} (havoid : ∀ m ≥ J₀, ω ∉ bigOsc X net m (a m))
    {J : ℕ} (hJ : J₀ ≤ J) {s t : T}
    (hs : s ∈ ⋃ j : ℕ, (↑(net j) : Set T)) (ht : t ∈ ⋃ j : ℕ, (↑(net j) : Set T))
    (hst : dist s t < 2 * (2 : ℝ) ^ (-(J : ℤ))) :
    |X s ω - X t ω| ≤ a J + 2 * ∑' k : ℕ, a (J + k) := by
  classical
  have hbound : ∀ m ≥ J₀, ∀ p ∈ closePairs net m, |X p.2 ω - X p.1 ω| ≤ a m := by
    intro m hm p hp
    have hnot := havoid m hm
    simp only [bigOsc, Set.mem_iUnion, not_exists, exists_prop, not_and] at hnot
    have := hnot p hp
    simpa [Set.mem_setOf_eq, not_lt] using this
  simp only [Set.mem_iUnion, Finset.mem_coe] at hs ht
  obtain ⟨jₛ, hsj⟩ := hs
  obtain ⟨jₜ, htj⟩ := ht
  have hsplit : |X s ω - X t ω|
      ≤ |X s ω - X (dyadicProj net hnet J s) ω|
        + |X (dyadicProj net hnet J s) ω - X (dyadicProj net hnet J t) ω|
        + |X (dyadicProj net hnet J t) ω - X t ω| := by
    calc |X s ω - X t ω|
        ≤ |X s ω - X (dyadicProj net hnet J s) ω| + |X (dyadicProj net hnet J s) ω - X t ω| := by
          have := abs_sub_le (X s ω) (X (dyadicProj net hnet J s) ω) (X t ω); linarith [this]
      _ ≤ |X s ω - X (dyadicProj net hnet J s) ω|
            + (|X (dyadicProj net hnet J s) ω - X (dyadicProj net hnet J t) ω|
              + |X (dyadicProj net hnet J t) ω - X t ω|) := by
          gcongr
          exact abs_sub_le (X (dyadicProj net hnet J s) ω) (X (dyadicProj net hnet J t) ω) (X t ω)
      _ = _ := by ring
  have hleg_s : |X s ω - X (dyadicProj net hnet J s) ω| ≤ ∑' k : ℕ, a (J + k) :=
    aeUC_vertical_leg (X := X) net hnet hnet_mono ha_pos ha_summable ω hbound hsj hJ
  have hleg_t : |X (dyadicProj net hnet J t) ω - X t ω| ≤ ∑' k : ℕ, a (J + k) := by
    rw [abs_sub_comm]
    exact aeUC_vertical_leg (X := X) net hnet hnet_mono ha_pos ha_summable ω hbound htj hJ
  have hmid : |X (dyadicProj net hnet J s) ω - X (dyadicProj net hnet J t) ω| ≤ a J := by
    have hmem := mem_closePairs_same_level' net hnet J hst
    have := hbound J hJ _ hmem
    rw [abs_sub_comm]
    simpa using this
  calc |X s ω - X t ω|
      ≤ |X s ω - X (dyadicProj net hnet J s) ω|
        + |X (dyadicProj net hnet J s) ω - X (dyadicProj net hnet J t) ω|
        + |X (dyadicProj net hnet J t) ω - X t ω| := hsplit
    _ ≤ (∑' k : ℕ, a (J + k)) + a J + (∑' k : ℕ, a (J + k)) := by
        gcongr
    _ = a J + 2 * ∑' k : ℕ, a (J + k) := by ring

/-- **A.s. uniform continuity on the countable dense skeleton via Borel–Cantelli.**
Off a `μ`-null set, only finitely many level events occur, so the dyadic
chaining sum converges uniformly and the path `t ↦ X t ω` is uniformly
continuous on the countable dense set `T₀ = ⋃ j, net j`.

Proof detail: `MeasureTheory.ae_eventually_notMem (summable_bigOsc …)` gives
`∀ᵐ ω, ∀ᶠ j, ω ∉ bigOsc net j (a j)`; combine with the telescope
`chain_telescope_path` to get a uniform Cauchy modulus on `T₀`.  UC is stated
via the pseudometric of `T` restricted to `T₀` (`UniformContinuousOn`). -/
theorem aeUC_via_borelCantelli
    (hK : 0 ≤ K)
    (hXmeas : ∀ t, Measurable (X t))
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (hnet_mono : Monotone net)
    (hSG : ∀ s t, ProbabilityTheory.HasSubgaussianMGF (fun ω => X s ω - X t ω)
      ⟨K ^ 2 * dist s t ^ 2, by positivity⟩ μ)
    (hDudley : Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card)))) :
    ∀ᵐ ω ∂μ, UniformContinuousOn (fun t => X t ω)
      (⋃ j : ℕ, (↑(net j) : Set T)) := by
  classical
  -- Step 1: Borel–Cantelli on the close-pair oscillation events.
  obtain ⟨a, ha_pos, ha_summable, ha_tsum⟩ := summable_bigOsc (X := X) hK net hSG hDudley
  have hbc := MeasureTheory.ae_eventually_notMem (μ := μ)
    (s := fun j => bigOsc X net j (a j)) ha_tsum
  -- The shifted schedule modulus `η J = a J + 2·∑' k, a (J+k)` tends to 0.
  have ha_tendsto : Filter.Tendsto a Filter.atTop (nhds 0) := ha_summable.tendsto_atTop_zero
  have htail_tendsto : Filter.Tendsto (fun J : ℕ => ∑' k : ℕ, a (J + k))
      Filter.atTop (nhds 0) := by
    have := tendsto_sum_nat_add a
    simpa [add_comm] using this
  have hη_tendsto : Filter.Tendsto (fun J : ℕ => a J + 2 * ∑' k : ℕ, a (J + k))
      Filter.atTop (nhds (0 : ℝ)) := by
    have := ha_tendsto.add (htail_tendsto.const_mul 2)
    simpa using this
  -- Filter-upwards on the a.s. Borel–Cantelli conclusion.
  filter_upwards [hbc] with ω hω
  -- From `hω` extract `J₀` and the per-level no-oscillation bound at all levels `≥ J₀`.
  rw [Filter.eventually_atTop] at hω
  obtain ⟨J₀, hJ₀⟩ := hω
  -- `hJ₀ : ∀ m ≥ J₀, ω ∉ bigOsc X net m (a m)` is exactly the avoidance hypothesis.
  -- Step 2: ε–δ modulus of continuity.
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  -- Pick `J ≥ J₀` with the deterministic modulus `η J < ε`.
  obtain ⟨J, hJJ₀, hηJ⟩ : ∃ J, J₀ ≤ J ∧ a J + 2 * ∑' k : ℕ, a (J + k) < ε := by
    have hev : ∀ᶠ J in Filter.atTop, a J + 2 * ∑' k : ℕ, a (J + k) < ε := by
      have := hη_tendsto.eventually (gt_mem_nhds hε)
      simpa using this
    rw [Filter.eventually_atTop] at hev
    obtain ⟨J₁, hJ₁⟩ := hev
    exact ⟨max J₀ J₁, le_max_left _ _, hJ₁ _ (le_max_right _ _)⟩
  refine ⟨(2 : ℝ) ^ (-(J : ℤ)), by positivity, ?_⟩
  intro s hs t ht hst
  -- The goal `dist (X s ω) (X t ω) < ε` is on ℝ; rewrite to absolute value, then
  -- invoke the deterministic-modulus telescope.
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (osc_le_of_avoid_bigOsc (X := X) net hnet hnet_mono ha_pos ha_summable ω hJ₀ hJJ₀ hs ht hst)
    hηJ

/-- **`T` is totally bounded.** Given `ε > 0`, pick a scale `j` with `2^{-j} < ε`
(Archimedean); the finite net `net j` is then a `2^{-j}`-net (`hnet`), hence an
ε-net, which is exactly the content of `Metric.totallyBounded_iff` for `Set.univ`:
it gives the finite cover `⋃ s ∈ net j, ball s ε`. -/
private theorem gc_totallyBounded_univ
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ))) :
    TotallyBounded (Set.univ : Set T) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- Pick a scale `j` with `2^{-j} < ε`.
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (2 : ℝ) ^ (-(j : ℤ)) < ε := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨j, ?_⟩
    have hpow : (2 : ℝ) ^ (-(j : ℤ)) = (1 / 2 : ℝ) ^ j := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [hpow]; exact hj
  refine ⟨(↑(net j) : Set T), (net j).finite_toSet, ?_⟩
  intro t _
  obtain ⟨s, hsS, hd⟩ := hnet j t
  exact Set.mem_iUnion₂.mpr ⟨s, hsS, by simpa [Metric.mem_ball] using lt_trans hd hj⟩

/-- **`T₀ = ⋃ⱼ net j` is dense.** Given `x` and `r > 0`, pick a scale
`j` with `2^{-j} < r` (Archimedean), then `hnet` gives a net point
`s ∈ net j ⊆ T₀` within `2^{-j} < r` of `x`. -/
private theorem gc_dense_iUnion
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ))) :
    Dense (⋃ j : ℕ, (↑(net j) : Set T)) := by
  rw [Metric.dense_iff]
  intro x r hr
  -- Pick a scale `j` with `2^{-j} < r`.
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (2 : ℝ) ^ (-(j : ℤ)) < r := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨j, ?_⟩
    have hpow : (2 : ℝ) ^ (-(j : ℤ)) = (1 / 2 : ℝ) ^ j := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [hpow]; exact hj
  obtain ⟨s, hsmem, hd⟩ := hnet j x
  refine ⟨s, ?_, ?_⟩
  · rw [Metric.mem_ball']; exact lt_trans hd hj
  · exact Set.mem_iUnion.mpr ⟨j, by simpa using hsmem⟩

/-- **A.e. bounded + UC on the explicit skeleton `⋃ j, net j`** (the shared core of
both `gaussianChaining_UC` and its explicit-witness variant). A.s. UC comes from
`aeUC_via_borelCantelli`; a.s. boundedness follows because the UC image of the
totally bounded `⋃ j, net j` is totally bounded, hence bounded. -/
private theorem gaussianChaining_UC_iUnion_aux
    (hK : 0 ≤ K)
    (hXmeas : ∀ t, Measurable (X t))
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (hnet_mono : Monotone net)
    (hSG : ∀ s t, ProbabilityTheory.HasSubgaussianMGF (fun ω => X s ω - X t ω)
      ⟨K ^ 2 * dist s t ^ 2, by positivity⟩ μ)
    (hDudley : Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card)))) :
    ∀ᵐ ω ∂μ, (BddAbove (Set.range
        (fun t : (⋃ j : ℕ, (↑(net j) : Set T)) => |X t ω|))) ∧
      UniformContinuousOn (fun t => X t ω) (⋃ j : ℕ, (↑(net j) : Set T)) := by
  classical
  -- `T₀ = ⋃ j, net j` is totally bounded (subset of the totally bounded `T`).
  have hT₀_tb : TotallyBounded (⋃ j : ℕ, (↑(net j) : Set T)) :=
    (gc_totallyBounded_univ net hnet).subset (Set.subset_univ _)
  filter_upwards [aeUC_via_borelCantelli hK hXmeas net hnet hnet_mono hSG hDudley] with ω hUC
  refine ⟨?_, hUC⟩
  -- BddAbove: `fun t : T₀ => |X t ω|` is uniformly continuous on the totally
  -- bounded `T₀`, so its range is totally bounded, hence bounded above.
  have hres : UniformContinuous
      ((⋃ j : ℕ, (↑(net j) : Set T)).restrict (fun t => X t ω)) :=
    (uniformContinuousOn_iff_restrict).mp hUC
  have habs : UniformContinuous
      (fun t : ↥(⋃ j : ℕ, (↑(net j) : Set T)) => |X t ω|) :=
    Real.uniformContinuous_abs.comp hres
  have huniv_tb : TotallyBounded
      (Set.univ : Set ↥(⋃ j : ℕ, (↑(net j) : Set T))) := by
    refine (totallyBounded_image_iff
      (isUniformEmbedding_subtype_val.toIsUniformInducing)).mp ?_
    rwa [Subtype.coe_image_univ]
  have hrange_tb : TotallyBounded
      (Set.range (fun t : ↥(⋃ j : ℕ, (↑(net j) : Set T)) => |X t ω|)) := by
    rw [← Set.image_univ]
    exact huniv_tb.image habs
  exact hrange_tb.isBounded.bddAbove

/-- **Gaussian chaining: a.s. bounded, uniformly-continuous paths.**
For a sub-Gaussian-increment process over a totally bounded pseudometric index
with finite Dudley entropy, there is a countable dense set `T₀` on which the
sample paths are a.s. bounded and uniformly continuous.  This is the analytic
heart of the `P`-Brownian-bridge existence (vdV §19.2 / §18.1).

Built from `aeUC_via_borelCantelli` (a.s. UC on the skeleton); a.s. boundedness
then follows because a uniformly continuous map on the totally bounded `T₀` has
totally bounded (hence bounded) range. `T₀ = ⋃ j, net j`; its density is
the `2^{-j} → 0` net coverage; countability is a countable union of finite sets.

This conclusion supplies the uniformly continuous path field used in the
construction of `G_P` and `IsPBrownianBridge`. -/
theorem gaussianChaining_UC
    (hK : 0 ≤ K)
    (hXmeas : ∀ t, Measurable (X t))
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (hnet_mono : Monotone net)
    (hSG : ∀ s t, ProbabilityTheory.HasSubgaussianMGF (fun ω => X s ω - X t ω)
      ⟨K ^ 2 * dist s t ^ 2, by positivity⟩ μ)
    (hDudley : Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card)))) :
    ∃ T₀ : Set T, T₀.Countable ∧ Dense T₀ ∧
      (∀ᵐ ω ∂μ, (BddAbove (Set.range (fun t : T₀ => |X t ω|))) ∧
                UniformContinuousOn (fun t => X t ω) T₀) :=
  ⟨⋃ j : ℕ, (↑(net j) : Set T),
    Set.countable_iUnion (fun j => (net j).finite_toSet.countable),
    gc_dense_iUnion net hnet,
    gaussianChaining_UC_iUnion_aux hK hXmeas net hnet hnet_mono hSG hDudley⟩

/-- **Explicit-witness Gaussian chaining (skeleton = `⋃ j, net j`).** Identical
content to `gaussianChaining_UC`, but with the dense skeleton named explicitly as
the dyadic union `⋃ j, net j` rather than hidden behind an existential.  The
modulus-ball `G_P`-tightness transport (`PBridgeTight`) needs the skeleton and the
chaining oscillation net to be the **same** set; this variant supplies that
alignment definitionally. -/
theorem gaussianChaining_UC_iUnion
    (hK : 0 ≤ K)
    (hXmeas : ∀ t, Measurable (X t))
    (net : ℕ → Finset T)
    (hnet : ∀ (j : ℕ) (t : T), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (hnet_mono : Monotone net)
    (hSG : ∀ s t, ProbabilityTheory.HasSubgaussianMGF (fun ω => X s ω - X t ω)
      ⟨K ^ 2 * dist s t ^ 2, by positivity⟩ μ)
    (hDudley : Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card)))) :
    (⋃ j : ℕ, (↑(net j) : Set T)).Countable
      ∧ Dense (⋃ j : ℕ, (↑(net j) : Set T)) ∧
      (∀ᵐ ω ∂μ, (BddAbove (Set.range
          (fun t : (⋃ j : ℕ, (↑(net j) : Set T)) => |X t ω|))) ∧
        UniformContinuousOn (fun t => X t ω) (⋃ j : ℕ, (↑(net j) : Set T))) :=
  ⟨Set.countable_iUnion (fun j => (net j).finite_toSet.countable),
    gc_dense_iUnion net hnet,
    gaussianChaining_UC_iUnion_aux hK hXmeas net hnet hnet_mono hSG hDudley⟩

end GaussianChaining
