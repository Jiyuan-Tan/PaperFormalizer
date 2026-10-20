module
public import StatLean.AsymptoticStatistics.ForMathlib.Prohorov

@[expose] public section

/-!
# Convergence and boundedness in probability (varying base)

Two "in probability" notions at the project's *varying-base* level — a sequence of
statistics `X k : Ω k → G` living on per-index probability spaces `(Ω k, P k)`, laws
compared via pushforwards `(P k).map (X k)`. Mathlib's `MeasureTheory.TendstoInMeasure`
fixes a single base measure on a single space; the delta method (and the classical
Z- and M-estimator normality theorems) need the varying-base form used throughout this
project (cf. `WeakConverges`, `slutsky_of_tendstoInMeasure_dist`).

* `TendstoInProbZero P Z` — `Z k → 0` in `P k`-probability (`→ₚ 0`). Same shape as the
  `hDist` hypothesis of `WeakConverges.slutsky_of_tendstoInMeasure_dist`.
* `IsBoundedInProb P X` — the family `{X k}` is uniformly tight, i.e. bounded in
  probability, `O_P(1)`.

Main lemmas:

* `isBoundedInProb_of_weakConverges` — a weakly convergent sequence of pushforward laws
  is `O_P(1)` (Prokhorov: `weakConverges_range_tight` + compact ⟹ bounded).
* `tendstoInProbZero_of_isBoundedInProb_smul` — if `sqn k • Z k = O_P(1)` and
  `sqn k → ∞`, then `Z k →ₚ 0` (the `o_P · O_P` collapse used to get consistency of an
  estimator from the weak limit of its rescaling).
-/

open MeasureTheory Filter Topology Set

namespace AsymptoticStatistics

variable {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]

/-- **Convergence to one in inner probability.** A sequence of arbitrary events `S n`
has inner probability tending to one if it contains measurable events `E n` whose
probabilities tend to one. This formulation does not require the target events themselves
to be measurable. -/
def TendstoInnerProbOne {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (S : ℕ → Set Ξ) : Prop :=
  ∃ E : ℕ → Set Ξ, (∀ n, MeasurableSet (E n)) ∧ (∀ n, E n ⊆ S n) ∧
    Tendsto (fun n => μ.real (E n)) atTop (𝓝 1)

/-- Inner probability tending to one implies the corresponding outer-measure statement. -/
theorem TendstoInnerProbOne.tendsto_measureReal {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ] {S : ℕ → Set Ξ}
    (h : TendstoInnerProbOne μ S) :
    Tendsto (fun n => μ.real (S n)) atTop (𝓝 1) := by
  obtain ⟨E, _, hES, hE⟩ := h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hE tendsto_const_nhds
    (Eventually.of_forall fun n => measureReal_mono (hES n))
    (Eventually.of_forall fun _ => measureReal_le_one)

/-- **Convergence in probability to `0`, varying base.** For statistics `Z k : Ω k → G`
on per-index measure spaces, `Z k → 0` in `P k`-probability: the `P k`-mass of
`{ω | ε ≤ ‖Z k ω‖}` tends to `0` for every `ε > 0`. Matches the `hDist` shape of
`WeakConverges.slutsky_of_tendstoInMeasure_dist`. -/
def TendstoInProbZero {G : Type*} [NormedAddCommGroup G]
    (P : ∀ k, Measure (Ω k)) (Z : ∀ k, Ω k → G) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun k => (P k).real {ω | ε ≤ ‖Z k ω‖}) atTop (𝓝 0)

/-- **Bounded in probability (`O_P(1)`), varying base.** The family `{X k}` is uniformly
tight: for every `ε > 0` there is a threshold `M` such that the `P k`-mass of
`{ω | M < ‖X k ω‖}` is `≤ ε` for *all* `k`. -/
def IsBoundedInProb {G : Type*} [NormedAddCommGroup G]
    (P : ∀ k, Measure (Ω k)) (X : ∀ k, Ω k → G) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k, (P k).real {ω | M < ‖X k ω‖} ≤ ε

/-- **Convergence in probability implies boundedness in probability.**

The measurability hypothesis supplies tightness for the finitely many indices
preceding the eventual `o_P(1)` tail bound. -/
theorem TendstoInProbZero.isBoundedInProb
    {G : Type*} [NormedAddCommGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {Z : ∀ k, Ω k → G}
    -- Convergence to zero in probability.
    (h : TendstoInProbZero P Z)
    -- required to obtain finite-prefix tightness of the pushforward laws.
    (hZ_meas : ∀ k, Measurable (Z k)) :
    IsBoundedInProb P Z := by
  intro ε hε
  have hev : ∀ᶠ k in atTop, (P k).real {ω | (1 : ℝ) ≤ ‖Z k ω‖} < ε :=
    (h 1 zero_lt_one).eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hindiv : ∀ k : ℕ, ∃ M : ℝ, (P k).real {ω | M < ‖Z k ω‖} ≤ ε := by
    intro k
    set s : ℕ → Set (Ω k) := fun M => {ω | (M : ℝ) < ‖Z k ω‖} with hs_def
    have hmeas : ∀ M, MeasurableSet (s M) :=
      fun M => measurableSet_lt measurable_const (hZ_meas k).norm
    have hanti : Antitone s := by
      intro a b hab ω hω
      change (b : ℝ) < ‖Z k ω‖ at hω
      change (a : ℝ) < ‖Z k ω‖
      exact lt_of_le_of_lt (by exact_mod_cast hab) hω
    have hiInter : (⋂ M, s M) = ∅ := by
      ext ω
      simp only [hs_def, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_lt]
      obtain ⟨M, hM⟩ := exists_nat_gt ‖Z k ω‖
      exact ⟨M, hM.le⟩
    have htends : Tendsto (fun M => (P k) (s M)) atTop (nhds ((P k) (⋂ M, s M))) :=
      tendsto_measure_iInter_atTop (fun M => (hmeas M).nullMeasurableSet) hanti
        ⟨0, measure_ne_top (P k) _⟩
    rw [hiInter, measure_empty] at htends
    have hs_eventually : ∀ᶠ M in atTop, (P k) (s M) < ENNReal.ofReal ε :=
      htends.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
    obtain ⟨M, hM⟩ := hs_eventually.exists
    refine ⟨(M : ℝ), ?_⟩
    rw [measureReal_def]
    calc
      ((P k) (s M)).toReal ≤ (ENNReal.ofReal ε).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hM.le
      _ = ε := ENNReal.toReal_ofReal hε.le
  have hprefix : ∀ K : ℕ, ∃ M : ℝ, (1 : ℝ) ≤ M ∧
      ∀ k, k < K → (P k).real {ω | M < ‖Z k ω‖} ≤ ε := by
    intro K
    induction K with
    | zero => exact ⟨1, le_rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ K ih =>
      obtain ⟨M, hM1, hM⟩ := ih
      obtain ⟨MK, hMK⟩ := hindiv K
      refine ⟨max M MK, hM1.trans (le_max_left _ _), fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact (measureReal_mono (fun ω hω =>
          lt_of_le_of_lt (le_max_left M MK) hω)).trans (hM k hlt)
      · exact (measureReal_mono (fun ω hω =>
          lt_of_le_of_lt (le_max_right M MK) hω)).trans hMK
  obtain ⟨M, hM1, hM⟩ := hprefix N
  refine ⟨M, fun k => ?_⟩
  rcases lt_or_ge k N with hk | hk
  · exact hM k hk
  · exact (measureReal_mono (fun ω hω =>
      hM1.trans (le_of_lt hω))).trans (le_of_lt (hN k hk))

/-- **A weakly convergent sequence of pushforward laws is `O_P(1)`.**

If `(P k).map (X k) ⇝ ν` with `ν` a probability measure on a Polish space `E`, then the
family `{X k}` is bounded in probability. Route: `Prohorov.weakConverges_range_tight`
gives uniform tightness of the laws; a compact tightness witness `K` is bounded, so
`{‖·‖ > M} ⊆ Kᶜ` for `M` large, and `map_apply` transports the bound back to
`(P k).real {ω | M < ‖X k ω‖}`. -/
theorem isBoundedInProb_of_weakConverges
    {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {X : ∀ k, Ω k → E} (hX_meas : ∀ k, Measurable (X k))
    {ν : Measure E} [IsProbabilityMeasure ν]
    (h_wc : WeakConverges (fun k => (P k).map (X k)) ν) :
    IsBoundedInProb P X := by
  haveI : ∀ k, IsProbabilityMeasure ((P k).map (X k)) :=
    fun k => Measure.isProbabilityMeasure_map (hX_meas k).aemeasurable
  have htight : IsTightMeasureSet (Set.range (fun k => (P k).map (X k))) :=
    Prohorov.weakConverges_range_tight _ ν h_wc
  intro ε hε
  obtain ⟨K, hK_compact, hK⟩ :=
    (Prohorov.isTightMeasureSet_range_iff_singleton_tight _).mp htight
      (ENNReal.ofReal ε) (by positivity)
  obtain ⟨r, hr⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : E)).mp hK_compact.isBounded
  refine ⟨max r 0, fun k => ?_⟩
  have hS_meas : MeasurableSet {x : E | max r 0 < ‖x‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hSKc : {x : E | max r 0 < ‖x‖} ⊆ Kᶜ := by
    intro x hx hxK
    have hxball : x ∈ Metric.closedBall (0 : E) (max r 0) :=
      (hr.trans (Metric.closedBall_subset_closedBall (le_max_left r 0))) hxK
    simp only [Metric.mem_closedBall, dist_zero_right] at hxball
    exact absurd hxball (not_le.mpr hx)
  have key : (P k) {ω | max r 0 < ‖X k ω‖}
      = ((P k).map (X k)) {x : E | max r 0 < ‖x‖} :=
    (Measure.map_apply (hX_meas k) hS_meas).symm
  have hmass : ((P k).map (X k)) {x : E | max r 0 < ‖x‖} ≤ ENNReal.ofReal ε :=
    le_trans (measure_mono hSKc) (hK k)
  rw [measureReal_def, key]
  calc (((P k).map (X k)) {x : E | max r 0 < ‖x‖}).toReal
      ≤ (ENNReal.ofReal ε).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
    _ = ε := ENNReal.toReal_ofReal hε.le

/-- **`o_P · O_P` collapse ⇒ consistency.** If `sqn k • Z k` is bounded in probability and
the deterministic scale `sqn k → ∞`, then `Z k → 0` in probability. Used to derive
`T k → θ₀` from the weak limit of `sqn k • (T k − θ₀)`. -/
theorem tendstoInProbZero_of_isBoundedInProb_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {Z : ∀ k, Ω k → E} {sqn : ℕ → ℝ}
    (h_sqn : Tendsto sqn atTop atTop)
    (h_OP : IsBoundedInProb P (fun k ω => sqn k • Z k ω)) :
    TendstoInProbZero P Z := by
  intro ε hε
  refine Metric.tendsto_atTop.mpr fun η hη => ?_
  obtain ⟨M, hM⟩ := h_OP (η / 2) (by positivity)
  have hev : ∀ᶠ k in atTop, M < |sqn k| * ε :=
    ((tendsto_abs_atTop_atTop.comp h_sqn).atTop_mul_const hε).eventually_gt_atTop M
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun k hk => ?_⟩
  have hsub : {ω | ε ≤ ‖Z k ω‖} ⊆ {ω | M < ‖sqn k • Z k ω‖} := by
    intro ω hω
    have h2 : |sqn k| * ε ≤ |sqn k| * ‖Z k ω‖ := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
    have h3 : ‖sqn k • Z k ω‖ = |sqn k| * ‖Z k ω‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    rw [Set.mem_setOf_eq, h3]
    linarith [hN k hk]
  have hle : (P k).real {ω | ε ≤ ‖Z k ω‖} ≤ η / 2 :=
    le_trans (measureReal_mono hsub) (hM k)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith

/-- **Continuous-linear-map preservation of `→ₚ 0`.** If `Z n → 0` in `μ`-probability and
`f` is a continuous linear map, then `f (Z n) → 0` in `μ`-probability. The `ε`-exceedance of
`‖f (Z n)‖` is contained in the `ε/(‖f‖+1)`-exceedance of `‖Z n‖` via `‖f z‖ ≤ ‖f‖·‖z‖`.
Reusable glue over a single base measure `μ` (the fixed-base specialization of the
varying-base `TendstoInProbZero`). -/
theorem tendstoInProbZero_clm {Ξ : Type*} [MeasurableSpace Ξ]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] {Z : ℕ → Ξ → E} (f : E →L[ℝ] F)
    (h : TendstoInProbZero (fun _ : ℕ => μ) Z) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => f (Z n ξ)) := by
  intro ε hε
  have hden : (0 : ℝ) < ‖f‖ + 1 := by positivity
  set δ : ℝ := ε / (‖f‖ + 1) with hδ_def
  have hδ_pos : 0 < δ := div_pos hε hden
  have hsub : ∀ n, {ξ | ε ≤ ‖f (Z n ξ)‖} ⊆ {ξ | δ ≤ ‖Z n ξ‖} := by
    intro n ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    have hbound : ‖f (Z n ξ)‖ ≤ ‖f‖ * ‖Z n ξ‖ := f.le_opNorm _
    rw [hδ_def, div_le_iff₀ hden]
    nlinarith [hbound, hξ, norm_nonneg (Z n ξ)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h δ hδ_pos)
    (Eventually.of_forall fun n => measureReal_nonneg)
    (Eventually.of_forall fun n => measureReal_mono (hsub n))

/-- **`O_P(1) · o_P(1) = o_P(1)` (random scalar coefficient).** If the scalar family
`A k` is bounded in probability (`O_P(1)`) and the family `Z k → 0` in probability, then
the product `A k • Z k → 0` in probability. Route: for `ε, η > 0` pick `M` with
`(P k){|A| > M} ≤ η/2` uniformly (from `hA`); then
`{ε ≤ ‖A • Z‖} = {ε ≤ |A|·‖Z‖} ⊆ {M < |A|} ∪ {ε ≤ M·‖Z‖} = {M < |A|} ∪ {ε/M ≤ ‖Z‖}`,
and the second event's mass → 0 by `hZ`. The `[IsProbabilityMeasure]` instance supplies
the finiteness for `measureReal_mono`/`measureReal_union_le`. Used to turn the vdV Taylor
remainder `ψ̈ · ‖θ̂ − θ₀‖²` (an `O_P(1)` empirical average times an `o_P(1)` distance) into
an `o_P(1)` term. -/
theorem tendstoInProbZero_of_isBoundedInProb_mul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {A : ∀ k, Ω k → ℝ} {Z : ∀ k, Ω k → G}
    (hA : IsBoundedInProb P A) (hZ : TendstoInProbZero P Z) :
    TendstoInProbZero P (fun k ω => A k ω • Z k ω) := by
  intro ε hε
  refine Metric.tendsto_atTop.mpr fun η hη => ?_
  -- Uniform threshold `M` for the `O_P(1)` family `A`, at level `η / 2`.
  obtain ⟨M, hM⟩ := hA (η / 2) (by positivity)
  -- Replace `M` by `M' := max M 1 > 0` so that `ε / M'` is a legitimate level for `hZ`.
  set M' : ℝ := max M 1 with hM'_def
  have hM'_pos : (0 : ℝ) < M' := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hMM' : M ≤ M' := le_max_left M 1
  have hlev_pos : (0 : ℝ) < ε / M' := div_pos hε hM'_pos
  -- `hZ` at level `ε / M'` eventually puts mass `< η / 2` on the exceedance set.
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hZ (ε / M') hlev_pos) (η / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  -- Off `{M < ‖A‖}` we have `‖A • Z‖ = ‖A‖ ‖Z‖ ≤ M' ‖Z‖`, so `ε ≤ ‖A • Z‖` forces
  -- `ε / M' ≤ ‖Z‖`.
  have hsub : {ω | ε ≤ ‖A k ω • Z k ω‖}
      ⊆ {ω | M < ‖A k ω‖} ∪ {ω | ε / M' ≤ ‖Z k ω‖} := by
    intro ω hω
    by_cases hbig : M < ‖A k ω‖
    · exact Or.inl hbig
    · refine Or.inr ?_
      simp only [Set.mem_setOf_eq, norm_smul] at hω ⊢
      have h1 : ‖A k ω‖ ≤ M' := (not_lt.mp hbig).trans hMM'
      have h2 : ‖A k ω‖ * ‖Z k ω‖ ≤ M' * ‖Z k ω‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      rw [div_le_iff₀ hM'_pos]
      nlinarith [hω, h2]
  have hsplit : (P k).real {ω | ε ≤ ‖A k ω • Z k ω‖}
      ≤ (P k).real {ω | M < ‖A k ω‖} + (P k).real {ω | ε / M' ≤ ‖Z k ω‖} :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hZ_small : (P k).real {ω | ε / M' ≤ ‖Z k ω‖} < η / 2 := by
    have := hN k hk
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith [hM k]

end AsymptoticStatistics
