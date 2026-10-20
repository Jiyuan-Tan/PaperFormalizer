module
public import StatLean.ConcentrationInequalities.Chaining.DudleyTail
public import StatLean.ConcentrationInequalities.Chaining.CountableSupLift
public import StatLean.ConcentrationInequalities.Chaining.SeparableProcess

@[expose] public section

/-!
# High-probability Dudley inequality with a genuine supremum

Honest `sup_{t,s ∈ T}` forms of the high-probability Dudley inequality
(HDP Remark 8.1.6 / Eq. (8.15)) over an arbitrary — possibly uncountable —
index set: the countable-subset **existential core**
`dudley_tail_three_term_exists` (the junk-free event
`{ω | ∃ t s ∈ C, thr < |X t ω − X s ω|}` via the tail lift engine), the
formal-`⨆` displays over `T` under `hsep : IsSeparableProcess X T μ`
(three-term and `200·K·(∫₀^D √log 𝒩 + u·diam)` thresholds), the countable
display `dudley_tail_countable`, and the extracted threshold arithmetic
`dudley_tail_threshold_le`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Remark 8.1.6 / Eq. (8.15); the general-`T`
forms realize the p. 227 footnote 1 ("we are assuming T is finite to avoid
measurability issues; the general case typically follows by approximation")
through separable versions.

**Proof formalization notes.** Thresholds and guards inherited verbatim from
the per-finite-subset family: the three-term threshold
`K·(9·dudleySum T + 17·diam T + 12u·diam T)` with the LEAN-ONLY summability
junk-guard `hS`, and the display threshold
`200·K·((dudleyLIntegral T D).toReal + u·diam T)` with BOTH `hS` and the
finiteness guard `hDL` (a real threshold cannot honestly encode divergent
entropy; (8.15) is vacuous there). Every threshold is a product of
nonnegatives, so the formal-`⨆` events reduce to the existential core
through `exists_pair_lt_of_lt_biSup_real` (whose `0 ≤ c` hypothesis absorbs
the `Real.sSup` junk), and the separable transport runs POINTWISE through
`exists_lt_comp_of_mem_closure` (two one-variable approximations; no
supremum transport is needed for events). Measures of the possibly
non-measurable sup events are sound: only outer-measure monotonicity and
continuity from below along a.e.-measurable finite windows are used. The
diagonal pair `t = s` is harmless on both sides (value `0`, threshold
nonnegative). Named-sorry fallback of this work item:
`dudley_tail_threshold_le` (the `nlinarith` constant arithmetic).

**Bibliographic comments.** Eq. (8.15) is HDP Exercise 8.1 (Gaussian case:
Exercise 8.2 via concentration); the chaining tail argument is standard
(Talagrand 2014, §2.2; Boucheron–Lugosi–Massart 2013, §13.1).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **High-probability Dudley inequality, existential countable-subset
core** (HDP §8.1, Eq. (8.15)): with probability at least `1 − 2e^{−u²}`, NO
pair of the countable subfamily `C ⊆ T` has oscillation exceeding the
three-term threshold. The junk-free engine stage of the formal-supremum
displays below. -/
theorem dudley_tail_three_term_exists {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- LEAN-ONLY: summable dyadic entropy (real-threshold junk-guard)
    (hS : Summable fun k : ℤ => dudleySummand T k)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    μ {ω | ∃ t ∈ C, ∃ s ∈ C,
        K * (9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T)
          < |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  classical
  -- The pair tail lift engine, fed the per-finite-subset three-term core.
  refine measure_exists_pair_lt_le_of_forall_finset
    (f := fun t s ω => |X t ω - X s ω|) hCcnt ?_
  intro F hFne hFC
  exact dudley_tail_three_term hcov hne hmeas hinc hS hu (hFC.trans hC) hFne

/-- **Threshold arithmetic** (extracted from the display form): under the
junk-guards, the three-term threshold is dominated by the display threshold
`200·((∫₀^D √log 𝒩).toReal + u·diam T)`. `K`-free; callers multiply by
`K ≥ 0`. -/
lemma dudley_tail_threshold_le {T : Set E}
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: summable dyadic entropy (real-threshold junk-guard)
    (hS : Summable fun k : ℤ => dudleySummand T k)
    -- LEAN-ONLY: finite entropy integral (real-threshold junk-guard)
    {D : ℝ} (hDL : dudleyLIntegral T D ≠ ⊤)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T
      ≤ 200 * ((dudleyLIntegral T D).toReal + u * Metric.diam T) := by
  set L : ℝ := (dudleyLIntegral T D).toReal with hLdef
  have hInt0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hdnn : 0 ≤ Metric.diam T := Metric.diam_nonneg
  -- `dudleySum T ≤ 2 L` from the ℝ≥0∞ twins.
  have hLSeq : dudleyLSum T = ENNReal.ofReal (dudleySum T) :=
    dudleyLSum_eq_ofReal_of_summable hS
  have hLS2 : dudleyLSum T ≤ 2 * dudleyLIntegral T D :=
    dudleyLSum_le_two_mul_dudleyLIntegral hcov hne hD hD0
  have h2ne : (2 * dudleyLIntegral T D) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hDL
  have hDs : dudleySum T ≤ 2 * L := by
    have hle : ENNReal.ofReal (dudleySum T) ≤ 2 * dudleyLIntegral T D := hLSeq ▸ hLS2
    have h := ENNReal.toReal_mono h2ne hle
    rwa [ENNReal.toReal_ofReal (dudleySum_nonneg T), ENNReal.toReal_mul,
      ENNReal.toReal_ofNat, ← hLdef] at h
  -- `diam T · √log 2 ≤ 8 L` from the diameter absorber.
  have hdabs : ENNReal.ofReal (Metric.diam T * Real.sqrt (Real.log 2)) ≤ 4 * dudleyLSum T :=
    ofReal_diam_mul_sqrt_log_two_le_four_mul_dudleyLSum hcov hne
  have hdiam : Metric.diam T * Real.sqrt (Real.log 2) ≤ 8 * L := by
    have hle : ENNReal.ofReal (Metric.diam T * Real.sqrt (Real.log 2))
        ≤ 4 * (2 * dudleyLIntegral T D) := le_trans hdabs (by gcongr)
    have h8ne : (4 * (2 * dudleyLIntegral T D)) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) h2ne
    have h := ENNReal.toReal_mono h8ne hle
    rw [ENNReal.toReal_ofReal (mul_nonneg hdnn (Real.sqrt_nonneg _)), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_ofNat, ← hLdef] at h
    linarith
  -- √(log 2) ≥ 68/91 (a valid lower bound: `(68/91)² ≈ 0.558 < log 2 ≈ 0.693`).
  have hL : (68 : ℝ) / 91 ≤ Real.sqrt (Real.log 2) := by
    rw [show (68 : ℝ) / 91 = Real.sqrt ((68 / 91) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.log_two_gt_d9])
  have hprod : 0 ≤ Metric.diam T * (Real.sqrt (Real.log 2) - 68 / 91) :=
    mul_nonneg hdnn (by linarith [hL])
  have hudiam : 0 ≤ u * Metric.diam T := mul_nonneg hu hdnn
  nlinarith [hDs, hdiam, hInt0, hprod, hudiam]

/-- **High-probability Dudley inequality, three-term separable supremum**
(HDP §8.1, Eq. (8.15), general `T`): for a separable version, the two-sided
oscillation supremum over `T` exceeds the three-term threshold with
probability at most `2e^{−u²}`. The nonnegative threshold absorbs the
`Real.sSup` junk branch, and the proof routes through the junk-free
existential core. -/
theorem dudley_tail_three_term_separable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- LEAN-ONLY: summable dyadic entropy (real-threshold junk-guard)
    (hS : Summable fun k : ℤ => dudleySummand T k)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | K * (9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T)
        < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  classical
  -- The three-term threshold is a product of nonnegatives (junk absorber).
  have hthr0 : (0 : ℝ) ≤ (K : ℝ) *
      (9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T) := by
    have hd : (0 : ℝ) ≤ Metric.diam T := Metric.diam_nonneg
    have hs0 : (0 : ℝ) ≤ dudleySum T := dudleySum_nonneg T
    have hud : (0 : ℝ) ≤ u * Metric.diam T := mul_nonneg hu hd
    exact mul_nonneg (NNReal.coe_nonneg K) (by nlinarith)
  obtain ⟨T₀, hT₀T, hT₀cnt, hae⟩ := hsep
  -- The formal-`⨆` event sits a.e. inside the junk-free existential core over
  -- the countable witness: two POINTWISE closure approximations, one variable
  -- at a time (no supremum transport is needed).
  refine le_trans (measure_mono_ae ?_)
    (dudley_tail_three_term_exists hcov hne hmeas hinc hS hu hT₀T hT₀cnt)
  filter_upwards [hae] with ω hω hmem
  obtain ⟨t, htT, s, hsT, hlt⟩ := exists_pair_lt_of_lt_biSup_real hthr0 hmem
  -- Approximate the first coordinate.
  obtain ⟨-, ⟨t', ht'C, rfl⟩, halt⟩ :=
    exists_lt_comp_of_mem_closure (hω t htT) (φ := fun v => |v - X s ω|)
      ((continuous_id.sub continuous_const).abs) hlt
  -- Approximate the second coordinate.
  obtain ⟨-, ⟨s', hs'C, rfl⟩, hblt⟩ :=
    exists_lt_comp_of_mem_closure (hω s hsT) (φ := fun w => |X t' ω - w|)
      ((continuous_const.sub continuous_id).abs) halt
  exact ⟨t', ht'C, s', hs'C, hblt⟩

/-- **High-probability Dudley inequality, display form, separable supremum**
(HDP §8.1, Eq. (8.15), general `T`): the two-sided oscillation supremum
exceeds `200·K·((∫₀^D √log 𝒩).toReal + u·diam T)` with probability at most
`2e^{−u²}`. Guards `hS` and `hDL` as in the per-finite-subset
`dudley_tail`. -/
theorem dudley_tail_separable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- LEAN-ONLY: summable dyadic entropy (real-threshold junk-guard)
    (hS : Summable fun k : ℤ => dudleySummand T k)
    -- LEAN-ONLY: finite entropy integral (real-threshold junk-guard)
    {D : ℝ} (hDL : dudleyLIntegral T D ≠ ⊤)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | 200 * K * ((dudleyLIntegral T D).toReal + u * Metric.diam T)
        < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  -- Absorb the display threshold into the three-term one (`K ≥ 0`), then the
  -- separable three-term form.
  have hthr := dudley_tail_threshold_le hcov hne hS hDL hD hD0 hu
  refine le_trans (measure_mono ?_)
    (dudley_tail_three_term_separable hcov hne hmeas hinc hsep hS hu)
  refine Set.setOf_subset_setOf.mpr fun ω hω => lt_of_le_of_lt ?_ hω
  calc (K : ℝ) * (9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T)
      ≤ (K : ℝ) * (200 * ((dudleyLIntegral T D).toReal + u * Metric.diam T)) :=
        mul_le_mul_of_nonneg_left hthr K.coe_nonneg
    _ = 200 * (K : ℝ) * ((dudleyLIntegral T D).toReal + u * Metric.diam T) := by ring

/-- **High-probability Dudley inequality, display form, countable supremum**
(HDP §8.1, Eq. (8.15)): the countable-`T` display with the
`200·K·((∫₀^D √log 𝒩).toReal + u·diam T)` threshold (the display twin of
the published three-term `dudley_tail_three_term_countable`). -/
theorem dudley_tail_countable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- LEAN-ONLY: summable dyadic entropy (real-threshold junk-guard)
    (hS : Summable fun k : ℤ => dudleySummand T k)
    -- LEAN-ONLY: finite entropy integral (real-threshold junk-guard)
    {D : ℝ} (hDL : dudleyLIntegral T D ≠ ⊤)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | 200 * K * ((dudleyLIntegral T D).toReal + u * Metric.diam T)
        < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  -- A countable carrier is its own separability witness (surely).
  exact dudley_tail_separable hcov hne hmeas hinc
    (IsSeparableProcess.of_countable hcnt) hS hDL hD hD0 hu

end StatLean.ConcentrationInequalities
