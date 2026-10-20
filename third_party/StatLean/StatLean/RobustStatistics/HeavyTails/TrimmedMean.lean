module
public import StatLean.RobustStatistics.ForMathlib.OrderStatPerturb
public import StatLean.RobustStatistics.LocationScale.Mean
public import StatLean.ConcentrationInequalities.Bernstein.Bernstein
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# The trimmed mean is sub-Gaussian — truncation at data-driven quantiles

Truncating at fixed levels cannot be sub-Gaussian (the levels must scale with the
confidence); the modern result — Oliveira–Orenstein (2019), presented as `LM §2.3` — is
that trimming a `log(1/δ)/n`-fraction *chosen from the data* is. This file formalizes
the sample-split variant analyzed in `LM Theorem 6`: one half of the data picks the
truncation levels as order statistics, the other half is averaged after truncation:

  `μ̂₂ₙ = (1/n) ∑ᵢ φ_{α,β}(Xᵢ)`,  `α = Y*₍εn₎`, `β = Y*₍₍₁₋ε₎n₎`, `ε = 16 log(8/δ)/(3n)`,

and `|μ̂₂ₙ − μ| ≤ 9σ√(log(8/δ)/n)` with probability `≥ 1 − δ`. Unlike median-of-means,
the trimmed mean is also robust to adversarial contamination (Lugosi–Mendelson (2021),
Ann. Statist. — bib note only; not formalized this round).

* `truncate` — the truncation function `φ_{a,b}` (`LM §2.3`); Huber's score is the
  symmetric special case `truncate (−c) c = huberPsi c`.
* `trimmedMeanAt` — the two-sample estimator with `Fin`-indexed truncation levels.
* `quantile` — `Q_p = sup{M : P(X ≥ M) ≥ 1 − p}` (`LM §2.3` proof).
* `orderStat_quantile_brackets` — the Bernstein bracketing `LM (2.6)`–`(2.7)`.
* `truncated_bias_le` / `truncated_concentration` — the two proof halves.
* `trimmedMean_deviation` — `LM Theorem 6`.

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §2.3, displays (2.6)–(2.7), Theorem 6; after R. I. Oliveira and P. Orenstein,
*The sub-Gaussian property of trimmed means* (2019). Truncation levels are Round-1
`orderStat`s; the count concentration is `ConcentrationInequalities.bernstein_inequality`.

**Closure notes (constants and route).**

* *The `3/16` of `(2.6)`–`(2.7)` is exact.* All four bracket events are upper deviations of
  a count over a half-line, so one Bernstein brick (`count_upper_deviation`) serves all
  four. Centred indicators are bounded by `1` with variance exactly `q(1−q)`, hence satisfy
  the Bernstein condition with scale `b = 1/3` — and `b = 1/3` is what produces `3/16`
  (the binding events are the `ε/2`-level ones, where the bound is attained with equality;
  the `2ε`-level events give the slacker `3/14`).
* *The `9` of Theorem 6 survives, but not through `LM`'s bias bound.* The bias is the
  **difference** `∫(α−X)⁺ − ∫(X−β)⁺` of two nonnegative tails, so it is bounded by the
  larger of the two, not by their sum; with the sharp one-sided bound `S² ≤ p(σ² + S²)`
  this gives `σ√(4r/n) ≈ 4.62 σ√(L/n)` (`truncated_bias_le_sharp`), of which the frozen
  `σ√(32r/n)` of `truncated_bias_le` is a weakening. `LM`'s own bookkeeping (add the tails,
  bound each by `σ√(8ε)`) yields `≈ 13.1 σ√(L/n)`, with which the composite constant `9` is
  unreachable. The remaining `4 σ√(L/n)` is spent on Bernstein, whose exponent is then at
  least `3 log(8/δ)` — a factor `3` of slack.
* *The conditioning step is proved, not assumed.* `block_transfer` compares the estimator to
  the constant `μ₀` rather than to the level-dependent centre `∫ φ_{α,β} dP`, which folds
  the bias into the fixed-level bound and removes the only hard measurability obligation
  (that of the parametrised integral). What is left is block independence, the product
  form of the joint law, `Measure.prod_apply`, and measurability of order statistics
  (`measurable_orderStat`, from the counting characterisation).

**Bibliographic comments.** Trimming is among the oldest robust devices (Tukey and
McLaughlin, *Sankhyā Ser. A* **25** (1963), 331–352; Bickel, *Ann. Math. Statist.* **36**
(1965), 847–858; Stigler, *Ann. Statist.* **1** (1973), 472–477), but its *non-asymptotic
sub-Gaussian* property at confidence-calibrated trim depth is recent: R. I. Oliveira and
P. Orenstein, *The sub-Gaussian property of trimmed means* (2019); the multivariate,
adversarially-contaminated optimality is Lugosi and Mendelson, "Robust multivariate mean
estimation: the optimality of trimmed mean," *Ann. Statist.* **49** (2021), 393–410.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

open StatLean.MultipleTesting in
/-- **The truncation function** `φ_{a,b}(x) = max a (min b x)` (`LM §2.3`): the identity
on `[a, b]`, clipped to the nearer endpoint outside. For `a ≤ b` this is the projection
onto `[a, b]`; Huber's score is the symmetric case `truncate (−c) c = huberPsi c`. -/
noncomputable def truncate (a b x : ℝ) : ℝ := max a (min b x)

/-- Truncation projects into the interval: `a ≤ b → truncate a b x ∈ [a, b]`. -/
theorem truncate_mem_Icc {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    truncate a b x ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left b x)⟩

/-- Truncation fixes interval points: `x ∈ [a, b] → truncate a b x = x`. -/
theorem truncate_eq_self {a b x : ℝ} (hx : x ∈ Set.Icc a b) : truncate a b x = x := by
  rw [truncate, min_eq_right hx.2, max_eq_right hx.1]

open StatLean.MultipleTesting in
/-- **The two-sample trimmed mean** (`LM §2.3`, the estimator of Theorem 6): truncate
the `x`-sample at the `a`-th and `b`-th order statistics of the independent `y`-sample
and average. The intended indices are `a = εn − 1` and `b = (1−ε)n − 1` (0-indexed) for
the trimming fraction `ε`; they are parameters here, fixed by the theorem. -/
noncomputable def trimmedMeanAt {n : ℕ} (a b : Fin n) (x y : Fin n → ℝ) : ℝ :=
  sampleMean (fun i => truncate (orderStat y a) (orderStat y b) (x i))

/-- **The upper quantile function** `Q_p = sup{M : P(X ≥ M) ≥ 1 − p}` (`LM §2.3`
proof). For a probability measure and `p ∈ (0, 1)` the defining set is nonempty and
bounded above, so the supremum is honest. -/
noncomputable def quantile (P : Measure ℝ) (p : ℝ) : ℝ :=
  sSup {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}}

/-! ### Right-tail mass: the elementary continuity bricks

`M ↦ P(X ≥ M)` is antitone with limits `1` at `−∞` and `0` at `+∞`; it is left-continuous
always (`Ici` is a decreasing intersection of `Ici`s) and right-continuous exactly when the
level carries no atom. These three facts are all the quantile lemmas below need. -/

/-- The right-tail mass `M ↦ P(X ≥ M)` is antitone. -/
private theorem tail_antitone (P : Measure ℝ) [IsProbabilityMeasure P] :
    Antitone (fun M : ℝ => P.real {x | M ≤ x}) := fun _ _ h =>
  measureReal_mono (fun _ hx => le_trans h hx)

/-- Right-tail mass tends to `1` at `−∞` (continuity from below: `⋃ M, [M, ∞) = ℝ`). -/
private theorem tail_tendsto_atBot (P : Measure ℝ) [IsProbabilityMeasure P] :
    Tendsto (fun M : ℝ => P.real {x | M ≤ x}) atBot (𝓝 1) := by
  have hU : (⋃ M : ℝ, {x : ℝ | M ≤ x}) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨x, le_rfl⟩
  have h := tendsto_measure_iUnion_atBot (μ := P) (s := fun M : ℝ => {x : ℝ | M ≤ x})
    (fun _ _ h _ hx => le_trans h hx)
  rw [hU, measure_univ] at h
  have := (ENNReal.tendsto_toReal (by simp)).comp h
  simpa [Function.comp, measureReal_def] using! this

/-- Right-tail mass tends to `0` at `+∞` (continuity from above: `⋂ M, [M, ∞) = ∅`). -/
private theorem tail_tendsto_atTop (P : Measure ℝ) [IsProbabilityMeasure P] :
    Tendsto (fun M : ℝ => P.real {x | M ≤ x}) atTop (𝓝 0) := by
  have hI : (⋂ M : ℝ, {x : ℝ | M ≤ x}) = (∅ : Set ℝ) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_le]
    exact ⟨x + 1, by linarith⟩
  have h := tendsto_measure_iInter_atTop (μ := P) (s := fun M : ℝ => {x : ℝ | M ≤ x})
    (fun _ => (measurableSet_Ici (a := _)).nullMeasurableSet)
    (fun _ _ h _ hx => le_trans h hx) ⟨0, measure_ne_top P _⟩
  rw [hI, measure_empty] at h
  have := (ENNReal.tendsto_toReal (by simp)).comp h
  simpa [Function.comp, measureReal_def] using! this

/-- Left-continuity of the right-tail mass, in the only form used: if the level `1 − p` is
attained strictly to the left of `Q`, it is attained at `Q`. -/
private theorem tail_le_of_forall_lt (P : Measure ℝ) [IsProbabilityMeasure P] {Q c : ℝ}
    (h : ∀ M, M < Q → c ≤ P.real {x | M ≤ x}) : c ≤ P.real {x | Q ≤ x} := by
  have hanti : Antitone (fun k : ℕ => {x : ℝ | Q - 1 / (k + 1) ≤ x}) := by
    intro k l hkl x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have h1 : (1 : ℝ) / (l + 1) ≤ 1 / (k + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hkl
    linarith
  have hI : (⋂ k : ℕ, {x : ℝ | Q - 1 / (k + 1) ≤ x}) = {x : ℝ | Q ≤ x} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx
      refine not_lt.1 fun hlt => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0:ℝ) < Q - x by linarith)
      have := hx k
      linarith
    · intro hx k
      have : (0:ℝ) < 1 / (k + 1) := by positivity
      linarith
  have hten := tendsto_measure_iInter_atTop (μ := P)
    (s := fun k : ℕ => {x : ℝ | Q - 1 / (k + 1) ≤ x})
    (fun _ => (measurableSet_Ici (a := _)).nullMeasurableSet) hanti ⟨0, measure_ne_top P _⟩
  rw [hI] at hten
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp hten
  refine ge_of_tendsto hreal ?_
  filter_upwards with k
  change c ≤ P.real {x : ℝ | Q - 1 / (k + 1) ≤ x}
  refine h _ ?_
  have : (0:ℝ) < 1 / (k + 1) := by positivity
  linarith

/-- The quantile's defining set is nonempty and bounded above when `0 < p < 1`
(`LM §2.3` proof, implicit): mass to the right tends to `1` at `−∞` and to `0` at
`+∞`. -/
theorem quantile_set_nonempty_bddAbove (P : Measure ℝ) [IsProbabilityMeasure P]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}}.Nonempty ∧
      BddAbove {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}} := by
  constructor
  · obtain ⟨M, hM⟩ :=
      ((tail_tendsto_atBot P).eventually_const_lt (show 1 - p < 1 by linarith)).exists
    exact ⟨M, hM.le⟩
  · obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      ((tail_tendsto_atTop P).eventually_lt_const (show (0:ℝ) < 1 - p by linarith))
    exact ⟨K, fun M hM => not_lt.1 fun hlt => absurd hM (not_le.2 (hK M hlt.le))⟩

/-- **Right-tail mass at the quantile** (`LM §2.3` proof, "in that case
`P(X ≥ Q_p) = 1 − p`"): for a nonatomic distribution the quantile achieves its level
exactly. The no-atoms hypothesis is LM's "assume `X` has a nonatomic distribution"
simplification, carried explicitly. -/
theorem measure_ge_quantile (P : Measure ℝ) [IsProbabilityMeasure P]
    -- USER-INPUT: nonatomic distribution; LM §2.3 proof ("for ease of exposition")
    (hatom : ∀ t : ℝ, P {t} = 0)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    P.real {x | quantile P p ≤ x} = 1 - p := by
  obtain ⟨hne, hbdd⟩ := quantile_set_nonempty_bddAbove P hp hp1
  have hQ : quantile P p = sSup {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}} := rfl
  refine le_antisymm ?_ (tail_le_of_forall_lt P fun M hM => ?_)
  · -- **Right-continuity at the quantile.** Beyond `Q` the defining inequality fails, and
    -- `(Q, ∞)` is the increasing union of the `[Q + 1/(k+1), ∞)`; the atom at `Q` is null.
    have hmono : Monotone (fun k : ℕ => {x : ℝ | quantile P p + 1 / (k + 1) ≤ x}) := by
      intro k l hkl x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      have h1 : (1:ℝ) / (l + 1) ≤ 1 / (k + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hkl)
      linarith
    have hU : (⋃ k : ℕ, {x : ℝ | quantile P p + 1 / (k + 1) ≤ x})
        = {x : ℝ | quantile P p < x} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨k, hk⟩
        have hpos : (0:ℝ) < 1 / (k + 1) := by positivity
        linarith
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0:ℝ) < x - quantile P p by linarith)
        exact ⟨k, by linarith⟩
    have hten := tendsto_measure_iUnion_atTop (μ := P) hmono
    rw [hU] at hten
    have hreal := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp hten
    have hlim : P.real {x : ℝ | quantile P p < x} ≤ 1 - p := by
      refine le_of_tendsto hreal ?_
      filter_upwards with k
      change P.real {x : ℝ | quantile P p + 1 / (k + 1) ≤ x} ≤ 1 - p
      by_contra hcon
      have hmem : quantile P p + 1 / (k + 1) ∈ {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}} :=
        (not_le.1 hcon).le
      have hle := le_csSup hbdd hmem
      rw [← hQ] at hle
      have hpos : (0:ℝ) < 1 / (k + 1) := by positivity
      linarith
    have hsplit : P.real {x : ℝ | quantile P p ≤ x} ≤ P.real {x : ℝ | quantile P p < x} := by
      simp only [measureReal_def]
      refine ENNReal.toReal_mono (measure_ne_top P _) ?_
      calc P {x : ℝ | quantile P p ≤ x} ≤ P ({quantile P p} ∪ {x : ℝ | quantile P p < x}) := by
            refine measure_mono fun x hx => ?_
            rcases eq_or_lt_of_le (Set.mem_setOf_eq ▸ hx) with h | h
            · exact Or.inl h.symm
            · exact Or.inr h
        _ ≤ P {quantile P p} + P {x : ℝ | quantile P p < x} := measure_union_le _ _
        _ = P {x : ℝ | quantile P p < x} := by rw [hatom (quantile P p), zero_add]
    linarith
  · -- **Left-continuity below the quantile.** Every `M < Q` is dominated by a member of the
    -- defining set, so the level `1 − p` is attained at every such `M`.
    rw [hQ] at hM
    obtain ⟨M', hM'S, hMM'⟩ := exists_lt_of_lt_csSup hne hM
    exact le_trans hM'S (tail_antitone P hMM'.le)

variable {Ξ : Type*} [MeasurableSpace Ξ] {μprob : Measure Ξ} [IsProbabilityMeasure μprob]
  {P : Measure ℝ} [IsProbabilityMeasure P]

/-! ### Bernstein for indicator counts

All four bracket events of `LM (2.6)`–`(2.7)` are upper deviations of the count
`#{i : Yᵢ ∈ A}` for a suitable half-line `A`, so one brick serves all four. A centred
indicator is bounded by `1` and has variance exactly `q(1−q)`, hence satisfies the Bernstein
moment condition with scale `b = 1/3` — the scale that produces `LM`'s `3/16`. -/

/-- The Bernstein moment condition for a bounded centred variable needs `2·3^{k-2} ≤ k!`
for `k ≥ 3` — with equality at `k = 3`, which is what pins the scale `b = 1/3`. -/
private theorem two_mul_three_pow_le_factorial {k : ℕ} (hk : 3 ≤ k) :
    2 * 3 ^ (k - 2) ≤ k.factorial := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ m hm ih =>
    have h1 : m + 1 - 2 = (m - 2) + 1 := by omega
    rw [h1, pow_succ, Nat.factorial_succ]
    calc 2 * (3 ^ (m - 2) * 3) = 3 * (2 * 3 ^ (m - 2)) := by ring
      _ ≤ 3 * m.factorial := by gcongr
      _ ≤ (m + 1) * m.factorial := by gcongr; omega

open scoped ENNReal NNReal in
open Finset in
/-- **Upper-deviation bound for an i.i.d. count** (the engine of `LM (2.6)`–`(2.7)`):
if `P(A) = q ∈ (0,1)` then, for every deviation `t > 0`,

  `μ{ #{i : Yᵢ ∈ A} ≥ qn + tn } ≤ exp(−n t²/(2(q(1−q) + t/3)))`.

This is `bernstein_inequality` for the centred indicators `1_A(Yᵢ) − q`, whose variance is
`q(1−q)` and whose Bernstein scale is `b = 1/3`. The count is written as a sum of
indicators (no decidability side conditions); the event is stated non-strictly, which is
what the order-statistic counting bricks produce, while `bernstein_inequality` supplies the
strict event — the two agree in the limit because the exponent is continuous in `t`. -/
private theorem count_upper_deviation {n : ℕ} {Y : Fin n → Ξ → ℝ} {A : Set ℝ} {q t : ℝ}
    (hY_meas : ∀ i, Measurable (Y i)) (hY_indep : iIndepFun Y μprob)
    (hY_law : ∀ i, μprob.map (Y i) = P) (hA : MeasurableSet A)
    (hq : P.real A = q) (hq0 : 0 < q) (hq1 : q < 1) (hn : 0 < n) (ht : 0 < t) :
    μprob {ξ | q * n + t * n ≤ ∑ i, A.indicator (fun _ => (1:ℝ)) (Y i ξ)}
      ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * t ^ 2 / (2 * (q * (1 - q) + t / 3)))) := by
  have hqq : 0 < q * (1 - q) := by nlinarith
  -- ### The centred indicator and its first two moments under `P`.
  have hgm : Measurable (fun x : ℝ => A.indicator (fun _ => (1:ℝ)) x - q) :=
    (measurable_const.indicator hA).sub measurable_const
  have hindint : Integrable (fun x : ℝ => A.indicator (fun _ => (1:ℝ)) x) P :=
    (integrable_const (1:ℝ)).indicator hA
  have hintind : ∫ x, A.indicator (fun _ => (1:ℝ)) x ∂P = q := by
    rw [integral_indicator_const (1:ℝ) hA, hq, smul_eq_mul, mul_one]
  have hmean : ∫ x, (A.indicator (fun _ => (1:ℝ)) x - q) ∂P = 0 := by
    rw [integral_sub hindint (integrable_const q), hintind, integral_const]
    simp
  have hsqpt : ∀ x : ℝ, (A.indicator (fun _ => (1:ℝ)) x - q) ^ 2
      = (1 - 2 * q) * A.indicator (fun _ => (1:ℝ)) x + q ^ 2 := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx]; ring
  have hsqint : Integrable (fun x : ℝ => (A.indicator (fun _ => (1:ℝ)) x - q) ^ 2) P := by
    refine Integrable.congr ((hindint.const_mul (1 - 2 * q)).add (integrable_const (q ^ 2))) ?_
    exact Filter.Eventually.of_forall fun x => (hsqpt x).symm
  have hvar : ∫ x, (A.indicator (fun _ => (1:ℝ)) x - q) ^ 2 ∂P = q * (1 - q) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hsqpt),
      integral_add (hindint.const_mul (1 - 2 * q)) (integrable_const (q ^ 2)),
      integral_const_mul, hintind, integral_const]
    simp
    ring
  -- ### Transfer of moments from `P` to `μprob` along the common law.
  have htr : ∀ f : ℝ → ℝ, Measurable f → ∀ i, ∫ ξ, f (Y i ξ) ∂μprob = ∫ x, f x ∂P := by
    intro f hf i
    rw [← hY_law i]
    exact (integral_map (hY_meas i).aemeasurable hf.aestronglyMeasurable).symm
  have htrL : ∀ f : ℝ → ℝ≥0∞, Measurable f → ∀ i,
      ∫⁻ ξ, f (Y i ξ) ∂μprob = ∫⁻ x, f x ∂P := by
    intro f hf i
    rw [← hY_law i]
    exact (lintegral_map hf (hY_meas i)).symm
  -- ### The Bernstein condition, with variance `q(1−q)` and scale `1/3`.
  have hB : ∀ i, ConcentrationInequalities.HasBernsteinCondition
      (fun ξ => A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q)
      (NNReal.mk (q * (1 - q)) hqq.le) (NNReal.mk (1/3) (by norm_num)) μprob := by
    intro i
    refine ⟨by rw [htr _ hgm i]; exact hmean, ?_, ?_⟩
    · rw [htr (fun x => (A.indicator (fun _ => (1:ℝ)) x - q) ^ 2) (hgm.pow_const 2) i]
      exact hvar
    · intro k hk
      have hpt : ∀ ξ : Ξ, |A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q| ^ k
          ≤ (A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q) ^ 2 := by
        intro ξ
        have hb : |A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q| ≤ 1 := by
          by_cases hx : Y i ξ ∈ A
          · rw [Set.indicator_of_mem hx, abs_le]; constructor <;> linarith
          · rw [Set.indicator_of_notMem hx, abs_le]; constructor <;> linarith
        calc |A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q| ^ k
            = |A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q| ^ 2
              * |A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q| ^ (k - 2) := by
              rw [← pow_add]; congr 1; omega
          _ ≤ |A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q| ^ 2 * 1 := by
              gcongr
              exact pow_le_one₀ (abs_nonneg _) hb
          _ = (A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q) ^ 2 := by rw [mul_one, sq_abs]
      calc ∫⁻ ξ, ENNReal.ofReal (|A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q| ^ k) ∂μprob
          ≤ ∫⁻ ξ, ENNReal.ofReal ((A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q) ^ 2) ∂μprob :=
            lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hpt ξ)
        _ = ENNReal.ofReal (q * (1 - q)) := by
            rw [htrL (fun x => ENNReal.ofReal ((A.indicator (fun _ => (1:ℝ)) x - q) ^ 2))
              (ENNReal.measurable_ofReal.comp (hgm.pow_const 2)) i,
              ← ofReal_integral_eq_lintegral_ofReal hsqint
                (Filter.Eventually.of_forall fun x => sq_nonneg _), hvar]
        _ ≤ ENNReal.ofReal ((⟨q * (1 - q), hqq.le⟩ : ℝ≥0) / 2 * (k.factorial : ℝ)
              * ((⟨1/3, by norm_num⟩ : ℝ≥0) : ℝ) ^ (k - 2)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hfac : (2 : ℝ) * 3 ^ (k - 2) ≤ (k.factorial : ℝ) := by
              exact_mod_cast two_mul_three_pow_le_factorial hk
            have hp : (0:ℝ) < (3 ^ (k - 2) : ℝ) := by positivity
            rw [show ((1:ℝ)/3) ^ (k - 2) = (3 ^ (k - 2) : ℝ)⁻¹ by
              rw [one_div, ← inv_pow], inv_eq_one_div, mul_one_div, le_div_iff₀ hp]
            nlinarith [mul_le_mul_of_nonneg_left hfac
              (show (0:ℝ) ≤ q * (1 - q) / 2 by positivity)]
  -- ### Bernstein at every deviation `s ∈ (0, t)`, then let `s ↑ t`.
  have hsum : ∀ ξ : Ξ, ∑ i, (A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q)
      = (∑ i, A.indicator (fun _ => (1:ℝ)) (Y i ξ)) - q * n := by
    intro ξ
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_comm (n : ℝ) q]
  have hkey : ∀ s : ℝ, 0 < s → s < t →
      μprob {ξ | q * n + t * n ≤ ∑ i, A.indicator (fun _ => (1:ℝ)) (Y i ξ)}
        ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * s ^ 2 / (2 * (q * (1 - q) + s / 3)))) := by
    intro s hs hst
    have hbern := ConcentrationInequalities.bernstein_inequality
      (X := fun i ξ => A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q) (μ := μprob)
      (fun i => (hgm.comp (hY_meas i)))
      (hY_indep.comp (fun _ => fun x : ℝ => A.indicator (fun _ => (1:ℝ)) x - q)
        (fun _ => hgm)) hB hn (by rw [← NNReal.coe_pos]; norm_num)
      (by rw [← NNReal.coe_pos]; simpa using hqq) hs
    have hsub : {ξ : Ξ | q * n + t * n ≤ ∑ i, A.indicator (fun _ => (1:ℝ)) (Y i ξ)}
        ⊆ {ξ : Ξ | s < (∑ i, (A.indicator (fun _ => (1:ℝ)) (Y i ξ) - q)) / (n : ℝ)} := by
      intro ξ hξ
      simp only [Set.mem_setOf_eq] at hξ ⊢
      rw [hsum ξ, lt_div_iff₀ (by exact_mod_cast hn)]
      nlinarith [show (0:ℝ) < n by exact_mod_cast hn]
    refine le_trans (measure_mono hsub) (le_trans hbern (le_of_eq ?_))
    congr 2
    simp only [NNReal.coe_mk]
    ring
  have hden : 2 * (q * (1 - q) + t / 3) ≠ 0 := by positivity
  have hcont : ContinuousAt
      (fun s : ℝ => ENNReal.ofReal
        (Real.exp (-(n : ℝ) * s ^ 2 / (2 * (q * (1 - q) + s / 3))))) t := by
    refine ENNReal.continuous_ofReal.continuousAt.comp ?_
    refine Real.continuous_exp.continuousAt.comp ?_
    exact ContinuousAt.div (by fun_prop) (by fun_prop) hden
  refine ge_of_tendsto (hcont.continuousWithinAt (s := Set.Iio t)) ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds ht).filter_mono nhdsWithin_le_nhds] with s hslt hspos
  exact hkey s hspos (Set.mem_Iio.1 hslt)

/-! ### From counts to order statistics -/

open Finset in
/-- Splitting the sample by a threshold: `#{j : v j ≤ c} + #{j : c < v j} = n`. -/
private theorem card_le_add_card_gt {m : ℕ} (v : Fin m → ℝ) (c : ℝ) :
    (univ.filter fun j => v j ≤ c).card + (univ.filter fun j => c < v j).card = m := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin m))) (p := fun j => v j ≤ c)
  simp only [not_le] at h
  simpa using h

open Finset in
/-- Splitting the sample by a threshold: `#{j : c ≤ v j} + #{j : v j < c} = n`. -/
private theorem card_ge_add_card_lt {m : ℕ} (v : Fin m → ℝ) (c : ℝ) :
    (univ.filter fun j => c ≤ v j).card + (univ.filter fun j => v j < c).card = m := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin m))) (p := fun j => c ≤ v j)
  simp only [not_le] at h
  simpa using h

open Finset in
/-- The indicator sum of a lower half-line is the corresponding count. -/
private theorem sum_indicator_lt_eq_card {m : ℕ} (v : Fin m → ℝ) (c : ℝ) :
    ∑ i, ({x : ℝ | x < c}).indicator (fun _ => (1:ℝ)) (v i)
      = ((univ.filter fun j => v j < c).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : v j < c
  · rw [Set.indicator_of_mem (show v j ∈ {x : ℝ | x < c} from hj), if_pos hj]
  · rw [Set.indicator_of_notMem (show v j ∉ {x : ℝ | x < c} from hj), if_neg hj]

open Finset in
/-- The indicator sum of an upper half-line is the corresponding count. -/
private theorem sum_indicator_gt_eq_card {m : ℕ} (v : Fin m → ℝ) (c : ℝ) :
    ∑ i, ({x : ℝ | c < x}).indicator (fun _ => (1:ℝ)) (v i)
      = ((univ.filter fun j => c < v j).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : c < v j
  · rw [Set.indicator_of_mem (show v j ∈ {x : ℝ | c < x} from hj), if_pos hj]
  · rw [Set.indicator_of_notMem (show v j ∉ {x : ℝ | c < x} from hj), if_neg hj]

/-- Mass strictly below a level, from the right-tail mass. -/
private theorem measureReal_lt_eq (P : Measure ℝ) [IsProbabilityMeasure P] (c : ℝ) :
    P.real {x : ℝ | x < c} = 1 - P.real {x : ℝ | c ≤ x} := by
  have h : {x : ℝ | x < c} = {x : ℝ | c ≤ x}ᶜ := by ext x; simp
  rw [h, measureReal_compl (μ := P) (s := {x : ℝ | c ≤ x}) measurableSet_Ici]
  simp

/-- Without atoms, strict and non-strict right tails agree. -/
private theorem measureReal_gt_eq (P : Measure ℝ) [IsProbabilityMeasure P]
    (hatom : ∀ t : ℝ, P {t} = 0) (c : ℝ) :
    P.real {x : ℝ | c < x} = P.real {x : ℝ | c ≤ x} := by
  have h : {x : ℝ | c ≤ x} = {c} ∪ {x : ℝ | c < x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    exact ⟨fun hx => (eq_or_lt_of_le hx).imp Eq.symm id, fun hx => by
      rcases hx with hx | hx
      · exact le_of_eq hx.symm
      · exact hx.le⟩
  have hm : P {x : ℝ | c ≤ x} = P {x : ℝ | c < x} := by
    rw [h, measure_union (Set.disjoint_singleton_left.2 (by simp))
      (show MeasurableSet {x : ℝ | c < x} from measurableSet_Ioi), hatom, zero_add]
  rw [measureReal_def, measureReal_def, hm]

/-- The Bernstein exponent at a bracket event, bounded by `LM`'s `−(3/16) r`: the count
variance `q(1−q)` is replaced by any upper bound `v` for which the rate arithmetic closes. -/
private theorem exp_exponent_le {r n : ℕ} {q t v : ℝ} (hqq : 0 < q * (1 - q)) (ht : 0 < t)
    (hv : q * (1 - q) ≤ v)
    (hkey : (3 / 16 : ℝ) * r * (2 * (v + t / 3)) ≤ n * t ^ 2) :
    Real.exp (-(n : ℝ) * t ^ 2 / (2 * (q * (1 - q) + t / 3)))
      ≤ Real.exp (-(3 / 16) * r) := by
  refine Real.exp_le_exp.2 ?_
  have hB : (0:ℝ) < 2 * (q * (1 - q) + t / 3) := by linarith
  have hr0 : (0:ℝ) ≤ (3 / 16 : ℝ) * r * 2 := by positivity
  have hmain : (3 / 16 : ℝ) * r ≤ (n : ℝ) * t ^ 2 / (2 * (q * (1 - q) + t / 3)) := by
    rw [le_div_iff₀ hB]
    nlinarith [mul_le_mul_of_nonneg_left hv hr0]
  rw [neg_mul, neg_div]
  linarith

open Finset in
/-- One bracket event: an order-statistic bracket fails only if a count deviates, and that
has probability at most `exp(−(3/16) r)` by `count_upper_deviation`. -/
private theorem bracket_event_bound {n r : ℕ} {Y : Fin n → Ξ → ℝ} {A : Set ℝ} {q t v : ℝ}
    (hY_meas : ∀ i, Measurable (Y i)) (hY_indep : iIndepFun Y μprob)
    (hY_law : ∀ i, μprob.map (Y i) = P) (hA : MeasurableSet A)
    (hq : P.real A = q) (hq0 : 0 < q) (hq1 : q < 1) (hn : 0 < n) (ht : 0 < t)
    (hv : q * (1 - q) ≤ v)
    (hkey : (3 / 16 : ℝ) * r * (2 * (v + t / 3)) ≤ n * t ^ 2) :
    μprob {ξ | q * n + t * n ≤ ∑ i, A.indicator (fun _ => (1:ℝ)) (Y i ξ)}
      ≤ ENNReal.ofReal (Real.exp (-(3 / 16) * r)) :=
  le_trans (count_upper_deviation hY_meas hY_indep hY_law hA hq hq0 hq1 hn ht)
    (ENNReal.ofReal_le_ofReal
      (exp_exponent_le (by nlinarith) ht hv hkey))

/-- Union bound in the shape the brackets need: if the complement of `G` is covered by four
events of probability at most `e`, then `G` has probability at least `1 − 4e`. No
measurability of `G` is needed (`1 = μ(G ∪ Gᶜ) ≤ μ G + μ Gᶜ` is subadditivity). -/
private theorem one_sub_four_le_measureReal {G B1 B2 B3 B4 : Set Ξ} {e : ℝ} (he : 0 ≤ e)
    (h : Gᶜ ⊆ B1 ∪ B2 ∪ B3 ∪ B4)
    (h1 : μprob B1 ≤ ENNReal.ofReal e) (h2 : μprob B2 ≤ ENNReal.ofReal e)
    (h3 : μprob B3 ≤ ENNReal.ofReal e) (h4 : μprob B4 ≤ ENNReal.ofReal e) :
    1 - 4 * e ≤ μprob.real G := by
  have hb : μprob Gᶜ ≤ ENNReal.ofReal (4 * e) := by
    refine le_trans (measure_mono h) ?_
    calc μprob (B1 ∪ B2 ∪ B3 ∪ B4) ≤ μprob (B1 ∪ B2 ∪ B3) + μprob B4 := measure_union_le _ _
      _ ≤ μprob (B1 ∪ B2) + μprob B3 + μprob B4 := by gcongr; exact measure_union_le _ _
      _ ≤ μprob B1 + μprob B2 + μprob B3 + μprob B4 := by gcongr; exact measure_union_le _ _
      _ ≤ ENNReal.ofReal e + ENNReal.ofReal e + ENNReal.ofReal e + ENNReal.ofReal e := by
          gcongr
      _ = ENNReal.ofReal (4 * e) := by
          rw [← ENNReal.ofReal_add he he, ← ENNReal.ofReal_add (by linarith) he,
            ← ENNReal.ofReal_add (by linarith) he]
          congr 1
          ring
  have hreal : μprob.real Gᶜ ≤ 4 * e := by
    rw [measureReal_def]
    calc (μprob Gᶜ).toReal ≤ (ENNReal.ofReal (4 * e)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      _ = 4 * e := ENNReal.toReal_ofReal (by linarith)
  have hu := measureReal_union_le (μ := μprob) G Gᶜ
  rw [Set.union_compl_self] at hu
  simp only [probReal_univ] at hu
  linarith

open StatLean.MultipleTesting in
/-- **The Bernstein order-statistic brackets** (`LM (2.6)`–`(2.7)`): with probability at
least `1 − 4 exp(−(3/16) r)`, the trimming order statistics of an i.i.d. sample `Y` are
bracketed by population quantiles — writing `ε = r/n`,

  `Q_{ε/2} ≤ Y*₍εn₎ ≤ Q_{2ε}`  and  `Q_{1−2ε} ≤ Y*₍₍₁₋ε₎n₎ ≤ Q_{1−ε/2}`.

Each one-sided count deviation is a Bernstein event for indicator sums at rate
`exp(−(3/16)εn) = exp(−(3/16)r)`. -/
theorem orderStat_quantile_brackets {n r : ℕ} {Y : Fin n → Ξ → ℝ}
    {a b : Fin n}
    -- LEAN-ONLY: coordinate measurability; LM §2.3 regularity
    (hY_meas : ∀ i, Measurable (Y i))
    -- USER-INPUT: jointly independent sample; LM Theorem 6
    (hY_indep : iIndepFun Y μprob)
    -- USER-INPUT: common law P; LM Theorem 6
    (hY_law : ∀ i, μprob.map (Y i) = P)
    -- USER-INPUT: nonatomic P; LM §2.3 proof simplification
    (hatom : ∀ t : ℝ, P {t} = 0)
    -- USER-INPUT: the trim count is in the working range 1 ≤ r, 4r < n
    -- (so that ε = r/n has 2ε < 1/2); LM Theorem 6 sample-size condition
    (hr1 : 1 ≤ r) (hrn : 4 * r < n)
    -- USER-INPUT: the trimming indices, 0-indexed: a = εn − 1, b = (1−ε)n − 1;
    -- LM §2.3 step (2)
    (ha : (a : ℕ) + 1 = r) (hb : (b : ℕ) + r + 1 = n) :
    1 - 4 * Real.exp (-(3 / 16) * r)
      ≤ μprob.real {ξ |
          quantile P (r / (2 * n)) ≤ orderStat (fun i => Y i ξ) a ∧
          orderStat (fun i => Y i ξ) a ≤ quantile P (2 * r / n) ∧
          quantile P (1 - 2 * r / n) ≤ orderStat (fun i => Y i ξ) b ∧
          orderStat (fun i => Y i ξ) b ≤ quantile P (1 - r / (2 * n))} := by
  have hn0 : 0 < n := by omega
  have hN : (0:ℝ) < n := by exact_mod_cast hn0
  have hR1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
  have hRN : 4 * (r:ℝ) < (n:ℝ) := by exact_mod_cast hrn
  -- ### The four population levels, and the masses of the corresponding half-lines.
  have hlo : (0:ℝ) < (r:ℝ) / (2 * n) := by positivity
  have hlo2 : (0:ℝ) < 2 * (r:ℝ) / n := by positivity
  have hhi : 2 * (r:ℝ) / n < 1 := by rw [div_lt_one hN]; linarith
  have hhi2 : (r:ℝ) / (2 * n) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hA1 : P.real {x : ℝ | x < quantile P ((r:ℝ) / (2 * n))} = (r:ℝ) / (2 * n) := by
    rw [measureReal_lt_eq, measure_ge_quantile P hatom hlo hhi2]; ring
  have hA2 : P.real {x : ℝ | quantile P (2 * (r:ℝ) / n) < x} = 1 - 2 * (r:ℝ) / n := by
    rw [measureReal_gt_eq P hatom, measure_ge_quantile P hatom hlo2 hhi]
  have hA3 : P.real {x : ℝ | x < quantile P (1 - 2 * (r:ℝ) / n)} = 1 - 2 * (r:ℝ) / n := by
    rw [measureReal_lt_eq,
      measure_ge_quantile P hatom (by linarith) (by linarith)]
    ring
  have hA4 : P.real {x : ℝ | quantile P (1 - (r:ℝ) / (2 * n)) < x} = (r:ℝ) / (2 * n) := by
    rw [measureReal_gt_eq P hatom, measure_ge_quantile P hatom (by linarith) (by linarith)]
    ring
  -- ### The rate arithmetic: each bracket event is a Bernstein count deviation at `3/16`.
  have hkeyA : (3 / 16 : ℝ) * r * (2 * ((r:ℝ) / (2 * n) + ((r:ℝ) / (2 * n)) / 3))
      ≤ n * ((r:ℝ) / (2 * n)) ^ 2 := by
    rw [show (3 / 16 : ℝ) * r * (2 * ((r:ℝ) / (2 * n) + ((r:ℝ) / (2 * n)) / 3))
        = (r:ℝ) ^ 2 / (4 * n) by field_simp; ring,
      show (n:ℝ) * ((r:ℝ) / (2 * n)) ^ 2 = (r:ℝ) ^ 2 / (4 * n) by field_simp; ring]
  have hkeyB : (3 / 16 : ℝ) * r * (2 * (2 * (r:ℝ) / n + ((r:ℝ) / n) / 3))
      ≤ n * ((r:ℝ) / n) ^ 2 := by
    rw [show (3 / 16 : ℝ) * r * (2 * (2 * (r:ℝ) / n + ((r:ℝ) / n) / 3))
        = 7 * (r:ℝ) ^ 2 / (8 * n) by field_simp; ring,
      show (n:ℝ) * ((r:ℝ) / n) ^ 2 = (r:ℝ) ^ 2 / n by field_simp]
    have hgap : (r:ℝ) ^ 2 / n - 7 * (r:ℝ) ^ 2 / (8 * n) = (r:ℝ) ^ 2 / (8 * n) := by
      field_simp; ring
    have hpos : (0:ℝ) ≤ (r:ℝ) ^ 2 / (8 * n) := by positivity
    linarith
  -- ### The four count events.
  have hE1 : μprob {ξ | (r:ℝ) / (2 * n) * n + (r:ℝ) / (2 * n) * n ≤
      ∑ i, ({x : ℝ | x < quantile P ((r:ℝ) / (2 * n))}).indicator (fun _ => (1:ℝ)) (Y i ξ)}
      ≤ ENNReal.ofReal (Real.exp (-(3 / 16) * r)) :=
    bracket_event_bound (v := (r:ℝ) / (2 * n)) hY_meas hY_indep hY_law measurableSet_Iio
      hA1 hlo hhi2 hn0 hlo (by nlinarith) hkeyA
  have hE2 : μprob {ξ | (1 - 2 * (r:ℝ) / n) * n + (r:ℝ) / n * n ≤
      ∑ i, ({x : ℝ | quantile P (2 * (r:ℝ) / n) < x}).indicator (fun _ => (1:ℝ)) (Y i ξ)}
      ≤ ENNReal.ofReal (Real.exp (-(3 / 16) * r)) :=
    bracket_event_bound (v := 2 * (r:ℝ) / n) hY_meas hY_indep hY_law measurableSet_Ioi
      hA2 (by linarith) (by linarith) hn0 (by positivity) (by nlinarith) hkeyB
  have hE3 : μprob {ξ | (1 - 2 * (r:ℝ) / n) * n + (r:ℝ) / n * n ≤
      ∑ i, ({x : ℝ | x < quantile P (1 - 2 * (r:ℝ) / n)}).indicator (fun _ => (1:ℝ)) (Y i ξ)}
      ≤ ENNReal.ofReal (Real.exp (-(3 / 16) * r)) :=
    bracket_event_bound (v := 2 * (r:ℝ) / n) hY_meas hY_indep hY_law measurableSet_Iio
      hA3 (by linarith) (by linarith) hn0 (by positivity) (by nlinarith) hkeyB
  have hE4 : μprob {ξ | (r:ℝ) / (2 * n) * n + (r:ℝ) / (2 * n) * n ≤
      ∑ i, ({x : ℝ | quantile P (1 - (r:ℝ) / (2 * n)) < x}).indicator (fun _ => (1:ℝ)) (Y i ξ)}
      ≤ ENNReal.ofReal (Real.exp (-(3 / 16) * r)) :=
    bracket_event_bound (v := (r:ℝ) / (2 * n)) hY_meas hY_indep hY_law measurableSet_Ioi
      hA4 hlo hhi2 hn0 hlo (by nlinarith) hkeyA
  -- ### A bracket fails only if one of the four counts deviates.
  refine one_sub_four_le_measureReal (Real.exp_pos _).le ?_ hE1 hE2 hE3 hE4
  intro ξ hξ
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or] at hξ
  have hrn' : r ≤ n := by omega
  have hcast : ((n - r : ℕ) : ℝ) = (n:ℝ) - r := by
    push_cast [Nat.cast_sub hrn']
    ring
  rcases hξ with h | h | h | h
  · refine Or.inl (Or.inl (Or.inl ?_))
    have hc : ¬ (n - (a:ℕ) ≤ (Finset.univ.filter fun j =>
        quantile P ((r:ℝ) / (2 * n)) ≤ Y j ξ).card) := fun hcc =>
      h (le_orderStat_of_card_le (fun i => Y i ξ) a _ hcc)
    have hsplit := card_ge_add_card_lt (fun i => Y i ξ) (quantile P ((r:ℝ) / (2 * n)))
    have haa : (a:ℕ) < n := a.isLt
    have hcount : r ≤ (Finset.univ.filter fun j =>
        Y j ξ < quantile P ((r:ℝ) / (2 * n))).card := by omega
    have hcount' : (r:ℝ) ≤ ((Finset.univ.filter fun j =>
        Y j ξ < quantile P ((r:ℝ) / (2 * n))).card : ℝ) := by exact_mod_cast hcount
    have hval : (r:ℝ) / (2 * n) * n + (r:ℝ) / (2 * n) * n = (r:ℝ) := by field_simp; ring
    simp only [Set.mem_setOf_eq, sum_indicator_lt_eq_card]
    linarith
  · refine Or.inl (Or.inl (Or.inr ?_))
    have hc : ¬ ((a:ℕ) + 1 ≤ (Finset.univ.filter fun j =>
        Y j ξ ≤ quantile P (2 * (r:ℝ) / n)).card) := fun hcc =>
      h (orderStat_le_of_card_le (fun i => Y i ξ) a _ hcc)
    have hsplit := card_le_add_card_gt (fun i => Y i ξ) (quantile P (2 * (r:ℝ) / n))
    have hcount : n - r ≤ (Finset.univ.filter fun j =>
        quantile P (2 * (r:ℝ) / n) < Y j ξ).card := by omega
    have hcount' : (n:ℝ) - r ≤ ((Finset.univ.filter fun j =>
        quantile P (2 * (r:ℝ) / n) < Y j ξ).card : ℝ) := by
      rw [← hcast]; exact_mod_cast hcount
    have hval : (1 - 2 * (r:ℝ) / n) * n + (r:ℝ) / n * n = (n:ℝ) - r := by field_simp; ring
    simp only [Set.mem_setOf_eq, sum_indicator_gt_eq_card]
    linarith
  · refine Or.inl (Or.inr ?_)
    have hc : ¬ (n - (b:ℕ) ≤ (Finset.univ.filter fun j =>
        quantile P (1 - 2 * (r:ℝ) / n) ≤ Y j ξ).card) := fun hcc =>
      h (le_orderStat_of_card_le (fun i => Y i ξ) b _ hcc)
    have hsplit := card_ge_add_card_lt (fun i => Y i ξ) (quantile P (1 - 2 * (r:ℝ) / n))
    have hbb : (b:ℕ) < n := b.isLt
    have hcount : n - r ≤ (Finset.univ.filter fun j =>
        Y j ξ < quantile P (1 - 2 * (r:ℝ) / n)).card := by omega
    have hcount' : (n:ℝ) - r ≤ ((Finset.univ.filter fun j =>
        Y j ξ < quantile P (1 - 2 * (r:ℝ) / n)).card : ℝ) := by
      rw [← hcast]; exact_mod_cast hcount
    have hval : (1 - 2 * (r:ℝ) / n) * n + (r:ℝ) / n * n = (n:ℝ) - r := by field_simp; ring
    simp only [Set.mem_setOf_eq, sum_indicator_lt_eq_card]
    linarith
  · refine Or.inr ?_
    have hc : ¬ ((b:ℕ) + 1 ≤ (Finset.univ.filter fun j =>
        Y j ξ ≤ quantile P (1 - (r:ℝ) / (2 * n))).card) := fun hcc =>
      h (orderStat_le_of_card_le (fun i => Y i ξ) b _ hcc)
    have hsplit := card_le_add_card_gt (fun i => Y i ξ) (quantile P (1 - (r:ℝ) / (2 * n)))
    have hbb : (b:ℕ) < n := b.isLt
    have hcount : r ≤ (Finset.univ.filter fun j =>
        quantile P (1 - (r:ℝ) / (2 * n)) < Y j ξ).card := by omega
    have hcount' : (r:ℝ) ≤ ((Finset.univ.filter fun j =>
        quantile P (1 - (r:ℝ) / (2 * n)) < Y j ξ).card : ℝ) := by exact_mod_cast hcount
    have hval : (r:ℝ) / (2 * n) * n + (r:ℝ) / (2 * n) * n = (r:ℝ) := by field_simp; ring
    simp only [Set.mem_setOf_eq, sum_indicator_gt_eq_card]
    linarith

/-! ### The truncation bias

The bias of a truncated variable is a *difference* of two one-sided tail integrals, so it
is bounded by the larger of the two, not by their sum. Each one-sided tail obeys the sharp
self-referential bound `S² ≤ p(σ² + S²)`: Cauchy–Schwarz gives `S² ≤ p·E[(X−β)²1_{X>β}]`,
and the second moment of the tail is controlled by `σ² + S²` because the mean shift
`μ₀ − β` is itself at most `S`. -/

omit [IsProbabilityMeasure P] in
/-- `max f 0` inherits integrability from `f` (`max a 0 = (a + |a|)/2`). -/
private theorem integrable_max_zero {f : ℝ → ℝ} (hf : Integrable f P) :
    Integrable (fun x => max (f x) 0) P := by
  refine ((hf.add hf.abs).div_const 2).congr (Filter.Eventually.of_forall fun x => ?_)
  change (f x + |f x|) / 2 = max (f x) 0
  rcases le_or_gt 0 (f x) with hx | hx
  · rw [max_eq_left hx, abs_of_nonneg hx]; ring
  · rw [max_eq_right hx.le, abs_of_neg hx]; ring

/-- **The one-sided tail bound** (`LM Theorem 6` proof, the Cauchy–Schwarz step): for an
`L²` function `f` with mean `m`, variance `w` and `P(f > 0) ≤ p`, the positive part obeys

  `(∫ f⁺)² ≤ p · (w + (∫ f⁺)²)`.

The self-reference is what makes the bound sharp without assuming the tail is on the far
side of the mean: when `m > 0` the second moment of `f⁺` costs `w + m²`, and `m ≤ ∫ f⁺`. -/
private theorem tail_sq_le {f : ℝ → ℝ} {m w p : ℝ} (hfm : Measurable f) (hf : MemLp f 2 P)
    (hm : ∫ x, f x ∂P = m) (hw : ∫ x, (f x - m) ^ 2 ∂P = w)
    (hp : P.real {x : ℝ | 0 < f x} ≤ p) :
    (∫ x, max (f x) 0 ∂P) ^ 2 ≤ p * (w + (∫ x, max (f x) 0 ∂P) ^ 2) := by
  have hfint : Integrable f P := hf.integrable one_le_two
  have hhint : Integrable (fun x => max (f x) 0) P := integrable_max_zero hfint
  have hsqint : Integrable (fun x => f x ^ 2) P := hf.integrable_sq
  have hwint : Integrable (fun x => (f x - m) ^ 2) P :=
    (hf.sub (memLp_const m)).integrable_sq
  have hhmeas : Measurable (fun x => max (f x) 0) := hfm.max measurable_const
  have hVint : Integrable (fun x => max (f x) 0 ^ 2) P := by
    refine hsqint.mono (hhmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rcases le_or_gt 0 (f x) with hx | hx
    · rw [max_eq_left hx]
    · rw [max_eq_right hx.le]
      simp only [Real.norm_eq_abs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, abs_zero]
      positivity
  have hS0 : 0 ≤ ∫ x, max (f x) 0 ∂P :=
    integral_nonneg fun x => le_max_right _ _
  have hV0 : 0 ≤ ∫ x, max (f x) 0 ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  have hmeasset : MeasurableSet {x : ℝ | 0 < f x} := hfm measurableSet_Ioi
  have hindint : Integrable
      (fun x => ({x : ℝ | 0 < f x}).indicator (fun _ => (1:ℝ)) x) P :=
    (integrable_const (1:ℝ)).indicator hmeasset
  have hindval : ∫ x, ({x : ℝ | 0 < f x}).indicator (fun _ => (1:ℝ)) x ∂P
      = P.real {x : ℝ | 0 < f x} := by
    rw [integral_indicator_const (1:ℝ) hmeasset, smul_eq_mul, mul_one]
  have hp0 : 0 ≤ P.real {x : ℝ | 0 < f x} := measureReal_nonneg
  -- ### Cauchy–Schwarz by the elementary `ab ≤ (λa² + b²/λ)/2`.
  have hlam : ∀ l : ℝ, 0 < l → ∫ x, max (f x) 0 ∂P
      ≤ l / 2 * ∫ x, max (f x) 0 ^ 2 ∂P + P.real {x : ℝ | 0 < f x} / (2 * l) := by
    intro l hl
    have hbound : ∫ x, max (f x) 0 ∂P
        ≤ ∫ x, (l / 2 * max (f x) 0 ^ 2
            + 1 / (2 * l) * ({x : ℝ | 0 < f x}).indicator (fun _ => (1:ℝ)) x) ∂P := by
      refine integral_mono hhint ((hVint.const_mul _).add (hindint.const_mul _))
        fun x => ?_
      rcases le_or_gt (f x) 0 with hx | hx
      · rw [max_eq_right hx]
        have hind : (0:ℝ) ≤ ({x : ℝ | 0 < f x}).indicator (fun _ => (1:ℝ)) x :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) x
        have hpos : 0 ≤ 1 / (2 * l) * ({x : ℝ | 0 < f x}).indicator (fun _ => (1:ℝ)) x :=
          mul_nonneg (by positivity) hind
        nlinarith [hpos]
      · rw [max_eq_left hx.le,
          Set.indicator_of_mem (show x ∈ {x : ℝ | 0 < f x} from hx)]
        have hstep : f x ≤ l / 2 * f x ^ 2 + 1 / (2 * l) := by
          rw [← sub_nonneg,
            show l / 2 * f x ^ 2 + 1 / (2 * l) - f x = (l * f x - 1) ^ 2 / (2 * l) by
              field_simp; ring]
          positivity
        simpa using hstep
    rw [integral_add (hVint.const_mul _) (hindint.const_mul _), integral_const_mul,
      integral_const_mul, hindval] at hbound
    calc ∫ x, max (f x) 0 ∂P
        ≤ l / 2 * ∫ x, max (f x) 0 ^ 2 ∂P + 1 / (2 * l) * P.real {x : ℝ | 0 < f x} := hbound
      _ = l / 2 * ∫ x, max (f x) 0 ^ 2 ∂P + P.real {x : ℝ | 0 < f x} / (2 * l) := by
          ring
  have hCS : (∫ x, max (f x) 0 ∂P) ^ 2
      ≤ P.real {x : ℝ | 0 < f x} * ∫ x, max (f x) 0 ^ 2 ∂P := by
    rcases eq_or_lt_of_le hS0 with hS | hS
    · rw [← hS]
      simpa using mul_nonneg hp0 hV0
    · have hVpos : 0 < ∫ x, max (f x) 0 ^ 2 ∂P := by
        rcases eq_or_lt_of_le hV0 with hV | hV
        · exfalso
          have hae : (fun x => max (f x) 0 ^ 2) =ᵐ[P] 0 :=
            (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hVint).1 hV.symm
          have hae2 : (fun x => max (f x) 0) =ᵐ[P] 0 := by
            filter_upwards [hae] with x hx
            simpa [pow_eq_zero_iff] using hx
          rw [integral_congr_ae hae2] at hS
          simp at hS
        · exact hV
      have hl := hlam ((∫ x, max (f x) 0 ∂P) / ∫ x, max (f x) 0 ^ 2 ∂P) (by positivity)
      rw [show (∫ x, max (f x) 0 ∂P) / (∫ x, max (f x) 0 ^ 2 ∂P) / 2
            * ∫ x, max (f x) 0 ^ 2 ∂P = (∫ x, max (f x) 0 ∂P) / 2 by
          field_simp,
        show P.real {x : ℝ | 0 < f x}
            / (2 * ((∫ x, max (f x) 0 ∂P) / ∫ x, max (f x) 0 ^ 2 ∂P))
            = P.real {x : ℝ | 0 < f x} * (∫ x, max (f x) 0 ^ 2 ∂P)
              / (2 * ∫ x, max (f x) 0 ∂P) by field_simp] at hl
      have h5 : (∫ x, max (f x) 0 ∂P) / 2
          ≤ P.real {x : ℝ | 0 < f x} * (∫ x, max (f x) 0 ^ 2 ∂P)
            / (2 * ∫ x, max (f x) 0 ∂P) := by linarith
      have h6 := mul_le_mul_of_nonneg_right h5
        (show (0:ℝ) ≤ 2 * ∫ x, max (f x) 0 ∂P by linarith)
      rw [show (∫ x, max (f x) 0 ∂P) / 2 * (2 * ∫ x, max (f x) 0 ∂P)
            = (∫ x, max (f x) 0 ∂P) ^ 2 by ring,
        show P.real {x : ℝ | 0 < f x} * (∫ x, max (f x) 0 ^ 2 ∂P)
            / (2 * ∫ x, max (f x) 0 ∂P) * (2 * ∫ x, max (f x) 0 ∂P)
            = P.real {x : ℝ | 0 < f x} * ∫ x, max (f x) 0 ^ 2 ∂P by field_simp] at h6
      exact h6
  -- ### The tail second moment: `V ≤ w + S²`.
  have hVw : ∫ x, max (f x) 0 ^ 2 ∂P ≤ w + (∫ x, max (f x) 0 ∂P) ^ 2 := by
    rcases le_or_gt m 0 with hm0 | hm0
    · have hle : ∫ x, max (f x) 0 ^ 2 ∂P ≤ ∫ x, (f x - m) ^ 2 ∂P := by
        refine integral_mono hVint hwint fun x => ?_
        rcases le_or_gt (f x) 0 with hx | hx
        · rw [max_eq_right hx]
          simpa using sq_nonneg (f x - m)
        · rw [max_eq_left hx.le]
          nlinarith
      rw [hw] at hle
      nlinarith [sq_nonneg (∫ x, max (f x) 0 ∂P)]
    · have h1 : ∫ x, max (f x) 0 ^ 2 ∂P ≤ ∫ x, f x ^ 2 ∂P := by
        refine integral_mono hVint hsqint fun x => ?_
        rcases le_or_gt (f x) 0 with hx | hx
        · rw [max_eq_right hx]
          simpa using sq_nonneg (f x)
        · rw [max_eq_left hx.le]
      have h2 : ∫ x, f x ^ 2 ∂P = w + m ^ 2 := by
        have hexp : ∫ x, (f x - m) ^ 2 ∂P
            = ∫ x, (f x ^ 2 - 2 * m * f x + m ^ 2) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
        have e1 : ∫ x, (f x ^ 2 - 2 * m * f x + m ^ 2) ∂P
            = (∫ x, (f x ^ 2 - 2 * m * f x) ∂P) + ∫ _x : ℝ, m ^ 2 ∂P :=
          integral_add (hsqint.sub (hfint.const_mul (2 * m))) (integrable_const (m ^ 2))
        have e2 : ∫ x, (f x ^ 2 - 2 * m * f x) ∂P
            = (∫ x, f x ^ 2 ∂P) - ∫ x, 2 * m * f x ∂P :=
          integral_sub hsqint (hfint.const_mul (2 * m))
        have e3 : ∫ x, 2 * m * f x ∂P = 2 * m * m := by rw [integral_const_mul, hm]
        have e4 : ∫ _x : ℝ, m ^ 2 ∂P = m ^ 2 := by simp
        rw [hexp, e1, e2, e3, e4] at hw
        linarith
      have h3 : m ≤ ∫ x, max (f x) 0 ∂P := by
        rw [← hm]
        exact integral_mono hfint hhint fun x => le_max_left _ _
      nlinarith
  nlinarith [hCS, hVw, hp0, hV0, mul_le_mul_of_nonneg_right hp hV0]

/-- The one-sided tail bound in the form used: `∫ f⁺ ≤ √w · √(p/(1−p))`. -/
private theorem tail_le_sqrt {f : ℝ → ℝ} {m w p : ℝ} (hfm : Measurable f) (hf : MemLp f 2 P)
    (hm : ∫ x, f x ∂P = m) (hw : ∫ x, (f x - m) ^ 2 ∂P = w)
    (hp : P.real {x : ℝ | 0 < f x} ≤ p) (_hp0 : 0 ≤ p) (hp1 : p < 1) (hw0 : 0 ≤ w) :
    ∫ x, max (f x) 0 ∂P ≤ Real.sqrt w * Real.sqrt (p / (1 - p)) := by
  have hkey := tail_sq_le hfm hf hm hw hp
  have hS0 : 0 ≤ ∫ x, max (f x) 0 ∂P := integral_nonneg fun x => le_max_right _ _
  have hsq : (∫ x, max (f x) 0 ∂P) ^ 2 ≤ w * (p / (1 - p)) := by
    rw [show w * (p / (1 - p)) = p * w / (1 - p) by ring, le_div_iff₀ (by linarith)]
    nlinarith
  rw [← Real.sqrt_mul hw0]
  calc ∫ x, max (f x) 0 ∂P = Real.sqrt ((∫ x, max (f x) 0 ∂P) ^ 2) := (Real.sqrt_sq hS0).symm
    _ ≤ Real.sqrt (w * (p / (1 - p))) := Real.sqrt_le_sqrt hsq

/-- The quantile is monotone in its level. -/
private theorem quantile_mono (P : Measure ℝ) [IsProbabilityMeasure P] {p p' : ℝ}
    (hp : 0 < p) (hp' : p' < 1) (hpp : p ≤ p') : quantile P p ≤ quantile P p' := by
  refine csSup_le_csSup (quantile_set_nonempty_bddAbove P (by linarith) hp').2
    (quantile_set_nonempty_bddAbove P hp (by linarith)).1 ?_
  intro M hM
  simp only [Set.mem_setOf_eq] at hM ⊢
  linarith

/-- **The sharp truncation-bias bound** (`LM Theorem 6` proof, the Cauchy–Schwarz display,
sharpened): the bias is the *difference* `∫(α−X)⁺ − ∫(X−β)⁺` of two nonnegative tails, so it
is bounded by the larger one, and each tail obeys `tail_le_sqrt` at level `p = 2r/n`. Since
`4r < n` gives `p/(1−p) ≤ 2p`, the bias is at most `σ√(4r/n)` — a factor `√8` better than
the `σ√(32r/n)` that `LM` records (they add the two tails and bound each by `σ√(8ε)`).
The main theorem needs this sharper form: `LM`'s composite constant `9` does not survive
the lossy version. -/
private theorem truncated_bias_le_sharp {μ₀ σ2 : ℝ} {r n : ℕ} {α β : ℝ}
    -- USER-INPUT: P is square-integrable with mean μ₀ and variance σ²; LM Theorem 6
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    -- USER-INPUT: nonatomic P; LM §2.3 proof simplification
    (hatom : ∀ t : ℝ, P {t} = 0)
    (hr1 : 1 ≤ r) (hrn : 4 * r < n)
    -- USER-INPUT: the levels sit inside the LM (2.6)–(2.7) brackets
    (_hα₁ : quantile P (r / (2 * n)) ≤ α) (hα₂ : α ≤ quantile P (2 * r / n))
    (hβ₁ : quantile P (1 - 2 * r / n) ≤ β) (_hβ₂ : β ≤ quantile P (1 - r / (2 * n))) :
    |(∫ x, truncate α β x ∂P) - μ₀| ≤ Real.sqrt σ2 * Real.sqrt (4 * r / n) := by
  have hn0 : 0 < n := by omega
  have hN : (0:ℝ) < n := by exact_mod_cast hn0
  have hR1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
  have hRN : 4 * (r:ℝ) < (n:ℝ) := by exact_mod_cast hrn
  have hL2' : MemLp (fun x : ℝ => x) 2 P := hL2
  have hσ0 : 0 ≤ σ2 := by rw [← hvar]; exact integral_nonneg fun x => sq_nonneg _
  -- ### The tail level `p = 2r/n < 1/2`.
  have hp0 : (0:ℝ) < 2 * (r:ℝ) / n := by positivity
  have hphalf : 2 * (r:ℝ) / n < 1 / 2 := by rw [div_lt_iff₀ hN]; linarith
  -- ### `α ≤ β`, so the truncation interval is honest.
  have hab : α ≤ β :=
    le_trans hα₂ (le_trans (quantile_mono P hp0 (by linarith) (by linarith)) hβ₁)
  -- ### Integrability of the pieces.
  have hidint : Integrable (fun x : ℝ => x) P := hL2'.integrable one_le_two
  have hαint : Integrable (fun x : ℝ => max (α - x) 0) P :=
    integrable_max_zero ((integrable_const α).sub hidint)
  have hβint : Integrable (fun x : ℝ => max (x - β) 0) P :=
    integrable_max_zero (hidint.sub (integrable_const β))
  -- ### The bias is the *difference* of the two one-sided tails.
  have hpt : ∀ x : ℝ, truncate α β x = x + max (α - x) 0 - max (x - β) 0 := by
    intro x
    rcases le_or_gt x α with hx | hx
    · rw [truncate, min_eq_right (le_trans hx hab), max_eq_left hx,
        max_eq_left (by linarith : (0:ℝ) ≤ α - x), max_eq_right (by linarith : x - β ≤ 0)]
      ring
    · rcases le_or_gt x β with hx2 | hx2
      · rw [truncate, min_eq_right hx2, max_eq_right hx.le,
          max_eq_right (by linarith : α - x ≤ 0), max_eq_right (by linarith : x - β ≤ 0)]
        ring
      · rw [truncate, min_eq_left hx2.le, max_eq_right hab,
          max_eq_right (by linarith : α - x ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ x - β)]
        ring
  have hint : ∫ x, truncate α β x ∂P
      = μ₀ + (∫ x, max (α - x) 0 ∂P) - ∫ x, max (x - β) 0 ∂P := by
    have e0 : ∫ x, truncate α β x ∂P = ∫ x, (x + max (α - x) 0 - max (x - β) 0) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    have e1 : ∫ x, (x + max (α - x) 0 - max (x - β) 0) ∂P
        = (∫ x, (x + max (α - x) 0) ∂P) - ∫ x, max (x - β) 0 ∂P :=
      integral_sub (hidint.add hαint) hβint
    have e2 : ∫ x, (x + max (α - x) 0) ∂P = (∫ x : ℝ, x ∂P) + ∫ x, max (α - x) 0 ∂P :=
      integral_add hidint hαint
    rw [e0, e1, e2, hmean]
  -- ### Each tail is at most `√σ² · √(p/(1−p))`.
  have hSβ : ∫ x, max (x - β) 0 ∂P
      ≤ Real.sqrt σ2 * Real.sqrt ((2 * (r:ℝ) / n) / (1 - 2 * (r:ℝ) / n)) := by
    refine tail_le_sqrt (m := μ₀ - β) (measurable_id.sub_const β)
      (hL2'.sub (memLp_const β)) ?_ ?_ ?_ hp0.le (by linarith) hσ0
    · rw [integral_sub hidint (integrable_const β), hmean, integral_const]
      simp
    · calc ∫ x, ((x - β) - (μ₀ - β)) ^ 2 ∂P = ∫ x, (x - μ₀) ^ 2 ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
        _ = σ2 := hvar
    · have hsub : {x : ℝ | 0 < x - β}
          ⊆ {x : ℝ | quantile P (1 - 2 * (r:ℝ) / n) ≤ x} := fun x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        linarith
      calc P.real {x : ℝ | 0 < x - β}
          ≤ P.real {x : ℝ | quantile P (1 - 2 * (r:ℝ) / n) ≤ x} := measureReal_mono hsub
        _ = 2 * (r:ℝ) / n := by
            rw [measure_ge_quantile P hatom (by linarith) (by linarith)]; ring
  have hSα : ∫ x, max (α - x) 0 ∂P
      ≤ Real.sqrt σ2 * Real.sqrt ((2 * (r:ℝ) / n) / (1 - 2 * (r:ℝ) / n)) := by
    refine tail_le_sqrt (m := α - μ₀) (measurable_const.sub measurable_id)
      ((memLp_const α).sub hL2') ?_ ?_ ?_ hp0.le (by linarith) hσ0
    · rw [integral_sub (integrable_const α) hidint, hmean, integral_const]
      simp
    · calc ∫ x, ((α - x) - (α - μ₀)) ^ 2 ∂P = ∫ x, (x - μ₀) ^ 2 ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
        _ = σ2 := hvar
    · have hsub : {x : ℝ | 0 < α - x} ⊆ {x : ℝ | x < quantile P (2 * (r:ℝ) / n)} :=
        fun x hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          linarith
      calc P.real {x : ℝ | 0 < α - x}
          ≤ P.real {x : ℝ | x < quantile P (2 * (r:ℝ) / n)} := measureReal_mono hsub
        _ = 2 * (r:ℝ) / n := by
            rw [measureReal_lt_eq, measure_ge_quantile P hatom hp0 (by linarith)]; ring
  -- ### A difference of two nonnegative terms is bounded by the larger of them.
  have hSα0 : 0 ≤ ∫ x, max (α - x) 0 ∂P := integral_nonneg fun x => le_max_right _ _
  have hSβ0 : 0 ≤ ∫ x, max (x - β) 0 ∂P := integral_nonneg fun x => le_max_right _ _
  have hfinal : Real.sqrt σ2 * Real.sqrt ((2 * (r:ℝ) / n) / (1 - 2 * (r:ℝ) / n))
      ≤ Real.sqrt σ2 * Real.sqrt (4 * (r:ℝ) / n) := by
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
    have hu : (0:ℝ) < (r:ℝ) / n := by positivity
    have hu2 : 2 * ((r:ℝ) / n) < 1 / 2 := by rw [← mul_div_assoc]; exact hphalf
    rw [show 2 * (r:ℝ) / n = 2 * ((r:ℝ) / n) by ring,
      show 4 * (r:ℝ) / n = 4 * ((r:ℝ) / n) by ring, div_le_iff₀ (by linarith)]
    nlinarith [hu, hu2]
  rw [hint]
  rw [abs_le]
  constructor <;> linarith

/-- **The truncation-bias bound** (`LM Theorem 6` proof, the display
`|E[φ_{α,β}(X)|Y] − μ| ≤ σ√(32ε)`): whenever the truncation levels are quantile-
bracketed as in `orderStat_quantile_brackets`, the conditional bias of the truncated
variable is at most `σ√(32ε)` with `ε = r/n` — via Chebyshev on the tail location
(`Q_{1−2ε} ≤ μ + σ/√(2ε)`) and Cauchy–Schwarz on the truncated tails. Stated at the
population level: for any deterministic levels `α β` inside the brackets. -/
theorem truncated_bias_le {μ₀ σ2 : ℝ} {r n : ℕ} {α β : ℝ}
    -- USER-INPUT: P is square-integrable with mean μ₀ and variance σ²; LM Theorem 6
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    -- USER-INPUT: nonatomic P; LM §2.3 proof simplification
    (hatom : ∀ t : ℝ, P {t} = 0)
    (hr1 : 1 ≤ r) (hrn : 4 * r < n)
    -- USER-INPUT: the levels sit inside the LM (2.6)–(2.7) brackets
    (hα₁ : quantile P (r / (2 * n)) ≤ α) (hα₂ : α ≤ quantile P (2 * r / n))
    (hβ₁ : quantile P (1 - 2 * r / n) ≤ β) (hβ₂ : β ≤ quantile P (1 - r / (2 * n))) :
    |(∫ x, truncate α β x ∂P) - μ₀| ≤ Real.sqrt σ2 * Real.sqrt (32 * r / n) := by
  refine le_trans (truncated_bias_le_sharp hL2 hmean hvar hatom hr1 hrn hα₁ hα₂ hβ₁ hβ₂) ?_
  have hN : (0:ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
  have : (0:ℝ) ≤ (r:ℝ) / n := by positivity
  rw [show 4 * (r:ℝ) / n = 4 * ((r:ℝ) / n) by ring,
    show 32 * (r:ℝ) / n = 32 * ((r:ℝ) / n) by ring]
  linarith

/-! ### Where the truncation levels sit, and how wide the truncated variable is

Chebyshev locates the quantiles within `σ/√p` of the mean, so a bracketed truncation
interval has width at most `2σ√(2n/r)` — the `M ≤ σ√(2/ε)` of `LM`'s Theorem 6 proof. That
width is the Bernstein scale of the truncated average; its variance is at most `σ²`
because truncation is a contraction. -/

/-- **Chebyshev's inequality** at the population level, in the form used below. -/
private theorem chebyshev_tail {μ₀ σ2 c : ℝ} (hL2 : MemLp id 2 P) (_hmean : ∫ x, x ∂P = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2) (hc : 0 < c) :
    P.real {x : ℝ | c ≤ |x - μ₀|} ≤ σ2 / c ^ 2 := by
  have hL2' : MemLp (fun x : ℝ => x) 2 P := hL2
  have hsqint : Integrable (fun x : ℝ => (x - μ₀) ^ 2) P :=
    (hL2'.sub (memLp_const μ₀)).integrable_sq
  have hmeas : MeasurableSet {x : ℝ | c ≤ |x - μ₀|} :=
    measurableSet_le measurable_const (measurable_id.sub_const μ₀).abs
  have hind : Integrable
      (fun x => ({x : ℝ | c ≤ |x - μ₀|}).indicator (fun _ => c ^ 2) x) P :=
    (integrable_const (c ^ 2)).indicator hmeas
  have hptw : ∀ x : ℝ,
      ({x : ℝ | c ≤ |x - μ₀|}).indicator (fun _ => c ^ 2) x ≤ (x - μ₀) ^ 2 := by
    intro x
    by_cases hx : x ∈ {x : ℝ | c ≤ |x - μ₀|}
    · rw [Set.indicator_of_mem hx]
      have h : c ≤ |x - μ₀| := hx
      nlinarith [abs_nonneg (x - μ₀), sq_abs (x - μ₀)]
    · rw [Set.indicator_of_notMem hx]
      positivity
  have hle := integral_mono hind hsqint hptw
  rw [integral_indicator_const (c ^ 2) hmeas, smul_eq_mul, hvar] at hle
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **Chebyshev locates the quantiles** (`LM Theorem 6` proof): `Q_{1−p} ≤ μ₀ + σ/√p`. -/
private theorem quantile_upper_le {μ₀ σ2 p : ℝ} (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2) (_hσ : 0 < σ2) (hp : 0 < p) (hp1 : p < 1) :
    quantile P (1 - p) ≤ μ₀ + Real.sqrt (σ2 / p) := by
  refine csSup_le (quantile_set_nonempty_bddAbove P (by linarith) (by linarith)).1 ?_
  intro M hM
  have hM' : 1 - (1 - p) ≤ P.real {x : ℝ | M ≤ x} := hM
  rcases le_or_gt M μ₀ with hle | hlt
  · have : 0 ≤ Real.sqrt (σ2 / p) := Real.sqrt_nonneg _
    linarith
  · have hsub : {x : ℝ | M ≤ x} ⊆ {x : ℝ | (M - μ₀) ≤ |x - μ₀|} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact le_trans (by linarith) (le_abs_self (x - μ₀))
    have hcheb := chebyshev_tail hL2 hmean hvar (show (0:ℝ) < M - μ₀ by linarith)
    have hmono : P.real {x : ℝ | M ≤ x} ≤ P.real {x : ℝ | M - μ₀ ≤ |x - μ₀|} :=
      measureReal_mono hsub
    have hchain : p ≤ σ2 / (M - μ₀) ^ 2 := by linarith
    have hsq : (M - μ₀) ^ 2 ≤ σ2 / p := by
      rw [le_div_iff₀ hp, ← sub_nonneg]
      rw [le_div_iff₀ (pow_pos (by linarith : (0:ℝ) < M - μ₀) 2)] at hchain
      linarith
    have : M - μ₀ ≤ Real.sqrt (σ2 / p) := by
      calc M - μ₀ = Real.sqrt ((M - μ₀) ^ 2) := (Real.sqrt_sq (by linarith)).symm
        _ ≤ Real.sqrt (σ2 / p) := Real.sqrt_le_sqrt hsq
    linarith

/-- **Chebyshev locates the quantiles** (`LM Theorem 6` proof): `μ₀ − σ/√p ≤ Q_p`. -/
private theorem le_quantile_lower {μ₀ σ2 p : ℝ} (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2) (hσ : 0 < σ2) (hp : 0 < p) (hp1 : p < 1) :
    μ₀ - Real.sqrt (σ2 / p) ≤ quantile P p := by
  refine le_csSup (quantile_set_nonempty_bddAbove P hp hp1).2 ?_
  change 1 - p ≤ P.real {x : ℝ | μ₀ - Real.sqrt (σ2 / p) ≤ x}
  have hspos : 0 < Real.sqrt (σ2 / p) := Real.sqrt_pos.2 (by positivity)
  have hcheb := chebyshev_tail hL2 hmean hvar hspos
  have hsq : Real.sqrt (σ2 / p) ^ 2 = σ2 / p := Real.sq_sqrt (by positivity)
  have hsub : {x : ℝ | μ₀ - Real.sqrt (σ2 / p) ≤ x}ᶜ
      ⊆ {x : ℝ | Real.sqrt (σ2 / p) ≤ |x - μ₀|} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx ⊢
    rw [abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self (μ₀ - x))
  have hcompl : P.real {x : ℝ | μ₀ - Real.sqrt (σ2 / p) ≤ x}ᶜ
      ≤ P.real {x : ℝ | Real.sqrt (σ2 / p) ≤ |x - μ₀|} := measureReal_mono hsub
  rw [measureReal_compl (μ := P) (s := {x : ℝ | μ₀ - Real.sqrt (σ2 / p) ≤ x})
    measurableSet_Ici] at hcompl
  simp only [probReal_univ] at hcompl
  rw [hsq, show σ2 / (σ2 / p) = p by field_simp] at hcheb
  linarith

/-- Truncation is a contraction: `|φ(x) − φ(y)| ≤ |x − y|`. -/
private theorem truncate_lipschitz (a b x y : ℝ) :
    |truncate a b x - truncate a b y| ≤ |x - y| := by
  have h1 := le_abs_self (x - y)
  have h2 := neg_abs_le (x - y)
  rw [truncate, truncate, abs_le]
  constructor <;>
    · simp only [max_def, min_def]
      split_ifs <;> linarith

/-! ### Bernstein for a bounded transform of the sample

The truncated average is an average of i.i.d. variables bounded by the width of the
truncation interval, with variance at most `σ²`. That is exactly the regime Bernstein's
inequality is for: the huge range `σ√(n/r)` enters only through the scale `b`, multiplied
by the (small) deviation `t`. -/

open scoped ENNReal NNReal in
/-- **Bernstein for a bounded transform**: if `|g − c| ≤ B` with `∫g = c` and variance `v`,
the centred average of `g(Xᵢ)` has the Bernstein upper tail with scale `b = B/3`. -/
private theorem bounded_bernstein_upper {n : ℕ} {X : Fin n → Ξ → ℝ} {g : ℝ → ℝ} {c B v t : ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X μprob)
    (hX_law : ∀ i, μprob.map (X i) = P) (hgm : Measurable g)
    (hgb : ∀ x, |g x - c| ≤ B) (hB : 0 < B)
    (hgmean : ∫ x, g x ∂P = c) (hgvar : ∫ x, (g x - c) ^ 2 ∂P = v) (hv : 0 < v)
    (hn : 0 < n) (ht : 0 < t) :
    μprob {ξ | t < (∑ i, (g (X i ξ) - c)) / n}
      ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * t ^ 2 / (2 * (v + B / 3 * t)))) := by
  have hgcm : Measurable (fun x => g x - c) := hgm.sub measurable_const
  have hgcint : Integrable (fun x => g x - c) P := by
    refine Integrable.mono' (integrable_const B) hgcm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hgb x
  have hg2int : Integrable (fun x => (g x - c) ^ 2) P := by
    refine Integrable.mono' (integrable_const (B ^ 2)) (hgcm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hgb x, abs_nonneg (g x - c), sq_abs (g x - c)]
  have hgint : Integrable g P := by
    refine (hgcint.add (integrable_const c)).congr (Filter.Eventually.of_forall fun x => ?_)
    change g x - c + c = g x
    ring
  have hmean0 : ∫ x, (g x - c) ∂P = 0 := by
    rw [integral_sub hgint (integrable_const c), hgmean, integral_const]
    simp
  have htr : ∀ f : ℝ → ℝ, Measurable f → ∀ i, ∫ ξ, f (X i ξ) ∂μprob = ∫ x, f x ∂P := by
    intro f hf i
    rw [← hX_law i]
    exact (integral_map (hX_meas i).aemeasurable hf.aestronglyMeasurable).symm
  have htrL : ∀ f : ℝ → ℝ≥0∞, Measurable f → ∀ i,
      ∫⁻ ξ, f (X i ξ) ∂μprob = ∫⁻ x, f x ∂P := by
    intro f hf i
    rw [← hX_law i]
    exact (lintegral_map hf (hX_meas i)).symm
  have hBc : ∀ i, ConcentrationInequalities.HasBernsteinCondition
      (fun ξ => g (X i ξ) - c) (NNReal.mk v hv.le) (NNReal.mk (B / 3) (by positivity)) μprob := by
    intro i
    refine ⟨by rw [htr _ hgcm i]; exact hmean0, by
      rw [htr (fun x => (g x - c) ^ 2) (hgcm.pow_const 2) i]; exact hgvar, ?_⟩
    intro k hk
    have hpt : ∀ ξ : Ξ, |g (X i ξ) - c| ^ k ≤ (g (X i ξ) - c) ^ 2 * B ^ (k - 2) := by
      intro ξ
      calc |g (X i ξ) - c| ^ k
          = |g (X i ξ) - c| ^ 2 * |g (X i ξ) - c| ^ (k - 2) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ |g (X i ξ) - c| ^ 2 * B ^ (k - 2) := by
            gcongr
            exact hgb _
        _ = (g (X i ξ) - c) ^ 2 * B ^ (k - 2) := by rw [sq_abs]
    calc ∫⁻ ξ, ENNReal.ofReal (|g (X i ξ) - c| ^ k) ∂μprob
        ≤ ∫⁻ ξ, ENNReal.ofReal ((g (X i ξ) - c) ^ 2 * B ^ (k - 2)) ∂μprob :=
          lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hpt ξ)
      _ = ENNReal.ofReal (v * B ^ (k - 2)) := by
          rw [htrL (fun x => ENNReal.ofReal ((g x - c) ^ 2 * B ^ (k - 2)))
            (ENNReal.measurable_ofReal.comp ((hgcm.pow_const 2).mul_const _)) i,
            ← ofReal_integral_eq_lintegral_ofReal (hg2int.mul_const _)
              (Filter.Eventually.of_forall fun x => by positivity),
            integral_mul_const, hgvar]
      _ ≤ ENNReal.ofReal ((⟨v, hv.le⟩ : ℝ≥0) / 2 * (k.factorial : ℝ)
            * ((⟨B / 3, by positivity⟩ : ℝ≥0) : ℝ) ^ (k - 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hfac : (2 : ℝ) * 3 ^ (k - 2) ≤ (k.factorial : ℝ) := by
            exact_mod_cast two_mul_three_pow_le_factorial hk
          have h3 : (B / 3) ^ (k - 2) = B ^ (k - 2) / 3 ^ (k - 2) := by
            rw [div_pow]
          have hp3 : (0:ℝ) < (3:ℝ) ^ (k - 2) := by positivity
          have hpB : (0:ℝ) < B ^ (k - 2) := by positivity
          rw [h3, show v / 2 * (k.factorial : ℝ) * (B ^ (k - 2) / 3 ^ (k - 2))
              = (v * B ^ (k - 2)) * ((k.factorial : ℝ) / (2 * 3 ^ (k - 2))) by
            field_simp]
          have hone : (1:ℝ) ≤ (k.factorial : ℝ) / (2 * 3 ^ (k - 2)) :=
            (one_le_div (by positivity)).mpr hfac
          nlinarith [mul_nonneg hv.le hpB.le, hone]
  have hbern := ConcentrationInequalities.bernstein_inequality
    (X := fun i ξ => g (X i ξ) - c) (μ := μprob) (fun i => (hgcm.comp (hX_meas i)))
    (hX_indep.comp (fun _ => fun x : ℝ => g x - c) (fun _ => hgcm)) hBc hn
    (by rw [← NNReal.coe_pos, NNReal.coe_mk]; positivity)
    (by rw [← NNReal.coe_pos]; simpa using hv) ht
  refine le_trans hbern (le_of_eq ?_)
  congr 2

/-- Ledger, denominator: `2(v + (B/3)t) ≤ 16σ²` at `t = 4σ√(L/n)`, `B ≤ 2σ√(2n/r)`,
`v ≤ σ²` and `√(2n/r)·√(L/n) ≤ 5/8`. -/
private theorem ledger_denominator {σ2 s q y z B v : ℝ}
    (hs : s * s = σ2) (hs0 : 0 < s) (_hq0 : 0 ≤ q) (hy0 : 0 ≤ y)
    (hqy : q * y = z) (hz : z ≤ 5 / 8)
    (hB : B ≤ 2 * (s * q)) (_hB0 : 0 < B) (hv : v ≤ σ2) (hv0 : 0 < v) :
    2 * (v + B / 3 * (4 * s * y)) ≤ 16 * σ2 := by
  have hsy : (0:ℝ) ≤ 4 * s * y := by positivity
  have hσ0 : 0 < σ2 := by nlinarith
  have h1 : B / 3 * (4 * s * y) ≤ 2 * (s * q) / 3 * (4 * s * y) := by nlinarith
  have h2 : 2 * (s * q) / 3 * (4 * s * y) = 8 / 3 * σ2 * z := by rw [← hqy, ← hs]; ring
  have h3 : 8 / 3 * σ2 * z ≤ 5 / 3 * σ2 := by nlinarith
  linarith

/-- Ledger, numerator: `n·t² = 16σ²L` at `t = 4σ√(L/n)`. -/
private theorem ledger_numerator {σ2 s y L N : ℝ} (hs : s * s = σ2) (hy : y * y = L / N)
    (hN : 0 < N) : N * (4 * s * y) ^ 2 = 16 * σ2 * L := by
  have h : (4 * s * y) ^ 2 = 16 * (s * s) * (y * y) := by ring
  rw [h, hs, hy]
  field_simp

/-- Ledger, exponent: with numerator `16σ²L` and denominator at most `16σ²`, the Bernstein
exponent is at least `L`, so the tail is at most `δ/8` when `L = log(8/δ)`. -/
private theorem exp_le_of_ledger {N t D L σ2 δ : ℝ} (hDpos : 0 < D)
    (hnum : N * t ^ 2 = 16 * σ2 * L) (hD : D ≤ 16 * σ2) (hL : 0 < L)
    (hlog : L = Real.log (8 / δ)) (hδ : 0 < δ) :
    Real.exp (-N * t ^ 2 / D) ≤ δ / 8 := by
  have hge : L ≤ N * t ^ 2 / D := by
    rw [le_div_iff₀ hDpos, hnum]
    nlinarith
  calc Real.exp (-N * t ^ 2 / D) ≤ Real.exp (-L) := by
        refine Real.exp_le_exp.2 ?_
        rw [neg_mul, neg_div]
        linarith
    _ = δ / 8 := by
        rw [hlog, Real.exp_neg, Real.exp_log (by positivity)]
        field_simp

/-- The one sqrt identity of the Theorem 6 ledger: at `L = 3r/16` the Bernstein scale and
the deviation combine into `√((2n/r)(L/n)) = √(3/8)`. -/
private theorem sqrt_prod_ledger {n r : ℕ} {L : ℝ} (hN : (0 : ℝ) < n) (hR : (0 : ℝ) < r)
    (hL : L = 3 * r / 16) :
    Real.sqrt (2 * n / r) * Real.sqrt (L / n) = Real.sqrt (3 / 8) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  rw [hL]
  field_simp
  ring

open StatLean.MultipleTesting in
/-- **The concentration half at fixed levels** (`LM Theorem 6` proof, the Bernstein step).
For *deterministic* levels inside the outer brackets `[Q_{ε/2}, Q_{1−ε/2}]`, the truncated
average is within `4σ√(log(8/δ)/n)` of its own mean except with probability `δ/2`.

The ledger: the truncated variable has variance `v ≤ σ²` (truncation is a contraction) and
range `B ≤ 2σ√(2n/r)` (Chebyshev locates the quantiles), so at `t = 4σ√(L/n)` with
`r = 16L/3` the Bernstein scale contributes `Bt/3 ≤ (8/3)σ²√(3/8) ≤ (5/3)σ²`, the
denominator is at most `(16/3)σ²`, and the exponent is at least `3L ≥ L` — a factor `3`
of slack. Degenerate case: if `v = 0` the truncated variable is a.e. constant and the
deviation event is null. -/
private theorem fixed_level_concentration {n r : ℕ} {X : Fin n → Ξ → ℝ}
    {μ₀ σ2 δ α₀ β₀ : ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X μprob)
    (hX_law : ∀ i, μprob.map (X i) = P)
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀) (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    (hσ : 0 < σ2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : (r : ℝ) = 16 * Real.log (8 / δ) / 3) (hr1 : 1 ≤ r) (hrn : 4 * r < n)
    (hα : quantile P ((r : ℝ) / (2 * n)) ≤ α₀)
    (hβ : β₀ ≤ quantile P (1 - (r : ℝ) / (2 * n))) (hab : α₀ ≤ β₀) :
    μprob {ξ | 4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
        < |sampleMean (fun i => truncate α₀ β₀ (X i ξ)) - ∫ x, truncate α₀ β₀ x ∂P|}
      ≤ ENNReal.ofReal (δ / 2) := by
  have hn0 : 0 < n := by omega
  have hN : (0:ℝ) < n := by exact_mod_cast hn0
  have hR1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
  have hRN : 4 * (r:ℝ) < (n:ℝ) := by exact_mod_cast hrn
  have hL : 0 < Real.log (8 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hs2 : Real.sqrt σ2 * Real.sqrt σ2 = σ2 := Real.mul_self_sqrt hσ.le
  have hspos : 0 < Real.sqrt σ2 := Real.sqrt_pos.2 hσ
  have hLn : 0 < Real.log (8 / δ) / n := by positivity
  have htpos : 0 < 4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n) := by
    have := Real.sqrt_pos.2 hLn
    positivity
  -- ### The truncated variable: bounded, with mean `c` and variance `v ≤ σ²`.
  have hφm : Measurable (truncate α₀ β₀) :=
    measurable_const.max (measurable_const.min measurable_id)
  have hφmem : ∀ x, truncate α₀ β₀ x ∈ Set.Icc α₀ β₀ := truncate_mem_Icc hab
  have hφint : Integrable (fun x => truncate α₀ β₀ x) P := by
    refine Integrable.mono' (integrable_const (|α₀| + |β₀|)) hφm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h := hφmem x
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [h.1, neg_abs_le α₀, abs_nonneg β₀]
    · linarith [h.2, le_abs_self β₀, abs_nonneg α₀]
  have hcmem : α₀ ≤ ∫ x, truncate α₀ β₀ x ∂P ∧ (∫ x, truncate α₀ β₀ x ∂P) ≤ β₀ := by
    constructor
    · have := integral_mono (integrable_const α₀) hφint (fun x => (hφmem x).1)
      simpa using this
    · have := integral_mono hφint (integrable_const β₀) (fun x => (hφmem x).2)
      simpa using this
  have hbd : ∀ x, |truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P| ≤ β₀ - α₀ := by
    intro x
    rw [abs_le]
    constructor
    · linarith [(hφmem x).1, hcmem.2]
    · linarith [(hφmem x).2, hcmem.1]
  have hφ2int : Integrable
      (fun x => (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2) P := by
    refine Integrable.mono' (integrable_const ((β₀ - α₀) ^ 2))
      ((hφm.sub measurable_const).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hbd x, abs_nonneg (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P),
      sq_abs (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P)]
  have hv0 : 0 ≤ ∫ x, (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 ∂P :=
    integral_nonneg fun x => sq_nonneg _
  -- ### The sample mean in centred form.
  have hmeaneq : ∀ ξ, sampleMean (fun i => truncate α₀ β₀ (X i ξ))
        - ∫ y, truncate α₀ β₀ y ∂P
      = (∑ i, (truncate α₀ β₀ (X i ξ) - ∫ y, truncate α₀ β₀ y ∂P)) / n := by
    intro ξ
    rw [sampleMean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rcases eq_or_lt_of_le hv0 with hv | hv
  · -- ### Degenerate case: the truncated variable is a.e. constant.
    have hae : (fun x => (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hφ2int).1 hv.symm
    have hnull : P {x : ℝ | truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P ≠ 0} = 0 := by
      have hsub : {x : ℝ | truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P ≠ 0}
          ⊆ {x : ℝ | (fun x => (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2) x
              ≠ (0 : ℝ → ℝ) x} := by
        intro x hx
        simpa [pow_eq_zero_iff] using hx
      exact measure_mono_null hsub (by simpa [Filter.EventuallyEq, ae_iff] using hae)
    have haei : ∀ i, ∀ᵐ ξ ∂μprob,
        truncate α₀ β₀ (X i ξ) - ∫ y, truncate α₀ β₀ y ∂P = 0 := by
      intro i
      have hms : MeasurableSet
          {x : ℝ | truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P ≠ 0} :=
        (hφm.sub measurable_const) (measurableSet_singleton (0:ℝ)).compl
      have : μprob ((X i) ⁻¹'
          {x : ℝ | truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P ≠ 0}) = 0 := by
        rw [← Measure.map_apply (hX_meas i) hms, hX_law i]
        exact hnull
      rw [ae_iff]
      exact this
    have hallae : ∀ᵐ ξ ∂μprob, ∀ i,
        truncate α₀ β₀ (X i ξ) - ∫ y, truncate α₀ β₀ y ∂P = 0 :=
      ae_all_iff.2 haei
    have hbadnull : μprob {ξ | 4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
        < |sampleMean (fun i => truncate α₀ β₀ (X i ξ))
          - ∫ x, truncate α₀ β₀ x ∂P|} = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hallae)
      intro ξ hξ hcon
      simp only [Set.mem_setOf_eq] at hξ
      rw [hmeaneq ξ, Finset.sum_congr rfl (fun i _ => hcon i), Finset.sum_const, smul_zero,
        zero_div, abs_zero] at hξ
      linarith
    rw [hbadnull]
    exact zero_le
  · -- ### The Bernstein regime.
    have hBpos : 0 < β₀ - α₀ := by
      rcases eq_or_lt_of_le hab with hEq | hlt
      · exfalso
        have hB0 : β₀ - α₀ = 0 := by rw [← hEq]; ring
        have hzero : ∀ x, truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P = 0 := fun x => by
          have h := hbd x
          rw [hB0] at h
          exact abs_nonpos_iff.1 h
        have hz2 : ∫ x, (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 ∂P = 0 := by
          have hcg : ∫ x, (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 ∂P
              = ∫ _x : ℝ, (0:ℝ) ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall fun x => by
              change (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 = 0
              rw [hzero x]; ring)
          rw [hcg, integral_zero]
        linarith
      · linarith
    -- variance `v ≤ σ²`
    have hvσ : (∫ x, (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 ∂P) ≤ σ2 := by
      have hL2' : MemLp (fun x : ℝ => x) 2 P := hL2
      have hd := truncate_lipschitz α₀ β₀
      have hcontr : ∀ x : ℝ, (truncate α₀ β₀ x - truncate α₀ β₀ μ₀) ^ 2 ≤ (x - μ₀) ^ 2 := by
        intro x
        have h := hd x μ₀
        nlinarith [abs_nonneg (truncate α₀ β₀ x - truncate α₀ β₀ μ₀), abs_nonneg (x - μ₀),
          sq_abs (truncate α₀ β₀ x - truncate α₀ β₀ μ₀), sq_abs (x - μ₀)]
      have hdint : Integrable (fun x => (truncate α₀ β₀ x - truncate α₀ β₀ μ₀) ^ 2) P := by
        refine Integrable.mono' (integrable_const ((β₀ - α₀) ^ 2))
          ((hφm.sub measurable_const).pow_const 2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 := hφmem x
        have h2 := hφmem μ₀
        nlinarith [h1.1, h1.2, h2.1, h2.2]
      have hsqint : Integrable (fun x : ℝ => (x - μ₀) ^ 2) P :=
        (hL2'.sub (memLp_const μ₀)).integrable_sq
      -- the mean minimises the second moment
      have hexp : ∀ d : ℝ, ∫ x, (truncate α₀ β₀ x - d) ^ 2 ∂P
          = (∫ x, (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 ∂P)
            + ((∫ y, truncate α₀ β₀ y ∂P) - d) ^ 2 := by
        intro d
        have hcint : Integrable (fun x => truncate α₀ β₀ x
            - ∫ y, truncate α₀ β₀ y ∂P) P := hφint.sub (integrable_const _)
        have e0 : ∫ x, (truncate α₀ β₀ x - d) ^ 2 ∂P
            = ∫ x, ((truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2
                + (2 * ((∫ y, truncate α₀ β₀ y ∂P) - d)
                    * (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P)
                  + ((∫ y, truncate α₀ β₀ y ∂P) - d) ^ 2)) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
        have e1 : ∫ x, ((truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2
              + (2 * ((∫ y, truncate α₀ β₀ y ∂P) - d)
                  * (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P)
                + ((∫ y, truncate α₀ β₀ y ∂P) - d) ^ 2)) ∂P
            = (∫ x, (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 ∂P)
              + ∫ x, (2 * ((∫ y, truncate α₀ β₀ y ∂P) - d)
                  * (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P)
                + ((∫ y, truncate α₀ β₀ y ∂P) - d) ^ 2) ∂P :=
          integral_add hφ2int ((hcint.const_mul _).add (integrable_const _))
        have e2 : ∫ x, (2 * ((∫ y, truncate α₀ β₀ y ∂P) - d)
                * (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P)
              + ((∫ y, truncate α₀ β₀ y ∂P) - d) ^ 2) ∂P
            = (∫ x, 2 * ((∫ y, truncate α₀ β₀ y ∂P) - d)
                * (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ∂P)
              + ∫ _x : ℝ, ((∫ y, truncate α₀ β₀ y ∂P) - d) ^ 2 ∂P :=
          integral_add (hcint.const_mul _) (integrable_const _)
        have e3 : ∫ x, 2 * ((∫ y, truncate α₀ β₀ y ∂P) - d)
              * (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ∂P = 0 := by
          rw [integral_const_mul, integral_sub hφint (integrable_const _), integral_const]
          simp
        rw [e0, e1, e2, e3, integral_const]
        simp
      have hmin := hexp (truncate α₀ β₀ μ₀)
      have hle : ∫ x, (truncate α₀ β₀ x - truncate α₀ β₀ μ₀) ^ 2 ∂P ≤ σ2 := by
        rw [← hvar]
        exact integral_mono hdint hsqint hcontr
      nlinarith [sq_nonneg ((∫ y, truncate α₀ β₀ y ∂P) - truncate α₀ β₀ μ₀)]
    -- range `B ≤ 2σ√(2n/r)`
    have hp : (0:ℝ) < (r:ℝ) / (2 * n) := by positivity
    have hp1 : (r:ℝ) / (2 * n) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have hBle : β₀ - α₀ ≤ 2 * (Real.sqrt σ2 * Real.sqrt (2 * n / r)) := by
      have hup := quantile_upper_le (P := P) hL2 hmean hvar hσ hp hp1
      have hlo := le_quantile_lower (P := P) hL2 hmean hvar hσ hp hp1
      have hsplit : Real.sqrt (σ2 / ((r:ℝ) / (2 * n)))
          = Real.sqrt σ2 * Real.sqrt (2 * n / r) := by
        rw [show σ2 / ((r:ℝ) / (2 * n)) = σ2 * (2 * n / r) by field_simp,
          Real.sqrt_mul hσ.le]
      rw [hsplit] at hup hlo
      linarith
    -- the ledger
    have hprod : Real.sqrt (2 * n / r) * Real.sqrt (Real.log (8 / δ) / n)
        = Real.sqrt (3 / 8) :=
      sqrt_prod_ledger hN (by linarith) (by linarith)
    have hsq38 : Real.sqrt (3 / 8) ≤ 5 / 8 := by
      rw [show (5:ℝ) / 8 = Real.sqrt ((5 / 8) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hden : 2 * ((∫ x, (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 ∂P)
        + (β₀ - α₀) / 3 * (4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)))
        ≤ 16 * σ2 :=
      ledger_denominator hs2 hspos (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hprod hsq38
        hBle hBpos hvσ hv
    have hnum : (n:ℝ) * (4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)) ^ 2
        = 16 * σ2 * Real.log (8 / δ) :=
      ledger_numerator hs2 (Real.mul_self_sqrt hLn.le) hN
    have hDpos : (0:ℝ) < 2 * ((∫ x, (truncate α₀ β₀ x
          - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 ∂P)
        + (β₀ - α₀) / 3 * (4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n))) := by
      have h1 : (0:ℝ) < (β₀ - α₀) / 3
          * (4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)) :=
        mul_pos (by linarith) htpos
      linarith
    have hexpbd : Real.exp (-(n:ℝ)
          * (4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)) ^ 2
          / (2 * ((∫ x, (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 ∂P)
              + (β₀ - α₀) / 3 * (4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)))))
        ≤ δ / 8 :=
      exp_le_of_ledger hDpos hnum hden hL rfl hδ
    -- ### Two-sided Bernstein.
    have hupper := bounded_bernstein_upper (P := P) (g := truncate α₀ β₀)
      (c := ∫ y, truncate α₀ β₀ y ∂P) (B := β₀ - α₀)
      (v := ∫ x, (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 ∂P)
      hX_meas hX_indep hX_law hφm hbd hBpos rfl rfl hv hn0 htpos
    have hlower := bounded_bernstein_upper (P := P) (g := fun x => -truncate α₀ β₀ x)
      (c := -∫ y, truncate α₀ β₀ y ∂P) (B := β₀ - α₀)
      (v := ∫ x, (truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) ^ 2 ∂P)
      hX_meas hX_indep hX_law hφm.neg
      (fun x => by rw [show -truncate α₀ β₀ x - -∫ y, truncate α₀ β₀ y ∂P
          = -(truncate α₀ β₀ x - ∫ y, truncate α₀ β₀ y ∂P) by ring, abs_neg]; exact hbd x)
      hBpos (by rw [integral_neg]) (by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring) hv hn0 htpos
    have hsub : {ξ | 4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
          < |sampleMean (fun i => truncate α₀ β₀ (X i ξ))
            - ∫ x, truncate α₀ β₀ x ∂P|}
        ⊆ {ξ | 4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
            < (∑ i, (truncate α₀ β₀ (X i ξ) - ∫ y, truncate α₀ β₀ y ∂P)) / n}
          ∪ {ξ | 4 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
            < (∑ i, ((fun x => -truncate α₀ β₀ x) (X i ξ)
                - -∫ y, truncate α₀ β₀ y ∂P)) / n} := by
      intro ξ hξ
      simp only [Set.mem_setOf_eq] at hξ
      rw [hmeaneq ξ] at hξ
      have hsum : (∑ i, ((fun x => -truncate α₀ β₀ x) (X i ξ)
            - -∫ y, truncate α₀ β₀ y ∂P))
          = -(∑ i, (truncate α₀ β₀ (X i ξ) - ∫ y, truncate α₀ β₀ y ∂P)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rcases lt_abs.1 hξ with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        simp only [Set.mem_setOf_eq]
        rw [hsum, neg_div]
        exact h
    refine le_trans (le_trans (measure_mono hsub) (measure_union_le _ _)) ?_
    refine le_trans (add_le_add hupper hlower) ?_
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith

open StatLean.MultipleTesting Finset in
/-- Order statistics are measurable functions of the sample: `{ξ | v₍ₖ₎ ≤ t}` is exactly the
event that at least `k+1` coordinates are `≤ t`, a finite Boolean combination. -/
private theorem measurable_orderStat {m : ℕ} {W : Fin m → Ξ → ℝ}
    (hW : ∀ i, Measurable (W i)) (k : Fin m) :
    Measurable (fun ξ => orderStat (fun i => W i ξ) k) := by
  refine measurable_of_Iic fun t => ?_
  have hcard : Measurable (fun ξ => (univ.filter fun j => W j ξ ≤ t).card) := by
    have hsum : ∀ ξ, (univ.filter fun j => W j ξ ≤ t).card
        = ∑ j, if W j ξ ≤ t then 1 else 0 := fun ξ => by rw [Finset.card_filter]
    simp only [hsum]
    refine Finset.measurable_sum _ fun j _ => ?_
    exact Measurable.ite (measurableSet_le (hW j) measurable_const) measurable_const
      measurable_const
  have hset : (fun ξ => orderStat (fun i => W i ξ) k) ⁻¹' Set.Iic t
      = (fun ξ => (univ.filter fun j => W j ξ ≤ t).card) ⁻¹' {c : ℕ | (k:ℕ) + 1 ≤ c} := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    constructor
    · intro h
      refine le_trans (card_le_orderStat_le (fun i => W i ξ) k) (Finset.card_le_card ?_)
      intro j hj
      simp only [mem_filter] at hj ⊢
      exact ⟨hj.1, le_trans hj.2 h⟩
    · exact orderStat_le_of_card_le (fun i => W i ξ) k t
  rw [hset]
  exact hcard (MeasurableSet.of_discrete)

set_option maxHeartbeats 1000000 in
-- The product-measure bookkeeping elaborates several large `Set`/`Measure` unifications;
-- no single step is expensive, but they share one budget.
open StatLean.MultipleTesting in
/-- **The conditioning step of `LM Theorem 6`** ("conditionally on the second sample the
first sample is still i.i.d. `P`"): a bound that holds for every *fixed* admissible pair of
levels also holds when the levels are the order statistics of the calibration block.

The two coordinate blocks of the jointly independent family are independent
(`iIndepFun.indepFun_finset`), so the joint law is the product of the block laws
(`indepFun_iff_map_prod_eq_prod_map_map`) and `Measure.prod_apply` integrates the
sectionwise bound over the calibration marginal. The sections are exactly the fixed-level
events (empty when the levels are inadmissible), and the event itself is measurable in the
product because order statistics are (`measurable_orderStat`).

Comparing to a *constant* centre `μ₀` — rather than to the level-dependent centre
`∫ φ_{α,β} dP` — is what keeps this elementary: it avoids having to prove that the
parametrised integral `(α, β) ↦ ∫ φ_{α,β} dP` is measurable. The bias is folded into the
fixed-level bound instead. -/
private theorem block_transfer {n : ℕ} {Z : Fin n ⊕ Fin n → Ξ → ℝ} {a b : Fin n}
    {t c μ₀ : ℝ} {Good : ℝ → ℝ → Prop}
    (hZ_meas : ∀ i, Measurable (Z i)) (hZ_indep : iIndepFun Z μprob)
    (hGood : MeasurableSet {p : ℝ × ℝ | Good p.1 p.2}) (_hc : 0 ≤ c)
    (hfixed : ∀ α₀ β₀ : ℝ, Good α₀ β₀ →
      μprob {ξ | t < |sampleMean (fun i => truncate α₀ β₀ (Z (Sum.inl i) ξ)) - μ₀|}
        ≤ ENNReal.ofReal c) :
    μprob {ξ | Good (orderStat (fun i => Z (Sum.inr i) ξ) a)
          (orderStat (fun i => Z (Sum.inr i) ξ) b) ∧
        t < |trimmedMeanAt a b (fun i => Z (Sum.inl i) ξ) (fun i => Z (Sum.inr i) ξ) - μ₀|}
      ≤ ENNReal.ofReal c := by
  classical
  have hYmeas : Measurable (fun ξ => (fun i => Z (Sum.inr i) ξ : Fin n → ℝ)) :=
    measurable_pi_lambda _ fun i => hZ_meas _
  have hXmeas : Measurable (fun ξ => (fun i => Z (Sum.inl i) ξ : Fin n → ℝ)) :=
    measurable_pi_lambda _ fun i => hZ_meas _
  -- ### The two coordinate blocks are independent.
  have hdisj : Disjoint (Finset.univ.image (Sum.inr : Fin n → Fin n ⊕ Fin n))
      (Finset.univ.image (Sum.inl : Fin n → Fin n ⊕ Fin n)) := by
    refine Finset.disjoint_left.2 fun i hi hi' => ?_
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi hi'
    obtain ⟨j, hj⟩ := hi
    obtain ⟨k, hk⟩ := hi'
    rw [← hj] at hk
    exact Sum.inl_ne_inr hk
  have hindep : IndepFun (fun ξ => (fun i => Z (Sum.inr i) ξ : Fin n → ℝ))
      (fun ξ => (fun i => Z (Sum.inl i) ξ : Fin n → ℝ)) μprob := by
    have hφ : Measurable (fun u : (Finset.univ.image (Sum.inr : Fin n → Fin n ⊕ Fin n))
        → ℝ => (fun i : Fin n => u ⟨Sum.inr i, by simp⟩ : Fin n → ℝ)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply _
    have hψ : Measurable (fun u : (Finset.univ.image (Sum.inl : Fin n → Fin n ⊕ Fin n))
        → ℝ => (fun i : Fin n => u ⟨Sum.inl i, by simp⟩ : Fin n → ℝ)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply _
    exact (hZ_indep.indepFun_finset _ _ hdisj hZ_meas).comp hφ hψ
  -- ### The deviation event is a measurable subset of the product.
  have hcoord1 : ∀ i : Fin n,
      Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i) :=
    fun i => (measurable_pi_apply i).comp measurable_fst
  have hcoord2 : ∀ i : Fin n,
      Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 i) :=
    fun i => (measurable_pi_apply i).comp measurable_snd
  have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => orderStat p.1 a) :=
    measurable_orderStat hcoord1 a
  have h2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => orderStat p.1 b) :=
    measurable_orderStat hcoord1 b
  have h3 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      |trimmedMeanAt a b p.2 p.1 - μ₀|) := by
    refine (Measurable.sub ?_ measurable_const).abs
    refine Measurable.div ?_ measurable_const
    refine Finset.measurable_sum _ fun i _ => ?_
    exact h1.max (h2.min (hcoord2 i))
  have hEmeas : MeasurableSet {p : (Fin n → ℝ) × (Fin n → ℝ) |
      Good (orderStat p.1 a) (orderStat p.1 b) ∧ t < |trimmedMeanAt a b p.2 p.1 - μ₀|} :=
    ((h1.prodMk h2) hGood).inter (measurableSet_lt measurable_const h3)
  -- ### Fubini for the product of the two block laws.
  have hpre : {ξ | Good (orderStat (fun i => Z (Sum.inr i) ξ) a)
        (orderStat (fun i => Z (Sum.inr i) ξ) b) ∧
      t < |trimmedMeanAt a b (fun i => Z (Sum.inl i) ξ) (fun i => Z (Sum.inr i) ξ) - μ₀|}
      = (fun ξ => ((fun i => Z (Sum.inr i) ξ : Fin n → ℝ),
          (fun i => Z (Sum.inl i) ξ : Fin n → ℝ))) ⁻¹'
        {p : (Fin n → ℝ) × (Fin n → ℝ) | Good (orderStat p.1 a) (orderStat p.1 b)
          ∧ t < |trimmedMeanAt a b p.2 p.1 - μ₀|} := rfl
  rw [hpre, ← Measure.map_apply (hYmeas.prodMk hXmeas) hEmeas,
    (indepFun_iff_map_prod_eq_prod_map_map hYmeas.aemeasurable hXmeas.aemeasurable).1 hindep,
    Measure.prod_apply hEmeas]
  have hsection : ∀ y : Fin n → ℝ,
      (μprob.map (fun ξ => (fun i => Z (Sum.inl i) ξ : Fin n → ℝ)))
          (Prod.mk y ⁻¹' {p : (Fin n → ℝ) × (Fin n → ℝ) |
            Good (orderStat p.1 a) (orderStat p.1 b)
              ∧ t < |trimmedMeanAt a b p.2 p.1 - μ₀|})
        ≤ ENNReal.ofReal c := by
    intro y
    rw [Measure.map_apply hXmeas (hEmeas.preimage measurable_prodMk_left)]
    by_cases hg : Good (orderStat y a) (orderStat y b)
    · refine le_trans (measure_mono ?_) (hfixed (orderStat y a) (orderStat y b) hg)
      intro ξ hξ
      exact hξ.2
    · have hempty : ((fun ξ => (fun i => Z (Sum.inl i) ξ : Fin n → ℝ)) ⁻¹'
          (Prod.mk y ⁻¹' {p : (Fin n → ℝ) × (Fin n → ℝ) |
            Good (orderStat p.1 a) (orderStat p.1 b)
              ∧ t < |trimmedMeanAt a b p.2 p.1 - μ₀|})) = ∅ := by
        ext ξ
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        exact fun hcon => absurd hcon hg
      rw [hempty, measure_empty]
      positivity
  have hprob : IsProbabilityMeasure
      (μprob.map (fun ξ => (fun i => Z (Sum.inr i) ξ : Fin n → ℝ))) :=
    Measure.isProbabilityMeasure_map hYmeas.aemeasurable
  calc ∫⁻ y, (μprob.map (fun ξ => (fun i => Z (Sum.inl i) ξ : Fin n → ℝ)))
          (Prod.mk y ⁻¹' {p : (Fin n → ℝ) × (Fin n → ℝ) |
            Good (orderStat p.1 a) (orderStat p.1 b)
              ∧ t < |trimmedMeanAt a b p.2 p.1 - μ₀|})
          ∂(μprob.map (fun ξ => (fun i => Z (Sum.inr i) ξ : Fin n → ℝ)))
      ≤ ∫⁻ _y, ENNReal.ofReal c
          ∂(μprob.map (fun ξ => (fun i => Z (Sum.inr i) ξ : Fin n → ℝ))) :=
        lintegral_mono hsection
    _ = ENNReal.ofReal c := by simp

open StatLean.MultipleTesting in
/-- **The trimmed mean is sub-Gaussian** (`LM Theorem 6`): two independent i.i.d.
samples of size `n` (presented as one jointly independent family on `Fin n ⊕ Fin n`;
`.inl` = averaged sample, `.inr` = truncation-calibration sample), variance `σ² > 0`,
`δ ∈ (0,1)` with `n > (16/3) log(8/δ)`, trim count `r = εn` for
`ε = 16 log(8/δ)/(3n)` (LM's "εn is an integer" simplification, carried as the
integrality hypothesis `hr`). Then with probability at least `1 − δ`,

  `|μ̂₂ₙ − μ₀| ≤ 9 σ √(log(8/δ)/n)`.

**Constant note.** LM's `9` combines a bias term they bound by `6σ√(log(8/δ)/n)` and a
Bernstein term bounded by `3σ√(log(8/δ)/n)`; the closure lane must verify the composite
constant and, per the project constants policy, repair to the provable value (keeping
the `σ√(log(8/δ)/n)` shape) with a documented deviation if `9` does not survive
formalization. -/
theorem trimmedMean_deviation {n r : ℕ} {Z : Fin n ⊕ Fin n → Ξ → ℝ}
    {a b : Fin n} {μ₀ σ2 δ : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §2.3 regularity
    (hZ_meas : ∀ i, Measurable (Z i))
    -- USER-INPUT: the 2n observations are jointly independent; LM Theorem 6
    (hZ_indep : iIndepFun Z μprob)
    -- USER-INPUT: common law P; LM Theorem 6
    (hZ_law : ∀ i, μprob.map (Z i) = P)
    -- USER-INPUT: P is square-integrable with mean μ₀ and variance σ² > 0; LM Thm 6
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2) (hσ : 0 < σ2)
    -- USER-INPUT: nonatomic P; LM §2.3 proof simplification
    (hatom : ∀ t : ℝ, P {t} = 0)
    -- USER-INPUT: confidence level and sample-size condition; LM Theorem 6
    (hδ : 0 < δ) (hδ1 : δ < 1) (hn : 16 / 3 * Real.log (8 / δ) < n)
    -- USER-INPUT: trim count integrality ε·n = r; LM §2.3 step (1) simplification
    (hr : (r : ℝ) = 16 * Real.log (8 / δ) / 3) (hr1 : 1 ≤ r) (hrn : 4 * r < n)
    -- USER-INPUT: trimming indices (0-indexed); LM §2.3 step (2)
    (ha : (a : ℕ) + 1 = r) (hb : (b : ℕ) + r + 1 = n) :
    μprob.real {ξ | 9 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
        < |trimmedMeanAt a b (fun i => Z (.inl i) ξ) (fun i => Z (.inr i) ξ) - μ₀|}
      ≤ δ := by
  have hn0 : 0 < n := by omega
  have hN : (0:ℝ) < n := by exact_mod_cast hn0
  have hR1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
  have hRN : 4 * (r:ℝ) < (n:ℝ) := by exact_mod_cast hrn
  have hL : 0 < Real.log (8 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hLn : 0 < Real.log (8 / δ) / n := by positivity
  -- ### The two blocks: each is an i.i.d. `P`-sample.
  have hYm : ∀ i, Measurable (fun ξ => Z (Sum.inr i) ξ) := fun i => hZ_meas _
  have hXm : ∀ i, Measurable (fun ξ => Z (Sum.inl i) ξ) := fun i => hZ_meas _
  have hYind : iIndepFun (fun i => Z (Sum.inr i)) μprob :=
    hZ_indep.precomp Sum.inr_injective
  have hXind : iIndepFun (fun i => Z (Sum.inl i)) μprob :=
    hZ_indep.precomp Sum.inl_injective
  have hYlaw : ∀ i, μprob.map (fun ξ => Z (Sum.inr i) ξ) = P := fun i => hZ_law _
  have hXlaw : ∀ i, μprob.map (fun ξ => Z (Sum.inl i) ξ) = P := fun i => hZ_law _
  -- ### The `δ`-bookkeeping: `4 exp(−(3/16) r) = δ/2` exactly, by the choice of `r`.
  have hexp : Real.exp (-(3 / 16) * r) = δ / 8 := by
    rw [show (-(3 / 16) : ℝ) * r = -Real.log (8 / δ) by rw [hr]; ring, Real.exp_neg,
      Real.exp_log (by positivity)]
    field_simp
  -- ### The bracket event and its measurability.
  have hbrack := orderStat_quantile_brackets (μprob := μprob) (P := P)
    (Y := fun i => Z (Sum.inr i)) (a := a) (b := b) hYm hYind hYlaw hatom hr1 hrn ha hb
  rw [hexp] at hbrack
  have hoa : Measurable (fun ξ => orderStat (fun i => Z (Sum.inr i) ξ) a) :=
    measurable_orderStat hYm a
  have hob : Measurable (fun ξ => orderStat (fun i => Z (Sum.inr i) ξ) b) :=
    measurable_orderStat hYm b
  have hGmeas : MeasurableSet {ξ |
      quantile P ((r:ℝ) / (2 * n)) ≤ orderStat (fun i => Z (Sum.inr i) ξ) a ∧
      orderStat (fun i => Z (Sum.inr i) ξ) a ≤ quantile P (2 * (r:ℝ) / n) ∧
      quantile P (1 - 2 * (r:ℝ) / n) ≤ orderStat (fun i => Z (Sum.inr i) ξ) b ∧
      orderStat (fun i => Z (Sum.inr i) ξ) b ≤ quantile P (1 - (r:ℝ) / (2 * n))} :=
    (measurableSet_le measurable_const hoa).inter
      ((measurableSet_le hoa measurable_const).inter
        ((measurableSet_le measurable_const hob).inter
          (measurableSet_le hob measurable_const)))
  have hGc : μprob.real {ξ |
      quantile P ((r:ℝ) / (2 * n)) ≤ orderStat (fun i => Z (Sum.inr i) ξ) a ∧
      orderStat (fun i => Z (Sum.inr i) ξ) a ≤ quantile P (2 * (r:ℝ) / n) ∧
      quantile P (1 - 2 * (r:ℝ) / n) ≤ orderStat (fun i => Z (Sum.inr i) ξ) b ∧
      orderStat (fun i => Z (Sum.inr i) ξ) b ≤ quantile P (1 - (r:ℝ) / (2 * n))}ᶜ
      ≤ δ / 2 := by
    rw [measureReal_compl hGmeas]
    simp only [probReal_univ]
    linarith
  -- ### The admissible level set, and the fixed-level concentration on it.
  have hGoodMeas : MeasurableSet {p : ℝ × ℝ |
      quantile P ((r:ℝ) / (2 * n)) ≤ p.1 ∧ p.1 ≤ quantile P (2 * (r:ℝ) / n) ∧
      quantile P (1 - 2 * (r:ℝ) / n) ≤ p.2 ∧ p.2 ≤ quantile P (1 - (r:ℝ) / (2 * n))} :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)))
  have hp0 : (0:ℝ) < 2 * (r:ℝ) / n := by positivity
  have hp1 : 2 * (r:ℝ) / n < 1 := by rw [div_lt_one hN]; linarith
  have hb5 : Real.sqrt σ2 * Real.sqrt (4 * (r:ℝ) / n)
      ≤ 5 * (Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)) := by
    have h25 : Real.sqrt (4 * (r:ℝ) / n) ≤ 5 * Real.sqrt (Real.log (8 / δ) / n) := by
      rw [show (5:ℝ) * Real.sqrt (Real.log (8 / δ) / n)
          = Real.sqrt (25 * (Real.log (8 / δ) / n)) by
        rw [Real.sqrt_mul (by norm_num),
          show Real.sqrt 25 = 5 by
            rw [show (25:ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
      refine Real.sqrt_le_sqrt ?_
      have hgap : 25 * (Real.log (8 / δ) / n) - 4 * (r:ℝ) / n
          = (25 * Real.log (8 / δ) - 4 * (r:ℝ)) / n := by ring
      have hnn : 0 ≤ (25 * Real.log (8 / δ) - 4 * (r:ℝ)) / n := by
        refine div_nonneg ?_ hN.le
        rw [hr]; linarith
      linarith
    nlinarith [Real.sqrt_nonneg σ2, Real.sqrt_nonneg (4 * (r:ℝ) / n)]
  -- ### The fixed-level deviation bound: bias + Bernstein, at deterministic levels.
  have hfixed : ∀ α₀ β₀ : ℝ,
      (quantile P ((r:ℝ) / (2 * n)) ≤ α₀ ∧ α₀ ≤ quantile P (2 * (r:ℝ) / n) ∧
        quantile P (1 - 2 * (r:ℝ) / n) ≤ β₀ ∧ β₀ ≤ quantile P (1 - (r:ℝ) / (2 * n))) →
      μprob {ξ | 9 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
          < |sampleMean (fun i => truncate α₀ β₀ (Z (Sum.inl i) ξ)) - μ₀|}
        ≤ ENNReal.ofReal (δ / 2) := by
    intro α₀ β₀ hgood
    have hhalf : 2 * (r:ℝ) / n ≤ 1 - 2 * (r:ℝ) / n := by
      rw [le_sub_iff_add_le, show 2 * (r:ℝ) / n + 2 * (r:ℝ) / n = 4 * (r:ℝ) / n by ring,
        div_le_one hN]
      linarith
    have hab : α₀ ≤ β₀ :=
      le_trans hgood.2.1
        (le_trans (quantile_mono P hp0 (by linarith) hhalf) hgood.2.2.1)
    have hconc := fixed_level_concentration hXm hXind hXlaw hL2 hmean hvar hσ hδ hδ1 hr
      hr1 hrn hgood.1 hgood.2.2.2 hab
    have hbias := truncated_bias_le_sharp (P := P) hL2 hmean hvar hatom hr1 hrn
      hgood.1 hgood.2.1 hgood.2.2.1 hgood.2.2.2
    refine le_trans (measure_mono ?_) hconc
    intro ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    have htri := abs_sub_le (sampleMean (fun i => truncate α₀ β₀ (Z (Sum.inl i) ξ)))
      (∫ x, truncate α₀ β₀ x ∂P) μ₀
    linarith
  -- ### Transfer to the data-driven levels.
  have hD := block_transfer (μ₀ := μ₀) (a := a) (b := b)
    (t := 9 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)) (c := δ / 2)
    hZ_meas hZ_indep hGoodMeas (by linarith) hfixed
  -- ### Union bound: brackets fail with probability `δ/2`, the deviation with `δ/2`.
  refine le_trans (le_trans (measureReal_mono (show
      {ξ | 9 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
        < |trimmedMeanAt a b (fun i => Z (Sum.inl i) ξ) (fun i => Z (Sum.inr i) ξ) - μ₀|}
      ⊆ {ξ |
        quantile P ((r:ℝ) / (2 * n)) ≤ orderStat (fun i => Z (Sum.inr i) ξ) a ∧
        orderStat (fun i => Z (Sum.inr i) ξ) a ≤ quantile P (2 * (r:ℝ) / n) ∧
        quantile P (1 - 2 * (r:ℝ) / n) ≤ orderStat (fun i => Z (Sum.inr i) ξ) b ∧
        orderStat (fun i => Z (Sum.inr i) ξ) b ≤ quantile P (1 - (r:ℝ) / (2 * n))}ᶜ
        ∪ {ξ | (quantile P ((r:ℝ) / (2 * n)) ≤ orderStat (fun i => Z (Sum.inr i) ξ) a ∧
              orderStat (fun i => Z (Sum.inr i) ξ) a ≤ quantile P (2 * (r:ℝ) / n) ∧
              quantile P (1 - 2 * (r:ℝ) / n) ≤ orderStat (fun i => Z (Sum.inr i) ξ) b ∧
              orderStat (fun i => Z (Sum.inr i) ξ) b
                ≤ quantile P (1 - (r:ℝ) / (2 * n))) ∧
            9 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
              < |trimmedMeanAt a b (fun i => Z (Sum.inl i) ξ) (fun i => Z (Sum.inr i) ξ)
                - μ₀|} from ?_))
    (measureReal_union_le _ _)) ?_
  · intro ξ hξ
    by_cases hg : quantile P ((r:ℝ) / (2 * n)) ≤ orderStat (fun i => Z (Sum.inr i) ξ) a ∧
        orderStat (fun i => Z (Sum.inr i) ξ) a ≤ quantile P (2 * (r:ℝ) / n) ∧
        quantile P (1 - 2 * (r:ℝ) / n) ≤ orderStat (fun i => Z (Sum.inr i) ξ) b ∧
        orderStat (fun i => Z (Sum.inr i) ξ) b ≤ quantile P (1 - (r:ℝ) / (2 * n))
    · exact Or.inr ⟨hg, hξ⟩
    · exact Or.inl hg
  · have hDreal : μprob.real {ξ | (quantile P ((r:ℝ) / (2 * n))
              ≤ orderStat (fun i => Z (Sum.inr i) ξ) a ∧
            orderStat (fun i => Z (Sum.inr i) ξ) a ≤ quantile P (2 * (r:ℝ) / n) ∧
            quantile P (1 - 2 * (r:ℝ) / n) ≤ orderStat (fun i => Z (Sum.inr i) ξ) b ∧
            orderStat (fun i => Z (Sum.inr i) ξ) b
              ≤ quantile P (1 - (r:ℝ) / (2 * n))) ∧
          9 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
            < |trimmedMeanAt a b (fun i => Z (Sum.inl i) ξ) (fun i => Z (Sum.inr i) ξ)
              - μ₀|} ≤ δ / 2 := by
      rw [measureReal_def]
      calc (μprob _).toReal ≤ (ENNReal.ofReal (δ / 2)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hD
        _ = δ / 2 := ENNReal.toReal_ofReal (by linarith)
    linarith

end StatLean.RobustStatistics
