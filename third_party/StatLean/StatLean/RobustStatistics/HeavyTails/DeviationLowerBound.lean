module
public import StatLean.RobustStatistics.Core.Contamination
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# The sub-Gaussian deviation rate is optimal — no estimator beats `σ√(log(1/(2δ))/n)`

The minimax counterpart of the estimators in this directory (`LM Theorem 1`, after
Devroye–Lerasle–Lugosi–Oliveira (2016)): for *any* mean estimator there is a
finite-variance distribution on which its deviation at confidence `δ` is at least
`σ√(log(1/(2δ))/n)`. The witness family is a two-point pair `P₊, P₋` placing mass `p` at
`±c` and `1 − p` at `0` — built here from Round-1's `contaminate` applied to Dirac
masses — coupled so that the two samples agree with probability `(1−p)ⁿ = 2δ`; on that
event no estimator can be simultaneously close to both means `±pc`.

**Constant.** `LM` print the threshold as `σ√(log(1/δ)/n)`; the threshold proved here is
`σ√(log(1/(2δ))/n)`. The `log 2` is the price of the factor `2` in the two-point
argument and cannot be removed along this route on the frozen window `δ < 1/2` — see the
`CONSTANT REPAIR` note on `mean_estimator_deviation_lower`.

* `twoPointPM` and its mean/variance.
* `twoPointCoupling` — the joint law on `ℝ × ℝ`, its marginals, and the diagonal mass.
* `agree_pow` — the samples agree with probability `(1 − p)ⁿ`.
* `mean_estimator_deviation_lower` — `LM Theorem 1`.

**Honest reading of the statement.** LM phrase the conclusion "there exists a
distribution with mean `μ` and variance `σ²`"; the two exhibited distributions have
means `±pc`, so the centering in the deviation event is the exhibited distribution's
*own* mean (the pair cannot share it), and the free centering `μ` of LM's phrasing is
recovered by translating the whole construction. We state the translation-fixed form.

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §2, Theorem 1; after L. Devroye, M. Lerasle, G. Lugosi and R. I. Oliveira,
*Sub-Gaussian mean estimators*, Ann. Statist. 44 (2016).

**Bibliographic comments.** The two-point coupling argument is Devroye, Lerasle, Lugosi and
Oliveira, "Sub-Gaussian mean estimators," *Ann. Statist.* **44** (2016), 2695–2725 (their
Theorem 3.1 context); the earlier sharpness-of-Chebyshev statement is Catoni (2012),
Proposition 6.2. Together they bracket the empirical mean strictly between the Chebyshev
baseline and the sub-Gaussian optimum.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

/-- **The two-point distribution** `P_c,p{c} = p`, `P_c,p{0} = 1 − p` (`LM Theorem 1`
proof): Round-1's `contaminate` of a Dirac mass at `0` by a Dirac mass at `c`. -/
noncomputable def twoPointPM (c p : ℝ) : Measure ℝ :=
  contaminate (Measure.dirac 0) (Measure.dirac c) p

/-- The two-point law is a probability measure for `p ∈ [0, 1]` — Round-1's
`isProbabilityMeasure_contaminate` applied to two Dirac masses. -/
theorem isProbabilityMeasure_twoPointPM {c p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (twoPointPM c p) :=
  isProbabilityMeasure_contaminate _ _ hp0 hp1

/-- Mean of the two-point distribution: `∫ x dP_{c,p} = pc` (`LM Theorem 1` proof,
"the means of the two distributions are ±pc"). -/
theorem integral_twoPointPM {c p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ x, x ∂twoPointPM c p = p * c := by
  rw [twoPointPM, integral_contaminate hp0 hp1 (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  ring

/-- Variance of the two-point distribution: `σ² = c²p(1 − p)` (`LM Theorem 1` proof). -/
theorem variance_twoPointPM {c p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ x, (x - p * c) ^ 2 ∂twoPointPM c p = c ^ 2 * p * (1 - p) := by
  rw [twoPointPM, integral_contaminate hp0 hp1 (integrable_dirac (by finiteness))
    (integrable_dirac (by finiteness)), integral_dirac, integral_dirac]
  ring

/-- **The coupling** (`LM Theorem 1` proof): the joint law of a pair `(X, Y)` with
`P(X = Y = 0) = 1 − p` and `P(X = c, Y = −c) = p`. -/
noncomputable def twoPointCoupling (c p : ℝ) : Measure (ℝ × ℝ) :=
  contaminate (Measure.dirac ((0 : ℝ), (0 : ℝ))) (Measure.dirac (c, -c)) p

/-- The first marginal of the coupling is `P₊ = P_{c,p}`. -/
theorem twoPointCoupling_fst {c p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (twoPointCoupling c p).map Prod.fst = twoPointPM c p := by
  rw [twoPointCoupling, map_contaminate measurable_fst, Measure.map_dirac' measurable_fst,
    Measure.map_dirac' measurable_fst, twoPointPM]

/-- The second marginal of the coupling is `P₋ = P_{−c,p}`. -/
theorem twoPointCoupling_snd {c p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (twoPointCoupling c p).map Prod.snd = twoPointPM (-c) p := by
  rw [twoPointCoupling, map_contaminate measurable_snd, Measure.map_dirac' measurable_snd,
    Measure.map_dirac' measurable_snd, twoPointPM]

/-- **The coupled samples agree with probability `(1 − p)ⁿ`** (`LM Theorem 1` proof,
`P{X₁ⁿ = Y₁ⁿ} = (1 − p)ⁿ`): under the `n`-fold product of the coupling, all coordinate
pairs are equal exactly when every pair drew its `(0,0)` atom. Requires `c ≠ 0` (else
the atoms coincide and the probability is `1`). -/
theorem twoPointCoupling_agree_pow {c p : ℝ} (hc : c ≠ 0) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) :
    (Measure.pi fun _ : Fin n => twoPointCoupling c p).real
        {w | ∀ i, (w i).1 = (w i).2}
      = (1 - p) ^ n := by
  haveI : IsProbabilityMeasure (twoPointCoupling c p) :=
    isProbabilityMeasure_contaminate _ _ hp0 hp1
  have hD : MeasurableSet {q : ℝ × ℝ | q.1 = q.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hset : {w : Fin n → ℝ × ℝ | ∀ i, (w i).1 = (w i).2}
      = Set.univ.pi fun _ : Fin n => {q : ℝ × ℝ | q.1 = q.2} := by
    ext w; simp [Set.mem_pi]
  have hcc : ((c, -c) : ℝ × ℝ) ∉ {q : ℝ × ℝ | q.1 = q.2} := by
    intro h
    simp only [Set.mem_setOf_eq] at h
    exact hc (by linarith)
  have hν : twoPointCoupling c p {q : ℝ × ℝ | q.1 = q.2} = ENNReal.ofReal (1 - p) := by
    rw [twoPointCoupling, contaminate_apply, Measure.dirac_apply' _ hD,
      Measure.dirac_apply' _ hD, Set.indicator_of_mem (by simp) _,
      Set.indicator_of_notMem hcc]
    simp
  rw [measureReal_def, hset, Measure.pi_pi]
  simp only [hν, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 1 - p)]
  exact ENNReal.toReal_ofReal (pow_nonneg (by linarith) n)

/-- **No mean estimator beats the sub-Gaussian rate** (`LM Theorem 1`): for every
sample size `n > 5`, confidence `δ ∈ (2e^{−n/4}, 1/2)`, target variance `σ² > 0`, and
*any* measurable estimator `μ̂ : (Fin n → ℝ) → ℝ`, there is a probability distribution
`P` with variance `σ²` whose own mean `μ_P` satisfies

  `Pⁿ( |μ̂ − μ_P| > σ√(log(1/(2δ))/n) ) ≥ δ`.

The witness is one of the coupled two-point pair with `1 − p = (2δ)^{1/n}` and
`c = σ/√(p(1−p))`; the agreement event has probability exactly `2δ` and forces one of
the two means — which are `2pc` apart — to be missed, so one of the two error
probabilities is `≥ δ`.

**CONSTANT REPAIR (deviation from `LM Theorem 1` as printed).** LM state the threshold
as `σ√(log(1/δ)/n)`; the threshold proved here is `σ√(log(1/(2δ))/n)`, i.e. their
`log(1/δ)` is replaced by `log(1/(2δ)) = log(1/δ) − log 2`. The shape (and the
asymptotics as `δ → 0`) is unchanged; the `log 2` is the honest price of the factor `2`
in the two-point argument, and it cannot be avoided along this route:

* the argument only ever gives `max(err₊, err₋) ≥ ½·P{X₁ⁿ = Y₁ⁿ} = ½(1−p)ⁿ`, so a
  conclusion `≥ δ` *requires* `(1−p)ⁿ ≥ 2δ`, i.e. `n·log(1/(1−p)) ≤ log(1/δ) − log 2`;
* the separation of the two means is `pc = σ√(p/(1−p))`, so a threshold
  `C·σ√(log(1/δ)/n)` *requires* `p/(1−p) > C²·log(1/δ)/n`.

Writing `q = p/(1−p)` and `L = log(1/δ)`, the first demand is exactly
`1 − p ≥ (2δ)^{1/n}`, i.e. `q ≤ e^{(L−log 2)/n} − 1`, while the second is
`q > C²L/n`. As `δ ↑ 1/2` the available separation `e^{(L−log 2)/n} − 1` tends to `0`
whereas the demanded one stays `≥ C²(log 2)/n > 0`, so **no constant `C > 0` works
uniformly on the frozen window `δ < 1/2`**: the `log 2` has to move inside the
logarithm, which is what the statement below does. (Restricting to `δ ≤ 1/4` would
instead permit `C = 1/√2`, since then `L ≥ 2 log 2` and `C²L ≤ L − log 2`.) The choice
`1 − p = (2δ)^{1/n}` used here is the extremal one — it makes the agreement probability
exactly `2δ` — and `e^x − 1 > x` then gives the strict separation.

This is an obstruction *for the two-point route*, not a refutation of `LM Theorem 1` as
printed: no estimator beating the `C = 1` threshold is exhibited here, so the original
statement is left open rather than marked false.

Only `0 < δ` is used from `hδlo` and only `0 < n` from `hn`; both frozen hypotheses are
kept (the sharper window is what `LM` need for their own choice `p = log(2/δ)/(2n)`,
which is not the optimal one). -/
theorem mean_estimator_deviation_lower {n : ℕ} (hn : 5 < n) {δ σ2 : ℝ}
    -- USER-INPUT: confidence window; LM Theorem 1 (`δ ∈ (2e^{−n/4}, 1/2)`)
    (hδlo : 2 * Real.exp (-(n : ℝ) / 4) < δ) (hδhi : δ < 1 / 2)
    -- USER-INPUT: nondegenerate variance; LM Theorem 1 (`σ > 0`)
    (hσ : 0 < σ2)
    -- USER-INPUT: the estimator, an arbitrary statistic of the sample; LM §2
    (μhat : (Fin n → ℝ) → ℝ)
    -- LEAN-ONLY: measurability of the estimator, for the deviation event
    (hμhat : Measurable μhat) :
    ∃ P : Measure ℝ, IsProbabilityMeasure P ∧
      (∫ x, (x - ∫ y, y ∂P) ^ 2 ∂P = σ2) ∧
      δ ≤ (Measure.pi fun _ : Fin n => P).real
        {x | Real.sqrt σ2 * Real.sqrt (Real.log (1 / (2 * δ)) / n)
          < |μhat x - ∫ y, y ∂P|} := by
  have hδ0 : 0 < δ := lt_trans (by positivity) hδlo
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have h2δ0 : 0 < 2 * δ := by linarith
  have h2δ1 : 2 * δ < 1 := by linarith
  -- `M = log(1/(2δ))`, the honest log budget, kept opaque from here on.
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = Real.log (1 / (2 * δ)) := ⟨_, rfl⟩
  rw [← hMdef]
  have hM : 0 < M := hMdef ▸ Real.log_pos ((one_lt_div h2δ0).mpr h2δ1)
  have hexpM : Real.exp (-M) = 2 * δ := by
    rw [hMdef, one_div, Real.log_inv, neg_neg, Real.exp_log h2δ0]
  have hMn : 0 < M / (n : ℝ) := div_pos hM hn0
  -- **the contamination level**: `1 − p = (2δ)^{1/n} = e^{−M/n}`.
  obtain ⟨p, hp0, hp1, hpn, hpsep⟩ :
      ∃ p : ℝ, 0 < p ∧ p < 1 ∧ (1 - p) ^ n = 2 * δ ∧ M / (n : ℝ) < p / (1 - p) := by
    have he0 : 0 < Real.exp (-(M / n)) := Real.exp_pos _
    have he1 : Real.exp (-(M / n)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    refine ⟨1 - Real.exp (-(M / n)), by linarith, by linarith, ?_, ?_⟩
    · rw [sub_sub_cancel, ← Real.exp_nat_mul, show (n : ℝ) * -(M / n) = -M by field_simp]
      exact hexpM
    · rw [sub_sub_cancel]
      have hne : Real.exp (M / n) ≠ 0 := (Real.exp_pos _).ne'
      have hx : (1 - Real.exp (-(M / n))) / Real.exp (-(M / n)) = Real.exp (M / n) - 1 := by
        rw [Real.exp_neg]
        field_simp
      rw [hx]
      have := Real.add_one_lt_exp (ne_of_gt hMn)
      linarith
  -- **the atom**: `c = σ/√(p(1−p))`, so the variance is exactly `σ²`.
  obtain ⟨c, hc0, hcvar, hcsep⟩ :
      ∃ c : ℝ, 0 < c ∧ c ^ 2 * p * (1 - p) = σ2 ∧
        Real.sqrt σ2 * Real.sqrt (M / (n : ℝ)) < p * c := by
    have hp1' : (0 : ℝ) < 1 - p := by linarith
    have hne1p : (1 : ℝ) - p ≠ 0 := hp1'.ne'
    have hpp : 0 < p * (1 - p) := mul_pos hp0 hp1'
    have hsq : Real.sqrt (p * (1 - p)) ≠ 0 := (Real.sqrt_pos.mpr hpp).ne'
    refine ⟨Real.sqrt σ2 / Real.sqrt (p * (1 - p)),
      div_pos (Real.sqrt_pos.mpr hσ) (Real.sqrt_pos.mpr hpp), ?_, ?_⟩
    · rw [div_pow, Real.sq_sqrt hσ.le, Real.sq_sqrt hpp.le]
      field_simp
    · have h1 : Real.sqrt (p / (1 - p)) * Real.sqrt (p * (1 - p)) = p := by
        rw [← Real.sqrt_mul (div_nonneg hp0.le hp1'.le),
          show p / (1 - p) * (p * (1 - p)) = p ^ 2 by field_simp]
        exact Real.sqrt_sq hp0.le
      have h2 : p / Real.sqrt (p * (1 - p)) = Real.sqrt (p / (1 - p)) := by
        rw [div_eq_iff hsq]
        exact h1.symm
      have hfold : p * (Real.sqrt σ2 / Real.sqrt (p * (1 - p)))
          = Real.sqrt σ2 * Real.sqrt (p / (1 - p)) := by
        rw [← h2]; ring
      rw [hfold]
      exact mul_lt_mul_of_pos_left
        (Real.sqrt_lt_sqrt hMn.le hpsep) (Real.sqrt_pos.mpr hσ)
  -- the two witnesses and the coupling
  haveI hPp : IsProbabilityMeasure (twoPointPM c p) :=
    isProbabilityMeasure_twoPointPM hp0.le hp1.le
  haveI hPm : IsProbabilityMeasure (twoPointPM (-c) p) :=
    isProbabilityMeasure_twoPointPM hp0.le hp1.le
  haveI hν : IsProbabilityMeasure (twoPointCoupling c p) :=
    isProbabilityMeasure_contaminate _ _ hp0.le hp1.le
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.sqrt σ2 * Real.sqrt (M / (n : ℝ)) := ⟨_, rfl⟩
  rw [← htdef] at hcsep ⊢
  -- the two deviation events and the two coordinate projections
  -- NB there is no `Measurable.abs` in this Mathlib pin (and `.abs` dot-notation fails
  -- because `Measurable` unfolds to a `∀`, so Lean looks for `Function.abs`): compose
  -- with the continuous absolute value instead.
  have habs : ∀ a : ℝ, Measurable fun x : Fin n → ℝ => |μhat x - a| := fun _ =>
    continuous_abs.measurable.comp (hμhat.sub measurable_const)
  have hEp : MeasurableSet {x : Fin n → ℝ | t < |μhat x - p * c|} :=
    measurableSet_lt measurable_const (habs _)
  have hEm : MeasurableSet {x : Fin n → ℝ | t < |μhat x - p * -c|} :=
    measurableSet_lt measurable_const (habs _)
  have hFp : Measurable fun w : Fin n → ℝ × ℝ => fun i => (w i).1 :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst
  have hFm : Measurable fun w : Fin n → ℝ × ℝ => fun i => (w i).2 :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).snd
  -- the product pushforwards of the coupling are the two product laws
  have hmapP : (Measure.pi fun _ : Fin n => twoPointCoupling c p).map
      (fun w i => (w i).1) = Measure.pi fun _ : Fin n => twoPointPM c p := by
    haveI : IsProbabilityMeasure ((twoPointCoupling c p).map (Prod.fst : ℝ × ℝ → ℝ)) := by
      rw [twoPointCoupling_fst hp0.le hp1.le]; exact hPp
    rw [Measure.pi_map_pi (f := fun _ : Fin n => (Prod.fst : ℝ × ℝ → ℝ))
      fun _ => measurable_fst.aemeasurable]
    simp only [twoPointCoupling_fst hp0.le hp1.le]
  have hmapM : (Measure.pi fun _ : Fin n => twoPointCoupling c p).map
      (fun w i => (w i).2) = Measure.pi fun _ : Fin n => twoPointPM (-c) p := by
    haveI : IsProbabilityMeasure ((twoPointCoupling c p).map (Prod.snd : ℝ × ℝ → ℝ)) := by
      rw [twoPointCoupling_snd hp0.le hp1.le]; exact hPm
    rw [Measure.pi_map_pi (f := fun _ : Fin n => (Prod.snd : ℝ × ℝ → ℝ))
      fun _ => measurable_snd.aemeasurable]
    simp only [twoPointCoupling_snd hp0.le hp1.le]
  -- **the union bound on the agreement event**
  have hkey : 2 * δ ≤ (Measure.pi fun _ : Fin n => twoPointPM c p).real
        {x : Fin n → ℝ | t < |μhat x - p * c|}
      + (Measure.pi fun _ : Fin n => twoPointPM (-c) p).real
        {x : Fin n → ℝ | t < |μhat x - p * -c|} := by
    have hagree := twoPointCoupling_agree_pow (c := c) (p := p) hc0.ne' hp0.le hp1.le n
    rw [hpn] at hagree
    rw [← hmapP, ← hmapM, map_measureReal_apply hFp hEp, map_measureReal_apply hFm hEm,
      ← hagree]
    refine le_trans (measureReal_mono ?_) (measureReal_union_le _ _)
    intro w hw
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    simp only [Set.mem_preimage, Set.mem_setOf_eq, not_lt] at h1 h2
    have hxy : (fun i => (w i).1) = fun i => (w i).2 := funext fun i => hw i
    rw [hxy] at h1
    have h1' := abs_le.mp h1
    have h2' := abs_le.mp h2
    linarith [h1'.1, h2'.2]
  -- one of the two error probabilities is at least `δ`
  by_cases h : δ ≤ (Measure.pi fun _ : Fin n => twoPointPM c p).real
      {x : Fin n → ℝ | t < |μhat x - p * c|}
  · refine ⟨twoPointPM c p, hPp, ?_, ?_⟩
    · rw [integral_twoPointPM hp0.le hp1.le, variance_twoPointPM hp0.le hp1.le]
      exact hcvar
    · rw [integral_twoPointPM hp0.le hp1.le]
      exact h
  · rw [not_le] at h
    refine ⟨twoPointPM (-c) p, hPm, ?_, ?_⟩
    · rw [integral_twoPointPM hp0.le hp1.le, variance_twoPointPM hp0.le hp1.le, neg_sq]
      exact hcvar
    · rw [integral_twoPointPM hp0.le hp1.le]
      linarith

end StatLean.RobustStatistics
