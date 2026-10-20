module
public import StatLean.HypothesisTesting.GoodnessOfFit.KSConsistency

@[expose] public section

/-!
# The Kolmogorov–Smirnov test has no power at `o(n^{-1/2})`

The companion of the uniform consistency theorem. The Kolmogorov–Smirnov test detects
alternatives at Kolmogorov distance `≫ n^{-1/2}` from the null with power tending to one;
in the opposite direction it is *powerless* against alternatives approaching the null
faster than `n^{-1/2}`:
$$ n^{1/2} d_K(F_n, F_0) \to 0
   \quad\Longrightarrow\quad
   \limsup_n\; P_{F_n}\{T_n > s_\alpha\} \;\le\; \alpha . $$
Thus the test cannot distinguish sequences at distance `o(n^{-1/2})` from `F₀`, the
distance being measured in the Kolmogorov metric.

Contents:

* `ks_local_power_le` — the general bound against `n^{1/2} d_K(Fₙ, F₀) → δ`;
* `ks_no_local_power` — the headline: `δ = 0` gives limiting power at most `α`.

**Calibration note (documented deviation, and a simplification).** As in
`KSConsistency.lean` the critical value is the DKW-calibrated constant `ksThreshold α`
rather than the `1 − α` quantile of the null law of `Tₙ`, so no appeal to the Kolmogorov
limit law is made. Under this calibration the conclusion becomes **easier, and carries no
constant slack at all**. The triangle inequality
`d_K(F̂ₙ, F₀) ≤ d_K(F̂ₙ, Fₙ) + d_K(Fₙ, F₀)` gives
$$ P\{T_n > s\} \;\le\; P\bigl\{n^{1/2} d_K(\hat F_n, F_n) > s - \delta_n\bigr\},
   \qquad \delta_n := n^{1/2} d_K(F_n, F_0), $$
and the sibling brick `ForMathlib/DKWUniform` bounds the right-hand side by
`4 exp(−(s − δₙ)²/16)`. Letting `δₙ → δ` and using the *definition* of `ksThreshold` — the
value at which `4 exp(−s²/16)` equals `α` — the `δ = 0` limit is exactly `α`, not `α` up to
a constant. In other words, with this calibration the level bound of `ks_dkw_level` and
the local-power bound of `ks_no_local_power` are the *same* inequality evaluated at two
ends of a limit, and the classical route (an upper bound `2 exp[−2(s_{1−α} − δ)²]` obtained
from the limit law plus a separate deviation step) is not needed. The general-`δ`
statement below is the calibrated analogue of that classical bound, and reduces to it when
the brick's constants are sharpened to `2` and `2`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 16 (Testing Goodness of
Fit), §16.2 (The Kolmogorov–Smirnov Test), Theorem 16.2.3 (the Kolmogorov–Smirnov test has no
power against alternatives at distance `o(n^{-1/2})`). (`TSH4 §16.2 Thm 16.2.3`.)

**Proof formalization notes.**
* Powers are real numbers in `[0,1]` (`ENNReal.toReal` of the rejection probability), so
  the real `Filter.limsup` is the faithful reading of the classical `lim sup`.
* The alternatives form a triangular array: each stage carries its own sampling law
  `μ n`, its own c.d.f. `F n` and its own sample `X n` of size `n`, exactly as in
  `ks_uniform_power`.
* Both proofs go through `ksStat_eq_sqrt_mul_ksDist`, the single bridge to the deviation
  brick; no continuity of the null c.d.f. is assumed, see `KSConsistency.lean`.

**Bibliographic comments.** The statistic and its limit law are due to A. N. Kolmogorov
("Sulla determinazione empirica di una legge di distribuzione," *Giornale dell'Istituto
Italiano degli Attuari* **4** (1933), 83–91) and N. V. Smirnov ("Table for estimating the
goodness of fit of empirical distributions," *Ann. Math. Statist.* **19** (1948),
279–281). The deviation inequality behind the calibration and behind both bounds below is
due to A. Dvoretzky, J. Kiefer and J. Wolfowitz (*Ann. Math. Statist.* **27** (1956),
642–669), sharpened by P. Massart (*Ann. Probab.* **18** (1990), 1269–1283).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Limiting power against `n^{1/2} d_K(Fₙ, F₀) → δ`.** The limiting power of the
calibrated Kolmogorov–Smirnov test against a sequence of alternatives approaching the null
at rate `δ / n^{1/2}` is at most `4 exp(−(s − δ)²/16)`, where `s = ksThreshold α`.

This is the calibrated analogue of the classical bound `2 exp[−2(s_{1−α} − δ)²]`, obtained
from the triangle inequality plus the uniform deviation brick. The hypothesis
`δ < ksThreshold α` is the classical `δ < s_{1−α}`: below that threshold the bound is
informative, above it, trivial. -/
theorem ks_local_power_le {α δ : ℝ} {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → ℝ} {μ : ℕ → Measure ℝ} [∀ n, IsProbabilityMeasure (μ n)]
    {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀] {F : ℕ → ℝ → ℝ} {F₀ : ℝ → ℝ}
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the observations are i.i.d.; Kolmogorov 1933
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at stage `n` every observation has law `μ n`
    (hlaw : ∀ n, ∀ i, (P n).map (X n i) = μ n)
    -- USER-INPUT: `F n` is the c.d.f. of the stage-`n` sampling law
    (hF : ∀ n, ∀ t : ℝ, F n t = cdf (μ n) t)
    -- USER-INPUT: `F₀` is the c.d.f. of the null law
    (hF₀ : ∀ t : ℝ, F₀ t = cdf μ₀ t)
    -- USER-INPUT: the alternatives approach the null at the rate `δ / n^{1/2}`
    (hrate : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * supCDFDist (F n) F₀) atTop (nhds δ))
    -- USER-INPUT: the approach rate is below the critical value (classical `δ < s_{1−α}`)
    (hδ : δ < ksThreshold α) :
    limsup (fun n => ((P n) {ω | ksThreshold α < ksStat (X n) F₀ ω}).toReal) atTop
      ≤ 4 * Real.exp (-((ksThreshold α - δ) ^ 2) / 16) := by
  set s := ksThreshold α with hs
  set dseq := fun n : ℕ => Real.sqrt (n : ℝ) * supCDFDist (F n) F₀ with hdseq
  have hsd : Tendsto (fun n => s - dseq n) atTop (nhds (s - δ)) := tendsto_const_nhds.sub hrate
  have hb : Tendsto (fun n => 4 * Real.exp (-((s - dseq n) ^ 2) / 16)) atTop
      (nhds (4 * Real.exp (-((s - δ) ^ 2) / 16))) := by
    have harg : Tendsto (fun n => -((s - dseq n) ^ 2) / 16) atTop
        (nhds (-((s - δ) ^ 2) / 16)) := ((hsd.pow 2).neg).div_const 16
    have hexp : Tendsto (fun n => Real.exp (-((s - dseq n) ^ 2) / 16)) atTop
        (nhds (Real.exp (-((s - δ) ^ 2) / 16))) := (Real.continuous_exp.tendsto _).comp harg
    exact hexp.const_mul 4
  have hev : (fun n => ((P n) {ω | s < ksStat (X n) F₀ ω}).toReal)
      ≤ᶠ[atTop] (fun n => 4 * Real.exp (-((s - dseq n) ^ 2) / 16)) := by
    filter_upwards [hrate.eventually (eventually_lt_nhds hδ), eventually_ge_atTop 1]
      with n hlt hn1
    have hn : 0 < n := hn1
    have hd0 : 0 ≤ s - dseq n := by linarith
    have hFnIcc : ∀ t, F n t ∈ Set.Icc (0 : ℝ) 1 := fun t => by
      rw [hF n t]; exact ⟨cdf_nonneg (μ n) t, cdf_le_one (μ n) t⟩
    have hF₀Icc : ∀ t, F₀ t ∈ Set.Icc (0 : ℝ) 1 := fun t => by
      rw [hF₀ t]; exact ⟨cdf_nonneg μ₀ t, cdf_le_one μ₀ t⟩
    have hEIcc : ∀ ω, ∀ t, empCDF (X n) ω t ∈ Set.Icc (0 : ℝ) 1 := fun ω t => by
      rw [← empiricalCDF_eq_empCDF]
      exact ⟨StatLean.MultipleTesting.empiricalCDF_nonneg (X n) t ω,
        StatLean.MultipleTesting.empiricalCDF_le_one (X n) t ω⟩
    have hsubset : {ω | s < ksStat (X n) F₀ ω}
        ⊆ {ω | s - dseq n ≤ Real.sqrt (n : ℝ) * ksDist (X n) (μ n) ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have hEval := hEIcc ω
      have htri : supCDFDist (fun t => empCDF (X n) ω t) F₀
          ≤ supCDFDist (fun t => empCDF (X n) ω t) (F n) + supCDFDist (F n) F₀ :=
        supCDFDist_triangle (bddAbove_absCDFDiff hEval hFnIcc)
          (bddAbove_absCDFDiff hFnIcc hF₀Icc)
      have hks : ksStat (X n) F₀ ω
          = Real.sqrt (n : ℝ) * supCDFDist (fun t => empCDF (X n) ω t) F₀ := by
        simp only [ksStat, supCDFDist, empiricalCDF_eq_empCDF]
      have hdist : ksDist (X n) (μ n) ω = supCDFDist (fun t => empCDF (X n) ω t) (F n) := by
        unfold ksDist supCDFDist
        exact iSup_congr fun t => by rw [hF n t]
      have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      have hchain : ksStat (X n) F₀ ω
          ≤ Real.sqrt (n : ℝ) * ksDist (X n) (μ n) ω + dseq n := by
        rw [hks, hdist, hdseq]
        calc Real.sqrt (n : ℝ) * supCDFDist (fun t => empCDF (X n) ω t) F₀
            ≤ Real.sqrt (n : ℝ) * (supCDFDist (fun t => empCDF (X n) ω t) (F n)
                + supCDFDist (F n) F₀) := mul_le_mul_of_nonneg_left htri hsqrt_nonneg
          _ = Real.sqrt (n : ℝ) * supCDFDist (fun t => empCDF (X n) ω t) (F n)
                + Real.sqrt (n : ℝ) * supCDFDist (F n) F₀ := by rw [mul_add]
      linarith
    have hdkw := dkw_uniform hn (μ n) (X n) (hX n) (hindep n) (hlaw n) hd0
    calc ((P n) {ω | s < ksStat (X n) F₀ ω}).toReal
        ≤ ((P n) {ω | s - dseq n ≤ Real.sqrt (n : ℝ) * ksDist (X n) (μ n) ω}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
      _ ≤ (ENNReal.ofReal (4 * Real.exp (-((s - dseq n) ^ 2) / 16))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hdkw
      _ = 4 * Real.exp (-((s - dseq n) ^ 2) / 16) := ENNReal.toReal_ofReal (by positivity)
  have hbelow : IsBoundedUnder (· ≥ ·) atTop
      (fun n => ((P n) {ω | s < ksStat (X n) F₀ ω}).toReal) :=
    ⟨0, Filter.eventually_map.mpr (Eventually.of_forall fun n => ENNReal.toReal_nonneg)⟩
  calc limsup (fun n => ((P n) {ω | s < ksStat (X n) F₀ ω}).toReal) atTop
      ≤ limsup (fun n => 4 * Real.exp (-((s - dseq n) ^ 2) / 16)) atTop :=
        limsup_le_limsup hev hbelow.isCoboundedUnder_le hb.isBoundedUnder_le
    _ = 4 * Real.exp (-((s - δ) ^ 2) / 16) := hb.limsup_eq

/-- **No power against `o(n^{-1/2})` alternatives.** For testing `F = F₀` at level `α`,
the limiting power of the calibrated Kolmogorov–Smirnov test is no better than `α` against
any sequence of alternatives `Fₙ` with `n^{1/2} d_K(Fₙ, F₀) → 0`.

The `δ = 0` case of `ks_local_power_le`: by the definition of `ksThreshold α` the bound
`4 exp(−(ksThreshold α)²/16)` *is* `α`, so the conclusion holds with no constant slack. -/
theorem ks_no_local_power {α : ℝ} {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → ℝ} {μ : ℕ → Measure ℝ} [∀ n, IsProbabilityMeasure (μ n)]
    {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀] {F : ℕ → ℝ → ℝ} {F₀ : ℝ → ℝ}
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the observations are i.i.d.; Kolmogorov 1933
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at stage `n` every observation has law `μ n`
    (hlaw : ∀ n, ∀ i, (P n).map (X n i) = μ n)
    -- USER-INPUT: `F n` is the c.d.f. of the stage-`n` sampling law
    (hF : ∀ n, ∀ t : ℝ, F n t = cdf (μ n) t)
    -- USER-INPUT: `F₀` is the c.d.f. of the null law
    (hF₀ : ∀ t : ℝ, F₀ t = cdf μ₀ t)
    -- USER-INPUT: the alternatives approach the null faster than `n^{-1/2}`
    (hrate : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * supCDFDist (F n) F₀) atTop (nhds 0)) :
    limsup (fun n => ((P n) {ω | ksThreshold α < ksStat (X n) F₀ ω}).toReal) atTop ≤ α := by
  have hspos : 0 < ksThreshold α := by
    rw [ksThreshold]
    apply Real.sqrt_pos.mpr
    have h1 : 1 < 4 / α := by rw [lt_div_iff₀ hα]; linarith
    have := Real.log_pos h1
    positivity
  have hmain := ks_local_power_le hα hα1 hX hindep hlaw hF hF₀ hrate hspos
  rwa [sub_zero, dkw_envelope_threshold hα hα1] at hmain

end StatLean.HypothesisTesting
