module
public import StatLean.RobustStatistics.Core.BreakdownPoint
public import StatLean.RobustStatistics.Core.InfluenceFunction
public import StatLean.RobustStatistics.Core.Bias
public import StatLean.RobustStatistics.Core.Equivariance

@[expose] public section

/-!
# The mean — the canonical fragile location estimator

The sample mean and the mean functional `T(P) = ∫ x dP`, with the three robustness
diagnostics that all agree on their fragility (`MMY §3.1–§3.3`):

* influence function `IF(x; T, P) = x - T(P)` — unbounded in the contamination point;
* finite-sample replacement breakdown count `m* = 0` — a single replaced observation
  already drives the sample mean beyond any bound;
* maximum contamination bias `= ∞` — point-mass contamination `δ_M` with `M → ∞` moves the
  functional arbitrarily far at any fixed level `ε > 0`.

This is the negative pole of the flagship contrast; the positive pole is the median
(`LocationScale/Median.lean`, `MedianBreakdown.lean`) and the Huber M-functional
(`MEstimation/Influence.lean`).

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §3.1 (mean IF),
§3.2.5 (mean breakdown), §3.3 (maximum bias), §3.7 (the mean as a functional).

**Bibliographic comments.** The fragility of the sample mean is the founding observation of
the subject: Tukey (1960) showed minute contamination destroys its efficiency, J. L. Hodges,
Jr. quantified its zero tolerance of extreme values ("Efficiency in normal samples and
tolerance of extreme values for some estimates of location," *Proc. Fifth Berkeley Symp.
Math. Statist. Probab.*, Vol. I, Univ. California Press, 1967), and Hampel (1974) exhibited
its unbounded influence curve.
-/

open MeasureTheory

namespace StatLean.RobustStatistics

/-! ### The sample mean -/

/-- The **sample mean** `x̄ = (∑ i, x i)/n` (`MMY §2.1`, "ave"). Junk value `0` when
`n = 0`. -/
noncomputable def sampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, x i) / n

/-- The sample mean is location equivariant. -/
theorem sampleMean_locEquivariant {n : ℕ} (hn : 0 < n) :
    PointEstimation.IsLocEquivariant (sampleMean (n := n)) := by
  intro a x
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsum : ∑ i, (x + a • (1 : Fin n → ℝ)) i = (∑ i, x i) + (n : ℝ) * a := by
    simp [Finset.sum_add_distrib, mul_comm]
  change (∑ i, (x + a • (1 : Fin n → ℝ)) i) / (n : ℝ) = (∑ i, x i) / (n : ℝ) + a
  rw [hsum, add_div, mul_div_cancel_left₀ a hn']

/-- **One replacement breaks the sample mean** (`MMY §3.2.5`): a single arbitrarily
placed observation drives `x̄` beyond any bound. -/
theorem sampleMean_breaksUnder_one {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    BreaksUnder sampleMean x 1 := by
  classical
  intro M
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- replace the single observation `i₀` by the value forcing the mean to be `M + 1`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (n : ℝ) * (M + 1) - ∑ i ∈ Finset.univ \ {i₀}, x i := ⟨_, rfl⟩
  refine ⟨Function.update x i₀ C, ?_, ?_⟩
  · refine le_trans (Finset.card_le_card (t := ({i₀} : Finset (Fin n))) fun i hi => ?_)
      (by simp)
    have hne : i ∈ ({i₀} : Finset (Fin n)) ∨ i ≠ i₀ := by
      by_cases h : i = i₀
      · exact Or.inl (by simp [h])
      · exact Or.inr h
    rcases hne with h | h
    · exact h
    · exact absurd (Function.update_of_ne h C x).symm (by simpa using (Finset.mem_filter.mp hi).2)
  · have hsum : ∑ i, Function.update x i₀ C i = C + ∑ i ∈ Finset.univ \ {i₀}, x i :=
      Finset.sum_update_of_mem (Finset.mem_univ i₀) x C
    have hmean : sampleMean (Function.update x i₀ C) = M + 1 := by
      change (∑ i, Function.update x i₀ C i) / (n : ℝ) = M + 1
      rw [hsum, hC]
      field_simp
      ring
    rw [hmean]
    exact lt_of_lt_of_le (by linarith) (le_abs_self (M + 1))

/-- **The sample mean has breakdown count `0`** (`MMY §3.2.5`): `m*(x̄) = 0`, hence
`ε*_n(x̄) = 0`. -/
theorem sampleMean_breakdownCount {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    breakdownCount sampleMean x = 0 :=
  breakdownCount_eq_zero_of_breaksUnder_one (sampleMean_breaksUnder_one hn x)

/-! ### The mean functional -/

/-- The **mean functional** `T(P) = ∫ x dP` (`MMY §3.7`). Junk value `0` on
non-integrable input (Bochner-integral convention). -/
noncomputable def meanFunctional (P : Measure ℝ) : ℝ :=
  ∫ x, x ∂P

/-- The mean of an `ε`-mixture is the convex combination of the means. -/
theorem meanFunctional_contaminate {P Q : Measure ℝ} {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    -- USER-INPUT: both mixture components have a well-defined mean; MMY §3.7
    (hP : Integrable id P) (hQ : Integrable id Q) :
    meanFunctional (contaminate P Q ε) = (1 - ε) * meanFunctional P + ε * meanFunctional Q :=
  integral_contaminate h0 h1 hP hQ

/-- Point-mass contamination of the mean: `T((1-ε)P + εδ_{x₀}) = (1-ε)T(P) + ε x₀`
(`MMY §3.1`, the curve differentiated by the influence function). -/
theorem meanFunctional_contaminate_dirac {P : Measure ℝ} {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    -- USER-INPUT: P has a well-defined mean; MMY §3.7
    (hP : Integrable id P) (x₀ : ℝ) :
    meanFunctional (contaminate P (Measure.dirac x₀) ε) = (1 - ε) * meanFunctional P + ε * x₀ :=
  integral_contaminate_dirac h0 h1 hP x₀

/-- **The influence function of the mean** (`MMY §3.1`): `IF(x₀; T, P) = x₀ - T(P)`. -/
theorem meanFunctional_hasInfluenceAt {P : Measure ℝ}
    -- USER-INPUT: P has a well-defined mean; MMY §3.1
    (hP : Integrable id P) (x₀ : ℝ) :
    HasInfluenceAt meanFunctional P x₀ (x₀ - meanFunctional P) := by
  -- for `0 < t ≤ 1` the difference quotient is *exactly* `x₀ - T(P)`
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht.1
  rw [meanFunctional_contaminate_dirac ht.1.le ht.2.le hP x₀]
  field_simp
  ring

/-- The full influence function of the mean: `x ↦ x - T(P)`. -/
theorem meanFunctional_isInfluenceFunction {P : Measure ℝ} (hP : Integrable id P) :
    IsInfluenceFunction meanFunctional P (fun x => x - meanFunctional P) := fun x₀ =>
  meanFunctional_hasInfluenceAt hP x₀

/-- **The influence function of the mean is unbounded** (`MMY §3.1`): no constant bounds
`|x₀ - T(P)|` over all contamination points `x₀ ∈ ℝ`. -/
theorem meanFunctional_influence_unbounded (P : Measure ℝ) :
    ∀ c : ℝ, ∃ x₀ : ℝ, c < |x₀ - meanFunctional P| := by
  intro c
  refine ⟨meanFunctional P + (|c| + 1), ?_⟩
  have hrw : meanFunctional P + (|c| + 1) - meanFunctional P = |c| + 1 := by ring
  rw [hrw, abs_of_nonneg (by positivity)]
  linarith [le_abs_self c]

/-- The mean functional is location equivariant on integrable probability measures. -/
theorem meanFunctional_locationEquivariantOn :
    IsLocationEquivariantOn meanFunctional
      {P | IsProbabilityMeasure P ∧ Integrable id P} := by
  rintro P ⟨hPp, hPi⟩ a
  haveI := hPp
  have hPi' : Integrable (fun x : ℝ => x) P := hPi
  have hmeas : Measurable (fun x : ℝ => x + a) := measurable_id.add_const a
  have h1 : ∫ y : ℝ, y ∂(P.map (fun x : ℝ => x + a)) = ∫ x : ℝ, (x + a) ∂P :=
    integral_map hmeas.aemeasurable measurable_id.aestronglyMeasurable
  have h2 : ∫ x : ℝ, (x + a) ∂P = (∫ x : ℝ, x ∂P) + a := by
    have h := integral_add hPi' (integrable_const a : Integrable (fun _ : ℝ => a) P)
    simpa using h
  change ∫ y : ℝ, y ∂(P.map (fun x : ℝ => x + a)) = (∫ x : ℝ, x ∂P) + a
  rw [h1, h2]

/-- **The maximum contamination bias of the mean is infinite** (`MMY §3.3`): at any level
`ε ∈ (0,1]`, no finite bound dominates the bias over all contaminating distributions —
contaminate with `δ_M` and let `M → ∞`. -/
theorem meanFunctional_bias_unbounded {P : Measure ℝ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    -- USER-INPUT: P has a well-defined mean; MMY §3.3
    (hP : Integrable id P) :
    ∀ b : ℝ, ¬ContaminationBiasLE meanFunctional P ε b := by
  intro b hb
  have hεne : ε ≠ 0 := ne_of_gt hε
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ = meanFunctional P + (|b| + 1) / ε := ⟨_, rfl⟩
  have h := hb (Measure.dirac x₀) inferInstance
  rw [meanFunctional_contaminate_dirac hε.le hε1 hP x₀] at h
  have hcalc : (1 - ε) * meanFunctional P + ε * x₀ - meanFunctional P = |b| + 1 := by
    rw [hx₀]; field_simp; ring
  rw [hcalc, abs_of_nonneg (by positivity)] at h
  linarith [le_abs_self b]

end StatLean.RobustStatistics
