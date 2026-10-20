module
public import StatLean.CausalInference.Observational.SelectionBias

@[expose] public section

/-!
# Manski-type worst-case bounds — what the data alone can say

Without any identification assumption the average causal effect is *not* identified, but it
is not arbitrary either: if the outcome is known to lie in `[lo, hi]`, then filling in the
missing potential outcomes with their extreme values gives sharp bounds. Writing
`p = P(Z = 1)`,

$$\tau\ \in\
 \bigl[\,p\,\mathbb E[Y\mid Z{=}1]+(1-p)\,\mathrm{lo}
        -p\,\mathrm{hi}-(1-p)\,\mathbb E[Y\mid Z{=}0],\
        p\,\mathbb E[Y\mid Z{=}1]+(1-p)\,\mathrm{hi}
        -p\,\mathrm{lo}-(1-p)\,\mathbb E[Y\mid Z{=}0]\,\bigr],$$

an interval of width exactly `hi - lo` — never empty, never a point. The interval is
**sharp**: both endpoints are attained by genuine potential-outcome laws with the same
observed-data distribution.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §18.2 (pp. 248–249: "Manski-type worst-case bounds
on the average causal effect without assumptions", where the bounds are derived as
unnumbered displays and the width is observed to be exactly `ȳ - y̲`);
Definition 18.1 (p. 249: partial identification). (`Ding §18.2; Definition 18.1`.)
Sensitivity analysis and bounds are ch. 22 of G. W. Imbens and D. B. Rubin, *Causal
Inference for Statistics, Social, and Biomedical Sciences*, Cambridge University Press,
2015. (`IR ch. 22`.)

**Scope.** Sharpness is **not** stated in either reference (it goes back to Manski's own
work); it is proved here anyway, in the natural form: the extreme values are *attained*, by
exhibiting potential outcomes that agree with the given ones on the observed arm and take
the extreme value on the unobserved arm. That is the honest content of "sharp" for this
bound, and it needs no additional theory.

**Proof formalization notes.** The whole file rests on the decomposition
`E[Y(1)] = p·E[Y|Z=1] + (1-p)·E[Y(1)|Z=0]` (`SelectionBias`-style two-arm split), in which
only the second summand is unidentified; bounding it by `lo` and `hi` gives the interval.
The width computation is then a cancellation: the identified parts drop out and what
remains is `(1-p)(hi - lo) + p(hi - lo)`. Sharpness constructs, for the upper endpoint,
`y1' = if Z then y1 else hi` and `y0' = if Z then lo else y0`; these have the same observed
outcome function as `(y1, y0)` by construction.

**Bibliographic comments.** C. F. Manski, "Nonparametric bounds on treatment effects,"
*Amer. Econ. Rev.* **80** (1990), 319–323, and *Partial Identification of Probability
Distributions*, Springer, 2003.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ}
  {lo hi : ℝ}

/-- The **Manski lower bound** on the mean of a potential outcome: the observed arm
contributes its mean, the unobserved arm its lowest possible value (Ding §18.2). -/
noncomputable def manskiLowerY1 (μ : Measure Ω) (Z : Ω → Bool) (Y : Ω → ℝ) (lo : ℝ) : ℝ :=
  (μ (treatedEvent Z)).toReal * ∫ ω, Y ω ∂(μ[|treatedEvent Z])
    + (μ {ω | Z ω = false}).toReal * lo

/-- The **Manski upper bound** on the mean of a potential outcome (Ding §18.2). -/
noncomputable def manskiUpperY1 (μ : Measure Ω) (Z : Ω → Bool) (Y : Ω → ℝ) (hi : ℝ) : ℝ :=
  (μ (treatedEvent Z)).toReal * ∫ ω, Y ω ∂(μ[|treatedEvent Z])
    + (μ {ω | Z ω = false}).toReal * hi

/-! ### Private infrastructure

Everything below rests on one decomposition: `obs Z f g` is the sum of the indicator of the
treated arm times `f` and the indicator of the control arm times `g`, so both its
integrability and its integral split over the two arms. The arm integrals are then turned
into conditional integrals by `measureReal_mul_integral_cond`, which is valid even on a null
arm — this is what lets every statement below dispense with positivity hypotheses. -/

omit [MeasurableSpace Ω] in
private lemma obs_apply_eq_indicator_add (Z : Ω → Bool) (f g : Ω → ℝ) (ω : Ω) :
    obs Z f g ω
      = (treatedEvent Z).indicator f ω + ({ω | Z ω = false}).indicator g ω := by
  by_cases h : Z ω = true <;> simp [obs, treatedEvent, h]

/-- The observed outcome built from two integrable potential outcomes is integrable. -/
private lemma integrable_obs (hZ : Measurable Z) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) : Integrable (obs Z f g) μ := by
  have hTs : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  have hCs : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  have h : Integrable
      (fun ω => (treatedEvent Z).indicator f ω + ({ω | Z ω = false}).indicator g ω) μ :=
    (hf.indicator hTs).add (hg.indicator hCs)
  exact h.congr (Filter.Eventually.of_forall fun ω => (obs_apply_eq_indicator_add Z f g ω).symm)

/-- **Two-arm split of an `obs`-type integral**: the treated arm contributes the conditional
mean of the treated component, the control arm that of the control component. -/
private lemma integral_obs_arm_split [IsFiniteMeasure μ] (hZ : Measurable Z) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ ω, obs Z f g ω ∂μ
      = (μ (treatedEvent Z)).toReal * ∫ ω, f ω ∂(μ[|treatedEvent Z])
        + (μ {ω | Z ω = false}).toReal * ∫ ω, g ω ∂(μ[|{ω | Z ω = false}]) := by
  have hTs : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  have hCs : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  simp only [obs_apply_eq_indicator_add]
  rw [integral_add (hf.indicator hTs) (hg.indicator hCs), integral_indicator hTs,
    integral_indicator hCs, measureReal_mul_integral_cond (measure_ne_top μ _),
    measureReal_mul_integral_cond (measure_ne_top μ _)]

/-- A weighted conditional mean of a constant is that constant, weighted — including on a
null conditioning event, where both sides are `0`. -/
private lemma weighted_integral_cond_const [IsFiniteMeasure μ] (s : Set Ω) (c : ℝ) :
    (μ s).toReal * ∫ _ω, c ∂(μ[|s]) = (μ s).toReal * c := by
  rw [measureReal_mul_integral_cond (measure_ne_top μ _), setIntegral_const, measureReal_def,
    smul_eq_mul]

/-- A pointwise lower bound survives weighted conditioning, with no positivity hypothesis. -/
private lemma weighted_const_le_integral_cond [IsFiniteMeasure μ] {s : Set Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) {c : ℝ} (hc : ∀ ω, c ≤ f ω) :
    (μ s).toReal * c ≤ (μ s).toReal * ∫ ω, f ω ∂(μ[|s]) := by
  have h1 : (μ s).toReal * c = ∫ _ω in s, c ∂μ := by
    rw [setIntegral_const, measureReal_def, smul_eq_mul]
  rw [h1, measureReal_mul_integral_cond (measure_ne_top μ _)]
  exact integral_mono (integrable_const c) hf.integrableOn hc

/-- A pointwise upper bound survives weighted conditioning. -/
private lemma weighted_integral_cond_le_const [IsFiniteMeasure μ] {s : Set Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) {c : ℝ} (hc : ∀ ω, f ω ≤ c) :
    (μ s).toReal * ∫ ω, f ω ∂(μ[|s]) ≤ (μ s).toReal * c := by
  have h1 : (μ s).toReal * c = ∫ _ω in s, c ∂μ := by
    rw [setIntegral_const, measureReal_def, smul_eq_mul]
  rw [h1, measureReal_mul_integral_cond (measure_ne_top μ _)]
  exact integral_mono hf.integrableOn (integrable_const c) hc

/-- The two arm probabilities sum to one. -/
private lemma prob_treated_add_prob_control [IsProbabilityMeasure μ] (hZ : Measurable Z) :
    (μ (treatedEvent Z)).toReal + (μ {ω | Z ω = false}).toReal = 1 := by
  have hTs : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  have hcompl : {ω | Z ω = false} = (treatedEvent Z)ᶜ := by
    ext ω
    simp [treatedEvent]
  rw [hcompl, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    measure_add_measure_compl hTs]
  simp

/-- The two-arm decomposition of a potential-outcome mean: only the counterfactual arm is
unidentified. -/
theorem integral_y1_eq_arm_split [IsProbabilityMeasure μ]
    -- USER-INPUT: measurability of the treatment; user-supplied data
    (hZ : Measurable Z)
    -- USER-INPUT: integrability of the potential outcome
    (hi1 : Integrable y1 μ) :
    ∫ ω, y1 ω ∂μ
      = (μ (treatedEvent Z)).toReal * ∫ ω, y1 ω ∂(μ[|treatedEvent Z])
        + (μ {ω | Z ω = false}).toReal * ∫ ω, y1 ω ∂(μ[|{ω | Z ω = false}]) := by
  have h := integral_obs_arm_split (μ := μ) (Z := Z) hZ hi1 hi1
  rwa [show obs Z y1 y1 = y1 from funext fun ω => by simp [obs]] at h

/-- **The Manski lower bound holds** (Ding §18.2). -/
theorem manskiLowerY1_le [IsProbabilityMeasure μ] (hZ : Measurable Z) (hi1 : Integrable y1 μ)
    -- USER-INPUT: the outcome is bounded below; the only assumption Manski bounds use
    (hlo : ∀ ω, lo ≤ y1 ω) :
    manskiLowerY1 μ Z (obs Z y1 y0) lo ≤ ∫ ω, y1 ω ∂μ := by
  simp only [manskiLowerY1]
  rw [integral_cond_treated_obs_eq hZ, integral_y1_eq_arm_split hZ hi1]
  have h := weighted_const_le_integral_cond (μ := μ) (s := {ω | Z ω = false}) hi1 hlo
  linarith

/-- **The Manski upper bound holds** (Ding §18.2). -/
theorem le_manskiUpperY1 [IsProbabilityMeasure μ] (hZ : Measurable Z) (hi1 : Integrable y1 μ)
    -- USER-INPUT: the outcome is bounded above
    (hhi : ∀ ω, y1 ω ≤ hi) :
    ∫ ω, y1 ω ∂μ ≤ manskiUpperY1 μ Z (obs Z y1 y0) hi := by
  simp only [manskiUpperY1]
  rw [integral_cond_treated_obs_eq hZ, integral_y1_eq_arm_split hZ hi1]
  have h := weighted_integral_cond_le_const (μ := μ) (s := {ω | Z ω = false}) hi1 hhi
  linarith

/-- The **Manski bounds on the average causal effect** (Ding §18.2): lower endpoint. -/
noncomputable def manskiLowerATE (μ : Measure Ω) (Z : Ω → Bool) (Y : Ω → ℝ)
    (lo hi : ℝ) : ℝ :=
  manskiLowerY1 μ Z Y lo
    - ((μ (treatedEvent Z)).toReal * hi
        + (μ {ω | Z ω = false}).toReal * ∫ ω, Y ω ∂(μ[|{ω | Z ω = false}]))

/-- The **Manski bounds on the average causal effect** (Ding §18.2): upper endpoint. -/
noncomputable def manskiUpperATE (μ : Measure Ω) (Z : Ω → Bool) (Y : Ω → ℝ)
    (lo hi : ℝ) : ℝ :=
  manskiUpperY1 μ Z Y hi
    - ((μ (treatedEvent Z)).toReal * lo
        + (μ {ω | Z ω = false}).toReal * ∫ ω, Y ω ∂(μ[|{ω | Z ω = false}]))

/-- **The average causal effect lies in the Manski interval** (Ding §18.2). -/
theorem ate_mem_manski_Icc [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: both potential outcomes lie in `[lo, hi]`; the only assumption used
    (hb1 : ∀ ω, y1 ω ∈ Set.Icc lo hi) (hb0 : ∀ ω, y0 ω ∈ Set.Icc lo hi) :
    ate μ y1 y0 ∈ Set.Icc (manskiLowerATE μ Z (obs Z y1 y0) lo hi)
      (manskiUpperATE μ Z (obs Z y1 y0) lo hi) := by
  have hTs : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  -- the treated potential outcome: identified on the treated arm, bounded on the control arm
  have h1lo := manskiLowerY1_le (y0 := y0) hZ hi1 fun ω => (hb1 ω).1
  have h1hi := le_manskiUpperY1 (y0 := y0) hZ hi1 fun ω => (hb1 ω).2
  -- the control potential outcome: identified on the control arm, bounded on the treated arm
  have h0 : ∫ ω, y0 ω ∂μ
      = (μ (treatedEvent Z)).toReal * ∫ ω, y0 ω ∂(μ[|treatedEvent Z])
        + (μ {ω | Z ω = false}).toReal * ∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = false}]) := by
    rw [integral_cond_control_obs_eq hZ]
    exact integral_y1_eq_arm_split hZ hi0
  have h0lo := weighted_const_le_integral_cond (μ := μ) (s := treatedEvent Z) hi0
    fun ω => (hb0 ω).1
  have h0hi := weighted_integral_cond_le_const (μ := μ) (s := treatedEvent Z) hi0
    fun ω => (hb0 ω).2
  rw [Set.mem_Icc, ate, integral_sub hi1 hi0]
  simp only [manskiLowerATE, manskiUpperATE]
  exact ⟨by linarith, by linarith⟩

/-- **The Manski interval has width exactly `hi - lo`** (Ding §18.2): the bound never
collapses to a point, and never exceeds the a priori range — the identified parts cancel
exactly. -/
theorem manski_width [IsProbabilityMeasure μ] (hZ : Measurable Z) (Y : Ω → ℝ) :
    manskiUpperATE μ Z Y lo hi - manskiLowerATE μ Z Y lo hi = hi - lo := by
  have hsum := prob_treated_add_prob_control (μ := μ) hZ
  simp only [manskiUpperATE, manskiLowerATE, manskiUpperY1, manskiLowerY1]
  linear_combination (hi - lo) * hsum

/-- **Sharpness of the upper bound**: the upper endpoint is attained by a potential-outcome
pair with the *same observed data*, so no argument from the observed distribution alone can
improve it. -/
theorem exists_ate_eq_manskiUpper [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hb1 : ∀ ω, y1 ω ∈ Set.Icc lo hi) (hb0 : ∀ ω, y0 ω ∈ Set.Icc lo hi) :
    ∃ y1' y0' : Ω → ℝ,
      obs Z y1' y0' = obs Z y1 y0
        ∧ (∀ ω, y1' ω ∈ Set.Icc lo hi) ∧ (∀ ω, y0' ω ∈ Set.Icc lo hi)
        ∧ ate μ y1' y0' = manskiUpperATE μ Z (obs Z y1 y0) lo hi := by
  refine ⟨obs Z y1 fun _ => hi, obs Z (fun _ => lo) y0, ?_, ?_, ?_, ?_⟩
  · funext ω
    by_cases h : Z ω = true <;> simp [obs, h]
  · intro ω
    have hlohi : lo ≤ hi := (hb1 ω).1.trans (hb1 ω).2
    rw [Set.mem_Icc]
    by_cases h : Z ω = true
    · have hv : obs Z y1 (fun _ => hi) ω = y1 ω := by simp [obs, h]
      rw [hv]
      exact ⟨(hb1 ω).1, (hb1 ω).2⟩
    · have hv : obs Z y1 (fun _ => hi) ω = hi := by simp [obs, h]
      rw [hv]
      exact ⟨hlohi, le_rfl⟩
  · intro ω
    have hlohi : lo ≤ hi := (hb0 ω).1.trans (hb0 ω).2
    rw [Set.mem_Icc]
    by_cases h : Z ω = true
    · have hv : obs Z (fun _ => lo) y0 ω = lo := by simp [obs, h]
      rw [hv]
      exact ⟨le_rfl, hlohi⟩
    · have hv : obs Z (fun _ => lo) y0 ω = y0 ω := by simp [obs, h]
      rw [hv]
      exact ⟨(hb0 ω).1, (hb0 ω).2⟩
  · have hy1' : Integrable (obs Z y1 fun _ => hi) μ :=
      integrable_obs hZ hi1 (integrable_const hi)
    have hy0' : Integrable (obs Z (fun _ => lo) y0) μ :=
      integrable_obs hZ (integrable_const lo) hi0
    simp only [ate, manskiUpperATE, manskiUpperY1]
    rw [integral_sub hy1' hy0', integral_obs_arm_split hZ hi1 (integrable_const hi),
      integral_obs_arm_split hZ (integrable_const lo) hi0, weighted_integral_cond_const,
      weighted_integral_cond_const, integral_cond_treated_obs_eq hZ,
      integral_cond_control_obs_eq hZ]

/-- **Sharpness of the lower bound**. -/
theorem exists_ate_eq_manskiLower [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hb1 : ∀ ω, y1 ω ∈ Set.Icc lo hi) (hb0 : ∀ ω, y0 ω ∈ Set.Icc lo hi) :
    ∃ y1' y0' : Ω → ℝ,
      obs Z y1' y0' = obs Z y1 y0
        ∧ (∀ ω, y1' ω ∈ Set.Icc lo hi) ∧ (∀ ω, y0' ω ∈ Set.Icc lo hi)
        ∧ ate μ y1' y0' = manskiLowerATE μ Z (obs Z y1 y0) lo hi := by
  refine ⟨obs Z y1 fun _ => lo, obs Z (fun _ => hi) y0, ?_, ?_, ?_, ?_⟩
  · funext ω
    by_cases h : Z ω = true <;> simp [obs, h]
  · intro ω
    have hlohi : lo ≤ hi := (hb1 ω).1.trans (hb1 ω).2
    rw [Set.mem_Icc]
    by_cases h : Z ω = true
    · have hv : obs Z y1 (fun _ => lo) ω = y1 ω := by simp [obs, h]
      rw [hv]
      exact ⟨(hb1 ω).1, (hb1 ω).2⟩
    · have hv : obs Z y1 (fun _ => lo) ω = lo := by simp [obs, h]
      rw [hv]
      exact ⟨le_rfl, hlohi⟩
  · intro ω
    have hlohi : lo ≤ hi := (hb0 ω).1.trans (hb0 ω).2
    rw [Set.mem_Icc]
    by_cases h : Z ω = true
    · have hv : obs Z (fun _ => hi) y0 ω = hi := by simp [obs, h]
      rw [hv]
      exact ⟨hlohi, le_rfl⟩
    · have hv : obs Z (fun _ => hi) y0 ω = y0 ω := by simp [obs, h]
      rw [hv]
      exact ⟨(hb0 ω).1, (hb0 ω).2⟩
  · have hy1' : Integrable (obs Z y1 fun _ => lo) μ :=
      integrable_obs hZ hi1 (integrable_const lo)
    have hy0' : Integrable (obs Z (fun _ => hi) y0) μ :=
      integrable_obs hZ (integrable_const hi) hi0
    simp only [ate, manskiLowerATE, manskiLowerY1]
    rw [integral_sub hy1' hy0', integral_obs_arm_split hZ hi1 (integrable_const lo),
      integral_obs_arm_split hZ (integrable_const hi) hi0, weighted_integral_cond_const,
      weighted_integral_cond_const, integral_cond_treated_obs_eq hZ,
      integral_cond_control_obs_eq hZ]

end StatLean.CausalInference
