module
public import StatLean.CausalInference.Observational.Standardization

@[expose] public section

/-!
# Inverse-probability weighting — identification by reweighting the observed arms

Weighting each treated unit by `1/e(X)` and each control unit by `1/(1-e(X))` recreates
the population that would have been observed had everyone been treated (resp. untreated):

$$\mathbb E[Y(1)]=\mathbb E\Bigl[\frac{ZY}{e(X)}\Bigr],\qquad
  \mathbb E[Y(0)]=\mathbb E\Bigl[\frac{(1-Z)Y}{1-e(X)}\Bigr],\qquad
  \tau=\mathbb E\Bigl[\frac{ZY}{e(X)}-\frac{(1-Z)Y}{1-e(X)}\Bigr].$$

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Theorem 11.2 (§11.2.1, p. 158), whose hypotheses
are strong ignorability `Z ⫫ {Y(1),Y(0)} | X` (Assumption 10.2) **and** overlap
`0 < e(X) < 1`; §11.2.2 (p. 160) for the Horvitz–Thompson and Hájek forms.
(`Ding Theorem 11.2; §11.2.2`.) See also G. W. Imbens and D. B. Rubin, *Causal Inference
for Statistics, Social, and Biomedical Sciences*, Cambridge University Press, 2015,
ch. 12. (`IR ch. 12`.)

**Proof formalization notes.** The route is cell-wise: decompose over covariate cells,
and inside a cell the weighted integrand is `1{Z=1}·Y/e(x)`, whose mean is
`e(x)·m₁(x)/e(x) = m₁(x)` — the weight exactly cancels the arm probability. Summing
against the cell probabilities and applying `Standardization.integral_y1_eq_sum_cellMean`
gives `E[Y(1)]`. Overlap is what makes the division legitimate on every cell that carries
mass; on null cells both sides vanish.

**Bibliographic comments.** D. G. Horvitz and D. J. Thompson, "A generalization of
sampling without replacement from a finite universe," *J. Amer. Statist. Assoc.* **47**
(1952), 663–685; the causal-inference use is due to J. M. Robins and collaborators.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-! ### Auxiliary bookkeeping -/

omit [MeasurableSpace Ω] [MeasurableSpace 𝒳] [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
/-- Auxiliary: the covariate cell is the preimage of a singleton — used to fold the
`X ⁻¹' {x}` produced by the `ForMathlib.CondAlgebra` decomposition lemmas back into
`cell`. -/
private lemma cell_eq (X : Ω → 𝒳) (x : 𝒳) : X ⁻¹' {x} = cell X x := rfl

/-- Auxiliary: a conditional measure of a finite measure takes no infinite value. -/
private lemma cond_apply_ne_top' [IsFiniteMeasure μ] {c : Set Ω} (hc : MeasurableSet c)
    (t : Set Ω) : (μ[|c]) t ≠ ⊤ := by
  rcases eq_or_ne (μ c) 0 with h | h
  · simp [cond_eq_zero_of_meas_eq_zero h]
  · rw [cond_apply hc]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h) (measure_ne_top _ _)

omit [Fintype 𝒳] in
/-- Auxiliary: inside a cell, the treated-indicator integral is the arm probability times
the treated arm regression function — conditioning twice is conditioning on the arm
cell. -/
private lemma integral_cond_cell_ind_mul [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hZ : Measurable Z) (hX : Measurable X) (x : 𝒳) :
    ∫ ω, ind (Z ω) * Y ω ∂(μ[|cell X x])
      = propensity μ Z X x * cellMean μ Z X Y true x := by
  have ht : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  have hind : (fun ω => ind (Z ω) * Y ω) = Set.indicator (treatedEvent Z) Y := by
    funext ω
    by_cases h : Z ω = true <;> simp [Set.indicator, ind, treatedEvent, h]
  rw [hind, integral_indicator ht,
    ← measureReal_mul_integral_cond (cond_apply_ne_top' hc (treatedEvent Z)) Y,
    cond_cond_eq_cond_inter' hc ht (measure_ne_top μ _), Set.inter_comm]
  rfl

omit [Fintype 𝒳] in
/-- Auxiliary: the control-arm counterpart of `integral_cond_cell_ind_mul`. -/
private lemma integral_cond_cell_ind_mul_control [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hZ : Measurable Z) (hX : Measurable X) (x : 𝒳) :
    ∫ ω, (1 - ind (Z ω)) * Y ω ∂(μ[|cell X x])
      = ((μ[|cell X x]) {ω | Z ω = false}).toReal * cellMean μ Z X Y false x := by
  have ht : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  have hind : (fun ω => (1 - ind (Z ω)) * Y ω) = Set.indicator {ω | Z ω = false} Y := by
    funext ω
    by_cases h : Z ω = true <;> simp [Set.indicator, ind, h]
  rw [hind, integral_indicator ht,
    ← measureReal_mul_integral_cond (cond_apply_ne_top' hc {ω | Z ω = false}) Y,
    cond_cond_eq_cond_inter' hc ht (measure_ne_top μ _), Set.inter_comm]
  rfl

omit [Fintype 𝒳] in
/-- Auxiliary: inside a cell of positive mass the control arm carries mass `1 - e(x)`. -/
private lemma cond_control_toReal [IsProbabilityMeasure μ] {x : 𝒳} (hZ : Measurable Z)
    (hX : Measurable X) (hcell : μ (cell X x) ≠ 0) :
    ((μ[|cell X x]) {ω | Z ω = false}).toReal = 1 - propensity μ Z X x := by
  have hsum := cond_treated_add_cond_control (μ := μ) (X := X) (Z := Z) hX hZ hcell
  simp only [cell_eq] at hsum
  simp only [propensity, treatedEvent]
  linarith

/-- Auxiliary: measurability of the observed outcome. -/
private lemma measurable_obs (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hZ : Measurable Z) : Measurable (obs Z y1 y0) := by
  unfold obs
  exact Measurable.ite (hZ (measurableSet_singleton true)) hy1 hy0

/-- Auxiliary: the propensity weight is a measurable function of `ω` — every function out
of a finite type with measurable singletons is measurable. -/
private lemma measurable_propensity_comp (hX : Measurable X) :
    Measurable (fun ω => propensity μ Z X (X ω)) :=
  (Measurable.of_discrete (f := propensity μ Z X)).comp hX

omit [MeasurableSpace Ω] in
/-- Auxiliary: the treated indicator kills the control potential outcome, so the weighted
treated integrand never sees `Y(0)` — this is why only `hi1` is needed. -/
private lemma ind_mul_obs (ω : Ω) : ind (Z ω) * obs Z y1 y0 ω = ind (Z ω) * y1 ω := by
  by_cases h : Z ω = true <;> simp [ind, obs, h]

omit [MeasurableSpace Ω] in
/-- Auxiliary: the control counterpart of `ind_mul_obs`. -/
private lemma one_sub_ind_mul_obs (ω : Ω) :
    (1 - ind (Z ω)) * obs Z y1 y0 ω = (1 - ind (Z ω)) * y0 ω := by
  by_cases h : Z ω = true <;> simp [ind, obs, h]

/-- Auxiliary: the treated arm of an integrable potential outcome is integrable. -/
private lemma integrable_ind_mul (hZ : Measurable Z) (hi1 : Integrable y1 μ) :
    Integrable (fun ω => ind (Z ω) * y1 ω) μ := by
  have h : (fun ω => ind (Z ω) * y1 ω) = Set.indicator {ω | Z ω = true} y1 := by
    funext ω
    by_cases h : Z ω = true <;> simp [Set.indicator, ind, h]
  rw [h]
  exact hi1.indicator (hZ (measurableSet_singleton true))

/-- Auxiliary: the control counterpart of `integrable_ind_mul`. -/
private lemma integrable_one_sub_ind_mul (hZ : Measurable Z) (hi0 : Integrable y0 μ) :
    Integrable (fun ω => (1 - ind (Z ω)) * y0 ω) μ := by
  have h : (fun ω => (1 - ind (Z ω)) * y0 ω) = Set.indicator {ω | Z ω = false} y0 := by
    funext ω
    by_cases h : Z ω = true <;> simp [Set.indicator, ind, h]
  rw [h]
  exact hi0.indicator (hZ (measurableSet_singleton false))

/-- Auxiliary: the inverse-probability-weighted treated integrand is integrable. No
overlap hypothesis is needed: the covariate is finite, so the weight takes finitely many
values and is dominated by the sum of their absolute values. -/
private lemma integrable_ipw_treated [IsProbabilityMeasure μ] (hy1 : Measurable y1)
    (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X) (hi1 : Integrable y1 μ) :
    Integrable (fun ω => ind (Z ω) * obs Z y1 y0 ω / propensity μ Z X (X ω)) μ := by
  have hti := integrable_ind_mul (μ := μ) (y1 := y1) hZ hi1
  refine Integrable.mono' (hti.norm.mul_const (∑ x : 𝒳, ‖(propensity μ Z X x)⁻¹‖)) ?_ ?_
  · exact ((((Measurable.of_discrete (f := ind)).comp hZ).mul
      (measurable_obs hy1 hy0 hZ)).div (measurable_propensity_comp hX)).aestronglyMeasurable
  · filter_upwards with ω
    rw [ind_mul_obs, div_eq_mul_inv, norm_mul]
    gcongr
    exact Finset.single_le_sum (f := fun x : 𝒳 => ‖(propensity μ Z X x)⁻¹‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ (X ω))

/-- Auxiliary: the control counterpart of `integrable_ipw_treated`. -/
private lemma integrable_ipw_control [IsProbabilityMeasure μ] (hy1 : Measurable y1)
    (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X) (hi0 : Integrable y0 μ) :
    Integrable
      (fun ω => (1 - ind (Z ω)) * obs Z y1 y0 ω / (1 - propensity μ Z X (X ω))) μ := by
  have hti := integrable_one_sub_ind_mul (μ := μ) (y0 := y0) hZ hi0
  refine Integrable.mono' (hti.norm.mul_const (∑ x : 𝒳, ‖(1 - propensity μ Z X x)⁻¹‖)) ?_ ?_
  · exact (((measurable_const.sub ((Measurable.of_discrete (f := ind)).comp hZ)).mul
      (measurable_obs hy1 hy0 hZ)).div
        (measurable_const.sub (measurable_propensity_comp hX))).aestronglyMeasurable
  · filter_upwards with ω
    rw [one_sub_ind_mul_obs, div_eq_mul_inv, norm_mul]
    gcongr
    exact Finset.single_le_sum (f := fun x : 𝒳 => ‖(1 - propensity μ Z X x)⁻¹‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ (X ω))

omit [Fintype 𝒳] in
/-- Auxiliary: on a cell, the weight `1/e(X ω)` may be replaced by the constant `1/e(x)`. -/
private lemma integral_cond_cell_freeze [IsProbabilityMeasure μ] {Y : Ω → ℝ} {w : 𝒳 → ℝ}
    (hX : Measurable X) (x : 𝒳) :
    ∫ ω, Y ω / w (X ω) ∂(μ[|cell X x]) = ∫ ω, Y ω / w x ∂(μ[|cell X x]) := by
  refine integral_congr_ae ?_
  filter_upwards [ae_cond_mem (hX (measurableSet_singleton x))] with ω hω
  simp only [cell, Set.mem_preimage, Set.mem_singleton_iff] at hω
  rw [hω]

/-! ### Identification -/

/-- Inside a covariate cell, the inverse-probability-weighted treated outcome has mean
equal to the treated arm regression function: the weight `1/e(x)` cancels the probability
of being treated. -/
theorem integral_cond_cell_ipw_treated [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X)
    -- USER-INPUT: integrability of the observed outcome
    (hint : Integrable (obs Z y1 y0) μ) {x : 𝒳}
    -- USER-INPUT: a covariate cell of positive probability
    (hcell : μ (cell X x) ≠ 0)
    -- USER-INPUT: positivity `e(x) > 0`; Ding §11.2.1
    (hpos : 0 < propensity μ Z X x) :
    ∫ ω, ind (Z ω) * obs Z y1 y0 ω / propensity μ Z X x ∂(μ[|cell X x])
      = cellMean μ Z X (obs Z y1 y0) true x := by
  rw [integral_div, integral_cond_cell_ind_mul hZ hX x, mul_comm, mul_div_assoc,
    div_self hpos.ne', mul_one]

/-- Inside a covariate cell, the inverse-probability-weighted control outcome has mean
equal to the control arm regression function. -/
theorem integral_cond_cell_ipw_control [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X) (hint : Integrable (obs Z y1 y0) μ) {x : 𝒳}
    (hcell : μ (cell X x) ≠ 0)
    -- USER-INPUT: positivity `e(x) < 1`; Ding §11.2.1
    (hpos : propensity μ Z X x < 1) :
    ∫ ω, (1 - ind (Z ω)) * obs Z y1 y0 ω / (1 - propensity μ Z X x) ∂(μ[|cell X x])
      = cellMean μ Z X (obs Z y1 y0) false x := by
  rw [integral_div, integral_cond_cell_ind_mul_control hZ hX x,
    cond_control_toReal hZ hX hcell, mul_comm, mul_div_assoc,
    div_self (sub_ne_zero.2 hpos.ne'), mul_one]

/-- **IPW identifies the treated mean** (Ding Theorem 11.2): `E[Y(1)] = E[ZY/e(X)]`. -/
theorem ipwTreated_eq_integral_y1 [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1
    (hpos : Positive μ Z X)
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    -- USER-INPUT: integrable potential outcome; Ding assumes finite means
    (hi1 : Integrable y1 μ) :
    ipwTreated μ Z X (obs Z y1 y0) = ∫ ω, y1 ω ∂μ := by
  rw [ipwTreated, integral_eq_sum_cell (μ := μ) hX
      (integrable_ipw_treated hy1 hy0 hZ hX hi1),
    integral_y1_eq_sum_cellMean hu hpos hy1 hy0 hZ hX hi1]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [cell_eq]
  rcases eq_or_ne (μ (cell X x)) 0 with h | h
  · rw [h]
    simp
  · rw [integral_cond_cell_freeze (μ := μ) (Y := fun ω => ind (Z ω) * obs Z y1 y0 ω)
      (w := propensity μ Z X) hX x, integral_div, integral_cond_cell_ind_mul hZ hX x,
    mul_comm (propensity μ Z X x) (cellMean μ Z X (obs Z y1 y0) true x), mul_div_assoc,
    div_self (hpos x h).1.ne', mul_one, mul_comm]

/-- **IPW identifies the control mean** (Ding Theorem 11.2):
`E[Y(0)] = E[(1-Z)Y/(1-e(X))]`. -/
theorem ipwControl_eq_integral_y0 [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi0 : Integrable y0 μ) :
    ipwControl μ Z X (obs Z y1 y0) = ∫ ω, y0 ω ∂μ := by
  rw [ipwControl, integral_eq_sum_cell (μ := μ) hX
      (integrable_ipw_control hy1 hy0 hZ hX hi0),
    integral_y0_eq_sum_cellMean hu hpos hy1 hy0 hZ hX hi0]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [cell_eq]
  rcases eq_or_ne (μ (cell X x)) 0 with h | h
  · rw [h]
    simp
  · rw [integral_cond_cell_freeze (μ := μ) (Y := fun ω => (1 - ind (Z ω)) * obs Z y1 y0 ω)
      (w := fun x => 1 - propensity μ Z X x) hX x, integral_div,
    integral_cond_cell_ind_mul_control hZ hX x, cond_control_toReal hZ hX h,
    mul_comm (1 - propensity μ Z X x) (cellMean μ Z X (obs Z y1 y0) false x),
    mul_div_assoc, div_self (sub_ne_zero.2 (hpos x h).2.ne'), mul_one, mul_comm]

/-- **IPW identifies the average causal effect** (Ding Theorem 11.2): the headline
weighting formula. -/
theorem ipwATE_eq_ate [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) :
    ipwATE μ Z X (obs Z y1 y0) = ate μ y1 y0 := by
  rw [ipwATE, ipwTreated_eq_integral_y1 hu hpos hy1 hy0 hZ hX hi1,
    ipwControl_eq_integral_y0 hu hpos hy1 hy0 hZ hX hi0, ate, integral_sub hi1 hi0]

/-- **Bounded weights under strong overlap** (Ding §11.2.3): if the propensity score stays
in `[α, 1-α]`, the treated inverse-probability weight is at most `1/α`. This is the
quantitative statement behind the practical warning that weak overlap inflates variance. -/
theorem ind_div_propensity_le [IsProbabilityMeasure μ] {α : ℝ}
    -- USER-INPUT: strong overlap `α ≤ e(X) ≤ 1 - α`; Ding §11.2.3
    (hα : 0 < α) (hover : StronglyOverlapping μ Z X α) {ω : Ω}
    -- USER-INPUT: the unit's covariate cell carries mass
    (hcell : μ (cell X (X ω)) ≠ 0) :
    ind (Z ω) / propensity μ Z X (X ω) ≤ 1 / α := by
  cases h : Z ω with
  | false =>
    rw [show ind false = 0 by simp [ind], zero_div]
    exact (one_div_pos.2 hα).le
  | true =>
    rw [show ind true = 1 by simp [ind]]
    exact one_div_le_one_div_of_le hα (hover (X ω) hcell).1

end StatLean.CausalInference
