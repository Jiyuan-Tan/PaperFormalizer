module
public import StatLean.CausalInference.Observational.Ignorability

@[expose] public section

/-!
# Standardization — identification of the average causal effect by outcome regression

The first identification theorem of observational causal inference. Under (mean)
ignorability and positivity, the mean potential outcome is the covariate-standardized
average of the arm regression function,

$$\mathbb E[Y(z)]=\sum_x \Pr(X=x)\,m_z(x),\qquad
  \tau=\sum_x \Pr(X=x)\,\bigl(m_1(x)-m_0(x)\bigr),$$

which is Ding's eq. (10.8) — the *g-formula* for a point treatment.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Theorem 10.1 (§10.3.1, p. 144) with its
hypotheses eqs. (10.3)–(10.4) (mean ignorability), conclusion eqs. (10.5)–(10.7), and the
discrete-covariate form eq. (10.8); Definition 10.1 (identification, p. 143); the
overlap/positivity condition of §11.2.1. (`Ding Theorem 10.1; §10.3.1; §11.2.1`.) See
also G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and
Biomedical Sciences*, Cambridge University Press, 2015, Part III. (`IR Part III`.)

**Proof formalization notes.** With a discrete covariate the proof is: decompose the
integral over covariate cells (`integral_eq_sum_cell`), replace each within-cell mean of
the potential outcome by the arm regression function
(`cellMean_true_eq_of_unconfounded`), and recombine. Positivity is what makes both arm
regression functions well defined in every cell that carries mass; on null cells both
sides contribute `0` and no hypothesis is needed. The theorem is stated under
`Unconfounded` (Ding Assumption 10.2) rather than the weaker mean-ignorability hypothesis
because the cell-mean bridge is proved from independence; a mean-ignorability version is
recorded separately as `ate_eq_sum_cellMean_of_meanIgnorable`.

**Bibliographic comments.** The formula is J. M. Robins's g-computation formula for a
point exposure, "A new approach to causal inference in mortality studies with a sustained
exposure period," *Math. Modelling* **7** (1986), 1393–1512; the standardization
terminology is standard in epidemiology.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

omit [MeasurableSpace Ω] [MeasurableSpace 𝒳] [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
/-- Auxiliary: the covariate cell is the preimage of a singleton — used to fold the
`X ⁻¹' {x}` produced by the `ForMathlib.CondAlgebra` decomposition lemmas back into
`cell`. -/
private lemma cell_eq (X : Ω → 𝒳) (x : 𝒳) : X ⁻¹' {x} = cell X x := rfl

/-- Auxiliary: integrability transfers to any conditional measure of a finite measure. -/
private lemma integrable_cond' [IsFiniteMeasure μ] {c : Set Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) : Integrable f (μ[|c]) := by
  rcases eq_or_ne (μ c) 0 with h | h
  · simp [cond_eq_zero_of_meas_eq_zero h]
  · exact (hf.integrableOn (s := c)).smul_measure (by simp [h])

omit [MeasurableSpace 𝒳] [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
/-- Auxiliary: a positive propensity says exactly that the treated arm of the cell is
non-null — the form in which `Ignorability` consumes positivity. -/
private lemma cond_treated_ne_zero {x : 𝒳} (h : 0 < propensity μ Z X x) :
    (μ[|cell X x]) (treatedEvent Z) ≠ 0 := by
  intro hm
  rw [propensity, hm] at h
  simp at h

omit [Fintype 𝒳] in
/-- Auxiliary: a propensity below one says exactly that the control arm of the cell is
non-null, the two arm probabilities inside a cell summing to one. -/
private lemma cond_control_ne_zero [IsProbabilityMeasure μ] {x : 𝒳} (hX : Measurable X)
    (hZ : Measurable Z) (hcell : μ (cell X x) ≠ 0) (h : propensity μ Z X x < 1) :
    (μ[|cell X x]) {ω | Z ω = false} ≠ 0 := by
  intro hm
  have hsum := cond_treated_add_cond_control (μ := μ) (X := X) (Z := Z) hX hZ hcell
  simp only [cell_eq] at hsum
  rw [hm, ENNReal.toReal_zero, add_zero] at hsum
  simp only [propensity, treatedEvent] at h
  linarith

/-- **Standardization identifies the treated mean** (Ding Theorem 10.1, eq. (10.5)):
`E[Y(1)] = ∑ₓ P(X = x)·m₁(x)`. -/
theorem integral_y1_eq_sum_cellMean [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1
    (hpos : Positive μ Z X)
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    -- USER-INPUT: integrable potential outcome; Ding assumes finite means
    (hint : Integrable y1 μ) :
    ∫ ω, y1 ω ∂μ
      = ∑ x : 𝒳, (μ (cell X x)).toReal * cellMean μ Z X (obs Z y1 y0) true x := by
  rw [integral_eq_sum_cell (μ := μ) hX hint]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [cell_eq]
  rcases eq_or_ne (μ (cell X x)) 0 with h | h
  · rw [h]
    simp
  · rw [cellMean_true_eq_of_unconfounded hu hy1 hy0 hZ hX hint h
      (cond_treated_ne_zero (hpos x h).1)]

/-- **Standardization identifies the control mean** (Ding Theorem 10.1, eq. (10.6)). -/
theorem integral_y0_eq_sum_cellMean [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable y0 μ) :
    ∫ ω, y0 ω ∂μ
      = ∑ x : 𝒳, (μ (cell X x)).toReal * cellMean μ Z X (obs Z y1 y0) false x := by
  rw [integral_eq_sum_cell (μ := μ) hX hint]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [cell_eq]
  rcases eq_or_ne (μ (cell X x)) 0 with h | h
  · rw [h]
    simp
  · rw [cellMean_false_eq_of_unconfounded hu hy1 hy0 hZ hX hint h
      (cond_control_ne_zero hX hZ h (hpos x h).2)]

/-- **The g-formula / standardization formula for the average causal effect**
(Ding Theorem 10.1, eqs. (10.7)–(10.8)): the average causal effect is identified by the
covariate-weighted contrast of the two arm regression functions — a functional of the
*observed-data* distribution alone. -/
theorem ate_eq_sum_cellMean_sub [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) :
    ate μ y1 y0
      = ∑ x : 𝒳, (μ (cell X x)).toReal
          * (cellMean μ Z X (obs Z y1 y0) true x - cellMean μ Z X (obs Z y1 y0) false x) := by
  rw [ate, integral_sub hi1 hi0, integral_y1_eq_sum_cellMean hu hpos hy1 hy0 hZ hX hi1,
    integral_y0_eq_sum_cellMean hu hpos hy1 hy0 hZ hX hi0, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => (mul_sub _ _ _).symm

/-- **The average causal effect is the average conditional effect** (Ding §10.3.1):
`τ = ∑ₓ P(X = x)·τ(x)`. No identification assumption is involved — this is the law of
total expectation. -/
theorem ate_eq_sum_cate [IsProbabilityMeasure μ]
    (hX : Measurable X)
    -- USER-INPUT: integrability of the individual effect
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ) :
    ate μ y1 y0 = ∑ x : 𝒳, (μ (cell X x)).toReal * cate μ X y1 y0 x := by
  simpa [ate, cate, cell] using integral_eq_sum_cell (μ := μ) hX hint

/-- **Cell-wise identification** (Ding Theorem 10.1): the conditional average causal effect
is the contrast of the arm regression functions in that cell. -/
theorem cate_eq_cellMean_sub [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) {x : 𝒳}
    -- USER-INPUT: a covariate cell of positive probability
    (hcell : μ (cell X x) ≠ 0) :
    cate μ X y1 y0 x
      = cellMean μ Z X (obs Z y1 y0) true x - cellMean μ Z X (obs Z y1 y0) false x := by
  rw [cate, integral_sub (integrable_cond' hi1) (integrable_cond' hi0),
    cellMean_true_eq_of_unconfounded hu hy1 hy0 hZ hX hi1 hcell
      (cond_treated_ne_zero (hpos x hcell).1),
    cellMean_false_eq_of_unconfounded hu hy1 hy0 hZ hX hi0 hcell
      (cond_control_ne_zero hX hZ hcell (hpos x hcell).2)]

omit [Fintype 𝒳] in
/-- Auxiliary: under mean ignorability the within-cell mean of a potential outcome is the
regression function of *either* arm — the two arm means are equal and their probabilities
sum to one. -/
private lemma integral_cond_cell_of_meanIgnorable [IsProbabilityMeasure μ] {y : Ω → ℝ}
    (hm : MeanIgnorable μ Z y X) (hZ : Measurable Z) (hX : Measurable X)
    (hi : Integrable y μ) {x : 𝒳} (hcell : μ (cell X x) ≠ 0) (z : Bool) :
    ∫ ω, y ω ∂(μ[|cell X x]) = cellMean μ Z X y z x := by
  have key : ∫ ω, y ω ∂(μ[|cell X x]) = ∫ ω, y ω ∂(μ[|armCell Z X true x]) := by
    have hsplit := integral_cond_cell_eq_arm_split (μ := μ) hX hZ hi x
    have hsum := cond_treated_add_cond_control (μ := μ) (X := X) (Z := Z) hX hZ hcell
    rw [show ({ω | Z ω = true} ∩ X ⁻¹' {x}) = armCell Z X true x from rfl,
      show ({ω | Z ω = false} ∩ X ⁻¹' {x}) = armCell Z X false x from rfl, ← hm x,
      ← add_mul, hsum, one_mul] at hsplit
    simpa only [cell_eq] using hsplit
  cases z
  · rw [cellMean, ← hm x]
    exact key
  · exact key

/-- **Standardization under mean ignorability** (Ding Theorem 10.1 with its stated
hypotheses (10.3)–(10.4)): the identification formula needs only equality of the arm
conditional means, not full independence. -/
theorem ate_eq_sum_cellMean_of_meanIgnorable [IsProbabilityMeasure μ]
    -- USER-INPUT: mean ignorability for both potential outcomes; Ding eqs. (10.3)–(10.4)
    (hm1 : MeanIgnorable μ Z y1 X) (hm0 : MeanIgnorable μ Z y0 X)
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) :
    ate μ y1 y0
      = ∑ x : 𝒳, (μ (cell X x)).toReal
          * (cellMean μ Z X (obs Z y1 y0) true x - cellMean μ Z X (obs Z y1 y0) false x) := by
  have e1 : ∀ x : 𝒳, cellMean μ Z X (obs Z y1 y0) true x = cellMean μ Z X y1 true x := by
    intro x
    rw [cellMean_obs_eq hZ hX]
    simp
  have e0 : ∀ x : 𝒳, cellMean μ Z X (obs Z y1 y0) false x = cellMean μ Z X y0 false x := by
    intro x
    rw [cellMean_obs_eq hZ hX]
    simp
  rw [ate, integral_sub hi1 hi0, integral_eq_sum_cell (μ := μ) hX hi1,
    integral_eq_sum_cell (μ := μ) hX hi0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [cell_eq, e1, e0]
  rcases eq_or_ne (μ (cell X x)) 0 with h | h
  · rw [h]
    simp
  · rw [integral_cond_cell_of_meanIgnorable hm1 hZ hX hi1 h true,
      integral_cond_cell_of_meanIgnorable hm0 hZ hX hi0 h false, mul_sub]

end StatLean.CausalInference
