module
public import StatLean.CausalInference.Observational.IPW

@[expose] public section

/-!
# Augmented inverse-probability weighting — the doubly robust identity

The augmented functional combines an outcome model `m̄₁` with a propensity model `ē`,

$$\tilde\mu_1^{\mathrm{dr}}
  =\mathbb E\Bigl[\bar m_1(X)+\frac{Z\{Y-\bar m_1(X)\}}{\bar e(X)}\Bigr],$$

and is **doubly robust**: it equals `E[Y(1)]` if *either* model is correct, neither needs
to be. The mechanism is the exact product-bias identity

$$\tilde\mu_1^{\mathrm{dr}}-\mathbb E[Y(1)]
  =\mathbb E\Bigl[\frac{e(X)-\bar e(X)}{\bar e(X)}\bigl\{m_1(X)-\bar m_1(X)\bigr\}\Bigr],$$

whose right-hand side is a *product* of the two model errors, so it vanishes as soon as
one factor does.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Theorem 12.1 (§12.1.1, p. 170), under
ignorability `Z ⫫ {Y(1),Y(0)} | X` and overlap `0 < e(X) < 1`, with the functionals of
eqs. (12.3)–(12.6); the product-bias identity appears inside the proof of Theorem 12.1
(p. 171) and again in §12.4 (p. 177) — it carries no number of its own.
(`Ding Theorem 12.1; §12.1, §12.4`.)

**Scope.** This is the *algebraic* double-robustness of the population functional, which
is what Ding's ch. 12 establishes. Estimation theory for the sample version (asymptotic
normality, efficiency, cross-fitting) is deliberately out of scope — it needs
semiparametric machinery beyond the two reference texts.

**Proof formalization notes.** Everything is a cell-wise computation. In cell `x` the
augmented integrand has mean
`m̄₁(x) + e(x)·(m₁(x) - m̄₁(x))/ē(x)`, and subtracting `m₁(x)` gives
`(e(x) - ē(x))·(m₁(x) - m̄₁(x))/ē(x)` after collecting terms; summing against the cell
probabilities is the identity. The two robustness corollaries then just observe that one
factor is `0`. Note that the working propensity must be bounded away from `0` on cells
that carry mass — otherwise the functional itself is undefined — which is a hypothesis on
the *working* model, separate from the true overlap condition.

**Bibliographic comments.** J. M. Robins, A. Rotnitzky and L. P. Zhao, "Estimation of
regression coefficients when some regressors are not always observed," *J. Amer. Statist.
Assoc.* **89** (1994), 846–866; the double-robustness terminology is from
J. M. Robins, "Robust estimation in sequentially ignorable missing data and causal
inference models," *Proc. Amer. Statist. Assoc.* (2000), 6–10.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}
  {ebar m1bar m0bar : 𝒳 → ℝ}

/-! ### Private toolkit

Everything below the fold is bookkeeping: rewriting the arm weights `Z` and `1 - Z` as
set indicators, integrability of the augmented integrand, and the two cell-wise means. -/

/-- Auxiliary: a conditional measure of a finite measure takes no infinite value. -/
private lemma cond_apply_ne_top' [IsFiniteMeasure μ] {c : Set Ω} (hc : MeasurableSet c)
    (t : Set Ω) : (μ[|c]) t ≠ ⊤ := by
  rcases eq_or_ne (μ c) 0 with h | h
  · simp [cond_eq_zero_of_meas_eq_zero h]
  · rw [cond_apply hc]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h) (measure_ne_top _ _)

/-- Auxiliary: integrability transfers to any conditional measure of a finite measure. -/
private lemma integrable_cond' [IsFiniteMeasure μ] {c : Set Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) : Integrable f (μ[|c]) := by
  rcases eq_or_ne (μ c) 0 with h | h
  · simp [cond_eq_zero_of_meas_eq_zero h]
  · exact (hf.integrableOn (s := c)).smul_measure (by simp [h])

/-- The treated weight is the indicator of the treated event. -/
private lemma ind_eq_indicator (Z : Ω → Bool) :
    (fun ω => ind (Z ω)) = Set.indicator {ω | Z ω = true} (1 : Ω → ℝ) := by
  funext ω; cases h : Z ω <;> simp [ind, Set.indicator, h]

/-- The control weight is the indicator of the control event. -/
private lemma one_sub_ind_eq_indicator (Z : Ω → Bool) :
    (fun ω => 1 - ind (Z ω)) = Set.indicator {ω | Z ω = false} (1 : Ω → ℝ) := by
  funext ω; cases h : Z ω <;> simp [ind, Set.indicator, h]

/-- Multiplying by the treated weight is restricting to the treated event. -/
private lemma ind_mul_eq_indicator (Z : Ω → Bool) (f : Ω → ℝ) :
    (fun ω => ind (Z ω) * f ω) = Set.indicator {ω | Z ω = true} f := by
  funext ω; cases h : Z ω <;> simp [ind, Set.indicator, h]

/-- Multiplying by the control weight is restricting to the control event. -/
private lemma one_sub_ind_mul_eq_indicator (Z : Ω → Bool) (f : Ω → ℝ) :
    (fun ω => (1 - ind (Z ω)) * f ω) = Set.indicator {ω | Z ω = false} f := by
  funext ω; cases h : Z ω <;> simp [ind, Set.indicator, h]

/-- A function of a finite covariate is bounded, hence integrable. -/
private lemma integrable_comp' [IsFiniteMeasure μ] (hX : Measurable X) (g : 𝒳 → ℝ) :
    Integrable (fun ω => g (X ω)) μ := by
  have hgm : Measurable fun ω => g (X ω) := (measurable_of_countable g).comp hX
  refine Integrable.mono' (integrable_const (∑ x : 𝒳, |g x|)) hgm.aestronglyMeasurable ?_
  filter_upwards with ω
  exact (le_of_eq (Real.norm_eq_abs _)).trans
    (Finset.single_le_sum (f := fun x => |g x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (X ω)))

/-- A bounded function of the covariate times an integrable function is integrable. -/
private lemma integrable_comp_mul' [IsFiniteMeasure μ] (hX : Measurable X) (g : 𝒳 → ℝ)
    {f : Ω → ℝ} (hf : Integrable f μ) : Integrable (fun ω => g (X ω) * f ω) μ := by
  have hgm : Measurable fun ω => g (X ω) := (measurable_of_countable g).comp hX
  refine hf.bdd_mul (c := ∑ x : 𝒳, |g x|) hgm.aestronglyMeasurable ?_
  filter_upwards with ω
  exact (le_of_eq (Real.norm_eq_abs _)).trans
    (Finset.single_le_sum (f := fun x => |g x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (X ω)))

/-- The augmented treated integrand is integrable. -/
private lemma integrable_aug [IsFiniteMeasure μ] (hZ : Measurable Z) (hX : Measurable X)
    {f : Ω → ℝ} (hf : Integrable f μ) (g w : 𝒳 → ℝ) :
    Integrable (fun ω => g (X ω) + ind (Z ω) * (f ω - g (X ω)) / w (X ω)) μ := by
  have h1 : Integrable (fun ω => g (X ω)) μ := integrable_comp' hX g
  have h2 : Integrable (fun ω => (f ω - g (X ω)) / w (X ω)) μ := by
    have hrw : (fun ω => (f ω - g (X ω)) / w (X ω))
        = fun ω => (w (X ω))⁻¹ * (f ω - g (X ω)) := by
      funext ω; rw [div_eq_inv_mul]
    rw [hrw]
    exact integrable_comp_mul' hX (fun x => (w x)⁻¹) (hf.sub h1)
  have h3 : Integrable (fun ω => ind (Z ω) * (f ω - g (X ω)) / w (X ω)) μ := by
    have hrw : (fun ω => ind (Z ω) * (f ω - g (X ω)) / w (X ω))
        = Set.indicator {ω | Z ω = true} (fun ω => (f ω - g (X ω)) / w (X ω)) := by
      funext ω; cases h : Z ω <;> simp [ind, Set.indicator, h]
    rw [hrw]
    exact h2.indicator (hZ (measurableSet_singleton true))
  exact h1.add h3

/-- The augmented control integrand is integrable. -/
private lemma integrable_augControl [IsFiniteMeasure μ] (hZ : Measurable Z) (hX : Measurable X)
    {f : Ω → ℝ} (hf : Integrable f μ) (g w : 𝒳 → ℝ) :
    Integrable (fun ω => g (X ω) + (1 - ind (Z ω)) * (f ω - g (X ω)) / (1 - w (X ω))) μ := by
  have h1 : Integrable (fun ω => g (X ω)) μ := integrable_comp' hX g
  have h2 : Integrable (fun ω => (f ω - g (X ω)) / (1 - w (X ω))) μ := by
    have hrw : (fun ω => (f ω - g (X ω)) / (1 - w (X ω)))
        = fun ω => (1 - w (X ω))⁻¹ * (f ω - g (X ω)) := by
      funext ω; rw [div_eq_inv_mul]
    rw [hrw]
    exact integrable_comp_mul' hX (fun x => (1 - w x)⁻¹) (hf.sub h1)
  have h3 : Integrable (fun ω => (1 - ind (Z ω)) * (f ω - g (X ω)) / (1 - w (X ω))) μ := by
    have hrw : (fun ω => (1 - ind (Z ω)) * (f ω - g (X ω)) / (1 - w (X ω)))
        = Set.indicator {ω | Z ω = false} (fun ω => (f ω - g (X ω)) / (1 - w (X ω))) := by
      funext ω; cases h : Z ω <;> simp [ind, Set.indicator, h]
    rw [hrw]
    exact h2.indicator (hZ (measurableSet_singleton false))
  exact h1.add h3

/-- The mass of the treated arm inside a cell is the propensity score. -/
private lemma integral_ind_cond_cell [IsFiniteMeasure μ] (hZ : Measurable Z) (hX : Measurable X)
    (x : 𝒳) : ∫ ω, ind (Z ω) ∂(μ[|cell X x]) = propensity μ Z X x := by
  have ht : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  rw [ind_eq_indicator, integral_indicator_one ht, measureReal_def]
  rfl

/-- The mass of the control arm inside a cell of positive mass. -/
private lemma integral_one_sub_ind_cond_cell [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hX : Measurable X) {x : 𝒳} (hcell : μ (cell X x) ≠ 0) :
    ∫ ω, (1 - ind (Z ω)) ∂(μ[|cell X x]) = 1 - propensity μ Z X x := by
  have hfl : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  rw [one_sub_ind_eq_indicator, integral_indicator_one hfl, measureReal_def]
  have hadd := cond_treated_add_cond_control (μ := μ) hX hZ hcell
  have hp : propensity μ Z X x = ((μ[|X ⁻¹' {x}]) {ω | Z ω = true}).toReal := rfl
  have h2 : ((μ[|cell X x]) {ω | Z ω = false}).toReal
      = ((μ[|X ⁻¹' {x}]) {ω | Z ω = false}).toReal := rfl
  rw [hp, h2]
  linarith

/-- The treated-arm partial mean inside a cell: the arm mass times the arm regression. -/
private lemma integral_ind_mul_cond_cell [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hZ : Measurable Z) (hX : Measurable X) (hf : Integrable f μ) (x : 𝒳) :
    ∫ ω, ind (Z ω) * f ω ∂(μ[|cell X x])
      = propensity μ Z X x * cellMean μ Z X f true x := by
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  have ht : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  rw [ind_mul_eq_indicator, integral_indicator ht,
    ← measureReal_mul_integral_cond (cond_apply_ne_top' hc _) f,
    cond_cond_eq_cond_inter' hc ht (measure_ne_top μ _), Set.inter_comm]
  rfl

/-- The control-arm partial mean inside a cell of positive mass. -/
private lemma integral_one_sub_ind_mul_cond_cell [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hZ : Measurable Z) (hX : Measurable X) (hf : Integrable f μ) {x : 𝒳}
    (hcell : μ (cell X x) ≠ 0) :
    ∫ ω, (1 - ind (Z ω)) * f ω ∂(μ[|cell X x])
      = (1 - propensity μ Z X x) * cellMean μ Z X f false x := by
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  have hfl : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  have hmass : ((μ[|cell X x]) {ω | Z ω = false}).toReal = 1 - propensity μ Z X x := by
    have hadd := cond_treated_add_cond_control (μ := μ) hX hZ hcell
    have hp : propensity μ Z X x = ((μ[|X ⁻¹' {x}]) {ω | Z ω = true}).toReal := rfl
    have h2 : ((μ[|cell X x]) {ω | Z ω = false}).toReal
        = ((μ[|X ⁻¹' {x}]) {ω | Z ω = false}).toReal := rfl
    rw [hp, h2]
    linarith
  rw [one_sub_ind_mul_eq_indicator, integral_indicator hfl,
    ← measureReal_mul_integral_cond (cond_apply_ne_top' hc _) f,
    cond_cond_eq_cond_inter' hc hfl (measure_ne_top μ _), Set.inter_comm, hmass]
  rfl

/-- The cell-wise mean of a general augmented treated integrand. -/
private lemma integral_cond_cell_aug [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hZ : Measurable Z) (hX : Measurable X) (hf : Integrable f μ) (g w : 𝒳 → ℝ) {x : 𝒳}
    (hcell : μ (cell X x) ≠ 0) :
    ∫ ω, (g (X ω) + ind (Z ω) * (f ω - g (X ω)) / w (X ω)) ∂(μ[|cell X x])
      = g x + propensity μ Z X x * (cellMean μ Z X f true x - g x) / w x := by
  haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure hcell
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  have ht : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  have hfc : Integrable f (μ[|cell X x]) := integrable_cond' hf
  have hI1 : Integrable (fun ω => ind (Z ω) * f ω) (μ[|cell X x]) := by
    rw [ind_mul_eq_indicator]; exact hfc.indicator ht
  have hI2 : Integrable (fun ω => ind (Z ω)) (μ[|cell X x]) := by
    rw [ind_eq_indicator]; exact (integrable_const (1 : ℝ)).indicator ht
  have hcongr : ∫ ω, (g (X ω) + ind (Z ω) * (f ω - g (X ω)) / w (X ω)) ∂(μ[|cell X x])
      = ∫ ω, (g x + ((w x)⁻¹ * (ind (Z ω) * f ω) - (g x * (w x)⁻¹) * ind (Z ω)))
          ∂(μ[|cell X x]) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_cond_mem hc] with ω hω
    have hXω : X ω = x := hω
    rw [hXω]; ring
  have e1 : ∫ ω, (g x + ((w x)⁻¹ * (ind (Z ω) * f ω) - (g x * (w x)⁻¹) * ind (Z ω)))
        ∂(μ[|cell X x])
      = (∫ _ω, g x ∂(μ[|cell X x]))
        + ∫ ω, ((w x)⁻¹ * (ind (Z ω) * f ω) - (g x * (w x)⁻¹) * ind (Z ω)) ∂(μ[|cell X x]) :=
    integral_add (integrable_const _) ((hI1.const_mul _).sub (hI2.const_mul _))
  have e2 : ∫ ω, ((w x)⁻¹ * (ind (Z ω) * f ω) - (g x * (w x)⁻¹) * ind (Z ω)) ∂(μ[|cell X x])
      = (∫ ω, (w x)⁻¹ * (ind (Z ω) * f ω) ∂(μ[|cell X x]))
        - ∫ ω, (g x * (w x)⁻¹) * ind (Z ω) ∂(μ[|cell X x]) :=
    integral_sub (hI1.const_mul _) (hI2.const_mul _)
  have e3 : ∫ ω, (w x)⁻¹ * (ind (Z ω) * f ω) ∂(μ[|cell X x])
      = (w x)⁻¹ * ∫ ω, ind (Z ω) * f ω ∂(μ[|cell X x]) := integral_const_mul _ _
  have e4 : ∫ ω, (g x * (w x)⁻¹) * ind (Z ω) ∂(μ[|cell X x])
      = (g x * (w x)⁻¹) * ∫ ω, ind (Z ω) ∂(μ[|cell X x]) := integral_const_mul _ _
  rw [hcongr, e1, e2, e3, e4, integral_ind_mul_cond_cell hZ hX hf x,
    integral_ind_cond_cell hZ hX x]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The cell-wise mean of a general augmented control integrand. -/
private lemma integral_cond_cell_augControl [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hZ : Measurable Z) (hX : Measurable X) (hf : Integrable f μ) (g w : 𝒳 → ℝ) {x : 𝒳}
    (hcell : μ (cell X x) ≠ 0) :
    ∫ ω, (g (X ω) + (1 - ind (Z ω)) * (f ω - g (X ω)) / (1 - w (X ω))) ∂(μ[|cell X x])
      = g x + (1 - propensity μ Z X x) * (cellMean μ Z X f false x - g x) / (1 - w x) := by
  haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure hcell
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  have hfl : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  have hfc : Integrable f (μ[|cell X x]) := integrable_cond' hf
  have hI1 : Integrable (fun ω => (1 - ind (Z ω)) * f ω) (μ[|cell X x]) := by
    rw [one_sub_ind_mul_eq_indicator]; exact hfc.indicator hfl
  have hI2 : Integrable (fun ω => 1 - ind (Z ω)) (μ[|cell X x]) := by
    rw [one_sub_ind_eq_indicator]; exact (integrable_const (1 : ℝ)).indicator hfl
  have hcongr : ∫ ω, (g (X ω) + (1 - ind (Z ω)) * (f ω - g (X ω)) / (1 - w (X ω)))
        ∂(μ[|cell X x])
      = ∫ ω, (g x + ((1 - w x)⁻¹ * ((1 - ind (Z ω)) * f ω)
          - (g x * (1 - w x)⁻¹) * (1 - ind (Z ω)))) ∂(μ[|cell X x]) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_cond_mem hc] with ω hω
    have hXω : X ω = x := hω
    rw [hXω]; ring
  have e1 : ∫ ω, (g x + ((1 - w x)⁻¹ * ((1 - ind (Z ω)) * f ω)
          - (g x * (1 - w x)⁻¹) * (1 - ind (Z ω)))) ∂(μ[|cell X x])
      = (∫ _ω, g x ∂(μ[|cell X x]))
        + ∫ ω, ((1 - w x)⁻¹ * ((1 - ind (Z ω)) * f ω)
            - (g x * (1 - w x)⁻¹) * (1 - ind (Z ω))) ∂(μ[|cell X x]) :=
    integral_add (integrable_const _) ((hI1.const_mul _).sub (hI2.const_mul _))
  have e2 : ∫ ω, ((1 - w x)⁻¹ * ((1 - ind (Z ω)) * f ω)
          - (g x * (1 - w x)⁻¹) * (1 - ind (Z ω))) ∂(μ[|cell X x])
      = (∫ ω, (1 - w x)⁻¹ * ((1 - ind (Z ω)) * f ω) ∂(μ[|cell X x]))
        - ∫ ω, (g x * (1 - w x)⁻¹) * (1 - ind (Z ω)) ∂(μ[|cell X x]) :=
    integral_sub (hI1.const_mul _) (hI2.const_mul _)
  have e3 : ∫ ω, (1 - w x)⁻¹ * ((1 - ind (Z ω)) * f ω) ∂(μ[|cell X x])
      = (1 - w x)⁻¹ * ∫ ω, (1 - ind (Z ω)) * f ω ∂(μ[|cell X x]) := integral_const_mul _ _
  have e4 : ∫ ω, (g x * (1 - w x)⁻¹) * (1 - ind (Z ω)) ∂(μ[|cell X x])
      = (g x * (1 - w x)⁻¹) * ∫ ω, (1 - ind (Z ω)) ∂(μ[|cell X x]) := integral_const_mul _ _
  rw [hcongr, e1, e2, e3, e4, integral_one_sub_ind_mul_cond_cell hZ hX hf hcell,
    integral_one_sub_ind_cond_cell hZ hX hcell]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The treated arm regression function of the observed outcome is that of `y1`. -/
private lemma cellMean_obs_true' [IsFiniteMeasure μ] (hZ : Measurable Z) (hX : Measurable X)
    (x : 𝒳) : cellMean μ Z X (obs Z y1 y0) true x = cellMean μ Z X y1 true x := by
  have hm : MeasurableSet (armCell Z X true x) :=
    (hZ (measurableSet_singleton true)).inter (hX (measurableSet_singleton x))
  refine integral_congr_ae ?_
  filter_upwards [ae_cond_mem (μ := μ) hm] with ω hω
  have hZω : Z ω = true := hω.1
  simp [obs, hZω]

/-- The control arm regression function of the observed outcome is that of `y0`. -/
private lemma cellMean_obs_false' [IsFiniteMeasure μ] (hZ : Measurable Z) (hX : Measurable X)
    (x : 𝒳) : cellMean μ Z X (obs Z y1 y0) false x = cellMean μ Z X y0 false x := by
  have hm : MeasurableSet (armCell Z X false x) :=
    (hZ (measurableSet_singleton false)).inter (hX (measurableSet_singleton x))
  refine integral_congr_ae ?_
  filter_upwards [ae_cond_mem (μ := μ) hm] with ω hω
  have hZω : Z ω = false := hω.1
  simp [obs, hZω]

/-- `integral_eq_sum_cell` in `cell` notation. -/
private lemma integral_eq_sum_cell' [IsFiniteMeasure μ] (hX : Measurable X) {f : Ω → ℝ}
    (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ = ∑ x : 𝒳, (μ (cell X x)).toReal * ∫ ω, f ω ∂(μ[|cell X x]) :=
  integral_eq_sum_cell hX hf

/-! ### The theorems -/

/-- The cell-wise mean of the augmented integrand for the treated arm. -/
theorem integral_cond_cell_aipwTreated [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X) (hint : Integrable (obs Z y1 y0) μ) {x : 𝒳}
    (hcell : μ (cell X x) ≠ 0)
    -- USER-INPUT: the working propensity is nonzero on this cell, else the functional is
    -- undefined; Ding §12.1 (working model, not the truth)
    (hebar : ebar x ≠ 0) :
    ∫ ω, (m1bar (X ω) + ind (Z ω) * (obs Z y1 y0 ω - m1bar (X ω)) / ebar (X ω))
        ∂(μ[|cell X x])
      = m1bar x
        + propensity μ Z X x * (cellMean μ Z X (obs Z y1 y0) true x - m1bar x) / ebar x :=
  integral_cond_cell_aug hZ hX hint m1bar ebar hcell

/-- **The product-bias identity for the treated functional** (Ding, proof of Theorem 12.1,
p. 171; §12.4): the error of the augmented functional is the covariate average of the
*product* of the propensity-model error and the outcome-model error. -/
theorem aipwTreated_sub_integral_y1_eq [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap for the true propensity; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ)
    -- USER-INPUT: the working propensity never vanishes; Ding §12.1
    (hebar : ∀ x, ebar x ≠ 0) :
    aipwTreated μ Z X (obs Z y1 y0) ebar m1bar - ∫ ω, y1 ω ∂μ
      = ∑ x : 𝒳, (μ (cell X x)).toReal
          * ((propensity μ Z X x - ebar x) / ebar x
              * (cellMean μ Z X (obs Z y1 y0) true x - m1bar x)) := by
  have hrepl : aipwTreated μ Z X (obs Z y1 y0) ebar m1bar
      = ∫ ω, (m1bar (X ω) + ind (Z ω) * (y1 ω - m1bar (X ω)) / ebar (X ω)) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    cases h : Z ω <;> simp [ind, obs, h]
  have hInt : Integrable
      (fun ω => m1bar (X ω) + ind (Z ω) * (y1 ω - m1bar (X ω)) / ebar (X ω)) μ :=
    integrable_aug hZ hX hi1 m1bar ebar
  rw [hrepl, integral_eq_sum_cell' hX hInt,
    integral_y1_eq_sum_cellMean hu hpos hy1 hy0 hZ hX hi1, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases eq_or_ne (μ (cell X x)) 0 with h0 | h0
  · simp [h0]
  · rw [integral_cond_cell_aug hZ hX hi1 m1bar ebar h0, cellMean_obs_true' hZ hX x]
    have he := hebar x
    field_simp
    ring

/-- **Double robustness of the treated functional, correct propensity branch**
(Ding Theorem 12.1(1)): if the working propensity is the truth, the augmented functional
identifies `E[Y(1)]` whatever the outcome model. -/
theorem aipwTreated_eq_of_correct_propensity [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hebar : ∀ x, ebar x ≠ 0)
    -- USER-INPUT: the propensity model is correctly specified; Ding Theorem 12.1
    (hcorrect : ∀ x, ebar x = propensity μ Z X x) :
    aipwTreated μ Z X (obs Z y1 y0) ebar m1bar = ∫ ω, y1 ω ∂μ := by
  have h := aipwTreated_sub_integral_y1_eq (m1bar := m1bar) hu hpos hy1 hy0 hZ hX hi1 hebar
  rw [Finset.sum_eq_zero fun x _ => by rw [hcorrect x, sub_self, zero_div, zero_mul,
    mul_zero]] at h
  exact sub_eq_zero.mp h

/-- **Double robustness of the treated functional, correct outcome branch**
(Ding Theorem 12.1(1)): if the working outcome model is the truth, the augmented
functional identifies `E[Y(1)]` whatever the propensity model. -/
theorem aipwTreated_eq_of_correct_outcome [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hebar : ∀ x, ebar x ≠ 0)
    -- USER-INPUT: the outcome model is correctly specified; Ding Theorem 12.1
    (hcorrect : ∀ x, μ (cell X x) ≠ 0 → m1bar x = cellMean μ Z X (obs Z y1 y0) true x) :
    aipwTreated μ Z X (obs Z y1 y0) ebar m1bar = ∫ ω, y1 ω ∂μ := by
  have h := aipwTreated_sub_integral_y1_eq (m1bar := m1bar) hu hpos hy1 hy0 hZ hX hi1 hebar
  rw [Finset.sum_eq_zero fun x _ => ?_] at h
  · exact sub_eq_zero.mp h
  rcases eq_or_ne (μ (cell X x)) 0 with h0 | h0
  · simp [h0]
  · rw [hcorrect x h0, sub_self, mul_zero, mul_zero]

/-- **Product-bias identity for the control functional** (Ding §12.4). -/
theorem aipwControl_sub_integral_y0_eq [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi0 : Integrable y0 μ)
    -- USER-INPUT: the working propensity is never one; Ding §12.1
    (hebar : ∀ x, 1 - ebar x ≠ 0) :
    aipwControl μ Z X (obs Z y1 y0) ebar m0bar - ∫ ω, y0 ω ∂μ
      = ∑ x : 𝒳, (μ (cell X x)).toReal
          * ((ebar x - propensity μ Z X x) / (1 - ebar x)
              * (cellMean μ Z X (obs Z y1 y0) false x - m0bar x)) := by
  have hrepl : aipwControl μ Z X (obs Z y1 y0) ebar m0bar
      = ∫ ω, (m0bar (X ω) + (1 - ind (Z ω)) * (y0 ω - m0bar (X ω)) / (1 - ebar (X ω))) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    cases h : Z ω <;> simp [ind, obs, h]
  have hInt : Integrable
      (fun ω => m0bar (X ω) + (1 - ind (Z ω)) * (y0 ω - m0bar (X ω)) / (1 - ebar (X ω))) μ :=
    integrable_augControl hZ hX hi0 m0bar ebar
  rw [hrepl, integral_eq_sum_cell' hX hInt,
    integral_y0_eq_sum_cellMean hu hpos hy1 hy0 hZ hX hi0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases eq_or_ne (μ (cell X x)) 0 with h0 | h0
  · simp [h0]
  · rw [integral_cond_cell_augControl hZ hX hi0 m0bar ebar h0, cellMean_obs_false' hZ hX x]
    have he := hebar x
    field_simp
    ring

/-- **The doubly robust identification theorem** (Ding Theorem 12.1(3)): if the propensity
model is correct, the augmented functional identifies the average causal effect —
regardless of the outcome models. -/
theorem aipwATE_eq_ate_of_correct_propensity [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: the propensity model is correctly specified; Ding Theorem 12.1
    (hcorrect : ∀ x, ebar x = propensity μ Z X x)
    -- USER-INPUT: the (true) propensity is never `0` or `1`, so the weights are defined
    (he0 : ∀ x, ebar x ≠ 0) (he1 : ∀ x, 1 - ebar x ≠ 0) :
    aipwATE μ Z X (obs Z y1 y0) ebar m1bar m0bar = ate μ y1 y0 := by
  have h1 : aipwTreated μ Z X (obs Z y1 y0) ebar m1bar = ∫ ω, y1 ω ∂μ :=
    aipwTreated_eq_of_correct_propensity hu hpos hy1 hy0 hZ hX hi1 he0 hcorrect
  have h0 : aipwControl μ Z X (obs Z y1 y0) ebar m0bar = ∫ ω, y0 ω ∂μ := by
    have h := aipwControl_sub_integral_y0_eq (m0bar := m0bar) hu hpos hy1 hy0 hZ hX hi0 he1
    rw [Finset.sum_eq_zero fun x _ => by rw [hcorrect x, sub_self, zero_div, zero_mul,
      mul_zero]] at h
    exact sub_eq_zero.mp h
  rw [aipwATE, h1, h0, ate, integral_sub hi1 hi0]

/-- **The doubly robust identification theorem, outcome branch** (Ding Theorem 12.1(3)):
if *both* outcome models are correct, the augmented functional identifies the average
causal effect — regardless of the propensity model. -/
theorem aipwATE_eq_ate_of_correct_outcome [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: both outcome models are correctly specified; Ding Theorem 12.1
    (hc1 : ∀ x, μ (cell X x) ≠ 0 → m1bar x = cellMean μ Z X (obs Z y1 y0) true x)
    (hc0 : ∀ x, μ (cell X x) ≠ 0 → m0bar x = cellMean μ Z X (obs Z y1 y0) false x)
    -- USER-INPUT: the working weights are defined
    (he0 : ∀ x, ebar x ≠ 0) (he1 : ∀ x, 1 - ebar x ≠ 0) :
    aipwATE μ Z X (obs Z y1 y0) ebar m1bar m0bar = ate μ y1 y0 := by
  have h1 : aipwTreated μ Z X (obs Z y1 y0) ebar m1bar = ∫ ω, y1 ω ∂μ :=
    aipwTreated_eq_of_correct_outcome hu hpos hy1 hy0 hZ hX hi1 he0 hc1
  have h0 : aipwControl μ Z X (obs Z y1 y0) ebar m0bar = ∫ ω, y0 ω ∂μ := by
    have h := aipwControl_sub_integral_y0_eq (m0bar := m0bar) hu hpos hy1 hy0 hZ hX hi0 he1
    rw [Finset.sum_eq_zero fun x _ => ?_] at h
    · exact sub_eq_zero.mp h
    rcases eq_or_ne (μ (cell X x)) 0 with hz | hz
    · simp [hz]
    · rw [hc0 x hz, sub_self, mul_zero, mul_zero]
  rw [aipwATE, h1, h0, ate, integral_sub hi1 hi0]

end StatLean.CausalInference
