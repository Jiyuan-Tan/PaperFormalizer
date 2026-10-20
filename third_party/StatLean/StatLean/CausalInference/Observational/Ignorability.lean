module
public import StatLean.CausalInference.Core.PopulationDefs
public import StatLean.CausalInference.ForMathlib.CondAlgebra

@[expose] public section

/-!
# Unconfoundedness — what it buys inside a covariate cell

The bridge between the assumption `{Y(1), Y(0)} ⫫ Z | X` and the identification formulas:
inside a covariate cell, the conditional mean of a potential outcome does not depend on
which arm one conditions on, i.e. **the arm regression function recovers the potential
outcome mean**,

$$m_z(x)=\mathbb E[Y\mid Z=z,X=x]=\mathbb E[Y(z)\mid X=x].$$

This is the only place where independence is used; every later identification theorem
(standardization, IPW, AIPW, ATT) consumes this file's conclusions.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Assumption 10.1 (ignorability `Y(z) ⫫ Z | X`,
eq. (10.10)), Assumption 10.2 (strong ignorability `{Y(1),Y(0)} ⫫ Z | X`, eq. (10.11)),
and eqs. (10.3)–(10.4) (the mean-ignorability hypotheses of Theorem 10.1).
(`Ding Assumptions 10.1–10.2; §10.3`.) The unconfoundedness terminology and its role in
observational studies is that of G. W. Imbens and D. B. Rubin, *Causal Inference for
Statistics, Social, and Biomedical Sciences*, Cambridge University Press, 2015, Part III.
(`IR Part III`.)

**Proof formalization notes.** With a discrete covariate, `Unconfounded` is cell-wise
independence under `μ[|{X = x}]` (see `Core.PopulationDefs`), so each result here is
`ForMathlib.CondAlgebra.integral_cond_arm_eq_of_indepFun` applied inside a cell, after
rewriting `μ[|{Z = z} ∩ {X = x}]` as `(μ[|{X = x}])[|{Z = z}]` — that rewriting
(`cond_cond_eq_cond_inter`) is the first lemma below. Observed outcomes agree with the
relevant potential outcome on each arm, which is what lets `cellMean` of the *observed*
outcome be replaced by a potential-outcome mean.

**Bibliographic comments.** P. R. Rosenbaum and D. B. Rubin, "The central role of the
propensity score in observational studies for causal effects," *Biometrika* **70** (1983),
41–55, introduce strong ignorability.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳]
  {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

omit [MeasurableSpace Ω] [MeasurableSpace 𝒳] in
/-- On the treated arm the observed outcome is the treated potential outcome. -/
theorem obs_eqOn_treated : Set.EqOn (obs Z y1 y0) y1 {ω | Z ω = true} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  simp only [obs, hω, if_true]

omit [MeasurableSpace Ω] [MeasurableSpace 𝒳] in
/-- On the control arm the observed outcome is the control potential outcome. -/
theorem obs_eqOn_control : Set.EqOn (obs Z y1 y0) y0 {ω | Z ω = false} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  simp only [obs, hω, Bool.false_eq_true, if_false]

/-! ### Private infrastructure

Two bricks carrying the measurability that the headline statements below supply.

* `cond_armCell_eq'` is the arm-cell instance of "conditioning twice is conditioning on the
  intersection". It is proved *by hand* rather than through `cond_cond_eq_cond_inter`
  because only the **arm** `{Z = z}` is known to be measurable here: the covariate cell
  `X ⁻¹' {x}` is not, `𝒳` carrying no `MeasurableSingletonClass`. Measurability of the arm
  is exactly what `Measure.restrict_restrict` and `Measure.restrict_apply` need, so the
  covariate cell never has to be measurable; the scalars then telescope because the cell
  has finite, nonzero mass.
* `cellMean_obs_eq'` is `cellMean_obs_eq` with `Measurable Z` supplied. The arm cell itself
  need not be measurable: it is a subset of the measurable arm, so `μ.restrict (armCell)`
  is dominated by `μ.restrict {Z = z}` and a.e. membership transfers. -/

/-- Conditioning on a covariate cell and then on an arm is conditioning on the arm cell. -/
private theorem cond_armCell_eq' [IsProbabilityMeasure μ] (hZ : Measurable Z) (z : Bool)
    (x : 𝒳) (hcell : μ (cell X x) ≠ 0) :
    μ[|armCell Z X z x] = (μ[|cell X x])[|{ω | Z ω = z}] := by
  have hZs : MeasurableSet {ω | Z ω = z} := hZ (measurableSet_singleton z)
  have hm0 : μ (cell X x) ≠ 0 := hcell
  have hmtop : μ (cell X x) ≠ ⊤ := measure_ne_top μ _
  have hcond : ∀ (ν : Measure Ω) (s : Set Ω), ν[|s] = (ν s)⁻¹ • ν.restrict s :=
    fun _ _ => rfl
  have harm : armCell Z X z x = {ω | Z ω = z} ∩ cell X x := rfl
  rw [harm]
  simp only [hcond, Measure.restrict_smul, Measure.restrict_restrict hZs, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply hZs, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr hmtop))
      (Or.inl (ENNReal.inv_ne_top.mpr hm0)), inv_inv,
    mul_comm (μ (cell X x)), mul_assoc, ENNReal.mul_inv_cancel hm0 hmtop, mul_one]

/-- Consistency inside an arm cell, with the measurability of the model variables supplied.
The arm cell `{Z = z} ∩ X ⁻¹' {x}` is measurable — this is where the area's standing scope
(a discrete covariate, `MeasurableSingletonClass 𝒳`) is used — so a.e. membership in it is
available under the conditional measure. -/
private theorem cellMean_obs_eq' [MeasurableSingletonClass 𝒳] (hZ : Measurable Z)
    (hX : Measurable X) (z : Bool) (x : 𝒳) :
    cellMean μ Z X (obs Z y1 y0) z x = cellMean μ Z X (if z then y1 else y0) z x := by
  have harm : MeasurableSet (armCell Z X z x) :=
    (hZ (measurableSet_singleton z)).inter (hX (measurableSet_singleton x))
  refine integral_congr_ae ?_
  filter_upwards [ProbabilityTheory.ae_cond_mem (μ := μ) harm] with ω hω
  have hz : Z ω = z := hω.1
  simp only [obs, hz]
  cases z <;> simp

/-- Inside a covariate cell of positive mass, an arm conditional mean of an independent
integrand is the cell conditional mean. -/
private theorem integral_cond_armCell_eq [IsProbabilityMeasure μ] {y : Ω → ℝ}
    (hZ : Measurable Z) (hy : Measurable y) (hint : Integrable y μ) {x : 𝒳} {z : Bool}
    (hindep : IndepFun y Z (μ[|cell X x])) (hcell : μ (cell X x) ≠ 0)
    (hpos : (μ[|cell X x]) {ω | Z ω = z} ≠ 0) :
    ∫ ω, y ω ∂(μ[|armCell Z X z x]) = ∫ ω, y ω ∂(μ[|cell X x]) := by
  haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure hcell
  have hintc : Integrable y (μ[|cell X x]) :=
    hint.restrict.smul_measure (ENNReal.inv_ne_top.mpr hcell)
  rw [cond_armCell_eq' hZ z x hcell]
  exact integral_cond_arm_eq_of_indepFun hindep hintc hy hZ hpos

/-- **Conditioning on a covariate cell and then on an arm is conditioning on the arm cell.**
The form of "conditioning twice is conditioning on the intersection" that the identification
proofs need. Only the *arm* has to be measurable: the covariate cell enters only through its
mass, which is finite and (by hypothesis) nonzero, so the two normalizing scalars
telescope. -/
theorem cond_armCell_eq [IsProbabilityMeasure μ]
    -- USER-INPUT: the treatment is a random variable; user-supplied data
    (hZ : Measurable Z) (z : Bool) (x : 𝒳)
    -- USER-INPUT: a covariate cell of positive probability; on a null cell the scalars no
    -- longer cancel
    (hcell : μ (cell X x) ≠ 0) :
    μ[|armCell Z X z x] = (μ[|cell X x])[|{ω | Z ω = z}] :=
  cond_armCell_eq' hZ z x hcell

/-- The arm regression function of the *observed* outcome is the arm regression function
of the corresponding *potential* outcome — consistency (Ding Assumption 2.2). -/
theorem cellMean_obs_eq [MeasurableSingletonClass 𝒳]
    -- USER-INPUT: the model variables are random variables; needed to know the arm cell is
    -- measurable, without which the a.e. consistency step is unavailable
    (hZ : Measurable Z) (hX : Measurable X) (z : Bool) (x : 𝒳) :
    cellMean μ Z X (obs Z y1 y0) z x
      = cellMean μ Z X (if z then y1 else y0) z x :=
  cellMean_obs_eq' hZ hX z x

/-- **Unconfoundedness identifies the cell means** (Ding Assumption 10.2 ⇒ eq. (10.5)):
inside a covariate cell of positive probability, the treated arm's regression function
equals the conditional mean of the treated potential outcome. -/
theorem cellMean_true_eq_of_unconfounded [IsProbabilityMeasure μ] [MeasurableSingletonClass 𝒳]
    -- USER-INPUT: strong ignorability `{Y(1),Y(0)} ⫫ Z | X`; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    -- USER-INPUT: integrability of the potential outcome; Ding assumes finite means
    (hint : Integrable y1 μ) {x : 𝒳}
    -- USER-INPUT: a covariate cell of positive probability
    (hcell : μ (cell X x) ≠ 0)
    -- USER-INPUT: positivity `e(x) > 0`; Ding §11.2.1 (else the treated arm is empty)
    (hpos : (μ[|cell X x]) (treatedEvent Z) ≠ 0) :
    cellMean μ Z X (obs Z y1 y0) true x = ∫ ω, y1 ω ∂(μ[|cell X x]) := by
  have hpos' : (μ[|cell X x]) {ω | Z ω = true} ≠ 0 := hpos
  have hindep : IndepFun y1 Z (μ[|cell X x]) := (hu x).comp measurable_fst measurable_id
  rw [cellMean_obs_eq' hZ hX true x, cellMean]
  simpa using integral_cond_armCell_eq hZ hy1 hint hindep hcell hpos'

/-- **Unconfoundedness identifies the cell means**, control arm (Ding Assumption 10.2 ⇒
eq. (10.6)). -/
theorem cellMean_false_eq_of_unconfounded [IsProbabilityMeasure μ] [MeasurableSingletonClass 𝒳]
    (hu : Unconfounded μ Z y1 y0 X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable y0 μ) {x : 𝒳}
    (hcell : μ (cell X x) ≠ 0)
    -- USER-INPUT: positivity `e(x) < 1`; Ding §11.2.1 (else the control arm is empty)
    (hpos : (μ[|cell X x]) {ω | Z ω = false} ≠ 0) :
    cellMean μ Z X (obs Z y1 y0) false x = ∫ ω, y0 ω ∂(μ[|cell X x]) := by
  have hindep : IndepFun y0 Z (μ[|cell X x]) := (hu x).comp measurable_snd measurable_id
  rw [cellMean_obs_eq' hZ hX false x, cellMean]
  simpa using integral_cond_armCell_eq hZ hy0 hint hindep hcell hpos

/-- **Strong ignorability implies ignorability for each arm** (Ding Assumption 10.2 ⇒
Assumption 10.1). -/
theorem Unconfounded.ignorable_left (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: measurability of the potential outcomes; needed to project the pair
    (hy1 : Measurable y1) (hy0 : Measurable y0) :
    Ignorable μ Z y1 X := fun x => (hu x).comp measurable_fst measurable_id

/-- **Strong ignorability implies ignorability for the control arm.** -/
theorem Unconfounded.ignorable_right (hu : Unconfounded μ Z y1 y0 X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) :
    Ignorable μ Z y0 X := fun x => (hu x).comp measurable_snd measurable_id

/-- **Ignorability implies mean ignorability** (Ding Assumption 10.1 ⇒ eqs. (10.3)–(10.4)):
the hypothesis actually used by the standardization theorem is weaker than independence. -/
theorem MeanIgnorable_of_ignorable [IsProbabilityMeasure μ] [MeasurableSingletonClass 𝒳]
    (hi : Ignorable μ Z y1 X)
    (hy1 : Measurable y1) (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable y1 μ)
    -- USER-INPUT: positivity in every cell, so that both arm means are genuine averages;
    -- Ding §11.2.1
    (hpos : Positive μ Z X) :
    MeanIgnorable μ Z y1 X := by
  intro x
  rcases eq_or_ne (μ (cell X x)) 0 with hcell | hcell
  · -- A null cell has null arms, so both conditional measures are zero and both means are `0`.
    have harm : ∀ z : Bool, μ (armCell Z X z x) = 0 :=
      fun z => measure_mono_null Set.inter_subset_right hcell
    simp [ProbabilityTheory.cond_eq_zero_of_meas_eq_zero (harm true),
      ProbabilityTheory.cond_eq_zero_of_meas_eq_zero (harm false)]
  · -- Both arms are non-null by positivity, so each arm mean is the cell mean.
    haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure hcell
    obtain ⟨hlt0, hlt1⟩ := hpos x hcell
    have hT : (μ[|cell X x]) {ω | Z ω = true} ≠ 0 := by
      have := (ENNReal.toReal_pos_iff.mp hlt0).1
      exact this.ne'
    have hC : (μ[|cell X x]) {ω | Z ω = false} ≠ 0 := by
      intro h
      have hZt : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
      have hcompl : ({ω | Z ω = true} : Set Ω)ᶜ = {ω | Z ω = false} := by ext ω; simp
      have h0 : (μ[|cell X x]) (({ω | Z ω = true} : Set Ω)ᶜ) = 0 := by rw [hcompl]; exact h
      have hge : 1 ≤ (μ[|cell X x]) {ω | Z ω = true} := by
        rw [prob_compl_eq_one_sub hZt] at h0
        exact tsub_eq_zero_iff_le.mp h0
      have hone : (μ[|cell X x]) {ω | Z ω = true} = 1 := le_antisymm prob_le_one hge
      have : propensity μ Z X x = 1 := by
        unfold propensity treatedEvent
        rw [hone]
        simp
      linarith
    rw [integral_cond_armCell_eq hZ hy1 hint (hi x) hcell hT,
      integral_cond_armCell_eq hZ hy1 hint (hi x) hcell hC]

end StatLean.CausalInference
