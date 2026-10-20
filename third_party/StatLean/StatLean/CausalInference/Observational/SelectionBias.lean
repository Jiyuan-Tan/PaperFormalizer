module
public import StatLean.CausalInference.Core.PopulationDefs
public import StatLean.CausalInference.ForMathlib.CondAlgebra

@[expose] public section

/-!
# Selection bias — why the naive comparison is not a causal effect

The decomposition that motivates every identification assumption:

$$\underbrace{\mathbb E[Y\mid Z=1]-\mathbb E[Y\mid Z=0]}_{\tau_{\mathrm{PF}}}
 =\underbrace{\mathbb E[Y(1)-Y(0)\mid Z=1]}_{\tau_T}
 +\underbrace{\mathbb E[Y(0)\mid Z=1]-\mathbb E[Y(0)\mid Z=0]}_{\text{selection bias}}.$$

The prima facie (observed) contrast equals the effect on the treated plus a term that
compares the two arms on the *same* potential outcome; the latter vanishes precisely when
the arms are comparable, which is what randomization or ignorability delivers.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §10.2 (pp. 141–142): the prima facie effect, the
two selection-bias decompositions, and eqs. (10.1)–(10.2) showing that
`Z ⫫ {Y(1),Y(0)}` collapses `τ_PF = τ_T = τ_C = τ`. The decompositions are unnumbered
displays in the text. (`Ding §10.2`.)

**Proof formalization notes.** The two decompositions are algebraic identities of
conditional integrals once `E[Y | Z = 1] = E[Y(1) | Z = 1]` (consistency on the treated
arm) is available; that step is `integral_cond_treated_obs_eq`. The unconfounded corollary
uses independence *unconditionally* (no covariate), which is the randomized-experiment
case `X` constant — stated here with an explicit `IndepFun` hypothesis rather than
through `Unconfounded` so that it applies verbatim to a completely randomized experiment.

**Bibliographic comments.** The decomposition is the population version of the argument in
D. B. Rubin, "Estimating causal effects of treatments in randomized and nonrandomized
studies," *J. Educ. Psychol.* **66** (1974), 688–701.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ}

/-! ### Private infrastructure

The consistency step "the observed outcome may be replaced by the relevant potential
outcome inside an arm" is an a.e. statement under the conditional measure, and a
conditional measure is a scalar multiple of a restriction; the a.e. membership in the
conditioning event needs that event to be measurable, i.e. `Measurable Z`. -/

/-- Replacing the integrand by a function agreeing with it on a measurable conditioning
event does not change the conditional integral. -/
private theorem integral_cond_congr_eqOn {s : Set Ω} (hs : MeasurableSet s) {f g : Ω → ℝ}
    (hfg : Set.EqOn f g s) : ∫ ω, f ω ∂(μ[|s]) = ∫ ω, g ω ∂(μ[|s]) := by
  refine integral_congr_ae ?_
  filter_upwards [ProbabilityTheory.ae_cond_mem (μ := μ) hs] with ω hω using hfg hω

omit [MeasurableSpace Ω] in
private theorem obs_eqOn_treated_aux : Set.EqOn (obs Z y1 y0) y1 (treatedEvent Z) := by
  intro ω hω
  simp only [treatedEvent, Set.mem_setOf_eq] at hω
  simp only [obs, hω, if_true]

omit [MeasurableSpace Ω] in
private theorem obs_eqOn_control_aux : Set.EqOn (obs Z y1 y0) y0 {ω | Z ω = false} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  simp only [obs, hω, Bool.false_eq_true, if_false]

/-- Integrability transfers to a conditional measure of a finite measure. -/
private theorem integrable_cond' [IsFiniteMeasure μ] {c : Set Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) : Integrable f (μ[|c]) := by
  rcases eq_or_ne (μ c) 0 with h | h
  · simp [ProbabilityTheory.cond_eq_zero_of_meas_eq_zero h]
  · exact (hf.integrableOn (s := c)).smul_measure (by simp [h])

/-- Consistency on the treated arm, with the measurability of the treatment supplied. -/
private theorem integral_cond_treated_obs_eq' (hZ : Measurable Z) :
    ∫ ω, obs Z y1 y0 ω ∂(μ[|treatedEvent Z]) = ∫ ω, y1 ω ∂(μ[|treatedEvent Z]) :=
  integral_cond_congr_eqOn (hZ (measurableSet_singleton true)) obs_eqOn_treated_aux

/-- Consistency on the control arm, with the measurability of the treatment supplied. -/
private theorem integral_cond_control_obs_eq' (hZ : Measurable Z) :
    ∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = false}]) = ∫ ω, y0 ω ∂(μ[|{ω | Z ω = false}]) :=
  integral_cond_congr_eqOn (hZ (measurableSet_singleton false)) obs_eqOn_control_aux

/-- On the treated arm the observed outcome has the treated potential outcome's
conditional mean (consistency, Ding Assumption 2.2). -/
theorem integral_cond_treated_obs_eq
    -- USER-INPUT: the treatment is a random variable; needed to know the conditioning event
    -- is measurable, without which the a.e. consistency step is unavailable
    (hZ : Measurable Z) :
    ∫ ω, obs Z y1 y0 ω ∂(μ[|treatedEvent Z]) = ∫ ω, y1 ω ∂(μ[|treatedEvent Z]) :=
  integral_cond_treated_obs_eq' hZ

/-- On the control arm the observed outcome has the control potential outcome's
conditional mean. -/
theorem integral_cond_control_obs_eq (hZ : Measurable Z) :
    ∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = false}]) = ∫ ω, y0 ω ∂(μ[|{ω | Z ω = false}]) :=
  integral_cond_control_obs_eq' hZ

/-- **Selection-bias decomposition** (Ding §10.2): the prima facie effect is the effect on
the treated plus the between-arm difference in the *control* potential outcome. -/
theorem primaFacie_eq_att_add_selectionBias [IsProbabilityMeasure μ]
    -- USER-INPUT: the treatment is a random variable; user-supplied data
    (hZ : Measurable Z)
    -- USER-INPUT: integrable potential outcomes, so the conditional means split additively
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) :
    primaFacie μ Z (obs Z y1 y0)
      = att μ Z y1 y0
        + (∫ ω, y0 ω ∂(μ[|treatedEvent Z]) - ∫ ω, y0 ω ∂(μ[|{ω | Z ω = false}])) := by
  have hTs : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  have hCs : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  have h1T : Integrable y1 (μ[|treatedEvent Z]) := integrable_cond' hi1
  have h0T : Integrable y0 (μ[|treatedEvent Z]) := integrable_cond' hi0
  rw [primaFacie, integral_cond_treated_obs_eq' hZ, integral_cond_control_obs_eq' hZ, att,
    integral_sub h1T h0T]
  ring

/-- **Selection-bias decomposition, control version** (Ding §10.2): the prima facie effect
is the effect on the controls plus the between-arm difference in the *treated* potential
outcome. -/
theorem primaFacie_eq_atc_add_selectionBias [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) :
    primaFacie μ Z (obs Z y1 y0)
      = atc μ Z y1 y0
        + (∫ ω, y1 ω ∂(μ[|treatedEvent Z]) - ∫ ω, y1 ω ∂(μ[|{ω | Z ω = false}])) := by
  have h1C : Integrable y1 (μ[|{ω | Z ω = false}]) := integrable_cond' hi1
  have h0C : Integrable y0 (μ[|{ω | Z ω = false}]) := integrable_cond' hi0
  rw [primaFacie, integral_cond_treated_obs_eq' hZ, integral_cond_control_obs_eq' hZ, atc,
    integral_sub h1C h0C]
  ring

/-- **Randomization removes selection bias** (Ding eqs. (10.1)–(10.2)): if the treatment
is independent of the potential outcomes, the prima facie effect *is* the average causal
effect. This is the population statement of why randomized experiments identify `τ`. -/
theorem primaFacie_eq_ate_of_indep [IsProbabilityMeasure μ]
    -- USER-INPUT: the treatment is independent of the potential outcomes (randomization);
    -- Ding eq. (10.1)
    (hindep : IndepFun (fun ω => (y1 ω, y0 ω)) Z μ)
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z)
    -- USER-INPUT: integrable potential outcomes; Ding assumes finite means
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: both arms have positive probability; else a conditional mean is a junk value
    (hT : μ (treatedEvent Z) ≠ 0) (hC : μ {ω | Z ω = false} ≠ 0) :
    primaFacie μ Z (obs Z y1 y0) = ate μ y1 y0 := by
  have hT' : μ {ω | Z ω = true} ≠ 0 := hT
  have h1 : IndepFun y1 Z μ := hindep.comp measurable_fst measurable_id
  have h0 : IndepFun y0 Z μ := hindep.comp measurable_snd measurable_id
  have e1 : ∫ ω, y1 ω ∂(μ[|treatedEvent Z]) = ∫ ω, y1 ω ∂μ :=
    integral_cond_arm_eq_of_indepFun h1 hi1 hy1 hZ hT'
  have e0 : ∫ ω, y0 ω ∂(μ[|{ω | Z ω = false}]) = ∫ ω, y0 ω ∂μ :=
    integral_cond_arm_eq_of_indepFun h0 hi0 hy0 hZ hC
  rw [primaFacie, integral_cond_treated_obs_eq' hZ, integral_cond_control_obs_eq' hZ, e1, e0,
    ate, integral_sub hi1 hi0]

/-- Under randomization the three estimands coincide (Ding eq. (10.2)). -/
theorem att_eq_ate_of_indep [IsProbabilityMeasure μ]
    (hindep : IndepFun (fun ω => (y1 ω, y0 ω)) Z μ)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hT : μ (treatedEvent Z) ≠ 0) :
    att μ Z y1 y0 = ate μ y1 y0 := by
  have hT' : μ {ω | Z ω = true} ≠ 0 := hT
  have hd : IndepFun (fun ω => y1 ω - y0 ω) Z μ :=
    hindep.comp (measurable_fst.sub measurable_snd) measurable_id
  exact integral_cond_arm_eq_of_indepFun hd (hi1.sub hi0) (hy1.sub hy0) hZ hT'

/-- **`ATE` as the prevalence-weighted average of `ATT` and `ATC`** (Ding §10.2):
`τ = P(Z = 1)·τ_T + P(Z = 0)·τ_C`. -/
theorem ate_eq_prob_smul_att_add_atc [IsProbabilityMeasure μ]
    -- USER-INPUT: measurability of the treatment; user-supplied data
    (hZ : Measurable Z)
    -- USER-INPUT: integrability of the individual effect
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ) :
    ate μ y1 y0
      = (μ (treatedEvent Z)).toReal * att μ Z y1 y0
        + (μ {ω | Z ω = false}).toReal * atc μ Z y1 y0 := by
  have hTs : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  have hcompl : {ω | Z ω = false} = (treatedEvent Z)ᶜ := by
    ext ω
    simp [treatedEvent]
  rw [att, atc, measureReal_mul_integral_cond (measure_ne_top μ _),
    measureReal_mul_integral_cond (measure_ne_top μ _), hcompl, ate]
  exact (integral_add_compl hTs hint).symm

end StatLean.CausalInference
