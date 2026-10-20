module
public import StatLean.CausalInference.Observational.Standardization

@[expose] public section

/-!
# Matching — exact matching, and the bias of inexact matches

Matching imputes each treated unit's missing control outcome by the outcome of a matched
control. Two facts govern its behaviour.

* **Exact matching balances the covariate**, so the imputation is unbiased: if the matched
  control has the *same* covariate value, its expected outcome is the same regression
  function `m₀(x)`.
* **Inexact matching leaves a bias** equal to the discrepancy of the control regression
  function between the two covariate values, `m₀(Xᵢ) - m₀(X_{j(i)})`. If `m₀` is
  `L`-Lipschitz this is at most `L·d(Xᵢ, X_{j(i)})` — so the bias is controlled by the
  match quality, which is the entire justification for bias-corrected matching.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). ch. 15 (*Matching in Observational Studies*):
§15.1 (pp. 203–204, incl. the footnote showing that an exactly matched study can be
analyzed as a matched-pair experiment, so that ch. 7's results apply — no theorem number);
§15.3.1 (pp. 206–207: the matching estimator `τ̂^m = n⁻¹∑{Ŷᵢ(1) - Ŷᵢ(0)}` with
`Ŷᵢ(0) = M⁻¹∑_{k∈Jᵢ}Y_k`, and the bias-correction term
`B̂ᵢ = M⁻¹∑_{k∈Jᵢ}{μ̂₀(Xᵢ) - μ̂₀(X_k)}`), **Proposition 15.1** (p. 207: the linear
expansion of the bias-corrected estimator). (`Ding ch. 15; §15.1; §15.3.1;
Proposition 15.1`.) Matching for balance and matching estimators are chs. 15 and 18 of
G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
Sciences*, Cambridge University Press, 2015. (`IR chs. 15, 18`.)

**Scope.** Formalized here are the **population/estimand-level** statements: exact matching
recovers the control regression function, and the inexact-matching bias equals the `m₀`
discrepancy and is Lipschitz-controlled. The finite-sample matching estimator with `M`
nearest neighbours, its bias-corrected version and Propositions 15.1–15.4 are *estimation*
results whose content is the asymptotic behaviour of the matching discrepancy; they are out
of scope for this release, which stops at identification.

**Proof formalization notes.** A matching is a map `j : Ω → Ω` sending each unit to its
matched partner (`matchedControl`); exactness is `X (j ω) = X ω`. The unbiasedness
statement is then a direct corollary of `Ignorability`'s cell-mean bridge: the matched
partner is drawn from the same covariate cell, whose control arm has mean `m₀(x)`. The
Lipschitz bound is a pointwise estimate with no probabilistic content — it is stated over a
`PseudoMetricSpace` covariate so that "match quality" has a meaning.

**Bibliographic comments.** The bias-corrected matching estimator and its asymptotics are
A. Abadie and G. W. Imbens, "Large sample properties of matching estimators for average
treatment effects," *Econometrica* **74** (2006), 235–267, and "Bias-corrected matching
estimators for average treatment effects," *J. Bus. Econom. Statist.* **29** (2011), 1–11.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- A **matching** is exact when each unit's matched partner has the same covariate value
(Ding §15.1). -/
def IsExactMatching (X : Ω → 𝒳) (j : Ω → Ω) : Prop := ∀ ω, X (j ω) = X ω

/-! ### Private infrastructure

Three bricks. The first two turn the *real-valued* overlap hypothesis `Positive` into the
*measure-valued* arm-nonnullity hypotheses that `Ignorability`'s cell-mean bridges ask for
— on a cell of positive mass, `e(x) < 1` says exactly that the control arm of that cell is
not null. The third is the ignorability step for the **control** potential outcome inside
the **treated** arm of a cell, which is what makes the treated average of the imputed
control means equal the treated average of `Y(0)`; it is the arm-cell independence
argument, reassembled here from the public `cond_armCell_eq` and
`integral_cond_arm_eq_of_indepFun`. -/

/-- Integrability transfers to a conditional measure of a finite measure. -/
private lemma integrable_cond_of [IsFiniteMeasure μ] {c : Set Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) : Integrable f (μ[|c]) := by
  rcases eq_or_ne (μ c) 0 with h | h
  · simp [ProbabilityTheory.cond_eq_zero_of_meas_eq_zero h]
  · exact (hf.integrableOn (s := c)).smul_measure (by simp [h])

/-- On a cell of positive mass, `e(x) > 0` says the treated arm is not null. -/
private lemma cond_treated_ne_zero {x : 𝒳} (hpos : 0 < propensity μ Z X x) :
    (μ[|cell X x]) {ω | Z ω = true} ≠ 0 := by
  intro h
  have : propensity μ Z X x = 0 := by
    simp only [propensity, treatedEvent]
    rw [h]
    simp
  linarith

/-- On a cell of positive mass, `e(x) < 1` says the control arm is not null. -/
private lemma cond_control_ne_zero [IsProbabilityMeasure μ] (hZ : Measurable Z) {x : 𝒳}
    (hcell : μ (cell X x) ≠ 0) (hlt : propensity μ Z X x < 1) :
    (μ[|cell X x]) {ω | Z ω = false} ≠ 0 := by
  haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure hcell
  have hZt : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  have hcompl : {ω | Z ω = false} = {ω | Z ω = true}ᶜ := by ext ω; simp
  intro h
  have hsum := measure_add_measure_compl (μ := μ[|cell X x]) hZt
  rw [← hcompl, h, add_zero, measure_univ] at hsum
  have hone : propensity μ Z X x = 1 := by
    simp only [propensity, treatedEvent]
    rw [hsum]
    simp
  linarith

/-- **Ignorability inside the treated arm of a cell**: the mean of the *control* potential
outcome over the treated units of a cell is its mean over the whole cell. This is the step
that makes matching work — the matched control's cell mean is what the treated unit's own
`Y(0)` averages to. -/
private lemma integral_y0_armCell_true [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hy0 : Measurable y0) (hZ : Measurable Z)
    (hi0 : Integrable y0 μ) {x : 𝒳} (hcell : μ (cell X x) ≠ 0)
    (harm : (μ[|cell X x]) {ω | Z ω = true} ≠ 0) :
    ∫ ω, y0 ω ∂(μ[|armCell Z X true x]) = ∫ ω, y0 ω ∂(μ[|cell X x]) := by
  haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure hcell
  rw [cond_armCell_eq hZ true x hcell]
  exact integral_cond_arm_eq_of_indepFun ((hu x).comp measurable_snd measurable_id)
    (integrable_cond_of hi0) hy0 hZ harm

/-- Under an exact matching, the matched partner lies in the same covariate cell — the
covariate is perfectly balanced by construction (Ding §15.1). -/
theorem cell_matched_eq (X : Ω → 𝒳) {j : Ω → Ω} (h : IsExactMatching X j) (ω : Ω) :
    cell X (X (j ω)) = cell X (X ω) := by
  rw [h ω]

/-- **Exact matching imputes the right counterfactual mean** (Ding §15.1): the control arm
of the matched unit's cell has mean `m₀(X ω)`, which under ignorability is the conditional
mean of the control potential outcome for that unit's cell. So the exactly matched
imputation is unbiased. -/
theorem cellMean_matched_eq_cate [IsProbabilityMeasure μ] {j : Ω → Ω}
    -- USER-INPUT: the matching is exact; Ding §15.1
    (hmatch : IsExactMatching X j)
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi0 : Integrable y0 μ) {ω : Ω}
    -- USER-INPUT: the unit's covariate cell carries mass
    (hcell : μ (cell X (X ω)) ≠ 0) :
    cellMean μ Z X (obs Z y1 y0) false (X (j ω))
      = ∫ ω', y0 ω' ∂(μ[|cell X (X ω)]) := by
  rw [hmatch ω]
  exact cellMean_false_eq_of_unconfounded hu hy1 hy0 hZ hX hi0 hcell
    (cond_control_ne_zero hZ hcell (hpos (X ω) hcell).2)

/-- **Exact matching identifies the effect on the treated** (Ding §15.1, via the matched-pair
reading): averaging the matched contrasts over the treated units gives `τ_T`. -/
theorem att_eq_integral_matched_contrast [IsProbabilityMeasure μ] {j : Ω → Ω}
    (hmatch : IsExactMatching X j) (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: some unit is treated; Ding ch. 13
    (hT : μ (treatedEvent Z) ≠ 0) :
    att μ Z y1 y0
      = ∫ ω, (obs Z y1 y0 ω - cellMean μ Z X (obs Z y1 y0) false (X (j ω)))
          ∂(μ[|treatedEvent Z]) := by
  classical
  -- Abbreviations: `ν` is the law conditioned on the treated arm, `m₀` the control
  -- regression function.
  rw [att]
  set ν : Measure Ω := μ[|treatedEvent Z] with hν
  set m₀ : 𝒳 → ℝ := cellMean μ Z X (obs Z y1 y0) false with hm₀
  have hTm : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  have hcm : ∀ x : 𝒳, MeasurableSet (cell X x) := fun x => hX (measurableSet_singleton x)
  haveI hνP : IsProbabilityMeasure ν := cond_isProbabilityMeasure hT
  have hi1ν : Integrable y1 ν := integrable_cond_of hi1
  have hi0ν : Integrable y0 ν := integrable_cond_of hi0
  -- `m₀ ∘ X` is a bounded measurable function: the covariate takes finitely many values.
  have hm₀X : Measurable fun ω => m₀ (X ω) := (measurable_of_finite m₀).comp hX
  have hm₀bd : ∀ ω, ‖m₀ (X ω)‖ ≤ ∑ x : 𝒳, |m₀ x| := fun ω => by
    simpa using
      Finset.single_le_sum (f := fun x => |m₀ x|) (fun i _ => abs_nonneg _) (Finset.mem_univ (X ω))
  have hm₀int : ∀ (τ : Measure Ω) [IsFiniteMeasure τ], Integrable (fun ω => m₀ (X ω)) τ :=
    fun τ _ => Integrable.mono' (integrable_const _) hm₀X.aestronglyMeasurable
      (ae_of_all _ hm₀bd)
  -- Step 1: on the treated arm the observed outcome *is* `Y(1)`, and — the matching being
  -- exact — the imputed mean only depends on the unit's own covariate.
  have hobs : ∫ ω, (obs Z y1 y0 ω - m₀ (X (j ω))) ∂ν = ∫ ω, (y1 ω - m₀ (X ω)) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [ae_cond_mem hTm] with ω hω
    rw [obs_eqOn_treated hω, hmatch ω]
  -- Step 2: the treated average of the imputed control means is the treated average of
  -- `Y(0)`. Both are the cell decomposition of the treated law against `m₀`.
  have hcell_ν : ∀ x : 𝒳, ν (cell X x) ≠ 0 → μ (cell X x) ≠ 0 := by
    intro x hx hμ
    exact hx (cond_absolutelyContinuous hμ)
  have hkey : ∀ x : 𝒳, ν (cell X x) ≠ 0 → ∫ ω, y0 ω ∂(ν[|cell X x]) = m₀ x := by
    intro x hx
    have hμx : μ (cell X x) ≠ 0 := hcell_ν x hx
    have hνc : ν[|cell X x] = μ[|armCell Z X true x] := by
      rw [hν, cond_cond_eq_cond_inter' hTm (hcm x) (measure_ne_top μ _)]
      rfl
    have harm : (μ[|cell X x]) {ω | Z ω = true} ≠ 0 :=
      cond_treated_ne_zero (hpos x hμx).1
    rw [hνc, integral_y0_armCell_true hu hy0 hZ hi0 hμx harm, hm₀]
    exact (cellMean_false_eq_of_unconfounded hu hy1 hy0 hZ hX hi0 hμx
      (cond_control_ne_zero hZ hμx (hpos x hμx).2)).symm
  have hstep2 : ∫ ω, y0 ω ∂ν = ∫ ω, m₀ (X ω) ∂ν := by
    rw [integral_eq_sum_cell hX hi0ν, integral_eq_sum_cell hX (hm₀int ν)]
    refine Finset.sum_congr rfl fun x _ => ?_
    -- `integral_eq_sum_cell` prints the cell as `X ⁻¹' {x}`; refold it.
    show (ν (cell X x)).toReal * ∫ ω, y0 ω ∂(ν[|cell X x])
      = (ν (cell X x)).toReal * ∫ ω, m₀ (X ω) ∂(ν[|cell X x])
    rcases eq_or_ne (ν (cell X x)) 0 with h | h
    · rw [h]; simp
    · haveI : IsProbabilityMeasure (ν[|cell X x]) := cond_isProbabilityMeasure h
      have hconst : ∫ ω, m₀ (X ω) ∂(ν[|cell X x]) = m₀ x := by
        have hae : ∀ᵐ ω ∂(ν[|cell X x]), m₀ (X ω) = m₀ x := by
          filter_upwards [ae_cond_mem (hcm x)] with ω hω
          have hXω : X ω = x := hω
          rw [hXω]
        rw [integral_congr_ae hae, integral_const]
        simp
      rw [hkey x h, hconst]
  -- Step 3: reassemble.
  rw [hobs, integral_sub hi1ν hi0ν, integral_sub hi1ν (hm₀int ν), hstep2]

/-- The **matching bias** of an inexact match at a unit: the discrepancy of the control
regression function between the unit's covariate value and its match's
(Ding §15.3.1, the `B̂ᵢ` term). -/
noncomputable def matchingBias (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ)
    (j : Ω → Ω) (ω : Ω) : ℝ :=
  cellMean μ Z X Y false (X ω) - cellMean μ Z X Y false (X (j ω))

/-- An exact match has no bias (Ding §15.1). -/
theorem matchingBias_eq_zero_of_exact {j : Ω → Ω} (h : IsExactMatching X j) (Y : Ω → ℝ)
    (ω : Ω) :
    matchingBias μ Z X Y j ω = 0 := by
  simp only [matchingBias, h ω, sub_self]

/-- **The matching bias is controlled by the match quality** (Ding §15.3.1; Abadie–Imbens):
if the control regression function is `L`-Lipschitz in the covariate, the bias at each unit
is at most `L` times the distance between the unit and its match. This is the estimate that
justifies bias-corrected matching. -/
theorem abs_matchingBias_le [PseudoMetricSpace 𝒳] {j : Ω → Ω} {L : ℝ} {Y : Ω → ℝ}
    -- USER-INPUT: the control regression function is Lipschitz; the smoothness condition
    -- of Ding §15.3.1 (Abadie–Imbens)
    (hL : LipschitzWith (Real.toNNReal L) (cellMean μ Z X Y false))
    -- LEAN-ONLY: a nonnegative Lipschitz constant, so `Real.toNNReal L` is `L`
    (hL0 : 0 ≤ L) (ω : Ω) :
    |matchingBias μ Z X Y j ω| ≤ L * dist (X ω) (X (j ω)) := by
  have hd := hL.dist_le_mul (X ω) (X (j ω))
  rw [Real.dist_eq, Real.coe_toNNReal L hL0] at hd
  exact hd

end StatLean.CausalInference
