module
public import StatLean.CausalInference.Observational.Ignorability

@[expose] public section

/-!
# The propensity score — balancing and dimension reduction

The propensity score `e(x) = P(Z = 1 | X = x)` is a **balancing score**: conditioning on it
alone makes the treatment probability constant across covariate values,

$$\Pr(Z=1\mid X=x)=\Pr\bigl(Z=1\mid e(X)=e(x)\bigr),$$

and under ignorability it suffices to adjust for `e(X)` instead of the full covariate —
the dimension-reduction property that makes propensity-score methods practical. This file
also proves the weighted-balance identity `E[Z h(X)/e(X)] = E[(1-Z) h(X)/(1-e(X))]` that
underlies weighting diagnostics.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Definition 11.1 (the propensity score, p. 153);
Theorem 11.3 (§11.3.1, p. 163: `Z ⫫ X | e(X)`, which needs *no* ignorability assumption,
together with the weighted balance eq. (11.2)); Theorem 11.1 (§11.1.1, p. 154: strong
ignorability given `X` implies strong ignorability given `e(X)`); §11.2.1 for
overlap. (`Ding Definition 11.1; Theorems 11.1, 11.3`.) Propensity-score design in
G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
Sciences*, Cambridge University Press, 2015, chs. 12–13. (`IR chs. 12–13`.)

**Scope.** Ding's Theorem 11.1 is stated as a conditional *independence*
`{Y(1),Y(0)} ⫫ Z | e(X)`. What is formalized here is its **mean form**
(`integral_cond_propensityLevel_arm_eq`): within a level set of the propensity score, the
arm-conditional mean of a potential outcome equals its unconditional mean. That is the
form every downstream identification result consumes, and it avoids building a
conditional-independence-given-a-real-valued-statistic layer that StatLean does not have.

**Proof formalization notes.** `propensityLevel μ Z X v` is the preimage `{e(X) = v}`, a
finite union of covariate cells because `𝒳` is finite. Both balancing results reduce to:
each cell in the level set has treatment probability exactly `v`, so the mixture over
cells also has treatment probability `v`. The weighted-balance identity is a cell-wise
computation in which the factor `e(x)` cancels.

**Bibliographic comments.** P. R. Rosenbaum and D. B. Rubin, "The central role of the
propensity score in observational studies for causal effects," *Biometrika* **70** (1983),
41–55 (Theorems 1–3 there are the balancing and dimension-reduction properties).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- The **level set of the propensity score**: the units whose covariate cell has
propensity `v`. A finite union of covariate cells. -/
def propensityLevel (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (v : ℝ) : Set Ω :=
  {ω | propensity μ Z X (X ω) = v}

/-! ### Private infrastructure

A propensity level `{e(X) = v}` is a **union of covariate cells**: membership depends on
`ω` only through `X ω`. That regrouping (`propensityLevel_inter_cell_eq` and
`propensityLevel_inter_cell_empty`, used inside the cell decomposition of an arbitrary
measurable set) is what every result below rests on. Two consequences are isolated: the
mass of the treated part of a level is `v` times the mass of the level
(`measureReal_treated_inter_propensityLevel`), and — under unconfoundedness — so is the
integral of a potential outcome over it (`setIntegral_treated_inter_propensityLevel`). The
level set is measurable because `e ∘ X` is a measurable function into `ℝ`, `𝒳` being
discrete. -/

private lemma measurableSet_cell (hX : Measurable X) (x : 𝒳) : MeasurableSet (cell X x) :=
  hX (measurableSet_singleton x)

omit [MeasurableSpace Ω] [MeasurableSpace 𝒳] [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
/-- Auxiliary: the covariate cell is the preimage of a singleton — used to fold the
`X ⁻¹' {x}` produced by the `ForMathlib.CondAlgebra` decomposition lemmas back into
`cell`. -/
private lemma cell_eq (X : Ω → 𝒳) (x : 𝒳) : X ⁻¹' {x} = cell X x := rfl

omit [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
/-- The traces of the covariate cells on a set are pairwise disjoint. -/
private lemma inter_cell_pairwise_disjoint (A : Set Ω) :
    Pairwise (Function.onFun Disjoint fun x : 𝒳 => A ∩ cell X x) := by
  intro a b hab
  simp only [Function.onFun, Set.disjoint_left]
  rintro ω ⟨-, ha⟩ ⟨-, hb⟩
  simp only [cell, Set.mem_preimage, Set.mem_singleton_iff] at ha hb
  exact hab (ha.symm.trans hb)

omit [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
/-- The traces of the covariate cells on a set cover it. -/
private lemma iUnion_inter_cell (A : Set Ω) : (⋃ x : 𝒳, A ∩ cell X x) = A := by
  rw [← Set.inter_iUnion]
  have hcov : (⋃ x : 𝒳, cell X x) = (Set.univ : Set Ω) := by
    ext ω
    simp only [Set.mem_iUnion, cell, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ,
      iff_true]
    exact ⟨X ω, rfl⟩
  rw [hcov, Set.inter_univ]

/-- The mass of a measurable set is the sum of the masses of its traces on the cells. -/
private lemma measure_eq_sum_inter_cell [IsFiniteMeasure μ] (hX : Measurable X) {A : Set Ω}
    (hA : MeasurableSet A) : μ A = ∑ x : 𝒳, μ (A ∩ cell X x) := by
  calc μ A = μ (⋃ x : 𝒳, A ∩ cell X x) := by rw [iUnion_inter_cell]
    _ = ∑' x : 𝒳, μ (A ∩ cell X x) :=
        measure_iUnion (inter_cell_pairwise_disjoint A)
          fun x => hA.inter (measurableSet_cell hX x)
    _ = ∑ x : 𝒳, μ (A ∩ cell X x) := tsum_fintype _

/-- The integral over a measurable set is the sum of the integrals over its traces on the
cells. -/
private lemma setIntegral_eq_sum_inter_cell [IsFiniteMeasure μ] (hX : Measurable X) {A : Set Ω}
    (hA : MeasurableSet A) {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫ ω in A, f ω ∂μ = ∑ x : 𝒳, ∫ ω in A ∩ cell X x, f ω ∂μ := by
  calc ∫ ω in A, f ω ∂μ = ∫ ω in ⋃ x : 𝒳, A ∩ cell X x, f ω ∂μ := by rw [iUnion_inter_cell]
    _ = ∑ x : 𝒳, ∫ ω in A ∩ cell X x, f ω ∂μ :=
        integral_iUnion_fintype (fun x => hA.inter (measurableSet_cell hX x))
          (inter_cell_pairwise_disjoint A) fun _ => hf.integrableOn

/-- The treated part of a cell carries mass `e(x)` times the mass of the cell — the
definition of the propensity score read backwards. Valid on a null cell too, both sides
being `0` there. -/
private lemma measureReal_treated_inter_cell [IsFiniteMeasure μ] (hX : Measurable X) (x : 𝒳) :
    (μ (treatedEvent Z ∩ cell X x)).toReal = propensity μ Z X x * (μ (cell X x)).toReal := by
  have hc : MeasurableSet (cell X x) := measurableSet_cell hX x
  rcases eq_or_ne (μ (cell X x)) 0 with h0 | h0
  · have hz : μ (treatedEvent Z ∩ cell X x) = 0 :=
      measure_mono_null Set.inter_subset_right h0
    rw [hz, h0]
    simp
  · have hne : (μ (cell X x)).toReal ≠ 0 := by
      simp [ENNReal.toReal_eq_zero_iff, h0, measure_ne_top μ _]
    have hp : propensity μ Z X x
        = (μ (cell X x)).toReal⁻¹ * (μ (cell X x ∩ treatedEvent Z)).toReal := by
      rw [propensity, cond_apply hc, ENNReal.toReal_mul, ENNReal.toReal_inv]
    calc (μ (treatedEvent Z ∩ cell X x)).toReal
        = (μ (cell X x ∩ treatedEvent Z)).toReal := by rw [Set.inter_comm]
      _ = (μ (cell X x)).toReal⁻¹ * (μ (cell X x ∩ treatedEvent Z)).toReal
            * (μ (cell X x)).toReal := by field_simp
      _ = propensity μ Z X x * (μ (cell X x)).toReal := by rw [hp]

omit [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
/-- A cell whose propensity is `v` lies inside the level `v`. -/
private lemma propensityLevel_inter_cell_eq {v : ℝ} {x : 𝒳} (h : propensity μ Z X x = v) :
    propensityLevel μ Z X v ∩ cell X x = cell X x := by
  refine Set.inter_eq_right.mpr fun ω hω => ?_
  have hx : X ω = x := hω
  show propensity μ Z X (X ω) = v
  rw [hx]; exact h

omit [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
/-- A cell whose propensity is not `v` misses the level `v` entirely. -/
private lemma propensityLevel_inter_cell_empty {v : ℝ} {x : 𝒳} (h : propensity μ Z X x ≠ v) :
    propensityLevel μ Z X v ∩ cell X x = ∅ := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hL hc
  have hx : X ω = x := hc
  have hv : propensity μ Z X (X ω) = v := hL
  rw [hx] at hv
  exact h hv

/-- A propensity level is measurable: it is a level set of the measurable function
`e ∘ X`. -/
private lemma measurableSet_propensityLevel (hX : Measurable X) (v : ℝ) :
    MeasurableSet (propensityLevel μ Z X v) :=
  ((Measurable.of_discrete (f := propensity μ Z X)).comp hX) (measurableSet_singleton v)

/-- **The treated part of a propensity level carries the fraction `v`** — the cell-wise
computation behind the balancing property: every cell of the level has treated fraction
exactly `v`, so their mixture does too. -/
private lemma measureReal_treated_inter_propensityLevel [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hX : Measurable X) (v : ℝ) :
    (μ (treatedEvent Z ∩ propensityLevel μ Z X v)).toReal
      = v * (μ (propensityLevel μ Z X v)).toReal := by
  have hL : MeasurableSet (propensityLevel μ Z X v) := measurableSet_propensityLevel hX v
  have hT : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  rw [measure_eq_sum_inter_cell hX (hT.inter hL), measure_eq_sum_inter_cell hX hL,
    ENNReal.toReal_sum (fun x _ => measure_ne_top μ _),
    ENNReal.toReal_sum (fun x _ => measure_ne_top μ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases eq_or_ne (propensity μ Z X x) v with h | h
  · rw [Set.inter_assoc, propensityLevel_inter_cell_eq h,
      measureReal_treated_inter_cell hX x, h]
  · rw [Set.inter_assoc, propensityLevel_inter_cell_empty h]
    simp

omit [MeasurableSpace Ω] [MeasurableSpace 𝒳] [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
/-- The treated indicator is the indicator function of the treated event. -/
private lemma ind_eq_indicator (Z : Ω → Bool) :
    (fun ω => ind (Z ω)) = Set.indicator (treatedEvent Z) (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases hb : Z ω = true <;> simp [Set.indicator, ind, treatedEvent, hb]

omit [MeasurableSpace Ω] [MeasurableSpace 𝒳] [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
/-- The control indicator is the indicator function of the control event. -/
private lemma one_sub_ind_eq_indicator (Z : Ω → Bool) :
    (fun ω => 1 - ind (Z ω)) = Set.indicator {ω | Z ω = false} (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases hb : Z ω = true <;> simp [Set.indicator, ind, hb]

/-- The treated indicator is integrable under any finite measure. -/
private lemma integrable_ind {ν : Measure Ω} [IsFiniteMeasure ν] (hZ : Measurable Z) :
    Integrable (fun ω => ind (Z ω)) ν := by
  rw [ind_eq_indicator]
  exact (integrable_const (1 : ℝ)).indicator (hZ (measurableSet_singleton true))

/-- Inside a cell, the mean of the treated indicator is the propensity score. -/
private lemma integral_ind_cond_cell [IsFiniteMeasure μ] (hZ : Measurable Z) (hX : Measurable X)
    (x : 𝒳) : ∫ ω, ind (Z ω) ∂(μ[|cell X x]) = propensity μ Z X x := by
  have ht : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  rw [ind_eq_indicator, integral_indicator ht, setIntegral_const, smul_eq_mul, mul_one]
  rfl

/-- Inside a cell of positive mass, the mean of the control indicator is `1 - e(x)`. -/
private lemma integral_one_sub_ind_cond_cell [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hX : Measurable X) {x : 𝒳} (h0 : μ (cell X x) ≠ 0) :
    ∫ ω, (1 - ind (Z ω)) ∂(μ[|cell X x]) = 1 - propensity μ Z X x := by
  haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure h0
  rw [integral_sub (integrable_const (1 : ℝ)) (integrable_ind hZ), integral_const,
    integral_ind_cond_cell hZ hX x]
  simp

/-- A function of the finite covariate is bounded, hence integrable. -/
private lemma integrable_comp [IsFiniteMeasure μ] (hX : Measurable X) (g : 𝒳 → ℝ) :
    Integrable (fun ω => g (X ω)) μ := by
  have hgm : Measurable fun ω => g (X ω) := (Measurable.of_discrete (f := g)).comp hX
  refine Integrable.mono' (integrable_const (∑ x : 𝒳, |g x|)) hgm.aestronglyMeasurable ?_
  filter_upwards with ω
  exact (le_of_eq (Real.norm_eq_abs _)).trans
    (Finset.single_le_sum (f := fun x => |g x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (X ω)))

/-- A weight depending only on the covariate, restricted to the treated arm, is
integrable. -/
private lemma integrable_comp_mul_ind [IsFiniteMeasure μ] (hZ : Measurable Z) (hX : Measurable X)
    (g : 𝒳 → ℝ) : Integrable (fun ω => g (X ω) * ind (Z ω)) μ := by
  have hrw : (fun ω => g (X ω) * ind (Z ω))
      = Set.indicator (treatedEvent Z) (fun ω => g (X ω)) := by
    funext ω
    by_cases hb : Z ω = true <;> simp [Set.indicator, ind, treatedEvent, hb]
  rw [hrw]
  exact (integrable_comp hX g).indicator (hZ (measurableSet_singleton true))

/-- A weight depending only on the covariate, restricted to the control arm, is
integrable. -/
private lemma integrable_comp_mul_one_sub_ind [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hX : Measurable X) (g : 𝒳 → ℝ) :
    Integrable (fun ω => g (X ω) * (1 - ind (Z ω))) μ := by
  have hrw : (fun ω => g (X ω) * (1 - ind (Z ω)))
      = Set.indicator {ω | Z ω = false} (fun ω => g (X ω)) := by
    funext ω
    by_cases hb : Z ω = true <;> simp [Set.indicator, ind, hb]
  rw [hrw]
  exact (integrable_comp hX g).indicator (hZ (measurableSet_singleton false))

/-- Integrability transfers to any conditional measure of a finite measure. -/
private lemma integrable_cond {ν : Measure Ω} [IsFiniteMeasure ν] {c : Set Ω} {f : Ω → ℝ}
    (hf : Integrable f ν) : Integrable f (ν[|c]) := by
  rcases eq_or_ne (ν c) 0 with h | h
  · simp [cond_eq_zero_of_meas_eq_zero h]
  · exact (hf.integrableOn (s := c)).smul_measure (by simp [h])

/-- **The treated part of a cell integrates a potential outcome to `e(x)` times the whole
cell** — the cell-wise form of unconfoundedness in the shape the level-set computation
needs. No positivity is required: on a null cell, and on a cell with `e(x) = 0`, both
sides vanish. -/
private lemma setIntegral_treated_cell [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hy1 : Measurable y1) (hZ : Measurable Z)
    (hX : Measurable X) (hint : Integrable y1 μ) (x : 𝒳) :
    ∫ ω in treatedEvent Z ∩ cell X x, y1 ω ∂μ
      = propensity μ Z X x * ∫ ω in cell X x, y1 ω ∂μ := by
  have hc : MeasurableSet (cell X x) := measurableSet_cell hX x
  rcases eq_or_ne (μ (cell X x)) 0 with h0 | h0
  · have hz : μ (treatedEvent Z ∩ cell X x) = 0 :=
      measure_mono_null Set.inter_subset_right h0
    rw [show μ.restrict (treatedEvent Z ∩ cell X x) = 0 from Measure.restrict_eq_zero.2 hz,
      show μ.restrict (cell X x) = 0 from Measure.restrict_eq_zero.2 h0]
    simp
  · rcases eq_or_ne ((μ[|cell X x]) (treatedEvent Z)) 0 with he | he
    · have hz : μ (treatedEvent Z ∩ cell X x) = 0 := by
        rw [cond_apply hc] at he
        rcases mul_eq_zero.mp he with h | h
        · exact absurd h (ENNReal.inv_ne_zero.2 (measure_ne_top μ _))
        · rw [Set.inter_comm]; exact h
      have hp : propensity μ Z X x = 0 := by rw [propensity, he]; simp
      rw [show μ.restrict (treatedEvent Z ∩ cell X x) = 0 from Measure.restrict_eq_zero.2 hz, hp]
      simp
    · have harm : treatedEvent Z ∩ cell X x = armCell Z X true x := rfl
      have hI : ∫ ω, y1 ω ∂(μ[|armCell Z X true x]) = ∫ ω, y1 ω ∂(μ[|cell X x]) := by
        haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure h0
        rw [cond_armCell_eq hZ true x h0]
        exact integral_cond_arm_eq_of_indepFun ((hu x).comp measurable_fst measurable_id)
          (integrable_cond hint) hy1 hZ he
      calc ∫ ω in treatedEvent Z ∩ cell X x, y1 ω ∂μ
          = (μ (treatedEvent Z ∩ cell X x)).toReal
              * ∫ ω, y1 ω ∂(μ[|treatedEvent Z ∩ cell X x]) :=
            (measureReal_mul_integral_cond (measure_ne_top μ _) y1).symm
        _ = propensity μ Z X x * (μ (cell X x)).toReal * ∫ ω, y1 ω ∂(μ[|cell X x]) := by
            rw [measureReal_treated_inter_cell hX x, harm, hI]
        _ = propensity μ Z X x * ∫ ω in cell X x, y1 ω ∂μ := by
            rw [mul_assoc, measureReal_mul_integral_cond (measure_ne_top μ _) y1]

/-- **The treated part of a propensity level integrates a potential outcome to `v` times
the whole level** — `measureReal_treated_inter_propensityLevel` with a potential outcome
in place of the constant `1`. -/
private lemma setIntegral_treated_inter_propensityLevel [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hy1 : Measurable y1) (hZ : Measurable Z)
    (hX : Measurable X) (hint : Integrable y1 μ) (v : ℝ) :
    ∫ ω in treatedEvent Z ∩ propensityLevel μ Z X v, y1 ω ∂μ
      = v * ∫ ω in propensityLevel μ Z X v, y1 ω ∂μ := by
  have hL : MeasurableSet (propensityLevel μ Z X v) := measurableSet_propensityLevel hX v
  have hT : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  rw [setIntegral_eq_sum_inter_cell hX (hT.inter hL) hint,
    setIntegral_eq_sum_inter_cell hX hL hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases eq_or_ne (propensity μ Z X x) v with h | h
  · rw [Set.inter_assoc, propensityLevel_inter_cell_eq h,
      setIntegral_treated_cell hu hy1 hZ hX hint x, h]
  · rw [Set.inter_assoc, propensityLevel_inter_cell_empty h]
    simp

/-- The propensity score of a cell is its conditional treatment probability — the
definition, restated for use. -/
theorem propensity_eq_cond (x : 𝒳) :
    propensity μ Z X x = ((μ[|cell X x]) (treatedEvent Z)).toReal := rfl

/-- The propensity score lies in `[0, 1]`. -/
theorem propensity_mem_Icc [IsProbabilityMeasure μ] (x : 𝒳) :
    propensity μ Z X x ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  rcases eq_or_ne (μ (cell X x)) 0 with h0 | h0
  · rw [propensity, cond_eq_zero_of_meas_eq_zero h0]
    simp
  · haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure h0
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simpa using prob_le_one (μ := μ[|cell X x]) (s := treatedEvent Z)

/-- **The propensity score is a balancing score** (Ding Theorem 11.3): the conditional
treatment probability given the whole covariate equals the conditional treatment
probability given only the propensity score. No ignorability assumption is used. -/
theorem cond_treated_propensityLevel_eq [IsProbabilityMeasure μ]
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hZ : Measurable Z) (hX : Measurable X) {x : 𝒳}
    -- USER-INPUT: a covariate cell of positive probability
    (hcell : μ (cell X x) ≠ 0) :
    ((μ[|propensityLevel μ Z X (propensity μ Z X x)]) (treatedEvent Z)).toReal
      = propensity μ Z X x := by
  have hL : MeasurableSet (propensityLevel μ Z X (propensity μ Z X x)) :=
    measurableSet_propensityLevel hX _
  -- The cell sits inside its own level, so the level is not null.
  have hsub : cell X x ⊆ propensityLevel μ Z X (propensity μ Z X x) := by
    intro ω hω
    have hx : X ω = x := hω
    show propensity μ Z X (X ω) = propensity μ Z X x
    rw [hx]
  have hLne : μ (propensityLevel μ Z X (propensity μ Z X x)) ≠ 0 := fun h =>
    hcell (measure_mono_null hsub h)
  have hLR : (μ (propensityLevel μ Z X (propensity μ Z X x))).toReal ≠ 0 := by
    simp [ENNReal.toReal_eq_zero_iff, hLne, measure_ne_top μ _]
  rw [cond_apply hL, ENNReal.toReal_mul, ENNReal.toReal_inv,
    Set.inter_comm (propensityLevel μ Z X (propensity μ Z X x)) (treatedEvent Z),
    measureReal_treated_inter_propensityLevel hZ hX (propensity μ Z X x),
    mul_comm (propensity μ Z X x), ← mul_assoc, inv_mul_cancel₀ hLR, one_mul]

/-- **`Z ⫫ X | e(X)`, mean form** (Ding Theorem 11.3): within a level set of the
propensity score, the treatment probability is the same in every covariate cell, so the
covariate carries no further information about the treatment. -/
theorem cond_treated_eq_of_propensity_eq [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X) {x x' : 𝒳}
    (hcell : μ (cell X x) ≠ 0) (hcell' : μ (cell X x') ≠ 0)
    -- USER-INPUT: the two cells share a propensity value; Ding Theorem 11.3
    (hprop : propensity μ Z X x = propensity μ Z X x') :
    ((μ[|cell X x]) (treatedEvent Z)).toReal = ((μ[|cell X x']) (treatedEvent Z)).toReal := by
  -- Both sides are, by definition, the propensity scores of the two cells; the level set
  -- `{e(X) = e(x)} = {e(X) = e(x')}` common to them carries the same value
  -- (`cond_treated_propensityLevel_eq` applied to each), which is `hprop`.
  calc ((μ[|cell X x]) (treatedEvent Z)).toReal
      = ((μ[|propensityLevel μ Z X (propensity μ Z X x)]) (treatedEvent Z)).toReal :=
        (cond_treated_propensityLevel_eq hZ hX hcell).symm
    _ = ((μ[|propensityLevel μ Z X (propensity μ Z X x')]) (treatedEvent Z)).toReal := by
        rw [hprop]
    _ = ((μ[|cell X x']) (treatedEvent Z)).toReal :=
        cond_treated_propensityLevel_eq hZ hX hcell'

/-- **Weighted covariate balance** (Ding eq. (11.2)): for any function of the covariate,
inverse-probability weighting equalizes the two arms. This is the population identity
behind balance diagnostics. -/
theorem integral_ind_div_propensity_eq [IsProbabilityMeasure μ]
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1 (the weights must be finite)
    (hpos : Positive μ Z X)
    (hZ : Measurable Z) (hX : Measurable X) (h : 𝒳 → ℝ) :
    ∫ ω, ind (Z ω) * h (X ω) / propensity μ Z X (X ω) ∂μ
      = ∫ ω, (1 - ind (Z ω)) * h (X ω) / (1 - propensity μ Z X (X ω)) ∂μ := by
  have hIT : Integrable (fun ω => ind (Z ω) * h (X ω) / propensity μ Z X (X ω)) μ := by
    have hrw : (fun ω => ind (Z ω) * h (X ω) / propensity μ Z X (X ω))
        = fun ω => (h (X ω) / propensity μ Z X (X ω)) * ind (Z ω) := by
      funext ω; ring
    rw [hrw]
    exact integrable_comp_mul_ind hZ hX fun x => h x / propensity μ Z X x
  have hIC : Integrable
      (fun ω => (1 - ind (Z ω)) * h (X ω) / (1 - propensity μ Z X (X ω))) μ := by
    have hrw : (fun ω => (1 - ind (Z ω)) * h (X ω) / (1 - propensity μ Z X (X ω)))
        = fun ω => (h (X ω) / (1 - propensity μ Z X (X ω))) * (1 - ind (Z ω)) := by
      funext ω; ring
    rw [hrw]
    exact integrable_comp_mul_one_sub_ind hZ hX fun x => h x / (1 - propensity μ Z X x)
  rw [integral_eq_sum_cell hX hIT, integral_eq_sum_cell hX hIC]
  simp only [cell_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases eq_or_ne (μ (cell X x)) 0 with h0 | h0
  · simp [h0]
  · have hc : MeasurableSet (cell X x) := measurableSet_cell hX x
    have he0 : propensity μ Z X x ≠ 0 := (hpos x h0).1.ne'
    have he1 : 1 - propensity μ Z X x ≠ 0 := sub_ne_zero.mpr (hpos x h0).2.ne'
    congr 1
    -- Inside the cell both weights are constant, and each integrates the arm indicator to
    -- exactly the mass it divides by.
    have hcongrL : ∫ ω, ind (Z ω) * h (X ω) / propensity μ Z X (X ω) ∂(μ[|cell X x])
        = ∫ ω, (h x / propensity μ Z X x) * ind (Z ω) ∂(μ[|cell X x]) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_cond_mem (μ := μ) hc] with ω hω
      have hXω : X ω = x := hω
      rw [hXω]; ring
    have hcongrR : ∫ ω, (1 - ind (Z ω)) * h (X ω) / (1 - propensity μ Z X (X ω))
          ∂(μ[|cell X x])
        = ∫ ω, (h x / (1 - propensity μ Z X x)) * (1 - ind (Z ω)) ∂(μ[|cell X x]) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_cond_mem (μ := μ) hc] with ω hω
      have hXω : X ω = x := hω
      rw [hXω]; ring
    rw [hcongrL, hcongrR, integral_const_mul, integral_const_mul,
      integral_ind_cond_cell hZ hX x, integral_one_sub_ind_cond_cell hZ hX h0]
    field_simp

/-- **The inverse-probability weights have mean one** (Ding §11.2.2): `E[Z/e(X)] = 1`.
The special case `h ≡ 1` of the balance identity, and the reason the Hájek estimator's
denominator is consistent for one. -/
theorem integral_ind_div_propensity_eq_one [IsProbabilityMeasure μ]
    (hpos : Positive μ Z X) (hZ : Measurable Z) (hX : Measurable X) :
    ∫ ω, ind (Z ω) / propensity μ Z X (X ω) ∂μ = 1 := by
  have hIT : Integrable (fun ω => ind (Z ω) / propensity μ Z X (X ω)) μ := by
    have hrw : (fun ω => ind (Z ω) / propensity μ Z X (X ω))
        = fun ω => (propensity μ Z X (X ω))⁻¹ * ind (Z ω) := by
      funext ω; ring
    rw [hrw]
    exact integrable_comp_mul_ind hZ hX fun x => (propensity μ Z X x)⁻¹
  -- Cell by cell the weighted treated indicator averages to `1`, exactly as the constant
  -- function `1` does; the cells then reassemble to the whole space.
  have key : ∫ ω, ind (Z ω) / propensity μ Z X (X ω) ∂μ = ∫ _ω, (1 : ℝ) ∂μ := by
    rw [integral_eq_sum_cell hX hIT, integral_eq_sum_cell hX (integrable_const (1 : ℝ))]
    simp only [cell_eq]
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases eq_or_ne (μ (cell X x)) 0 with h0 | h0
    · simp [h0]
    · haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure h0
      have hc : MeasurableSet (cell X x) := measurableSet_cell hX x
      have he0 : propensity μ Z X x ≠ 0 := (hpos x h0).1.ne'
      congr 1
      have hcongr : ∫ ω, ind (Z ω) / propensity μ Z X (X ω) ∂(μ[|cell X x])
          = ∫ ω, (propensity μ Z X x)⁻¹ * ind (Z ω) ∂(μ[|cell X x]) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_cond_mem (μ := μ) hc] with ω hω
        have hXω : X ω = x := hω
        rw [hXω]; ring
      rw [hcongr, integral_const_mul, integral_ind_cond_cell hZ hX x]
      simp [inv_mul_cancel₀ he0]
  rw [key]
  simp

/-- **Dimension reduction, mean form** (Ding Theorem 11.1): under strong ignorability
given the covariate, the arm-conditional mean of a potential outcome within a level set of
the propensity score equals its unconditional mean there — adjusting for the scalar
`e(X)` is as good as adjusting for `X`. -/
theorem integral_cond_propensityLevel_arm_eq [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability given `X`; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable y1 μ) {v : ℝ}
    -- USER-INPUT: a propensity level of positive probability
    (hlevel : μ (propensityLevel μ Z X v) ≠ 0)
    -- USER-INPUT: the level is a genuine treatment probability; Ding §11.2.1
    (hv : 0 < v) :
    ∫ ω, y1 ω ∂(μ[|treatedEvent Z ∩ propensityLevel μ Z X v])
      = ∫ ω, y1 ω ∂(μ[|propensityLevel μ Z X v]) := by
  -- Both conditional means are set integrals rescaled by the mass of the conditioning
  -- event. Passing to the treated part of the level multiplies numerator *and*
  -- denominator by the same factor `v`, which is where `0 < v` is used.
  rw [integral_cond_eq_setIntegral, integral_cond_eq_setIntegral,
    measureReal_treated_inter_propensityLevel hZ hX v,
    setIntegral_treated_inter_propensityLevel hu hy1 hZ hX hint v,
    mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hv.ne', one_mul]

end StatLean.CausalInference
