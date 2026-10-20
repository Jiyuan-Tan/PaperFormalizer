module
public import StatLean.CausalInference.Observational.Standardization

@[expose] public section

/-!
# Subclassification — stratifying on the covariate or on the propensity score

Standardization, read as an estimator: split the sample into subclasses, take the
difference in means inside each, and average the results with subclass weights,

$$\hat\tau_{\mathrm{sub}}=\sum_k \hat\pi_{[k]}\bigl(\bar Y_{1[k]}-\bar Y_{0[k]}\bigr).$$

This file records the population identity behind that recipe — it is exactly the
standardization formula — and the propensity-score version: because the propensity score is
a balancing score, stratifying on it identifies the average causal effect just as
stratifying on the full covariate does.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §10.4.1 (p. 146: "stratification or
standardization based on discrete covariates", where the estimator
`τ̂ = ∑_k π_[k]{Ŷ_[k](1) - Ŷ_[k](0)}` is introduced and noted to be *identical* to the
stratified/post-stratified estimator of ch. 5 — stated in the text, no theorem number),
with identification by **Theorem 10.1** and its discrete form eq. (10.8); §11.1.2
(pp. 155–158: propensity-score stratification, licensed by **Theorem 11.1**, again with no
separate numbered theorem). (`Ding §10.4.1; Theorem 10.1; §11.1.2; Theorem 11.1`.)
Subclassification on the propensity score is ch. 17 of G. W. Imbens and D. B. Rubin,
*Causal Inference for Statistics, Social, and Biomedical Sciences*, Cambridge University
Press, 2015. (`IR ch. 17`.)

**Proof formalization notes.** `subclassEstimand` is written with a general subclass map
`s : 𝒳 → 𝒦` so that both cases are instances: `s = id` gives covariate stratification and
`s = ` (a discretization of) `e(·)` gives propensity stratification. The covariate version
is a regrouping of `Standardization.ate_eq_sum_cellMean_sub` — a finite `Finset.sum_fiberwise`
— and the propensity version additionally needs that the arm regression functions are
constant on a propensity level set, which is where `PropensityScore` is used. Subclasses of
probability zero contribute `0` on both sides and need no hypothesis.

**Bibliographic comments.** Subclassification is W. G. Cochran, "The effectiveness of
adjustment by subclassification in removing bias in observational studies," *Biometrics*
**24** (1968), 295–313; the propensity-score version is Rosenbaum–Rubin (1983).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {𝒦 : Type*} [Fintype 𝒦] [DecidableEq 𝒦]
  {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- The **subclass** `{s(X) = k}` induced by a subclass map `s`. -/
def subclass (X : Ω → 𝒳) (s : 𝒳 → 𝒦) (k : 𝒦) : Set Ω := (s ∘ X) ⁻¹' {k}

/-- The **subclassification estimand**: the subclass-probability-weighted average of the
within-subclass arm contrasts (Ding §10.4.1). -/
noncomputable def subclassEstimand (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ)
    (s : 𝒳 → 𝒦) : ℝ :=
  ∑ k : 𝒦, (μ (subclass X s k)).toReal
    * (∫ ω, Y ω ∂(μ[|{ω | Z ω = true} ∩ subclass X s k])
        - ∫ ω, Y ω ∂(μ[|{ω | Z ω = false} ∩ subclass X s k]))

/-! ### Private infrastructure

A subclass is a finite disjoint union of covariate cells, so every subclass-level quantity
is a sum of cell-level quantities: this is the only geometry in the file. The remaining
brick is `measureReal_armCell`, which resolves an arm cell's mass into the cell's mass
times the cell's arm probability — the step that lets a *constant* propensity across a
subclass cancel between the numerator and the denominator of a within-subclass arm mean. -/

/-- The covariate cells are pairwise disjoint. -/
private lemma cell_pairwiseDisjoint (X : Ω → 𝒳) (F : Finset 𝒳) :
    (F : Set 𝒳).PairwiseDisjoint (cell X) := by
  intro a _ b _ hab
  simp only [Function.onFun, Set.disjoint_left, cell, Set.mem_preimage, Set.mem_singleton_iff]
  intro ω ha hb
  exact hab (ha.symm.trans hb)

/-- The arm cells of a fixed arm are pairwise disjoint. -/
private lemma armCell_pairwiseDisjoint (Z : Ω → Bool) (X : Ω → 𝒳) (z : Bool) (F : Finset 𝒳) :
    (F : Set 𝒳).PairwiseDisjoint (armCell Z X z) := by
  intro a _ b _ hab
  simp only [Function.onFun, Set.disjoint_left, armCell, cell, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]
  rintro ω ⟨-, ha⟩ ⟨-, hb⟩
  exact hab (ha.symm.trans hb)

/-- A subclass is the union of the covariate cells it contains. -/
private lemma subclass_eq_biUnion [DecidableEq 𝒦] (X : Ω → 𝒳) (s : 𝒳 → 𝒦) (k : 𝒦) :
    subclass X s k = ⋃ x ∈ Finset.univ.filter fun x => s x = k, cell X x := by
  ext ω
  simp only [subclass, Function.comp_apply, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, cell, exists_prop]
  exact ⟨fun h => ⟨X ω, h, rfl⟩, fun ⟨_, hx, hxe⟩ => hxe ▸ hx⟩

/-- An arm of a subclass is the union of the corresponding arm cells. -/
private lemma arm_subclass_eq_biUnion [DecidableEq 𝒦] (Z : Ω → Bool) (X : Ω → 𝒳) (s : 𝒳 → 𝒦)
    (z : Bool) (k : 𝒦) :
    {ω | Z ω = z} ∩ subclass X s k
      = ⋃ x ∈ Finset.univ.filter fun x => s x = k, armCell Z X z x := by
  rw [subclass_eq_biUnion, Set.inter_iUnion₂]
  rfl

/-- **The mass of an arm cell**: the cell's mass times the cell's arm probability. Both
sides vanish on a null cell, so no positivity is needed. -/
private lemma measureReal_armCell [IsProbabilityMeasure μ] (hX : Measurable X) (z : Bool)
    (x : 𝒳) :
    (μ (armCell Z X z x)).toReal
      = (μ (cell X x)).toReal * ((μ[|cell X x]) {ω | Z ω = z}).toReal := by
  have hcm : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  rcases eq_or_ne (μ (cell X x)) 0 with h | h
  · have harm : μ (armCell Z X z x) = 0 :=
      measure_mono_null Set.inter_subset_right h
    rw [harm, h]
    simp
  · have hw : (μ (cell X x)).toReal ≠ 0 := by
      simp [ENNReal.toReal_eq_zero_iff, h, measure_ne_top]
    rw [cond_apply hcm, ENNReal.toReal_mul, ENNReal.toReal_inv,
      show cell X x ∩ {ω | Z ω = z} = armCell Z X z x from Set.inter_comm _ _,
      ← mul_assoc, mul_inv_cancel₀ hw, one_mul]

/-- The probability of a subclass is the sum of the probabilities of the covariate cells it
contains. -/
theorem measure_subclass_eq_sum [IsProbabilityMeasure μ] [DecidableEq 𝒳]
    -- USER-INPUT: measurability of the covariate; user-supplied data
    (hX : Measurable X) (s : 𝒳 → 𝒦) (k : 𝒦) :
    (μ (subclass X s k)).toReal
      = ∑ x ∈ Finset.univ.filter fun x => s x = k, (μ (cell X x)).toReal := by
  rw [subclass_eq_biUnion, measure_biUnion_finset (cell_pairwiseDisjoint X _)
    (fun x _ => hX (measurableSet_singleton x)),
    ENNReal.toReal_sum (fun x _ => measure_ne_top μ _)]

/-- **Exact subclassification on the covariate identifies the average causal effect**
(Ding §10.4.1, from Theorem 10.1): taking each covariate value as its own subclass, the
subclassification estimand is the average causal effect. -/
theorem subclassEstimand_id_eq_ate [IsProbabilityMeasure μ] [DecidableEq 𝒳]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) :
    subclassEstimand μ Z X (obs Z y1 y0) (id : 𝒳 → 𝒳) = ate μ y1 y0 := by
  -- `subclass X id x` *is* `cell X x` and `{Z = z} ∩ cell X x` *is* `armCell Z X z x`,
  -- both definitionally, so the estimand is literally the standardization sum.
  have h : subclassEstimand μ Z X (obs Z y1 y0) (id : 𝒳 → 𝒳)
      = ∑ x : 𝒳, (μ (cell X x)).toReal
          * (cellMean μ Z X (obs Z y1 y0) true x - cellMean μ Z X (obs Z y1 y0) false x) := rfl
  rw [h, ← ate_eq_sum_cellMean_sub hu hpos hy1 hy0 hZ hX hi1 hi0]

/-- **Subclassification is standardization**: for any subclass map the estimand regroups
the covariate cells, so a coarser subclassification is the cell-weighted average of the
coarser arm contrasts (Ding §10.4.1, "identical to the stratified estimator"). -/
theorem subclassEstimand_eq_sum_fiber [IsProbabilityMeasure μ] [DecidableEq 𝒳]
    (hZ : Measurable Z) (hX : Measurable X) (s : 𝒳 → 𝒦) (Y : Ω → ℝ)
    -- USER-INPUT: integrability of the observed outcome
    (hint : Integrable Y μ) :
    subclassEstimand μ Z X Y s
      = ∑ k : 𝒦, (μ (subclass X s k)).toReal
          * (∫ ω, Y ω ∂(μ[|{ω | Z ω = true} ∩ subclass X s k])
              - ∫ ω, Y ω ∂(μ[|{ω | Z ω = false} ∩ subclass X s k])) := rfl

/-- **The within-subclass arm mean is the cell-weighted average of the within-cell arm
means**, when the propensity score is constant on the subclass.

This is the whole content of propensity subclassification. The subclass's arm cell has mass
`∑ₓ P(X = x)·c` and integral `∑ₓ P(X = x)·c·m_z(x)`, where `c` — the arm probability of a
cell — is the *same* for every cell of the subclass precisely because the propensity score
is. So `c` cancels between numerator and denominator, and the arm mean is reweighted by the
*covariate* distribution rather than by the arm's. Balancing-score property, in one line of
arithmetic.

Two edge cases are absorbed rather than assumed. A null subclass makes both sides `0`. And
a null cell can never sit in a subclass that carries mass: its propensity is the junk value
`0`, whereas `hs` forces it to agree with a positive one. -/
private lemma subclass_arm_key [IsProbabilityMeasure μ] [DecidableEq 𝒳] [DecidableEq 𝒦]
    (hZ : Measurable Z) (hX : Measurable X) (hpos : Positive μ Z X) {Y : Ω → ℝ}
    (hint : Integrable Y μ) (s : 𝒳 → 𝒦)
    (hs : ∀ x x', s x = s x' ↔ propensity μ Z X x = propensity μ Z X x')
    (z : Bool) (k : 𝒦) :
    (μ (subclass X s k)).toReal * ∫ ω, Y ω ∂(μ[|{ω | Z ω = z} ∩ subclass X s k])
      = ∑ x ∈ Finset.univ.filter fun x => s x = k,
          (μ (cell X x)).toReal * cellMean μ Z X Y z x := by
  have hcm : ∀ x : 𝒳, MeasurableSet (cell X x) := fun x => hX (measurableSet_singleton x)
  have hZm : MeasurableSet {ω | Z ω = z} := hZ (measurableSet_singleton z)
  have hAm : ∀ x : 𝒳, MeasurableSet (armCell Z X z x) := fun x => hZm.inter (hcm x)
  -- Resolve the arm of the subclass into arm cells: masses and integrals both split.
  have hmuA : (μ ({ω | Z ω = z} ∩ subclass X s k)).toReal
      = ∑ x ∈ Finset.univ.filter fun x => s x = k, (μ (armCell Z X z x)).toReal := by
    rw [arm_subclass_eq_biUnion, measure_biUnion_finset (armCell_pairwiseDisjoint Z X z _)
      (fun x _ => hAm x), ENNReal.toReal_sum (fun x _ => measure_ne_top μ _)]
  have hintA : ∫ ω in {ω | Z ω = z} ∩ subclass X s k, Y ω ∂μ
      = ∑ x ∈ Finset.univ.filter fun x => s x = k,
          (μ (armCell Z X z x)).toReal * cellMean μ Z X Y z x := by
    rw [arm_subclass_eq_biUnion, integral_biUnion_finset (s := armCell Z X z) _
      (fun x _ => hAm x) (armCell_pairwiseDisjoint Z X z _) (fun x _ => hint.integrableOn)]
    exact Finset.sum_congr rfl fun x _ =>
      (measureReal_mul_integral_cond (measure_ne_top μ _) Y).symm
  rw [integral_cond_eq_setIntegral, hintA]
  rcases eq_or_ne (μ (subclass X s k)) 0 with h0 | h0
  · -- A null subclass: every cell it contains is null, so both sides are `0`.
    have hsub : ∀ x ∈ Finset.univ.filter fun x => s x = k, cell X x ⊆ subclass X s k := by
      intro x hx ω hω
      have hXω : X ω = x := hω
      show s (X ω) = k
      rw [hXω]
      exact (Finset.mem_filter.mp hx).2
    rw [h0, ENNReal.toReal_zero, zero_mul]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    rw [show (μ (cell X x)).toReal = 0 by
      rw [measure_mono_null (hsub x hx) h0]; simp, zero_mul]
  · -- A subclass of positive mass. Some cell in it carries mass, and then *every* cell in
    -- it does, all with the same propensity score.
    obtain ⟨x₀, hx₀F, hx₀⟩ : ∃ x ∈ Finset.univ.filter fun x => s x = k, μ (cell X x) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      refine h0 ?_
      rw [subclass_eq_biUnion, measure_biUnion_finset (cell_pairwiseDisjoint X _)
        (fun x _ => hcm x)]
      exact Finset.sum_eq_zero hcon
    have he0 := hpos x₀ hx₀
    have hprop : ∀ x ∈ Finset.univ.filter fun x => s x = k,
        propensity μ Z X x = propensity μ Z X x₀ := fun x hx =>
      (hs x x₀).mp ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hx₀F).2.symm)
    have hallne : ∀ x ∈ Finset.univ.filter fun x => s x = k, μ (cell X x) ≠ 0 := by
      intro x hx hc
      have hzero : propensity μ Z X x = 0 := by
        simp [propensity, ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hc]
      rw [hprop x hx] at hzero
      exact absurd hzero he0.1.ne'
    -- The common arm probability of the cells of this subclass.
    obtain ⟨c, hcpos, harm⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Finset.univ.filter fun x => s x = k,
        ((μ[|cell X x]) {ω | Z ω = z}).toReal = c := by
      cases z with
      | true =>
          refine ⟨propensity μ Z X x₀, he0.1, fun x hx => ?_⟩
          show propensity μ Z X x = propensity μ Z X x₀
          exact hprop x hx
      | false =>
          refine ⟨1 - propensity μ Z X x₀, by linarith [he0.2], fun x hx => ?_⟩
          have hsum : ((μ[|cell X x]) {ω | Z ω = true}).toReal
              + ((μ[|cell X x]) {ω | Z ω = false}).toReal = 1 :=
            cond_treated_add_cond_control hX hZ (hallne x hx)
          have hp : ((μ[|cell X x]) {ω | Z ω = true}).toReal = propensity μ Z X x := rfl
          rw [hp, hprop x hx] at hsum
          linarith
    -- `c` factors out of both the mass and the integral of the subclass's arm.
    have hAc : (μ ({ω | Z ω = z} ∩ subclass X s k)).toReal
        = c * (μ (subclass X s k)).toReal := by
      rw [hmuA, measure_subclass_eq_sum hX s k, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [measureReal_armCell hX z x, harm x hx]
      ring
    have hNc : ∑ x ∈ Finset.univ.filter fun x => s x = k,
          (μ (armCell Z X z x)).toReal * cellMean μ Z X Y z x
        = c * ∑ x ∈ Finset.univ.filter fun x => s x = k,
            (μ (cell X x)).toReal * cellMean μ Z X Y z x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [measureReal_armCell hX z x, harm x hx]
      ring
    have hS : (μ (subclass X s k)).toReal ≠ 0 := by
      simp [ENNReal.toReal_eq_zero_iff, h0, measure_ne_top]
    rw [hAc, hNc]
    field_simp

/-- **Exact subclassification on the propensity score identifies the average causal
effect** (Ding §11.1.2, from Theorem 11.1): stratifying on `e(X)` — a scalar — is as good
as stratifying on the whole covariate, provided each level set of `e` is taken as one
subclass. -/
theorem subclassEstimand_propensity_eq_ate [IsProbabilityMeasure μ] [DecidableEq 𝒳]
    [Fintype 𝒦] (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) (s : 𝒳 → 𝒦)
    -- USER-INPUT: the subclass map is exactly the propensity score, i.e. two covariate
    -- values share a subclass iff they share a propensity value; Ding §11.1.2
    (hs : ∀ x x', s x = s x' ↔ propensity μ Z X x = propensity μ Z X x') :
    subclassEstimand μ Z X (obs Z y1 y0) s = ate μ y1 y0 := by
  classical
  -- The observed outcome is integrable: it is pointwise dominated by `|Y(1)| + |Y(0)|`.
  have hobsm : Measurable (obs Z y1 y0) :=
    Measurable.ite (hZ (measurableSet_singleton true)) hy1 hy0
  -- ascribe the bound's type: `Integrable.add` would leave an unreduced `Pi.add`
  have hbd : Integrable (fun ω => |y1 ω| + |y0 ω|) μ := hi1.abs.add hi0.abs
  have hobs : Integrable (obs Z y1 y0) μ := by
    refine Integrable.mono' hbd hobsm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    simp only [obs]
    by_cases hz : Z ω = true
    · rw [if_pos hz]; linarith [abs_nonneg (y0 ω)]
    · rw [if_neg hz]; linarith [abs_nonneg (y1 ω)]
  -- Each subclass contributes the cell-weighted contrast over the cells it contains.
  have hkey : ∀ k : 𝒦, (μ (subclass X s k)).toReal
      * (∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = true} ∩ subclass X s k])
          - ∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = false} ∩ subclass X s k]))
      = ∑ x ∈ Finset.univ.filter fun x => s x = k, (μ (cell X x)).toReal
          * (cellMean μ Z X (obs Z y1 y0) true x
              - cellMean μ Z X (obs Z y1 y0) false x) := by
    intro k
    rw [mul_sub, subclass_arm_key hZ hX hpos hobs s hs true k,
      subclass_arm_key hZ hX hpos hobs s hs false k, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => (mul_sub _ _ _).symm
  -- Summing over subclasses regroups the covariate cells: `Finset.sum_fiberwise`.
  rw [subclassEstimand, Finset.sum_congr rfl (fun k _ => hkey k),
    Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (s x)),
    ← ate_eq_sum_cellMean_sub hu hpos hy1 hy0 hZ hX hi1 hi0]

end StatLean.CausalInference
