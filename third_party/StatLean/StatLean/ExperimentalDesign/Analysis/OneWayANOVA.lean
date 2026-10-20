module
public import StatLean.ExperimentalDesign.Core.Design
public import StatLean.ExperimentalDesign.Core.FinitePopulation

@[expose] public section

/-!
# The one-way analysis-of-variance identity

For observed data `y : U → ℝ` on the units of a completed one-way (completely
randomised) experiment with treatment assignment `g : U → T`, the **analysis of
variance identity** splits the total variation around the grand mean into
between-treatment and within-treatment (residual) parts:
$$\underbrace{\sum_i (y_i - \bar y)^2}_{SS_{\rm Total}}
  = \underbrace{\sum_i (\bar y_{g(i)} - \bar y)^2}_{SS_{\rm Treatment}}
  + \underbrace{\sum_i (y_i - \bar y_{g(i)})^2}_{SS_{\rm Residual}},$$
where `ȳ_t` is the mean of the arm of `t` and `ȳ` the grand mean.  The between part
also takes the familiar grouped form `∑_t n_t (ȳ_t − ȳ)²`.  This is the purely
algebraic content of the ANOVA table; distributional facts (χ², F) belong to
`HypothesisTesting` adapters, not here.

The assignment enters only as a fixed function `g` — the identity holds for every
allocation, which is exactly why it can be combined with randomisation moments
downstream (`Mead §9.4` takes expectations of these same sums of squares).

## Main results

* `totalSS`, `treatmentSS`, `residualSS` — the three sums of squares (all as sums
  over units, avoiding empty-group conventions).
* `sum_sub_armMean_eq_zero` — within-arm residuals sum to zero.
* `anova_decomposition` — `SS_Total = SS_Treatment + SS_Residual`.
* `treatmentSS_eq_sum_card` — the grouped form `∑_t n_t (ȳ_t − ȳ)²`.
* `totalSS_nonneg`, `treatmentSS_nonneg`, `residualSS_nonneg`,
  `residualSS_le_totalSS` — positivity and the trivial bound.

**Reference.** R. Mead, *The Design of Experiments*, CUP, 1988: the analysis of
variance identity, §2.2 (randomised blocks; the same partition argument) and the
completely randomised design's treatment/residual table, §6.2 (Table 6.1, between-
and within-treatment SS); the treatment-structure identity, §3.4.  (`Mead §2.2`,
`Mead §6.2`, `Mead §3.4`.)

**Proof formalization notes.**
* `treatmentSS` and `residualSS` are sums over *units* of quantities built from
  `armMean y (g i) g`; since the arm of `g i` always contains `i`, no empty-arm
  division convention is ever exercised, and the identity holds without any
  nonemptiness hypotheses.
* The decomposition is the cross-term computation: split
  `(y_i − ȳ) = (y_i − ȳ_{g(i)}) + (ȳ_{g(i)} − ȳ)`, expand, and kill the cross term
  by fibering the sum over arms (`Finset.sum_fiberwise`-style) and applying
  `sum_sub_armMean_eq_zero` arm by arm.
* `treatmentSS_eq_sum_card` is the same fibering applied to the constant-on-arms
  summand.
-/

namespace StatLean.ExperimentalDesign

variable {U T : Type*} [Fintype U] [DecidableEq U] [Fintype T] [DecidableEq T]

/-- The **total sum of squares**: variation of the data around the grand mean
(`Mead §6.2`). -/
noncomputable def totalSS (y : U → ℝ) : ℝ :=
  ∑ i, (y i - populationMean y) ^ 2

/-- The **treatment (between-groups) sum of squares**, as a sum over units of the
squared deviation of each unit's arm mean from the grand mean (`Mead §6.2`,
Table 6.1).  Equivalent to the grouped form `∑_t n_t (ȳ_t − ȳ)²`
(`treatmentSS_eq_sum_card`). -/
noncomputable def treatmentSS (y : U → ℝ) (g : Allocation U T) : ℝ :=
  ∑ i, (armMean y (g i) g - populationMean y) ^ 2

/-- The **residual (within-groups) sum of squares**: variation of each observation
around its own arm mean (`Mead §6.2`, Table 6.1). -/
noncomputable def residualSS (y : U → ℝ) (g : Allocation U T) : ℝ :=
  ∑ i, (y i - armMean y (g i) g) ^ 2

/-- Within one arm, residuals from the arm mean sum to zero (the defining property
of the arm mean; `Mead §2.4`, residuals). -/
theorem sum_sub_armMean_eq_zero (y : U → ℝ) (g : Allocation U T) (t : T) :
    ∑ i ∈ arm t g, (y i - armMean y t g) = 0 := by
  classical
  rcases eq_or_ne ((arm t g).card) 0 with h | h
  · have he : arm t g = ∅ := Finset.card_eq_zero.mp h
    simp [he]
  · have hc : ((arm t g).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    unfold armMean
    rw [mul_inv_cancel_left₀ hc, sub_self]

/-- **The one-way analysis of variance identity** (`Mead §2.2`, `Mead §6.2`):
`SS_Total = SS_Treatment + SS_Residual`. -/
theorem anova_decomposition (y : U → ℝ) (g : Allocation U T) :
    totalSS y = treatmentSS y g + residualSS y g := by
  classical
  have key : ∑ i, (y i - armMean y (g i) g) * (armMean y (g i) g - populationMean y)
      = 0 := by
    have hfib : ∑ t, ∑ i ∈ Finset.univ.filter (fun i => g i = t),
        ((y i - armMean y (g i) g) * (armMean y (g i) g - populationMean y))
        = ∑ i, (y i - armMean y (g i) g) * (armMean y (g i) g - populationMean y) :=
      Finset.sum_fiberwise _ _ _
    rw [← hfib]
    refine Finset.sum_eq_zero fun t _ => ?_
    have hfe : Finset.univ.filter (fun i => g i = t) = arm t g := rfl
    rw [hfe]
    have hcongr : ∀ i ∈ arm t g,
        (y i - armMean y (g i) g) * (armMean y (g i) g - populationMean y)
        = (y i - armMean y t g) * (armMean y t g - populationMean y) := by
      intro i hi
      rw [mem_arm_iff.mp hi]
    rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul, sum_sub_armMean_eq_zero,
      zero_mul]
  unfold totalSS treatmentSS residualSS
  calc ∑ i, (y i - populationMean y) ^ 2
      = ∑ i, ((armMean y (g i) g - populationMean y) ^ 2
          + (y i - armMean y (g i) g) ^ 2
          + 2 * ((y i - armMean y (g i) g) * (armMean y (g i) g - populationMean y))) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, (armMean y (g i) g - populationMean y) ^ 2
          + ∑ i, (y i - armMean y (g i) g) ^ 2
          + 2 * ∑ i, (y i - armMean y (g i) g) * (armMean y (g i) g - populationMean y) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ i, (armMean y (g i) g - populationMean y) ^ 2
          + ∑ i, (y i - armMean y (g i) g) ^ 2 := by
        rw [key, mul_zero, add_zero]

/-- The grouped form of the treatment sum of squares:
`SS_Treatment = ∑_t n_t (ȳ_t − ȳ)²` (`Mead §6.2`, Table 6.1). -/
theorem treatmentSS_eq_sum_card (y : U → ℝ) (g : Allocation U T) :
    treatmentSS y g
      = ∑ t, ((arm t g).card : ℝ) * (armMean y t g - populationMean y) ^ 2 := by
  classical
  unfold treatmentSS
  have hfib : ∑ t, ∑ i ∈ Finset.univ.filter (fun i => g i = t),
      (armMean y (g i) g - populationMean y) ^ 2
      = ∑ i, (armMean y (g i) g - populationMean y) ^ 2 :=
    Finset.sum_fiberwise _ _ _
  rw [← hfib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hfe : Finset.univ.filter (fun i => g i = t) = arm t g := rfl
  rw [hfe]
  have hcongr : ∀ i ∈ arm t g, (armMean y (g i) g - populationMean y) ^ 2
      = (armMean y t g - populationMean y) ^ 2 := by
    intro i hi
    rw [mem_arm_iff.mp hi]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]

/-- The total sum of squares is nonnegative. -/
theorem totalSS_nonneg (y : U → ℝ) : 0 ≤ totalSS y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The treatment sum of squares is nonnegative. -/
theorem treatmentSS_nonneg (y : U → ℝ) (g : Allocation U T) :
    0 ≤ treatmentSS y g :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The residual sum of squares is nonnegative. -/
theorem residualSS_nonneg (y : U → ℝ) (g : Allocation U T) :
    0 ≤ residualSS y g :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Fitting group means never increases the residual variation:
`SS_Residual ≤ SS_Total`. -/
theorem residualSS_le_totalSS (y : U → ℝ) (g : Allocation U T) :
    residualSS y g ≤ totalSS y := by
  have h := anova_decomposition y g
  have ht := treatmentSS_nonneg y g
  linarith

end StatLean.ExperimentalDesign
