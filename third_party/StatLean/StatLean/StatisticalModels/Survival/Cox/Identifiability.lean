module
public import StatLean.StatisticalModels.Survival.Cox.Defs

@[expose] public section

/-!
# Cox model identifiability — `(β, Λ₀)` is determined by the structure

**S5.3.** If a covariate-indexed family carries the proportional-hazards structure for two
parameter pairs, and the covariate design is rich enough (a base point plus covariate
differences spanning `ℝᵖ`), then the regression coefficients and the baseline agree:
the Cox parametrization is identified — exactly, by pure measure algebra, with no estimation
theory. Combined with the Core layer this makes `(β, Λ₀) ↦` model law injective on rich
designs; the semiparametric target `β = Prod.fst` is identified.

**Reference.** `Cox72 §2` (the scale ambiguity between `β`-intercepts and the baseline is
resolved exactly by covariate variation); A. A. Tsiatis, *Semiparametric Theory and Missing
Data*, Springer, 2006, Ch. 5 (verify §).

**Proof formalization notes.** From the two structures, `e^{⟪β,z⟫} • Λ₀ = e^{⟪β',z⟫} • Λ₀'`
for every design covariate `z`. Evaluating on a σ-finiteness-supplied set of finite positive
`Λ₀`-mass turns proportionality into the scalar identity
`e^{⟪β−β', z⟫} = c` on the design; against a base point, the linear functional
`⟪β − β', ·⟫` is constant on a spanning set of differences, forcing `β = β'` (injectivity of
`exp` + linearity), and then `Λ₀ = Λ₀'`. The scalar-extraction step is isolated as
`smul_measure_cancel` (a reusable brick).

**Bibliographic comments.** Identifiability of `(β, Λ₀)` under covariate variation is
folklore made precise in the semiparametric-efficiency literature (Tsiatis Ch. 5;
Begun–Hall–Huang–Wellner, *Ann. Statist.* **11** (1983) for the information geometry).
-/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.Survival

variable {p : ℕ}

/-- Scalar extraction brick: equal positive scalings of a nonzero σ-finite measure have
equal scales. -/
-- LEAN-ONLY: nonzero measure to cancel; brick hypothesis
theorem smul_measure_cancel {Λ : Measure ℝ} [SigmaFinite Λ] (hΛ : Λ ≠ 0) {c c' : ℝ≥0∞}
    -- LEAN-ONLY: finite nonzero scales (the Cox coefficients e^{⟪β,z⟫} are such)
    -- LEAN-ONLY: smul equation being cancelled; antecedent
    (hc : c ≠ 0) (hc' : c ≠ ⊤) (h : c • Λ = c' • Λ) : c = c' := by
  -- σ-finiteness supplies a spanning set of finite mass; nonvanishing of `Λ` puts positive
  -- mass on one of them, giving a witness `A` with `0 < Λ A < ∞` to cancel against.
  obtain ⟨n, hn⟩ : ∃ n, Λ (spanningSets Λ n) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine Measure.measure_univ_ne_zero.2 hΛ ?_
    rw [← iUnion_spanningSets Λ]
    exact measure_iUnion_null hcon
  have hAfin : Λ (spanningSets Λ n) ≠ ⊤ := (measure_spanningSets_lt_top Λ n).ne
  have hval := congrArg (fun μ : Measure ℝ => μ (spanningSets Λ n)) h
  simp only [Measure.smul_apply, smul_eq_mul] at hval
  exact (ENNReal.mul_left_inj hn hAfin).1 hval

/-- **S5.3, Cox identifiability** (`Cox72 §2`; Tsiatis Ch. 5): two proportional-hazards
structures on one covariate-indexed family, over a design containing a base point whose
differences span `ℝᵖ`, have equal coefficients and equal baselines. -/
theorem coxParameters_eq_of_isProportionalHazards
    {P : EuclideanSpace ℝ (Fin p) → Measure ℝ} {β β' : EuclideanSpace ℝ (Fin p)}
    {Λ₀ Λ₀' : Measure ℝ} {Z : Set (EuclideanSpace ℝ (Fin p))}
    {z₀ : EuclideanSpace ℝ (Fin p)}
    -- USER-INPUT: both structures hold on the design; Cox72 §2
    (h : ∀ z ∈ Z, cumHazard (P z) = ENNReal.ofReal (Real.exp ⟪β, z⟫_ℝ) • Λ₀)
    (h' : ∀ z ∈ Z, cumHazard (P z) = ENNReal.ofReal (Real.exp ⟪β', z⟫_ℝ) • Λ₀')
    -- USER-INPUT: design richness — base point + spanning differences; Cox72 §2
    (hz₀ : z₀ ∈ Z)
    (hspan : Submodule.span ℝ ((fun z => z - z₀) '' Z) = ⊤)
    -- USER-INPUT: nondegenerate baseline; Cox72 §2
    (hΛ : Λ₀ ≠ 0)
    -- LEAN-ONLY: σ-finite baselines (to extract a finite positive-mass witness)
    [SigmaFinite Λ₀] [SigmaFinite Λ₀'] :
    β = β' ∧ Λ₀ = Λ₀' := by
  -- (†) at `z` and at the base point `z₀`, cross-multiplied, is a scalar identity on `Λ₀`
  have base : ENNReal.ofReal (Real.exp ⟪β, z₀⟫_ℝ) • Λ₀
      = ENNReal.ofReal (Real.exp ⟪β', z₀⟫_ℝ) • Λ₀' := (h z₀ hz₀).symm.trans (h' z₀ hz₀)
  have key : ∀ z ∈ Z, ⟪β - β', z - z₀⟫_ℝ = 0 := by
    intro z hz
    have e1 : ENNReal.ofReal (Real.exp ⟪β, z⟫_ℝ) • Λ₀
        = ENNReal.ofReal (Real.exp ⟪β', z⟫_ℝ) • Λ₀' := (h z hz).symm.trans (h' z hz)
    have e2 : (ENNReal.ofReal (Real.exp ⟪β', z₀⟫_ℝ) * ENNReal.ofReal (Real.exp ⟪β, z⟫_ℝ)) • Λ₀
        = (ENNReal.ofReal (Real.exp ⟪β', z⟫_ℝ) * ENNReal.ofReal (Real.exp ⟪β, z₀⟫_ℝ)) • Λ₀ := by
      rw [mul_smul, mul_smul, e1, base, ← mul_smul, ← mul_smul, mul_comm]
    have e3 := smul_measure_cancel hΛ
      (mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
        (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) e2
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity), ← Real.exp_add,
      ← Real.exp_add, Real.exp_eq_exp] at e3
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    linarith
  -- the functional `⟪β − β', ·⟫` kills a spanning set, hence everything
  have hker : ∀ w : EuclideanSpace ℝ (Fin p), ⟪β - β', w⟫_ℝ = 0 := by
    have hsub : ((fun z => z - z₀) '' Z)
        ⊆ (LinearMap.ker (innerSL ℝ (β - β')).toLinearMap : Set (EuclideanSpace ℝ (Fin p))) := by
      rintro _ ⟨z, hz, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        innerSL_apply_apply]
      exact key z hz
    have hle := Submodule.span_le.2 hsub
    rw [hspan] at hle
    intro w
    have hw := hle (Submodule.mem_top : w ∈ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin p))))
    simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] using hw
  have hββ : β = β' := sub_eq_zero.1 (inner_self_eq_zero.1 (hker (β - β')))
  refine ⟨hββ, ?_⟩
  rw [← hββ] at base
  ext s hs
  have hval := congrArg (fun μ : Measure ℝ => μ s) base
  simp only [Measure.smul_apply, smul_eq_mul] at hval
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    ENNReal.ofReal_ne_top).1 hval

end StatLean.StatisticalModels.Survival
