module
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-! # Restricted translated Gaussian priors on an effective cone span -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace AsymptoticStatistics.LowerBounds.GaussianConePrior

variable {m : ℕ}

noncomputable def effectiveSpan (C : Set (EuclideanSpace ℝ (Fin m))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin m)) := Submodule.span ℝ C

/-- The cone viewed inside its effective linear span. -/
def coneInEffectiveSpan (C : Set (EuclideanSpace ℝ (Fin m))) :
    Set ↥(effectiveSpan C) := {x | (x : EuclideanSpace ℝ (Fin m)) ∈ C}

/-- Convex nonempty cones have a nonempty relative interior in their
finite-dimensional effective span.  This includes `C={0}`. -/
theorem exists_effectiveInteriorBall
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (_h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ C)
    (_hconv : Convex ℝ C) :
    ∃ h0 : ↥(effectiveSpan C), ∃ r : ℝ, 0 < r ∧
      Metric.ball h0 r ⊆ coneInEffectiveSpan C := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let D : Set ↥S := coneInEffectiveSpan C
  have hC_sub : C ⊆ S := fun x hx => Submodule.subset_span hx
  have himage : S.subtype '' D = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hC_sub hx⟩, hx, rfl⟩
  have hspanD : Submodule.span ℝ D = ⊤ := by
    apply (Submodule.map_injective_of_injective S.injective_subtype)
    rw [Submodule.map_span, himage, Submodule.map_top,
      Submodule.range_subtype]
    rfl
  have hzeroD : (0 : ↥S) ∈ D := _h0
  have haff : affineSpan ℝ D = ⊤ := by
    apply SetLike.coe_injective
    rw [← Set.insert_eq_of_mem hzeroD, affineSpan_insert_zero, hspanD]
    rfl
  have hconvD : Convex ℝ D := by
    intro x hx y hy a b ha hb hab
    change (a • (x : EuclideanSpace ℝ (Fin m)) +
      b • (y : EuclideanSpace ℝ (Fin m))) ∈ C
    exact _hconv hx hy ha hb hab
  obtain ⟨h0, hh0⟩ :=
    (hconvD.interior_nonempty_iff_affineSpan_eq_top.mpr haff)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hh0)
  exact ⟨h0, r, hr, hball⟩

/-- Exact Cramér--Wold specification of the translated isotropic Gaussian
intrinsic to `effectiveSpan C`.  Every effective-span linear projection has
mean `inner u h0` and variance `c²‖u‖²`; together with support on the span this
characterizes the intrinsic Gaussian law used in Bayes flattening. -/
def IsTranslatedIsotropicGaussian
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ν (effectiveSpan C) = 1 ∧
    ∀ u : ↥(effectiveSpan C),
      Measure.map (fun x : EuclideanSpace ℝ (Fin m) =>
        ⟪(u : EuclideanSpace ℝ (Fin m)), x⟫_ℝ) ν =
        gaussianReal
          ⟪(u : EuclideanSpace ℝ (Fin m)), (h0 : EuclideanSpace ℝ (Fin m))⟫_ℝ
          ⟨c ^ 2 * ‖u‖ ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩

private noncomputable def intrinsicTranslatedGaussian
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) :
    Measure (EuclideanSpace ℝ (Fin m)) := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  letI : MeasurableSpace ↥S := borel ↥S
  letI : BorelSpace ↥S := ⟨rfl⟩
  exact (stdGaussian ↥S).map fun z =>
    ((h0 + c • z : ↥S) : EuclideanSpace ℝ (Fin m))

private theorem intrinsicTranslatedGaussian_spec
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) :
    IsTranslatedIsotropicGaussian C
      (intrinsicTranslatedGaussian C h0 c) h0 c := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  letI hmeas : MeasurableSpace ↥S := borel ↥S
  letI hborel : BorelSpace ↥S := ⟨rfl⟩
  letI hstdprob : IsProbabilityMeasure (stdGaussian ↥S) :=
    @isProbabilityMeasure_stdGaussian _ _ _ _ hmeas hborel
  letI hstdgauss : IsGaussian (stdGaussian ↥S) :=
    @isGaussian_stdGaussian _ _ _ _ hmeas hborel
  let affineInclusion : ↥S → EuclideanSpace ℝ (Fin m) :=
    fun z => ((h0 + c • z : ↥S) : EuclideanSpace ℝ (Fin m))
  have haffine_meas : Measurable affineInclusion := by
    fun_prop
  let ν : Measure (EuclideanSpace ℝ (Fin m)) :=
    (stdGaussian ↥S).map affineInclusion
  change IsTranslatedIsotropicGaussian C ν h0 c
  haveI hνprob : IsProbabilityMeasure ν := by
    exact Measure.isProbabilityMeasure_map haffine_meas.aemeasurable
  refine ⟨inferInstance, ?_, ?_⟩
  · have hSclosed : IsClosed (S : Set (EuclideanSpace ℝ (Fin m))) :=
      S.closed_of_finiteDimensional
    rw [Measure.map_apply haffine_meas hSclosed.measurableSet]
    have hpre : affineInclusion ⁻¹' (S : Set (EuclideanSpace ℝ (Fin m))) = Set.univ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact (h0 + c • z).property
    rw [hpre, measure_univ]
  · intro u
    let L : ↥S →L[ℝ] ℝ := innerSL ℝ u
    let q : ℝ → ℝ := fun x => c * x +
      ⟪(u : EuclideanSpace ℝ (Fin m)),
        (h0 : EuclideanSpace ℝ (Fin m))⟫_ℝ
    have hL_meas : Measurable L := L.continuous.measurable
    have hq_meas : Measurable q := by fun_prop
    have hmean : (∫ x, L x ∂(stdGaussian ↥S)) = 0 := by
      simpa only [L] using
        (@integral_strongDual_stdGaussian _ _ _ _ hmeas hborel
          (innerSL ℝ u))
    have hvar : Var[L; stdGaussian ↥S] = ‖u‖ ^ 2 := by
      simpa only [L, innerSL_apply_norm] using
        (@variance_dual_stdGaussian _ _ _ _ hmeas hborel
          (innerSL ℝ u))
    have hbase : (stdGaussian ↥S).map L =
        gaussianReal 0 (NNReal.mk (‖u‖ ^ 2) (sq_nonneg _)) := by
      rw [IsGaussian.map_eq_gaussianReal L]
      rw [hmean, hvar]
      congr 2
      ext
      simp
    have hcomp : (fun z : ↥S =>
        ⟪(u : EuclideanSpace ℝ (Fin m)), affineInclusion z⟫_ℝ) = q ∘ L := by
      funext z
      simp only [Function.comp_apply, affineInclusion, q, L]
      change ⟪(u : EuclideanSpace ℝ (Fin m)),
        (h0 : EuclideanSpace ℝ (Fin m)) + c •
          (z : EuclideanSpace ℝ (Fin m))⟫_ℝ =
        c * ⟪(u : EuclideanSpace ℝ (Fin m)),
          (z : EuclideanSpace ℝ (Fin m))⟫_ℝ +
          ⟪(u : EuclideanSpace ℝ (Fin m)),
            (h0 : EuclideanSpace ℝ (Fin m))⟫_ℝ
      rw [inner_add_right, real_inner_smul_right]
      ring
    rw [show Measure.map (fun x : EuclideanSpace ℝ (Fin m) =>
          ⟪(u : EuclideanSpace ℝ (Fin m)), x⟫_ℝ) ν =
        (stdGaussian ↥S).map (q ∘ L) by
          change (Measure.map affineInclusion (stdGaussian ↥S)).map
              (fun x : EuclideanSpace ℝ (Fin m) =>
                ⟪(u : EuclideanSpace ℝ (Fin m)), x⟫_ℝ) = _
          rw [Measure.map_map (by fun_prop) haffine_meas]
          congr 1]
    rw [← Measure.map_map hq_meas hL_meas, hbase]
    simp only [q]
    change (gaussianReal 0 (NNReal.mk (‖u‖ ^ 2) (sq_nonneg _))).map
        ((fun x : ℝ => x + ⟪(u : EuclideanSpace ℝ (Fin m)),
          (h0 : EuclideanSpace ℝ (Fin m))⟫_ℝ) ∘ fun x : ℝ => c * x) = _
    rw [← Measure.map_map (by fun_prop : Measurable fun x : ℝ =>
          x + ⟪(u : EuclideanSpace ℝ (Fin m)),
            (h0 : EuclideanSpace ℝ (Fin m))⟫_ℝ)
        (by fun_prop : Measurable fun x : ℝ => c * x),
      gaussianReal_map_const_mul, mul_zero, gaussianReal_map_add_const, zero_add]
    congr 2

/-- Existence of the exact translated isotropic Gaussian law intrinsic to the
effective span.  A proper span is handled intrinsically, not by restricting an
ambient nondegenerate Gaussian of zero span-mass. -/
theorem exists_translatedGaussianOnEffectiveSpan
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) :
    ∃ ν : Measure (EuclideanSpace ℝ (Fin m)),
      IsTranslatedIsotropicGaussian C ν h0 c := by
  exact ⟨intrinsicTranslatedGaussian C h0 c,
    intrinsicTranslatedGaussian_spec C h0 c⟩

/-- Translated Gaussian law constructed intrinsically on the effective span
and then included in the ambient Euclidean space. -/
noncomputable def translatedGaussianOnEffectiveSpan
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) : Measure (EuclideanSpace ℝ (Fin m)) :=
  if _hc : 0 < c then
    Classical.choose (exists_translatedGaussianOnEffectiveSpan C h0 c)
  else 0

/-- The chosen intrinsic law retains its exact center, scale, support, and
Cramér--Wold Gaussian specification. -/
theorem translatedGaussianOnEffectiveSpan_spec
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) (_hc : 0 < c) :
    IsTranslatedIsotropicGaussian C
      (translatedGaussianOnEffectiveSpan C h0 c) h0 c := by
  rw [translatedGaussianOnEffectiveSpan, dif_pos _hc]
  exact Classical.choose_spec (exists_translatedGaussianOnEffectiveSpan C h0 c)

private theorem isTranslatedIsotropicGaussian_unique
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (ν μ : Measure (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ)
    (hν : IsTranslatedIsotropicGaussian C ν h0 c)
    (hμ : IsTranslatedIsotropicGaussian C μ h0 c) : ν = μ := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure μ := hμ.1
  have hSmeas : MeasurableSet (S : Set (EuclideanSpace ℝ (Fin m))) :=
    S.closed_of_finiteDimensional.measurableSet
  apply Measure.ext_of_charFun
  ext u
  let us : ↥S := S.orthogonalProjection u
  have hνS : ∀ᵐ x ∂ν, x ∈ S :=
    (mem_ae_iff_prob_eq_one hSmeas).2 hν.2.1
  have hμS : ∀ᵐ x ∂μ, x ∈ S :=
    (mem_ae_iff_prob_eq_one hSmeas).2 hμ.2.1
  have hνmap : Measure.map (InnerProductSpace.toDualMap ℝ _ u) ν =
      gaussianReal
        ⟪(us : EuclideanSpace ℝ (Fin m)), (h0 : EuclideanSpace ℝ (Fin m))⟫_ℝ
        ⟨c ^ 2 * ‖us‖ ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩ := by
    calc
      Measure.map (InnerProductSpace.toDualMap ℝ _ u) ν =
          Measure.map (fun x : EuclideanSpace ℝ (Fin m) =>
            ⟪(us : EuclideanSpace ℝ (Fin m)), x⟫_ℝ) ν := by
        apply Measure.map_congr
        filter_upwards [hνS] with x hx
        simpa only [InnerProductSpace.toDualMap_apply_apply] using!
          (S.inner_orthogonalProjection_eq_of_mem_right ⟨x, hx⟩ u).symm
      _ = _ := hν.2.2 us
  have hμmap : Measure.map (InnerProductSpace.toDualMap ℝ _ u) μ =
      gaussianReal
        ⟪(us : EuclideanSpace ℝ (Fin m)), (h0 : EuclideanSpace ℝ (Fin m))⟫_ℝ
        ⟨c ^ 2 * ‖us‖ ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩ := by
    calc
      Measure.map (InnerProductSpace.toDualMap ℝ _ u) μ =
          Measure.map (fun x : EuclideanSpace ℝ (Fin m) =>
            ⟪(us : EuclideanSpace ℝ (Fin m)), x⟫_ℝ) μ := by
        apply Measure.map_congr
        filter_upwards [hμS] with x hx
        simpa only [InnerProductSpace.toDualMap_apply_apply] using!
          (S.inner_orthogonalProjection_eq_of_mem_right ⟨x, hx⟩ u).symm
      _ = _ := hμ.2.2 us
  calc
    charFun ν u = charFunDual ν
        (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin m)) u) :=
      charFun_eq_charFunDual_toDualMap (μ := ν) u
    _ = charFun (Measure.map
        (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin m)) u) ν) 1 :=
      charFunDual_eq_charFun_map_one (μ := ν) _
    _ = charFun (gaussianReal
        ⟪(us : EuclideanSpace ℝ (Fin m)), (h0 : EuclideanSpace ℝ (Fin m))⟫_ℝ
        ⟨c ^ 2 * ‖us‖ ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩) 1 := by
      rw [hνmap]
    _ = charFun (Measure.map
        (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin m)) u) μ) 1 := by
      rw [hμmap]
    _ = charFunDual μ
        (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin m)) u) :=
      (charFunDual_eq_charFun_map_one (μ := μ) _).symm
    _ = charFun μ u := (charFun_eq_charFunDual_toDualMap (μ := μ) u).symm

/-- Mass used to normalize the cone restriction. -/
noncomputable def conePriorNormalizer
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) : ℝ≥0∞ :=
  translatedGaussianOnEffectiveSpan C h0 c C

/-- Normalized translated Gaussian restricted to the cone. -/
noncomputable def restrictedTranslatedGaussianPrior
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) : Measure (EuclideanSpace ℝ (Fin m)) :=
  (conePriorNormalizer C h0 c)⁻¹ •
    (translatedGaussianOnEffectiveSpan C h0 c).restrict C

/-- Positivity, finiteness, probability, and support specification for the
restricted translated prior. -/
theorem restrictedTranslatedGaussianPrior_spec
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (r c : ℝ) (_hr : 0 < r)
    (_hball : Metric.ball h0 r ⊆ coneInEffectiveSpan C) (_hc : 0 < c) :
    0 < conePriorNormalizer C h0 c ∧
      conePriorNormalizer C h0 c < ∞ ∧
      IsTranslatedIsotropicGaussian C
        (translatedGaussianOnEffectiveSpan C h0 c) h0 c ∧
      IsProbabilityMeasure (restrictedTranslatedGaussianPrior C h0 c) ∧
      restrictedTranslatedGaussianPrior C h0 c C = 1 := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  letI hmeas : MeasurableSpace ↥S := borel ↥S
  letI hborel : BorelSpace ↥S := ⟨rfl⟩
  letI hstdprob : IsProbabilityMeasure (stdGaussian ↥S) :=
    @isProbabilityMeasure_stdGaussian _ _ _ _ hmeas hborel
  letI hrealOpen : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  letI hpiOpen : Measure.IsOpenPosMeasure
      (Measure.pi fun _ : Fin (Module.finrank ℝ ↥S) => gaussianReal 0 1) :=
    Measure.pi.isOpenPosMeasure _
  let synth : (Fin (Module.finrank ℝ ↥S) → ℝ) → ↥S :=
    fun x => ∑ i, x i • stdOrthonormalBasis ℝ ↥S i
  have hsynth_cont : Continuous synth := by
    fun_prop
  have hsynth_surj : Function.Surjective synth := by
    intro y
    refine ⟨fun i => (stdOrthonormalBasis ℝ ↥S).repr y i, ?_⟩
    exact (stdOrthonormalBasis ℝ ↥S).sum_repr y
  letI hstdOpen : Measure.IsOpenPosMeasure (stdGaussian ↥S) := by
    rw [stdGaussian]
    exact hsynth_cont.isOpenPosMeasure_map hsynth_surj
  let affineInclusion : ↥S → EuclideanSpace ℝ (Fin m) :=
    fun z => ((h0 + c • z : ↥S) : EuclideanSpace ℝ (Fin m))
  have haffine_meas : Measurable affineInclusion := by
    fun_prop
  let B : Set (EuclideanSpace ℝ (Fin m)) :=
    (S : Set (EuclideanSpace ℝ (Fin m))) ∩
      Metric.ball (h0 : EuclideanSpace ℝ (Fin m)) r
  have hBmeas : MeasurableSet B :=
    S.closed_of_finiteDimensional.measurableSet.inter measurableSet_ball
  have hBsub : B ⊆ C := by
    rintro x ⟨hxS, hxball⟩
    let y : ↥S := ⟨x, hxS⟩
    have hyball : y ∈ Metric.ball h0 r := by
      exact hxball
    exact _hball hyball
  have hscaledRadius : 0 < r / c := div_pos _hr _hc
  have hsmallBallPos :
      0 < (stdGaussian ↥S) (Metric.ball 0 (r / c)) :=
    Metric.isOpen_ball.measure_pos _ (Metric.nonempty_ball.mpr hscaledRadius)
  have hpreSub : Metric.ball (0 : ↥S) (r / c) ⊆ affineInclusion ⁻¹' B := by
    intro z hz
    have hz' : ‖(z : EuclideanSpace ℝ (Fin m))‖ < r / c := by
      change dist (z : EuclideanSpace ℝ (Fin m)) 0 < r / c at hz
      simpa only [dist_zero_right] using hz
    have hcz : c * ‖(z : EuclideanSpace ℝ (Fin m))‖ < r := by
      simpa only [mul_comm] using (lt_div_iff₀ _hc).mp hz'
    constructor
    · exact (h0 + c • z).property
    · change ‖((h0 + c • z : ↥S) : EuclideanSpace ℝ (Fin m)) -
          (h0 : EuclideanSpace ℝ (Fin m))‖ < r
      simpa only [Submodule.coe_add, Submodule.coe_smul, add_sub_cancel_left,
        norm_smul, Real.norm_eq_abs, abs_of_pos _hc] using hcz
  have hnormalizerPos : 0 < conePriorNormalizer C h0 c := by
    apply hsmallBallPos.trans_le
    calc
      (stdGaussian ↥S) (Metric.ball 0 (r / c))
          ≤ (stdGaussian ↥S) (affineInclusion ⁻¹' B) := measure_mono hpreSub
      _ = translatedGaussianOnEffectiveSpan C h0 c B := by
        have hchosen : translatedGaussianOnEffectiveSpan C h0 c =
            intrinsicTranslatedGaussian C h0 c :=
          isTranslatedIsotropicGaussian_unique C _ _ h0 c
            (translatedGaussianOnEffectiveSpan_spec C h0 c _hc)
            (intrinsicTranslatedGaussian_spec C h0 c)
        rw [hchosen, intrinsicTranslatedGaussian,
          Measure.map_apply haffine_meas hBmeas]
      _ ≤ translatedGaussianOnEffectiveSpan C h0 c C := measure_mono hBsub
      _ = conePriorNormalizer C h0 c := rfl
  have hgauss := translatedGaussianOnEffectiveSpan_spec C h0 c _hc
  letI htranslatedProb : IsProbabilityMeasure
      (translatedGaussianOnEffectiveSpan C h0 c) := hgauss.1
  have hnormalizerFinite : conePriorNormalizer C h0 c < ∞ := by
    exact measure_lt_top _ _
  have hrestrictedProb :
      IsProbabilityMeasure (restrictedTranslatedGaussianPrior C h0 c) := by
    refine ⟨?_⟩
    rw [restrictedTranslatedGaussianPrior, Measure.smul_apply,
      Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hnormalizerPos.ne' hnormalizerFinite.ne
  have hrestrictedSupport : restrictedTranslatedGaussianPrior C h0 c C = 1 := by
    rw [restrictedTranslatedGaussianPrior, Measure.smul_apply,
      Measure.restrict_apply_self, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hnormalizerPos.ne' hnormalizerFinite.ne
  exact ⟨hnormalizerPos, hnormalizerFinite, hgauss,
    hrestrictedProb, hrestrictedSupport⟩

end AsymptoticStatistics.LowerBounds.GaussianConePrior
