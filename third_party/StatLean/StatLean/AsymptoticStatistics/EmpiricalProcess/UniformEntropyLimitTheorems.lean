module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformEntropyStructural
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.DonskerProcessData

@[expose] public section

/-!
# Uniform entropy limit theorems

Auxiliary results for van der Vaart Theorems 19.13 and 19.14.

Reference: van der Vaart, *Asymptotic Statistics*, §19.2, p.274.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

open UniformEntropyStructural

/-- Finite-net data extracted from a finite uniform entropy integral.

Constitutive (vdV §19.2 p.274): this proof package records the finite nets and
summable entropy needed by the Dudley chaining proof. It is not an additional
regularity assumption: `dudleyNetData_of_uniformEntropy` constructs it from
the entropy hypothesis. -/
structure DudleyNetData (F : Set (Ω → ℝ)) (G : Ω → ℝ) : Prop where
  /-- Constitutive (vdV §19.2 p.274): every positive dyadic scale has finite
  uniform relative `L²` covering number. -/
  finiteCover : ∀ q : ℕ,
    uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ q) < ⊤
  /-- Constitutive (vdV §19.2 p.274): the uniform `L²` entropy integral is finite. -/
  entropyFinite : uniformEntropyIntegral 1 F G 2 < ⊤

/-- Construct the Dudley-net proof data internally from the entropy-integral
hypothesis, including the empty-class and zero-envelope branches. -/
theorem dudleyNetData_of_uniformEntropy
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤) : DudleyNetData F G := by
  refine ⟨?_, hJ⟩
  intro q
  let ε : ℝ := (1 / 2 : ℝ) ^ q
  have hε : 0 < ε := pow_pos (by norm_num) q
  let ε₀ : ℝ := min ε 1
  have hε₀_pos : 0 < ε₀ := lt_min hε one_pos
  have hε₀_le_ε : ε₀ ≤ ε := min_le_left _ _
  have hε₀_le_one : ε₀ ≤ 1 := min_le_right _ _
  refine lt_of_le_of_lt (uniformLpCoveringNumber_antitone_eps hε₀_le_ε) ?_
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  have hweight_top : ∀ ε' ∈ Set.Ioc (0 : ℝ) ε₀,
      entropyWeight (uniformLpCoveringNumber F G 2 ε') = ⊤ := by
    intro ε' hε'
    have hcover_top : uniformLpCoveringNumber F G 2 ε' = ⊤ :=
      top_unique (htop ▸ uniformLpCoveringNumber_antitone_eps hε'.2)
    rw [hcover_top, entropyWeight_top]
  have hJ_top : uniformEntropyIntegral 1 F G 2 = ⊤ := by
    unfold uniformEntropyIntegral
    refine top_le_iff.mp ?_
    calc
      (⊤ : ℝ≥0∞) = ∫⁻ _ε in Set.Ioc (0 : ℝ) ε₀, (⊤ : ℝ≥0∞) ∂volume := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc, sub_zero,
          ENNReal.top_mul (ENNReal.ofReal_ne_zero_iff.mpr hε₀_pos)]
      _ = ∫⁻ ε' in Set.Ioc (0 : ℝ) ε₀,
          entropyWeight (uniformLpCoveringNumber F G 2 ε') ∂volume :=
        (setLIntegral_congr_fun measurableSet_Ioc hweight_top).symm
      _ ≤ ∫⁻ ε' in Set.Ioc (0 : ℝ) 1,
          entropyWeight (uniformLpCoveringNumber F G 2 ε') ∂volume :=
        lintegral_mono_set (Set.Ioc_subset_Ioc_right hε₀_le_one)
  rw [hJ_top] at hJ
  exact (lt_irrefl _ hJ).elim

/-- The finite-dimensional marginal CLT forced by the measurable `L²`
envelope assumptions of Theorem 19.14. -/
theorem uniformEntropy_marginalCLT
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hF_meas : ∀ f ∈ F, Measurable f) -- vdV 19.14.
    (hEnv : UniformEntropyStructural.IsEnvelope F G) -- vdV 19.14.
    (hG2 : outerLpNorm P G 2 < ⊤) : -- vdV 19.14, P*G² < ∞.
    IsMarginalCLT F P := by
  apply isMarginalCLT_of_memLp
  intro f hf
  refine ⟨(hF_meas f hf).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) ENNReal.ofNat_ne_top]
  have houterG : outerExpectation P (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) < ⊤ := by
    unfold outerLpNorm at hG2
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)).mp hG2
  calc
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂P =
        outerExpectation P (fun x => ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal) := by
          symm
          exact outerExpectation_eq_lintegral
            (by simpa using (hF_meas f hf).enorm.pow_const 2)
    _ ≤ outerExpectation P (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) := by
      refine outerExpectation_mono fun x => ?_
      simp only [ENNReal.toReal_ofNat, Real.enorm_eq_ofReal_abs]
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal (by
          simpa [abs_of_nonneg (hEnv.1 x)] using hEnv.2 f hf x)) (by norm_num)
    _ < ⊤ := houterG

end AsymptoticStatistics.EmpiricalProcess
