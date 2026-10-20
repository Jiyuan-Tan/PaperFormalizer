module
public import StatLean.AsymptoticStatistics.LowerBounds.GaussianConeBayes
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import Mathlib.MeasureTheory.Measure.Support

@[expose] public section

/-! # Uniform risk continuity and finite epsilon quantization -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace AsymptoticStatistics.LowerBounds.GaussianConeQuantization
open AsymptoticStatistics.LowerBounds.GaussianConeBayes
variable {m : ℕ}

private noncomputable def gaussianLikelihood
    (a z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.exp (⟪a, z⟫ - ‖a‖ ^ 2 / 2)

private theorem integral_gaussianLikelihood
    (a : EuclideanSpace ℝ (Fin m)) :
    ∫ z, gaussianLikelihood a z ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = 1 := by
  rw [show gaussianLikelihood a = fun z =>
      Real.exp (-‖a‖ ^ 2 / 2) * Real.exp ⟪a, z⟫ by
        funext z
        unfold gaussianLikelihood
        rw [← Real.exp_add]
        congr 1
        ring]
  rw [integral_const_mul, integral_exp_inner_stdGaussian, ← Real.exp_add]
  ring_nf
  simp

private theorem integral_sq_gaussianLikelihood_sub_one
    (a : EuclideanSpace ℝ (Fin m)) :
    ∫ z, (gaussianLikelihood a z - 1) ^ 2
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) =
      Real.exp (‖a‖ ^ 2) - 1 := by
  have hexp (b : EuclideanSpace ℝ (Fin m)) :
      Integrable (fun z => Real.exp ⟪b, z⟫)
        (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_exp_inner_stdGaussian]
    positivity
  have hq : Integrable (gaussianLikelihood a)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    convert (hexp a).const_mul (Real.exp (-‖a‖ ^ 2 / 2)) using 1
    funext z
    unfold gaussianLikelihood
    rw [← Real.exp_add]
    congr 1
    ring
  have hq2fun : (fun z => (gaussianLikelihood a z) ^ 2) =
      fun z => Real.exp (-‖a‖ ^ 2) * Real.exp ⟪(2 : ℝ) • a, z⟫ := by
    funext z
    unfold gaussianLikelihood
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [real_inner_smul_left]
    ring
  have hq2int : ∫ z, (gaussianLikelihood a z) ^ 2
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = Real.exp (‖a‖ ^ 2) := by
    rw [hq2fun, integral_const_mul, integral_exp_inner_stdGaussian]
    rw [norm_smul]
    norm_num
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hq2 : Integrable (fun z => (gaussianLikelihood a z) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    apply Integrable.of_integral_ne_zero
    rw [hq2int]
    positivity
  have hinner : Integrable (fun z => gaussianLikelihood a z * 2 - 1)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    (hq.mul_const 2).sub (integrable_const 1)
  have hsq : Integrable (fun z => (gaussianLikelihood a z - 1) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    convert hq2.sub hinner using 1
    funext z
    simp only [Pi.sub_apply]
    ring
  rw [show (fun z => (gaussianLikelihood a z - 1) ^ 2) =
      fun z => (gaussianLikelihood a z) ^ 2 - (gaussianLikelihood a z * 2 - 1) by
        funext z; ring]
  rw [integral_sub hq2 hinner,
    integral_sub (hq.mul_const 2) (integrable_const 1), integral_mul_const,
    integral_gaussianLikelihood, hq2int]
  norm_num

private theorem integral_abs_gaussianLikelihood_sub_one_le
    (a : EuclideanSpace ℝ (Fin m)) :
    ∫ z, |gaussianLikelihood a z - 1|
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) ≤
      (Real.exp (‖a‖ ^ 2) - 1) ^ (1 / 2 : ℝ) := by
  have hsqint : Integrable (fun z => (gaussianLikelihood a z - 1) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    by_cases ha : a = 0
    · subst a
      simp [gaussianLikelihood]
    · apply Integrable.of_integral_ne_zero
      rw [integral_sq_gaussianLikelihood_sub_one]
      have hs : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
      exact sub_ne_zero.mpr (ne_of_gt ((Real.one_lt_exp_iff).mpr hs))
  have hf : MemLp (fun z => gaussianLikelihood a z - 1) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    (memLp_two_iff_integrable_sq (by
      apply Measurable.aestronglyMeasurable
      unfold gaussianLikelihood
      fun_prop)).2 hsqint
  have hg : MemLp (fun _z : EuclideanSpace ℝ (Fin m) => (1 : ℝ)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    exact memLp_const _
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (f := fun z => gaussianLikelihood a z - 1)
    (g := fun _z : EuclideanSpace ℝ (Fin m) => (1 : ℝ))
    Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
  have hsquare : ∫ z, |gaussianLikelihood a z - 1| ^ (2 : ℝ)
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) =
      Real.exp (‖a‖ ^ 2) - 1 := by
    simp_rw [Real.rpow_two]
    rw [← integral_sq_gaussianLikelihood_sub_one a]
    apply integral_congr_ae
    filter_upwards with z
    exact sq_abs (gaussianLikelihood a z - 1)
  have hcs' : ∫ z, |gaussianLikelihood a z - 1|
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) ≤
      (∫ z, |gaussianLikelihood a z - 1| ^ (2 : ℝ)
        ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ^ (1 / 2 : ℝ) *
      (∫ _z : EuclideanSpace ℝ (Fin m), (1 : ℝ) ^ (2 : ℝ)
        ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using hcs
  rw [hsquare] at hcs'
  simpa [measureReal_def] using hcs'

private theorem stdGaussian_withDensity_gaussianLikelihood
    (a : EuclideanSpace ℝ (Fin m)) :
      (stdGaussian (EuclideanSpace ℝ (Fin m))).withDensity
        (fun z => ENNReal.ofReal (gaussianLikelihood a z)) =
        multivariateGaussian a (1 : Matrix (Fin m) (Fin m) ℝ) := by
  have h := multivariateGaussian_withDensity_exp_shift
    (Matrix.PosDef.one (n := Fin m)).posSemidef a
  have hdot : a.ofLp ⬝ᵥ a.ofLp = ‖a‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, dotProduct]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simpa [gaussianLikelihood, hdot] using h

private theorem abs_lintegral_bind_shift_le {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hg : Measurable g)
    (B : ℝ≥0∞) (hgB : ∀ x, g x ≤ B)
    (Btop : B ≠ ∞)
    (κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d)))
    (a : EuclideanSpace ℝ (Fin m)) :
    |(∫⁻ y, g y ∂((multivariateGaussian a 1).bind κ.1)).toReal -
      (∫⁻ y, g y ∂((multivariateGaussian 0 1).bind κ.1)).toReal| ≤
      B.toReal * ∫ z, |gaussianLikelihood a z - 1|
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  letI : IsMarkovKernel κ.1 := κ.2
  let H : EuclideanSpace ℝ (Fin m) → ℝ≥0∞ := fun z => ∫⁻ y, g y ∂(κ.1 z)
  have hHmeas : Measurable H := hg.lintegral_kernel
  have hHB : ∀ z, H z ≤ B := by
    intro z
    calc
      H z ≤ ∫⁻ _y, B ∂(κ.1 z) := lintegral_mono fun y => hgB y
      _ = B := by simp
  have hHtop : ∀ z, H z ≠ ∞ := fun z => ne_of_lt ((hHB z).trans_lt (lt_top_iff_ne_top.mpr Btop))
  have hunfold (v : EuclideanSpace ℝ (Fin m)) :
      (∫⁻ y, g y ∂((multivariateGaussian v 1).bind κ.1)).toReal =
        (∫ z, (H z).toReal ∂multivariateGaussian v 1) := by
    rw [Measure.lintegral_bind κ.1.measurable.aemeasurable hg.aemeasurable]
    symm
    exact integral_toReal hHmeas.aemeasurable (Filter.Eventually.of_forall fun z =>
      lt_top_iff_ne_top.mpr (hHtop z))
  rw [hunfold a, hunfold 0]
  have hden : multivariateGaussian a (1 : Matrix (Fin m) (Fin m) ℝ) =
      (stdGaussian (EuclideanSpace ℝ (Fin m))).withDensity
        (fun z => ENNReal.ofReal (gaussianLikelihood a z)) :=
    (stdGaussian_withDensity_gaussianLikelihood a).symm
  have hzero : multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1 =
      stdGaussian (EuclideanSpace ℝ (Fin m)) := by simp
  rw [hden, hzero, integral_withDensity_eq_integral_toReal_smul
    (by unfold gaussianLikelihood; fun_prop)
    (Filter.Eventually.of_forall fun z => lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)]
  have hHint : Integrable (fun z => (H z).toReal)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    refine (integrable_const B.toReal).mono' hHmeas.ennreal_toReal.aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono Btop (hHB z)
  have hqH : Integrable (fun z => gaussianLikelihood a z * (H z).toReal)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    have hnonneg : ∀ z, 0 ≤ gaussianLikelihood a z := fun z => (Real.exp_pos _).le
    have hm : Measurable (fun z => ENNReal.ofReal (gaussianLikelihood a z)) := by
      unfold gaussianLikelihood
      fun_prop
    have hfin : ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin m)),
        ENNReal.ofReal (gaussianLikelihood a z) < ∞ :=
      Filter.Eventually.of_forall fun z => lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
    have hHi : Integrable (fun z => (H z).toReal)
        ((stdGaussian (EuclideanSpace ℝ (Fin m))).withDensity
          (fun z => ENNReal.ofReal (gaussianLikelihood a z))) := by
      rw [stdGaussian_withDensity_gaussianLikelihood a]
      refine (integrable_const B.toReal).mono'
        hHmeas.ennreal_toReal.aestronglyMeasurable ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono Btop (hHB z)
    have hprod := (integrable_withDensity_iff hm hfin).mp hHi
    simpa only [ENNReal.toReal_ofReal (hnonneg _), mul_comm] using hprod
  simp_rw [ENNReal.toReal_ofReal (show 0 ≤ gaussianLikelihood a _ by
    exact (Real.exp_pos _).le), smul_eq_mul]
  rw [← integral_sub hqH hHint]
  have hq : Integrable (gaussianLikelihood a)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_gaussianLikelihood]
    norm_num
  have habsint : Integrable (fun z => |gaussianLikelihood a z - 1|)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    (hq.sub (integrable_const 1)).abs
  calc
    |∫ z, gaussianLikelihood a z * (H z).toReal - (H z).toReal
        ∂stdGaussian (EuclideanSpace ℝ (Fin m))| ≤
        ∫ z, |gaussianLikelihood a z * (H z).toReal - (H z).toReal|
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) :=
      by simpa [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (fun z => gaussianLikelihood a z * (H z).toReal - (H z).toReal))
    _ ≤ ∫ z, B.toReal * |gaussianLikelihood a z - 1|
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun z => abs_nonneg _
      · exact habsint.const_mul _
      · filter_upwards with z
        have hz : (H z).toReal ≤ B.toReal := ENNReal.toReal_mono Btop (hHB z)
        rw [show gaussianLikelihood a z * (H z).toReal - (H z).toReal =
          (gaussianLikelihood a z - 1) * (H z).toReal by ring, abs_mul,
          abs_of_nonneg ENNReal.toReal_nonneg]
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left hz (abs_nonneg (gaussianLikelihood a z - 1)))
    _ = B.toReal * ∫ z, |gaussianLikelihood a z - 1|
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
      rw [integral_const_mul]

private theorem multivariateGaussian_map_add_left
    (u v : EuclideanSpace ℝ (Fin m)) :
    (multivariateGaussian v (1 : Matrix (Fin m) (Fin m) ℝ)).map (fun x => u + x) =
      multivariateGaussian (u + v) (1 : Matrix (Fin m) (Fin m) ℝ) := by
  unfold multivariateGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [add_assoc]

private theorem abs_lintegral_bind_two_shifts_le {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hg : Measurable g)
    (B : ℝ≥0∞) (hgB : ∀ x, g x ≤ B) (Btop : B ≠ ∞)
    (κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d)))
    (h k : EuclideanSpace ℝ (Fin m)) :
    |(∫⁻ y, g y ∂((multivariateGaussian h 1).bind κ.1)).toReal -
      (∫⁻ y, g y ∂((multivariateGaussian k 1).bind κ.1)).toReal| ≤
      B.toReal * ∫ z, |gaussianLikelihood (h - k) z - 1|
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  letI : IsMarkovKernel κ.1 := κ.2
  let shift : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun z => k + z
  have hshift : Measurable shift := by fun_prop
  let κ' : Kernel (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin d)) :=
    κ.1.comap shift hshift
  letI : IsMarkovKernel κ' := Kernel.IsMarkovKernel.comap κ.1 hshift
  let κM : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d)) := ⟨κ', inferInstance⟩
  have heq (a : EuclideanSpace ℝ (Fin m)) :
      ∫⁻ y, g y ∂((multivariateGaussian a 1).bind κ') =
        ∫⁻ y, g y ∂((multivariateGaussian (k + a) 1).bind κ.1) := by
    rw [Measure.lintegral_bind κ'.measurable.aemeasurable hg.aemeasurable,
      Measure.lintegral_bind κ.1.measurable.aemeasurable hg.aemeasurable,
      ← multivariateGaussian_map_add_left k a,
      lintegral_map (hg.lintegral_kernel) hshift]
    rfl
  have hbound := abs_lintegral_bind_shift_le g hg B hgB Btop κM (h - k)
  rw [heq, heq] at hbound
  have hkh : k + (h - k) = h := by abel
  rw [hkh, add_zero] at hbound
  exact hbound

private theorem abs_lintegral_two_shifts_le
    (g : EuclideanSpace ℝ (Fin m) → ℝ≥0∞) (hg : Measurable g)
    (B : ℝ≥0∞) (hgB : ∀ x, g x ≤ B) (Btop : B ≠ ∞)
    (h k : EuclideanSpace ℝ (Fin m)) :
    |(∫⁻ y, g y ∂(multivariateGaussian h 1)).toReal -
      (∫⁻ y, g y ∂(multivariateGaussian k 1)).toReal| ≤
      B.toReal * ∫ z, |gaussianLikelihood (h - k) z - 1|
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let shift : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun z => k + z
  let H : EuclideanSpace ℝ (Fin m) → ℝ≥0∞ := fun z => g (shift z)
  have hshift : Measurable shift := by fun_prop
  have hH : Measurable H := hg.comp hshift
  have hHB : ∀ z, H z ≤ B := fun z => hgB _
  have hden (a : EuclideanSpace ℝ (Fin m)) :
      multivariateGaussian a (1 : Matrix (Fin m) (Fin m) ℝ) =
        (stdGaussian (EuclideanSpace ℝ (Fin m))).withDensity
          (fun z => ENNReal.ofReal (gaussianLikelihood a z)) :=
    (stdGaussian_withDensity_gaussianLikelihood a).symm
  have hHtop : ∀ z, H z ≠ ∞ := fun z =>
    ne_of_lt ((hHB z).trans_lt (lt_top_iff_ne_top.mpr Btop))
  have hunfold (a : EuclideanSpace ℝ (Fin m)) :
      (∫⁻ z, H z ∂(multivariateGaussian a 1)).toReal =
        ∫ z, (H z).toReal ∂multivariateGaussian a 1 := by
    symm
    exact integral_toReal hH.aemeasurable
      (Filter.Eventually.of_forall fun z => lt_top_iff_ne_top.mpr (hHtop z))
  have hzero : multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1 =
      stdGaussian (EuclideanSpace ℝ (Fin m)) := by simp
  have hbase :
      |(∫⁻ z, H z ∂(multivariateGaussian (h - k) 1)).toReal -
        (∫⁻ z, H z ∂(multivariateGaussian 0 1)).toReal| ≤
        B.toReal * ∫ z, |gaussianLikelihood (h - k) z - 1|
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
    rw [hunfold, hunfold, hden, hzero,
      integral_withDensity_eq_integral_toReal_smul
        (by unfold gaussianLikelihood; fun_prop)
        (Filter.Eventually.of_forall fun z =>
          lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)]
    have hHint : Integrable (fun z => (H z).toReal)
        (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
      refine (integrable_const B.toReal).mono'
        hH.ennreal_toReal.aestronglyMeasurable ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono Btop (hHB z)
    have hqH : Integrable
        (fun z => gaussianLikelihood (h - k) z * (H z).toReal)
        (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
      have hnonneg : ∀ z, 0 ≤ gaussianLikelihood (h - k) z := fun z =>
        (Real.exp_pos _).le
      have hm : Measurable
          (fun z => ENNReal.ofReal (gaussianLikelihood (h - k) z)) := by
        unfold gaussianLikelihood
        fun_prop
      have hfin : ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin m)),
          ENNReal.ofReal (gaussianLikelihood (h - k) z) < ∞ :=
        Filter.Eventually.of_forall fun z =>
          lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
      have hHi : Integrable (fun z => (H z).toReal)
          ((stdGaussian (EuclideanSpace ℝ (Fin m))).withDensity
            (fun z => ENNReal.ofReal (gaussianLikelihood (h - k) z))) := by
        rw [stdGaussian_withDensity_gaussianLikelihood (h - k)]
        refine (integrable_const B.toReal).mono'
          hH.ennreal_toReal.aestronglyMeasurable ?_
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_mono Btop (hHB z)
      have hprod := (integrable_withDensity_iff hm hfin).mp hHi
      simpa only [ENNReal.toReal_ofReal (hnonneg _), mul_comm] using hprod
    simp_rw [ENNReal.toReal_ofReal
      (show 0 ≤ gaussianLikelihood (h - k) _ by exact (Real.exp_pos _).le),
      smul_eq_mul]
    rw [← integral_sub hqH hHint]
    have hq : Integrable (gaussianLikelihood (h - k))
        (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
      apply Integrable.of_integral_ne_zero
      rw [integral_gaussianLikelihood]
      norm_num
    have habsint : Integrable
        (fun z => |gaussianLikelihood (h - k) z - 1|)
        (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
      (hq.sub (integrable_const 1)).abs
    calc
      |∫ z, gaussianLikelihood (h - k) z * (H z).toReal - (H z).toReal
          ∂stdGaussian (EuclideanSpace ℝ (Fin m))| ≤
          ∫ z, |gaussianLikelihood (h - k) z * (H z).toReal - (H z).toReal|
            ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun z => gaussianLikelihood (h - k) z * (H z).toReal - (H z).toReal)
      _ ≤ ∫ z, B.toReal * |gaussianLikelihood (h - k) z - 1|
            ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun z => abs_nonneg _
        · exact habsint.const_mul _
        · filter_upwards with z
          have hz : (H z).toReal ≤ B.toReal := ENNReal.toReal_mono Btop (hHB z)
          rw [show gaussianLikelihood (h - k) z * (H z).toReal - (H z).toReal =
            (gaussianLikelihood (h - k) z - 1) * (H z).toReal by ring,
            abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          simpa [mul_comm] using
            mul_le_mul_of_nonneg_left hz (abs_nonneg (gaussianLikelihood (h - k) z - 1))
      _ = B.toReal * ∫ z, |gaussianLikelihood (h - k) z - 1|
            ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
        rw [integral_const_mul]
  have heq (a : EuclideanSpace ℝ (Fin m)) :
      ∫⁻ z, H z ∂(multivariateGaussian a 1) =
        ∫⁻ z, g z ∂(multivariateGaussian (k + a) 1) := by
    rw [← multivariateGaussian_map_add_left k a,
      lintegral_map hg hshift]
  rw [heq, heq, add_zero] at hbase
  have hkh : k + (h - k) = h := by abel
  rwa [hkh] at hbase

/-- Bounded uniformly continuous loss gives uniform continuity of Gaussian
shift risk in the parameter, uniformly over measurable decisions. -/
theorem gaussianShiftRisk_uniformContinuous
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (ℓ : ℝ → ℝ≥0∞)
    (_hfinite : ∀ x, ℓ x ≠ ∞)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (_huc : UniformContinuous fun x => (ℓ x).toReal) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (T : EuclideanSpace ℝ (Fin m) → ℝ), Measurable T →
      ∀ h k, dist h k < δ →
        |(∫⁻ X, ℓ (T X - A h)
            ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ))).toReal -
          (∫⁻ X, ℓ (T X - A k)
            ∂(multivariateGaussian k (1 : Matrix (Fin m) (Fin m) ℝ))).toReal| < ε := by
  intro ε hε
  rcases _hbdd with ⟨B, hBtop, hB⟩
  let e : ℝ := ε / 2
  have he : 0 < e := half_pos hε
  rcases (Metric.uniformContinuous_iff.mp _huc) e he with ⟨η, hη, hloss⟩
  let δA : ℝ := η / (‖A‖ + 1)
  have hδA : 0 < δA := div_pos hη (by positivity)
  let tvmod : EuclideanSpace ℝ (Fin m) → ℝ := fun a =>
    B.toReal * Real.sqrt (Real.exp (‖a‖ ^ 2) - 1)
  have htvcont : Continuous tvmod := by
    dsimp [tvmod]
    fun_prop
  have htvzero : tvmod 0 < e := by simp [tvmod, he]
  have htvopen : IsOpen {a | tvmod a < e} := isOpen_lt htvcont continuous_const
  rcases Metric.isOpen_iff.mp htvopen 0 htvzero with ⟨δT, hδT, hballT⟩
  refine ⟨min δA δT, lt_min hδA hδT, ?_⟩
  intro T hT h k hhk
  have hdistA : dist (A h) (A k) < η := by
    calc
      dist (A h) (A k) ≤ ‖A‖ * dist h k := A.dist_le_opNorm h k
      _ ≤ (‖A‖ + 1) * dist h k := mul_le_mul_of_nonneg_right
        (by linarith [norm_nonneg A]) dist_nonneg
      _ < (‖A‖ + 1) * δA := mul_lt_mul_of_pos_left
        (hhk.trans_le (min_le_left _ _)) (by positivity)
      _ = η := by dsimp [δA]; field_simp
  have hpoint : ∀ y : ℝ,
      |(ℓ (y - A h)).toReal - (ℓ (y - A k)).toReal| < e := by
    intro y
    have hd : dist (y - A h) (y - A k) < η := by
      change |(y - A h) - (y - A k)| < η
      change |A h - A k| < η at hdistA
      rw [show (y - A h) - (y - A k) = -(A h - A k) by ring, abs_neg]
      exact hdistA
    simpa [Real.dist_eq] using hloss hd
  have htvarg : h - k ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) δT := by
    change dist (h - k) 0 < δT
    simpa [dist_eq_norm] using hhk.trans_le (min_le_right _ _)
  have htvsmall : tvmod (h - k) < e := hballT htvarg
  let gh : EuclideanSpace ℝ (Fin m) → ℝ≥0∞ := fun y => ℓ (T y - A h)
  let gk : EuclideanSpace ℝ (Fin m) → ℝ≥0∞ := fun y => ℓ (T y - A k)
  have hℓmeas : Measurable ℓ := by
    have hm := _huc.continuous.measurable.ennreal_ofReal
    convert hm using 1
    funext x
    exact (ENNReal.ofReal_toReal (_hfinite x)).symm
  have hgh : Measurable gh := hℓmeas.comp (hT.sub measurable_const)
  have hgk : Measurable gk := hℓmeas.comp (hT.sub measurable_const)
  have hghB : ∀ y, gh y ≤ B := fun y => hB _
  have hgkB : ∀ y, gk y ≤ B := fun y => hB _
  let μh := multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)
  let μk := multivariateGaussian k (1 : Matrix (Fin m) (Fin m) ℝ)
  have hfirst : |(∫⁻ y, gh y ∂μh).toReal - (∫⁻ y, gh y ∂μk).toReal| < e := by
    have hb := abs_lintegral_two_shifts_le gh hgh B hghB hBtop.ne h k
    refine hb.trans_lt ?_
    calc
      B.toReal * ∫ z, |gaussianLikelihood (h - k) z - 1|
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) ≤
          B.toReal * (Real.exp (‖h - k‖ ^ 2) - 1) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (integral_abs_gaussianLikelihood_sub_one_le (h - k)) ENNReal.toReal_nonneg
      _ = tvmod (h - k) := by rw [← Real.sqrt_eq_rpow]
      _ < e := htvsmall
  have hsecond : |(∫⁻ y, gh y ∂μk).toReal - (∫⁻ y, gk y ∂μk).toReal| ≤ e := by
    haveI : IsProbabilityMeasure μk := by dsimp [μk]; infer_instance
    have hghtop : ∀ᵐ y ∂μk, gh y < ∞ := Filter.Eventually.of_forall fun y =>
      lt_top_iff_ne_top.mpr (ne_of_lt ((hghB y).trans_lt hBtop))
    have hgktop : ∀ᵐ y ∂μk, gk y < ∞ := Filter.Eventually.of_forall fun y =>
      lt_top_iff_ne_top.mpr (ne_of_lt ((hgkB y).trans_lt hBtop))
    have hghint : Integrable (fun y => (gh y).toReal) μk :=
      (integrable_const B.toReal).mono' hgh.ennreal_toReal.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_mono hBtop.ne (hghB y))
    have hgkint : Integrable (fun y => (gk y).toReal) μk :=
      (integrable_const B.toReal).mono' hgk.ennreal_toReal.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_mono hBtop.ne (hgkB y))
    rw [← integral_toReal hgh.aemeasurable hghtop,
      ← integral_toReal hgk.aemeasurable hgktop, ← integral_sub hghint hgkint]
    calc
      |∫ y, (gh y).toReal - (gk y).toReal ∂μk| ≤
          ∫ y, |(gh y).toReal - (gk y).toReal| ∂μk := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun y => (gh y).toReal - (gk y).toReal)
      _ ≤ ∫ _y, e ∂μk := by
        apply integral_mono
        · exact (integrable_const e).mono'
            (hgh.ennreal_toReal.sub hgk.ennreal_toReal).abs.aestronglyMeasurable
            (Filter.Eventually.of_forall fun y => by
              simpa [Real.norm_eq_abs, gh, gk] using (hpoint (T y)).le)
        · exact integrable_const e
        · intro y
          exact (hpoint (T y)).le
      _ = e := by simp
  change |(∫⁻ y, gh y ∂μh).toReal - (∫⁻ y, gk y ∂μk).toReal| < ε
  calc
    |(∫⁻ y, gh y ∂μh).toReal - (∫⁻ y, gk y ∂μk).toReal| ≤
        |(∫⁻ y, gh y ∂μh).toReal - (∫⁻ y, gh y ∂μk).toReal| +
        |(∫⁻ y, gh y ∂μk).toReal - (∫⁻ y, gk y ∂μk).toReal| :=
      abs_sub_le _ _ _
    _ < e + e := add_lt_add_of_lt_of_le hfirst hsecond
    _ = ε := by dsimp [e]; ring

/-- A cone-supported finite prior quantization approximates Bayes risk for
finite bounded uniformly continuous loss. -/
theorem exists_finite_quantization
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (π : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure π]
    (_hsupp : π C = 1)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (ℓ : ℝ → ℝ≥0∞)
    (_hfinite : ∀ x, ℓ x ≠ ∞)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (_huc : UniformContinuous fun x => (ℓ x).toReal)
    (ε : ℝ≥0∞) (_hε : 0 < ε) :
    ∃ I : Finset (EuclideanSpace ℝ (Fin m)), (I : Set _) ⊆ C ∧
      measurableBayesRisk π A ℓ ≤
        (⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
          ⨆ h ∈ I, ∫⁻ X, ℓ (T.1 X - A h)
            ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ))) + ε := by
  classical
  have hC : C.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h] at _hsupp
    simp at _hsupp
  by_cases hεtop : ε = ∞
  · rcases hC with ⟨c, hc⟩
    refine ⟨{c}, by simpa, ?_⟩
    rw [hεtop, add_top]
    exact le_top
  let e : ℝ≥0∞ := ε / 2
  have he : 0 < e := ENNReal.half_pos _hε.ne'
  have hetop : e ≠ ∞ := ENNReal.div_ne_top hεtop (by norm_num)
  have heReal : 0 < e.toReal := ENNReal.toReal_pos he.ne' hetop
  rcases _hbdd with ⟨B, hBtop, hB⟩
  rcases ENNReal.exists_pos_mul_lt hBtop.ne he.ne' with ⟨δ, hδ, hδB⟩
  have htight : IsTightMeasureSet {π} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  rcases htight δ hδ with ⟨K, hK, hKtail⟩
  have hKtail : π Kᶜ ≤ δ := hKtail π (by simp)
  let K' : Set (EuclideanSpace ℝ (Fin m)) := K ∩ Measure.support π
  have hK'comp : π K'ᶜ ≤ δ := by
    calc
      π K'ᶜ ≤ π Kᶜ + π (Measure.support π)ᶜ := by
        rw [show K'ᶜ = Kᶜ ∪ (Measure.support π)ᶜ by
          ext x
          simp only [K', Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union]
          tauto]
        exact measure_union_le _ _
      _ ≤ δ := by rw [Measure.measure_compl_support, add_zero]; exact hKtail
  rcases gaussianShiftRisk_uniformContinuous A ℓ _hfinite
    ⟨B, hBtop, hB⟩ _huc e.toReal heReal with ⟨η, hη, huc⟩
  have hK'tb : TotallyBounded K' :=
    TotallyBounded.subset Set.inter_subset_left hK.totallyBounded
  rcases Metric.finite_approx_of_totallyBounded hK'tb (η / 2) (half_pos hη) with
    ⟨t, htK, htfin, hcover⟩
  have hcenter (x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ t) :
      ∃ c ∈ C, c ∈ Metric.ball x (η / 2) := by
    have hxsupp : x ∈ Measure.support π := (htK hx).2
    have hballpos : 0 < π (Metric.ball x (η / 2)) :=
      (Measure.mem_support_iff_forall x).mp hxsupp _
        (Metric.ball_mem_nhds x (half_pos hη))
    by_contra hempty
    have hsub : C ⊆ (Metric.ball x (η / 2))ᶜ := by
      intro z hz hzb
      exact hempty ⟨z, hz, hzb⟩
    have hle : π C ≤ π (Metric.ball x (η / 2))ᶜ := measure_mono hsub
    have hcompl : π (Metric.ball x (η / 2))ᶜ < 1 := by
      have hballtop : π (Metric.ball x (η / 2)) ≠ ∞ := by
        apply ne_of_lt
        calc
          π (Metric.ball x (η / 2)) ≤ π Set.univ :=
            measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
          _ < ∞ := ENNReal.one_lt_top
      rw [measure_compl measurableSet_ball hballtop, measure_univ]
      apply ENNReal.sub_lt_self
      · simp
      · simp
      · exact hballpos.ne'
    rw [_hsupp] at hle
    exact (not_lt_of_ge hle) hcompl
  let c : ↥t → EuclideanSpace ℝ (Fin m) := fun x =>
    Classical.choose (hcenter x x.property)
  have hcC : ∀ x : ↥t, c x ∈ C := fun x =>
    (Classical.choose_spec (hcenter x x.property)).1
  have hcball : ∀ x : ↥t,
      c x ∈ Metric.ball (x : EuclideanSpace ℝ (Fin m)) (η / 2) := fun x =>
    (Classical.choose_spec (hcenter x x.property)).2
  letI : Fintype ↥t := htfin.fintype
  let I : Finset (EuclideanSpace ℝ (Fin m)) :=
    Set.Finite.toFinset (Set.finite_range c)
  have hIC : (I : Set _) ⊆ C := by
    intro z hz
    have hz : z ∈ Set.range c := by simpa [I] using hz
    rcases hz with ⟨x, rfl⟩
    exact hcC x
  have hcoverI : K' ⊆ ⋃ z ∈ (I : Set _), Metric.ball z η := by
    intro y hy
    rcases Set.mem_iUnion₂.mp (hcover hy) with ⟨x, hx, hyx⟩
    let xs : ↥t := ⟨x, hx⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨c xs, ?_, ?_⟩
    · simp [I]
    · change dist y (c xs) < η
      calc
        dist y (c xs) ≤ dist y x + dist x (c xs) := dist_triangle _ _ _
        _ < η / 2 + η / 2 := add_lt_add hyx (by
          simpa only [Metric.mem_ball, dist_comm] using hcball xs)
        _ = η := by ring
  let D : Set (EuclideanSpace ℝ (Fin m)) := ⋃ z ∈ I, Metric.ball z η
  have hD : MeasurableSet D := by
    dsimp [D]
    exact I.measurableSet_biUnion fun z hz => measurableSet_ball
  have hDcomp : π Dᶜ ≤ δ :=
    (measure_mono (Set.compl_subset_compl.mpr hcoverI)).trans hK'comp
  refine ⟨I, hIC, ?_⟩
  unfold measurableBayesRisk
  calc
    (⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
      ∫⁻ h, ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1) ∂π) ≤
        (⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
          (⨆ h ∈ I, ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1)) + ε) := by
      apply iInf_mono
      intro T
      let S : ℝ≥0∞ :=
        ⨆ h ∈ I, ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1)
      have hriskB : ∀ h,
          ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1) ≤ B := by
        intro h
        calc
          ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1) ≤
              ∫⁻ _X, B ∂(multivariateGaussian h 1) :=
            lintegral_mono fun X => hB _
          _ = B := by simp
      have hin : ∀ h ∈ D,
          ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1) ≤ S + e := by
        intro h hh
        rcases Set.mem_iUnion₂.mp hh with ⟨z, hzI, hhz⟩
        have huz := huc T.1 T.2 h z hhz
        have hrtop : (∫⁻ X, ℓ (T.1 X - A h)
            ∂(multivariateGaussian h 1)) ≠ ∞ :=
          ne_of_lt ((hriskB h).trans_lt hBtop)
        have hztop : (∫⁻ X, ℓ (T.1 X - A z)
            ∂(multivariateGaussian z 1)) ≠ ∞ :=
          ne_of_lt ((hriskB z).trans_lt hBtop)
        have hleReal : (∫⁻ X, ℓ (T.1 X - A h)
              ∂(multivariateGaussian h 1)).toReal ≤
            (∫⁻ X, ℓ (T.1 X - A z)
              ∂(multivariateGaussian z 1)).toReal + e.toReal := by
          linarith [le_abs_self ((∫⁻ X, ℓ (T.1 X - A h)
            ∂(multivariateGaussian h 1)).toReal -
            (∫⁻ X, ℓ (T.1 X - A z)
              ∂(multivariateGaussian z 1)).toReal)]
        have hze : (∫⁻ X, ℓ (T.1 X - A z)
              ∂(multivariateGaussian z 1)) + e ≠ ∞ :=
          ENNReal.add_ne_top.mpr ⟨hztop, hetop⟩
        have hle : (∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1)) ≤
            (∫⁻ X, ℓ (T.1 X - A z) ∂(multivariateGaussian z 1)) + e := by
          apply (ENNReal.toReal_le_toReal hrtop hze).mp
          simpa [ENNReal.toReal_add hztop hetop] using hleReal
        have hzS : (∫⁻ X, ℓ (T.1 X - A z) ∂(multivariateGaussian z 1)) ≤ S := by
          dsimp [S]
          exact le_iSup_of_le z (le_iSup
            (fun _ : z ∈ I => ∫⁻ X, ℓ (T.1 X - A z) ∂(multivariateGaussian z 1)) hzI)
        exact hle.trans (add_le_add_left hzS e)
      rw [← lintegral_add_compl
        (fun h => ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1)) hD]
      calc
        (∫⁻ h in D, ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1) ∂π) +
            ∫⁻ h in Dᶜ, ∫⁻ X, ℓ (T.1 X - A h)
              ∂(multivariateGaussian h 1) ∂π ≤
            (∫⁻ _h in D, S + e ∂π) + ∫⁻ _h in Dᶜ, B ∂π :=
          add_le_add
            (setLIntegral_mono' hD (fun h hh => hin h hh))
            (setLIntegral_mono' hD.compl (fun h hh => hriskB h))
        _ = (S + e) * π D + B * π Dᶜ := by
          rw [setLIntegral_const, setLIntegral_const]
        _ ≤ (S + e) + e := by
          apply add_le_add
          · exact mul_le_of_le_one_right (by positivity) (by
              calc
                π D ≤ π Set.univ := measure_mono (Set.subset_univ D)
                _ = 1 := measure_univ)
          · calc
              B * π Dᶜ ≤ B * δ := mul_le_mul_right hDcomp B
              _ = δ * B := mul_comm _ _
              _ ≤ e := hδB.le
        _ = S + ε := by rw [add_assoc, ENNReal.add_halves]
    _ = (⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
          ⨆ h ∈ I, ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1)) + ε :=
      (ENNReal.iInf_add).symm

/-- Bounded uniformly-continuous vector loss gives risk continuity uniformly
over all randomized Markov decisions. -/
theorem gaussianShiftRisk_uniformContinuous_vec {d : ℕ}
    (A : Matrix (Fin d) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hfinite : ∀ x, ℓ x ≠ ∞)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (_huc : UniformContinuous fun x => (ℓ x).toReal) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin d)),
      ∀ h k, dist h k < δ →
        |(gaussianShiftKernelRiskVec A ℓ κ h).toReal -
          (gaussianShiftKernelRiskVec A ℓ κ k).toReal| < ε := by
  intro ε hε
  rcases _hbdd with ⟨B, hBtop, hB⟩
  let e : ℝ := ε / 2
  have he : 0 < e := half_pos hε
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    matrixToEuclideanCLMRect A
  rcases (Metric.uniformContinuous_iff.mp _huc) e he with ⟨η, hη, hloss⟩
  let δL : ℝ := η / (‖L‖ + 1)
  have hδL : 0 < δL := div_pos hη (by positivity)
  let tvmod : EuclideanSpace ℝ (Fin m) → ℝ := fun a =>
    B.toReal * Real.sqrt (Real.exp (‖a‖ ^ 2) - 1)
  have htvcont : Continuous tvmod := by
    dsimp [tvmod]
    fun_prop
  have htvzero : tvmod 0 < e := by
    simp [tvmod, he]
  have htvopen : IsOpen {a | tvmod a < e} :=
    isOpen_lt htvcont continuous_const
  rcases Metric.isOpen_iff.mp htvopen 0 htvzero with ⟨δT, hδT, hballT⟩
  refine ⟨min δL δT, lt_min hδL hδT, ?_⟩
  intro κ h k hhk
  letI : IsMarkovKernel κ.1 := κ.2
  have hdistL : dist (L h) (L k) < η := by
    calc
      dist (L h) (L k) ≤ ‖L‖ * dist h k := L.dist_le_opNorm h k
      _ ≤ (‖L‖ + 1) * dist h k := mul_le_mul_of_nonneg_right
        (by linarith [norm_nonneg L]) dist_nonneg
      _ < (‖L‖ + 1) * δL := mul_lt_mul_of_pos_left
        (hhk.trans_le (min_le_left _ _)) (by positivity)
      _ = η := by dsimp [δL]; field_simp
  have hpoint : ∀ y : EuclideanSpace ℝ (Fin d),
      |(ℓ (y - L h)).toReal - (ℓ (y - L k)).toReal| < e := by
    intro y
    have hd : dist (y - L h) (y - L k) < η := by
      simpa [dist_eq_norm, norm_sub_rev] using hdistL
    simpa [Real.dist_eq] using hloss hd
  have htvarg : h - k ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) δT := by
    change dist (h - k) 0 < δT
    simpa [dist_eq_norm] using hhk.trans_le (min_le_right _ _)
  have htvsmall : tvmod (h - k) < e := hballT htvarg
  let gh : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun y => ℓ (y - L h)
  let gk : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun y => ℓ (y - L k)
  let μh := (multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)).bind κ.1
  let μk := (multivariateGaussian k (1 : Matrix (Fin m) (Fin m) ℝ)).bind κ.1
  have hℓmeas : Measurable ℓ := by
    have hm := _huc.continuous.measurable.ennreal_ofReal
    convert hm using 1
    funext x
    exact (ENNReal.ofReal_toReal (_hfinite x)).symm
  have hgh : Measurable gh := hℓmeas.comp (measurable_id.sub measurable_const)
  have hgk : Measurable gk := hℓmeas.comp (measurable_id.sub measurable_const)
  have hghB : ∀ y, gh y ≤ B := fun y => hB _
  have hgkB : ∀ y, gk y ≤ B := fun y => hB _
  have hfirst : |(∫⁻ y, gh y ∂μh).toReal - (∫⁻ y, gh y ∂μk).toReal| < e := by
    have hb := abs_lintegral_bind_two_shifts_le gh hgh B hghB hBtop.ne κ h k
    refine hb.trans_lt ?_
    calc
      B.toReal * ∫ z, |gaussianLikelihood (h - k) z - 1|
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) ≤
          B.toReal * (Real.exp (‖h - k‖ ^ 2) - 1) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (integral_abs_gaussianLikelihood_sub_one_le (h - k))
          ENNReal.toReal_nonneg
      _ = tvmod (h - k) := by rw [← Real.sqrt_eq_rpow]
      _ < e := htvsmall
  have hsecond : |(∫⁻ y, gh y ∂μk).toReal - (∫⁻ y, gk y ∂μk).toReal| ≤ e := by
    haveI : IsProbabilityMeasure μk := by dsimp [μk]; infer_instance
    have hghtop : ∀ᵐ y ∂μk, gh y < ∞ := Filter.Eventually.of_forall fun y =>
      lt_top_iff_ne_top.mpr (ne_of_lt ((hghB y).trans_lt hBtop))
    have hgktop : ∀ᵐ y ∂μk, gk y < ∞ := Filter.Eventually.of_forall fun y =>
      lt_top_iff_ne_top.mpr (ne_of_lt ((hgkB y).trans_lt hBtop))
    have hghint : Integrable (fun y => (gh y).toReal) μk :=
      (integrable_const B.toReal).mono' hgh.ennreal_toReal.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_mono hBtop.ne (hghB y))
    have hgkint : Integrable (fun y => (gk y).toReal) μk :=
      (integrable_const B.toReal).mono' hgk.ennreal_toReal.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_mono hBtop.ne (hgkB y))
    rw [← integral_toReal hgh.aemeasurable hghtop,
      ← integral_toReal hgk.aemeasurable hgktop, ← integral_sub hghint hgkint]
    calc
        |∫ y, (gh y).toReal - (gk y).toReal ∂μk| ≤
            ∫ y, |(gh y).toReal - (gk y).toReal| ∂μk := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun y => (gh y).toReal - (gk y).toReal)
        _ ≤ ∫ _y, e ∂μk := by
          apply integral_mono
          · exact (integrable_const e).mono'
              (hgh.ennreal_toReal.sub hgk.ennreal_toReal).abs.aestronglyMeasurable
              (Filter.Eventually.of_forall fun y => by
                simpa [Real.norm_eq_abs, gh, gk] using (hpoint y).le)
          · exact integrable_const e
          · intro y
            exact (hpoint y).le
        _ = e := by simp
  unfold gaussianShiftKernelRiskVec
  change |(∫⁻ y, gh y ∂μh).toReal - (∫⁻ y, gk y ∂μk).toReal| < ε
  calc
    |(∫⁻ y, gh y ∂μh).toReal - (∫⁻ y, gk y ∂μk).toReal| ≤
        |(∫⁻ y, gh y ∂μh).toReal - (∫⁻ y, gh y ∂μk).toReal| +
        |(∫⁻ y, gh y ∂μk).toReal - (∫⁻ y, gk y ∂μk).toReal| :=
      abs_sub_le _ _ _
    _ < e + e := add_lt_add_of_lt_of_le hfirst hsecond
    _ = ε := by dsimp [e]; ring

/-- A cone-supported prior admits a finite-support risk quantization for
randomized vector decisions. -/
theorem exists_finite_quantization_vec {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (π : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure π]
    (_hsupp : π C = 1)
    (A : Matrix (Fin d) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hfinite : ∀ x, ℓ x ≠ ∞)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (_huc : UniformContinuous fun x => (ℓ x).toReal)
    (ε : ℝ≥0∞) (_hε : 0 < ε) :
    ∃ I : Finset (EuclideanSpace ℝ (Fin m)), (I : Set _) ⊆ C ∧
      measurableBayesRiskVec π A ℓ ≤
        (⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
            (EuclideanSpace ℝ (Fin d)),
          ⨆ h ∈ I, gaussianShiftKernelRiskVec A ℓ κ h) + ε := by
  classical
  have hC : C.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h] at _hsupp
    simp at _hsupp
  by_cases hεtop : ε = ∞
  · rcases hC with ⟨c, hc⟩
    refine ⟨{c}, by simpa, ?_⟩
    rw [hεtop, add_top]
    exact le_top
  let e : ℝ≥0∞ := ε / 2
  have he : 0 < e := ENNReal.half_pos _hε.ne'
  have hetop : e ≠ ∞ := ENNReal.div_ne_top hεtop (by norm_num)
  have heReal : 0 < e.toReal := ENNReal.toReal_pos he.ne' hetop
  rcases _hbdd with ⟨B, hBtop, hB⟩
  rcases ENNReal.exists_pos_mul_lt hBtop.ne he.ne' with ⟨δ, hδ, hδB⟩
  have htight : IsTightMeasureSet {π} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  rcases htight δ hδ with ⟨K, hK, hKtail⟩
  have hKtail : π Kᶜ ≤ δ := hKtail π (by simp)
  let K' : Set (EuclideanSpace ℝ (Fin m)) := K ∩ Measure.support π
  have hK'comp : π K'ᶜ ≤ δ := by
    calc
      π K'ᶜ ≤ π Kᶜ + π (Measure.support π)ᶜ := by
        rw [show K'ᶜ = Kᶜ ∪ (Measure.support π)ᶜ by
          ext x
          simp only [K', Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union]
          tauto]
        exact measure_union_le _ _
      _ ≤ δ := by rw [Measure.measure_compl_support, add_zero]; exact hKtail
  rcases gaussianShiftRisk_uniformContinuous_vec A ℓ _hfinite
    ⟨B, hBtop, hB⟩ _huc e.toReal heReal with ⟨η, hη, huc⟩
  have hK'tb : TotallyBounded K' :=
    TotallyBounded.subset (Set.inter_subset_left) hK.totallyBounded
  rcases Metric.finite_approx_of_totallyBounded hK'tb (η / 2) (half_pos hη) with
    ⟨t, htK, htfin, hcover⟩
  have hcenter (x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ t) :
      ∃ c ∈ C, c ∈ Metric.ball x (η / 2) := by
    have hxsupp : x ∈ Measure.support π := (htK hx).2
    have hballpos : 0 < π (Metric.ball x (η / 2)) :=
      (Measure.mem_support_iff_forall x).mp hxsupp _
        (Metric.ball_mem_nhds x (half_pos hη))
    by_contra hempty
    have hsub : C ⊆ (Metric.ball x (η / 2))ᶜ := by
      intro z hz hzb
      exact hempty ⟨z, hz, hzb⟩
    have hle : π C ≤ π (Metric.ball x (η / 2))ᶜ := measure_mono hsub
    have hcompl : π (Metric.ball x (η / 2))ᶜ < 1 := by
      have hballtop : π (Metric.ball x (η / 2)) ≠ ∞ := by
        apply ne_of_lt
        calc
          π (Metric.ball x (η / 2)) ≤ π Set.univ :=
            measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
          _ < ∞ := ENNReal.one_lt_top
      rw [measure_compl measurableSet_ball hballtop, measure_univ]
      apply ENNReal.sub_lt_self
      · simp
      · simp
      · exact hballpos.ne'
    rw [_hsupp] at hle
    exact (not_lt_of_ge hle) hcompl
  let c : ↥t → EuclideanSpace ℝ (Fin m) := fun x =>
    Classical.choose (hcenter x x.property)
  have hcC : ∀ x : ↥t, c x ∈ C := fun x =>
    (Classical.choose_spec (hcenter x x.property)).1
  have hcball : ∀ x : ↥t, c x ∈ Metric.ball (x : EuclideanSpace ℝ (Fin m)) (η / 2) :=
    fun x => (Classical.choose_spec (hcenter x x.property)).2
  letI : Fintype ↥t := htfin.fintype
  let I : Finset (EuclideanSpace ℝ (Fin m)) := Set.Finite.toFinset (Set.finite_range c)
  have hIC : (I : Set _) ⊆ C := by
    intro z hz
    have hz : z ∈ Set.range c := by simpa [I] using hz
    rcases hz with ⟨x, rfl⟩
    exact hcC x
  have hcoverI : K' ⊆ ⋃ z ∈ (I : Set _), Metric.ball z η := by
    intro y hy
    rcases Set.mem_iUnion₂.mp (hcover hy) with ⟨x, hx, hyx⟩
    let xs : ↥t := ⟨x, hx⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨c xs, ?_, ?_⟩
    · simp [I]
    · change dist y (c xs) < η
      calc
        dist y (c xs) ≤ dist y x + dist x (c xs) := dist_triangle _ _ _
        _ < η / 2 + η / 2 := add_lt_add hyx (by
          simpa only [Metric.mem_ball, dist_comm] using hcball xs)
        _ = η := by ring
  let D : Set (EuclideanSpace ℝ (Fin m)) :=
    ⋃ z ∈ I, Metric.ball z η
  have hD : MeasurableSet D := by
    dsimp [D]
    exact I.measurableSet_biUnion fun z hz => measurableSet_ball
  have hDcomp : π Dᶜ ≤ δ :=
    (measure_mono (Set.compl_subset_compl.mpr hcoverI)).trans hK'comp
  refine ⟨I, hIC, ?_⟩
  unfold measurableBayesRiskVec
  calc
    (⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin d)),
      ∫⁻ h, gaussianShiftKernelRiskVec A ℓ κ h ∂π) ≤
      (⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin d)),
        (⨆ h ∈ I, gaussianShiftKernelRiskVec A ℓ κ h) + ε) := by
      apply iInf_mono
      intro κ
      letI : IsMarkovKernel κ.1 := κ.2
      let S : ℝ≥0∞ := ⨆ h ∈ I, gaussianShiftKernelRiskVec A ℓ κ h
      have hriskB : ∀ h, gaussianShiftKernelRiskVec A ℓ κ h ≤ B := by
        intro h
        unfold gaussianShiftKernelRiskVec
        calc
          ∫⁻ a, ℓ (a - matrixActionVec A h)
              ∂((multivariateGaussian h 1).bind κ.1) ≤
              ∫⁻ _a, B ∂((multivariateGaussian h 1).bind κ.1) :=
            lintegral_mono fun a => hB _
          _ = B := by simp
      have hin : ∀ h ∈ D, gaussianShiftKernelRiskVec A ℓ κ h ≤ S + e := by
        intro h hh
        rcases Set.mem_iUnion₂.mp hh with ⟨z, hzI, hhz⟩
        have huz := huc κ h z hhz
        have hrtop : gaussianShiftKernelRiskVec A ℓ κ h ≠ ∞ :=
          ne_of_lt ((hriskB h).trans_lt hBtop)
        have hztop : gaussianShiftKernelRiskVec A ℓ κ z ≠ ∞ :=
          ne_of_lt ((hriskB z).trans_lt hBtop)
        have hleReal : (gaussianShiftKernelRiskVec A ℓ κ h).toReal ≤
            (gaussianShiftKernelRiskVec A ℓ κ z).toReal + e.toReal := by
          linarith [le_abs_self ((gaussianShiftKernelRiskVec A ℓ κ h).toReal -
            (gaussianShiftKernelRiskVec A ℓ κ z).toReal)]
        have hze : gaussianShiftKernelRiskVec A ℓ κ z + e ≠ ∞ :=
          ENNReal.add_ne_top.mpr ⟨hztop, hetop⟩
        have hle : gaussianShiftKernelRiskVec A ℓ κ h ≤
            gaussianShiftKernelRiskVec A ℓ κ z + e := by
          apply (ENNReal.toReal_le_toReal hrtop hze).mp
          simpa [ENNReal.toReal_add hztop hetop] using hleReal
        have hzS : gaussianShiftKernelRiskVec A ℓ κ z ≤ S := by
          dsimp [S]
          exact le_iSup_of_le z (le_iSup (fun _ : z ∈ I =>
            gaussianShiftKernelRiskVec A ℓ κ z) hzI)
        exact hle.trans (add_le_add_left hzS e)
      rw [← lintegral_add_compl
        (fun h => gaussianShiftKernelRiskVec A ℓ κ h) hD]
      calc
        (∫⁻ h in D, gaussianShiftKernelRiskVec A ℓ κ h ∂π) +
            ∫⁻ h in Dᶜ, gaussianShiftKernelRiskVec A ℓ κ h ∂π ≤
            (∫⁻ _h in D, S + e ∂π) + ∫⁻ _h in Dᶜ, B ∂π :=
          add_le_add
            (setLIntegral_mono' hD (fun h hh => hin h hh))
            (setLIntegral_mono' hD.compl (fun h hh => hriskB h))
        _ = (S + e) * π D + B * π Dᶜ := by
          rw [setLIntegral_const, setLIntegral_const]
        _ ≤ (S + e) + e := by
          apply add_le_add
          · exact mul_le_of_le_one_right (by positivity) (by
              calc
                π D ≤ π Set.univ := measure_mono (Set.subset_univ D)
                _ = 1 := measure_univ)
          · calc
              B * π Dᶜ ≤ B * δ := mul_le_mul_right hDcomp B
              _ = δ * B := mul_comm _ _
              _ ≤ e := hδB.le
        _ = S + ε := by rw [add_assoc, ENNReal.add_halves]
    _ = (⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin d)),
        ⨆ h ∈ I, gaussianShiftKernelRiskVec A ℓ κ h) + ε :=
      (ENNReal.iInf_add).symm

end AsymptoticStatistics.LowerBounds.GaussianConeQuantization
