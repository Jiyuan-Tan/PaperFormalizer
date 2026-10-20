module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringMeasurability
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import StatLean.AsymptoticStatistics.ForMathlib.OuterIntegration.OuterExpectation
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

namespace AsymptoticStatistics.EmpiricalProcess
open MeasureTheory Filter
open scoped ENNReal

def signedGhostSwap {Ω : Type*} (n : ℕ) :
    (((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool)) →
      (((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool)) :=
  fun z =>
    (((fun i => if z.2 i then z.1.2 i else z.1.1 i),
      (fun i => if z.2 i then z.1.1 i else z.1.2 i)), z.2)

theorem signedGhostSwap_eval_sub_apply
    {Ω : Type*} (n : ℕ) (f : Ω → ℝ)
    (z : ((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool))
    (i : Fin n) :
    f ((signedGhostSwap n z).1.1 i) -
        f ((signedGhostSwap n z).1.2 i) =
      ProbabilityTheory.rademacherSign (z.2 i) *
        (f (z.1.1 i) - f (z.1.2 i)) := by
  cases h : z.2 i <;> simp [signedGhostSwap, h, ProbabilityTheory.rademacherSign]

theorem signedGhostSwap_involutive {Ω : Type*} (n : ℕ) :
    Function.Involutive (signedGhostSwap (Ω := Ω) n) := by
  intro z
  ext i <;> simp only [signedGhostSwap] <;> split <;> simp_all

theorem measurable_signedGhostSwap
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) :
    Measurable (signedGhostSwap (Ω := Ω) n) := by
  unfold signedGhostSwap
  refine ((measurable_pi_lambda _ fun i => ?_).prodMk
    (measurable_pi_lambda _ fun i => ?_)).prodMk measurable_snd
  · have hε : Measurable (fun z :
        ((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool) => z.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    have hcond : MeasurableSet {z :
        ((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool) | z.2 i = true} :=
      hε (measurableSet_singleton true)
    exact Measurable.ite hcond
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))
  · have hε : Measurable (fun z :
        ((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool) => z.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    have hcond : MeasurableSet {z :
        ((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool) | z.2 i = true} :=
      hε (measurableSet_singleton true)
    exact Measurable.ite hcond
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))

theorem measurePreserving_signedGhostSwap
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) :
    MeasurePreserving (signedGhostSwap (Ω := Ω) n)
      (((Measure.pi (fun _ : Fin n => P)).prod
          (Measure.pi (fun _ : Fin n => P))).prod
        (ProbabilityTheory.rademacherCube n))
      (((Measure.pi (fun _ : Fin n => P)).prod
          (Measure.pi (fun _ : Fin n => P))).prod
        (ProbabilityTheory.rademacherCube n)) := by
  let μn : Measure (Fin n → Ω) := Measure.pi (fun _ => P)
  let μpair : Measure (Fin n → Ω × Ω) := Measure.pi (fun _ => P.prod P)
  let ν : Measure (Fin n → Bool) := ProbabilityTheory.rademacherCube n
  let e := MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin n)
  let swapAt (b : Bool) : Ω × Ω → Ω × Ω := fun p => if b then p.swap else p
  let swapPi (ε : Fin n → Bool) : (Fin n → Ω × Ω) → (Fin n → Ω × Ω) :=
    fun u i => swapAt (ε i) (u i)
  let swapSamples (ε : Fin n → Bool) :
      (Fin n → Ω) × (Fin n → Ω) → (Fin n → Ω) × (Fin n → Ω) :=
    fun xy => e (swapPi ε (e.symm xy))
  have he : MeasurePreserving e μpair (μn.prod μn) := by
    exact measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin n)
      (fun _ => P) (fun _ => P)
  have hswapPi (ε : Fin n → Bool) : MeasurePreserving (swapPi ε) μpair μpair := by
    apply measurePreserving_pi
    intro i
    by_cases h : ε i
    · simpa [swapAt, h] using
        (Measure.measurePreserving_swap (μ := P) (ν := P))
    · simpa [swapAt, h] using! (MeasurePreserving.id (P.prod P))
  have hswapSamples (ε : Fin n → Bool) :
      MeasurePreserving (swapSamples ε) (μn.prod μn) (μn.prod μn) := by
    exact he.comp ((hswapPi ε).comp (he.symm e))
  have hswapPi_meas : Measurable (Function.uncurry swapPi) := by
    apply measurable_pi_lambda
    intro i
    have hε : Measurable (fun p : (Fin n → Bool) × (Fin n → Ω × Ω) => p.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    have hcond : MeasurableSet {p : (Fin n → Bool) × (Fin n → Ω × Ω) |
        p.1 i = true} := hε (measurableSet_singleton true)
    exact Measurable.ite hcond
      (measurable_swap.comp ((measurable_pi_apply i).comp measurable_snd))
      ((measurable_pi_apply i).comp measurable_snd)
  have hswapSamples_meas : Measurable (Function.uncurry swapSamples) := by
    exact e.measurable.comp (hswapPi_meas.comp
      (measurable_fst.prodMk (e.symm.measurable.comp measurable_snd)))
  have hskew : MeasurePreserving
      (fun p : (Fin n → Bool) × ((Fin n → Ω) × (Fin n → Ω)) =>
        (p.1, swapSamples p.1 p.2))
      (ν.prod (μn.prod μn)) (ν.prod (μn.prod μn)) := by
    apply (MeasurePreserving.id ν).skew_product
    · exact hswapSamples_meas
    · exact ae_of_all _ fun ε => (hswapSamples ε).map_eq
  have hconj := Measure.measurePreserving_swap.comp
    (hskew.comp Measure.measurePreserving_swap)
  convert hconj using 1
  funext z
  ext i <;> simp [signedGhostSwap, swapSamples, swapPi, swapAt, e,
    MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow] <;>
    split <;> rfl

noncomputable def signedGhostDifferenceSup {Ω : Type*}
    (F : Set (Ω → ℝ)) (n : ℕ) (x y : Fin n → Ω)
    (ε : Fin n → Bool) : ℝ≥0∞ :=
  supNormOver F (fun f => (Real.sqrt n)⁻¹ *
    ∑ i, ProbabilityTheory.rademacherSign (ε i) *
      (f (x i) - f (y i)))

noncomputable def ghostLIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Set (Ω → ℝ)) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ z : (Fin n → Ω) × (Fin n → Ω),
    ghostDifferenceSup F n z.1 z.2
      ∂((Measure.pi (fun _ : Fin n => P)).prod
        (Measure.pi (fun _ : Fin n => P)))

noncomputable def signedGhostLIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Set (Ω → ℝ)) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ z : ((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool),
    signedGhostDifferenceSup F n z.1.1 z.1.2 z.2
      ∂(((Measure.pi (fun _ : Fin n => P)).prod
          (Measure.pi (fun _ : Fin n => P))).prod
        (ProbabilityTheory.rademacherCube n))

theorem integral_ghostDifference_eq_empiricalProcess
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (x : Fin n → Ω) (f : Ω → ℝ)
    (hf : Integrable f P) :
    (∫ y : Fin n → Ω,
      (Real.sqrt n)⁻¹ * ∑ i, (f (x i) - f (y i))
        ∂Measure.pi (fun _ : Fin n => P)) =
      empiricalProcess P n x f := by
  by_cases hn : n = 0
  · subst n
    simp
  have hsqrt : Real.sqrt n ≠ 0 := by positivity
  have hsqrt_sq : Real.sqrt n * Real.sqrt n = n := by
    rw [← sq]
    exact Real.sq_sqrt (Nat.cast_nonneg n)
  have hcomp (i : Fin n) : Integrable (fun y : Fin n → Ω => f (y i))
      (Measure.pi fun _ : Fin n => P) :=
    integrable_comp_eval hf
  rw [integral_const_mul, integral_finset_sum Finset.univ]
  · simp_rw [integral_sub (integrable_const _) (hcomp _), integral_const,
      probReal_univ, one_smul]
    simp_rw [integral_comp_eval (μ := fun _ : Fin n => P) hf.aestronglyMeasurable]
    unfold empiricalProcess empiricalAvg
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    field_simp
    rw [sq, hsqrt_sq]
  · intro i _
    exact (integrable_const _).sub (hcomp i)

theorem rawEmpiricalProcessSup_le_ghostLIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (n : ℕ) (x : Fin n → Ω) :
    supNormOver F (empiricalProcess P n x) ≤
      ∫⁻ y : Fin n → Ω, ghostDifferenceSup F n x y
        ∂Measure.pi (fun _ : Fin n => P) := by
  obtain ⟨_, _, _, _, Φ, hΦint, hΦdom⟩ := hDense
  refine iSup₂_le fun f hfF => ?_
  have hfint : Integrable f P := hΦint.mono
    (hF_meas f hfF).aestronglyMeasurable
    (Eventually.of_forall fun a => by
      simpa [Real.norm_eq_abs] using
        (hΦdom f hfF a).trans (le_abs_self (Φ a)))
  rw [← integral_ghostDifference_eq_empiricalProcess P n x f hfint,
    ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine lintegral_mono fun y => ?_
  rw [Real.enorm_eq_ofReal_abs]
  exact le_supNormOver hfF

theorem ghostDifferenceSup_signedGhostSwap
    {Ω : Type*} (F : Set (Ω → ℝ)) (n : ℕ)
    (z : ((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool)) :
    ghostDifferenceSup F n
        (signedGhostSwap n z).1.1 (signedGhostSwap n z).1.2 =
      signedGhostDifferenceSup F n z.1.1 z.1.2 z.2 := by
  unfold ghostDifferenceSup signedGhostDifferenceSup
  apply congrArg (supNormOver F)
  funext f
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact signedGhostSwap_eval_sub_apply n f z i

theorem ghostLIntegral_eq_signedGhostLIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f) (n : ℕ) :
    ghostLIntegral P F n = signedGhostLIntegral P F n := by
  let μn : Measure (Fin n → Ω) := Measure.pi (fun _ => P)
  let μpair : Measure ((Fin n → Ω) × (Fin n → Ω)) := μn.prod μn
  let ν : Measure (Fin n → Bool) := ProbabilityTheory.rademacherCube n
  let G : ((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool) → ℝ≥0∞ :=
    fun z => ghostDifferenceSup F n z.1.1 z.1.2
  have hG_meas : Measurable G :=
    (measurable_ghostDifferenceSup_dense P F hDense hF_meas n).comp measurable_fst
  have hmp := measurePreserving_signedGhostSwap P n
  unfold ghostLIntegral signedGhostLIntegral
  change (∫⁻ z, ghostDifferenceSup F n z.1 z.2 ∂μpair) =
    ∫⁻ z, signedGhostDifferenceSup F n z.1.1 z.1.2 z.2 ∂μpair.prod ν
  symm
  calc
    (∫⁻ z, signedGhostDifferenceSup F n z.1.1 z.1.2 z.2 ∂μpair.prod ν) =
        ∫⁻ z, G (signedGhostSwap n z) ∂μpair.prod ν := by
      apply lintegral_congr
      intro z
      exact (ghostDifferenceSup_signedGhostSwap F n z).symm
    _ = ∫⁻ z, G z ∂μpair.prod ν := hmp.lintegral_comp hG_meas
    _ = ∫⁻ z, ghostDifferenceSup F n z.1 z.2 ∂μpair := by
      rw [lintegral_prod G hG_meas.aemeasurable]
      simp [G, ν]

theorem signedGhostDifferenceSup_le_rademacherSup_add
    {Ω : Type*} (F : Set (Ω → ℝ)) (n : ℕ)
    (x y : Fin n → Ω) (ε : Fin n → Bool) :
    signedGhostDifferenceSup F n x y ε ≤
      rademacherSup F n x ε + rademacherSup F n y ε := by
  unfold signedGhostDifferenceSup
  refine iSup₂_le fun f hf => ?_
  have heval :
      (Real.sqrt n)⁻¹ *
          ∑ i, ProbabilityTheory.rademacherSign (ε i) *
            (f (x i) - f (y i)) =
        rademacherAverage n x ε f - rademacherAverage n y ε f := by
    simp only [rademacherAverage, Finset.mul_sum, mul_sub,
      Finset.sum_sub_distrib]
  change ENNReal.ofReal
      |(Real.sqrt n)⁻¹ *
        ∑ i, ProbabilityTheory.rademacherSign (ε i) *
          (f (x i) - f (y i))| ≤ _
  rw [heval]
  calc
    ENNReal.ofReal
          |rademacherAverage n x ε f - rademacherAverage n y ε f| ≤
        ENNReal.ofReal
          (|rademacherAverage n x ε f| + |rademacherAverage n y ε f|) :=
      ENNReal.ofReal_le_ofReal (abs_sub _ _)
    _ = ENNReal.ofReal |rademacherAverage n x ε f| +
        ENNReal.ofReal |rademacherAverage n y ε f| := by
      rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    _ ≤ rademacherSup F n x ε + rademacherSup F n y ε :=
      add_le_add (le_supNormOver hf) (le_supNormOver hf)

theorem signedGhostLIntegral_le_two_conditionalRademacher
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f) (n : ℕ) :
    signedGhostLIntegral P F n ≤
      2 * ∫⁻ x : Fin n → Ω, conditionalRademacherSup F n x
        ∂Measure.pi (fun _ : Fin n => P) := by
  let μn : Measure (Fin n → Ω) := Measure.pi (fun _ => P)
  let μpair : Measure ((Fin n → Ω) × (Fin n → Ω)) := μn.prod μn
  let ν : Measure (Fin n → Bool) := ProbabilityTheory.rademacherCube n
  let R : (Fin n → Ω) × (Fin n → Bool) → ℝ≥0∞ :=
    fun z => rademacherSup F n z.1 z.2
  let A : ((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool) → ℝ≥0∞ :=
    fun z => R (z.1.1, z.2)
  let B : ((Fin n → Ω) × (Fin n → Ω)) × (Fin n → Bool) → ℝ≥0∞ :=
    fun z => R (z.1.2, z.2)
  have hR : Measurable R :=
    measurable_rademacherSup_dense P F hDense hF_meas n
  have hA : Measurable A :=
    hR.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hB : Measurable B :=
    hR.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hAint : (∫⁻ z, A z ∂μpair.prod ν) =
      ∫⁻ x, conditionalRademacherSup F n x ∂μn := by
    rw [lintegral_prod A hA.aemeasurable]
    simp only [A, R, conditionalRademacherSup]
    rw [lintegral_prod]
    · simp [ν]
    · exact (measurable_conditionalRademacherSup_dense P F hDense hF_meas n).comp
        measurable_fst |>.aemeasurable
  have hBint : (∫⁻ z, B z ∂μpair.prod ν) =
      ∫⁻ x, conditionalRademacherSup F n x ∂μn := by
    rw [lintegral_prod B hB.aemeasurable]
    simp only [B, R, conditionalRademacherSup]
    rw [lintegral_prod]
    · simp [ν]
    · exact (measurable_conditionalRademacherSup_dense P F hDense hF_meas n).comp
        measurable_snd |>.aemeasurable
  unfold signedGhostLIntegral
  change (∫⁻ z, signedGhostDifferenceSup F n z.1.1 z.1.2 z.2
      ∂μpair.prod ν) ≤ _
  calc
    (∫⁻ z, signedGhostDifferenceSup F n z.1.1 z.1.2 z.2
        ∂μpair.prod ν) ≤ ∫⁻ z, A z + B z ∂μpair.prod ν :=
      lintegral_mono fun z => signedGhostDifferenceSup_le_rademacherSup_add
        F n z.1.1 z.1.2 z.2
    _ = (∫⁻ z, A z ∂μpair.prod ν) + ∫⁻ z, B z ∂μpair.prod ν :=
      lintegral_add_left hA B
    _ = 2 * ∫⁻ x, conditionalRademacherSup F n x ∂μn := by
      rw [hAint, hBint, two_mul]

theorem ghostLIntegral_le_two_conditionalRademacher
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f) (n : ℕ) :
    ghostLIntegral P F n ≤
      2 * ∫⁻ x : Fin n → Ω, conditionalRademacherSup F n x
        ∂Measure.pi (fun _ : Fin n => P) := by
  rw [ghostLIntegral_eq_signedGhostLIntegral P F hDense hF_meas n]
  exact signedGhostLIntegral_le_two_conditionalRademacher P F hDense hF_meas n

theorem canonical_symmetrization_empiricalProcess
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f) (n : ℕ) :
    (∫⁻ x : Fin n → Ω,
      supNormOver F (empiricalProcess P n x)
        ∂Measure.pi (fun _ : Fin n => P)) ≤
      2 * ∫⁻ x : Fin n → Ω, conditionalRademacherSup F n x
        ∂Measure.pi (fun _ : Fin n => P) := by
  have hghost : Measurable
      (fun z : (Fin n → Ω) × (Fin n → Ω) =>
        ghostDifferenceSup F n z.1 z.2) :=
    measurable_ghostDifferenceSup_dense P F hDense hF_meas n
  calc
    (∫⁻ x : Fin n → Ω, supNormOver F (empiricalProcess P n x)
        ∂Measure.pi (fun _ : Fin n => P)) ≤
        ∫⁻ x : Fin n → Ω, ∫⁻ y : Fin n → Ω,
          ghostDifferenceSup F n x y
            ∂Measure.pi (fun _ : Fin n => P)
          ∂Measure.pi (fun _ : Fin n => P) :=
      lintegral_mono fun x =>
        rawEmpiricalProcessSup_le_ghostLIntegral P F hDense hF_meas n x
    _ = ghostLIntegral P F n := by
      rw [ghostLIntegral]
      exact (lintegral_prod _ hghost.aemeasurable).symm
    _ ≤ 2 * ∫⁻ x : Fin n → Ω, conditionalRademacherSup F n x
        ∂Measure.pi (fun _ : Fin n => P) :=
      ghostLIntegral_le_two_conditionalRademacher P F hDense hF_meas n

theorem outer_symmetrization_empiricalProcess
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i,
      ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f) (n : ℕ) :
    MeasureTheory.outerExpectation μ (fun ξ =>
      supNormOver F
        (empiricalProcess P n (fun i : Fin n => X i.val ξ))) ≤
      2 * ∫⁻ ξ, conditionalRademacherSup F n
        (fun i : Fin n => X i.val ξ) ∂μ := by
  let Y : Ξ → (Fin n → Ω) := fun ξ i => X i.val ξ
  let raw : (Fin n → Ω) → ℝ≥0∞ := fun x =>
    supNormOver F (empiricalProcess P n x)
  let cond : (Fin n → Ω) → ℝ≥0∞ := fun x =>
    conditionalRademacherSup F n x
  have hY_meas : Measurable Y :=
    measurable_pi_lambda _ fun i => hX_meas i.val
  have hY_map : μ.map Y = Measure.pi (fun _ : Fin n => P) :=
    AsymptoticStatistics.map_fin_restrict_eq_pi_of_iid
      P μ X hX_meas hX_iindep hX_idem hX_law n
  have hraw_meas : Measurable raw :=
    measurable_canonicalEmpiricalProcessSup_dense P F hDense hF_meas n
  have hcond_meas : Measurable cond :=
    measurable_conditionalRademacherSup_dense P F hDense hF_meas n
  have hrawY_meas : Measurable (fun ξ => raw (Y ξ)) := by
    simpa only [Function.comp_apply] using! hraw_meas.comp hY_meas
  change MeasureTheory.outerExpectation μ (fun ξ => raw (Y ξ)) ≤
    2 * ∫⁻ ξ, cond (Y ξ) ∂μ
  rw [MeasureTheory.outerExpectation_eq_lintegral hrawY_meas]
  calc
    (∫⁻ ξ, raw (Y ξ) ∂μ) =
        ∫⁻ x, raw x ∂Measure.pi (fun _ : Fin n => P) := by
      rw [← hY_map, lintegral_map hraw_meas hY_meas]
    _ ≤ 2 * ∫⁻ x, cond x ∂Measure.pi (fun _ : Fin n => P) :=
      canonical_symmetrization_empiricalProcess P F hDense hF_meas n
    _ = 2 * ∫⁻ ξ, cond (Y ξ) ∂μ := by
      rw [← hY_map, lintegral_map hcond_meas hY_meas]

end AsymptoticStatistics.EmpiricalProcess
