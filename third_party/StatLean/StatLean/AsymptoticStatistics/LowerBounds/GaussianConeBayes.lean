module
public import StatLean.AsymptoticStatistics.LowerBounds.GaussianConePrior
public import StatLean.AsymptoticStatistics.ForMathlib.BowlShaped
public import StatLean.AsymptoticStatistics.ForMathlib.Anderson
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianSmul
public import StatLean.AsymptoticStatistics.Experiment.GaussianShiftMinimax
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

/-! # Bayes bound for Gaussian shifts on an effective cone span -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder RealInnerProductSpace
namespace AsymptoticStatistics.LowerBounds.GaussianConeBayes
open AsymptoticStatistics
open AsymptoticStatistics.LowerBounds.GaussianConePrior
open AsymptoticStatistics.GaussianShiftMinimax
variable {m : ℕ}

/-- A randomized decision rule: a Markov kernel from observations to actions.
This is the kernel form of vdV's randomized estimator.  There is no fallback
case: membership records exactly the Markov property. -/
def MarkovDecision (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] :=
  {κ : Kernel X A // IsMarkovKernel κ}

/-- Rectangular matrix action on Euclidean spaces, represented in the
`WithLp` model. -/
noncomputable def matrixActionVec {d : ℕ}
    (A : Matrix (Fin d) (Fin m) ℝ) (h : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 _).symm (A.mulVec ((WithLp.equiv 2 _) h))

/-- Risk of a randomized vector action in the standard Gaussian shift
experiment.  The rectangular matrix maps the shift parameter to the action
centering. -/
noncomputable def gaussianShiftKernelRiskVec {d : ℕ}
    (A : Matrix (Fin d) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d)))
    (h : EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  ∫⁻ a, ℓ (a - matrixActionVec A h) ∂((multivariateGaussian h
    (1 : Matrix (Fin m) (Fin m) ℝ)).bind κ.1)

/-- Bayes risk of randomized vector decisions under a cone-supported prior. -/
noncomputable def measurableBayesRiskVec {d : ℕ}
    (π : Measure (EuclideanSpace ℝ (Fin m)))
    (A : Matrix (Fin d) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d)),
    ∫⁻ h, gaussianShiftKernelRiskVec A ℓ κ h ∂π

private theorem bayesRiskAtTau_le_averageKernelVec {d : ℕ}
    (A : Matrix (Fin d) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hℓ : BowlShaped ℓ)
    (κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d)))
    {τ : ℝ} (hτ : 0 < τ) :
    bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ ≤
      ∫⁻ h, gaussianShiftKernelRiskVec A ℓ κ h
        ∂(multivariateGaussian 0 ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ))) := by
  letI : IsMarkovKernel κ.1 := κ.2
  let ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d) := matrixActionVec A
  have hψmeas : Measurable ψ := by
    exact (matrixToEuclideanCLMRect A).continuous.measurable
  have hψmat : ∀ h : EuclideanSpace ℝ (Fin m),
      ψ h = (WithLp.equiv 2 _).symm (A.mulVec ((WithLp.equiv 2 _) h)) := fun _ => rfl
  let Sτ := posteriorCov (1 : Matrix (Fin m) (Fin m) ℝ) τ
  have hSτpsd : Sτ.PosSemidef :=
    (posteriorCov_posDef Matrix.PosDef.one hτ).posSemidef
  let Q := A * Sτ * A.transpose
  have hQpsd : Q.PosSemidef := by
    have h := hSτpsd.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hclm : ∀ g : EuclideanSpace ℝ (Fin m),
      matrixToEuclideanCLMRect A g = ψ g := fun _ => rfl
  have hψadd : ∀ a b : EuclideanSpace ℝ (Fin m), ψ (a + b) = ψ a + ψ b := by
    intro a b
    exact map_add (matrixToEuclideanCLMRect A) a b
  have hinner : ∀ (x : EuclideanSpace ℝ (Fin m))
      (y : EuclideanSpace ℝ (Fin d)),
      bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ ≤
        ∫⁻ g, ℓ (y - ψ (g + posteriorMean 1 τ x))
          ∂(multivariateGaussian 0 Sτ) := by
    intro x y
    let c := y - ψ (posteriorMean 1 τ x)
    have hsplit : ∀ g : EuclideanSpace ℝ (Fin m),
        y - ψ (g + posteriorMean 1 τ x) = c - ψ g := by
      intro g
      rw [hψadd]
      dsimp [c]
      abel
    calc
      bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ
          = ∫⁻ z, ℓ z ∂(multivariateGaussian 0 Q) := rfl
      _ ≤ ∫⁻ z, ℓ (c - z) ∂(multivariateGaussian 0 Q) :=
        lintegral_loss_translated_ge hQpsd hℓ c
      _ = ∫⁻ z, ℓ (c - z) ∂((multivariateGaussian 0 Sτ).map
          (matrixToEuclideanCLMRect A)) := by
        rw [multivariateGaussian_map_rectangular A 0 hSτpsd]
        rw [(matrixToEuclideanCLMRect A).map_zero]
      _ = ∫⁻ g, ℓ (c - matrixToEuclideanCLMRect A g)
          ∂(multivariateGaussian 0 Sτ) := by
        exact lintegral_map (hℓ.measurable.comp (measurable_const.sub measurable_id))
          (matrixToEuclideanCLMRect A).continuous.measurable
      _ = ∫⁻ g, ℓ (c - ψ g) ∂(multivariateGaussian 0 Sτ) := by
        refine lintegral_congr fun g => ?_
        rw [hclm]
      _ = ∫⁻ g, ℓ (y - ψ (g + posteriorMean 1 τ x))
          ∂(multivariateGaussian 0 Sτ) := by
        refine lintegral_congr fun g => ?_
        rw [hsplit]
  let πX := marginalGaussianShift (1 : Matrix (Fin m) (Fin m) ℝ) τ
  let πτ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
    ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ))
  let f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ≥0∞ :=
    fun h x => ∫⁻ y, ℓ (y - ψ h) ∂(κ.1 x)
  have hfmeas : Measurable (Function.uncurry f) := by
    let snd : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) →
        EuclideanSpace ℝ (Fin m) := Prod.snd
    let κ' : Kernel (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin d)) := κ.1.comap snd measurable_snd
    letI : IsMarkovKernel κ' := Kernel.IsMarkovKernel.comap κ.1 measurable_snd
    have hm : Measurable (fun p : (EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin d) =>
        ℓ (p.2 - ψ p.1.1)) := by
      exact hℓ.measurable.comp (measurable_snd.sub (hψmeas.comp measurable_fst.fst))
    have H := Measurable.lintegral_kernel_prod_right' (κ := κ') hm
    exact H
  haveI hπX : IsProbabilityMeasure πX := by
    unfold πX marginalGaussianShift
    infer_instance
  haveI hπτ : IsProbabilityMeasure πτ := by
    unfold πτ
    infer_instance
  calc
    bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ
        = ∫⁻ x, ∫⁻ _y : EuclideanSpace ℝ (Fin d),
            bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ
            ∂(κ.1 x) ∂πX := by
          simp
    _ ≤ ∫⁻ x, ∫⁻ y, ∫⁻ g, ℓ (y - ψ (g + posteriorMean 1 τ x))
          ∂(multivariateGaussian 0 Sτ) ∂(κ.1 x) ∂πX := by
      refine lintegral_mono fun x => lintegral_mono fun y => hinner x y
    _ = ∫⁻ x, ∫⁻ g, ∫⁻ y, ℓ (y - ψ (g + posteriorMean 1 τ x))
          ∂(κ.1 x) ∂(multivariateGaussian 0 Sτ) ∂πX := by
      refine lintegral_congr fun x => lintegral_lintegral_swap ?_
      exact (hℓ.measurable.comp (measurable_fst.sub
        (hψmeas.comp (measurable_snd.add measurable_const)))).aemeasurable
    _ = ∫⁻ h, ∫⁻ x, ∫⁻ y, ℓ (y - ψ h) ∂(κ.1 x)
          ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)) ∂πτ := by
      simpa [Sτ, πX, πτ] using
        (gaussianShift_innovations_repr Matrix.PosDef.one hτ f hfmeas).symm
    _ = ∫⁻ h, gaussianShiftKernelRiskVec A ℓ κ h ∂πτ := by
      refine lintegral_congr fun h => ?_
      have hm : AEMeasurable (fun y : EuclideanSpace ℝ (Fin d) => ℓ (y - ψ h))
          ((multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)).bind κ.1) :=
        (hℓ.measurable.comp (measurable_id.sub_const _)).aemeasurable
      exact (Measure.lintegral_bind κ.1.measurable.aemeasurable hm).symm

private theorem multivariateGaussian_map_add_left
    (u v : EuclideanSpace ℝ (Fin m)) (S : Matrix (Fin m) (Fin m) ℝ) :
    (multivariateGaussian v S).map (fun x => u + x) =
      multivariateGaussian (u + v) S := by
  unfold multivariateGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [add_assoc]

private theorem gaussianShiftKernelRiskVec_measurable {d : ℕ}
    (A : Matrix (Fin d) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hℓ : Measurable ℓ)
    (κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d))) :
    Measurable (gaussianShiftKernelRiskVec A ℓ κ) := by
  letI : IsMarkovKernel κ.1 := κ.2
  let shiftObs : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m) := fun p => p.1 +
        Matrix.toEuclideanCLM (𝕜 := ℝ)
          (CFC.sqrt (1 : Matrix (Fin m) (Fin m) ℝ)) p.2
  have hshift : Measurable shiftObs := by fun_prop
  let κ' : Kernel (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d)) := κ.1.comap shiftObs hshift
  letI : IsMarkovKernel κ' := Kernel.IsMarkovKernel.comap κ.1 hshift
  have hjoint : Measurable (fun p : (EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin d) =>
      ℓ (p.2 - matrixActionVec A p.1.1)) := by
    exact hℓ.comp (measurable_snd.sub
      ((matrixToEuclideanCLMRect A).continuous.measurable.comp measurable_fst.fst))
  have hin : Measurable (fun p : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) =>
      ∫⁻ a, ℓ (a - matrixActionVec A p.1) ∂(κ' p)) :=
    Measurable.lintegral_kernel_prod_right' (κ := κ') hjoint
  have hout : Measurable (fun h => ∫⁻ z,
      ∫⁻ a, ℓ (a - matrixActionVec A h) ∂(κ' (h, z))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))) :=
    hin.lintegral_prod_right'
  convert hout using 1
  funext h
  unfold gaussianShiftKernelRiskVec multivariateGaussian
  calc
    ∫⁻ a, ℓ (a - matrixActionVec A h) ∂((Measure.map
          (fun x => h + Matrix.toEuclideanCLM (𝕜 := ℝ)
            (CFC.sqrt (1 : Matrix (Fin m) (Fin m) ℝ)) x)
          (stdGaussian (EuclideanSpace ℝ (Fin m)))).bind κ.1)
        = ∫⁻ x, ∫⁻ a, ℓ (a - matrixActionVec A h) ∂(κ.1 x)
            ∂(Measure.map (fun x => h + Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (1 : Matrix (Fin m) (Fin m) ℝ)) x)
              (stdGaussian (EuclideanSpace ℝ (Fin m)))) :=
          Measure.lintegral_bind κ.1.measurable.aemeasurable
            (hℓ.comp (measurable_id.sub_const _)).aemeasurable
    _ = ∫⁻ z, ∫⁻ a, ℓ (a - matrixActionVec A h) ∂(κ' (h, z))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
      rw [lintegral_map (by
        exact Measurable.lintegral_kernel_prod_right' (κ := κ.1)
          (hℓ.comp (measurable_snd.sub measurable_const))) (by fun_prop)]
      rfl

private theorem bayesRiskAtTau_le_averageKernelVec_translated {d : ℕ}
    (A : Matrix (Fin d) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hℓ : BowlShaped ℓ)
    (κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d)))
    (h0 : EuclideanSpace ℝ (Fin m)) {τ : ℝ} (hτ : 0 < τ) :
    bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ ≤
      ∫⁻ h, gaussianShiftKernelRiskVec A ℓ κ h
        ∂(multivariateGaussian h0 ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ))) := by
  letI : IsMarkovKernel κ.1 := κ.2
  let Ah0 : EuclideanSpace ℝ (Fin d) := matrixActionVec A h0
  let shiftData : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun x => h0 + x
  let shiftAction : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun a => a - Ah0
  have hData : Measurable shiftData := by fun_prop
  have hAction : Measurable shiftAction := by fun_prop
  let κ' : Kernel (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin d)) :=
    (κ.1.comap shiftData hData).map shiftAction
  letI : IsMarkovKernel κ' := by
    exact Kernel.IsMarkovKernel.map _ hAction
  let κM : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d)) := ⟨κ', inferInstance⟩
  have hrisk : ∀ g : EuclideanSpace ℝ (Fin m),
      gaussianShiftKernelRiskVec A ℓ κM g =
        gaussianShiftKernelRiskVec A ℓ κ (h0 + g) := by
    intro g
    have hAadd : matrixActionVec A (h0 + g) = Ah0 + matrixActionVec A g := by
      exact map_add (matrixToEuclideanCLMRect A) h0 g
    unfold gaussianShiftKernelRiskVec
    change ∫⁻ a, ℓ (a - matrixActionVec A g) ∂((multivariateGaussian g 1).bind κ') =
      ∫⁻ a, ℓ (a - matrixActionVec A (h0 + g))
        ∂((multivariateGaussian (h0 + g) 1).bind κ.1)
    calc
      ∫⁻ a, ℓ (a - matrixActionVec A g) ∂((multivariateGaussian g 1).bind κ')
          = ∫⁻ x, ∫⁻ a, ℓ (a - matrixActionVec A g) ∂(κ' x)
              ∂(multivariateGaussian g 1) :=
            Measure.lintegral_bind κ'.measurable.aemeasurable
              (hℓ.measurable.comp (measurable_id.sub_const _)).aemeasurable
      _ = ∫⁻ x, ∫⁻ a, ℓ (a - matrixActionVec A (h0 + g)) ∂(κ.1 x)
              ∂(multivariateGaussian (h0 + g) 1) := by
        rw [← multivariateGaussian_map_add_left h0 g
          (1 : Matrix (Fin m) (Fin m) ℝ)]
        rw [lintegral_map (by
          exact Measurable.lintegral_kernel_prod_right' (κ := κ.1)
            (hℓ.measurable.comp (measurable_snd.sub measurable_const))) hData]
        refine lintegral_congr fun x => ?_
        rw [show κ' x = (κ.1 (shiftData x)).map shiftAction by
          exact Kernel.map_apply _ hAction _]
        calc
          ∫⁻ a, ℓ (a - matrixActionVec A g)
                ∂(Measure.map shiftAction (κ.1 (shiftData x)))
              = ∫⁻ a, ℓ (shiftAction a - matrixActionVec A g)
                  ∂(κ.1 (shiftData x)) :=
                lintegral_map (hℓ.measurable.comp (measurable_id.sub_const _)) hAction
          _ = ∫⁻ a, ℓ (a - matrixActionVec A (h0 + g))
                  ∂(κ.1 (shiftData x)) := by
            refine lintegral_congr fun a => ?_
            dsimp [shiftAction, shiftData, Ah0]
            rw [hAadd]
            congr 1
            abel
      _ = ∫⁻ a, ℓ (a - matrixActionVec A (h0 + g))
              ∂((multivariateGaussian (h0 + g) 1).bind κ.1) :=
            (Measure.lintegral_bind κ.1.measurable.aemeasurable
              (hℓ.measurable.comp (measurable_id.sub_const _)).aemeasurable).symm
  refine (bayesRiskAtTau_le_averageKernelVec A ℓ hℓ κM hτ).trans_eq ?_
  have hmap : (multivariateGaussian 0
      ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ))).map shiftData =
      multivariateGaussian h0 ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
    simpa [shiftData] using multivariateGaussian_map_add_left h0 0
      ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ))
  rw [← hmap]
  rw [lintegral_map (gaussianShiftKernelRiskVec_measurable A ℓ hℓ.measurable κ) hData]
  refine lintegral_congr fun g => ?_
  exact hrisk g

private theorem translatedGaussian_eq_multivariateGaussian_of_fullSpan
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (hspan : effectiveSpan C = ⊤) (h0 : ↥(effectiveSpan C))
    (c : ℝ) (hc : 0 < c) :
    translatedGaussianOnEffectiveSpan C h0 c =
      multivariateGaussian (h0 : EuclideanSpace ℝ (Fin m))
        ((c ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  have hs := translatedGaussianOnEffectiveSpan_spec C h0 c hc
  let ν := translatedGaussianOnEffectiveSpan C h0 c
  haveI : IsProbabilityMeasure ν := hs.1
  have hcov : ((c ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
    Matrix.PosDef.one.posSemidef.smul (sq_nonneg c)
  apply Measure.ext_of_charFun
  ext u
  let us : ↥(effectiveSpan C) := ⟨u, by rw [hspan]; trivial⟩
  have hmap := hs.2.2 us
  rw [charFun_eq_charFunDual_toDualMap, charFunDual_eq_charFun_map_one,
    show ν.map (InnerProductSpace.toDualMap ℝ _ u) =
        gaussianReal (inner ℝ u (h0 : EuclideanSpace ℝ (Fin m)))
          (NNReal.mk (c ^ 2 * ‖us‖ ^ 2) (mul_nonneg (sq_nonneg _) (sq_nonneg _))) by
      simpa [ν, InnerProductSpace.toDualMap_apply_apply] using! hmap,
    charFun_gaussianReal, charFun_multivariateGaussian hcov]
  norm_num
  have hunorm : ‖(us : EuclideanSpace ℝ (Fin m))‖ = ‖u‖ := rfl
  rw [hunorm]
  have hdot : u.ofLp ⬝ᵥ ((c ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).mulVec u.ofLp =
      c ^ 2 * ‖u‖ ^ 2 := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct,
      EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdot]
  norm_cast

private theorem exists_ball_compl_measure_lt
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ n : ℕ, P (Metric.ball 0 (n : ℝ))ᶜ < δ := by
  let s : ℕ → Set (EuclideanSpace ℝ (Fin m)) := fun n => (Metric.ball 0 (n : ℝ))ᶜ
  have hs : ∀ n, NullMeasurableSet (s n) P := fun n =>
    measurableSet_ball.compl.nullMeasurableSet
  have hanti : Antitone s := by
    intro n k hnk
    exact Set.compl_subset_compl.mpr (Metric.ball_subset_ball (by exact_mod_cast hnk))
  have hinter : ⋂ n, s n = ∅ := by
    rw [← Set.compl_iUnion, Metric.iUnion_ball_nat, Set.compl_univ]
  have ht := tendsto_measure_iInter_atTop hs hanti ⟨0, by simp⟩
  rw [hinter, measure_empty] at ht
  exact (ht.eventually (Iio_mem_nhds hδ)).exists

private theorem gaussianShiftKernelRiskVec_le {d : ℕ}
    (A : Matrix (Fin d) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d)))
    (B : ℝ≥0∞) (hB : ∀ x, ℓ x ≤ B) (h : EuclideanSpace ℝ (Fin m)) :
    gaussianShiftKernelRiskVec A ℓ κ h ≤ B := by
  letI : IsMarkovKernel κ.1 := κ.2
  unfold gaussianShiftKernelRiskVec
  calc
    ∫⁻ a, ℓ (a - matrixActionVec A h) ∂((multivariateGaussian h 1).bind κ.1)
        ≤ ∫⁻ _a, B ∂((multivariateGaussian h 1).bind κ.1) :=
      lintegral_mono fun a => hB _
    _ = B := by simp

private theorem lintegral_le_normalized_restrict_add {E : Type*}
    [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (C : Set E) (f : E → ℝ≥0∞)
    (B : ℝ≥0∞) (hfB : ∀ x, f x ≤ B) :
    ∫⁻ x, f x ∂P ≤
      ∫⁻ x, f x ∂((P C)⁻¹ • P.restrict C) +
        B * P (toMeasurable P C)ᶜ := by
  let D := toMeasurable P C
  have hD : MeasurableSet D := measurableSet_toMeasurable P C
  have hPCle : P C ≤ 1 := by
    calc
      P C ≤ P Set.univ := measure_mono (Set.subset_univ C)
      _ = 1 := measure_univ
  have hPCtop : P C ≠ ∞ := ne_of_lt (hPCle.trans_lt ENNReal.one_lt_top)
  have hrest : P.restrict D = P.restrict C := P.restrict_toMeasurable hPCtop
  have hinv : 1 ≤ (P C)⁻¹ := (ENNReal.le_inv_iff_mul_le).mpr (by simpa)
  have hinside : ∫⁻ x in D, f x ∂P ≤ ∫⁻ x, f x ∂((P C)⁻¹ • P.restrict C) := by
    rw [← hrest, lintegral_smul_measure]
    simpa [smul_eq_mul, mul_comm] using
      (mul_le_mul_right hinv (∫⁻ x in D, f x ∂P))
  have houtside : ∫⁻ x in Dᶜ, f x ∂P ≤ B * P Dᶜ := by
    calc
      ∫⁻ x in Dᶜ, f x ∂P ≤ ∫⁻ _x in Dᶜ, B ∂P :=
        setLIntegral_mono' hD.compl (fun x hx => hfB x)
      _ = B * P Dᶜ := by rw [setLIntegral_const]
  rw [← lintegral_add_compl f hD]
  exact add_le_add hinside houtside

private theorem cone_ball_of_radius
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (hcone : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C)
    (v : ↥(effectiveSpan C)) (r : ℝ) (hr : 0 < r)
    (hv : Metric.ball v r ⊆ coneInEffectiveSpan C)
    (R : ℝ) (hR : 0 < R) :
    ∃ h0 : ↥(effectiveSpan C),
      Metric.ball h0 R ⊆ coneInEffectiveSpan C := by
  let t : ℝ := R / r
  have ht : 0 < t := div_pos hR hr
  refine ⟨t • v, ?_⟩
  intro y hy
  have hy' : t⁻¹ • y ∈ Metric.ball v r := by
    change dist (((t⁻¹ • y : ↥(effectiveSpan C)) :
      EuclideanSpace ℝ (Fin m))) (v : EuclideanSpace ℝ (Fin m)) < r
    have hyd : dist (y : EuclideanSpace ℝ (Fin m))
        ((t • v : ↥(effectiveSpan C)) : EuclideanSpace ℝ (Fin m)) < R := by
      simpa only [Metric.mem_ball] using! hy
    calc
      dist (t⁻¹ • (y : EuclideanSpace ℝ (Fin m)))
          (v : EuclideanSpace ℝ (Fin m)) =
          dist (t⁻¹ • (y : EuclideanSpace ℝ (Fin m)))
            (t⁻¹ • (t • (v : EuclideanSpace ℝ (Fin m)))) := by
        simp [smul_smul, ht.ne']
      _ = ‖t⁻¹‖ * dist (y : EuclideanSpace ℝ (Fin m))
          (t • (v : EuclideanSpace ℝ (Fin m))) := dist_smul₀ _ _ _
      _ = t⁻¹ * dist (y : EuclideanSpace ℝ (Fin m))
          (t • (v : EuclideanSpace ℝ (Fin m))) := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      _ < t⁻¹ * R := mul_lt_mul_of_pos_left (by simpa using hyd) (inv_pos.mpr ht)
      _ = r := by
        dsimp [t]
        field_simp
  have hsmall : ((t⁻¹ • y : ↥(effectiveSpan C)) :
      EuclideanSpace ℝ (Fin m)) ∈ C := hv hy'
  have hscaled := hcone _ hsmall t ht.le
  simpa [smul_smul, ht.ne'] using! hscaled

private theorem multivariateGaussian_ball_compl_translate
    (h0 : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) (R : ℝ) :
    multivariateGaussian h0 S (Metric.ball h0 R)ᶜ =
      multivariateGaussian 0 S (Metric.ball 0 R)ᶜ := by
  have hmap := multivariateGaussian_map_add_left h0 0 S
  simp only [add_zero] at hmap
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_ball.compl]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_ball]
  simp

private theorem stdGaussian_prod_map_toLp
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] :
    ((stdGaussian E).prod (stdGaussian F)).map (WithLp.toLp 2) =
      stdGaussian (WithLp 2 (E × F)) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_prod, charFun_stdGaussian, charFun_stdGaussian,
    charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  have hnorm : (‖t‖ : ℂ) ^ 2 =
      (‖t.ofLp.1‖ : ℂ) ^ 2 + (‖t.ofLp.2‖ : ℂ) ^ 2 := by
    exact_mod_cast WithLp.prod_norm_sq_eq_of_L2 t
  rw [hnorm]
  ring

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
        (@inner ℝ _ _ (us : EuclideanSpace ℝ (Fin m))
          (h0 : EuclideanSpace ℝ (Fin m)))
        ⟨c ^ 2 * ‖us‖ ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩ := by
    calc
      Measure.map (InnerProductSpace.toDualMap ℝ _ u) ν =
          Measure.map (fun x : EuclideanSpace ℝ (Fin m) =>
            @inner ℝ _ _ (us : EuclideanSpace ℝ (Fin m)) x) ν := by
        apply Measure.map_congr
        filter_upwards [hνS] with x hx
        simpa only [InnerProductSpace.toDualMap_apply_apply] using!
          (S.inner_orthogonalProjection_eq_of_mem_right ⟨x, hx⟩ u).symm
      _ = _ := hν.2.2 us
  have hμmap : Measure.map (InnerProductSpace.toDualMap ℝ _ u) μ =
      gaussianReal
        (@inner ℝ _ _ (us : EuclideanSpace ℝ (Fin m))
          (h0 : EuclideanSpace ℝ (Fin m)))
        ⟨c ^ 2 * ‖us‖ ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩ := by
    calc
      Measure.map (InnerProductSpace.toDualMap ℝ _ u) μ =
          Measure.map (fun x : EuclideanSpace ℝ (Fin m) =>
            @inner ℝ _ _ (us : EuclideanSpace ℝ (Fin m)) x) μ := by
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
        (@inner ℝ _ _ (us : EuclideanSpace ℝ (Fin m))
          (h0 : EuclideanSpace ℝ (Fin m)))
        ⟨c ^ 2 * ‖us‖ ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩) 1 := by
      rw [hνmap]
    _ = charFun (Measure.map
        (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin m)) u) μ) 1 := by
      rw [hμmap]
    _ = charFunDual μ
        (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin m)) u) :=
      (charFunDual_eq_charFun_map_one (μ := μ) _).symm
    _ = charFun μ u := (charFun_eq_charFunDual_toDualMap (μ := μ) u).symm

private noncomputable def intrinsicGaussian
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) :
    Measure (EuclideanSpace ℝ (Fin m)) := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let hSborel : BorelSpace ↥S := Subtype.borelSpace _
  letI : BorelSpace ↥S := hSborel
  exact (stdGaussian ↥S).map fun z =>
    ((h0 + c • z : ↥S) : EuclideanSpace ℝ (Fin m))

private theorem intrinsicGaussian_spec
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) :
    IsTranslatedIsotropicGaussian C (intrinsicGaussian C h0 c) h0 c := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let hSborel : BorelSpace ↥S := Subtype.borelSpace _
  letI : BorelSpace ↥S := hSborel
  letI : IsProbabilityMeasure (stdGaussian ↥S) :=
    @isProbabilityMeasure_stdGaussian _ _ _ _ _ hSborel
  letI : IsGaussian (stdGaussian ↥S) :=
    @isGaussian_stdGaussian _ _ _ _ _ hSborel
  let affineInclusion : ↥S → EuclideanSpace ℝ (Fin m) :=
    fun z => ((h0 + c • z : ↥S) : EuclideanSpace ℝ (Fin m))
  have haffine : Measurable affineInclusion := by fun_prop
  let ν : Measure (EuclideanSpace ℝ (Fin m)) :=
    (stdGaussian ↥S).map affineInclusion
  change IsTranslatedIsotropicGaussian C ν h0 c
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map haffine.aemeasurable
  refine ⟨inferInstance, ?_, ?_⟩
  · have hSclosed : IsClosed (S : Set (EuclideanSpace ℝ (Fin m))) :=
      S.closed_of_finiteDimensional
    rw [Measure.map_apply haffine hSclosed.measurableSet]
    have hpre : affineInclusion ⁻¹' (S : Set (EuclideanSpace ℝ (Fin m))) =
        Set.univ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact (h0 + c • z).property
    rw [hpre, measure_univ]
  · intro u
    change ↥S at u
    let L : ↥S →L[ℝ] ℝ := innerSL ℝ u
    let q : ℝ → ℝ := fun x => c * x +
      @inner ℝ _ _ (u : EuclideanSpace ℝ (Fin m))
        (h0 : EuclideanSpace ℝ (Fin m))
    have hL : Measurable L := L.continuous.measurable
    have hq : Measurable q := by fun_prop
    have hmean : (∫ x, L x ∂(stdGaussian ↥S)) = 0 := by
      simpa only [L] using
        (@integral_strongDual_stdGaussian _ _ _ _ _ hSborel (innerSL ℝ u))
    have hvar : Var[L; stdGaussian ↥S] = ‖u‖ ^ 2 := by
      simpa only [L, innerSL_apply_norm] using
        (@variance_dual_stdGaussian _ _ _ _ _ hSborel (innerSL ℝ u))
    have hbase : (stdGaussian ↥S).map L =
        gaussianReal 0 (NNReal.mk (‖u‖ ^ 2) (sq_nonneg _)) := by
      rw [IsGaussian.map_eq_gaussianReal L, hmean, hvar]
      congr 2
      ext
      simp
    have hcomp : (fun z : ↥S =>
        @inner ℝ _ _ (u : EuclideanSpace ℝ (Fin m)) (affineInclusion z)) =
        q ∘ L := by
      funext z
      simp only [Function.comp_apply, affineInclusion, q, L]
      change @inner ℝ _ _ (u : EuclideanSpace ℝ (Fin m))
          ((h0 : EuclideanSpace ℝ (Fin m)) + c •
            (z : EuclideanSpace ℝ (Fin m))) =
        c * @inner ℝ _ _ (u : EuclideanSpace ℝ (Fin m))
            (z : EuclideanSpace ℝ (Fin m)) +
          @inner ℝ _ _ (u : EuclideanSpace ℝ (Fin m))
            (h0 : EuclideanSpace ℝ (Fin m))
      rw [inner_add_right, real_inner_smul_right]
      ring
    rw [show Measure.map (fun x : EuclideanSpace ℝ (Fin m) =>
          @inner ℝ _ _ (u : EuclideanSpace ℝ (Fin m)) x) ν =
        (stdGaussian ↥S).map (q ∘ L) by
          change (Measure.map affineInclusion (stdGaussian ↥S)).map
              (fun x : EuclideanSpace ℝ (Fin m) =>
                @inner ℝ _ _ (u : EuclideanSpace ℝ (Fin m)) x) = _
          rw [Measure.map_map (by fun_prop) haffine]
          congr 1]
    rw [← Measure.map_map hq hL, hbase]
    simp only [q]
    change (gaussianReal 0 (NNReal.mk (‖u‖ ^ 2) (sq_nonneg _))).map
        ((fun x : ℝ => x + @inner ℝ _ _
          (u : EuclideanSpace ℝ (Fin m))
          (h0 : EuclideanSpace ℝ (Fin m))) ∘ fun x : ℝ => c * x) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop),
      gaussianReal_map_const_mul, mul_zero, gaussianReal_map_add_const, zero_add]
    congr 2

private theorem translatedGaussian_eq_intrinsicGaussian
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) (hc : 0 < c) :
    translatedGaussianOnEffectiveSpan C h0 c = intrinsicGaussian C h0 c :=
  isTranslatedIsotropicGaussian_unique C _ _ h0 c
    (translatedGaussianOnEffectiveSpan_spec C h0 c hc)
    (intrinsicGaussian_spec C h0 c)

private theorem translatedGaussian_map_add
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) (hc : 0 < c) :
    translatedGaussianOnEffectiveSpan C h0 c =
      (translatedGaussianOnEffectiveSpan C 0 c).map
        (fun x : EuclideanSpace ℝ (Fin m) => (h0 : EuclideanSpace ℝ (Fin m)) + x) := by
  rw [translatedGaussian_eq_intrinsicGaussian C h0 c hc,
    translatedGaussian_eq_intrinsicGaussian C 0 c hc]
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let hSborel : BorelSpace ↥S := Subtype.borelSpace _
  letI : BorelSpace ↥S := hSborel
  simp only [intrinsicGaussian]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp

private theorem translatedGaussian_ball_compl_translate
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) (hc : 0 < c) (R : ℝ) :
    translatedGaussianOnEffectiveSpan C h0 c
        (Metric.ball (h0 : EuclideanSpace ℝ (Fin m)) R)ᶜ =
      translatedGaussianOnEffectiveSpan C 0 c (Metric.ball 0 R)ᶜ := by
  rw [translatedGaussian_map_add C h0 c hc,
    Measure.map_apply (by fun_prop) measurableSet_ball.compl]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_ball]
  simp

private theorem intrinsicGaussian_eq_coordinate
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h0 : ↥(effectiveSpan C)) (c : ℝ) :
    let r := Module.finrank ℝ ↥(effectiveSpan C)
    let b := stdOrthonormalBasis ℝ ↥(effectiveSpan C)
    intrinsicGaussian C h0 c =
      (multivariateGaussian (b.repr h0)
        ((c ^ 2) • (1 : Matrix (Fin r) (Fin r) ℝ))).map
        (fun x => ((b.repr.symm x : ↥(effectiveSpan C)) :
          EuclideanSpace ℝ (Fin m))) := by
  dsimp only
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let hSborel : BorelSpace ↥S := Subtype.borelSpace _
  letI : BorelSpace ↥S := hSborel
  let r := Module.finrank ℝ ↥S
  let b := stdOrthonormalBasis ℝ ↥S
  let e := b.repr
  have he : Measurable e := by fun_prop
  have hes : Measurable e.symm := by fun_prop
  have hsub : Measurable S.subtypeL := by fun_prop
  have hsube : Measurable (fun x : EuclideanSpace ℝ (Fin r) =>
      ((e.symm x : ↥S) : EuclideanSpace ℝ (Fin m))) := by fun_prop
  have hadd : Measurable (fun x : EuclideanSpace ℝ (Fin r) => e h0 + x) := by
    fun_prop
  simp only [intrinsicGaussian]
  change (stdGaussian ↥S).map
      (fun z => ((h0 + c • z : ↥S) : EuclideanSpace ℝ (Fin m))) =
    (multivariateGaussian (e h0)
      ((c ^ 2) • (1 : Matrix (Fin r) (Fin r) ℝ))).map
      (fun x => ((e.symm x : ↥S) : EuclideanSpace ℝ (Fin m)))
  have htrans := multivariateGaussian_map_add_left (e h0) 0
    ((c ^ 2) • (1 : Matrix (Fin r) (Fin r) ℝ))
  simp only [add_zero] at htrans
  rw [← htrans]
  rw [AsymptoticStatistics.ForMathlib.multivariateGaussian_eq_stdGaussian_map_smul]
  have hstd : (stdGaussian ↥S).map e = stdGaussian (EuclideanSpace ℝ (Fin r)) :=
    @stdGaussian_map ↥S _ _ _ _ hSborel
      (EuclideanSpace ℝ (Fin r)) _ _ _ _ e
  rw [← hstd]
  rw [Measure.map_map hsube hadd,
    Measure.map_map (hsube.comp hadd) (by fun_prop)]
  symm
  calc
    Measure.map
        (((fun x => ((e.symm x : ↥S) : EuclideanSpace ℝ (Fin m))) ∘
          (fun x => e h0 + x)) ∘ fun x => c • x)
        (Measure.map e (stdGaussian ↥S)) =
      Measure.map
        ((((fun x => ((e.symm x : ↥S) : EuclideanSpace ℝ (Fin m))) ∘
          (fun x => e h0 + x)) ∘ fun x => c • x) ∘ e)
        (stdGaussian ↥S) := Measure.map_map (by fun_prop) he
    _ = Measure.map (fun z =>
        ((h0 + c • z : ↥S) : EuclideanSpace ℝ (Fin m)))
        (stdGaussian ↥S) := by
      congr 1
      funext z
      simp [e]

private theorem stdGaussian_eq_map_orthogonal_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (S : Submodule ℝ E) :
    ((stdGaussian ↥S).prod (stdGaussian ↥Sᗮ)).map
        (fun p => (p.1 : E) + (p.2 : E)) = stdGaussian E := by
  let hSborel : BorelSpace ↥S := Subtype.borelSpace _
  let hSperpborel : BorelSpace ↥Sᗮ := Subtype.borelSpace _
  letI := hSborel
  letI := hSperpborel
  letI : SecondCountableTopology ↥S :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  letI : SecondCountableTopology ↥Sᗮ :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let hsecond : SecondCountableTopologyEither ↥S ↥Sᗮ := inferInstance
  let hWithBorel : BorelSpace (WithLp 2 (↥S × ↥Sᗮ)) :=
    @WithLp.borelSpace 2 ↥S _ ↥Sᗮ _ _ _ hSborel hSperpborel hsecond
  letI := hWithBorel
  let e := S.orthogonalDecomposition
  have hsum : (fun p : ↥S × ↥Sᗮ => (p.1 : E) + (p.2 : E)) =
      (fun z : WithLp 2 (↥S × ↥Sᗮ) => e.symm z) ∘ WithLp.toLp 2 := by
    funext p
    simp [e]
  rw [hsum, ← Measure.map_map (by fun_prop) (by fun_prop),
    show ((stdGaussian ↥S).prod (stdGaussian ↥Sᗮ)).map (WithLp.toLp 2) =
        stdGaussian (WithLp 2 (↥S × ↥Sᗮ)) from
      @stdGaussian_prod_map_toLp ↥S ↥Sᗮ _ _ _ _ hSborel _ _ _ _ hSperpborel]
  exact @stdGaussian_map (WithLp 2 (↥S × ↥Sᗮ)) _ _ _ _ hWithBorel
    E _ _ _ _ e.symm

/-- Restriction of the target functional to the effective span. -/
noncomputable def effectiveA (C : Set (EuclideanSpace ℝ (Fin m)))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) : ↥(effectiveSpan C) →L[ℝ] ℝ :=
  A.comp (effectiveSpan C).subtypeL

/-- Operator scale on the effective span, defined directly through
`effectiveA` so the zero-dimensional span is supported. -/
noncomputable def effectiveScale (C : Set (EuclideanSpace ℝ (Fin m)))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : ↥(effectiveSpan C), ‖x‖ ≤ 1 ∧
    r = |effectiveA C A x|}

private theorem effectiveScale_eq_opNorm
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :
    effectiveScale C A = ContinuousLinearMap.opNorm (effectiveA C A) := by
  letI : FiniteDimensional ℝ ↥(effectiveSpan C) :=
    FiniteDimensional.of_injective (effectiveSpan C).subtype
      (effectiveSpan C).injective_subtype
  letI : Norm (↥(effectiveSpan C) →L[ℝ] ℝ) :=
    ContinuousLinearMap.hasOpNorm
  let f := effectiveA C A
  let R : Set ℝ := {r | ∃ x : ↥(effectiveSpan C), ‖x‖ ≤ 1 ∧ r = |f x|}
  have hRne : R.Nonempty := by
    refine ⟨0, 0, by simp [f]⟩
  have hRbdd : BddAbove R := by
    refine ⟨‖f‖, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    simpa [Real.norm_eq_abs] using f.le_opNorm_of_le hx
  apply le_antisymm
  · unfold effectiveScale
    apply csSup_le hRne
    rintro r ⟨x, hx, rfl⟩
    simpa [Real.norm_eq_abs] using! f.le_opNorm_of_le hx
  · apply f.opNorm_le_bound
    · exact le_csSup hRbdd ⟨(0 : ↥(effectiveSpan C)), by simp, by simp⟩
    · intro x
      by_cases hx0 : x = 0
      · subst x
        simp
      let y : ↥(effectiveSpan C) := ‖x‖⁻¹ • x
      have hy : ‖y‖ ≤ 1 := by
        simp [y, norm_smul, hx0]
      have hmem : |f y| ∈ R := ⟨y, hy, rfl⟩
      have hle : |f y| ≤ sSup R := le_csSup hRbdd hmem
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hxne : ‖(x : EuclideanSpace ℝ (Fin m))‖ ≠ 0 := hxpos.ne'
      have hxy : ‖x‖ • y = x := by
        dsimp [y]
        rw [smul_smul, mul_inv_cancel₀ hxne, one_smul]
      have hfx : f x = ‖x‖ • f y := by
        calc
          f x = f (‖x‖ • y) := congrArg f hxy.symm
          _ = ‖x‖ • f y := map_smul f _ _
      have hscale : |f x| = |f y| * ‖x‖ := by
        rw [hfx]
        simp [abs_mul, mul_comm]
      rw [Real.norm_eq_abs]
      change |f x| ≤ sSup R * ‖x‖
      rw [hscale]
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg x)

private noncomputable def scalarToFin1CLM {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E →L[ℝ] ℝ) : E →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.single ℝ (fun _ : Fin 1 => ℝ) 0).comp F)

private noncomputable def scalarMatrix {k : ℕ}
    (F : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) :
    Matrix (Fin 1) (Fin k) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
    (scalarToFin1CLM F).toLinearMap

private theorem matrixActionVec_scalarMatrix {k : ℕ}
    (F : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    matrixActionVec (scalarMatrix F) x = scalarToFin1CLM F x := by
  apply (WithLp.equiv 2 _).injective
  change (matrixActionVec (scalarMatrix F) x).ofLp =
    (scalarToFin1CLM F x).ofLp
  rw [show (matrixActionVec (scalarMatrix F) x).ofLp =
      (scalarMatrix F).mulVec x.ofLp from rfl]
  exact LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
    (scalarToFin1CLM F).toLinearMap x

private theorem scalarMatrix_mul_transpose_apply
    {k : ℕ} (F : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) :
    (scalarMatrix F * (scalarMatrix F).transpose) 0 0 =
      ContinuousLinearMap.opNorm F ^ 2 := by
  letI : Norm (EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) :=
    ContinuousLinearMap.hasOpNorm
  change (scalarMatrix F * (scalarMatrix F).transpose) 0 0 = ‖F‖ ^ 2
  rw [Matrix.mul_apply, OrthonormalBasis.norm_dual
    (EuclideanSpace.basisFun (Fin k) ℝ) F]
  apply Finset.sum_congr rfl
  intro j hj
  simp [scalarMatrix, scalarToFin1CLM, LinearMap.toMatrix_apply, pow_two]

private theorem scalarGaussian_lintegral_eq_fin1 {k : ℕ}
    (F : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ u, g u ∂(gaussianReal 0
        ⟨ContinuousLinearMap.opNorm F ^ 2, sq_nonneg _⟩) =
      ∫⁻ y : EuclideanSpace ℝ (Fin 1), g (y 0)
        ∂(multivariateGaussian 0 (scalarMatrix F * (scalarMatrix F).transpose)) := by
  let Q := scalarMatrix F * (scalarMatrix F).transpose
  have hQpsd : Q.PosSemidef := by
    have h := Matrix.PosSemidef.one.mul_mul_conjTranspose_same (scalarMatrix F)
    simpa [Q, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hentry : Q 0 0 = ContinuousLinearMap.opNorm F ^ 2 := by
    exact scalarMatrix_mul_transpose_apply F
  have hMP : MeasurePreserving
      (fun y : EuclideanSpace ℝ (Fin 1) => y 0)
      (multivariateGaussian 0 Q)
      (gaussianReal 0 ⟨ContinuousLinearMap.opNorm F ^ 2, sq_nonneg _⟩) := by
    have hbase := measurePreserving_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ (Fin 1))) (S := Q) hQpsd (i := (0 : Fin 1))
    have hvar : (Q 0 0).toNNReal =
        (NNReal.mk (ContinuousLinearMap.opNorm F ^ 2) (sq_nonneg _)) := by
      rw [hentry]
      apply NNReal.eq
      simp only [Real.coe_toNNReal _ (sq_nonneg _), NNReal.coe_mk]
    simpa [hvar] using! hbase
  exact (hMP.lintegral_comp hg).symm

private noncomputable def coordinateFunctional
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(effectiveSpan C))) →L[ℝ] ℝ := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  exact (effectiveA C A).comp
    (stdOrthonormalBasis ℝ ↥S).repr.symm.toContinuousLinearMap

private theorem coordinateFunctional_opNorm
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :
    ContinuousLinearMap.opNorm (coordinateFunctional C A) =
      ContinuousLinearMap.opNorm (effectiveA C A) := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let r := Module.finrank ℝ ↥S
  let e := (stdOrthonormalBasis ℝ ↥S).repr
  let f := effectiveA C A
  let g := coordinateFunctional C A
  letI : Norm (↥S →L[ℝ] ℝ) := ContinuousLinearMap.hasOpNorm
  letI : Norm (EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ) :=
    ContinuousLinearMap.hasOpNorm
  change ‖g‖ = ‖f‖
  apply le_antisymm
  · apply g.opNorm_le_bound (ContinuousLinearMap.opNorm_nonneg _)
    intro x
    change ‖f (e.symm x)‖ ≤ ‖f‖ * ‖x‖
    simpa only [e.symm.norm_map] using f.le_opNorm (e.symm x)
  · apply f.opNorm_le_bound (ContinuousLinearMap.opNorm_nonneg _)
    intro x
    have h := g.le_opNorm (e x)
    change ‖f (e.symm (e x))‖ ≤ ‖g‖ * ‖e x‖ at h
    change ‖f x‖ ≤ ‖g‖ * ‖x‖
    simpa only [e.symm_apply_apply, e.norm_map] using h

set_option maxHeartbeats 800000 in
-- Expanding the orthogonal-product Gaussian transport needs extra simplifier budget.
private theorem multivariateGaussian_coordinate_prod
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (h : ↥(effectiveSpan C)) :
    let r := Module.finrank ℝ ↥(effectiveSpan C)
    let e := (stdOrthonormalBasis ℝ ↥(effectiveSpan C)).repr
    ((multivariateGaussian (e h) (1 : Matrix (Fin r) (Fin r) ℝ)).prod
      (stdGaussian ↥(effectiveSpan C)ᗮ)).map
      (fun p => ((e.symm p.1 : ↥(effectiveSpan C)) :
          EuclideanSpace ℝ (Fin m)) +
        (p.2 : EuclideanSpace ℝ (Fin m))) =
      multivariateGaussian (h : EuclideanSpace ℝ (Fin m))
        (1 : Matrix (Fin m) (Fin m) ℝ) := by
  dsimp only
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let hSborel : BorelSpace ↥S := Subtype.borelSpace _
  let hSperpborel : BorelSpace ↥Sᗮ := Subtype.borelSpace _
  letI : BorelSpace ↥S := hSborel
  letI : BorelSpace ↥Sᗮ := hSperpborel
  letI : IsProbabilityMeasure (stdGaussian ↥S) :=
    @isProbabilityMeasure_stdGaussian _ _ _ _ _ hSborel
  letI : IsProbabilityMeasure (stdGaussian ↥Sᗮ) :=
    @isProbabilityMeasure_stdGaussian _ _ _ _ _ hSperpborel
  let r := Module.finrank ℝ ↥S
  let e := (stdOrthonormalBasis ℝ ↥S).repr
  have he : Measurable e := by fun_prop
  have hes : Measurable e.symm := by fun_prop
  have hperp : Measurable (fun z : ↥Sᗮ =>
      (z : EuclideanSpace ℝ (Fin m))) := by fun_prop
  have hsum : Measurable (fun p : ↥S × ↥Sᗮ =>
      (p.1 : EuclideanSpace ℝ (Fin m)) +
        (p.2 : EuclideanSpace ℝ (Fin m))) := by fun_prop
  rw [multivariateGaussian_eq_translate]
  rw [multivariateGaussian_zero_one]
  rw [multivariateGaussian_eq_translate]
  rw [multivariateGaussian_zero_one]
  have hstd : (stdGaussian ↥S).map e = stdGaussian (EuclideanSpace ℝ (Fin r)) :=
    @stdGaussian_map ↥S _ _ _ _ hSborel
      (EuclideanSpace ℝ (Fin r)) _ _ _ _ e
  rw [← hstd]
  have hid : (stdGaussian ↥Sᗮ).map id = stdGaussian ↥Sᗮ := Measure.map_id
  rw [← hid]
  rw [Measure.map_prod_map _ _ (measurable_const_add _) measurable_id]
  rw [← hid]
  rw [Measure.map_prod_map _ _ he measurable_id]
  rw [Measure.map_map (by fun_prop) (he.prodMap measurable_id)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [← stdGaussian_eq_map_orthogonal_sum S]
  rw [Measure.map_map (by fun_prop) hsum]
  congr 1
  funext p
  simp only [Function.comp_apply]
  dsimp only [Prod.map]
  change (e.symm (e h + e p.1) : ↥S) +
      (p.2 : EuclideanSpace ℝ (Fin m)) =
    (h : EuclideanSpace ℝ (Fin m)) +
      ((p.1 : EuclideanSpace ℝ (Fin m)) +
        (p.2 : EuclideanSpace ℝ (Fin m)))
  rw [map_add, e.symm_apply_apply, e.symm_apply_apply, Submodule.coe_add, add_assoc]

private noncomputable def scalarCoordinateKernel
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f}) :
    Kernel
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(effectiveSpan C))))
      (EuclideanSpace ℝ (Fin 1)) := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let hSperpborel : BorelSpace ↥Sᗮ := Subtype.borelSpace _
  letI : BorelSpace ↥Sᗮ := hSperpborel
  let r := Module.finrank ℝ ↥S
  let e := (stdOrthonormalBasis ℝ ↥S).repr
  let η : Kernel (EuclideanSpace ℝ (Fin r)) ↥Sᗮ :=
    Kernel.const _ (stdGaussian ↥Sᗮ)
  let act : EuclideanSpace ℝ (Fin r) × ↥Sᗮ →
      EuclideanSpace ℝ (Fin 1) := fun p =>
    EuclideanSpace.single 0 (T.1
      (((e.symm p.1 : ↥S) : EuclideanSpace ℝ (Fin m)) +
        (p.2 : EuclideanSpace ℝ (Fin m))))
  exact (Kernel.id ×ₖ η).map act

private theorem scalarCoordinateKernel_markov
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f}) :
    IsMarkovKernel (scalarCoordinateKernel C T) := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let hSperpborel : BorelSpace ↥Sᗮ := Subtype.borelSpace _
  letI : BorelSpace ↥Sᗮ := hSperpborel
  letI : IsProbabilityMeasure (stdGaussian ↥Sᗮ) :=
    @isProbabilityMeasure_stdGaussian _ _ _ _ _ hSperpborel
  let r := Module.finrank ℝ ↥S
  let e := (stdOrthonormalBasis ℝ ↥S).repr
  let η : Kernel (EuclideanSpace ℝ (Fin r)) ↥Sᗮ :=
    Kernel.const _ (stdGaussian ↥Sᗮ)
  let act : EuclideanSpace ℝ (Fin r) × ↥Sᗮ →
      EuclideanSpace ℝ (Fin 1) := fun p =>
    EuclideanSpace.single 0 (T.1
      (((e.symm p.1 : ↥S) : EuclideanSpace ℝ (Fin m)) +
        (p.2 : EuclideanSpace ℝ (Fin m))))
  have hobs : Measurable (fun p : EuclideanSpace ℝ (Fin r) × ↥Sᗮ =>
      ((e.symm p.1 : ↥S) : EuclideanSpace ℝ (Fin m)) +
        (p.2 : EuclideanSpace ℝ (Fin m))) := by fun_prop
  have hsingle : Measurable (fun a : ℝ =>
      EuclideanSpace.single (0 : Fin 1) a) := by
    exact ((EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 1 => ℝ) 0)).continuous.measurable
  have hact : Measurable act := hsingle.comp (T.2.comp hobs)
  change IsMarkovKernel ((Kernel.id ×ₖ η).map act)
  letI : IsMarkovKernel η := inferInstance
  letI : IsMarkovKernel (Kernel.id ×ₖ η) := inferInstance
  exact Kernel.IsMarkovKernel.map _ hact

set_option maxHeartbeats 800000 in
-- Kernel bind normalization through the coordinate isometry is simplifier-intensive.
private theorem scalarCoordinateKernel_bind
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f})
    (h : ↥(effectiveSpan C)) :
    let r := Module.finrank ℝ ↥(effectiveSpan C)
    (multivariateGaussian
        ((stdOrthonormalBasis ℝ ↥(effectiveSpan C)).repr h)
        (1 : Matrix (Fin r) (Fin r) ℝ)).bind
        (scalarCoordinateKernel C T) =
      (multivariateGaussian (h : EuclideanSpace ℝ (Fin m))
        (1 : Matrix (Fin m) (Fin m) ℝ)).map
        (fun x => EuclideanSpace.single (0 : Fin 1) (T.1 x)) := by
  dsimp only
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let hSborel : BorelSpace ↥S := Subtype.borelSpace _
  let hSperpborel : BorelSpace ↥Sᗮ := Subtype.borelSpace _
  letI : BorelSpace ↥S := hSborel
  letI : BorelSpace ↥Sᗮ := hSperpborel
  letI : IsProbabilityMeasure (stdGaussian ↥S) :=
    @isProbabilityMeasure_stdGaussian _ _ _ _ _ hSborel
  letI : IsProbabilityMeasure (stdGaussian ↥Sᗮ) :=
    @isProbabilityMeasure_stdGaussian _ _ _ _ _ hSperpborel
  let r := Module.finrank ℝ ↥S
  let e := (stdOrthonormalBasis ℝ ↥S).repr
  let μ := multivariateGaussian (e h) (1 : Matrix (Fin r) (Fin r) ℝ)
  let η : Kernel (EuclideanSpace ℝ (Fin r)) ↥Sᗮ :=
    Kernel.const _ (stdGaussian ↥Sᗮ)
  let obs : EuclideanSpace ℝ (Fin r) × ↥Sᗮ →
      EuclideanSpace ℝ (Fin m) := fun p =>
    ((e.symm p.1 : ↥S) : EuclideanSpace ℝ (Fin m)) +
      (p.2 : EuclideanSpace ℝ (Fin m))
  let out : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 1) :=
    fun x => EuclideanSpace.single 0 (T.1 x)
  let act : EuclideanSpace ℝ (Fin r) × ↥Sᗮ →
      EuclideanSpace ℝ (Fin 1) := out ∘ obs
  have hobs : Measurable obs := by fun_prop
  have hout : Measurable out := by
    have hsingle : Measurable (fun a : ℝ =>
        EuclideanSpace.single (0 : Fin 1) a) :=
      ((EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 1 => ℝ) 0)).continuous.measurable
    exact hsingle.comp T.2
  have hact : Measurable act := hout.comp hobs
  change ((Kernel.id ×ₖ η).map act) ∘ₘ μ = _
  rw [← Measure.map_comp μ (Kernel.id ×ₖ η) hact]
  rw [← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  have hnoise := multivariateGaussian_coordinate_prod C h
  change (μ.prod (stdGaussian ↥Sᗮ)).map act = _
  change (μ.prod (stdGaussian ↥Sᗮ)).map (out ∘ obs) = _
  rw [← Measure.map_map hout hobs, hnoise]

private def scalarLossFin1 (ℓ : ℝ → ℝ≥0∞) :
    EuclideanSpace ℝ (Fin 1) → ℝ≥0∞ := fun y => ℓ (y 0)

private theorem scalarLossFin1_bowl
    (ℓ : ℝ → ℝ≥0∞) (hℓ : BowlShaped ℓ) :
    BowlShaped (scalarLossFin1 ℓ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hℓ.measurable.comp <|
      (measurable_pi_apply 0).comp <| WithLp.measurable_ofLp 2 (Fin 1 → ℝ)
  · intro y
    exact hℓ.symm (y 0)
  · intro c
    have hset : {y : EuclideanSpace ℝ (Fin 1) | scalarLossFin1 ℓ y ≤ c} =
        (fun y : EuclideanSpace ℝ (Fin 1) => y 0) ⁻¹' {x : ℝ | ℓ x ≤ c} := rfl
    rw [hset]
    exact (hℓ.convex_sublevel c).linear_preimage
      { toFun := fun y : EuclideanSpace ℝ (Fin 1) => y 0
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }

private theorem scalarLossFin1_lsc
    (ℓ : ℝ → ℝ≥0∞) (hℓ : LowerSemicontinuous ℓ) :
    LowerSemicontinuous (scalarLossFin1 ℓ) := by
  exact hℓ.comp <| (continuous_apply (0 : Fin 1)).comp <|
    PiLp.continuous_ofLp 2 (fun _ : Fin 1 => ℝ)

private theorem coordinateFunctional_repr
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (h : ↥(effectiveSpan C)) :
    coordinateFunctional C A
        ((stdOrthonormalBasis ℝ ↥(effectiveSpan C)).repr h) = A h := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  change effectiveA C A
      ((stdOrthonormalBasis ℝ ↥S).repr.symm
        ((stdOrthonormalBasis ℝ ↥S).repr h)) = A h
  rw [(stdOrthonormalBasis ℝ ↥S).repr.symm_apply_apply]
  rfl

set_option maxHeartbeats 800000 in
-- Rewriting the kernel risk through both Gaussian transports needs extra elaboration budget.
private theorem gaussianShiftKernelRiskVec_coordinate
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (ℓ : ℝ → ℝ≥0∞) (hℓ : Measurable ℓ)
    (T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f})
    (h : ↥(effectiveSpan C)) :
    let r := Module.finrank ℝ ↥(effectiveSpan C)
    let e := (stdOrthonormalBasis ℝ ↥(effectiveSpan C)).repr
    let F := coordinateFunctional C A
    let κ : MarkovDecision (EuclideanSpace ℝ (Fin r))
        (EuclideanSpace ℝ (Fin 1)) :=
      ⟨scalarCoordinateKernel C T, scalarCoordinateKernel_markov C T⟩
    gaussianShiftKernelRiskVec (scalarMatrix F) (scalarLossFin1 ℓ) κ (e h) =
      ∫⁻ X, ℓ (T.1 X - A h)
        ∂(multivariateGaussian (h : EuclideanSpace ℝ (Fin m))
          (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  dsimp only
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let r := Module.finrank ℝ ↥S
  let e := (stdOrthonormalBasis ℝ ↥S).repr
  let F := coordinateFunctional C A
  let κ : MarkovDecision (EuclideanSpace ℝ (Fin r))
      (EuclideanSpace ℝ (Fin 1)) :=
    ⟨scalarCoordinateKernel C T, scalarCoordinateKernel_markov C T⟩
  unfold gaussianShiftKernelRiskVec
  rw [scalarCoordinateKernel_bind C T h]
  rw [lintegral_map (by
    have heval : Measurable (fun y : EuclideanSpace ℝ (Fin 1) => y 0) :=
      (measurable_pi_apply 0).comp (WithLp.measurable_ofLp 2 (Fin 1 → ℝ))
    exact hℓ.comp (heval.comp (measurable_id.sub_const _))) (by
      exact ((EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 1 => ℝ) 0)).continuous.measurable.comp T.2)]
  refine lintegral_congr fun X => ?_
  rw [matrixActionVec_scalarMatrix]
  change ℓ (T.1 X - F (e h)) = ℓ (T.1 X - A h)
  rw [coordinateFunctional_repr]

private theorem scalarGaussianRisk_measurable
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (ℓ : ℝ → ℝ≥0∞) (hℓ : Measurable ℓ)
    (T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f}) :
    Measurable (fun h : EuclideanSpace ℝ (Fin m) =>
      ∫⁻ X, ℓ (T.1 X - A h)
        ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ))) := by
  have hjoint : Measurable (fun p : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) =>
      ℓ (T.1 (p.1 + p.2) - A p.1)) :=
    hℓ.comp ((T.2.comp (measurable_fst.add measurable_snd)).sub
      (A.continuous.measurable.comp measurable_fst))
  have hout : Measurable (fun h : EuclideanSpace ℝ (Fin m) =>
      ∫⁻ z, ℓ (T.1 (h + z) - A h)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))) :=
    hjoint.lintegral_prod_right'
  convert hout using 1
  funext h
  rw [multivariateGaussian_eq_translate, multivariateGaussian_zero_one]
  exact lintegral_map
    (hℓ.comp (T.2.sub measurable_const)) (measurable_const_add h)

noncomputable def measurableBayesRisk
    (π : Measure (EuclideanSpace ℝ (Fin m)))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (ℓ : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
    ∫⁻ h, ∫⁻ X, ℓ (T.1 X - A h)
      ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)) ∂π

/-- A sufficiently deep and diffuse intrinsic Gaussian cone prior approaches
the effective-span benchmark.  The center and scale are existential outputs;
the theorem does not claim the comparison for an arbitrary fixed prior.

Proof idea: derive an effective relative-interior ball, choose a translated
Gaussian center/scale far enough inside the cone, condition it, and combine
Gaussian flattening with bounded uniformly-continuous risk control. -/
theorem exists_conePrior_bayes_lower_bound
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (_hzero : (0 : EuclideanSpace ℝ (Fin m)) ∈ C)
    (_hconv : Convex ℝ C)
    (_hcone : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (ℓ : ℝ → ℝ≥0∞)
    (_hbowl : BowlShaped ℓ) (_hlsc : LowerSemicontinuous ℓ)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (ε : ℝ≥0∞) (_hε : 0 < ε) :
    ∃ (h0 : ↥(effectiveSpan C)) (c : ℝ), 0 < c ∧
      IsTranslatedIsotropicGaussian C
        (translatedGaussianOnEffectiveSpan C h0 c) h0 c ∧
      0 < conePriorNormalizer C h0 c ∧
      conePriorNormalizer C h0 c < ∞ ∧
      IsProbabilityMeasure (restrictedTranslatedGaussianPrior C h0 c) ∧
      restrictedTranslatedGaussianPrior C h0 c C = 1 ∧
      (∫⁻ u, ℓ u ∂(gaussianReal 0
        ⟨effectiveScale C A ^ 2, sq_nonneg _⟩)) ≤
        measurableBayesRisk (restrictedTranslatedGaussianPrior C h0 c) A ℓ + ε := by
  let S := effectiveSpan C
  letI : FiniteDimensional ℝ ↥S :=
    FiniteDimensional.of_injective S.subtype S.injective_subtype
  let r := Module.finrank ℝ ↥S
  let eS := (stdOrthonormalBasis ℝ ↥S).repr
  let F := coordinateFunctional C A
  let AF := scalarMatrix F
  let L := scalarLossFin1 ℓ
  have hL_bowl : BowlShaped L := scalarLossFin1_bowl ℓ _hbowl
  have hL_lsc : LowerSemicontinuous L := scalarLossFin1_lsc ℓ _hlsc
  let target : ℝ≥0∞ := ∫⁻ u, ℓ u ∂(gaussianReal 0
    (NNReal.mk (effectiveScale C A ^ 2) (sq_nonneg _)))
  let targetVec : ℝ≥0∞ :=
    ∫⁻ y, L y ∂(multivariateGaussian 0 (AF * AF.transpose))
  have htarget_eq : target = targetVec := by
    dsimp [target, targetVec, L, AF]
    rw [effectiveScale_eq_opNorm, ← coordinateFunctional_opNorm C A]
    exact scalarGaussian_lintegral_eq_fin1 F ℓ _hbowl.measurable
  let e : ℝ≥0∞ := ε / 2
  have he : 0 < e := ENNReal.half_pos _hε.ne'
  have hee : e + e = ε := ENNReal.add_halves ε
  rcases _hbdd with ⟨B, hBtop, hB⟩
  have htarget_le : target ≤ B := by
    dsimp [target]
    calc
      ∫⁻ u, ℓ u ∂(gaussianReal 0 (NNReal.mk (effectiveScale C A ^ 2) (sq_nonneg _))) ≤
          ∫⁻ _u, B ∂(gaussianReal 0 (NNReal.mk (effectiveScale C A ^ 2) (sq_nonneg _))) :=
        lintegral_mono fun u => hB u
      _ = B := by simp
  have htarget_top : target ≠ ∞ := ne_of_lt (htarget_le.trans_lt hBtop)
  have hsup :
      (⨆ τ ∈ Set.Ioi (0 : ℝ),
        bayesRiskAtTau (1 : Matrix (Fin r) (Fin r) ℝ) AF L τ) = target := by
    rw [htarget_eq]
    simpa [targetVec] using
      (gaussianShift_bayes_risk_sup_eq_target Matrix.PosDef.one AF L hL_bowl hL_lsc)
  obtain ⟨τ, hτ, htargetτ⟩ : ∃ τ : ℝ, 0 < τ ∧
      target ≤ bayesRiskAtTau (1 : Matrix (Fin r) (Fin r) ℝ) AF L τ + e := by
    by_cases hsmall : target ≤ e
    · refine ⟨1, by norm_num, hsmall.trans ?_⟩
      exact le_add_left le_rfl
    · have htarget0 : target ≠ 0 := by
        intro hz
        apply hsmall
        rw [hz]
        exact bot_le
      have hsub : target - e < target :=
        ENNReal.sub_lt_self htarget_top htarget0 he.ne'
      rw [← hsup] at hsub
      rcases lt_iSup_iff.mp hsub with ⟨τ, hsub⟩
      rcases lt_iSup_iff.mp hsub with ⟨hτ, hsub⟩
      refine ⟨τ, hτ, ?_⟩
      have hsub' : target - e <
          bayesRiskAtTau (1 : Matrix (Fin r) (Fin r) ℝ) AF L τ := by
        simpa only [hsup] using hsub
      calc
        target = target - e + e :=
          (tsub_add_cancel_of_le (le_of_not_ge hsmall)).symm
        _ ≤ bayesRiskAtTau (1 : Matrix (Fin r) (Fin r) ℝ) AF L τ + e :=
          add_le_add_left hsub'.le e
  rcases ENNReal.exists_pos_mul_lt hBtop.ne he.ne' with ⟨δ, hδ, hδB⟩
  let P₀ : Measure (EuclideanSpace ℝ (Fin m)) :=
    translatedGaussianOnEffectiveSpan C 0 τ
  have hP₀spec := translatedGaussianOnEffectiveSpan_spec C 0 τ hτ
  letI : IsProbabilityMeasure P₀ := hP₀spec.1
  rcases exists_ball_compl_measure_lt P₀ δ hδ with ⟨n, hn⟩
  rcases exists_effectiveInteriorBall C _hzero _hconv with ⟨v, rv, hrv, hv⟩
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  rcases cone_ball_of_radius C _hcone v rv hrv hv R hR with ⟨h₀, hball⟩
  let ν : Measure (EuclideanSpace ℝ (Fin m)) :=
    translatedGaussianOnEffectiveSpan C h₀ τ
  have hνspec := translatedGaussianOnEffectiveSpan_spec C h₀ τ hτ
  letI : IsProbabilityMeasure ν := hνspec.1
  have hSmeas : MeasurableSet (S : Set (EuclideanSpace ℝ (Fin m))) :=
    S.closed_of_finiteDimensional.measurableSet
  have hνS : ∀ᵐ x ∂ν, x ∈ S :=
    (mem_ae_iff_prob_eq_one hSmeas).2 hνspec.2.1
  have htail : ν (toMeasurable ν C)ᶜ < δ := by
    calc
      ν (toMeasurable ν C)ᶜ ≤
          ν (Metric.ball (h₀ : EuclideanSpace ℝ (Fin m)) R)ᶜ := by
        apply measure_mono_ae
        filter_upwards [hνS] with x hxS
        intro hxC hxball
        let xs : ↥S := ⟨x, hxS⟩
        have hxsball : xs ∈ Metric.ball h₀ R := by exact hxball
        exact hxC (subset_toMeasurable ν C (hball hxsball))
      _ = P₀ (Metric.ball 0 R)ᶜ := by
        exact translatedGaussian_ball_compl_translate C h₀ τ hτ R
      _ ≤ P₀ (Metric.ball 0 (n : ℝ))ᶜ := by
        exact measure_mono (Set.compl_subset_compl.mpr
          (Metric.ball_subset_ball (by dsimp [R]; linarith)))
      _ < δ := hn
  have htailB : B * ν (toMeasurable ν C)ᶜ < e := by
    calc
      B * ν (toMeasurable ν C)ᶜ =
          ν (toMeasurable ν C)ᶜ * B := mul_comm _ _
      _ ≤ δ * B := mul_le_mul_left htail.le B
      _ < e := hδB
  have hspec := restrictedTranslatedGaussianPrior_spec C h₀ R τ hR hball hτ
  refine ⟨h₀, τ, hτ, hspec.2.2.1, hspec.1, hspec.2.1,
    hspec.2.2.2.1, hspec.2.2.2.2, ?_⟩
  change target ≤ measurableBayesRisk
    (restrictedTranslatedGaussianPrior C h₀ τ) A ℓ + ε
  rw [measurableBayesRisk, ENNReal.iInf_add]
  refine le_iInf fun T => ?_
  let κ : MarkovDecision (EuclideanSpace ℝ (Fin r))
      (EuclideanSpace ℝ (Fin 1)) :=
    ⟨scalarCoordinateKernel C T, scalarCoordinateKernel_markov C T⟩
  have hνeqcoord : ν =
      (multivariateGaussian (eS h₀)
        ((τ ^ 2) • (1 : Matrix (Fin r) (Fin r) ℝ))).map
        (fun x => ((eS.symm x : ↥S) : EuclideanSpace ℝ (Fin m))) := by
    change translatedGaussianOnEffectiveSpan C h₀ τ = _
    rw [translatedGaussian_eq_intrinsicGaussian C h₀ τ hτ]
    exact intrinsicGaussian_eq_coordinate C h₀ τ
  have hBR : bayesRiskAtTau (1 : Matrix (Fin r) (Fin r) ℝ) AF L τ ≤
      ∫⁻ h, ∫⁻ X, ℓ (T.1 X - A h)
          ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)) ∂ν := by
    have hv := bayesRiskAtTau_le_averageKernelVec_translated AF L hL_bowl κ
      (eS h₀) hτ
    rw [hνeqcoord]
    rw [lintegral_map (scalarGaussianRisk_measurable A ℓ _hbowl.measurable T)
      (by fun_prop)]
    refine hv.trans_eq ?_
    refine lintegral_congr fun h => ?_
    change gaussianShiftKernelRiskVec (scalarMatrix (coordinateFunctional C A))
        (scalarLossFin1 ℓ)
        ⟨scalarCoordinateKernel C T, scalarCoordinateKernel_markov C T⟩ h = _
    have hh :=
      gaussianShiftKernelRiskVec_coordinate C A ℓ _hbowl.measurable T (eS.symm h)
    have hrepr : (stdOrthonormalBasis ℝ ↥(effectiveSpan C)).repr
        (eS.symm h) = h := by
      change eS (eS.symm h) = h
      exact eS.apply_symm_apply h
    dsimp only at hh
    rw [hrepr] at hh
    exact hh
  have hrisk_le : ∀ h : EuclideanSpace ℝ (Fin m),
      (∫⁻ X, ℓ (T.1 X - A h)
        ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ))) ≤ B := by
    intro h
    calc
      ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1) ≤
          ∫⁻ _X, B ∂(multivariateGaussian h 1) :=
        lintegral_mono fun X => hB _
      _ = B := by simp
  have hcomp : (∫⁻ h, ∫⁻ X, ℓ (T.1 X - A h)
        ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)) ∂ν) ≤
      (∫⁻ h, ∫⁻ X, ℓ (T.1 X - A h)
        ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ))
          ∂(restrictedTranslatedGaussianPrior C h₀ τ)) + e := by
    have hc := lintegral_le_normalized_restrict_add ν C
      (fun h => ∫⁻ X, ℓ (T.1 X - A h)
        ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ))) B hrisk_le
    have hdef : (conePriorNormalizer C h₀ τ)⁻¹ • ν.restrict C =
        restrictedTranslatedGaussianPrior C h₀ τ := by rfl
    have hnorm : ν C = conePriorNormalizer C h₀ τ := rfl
    rw [hnorm, hdef] at hc
    exact hc.trans (add_le_add_right htailB.le _)
  calc
    target ≤ bayesRiskAtTau (1 : Matrix (Fin r) (Fin r) ℝ) AF L τ + e := htargetτ
    _ ≤ (∫⁻ h, ∫⁻ X, ℓ (T.1 X - A h)
          ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)) ∂ν) + e :=
      add_le_add_left hBR e
    _ ≤ ((∫⁻ h, ∫⁻ X, ℓ (T.1 X - A h)
          ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ))
            ∂(restrictedTranslatedGaussianPrior C h₀ τ)) + e) + e :=
      add_le_add_left hcomp e
    _ = (∫⁻ h, ∫⁻ X, ℓ (T.1 X - A h)
          ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ))
            ∂(restrictedTranslatedGaussianPrior C h₀ τ)) + ε := by
      rw [add_assoc, hee]

/-- Existential diffuse-prior Bayes lower bound. -/
theorem conePrior_bayes_lower_bound
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (_h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ C)
    (_hconv : Convex ℝ C)
    (_hcone : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (ℓ : ℝ → ℝ≥0∞)
    (_hbowl : BowlShaped ℓ) (_hlsc : LowerSemicontinuous ℓ)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (ε : ℝ≥0∞) (_hε : 0 < ε) :
    ∃ (h0 : ↥(effectiveSpan C)) (c : ℝ), 0 < c ∧
      IsTranslatedIsotropicGaussian C
        (translatedGaussianOnEffectiveSpan C h0 c) h0 c ∧
      0 < conePriorNormalizer C h0 c ∧
      conePriorNormalizer C h0 c < ∞ ∧
      IsProbabilityMeasure (restrictedTranslatedGaussianPrior C h0 c) ∧
      restrictedTranslatedGaussianPrior C h0 c C = 1 ∧
      (∫⁻ u, ℓ u ∂(gaussianReal 0
        ⟨effectiveScale C A ^ 2, sq_nonneg _⟩))
      ≤ measurableBayesRisk (restrictedTranslatedGaussianPrior C h0 c) A ℓ + ε := by
  exact exists_conePrior_bayes_lower_bound C _h0 _hconv _hcone A ℓ
    _hbowl _hlsc _hbdd ε _hε

/-- Vector/kernel diffuse-prior Bayes lower bound on a full-span convex cone.
The target covariance is the raw rectangular covariance `A Aᵀ`; no rank,
positive-definiteness, or nonzero-dimension condition is imposed.

Proof idea: apply the intrinsic translated cone prior, use the Markov-kernel
Bayes calculation, and let the intrinsic scale diverge. -/
theorem exists_conePrior_bayes_lower_bound_vec {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (_hzero : (0 : EuclideanSpace ℝ (Fin m)) ∈ C)
    (_hconv : Convex ℝ C)
    (_hcone : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C)
    (_hspan : Submodule.span ℝ C = ⊤)
    (A : Matrix (Fin d) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hbowl : BowlShaped ℓ) (_hlsc : LowerSemicontinuous ℓ)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (ε : ℝ≥0∞) (_hε : 0 < ε) :
    ∃ (h0 : ↥(effectiveSpan C)) (c : ℝ), 0 < c ∧
      IsTranslatedIsotropicGaussian C
        (translatedGaussianOnEffectiveSpan C h0 c) h0 c ∧
      0 < conePriorNormalizer C h0 c ∧
      conePriorNormalizer C h0 c < ∞ ∧
      IsProbabilityMeasure (restrictedTranslatedGaussianPrior C h0 c) ∧
      restrictedTranslatedGaussianPrior C h0 c C = 1 ∧
      (∫⁻ u, ℓ u ∂(multivariateGaussian 0 (A * A.transpose))) ≤
        measurableBayesRiskVec
          (restrictedTranslatedGaussianPrior C h0 c) A ℓ + ε := by
  let e : ℝ≥0∞ := ε / 2
  have he : 0 < e := ENNReal.half_pos _hε.ne'
  have hee : e + e = ε := ENNReal.add_halves ε
  rcases _hbdd with ⟨B, hBtop, hB⟩
  let target : ℝ≥0∞ :=
    ∫⁻ u, ℓ u ∂(multivariateGaussian 0 (A * A.transpose))
  have htarget_le : target ≤ B := by
    dsimp [target]
    calc
      ∫⁻ u, ℓ u ∂(multivariateGaussian 0 (A * A.transpose)) ≤
          ∫⁻ _u, B ∂(multivariateGaussian 0 (A * A.transpose)) :=
        lintegral_mono fun u => hB u
      _ = B := by simp
  have htarget_top : target ≠ ∞ := ne_of_lt (htarget_le.trans_lt hBtop)
  have hsup :
      (⨆ τ ∈ Set.Ioi (0 : ℝ),
        bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ) = target := by
    simpa [target] using
      (gaussianShift_bayes_risk_sup_eq_target Matrix.PosDef.one A ℓ _hbowl _hlsc)
  obtain ⟨τ, hτ, htargetτ⟩ : ∃ τ : ℝ, 0 < τ ∧
      target ≤ bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ + e := by
    by_cases hsmall : target ≤ e
    · refine ⟨1, by norm_num, hsmall.trans ?_⟩
      exact le_add_left le_rfl
    · have htarget0 : target ≠ 0 := by
        intro hz
        apply hsmall
        rw [hz]
        exact bot_le
      have hsub : target - e < target :=
        ENNReal.sub_lt_self htarget_top htarget0 he.ne'
      rw [← hsup] at hsub
      rcases lt_iSup_iff.mp hsub with ⟨τ, hsub⟩
      rcases lt_iSup_iff.mp hsub with ⟨hτ, hsub⟩
      refine ⟨τ, hτ, ?_⟩
      have hsub' : target - e <
          bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ := by
        simpa only [hsup] using hsub
      calc
        target = target - e + e :=
          (tsub_add_cancel_of_le (le_of_not_ge hsmall)).symm
        _ ≤ bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ + e :=
          add_le_add_left hsub'.le e
  rcases ENNReal.exists_pos_mul_lt hBtop.ne he.ne' with ⟨δ, hδ, hδB⟩
  let P₀ : Measure (EuclideanSpace ℝ (Fin m)) :=
    multivariateGaussian 0 ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ))
  haveI : IsProbabilityMeasure P₀ := by
    dsimp [P₀]
    infer_instance
  rcases exists_ball_compl_measure_lt P₀ δ hδ with ⟨n, hn⟩
  rcases exists_effectiveInteriorBall C _hzero _hconv with
    ⟨v, r, hr, hv⟩
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  rcases cone_ball_of_radius C _hcone v r hr hv R hR with ⟨h₀, hball⟩
  have heff : effectiveSpan C = ⊤ := _hspan
  have hamball : Metric.ball (h₀ : EuclideanSpace ℝ (Fin m)) R ⊆ C := by
    intro x hx
    let xs : ↥(effectiveSpan C) := ⟨x, by rw [heff]; trivial⟩
    have hxsball : xs ∈ Metric.ball h₀ R := by
      change dist x (h₀ : EuclideanSpace ℝ (Fin m)) < R
      simpa only [Metric.mem_ball] using hx
    exact hball hxsball
  let ν : Measure (EuclideanSpace ℝ (Fin m)) :=
    translatedGaussianOnEffectiveSpan C h₀ τ
  have hνeq : ν = multivariateGaussian (h₀ : EuclideanSpace ℝ (Fin m))
      ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
    exact translatedGaussian_eq_multivariateGaussian_of_fullSpan C heff h₀ τ hτ
  haveI : IsProbabilityMeasure ν := by
    rw [hνeq]
    infer_instance
  have htail : ν (toMeasurable ν C)ᶜ < δ := by
    calc
      ν (toMeasurable ν C)ᶜ ≤ ν (Metric.ball
          (h₀ : EuclideanSpace ℝ (Fin m)) R)ᶜ :=
        measure_mono (Set.compl_subset_compl.mpr
          (hamball.trans (subset_toMeasurable ν C)))
      _ = P₀ (Metric.ball 0 R)ᶜ := by
        rw [hνeq]
        exact multivariateGaussian_ball_compl_translate
          (h₀ : EuclideanSpace ℝ (Fin m)) _ R
      _ ≤ P₀ (Metric.ball 0 (n : ℝ))ᶜ := by
        exact measure_mono (Set.compl_subset_compl.mpr
          (Metric.ball_subset_ball (by dsimp [R]; linarith)))
      _ < δ := hn
  have htailB : B * ν (toMeasurable ν C)ᶜ < e := by
    calc
      B * ν (toMeasurable ν C)ᶜ =
          ν (toMeasurable ν C)ᶜ * B := mul_comm _ _
      _ ≤ δ * B := mul_le_mul_left htail.le B
      _ < e := hδB
  have hspec := restrictedTranslatedGaussianPrior_spec C h₀ R τ hR hball hτ
  refine ⟨h₀, τ, hτ, hspec.2.2.1, hspec.1, hspec.2.1,
    hspec.2.2.2.1, hspec.2.2.2.2, ?_⟩
  change target ≤ measurableBayesRiskVec
    (restrictedTranslatedGaussianPrior C h₀ τ) A ℓ + ε
  rw [measurableBayesRiskVec, ENNReal.iInf_add]
  refine le_iInf fun κ => ?_
  have hBR : bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ ≤
      ∫⁻ h, gaussianShiftKernelRiskVec A ℓ κ h ∂ν := by
    rw [hνeq]
    exact bayesRiskAtTau_le_averageKernelVec_translated A ℓ _hbowl κ
      (h₀ : EuclideanSpace ℝ (Fin m)) hτ
  have hcomp : ∫⁻ h, gaussianShiftKernelRiskVec A ℓ κ h ∂ν ≤
      ∫⁻ h, gaussianShiftKernelRiskVec A ℓ κ h
        ∂(restrictedTranslatedGaussianPrior C h₀ τ) + e := by
    have hc := lintegral_le_normalized_restrict_add ν C
      (gaussianShiftKernelRiskVec A ℓ κ) B
      (gaussianShiftKernelRiskVec_le A ℓ κ B hB)
    have hdef : (conePriorNormalizer C h₀ τ)⁻¹ • ν.restrict C =
        restrictedTranslatedGaussianPrior C h₀ τ := by
      rfl
    have hnorm : ν C = conePriorNormalizer C h₀ τ := rfl
    rw [hnorm, hdef] at hc
    exact hc.trans (add_le_add_right htailB.le _)
  calc
    target ≤ bayesRiskAtTau (1 : Matrix (Fin m) (Fin m) ℝ) A ℓ τ + e :=
      htargetτ
    _ ≤ (∫⁻ h, gaussianShiftKernelRiskVec A ℓ κ h ∂ν) + e :=
      add_le_add_left hBR e
    _ ≤ ((∫⁻ h, gaussianShiftKernelRiskVec A ℓ κ h
        ∂(restrictedTranslatedGaussianPrior C h₀ τ)) + e) + e :=
      add_le_add_left hcomp e
    _ = (∫⁻ h, gaussianShiftKernelRiskVec A ℓ κ h
        ∂(restrictedTranslatedGaussianPrior C h₀ τ)) + ε := by
      rw [add_assoc, hee]

end AsymptoticStatistics.LowerBounds.GaussianConeBayes
