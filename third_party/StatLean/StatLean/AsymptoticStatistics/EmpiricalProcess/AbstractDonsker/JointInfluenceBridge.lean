module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.JointInfluenceGaussianExtension
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterFiniteProduct

@[expose] public section

/-!
# Joint empirical-process and influence-function weak convergence

This theorem identifies every mixed finite-dimensional law and combines it
with asymptotic tightness to prove joint outer weak
convergence in `ℓ∞(F) × EuclideanSpace ℝ (Fin k)`.

Reference: van der Vaart, *Asymptotic Statistics*, Theorem 19.23, pp.278–279.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal InnerProductSpace
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperationalVec

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
private theorem mixedEvalCLM_joint_apply
    {F : Set (Ω → ℝ)} {k m : ℕ} (a : Fin m → Sum ↥F (Fin k))
    (w : LinfF F × EuclideanSpace ℝ (Fin k)) (i : Fin m) :
    (mixedEvalCLM (linfEvalCLM F) a w).ofLp i = jointEval w (a i) := by
  cases h : a i with
  | inl f => simp [mixedEvalCLM, jointEval, linfEvalCLM, h]; rfl
  | inr j => simp [mixedEvalCLM, jointEval, linfEvalCLM, h]

private theorem jointBridge_mixedEval_hasGaussianLaw
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k m : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ)
    (a : Fin m → Sum ↥F (Fin k)) :
    HasGaussianLaw (mixedEvalCLM (linfEvalCLM F) a) κ := by
  let L : (Fin m → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm
  have h := (hκ.gaussianFDD m a).map_equiv L
  have hcomp : L ∘ (fun w : LinfF F × EuclideanSpace ℝ (Fin k) =>
      fun i => jointEval w (a i)) = mixedEvalCLM (linfEvalCLM F) a := by
    funext w
    apply PiLp.ext
    intro i
    exact (mixedEvalCLM_joint_apply a w i).symm
  rwa [hcomp] at h

private theorem jointBridge_mixedEval_eq_multivariateGaussian
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k m : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P)
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ)
    (a : Fin m → Sum ↥F (Fin k)) :
    κ.map (mixedEvalCLM (linfEvalCLM F) a) =
      multivariateGaussian 0
        (marginalCovMatrix P (fun i => jointIndexFunction ψ (a i))) := by
  letI : IsProbabilityMeasure κ := hκ.isProbabilityMeasure
  let R := mixedEvalCLM (linfEvalCLM F) a
  let φ : Fin m → Ω → ℝ := fun i => jointIndexFunction ψ (a i)
  have hφmem : ∀ i, MemLp (φ i) 2 P := by
    intro i
    dsimp [φ]
    cases a i with
    | inl f => exact hF_L2 f f.2
    | inr j =>
        exact (memLp_congr_ae (influenceFunction_ae_eq ψ j)).mp
          (Lp.memLp (ψ j : Lp ℝ 2 P))
  have hS : (marginalCovMatrix P φ).PosSemidef :=
    marginalCovMatrix_posSemidef_of_memLp φ hφmem
  have hRgauss : HasGaussianLaw R κ := jointBridge_mixedEval_hasGaussianLaw ψ hκ a
  haveI hmap_gauss : IsGaussian (κ.map R) := hRgauss.isGaussian_map
  have hRmem : MemLp R 2 κ := hRgauss.memLp_two
  change κ.map R = multivariateGaussian 0 (marginalCovMatrix P φ)
  refine ProbabilityTheory.IsGaussian.ext ?_ ?_
  · have hmvmean :
        ∫ x : EuclideanSpace ℝ (Fin m), id x
            ∂multivariateGaussian 0 (marginalCovMatrix P φ) = 0 := by
        simpa only [id_eq] using
          (integral_id_multivariateGaussian
            (μ := (0 : EuclideanSpace ℝ (Fin m)))
            (S := marginalCovMatrix P φ))
    rw [hmvmean]
    rw [integral_map R.continuous.measurable.aemeasurable aestronglyMeasurable_id]
    simp only [id_eq]
    apply PiLp.ext
    intro i
    have hproj := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
      (hRmem.integrable (by norm_num))
    have hcoord : (fun w => (EuclideanSpace.proj (𝕜 := ℝ) i) (R w)) =
        fun w => jointEval w (a i) := by
      funext w
      simpa [R, EuclideanSpace.coe_proj] using mixedEvalCLM_joint_apply a w i
    rw [show (0 : EuclideanSpace ℝ (Fin m)).ofLp i = 0 from rfl]
    change (EuclideanSpace.proj (𝕜 := ℝ) i)
        (∫ x : LinfF F × EuclideanSpace ℝ (Fin k), R x ∂κ) = 0
    rw [← hproj]
    simpa only [hcoord] using hκ.mean (a i)
  · have hMemMap : MemLp id 2 (κ.map R) := IsGaussian.memLp_two_id
    have hbasis : ∀ i : Fin m,
        (fun u : EuclideanSpace ℝ (Fin m) =>
          (inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis i) u : ℝ)) =
      fun u => u.ofLp i := by
      intro i
      funext u
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, PiLp.inner_apply]
      have hpt : ∀ x : Fin m,
          (inner ℝ ((EuclideanSpace.single i (1 : ℝ)).ofLp x) (u.ofLp x) : ℝ) =
            u.ofLp x * (if x = i then (1 : ℝ) else 0) := by
        intro x
        rw [PiLp.single_apply]
        rfl
      simp_rw [hpt]
      simp [Finset.sum_ite_eq']
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      ProbabilityTheory.covarianceBilin_apply_eq_cov (μ := κ.map R) hMemMap,
      ProbabilityTheory.covarianceBilin_apply_eq_cov
        (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (marginalCovMatrix P φ)) IsGaussian.memLp_two_id,
      hbasis i, hbasis j,
      ProbabilityTheory.covariance_eval_multivariateGaussian hS]
    have hcoord_meas : ∀ q : Fin m,
        AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin m) => u.ofLp q) (κ.map R) :=
      fun q => (EuclideanSpace.proj (𝕜 := ℝ) q).continuous.measurable.aestronglyMeasurable
    rw [ProbabilityTheory.covariance_map (hcoord_meas i) (hcoord_meas j)
      R.continuous.measurable.aemeasurable]
    have hcoord : ∀ q : Fin m,
        ((fun u : EuclideanSpace ℝ (Fin m) => u.ofLp q) ∘ R) =
          fun w => jointEval w (a q) := by
      intro q
      funext w
      simpa [R, EuclideanSpace.coe_proj] using mixedEvalCLM_joint_apply a w q
    have hcoord_mem : ∀ q : Fin m,
        MemLp (fun w => jointEval w (a q)) 2 κ := by
      intro q
      rw [← hcoord q]
      exact (EuclideanSpace.proj (𝕜 := ℝ) q).lipschitz.comp_memLp
        (map_zero _) hRmem
    rw [hcoord i, hcoord j]
    rw [ProbabilityTheory.covariance_eq_sub (hcoord_mem i) (hcoord_mem j),
      hκ.mean (a i), hκ.mean (a j)]
    simp only [Pi.mul_apply]
    rw [hκ.covariance (a i) (a j)]
    simp [φ, marginalCovMatrix, marginalCovEntry, jointCov]

/-- The normalized finite vector of influence-function empirical sums.
Edge behavior: at `n = 0`, the empty sum is zero (regardless of the inverse
square-root convention). -/
noncomputable def influenceEmpiricalVector
    (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) (n : ℕ) (X : Fin n → Ω) :
    EuclideanSpace ℝ (Fin k) := by
  exact (WithLp.equiv 2 _).symm
    (fun j => empiricalProcess P n X (influenceFunction ψ j))

private theorem mixedEval_jointEmpirical_eq_std
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k m : ℕ}
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P)
    (ψ : Fin k → ↥(L2ZeroMean P))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_law : μ.map (X 0) = P)
    (a : Fin m → Sum ↥F (Fin k))
    (hmem : ∀ n ξ, Memℓp
      (fun f : ↥F => empiricalProcess P n
        (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)) ∞)
    (n : ℕ) (ξ : Ξ) :
    mixedEvalCLM (linfEvalCLM F) a
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
          influenceEmpiricalVector P ψ n (fun i : Fin n => X i.val ξ)) =
      (Real.sqrt n)⁻¹ •
        (∑ i ∈ Finset.range n,
          tupleVec (fun q => jointIndexFunction ψ (a q)) (X i ξ) -
            n • μ[fun ζ => tupleVec (fun q => jointIndexFunction ψ (a q)) (X 0 ζ)]) := by
  let φ : Fin m → Ω → ℝ := fun q => jointIndexFunction ψ (a q)
  have hφmeas : ∀ q, Measurable (φ q) := by
    intro q
    dsimp [φ]
    cases a q with
    | inl f => exact hF_meas f f.2
    | inr j =>
        change Measurable (influenceFunction ψ j)
        exact (Lp.aestronglyMeasurable (ψ j : Lp ℝ 2 P)).measurable_mk
  have hφmem : ∀ q, MemLp (φ q) 2 P := by
    intro q
    dsimp [φ]
    cases a q with
    | inl f => exact hF_L2 f f.2
    | inr j =>
        change MemLp (influenceFunction ψ j) 2 P
        exact ((memLp_congr_ae (influenceFunction_ae_eq ψ j)).mp
          (Lp.memLp (ψ j : Lp ℝ 2 P)))
  have htv_meas : Measurable (tupleVec φ) := by
    have hpi : Measurable (fun x => (fun q => φ q x) : Ω → (Fin m → ℝ)) :=
      measurable_pi_iff.mpr hφmeas
    exact (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.measurable.comp hpi
  have htv_intP : Integrable (tupleVec φ) P := by
    have hLp : MemLp (tupleVec φ) 2 P := memLp_piLp_iff.mpr hφmem
    exact hLp.integrable (by norm_num)
  have htv_int : Integrable (fun ζ => tupleVec φ (X 0 ζ)) μ := by
    have hc : Integrable (tupleVec φ ∘ X 0) μ :=
      (integrable_map_measure htv_meas.aestronglyMeasurable
        (hX_meas 0).aemeasurable).mp (by rw [hX_law]; exact htv_intP)
    exact hc
  apply PiLp.ext
  intro q
  have hleft :
      (mixedEvalCLM (linfEvalCLM F) a
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
          influenceEmpiricalVector P ψ n (fun i : Fin n => X i.val ξ))).ofLp q =
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (φ q) := by
    rw [mixedEvalCLM_joint_apply]
    change jointEval
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
          influenceEmpiricalVector P ψ n (fun i : Fin n => X i.val ξ)) (a q) =
      empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (jointIndexFunction ψ (a q))
    cases a q <;> rfl
  rw [hleft]
  have hproj_tv : ∀ x, (EuclideanSpace.proj q) (tupleVec φ x) = φ q x := by
    intro x
    rw [EuclideanSpace.coe_proj]
    rfl
  have hint_q : (EuclideanSpace.proj q)
      (μ[fun ζ => tupleVec φ (X 0 ζ)]) = μ[fun ζ => φ q (X 0 ζ)] := by
    rw [← ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj q) htv_int]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ζ => hproj_tv (X 0 ζ))
  have hcoord :
      ((Real.sqrt n)⁻¹ •
          (∑ i ∈ Finset.range n, tupleVec φ (X i ξ) -
            n • μ[fun ζ => tupleVec φ (X 0 ζ)])).ofLp q =
        (Real.sqrt n)⁻¹ *
          ((∑ i ∈ Finset.range n, φ q (X i ξ)) -
            n * μ[fun ζ => φ q (X 0 ζ)]) := by
    change (EuclideanSpace.proj (𝕜 := ℝ) q)
        ((Real.sqrt n)⁻¹ •
          (∑ i ∈ Finset.range n, tupleVec φ (X i ξ) -
            n • μ[fun ζ => tupleVec φ (X 0 ζ)])) = _
    rw [map_smul, map_sub, map_sum, map_nsmul, hint_q]
    simp only [hproj_tv, smul_eq_mul, nsmul_eq_mul]
  rw [hcoord]
  have hint_law : μ[fun ζ => φ q (X 0 ζ)] = ∫ x, φ q x ∂P := by
    rw [← hX_law, integral_map (hX_meas 0).aemeasurable
      (hφmeas q).aestronglyMeasurable]
  rw [hint_law]
  have hsum : ∑ i ∈ Finset.range n, φ q (X i ξ) =
      ∑ i : Fin n, φ q (X i.val ξ) := by
    rw [Finset.sum_range]
  rw [empiricalProcess, empiricalAvg, hsum]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hsqrt_ne : Real.sqrt n ≠ 0 := hsqrt_pos.ne'
    have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have h1 : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
      field_simp
      linear_combination hsq
    have h2 : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
      rw [inv_mul_eq_div, eq_comm, eq_div_iff hsqrt_ne, hsq]
    set A := ∑ i : Fin n, φ q (X i.val ξ)
    set B := ∫ x, φ q x ∂P
    linear_combination A * h1 + B * h2

private theorem jointEmpirical_mixed_weakConvergesOuter
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P)
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ)
    (hX_id : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hmem : ∀ n ξ, Memℓp
      (fun f : ↥F => empiricalProcess P n
        (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)) ∞)
    (m : ℕ) (a : Fin m → Sum ↥F (Fin k)) :
    WeakConvergesOuter (fun _ => μ)
      (fun n ξ => mixedEvalCLM (linfEvalCLM F) a
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
          influenceEmpiricalVector P ψ n (fun i : Fin n => X i.val ξ)))
      (κ.map (mixedEvalCLM (linfEvalCLM F) a)) := by
  let φ : Fin m → Ω → ℝ := fun q => jointIndexFunction ψ (a q)
  have hφmeas : ∀ q, Measurable (φ q) := by
    intro q
    dsimp [φ]
    cases a q with
    | inl f => exact hF_meas f f.2
    | inr j =>
        change Measurable (influenceFunction ψ j)
        exact (Lp.aestronglyMeasurable (ψ j : Lp ℝ 2 P)).measurable_mk
  have hφmem : ∀ q, MemLp (φ q) 2 P := by
    intro q
    dsimp [φ]
    cases a q with
    | inl f => exact hF_L2 f f.2
    | inr j =>
        change MemLp (influenceFunction ψ j) 2 P
        exact ((memLp_congr_ae (influenceFunction_ae_eq ψ j)).mp
          (Lp.memLp (ψ j : Lp ℝ 2 P)))
  let stdVec : ℕ → Ξ → EuclideanSpace ℝ (Fin m) := fun n ξ =>
    (Real.sqrt n)⁻¹ •
      (∑ i ∈ Finset.range n, tupleVec φ (X i ξ) -
        n • μ[fun ζ => tupleVec φ (X 0 ζ)])
  have htv_meas : Measurable (tupleVec φ) := by
    have hpi : Measurable (fun x => (fun q => φ q x) : Ω → (Fin m → ℝ)) :=
      measurable_pi_iff.mpr hφmeas
    exact (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.measurable.comp hpi
  have hstd_meas : ∀ n, Measurable (stdVec n) := by
    intro n
    exact Measurable.const_smul
      ((Finset.measurable_sum _ fun i _ => htv_meas.comp (hX_meas i)).sub measurable_const)
      ((Real.sqrt n)⁻¹)
  let Wmix : ℕ → Ξ → EuclideanSpace ℝ (Fin m) := fun n ξ =>
    mixedEvalCLM (linfEvalCLM F) a
      (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
        influenceEmpiricalVector P ψ n (fun i : Fin n => X i.val ξ))
  have hWstd : ∀ n, Wmix n = stdVec n := by
    intro n
    funext ξ
    exact mixedEval_jointEmpirical_eq_std hF_meas hF_L2 ψ μ X hX_meas hX_law
      a hmem n ξ
  have hWmeas : ∀ n, Measurable (Wmix n) := fun n => hWstd n ▸ hstd_meas n
  obtain ⟨Y, hYlaw, hTID⟩ := marginalCLT_fdd_of_iid
    (F := Set.range φ) μ X hX_meas hX_indep hX_id hX_law φ hφmem
  have hWC : WeakConverges (fun n => μ.map (stdVec n))
      (multivariateGaussian 0 (marginalCovMatrix P φ)) := by
    have hlim_eq :
        (⟨(multivariateGaussian 0 (marginalCovMatrix P φ)).map Y,
            Measure.isProbabilityMeasure_map hTID.aemeasurable_limit⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin m))) =
        ⟨multivariateGaussian 0 (marginalCovMatrix P φ), inferInstance⟩ :=
      Subtype.ext hYlaw.map_eq
    intro g
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (hlim_eq ▸ hTID.tendsto)) g
  rw [weakConvergesOuter_of_measurable hWmeas]
  have hmaps : (fun n => μ.map (Wmix n)) = fun n => μ.map (stdVec n) := by
    funext n
    rw [hWstd n]
  rw [hmaps,
    jointBridge_mixedEval_eq_multivariateGaussian hF_L2 ψ hκ a]
  exact hWC

set_option linter.unusedVariables false in
/-- A constitutively bundled Donsker process and finitely many `L²₀(P)`
influence coordinates converge jointly in
`ℓ∞(F) × EuclideanSpace ℝ (Fin k)`.

The conclusion is genuine joint outer weak convergence. Its proof obligation
includes every mixed `Sum ↥F (Fin k)` finite-dimensional distribution; no
separate-marginal shortcut is permitted. -/
theorem PDonskerProcessData.jointInfluence_weakConvergesOuter
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hD : PDonskerProcessData F P)
    (ψ : Fin k → ↥(L2ZeroMean P))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ (ν : Measure (LinfF F))
      (κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k)))
      (hν : IsPBrownianBridge F P ν)
      (hκ : IsJointBridgeInfluence F P ψ ν κ)
      (hmem : ∀ n ξ, Memℓp
        (fun f : ↥F => empiricalProcess P n
          (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)) ∞),
      WeakConvergesOuter (fun _ => μ)
        (fun n ξ =>
          (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
            influenceEmpiricalVector P ψ n (fun i : Fin n => X i.val ξ))) κ := by
  rcases hD.literal with ⟨ν, hν, hliteral⟩
  obtain ⟨hmem, hfirstWCO⟩ :=
    hliteral (Ξ := Ξ) μ X hX_meas hX_indep hX_id hX_law
  obtain ⟨κ, hκ⟩ := exists_jointBridgeInfluence hν
    (fun f hf => hD.memLp hf) ψ
  letI : IsProbabilityMeasure ν := hν.isProbabilityMeasure
  letI : IsProbabilityMeasure κ := hκ.isProbabilityMeasure
  let Wn : ℕ → Ξ → LinfF F × EuclideanSpace ℝ (Fin k) := fun n ξ =>
    (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
      influenceEmpiricalVector P ψ n (fun i : Fin n => X i.val ξ))
  have hfirstTight : IsAsymptoticallyTight (fun _ => μ)
      (fun n ξ => empiricalProcessLinf
        (fun i : Fin n => X i.val ξ) (hmem n ξ)) :=
    AsymptoticStatistics.isAsymptoticallyTight_of_weakConvergesOuter
      hfirstWCO hν.tight
  let ainfluence : Fin k → Sum ↥F (Fin k) := fun j => Sum.inr j
  have hinfluenceWCO := jointEmpirical_mixed_weakConvergesOuter
    hD.measurable (fun f hf => hD.memLp hf) ψ hκ μ X hX_meas hX_indep
      hX_id hX_law hmem k ainfluence
  haveI : IsProbabilityMeasure
      (κ.map (mixedEvalCLM (linfEvalCLM F) ainfluence)) :=
    Measure.isProbabilityMeasure_map
      (mixedEvalCLM (linfEvalCLM F) ainfluence).continuous.measurable.aemeasurable
  have hinfluenceTightMixed : IsAsymptoticallyTight (fun _ => μ)
      (fun n ξ => mixedEvalCLM (linfEvalCLM F) ainfluence (Wn n ξ)) :=
    AsymptoticStatistics.isAsymptoticallyTight_of_weakConvergesOuter
      hinfluenceWCO MeasureTheory.isTightMeasureSet_singleton
  have hinfluence_eq :
      (fun n ξ => mixedEvalCLM (linfEvalCLM F) ainfluence (Wn n ξ)) =
        fun n ξ => influenceEmpiricalVector P ψ n
          (fun i : Fin n => X i.val ξ) := by
    funext n ξ
    apply PiLp.ext
    intro j
    simp [ainfluence, Wn, mixedEvalCLM]
  have hinfluenceTight : IsAsymptoticallyTight (fun _ => μ)
      (fun n ξ => influenceEmpiricalVector P ψ n
        (fun i : Fin n => X i.val ξ)) := by
    rw [← hinfluence_eq]
    exact hinfluenceTightMixed
  have hWnTight : IsAsymptoticallyTight (fun _ => μ) Wn :=
    hfirstTight.prodMk hinfluenceTight
  refine ⟨ν, κ, hν, hκ, hmem, ?_⟩
  apply weakConvergesOuter_prod_of_tight_mixedEval
    (linfEvalCLM F)
  · intro z w hzw
    ext f
    exact hzw f
  · exact hWnTight
  · exact hκ.tight
  · intro m a
    exact jointEmpirical_mixed_weakConvergesOuter
      hD.measurable (fun f hf => hD.memLp hf) ψ hκ μ X hX_meas hX_indep
        hX_id hX_law hmem m a

end AsymptoticStatistics.EmpiricalProcess
