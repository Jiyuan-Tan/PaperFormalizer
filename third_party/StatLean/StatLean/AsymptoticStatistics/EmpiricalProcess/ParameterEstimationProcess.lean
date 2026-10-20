module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.JointInfluenceBridge
public import StatLean.AsymptoticStatistics.EmpiricalProcess.IIDChebyshev
public import StatLean.AsymptoticStatistics.EmpiricalProcess.IIDFiniteRestriction
public import StatLean.AsymptoticStatistics.ForMathlib.DeltaMethod
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterSlutsky
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

/-!
# Empirical processes under finite-dimensional parameter estimation

This is the full path-space form of van der Vaart Theorem 19.23. The parameter
has dimension `k`, the precursor converges jointly in `ℓ∞(F) × ℝᵏ`, and the
conclusion is weak convergence in outer expectation in `ℓ∞(F)`.
It is deliberately separate from the existing scalar pointwise specialization
in `ParameterEstimation.lean`.

Reference: van der Vaart, *Asymptotic Statistics*, Theorem 19.23, pp.278–279.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperationalVec

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `j`th standard basis vector in `EuclideanSpace ℝ (Fin k)`.
Edge behavior: there is no inhabitant `j` when `k = 0`. -/
noncomputable def euclideanBasisVector {k : ℕ} (j : Fin k) :
    EuclideanSpace ℝ (Fin k) := by
  exact (EuclideanSpace.equiv (Fin k) ℝ).symm (Pi.single j 1)

/-- The continuous linear correction `(z, v) ↦ z - Dv` used in the
continuous-mapping step of Theorem 19.23.

Edge behavior: for `k = 0`, `v` is the unique zero vector and the map reduces
to the first projection. -/
noncomputable def parameterCorrectionCLM
    {F : Set (Ω → ℝ)} {k : ℕ}
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) :
    (LinfF F × EuclideanSpace ℝ (Fin k)) →L[ℝ] LinfF F := by
  exact ContinuousLinearMap.fst ℝ (LinfF F) (EuclideanSpace ℝ (Fin k)) -
    D.comp (ContinuousLinearMap.snd ℝ (LinfF F) (EuclideanSpace ℝ (Fin k)))

/-- The residual influence function at coordinate `f`:
`f - Pf - Σⱼ ((D eⱼ) f) ψⱼ`.

This is the covariance-bearing form of vdV Theorem 19.23. Edge behavior: for
`k = 0` the sum is empty and the residual is the usual centered function. -/
noncomputable def parameterResidual
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P))
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F)
    (f : ↥F) : Ω → ℝ := by
  exact fun x => (f : Ω → ℝ) x - ∫ y, (f : Ω → ℝ) y ∂P -
    ∑ j : Fin k, (D (euclideanBasisVector j)) f *
      ((((ψ j : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) x)

/-- Covariance of the limiting parameter-corrected process, expressed as the
`L²(P)` inner product of the two residual influence functions.

Edge behavior follows `parameterResidual`; the theorem-level Donsker data
derives the required `L²` membership. -/
noncomputable def parameterLimitCov
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P))
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F)
    (f g : ↥F) : ℝ := by
  exact ∫ x, parameterResidual P ψ D f x * parameterResidual P ψ D g x ∂P

/-- Specification of the centered Gaussian `ℓ∞(F)` limit in Theorem 19.23,
including its evaluation covariance. -/
structure IsParameterEstimationLimit
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P))
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F)
    (ρ : Measure (LinfF F)) : Prop where
  /-- Constitutive (vdV Theorem 19.23 pp.278–279): the limit is a probability
  law on the full path space. -/
  isProbabilityMeasure : IsProbabilityMeasure ρ
  /-- Constitutive (vdV Theorem 19.23 p.279): every finite tuple of path
  evaluations is jointly Gaussian. -/
  gaussianFDD : ∀ (m : ℕ) (a : Fin m → ↥F),
    HasGaussianLaw (fun z : LinfF F => fun i => z (a i)) ρ
  /-- Constitutive (vdV Theorem 19.23 p.279): each evaluation is centered. -/
  mean : ∀ f : ↥F, ∫ z : LinfF F, z f ∂ρ = 0
  /-- Constitutive (vdV Theorem 19.23 p.279): evaluation covariance is the
  covariance of `f - Pf - Σⱼ ((D eⱼ) f) ψⱼ`. -/
  covariance : ∀ f g : ↥F,
    ∫ z : LinfF F, z f * z g ∂ρ = parameterLimitCov P ψ D f g

/-- The genuine `ℓ∞(F)`-valued empirical-minus-estimated process, represented
using the population path `Q θ = (f ↦ P_θ f)`:
`𝔾ₙ - √n • (Q(θ̂ₙ) - Q(θ₀))`.

The `populationPath_apply` field below identifies each evaluation with
`√n(Pₙf-P_{θ̂ₙ}f)`. Edge behavior at `n = 0` uses `Real.sqrt 0 = 0`. -/
noncomputable def parameterEstimatedProcess
    {F : Set (Ω → ℝ)} {k n : ℕ} {P : Measure Ω}
    (Q : EuclideanSpace ℝ (Fin k) → LinfF F)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (θ_hat : (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (X : Fin n → Ω)
    (hmem : Memℓp (fun f : ↥F => empiricalProcess P n X (f : Ω → ℝ)) ∞) :
    LinfF F := by
  exact empiricalProcessLinf X hmem - Real.sqrt n • (Q (θ_hat X) - Q θ₀)

/-- **Bundled hypotheses for the finite-dimensional path-space Theorem
19.23.** The single `donsker` field is the constitutive book assumption; its
operational and literal facets are not two caller assumptions. -/
structure Theorem19_23FiniteHyp
    (F : Set (Ω → ℝ)) (P_θ : EuclideanSpace ℝ (Fin k) → Measure Ω)
    (θ₀ : EuclideanSpace ℝ (Fin k)) [IsProbabilityMeasure (P_θ θ₀)]
    (ψ : Fin k → ↥(L2ZeroMean (P_θ θ₀)))
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (Q : EuclideanSpace ℝ (Fin k) → LinfF F)
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) : Prop where
  /-- Constitutive (vdV Theorem 19.23 p.278): `F` is a measurable
  `P_{θ₀}`-Donsker class. -/
  donsker : PDonskerProcessData F (P_θ θ₀)
  /-- Constitutive (vdV Theorem 19.23 p.278): `θ̂ₙ` is asymptotically linear
  with influence function tuple `ψ`. -/
  asymptoticallyLinear :
    AsymptoticallyLinearAt_vec θ_hat (P_θ θ₀) ψ θ₀
  /-- Constitutive (vdV Theorem 19.23 footnote p.278): `Q` is exactly the map
  `θ ↦ P_θ` viewed in `ℓ∞(F)`, not a freely chosen proxy. -/
  populationPath_apply : ∀ θ f,
    Q θ f = ∫ x, (f : Ω → ℝ) x ∂(P_θ θ)
  /-- Constitutive (vdV Theorem 19.23 p.278): the map `θ ↦ P_θ` into
  `ℓ∞(F)` is Fréchet differentiable at `θ₀` with derivative `D`. -/
  frechet : HasFDerivAt Q D θ₀

/-- The vector asymptotic-linearity residual, transported from the product
experiment in `AsymptoticallyLinearAt_vec` to an arbitrary iid realization on
the common sample space `Ξ`. -/
private theorem asymptoticallyLinearAt_vec_on_iid_sample
    (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P))
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (hAL : AsymptoticallyLinearAt_vec θ_hat P ψ θ₀)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∀ δ > 0, Tendsto (fun (n : ℕ) => μ.real {ξ | δ ≤
      ‖Real.sqrt n •
          (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) -
        (Real.sqrt n)⁻¹ •
          (∑ i : Fin n, tupleEval P ψ (X i.val ξ))‖}) atTop (𝓝 0) := by
  intro δ hδ
  have hprod := hAL δ hδ
  have hprod_real : Tendsto (fun (n : ℕ) =>
      (Measure.pi (fun _ : Fin n => P)).real
        {x : Fin n → Ω | δ ≤
          ‖Real.sqrt n • (θ_hat n x - θ₀) -
            (Real.sqrt n)⁻¹ • (∑ i, tupleEval P ψ (x i))‖}) atTop (𝓝 0) := by
    simpa only [Measure.real, ENNReal.toReal_zero] using!
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hprod
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod_real
    (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun n => ?_)
  let sample : Ξ → (Fin n → Ω) := fun ξ i => X i.val ξ
  let bad : Set (Fin n → Ω) := {x | δ ≤
    ‖Real.sqrt n • (θ_hat n x - θ₀) -
      (Real.sqrt n)⁻¹ • (∑ i, tupleEval P ψ (x i))‖}
  have hsample : Measurable sample :=
    measurable_pi_lambda _ (fun i => hX_meas i.val)
  have hle : μ (sample ⁻¹' bad) ≤ (μ.map sample) bad :=
    Measure.le_map_apply hsample.aemeasurable bad
  have hmap : μ.map sample = Measure.pi (fun _ : Fin n => P) :=
    iidFiniteRestriction_map_eq_pi P μ X hX_meas hX_indep hX_id hX_law n
  rw [Measure.real, Measure.real]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  change μ (sample ⁻¹' bad) ≤ (Measure.pi (fun _ : Fin n => P)) bad
  rw [← hmap]
  exact hle

/-- The normalized empirical influence vector is uniformly bounded in
probability.  This universe-polymorphic finite-coordinate bound is the
Chebyshev substitute for invoking the small-universe multivariate CLT. -/
private theorem influenceEmpiricalVector_isBoundedInProb
    (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P))
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    AsymptoticStatistics.IsBoundedInProb (fun _ => μ)
      (fun n ξ => influenceEmpiricalVector P ψ n
        (fun i : Fin n => X i.val ξ)) := by
  intro η hη
  let I : Fin k → ℝ := fun j => ∫ x, (influenceFunction ψ j x) ^ 2 ∂P
  have hI : ∀ j, 0 ≤ I j := fun j => integral_nonneg fun _ => sq_nonneg _
  let C : ℝ := 1 + ∑ j, I j
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hI j)
  let A : ℝ := C * (1 + η⁻¹)
  have hA : 0 < A := mul_pos (lt_of_lt_of_le zero_lt_one hC) (by positivity)
  refine ⟨k * A, fun n => ?_⟩
  let E : Fin k → Set Ξ := fun j =>
    {ξ | A ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ)
      (influenceFunction ψ j)|}
  have hsub : {ξ | k * A < ‖influenceEmpiricalVector P ψ n
        (fun i : Fin n => X i.val ξ)‖} ⊆ ⋃ j, E j := by
    intro ξ hξ
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists] at hnot
    have hcoord : ∀ j : Fin k,
        |(influenceEmpiricalVector P ψ n
          (fun i : Fin n => X i.val ξ)).ofLp j| ≤ A := by
      intro j
      have hj : ¬ A ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (influenceFunction ψ j)| := by simpa [E] using hnot j
      simpa [influenceEmpiricalVector] using (not_le.mp hj).le
    have hnorm : ‖influenceEmpiricalVector P ψ n
          (fun i : Fin n => X i.val ξ)‖ ≤
        ∑ j, |(influenceEmpiricalVector P ψ n
          (fun i : Fin n => X i.val ξ)).ofLp j| := by
      let w := influenceEmpiricalVector P ψ n (fun i : Fin n => X i.val ξ)
      have hdec : ∑ j, w.ofLp j • EuclideanSpace.single j (1 : ℝ) = w := by
        simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
          (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr w
      calc
        ‖w‖ = ‖∑ j, w.ofLp j • EuclideanSpace.single j (1 : ℝ)‖ := by rw [hdec]
        _ ≤ ∑ j, ‖w.ofLp j • EuclideanSpace.single j (1 : ℝ)‖ := norm_sum_le _ _
        _ = ∑ j, |w.ofLp j| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have hsum : (∑ j, |(influenceEmpiricalVector P ψ n
          (fun i : Fin n => X i.val ξ)).ofLp j|) ≤ k * A := by
      calc
        _ ≤ ∑ _j : Fin k, A := Finset.sum_le_sum fun j _ => hcoord j
        _ = k * A := by simp
    exact (not_lt_of_ge (hnorm.trans hsum)) hξ
  calc
    μ.real {ξ | k * A < ‖influenceEmpiricalVector P ψ n
        (fun i : Fin n => X i.val ξ)‖}
        ≤ μ.real (⋃ j, E j) := measureReal_mono hsub
    _ ≤ ∑ j, μ.real (E j) := by
      rw [Measure.real]
      calc
        (μ (⋃ j, E j)).toReal ≤ (∑ j, μ (E j)).toReal :=
          ENNReal.toReal_mono
            (ENNReal.sum_ne_top.mpr fun j _ => measure_ne_top μ (E j))
            (measure_iUnion_fintype_le μ E)
        _ = ∑ j, μ.real (E j) := by
          simp only [Measure.real, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
    _ ≤ ∑ j, I j / A ^ 2 := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hψL2 : MemLp (influenceFunction ψ j) 2 P :=
        ((memLp_congr_ae (influenceFunction_ae_eq ψ j)).mp
          (Lp.memLp (ψ j : Lp ℝ 2 P)))
      have ht := empiricalProcess_chebyshev_tail P μ X hX_meas hX_indep hX_id
        hX_law n (influenceFunction ψ j) hψL2 hA
      rw [Measure.real]
      calc
        (μ (E j)).toReal ≤ (ENNReal.ofReal (I j / A ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
        _ = I j / A ^ 2 := ENNReal.toReal_ofReal (div_nonneg (hI j) (sq_nonneg A))
    _ = (∑ j, I j) / A ^ 2 := by rw [Finset.sum_div]
    _ ≤ η := by
      have hηinv : 0 < η⁻¹ := inv_pos.mpr hη
      have hA2 : C / η ≤ A ^ 2 := by
        have ht : η⁻¹ ≤ (1 + η⁻¹) ^ 2 := by
          nlinarith [sq_nonneg η⁻¹]
        have hC0 : 0 ≤ C := zero_le_one.trans hC
        calc
          C / η = C * η⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ C * (1 + η⁻¹) ^ 2 := mul_le_mul_of_nonneg_left ht hC0
          _ ≤ C ^ 2 * (1 + η⁻¹) ^ 2 := by
            gcongr
            nlinarith
          _ = A ^ 2 := by simp only [A]; ring
      have hsumC : ∑ j, I j ≤ C := by dsimp [C]; linarith
      calc
        (∑ j, I j) / A ^ 2 ≤ C / A ^ 2 :=
          div_le_div_of_nonneg_right hsumC (sq_nonneg A)
        _ ≤ η := (div_le_iff₀ (sq_pos_of_pos hA)).2 (by
          rw [mul_comm]
          exact (div_le_iff₀ hη).1 hA2)

/-- The measurable influence representatives used by
`influenceEmpiricalVector` agree almost everywhere with the raw `L²`
representatives used by `AsymptoticallyLinearAt_vec`. -/
private theorem influenceEmpiricalVector_ae_eq_raw
    (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P))
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) (n : ℕ) :
    (fun ξ => influenceEmpiricalVector P ψ n (fun i : Fin n => X i.val ξ)) =ᵐ[μ]
      fun ξ => (Real.sqrt n)⁻¹ •
        ∑ i : Fin n, tupleEval P ψ (X i.val ξ) := by
  have hmap : ∀ i, μ.map (X i) = P := fun i => (hX_id i).map_eq.trans hX_law
  have hrep : ∀ i : Fin n, ∀ j : Fin k,
      (fun ξ => (((ψ j : Lp ℝ 2 P) : Ω → ℝ) (X i.val ξ))) =ᵐ[μ]
        fun ξ => influenceFunction ψ j (X i.val ξ) := by
    intro i j
    exact ae_eq_comp (hX_meas i.val).aemeasurable (by
      rw [hmap i.val]
      exact influenceFunction_ae_eq ψ j)
  have hmean : ∀ j : Fin k, ∫ x, influenceFunction ψ j x ∂P = 0 := by
    intro j
    rw [← integral_congr_ae (influenceFunction_ae_eq ψ j)]
    have hz := (ψ j).2
    change integralL2 P (ψ j : Lp ℝ 2 P) = 0 at hz
    unfold integralL2 at hz
    rw [innerSL_apply_apply, L2.inner_def] at hz
    have hone : ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
        fun _ => (1 : ℝ) := (memLp_const (1 : ℝ)).coeFn_toLp
    rw [integral_congr_ae (by
      filter_upwards [hone] with x hx
      rw [hx])] at hz
    have hinner : ∀ y : ℝ, ⟪(1 : ℝ), y⟫_ℝ = y := by
      intro y
      rw [show y = y • (1 : ℝ) by simp, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      norm_num
    simp_rw [hinner] at hz
    simpa using hz
  have hall : ∀ᵐ ξ ∂μ, ∀ i : Fin n, ∀ j : Fin k,
      (((ψ j : Lp ℝ 2 P) : Ω → ℝ) (X i.val ξ)) =
        influenceFunction ψ j (X i.val ξ) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hrep i j
  filter_upwards [hall] with ξ hξ
  apply PiLp.ext
  intro j
  rw [show (influenceEmpiricalVector P ψ n
      (fun i : Fin n => X i.val ξ)).ofLp j =
      empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (influenceFunction ψ j) from rfl]
  rw [show ((Real.sqrt n)⁻¹ •
      ∑ i : Fin n, tupleEval P ψ (X i.val ξ)).ofLp j =
      (Real.sqrt n)⁻¹ * ∑ i : Fin n,
        (((ψ j : Lp ℝ 2 P) : Ω → ℝ) (X i.val ξ)) by
      simp [tupleEval]]
  rw [empiricalProcess, empiricalAvg, hmean j]
  simp_rw [hξ _ j]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n :=
      Real.mul_self_sqrt (by positivity)
    field_simp
    linear_combination (∑ i : Fin n, influenceFunction ψ j (X i.val ξ)) * hsq

omit [MeasurableSpace Ω] in
private theorem parameterDerivative_eval_eq_sum
    {F : Set (Ω → ℝ)} {k : ℕ}
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F)
    (v : EuclideanSpace ℝ (Fin k)) (f : ↥F) :
    D v f = ∑ j : Fin k, (D (euclideanBasisVector j)) f * v.ofLp j := by
  have hv : ∑ j : Fin k, v.ofLp j • euclideanBasisVector j = v := by
    simpa [euclideanBasisVector, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr v
  calc
    D v f = linfEvalCLM F f (D v) := rfl
    _ = linfEvalCLM F f
        (D (∑ j : Fin k, v.ofLp j • euclideanBasisVector j)) := by rw [hv]
    _ = ∑ j : Fin k, (D (euclideanBasisVector j)) f * v.ofLp j := by
      rw [map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, map_smul]
      change v.ofLp j * (D (euclideanBasisVector j)) f =
        (D (euclideanBasisVector j)) f * v.ofLp j
      ring

private noncomputable def parameterFiniteIndices
    {F : Set (Ω → ℝ)} {k m : ℕ} (a : Fin m → ↥F) :
    Fin (m + k) → Sum ↥F (Fin k) :=
  Fin.append (fun i => Sum.inl (a i)) (fun j => Sum.inr j)

private noncomputable def parameterFiniteCorrectionCLM
    {F : Set (Ω → ℝ)} {k m : ℕ}
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (a : Fin m → ↥F) :
    (Fin (m + k) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (Fin.castAdd k i) -
      ∑ j : Fin k, (D (euclideanBasisVector j)) (a i) •
        ContinuousLinearMap.proj (Fin.natAdd m j)

private theorem parameterCorrection_fdd_gaussian_on_joint
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ)
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F)
    (m : ℕ) (a : Fin m → ↥F) :
    HasGaussianLaw (fun w : LinfF F × EuclideanSpace ℝ (Fin k) =>
      fun i => parameterCorrectionCLM D w (a i)) κ := by
  have hg := (hκ.gaussianFDD (m + k) (parameterFiniteIndices a)).map
    (parameterFiniteCorrectionCLM D a)
  apply hg.congr
  filter_upwards [] with w
  funext i
  simp only [Function.comp_apply, parameterFiniteCorrectionCLM,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  change jointEval w (parameterFiniteIndices a (Fin.castAdd k i)) -
      ∑ j : Fin k, (D (euclideanBasisVector j)) (a i) *
        jointEval w (parameterFiniteIndices a (Fin.natAdd m j)) =
    parameterCorrectionCLM D w (a i)
  have hleft : parameterFiniteIndices a (Fin.castAdd k i) = Sum.inl (a i) := by
    simp [parameterFiniteIndices]
  have hright : ∀ j : Fin k,
      parameterFiniteIndices a (Fin.natAdd m j) = Sum.inr j := by
    intro j
    simp [parameterFiniteIndices]
  rw [hleft]
  simp_rw [hright]
  change w.1 (a i) - ∑ j : Fin k,
      (D (euclideanBasisVector j)) (a i) * w.2.ofLp j =
    w.1 (a i) - D w.2 (a i)
  rw [parameterDerivative_eval_eq_sum]

private theorem parameterCorrection_fdd_gaussian_map
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ)
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F)
    (m : ℕ) (a : Fin m → ↥F) :
    HasGaussianLaw (fun z : LinfF F => fun i => z (a i))
      (κ.map (parameterCorrectionCLM D)) := by
  let C := parameterCorrectionCLM D
  let E : LinfF F → (Fin m → ℝ) := fun z i => z (a i)
  have hE : Measurable E := measurable_pi_iff.mpr fun i =>
    (linfEvalCLM F (a i)).continuous.measurable
  have hg := parameterCorrection_fdd_gaussian_on_joint ψ hκ D m a
  refine ⟨?_⟩
  rw [Measure.map_map hE C.continuous.measurable]
  simpa only [C, E, Function.comp_apply] using! hg.isGaussian_map

private theorem jointEval_memLp_two
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ) (a : Sum ↥F (Fin k)) :
    MemLp (fun w => jointEval w a) 2 κ := by
  let pr : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hg := (hκ.gaussianFDD 1 (fun _ => a)).map pr
  simpa only [Function.comp_apply, pr] using! hg.memLp_two

private noncomputable def parameterLinearIndex
    {F : Set (Ω → ℝ)} {k : ℕ} (f : ↥F) :
    Sum Unit (Fin k) → Sum ↥F (Fin k)
  | Sum.inl _ => Sum.inl f
  | Sum.inr j => Sum.inr j

private noncomputable def parameterLinearWeight
    {F : Set (Ω → ℝ)} {k : ℕ}
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (f : ↥F) :
    Sum Unit (Fin k) → ℝ
  | Sum.inl _ => 1
  | Sum.inr j => -(D (euclideanBasisVector j)) f

private noncomputable def parameterJointLinear
    {F : Set (Ω → ℝ)} {k : ℕ}
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (f : ↥F)
    (w : LinfF F × EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∑ q : Sum Unit (Fin k),
    parameterLinearWeight D f q * jointEval w (parameterLinearIndex f q)

private noncomputable def parameterPopulationLinear
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P))
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (f : ↥F) (x : Ω) : ℝ :=
  ∑ q : Sum Unit (Fin k), parameterLinearWeight D f q *
    jointIndexFunction ψ (parameterLinearIndex f q) x

omit [MeasurableSpace Ω] in
private theorem parameterJointLinear_apply
    {F : Set (Ω → ℝ)} {k : ℕ}
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (f : ↥F)
    (w : LinfF F × EuclideanSpace ℝ (Fin k)) :
    parameterJointLinear D f w = parameterCorrectionCLM D w f := by
  rw [parameterJointLinear, Fintype.sum_sum_type]
  simp only [parameterLinearWeight, parameterLinearIndex, jointEval,
    Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]
  rw [show parameterCorrectionCLM D w = w.1 - D w.2 from rfl]
  change 1 * w.1.1 f + ∑ j : Fin k,
      -(D (euclideanBasisVector j)) f * w.2.ofLp j =
    (w.1 - D w.2).1 f
  change 1 * w.1.1 f + ∑ j : Fin k,
      -(D (euclideanBasisVector j)) f * w.2.ofLp j =
    w.1.1 f - (D w.2).1 f
  rw [one_mul]
  rw [parameterDerivative_eval_eq_sum]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

private theorem parameterPopulationLinear_apply
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P))
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (f : ↥F) (x : Ω) :
    parameterPopulationLinear ψ D f x = (f : Ω → ℝ) x -
      ∑ j : Fin k, (D (euclideanBasisVector j)) f * influenceFunction ψ j x := by
  rw [parameterPopulationLinear, Fintype.sum_sum_type]
  simp only [parameterLinearWeight, parameterLinearIndex, jointIndexFunction,
    Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul,
    neg_mul, Finset.sum_neg_distrib]
  ring

private theorem jointIndexFunction_memLp_two
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P)
    (ψ : Fin k → ↥(L2ZeroMean P)) (a : Sum ↥F (Fin k)) :
    MemLp (jointIndexFunction ψ a) 2 P := by
  cases a with
  | inl f => exact hF_L2 f f.2
  | inr j =>
      exact (memLp_congr_ae (influenceFunction_ae_eq ψ j)).mp
        (Lp.memLp (ψ j : Lp ℝ 2 P))

private theorem jointEval_covariance_eq_jointCov
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ) (a b : Sum ↥F (Fin k)) :
    cov[fun w => jointEval w a, fun w => jointEval w b; κ] = jointCov P ψ a b := by
  letI : IsProbabilityMeasure κ := hκ.isProbabilityMeasure
  rw [covariance_eq_sub (jointEval_memLp_two ψ hκ a)
    (jointEval_memLp_two ψ hκ b), hκ.mean, hκ.mean, mul_zero, sub_zero]
  simp only [Pi.mul_apply]
  rw [hκ.covariance]

private theorem jointIndexFunction_covariance_eq_jointCov
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P)
    (ψ : Fin k → ↥(L2ZeroMean P)) (a b : Sum ↥F (Fin k)) :
    cov[jointIndexFunction ψ a, jointIndexFunction ψ b; P] = jointCov P ψ a b := by
  rw [covariance_eq_sub (jointIndexFunction_memLp_two hF_L2 ψ a)
    (jointIndexFunction_memLp_two hF_L2 ψ b)]
  rfl

private theorem parameterLinear_covariance_eq
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P)
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ)
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (f g : ↥F) :
    cov[parameterJointLinear D f, parameterJointLinear D g; κ] =
      cov[parameterPopulationLinear ψ D f, parameterPopulationLinear ψ D g; P] := by
  letI : IsProbabilityMeasure κ := hκ.isProbabilityMeasure
  let Jf : Sum Unit (Fin k) →
      (LinfF F × EuclideanSpace ℝ (Fin k) → ℝ) := fun q w =>
    parameterLinearWeight D f q * jointEval w (parameterLinearIndex f q)
  let Jg : Sum Unit (Fin k) →
      (LinfF F × EuclideanSpace ℝ (Fin k) → ℝ) := fun q w =>
    parameterLinearWeight D g q * jointEval w (parameterLinearIndex g q)
  let Pf : Sum Unit (Fin k) → (Ω → ℝ) := fun q x =>
    parameterLinearWeight D f q * jointIndexFunction ψ (parameterLinearIndex f q) x
  let Pg : Sum Unit (Fin k) → (Ω → ℝ) := fun q x =>
    parameterLinearWeight D g q * jointIndexFunction ψ (parameterLinearIndex g q) x
  have hJf : ∀ q, MemLp (Jf q) 2 κ := fun q =>
    (jointEval_memLp_two ψ hκ (parameterLinearIndex f q)).const_mul _
  have hJg : ∀ q, MemLp (Jg q) 2 κ := fun q =>
    (jointEval_memLp_two ψ hκ (parameterLinearIndex g q)).const_mul _
  have hPf : ∀ q, MemLp (Pf q) 2 P := fun q =>
    (jointIndexFunction_memLp_two hF_L2 ψ (parameterLinearIndex f q)).const_mul _
  have hPg : ∀ q, MemLp (Pg q) 2 P := fun q =>
    (jointIndexFunction_memLp_two hF_L2 ψ (parameterLinearIndex g q)).const_mul _
  change cov[fun w => ∑ q, Jf q w, fun w => ∑ q, Jg q w; κ] =
    cov[fun x => ∑ q, Pf q x, fun x => ∑ q, Pg q x; P]
  rw [covariance_fun_sum_fun_sum hJf hJg, covariance_fun_sum_fun_sum hPf hPg]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  dsimp only [Jf, Jg, Pf, Pg]
  rw [covariance_const_mul_left, covariance_const_mul_right,
    jointEval_covariance_eq_jointCov ψ hκ,
    covariance_const_mul_left, covariance_const_mul_right,
    jointIndexFunction_covariance_eq_jointCov hF_L2 ψ]

private theorem parameterJointLinear_memLp_two
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ)
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (f : ↥F) :
    MemLp (parameterJointLinear D f) 2 κ := by
  unfold parameterJointLinear
  have hsum := memLp_finset_sum' Finset.univ fun q _ =>
    (jointEval_memLp_two ψ hκ (parameterLinearIndex f q)).const_mul
      (parameterLinearWeight D f q)
  have heq : (∑ q : Sum Unit (Fin k), fun w =>
      parameterLinearWeight D f q * jointEval w (parameterLinearIndex f q)) =
      fun w => ∑ q : Sum Unit (Fin k),
        parameterLinearWeight D f q * jointEval w (parameterLinearIndex f q) := by
    funext w
    simp
  rw [← heq]
  exact hsum

private theorem parameterJointLinear_integral_zero
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ)
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (f : ↥F) :
    ∫ w, parameterJointLinear D f w ∂κ = 0 := by
  letI : IsProbabilityMeasure κ := hκ.isProbabilityMeasure
  change (∫ w, ∑ q : Sum Unit (Fin k),
    parameterLinearWeight D f q * jointEval w (parameterLinearIndex f q) ∂κ) = 0
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro q _
    rw [integral_const_mul, hκ.mean, mul_zero]
  · intro q _
    exact ((jointEval_memLp_two ψ hκ (parameterLinearIndex f q)).integrable
      (by norm_num)).const_mul _

private theorem influenceFunction_integral_zero
    {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) (j : Fin k) :
    ∫ x, influenceFunction ψ j x ∂P = 0 := by
  rw [← integral_congr_ae (influenceFunction_ae_eq ψ j)]
  have hz := (ψ j).2
  change integralL2 P (ψ j : Lp ℝ 2 P) = 0 at hz
  unfold integralL2 at hz
  rw [innerSL_apply_apply, L2.inner_def] at hz
  have hone : ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
      fun _ => (1 : ℝ) := (memLp_const (1 : ℝ)).coeFn_toLp
  rw [integral_congr_ae (by
    filter_upwards [hone] with x hx
    rw [hx])] at hz
  have hinner : ∀ y : ℝ, ⟪(1 : ℝ), y⟫_ℝ = y := by
    intro y
    rw [show y = y • (1 : ℝ) by simp, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    norm_num
  simpa only [hinner] using hz

private theorem parameterResidual_ae_eq_centeredLinear
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P)
    (ψ : Fin k → ↥(L2ZeroMean P))
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (f : ↥F) :
    parameterResidual P ψ D f =ᵐ[P] fun x =>
      parameterPopulationLinear ψ D f x - ∫ y, parameterPopulationLinear ψ D f y ∂P := by
  have hfint : Integrable (f : Ω → ℝ) P := (hF_L2 f f.2).integrable (by norm_num)
  have hjint : ∀ j : Fin k, Integrable (influenceFunction ψ j) P := fun j =>
    ((memLp_congr_ae (influenceFunction_ae_eq ψ j)).mp
      (Lp.memLp (ψ j : Lp ℝ 2 P))).integrable (by norm_num)
  have hPmean : ∫ y, parameterPopulationLinear ψ D f y ∂P =
      ∫ y, (f : Ω → ℝ) y ∂P := by
    rw [integral_congr_ae (Eventually.of_forall fun x => parameterPopulationLinear_apply ψ D f x)]
    rw [integral_sub hfint (integrable_finset_sum _ fun j _ => (hjint j).const_mul _),
      integral_finset_sum]
    · have hsum0 : ∑ j : Fin k,
          ∫ a, (D (euclideanBasisVector j)) f * influenceFunction ψ j a ∂P = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [integral_const_mul, influenceFunction_integral_zero, mul_zero]
      rw [hsum0, sub_zero]
    · exact fun j _ => (hjint j).const_mul _
  have hall : ∀ᵐ x ∂P, ∀ j : Fin k,
      ((((ψ j : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) x) =
        influenceFunction ψ j x := ae_all_iff.mpr fun j => influenceFunction_ae_eq ψ j
  filter_upwards [hall] with x hx
  rw [parameterPopulationLinear_apply, hPmean]
  unfold parameterResidual
  simp_rw [hx]
  ring

private theorem parameterCorrection_covariance_map
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P)
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ)
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (f g : ↥F) :
    ∫ z : LinfF F, z f * z g ∂(κ.map (parameterCorrectionCLM D)) =
      parameterLimitCov P ψ D f g := by
  letI : IsProbabilityMeasure κ := hκ.isProbabilityMeasure
  have hEval : AEStronglyMeasurable (fun z : LinfF F => z f * z g)
      (κ.map (parameterCorrectionCLM D)) :=
    ((linfEvalCLM F f).continuous.measurable.aestronglyMeasurable.mul
      (linfEvalCLM F g).continuous.measurable.aestronglyMeasurable)
  rw [integral_map (parameterCorrectionCLM D).continuous.measurable.aemeasurable hEval]
  have hJf := parameterJointLinear_memLp_two ψ hκ D f
  have hJg := parameterJointLinear_memLp_two ψ hκ D g
  calc
    (∫ w, parameterCorrectionCLM D w f * parameterCorrectionCLM D w g ∂κ) =
        ∫ w, parameterJointLinear D f w * parameterJointLinear D g w ∂κ := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [parameterJointLinear_apply, parameterJointLinear_apply]
    _ = cov[parameterJointLinear D f, parameterJointLinear D g; κ] := by
      rw [covariance_eq_sub hJf hJg]
      simp only [Pi.mul_apply]
      rw [
        parameterJointLinear_integral_zero ψ hκ D f,
        parameterJointLinear_integral_zero ψ hκ D g, mul_zero, sub_zero]
    _ = cov[parameterPopulationLinear ψ D f, parameterPopulationLinear ψ D g; P] :=
      parameterLinear_covariance_eq hF_L2 ψ hκ D f g
    _ = parameterLimitCov P ψ D f g := by
      rw [covariance, parameterLimitCov]
      apply integral_congr_ae
      exact (parameterResidual_ae_eq_centeredLinear P hF_L2 ψ D f).mul
        (parameterResidual_ae_eq_centeredLinear P hF_L2 ψ D g) |>.symm

private theorem parameterCorrection_mean_map
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) {ν : Measure (LinfF F)}
    {κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k))}
    (hκ : IsJointBridgeInfluence F P ψ ν κ)
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F) (f : ↥F) :
    ∫ z : LinfF F, z f ∂(κ.map (parameterCorrectionCLM D)) = 0 := by
  letI : IsProbabilityMeasure κ := hκ.isProbabilityMeasure
  have hEval : AEStronglyMeasurable (fun z : LinfF F => z f)
      (κ.map (parameterCorrectionCLM D)) :=
    (linfEvalCLM F f).continuous.measurable.aestronglyMeasurable
  rw [integral_map (parameterCorrectionCLM D).continuous.measurable.aemeasurable hEval]
  have heq : (fun w : LinfF F × EuclideanSpace ℝ (Fin k) =>
      parameterCorrectionCLM D w f) = fun w =>
        jointEval w (Sum.inl f) - ∑ j : Fin k,
          (D (euclideanBasisVector j)) f * jointEval w (Sum.inr j) := by
    funext w
    change w.1 f - D w.2 f = w.1 f - ∑ j : Fin k,
      (D (euclideanBasisVector j)) f * w.2.ofLp j
    rw [parameterDerivative_eval_eq_sum]
  rw [heq]
  have hfint : Integrable (fun w => jointEval w (Sum.inl f)) κ :=
    (jointEval_memLp_two ψ hκ (Sum.inl f)).integrable (by norm_num)
  have hjint : ∀ j : Fin k, Integrable (fun w => jointEval w (Sum.inr j)) κ :=
    fun j => (jointEval_memLp_two ψ hκ (Sum.inr j)).integrable (by norm_num)
  have hsumint : Integrable (fun w => ∑ j : Fin k,
      (D (euclideanBasisVector j)) f * jointEval w (Sum.inr j)) κ :=
    integrable_finset_sum _ fun j _ => (hjint j).const_mul _
  rw [integral_sub hfint hsumint, integral_finset_sum]
  · rw [hκ.mean]
    simp only [zero_sub, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro j _
    rw [integral_const_mul, hκ.mean, mul_zero]
  · exact fun j _ => (hjint j).const_mul _

/-- The nonlinear parameter-estimation remainder is negligible in outer
probability in the full `ℓ∞(F)` norm. This is the path-valued form of (19.22),
not a pointwise remainder statement. -/
theorem parameter_estimation_remainder_outer
    {F : Set (Ω → ℝ)}
    (P_θ : EuclideanSpace ℝ (Fin k) → Measure Ω)
    (θ₀ : EuclideanSpace ℝ (Fin k)) [IsProbabilityMeasure (P_θ θ₀)]
    (ψ : Fin k → ↥(L2ZeroMean (P_θ θ₀)))
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (Q : EuclideanSpace ℝ (Fin k) → LinfF F)
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F)
    -- USER-INPUT: Donsker, asymptotic-linearity, differentiability, and remainder
    -- hypotheses bundled from vdV Theorem 19.23.
    (h : Theorem19_23FiniteHyp F P_θ θ₀ ψ θ_hat Q D)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P_θ θ₀)
    (hmem : ∀ n ξ, Memℓp
      (fun f : ↥F => empiricalProcess (P_θ θ₀) n
        (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)) ∞) :
    ∀ δ > 0, Tendsto
      (fun n => μ.real {ξ | δ ≤ dist
        (parameterCorrectionCLM D
          (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
            influenceEmpiricalVector (P_θ θ₀) ψ n
              (fun i : Fin n => X i.val ξ)))
        (parameterEstimatedProcess Q θ₀ (θ_hat n)
          (fun i : Fin n => X i.val ξ) (hmem n ξ))})
      atTop (𝓝 0) := by
  let T : ℕ → Ξ → EuclideanSpace ℝ (Fin k) := fun n ξ =>
    θ_hat n (fun i : Fin n => X i.val ξ)
  let V : ℕ → Ξ → EuclideanSpace ℝ (Fin k) := fun n ξ =>
    influenceEmpiricalVector (P_θ θ₀) ψ n (fun i : Fin n => X i.val ξ)
  let S : ℕ → Ξ → EuclideanSpace ℝ (Fin k) := fun n ξ =>
    Real.sqrt n • (T n ξ - θ₀)
  let R : ℕ → Ξ → EuclideanSpace ℝ (Fin k) := fun n ξ => S n ξ - V n ξ
  have hALraw := asymptoticallyLinearAt_vec_on_iid_sample (P_θ θ₀) ψ θ_hat θ₀
    h.asymptoticallyLinear μ X hX_meas hX_indep hX_id hX_law
  have hAL : AsymptoticStatistics.TendstoInProbZero (fun _ => μ) R := by
    intro ε hε
    have hraw := hALraw ε hε
    refine hraw.congr' (Eventually.of_forall fun n => ?_)
    apply congrArg ENNReal.toReal
    apply MeasureTheory.measure_congr
    filter_upwards [influenceEmpiricalVector_ae_eq_raw (P_θ θ₀) ψ μ X
      hX_meas hX_id hX_law n] with ξ hV
    change (ε ≤ ‖Real.sqrt n • (T n ξ - θ₀) -
        (Real.sqrt n)⁻¹ • ∑ i : Fin n, tupleEval (P_θ θ₀) ψ (X i.val ξ)‖) =
      (ε ≤ ‖R n ξ‖)
    rw [show R n ξ = Real.sqrt n • (T n ξ - θ₀) - V n ξ from rfl,
      show V n ξ = influenceEmpiricalVector (P_θ θ₀) ψ n
        (fun i : Fin n => X i.val ξ) from rfl, hV]
  have hVOP := influenceEmpiricalVector_isBoundedInProb (P_θ θ₀) ψ μ X
    hX_meas hX_indep hX_id hX_law
  have hStight : ∀ η > 0, ∃ M : ℝ,
      ∀ᶠ n in atTop, μ.real {ξ | M < ‖S n ξ‖} ≤ η := by
    intro η hη
    have hη2 : 0 < η / 2 := by positivity
    obtain ⟨MV, hMV⟩ := hVOP (η / 2) hη2
    have hRev : ∀ᶠ n in atTop, μ.real {ξ | (1 : ℝ) ≤ ‖R n ξ‖} < η / 2 :=
      (hAL 1 zero_lt_one).eventually (Iio_mem_nhds hη2)
    refine ⟨MV + 1, ?_⟩
    filter_upwards [hRev] with n hRn
    have hsub : {ξ | MV + 1 < ‖S n ξ‖} ⊆
        {ξ | MV < ‖V n ξ‖} ∪ {ξ | (1 : ℝ) ≤ ‖R n ξ‖} := by
      intro ξ hξ
      by_contra hnot
      rw [Set.mem_union, not_or] at hnot
      have hVle : ‖V n ξ‖ ≤ MV := not_lt.mp hnot.1
      have hRlt : ‖R n ξ‖ < 1 := not_le.mp hnot.2
      have hdec : S n ξ = R n ξ + V n ξ := by
        dsimp only [R]
        abel
      change MV + 1 < ‖S n ξ‖ at hξ
      rw [hdec] at hξ
      linarith [norm_add_le (R n ξ) (V n ξ)]
    calc
      μ.real {ξ | MV + 1 < ‖S n ξ‖}
          ≤ μ.real ({ξ | MV < ‖V n ξ‖} ∪ {ξ | (1 : ℝ) ≤ ‖R n ξ‖}) :=
        measureReal_mono hsub
      _ ≤ μ.real {ξ | MV < ‖V n ξ‖} + μ.real {ξ | (1 : ℝ) ≤ ‖R n ξ‖} :=
        measureReal_union_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add (hMV n) hRn.le
      _ = η := by ring
  have hcons : AsymptoticStatistics.TendstoInProbZero (fun _ => μ)
      (fun n ξ => T n ξ - θ₀) := by
    intro ε hε
    rw [Metric.tendsto_atTop]
    intro η hη
    have hη2 : 0 < η / 2 := by positivity
    obtain ⟨M, hM⟩ := hStight (η / 2) hη2
    have hsqrt : ∀ᶠ n : ℕ in atTop, M / ε < Real.sqrt n :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
        (M / ε)
    apply eventually_atTop.mp
    filter_upwards [hM, hsqrt] with n hMn hsn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    have hsub : {ξ | ε ≤ ‖T n ξ - θ₀‖} ⊆ {ξ | M < ‖S n ξ‖} := by
      intro ξ hξ
      have hsqrt0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
      have hMlt : M < Real.sqrt n * ε := by
        calc
          M = (M / ε) * ε := by field_simp
          _ < Real.sqrt n * ε := mul_lt_mul_of_pos_right hsn hε
      calc
        M < Real.sqrt n * ε := hMlt
        _ ≤ Real.sqrt n * ‖T n ξ - θ₀‖ :=
          mul_le_mul_of_nonneg_left hξ hsqrt0
        _ = ‖S n ξ‖ := by simp [S, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrt0]
    exact lt_of_le_of_lt (measureReal_mono hsub |>.trans hMn) (half_lt_self hη)
  let NQ : ℕ → Ξ → LinfF F := fun n ξ =>
    Real.sqrt n • (Q (T n ξ) - Q θ₀ - D (T n ξ - θ₀))
  have hQrem : AsymptoticStatistics.TendstoInProbZero (fun _ => μ) NQ := by
    intro ε hε
    rw [Metric.tendsto_atTop]
    intro η hη
    have hη2 : 0 < η / 2 := by positivity
    obtain ⟨M₀, hM₀⟩ := hStight (η / 2) hη2
    let M : ℝ := max M₀ 1
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right M₀ 1)
    have hMev : ∀ᶠ n in atTop, μ.real {ξ | M < ‖S n ξ‖} ≤ η / 2 := by
      filter_upwards [hM₀] with n hn
      exact (measureReal_mono fun ξ hξ => lt_of_le_of_lt (le_max_left M₀ 1) hξ).trans hn
    have hc : 0 < ε / (2 * M) := by positivity
    have hcM : ε / (2 * M) * M = ε / 2 := by field_simp
    obtain ⟨r, hrpos, hr⟩ :=
      Metric.eventually_nhds_iff.mp ((Asymptotics.isLittleO_iff.mp h.frechet.isLittleO) hc)
    have hconsev : ∀ᶠ n in atTop,
        μ.real {ξ | r ≤ ‖T n ξ - θ₀‖} < η / 2 :=
      (hcons r hrpos).eventually (Iio_mem_nhds hη2)
    apply eventually_atTop.mp
    filter_upwards [hMev, hconsev] with n hMn hcn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    have hsub : {ξ | ε ≤ ‖NQ n ξ‖} ⊆
        {ξ | r ≤ ‖T n ξ - θ₀‖} ∪ {ξ | M < ‖S n ξ‖} := by
      intro ξ hξ
      by_contra hnot
      rw [Set.mem_union, not_or] at hnot
      have hlocal : dist (T n ξ) θ₀ < r := by
        rw [dist_eq_norm]
        exact not_le.mp hnot.1
      have hTaylor := hr hlocal
      have hSle : ‖S n ξ‖ ≤ M := not_lt.mp hnot.2
      have hsqrt0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
      have hchain : ‖NQ n ξ‖ ≤ ε / 2 := by
        rw [show NQ n ξ = Real.sqrt n •
          (Q (T n ξ) - Q θ₀ - D (T n ξ - θ₀)) from rfl,
          norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrt0]
        calc
          Real.sqrt n * ‖Q (T n ξ) - Q θ₀ - D (T n ξ - θ₀)‖
              ≤ Real.sqrt n * ((ε / (2 * M)) * ‖T n ξ - θ₀‖) :=
            mul_le_mul_of_nonneg_left hTaylor hsqrt0
          _ = (ε / (2 * M)) * ‖S n ξ‖ := by
            rw [show ‖S n ξ‖ = Real.sqrt n * ‖T n ξ - θ₀‖ by
              simp [S, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrt0]]
            ring
          _ ≤ (ε / (2 * M)) * M := mul_le_mul_of_nonneg_left hSle hc.le
          _ = ε / 2 := hcM
      change ε ≤ ‖NQ n ξ‖ at hξ
      linarith
    calc
      μ.real {ξ | ε ≤ ‖NQ n ξ‖}
          ≤ μ.real ({ξ | r ≤ ‖T n ξ - θ₀‖} ∪ {ξ | M < ‖S n ξ‖}) :=
        measureReal_mono hsub
      _ ≤ μ.real {ξ | r ≤ ‖T n ξ - θ₀‖} + μ.real {ξ | M < ‖S n ξ‖} :=
        measureReal_union_le _ _
      _ < η / 2 + η / 2 := add_lt_add_of_lt_of_le hcn hMn
      _ = η := by ring
  intro δ hδ
  let c : ℝ := δ / (2 * (‖D‖ + 1))
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hDc : ‖D‖ * c < δ / 2 := by
    dsimp only [c]
    have hnorm : 0 ≤ ‖D‖ := norm_nonneg _
    have hden : 0 < ‖D‖ + 1 := by positivity
    calc
      ‖D‖ * (δ / (2 * (‖D‖ + 1)))
          = δ / 2 * (‖D‖ / (‖D‖ + 1)) := by field_simp
      _ < δ / 2 * 1 := mul_lt_mul_of_pos_left
        ((div_lt_one hden).2 (by linarith)) (half_pos hδ)
      _ = δ / 2 := mul_one _
  have hbound : ∀ n,
      μ.real {ξ | δ ≤ dist
        (parameterCorrectionCLM D
          (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
            influenceEmpiricalVector (P_θ θ₀) ψ n
              (fun i : Fin n => X i.val ξ)))
        (parameterEstimatedProcess Q θ₀ (θ_hat n)
          (fun i : Fin n => X i.val ξ) (hmem n ξ))} ≤
      μ.real {ξ | δ / 2 ≤ ‖NQ n ξ‖} + μ.real {ξ | c ≤ ‖R n ξ‖} := by
    intro n
    apply (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro ξ hξ
    have hdist : dist
        (parameterCorrectionCLM D
          (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
            influenceEmpiricalVector (P_θ θ₀) ψ n
              (fun i : Fin n => X i.val ξ)))
        (parameterEstimatedProcess Q θ₀ (θ_hat n)
          (fun i : Fin n => X i.val ξ) (hmem n ξ)) =
        ‖NQ n ξ + D (R n ξ)‖ := by
      change dist
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ) - D (V n ξ))
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ) -
          Real.sqrt n • (Q (T n ξ) - Q θ₀)) = ‖NQ n ξ + D (R n ξ)‖
      have hmap : D (Real.sqrt n • (T n ξ - θ₀) - V n ξ) =
          Real.sqrt n • D (T n ξ - θ₀) - D (V n ξ) := by
        rw [map_sub, map_smul]
      have hsmul : Real.sqrt n •
          (Q (T n ξ) - Q θ₀ - D (T n ξ - θ₀)) =
          Real.sqrt n • (Q (T n ξ) - Q θ₀) -
            Real.sqrt n • D (T n ξ - θ₀) := smul_sub _ _ _
      rw [dist_eq_norm]
      congr 1
      rw [show NQ n ξ = Real.sqrt n •
        (Q (T n ξ) - Q θ₀ - D (T n ξ - θ₀)) from rfl,
        show R n ξ = Real.sqrt n • (T n ξ - θ₀) - V n ξ from rfl,
        hmap, hsmul]
      abel
    change δ ≤ dist
      (parameterCorrectionCLM D
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
          influenceEmpiricalVector (P_θ θ₀) ψ n (fun i : Fin n => X i.val ξ)))
      (parameterEstimatedProcess Q θ₀ (θ_hat n)
        (fun i : Fin n => X i.val ξ) (hmem n ξ)) at hξ
    rw [hdist] at hξ
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hNlt : ‖NQ n ξ‖ < δ / 2 := not_le.mp hnot.1
    have hRlt : ‖R n ξ‖ < c := not_le.mp hnot.2
    have hDR : ‖D (R n ξ)‖ ≤ ‖D‖ * ‖R n ξ‖ := D.le_opNorm _
    have hDRlt : ‖D (R n ξ)‖ < δ / 2 :=
      hDR.trans_lt ((mul_le_mul_of_nonneg_left hRlt.le (norm_nonneg D)).trans_lt hDc)
    linarith [norm_add_le (NQ n ξ) (D (R n ξ))]
  apply squeeze_zero (fun _ => measureReal_nonneg) hbound
  simpa only [add_zero] using (hQrem (δ / 2) (half_pos hδ)).add (hAL c hc)

set_option linter.unusedVariables false in
/-- **Theorem 19.23, finite-dimensional joint-process form.**

The first convergence below is the joint outer weak convergence of
`(𝔾ₙ, n⁻¹ᐟ² Σψ(Xᵢ))` in `ℓ∞(F) × ℝᵏ`. The second is its continuous-linear
image and Slutsky transfer, hence genuine outer weak convergence of the full
`f ↦ √n(Pₙf-P_{θ̂ₙ}f)` path in `ℓ∞(F)`. The final predicate records Gaussian
finite-dimensional marginals and the correct residual covariance. -/
theorem empiricalProcess_parameter_estimation_finite
    {F : Set (Ω → ℝ)}
    (P_θ : EuclideanSpace ℝ (Fin k) → Measure Ω)
    (θ₀ : EuclideanSpace ℝ (Fin k)) [IsProbabilityMeasure (P_θ θ₀)]
    (ψ : Fin k → ↥(L2ZeroMean (P_θ θ₀)))
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (Q : EuclideanSpace ℝ (Fin k) → LinfF F)
    (D : EuclideanSpace ℝ (Fin k) →L[ℝ] LinfF F)
    -- USER-INPUT: Donsker, asymptotic-linearity, differentiability, and remainder
    -- hypotheses bundled from vdV Theorem 19.23.
    (h : Theorem19_23FiniteHyp F P_θ θ₀ ψ θ_hat Q D)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    -- LEAN-ONLY: measurability of each sample coordinate.
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: iid observations from `P_{θ₀}`; vdV Theorem 19.23.
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P_θ θ₀) :
    ∃ (ν : Measure (LinfF F))
      (κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k)))
      (hν : IsPBrownianBridge F (P_θ θ₀) ν)
      (hκ : IsJointBridgeInfluence F (P_θ θ₀) ψ ν κ)
      (hmem : ∀ n ξ, Memℓp
        (fun f : ↥F => empiricalProcess (P_θ θ₀) n
          (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)) ∞),
      WeakConvergesOuter (fun _ => μ)
        (fun n ξ =>
          (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ),
            influenceEmpiricalVector (P_θ θ₀) ψ n
              (fun i : Fin n => X i.val ξ))) κ
      ∧ WeakConvergesOuter (fun _ => μ)
        (fun n ξ => parameterEstimatedProcess Q θ₀ (θ_hat n)
          (fun i : Fin n => X i.val ξ) (hmem n ξ))
        (κ.map (parameterCorrectionCLM D))
      ∧ IsParameterEstimationLimit F (P_θ θ₀) ψ D
        (κ.map (parameterCorrectionCLM D)) := by
  obtain ⟨ν, κ, hν, hκ, hmem, hjoint⟩ :=
    h.donsker.jointInfluence_weakConvergesOuter ψ μ X hX_meas hX_indep hX_id hX_law
  letI : IsProbabilityMeasure κ := hκ.isProbabilityMeasure
  letI : IsProbabilityMeasure (κ.map (parameterCorrectionCLM D)) :=
    Measure.isProbabilityMeasure_map
      (parameterCorrectionCLM D).continuous.measurable.aemeasurable
  have hmapped := hjoint.map (parameterCorrectionCLM D)
    (parameterCorrectionCLM D).continuous
    (parameterCorrectionCLM D).continuous.measurable.aemeasurable
  have hremainder := parameter_estimation_remainder_outer P_θ θ₀ ψ θ_hat Q D h μ X
    hX_meas hX_indep hX_id hX_law hmem
  have hestimated : WeakConvergesOuter (fun _ => μ)
      (fun n ξ => parameterEstimatedProcess Q θ₀ (θ_hat n)
        (fun i : Fin n => X i.val ξ) (hmem n ξ))
      (κ.map (parameterCorrectionCLM D)) :=
    hmapped.slutsky_of_tendstoInOuterProbability_dist hremainder
  have hlimit : IsParameterEstimationLimit F (P_θ θ₀) ψ D
      (κ.map (parameterCorrectionCLM D)) := by
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · exact parameterCorrection_fdd_gaussian_map ψ hκ D
    · exact parameterCorrection_mean_map ψ hκ D
    · exact parameterCorrection_covariance_map (fun f hf => h.donsker.memLp hf) ψ hκ D
  exact ⟨ν, κ, hν, hκ, hmem, hjoint, hestimated, hlimit⟩

end AsymptoticStatistics.EmpiricalProcess
