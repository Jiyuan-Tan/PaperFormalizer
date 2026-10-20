module
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-!
# Rademacher signs and their finite product law

This file provides the uniform Boolean realization of a Rademacher sign and
its finite product measure.  The convention is `false ↦ 1` and `true ↦ -1`.
-/

open MeasureTheory

namespace ProbabilityTheory

/-- The uniform probability mass function on the two Boolean values. -/
noncomputable def rademacherPMF : PMF Bool :=
  PMF.uniformOfFintype Bool

/-- The uniform probability measure on the two Boolean values. -/
noncomputable def rademacherMeasure : Measure Bool :=
  rademacherPMF.toMeasure

instance rademacherMeasure_isProbabilityMeasure :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- A Rademacher sign, with the convention `false ↦ 1` and `true ↦ -1`. -/
def rademacherSign (b : Bool) : ℝ :=
  if b then -1 else 1

/-- The law of `n` independent Boolean Rademacher signs.

For `n = 0`, this is the probability measure on the singleton empty product.
-/
noncomputable def rademacherCube (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ => rademacherMeasure)

instance rademacherCube_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (rademacherCube n) := by
  unfold rademacherCube
  infer_instance

/-- A Rademacher sign has mean zero under the uniform Boolean law. -/
theorem integral_rademacherSign :
    ∫ b, rademacherSign b ∂rademacherMeasure = 0 := by
  rw [rademacherMeasure, PMF.integral_eq_sum]
  simp [rademacherPMF, rademacherSign]

/-- A Rademacher sign is sub-Gaussian with proxy variance one. -/
theorem rademacherSign_hasSubgaussianMGF :
    HasSubgaussianMGF rademacherSign 1 rademacherMeasure := by
  have hmeas : AEMeasurable rademacherSign rademacherMeasure :=
    (measurable_of_finite rademacherSign).aemeasurable
  have hbound : ∀ᵐ b ∂rademacherMeasure, rademacherSign b ∈ Set.Icc (-1 : ℝ) 1 :=
    Filter.Eventually.of_forall fun b => by
      cases b <;> simp [rademacherSign]
  convert hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := rademacherSign) (μ := rademacherMeasure) hmeas hbound integral_rademacherSign using 1
  norm_num

/-- The weighted sum of a finite family of Rademacher signs. -/
noncomputable def rademacherSum {n : ℕ}
    (a : Fin n → ℝ) (ε : Fin n → Bool) : ℝ :=
  ∑ i, a i * rademacherSign (ε i)

/-- A weighted sum of independent Rademacher signs is sub-Gaussian with
proxy variance equal to the sum of the squared weights. -/
theorem rademacherSum_hasSubgaussianMGF {n : ℕ} (a : Fin n → ℝ) :
    HasSubgaussianMGF (rademacherSum a)
      (∑ i, ⟨(a i)^2, sq_nonneg (a i)⟩) (rademacherCube n) := by
  classical
  have h_indep :
      iIndepFun (fun i (ε : Fin n → Bool) => a i * rademacherSign (ε i))
        (rademacherCube n) := by
    unfold rademacherCube
    have h_eval := iIndepFun_pi
      (μ := fun _ : Fin n => rademacherMeasure)
      (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    simpa [Function.comp_def] using h_eval.comp
      (fun i b => a i * rademacherSign b) (fun _ => measurable_of_finite _)
  have h_coord (i : Fin n) :
      HasSubgaussianMGF
        (fun ε : Fin n → Bool => a i * rademacherSign (ε i))
        ⟨(a i) ^ 2, sq_nonneg (a i)⟩ (rademacherCube n) := by
    have h_mapped :
        HasSubgaussianMGF (fun b => a i * rademacherSign b)
          ⟨(a i) ^ 2, sq_nonneg (a i)⟩
          ((rademacherCube n).map fun ε => ε i) := by
      rw [rademacherCube,
        (measurePreserving_eval (fun _ : Fin n => rademacherMeasure) i).map_eq]
      have h := rademacherSign_hasSubgaussianMGF.const_mul (a i)
      have e : (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : NNReal) * 1 = ⟨(a i) ^ 2, sq_nonneg (a i)⟩ :=
        mul_one _
      exact e ▸ h
    simpa [Function.comp_def] using
      HasSubgaussianMGF.of_map (μ := rademacherCube n)
        (Y := fun ε : Fin n → Bool => ε i)
        (X := fun b => a i * rademacherSign b)
        (measurable_pi_apply i).aemeasurable h_mapped
  simpa [rademacherSum] using!
    (HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) h_indep
      (fun i _ => h_coord i))

end ProbabilityTheory
