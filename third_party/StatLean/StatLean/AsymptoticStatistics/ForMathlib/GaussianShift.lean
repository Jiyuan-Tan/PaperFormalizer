module
public import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-!
# Multivariate Gaussian shift change of measure

The standard Gaussian-shift Radon–Nikodym identity in the **product** form,
between two centred-product multivariate Gaussians with identity covariance
differing only in mean:
```
∫ X, f X ∂Measure.pi (fun i => gaussianReal (h i) 1)
  = ∫ X, exp(∑ i, h i * X i - ∑ i, (h i)^2 / 2) * f X
      ∂Measure.pi (fun _ => gaussianReal 0 1).
```

The headline declarations are `gaussianShift_change_of_measure` (the Girsanov
change-of-measure identity) and `gaussianShift_integrable` (integrability of
the shift-weighted bounded loss). The identity is assembled from the 1D
Gaussian Girsanov shift `gaussianReal_withDensity_exp_shift_1d`, the
`Measure.pi` `withDensity` decomposition `pi_withDensity_prod`, and
`integral_withDensity_eq_integral_toReal_smul`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- **1D Gaussian Girsanov shift density identity**: tilting the standard
1D Gaussian `N(0, 1)` by the exponential `exp(a·x - a²/2)` shifts its mean
to `a`:
```
(gaussianReal 0 1).withDensity (fun x => ENNReal.ofReal (exp(a·x - a²/2)))
  = gaussianReal a 1.
```
Both sides admit explicit `volume.withDensity gaussianPDF`-form (variance
`1 ≠ 0`); the identity reduces to the pointwise PDF identity
`gaussianPDFReal 0 1 x · exp(a·x - a²/2) = gaussianPDFReal a 1 x`. -/
private lemma gaussianReal_withDensity_exp_shift_1d (a : ℝ) :
    (gaussianReal 0 1).withDensity
        (fun x => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2)))
      = gaussianReal a 1 := by
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0),
    gaussianReal_of_var_ne_zero a (by norm_num : (1 : NNReal) ≠ 0)]
  have h_tilt_meas :
      Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2))) := by
    fun_prop
  rw [← MeasureTheory.withDensity_mul volume (measurable_gaussianPDF 0 1) h_tilt_meas]
  congr 1
  ext x
  -- Pointwise identity on densities. Move `ENNReal.ofReal` out and reduce
  -- to a real algebra step `exp(-x²/2) · exp(a·x - a²/2) = exp(-(x-a)²/2)`.
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Pi-product 1D Gaussian Girsanov shift density**: tilting the product
of `ι` copies of `N(0, 1)` by the multivariate Girsanov density
`exp(∑ᵢ hᵢ yᵢ − ∑ᵢ hᵢ²/2)` shifts each coordinate's mean independently:
```
(Measure.pi (fun _ => gaussianReal 0 1)).withDensity
    (fun y => ENNReal.ofReal (exp (∑ i, h i * y i - ∑ i, (h i)² / 2)))
  = Measure.pi (fun i => gaussianReal (h i) 1).
```

Proof: the density factors as `∏ᵢ exp(hᵢ yᵢ - hᵢ²/2)`; apply
`pi_withDensity_prod` to factor the `withDensity` into per-coordinate
tilts; each per-coordinate tilt is the 1D Girsanov shift
`gaussianReal_withDensity_exp_shift_1d`. -/
private lemma pi_gaussianReal_withDensity_exp_shift
    {ι : Type*} [Fintype ι] (h : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).withDensity
        (fun y => ENNReal.ofReal
          (Real.exp ((∑ i, h i * y i) - ∑ i, (h i) ^ 2 / 2)))
      = Measure.pi (fun i : ι => gaussianReal (h i) 1) := by
  classical
  have h1d : ∀ i, (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (h i * x - (h i) ^ 2 / 2)))
        = gaussianReal (h i) 1 :=
    fun i => gaussianReal_withDensity_exp_shift_1d (h i)
  haveI : ∀ i, IsProbabilityMeasure ((gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (h i * x - (h i) ^ 2 / 2)))) := by
    intro i; rw [h1d i]; infer_instance
  -- Factor `exp(∑ - ∑) = ∏ exp(_ - _)` so `pi_withDensity_prod` applies.
  have h_density : (fun y : ι → ℝ =>
        ENNReal.ofReal (Real.exp ((∑ i, h i * y i) - ∑ i, (h i) ^ 2 / 2)))
      = fun y => ∏ i, ENNReal.ofReal (Real.exp (h i * y i - (h i) ^ 2 / 2)) := by
    funext y
    rw [show ((∑ i, h i * y i) - ∑ i, (h i) ^ 2 / 2)
          = ∑ i, (h i * y i - (h i) ^ 2 / 2) from
          (Finset.sum_sub_distrib _ _).symm,
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg
        (fun _ _ => Real.exp_nonneg _)]
  rw [h_density, pi_withDensity_prod
    (f := fun i x => ENNReal.ofReal (Real.exp (h i * x - (h i) ^ 2 / 2)))
    (fun i => by fun_prop)]
  congr 1
  funext i
  exact h1d i

/-- **Multivariate Gaussian shift change of measure** (`Measure.pi` form).

For any `ι : Fintype`, mean-shift vector `h : ι → ℝ`, and integrable
`f : (ι → ℝ) → ℝ`, integration against the shifted product Gaussian
`Measure.pi (fun i => gaussianReal (h i) 1)` equals integration against
the centred product Gaussian `Measure.pi (fun _ => gaussianReal 0 1)`
weighted by the multivariate Gaussian-shift density
`exp(∑ i, h i * X i - ∑ i, (h i)² / 2)`:

```
∫ X, f X ∂Measure.pi (fun i => gaussianReal (h i) 1)
  = ∫ X, exp(∑ i, h i * X i - ∑ i, (h i)^2 / 2) * f X
      ∂Measure.pi (fun _ => gaussianReal 0 1).
```

This is the standard multivariate Girsanov identity for identity-covariance
Gaussians. The Radon–Nikodym derivative
`d N(h, I) / d N(0, I) (X) = exp(⟨h, X⟩ − ‖h‖²/2)` is folded into the
integrand on the right.

**Proof.** Apply `pi_gaussianReal_withDensity_exp_shift` (above) to rewrite
the LHS measure as a `withDensity` against the centred product. Then
`integral_withDensity_eq_integral_toReal_smul` converts to an integral
against the centred measure with the density inserted. The density's
`ENNReal.ofReal (Real.exp _)`-form has `.toReal = Real.exp _` because
`Real.exp` is non-negative; `smul` on `ℝ` is multiplication. -/
theorem gaussianShift_change_of_measure
    {ι : Type*} [Fintype ι] (h : ι → ℝ) (f : (ι → ℝ) → ℝ) :
    ∫ X : ι → ℝ, f X ∂Measure.pi (fun i : ι => gaussianReal (h i) 1)
      = ∫ X : ι → ℝ,
          Real.exp ((∑ i, h i * X i) - (∑ i, (h i) ^ 2) / 2) * f X
            ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  -- Step 1: rewrite the shifted product Gaussian as a `withDensity` tilt
  -- of the centred product Gaussian by the multivariate Girsanov density.
  -- Match the `∑ (h i)^2 / 2` convention of `pi_gaussianReal_withDensity_exp_shift`
  -- by pulling the `1/2` outside the sum.
  have h_sum_div : (∑ i, (h i) ^ 2) / 2 = ∑ i, (h i) ^ 2 / 2 := by
    rw [Finset.sum_div]
  have h_density :
      Measure.pi (fun i : ι => gaussianReal (h i) 1)
        = (Measure.pi (fun _ : ι => gaussianReal 0 1)).withDensity
            (fun y => ENNReal.ofReal
              (Real.exp ((∑ i, h i * y i) - (∑ i, (h i) ^ 2) / 2))) := by
    rw [show (fun y : ι → ℝ =>
          ENNReal.ofReal
            (Real.exp ((∑ i, h i * y i) - (∑ i, (h i) ^ 2) / 2)))
          = (fun y : ι → ℝ =>
            ENNReal.ofReal
              (Real.exp ((∑ i, h i * y i) - ∑ i, (h i) ^ 2 / 2))) from ?_]
    · exact (pi_gaussianReal_withDensity_exp_shift h).symm
    · funext _; rw [h_sum_div]
  rw [h_density]
  -- Step 2: push the density into the integrand via
  -- `integral_withDensity_eq_integral_toReal_smul`.
  have h_meas :
      Measurable (fun y : ι → ℝ =>
        ENNReal.ofReal
          (Real.exp ((∑ i, h i * y i) - (∑ i, (h i) ^ 2) / 2))) := by
    fun_prop
  have h_lt_top : ∀ᵐ y ∂Measure.pi (fun _ : ι => gaussianReal 0 1),
      ENNReal.ofReal
          (Real.exp ((∑ i, h i * y i) - (∑ i, (h i) ^ 2) / 2)) < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul h_meas h_lt_top]
  -- Step 3: reduce `(ENNReal.ofReal (exp _)).toReal • f X` to `exp _ * f X`.
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

/-- **Integrability of the Gaussian-shift–weighted bounded loss**.

For any mean-shift vector `h : ι → ℝ` (with `ι` a finite type), any
**bounded AE-strongly-measurable** function `f : (ι → ℝ) → ℝ`, and the
multivariate Gaussian-shift density `exp(∑ i, h i · X i − ‖h‖²/2)`,
the product is integrable against the centred product Gaussian
`Measure.pi (fun _ => gaussianReal 0 1)`.

**Proof.** The exponential factorises as
`exp(-‖h‖²/2) · ∏ i, exp(h i · X i)`. Each per-coordinate factor is
integrable against `gaussianReal 0 1` by Mathlib's
`ProbabilityTheory.integrable_exp_mul_gaussianReal` (the 1D Gaussian
MGF is finite at every real argument). `Integrable.fintype_prod` then
gives integrability of the product against `Measure.pi`. Multiplying
by the constant `exp(-‖h‖²/2)` preserves integrability
(`Integrable.const_mul`). Finally, multiplying by the bounded
`f` preserves integrability (`Integrable.mul_bdd`). -/
theorem gaussianShift_integrable
    {ι : Type*} [Fintype ι] (h : ι → ℝ)
    {f : (ι → ℝ) → ℝ}
    (hf_meas : AEStronglyMeasurable f
      (Measure.pi (fun _ : ι => gaussianReal 0 1)))
    {B : ℝ} (hf_bdd : ∀ x, ‖f x‖ ≤ B) :
    Integrable
      (fun X : ι → ℝ =>
        Real.exp ((∑ i, h i * X i) - (∑ i, (h i) ^ 2) / 2) * f X)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  -- Step 1: the exponential factor is integrable against the centred
  -- product Gaussian. `exp(∑ h_i X_i − C) = exp(-C) · ∏ exp(h_i X_i)`.
  -- Each `exp(h_i · X_i)` is integrable against `gaussianReal 0 1`
  -- (Gaussian MGF), and `Integrable.fintype_prod` lifts the product to
  -- the product measure.
  have h_each_int : ∀ i : ι,
      Integrable (fun x : ℝ => Real.exp (h i * x))
        (gaussianReal 0 1) :=
    fun i => ProbabilityTheory.integrable_exp_mul_gaussianReal (h i)
  have h_prod : Integrable
      (fun X : ι → ℝ => ∏ i, Real.exp (h i * X i))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    MeasureTheory.Integrable.fintype_prod
      (μ := fun _ : ι => gaussianReal 0 1) h_each_int
  -- Pull out the constant `exp(-C)` factor: `exp(S − C) = exp(-C) · ∏ exp(_)`.
  have h_exp_eq : (fun X : ι → ℝ =>
      Real.exp ((∑ i, h i * X i) - (∑ i, (h i) ^ 2) / 2))
      = fun X => Real.exp (-((∑ i, (h i) ^ 2) / 2))
          * ∏ i, Real.exp (h i * X i) := by
    funext X
    rw [show (∑ i, h i * X i) - (∑ i, (h i) ^ 2) / 2
        = -((∑ i, (h i) ^ 2) / 2) + ∑ i, h i * X i from by ring,
      Real.exp_add, ← Real.exp_sum]
  have h_exp_int : Integrable
      (fun X : ι → ℝ =>
        Real.exp ((∑ i, h i * X i) - (∑ i, (h i) ^ 2) / 2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    rw [h_exp_eq]
    exact h_prod.const_mul _
  -- Step 2: bounded × integrable is integrable (`Integrable.mul_bdd`).
  exact h_exp_int.mul_bdd hf_meas
    (Filter.Eventually.of_forall hf_bdd)

end ProbabilityTheory
