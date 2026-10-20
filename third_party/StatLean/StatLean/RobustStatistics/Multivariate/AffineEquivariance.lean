module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Affine equivariance of multivariate location and scatter functionals

The interface layer for multivariate robust statistics (`MMY §6.17.1`, "Why affine
equivariance?"): a multivariate location functional should follow affine maps,
`T((Ax+b)_\#P) = A\,T(P) + b`, and a scatter functional should transform as
`S((Ax+b)_\#P) = A\,S(P)\,A^\top`. The mean vector and the covariance matrix are the
sanity-check instances; the high-breakdown multivariate estimators of `MMY §6` are
deferred to a later round.

Vectors are coordinate functions `Fin d → ℝ` and affine maps act through `Matrix.mulVec`,
avoiding inner-product-space packaging.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §6.2, §6.17.1.

**Bibliographic comments.** Affine-equivariant multivariate location and scatter estimation
begins with R. A. Maronna, "Robust M-estimators of multivariate location and scatter,"
*Ann. Statist.* **4** (1976), 51–67; see also ch. 8 of Huber, *Robust Statistics*, Wiley,
1981, and P. L. Davies, "Asymptotic behaviour of S-estimates of multivariate location
parameters and dispersion matrices," *Ann. Statist.* **15** (1987), 1269–1292.
-/

open MeasureTheory

namespace StatLean.RobustStatistics

variable {d : ℕ}

/-- **Affine equivariance of a multivariate location functional** on a domain class
(`MMY §6.17.1`): `T((Ax+b)_#P) = A T(P) + b` for every invertible `A`. -/
def IsAffineEquivariantLocation (T : Measure (Fin d → ℝ) → (Fin d → ℝ))
    (𝒟 : Set (Measure (Fin d → ℝ))) : Prop :=
  ∀ P ∈ 𝒟, ∀ A : Matrix (Fin d) (Fin d) ℝ, IsUnit A.det → ∀ b : Fin d → ℝ,
    T (P.map fun x => A.mulVec x + b) = A.mulVec (T P) + b

/-- **Affine equivariance of a scatter functional** on a domain class (`MMY §6.17.1`):
`S((Ax+b)_#P) = A S(P) Aᵀ`. -/
def IsAffineEquivariantScatter (S : Measure (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (𝒟 : Set (Measure (Fin d → ℝ))) : Prop :=
  ∀ P ∈ 𝒟, ∀ A : Matrix (Fin d) (Fin d) ℝ, IsUnit A.det → ∀ b : Fin d → ℝ,
    S (P.map fun x => A.mulVec x + b) = A * S P * A.transpose

/-- The **mean vector functional**, coordinatewise (`MMY §6.1` context). Junk value `0`
in non-integrable coordinates. -/
noncomputable def meanVecFunctional (P : Measure (Fin d → ℝ)) : Fin d → ℝ :=
  fun i => ∫ x, x i ∂P

/-- The **covariance matrix functional** (`MMY §6.1` context). -/
noncomputable def covMatrixFunctional (P : Measure (Fin d → ℝ)) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j =>
    ∫ x, (x i - meanVecFunctional P i) * (x j - meanVecFunctional P j) ∂P

/-- Coordinates of an affine image: `(Ax + b)ᵢ = ∑ⱼ Aᵢⱼ xⱼ + bᵢ`. -/
private theorem mulVec_add_apply (A : Matrix (Fin d) (Fin d) ℝ) (b x : Fin d → ℝ)
    (i : Fin d) : (A.mulVec x + b) i = (∑ j, A i j * x j) + b i := by
  simp [Matrix.mulVec, dotProduct]

/-- An affine map of `Fin d → ℝ` is continuous, hence a.e.-measurable; this is what makes
the pushforward integrals computable by `integral_map`. -/
private theorem continuous_affine (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    Continuous fun x : Fin d → ℝ => A.mulVec x + b := by
  refine Continuous.add (continuous_pi fun i => ?_) continuous_const
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j)

/-- Centred coordinates transform linearly under an affine map: the translation `b`
cancels and `(Ax + b)ᵢ - (Am + b)ᵢ = ∑ₖ Aᵢₖ (xₖ - mₖ)`. -/
private theorem centered_coord (A : Matrix (Fin d) (Fin d) ℝ) (b m x : Fin d → ℝ)
    (i : Fin d) :
    (A.mulVec x + b) i - (A.mulVec m + b) i = ∑ k, A i k * (x k - m k) := by
  have h1 : (A.mulVec x + b) i - (A.mulVec m + b) i
      = (∑ k, A i k * x k) - ∑ k, A i k * m k := by
    rw [mulVec_add_apply, mulVec_add_apply]; ring
  rw [h1, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => (mul_sub _ _ _).symm

/-- **The mean vector is affine equivariant** (`MMY §6.17.1`, sanity check) on
probability measures with integrable coordinates. -/
theorem meanVecFunctional_affineEquivariant :
    IsAffineEquivariantLocation (meanVecFunctional (d := d))
      {P | IsProbabilityMeasure P ∧ ∀ i, Integrable (fun x => x i) P} := by
  rintro P ⟨hP, hint⟩ A _ b
  haveI : IsProbabilityMeasure P := hP
  funext i
  have hmap : meanVecFunctional (P.map fun x => A.mulVec x + b) i
      = ∫ x, (A.mulVec x + b) i ∂P :=
    integral_map (continuous_affine A b).aemeasurable
      (measurable_pi_apply i).aestronglyMeasurable
  have hint2 : Integrable (fun x : Fin d → ℝ => ∑ j, A i j * x j) P :=
    integrable_finset_sum _ fun j _ => (hint j).const_mul _
  rw [hmap]
  calc ∫ x, (A.mulVec x + b) i ∂P
      = ∫ x, ((∑ j, A i j * x j) + b i) ∂P := by simp only [mulVec_add_apply]
    _ = (∫ x, ∑ j, A i j * x j ∂P) + ∫ _x, b i ∂P :=
        integral_add hint2 (integrable_const _)
    _ = (∑ j, A i j * ∫ x, x j ∂P) + b i := by
        rw [integral_finset_sum _ fun j _ => (hint j).const_mul _]
        simp only [integral_const_mul]
        simp
    _ = (A.mulVec (meanVecFunctional P) + b) i := by rw [mulVec_add_apply]; rfl

/-- The `(i, j)` entry of the covariance of an affine image, pushed back to `P`: expand
the product of the two centred coordinate sums and integrate term by term. Integrability
of each product `(xₖ - mₖ)(x_l - m_l)` is Cauchy–Schwarz (`MemLp.integrable_mul`). -/
private theorem cov_map_entry {P : Measure (Fin d → ℝ)} [IsProbabilityMeasure P]
    (h2 : ∀ i, MemLp (fun x : Fin d → ℝ => x i) 2 P)
    (A : Matrix (Fin d) (Fin d) ℝ) (b m : Fin d → ℝ) (i j : Fin d) :
    (∫ x, ((A.mulVec x + b) i - (A.mulVec m + b) i) *
        ((A.mulVec x + b) j - (A.mulVec m + b) j) ∂P)
      = ∑ k, ∑ l, A i k * A j l * ∫ x, (x k - m k) * (x l - m l) ∂P := by
  have hIkl : ∀ k l : Fin d,
      Integrable (fun x : Fin d → ℝ => (x k - m k) * (x l - m l)) P := by
    intro k l
    have hk : MemLp (fun x : Fin d → ℝ => x k - m k) 2 P := (h2 k).sub (memLp_const _)
    have hl : MemLp (fun x : Fin d → ℝ => x l - m l) 2 P := (h2 l).sub (memLp_const _)
    exact hk.integrable_mul hl
  have hexp : ∀ x : Fin d → ℝ,
      ((A.mulVec x + b) i - (A.mulVec m + b) i) * ((A.mulVec x + b) j - (A.mulVec m + b) j)
        = ∑ k, ∑ l, A i k * A j l * ((x k - m k) * (x l - m l)) := by
    intro x
    rw [centered_coord A b m x i, centered_coord A b m x j, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [hexp]
  rw [integral_finset_sum _ fun k _ =>
    integrable_finset_sum _ fun l _ => (hIkl k l).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finset_sum _ fun l _ => (hIkl k l).const_mul _]
  simp only [integral_const_mul]

/-- **The covariance matrix is affine equivariant scatter** (`MMY §6.17.1`, sanity
check) on probability measures with square-integrable coordinates. -/
theorem covMatrixFunctional_affineEquivariant :
    IsAffineEquivariantScatter (covMatrixFunctional (d := d))
      {P | IsProbabilityMeasure P ∧ ∀ i, MemLp (fun x => x i) 2 P} := by
  rintro P ⟨hP, h2⟩ A hA b
  haveI : IsProbabilityMeasure P := hP
  have hint : ∀ i, Integrable (fun x : Fin d → ℝ => x i) P :=
    fun i => (h2 i).integrable (by norm_num)
  -- the centring of the image is the image of the centring, by the location result
  have hmean : meanVecFunctional (P.map fun x => A.mulVec x + b)
      = A.mulVec (meanVecFunctional P) + b :=
    meanVecFunctional_affineEquivariant P ⟨hP, hint⟩ A hA b
  ext i j
  simp only [covMatrixFunctional, Matrix.of_apply, hmean]
  have hmeas : AEStronglyMeasurable
      (fun y : Fin d → ℝ => (y i - (A.mulVec (meanVecFunctional P) + b) i) *
        (y j - (A.mulVec (meanVecFunctional P) + b) j))
      (P.map fun x => A.mulVec x + b) :=
    (((measurable_pi_apply i).sub measurable_const).mul
      ((measurable_pi_apply j).sub measurable_const)).aestronglyMeasurable
  rw [integral_map (continuous_affine A b).aemeasurable hmeas,
    cov_map_entry h2 A b (meanVecFunctional P) i j]
  -- `(A S Aᵀ) i j = ∑ₖ ∑_l Aᵢₖ A_{j l} S_{k l}`
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    simp only [Matrix.of_apply]; ring

end StatLean.RobustStatistics
