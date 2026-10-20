module
public import StatLean.StatisticalModels.Gaussian.Affine

@[expose] public section

/-!
# The Fin corridor — reindexing multivariate Gaussians

The quarantine file for index bookkeeping: everything in the Gaussian slice lives on
abstract sum indices `ι₁ ⊕ ι₂`; users with `Fin (d₁ + d₂)` data cross to sum-index land
through **one** reindexing transport and stay there. `Fin`-arithmetic never appears
elsewhere in the slice.

* `multivariateGaussian_map_reindex` — the law of a reindexed Gaussian vector is the
  Gaussian with reindexed mean and submatrix-permuted covariance (for any index
  equivalence `e : ι ≃ ι'`, via the isometric coordinate permutation `piLpCongrLeft`);
  instantiating `e := finSumFinEquiv : Fin d₁ ⊕ Fin d₂ ≃ Fin (d₁ + d₂)` is the corridor.

**Reference.** LEAN-ONLY plumbing (coordinate permutation of a normal vector is a special
affine image, `And58 §2.4`).

**Proof formalization notes.** By charFun: a coordinate permutation is a linear isometry,
so `⟪t, e·x⟫ = ⟪e⁻¹·t, x⟫` and both sides' characteristic functions match with the
submatrix covariance (`Matrix.submatrix` algebra). Alternatively an instance of
`multivariateGaussian_map_affine` at the permutation matrix — whichever lands first.

**Bibliographic comments.** None (plumbing).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels

/-- **Reindex transport**: for an index equivalence `e : ι ≃ ι'`, the image of `N(m, S)`
under the coordinate permutation `piLpCongrLeft e` is the Gaussian with permuted mean and
covariance `S.submatrix e.symm e.symm`. Instantiate `e := finSumFinEquiv` to cross between
`Fin (d₁ + d₂)` and `Fin d₁ ⊕ Fin d₂` (the corridor). -/
theorem multivariateGaussian_map_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι') (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ)
    -- USER-INPUT: genuine covariance parameter; And58 §2.4
    (hS : S.PosSemidef) :
    (multivariateGaussian m S).map (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)
      = multivariateGaussian ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) m)
          (S.submatrix e.symm e.symm) := by
  have hf : Measurable ⇑(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).continuous.measurable
  haveI : IsProbabilityMeasure ((multivariateGaussian m S).map
      ⇑(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hL : charFun ((multivariateGaussian m S).map
      ⇑(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)) t
      = charFun (multivariateGaussian m S)
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm t) := by
    rw [charFun_apply, charFun_apply,
      integral_map hf.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp_rw [LinearIsometryEquiv.inner_map_eq_flip]
  rw [hL, charFun_multivariateGaussian hS,
    charFun_multivariateGaussian (hS.submatrix ⇑e.symm)]
  have hofLp : ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm t).ofLp
      = t.ofLp ∘ ⇑e := by
    ext i
    simp [LinearIsometryEquiv.piLpCongrLeft_symm, Equiv.piCongrLeft']
  have hquad : (t.ofLp ∘ ⇑e) ⬝ᵥ S *ᵥ (t.ofLp ∘ ⇑e)
      = t.ofLp ⬝ᵥ S.submatrix ⇑e.symm ⇑e.symm *ᵥ t.ofLp := by
    rw [submatrix_mulVec_equiv, Equiv.symm_symm, dotProduct_comp_equiv_symm]
  congr 1
  rw [LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm, hofLp, hquad]

end StatLean.StatisticalModels
