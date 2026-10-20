module
public import StatLean.StatisticalModels.Gaussian.Marginal
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Disintegration.Unique

@[expose] public section

/-!
# Gaussian conditioning — the block conditional law

**The slice headline (G3.4).** For a joint Gaussian on the sum index `ι₁ ⊕ ι₂` with mean
blocks `(m₁, m₂)` and covariance `fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂` (one off-diagonal block
carried; its transpose is definitional), the conditional law of the second block given the
first is the Gaussian kernel
$$x \mapsto N\big(m₂ + S₂₁ S₁₁^{-1}(x - m₁),\; S₂₂ - S₂₁ S₁₁^{-1} S₁₂\big),$$
in the exact disintegration sense: `first marginal ⊗ₘ kernel = joint`. Mathlib has no
Gaussian conditioning in any form — this is the load-bearing substrate for BLUP/mixed
models (M-B2) and any finite-dimensional Gaussian regression.

* `condMeanMatrix` / `condCovMatrix` — the regression matrix `S₂₁ S₁₁⁻¹` and the Schur
  complement;
* `gaussianCondKernel` — the conditional kernel (constructed compositionally; its
  `@[simp]` spec is the contract), unconditionally Markov (the degenerate-parameter
  fallback of `multivariateGaussian` is a Dirac — still a probability);
* `posSemidef_condCovMatrix` (G3.1) — the Schur complement is a genuine covariance;
* `dotProduct_fromBlocks_split` (G3.2) — completing the square in the quadratic form, the
  charFun engine;
* **`compProd_gaussianCondKernel` (G3.4)** — the headline disintegration identity;
* `condKernel_ae_eq_gaussianCondKernel` (G3.5) — the abstract disintegration kernel of the
  joint agrees a.e. with the explicit Gaussian kernel (uniqueness of disintegration).

PSD-degenerate `S₁₁` (pseudoinverse form) is a named future debt (D-G1); the conditional-
expectation corollary is deferred with it.

**Reference.** T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*,
Wiley, 1958, Thm 2.5.1 (the conditional normal law) (verify §) (`And58 Thm 2.5.1`);
M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, Wiley, 1983, Prop. 3.13
(verify §).

**Proof formalization notes.** charFun-only, on the sum space (the area doctrine): the
charFun of the compProd is computed by `MeasureTheory.integral_compProd` (bounded
integrand), the inner Gaussian charFun contributes the affine-mean phase, the outer
integral is the `S₁₁`-charFun at the shifted argument `t₁ + S₁₁⁻¹S₁₂ t₂`, and G3.2/the
mean split reassemble the joint block charFun; conclude by `Measure.ext_of_charFun`
transported through `ext_of_map_sumMeasEquivProd`. `S₁₁.PosDef` is USER-INPUT (the
classical nondegeneracy of the conditioning block); the joint PSD is USER-INPUT.

**Bibliographic comments.** The conditional normal distribution is 19th-century
(Galton–Pearson regression); the matrix form with the Schur complement is standard since
Anderson (1958). The disintegration (`compProd`) formulation is the modern
regular-conditional-probability reading.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- The Gaussian regression matrix `S₂₁ S₁₁⁻¹` (And58 Thm 2.5.1). -/
noncomputable def condMeanMatrix (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) :
    Matrix ι₂ ι₁ ℝ :=
  S₁₂ᵀ * S₁₁⁻¹

/-- The **Schur complement** `S₂₂ − S₂₁ S₁₁⁻¹ S₁₂` — the conditional covariance
(And58 Thm 2.5.1). -/
noncomputable def condCovMatrix (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ)
    (S₂₂ : Matrix ι₂ ι₂ ℝ) : Matrix ι₂ ι₂ ℝ :=
  S₂₂ - S₁₂ᵀ * S₁₁⁻¹ * S₁₂

omit [DecidableEq ι₂] in
/-- LEAN-ONLY: a matrix acts measurably on Euclidean space (linear on a
finite-dimensional space, hence continuous). -/
theorem measurable_toEuclideanLin (A : Matrix ι₂ ι₁ ℝ) :
    Measurable fun x : EuclideanSpace ℝ ι₁ => Matrix.toEuclideanLin (𝕜 := ℝ) A x :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) A).continuous_of_finiteDimensional).measurable

omit [Fintype ι₁] [DecidableEq ι₁] in
/-- LEAN-ONLY: translation of `multivariateGaussian` with **no** PSD side condition — the
degenerate-parameter fallback is a Dirac mass, which translates as well. -/
private theorem multivariateGaussian_map_add_left (m : EuclideanSpace ℝ ι₂)
    (S : Matrix ι₂ ι₂ ℝ) (c : EuclideanSpace ℝ ι₂) :
    (multivariateGaussian m S).map (fun x => c + x) = multivariateGaussian (c + m) S := by
  by_cases hS : S.PosSemidef
  · exact multivariateGaussian_map_const_add m S hS c
  · rw [multivariateGaussian_of_not_posSemidef _ hS,
      multivariateGaussian_of_not_posSemidef _ hS]
    exact Measure.map_dirac' (measurable_const_add c) m

/-- The **Gaussian conditional kernel**
`x ↦ N(m₂ + S₂₁S₁₁⁻¹(x − m₁), S₂₂ − S₂₁S₁₁⁻¹S₁₂)` (And58 Thm 2.5.1). Constructed
compositionally (the `@[simp]` spec below is the frozen contract). -/
noncomputable def gaussianCondKernel (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ) :
    Kernel (EuclideanSpace ℝ ι₁) (EuclideanSpace ℝ ι₂) :=
  affineNoiseKernel (multivariateGaussian 0 (condCovMatrix S₁₁ S₁₂ S₂₂))
    (fun x => Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) x)
    (measurable_toEuclideanLin _)
    (m₂ - Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁)

@[simp]
theorem gaussianCondKernel_apply (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    (x : EuclideanSpace ℝ ι₁) :
    gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ x
      = multivariateGaussian
          (m₂ + Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) (x - m₁))
          (condCovMatrix S₁₁ S₁₂ S₂₂) := by
  rw [gaussianCondKernel, affineNoiseKernel_apply, multivariateGaussian_map_add_left]
  congr 1
  rw [add_zero, map_sub]
  abel

instance (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂) (S₁₁ : Matrix ι₁ ι₁ ℝ)
    (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ) :
    IsMarkovKernel (gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂) := by
  rw [gaussianCondKernel]; infer_instance

/-- **G3.1, the Schur complement is PSD** (Schur 1917; And58 Thm 2.5.1): under a genuine
joint covariance with nondegenerate conditioning block, the conditional covariance is a
covariance. -/
theorem posSemidef_condCovMatrix {S₁₁ : Matrix ι₁ ι₁ ℝ} {S₁₂ : Matrix ι₁ ι₂ ℝ}
    {S₂₂ : Matrix ι₂ ι₂ ℝ}
    -- USER-INPUT: genuine joint covariance; And58 Thm 2.5.1
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosSemidef)
    -- USER-INPUT: nondegenerate conditioning block; And58 Thm 2.5.1
    (h₁₁ : S₁₁.PosDef) :
    (condCovMatrix S₁₁ S₁₂ S₂₂).PosSemidef := by
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  have hconj : S₁₂ᴴ = S₁₂ᵀ := Matrix.conjTranspose_eq_transpose_of_trivial S₁₂
  have h := (Matrix.PosDef.fromBlocks₁₁ (A := S₁₁) S₁₂ S₂₂ h₁₁).mp (by rwa [hconj])
  rwa [hconj] at h

/-- **G3.2, completing the square** — the block quadratic form splits into the marginal
form at the shifted argument plus the Schur form (the charFun engine). -/
theorem dotProduct_fromBlocks_split (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ)
    (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: nondegenerate symmetric conditioning block; And58 Thm 2.5.1
    (h₁₁ : S₁₁.PosDef) (t₁ : ι₁ → ℝ) (t₂ : ι₂ → ℝ) :
    Sum.elim t₁ t₂ ⬝ᵥ (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) *ᵥ Sum.elim t₁ t₂
      = (t₁ + (S₁₁⁻¹ * S₁₂) *ᵥ t₂) ⬝ᵥ S₁₁ *ᵥ (t₁ + (S₁₁⁻¹ * S₁₂) *ᵥ t₂)
          + t₂ ⬝ᵥ (condCovMatrix S₁₁ S₁₂ S₂₂) *ᵥ t₂ := by
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  have hconj : S₁₂ᴴ = S₁₂ᵀ := Matrix.conjTranspose_eq_transpose_of_trivial S₁₂
  have h := Matrix.schur_complement_eq₁₁ (A := S₁₁) S₁₂ S₂₂ t₁ t₂ h₁₁.isHermitian
  rw [hconj] at h
  simp only [star_trivial] at h
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    condCovMatrix]
  exact h

/-- LEAN-ONLY -/
private theorem euclideanInner_eq_dotProduct {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℝ ι) : ⟪x, y⟫_ℝ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y :=
  dotProduct_comm _ _

/-- LEAN-ONLY -/
private theorem inner_toEuclideanLin_left (A : Matrix ι₂ ι₁ ℝ) (x : EuclideanSpace ℝ ι₁)
    (t : EuclideanSpace ℝ ι₂) :
    ⟪Matrix.toEuclideanLin (𝕜 := ℝ) A x, t⟫_ℝ
      = ⟪x, Matrix.toEuclideanLin (𝕜 := ℝ) Aᵀ t⟫_ℝ := by
  rw [euclideanInner_eq_dotProduct, euclideanInner_eq_dotProduct]
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  exact dotProduct_comm _ _

omit [Fintype ι₂] [DecidableEq ι₂] in
/-- LEAN-ONLY: transpose of the regression matrix. -/
private theorem transpose_condMeanMatrix {S₁₁ : Matrix ι₁ ι₁ ℝ} (S₁₂ : Matrix ι₁ ι₂ ℝ)
    (h₁₁ : S₁₁.PosDef) : (condMeanMatrix S₁₁ S₁₂)ᵀ = S₁₁⁻¹ * S₁₂ := by
  have hsymm : S₁₁ᵀ = S₁₁ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact h₁₁.isHermitian
  rw [condMeanMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, hsymm]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
/-- LEAN-ONLY: the coordinate vector of a sum-index point is the `Sum.elim` of its
blocks. -/
private theorem elim_ofLp (t : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) :
    Sum.elim (WithLp.ofLp (blockFst t)) (WithLp.ofLp (blockSnd t)) = WithLp.ofLp t := by
  funext k; cases k <;> rfl

/-- **G3.4, HEADLINE — Gaussian conditioning as exact disintegration** (And58 Thm 2.5.1;
Eaton Prop. 3.13): the first block marginal composed with the Gaussian conditional kernel
is the joint block Gaussian. Mathlib has no Gaussian conditioning; this is the substrate
theorem for BLUP and Gaussian regression. -/
theorem compProd_gaussianCondKernel (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: genuine joint covariance; And58 Thm 2.5.1
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosSemidef)
    -- USER-INPUT: nondegenerate conditioning block; And58 Thm 2.5.1
    (h₁₁ : S₁₁.PosDef) :
    multivariateGaussian m₁ S₁₁ ⊗ₘ gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂
      = (multivariateGaussian (blockPair m₁ m₂)
          (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
            (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)) := by
  have hSc : (condCovMatrix S₁₁ S₁₂ S₂₂).PosSemidef := posSemidef_condCovMatrix hJ h₁₁
  have hS : S₁₁.PosSemidef := h₁₁.posSemidef
  have hmeas : Measurable ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm :=
    (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm.measurable
  have key : (multivariateGaussian m₁ S₁₁ ⊗ₘ gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂).map
        ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm
      = multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) := by
    haveI : IsProbabilityMeasure
        ((multivariateGaussian m₁ S₁₁ ⊗ₘ gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂).map
          ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm) :=
      Measure.isProbabilityMeasure_map hmeas.aemeasurable
    refine Measure.ext_of_charFun (funext fun t => ?_)
    have hcont : Continuous fun x : EuclideanSpace ℝ (ι₁ ⊕ ι₂) =>
        Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I) := by fun_prop
    have hint : Integrable (fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ =>
        Complex.exp ((⟪(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm p, t⟫_ℝ : ℂ) * Complex.I))
        (multivariateGaussian m₁ S₁₁ ⊗ₘ gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂) :=
      Integrable.mono' (integrable_const 1)
        (hcont.measurable.comp hmeas).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => by simp [Complex.norm_exp_ofReal_mul_I])
    rw [charFun_apply, integral_map hmeas.aemeasurable hcont.aestronglyMeasurable,
      Measure.integral_compProd hint]
    have hinner : ∀ a : EuclideanSpace ℝ ι₁,
        ∫ b, Complex.exp ((⟪(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm (a, b), t⟫_ℝ : ℂ)
              * Complex.I) ∂(gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ a)
          = Complex.exp (((⟪blockSnd t, m₂⟫_ℝ
                  - ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁⟫_ℝ
                  : ℝ) : ℂ) * Complex.I
                - ((WithLp.ofLp (blockSnd t) ⬝ᵥ (condCovMatrix S₁₁ S₁₂ S₂₂)
                      *ᵥ WithLp.ofLp (blockSnd t) : ℝ) : ℂ) / 2)
            * Complex.exp ((⟪a, blockFst t
                  + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ : ℂ)
                * Complex.I) := by
      intro a
      have hsplit : ∀ b : EuclideanSpace ℝ ι₂,
          Complex.exp ((⟪(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm (a, b), t⟫_ℝ : ℂ)
              * Complex.I)
            = Complex.exp ((⟪a, blockFst t⟫_ℝ : ℂ) * Complex.I)
              * Complex.exp ((⟪b, blockSnd t⟫_ℝ : ℂ) * Complex.I) := by
        intro b
        rw [← Complex.exp_add]
        congr 1
        simp only [sumMeasEquivProd_symm_apply, inner_sum_split (blockPair a b) t,
          blockFst_blockPair, blockSnd_blockPair]
        push_cast
        ring
      simp_rw [hsplit]
      have hcm : ∫ b, Complex.exp ((⟪a, blockFst t⟫_ℝ : ℂ) * Complex.I)
            * Complex.exp ((⟪b, blockSnd t⟫_ℝ : ℂ) * Complex.I)
            ∂(gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ a)
          = Complex.exp ((⟪a, blockFst t⟫_ℝ : ℂ) * Complex.I)
            * ∫ b, Complex.exp ((⟪b, blockSnd t⟫_ℝ : ℂ) * Complex.I)
                ∂(gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ a) :=
        integral_const_mul _ _
      rw [hcm,
        show (∫ b, Complex.exp ((⟪b, blockSnd t⟫_ℝ : ℂ) * Complex.I)
              ∂(gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ a))
            = charFun (gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ a) (blockSnd t) from
          (charFun_apply _).symm,
        gaussianCondKernel_apply, charFun_multivariateGaussian hSc,
        ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      have hA : ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) a⟫_ℝ
          = ⟪a, Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ := by
        rw [real_inner_comm, inner_toEuclideanLin_left, transpose_condMeanMatrix S₁₂ h₁₁]
      have hlin : ⟪blockSnd t,
            m₂ + Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) (a - m₁)⟫_ℝ
          = ⟪blockSnd t, m₂⟫_ℝ
            - ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁⟫_ℝ
            + ⟪a, Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ := by
        rw [map_sub, inner_add_right, inner_sub_right, hA]
        ring
      rw [hlin, inner_add_right]
      push_cast
      ring
    simp_rw [hinner]
    have hcm' : ∫ a, Complex.exp (((⟪blockSnd t, m₂⟫_ℝ
              - ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁⟫_ℝ
              : ℝ) : ℂ) * Complex.I
            - ((WithLp.ofLp (blockSnd t) ⬝ᵥ (condCovMatrix S₁₁ S₁₂ S₂₂)
                  *ᵥ WithLp.ofLp (blockSnd t) : ℝ) : ℂ) / 2)
          * Complex.exp ((⟪a, blockFst t
                + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ : ℂ) * Complex.I)
          ∂(multivariateGaussian m₁ S₁₁)
        = Complex.exp (((⟪blockSnd t, m₂⟫_ℝ
              - ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁⟫_ℝ
              : ℝ) : ℂ) * Complex.I
            - ((WithLp.ofLp (blockSnd t) ⬝ᵥ (condCovMatrix S₁₁ S₁₂ S₂₂)
                  *ᵥ WithLp.ofLp (blockSnd t) : ℝ) : ℂ) / 2)
          * ∫ a, Complex.exp ((⟪a, blockFst t
                + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ : ℂ) * Complex.I)
              ∂(multivariateGaussian m₁ S₁₁) :=
      integral_const_mul _ _
    rw [hcm',
      show (∫ a, Complex.exp ((⟪a, blockFst t
              + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ : ℂ) * Complex.I)
            ∂(multivariateGaussian m₁ S₁₁))
          = charFun (multivariateGaussian m₁ S₁₁)
              (blockFst t + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)) from
        (charFun_apply _).symm,
      charFun_multivariateGaussian hS, charFun_multivariateGaussian hJ, ← Complex.exp_add]
    congr 1
    have hAm : ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁⟫_ℝ
        = ⟪Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t), m₁⟫_ℝ := by
      rw [real_inner_comm, inner_toEuclideanLin_left, transpose_condMeanMatrix S₁₂ h₁₁,
        real_inner_comm]
    have htm : ⟪t, blockPair m₁ m₂⟫_ℝ = ⟪blockFst t, m₁⟫_ℝ + ⟪blockSnd t, m₂⟫_ℝ := by
      simp [inner_sum_split t (blockPair m₁ m₂)]
    have hofLp : WithLp.ofLp (blockFst t
          + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t))
        = WithLp.ofLp (blockFst t) + (S₁₁⁻¹ * S₁₂) *ᵥ WithLp.ofLp (blockSnd t) := by
      simp [Matrix.toLpLin_apply]
    have hquad : WithLp.ofLp t ⬝ᵥ (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) *ᵥ WithLp.ofLp t
        = WithLp.ofLp (blockFst t
              + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t))
            ⬝ᵥ S₁₁ *ᵥ WithLp.ofLp (blockFst t
              + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t))
          + WithLp.ofLp (blockSnd t) ⬝ᵥ (condCovMatrix S₁₁ S₁₂ S₂₂)
              *ᵥ WithLp.ofLp (blockSnd t) := by
      rw [hofLp, ← elim_ofLp t]
      exact dotProduct_fromBlocks_split S₁₁ S₁₂ S₂₂ h₁₁ _ _
    rw [htm, hquad, inner_add_left, hAm]
    push_cast
    ring
  rw [← key, Measure.map_map (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).measurable hmeas,
    show (⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
        ∘ ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm) = id from
      funext fun p => (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).apply_symm_apply p,
    Measure.map_id]

/-- **G3.5, uniqueness corollary**: the abstract disintegration kernel of the joint law
agrees a.e. with the explicit Gaussian conditional kernel. -/
theorem condKernel_ae_eq_gaussianCondKernel (m₁ : EuclideanSpace ℝ ι₁)
    (m₂ : EuclideanSpace ℝ ι₂) (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ)
    (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: genuine joint covariance; And58 Thm 2.5.1
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosSemidef)
    -- USER-INPUT: nondegenerate conditioning block; And58 Thm 2.5.1
    (h₁₁ : S₁₁.PosDef) :
    ∀ᵐ x ∂(multivariateGaussian m₁ S₁₁),
      ((multivariateGaussian (blockPair m₁ m₂)
          (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
            (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))).condKernel x
        = gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ x := by
  haveI : IsProbabilityMeasure ((multivariateGaussian (blockPair m₁ m₂)
      (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
        ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))) :=
    Measure.isProbabilityMeasure_map
      (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).measurable.aemeasurable
  have hG34 := compProd_gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ hJ h₁₁
  have hfst : ((multivariateGaussian (blockPair m₁ m₂)
        (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
          ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))).fst = multivariateGaussian m₁ S₁₁ := by
    rw [← hG34, Measure.fst_compProd]
  have hcp : (multivariateGaussian (blockPair m₁ m₂)
        (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
          ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
      = ((multivariateGaussian (blockPair m₁ m₂)
          (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
            ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))).fst
          ⊗ₘ gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ := by
    rw [hfst, ← hG34]
  have h := eq_condKernel_of_measure_eq_compProd _ hcp
  rw [hfst] at h
  filter_upwards [h] with x hx using hx.symm

end StatLean.StatisticalModels
