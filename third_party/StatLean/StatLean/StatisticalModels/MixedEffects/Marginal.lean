module
public import StatLean.StatisticalModels.MixedEffects.Defs
public import StatLean.StatisticalModels.ForMathlib.CovarianceMatrix
public import StatLean.StatisticalModels.Gaussian.Affine

@[expose] public section

/-!
# Marginal moments and the Gaussian marginal of the linear mixed model

The two marginal theorems of the LMM:

* **M1 (no Gaussianity)** — under mean-zero, second-moment latent effects and noise:
  `E Y = Xβ` and `Cov Y = Z·Cov(b)·Zᵀ + Cov(ε)` — pure covariance calculus, valid for
  arbitrary latent laws;
* **M2 (Gaussian case)** — with `b ∼ N(0, Gm)` and `ε ∼ N(0, Rm)`:
  `Y ∼ N(Xβ, Z Gm Zᵀ + Rm)` (`LW82` Eq. (1.2)) — the affine-image and convolution calculus
  of the Gaussian slice.

**Reference.** `LW82` Eq. (1.2); `FLW Ch. 8` (verify §); `MSN Ch. 6` (verify §).

**Proof formalization notes.** M1 instantiates the G-B1 covariance calculus
(`covMatrix_map_add_prod` at `A = Z`, `B = 1`, plus the constant shift `Xβ` through
`covMatrix_map_affine`/`meanVec_map_affine`). M2 rewrites `lmmLaw` as an affine image of the
product Gaussian, then convolves the two independent Gaussian summands. *Book vs Lean:* M1's moment-only
hypotheses have no Gaussianity — stronger than the books' statements.

**Bibliographic comments.** The marginal covariance `Z G Zᵀ + R` is the variance-components
decomposition of Henderson (1950) and Laird–Ware (1982).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.MixedEffects

open StatLean.StatisticalModels

variable {n p q : ℕ} (D : LMMDesign n p q) (β : EuclideanSpace ℝ (Fin p))

/-! ### LEAN-ONLY plumbing

The matrix action as a continuous linear map, measurability of the LMM observation map, and
the split of `lmmLaw` into a constant-free "inner" layer followed by the translation by `Xβ`.
-/

/-- LEAN-ONLY: the matrix action on Euclidean space as a continuous linear map. -/
private noncomputable def matCLM {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    EuclideanSpace ℝ (Fin b) →L[ℝ] EuclideanSpace ℝ (Fin a) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (𝕜 := ℝ) A)

/-- LEAN-ONLY: the matrix action is measurable. -/
private theorem measurable_matAct {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    Measurable fun x : EuclideanSpace ℝ (Fin b) => Matrix.toEuclideanLin (𝕜 := ℝ) A x :=
  (matCLM A).continuous.measurable

/-- LEAN-ONLY: the matrix action is a.e.-strongly measurable. -/
private theorem aesm_matAct {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    {μ : Measure (EuclideanSpace ℝ (Fin b))} :
    AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin b) => Matrix.toEuclideanLin (𝕜 := ℝ) A x) μ :=
  (matCLM A).continuous.aestronglyMeasurable

/-- LEAN-ONLY: coordinate evaluation is a.e.-strongly measurable for any law. -/
private theorem aesm_proj {ι : Type*} [Fintype ι]
    {ν : Measure (EuclideanSpace ℝ ι)} (i : ι) :
    AEStronglyMeasurable (fun y : EuclideanSpace ℝ ι => y i) ν :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.aestronglyMeasurable

/-- LEAN-ONLY: the identity is a.e.-strongly measurable for any law. -/
private theorem aesm_self {ι : Type*} [Fintype ι] {ν : Measure (EuclideanSpace ℝ ι)} :
    AEStronglyMeasurable (fun y : EuclideanSpace ℝ ι => y) ν :=
  continuous_id.aestronglyMeasurable

/-- LEAN-ONLY: the identity matrix acts as the identity. -/
private theorem toEuclideanLin_one_apply {a : ℕ} (x : EuclideanSpace ℝ (Fin a)) :
    Matrix.toEuclideanLin (𝕜 := ℝ) (1 : Matrix (Fin a) (Fin a) ℝ) x = x := by
  simp

/-- LEAN-ONLY: the LMM observation map `(b, ε) ↦ Xβ + Z b + ε` is measurable. -/
private theorem measurable_lmmMap :
    Measurable fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) D.X β
        + Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 + be.2 :=
  (((measurable_matAct D.Z).comp measurable_fst).const_add _).add measurable_snd

/-- LEAN-ONLY: the constant-free layer `(b, ε) ↦ Z b + ε` is measurable. -/
private theorem measurable_innerMap :
    Measurable fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 + be.2 :=
  ((measurable_matAct D.Z).comp measurable_fst).add measurable_snd

/-- LEAN-ONLY: the law of `Z b + ε` — `lmmLaw` without the fixed-effects offset. -/
private noncomputable def lmmInner (G : Measure (EuclideanSpace ℝ (Fin q)))
    (R : Measure (EuclideanSpace ℝ (Fin n))) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (G.prod R).map fun be => Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 + be.2

/-- LEAN-ONLY: `lmmLaw` is the translation of `lmmInner` by `Xβ`. -/
private theorem lmmLaw_eq_map_lmmInner (G : Measure (EuclideanSpace ℝ (Fin q)))
    (R : Measure (EuclideanSpace ℝ (Fin n))) [SFinite G] [SFinite R] :
    lmmLaw D β G R
      = (lmmInner D G R).map fun y => Matrix.toEuclideanLin (𝕜 := ℝ) D.X β + y := by
  have h : (fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
        Matrix.toEuclideanLin (𝕜 := ℝ) D.X β
          + Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 + be.2)
      = (fun y : EuclideanSpace ℝ (Fin n) => Matrix.toEuclideanLin (𝕜 := ℝ) D.X β + y)
        ∘ fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
            Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 + be.2 := by
    funext be
    simp only [Function.comp_apply, add_assoc]
  rw [lmmInner, Measure.map_map (measurable_const_add _) (measurable_innerMap D), ← h, lmmLaw]

/-- LEAN-ONLY: an integral of a function of the first coordinate lives on the first marginal. -/
private theorem integral_comp_fst {E α γ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace α] [MeasurableSpace γ] {μ : Measure α} {ν : Measure γ}
    [SFinite μ] [IsProbabilityMeasure ν] (f : α → E) (hf : AEStronglyMeasurable f μ) :
    ∫ z : α × γ, f z.1 ∂(μ.prod ν) = ∫ x, f x ∂μ := by
  have hm : (μ.prod ν).map Prod.fst = μ := Measure.fst_prod
  have h : ∫ y, f y ∂((μ.prod ν).map Prod.fst) = ∫ z : α × γ, f z.1 ∂(μ.prod ν) :=
    integral_map measurable_fst.aemeasurable (by rw [hm]; exact hf)
  rw [hm] at h
  exact h.symm

/-- LEAN-ONLY: an integral of a function of the second coordinate lives on the second
marginal. -/
private theorem integral_comp_snd {E α γ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace α] [MeasurableSpace γ] {μ : Measure α} {ν : Measure γ}
    [IsProbabilityMeasure μ] [SFinite ν] (f : γ → E) (hf : AEStronglyMeasurable f ν) :
    ∫ z : α × γ, f z.2 ∂(μ.prod ν) = ∫ y, f y ∂ν := by
  have hm : (μ.prod ν).map Prod.snd = ν := Measure.snd_prod
  have h : ∫ y, f y ∂((μ.prod ν).map Prod.snd) = ∫ z : α × γ, f z.2 ∂(μ.prod ν) :=
    integral_map measurable_snd.aemeasurable (by rw [hm]; exact hf)
  rw [hm] at h
  exact h.symm

/-- LEAN-ONLY: the constant-free layer is the convolution of the transported latent law with
the noise law — this is where independence of `b` and `ε` is spent. -/
private theorem lmmInner_eq_conv (G : Measure (EuclideanSpace ℝ (Fin q)))
    (R : Measure (EuclideanSpace ℝ (Fin n))) [SFinite G] [SFinite R] :
    lmmInner D G R = (G.map fun x => Matrix.toEuclideanLin (𝕜 := ℝ) D.Z x) ∗ R := by
  have hmap : (G.map fun x => Matrix.toEuclideanLin (𝕜 := ℝ) D.Z x).prod R
      = (G.prod R).map (Prod.map (fun x => Matrix.toEuclideanLin (𝕜 := ℝ) D.Z x) id) := by
    have h := Measure.map_prod_map G R (measurable_matAct D.Z)
      (measurable_id (α := EuclideanSpace ℝ (Fin n)))
    rwa [Measure.map_id] at h
  have hadd : Measurable fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      z.1 + z.2 := measurable_add
  calc lmmInner D G R
      = (G.prod R).map ((fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            z.1 + z.2) ∘ Prod.map (fun x => Matrix.toEuclideanLin (𝕜 := ℝ) D.Z x) id) := rfl
    _ = ((G.prod R).map (Prod.map (fun x => Matrix.toEuclideanLin (𝕜 := ℝ) D.Z x) id)).map
          (fun z => z.1 + z.2) :=
        (Measure.map_map hadd ((measurable_matAct D.Z).prodMap measurable_id)).symm
    _ = (G.map fun x => Matrix.toEuclideanLin (𝕜 := ℝ) D.Z x) ∗ R := by
        rw [← hmap]; rfl

instance (G : Measure (EuclideanSpace ℝ (Fin q))) (R : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure G] [IsProbabilityMeasure R] :
    IsProbabilityMeasure (lmmLaw D β G R) :=
  Measure.isProbabilityMeasure_map (measurable_lmmMap D β).aemeasurable

/-- **M1a, marginal mean without Gaussianity**: centered latent effects and noise give
`E Y = Xβ` (`LW82` Eq. (1.2), moment form). -/
theorem meanVec_lmmLaw (G : Measure (EuclideanSpace ℝ (Fin q)))
    (R : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure G]
    [IsProbabilityMeasure R]
    -- USER-INPUT: centered latent effects and noise, first moments; LW82 Eq. (1.1)
    (hG : meanVec G = 0) (hR : meanVec R = 0)
    (hG1 : Integrable id G) (hR1 : Integrable id R) :
    meanVec (lmmLaw D β G R) = Matrix.toEuclideanLin (𝕜 := ℝ) D.X β := by
  have hG1' : Integrable (fun x : EuclideanSpace ℝ (Fin q) => x) G := hG1
  have hR1' : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x) R := hR1
  have hZ : Integrable (fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1) (G.prod R) :=
    ((matCLM D.Z).integrable_comp hG1').comp_fst R
  have hE : Integrable (fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
      be.2) (G.prod R) := hR1'.comp_snd G
  have hZ0 : ∫ be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n),
      Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 ∂(G.prod R) = 0 := by
    have hcomm : ∫ x, Matrix.toEuclideanLin (𝕜 := ℝ) D.Z x ∂G
        = Matrix.toEuclideanLin (𝕜 := ℝ) D.Z (∫ x, x ∂G) :=
      (matCLM D.Z).integral_comp_comm hG1'
    rw [integral_comp_fst _ (aesm_matAct D.Z), hcomm,
      show (∫ x, x ∂G) = meanVec G from rfl, hG, map_zero]
  have hE0 : ∫ be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n), be.2 ∂(G.prod R)
      = 0 := by
    have h := integral_comp_snd (μ := G) (ν := R)
      (fun y : EuclideanSpace ℝ (Fin n) => y) aesm_self
    rw [h]
    exact hR
  have hmap : ∫ y : EuclideanSpace ℝ (Fin n), y ∂(lmmLaw D β G R)
      = ∫ be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n),
          (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β
            + Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 + be.2) ∂(G.prod R) := by
    rw [lmmLaw]
    exact integral_map (measurable_lmmMap D β).aemeasurable aesm_self
  -- `Pi.add` reshapes the integrand, so the two splits go through explicit `have`s
  have hsplit1 : ∫ be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n),
        (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β
          + Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 + be.2) ∂(G.prod R)
      = (∫ be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n),
            (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β
              + Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1) ∂(G.prod R))
        + ∫ be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n), be.2 ∂(G.prod R) :=
    integral_add ((integrable_const _).add hZ) hE
  have hsplit2 : ∫ be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n),
        (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β
          + Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1) ∂(G.prod R)
      = (∫ _be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n),
            Matrix.toEuclideanLin (𝕜 := ℝ) D.X β ∂(G.prod R))
        + ∫ be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n),
            Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 ∂(G.prod R) :=
    integral_add (integrable_const _) hZ
  rw [meanVec, hmap, hsplit1, hsplit2, hZ0, hE0, integral_const]
  simp

/-- **M1b, marginal covariance without Gaussianity**: `Cov Y = Z·Cov(b)·Zᵀ + Cov(ε)` —
the variance-components decomposition, for arbitrary latent laws (`LW82` Eq. (1.2), moment
form; `Hen50`). -/
theorem covMatrix_lmmLaw (G : Measure (EuclideanSpace ℝ (Fin q)))
    (R : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure G]
    [IsProbabilityMeasure R]
    -- USER-INPUT: second moments of latent effects and noise; LW82 Eq. (1.1)
    (hG2 : MemLp id 2 G) (hR2 : MemLp id 2 R) :
    covMatrix (lmmLaw D β G R) = D.Z * covMatrix G * D.Zᵀ + covMatrix R := by
  have hG1 : Integrable (fun x : EuclideanSpace ℝ (Fin q) => x) G :=
    hG2.integrable (by norm_num)
  have hR1 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x) R :=
    hR2.integrable (by norm_num)
  have hZ : Integrable (fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1) (G.prod R) :=
    ((matCLM D.Z).integrable_comp hG1).comp_fst R
  have hE : Integrable (fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
      be.2) (G.prod R) := hR1.comp_snd G
  have hco : ∀ i : Fin n, Integrable (fun be : EuclideanSpace ℝ (Fin q) ×
      EuclideanSpace ℝ (Fin n) =>
        (Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1) i + be.2 i) (G.prod R) := fun i =>
    ((EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hZ).add
      ((EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hE)
  -- the fixed-effects offset is a constant and drops out of every covariance entry
  have hdrop : covMatrix (lmmLaw D β G R) = covMatrix (lmmInner D G R) := by
    ext i j
    rw [lmmLaw, lmmInner, covMatrix_apply, covMatrix_apply,
      covariance_map_fun (aesm_proj i) (aesm_proj j) (measurable_lmmMap D β).aemeasurable,
      covariance_map_fun (aesm_proj i) (aesm_proj j) (measurable_innerMap D).aemeasurable]
    simp only [PiLp.add_apply, add_assoc]
    rw [covariance_const_add_left (hco i), covariance_const_add_right (hco j)]
  have hone : (fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 + be.2)
      = fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
          Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1
            + Matrix.toEuclideanLin (𝕜 := ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) be.2 := by
    funext be
    rw [toEuclideanLin_one_apply]
  rw [hdrop, lmmInner, hone,
    covMatrix_map_add_prod G R D.Z (1 : Matrix (Fin n) (Fin n) ℝ) hG2 hR2]
  simp

/-- **M2, the Gaussian marginal** (`LW82` Eq. (1.2)): with Gaussian latent effects and
noise, `Y ∼ N(Xβ, Z Gm Zᵀ + Rm)`. -/
theorem lmmLaw_multivariateGaussian (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: genuine covariance parameters; LW82 Eq. (1.1)
    (hGm : Gm.PosSemidef) (hRm : Rm.PosSemidef) :
    lmmLaw D β (multivariateGaussian 0 Gm) (multivariateGaussian 0 Rm)
      = multivariateGaussian (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β)
          (D.Z * Gm * D.Zᵀ + Rm) := by
  have hZG : (D.Z * Gm * D.Zᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hGm.mul_mul_conjTranspose_same D.Z
  have hS : (D.Z * Gm * D.Zᵀ + Rm).PosSemidef := hZG.add hRm
  have hmapG : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) Gm).map
      (fun x => Matrix.toEuclideanLin (𝕜 := ℝ) D.Z x)
      = multivariateGaussian 0 (D.Z * Gm * D.Zᵀ) := by
    have h := multivariateGaussian_map_affine (0 : EuclideanSpace ℝ (Fin q)) Gm hGm D.Z 0
    simpa using h
  have hinner : lmmInner D (multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) Gm)
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) Rm)
      = multivariateGaussian 0 (D.Z * Gm * D.Zᵀ + Rm) := by
    rw [lmmInner_eq_conv, hmapG,
      AsymptoticStatistics.multivariateGaussian_conv_multivariateGaussian 0 0 hZG hRm]
    simp
  rw [lmmLaw_eq_map_lmmInner, hinner, multivariateGaussian_map_const_add 0 _ hS]
  simp

/-- The marginal covariance is positive semidefinite (sanity corollary of M1b). -/
theorem posSemidef_variance_components (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: genuine covariance parameters; LW82 Eq. (1.1)
    (hGm : Gm.PosSemidef) (hRm : Rm.PosSemidef) :
    (D.Z * Gm * D.Zᵀ + Rm).PosSemidef := by
  refine Matrix.PosSemidef.add ?_ hRm
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hGm.mul_mul_conjTranspose_same D.Z

end StatLean.StatisticalModels.MixedEffects
