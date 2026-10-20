module
public import StatLean.StatisticalModels.Longitudinal.Defs
public import StatLean.StatisticalModels.ForMathlib.CovarianceMatrix

@[expose] public section

/-!
# The exact finite-sample sandwich — bread, meat, and the GEE estimator's moments

The conditional-on-design (fixed-matrix) GEE layer: `N` independent subjects with fixed
per-subject Jacobians `D i`, working covariances `V i`, and response laws `Qs i` (true
covariances `Covs i`, unknown). Everything here is **exact at finite `N`** — zero asymptotics:

* `geeBread D V = ∑ Dᵢᵀ Vᵢ⁻¹ Dᵢ` and `geeMeat D V Covs = ∑ Dᵢᵀ Vᵢ⁻¹ Σᵢ Vᵢ⁻¹ Dᵢ`;
* `geeScoreTotal` — the centered total estimating function; `geeEstimatorMap` — the linear
  GEE/WLS estimator `B⁻¹ ∑ Dᵢᵀ Vᵢ⁻¹ yᵢ`;
* `geeEstimatorMap_eq_add` — the linearization `β̂ = β₀ + B⁻¹ U(β₀)` (the workhorse);
* `meanVec_geeScoreTotal` / `meanVec_geeEstimator` — unbiasedness under the mean model;
* **`covMatrix_geeScoreTotal` (the meat)** and **`covMatrix_geeEstimator` (the exact
  bread-meat-bread sandwich)** `Cov(β̂) = B⁻¹ M B⁻¹` — `LZ86 §3` Eq. (13) with the
  asymptotics stripped away.

Cluster-independence additivity is not a separate statement: it *is* the
`covMatrix_map_sum_pi` engine (G-B1) these proofs instantiate.

**Reference.** K.-Y. Liang and S. L. Zeger, *Biometrika* **73** (1986), §3, Eq. (13) (the
robust/sandwich covariance) (`LZ86 §3`); bibliographic lineage: P. J. Huber (1967 Berkeley
Symposium) and H. White, *Econometrica* **48** (1980) (heteroscedasticity-consistent
covariance); FLW Ch. 13 (verify §).

**Proof formalization notes.** *Book vs Lean:* LZ86 state the sandwich asymptotically; here
the estimator is exactly linear in the data, so its mean and covariance are exact matrix
identities — a strict finite-sample strengthening. The design is conditional-on-covariates
(fixed matrices); the random-`X` version is a named future debt (D-M1). Working covariances
are required symmetric (USER-INPUT `hVsymm` — every covariance model is); invertibility of
the bread enters as `IsUnit (geeBread D V).det`.

**Bibliographic comments.** The bread–meat vocabulary is folklore for the
Huber–White–Liang–Zeger estimator; Godambe optimality of the weights is
`Longitudinal.Godambe`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.Longitudinal

open StatLean.StatisticalModels

variable {N m q : ℕ}

section Helpers

set_option linter.unusedSectionVars false

variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
  [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]

/-- LEAN-ONLY: `toEuclideanLin` turns matrix multiplication into composition. -/
private theorem toEuclideanLin_comp (A : Matrix ι₃ ι₂ ℝ) (B : Matrix ι₂ ι₁ ℝ)
    (x : EuclideanSpace ℝ ι₁) :
    Matrix.toEuclideanLin (𝕜 := ℝ) A (Matrix.toEuclideanLin (𝕜 := ℝ) B x)
      = Matrix.toEuclideanLin (𝕜 := ℝ) (A * B) x := by
  simp [Matrix.toLpLin_apply]

/-- LEAN-ONLY: the identity matrix acts as the identity. -/
private theorem toEuclideanLin_one_apply (x : EuclideanSpace ℝ ι₁) :
    Matrix.toEuclideanLin (𝕜 := ℝ) (1 : Matrix ι₁ ι₁ ℝ) x = x := by
  simp

/-- LEAN-ONLY: the matrix action as a continuous linear map (finite dimension). -/
private noncomputable def matCLM (A : Matrix ι₂ ι₁ ℝ) :
    EuclideanSpace ℝ ι₁ →L[ℝ] EuclideanSpace ℝ ι₂ :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (𝕜 := ℝ) A)

private theorem matCLM_apply (A : Matrix ι₂ ι₁ ℝ) (x : EuclideanSpace ℝ ι₁) :
    matCLM A x = Matrix.toEuclideanLin (𝕜 := ℝ) A x := rfl

variable {N' : ℕ} (μs : Fin N' → Measure (EuclideanSpace ℝ ι₁))
  [∀ k, IsProbabilityMeasure (μs k)]

/-- LEAN-ONLY: a coordinate of the product law inherits the factor's second moment. -/
private theorem memLp_coord (hL2 : ∀ k, MemLp id 2 (μs k)) (k : Fin N') :
    MemLp (fun x : Fin N' → EuclideanSpace ℝ ι₁ => x k) 2 (Measure.pi μs) := by
  simpa [Function.comp_def] using (hL2 k).comp_measurePreserving (measurePreserving_eval μs k)

/-- LEAN-ONLY: a coordinate of the product law inherits the factor's first moment. -/
private theorem integrable_coord (h1 : ∀ k, Integrable id (μs k)) (k : Fin N') :
    Integrable (fun x : Fin N' → EuclideanSpace ℝ ι₁ => x k) (Measure.pi μs) := by
  simpa [Function.comp_def] using
    (measurePreserving_eval μs k).integrable_comp_of_integrable (h1 k)

/-- LEAN-ONLY: marginalization of the mean onto the `k`-th factor. -/
private theorem integral_coord (k : Fin N') :
    ∫ x : Fin N' → EuclideanSpace ℝ ι₁, x k ∂(Measure.pi μs) = meanVec (μs k) := by
  have h := (measurePreserving_eval μs k).map_eq
  rw [meanVec, ← h]
  exact (integral_map (φ := fun x : Fin N' → EuclideanSpace ℝ ι₁ => x k)
    (f := fun y : EuclideanSpace ℝ ι₁ => y) (measurable_pi_apply k).aemeasurable
    (by fun_prop)).symm

private theorem continuous_wsum (A : Fin N' → Matrix ι₃ ι₁ ℝ) :
    Continuous fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k) := by
  refine continuous_finset_sum Finset.univ fun k _ => ?_
  exact (matCLM (A k)).continuous.comp (continuous_apply k)

/-- **Mean of a weighted sum of independent coordinates plus a constant** — the `meanVec`
counterpart of the covariance engine `covMatrix_map_sum_pi` (And58 Ch. 2). -/
private theorem meanVec_map_wsum_add (A : Fin N' → Matrix ι₃ ι₁ ℝ) (b : EuclideanSpace ℝ ι₃)
    (h1 : ∀ k, Integrable id (μs k)) :
    meanVec ((Measure.pi μs).map fun x =>
        (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) + b)
      = (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (meanVec (μs k))) + b := by
  have hterm : ∀ k, Integrable (fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) (Measure.pi μs) := fun k =>
    (matCLM (A k)).integrable_comp (integrable_coord μs h1 k)
  have hG : Integrable (fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) (Measure.pi μs) :=
    integrable_finset_sum _ fun k _ => hterm k
  have hcont : Continuous fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) + b :=
    (continuous_wsum A).add continuous_const
  rw [meanVec, integral_map (f := fun y : EuclideanSpace ℝ ι₃ => y) hcont.aemeasurable
    (by fun_prop)]
  have hsplit : ∫ x : Fin N' → EuclideanSpace ℝ ι₁,
        ((∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) + b) ∂(Measure.pi μs)
      = (∫ x : Fin N' → EuclideanSpace ℝ ι₁,
          (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) ∂(Measure.pi μs))
        + ∫ _x : Fin N' → EuclideanSpace ℝ ι₁, b ∂(Measure.pi μs) :=
    integral_add hG (integrable_const b)
  rw [hsplit, integral_const, integral_finset_sum _ fun k _ => hterm k]
  simp only [probReal_univ, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k))
      = (fun x : Fin N' → EuclideanSpace ℝ ι₁ => matCLM (A k) (x k)) from rfl,
    (matCLM (A k)).integral_comp_comm (integrable_coord μs h1 k), integral_coord μs k,
    matCLM_apply]

/-- **Covariance of a weighted sum of independent coordinates plus a constant** — the
centering constant drops out (And58 Ch. 2). -/
private theorem covMatrix_map_wsum_add (A : Fin N' → Matrix ι₃ ι₁ ℝ) (b : EuclideanSpace ℝ ι₃)
    (hL2 : ∀ k, MemLp id 2 (μs k)) :
    covMatrix ((Measure.pi μs).map fun x =>
        (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) + b)
      = ∑ k, A k * covMatrix (μs k) * (A k)ᵀ := by
  have hmeasG : Measurable fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k) := (continuous_wsum A).measurable
  haveI hprob : IsProbabilityMeasure ((Measure.pi μs).map fun x =>
      ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) :=
    Measure.isProbabilityMeasure_map hmeasG.aemeasurable
  have hL2ν : MemLp id 2 ((Measure.pi μs).map fun x =>
      ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hmeasG.aemeasurable]
    simpa [Function.comp_def] using! memLp_finset_sum Finset.univ fun k (_ : k ∈ Finset.univ) =>
      (matCLM (A k)).comp_memLp' (memLp_coord μs hL2 k)
  have hmap : ((Measure.pi μs).map fun x =>
        (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) + b)
      = ((Measure.pi μs).map fun x =>
          ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)).map
        fun z => Matrix.toEuclideanLin (𝕜 := ℝ) (1 : Matrix ι₃ ι₃ ℝ) z + b := by
    rw [Measure.map_map (by fun_prop) hmeasG]
    congr 1
    funext x
    simp
  rw [hmap, covMatrix_map_affine _ 1 b hL2ν, Matrix.one_mul, Matrix.transpose_one,
    Matrix.mul_one, covMatrix_map_sum_pi μs A hL2]

end Helpers

/-- The **bread** `B = ∑ Dᵢᵀ Vᵢ⁻¹ Dᵢ` (`LZ86 §3`). -/
noncomputable def geeBread (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  ∑ i, (D i)ᵀ * (V i)⁻¹ * D i

/-- The **meat** `M = ∑ Dᵢᵀ Vᵢ⁻¹ Σᵢ Vᵢ⁻¹ Dᵢ` (`LZ86 §3` Eq. (13)). -/
noncomputable def geeMeat (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V Covs : Fin N → Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  ∑ i, (D i)ᵀ * (V i)⁻¹ * Covs i * (V i)⁻¹ * D i

/-- The centered total estimating function `U(β₀)(y) = ∑ Dᵢᵀ Vᵢ⁻¹ (yᵢ − Dᵢ β₀)`. -/
noncomputable def geeScoreTotal (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q))
    (y : Fin N → EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin q) :=
  ∑ i, Matrix.toEuclideanLin (𝕜 := ℝ) ((D i)ᵀ * (V i)⁻¹)
    (y i - Matrix.toEuclideanLin (𝕜 := ℝ) (D i) β₀)

/-- The linear GEE/WLS estimator `β̂(y) = B⁻¹ ∑ Dᵢᵀ Vᵢ⁻¹ yᵢ` (`LZ86 §2`). -/
noncomputable def geeEstimatorMap (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (y : Fin N → EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin q) :=
  Matrix.toEuclideanLin (𝕜 := ℝ) (geeBread D V)⁻¹
    (∑ i, Matrix.toEuclideanLin (𝕜 := ℝ) ((D i)ᵀ * (V i)⁻¹) (y i))

section Algebra

/-- LEAN-ONLY: the weighted Jacobians reassemble the bread. -/
private theorem sum_weight_apply (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q)) :
    ∑ i, Matrix.toEuclideanLin (𝕜 := ℝ) ((D i)ᵀ * (V i)⁻¹)
        (Matrix.toEuclideanLin (𝕜 := ℝ) (D i) β₀)
      = Matrix.toEuclideanLin (𝕜 := ℝ) (geeBread D V) β₀ := by
  simp only [toEuclideanLin_comp, geeBread, map_sum, LinearMap.sum_apply]

/-- LEAN-ONLY: the bread is symmetric when the working covariances are. -/
private theorem geeBread_transpose (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (hVsymm : ∀ i, (V i)ᵀ = V i) :
    (geeBread D V)ᵀ = geeBread D V := by
  simp only [geeBread, Matrix.transpose_sum, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, hVsymm]
  exact Finset.sum_congr rfl fun i _ => by rw [← Matrix.mul_assoc]

/-- LEAN-ONLY: the estimating function as a weighted coordinate sum plus a constant. -/
private theorem geeScoreTotal_eq (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q)) :
    geeScoreTotal D V β₀ = fun y : Fin N → EuclideanSpace ℝ (Fin m) =>
      (∑ i, Matrix.toEuclideanLin (𝕜 := ℝ) ((D i)ᵀ * (V i)⁻¹) (y i))
        + (-Matrix.toEuclideanLin (𝕜 := ℝ) (geeBread D V) β₀) := by
  funext y
  rw [← sub_eq_add_neg, ← sum_weight_apply D V β₀, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => map_sub _ _ _

/-- LEAN-ONLY: the estimator as a weighted coordinate sum (no constant term). -/
private theorem geeEstimatorMap_eq (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) :
    geeEstimatorMap D V = fun y : Fin N → EuclideanSpace ℝ (Fin m) =>
      (∑ i, Matrix.toEuclideanLin (𝕜 := ℝ)
        ((geeBread D V)⁻¹ * ((D i)ᵀ * (V i)⁻¹)) (y i)) + (0 : EuclideanSpace ℝ (Fin q)) := by
  funext y
  rw [add_zero, geeEstimatorMap, map_sum]
  exact Finset.sum_congr rfl fun i _ => toEuclideanLin_comp _ _ _

end Algebra

/-- **Linearization** `β̂(y) = β₀ + B⁻¹ U(β₀)(y)` — the exact-moments workhorse. -/
theorem geeEstimatorMap_eq_add (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q))
    -- USER-INPUT: invertible bread (identified design); LZ86 §2
    (hB : IsUnit (geeBread D V).det) (y : Fin N → EuclideanSpace ℝ (Fin m)) :
    geeEstimatorMap D V y
      = β₀ + Matrix.toEuclideanLin (𝕜 := ℝ) (geeBread D V)⁻¹ (geeScoreTotal D V β₀ y) := by
  simp only [geeScoreTotal_eq D V β₀]
  rw [← sub_eq_add_neg, map_sub, toEuclideanLin_comp, Matrix.nonsing_inv_mul _ hB,
    toEuclideanLin_one_apply, geeEstimatorMap]
  abel

/-- The total estimating function is centered under the mean model (the fixed-design form
of `gee_unbiased`). -/
theorem meanVec_geeScoreTotal (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q))
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m)))
    [∀ i, IsProbabilityMeasure (Qs i)]
    -- USER-INPUT: correct marginal means; LZ86 §2
    (hmean : ∀ i, meanVec (Qs i) = Matrix.toEuclideanLin (𝕜 := ℝ) (D i) β₀)
    -- USER-INPUT: integrable responses; LZ86 §3
    (hL1 : ∀ i, Integrable id (Qs i)) :
    meanVec ((Measure.pi Qs).map (geeScoreTotal D V β₀)) = 0 := by
  rw [geeScoreTotal_eq D V β₀, meanVec_map_wsum_add Qs _ _ hL1]
  simp only [hmean]
  rw [sum_weight_apply]
  abel

/-- **Unbiasedness of the GEE estimator** (exact, finite `N`). -/
theorem meanVec_geeEstimator (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q))
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m)))
    [∀ i, IsProbabilityMeasure (Qs i)]
    -- USER-INPUT: correct marginal means; LZ86 §2
    (hmean : ∀ i, meanVec (Qs i) = Matrix.toEuclideanLin (𝕜 := ℝ) (D i) β₀)
    -- USER-INPUT: integrable responses; LZ86 §3
    (hL1 : ∀ i, Integrable id (Qs i))
    -- USER-INPUT: invertible bread; LZ86 §2
    (hB : IsUnit (geeBread D V).det) :
    meanVec ((Measure.pi Qs).map (geeEstimatorMap D V)) = β₀ := by
  have hsum : ∑ i, (geeBread D V)⁻¹ * ((D i)ᵀ * (V i)⁻¹) * D i
      = (geeBread D V)⁻¹ * geeBread D V := by
    rw [geeBread, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mul_assoc]
  rw [geeEstimatorMap_eq D V, meanVec_map_wsum_add Qs _ _ hL1, add_zero]
  simp only [hmean, toEuclideanLin_comp]
  rw [← LinearMap.sum_apply, ← map_sum, hsum, Matrix.nonsing_inv_mul _ hB,
    toEuclideanLin_one_apply]

/-- **The meat** (exact): the covariance of the total estimating function is
`∑ Dᵢᵀ Vᵢ⁻¹ Σᵢ Vᵢ⁻¹ Dᵢ` (`LZ86 §3` Eq. (13), finite-sample form). -/
theorem covMatrix_geeScoreTotal (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V Covs : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q))
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m)))
    [∀ i, IsProbabilityMeasure (Qs i)]
    -- USER-INPUT: true response covariances; LZ86 §3
    (hcov : ∀ i, covMatrix (Qs i) = Covs i)
    -- USER-INPUT: second moments; LZ86 §3
    (hL2 : ∀ i, MemLp id 2 (Qs i))
    -- USER-INPUT: symmetric working covariances; LZ86 §2
    (hVsymm : ∀ i, (V i)ᵀ = V i) :
    covMatrix ((Measure.pi Qs).map (geeScoreTotal D V β₀)) = geeMeat D V Covs := by
  rw [geeScoreTotal_eq D V β₀, covMatrix_map_wsum_add Qs _ _ hL2, geeMeat]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcov, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hVsymm,
    Matrix.transpose_transpose, ← Matrix.mul_assoc]

/-- **The exact sandwich** `Cov(β̂) = B⁻¹ M B⁻¹` (`LZ86 §3` Eq. (13), exact at finite `N`).
The book's mean-correctness and bread-invertibility assumptions are not hypotheses here:
`covMatrix` is translation-invariant, and `(A⁻¹)ᵀ = (Aᵀ)⁻¹` holds unconditionally for
`Matrix.inv` — so the identity is exact for arbitrary means and (junk-coherently) for
singular bread. -/
theorem covMatrix_geeEstimator (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V Covs : Fin N → Matrix (Fin m) (Fin m) ℝ)
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m)))
    [∀ i, IsProbabilityMeasure (Qs i)]
    -- USER-INPUT: true covariances, second moments; LZ86 §2–3
    (hcov : ∀ i, covMatrix (Qs i) = Covs i) (hL2 : ∀ i, MemLp id 2 (Qs i))
    -- USER-INPUT: symmetric working covariances; LZ86 §2
    (hVsymm : ∀ i, (V i)ᵀ = V i) :
    covMatrix ((Measure.pi Qs).map (geeEstimatorMap D V))
      = (geeBread D V)⁻¹ * geeMeat D V Covs * (geeBread D V)⁻¹ := by
  have hBt : ((geeBread D V)⁻¹)ᵀ = (geeBread D V)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, geeBread_transpose D V hVsymm]
  rw [geeEstimatorMap_eq D V, covMatrix_map_wsum_add Qs _ _ hL2, geeMeat, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcov, Matrix.transpose_mul, hBt, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    hVsymm, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

end StatLean.StatisticalModels.Longitudinal
