module
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Covariance

@[expose] public section

/-!
# Mean vector and covariance matrix of a law on Euclidean space

The canonical second-moment objects for measures on `EuclideanSpace ℝ ι`, the shared substrate
of the Gaussian, mixed-effects and GEE slices:

* `meanVec μ` — the Bochner mean vector `∫ x ∂μ`;
* `covMatrix μ` — the covariance matrix `Σᵢⱼ = cov(xᵢ, xⱼ)`;
* `crossCovMatrix μ f g` — the cross-covariance matrix of two vector statistics;

with the calculus: positive semidefiniteness, the values on `multivariateGaussian`, the affine
pushforward law `Σ ↦ A Σ Aᵀ`, additivity for independent summands (product form and
finite-product form), and the cross-covariance rules.

Every statement carries `MemLp` second-moment hypotheses as USER-INPUT: Mathlib's `covariance`
junk-values to `0` without integrability, so the lemmas would be silently vacuous, not false.

The library has three prior ad-hoc special cases (`HypothesisTesting.covMatrix` on
`Fin k`-Euclidean space, `sampleCovMatrix`, `marginalCovMatrix`); this file is the general
carrier. Deduplication of those is a documented laptop follow-up — no other area is touched
here.

**Reference.** T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, Wiley,
1958, Ch. 2 (moments of random vectors; the affine transformation law) (verify §)
(`And58 Ch. 2`).

**Proof formalization notes.** PSD generalizes the `Fin k` argument used privately at
`HypothesisTesting/Bootstrap/Multivariate.lean` (quadratic form = variance of `⟪u, ·⟫ ≥ 0`).
Affine pushforward is coordinate bilinearity of `covariance` (`covariance_add_left`-family)
plus `integral_map`; the Gaussian values are `integral_id_multivariateGaussian` and
`covariance_eval_multivariateGaussian`. Independent additivity kills cross terms with the
independence-vanishing lemma for `covariance` under `Measure.prod` coordinates.

**Bibliographic comments.** The covariance-matrix calculus is 19th-century (Bravais, Pearson);
its systematic matrix form is Anderson (1958). Nothing here is original.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels

variable {ι ι₁ ι₂ : Type*} [Fintype ι] [Fintype ι₁] [Fintype ι₂]
  {Ω : Type*} [MeasurableSpace Ω]

/-- The **mean vector** `∫ x ∂μ` of a law on Euclidean space (And58 Ch. 2). -/
noncomputable def meanVec (μ : Measure (EuclideanSpace ℝ ι)) : EuclideanSpace ℝ ι :=
  ∫ x, x ∂μ

/-- The **covariance matrix** `Σᵢⱼ = cov(xᵢ, xⱼ)` of a law on Euclidean space
(And58 Ch. 2). Junk-values to `0` entries without second moments. -/
noncomputable def covMatrix (μ : Measure (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  Matrix.of fun i j => cov[fun x => x i, fun x => x j; μ]

/-- The **cross-covariance matrix** of two vector statistics on a common sample space
(the BLUP/Godambe workhorse). -/
noncomputable def crossCovMatrix (μ : Measure Ω) (f : Ω → EuclideanSpace ℝ ι₁)
    (g : Ω → EuclideanSpace ℝ ι₂) : Matrix ι₁ ι₂ ℝ :=
  Matrix.of fun i j => cov[fun ω => f ω i, fun ω => g ω j; μ]

@[simp]
theorem covMatrix_apply (μ : Measure (EuclideanSpace ℝ ι)) (i j : ι) :
    covMatrix μ i j = cov[fun x => x i, fun x => x j; μ] := rfl

@[simp]
theorem crossCovMatrix_apply (μ : Measure Ω) (f : Ω → EuclideanSpace ℝ ι₁)
    (g : Ω → EuclideanSpace ℝ ι₂) (i : ι₁) (j : ι₂) :
    crossCovMatrix μ f g i j = cov[fun ω => f ω i, fun ω => g ω j; μ] := rfl

/-- Coordinate evaluations inherit the second moment of the identity: `fun x ↦ x i` is the
coordinate functional applied to `id`. -/
private theorem memLp_eval {μ : Measure (EuclideanSpace ℝ ι)} (hL2 : MemLp id 2 μ) (i : ι) :
    MemLp (fun x : EuclideanSpace ℝ ι => x i) 2 μ :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hL2

/-- The covariance matrix is symmetric. -/
theorem covMatrix_transpose (μ : Measure (EuclideanSpace ℝ ι)) :
    (covMatrix μ)ᵀ = covMatrix μ := by
  ext i j
  exact covariance_comm _ _

/-- Cross-covariance transposes to the swapped cross-covariance. -/
theorem crossCovMatrix_transpose (μ : Measure Ω) (f : Ω → EuclideanSpace ℝ ι₁)
    (g : Ω → EuclideanSpace ℝ ι₂) :
    (crossCovMatrix μ f g)ᵀ = crossCovMatrix μ g f := by
  ext i j
  exact covariance_comm _ _

/-- **Positive semidefiniteness** of the covariance matrix (And58 Ch. 2): the quadratic form
`uᵀ Σ u` is the variance of `⟪u, x⟫`. -/
theorem posSemidef_covMatrix (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    -- USER-INPUT: second moments; And58 Ch. 2
    (hL2 : MemLp id 2 μ) :
    (covMatrix μ).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun u => ?_⟩
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial, covMatrix_apply] using
      covariance_comm (fun x : EuclideanSpace ℝ ι => x j) (fun x : EuclideanSpace ℝ ι => x i)
  · have hmem : ∀ i, MemLp (fun x : EuclideanSpace ℝ ι => u i * x i) 2 μ := fun i =>
      (memLp_eval hL2 i).const_mul (u i)
    have key : star u ⬝ᵥ (covMatrix μ *ᵥ u)
        = cov[fun x : EuclideanSpace ℝ ι => ∑ i, u i * x i,
              fun x : EuclideanSpace ℝ ι => ∑ j, u j * x j; μ] := by
      rw [covariance_fun_sum_fun_sum hmem hmem]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        covariance_const_mul_left, covariance_const_mul_right, covMatrix_apply,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [key, covariance_self]
    · exact variance_nonneg _ _
    · exact (memLp_finset_sum Finset.univ fun i _ =>
        hmem i).aestronglyMeasurable.aemeasurable

/-- Mean vector of the multivariate Gaussian. Unconditional in `S`: the pin's
`multivariateGaussian` has mean `m` in its degenerate/junk regime as well, so no
positive-semidefiniteness hypothesis is needed (contrast `covMatrix_multivariateGaussian`). -/
theorem meanVec_multivariateGaussian [DecidableEq ι] (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) :
    meanVec (multivariateGaussian m S) = m :=
  integral_id_multivariateGaussian

/-- Covariance matrix of the multivariate Gaussian. -/
theorem covMatrix_multivariateGaussian [DecidableEq ι] (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ)
    -- USER-INPUT: a genuine covariance parameter; And58 Ch. 2
    (hS : S.PosSemidef) :
    covMatrix (multivariateGaussian m S) = S := by
  ext i j
  exact covariance_eval_multivariateGaussian hS i j

/-- The matrix action on Euclidean space as a continuous linear map (finite dimension). -/
private noncomputable def matrixCLM [DecidableEq ι₁] (A : Matrix ι₂ ι₁ ℝ) :
    EuclideanSpace ℝ ι₁ →L[ℝ] EuclideanSpace ℝ ι₂ :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (𝕜 := ℝ) A)

private theorem matrixCLM_apply [DecidableEq ι₁] (A : Matrix ι₂ ι₁ ℝ)
    (x : EuclideanSpace ℝ ι₁) :
    matrixCLM A x = Matrix.toEuclideanLin (𝕜 := ℝ) A x := rfl

/-- Coordinates of the matrix action are the row sums. -/
private theorem toEuclideanLin_coord [DecidableEq ι₁] (A : Matrix ι₂ ι₁ ℝ)
    (x : EuclideanSpace ℝ ι₁) (k : ι₂) :
    (Matrix.toEuclideanLin (𝕜 := ℝ) A x) k = ∑ l, A k l * x l := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- Coordinate evaluation on the target of a measurable map is a.e.-strongly measurable. -/
private theorem aesm_eval {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {F : α → EuclideanSpace ℝ ι} (k : ι) :
    AEStronglyMeasurable (fun y : EuclideanSpace ℝ ι => y k) (ν.map F) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.aestronglyMeasurable

/-- The core bilinear computation: the covariance of two matrix rows evaluated against a law
with second moments is the corresponding entry of `A Σ Bᵀ`. -/
private theorem covariance_rows {ι₃ : Type*} [Fintype ι₃]
    {μ : Measure (EuclideanSpace ℝ ι₁)} [IsFiniteMeasure μ] (hL2 : MemLp id 2 μ)
    (A B : Matrix ι₃ ι₁ ℝ) (i j : ι₃) :
    cov[fun x : EuclideanSpace ℝ ι₁ => ∑ k, A i k * x k,
        fun x : EuclideanSpace ℝ ι₁ => ∑ l, B j l * x l; μ] = (A * covMatrix μ * Bᵀ) i j := by
  rw [covariance_fun_sum_fun_sum (fun k => (memLp_eval hL2 k).const_mul (A i k))
    (fun l => (memLp_eval hL2 l).const_mul (B j l))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, ← covMatrix_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **Mean of an affine pushforward**: `E[A x + b] = A (E x) + b` (And58 Ch. 2). -/
theorem meanVec_map_affine [DecidableEq ι₁] (μ : Measure (EuclideanSpace ℝ ι₁))
    [IsProbabilityMeasure μ]
    (A : Matrix ι₂ ι₁ ℝ) (b : EuclideanSpace ℝ ι₂)
    -- USER-INPUT: first moments; And58 Ch. 2
    (h1 : Integrable id μ) :
    meanVec (μ.map fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x + b)
      = Matrix.toEuclideanLin (𝕜 := ℝ) A (meanVec μ) + b := by
  have hAint : Integrable (fun x => matrixCLM A x) μ :=
    (matrixCLM A).integrable_comp h1
  have hmap : ∫ y : EuclideanSpace ℝ ι₂, y
        ∂(μ.map fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x + b)
      = ∫ x, (Matrix.toEuclideanLin (𝕜 := ℝ) A x + b) ∂μ :=
    integral_map (by fun_prop) (by fun_prop)
  have hsplit : ∫ x, (Matrix.toEuclideanLin (𝕜 := ℝ) A x + b) ∂μ
      = (∫ x, matrixCLM A x ∂μ) + ∫ _x : EuclideanSpace ℝ ι₁, b ∂μ :=
    integral_add hAint (integrable_const b)
  have h1' : Integrable (fun x : EuclideanSpace ℝ ι₁ => x) μ := h1
  have hcomm : ∫ x, matrixCLM A x ∂μ = matrixCLM A (∫ x, x ∂μ) :=
    (matrixCLM A).integral_comp_comm h1'
  rw [meanVec, hmap, hsplit, hcomm, integral_const]
  simp [meanVec, matrixCLM_apply]

/-- **Covariance of an affine pushforward**: `Cov(A x + b) = A Σ Aᵀ` (And58 Ch. 2). -/
theorem covMatrix_map_affine [DecidableEq ι₁] (μ : Measure (EuclideanSpace ℝ ι₁))
    [IsProbabilityMeasure μ]
    (A : Matrix ι₂ ι₁ ℝ) (b : EuclideanSpace ℝ ι₂)
    -- USER-INPUT: second moments; And58 Ch. 2
    (hL2 : MemLp id 2 μ) :
    covMatrix (μ.map fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x + b)
      = A * covMatrix μ * Aᵀ := by
  have hmem : ∀ (k : ι₂) (l : ι₁), MemLp (fun x : EuclideanSpace ℝ ι₁ => A k l * x l) 2 μ :=
    fun k l => (memLp_eval hL2 l).const_mul (A k l)
  have hrow : ∀ k : ι₂, Integrable (fun x : EuclideanSpace ℝ ι₁ => ∑ l, A k l * x l) μ :=
    fun k => (memLp_finset_sum Finset.univ fun l _ => hmem k l).integrable (by norm_num)
  ext i j
  rw [covMatrix_apply, covariance_map_fun (aesm_eval i) (aesm_eval j) (by fun_prop)]
  simp only [PiLp.add_apply, toEuclideanLin_coord]
  rw [covariance_add_const_left (hrow i), covariance_add_const_right (hrow j)]
  exact covariance_rows hL2 A A i j

/-- Covariance of two statistics of the first factor is computed on that factor's marginal. -/
private theorem covariance_comp_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [IsProbabilityMeasure ν] {X Y : α → ℝ}
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    cov[fun p : α × β => X p.1, fun p : α × β => Y p.1; μ.prod ν] = cov[X, Y; μ] := by
  have hm : (μ.prod ν).map Prod.fst = μ := Measure.fst_prod
  have h := covariance_map_fun (X := X) (Y := Y) (Z := Prod.fst) (μ := μ.prod ν)
    (by rw [hm]; exact hX) (by rw [hm]; exact hY) measurable_fst.aemeasurable
  rw [hm] at h
  exact h.symm

/-- Covariance of two statistics of the second factor is computed on that factor's marginal. -/
private theorem covariance_comp_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [SFinite ν] {X Y : β → ℝ}
    (hX : AEStronglyMeasurable X ν) (hY : AEStronglyMeasurable Y ν) :
    cov[fun p : α × β => X p.2, fun p : α × β => Y p.2; μ.prod ν] = cov[X, Y; ν] := by
  have hm : (μ.prod ν).map Prod.snd = ν := Measure.snd_prod
  have h := covariance_map_fun (X := X) (Y := Y) (Z := Prod.snd) (μ := μ.prod ν)
    (by rw [hm]; exact hX) (by rw [hm]; exact hY) measurable_snd.aemeasurable
  rw [hm] at h
  exact h.symm

/-- **Additivity under independence (product form)**: the covariance of a sum of linear images
of the two independent coordinates of a product law is the sum of the transported covariances
— cross terms vanish (And58 Ch. 2). -/
theorem covMatrix_map_add_prod [DecidableEq ι₁] [DecidableEq ι₂]
    (μ : Measure (EuclideanSpace ℝ ι₁))
    (ν : Measure (EuclideanSpace ℝ ι₂)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ι₃ : Type*} [Fintype ι₃]
    (A : Matrix ι₃ ι₁ ℝ) (B : Matrix ι₃ ι₂ ℝ)
    -- USER-INPUT: second moments of both factors; And58 Ch. 2
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) :
    covMatrix ((μ.prod ν).map fun p =>
        Matrix.toEuclideanLin (𝕜 := ℝ) A p.1 + Matrix.toEuclideanLin (𝕜 := ℝ) B p.2)
      = A * covMatrix μ * Aᵀ + B * covMatrix ν * Bᵀ := by
  have hmemμ : ∀ k : ι₃, MemLp (fun x : EuclideanSpace ℝ ι₁ => ∑ l, A k l * x l) 2 μ :=
    fun k => memLp_finset_sum _ fun l _ => (memLp_eval hμ l).const_mul (A k l)
  have hmemν : ∀ k : ι₃, MemLp (fun y : EuclideanSpace ℝ ι₂ => ∑ m, B k m * y m) 2 ν :=
    fun k => memLp_finset_sum _ fun m _ => (memLp_eval hν m).const_mul (B k m)
  have hPμ : ∀ k : ι₃, MemLp (fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ =>
      ∑ l, A k l * p.1 l) 2 (μ.prod ν) := fun k => (hmemμ k).comp_fst ν
  have hPν : ∀ k : ι₃, MemLp (fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ =>
      ∑ m, B k m * p.2 m) 2 (μ.prod ν) := fun k => (hmemν k).comp_snd μ
  have hsplit : ∀ k : ι₃,
      (fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ =>
        (Matrix.toEuclideanLin (𝕜 := ℝ) A p.1 + Matrix.toEuclideanLin (𝕜 := ℝ) B p.2) k)
        = (fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ => ∑ l, A k l * p.1 l)
          + fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ => ∑ m, B k m * p.2 m := by
    intro k
    funext p
    simp [toEuclideanLin_coord]
  ext i j
  rw [covMatrix_apply, covariance_map_fun (aesm_eval i) (aesm_eval j) (by fun_prop)]
  have h11 : cov[fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ => ∑ l, A i l * p.1 l,
      fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ => ∑ l, A j l * p.1 l; μ.prod ν]
      = (A * covMatrix μ * Aᵀ) i j := by
    rw [covariance_comp_fst (hmemμ i).aestronglyMeasurable (hmemμ j).aestronglyMeasurable]
    exact covariance_rows hμ A A i j
  have h22 : cov[fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ => ∑ m, B i m * p.2 m,
      fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ => ∑ m, B j m * p.2 m; μ.prod ν]
      = (B * covMatrix ν * Bᵀ) i j := by
    rw [covariance_comp_snd (hmemν i).aestronglyMeasurable (hmemν j).aestronglyMeasurable]
    exact covariance_rows hν B B i j
  have h12 : cov[fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ => ∑ l, A i l * p.1 l,
      fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ => ∑ m, B j m * p.2 m; μ.prod ν] = 0 :=
    covariance_fst_snd_prod (hmemμ i) (hmemν j)
  have h21 : cov[fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ => ∑ m, B i m * p.2 m,
      fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ => ∑ l, A j l * p.1 l; μ.prod ν] = 0 := by
    rw [covariance_comm _ _]
    exact covariance_fst_snd_prod (hmemμ j) (hmemν i)
  rw [hsplit i, hsplit j, covariance_add_left (hPμ i) (hPν i) ((hPμ j).add (hPν j)),
    covariance_add_right (hPμ i) (hPμ j) (hPν j),
    covariance_add_right (hPν i) (hPμ j) (hPν j), h11, h12, h21, h22, Matrix.add_apply]
  ring

/-- **Additivity under independence (finite-product form)**: covariance of a sum of linear
images of independent coordinates under `Measure.pi` (the L2/M1 workhorse). -/
theorem covMatrix_map_sum_pi [DecidableEq ι₁] {N : ℕ}
    (μs : Fin N → Measure (EuclideanSpace ℝ ι₁))
    [∀ k, IsProbabilityMeasure (μs k)]
    {ι₃ : Type*} [Fintype ι₃] (A : Fin N → Matrix ι₃ ι₁ ℝ)
    -- USER-INPUT: second moments of every factor; And58 Ch. 2
    (hL2 : ∀ k, MemLp id 2 (μs k)) :
    covMatrix ((Measure.pi μs).map fun x =>
        ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k))
      = ∑ k, A k * covMatrix (μs k) * (A k)ᵀ := by
  -- the `k`-th block of the `i`-th coordinate, on the factor and on the product
  have hg : ∀ (k : Fin N) (i : ι₃),
      MemLp (fun y : EuclideanSpace ℝ ι₁ => ∑ l, A k i l * y l) 2 (μs k) :=
    fun k i => memLp_finset_sum _ fun l _ => (memLp_eval (hL2 k) l).const_mul (A k i l)
  have hgp : ∀ (k : Fin N) (i : ι₃),
      MemLp (fun x : ∀ _ : Fin N, EuclideanSpace ℝ ι₁ => ∑ l, A k i l * x k l) 2
        (Measure.pi μs) := by
    intro k i
    simpa [Function.comp_def] using
      (hg k i).comp_measurePreserving (measurePreserving_eval μs k)
  -- distinct blocks are independent, so their covariance vanishes
  have hindep : ∀ (k k' : Fin N), k ≠ k' → ∀ i j : ι₃,
      cov[fun x : ∀ _ : Fin N, EuclideanSpace ℝ ι₁ => ∑ l, A k i l * x k l,
          fun x : ∀ _ : Fin N, EuclideanSpace ℝ ι₁ => ∑ l, A k' j l * x k' l;
        Measure.pi μs] = 0 := by
    intro k k' hkk' i j
    have hiid : iIndepFun (fun (k : Fin N) (x : ∀ _ : Fin N, EuclideanSpace ℝ ι₁) => x k)
        (Measure.pi μs) := iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
    have h2 := (hiid.indepFun hkk').comp
      (φ := fun y : EuclideanSpace ℝ ι₁ => ∑ l, A k i l * y l)
      (ψ := fun y : EuclideanSpace ℝ ι₁ => ∑ l, A k' j l * y l) (by fun_prop) (by fun_prop)
    exact h2.covariance_eq_zero (hgp k i) (hgp k' j)
  -- a single block reduces to its own factor
  have hdiag : ∀ (k : Fin N) (i j : ι₃),
      cov[fun x : ∀ _ : Fin N, EuclideanSpace ℝ ι₁ => ∑ l, A k i l * x k l,
          fun x : ∀ _ : Fin N, EuclideanSpace ℝ ι₁ => ∑ l, A k j l * x k l; Measure.pi μs]
        = (A k * covMatrix (μs k) * (A k)ᵀ) i j := by
    intro k i j
    have hm : (Measure.pi μs).map (Function.eval k) = μs k :=
      (measurePreserving_eval μs k).map_eq
    have h := covariance_map_fun (μ := Measure.pi μs) (Z := Function.eval k)
      (X := fun y : EuclideanSpace ℝ ι₁ => ∑ l, A k i l * y l)
      (Y := fun y : EuclideanSpace ℝ ι₁ => ∑ l, A k j l * y l)
      (by rw [hm]; exact (hg k i).aestronglyMeasurable)
      (by rw [hm]; exact (hg k j).aestronglyMeasurable) (measurable_pi_apply k).aemeasurable
    rw [hm] at h
    exact h.symm.trans (covariance_rows (hL2 k) (A k) (A k) i j)
  have hcoord : ∀ (i : ι₃) (x : ∀ _ : Fin N, EuclideanSpace ℝ ι₁),
      (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) i = ∑ k, ∑ l, A k i l * x k l := by
    intro i x
    simp [WithLp.ofLp_sum, Finset.sum_apply, Matrix.mulVec, dotProduct]
  have hcont : ∀ k : Fin N, Continuous fun x : ∀ _ : Fin N, EuclideanSpace ℝ ι₁ =>
      Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k) :=
    fun k => (matrixCLM (A k)).continuous.comp (continuous_apply k)
  have hmeas : AEMeasurable (fun x : ∀ _ : Fin N, EuclideanSpace ℝ ι₁ =>
      ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) (Measure.pi μs) :=
    (continuous_finset_sum Finset.univ fun k _ => hcont k).aemeasurable
  ext i j
  rw [covMatrix_apply, covariance_map_fun (aesm_eval i) (aesm_eval j) hmeas]
  simp only [hcoord]
  rw [covariance_fun_sum_fun_sum (fun k => hgp k i) (fun k => hgp k j), Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun k' _ hne => hindep k k' (Ne.symm hne) i j)
    fun h => absurd (Finset.mem_univ k) h]
  exact hdiag k i j

/-- Cross-covariance of a statistic with itself under the image law. -/
theorem crossCovMatrix_self (μ : Measure Ω) {f : Ω → EuclideanSpace ℝ ι₁}
    -- LEAN-ONLY: measurability for the image-law rewrite
    (hf : AEMeasurable f μ) :
    crossCovMatrix μ f f = covMatrix (μ.map f) := by
  ext i j
  exact (covariance_map_fun (aesm_eval i) (aesm_eval j) hf).symm

end StatLean.StatisticalModels
