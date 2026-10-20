module
public import StatLean.MultipleTesting.ForMathlib.ChiSquared
public import StatLean.AsymptoticStatistics.ForMathlib.Anderson
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import StatLean.HypothesisTesting.ForMathlib.LindebergCLT
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLawExists

@[expose] public section

/-!
# The noncentral chi-squared distribution

The **noncentral chi-squared law** with `k` degrees of freedom and noncentrality parameter
`λ ≥ 0` is the law of the squared norm of a `k`-dimensional Gaussian vector with identity
covariance whose mean has squared length `λ`:
$$\chi^2_k(\lambda) \;=\; \mathcal L\bigl(\|Z + \mu\|^2\bigr), \qquad
  Z \sim N(0, I_k),\quad \|\mu\|^2 = \lambda .$$
It is the limiting law of quadratic-form goodness-of-fit statistics under local
alternatives, and the whole asymptotic power theory of such tests is a statement about the
function `λ ↦ χ²_k(λ)((c, ∞))`.

We take as the definition the pushforward of `multivariateGaussian` under `z ↦ ‖z‖²`, with
the mean placed on the first coordinate axis; that the direction of the mean is irrelevant
is `map_normSq_multivariateGaussian_of_norm_eq`, which is what licenses calling `λ` "the"
noncentrality parameter.

## Main results

* `noncentralChiSquared` — the definition, and `noncentralChiSquared_zero` identifying
  `λ = 0` with the central chi-squared law already in the library.
* `map_normSq_multivariateGaussian_of_norm_eq` — direction invariance: any mean vector of
  squared length `λ` produces the same law.
* `chiSquared_tail_le_noncentralChiSquared`, `noncentralChiSquared_tail_mono` — the upper
  tail is at least the central one, and increases with the noncentrality parameter.
* `weakConverges_chiSquared_standardized`,
  `tendsto_chiSquared_quantile_standardized`,
  `weakConverges_noncentralChiSquared_standardized` — the large-`k` normalisations:
  `(χ²_k − k)/√(2k) ⇝ N(0,1)`, the matching convergence of standardised upper quantiles,
  and the noncentral version with a drift.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 16 (Testing Goodness of
Fit), §16.3 (Pearson's Chi-Squared Statistic), supporting material for Lemma 16.3.1: the
noncentral chi-squared distribution and its tail function. (`TSH4 §16.3 Lem 16.3.1`.)

**Proof formalization notes.**
* Edge cases of the definition. For `k = 0` the ambient space is a single point, so
  `noncentralChiSquared 0 λ = δ₀` for every `λ`; the bridge to the library's central
  `chiSquared` therefore requires `0 < k` (the library's `chiSquared 0` is the degenerate
  `Gamma(0, 1/2)`, not `δ₀`). The mean vector is built by an `if (i : ℕ) = 0` test rather
  than `EuclideanSpace.single`, so that no inhabitant of `Fin k` is needed and `k = 0`
  elaborates.
* The covariance is the identity matrix `(1 : Matrix (Fin k) (Fin k) ℝ)`, which is positive
  semidefinite, so the degenerate `multivariateGaussian` branch is never taken.
* `noncentralChiSquared_zero` reduces, via `multivariateGaussian_zero_one`, to the
  library's exact sum-of-squares law for i.i.d. standard normals.
* Tail comparison with the central law is the set form of Anderson's inequality
  (`AsymptoticStatistics.anderson_lemma_set` in the asymptotics area): closed balls are
  convex and symmetric, so shifting the Gaussian away from the origin can only decrease the
  ball probability, i.e. only increase the complementary upper tail.
* Full monotonicity in `λ` is *not* a direct corollary of that set form (which compares a
  shift with no shift). The route is a one-dimensional reduction: by direction invariance
  and independence of the coordinates, `χ²_k(h²)` is the law of `(Z₁ + h)² + W` with `W`
  independent of `Z₁`; conditionally on `W`, the map `h ↦ P((Z₁ + h)² ≤ s)` is
  nonincreasing in `|h|` because the standard normal density is symmetric and unimodal and
  `{z : z² ≤ s}` is a symmetric interval. Integrating over `W` gives the claim.
* Large-`k` statements use the project's measure-level weak-convergence predicate
  `AsymptoticStatistics.WeakConverges` (indexed by the degrees of freedom, which is the
  quantity going to infinity here); no random-variable representation is needed. Junk
  values at `k = 0` are irrelevant to an `atTop` statement.
* In the quantile statement the upper-`α` quantiles `c k` and `z` are supplied as data
  together with their defining tail identities, rather than through a quantile
  construction; `α ∈ (0,1)` is then forced by those identities and is not assumed.

**Bibliographic comments.** The noncentral chi-squared distribution appears in R. A. Fisher,
"The general sampling distribution of the multiple correlation coefficient," *Proc. Roy.
Soc. A* **121** (1928), 654–673; its systematic study and tabulation are due to
P. B. Patnaik, "The non-central χ²- and F-distributions and their applications,"
*Biometrika* **36** (1949), 202–232. The role of the central chi-squared law in
goodness-of-fit testing originates with K. Pearson, "On the criterion that a given system
of deviations from the probable in the case of a correlated system of variables is such
that it can be reasonably supposed to have arisen from random sampling," *Phil. Mag.* **50**
(1900), 157–175. The monotonicity of the tail in the noncentrality parameter rests on
T. W. Anderson, "The integral of a symmetric unimodal function over a symmetric convex set
and some probability inequalities," *Proc. Amer. Math. Soc.* **6** (1955), 170–176.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix MatrixOrder

namespace StatLean.HypothesisTesting

/-- The mean vector used to define the noncentral chi-squared law: the vector of squared
length `l` supported on the first coordinate. For `k = 0` this is the unique point of the
zero-dimensional space. -/
noncomputable def noncentralMean (k : ℕ) (l : ℝ≥0) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun i => if (i : ℕ) = 0 then Real.sqrt (l : ℝ) else 0

/-- The **noncentral chi-squared distribution** with `k` degrees of freedom and
noncentrality parameter `l`: the law of `‖Z‖²` for `Z ∼ N(μ, I_k)` with `‖μ‖² = l`.

Edge behaviour: for `k = 0` the ambient space is a point and the law is `δ₀` for every `l`;
for `l = 0` it is the central chi-squared law (`noncentralChiSquared_zero`, for `0 < k`). -/
noncomputable def noncentralChiSquared (k : ℕ) (l : ℝ≥0) : Measure ℝ :=
  (multivariateGaussian (noncentralMean k l) 1).map fun z => ‖z‖ ^ 2

/-- With unit covariance, `multivariateGaussian` is a translate of the standard Gaussian. -/
private lemma multivariateGaussian_one_eq_map_add {k : ℕ}
    (v : EuclideanSpace ℝ (Fin k)) :
    multivariateGaussian v 1
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => v + x) := by
  rw [multivariateGaussian]
  simp only [CFC.sqrt_one, map_one, ContinuousLinearMap.one_apply]

/-- The mean vector vanishes when the noncentrality parameter is `0`. -/
@[simp] private lemma noncentralMean_zero {k : ℕ} : noncentralMean k (0 : ℝ≥0) = 0 := by
  ext i
  simp [noncentralMean]

/-- The mean vector has the prescribed length `√l` (when there is at least one coordinate). -/
private lemma noncentralMean_norm {k : ℕ} (hk : 0 < k) (l : ℝ≥0) :
    ‖noncentralMean k l‖ = Real.sqrt (l : ℝ) := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have h2 : ‖noncentralMean k l‖ ^ 2 = (l : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hval : ∀ i : Fin k,
        (noncentralMean k l i) ^ 2 = if i = 0 then (l : ℝ) else 0 := by
      intro i
      by_cases hi : i = 0
      · simp only [noncentralMean, hi, Fin.val_zero, if_pos, if_true]
        rw [Real.sq_sqrt l.coe_nonneg]
      · have hi' : (i : ℕ) ≠ 0 := by simpa [Fin.val_eq_zero_iff] using hi
        simp [noncentralMean, hi, hi']
    simp_rw [hval]
    simp [Finset.sum_ite_eq']
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-- Direction-invariance core: translating the standard Gaussian by mean vectors of equal
length gives the same squared-norm law. Proved with the reflection that swaps the means. -/
private lemma map_normSq_stdGaussian_add_congr {k : ℕ}
    {v w : EuclideanSpace ℝ (Fin k)} (h : ‖v‖ = ‖w‖) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => ‖v + x‖ ^ 2)
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => ‖w + x‖ ^ 2) := by
  obtain ⟨f, hf⟩ : ∃ f : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k), f v = w :=
    ⟨_, Submodule.reflection_sub h⟩
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin k))).map (f : _ → _)
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := stdGaussian_map f
  symm
  calc (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => ‖w + x‖ ^ 2)
      = ((stdGaussian (EuclideanSpace ℝ (Fin k))).map (f : _ → _)).map
          (fun x => ‖w + x‖ ^ 2) := by rw [hmap]
    _ = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun y => ‖w + f y‖ ^ 2) := by
          rw [Measure.map_map (by fun_prop)
            (LinearIsometryEquiv.continuous f).measurable]; rfl
    _ = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun y => ‖v + y‖ ^ 2) := by
          have hfun : (fun y => ‖w + f y‖ ^ 2)
              = (fun y : EuclideanSpace ℝ (Fin k) => ‖v + y‖ ^ 2) := by
            funext y
            rw [← hf, ← map_add, LinearIsometryEquiv.norm_map]
          rw [hfun]

/-- The noncentral chi-squared law is a probability measure: it is the pushforward of a
Gaussian (hence probability) measure under a continuous map. -/
instance isProbabilityMeasure_noncentralChiSquared (k : ℕ) (l : ℝ≥0) :
    IsProbabilityMeasure (noncentralChiSquared k l) := by
  rw [noncentralChiSquared]
  exact Measure.isProbabilityMeasure_map
    (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 2).aemeasurable

/-- **Direction invariance.** Any Gaussian mean vector whose norm is `√l` yields the same
squared-norm law, so the noncentrality parameter `l = ‖μ‖²` is a complete invariant. Follows
from the orthogonal invariance of the standard Gaussian on `EuclideanSpace ℝ (Fin k)`. -/
theorem map_normSq_multivariateGaussian_of_norm_eq (k : ℕ) (l : ℝ≥0)
    {v : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: the mean vector has the prescribed length.
    (hv : ‖v‖ = Real.sqrt (l : ℝ)) :
    (multivariateGaussian v 1).map (fun z => ‖z‖ ^ 2) = noncentralChiSquared k l := by
  have hnorm : ‖v‖ = ‖noncentralMean k l‖ := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [Subsingleton.elim v (noncentralMean 0 l)]
    · rw [hv, noncentralMean_norm hk]
  rw [noncentralChiSquared, multivariateGaussian_one_eq_map_add,
    multivariateGaussian_one_eq_map_add,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def]
  exact map_normSq_stdGaussian_add_congr hnorm

/-- **Zero noncentrality is the central chi-squared law.** For `0 < k`,
`χ²_k(0) = χ²_k`. Via `multivariateGaussian_zero_one` the Gaussian becomes standard, its
coordinates are i.i.d. `N(0,1)`, and `‖z‖² = ∑ᵢ zᵢ²` has the central chi-squared law by the
library's sum-of-squares theorem. -/
theorem noncentralChiSquared_zero {k : ℕ}
    -- USER-INPUT: at least one degree of freedom (`chiSquared 0` is degenerate).
    (hk : 0 < k) :
    noncentralChiSquared k 0 = StatLean.MultipleTesting.chiSquared k := by
  haveI : NeZero k := ⟨hk.ne'⟩
  rw [noncentralChiSquared, noncentralMean_zero, multivariateGaussian_zero_one,
    ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : ((fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 2) ∘ (WithLp.toLp 2))
      = (fun x : Fin k → ℝ => ∑ i, (x i) ^ 2) := by
    funext x
    simp only [Function.comp_apply, EuclideanSpace.real_norm_sq_eq]
  rw [hfun]
  exact StatLean.MultipleTesting.map_sum_sq_eq_chiSquared hk
    (Measure.pi fun _ => gaussianReal 0 1)
    (fun i x => x i) (fun i => measurable_pi_apply i)
    (fun i => (measurePreserving_eval _ i).map_eq)
    (iIndepFun_pi (fun _ => aemeasurable_id))

/-- **The Gaussian ↔ chi-squared bridge (noncentral case).** For a positive-definite
covariance `S` and any mean `μ`, the Gaussian quadratic form `z ↦ ⟪z, S⁻¹ z⟫` pushes
`N(μ, S)` forward to the noncentral chi-squared law with `k` degrees of freedom and
noncentrality parameter `⟪μ, S⁻¹ μ⟫`.

Proof by whitening. With `A = (√S)⁻¹` (the inverse of the positive-definite matrix square
root) one has `A · S · Aᴴ = I` and `A · A = S⁻¹`, so
`(N(μ, S)).map A = N(Aμ, I)` (`multivariateGaussian_map_toEuclideanCLM`), while
`⟪z, S⁻¹ z⟫ = ‖A z‖²` because `A` is self-adjoint and `A² = S⁻¹`. Pushing the squared norm
through the whitened Gaussian `N(Aμ, I)` gives `noncentralChiSquared k ‖Aμ‖²`, and
`‖Aμ‖² = ⟪μ, S⁻¹ μ⟫`, whose `toNNReal` is the stated noncentrality. -/
theorem multivariateGaussian_map_inner_inv_eq_noncentralChiSquared {k : ℕ}
    {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) (μ : EuclideanSpace ℝ (Fin k)) :
    (multivariateGaussian μ S).map
        (fun z => ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ z⟫)
      = noncentralChiSquared k
          (⟪μ, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ μ⟫).toNNReal := by
  classical
  -- The whitening matrix `A = (√S)⁻¹`.
  set B : Matrix (Fin k) (Fin k) ℝ := CFC.sqrt S with hB_def
  have hB_sa : IsSelfAdjoint B := by rw [hB_def]; exact (CFC.sqrt_nonneg S).isSelfAdjoint
  have hBB : B * B = S := by rw [hB_def]; exact CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hB_unit : IsUnit B := by rw [hB_def]; exact hS.isStrictlyPositive.sqrt.isUnit
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB_unit
  have hBl : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBdet
  have hBr : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBdet
  set A : Matrix (Fin k) (Fin k) ℝ := B⁻¹ with hA_def
  -- `A` is self-adjoint.
  have hA_sa : IsSelfAdjoint A := by
    show star A = A
    rw [hA_def, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv,
      ← Matrix.star_eq_conjTranspose, hB_sa]
  have hAH : Aᴴ = A := by rw [← Matrix.star_eq_conjTranspose]; exact hA_sa
  -- `A · A = S⁻¹`.
  have hAA : A * A = S⁻¹ := by rw [hA_def, ← Matrix.mul_inv_rev, hBB]
  -- `A · S · Aᴴ = I`.
  have hASA : A * S * Aᴴ = 1 := by
    rw [hAH, hA_def, ← hBB, Matrix.mul_assoc, Matrix.mul_assoc, hBr, Matrix.mul_one, hBl]
  -- `Aᵀ = A` for the real self-adjoint whitening matrix.
  have hAt : Aᵀ = A := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose]
    exact hA_sa
  -- Pointwise: `‖A z‖² = ⟪z, S⁻¹ z⟫`, via `inner_toEuclideanCLM` and matrix algebra.
  have hnorm : ∀ z : EuclideanSpace ℝ (Fin k),
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A z‖ ^ 2
        = ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ z⟫ := by
    intro z
    rw [sq, ← real_inner_self_eq_norm_mul_norm, Matrix.inner_toEuclideanCLM,
      Matrix.inner_toEuclideanCLM]
    show (A *ᵥ z) ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ S⁻¹ *ᵥ z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hAt, hAA,
      dotProduct_comm]
  -- Assemble via the whitening pushforward and the squared-norm law of `N(Aμ, I)`.
  have hqnn : 0 ≤ ⟪μ, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ μ⟫ := by
    rw [← hnorm μ]; positivity
  have hv : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A μ‖
      = Real.sqrt ((⟪μ, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ μ⟫).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ hqnn, ← hnorm μ, Real.sqrt_sq (norm_nonneg _)]
  have hcomp :
      (fun z : EuclideanSpace ℝ (Fin k) => ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ z⟫)
        = (fun w => ‖w‖ ^ 2) ∘ (Matrix.toEuclideanCLM (𝕜 := ℝ) A) := by
    funext z; simp only [Function.comp_apply]; exact (hnorm z).symm
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    multivariateGaussian_map_toEuclideanCLM A μ hS.posSemidef, hASA]
  exact map_normSq_multivariateGaussian_of_norm_eq k _ hv

/-- **The Gaussian ↔ chi-squared bridge (central case).** For a positive-definite covariance
`S` (with `0 < k`), the Gaussian quadratic form `z ↦ ⟪z, S⁻¹ z⟫` pushes the centred Gaussian
`N(0, S)` forward to the central chi-squared law `χ²_k`. The exact distributional identity
`Zᵀ S⁻¹ Z ∼ χ²_k` for `Z ∼ N(0, S)`, the `μ = 0` specialisation of
`multivariateGaussian_map_inner_inv_eq_noncentralChiSquared`. -/
theorem multivariateGaussian_map_inner_inv_eq_chiSquared {k : ℕ} (hk : 0 < k)
    {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S).map
        (fun z => ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ z⟫)
      = StatLean.MultipleTesting.chiSquared k := by
  rw [multivariateGaussian_map_inner_inv_eq_noncentralChiSquared hS 0,
    show (⟪(0 : EuclideanSpace ℝ (Fin k)), Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ 0⟫).toNNReal
        = 0 from by rw [inner_zero_left]; simp]
  exact noncentralChiSquared_zero hk

/-- The upper tail of `noncentralChiSquared` as a standard-Gaussian ball-complement measure. -/
private lemma noncentralChiSquared_Ioi_eq {k : ℕ} (l : ℝ≥0) (t : ℝ) :
    noncentralChiSquared k l (Set.Ioi t)
      = stdGaussian (EuclideanSpace ℝ (Fin k))
          {x | t < ‖noncentralMean k l + x‖ ^ 2} := by
  rw [noncentralChiSquared, multivariateGaussian_one_eq_map_add,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) measurableSet_Ioi]
  rfl

/-- **The noncentral upper tail dominates the central one.** Direct consequence of the set
form of Anderson's inequality applied to the closed ball `{z : ‖z‖² ≤ t}`, which is convex
and symmetric: shifting the mean can only decrease its probability. -/
theorem chiSquared_tail_le_noncentralChiSquared {k : ℕ}
    -- USER-INPUT: at least one degree of freedom (`chiSquared 0` is degenerate).
    (hk : 0 < k) (l : ℝ≥0) (t : ℝ) :
    (StatLean.MultipleTesting.chiSquared k) (Set.Ioi t)
      ≤ (noncentralChiSquared k l) (Set.Ioi t) := by
  rw [← noncentralChiSquared_zero hk, noncentralChiSquared_Ioi_eq,
    noncentralChiSquared_Ioi_eq, noncentralMean_zero]
  set E := EuclideanSpace ℝ (Fin k)
  set μ := stdGaussian E
  -- the closed ball `C = {z : ‖z‖² ≤ t}`, convex and symmetric
  set C : Set E := {z | ‖z‖ ^ 2 ≤ t} with hC
  have hCmeas : MeasurableSet C := by
    have : Measurable fun z : E => ‖z‖ ^ 2 := by fun_prop
    exact measurableSet_le this measurable_const
  have hCconv : Convex ℝ C := by
    by_cases ht : (0 : ℝ) ≤ t
    · have hset : C = Metric.closedBall (0 : E) (Real.sqrt t) := by
        ext z
        simp only [hC, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
        constructor
        · intro h
          rw [← Real.sqrt_sq (norm_nonneg z)]
          exact Real.sqrt_le_sqrt h
        · intro h
          have hmul := mul_self_le_mul_self (norm_nonneg z) h
          rw [Real.mul_self_sqrt ht] at hmul
          rw [pow_two]; exact hmul
      rw [hset]; exact convex_closedBall _ _
    · have ht' : t < 0 := not_le.mp ht
      have hset : C = (∅ : Set E) := by
        ext z
        simp only [hC, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact lt_of_lt_of_le ht' (sq_nonneg _)
      rw [hset]; exact convex_empty
  have hCsymm : ∀ z ∈ C, -z ∈ C := by
    intro z hz; simpa [hC] using hz
  -- both tails are complements of `{· ∈ C}` events under the standard Gaussian
  have hmeasA : MeasurableSet {x : E | ‖(0 : E) + x‖ ^ 2 ≤ t} := by
    have : Measurable fun x : E => ‖(0 : E) + x‖ ^ 2 := by fun_prop
    exact measurableSet_le this measurable_const
  have hmeasB : MeasurableSet {x : E | ‖noncentralMean k l + x‖ ^ 2 ≤ t} := by
    have : Measurable fun x : E => ‖noncentralMean k l + x‖ ^ 2 := by fun_prop
    exact measurableSet_le this measurable_const
  have key : μ {x | noncentralMean k l + x ∈ C} ≤ μ C := by
    have hand := AsymptoticStatistics.anderson_lemma_set_stdGaussian hCmeas hCconv hCsymm
      (noncentralMean k l)
    rwa [show {x : E | x + noncentralMean k l ∈ C}
        = {x : E | noncentralMean k l + x ∈ C} from by
      ext x; simp only [Set.mem_setOf_eq]; rw [add_comm]] at hand
  have hCeq : {x : E | (0 : E) + x ∈ C} = {x : E | ‖(0 : E) + x‖ ^ 2 ≤ t} := rfl
  have hBeq : {x : E | noncentralMean k l + x ∈ C}
      = {x : E | ‖noncentralMean k l + x‖ ^ 2 ≤ t} := rfl
  have hEA : {x : E | t < ‖(0 : E) + x‖ ^ 2} = {x : E | ‖(0 : E) + x‖ ^ 2 ≤ t}ᶜ := by
    ext x; simp [not_le]
  have hEB : {x : E | t < ‖noncentralMean k l + x‖ ^ 2}
      = {x : E | ‖noncentralMean k l + x‖ ^ 2 ≤ t}ᶜ := by
    ext x; simp [not_le]
  rw [hEA, hEB, measure_compl hmeasA (measure_ne_top _ _),
    measure_compl hmeasB (measure_ne_top _ _)]
  have key' : μ {x | ‖noncentralMean k l + x‖ ^ 2 ≤ t} ≤ μ {x | ‖(0 : E) + x‖ ^ 2 ≤ t} := by
    have h0 : μ {x | (0 : E) + x ∈ C} = μ C := by
      simp
    rw [← hBeq, ← hCeq]
    calc μ {x | noncentralMean k l + x ∈ C} ≤ μ C := key
      _ = μ {x | (0 : E) + x ∈ C} := h0.symm
  exact tsub_le_tsub_left key' _

/-! ### Anderson's inequality in its *scaled* (shrink-shift) form

`AsymptoticStatistics.anderson_lemma_set_stdGaussian` supplies only the `a = 0` endpoint
`μ(C − y) ≤ μ(C)` of Anderson's inequality; the shrink monotonicity `μ(C − y) ≤ μ(C − c·y)`
for `0 ≤ c ≤ 1` is *not* a corollary of it (the intermediate set `C − c·y` is no longer
symmetric). It is, however, the *same* Prékopa–Leindler argument run with **unequal weights**
`t = (1+c)/2` and `1 − t` instead of the symmetric `½`-midpoint: for `u + y ∈ C` and
`v − y ∈ C`,
`t • u + (1−t) • v + c • y = t • (u + y) + (1−t) • (v − y) ∈ C`,
so PL gives `ν(C−y)^t · ν(C+y)^{1−t} ≤ ν(C − c·y)`, and `ν(C+y) = ν(C−y)` by the reflection
symmetry of the Gaussian and of `C`. This section develops that general-weight variant (the
`t = 1/2` case is `AsymptoticStatistics._pl_anderson_pi_general`, which is `private` there and
in any case not general enough). -/

section AndersonScaled

open AsymptoticStatistics

variable {ι : Type*} [Fintype ι]

/-- **General-weight log-concavity of the standard 1-D Gaussian density.** For `0 ≤ t ≤ 1`,
`φ(x)^t · φ(y)^{1−t} ≤ φ(t x + (1−t) y)`. Equivalent to convexity of `x ↦ x²`; the
`t = 1/2` case is `AsymptoticStatistics.gaussianPDFReal_one_log_concave`. -/
private lemma gaussianPDFReal_log_concave_gen {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x y : ℝ) :
    gaussianPDFReal 0 1 x ^ t * gaussianPDFReal 0 1 y ^ (1 - t)
      ≤ gaussianPDFReal 0 1 (t * x + (1 - t) * y) := by
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  set c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ with hc_def
  have hc : 0 < c := by rw [hc_def]; positivity
  have hcc : c ^ t * c ^ (1 - t) = c := by
    rw [← Real.rpow_add hc]; norm_num
  have hkey : Real.exp (-x ^ 2 / 2) ^ t * Real.exp (-y ^ 2 / 2) ^ (1 - t)
      ≤ Real.exp (-(t * x + (1 - t) * y) ^ 2 / 2) := by
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (sq_nonneg (x - y))]
  calc (c * Real.exp (-x ^ 2 / 2)) ^ t * (c * Real.exp (-y ^ 2 / 2)) ^ (1 - t)
      = c ^ t * c ^ (1 - t)
          * (Real.exp (-x ^ 2 / 2) ^ t * Real.exp (-y ^ 2 / 2) ^ (1 - t)) := by
        rw [Real.mul_rpow hc.le (Real.exp_pos _).le,
          Real.mul_rpow hc.le (Real.exp_pos _).le]
        ring
    _ = c * (Real.exp (-x ^ 2 / 2) ^ t * Real.exp (-y ^ 2 / 2) ^ (1 - t)) := by rw [hcc]
    _ ≤ c * Real.exp (-(t * x + (1 - t) * y) ^ 2 / 2) := by
        exact mul_le_mul_of_nonneg_left hkey hc.le

/-- `ENNReal` form of `gaussianPDFReal_log_concave_gen`. -/
private lemma gaussianPDF_log_concave_gen {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x y : ℝ) :
    gaussianPDF 0 1 x ^ t * gaussianPDF 0 1 y ^ (1 - t)
      ≤ gaussianPDF 0 1 (t * x + (1 - t) * y) := by
  simp_rw [gaussianPDF_def]
  rw [ENNReal.ofReal_rpow_of_nonneg (gaussianPDFReal_nonneg _ _ _) ht0,
    ENNReal.ofReal_rpow_of_nonneg (gaussianPDFReal_nonneg _ _ _) (by linarith),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (gaussianPDFReal_nonneg _ _ _) t)]
  exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_log_concave_gen ht0 ht1 x y)

/-- Product (Pi) form of the general-weight Gaussian log-concavity. -/
private lemma gaussianPDF_pi_log_concave_gen {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (u v : ι → ℝ) :
    (∏ i, gaussianPDF 0 1 (u i)) ^ t * (∏ i, gaussianPDF 0 1 (v i)) ^ (1 - t)
      ≤ ∏ i, gaussianPDF 0 1 ((t • u + (1 - t) • v) i) := by
  have hcoord : ∀ i : ι, (t • u + (1 - t) • v) i = t * u i + (1 - t) * v i := by
    intro i; simp
  simp only [hcoord]
  rw [← ENNReal.prod_rpow_of_nonneg ht0,
    ← ENNReal.prod_rpow_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t), ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod' fun i _ => gaussianPDF_log_concave_gen ht0 ht1 (u i) (v i)

/-- **Generalised (unequal-weight) PL–Anderson on `Measure.pi (gaussianReal 0 1)`.**
If the `t`-weighted Minkowski combination of `A` and `B` lands in `K`, and `A`, `B` have the
same Gaussian mass, then that common mass is at most the mass of `K`. -/
private lemma pl_anderson_pi_gen {A B K : Set (ι → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hK : MeasurableSet K)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hmean : ∀ u ∈ A, ∀ v ∈ B, t • u + (1 - t) • v ∈ K)
    (hsymm : (Measure.pi fun _ : ι => gaussianReal 0 1) B
      = (Measure.pi fun _ : ι => gaussianReal 0 1) A) :
    (Measure.pi fun _ : ι => gaussianReal 0 1) A
      ≤ (Measure.pi fun _ : ι => gaussianReal 0 1) K := by
  set ν := Measure.pi (fun _ : ι => gaussianReal 0 1) with hν_def
  set ρ : (ι → ℝ) → ℝ≥0∞ := fun x => ∏ i, gaussianPDF 0 1 (x i) with hρ_def
  have hρ_meas : Measurable ρ :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  have hν_set : ∀ S : Set (ι → ℝ), MeasurableSet S →
      ν S = ∫⁻ x, S.indicator ρ x ∂volume := by
    intro S hS
    rw [hν_def, pi_gaussianReal_eq_withDensity, withDensity_apply _ hS, ← lintegral_indicator hS]
  have hPL : (∫⁻ x, A.indicator ρ x ∂volume) ^ t * (∫⁻ x, B.indicator ρ x ∂volume) ^ (1 - t)
      ≤ ∫⁻ z, K.indicator ρ z ∂volume := by
    refine prekopaLeindler (hρ_meas.indicator hA) (hρ_meas.indicator hB)
      (hρ_meas.indicator hK) ht0 ht1 ?_
    intro u v
    by_cases hu : u ∈ A
    · by_cases hv : v ∈ B
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hv,
          Set.indicator_of_mem (hmean u hu v hv), hρ_def]
        exact gaussianPDF_pi_log_concave_gen ht0.le ht1.le u v
      · rw [Set.indicator_of_notMem hv, ENNReal.zero_rpow_of_pos (by linarith), mul_zero]
        exact zero_le
    · rw [Set.indicator_of_notMem hu, ENNReal.zero_rpow_of_pos ht0, zero_mul]
      exact zero_le
  rw [← hν_set A hA, ← hν_set B hB, ← hν_set K hK, hsymm,
    ← ENNReal.rpow_add_of_nonneg _ _ ht0.le (by linarith : (0 : ℝ) ≤ 1 - t),
    show t + (1 - t) = (1 : ℝ) from by ring, ENNReal.rpow_one] at hPL
  exact hPL

/-- **Scaled Anderson on `Measure.pi (gaussianReal 0 1)`.** For convex symmetric `C` and
`0 ≤ c ≤ 1`, shrinking the shift increases the mass: `ν(C − y) ≤ ν(C − c·y)`. -/
private lemma pi_gaussian_shift_antitone {C : Set (ι → ℝ)} (hC : MeasurableSet C)
    (hconv : Convex ℝ C) (hCsymm : ∀ x ∈ C, -x ∈ C) (y : ι → ℝ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (Measure.pi fun _ : ι => gaussianReal 0 1) {x | x + y ∈ C}
      ≤ (Measure.pi fun _ : ι => gaussianReal 0 1) {x | x + c • y ∈ C} := by
  rcases eq_or_lt_of_le hc1 with hc | hclt
  · rw [hc, one_smul]
  -- the weight `t = (1+c)/2 ∈ (0,1)` produces exactly the residual shift `2t − 1 = c`
  set t : ℝ := (1 + c) / 2 with ht_def
  have ht0 : 0 < t := by rw [ht_def]; linarith
  have ht1 : t < 1 := by rw [ht_def]; linarith
  have hct : c = 2 * t - 1 := by rw [ht_def]; ring
  have hmA : MeasurableSet {x : ι → ℝ | x + y ∈ C} := (measurable_id.add_const y) hC
  have hmB : MeasurableSet {x : ι → ℝ | x + -y ∈ C} := (measurable_id.add_const (-y)) hC
  have hmK : MeasurableSet {x : ι → ℝ | x + c • y ∈ C} := (measurable_id.add_const (c • y)) hC
  refine pl_anderson_pi_gen hmA hmB hmK ht0 ht1 ?_ ?_
  · intro u hu v hv
    have hmem : t • (u + y) + (1 - t) • (v + -y) ∈ C :=
      hconv hu hv ht0.le (by linarith) (by ring)
    have hid : t • (u + y) + (1 - t) • (v + -y) = t • u + (1 - t) • v + c • y := by
      rw [hct]; module
    rwa [hid] at hmem
  · -- reflection symmetry: `{x | x − y ∈ C} = (fun x => −x) ⁻¹' {x | x + y ∈ C}`
    have hpre : {x : ι → ℝ | x + -y ∈ C} = (fun x : ι → ℝ => -x) ⁻¹' {x | x + y ∈ C} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · intro hx
        have := hCsymm _ hx
        rwa [show -(x + -y) = -x + y from by ring] at this
      · intro hx
        have := hCsymm _ hx
        rwa [show -(-x + y) = x + -y from by ring] at this
    rw [hpre, ← Measure.map_apply measurable_neg hmA, pi_gaussianReal_neg_invariant]

/-- **Scaled Anderson for the standard Gaussian on `EuclideanSpace`.** For a convex symmetric
measurable `C` and `0 ≤ c ≤ 1`, `μ(C − y) ≤ μ(C − c·y)`: shrinking the shift towards the
origin can only increase the mass. The `c = 0` case is
`AsymptoticStatistics.anderson_lemma_set_stdGaussian`. -/
private lemma stdGaussian_shift_antitone {C : Set (EuclideanSpace ℝ ι)}
    (hC : MeasurableSet C) (hconv : Convex ℝ C) (hCsymm : ∀ x ∈ C, -x ∈ C)
    (y : EuclideanSpace ℝ ι) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    stdGaussian (EuclideanSpace ℝ ι) {x | x + y ∈ C}
      ≤ stdGaussian (EuclideanSpace ℝ ι) {x | x + c • y ∈ C} := by
  rw [← map_pi_eq_stdGaussian]
  set e : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm with he_def
  have h_toLp_eq : (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) = e := rfl
  rw [h_toLp_eq]
  have h_e_meas : Measurable e := e.toLinearMap.continuous_of_finiteDimensional.measurable
  have hmA : MeasurableSet {x : EuclideanSpace ℝ ι | x + y ∈ C} :=
    (measurable_id.add_const y) hC
  have hmK : MeasurableSet {x : EuclideanSpace ℝ ι | x + c • y ∈ C} :=
    (measurable_id.add_const (c • y)) hC
  rw [Measure.map_apply h_e_meas hmA, Measure.map_apply h_e_meas hmK]
  have hpreA : (e : (ι → ℝ) → EuclideanSpace ℝ ι) ⁻¹' {x | x + y ∈ C}
      = {u | u + e.symm y ∈ e ⁻¹' C} := by
    ext u
    change e u + y ∈ C ↔ e (u + e.symm y) ∈ C
    rw [map_add, e.apply_symm_apply]
  have hpreK : (e : (ι → ℝ) → EuclideanSpace ℝ ι) ⁻¹' {x | x + c • y ∈ C}
      = {u | u + c • e.symm y ∈ e ⁻¹' C} := by
    ext u
    change e u + c • y ∈ C ↔ e (u + c • e.symm y) ∈ C
    rw [map_add, map_smul, e.apply_symm_apply]
  rw [hpreA, hpreK]
  exact pi_gaussian_shift_antitone (h_e_meas hC) (hconv.linear_preimage e.toLinearMap)
    (fun u hu => by rw [Set.mem_preimage, map_neg]; exact hCsymm _ hu) _ hc0 hc1

end AndersonScaled

/-- The closed "ball" `{z | ‖z‖² ≤ t}` is measurable, convex and symmetric (it is empty for
`t < 0` and the closed ball of radius `√t` otherwise). -/
private lemma normSq_le_isConvexSymm {ι : Type*} [Fintype ι] (t : ℝ) :
    MeasurableSet {z : EuclideanSpace ℝ ι | ‖z‖ ^ 2 ≤ t}
      ∧ Convex ℝ {z : EuclideanSpace ℝ ι | ‖z‖ ^ 2 ≤ t}
      ∧ ∀ z ∈ {z : EuclideanSpace ℝ ι | ‖z‖ ^ 2 ≤ t}, -z ∈ {z | ‖z‖ ^ 2 ≤ t} := by
  refine ⟨measurableSet_le (by fun_prop) measurable_const, ?_, fun z hz => by simpa using hz⟩
  by_cases ht : (0 : ℝ) ≤ t
  · have hset : {z : EuclideanSpace ℝ ι | ‖z‖ ^ 2 ≤ t}
        = Metric.closedBall (0 : EuclideanSpace ℝ ι) (Real.sqrt t) := by
      ext z
      simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
      constructor
      · intro h
        rw [← Real.sqrt_sq (norm_nonneg z)]
        exact Real.sqrt_le_sqrt h
      · intro h
        have hmul := mul_self_le_mul_self (norm_nonneg z) h
        rw [Real.mul_self_sqrt ht] at hmul
        rw [pow_two]; exact hmul
    rw [hset]; exact convex_closedBall _ _
  · have hset : {z : EuclideanSpace ℝ ι | ‖z‖ ^ 2 ≤ t} = (∅ : Set (EuclideanSpace ℝ ι)) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (not_le.mp ht) (sq_nonneg _)
    rw [hset]; exact convex_empty

/-- **Anderson shrink-shift monotonicity for the standard-Gaussian ball measure.**
For the convex symmetric closed ball `{z | ‖z‖² ≤ t}`, shifting its centre further from the
origin along the first axis can only decrease the standard-Gaussian mass:
`ℓ ↦ μ{x | ‖√ℓ·e₁ + x‖² ≤ t}` is nonincreasing.

This is Anderson's inequality in its *scaled* form `μ(C − y) ≤ μ(C − c·y)`, `0 ≤ c ≤ 1`,
proved in `stdGaussian_shift_antitone` by the unequal-weight Prékopa–Leindler argument (see
the section header above); here `y = √ℓ₂·e₁` and `c = √ℓ₁/√ℓ₂`, so that `c·y = √ℓ₁·e₁`. -/
private lemma stdGaussian_normSq_le_antitone {k : ℕ} (t : ℝ) {l₁ l₂ : ℝ≥0} (h : l₁ ≤ l₂) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))) {x | ‖noncentralMean k l₂ + x‖ ^ 2 ≤ t}
      ≤ (stdGaussian (EuclideanSpace ℝ (Fin k))) {x | ‖noncentralMean k l₁ + x‖ ^ 2 ≤ t} := by
  obtain ⟨hCmeas, hCconv, hCsymm⟩ := normSq_le_isConvexSymm (ι := Fin k) t
  rcases eq_or_lt_of_le (zero_le (a := l₂)) with hl2 | hl2
  · -- degenerate case `l₂ = 0`, hence `l₁ = 0`
    have hl1 : l₁ = 0 := le_antisymm (hl2 ▸ h) (zero_le)
    rw [hl1, ← hl2]
  · have hs2 : 0 < Real.sqrt (l₂ : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hl2)
    set c : ℝ := Real.sqrt (l₁ : ℝ) / Real.sqrt (l₂ : ℝ) with hc_def
    have hc0 : 0 ≤ c := by rw [hc_def]; positivity
    have hc1 : c ≤ 1 := by
      rw [hc_def, div_le_one hs2]
      exact Real.sqrt_le_sqrt (by exact_mod_cast h)
    have hscale : c • noncentralMean k l₂ = noncentralMean k l₁ := by
      have hmul : c * Real.sqrt (l₂ : ℝ) = Real.sqrt (l₁ : ℝ) := by
        rw [hc_def]; field_simp
      ext i
      by_cases hi : (i : ℕ) = 0
      · simp [noncentralMean, hi, hmul]
      · simp [noncentralMean, hi]
    have hkey := stdGaussian_shift_antitone hCmeas hCconv hCsymm (noncentralMean k l₂) hc0 hc1
    rw [hscale] at hkey
    have hcomm : ∀ l : ℝ≥0,
        {x : EuclideanSpace ℝ (Fin k) | x + noncentralMean k l ∈ {z | ‖z‖ ^ 2 ≤ t}}
          = {x : EuclideanSpace ℝ (Fin k) | ‖noncentralMean k l + x‖ ^ 2 ≤ t} := by
      intro l; ext x; simp only [Set.mem_setOf_eq]; rw [add_comm]
    rwa [hcomm l₂, hcomm l₁] at hkey

/-- **The upper tail increases with the noncentrality parameter.** The noncentral
chi-squared family is stochastically ordered in `l`. Reduces (via `noncentralChiSquared_Ioi_eq`
and complementation of the closed ball) to the scaled Anderson shrink monotonicity
`stdGaussian_normSq_le_antitone`. -/
theorem noncentralChiSquared_tail_mono (k : ℕ) (t : ℝ) :
    Monotone fun l : ℝ≥0 => (noncentralChiSquared k l) (Set.Ioi t) := by
  intro l₁ l₂ h
  show (noncentralChiSquared k l₁) (Set.Ioi t) ≤ (noncentralChiSquared k l₂) (Set.Ioi t)
  rw [noncentralChiSquared_Ioi_eq, noncentralChiSquared_Ioi_eq]
  set E := EuclideanSpace ℝ (Fin k)
  have hmeas : ∀ l : ℝ≥0, MeasurableSet {x : E | ‖noncentralMean k l + x‖ ^ 2 ≤ t} := by
    intro l
    exact measurableSet_le (by fun_prop) measurable_const
  have hcompl : ∀ l : ℝ≥0, {x : E | t < ‖noncentralMean k l + x‖ ^ 2}
      = {x : E | ‖noncentralMean k l + x‖ ^ 2 ≤ t}ᶜ := by
    intro l; ext x; simp [not_le]
  rw [hcompl l₁, hcompl l₂, measure_compl (hmeas l₁) (measure_ne_top _ _),
    measure_compl (hmeas l₂) (measure_ne_top _ _)]
  exact tsub_le_tsub_left (stdGaussian_normSq_le_antitone t h) _

/-- **Central i.i.d. CLT for the standardised sum of squares** (random-variable form).
For any i.i.d. `N(0,1)` sequence `Z`, the standardised partial sum of squares
`(∑_{i<n+1} Zᵢ² − (n+1))/√(2(n+1))` converges in distribution to `N(0,1)`. This is the
`weighted_iid_clt` applied to the mean-zero variance-two increments `Zᵢ² − 1` with unit
weights and scale `√2`; used both for the central and the noncentral large-`k`
normalisations. -/
private lemma tendstoInDistribution_central_standardized {Ω₀ : Type*} [MeasurableSpace Ω₀]
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] (Z : ℕ → Ω₀ → ℝ)
    (hZmeas : ∀ i, Measurable (Z i)) (hZlaw : ∀ i, Measure.map (Z i) P₀ = gaussianReal 0 1)
    (hZindep : iIndepFun Z P₀) :
    TendstoInDistribution
      (fun n (ω : Ω₀) => ((∑ i : Fin (n + 1), (Z (i : ℕ) ω) ^ 2) - ((n + 1 : ℕ) : ℝ))
        / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)))
      atTop (id : ℝ → ℝ) (fun _ => P₀) (gaussianReal 0 1) := by
  classical
  -- mean-zero squared-normal increments `Y i = (Z i)² - 1`
  set Y : ℕ → Ω₀ → ℝ := fun i ω => (Z i ω) ^ 2 - 1 with hY
  have hYmeas : ∀ i, Measurable (Y i) :=
    fun i => ((hZmeas i).pow_const 2).sub measurable_const
  -- the law of a single square is `χ²₁`
  have hsq1 : Measure.map (fun ω => (Z 0 ω) ^ 2) P₀
      = StatLean.MultipleTesting.chiSquared 1 := by
    have h := StatLean.MultipleTesting.map_sum_sq_eq_chiSquared (n := 1) one_pos P₀
      (fun i : Fin 1 => Z (i : ℕ)) (fun i => hZmeas _) (fun i => hZlaw _)
      (hZindep.precomp Fin.val_injective)
    simpa [Fin.sum_univ_one] using h
  -- `L²`-membership of the increments (Gaussian fourth moment is finite)
  have hL2 : MemLp (Y 0) 2 P₀ := by
    haveI : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := ⟨by
      rw [← two_mul, show (4 : ℝ≥0∞) = 2 * 2 from by norm_num,
        ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
    have h4 : MemLp (fun x : ℝ => x) 4 (gaussianReal 0 1) :=
      memLp_id_gaussianReal' (4 : ℝ≥0∞) (by simp)
    have hx2 : MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal 0 1) := by
      have hmul : MemLp (fun x : ℝ => x * x) 2 (gaussianReal 0 1) := h4.mul' h4
      simpa [pow_two] using hmul
    have hg : MemLp (fun x : ℝ => x ^ 2 - 1) 2 (gaussianReal 0 1) :=
      hx2.sub (memLp_const (1 : ℝ))
    rw [← hZlaw 0] at hg
    have := (memLp_map_measure_iff hg.aestronglyMeasurable (hZmeas 0).aemeasurable).mp hg
    simpa [hY, Function.comp] using! this
  -- integrability of `Y 0` and of a single square
  have hiY0 : Integrable (Y 0) P₀ := hL2.integrable one_le_two
  have hi2 : Integrable (fun ω => (Z 0 ω) ^ 2) P₀ := by
    have heq : (fun ω => (Z 0 ω) ^ 2) = fun ω => Y 0 ω + 1 := by funext ω; simp [hY]
    rw [heq]; exact hiY0.add (integrable_const 1)
  -- second moment of the standard normal is `1`
  have hE2 : ∫ ω, (Z 0 ω) ^ 2 ∂ P₀ = 1 := by
    have h := integral_map (μ := P₀) (φ := fun ω => (Z 0 ω) ^ 2)
      ((hZmeas 0).pow_const 2).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
    rw [hsq1, StatLean.MultipleTesting.integral_id_chiSquared one_pos] at h
    simpa using h.symm
  -- mean of the increments is `0`
  have hmean : ∫ ω, Y 0 ω ∂ P₀ = 0 := by
    simp only [hY]
    rw [integral_sub hi2 (integrable_const 1), hE2, integral_const]
    simp
  -- fourth-moment identity: the increments have variance `2`
  have hYsq : ∫ ω, (Y 0 ω) ^ 2 ∂ P₀ = 2 := by
    have h := integral_map (μ := P₀) (φ := fun ω => (Z 0 ω) ^ 2)
      ((hZmeas 0).pow_const 2).aemeasurable (f := fun x : ℝ => (x - 1) ^ 2) (by fun_prop)
    rw [hsq1] at h
    have hv := StatLean.MultipleTesting.variance_chiSquared (k := 1) one_pos
    rw [Nat.cast_one] at hv
    rw [show (fun ω => (Y 0 ω) ^ 2) = fun ω => ((Z 0 ω) ^ 2 - 1) ^ 2 from by
      funext ω; simp [hY]]
    rw [← h, hv]; norm_num
  have hvar : Var[Y 0 ; P₀] = (Real.sqrt 2) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), variance_eq_integral (hYmeas 0).aemeasurable]
    have hmz : P₀[Y 0] = 0 := hmean
    rw [hmz]; simp only [sub_zero]; exact hYsq
  have hσpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- independence and identical distribution of the increments
  have hindep : iIndepFun Y P₀ :=
    hZindep.comp (fun _ : ℕ => fun z : ℝ => z ^ 2 - 1) (fun _ => by fun_prop)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P₀ P₀ := by
    intro i
    have hZid : IdentDistrib (Z i) (Z 0) P₀ P₀ :=
      ⟨(hZmeas i).aemeasurable, (hZmeas 0).aemeasurable,
        (hZlaw i).trans (hZlaw 0).symm⟩
    exact hZid.comp (by fun_prop : Measurable (fun z : ℝ => z ^ 2 - 1))
  -- weight negligibility: the constant unit weights satisfy `1 ≤ ε · (n+1)` eventually
  have hw : ∀ n : ℕ, 0 < ∑ _i : Fin (n + 1), ((1 : ℝ)) ^ 2 := by
    intro n
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    positivity
  have hneg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i : Fin (n + 1), ((1 : ℝ)) ^ 2 ≤ ε * ∑ _j : Fin (n + 1), ((1 : ℝ)) ^ 2 := by
    intro ε hε
    have htend : Tendsto (fun n : ℕ => ε * ((n : ℝ) + 1)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hε
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    filter_upwards [htend.eventually_ge_atTop 1] with n hn i
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    push_cast at hn ⊢
    linarith
  -- the weighted i.i.d. CLT applied to the constant-unit-weight rows, rewritten to clean form
  have hclt := weighted_iid_clt (m := fun n => n + 1) (w := fun _ _ => (1 : ℝ))
    (σ := Real.sqrt 2) (Z := (id : ℝ → ℝ)) hYmeas hindep hident hL2 hmean hσpos hvar hw hneg
    HasLaw.id
  refine hclt.congr (fun n => ?_) Filter.EventuallyEq.rfl
  refine Filter.Eventually.of_forall (fun ω => ?_)
  have e1 : (∑ _i : Fin (n + 1), ((1 : ℝ)) ^ 2) = ((n + 1 : ℕ) : ℝ) := by simp
  have e2 : (∑ i : Fin (n + 1), (1 : ℝ) * Y (i : ℕ) ω)
      = (∑ i : Fin (n + 1), (Z (i : ℕ) ω) ^ 2) - ((n + 1 : ℕ) : ℝ) := by
    simp only [one_mul, hY]
    rw [Finset.sum_sub_distrib]; simp
  show (Real.sqrt 2 * Real.sqrt (∑ _i : Fin (n + 1), ((1 : ℝ)) ^ 2))⁻¹
        * ∑ i : Fin (n + 1), (1 : ℝ) * Y (i : ℕ) ω
      = ((∑ i : Fin (n + 1), (Z (i : ℕ) ω) ^ 2) - ((n + 1 : ℕ) : ℝ))
        / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ))
  rw [e1, e2, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), div_eq_inv_mul]

/-- **The standardised pushforward of a sum of squares is the standardised `χ²_{n+1}`.**
Bridges the random-variable CLT statistic to the measure-level statement. -/
private lemma map_sumSq_standardized {Ω₀ : Type*} [MeasurableSpace Ω₀]
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] (Z : ℕ → Ω₀ → ℝ)
    (hZmeas : ∀ i, Measurable (Z i)) (hZlaw : ∀ i, Measure.map (Z i) P₀ = gaussianReal 0 1)
    (hZindep : iIndepFun Z P₀) (n : ℕ) :
    P₀.map (fun ω => ((∑ i : Fin (n + 1), (Z (i : ℕ) ω) ^ 2) - ((n + 1 : ℕ) : ℝ))
        / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)))
      = (StatLean.MultipleTesting.chiSquared (n + 1)).map
          (fun x => (x - ((n + 1 : ℕ) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ))) := by
  have hSS : Measure.map (fun ω => ∑ i : Fin (n + 1), (Z (i : ℕ) ω) ^ 2) P₀
      = StatLean.MultipleTesting.chiSquared (n + 1) :=
    StatLean.MultipleTesting.map_sum_sq_eq_chiSquared n.succ_pos P₀
      (fun i => Z (i : ℕ)) (fun i => hZmeas _) (fun i => hZlaw _)
      (hZindep.precomp Fin.val_injective)
  rw [show (fun ω => ((∑ i : Fin (n + 1), (Z (i : ℕ) ω) ^ 2) - ((n + 1 : ℕ) : ℝ))
            / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)))
        = (fun x : ℝ => (x - ((n + 1 : ℕ) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)))
            ∘ (fun ω => ∑ i : Fin (n + 1), (Z (i : ℕ) ω) ^ 2) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), hSS]

/-- **Large-`k` normalisation of the central chi-squared law.**
`(χ²_k − k)/√(2k)` converges weakly to the standard normal law as the number of degrees of
freedom grows: the chi-squared variable is a sum of `k` i.i.d. squared standard normals
with mean `1` and variance `2`, so this is the i.i.d. central limit theorem. -/
theorem weakConverges_chiSquared_standardized :
    AsymptoticStatistics.WeakConverges
      (fun k : ℕ => (StatLean.MultipleTesting.chiSquared k).map
        (fun x => (x - k) / Real.sqrt (2 * k)))
      (gaussianReal 0 1) := by
  classical
  -- canonical i.i.d. `N(0,1)` sequence
  obtain ⟨Ω₀, mΩ₀, P₀, Z, hZmeas, hZlaw, hZindep, hP₀prob⟩ :=
    ProbabilityTheory.exists_iid ℕ (gaussianReal 0 1)
  letI : MeasurableSpace Ω₀ := mΩ₀
  haveI : IsProbabilityMeasure P₀ := hP₀prob
  have hclt' := tendstoInDistribution_central_standardized Z hZmeas
    (fun i => (hZlaw i).map_eq) hZindep
  -- the `TendstoInDistribution → WeakConverges` bridge
  intro f
  have hint := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hclt'.tendsto) f
  simp only [Measure.map_id] at hint
  rw [← tendsto_add_atTop_iff_nat 1]
  have hpt_int : ∀ n : ℕ,
      ∫ ω, f ω ∂((StatLean.MultipleTesting.chiSquared (n + 1)).map
        (fun x => (x - ((n + 1 : ℕ) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ))))
      = ∫ ω, f ω ∂(P₀.map (fun ω => ((∑ i : Fin (n + 1), (Z (i : ℕ) ω) ^ 2)
          - ((n + 1 : ℕ) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)))) :=
    fun n => by rw [map_sumSq_standardized Z hZmeas (fun i => (hZlaw i).map_eq) hZindep n]
  simpa only [hpt_int, ProbabilityMeasure.coe_mk] using hint

/-- **Large-`k` normalisation of the chi-squared upper quantiles.**
If `c k` is the upper-`α` quantile of `χ²_k` and `z` the upper-`α` quantile of `N(0,1)`,
then `(c k − k)/√(2k) → z`.

Consequence of `weakConverges_chiSquared_standardized`: the limiting distribution function
is continuous and strictly increasing, so weak convergence upgrades to convergence of
quantiles. The identities also force `α ∈ (0,1)`, which is therefore not assumed. -/
theorem tendsto_chiSquared_quantile_standardized {α : ℝ} {c : ℕ → ℝ} {z : ℝ}
    -- USER-INPUT: `c k` is the upper-`α` quantile of `χ²_k` (`k ≥ 1`).
    (hc : ∀ k : ℕ, 0 < k →
      (StatLean.MultipleTesting.chiSquared k) (Set.Ioi (c k)) = ENNReal.ofReal α)
    -- USER-INPUT: `z` is the upper-`α` quantile of the standard normal law.
    (hz : (gaussianReal 0 1) (Set.Ioi z) = ENNReal.ofReal α) :
    Tendsto (fun k : ℕ => (c k - k) / Real.sqrt (2 * k)) atTop (𝓝 z) := by
  classical
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  set S : ℕ → ℝ := fun k => (c k - (k : ℝ)) / Real.sqrt (2 * (k : ℝ)) with hS
  -- standardised `χ²_{n+1}` pushforwards (indexed so the d.o.f. is positive)
  set μ' : ℕ → Measure ℝ := fun n => (StatLean.MultipleTesting.chiSquared (n + 1)).map
    (fun x => (x - ((n + 1 : ℕ) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ))) with hμ'
  have hμ'prob : ∀ n, IsProbabilityMeasure (μ' n) := by
    intro n
    haveI : NeZero (n + 1) := ⟨n.succ_ne_zero⟩
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  set μs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨μ' n, hμ'prob n⟩ with hμs
  set ν' : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, by infer_instance⟩ with hν'
  -- weak convergence, as `ProbabilityMeasure` convergence (via target `A`, reindexed by `+1`)
  have htend : Tendsto μs atTop (𝓝 ν') := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hA := weakConverges_chiSquared_standardized f
    have := (tendsto_add_atTop_iff_nat (f := fun k => ∫ x, f x
      ∂((StatLean.MultipleTesting.chiSquared k).map
        (fun x => (x - (k : ℝ)) / Real.sqrt (2 * (k : ℝ))))) 1).mpr hA
    simpa [hμs, hμ', hν'] using this
  -- fixed-threshold portmanteau convergence
  have hconv : ∀ t : ℝ,
      Tendsto (fun n => μ' n (Set.Ioi t)) atTop (𝓝 (gaussianReal 0 1 (Set.Ioi t))) := by
    intro t
    have hfront : (ν' : Measure ℝ) (frontier (Set.Ioi t)) = 0 := by
      rw [frontier_Ioi]; simp [hν']
    have := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      htend (E := Set.Ioi t) hfront
    simpa [hμs, hμ', hν'] using this
  -- the standardised tail as a `χ²` tail
  have hpre : ∀ n : ℕ, ∀ t : ℝ,
      μ' n (Set.Ioi t) = StatLean.MultipleTesting.chiSquared (n + 1)
        (Set.Ioi (t * Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) + ((n + 1 : ℕ) : ℝ))) := by
    intro n t
    have hsk : (0 : ℝ) < Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) :=
      Real.sqrt_pos.mpr (by positivity)
    rw [hμ', Measure.map_apply (by fun_prop) measurableSet_Ioi]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, lt_div_iff₀ hsk]
    constructor <;> intro h <;> linarith
  -- at the standardised upper quantile the tail equals `α`
  have hquant : ∀ n : ℕ, μ' n (Set.Ioi (S (n + 1))) = ENNReal.ofReal α := by
    intro n
    have hsk : Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity)).ne'
    have hthr : S (n + 1) * Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) + ((n + 1 : ℕ) : ℝ)
        = c (n + 1) := by
      rw [hS]; simp only []; rw [div_mul_cancel₀ _ hsk]; ring
    rw [hpre n (S (n + 1)), hthr]
    exact hc (n + 1) n.succ_pos
  -- the standard normal tail is strictly decreasing (positive Gaussian mass on intervals)
  have hstrict : ∀ a b : ℝ, a < b →
      gaussianReal 0 1 (Set.Ioi b) < gaussianReal 0 1 (Set.Ioi a) := by
    intro a b hab
    have hpos : 0 < gaussianReal 0 1 (Set.Ioc a b) := by
      rw [gaussianReal_apply_eq_integral 0 one_ne_zero, ENNReal.ofReal_pos,
        ← intervalIntegral.integral_of_le hab.le]
      exact intervalIntegral.intervalIntegral_pos_of_pos
        ((integrable_gaussianPDFReal 0 1).intervalIntegrable)
        (fun x => gaussianPDFReal_pos 0 1 x one_ne_zero) hab
    have hadd : gaussianReal 0 1 (Set.Ioi a)
        = gaussianReal 0 1 (Set.Ioc a b) + gaussianReal 0 1 (Set.Ioi b) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hab.le,
        measure_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi]
    rw [hadd, add_comm]
    exact ENNReal.lt_add_right (measure_ne_top _ _) hpos.ne'
  -- squeeze `S (n+1)` into `(z - ε, z + ε)` eventually, then reindex
  rw [← tendsto_add_atTop_iff_nat (f := S) 1]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hup : ∀ᶠ n in atTop, S (n + 1) < z + ε := by
    have hlt : gaussianReal 0 1 (Set.Ioi (z + ε)) < ENNReal.ofReal α := by
      rw [← hz]; exact hstrict z (z + ε) (by linarith)
    filter_upwards [(hconv (z + ε)).eventually_lt_const hlt] with n hn
    by_contra hcon
    push_neg at hcon
    have := measure_mono (μ := μ' n) (Set.Ioi_subset_Ioi hcon)
    rw [hquant n] at this
    exact absurd (this.trans_lt hn) (lt_irrefl _)
  have hlo : ∀ᶠ n in atTop, z - ε < S (n + 1) := by
    have hgt : ENNReal.ofReal α < gaussianReal 0 1 (Set.Ioi (z - ε)) := by
      rw [← hz]; exact hstrict (z - ε) z (by linarith)
    filter_upwards [(hconv (z - ε)).eventually_const_lt hgt] with n hn
    by_contra hcon
    push_neg at hcon
    have := measure_mono (μ := μ' n) (Set.Ioi_subset_Ioi hcon)
    rw [hquant n] at this
    exact absurd (hn.trans_le this) (lt_irrefl _)
  have hfin : ∀ᶠ n in atTop, dist (S (n + 1)) z < ε := by
    filter_upwards [hup, hlo] with n hu hl
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  exact eventually_atTop.mp hfin

/-- **Sum-of-squares realisation of the noncentral chi-squared law.** For an i.i.d. `N(0,1)`
sequence `Z`, the pushforward of `∑ᵢ ((√l·[i=0]) + Zᵢ)²` (the squared norm of the shifted
Gaussian vector with mean `√l` on the first axis) is `noncentralChiSquared k l`. -/
private lemma map_noncentral_sumSq_eq {k : ℕ} {Ω₀ : Type*} [MeasurableSpace Ω₀]
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] (Z : ℕ → Ω₀ → ℝ)
    (hZmeas : ∀ i, Measurable (Z i)) (hZlaw : ∀ i, Measure.map (Z i) P₀ = gaussianReal 0 1)
    (hZindep : iIndepFun Z P₀) (l : ℝ≥0) :
    Measure.map (fun ω => ∑ i : Fin k,
        ((if (i : ℕ) = 0 then Real.sqrt (l : ℝ) else 0) + Z (i : ℕ) ω) ^ 2) P₀
      = noncentralChiSquared k l := by
  classical
  -- the coordinate vector is standard Gaussian on `EuclideanSpace ℝ (Fin k)`
  have hXlaw : Measure.map (fun ω => (WithLp.toLp 2 (fun i : Fin k => Z (i : ℕ) ω)
      : EuclideanSpace ℝ (Fin k))) P₀ = stdGaussian (EuclideanSpace ℝ (Fin k)) := by
    have hcomp : (fun ω => (WithLp.toLp 2 (fun i : Fin k => Z (i : ℕ) ω)
        : EuclideanSpace ℝ (Fin k)))
        = (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k))
            ∘ (fun ω (i : Fin k) => Z (i : ℕ) ω) := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop)
        (measurable_pi_lambda _ (fun i => hZmeas _)), ← map_pi_eq_stdGaussian]
    congr 1
    rw [(iIndepFun_iff_map_fun_eq_pi_map
        (f := fun i : Fin k => Z (i : ℕ)) (fun i => (hZmeas (i : ℕ)).aemeasurable)).1
      (hZindep.precomp Fin.val_injective)]
    congr 1; funext i; exact hZlaw (i : ℕ)
  rw [noncentralChiSquared, multivariateGaussian_one_eq_map_add,
    Measure.map_map (by fun_prop) (by fun_prop), ← hXlaw,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext ω
  simp only [Function.comp_apply, EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hcoord : (noncentralMean k l + WithLp.toLp 2 (fun j : Fin k => Z (j : ℕ) ω)) i
      = (if (i : ℕ) = 0 then Real.sqrt (l : ℝ) else 0) + Z (i : ℕ) ω := by
    rw [noncentralMean]; rfl
  rw [hcoord]

/-- **Large-`k` normalisation of the noncentral chi-squared law.**
If the noncentrality parameters satisfy `l k / √(2k) → c`, then
`(χ²_k(l k) − k)/√(2k)` converges weakly to `N(c, 1)`: writing the noncentral variable as
`(Z₁ + h)² + ∑_{i≥2} Z_i²` with `h = √(l k)`, the tail sum contributes the standard normal
limit, `h²/√(2k) → c` contributes the drift, and both `Z₁²/√(2k)` and `2hZ₁/√(2k)` vanish in
probability. Taking `l = 0` recovers the central normalisation. -/
theorem weakConverges_noncentralChiSquared_standardized {l : ℕ → ℝ≥0} {c : ℝ}
    -- USER-INPUT: the standardised noncentrality parameters converge.
    (hl : Tendsto (fun k : ℕ => (l k : ℝ) / Real.sqrt (2 * k)) atTop (𝓝 c)) :
    AsymptoticStatistics.WeakConverges
      (fun k : ℕ => (noncentralChiSquared k (l k)).map
        (fun x => (x - k) / Real.sqrt (2 * k)))
      (gaussianReal c 1) := by
  classical
  obtain ⟨Ω₀, mΩ₀, P₀, Z, hZmeas, hZlaw, hZindep, hP₀prob⟩ :=
    ProbabilityTheory.exists_iid ℕ (gaussianReal 0 1)
  letI : MeasurableSpace Ω₀ := mΩ₀
  haveI : IsProbabilityMeasure P₀ := hP₀prob
  have hZlaw' : ∀ i, Measure.map (Z i) P₀ = gaussianReal 0 1 := fun i => (hZlaw i).map_eq
  -- central standardised statistic ⟹ N(0,1), then shifted by the drift `c` ⟹ N(c,1)
  have hcentral := tendstoInDistribution_central_standardized Z hZmeas hZlaw' hZindep
  have hshift := hcentral.continuous_comp (g := fun x : ℝ => x + c) (by fun_prop)
  -- the noncentral (shifted-Gaussian squared-norm) standardised statistic
  set Yfun : ℕ → Ω₀ → ℝ := fun n ω =>
    ((∑ i : Fin (n + 1),
        ((if (i : ℕ) = 0 then Real.sqrt ((l (n + 1) : ℝ)) else 0) + Z (i : ℕ) ω) ^ 2)
      - ((n + 1 : ℕ) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) with hYfun
  have hYmeas : ∀ n, Measurable (Yfun n) := by
    intro n; rw [hYfun]; fun_prop
  -- reindexed convergence of the standardised noncentrality
  have hl1 : Tendsto (fun n : ℕ => (l (n + 1) : ℝ) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 c) :=
    (tendsto_add_atTop_iff_nat (f := fun k => (l k : ℝ) / Real.sqrt (2 * (k : ℝ))) 1).mpr hl
  have hsqrtpos : ∀ n : ℕ, (0 : ℝ) < Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) :=
    fun n => Real.sqrt_pos.mpr (by positivity)
  -- the drift-corrected difference `b n → 0`
  have hb : Tendsto (fun n : ℕ =>
      (l (n + 1) : ℝ) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) - c) atTop (𝓝 0) := by
    simpa using hl1.sub (tendsto_const_nhds (x := c))
  -- the cross-term coefficient `a n → 0`
  have hsqrt_inf : Tendsto (fun n : ℕ => Real.sqrt (2 * ((n + 1 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Filter.Tendsto.const_mul_atTop (by norm_num)
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
  have hratio0 : Tendsto (fun n : ℕ =>
      (l (n + 1) : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => (l (n + 1) : ℝ) / (2 * ((n + 1 : ℕ) : ℝ)))
        = fun n => ((l (n + 1) : ℝ) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)))
            / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) := by
      funext n; rw [div_div, Real.mul_self_sqrt (by positivity)]
    rw [heq]
    exact hl1.div_atTop hsqrt_inf
  have ha0 : Tendsto (fun n : ℕ =>
      2 * Real.sqrt ((l (n + 1) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have hcoef : (fun n : ℕ =>
          2 * Real.sqrt ((l (n + 1) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)))
        = fun n => 2 * Real.sqrt ((l (n + 1) : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) := by
      funext n
      rw [Real.sqrt_div (l (n + 1)).coe_nonneg, mul_div_assoc]
    rw [hcoef]
    have hcomp := (Real.continuous_sqrt.tendsto 0).comp hratio0
    rw [Real.sqrt_zero] at hcomp
    simpa using hcomp.const_mul 2
  -- the Slutsky remainder is a pointwise limit `a n · Z₀ + b n → 0`, hence tends to 0 in measure
  have hpt : ∀ n : ℕ, ∀ ω, (Yfun - fun n => (fun x : ℝ => x + c) ∘
      (fun ω => ((∑ i : Fin (n + 1), (Z (i : ℕ) ω) ^ 2) - ((n + 1 : ℕ) : ℝ))
        / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)))) n ω
      = (2 * Real.sqrt ((l (n + 1) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ))) * Z 0 ω
        + ((l (n + 1) : ℝ) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) - c) := by
    intro n ω
    have hsne : Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) ≠ 0 := (hsqrtpos n).ne'
    have hdiff : (∑ i : Fin (n + 1),
          ((if (i : ℕ) = 0 then Real.sqrt ((l (n + 1) : ℝ)) else 0) + Z (i : ℕ) ω) ^ 2)
        - (∑ i : Fin (n + 1), (Z (i : ℕ) ω) ^ 2)
        = 2 * Real.sqrt ((l (n + 1) : ℝ)) * Z 0 ω + (l (n + 1) : ℝ) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (0 : Fin (n + 1))]
      · have h0 : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
        simp only [h0, if_pos]
        have hsq : (Real.sqrt ((l (n + 1) : ℝ))) ^ 2 = (l (n + 1) : ℝ) :=
          Real.sq_sqrt (l (n + 1)).coe_nonneg
        nlinarith [hsq]
      · intro i _ hi
        have : (i : ℕ) ≠ 0 := by simpa [Fin.val_eq_zero_iff] using hi
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [Pi.sub_apply, hYfun, Function.comp_apply]
    rw [div_add' _ _ _ hsne]
    field_simp
    linear_combination hdiff
  have hXY : TendstoInMeasure P₀ (Yfun - fun n => (fun x : ℝ => x + c) ∘
      (fun ω => ((∑ i : Fin (n + 1), (Z (i : ℕ) ω) ^ 2) - ((n + 1 : ℕ) : ℝ))
        / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)))) atTop 0 := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) (Filter.Eventually.of_forall ?_)
    · simp only [Pi.sub_apply, Function.comp_apply]
      exact ((hYmeas n).sub (by fun_prop)).aestronglyMeasurable
    · intro ω
      have hlim0 : Tendsto (fun n : ℕ =>
          (2 * Real.sqrt ((l (n + 1) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ))) * Z 0 ω
            + ((l (n + 1) : ℝ) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) - c)) atTop (𝓝 0) := by
        simpa using (ha0.mul_const (Z 0 ω)).add hb
      simpa only [Pi.zero_apply] using (tendsto_congr (fun n => hpt n ω)).mpr hlim0
  -- Slutsky: `Yfun ⟹ N(c,1)`
  have hYdist := tendstoInDistribution_of_tendstoInMeasure_sub Yfun (fun x : ℝ => x + c)
    hshift hXY (fun n => (hYmeas n).aemeasurable)
  -- law identity: `Yfun n` pushes `P₀` to the standardised `χ²_{n+1}(l(n+1))`
  have hlawY : ∀ n : ℕ, P₀.map (Yfun n)
      = (noncentralChiSquared (n + 1) (l (n + 1))).map
          (fun x => (x - ((n + 1 : ℕ) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ))) := by
    intro n
    have hcomp : Yfun n
        = (fun x : ℝ => (x - ((n + 1 : ℕ) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)))
            ∘ (fun ω => ∑ i : Fin (n + 1),
              ((if (i : ℕ) = 0 then Real.sqrt ((l (n + 1) : ℝ)) else 0) + Z (i : ℕ) ω) ^ 2) := by
      funext ω; simp only [hYfun, Function.comp_apply]
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
      map_noncentral_sumSq_eq Z hZmeas hZlaw' hZindep (l (n + 1))]
  -- the limit law is `N(c,1)`
  have hlim : (gaussianReal 0 1).map (fun x : ℝ => x + c) = gaussianReal c 1 := by
    have := (gaussianReal_add_const (X := (id : ℝ → ℝ)) (μ := 0) (v := 1)
      (P := gaussianReal 0 1) HasLaw.id c).map_eq
    simpa using this
  -- bridge `TendstoInDistribution → WeakConverges` and reindex
  intro f
  have hint := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hYdist.tendsto) f
  rw [← tendsto_add_atTop_iff_nat 1]
  have hpt_int : ∀ n : ℕ,
      ∫ ω, f ω ∂((noncentralChiSquared (n + 1) (l (n + 1))).map
        (fun x => (x - ((n + 1 : ℕ) : ℝ)) / Real.sqrt (2 * ((n + 1 : ℕ) : ℝ))))
      = ∫ ω, f ω ∂(P₀.map (Yfun n)) := fun n => by rw [hlawY n]
  simp only [hlim] at hint
  simpa only [hpt_int, ProbabilityMeasure.coe_mk] using hint

end StatLean.HypothesisTesting
