module
public import StatLean.ConcentrationInequalities.Orlicz.SumNorm
public import StatLean.ConcentrationInequalities.Orlicz.Triangle
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

/-!
# Sub-Gaussian random vectors

A random vector $X$ in $\mathbb{R}^n$ is *sub-Gaussian* if every
one-dimensional marginal $\langle X, v\rangle$ is a sub-Gaussian random
variable; its norm is
$$ \|X\|_{\psi_2} \;=\; \sup_{v \in S^{n-1}} \|\langle X, v\rangle\|_{\psi_2}. $$
For independent mean-zero coordinates (Lemma 3.4.2),
$$ \max_i \|X_i\|_{\psi_2} \;\le\; \|X\|_{\psi_2}
   \;\le\; \sqrt{18}\, \max_i \|X_i\|_{\psi_2}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §3.4, Definition 3.4.1 and Lemma 3.4.2.

**Proof formalization notes.** Carrier `EuclideanSpace ℝ (Fin n)`; the norm
is a `⨆` of `ℝ≥0∞`-numbers over the unit sphere — a supremum of *numbers*,
so the batch's E-sup measurability policy is not triggered. Constants:
Lemma 3.4.2's lower bound holds with constant `1` (coordinate directions
`EuclideanSpace.single i 1`); the upper bound is frozen at `C = √18 = 3√2`
(formula: B3 ∘ B2 through `subGaussianNorm_weighted_sum_le` at
`∑ vᵢ² = ‖v‖² = 1`; book's absolute `C`). Work-item single named-sorry
fallback: `subGaussianVecNorm_le_of_indep` (Lemma 3.4.2 upper — the
inner-product/sphere plumbing); the definitions, the lower bound, and the
marginal predicate lemmas must close.

**Bibliographic comments.** The definition of sub-Gaussian random vectors
via one-dimensional marginals and the control of a vector norm by coordinate
norms under independence are both standard (see also
Hsu–Kakade–Zhang, "A tail inequality for quadratic forms of subgaussian
random vectors," *Electron. Commun. Probab.* 17 (2012), for the quadratic
sequel).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Sub-Gaussian vector norm** (HDP Definition 3.4.1): the supremum of the
marginal ψ₂ norms over unit directions. A `⨆` of `ℝ≥0∞` values over the
sphere — no measurability content. Edge behavior: `n = 0` gives an empty
sphere and norm `0`; a non-sub-Gaussian marginal makes the sup `⊤`. -/
noncomputable def subGaussianVecNorm {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (μ : Measure Ω := by volume_tac) : ℝ≥0∞ :=
  ⨆ v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    subGaussianNorm (fun ω => ⟪X ω, v⟫) μ

/-- **Sub-Gaussian random vector** (HDP Definition 3.4.1): every
one-dimensional marginal is sub-Gaussian (finite marginal ψ₂ norm; stated
over all `v`, not just unit `v`, which is equivalent by homogeneity). -/
def IsSubGaussianVec {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n))
    (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin n),
    subGaussianNorm (fun ω => ⟪X ω, v⟫) μ ≠ ⊤

/-- Unit-direction marginals are bounded by the vector norm (LEAN-ONLY:
`le_biSup`). -/
theorem subGaussianNorm_inner_le_vecNorm {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω}
    {v : EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: unit direction; HDP Def 3.4.1 (the sup runs over S^{n−1})
    (hv : ‖v‖ = 1) :
    subGaussianNorm (fun ω => ⟪X ω, v⟫) μ ≤ subGaussianVecNorm X μ := by
  have hmem : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    Metric.mem_sphere.mpr (by rw [dist_zero_right]; exact hv)
  exact le_iSup₂ (f := fun w (_ : w ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) =>
    subGaussianNorm (fun ω => ⟪X ω, w⟫) μ) v hmem

/-- Coordinate marginals are bounded by the vector norm (HDP Lemma 3.4.2,
lower bound, constant `1`; direction `EuclideanSpace.single i 1`). -/
theorem subGaussianNorm_coord_le_vecNorm {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω} (i : Fin n) :
    subGaussianNorm (fun ω => X ω i) μ ≤ subGaussianVecNorm X μ := by
  have hv : ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by simp
  have h := subGaussianNorm_inner_le_vecNorm (X := X) (μ := μ)
    (v := EuclideanSpace.single i (1 : ℝ)) hv
  have hfun : (fun ω => ⟪X ω, EuclideanSpace.single i (1 : ℝ)⟫) = (fun ω => X ω i) := by
    funext ω
    rw [PiLp.inner_apply, Finset.sum_eq_single i]
    · show (EuclideanSpace.single i (1 : ℝ)) i * (starRingEnd ℝ) (X ω i) = X ω i
      simp [EuclideanSpace.single_apply]
    · intro j _ hj
      show (EuclideanSpace.single i (1 : ℝ)) j * (starRingEnd ℝ) (X ω j) = 0
      simp [EuclideanSpace.single_apply, if_neg hj]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rwa [hfun] at h

/-- Finite-dimensional marginal criterion (LEAN-ONLY: expand
`⟪X, v⟫ = ∑ vᵢ Xᵢ` and use the finset-sum triangle inequality +
homogeneity from `Orlicz/Triangle.lean`/`Orlicz/Basic.lean`). -/
theorem isSubGaussianVec_of_coords {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurable coordinates; triangle-lemma regularity
    (hmeas : ∀ i, AEMeasurable (fun ω => X ω i) μ)
    -- USER-INPUT: sub-Gaussian coordinates; HDP Def 3.4.1 discussion
    (h : ∀ i, subGaussianNorm (fun ω => X ω i) μ ≠ ⊤) :
    IsSubGaussianVec X μ := by
  intro v
  -- Expand the marginal as a finite weighted sum of coordinates.
  have hinner : (fun ω => ⟪X ω, v⟫) = (fun ω => ∑ i, v i * X ω i) := by
    funext ω
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show v i * (starRingEnd ℝ) (X ω i) = v i * X ω i
    simp
  rw [hinner]
  -- Each weighted coordinate has finite ψ₂ norm; the finset triangle bound is finite.
  have hbound : subGaussianNorm (fun ω => ∑ i, v i * X ω i) μ ≤
      ∑ i, subGaussianNorm (fun ω => v i * X ω i) μ := by
    rw [subGaussianNorm_def]
    refine le_trans (orliczNorm_finset_sum_le psiTwo_monotoneOn psiTwo_convexOn
      psiTwo_zero.le psiTwo_measurable Finset.univ
      (fun i _ => (measurable_id.const_mul (v i)).comp_aemeasurable (hmeas i))) ?_
    exact le_of_eq (Finset.sum_congr rfl (fun i _ => (subGaussianNorm_def _ _).symm))
  refine ne_of_lt (lt_of_le_of_lt hbound ?_)
  refine ENNReal.sum_lt_top.mpr (fun i _ => ?_)
  rcases eq_or_ne (v i) 0 with hvi | hvi
  · rw [hvi]
    rw [subGaussianNorm_def, orliczNorm_const_mul_zero psiTwo_zero.le]
    exact ENNReal.zero_lt_top
  · rw [subGaussianNorm_const_mul hvi]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h i).lt_top

/-- **Lemma 3.4.2, upper bound** (HDP §3.4; frozen constant `√18 = 3√2`,
formula B3∘B2 via `subGaussianNorm_weighted_sum_le` at `‖v‖ = 1`): for
independent mean-zero coordinates with uniform ψ₂ bound `K`,
`‖X‖_{ψ₂} ≤ √18 · K`. This work item's single named-sorry fallback. -/
theorem subGaussianVecNorm_le_of_indep
    {μ : Measure Ω}
    -- LEAN-ONLY: probability measure (bridge B2/B3 requirement)
    [IsProbabilityMeasure μ] {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {K : ℝ≥0}
    -- LEAN-ONLY: positive bound (mild strengthening, see module notes)
    (hK : 0 < K)
    -- LEAN-ONLY: measurable coordinates
    (hmeas : ∀ i, Measurable (fun ω => X ω i))
    -- USER-INPUT: independent coordinates; HDP Lemma 3.4.2
    (hindep : ProbabilityTheory.iIndepFun (fun i ω => X ω i) μ)
    -- USER-INPUT: mean-zero coordinates; HDP Lemma 3.4.2
    (hmean : ∀ i, ∫ x, X x i ∂μ = 0)
    -- USER-INPUT: uniform coordinate ψ₂ bound; HDP Lemma 3.4.2
    (hnorm : ∀ i, subGaussianNorm (fun ω => X ω i) μ ≤ K) :
    subGaussianVecNorm X μ ≤ (NNReal.sqrt 18 * K : ℝ≥0∞) := by
  unfold subGaussianVecNorm
  refine iSup₂_le fun v hv => ?_
  have hv1 : ‖v‖ = 1 := by
    rw [Metric.mem_sphere, dist_zero_right] at hv; exact hv
  -- marginal as a weighted coordinate sum
  have hinner : (fun ω => ⟪X ω, v⟫) = (fun ω => ∑ i, v i * X ω i) := by
    funext ω
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show v i * (starRingEnd ℝ) (X ω i) = v i * X ω i
    simp
  rw [hinner]
  -- the `∑ (v i)² = ‖v‖² = 1` identity, over `ℝ`
  have hsumR : ∑ i, (v i) ^ 2 = 1 := by
    have h2 : ∑ i, (v i) ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
    rw [h2, hv1, one_pow]
  have harg : (18 * (∑ i, ⟨(v i) ^ 2, sq_nonneg _⟩ * K ^ 2 : ℝ≥0)) = 18 * K ^ 2 := by
    have h1 : (∑ i, NNReal.mk ((v i) ^ 2) (sq_nonneg _)) = 1 :=
      NNReal.eq (by rw [NNReal.coe_sum]; exact hsumR)
    calc (18 * (∑ i, NNReal.mk ((v i) ^ 2) (sq_nonneg _) * K ^ 2) : ℝ≥0)
        = 18 * ((∑ i, NNReal.mk ((v i) ^ 2) (sq_nonneg _)) * K ^ 2) := by rw [Finset.sum_mul]
      _ = 18 * K ^ 2 := by rw [h1, one_mul]
  have hconst : NNReal.sqrt (18 * (∑ i, ⟨(v i) ^ 2, sq_nonneg _⟩ * K ^ 2 : ℝ≥0))
      = NNReal.sqrt 18 * K := by
    rw [harg, NNReal.sqrt_mul, NNReal.sqrt_sq]
  calc subGaussianNorm (fun ω => ∑ i, v i * X ω i) μ
      ≤ (NNReal.sqrt (18 * (∑ i, ⟨(v i) ^ 2, sq_nonneg _⟩ * K ^ 2 : ℝ≥0)) : ℝ≥0∞) :=
        subGaussianNorm_weighted_sum_le (X := fun i ω => X ω i) (K := fun _ => K)
          v hmeas hindep hmean (fun _ => hK) hnorm
    _ = (NNReal.sqrt 18 * K : ℝ≥0∞) := by rw [← ENNReal.coe_mul, hconst]

/-- Lemma 3.4.2 statement packaging: the coordinate-max lower bound as a
finite `⨆` (HDP §3.4). -/
theorem max_coord_le_subGaussianVecNorm {n : ℕ} [NeZero n]
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω} :
    (⨆ i : Fin n, subGaussianNorm (fun ω => X ω i) μ) ≤
      subGaussianVecNorm X μ :=
  iSup_le fun i => subGaussianNorm_coord_le_vecNorm i

end StatLean.ConcentrationInequalities
