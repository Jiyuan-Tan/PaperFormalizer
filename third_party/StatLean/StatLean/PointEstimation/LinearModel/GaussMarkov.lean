module
public import StatLean.PointEstimation.LinearModel.LeastSquares
public import StatLean.PointEstimation.LinearModel.Equivariant
public import Mathlib.Probability.Moments.Covariance

@[expose] public section

/-!
# The Gauss–Markov theorem: least squares among linear estimators

Dropping normality *and* independence, and retaining only the first two moments — the mean
vector lies in the subspace `W` and the coordinates are uncorrelated with common variance
`σ²` — the least-squares functional `y ↦ ⟪γ, P_W y⟫` still minimizes the variance among all
linear estimators unbiased throughout `W`, and it is the *only* one that does so:

* `integral_inner_lse` — the least-squares functional is unbiased under the moment
  assumptions alone;
* `gauss_markov` — its variance does not exceed that of any competing linear unbiased
  estimator `y ↦ ⟪c, y⟫`;
* `blue_lse` — the best linear unbiased estimator is unique: a minimizing coefficient
  vector must be `P_W γ`;
* `isSubspaceEquivariant_inner_iff` — for linear estimators, equivariance under
  translations by `W` is exactly unbiasedness throughout `W`;
* `isMRE_lse_among_linear_equivariant` — consequently, under squared error the
  least-squares functional is minimum risk equivariant among linear equivariant estimators.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.4 (Normal
Linear Models), Theorem 4.12 (Gauss–Markov: least squares is UMVU among linear estimators) and
Corollary 4.13 (BLUE). (`TPE2 §3.4 Thm 4.12, Cor 4.13`.)

**Proof formalization notes.**
* *Moments only.* The unknown law is a single probability measure `P` on the observation
  space constrained by mean and covariance hypotheses; no dominatedness, no independence,
  no family indexed by a parameter. The parameter enters only through the vector `ξ` named
  in the mean hypothesis.
* *Junk-value discipline.* Mathlib's `covariance` and `variance` return junk off `L²`, and
  Bochner integrals return junk off `L¹`; the integrability and square-integrability
  hypotheses — both part of the classical assumption that the coordinates have mean `ξᵢ`
  and finite variance `σ²` — are therefore carried explicitly, each statement asking only
  for the one it needs.
* *Where the hypotheses are used.* The variance comparison needs only the second-moment
  structure and the competitor's unbiasedness relation `⟪c, ζ⟫ = ⟪γ, ζ⟫` on `W`; the mean
  hypotheses are used exactly for the unbiasedness statement and for the squared-error
  (risk) form. They are kept apart for that reason instead of being bundled.
* The intended proof of the variance comparison is the classical one: unbiasedness on `W`
  says `P_W c = P_W γ`, whence `‖c‖² = ‖P_W γ‖² + ‖c − P_W c‖²`, and both variances are
  `σ²` times the respective squared norms; uniqueness is the equality case.
* *Imports.* Although the statements assume no normality, this file sits above the normal
  theory: the classical argument derives the comparison from the normal-model optimality
  (variances of linear statistics depend on the first two moments only), and the
  equivariance predicate is the one already fixed for the normal model rather than a second
  copy of it.

**Bibliographic comments.** The theorem is due to C. F. Gauss (*Theoria combinationis
observationum erroribus minimis obnoxiae*, 1821/1823), with the formulation for linear
unbiased estimators associated with A. A. Markov (*Wahrscheinlichkeitsrechnung*, Teubner,
1912); see W. Kruskal ("When are Gauss–Markov and least squares estimators identical?" in
*Essays in Probability and Statistics*, 1965) for the coordinate-free treatment, and
H. Scheffé (*The Analysis of Variance*, Wiley, 1959) and C. R. Rao (*Linear Statistical
Inference and Its Applications*, 2nd ed., Wiley, 1973) for the standard developments and
extensions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {n : ℕ}

/-- The real inner product on `EuclideanSpace ℝ (Fin n)` in coordinates. -/
private lemma real_inner_euclidean (a y : EuclideanSpace ℝ (Fin n)) :
    ⟪a, y⟫_ℝ = ∑ i, a i * y i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  change y i * a i = a i * y i
  ring

/-- The variance of a linear statistic `⟪a, ·⟫` under the moment assumptions is `σ² ‖a‖²`. -/
private lemma variance_inner_linear (a : EuclideanSpace ℝ (Fin n)) {σ2 : ℝ}
    {P : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure P]
    (hcov : ∀ i j, covariance (fun y => y i) (fun y => y j) P = if i = j then σ2 else 0)
    (hL2 : ∀ i, MemLp (fun y => y i) 2 P) :
    variance (fun y => ⟪a, y⟫_ℝ) P = σ2 * ‖a‖ ^ 2 := by
  have hbody : (fun y : EuclideanSpace ℝ (Fin n) => ⟪a, y⟫_ℝ)
      = ∑ i, (fun y => a i * y i) := by
    funext y; rw [real_inner_euclidean, Finset.sum_apply]
  rw [hbody, variance_sum (fun i => (hL2 i).const_mul (a i))]
  have hcov2 : ∀ i j, covariance (fun y => a i * y i) (fun y => a j * y j) P
      = a i * a j * covariance (fun y => y i) (fun y => y j) P := by
    intro i j
    rw [show (fun y : EuclideanSpace ℝ (Fin n) => a i * y i)
            = a i • (fun y : EuclideanSpace ℝ (Fin n) => y i) from by
          funext y; rw [Pi.smul_apply, smul_eq_mul],
        show (fun y : EuclideanSpace ℝ (Fin n) => a j * y j)
            = a j • (fun y : EuclideanSpace ℝ (Fin n) => y j) from by
          funext y; rw [Pi.smul_apply, smul_eq_mul],
        covariance_smul_left, covariance_smul_right, ← mul_assoc]
  simp_rw [hcov2, hcov]
  rw [← real_inner_self_eq_norm_sq, real_inner_euclidean]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [if_neg (fun h => hji h.symm), mul_zero])
        (fun h => absurd (Finset.mem_univ i) h)]
  rw [if_pos rfl]; ring

/-- A linear statistic `⟪a, ·⟫` is square-integrable under the moment assumptions. -/
private lemma memLp_inner_linear (a : EuclideanSpace ℝ (Fin n))
    {P : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure P]
    (hL2 : ∀ i, MemLp (fun y => y i) 2 P) :
    MemLp (fun y => ⟪a, y⟫_ℝ) 2 P := by
  have hbody : (fun y : EuclideanSpace ℝ (Fin n) => ⟪a, y⟫_ℝ)
      = ∑ i, (fun y => a i * y i) := by
    funext y; rw [real_inner_euclidean, Finset.sum_apply]
  rw [hbody]
  exact memLp_finset_sum' _ (fun i _ => (hL2 i).const_mul (a i))

/-- The mean of a linear statistic `⟪a, ·⟫` is `⟪a, ξ⟫`. -/
private lemma integral_inner_linear (a : EuclideanSpace ℝ (Fin n))
    {ξ : EuclideanSpace ℝ (Fin n)} {P : Measure (EuclideanSpace ℝ (Fin n))}
    [IsProbabilityMeasure P] (hmean : ∀ i, ∫ y, y i ∂P = ξ i)
    (hint : ∀ i, Integrable (fun y => y i) P) :
    ∫ y, ⟪a, y⟫_ℝ ∂P = ⟪a, ξ⟫_ℝ := by
  simp_rw [real_inner_euclidean a]
  rw [integral_finset_sum Finset.univ (fun i _ => (hint i).const_mul (a i))]
  simp_rw [integral_const_mul, hmean]

/-- The least-squares functional rewritten as the linear statistic `⟪P_W γ, ·⟫`. -/
private lemma variance_lse_eq (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection] (γ : EuclideanSpace ℝ (Fin n))
    {P : Measure (EuclideanSpace ℝ (Fin n))} :
    variance (fun y => ⟪γ, lse W y⟫_ℝ) P
      = variance (fun y => ⟪W.starProjection γ, y⟫_ℝ) P := by
  congr 1; funext y; exact inner_lse_eq_inner_starProjection W γ y

/-- Unbiasedness on `W` forces the projections of the two coefficient vectors to agree. -/
private lemma starProjection_eq_of_unbiased {W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    [W.HasOrthogonalProjection] {γ c : EuclideanSpace ℝ (Fin n)}
    (hc : ∀ ζ ∈ W, ⟪c, ζ⟫_ℝ = ⟪γ, ζ⟫_ℝ) :
    W.starProjection c = W.starProjection γ := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.starProjection_apply_mem W γ) (fun w hw => ?_)
  rw [inner_sub_left, hc w hw, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hw, sub_self]

/-- **Unbiasedness of the least-squares functional under the moment assumptions**: if the
mean vector lies in `W`, then `y ↦ ⟪γ, P_W y⟫` has mean `⟪γ, ξ⟫`. -/
theorem integral_inner_lse {W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    [W.HasOrthogonalProjection] {γ ξ : EuclideanSpace ℝ (Fin n)}
    {P : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure P]
    -- USER-INPUT: the mean vector is constrained to the mean subspace
    (hξ : ξ ∈ W)
    -- USER-INPUT: first moments of the observation
    (hmean : ∀ i, ∫ y, y i ∂P = ξ i)
    -- USER-INPUT: integrable coordinates (the first moments exist; Bochner integrals are
    -- junk-valued off `L¹`, so this cannot be left implicit in `hmean`)
    (hint : ∀ i, Integrable (fun y => y i) P) :
    ∫ y, ⟪γ, lse W y⟫_ℝ ∂P = ⟪γ, ξ⟫_ℝ := by
  have hbody : ∀ y, ⟪γ, lse W y⟫_ℝ = ∑ i, (W.starProjection γ) i * y i := by
    intro y; rw [inner_lse_eq_inner_starProjection, real_inner_euclidean]
  simp_rw [hbody]
  rw [integral_finset_sum Finset.univ
        (fun i _ => (hint i).const_mul (W.starProjection γ i))]
  simp_rw [integral_const_mul, hmean]
  rw [← real_inner_euclidean, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hξ]

/-- **Gauss–Markov**: among the linear estimators unbiased throughout the mean subspace,
the least-squares functional has the smallest variance. -/
theorem gauss_markov {W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    [W.HasOrthogonalProjection] {σ2 : ℝ} {γ c : EuclideanSpace ℝ (Fin n)}
    {P : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure P]
    -- USER-INPUT: uncorrelated coordinates with common variance σ² (the second-moment
    -- assumption; neither normality nor independence is assumed)
    (hcov : ∀ i j, covariance (fun y => y i) (fun y => y j) P = if i = j then σ2 else 0)
    -- USER-INPUT: square-integrable coordinates (finite second moments, part of the
    -- moment assumptions)
    (hL2 : ∀ i, MemLp (fun y => y i) 2 P)
    -- USER-INPUT: the competing linear estimator is unbiased throughout the mean subspace
    (hc : ∀ ζ ∈ W, ⟪c, ζ⟫_ℝ = ⟪γ, ζ⟫_ℝ) :
    variance (fun y => ⟪γ, lse W y⟫_ℝ) P ≤ variance (fun y => ⟪c, y⟫_ℝ) P := by
  rw [variance_lse_eq, variance_inner_linear (W.starProjection γ) hcov hL2,
    variance_inner_linear c hcov hL2]
  -- geometry: ‖P_W γ‖² ≤ ‖c‖²
  have hPeq := starProjection_eq_of_unbiased hc
  have hdecomp := Submodule.norm_sq_eq_add_norm_sq_starProjection c W
  rw [hPeq] at hdecomp
  have hgeom : ‖W.starProjection γ‖ ^ 2 ≤ ‖c‖ ^ 2 := by
    rw [hdecomp]; nlinarith [sq_nonneg ‖Wᗮ.starProjection c‖]
  rcases isEmpty_or_nonempty (Fin n) with he | he
  · haveI := he
    have hc0 : ‖c‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, real_inner_euclidean, Finset.univ_eq_empty,
        Finset.sum_empty]
    have hp0 : ‖W.starProjection γ‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, real_inner_euclidean, Finset.univ_eq_empty,
        Finset.sum_empty]
    rw [hc0, hp0]
  · obtain ⟨i⟩ := he
    have hii := hcov i i; rw [if_pos rfl] at hii
    have hσ : 0 ≤ σ2 := by
      rw [← hii, covariance_self (hL2 i).aemeasurable]; exact variance_nonneg _ _
    exact mul_le_mul_of_nonneg_left hgeom hσ

/-- **Uniqueness of the best linear unbiased estimator**: a linear estimator unbiased
throughout the mean subspace whose variance is minimal has coefficient vector `P_W γ`, that
is, it *is* the least-squares functional. -/
theorem blue_lse {W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    [W.HasOrthogonalProjection] {σ2 : ℝ} {γ c : EuclideanSpace ℝ (Fin n)}
    {P : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure P]
    -- USER-INPUT: nondegenerate observation; with σ² = 0 every coefficient vector ties
    (hσ2 : 0 < σ2)
    -- USER-INPUT: uncorrelated coordinates with common variance σ²
    (hcov : ∀ i j, covariance (fun y => y i) (fun y => y j) P = if i = j then σ2 else 0)
    -- USER-INPUT: square-integrable coordinates (finite second moments)
    (hL2 : ∀ i, MemLp (fun y => y i) 2 P)
    -- USER-INPUT: the linear estimator is unbiased throughout the mean subspace
    (hc : ∀ ζ ∈ W, ⟪c, ζ⟫_ℝ = ⟪γ, ζ⟫_ℝ)
    -- LEAN-ONLY: the competitor attains the minimum of the previous theorem; this is the
    -- equality case, not an extra modelling assumption
    (hbest : variance (fun y => ⟪c, y⟫_ℝ) P ≤ variance (fun y => ⟪γ, lse W y⟫_ℝ) P) :
    c = W.starProjection γ := by
  have hgm := gauss_markov hcov hL2 hc
  have e := le_antisymm hbest hgm
  rw [variance_inner_linear c hcov hL2, variance_lse_eq,
    variance_inner_linear (W.starProjection γ) hcov hL2] at e
  have hnormeq : ‖c‖ ^ 2 = ‖W.starProjection γ‖ ^ 2 := mul_left_cancel₀ (ne_of_gt hσ2) e
  have hPeq := starProjection_eq_of_unbiased hc
  have hdecomp := Submodule.norm_sq_eq_add_norm_sq_starProjection c W
  rw [hPeq] at hdecomp
  have hz : ‖Wᗮ.starProjection c‖ ^ 2 = 0 := by rw [hnormeq] at hdecomp; linarith
  have hzero : Wᗮ.starProjection c = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
    exact norm_eq_zero.mp this
  have hadd := W.starProjection_add_starProjection_orthogonal c
  rw [hzero, add_zero] at hadd
  rw [← hadd]; exact hPeq

/-- For a **linear** estimator, equivariance under translations by the mean subspace is the
same as unbiasedness throughout the mean subspace. -/
theorem isSubspaceEquivariant_inner_iff (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (γ c : EuclideanSpace ℝ (Fin n)) :
    IsSubspaceEquivariant W γ (fun y => ⟪c, y⟫_ℝ) ↔ ∀ b ∈ W, ⟪c, b⟫_ℝ = ⟪γ, b⟫_ℝ := by
  constructor
  · intro h b hb
    have hb0 := h b hb 0
    simpa using hb0
  · intro h b hb y
    show ⟪c, y + b⟫_ℝ = ⟪c, y⟫_ℝ + ⟪γ, b⟫_ℝ
    rw [inner_add_right, h b hb]

/-- Under squared error, the least-squares functional is minimum risk equivariant among the
**linear** equivariant estimators, under the moment assumptions alone. -/
theorem isMRE_lse_among_linear_equivariant {W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    [W.HasOrthogonalProjection] {σ2 : ℝ} {γ c ξ : EuclideanSpace ℝ (Fin n)}
    {P : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure P]
    -- USER-INPUT: the mean vector is constrained to the mean subspace
    (hξ : ξ ∈ W)
    -- USER-INPUT: first moments of the observation
    (hmean : ∀ i, ∫ y, y i ∂P = ξ i)
    -- USER-INPUT: uncorrelated coordinates with common variance σ²
    (hcov : ∀ i j, covariance (fun y => y i) (fun y => y j) P = if i = j then σ2 else 0)
    -- USER-INPUT: square-integrable coordinates (finite second moments)
    (hL2 : ∀ i, MemLp (fun y => y i) 2 P)
    -- USER-INPUT: the competing linear estimator is equivariant under translations by the
    -- mean subspace
    (hequiv : IsSubspaceEquivariant W γ (fun y => ⟪c, y⟫_ℝ)) :
    ∫ y, (⟪γ, lse W y⟫_ℝ - ⟪γ, ξ⟫_ℝ) ^ 2 ∂P ≤ ∫ y, (⟪c, y⟫_ℝ - ⟪γ, ξ⟫_ℝ) ^ 2 ∂P := by
  have hc : ∀ ζ ∈ W, ⟪c, ζ⟫_ℝ = ⟪γ, ζ⟫_ℝ := (isSubspaceEquivariant_inner_iff W γ c).mp hequiv
  have hint : ∀ i, Integrable (fun y => y i) P := fun i => (hL2 i).integrable one_le_two
  -- both estimators are unbiased for `⟪γ, ξ⟫`, so their MSE equals their variance
  have hElse : ∫ y, ⟪γ, lse W y⟫_ℝ ∂P = ⟪γ, ξ⟫_ℝ := integral_inner_lse hξ hmean hint
  have hEc : ∫ y, ⟪c, y⟫_ℝ ∂P = ⟪γ, ξ⟫_ℝ :=
    (integral_inner_linear c hmean hint).trans (hc ξ hξ)
  have hlseEq : (fun y => ⟪γ, lse W y⟫_ℝ) = fun y => ⟪W.starProjection γ, y⟫_ℝ := by
    funext y; exact inner_lse_eq_inner_starProjection W γ y
  have hml : MemLp (fun y => ⟪γ, lse W y⟫_ℝ) 2 P := by
    rw [hlseEq]; exact memLp_inner_linear (W.starProjection γ) hL2
  have hmc : MemLp (fun y => ⟪c, y⟫_ℝ) 2 P := memLp_inner_linear c hL2
  have key : ∀ δ : EuclideanSpace ℝ (Fin n) → ℝ, AEMeasurable δ P →
      (∫ y, δ y ∂P = ⟪γ, ξ⟫_ℝ) → ∫ y, (δ y - ⟪γ, ξ⟫_ℝ) ^ 2 ∂P = variance δ P := by
    intro δ hδ hE; rw [variance_eq_integral hδ, hE]
  rw [key _ hml.aemeasurable hElse, key _ hmc.aemeasurable hEc]
  exact gauss_markov hcov hL2 hc

end StatLean.PointEstimation
