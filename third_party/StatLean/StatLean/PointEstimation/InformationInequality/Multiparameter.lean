module
public import StatLean.PointEstimation.InformationInequality.CramerRao
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

@[expose] public section

/-!
# The multiparameter information inequality

The one-dimensional covariance inequality `var(δ) ≥ cov(δ, ψ)² / var(ψ)` sharpens to a
quadratic form when several auxiliary functions `ψ_1, …, ψ_r` are available: optimizing the
one-dimensional bound over all linear combinations `∑ a_i ψ_i` gives
$$ \operatorname{var}(\delta) \;\ge\; \gamma^{\mathsf T} C^{-1}\gamma, \qquad
   \gamma_i = \operatorname{cov}(\delta, \psi_i), \quad
   C_{ij} = \operatorname{cov}(\psi_i, \psi_j). $$
Taking the `ψ_i` to be the coordinate scores `∂_{θ_i} \log p_\theta` turns `C` into the
information matrix and `γ` into the gradient of the expectation of `δ`, which is the
information inequality for a vector parameter.

Contents:
* `covariance_matrix_inequality` — the quadratic-form covariance inequality for an
  arbitrary finite family of square-integrable auxiliary functions;
* `multiparameter_cramer_rao` — its specialization to the coordinate scores: the variance of
  a statistic is at least `∇(E_θ δ)ᵀ I(θ)⁻¹ ∇(E_θ δ)`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.6 (The
Multiparameter Case and Other Extensions), Theorem 6.1 (the covariance-matrix inequality),
Theorem 6.2 (the exponential-family information matrix) and Theorem 6.6 (the multiparameter
Cramér–Rao bound `(∂g)ᵀ I(θ)⁻¹ (∂g)`). (`TPE2 §2.6 Thm 6.1, Thm 6.2, Thm 6.6`.)

**Proof formalization notes.**
* The quadratic-form inequality is stated at a *fixed* measure: it is a statement of
  second-moment geometry, with no model, parameter or estimand involved. Unbiasedness of `δ`
  plays no role in its proof and is therefore not assumed — it matters only for the *use* of
  the bound, where one wants the right-hand side to depend on `δ` through its expectation
  alone, which happens exactly when each `ψ_i` is uncorrelated with every unbiased estimator
  of zero. Dropping the hypothesis is a strengthening, recorded here to make the deviation
  from the classical phrasing explicit.
* The covariance matrix and the covariance vector are supplied as data together with their
  defining identities, rather than inlined, so the statement reads as the classical
  `γᵀ C⁻¹ γ ≤ var(δ)` and so that consumers may substitute any matrix they have already
  computed.
* Positive definiteness of `C` is a genuine hypothesis: without it the inverse is Lean's
  junk value and the bound carries no content. In the specialization it is positive
  definiteness of the information matrix, which fails exactly when the coordinate scores are
  linearly dependent — the classical degeneracy.
* Partial derivatives in the vector parameter are expressed as one-dimensional derivatives
  along the coordinate directions at `0`, matching the definition of the score vector, so no
  Fréchet-differentiability machinery is needed to state the theorem.

**Bibliographic comments.** The matrix form of the information inequality is due to
C. R. Rao ("Information and the accuracy attainable in the estimation of statistical
parameters," *Bull. Calcutta Math. Soc.* **37** (1945), 81–91); the one-dimensional bound it
generalizes was obtained independently by Rao and by H. Cramér (*Mathematical Methods of
Statistics*, Princeton University Press, 1946, §32.3), with earlier forms in M. Fréchet
("Sur l'extension de certaines évaluations statistiques au cas de petits échantillons,"
*Rev. Inst. Int. Statist.* **11** (1943), 182–205) and G. Darmois ("Sur les limites de la
dispersion de certaines estimations," *Rev. Inst. Int. Statist.* **13** (1945), 9–15).
Sharpening the bound by adjoining higher-order derivatives of the density to the family
`ψ_i` is A. Bhattacharyya's ("On some analogues of the amount of information and their use
in statistical estimation," *Sankhyā* **8** (1946), 1–14, 201–218, 315–328).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- Cauchy–Schwarz for the Bochner integral against a probability measure:
`(∫ X·Y)² ≤ (∫ X²)(∫ Y²)`, via nonnegativity of `∫ (X - tY)²` (a quadratic in `t`). -/
private lemma sq_integral_mul_le {P : Measure 𝓧} [IsProbabilityMeasure P] {X Y : 𝓧 → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    (∫ x, X x * Y x ∂P) ^ 2 ≤ (∫ x, X x ^ 2 ∂P) * (∫ x, Y x ^ 2 ∂P) := by
  have iX2 : Integrable (fun x => X x ^ 2) P := hX.integrable_sq
  have iY2 : Integrable (fun x => Y x ^ 2) P := hY.integrable_sq
  have iXY : Integrable (fun x => X x * Y x) P := memLp_one_iff_integrable.mp (hY.mul' hX)
  have hquad : ∀ t : ℝ,
      0 ≤ (∫ x, Y x ^ 2 ∂P) * (t * t) + (-2 * ∫ x, X x * Y x ∂P) * t + (∫ x, X x ^ 2 ∂P) := by
    intro t
    have hnn : 0 ≤ ∫ x, (X x - t * Y x) ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
    have hfun : (fun x => (X x - t * Y x) ^ 2)
        = fun x => (X x ^ 2 - (2 * t) * (X x * Y x)) + t ^ 2 * Y x ^ 2 := by funext x; ring
    rw [hfun,
      integral_add (show Integrable (fun x => X x ^ 2 - (2 * t) * (X x * Y x)) P from
          iX2.sub (iXY.const_mul (2 * t)))
        (show Integrable (fun x => t ^ 2 * Y x ^ 2) P from iY2.const_mul (t ^ 2)),
      integral_sub iX2 (show Integrable (fun x => (2 * t) * (X x * Y x)) P from
          iXY.const_mul (2 * t)),
      integral_const_mul, integral_const_mul] at hnn
    nlinarith [hnn]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- Cauchy–Schwarz for the covariance: `cov(X, Y)² ≤ var(X)·var(Y)`. -/
private lemma sq_covariance_le {P : Measure 𝓧} [IsProbabilityMeasure P] {X Y : 𝓧 → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    covariance X Y P ^ 2 ≤ variance X P * variance Y P := by
  rw [covariance, variance_eq_integral hX.aemeasurable, variance_eq_integral hY.aemeasurable]
  exact sq_integral_mul_le (hX.sub (memLp_const _)) (hY.sub (memLp_const _))

/-- **The covariance inequality in quadratic form.** For square-integrable `δ` and
auxiliary functions `ψ_1, …, ψ_r` whose covariance matrix `C` is positive definite,
`γᵀ C⁻¹ γ ≤ var(δ)`, where `γ_i = cov(δ, ψ_i)`.

Optimizing the one-dimensional covariance bound over linear combinations `∑ a_i ψ_i` gives
exactly the maximum `max_a (aᵀγ)² / (aᵀ C a) = γᵀ C⁻¹ γ`. -/
theorem covariance_matrix_inequality {r : ℕ} (P : Measure 𝓧)
    -- USER-INPUT: the statement is about a probability measure (a fixed member of a model)
    [IsProbabilityMeasure P]
    (δ : 𝓧 → ℝ) (ψ : Fin r → 𝓧 → ℝ)
    -- USER-INPUT: the statistic has a finite second moment
    (hδ : MemLp δ 2 P)
    -- USER-INPUT: each auxiliary function has a finite second moment
    (hψ : ∀ i, MemLp (ψ i) 2 P)
    (C : Matrix (Fin r) (Fin r) ℝ)
    -- USER-INPUT: `C` is the covariance matrix of the auxiliary functions
    (hC : ∀ i j, C i j = covariance (ψ i) (ψ j) P)
    -- USER-INPUT: that covariance matrix is nonsingular; the classical nondegeneracy
    -- condition, without which the bound is vacuous
    (hCpos : C.PosDef)
    (γ : Fin r → ℝ)
    -- USER-INPUT: `γ` is the vector of covariances of the statistic with the auxiliary
    -- functions
    (hγ : ∀ i, γ i = covariance δ (ψ i) P) :
    γ ⬝ᵥ (C⁻¹ *ᵥ γ) ≤ variance δ P := by
  classical
  have hdot : ∀ u v : Fin r → ℝ, u ⬝ᵥ v = ∑ i, u i * v i := fun _ _ => rfl
  set a : Fin r → ℝ := C⁻¹ *ᵥ γ with ha
  set W : 𝓧 → ℝ := fun x => ∑ i, a i * ψ i x with hW
  set q : ℝ := γ ⬝ᵥ (C⁻¹ *ᵥ γ) with hq
  -- `W ∈ L²`
  have hWmem : MemLp W 2 P := by
    rw [hW]; exact memLp_finset_sum _ (fun i _ => (hψ i).const_mul (a i))
  -- `C⁻¹` is positive definite, so `q ≥ 0` and `C` is nonsingular
  have hCinv : (C⁻¹).PosDef := hCpos.inv
  have hqnn : 0 ≤ q := by rw [hq]; exact hCinv.posSemidef.dotProduct_mulVec_nonneg γ
  have hunit : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hCpos.isUnit
  -- `C *ᵥ a = γ`
  have hCa : C *ᵥ a = γ := by
    rw [ha, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv C hunit, Matrix.one_mulVec]
  -- `a ⬝ᵥ γ = q`
  have haγ : a ⬝ᵥ γ = q := by rw [hq, ha, dotProduct_comm]
  -- covariance of `δ` with `W`
  have hcovW : covariance δ W P = q := by
    nth_rewrite 1 [hW]
    rw [covariance_fun_sum_right (fun i => (hψ i).const_mul (a i)) hδ]
    rw [show (∑ i, covariance δ (fun x => a i * ψ i x) P) = ∑ i, a i * γ i from
      Finset.sum_congr rfl fun i _ => by rw [covariance_const_mul_right, ← hγ i]]
    rw [← haγ, hdot]
  -- variance of `W`
  have hvarW : variance W P = q := by
    rw [← covariance_self hWmem.aemeasurable]
    nth_rewrite 1 [hW]
    rw [covariance_fun_sum_left (fun i => (hψ i).const_mul (a i)) hWmem]
    have hterm : ∀ i, covariance (fun x => a i * ψ i x) W P = a i * (C *ᵥ a) i := by
      intro i
      have hmv : (C *ᵥ a) i = ∑ j, C i j * a j := rfl
      rw [covariance_const_mul_left, hW,
        covariance_fun_sum_right (fun j => (hψ j).const_mul (a j)) (hψ i), hmv,
        show (∑ j, covariance (ψ i) (fun x => a j * ψ j x) P) = ∑ j, C i j * a j from
          Finset.sum_congr rfl fun j _ => by rw [covariance_const_mul_right, ← hC i j, mul_comm]]
    simp_rw [hterm, hCa]
    rw [← haγ, hdot]
  -- Cauchy–Schwarz and conclude
  have hCS : covariance δ W P ^ 2 ≤ variance δ P * variance W P := sq_covariance_le hδ hWmem
  rw [hcovW, hvarW] at hCS
  rcases eq_or_lt_of_le hqnn with h0 | hpos
  · rw [← h0]; exact variance_nonneg δ P
  · have : q * q ≤ variance δ P * q := by rw [← sq]; exact hCS
    exact le_of_mul_le_mul_right this hpos

/-- **The multiparameter information inequality.** For a dominated family on an
`s`-dimensional parameter with a common support, mean-zero coordinate scores and a positive
definite information matrix, and a square-integrable statistic `δ` whose expectation has
partial derivatives `α_i` obtained by differentiating under the integral sign,
`αᵀ I(θ)⁻¹ α ≤ var_θ(δ)`.

For an unbiased estimator of an estimand `g` the vector `α` is the gradient `∇g(θ)`; in
general it is the gradient of `θ ↦ E_θ δ`, so that a bias contributes through its
gradient. -/
theorem multiparameter_cramer_rao {s : ℕ} (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : EuclideanSpace ℝ (Fin s)) (δ : 𝓧 → ℝ) (α : Fin s → ℝ)
    -- USER-INPUT: on the support, the density is differentiable along each coordinate
    -- direction; classical smoothness condition for a vector parameter
    (hdiff : ∀ i x, 0 < M.density θ x →
      DifferentiableAt ℝ (fun t : ℝ => M.density (θ + t • EuclideanSpace.single i 1) x) 0)
    -- USER-INPUT: the statistic has a finite second moment at `θ`
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ))
    -- LEAN-ONLY: measurability of each coordinate score, which is built from a `deriv` in
    -- the parameter and therefore carries no measurability in `x` by construction
    (hmeas : ∀ i, AEStronglyMeasurable (fun x => scoreVec M θ x i) μ)
    -- LEAN-ONLY: finiteness of the diagonal information entries as Bochner integrals; the
    -- off-diagonal entries then converge by Cauchy–Schwarz
    (hscore_int : ∀ i, Integrable (fun x => scoreVec M θ x i ^ 2 * M.density θ x) μ)
    -- USER-INPUT: every coordinate score has mean zero; classical regularity condition
    (hmean0 : ∀ i, ∫ x, scoreVec M θ x i * M.density θ x ∂μ = 0)
    -- USER-INPUT: the information matrix is nonsingular; it fails to be so exactly when the
    -- coordinate scores are linearly dependent
    (hIpos : (infoMatrix M μ θ).PosDef)
    -- USER-INPUT: the expectation of the statistic has a partial derivative `α i` in each
    -- coordinate direction
    (hα : ∀ i, HasDerivAt
      (fun t : ℝ => ∫ x, δ x * M.density (θ + t • EuclideanSpace.single i 1) x ∂μ) (α i) 0)
    -- USER-INPUT: those derivatives are obtained by differentiating under the integral sign
    (hswap : ∀ i, α i = ∫ x, δ x * scoreVec M θ x i * M.density θ x ∂μ) :
    α ⬝ᵥ ((infoMatrix M μ θ)⁻¹ *ᵥ α) ≤ variance δ (M.toMeasure μ θ) := by
  haveI hP : IsProbabilityMeasure (M.toMeasure μ θ) := by
    refine ⟨?_⟩
    rw [show M.toMeasure μ θ = μ.withDensity (fun x => ENNReal.ofReal (M.density θ x)) from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hpdf.density_integrable θ)
        (Filter.Eventually.of_forall (M.density_nonneg θ)), hpdf.density_integral_eq_one θ,
      ENNReal.ofReal_one]
  set ψ : Fin s → 𝓧 → ℝ := fun i x => scoreVec M θ x i with hψdef
  -- integration against `P_θ` is integration of `g · p_θ` against `μ`
  have hint_tm : ∀ g : 𝓧 → ℝ, ∫ x, g x ∂(M.toMeasure μ θ) = ∫ x, g x * M.density θ x ∂μ := by
    intro g
    rw [show M.toMeasure μ θ = μ.withDensity (fun x => ENNReal.ofReal (M.density θ x)) from rfl,
      integral_withDensity_eq_integral_toReal_smul (M.density_meas θ).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (M.density_nonneg θ x), smul_eq_mul]; ring
  -- each coordinate score has mean zero under `P_θ`
  have hmean0P : ∀ i, ∫ x, ψ i x ∂(M.toMeasure μ θ) = 0 := by
    intro i; rw [hint_tm]; exact hmean0 i
  -- and is square-integrable under `P_θ`
  have hψmem : ∀ i, MemLp (ψ i) 2 (M.toMeasure μ θ) := by
    intro i
    have hmeasP : AEStronglyMeasurable (ψ i) (M.toMeasure μ θ) :=
      (hmeas i).mono_ac (withDensity_absolutelyContinuous _ _)
    have hintP : Integrable (fun x => ψ i x ^ 2) (M.toMeasure μ θ) := by
      rw [show M.toMeasure μ θ = μ.withDensity (fun x => ENNReal.ofReal (M.density θ x)) from rfl,
        integrable_withDensity_iff (M.density_meas θ).ennreal_ofReal
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine (integrable_congr (Filter.Eventually.of_forall fun x => ?_)).2 (hscore_int i)
      rw [ENNReal.toReal_ofReal (M.density_nonneg θ x)]
    exact (memLp_two_iff_integrable_sq hmeasP).2 hintP
  -- covariance with a mean-zero variable is the uncentered second moment
  have hcov_mean0 : ∀ (X Y : 𝓧 → ℝ), MemLp X 2 (M.toMeasure μ θ) → MemLp Y 2 (M.toMeasure μ θ) →
      (∫ x, Y x ∂(M.toMeasure μ θ)) = 0 →
      covariance X Y (M.toMeasure μ θ) = ∫ x, X x * Y x ∂(M.toMeasure μ θ) := by
    intro X Y hX hY hY0
    rw [covariance_eq_sub hX hY, hY0, mul_zero, sub_zero]
    simp only [Pi.mul_apply]
  -- the information matrix is the covariance matrix of the coordinate scores
  have hC : ∀ i j, infoMatrix M μ θ i j = covariance (ψ i) (ψ j) (M.toMeasure μ θ) := by
    intro i j
    rw [hcov_mean0 _ _ (hψmem i) (hψmem j) (hmean0P j), hint_tm]
    simp only [infoMatrix, hψdef]
  -- the gradient is the covariance vector of `δ` with the coordinate scores
  have hγ : ∀ i, α i = covariance δ (ψ i) (M.toMeasure μ θ) := by
    intro i
    rw [hcov_mean0 _ _ hδ2 (hψmem i) (hmean0P i), hint_tm, hswap i]
  exact covariance_matrix_inequality (M.toMeasure μ θ) δ ψ hδ2 hψmem
    (infoMatrix M μ θ) hC hIpos α hγ

end StatLean.PointEstimation
