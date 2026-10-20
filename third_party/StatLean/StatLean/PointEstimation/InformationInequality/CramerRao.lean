module
public import StatLean.PointEstimation.InformationInequality.Basic
public import StatLean.PointEstimation.UMVU.Defs
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Algebra.QuadraticDiscriminant

@[expose] public section

/-!
# The information inequality (Cramér–Rao bound)

For a dominated family with a common support whose score has mean zero and positive
information, every square-integrable statistic `δ` whose expectation may be differentiated
under the integral sign satisfies
$$ \operatorname{var}_\theta(\delta) \;\ge\;
   \frac{\bigl(\tfrac{\partial}{\partial\theta} E_\theta \delta\bigr)^2}{I(\theta)} . $$
Writing `E_θ δ = g(θ) + b(θ)` for an estimand `g` and the bias `b` of `δ`, the same
inequality reads `var_θ(δ) ≥ (b'(θ) + g'(θ))² / I(θ)`: no unbiasedness is needed, the bias
simply enters through its derivative.

Contents:
* `cramer_rao` — the information inequality in the form with the derivative of the
  expectation supplied as data;
* `cramer_rao_of_deriv` — the bias form, for an estimator of a differentiable estimand
  which need not be unbiased.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.5 (The
Information Inequality), Theorem 5.10 (the information inequality: `var δ ≥ g′(θ)²/I(θ)`).
(`TPE2 §2.5 Thm 5.10`.)

**Proof formalization notes.**
* The proof is the covariance inequality `var(δ) ≥ cov(δ, ψ)² / var(ψ)` (Cauchy–Schwarz
  for the centered variables) applied to `ψ = ℓ̇_θ`, the score: the mean-zero property turns
  `var(ψ)` into `I(θ)` and turns `cov(δ, ψ)` into `∫ δ · ∂_θ p_θ dμ`, which the
  differentiation-under-the-integral hypothesis identifies with `∂_θ E_θ δ`.
* The derivative of `t ↦ ∫ δ p_t dμ` is supplied as an explicit `HasDerivAt` datum together
  with the identification `hswap` of its value as `∫ δ ∂_θ p_θ dμ`; these are exactly the
  two classical conditions on the estimator. They are *conditions*, not consequences: the
  companion file `InformationInequality.DensityRegularity` discharges both from a
  dominated-difference-quotient condition on the family alone.
* The common-support condition is what lets the junk-safe score be traded for the density
  derivative (`score_mul_density_eq_deriv`); without it the two integrals
  `∫ δ ℓ̇_θ p_θ dμ` and `∫ δ ∂_θ p_θ dμ` differ by the contribution of the set where the
  density vanishes, and the inequality is false in general.
* The bound is written as `g'^2 / I(θ) ≤ var(δ)` rather than with the division on the
  larger side, so that the vanishing-information case falls back on Lean's `x / 0 = 0`
  convention harmlessly; the hypothesis `0 < I(θ)` is nonetheless kept, as in the classical
  statement.

**Bibliographic comments.** The inequality was obtained independently by C. R. Rao
("Information and the accuracy attainable in the estimation of statistical parameters,"
*Bull. Calcutta Math. Soc.* **37** (1945), 81–91) and H. Cramér (*Mathematical Methods of
Statistics*, Princeton University Press, 1946, §32.3), with earlier forms in M. Fréchet
("Sur l'extension de certaines évaluations statistiques au cas de petits échantillons,"
*Rev. Inst. Int. Statist.* **11** (1943), 182–205) and G. Darmois ("Sur les limites de la
dispersion de certaines estimations," *Rev. Inst. Int. Statist.* **13** (1945), 9–15). The
underlying covariance inequality goes back to R. A. Fisher's information calculus
("Theory of statistical estimation," *Proc. Camb. Phil. Soc.* **22** (1925), 700–725).
-/

open MeasureTheory ProbabilityTheory

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

/-- Shared core of the information inequality: with the derivative of the expectation given
as `g'` (identified with `∫ δ ∂_θ p_θ` by `hswap`), the bound `g'² / I ≤ var δ` follows from
Cauchy–Schwarz applied to the centered statistic and the mean-zero score. -/
private theorem cramer_rao_core (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    (hpdf : IsPDFOf M μ) (hsupp : HasCommonSupport M) (θ : ℝ) (δ : 𝓧 → ℝ) (g' : ℝ)
    (hmeas : AEStronglyMeasurable (score M θ) μ)
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ))
    (hscore_int : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ)
    (hI : 0 < fisherInfo M μ θ)
    (hswap : g' = ∫ x, δ x * deriv (fun t => M.density t x) θ ∂μ)
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0) :
    g' ^ 2 / fisherInfo M μ θ ≤ variance δ (M.toMeasure μ θ) := by
  haveI hP := isProbabilityMeasure_toMeasure M μ hpdf θ
  have hscoreL2 : MemLp (score M θ) 2 (M.toMeasure μ θ) := memLp_score M μ θ hmeas hscore_int
  set m := ∫ x, δ x ∂(M.toMeasure μ θ) with hm
  have hXL2 : MemLp (fun x => δ x - m) 2 (M.toMeasure μ θ) := hδ2.sub (memLp_const m)
  have hmean0P : ∫ x, score M θ x ∂(M.toMeasure μ θ) = 0 := by
    rw [integral_toMeasure_eq M μ θ (score M θ)]; exact hmean0
  have hscore_intP : Integrable (score M θ) (M.toMeasure μ θ) := hscoreL2.integrable one_le_two
  have hδscore : Integrable (fun x => δ x * score M θ x) (M.toMeasure μ θ) :=
    memLp_one_iff_integrable.mp (hscoreL2.mul' hδ2)
  have hg'core : ∫ x, δ x * score M θ x ∂(M.toMeasure μ θ) = g' := by
    rw [integral_toMeasure_eq M μ θ (fun x => δ x * score M θ x), hswap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [mul_assoc, score_mul_density_eq_deriv hsupp]
  have hcenter : ∫ x, (δ x - m) * score M θ x ∂(M.toMeasure μ θ) = g' := by
    have hsplit : (fun x => (δ x - m) * score M θ x)
        = fun x => δ x * score M θ x - m * score M θ x := by funext x; ring
    rw [hsplit, integral_sub hδscore (hscore_intP.const_mul m), integral_const_mul, hmean0P,
      mul_zero, sub_zero, hg'core]
  have hvar : variance δ (M.toMeasure μ θ) = ∫ x, (δ x - m) ^ 2 ∂(M.toMeasure μ θ) := by
    rw [variance_eq_integral hδ2.aemeasurable, ← hm]
  have hI_eq : fisherInfo M μ θ = ∫ x, score M θ x ^ 2 ∂(M.toMeasure μ θ) := by
    rw [fisherInfo]
    exact (integral_toMeasure_eq M μ θ (fun x => score M θ x ^ 2)).symm
  have hcs := sq_integral_mul_le hXL2 hscoreL2
  rw [hcenter, ← hvar, ← hI_eq] at hcs
  rw [div_le_iff₀ hI]
  exact hcs

/-- **The information inequality (Cramér–Rao bound).** For a dominated family with a
common support, mean-zero score and positive information, and for a square-integrable
statistic `δ` whose expectation `t ↦ E_t δ` is differentiable at `θ` with derivative `g'`
obtained by differentiating under the integral sign,
`(∂_θ E_θ δ)² / I(θ) ≤ var_θ(δ)`.

For an unbiased estimator of an estimand `g` this is the familiar `g'(θ)² / I(θ)`; the
biased case is `cramer_rao_of_deriv`. -/
theorem cramer_rao (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ) (δ : 𝓧 → ℝ) (g' : ℝ)
    -- LEAN-ONLY: measurability of the score, which is built from a `deriv` in the parameter
    -- and therefore carries no measurability in `x` by construction; it is a consequence of
    -- the family-side regularity used in `cramer_rao_of_density_regular`, and only in this
    -- estimator-side shape does it have to be supplied
    (hmeas : AEStronglyMeasurable (score M θ) μ)
    -- USER-INPUT: the statistic has a finite second moment at `θ`; the first classical
    -- condition on the estimator
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ))
    -- LEAN-ONLY: finiteness of the information as a Bochner integral, so that `fisherInfo`
    -- is the genuine second moment of the score rather than the junk value `0`; redundant
    -- given positivity of the information below, kept as an explicit datum of this shape
    (hscore_int : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ)
    -- USER-INPUT: the information is positive; classical standing assumption
    (hI : 0 < fisherInfo M μ θ)
    -- USER-INPUT: the expectation of the statistic is differentiable at `θ`; the second
    -- classical condition on the estimator
    (hdiff : HasDerivAt (fun t => ∫ x, δ x * M.density t x ∂μ) g' θ)
    -- USER-INPUT: that derivative is obtained by differentiating under the integral sign
    (hswap : g' = ∫ x, δ x * deriv (fun t => M.density t x) θ ∂μ)
    -- USER-INPUT: the score has mean zero; classical regularity condition, implied by
    -- differentiation under the integral sign in the normalisation identity
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0) :
    g' ^ 2 / fisherInfo M μ θ ≤ variance δ (M.toMeasure μ θ) :=
  cramer_rao_core M μ hpdf hsupp θ δ g' hmeas hδ2 hscore_int hI hswap hmean0

/-- **The information inequality with bias.** If `δ` estimates `g` with bias `b`, so that
`E_t δ = g(t) + b(t)`, and both `g` and `b` are differentiable at `θ`, then
`(b'(θ) + g'(θ))² / I(θ) ≤ var_θ(δ)`.

Unbiasedness is *not* assumed: for `b = 0` this is the bound `g'(θ)² / I(θ)` for unbiased
estimators, and in general the bias enters only through its derivative, so an estimator can
beat the unbiased bound only by having a nonconstant bias. -/
theorem cramer_rao_of_deriv (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ) (δ : 𝓧 → ℝ) (g b : ℝ → ℝ) (g' b' : ℝ)
    -- USER-INPUT: `b` is the bias of `δ` as an estimator of `g`
    (hbias : ∀ t, ∫ x, δ x * M.density t x ∂μ = g t + b t)
    -- USER-INPUT: the estimand is differentiable at `θ`
    (hg : HasDerivAt g g' θ)
    -- USER-INPUT: the bias is differentiable at `θ`
    (hb : HasDerivAt b b' θ)
    -- LEAN-ONLY: measurability of the score (see `cramer_rao`)
    (hmeas : AEStronglyMeasurable (score M θ) μ)
    -- USER-INPUT: the statistic has a finite second moment at `θ`
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ))
    -- LEAN-ONLY: finiteness of the information as a Bochner integral
    (hscore_int : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ)
    -- USER-INPUT: the information is positive; classical standing assumption
    (hI : 0 < fisherInfo M μ θ)
    -- USER-INPUT: the derivative of the expectation is obtained by differentiating under
    -- the integral sign
    (hswap : b' + g' = ∫ x, δ x * deriv (fun t => M.density t x) θ ∂μ)
    -- USER-INPUT: the score has mean zero; classical regularity condition
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0) :
    (b' + g') ^ 2 / fisherInfo M μ θ ≤ variance δ (M.toMeasure μ θ) :=
  cramer_rao_core M μ hpdf hsupp θ δ (b' + g') hmeas hδ2 hscore_int hI hswap hmean0

end StatLean.PointEstimation
