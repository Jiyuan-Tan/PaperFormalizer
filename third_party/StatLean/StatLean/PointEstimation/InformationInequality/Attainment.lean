module
public import StatLean.PointEstimation.InformationInequality.CramerRao
public import StatLean.PointEstimation.ExponentialFamily.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

/-!
# Attainment of the information bound: exponential families

The information inequality comes from Cauchy–Schwarz, so it is an equality exactly when the
statistic is an affine function of the score,
$$ \delta(x) = a\,\frac{\partial}{\partial\theta}\log p_\theta(x) + b, $$
with `a, b` allowed to depend on `θ`. If this happens *at every* parameter value with `a`
and `b` free of `x`, the family is forced to be an exponential family in which `δ` is the
natural statistic: the density takes the form `exp(η(θ) δ(x) − B(θ)) h(x)`.

Contents:
* `cramer_rao_attained_of_affine` — the easy direction: an affine function of the score
  attains the bound, with no regularity conditions on the family;
* `score_ae_eq_of_cramer_rao_attained` — the equality case of Cauchy–Schwarz: attainment at
  `θ`, with the differentiation-under-the-integral swap and `g'(θ) ≠ 0`, makes the score an
  affine function of `δ` almost surely.

**Not present: the converse.** The source's converse — attainment at every parameter value
forces the exponential form — was formalized, found to be **false as written**, and has been
removed rather than carried as a debt. The attainment identity `var_θ(δ) = g'(θ)²/I(θ)` is
vacuous wherever `g'(θ) = 0` and `var_θ(δ) = 0`: Cauchy–Schwarz equality then holds trivially
with `δ` a.e. constant and constrains the score not at all. The Gaussian location family
`p_θ(x) = φ(x − θ)` with `δ ≡ 0` satisfies every hypothesis, yet is not exponential in `δ`
(comparing `θ = 1` with `θ = 0` would force `φ(x−1)/φ(x) = e^{x−1/2}` to be a.e. constant).
The source carries `g'(θ) ≠ 0` implicitly, through the companion identity `I(θ) = η'(θ)g'(θ)`.
Restoring the converse is a **signature change** — add `∀ θ, g' θ ≠ 0` — and a decision for
the library, not a proof obligation; the full analysis, with the counterexample and the
repair, is in `notes/point_estimation/defective-statements.tex`. Note that
`score_ae_eq_of_cramer_rao_attained` above already supplies the Cauchy–Schwarz equality step
that a repaired converse would consume.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.5 (The
Information Inequality), Theorem 5.12 (the bound is attained iff the family is exponential and
the estimator is affine in the natural statistic). (`TPE2 §2.5 Thm 5.12`.)

**Proof formalization notes.**
* The easy direction is stated at a *single* parameter value and assumes nothing about the
  family beyond the mean-zero score and a positive, finite information at that value: it is
  the equality case of Cauchy–Schwarz, and the constants `a, b` may depend on `θ`. If they
  do depend on `θ`, the affine function of the score is not an estimator, and no estimator
  attains the bound — which is why the converse quantifies over all parameter values with
  one fixed `δ`.
* The conclusion carries measurability and non-negativity of the carrier `h`, so that the
  produced representation can be fed to the exponential-family constructor that absorbs a
  carrier into the reference measure.
* The classical statement also records the accompanying identities relating the natural
  parameter, the estimand and the information — the estimator equals `(g'(θ)/I(θ))` times
  the score plus `g(θ)`, and `I(θ) = η'(θ) g'(θ)`. They are consequences of the
  representation and of the easy direction, and are not part of this conclusion.

**Bibliographic comments.** That equality in the information inequality characterizes
exponential families with the estimator as natural statistic was observed already by
C. R. Rao ("Information and the accuracy attainable in the estimation of statistical
parameters," *Bull. Calcutta Math. Soc.* **37** (1945), 81–91) and H. Cramér (*Mathematical
Methods of Statistics*, Princeton University Press, 1946, §32.3), in the spirit of the
characterizations of exponential families by G. Darmois ("Sur les lois de probabilité à
estimation exhaustive," *C. R. Acad. Sci. Paris* **200** (1935), 1265–1266). Necessary and
sufficient conditions for attainment under weak regularity are due to R. A. Wijsman ("On the
attainment of the Cramér–Rao lower bound," *Ann. Statist.* **1** (1973), 538–542) and
V. Fabian and J. Hannan ("On the Cramér–Rao inequality," *Ann. Statist.* **5** (1977),
197–205).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **Affine functions of the score attain the information bound.** If, at the parameter
value `θ`, the statistic is almost surely `a · ℓ̇_θ + b` for constants `a, b`, then its
variance equals the information bound `(E_θ[δ ℓ̇_θ])² / I(θ)`.

No regularity of the family is needed: this is the equality case of Cauchy–Schwarz, applied
to the centered score. The constants are allowed to depend on `θ` — in which case the affine
function is not an estimator and no estimator attains the bound. -/
theorem cramer_rao_attained_of_affine (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    (θ : ℝ) (δ : 𝓧 → ℝ) (a b : ℝ)
    -- LEAN-ONLY: measurability of the score, which is built from a `deriv` in the parameter
    (hmeas : AEStronglyMeasurable (score M θ) μ)
    -- USER-INPUT: the information is positive (and hence finite as a Bochner integral)
    (hI : 0 < fisherInfo M μ θ)
    -- USER-INPUT: the score has mean zero; classical regularity condition
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0)
    -- USER-INPUT: the statistic is an affine function of the score at `θ`
    (haffine : ∀ᵐ x ∂(M.toMeasure μ θ), δ x = a * score M θ x + b) :
    variance δ (M.toMeasure μ θ)
      = (∫ x, δ x * score M θ x * M.density θ x ∂μ) ^ 2 / fisherInfo M μ θ := by
  haveI hP := isProbabilityMeasure_toMeasure M μ hpdf θ
  have hIne : fisherInfo M μ θ ≠ 0 := hI.ne'
  -- positivity of the information makes the second moment of the score genuinely integrable
  have hscore_int : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ := by
    by_contra h
    rw [fisherInfo, integral_undef h] at hI
    exact lt_irrefl 0 hI
  have hscoreL2 : MemLp (score M θ) 2 (M.toMeasure μ θ) := memLp_score M μ θ hmeas hscore_int
  have hmean0P : ∫ x, score M θ x ∂(M.toMeasure μ θ) = 0 := by
    rw [integral_toMeasure_eq]; exact hmean0
  have hI_eq : fisherInfo M μ θ = ∫ x, score M θ x ^ 2 ∂(M.toMeasure μ θ) := by
    rw [fisherInfo, integral_toMeasure_eq]
  -- the score is centered, so its variance is the information
  have hvarscore : variance (score M θ) (M.toMeasure μ θ) = fisherInfo M μ θ := by
    rw [variance_of_integral_eq_zero hscoreL2.aemeasurable hmean0P, hI_eq]
  -- `∫ δ · ℓ̇ = a · I`
  have hδscore : ∫ x, δ x * score M θ x ∂(M.toMeasure μ θ) = a * fisherInfo M μ θ := by
    have hae : (fun x => δ x * score M θ x)
        =ᵐ[M.toMeasure μ θ] fun x => a * score M θ x ^ 2 + b * score M θ x := by
      filter_upwards [haffine] with x hx; rw [hx]; ring
    rw [integral_congr_ae hae, integral_add (hscoreL2.integrable_sq.const_mul a)
      ((hscoreL2.integrable one_le_two).const_mul b), integral_const_mul, integral_const_mul,
      hmean0P, mul_zero, add_zero, hI_eq]
  -- variance of `δ = a·ℓ̇ + b` is `a²·I`
  have hvarδ : variance δ (M.toMeasure μ θ) = a ^ 2 * fisherInfo M μ θ := by
    rw [variance_congr haffine,
      variance_add_const (hscoreL2.const_mul a).aestronglyMeasurable b,
      variance_const_mul, hvarscore]
  rw [hvarδ, show (∫ x, δ x * score M θ x * M.density θ x ∂μ) = a * fisherInfo M μ θ from by
    rw [← integral_toMeasure_eq]; exact hδscore]
  rw [eq_div_iff hIne]
  ring

/-- **The equality case of Cauchy–Schwarz in the information inequality.**

Suppose that at `θ` the number `g'` is genuinely the covariance of `δ` with the score
(hypothesis `hcov`: this is exactly what differentiation under the integral sign delivers, and
it is *not* a consequence of `HasDerivAt (fun t => ∫ δ p_t) g' θ` alone), that `g' ≠ 0`, and
that the information bound `g'²/I(θ)` is attained. Then the score is `P_θ`-almost surely an
affine function of `δ`:
`ℓ̇_θ = (I(θ)/g') · (δ − E_θ δ)`.

Proof: the residual `δ − (g'/I)·ℓ̇_θ` has variance
`var δ − 2(g'/I)·cov + (g'/I)²·I = g'²/I − 2g'²/I + g'²/I = 0`, so it is a.s. constant, and
the constant is its mean `E_θ δ` because the score is centered.

This is the analytic content of the equality case, i.e. step 2 of the classical proof that
attainment at every parameter value forces an exponential family. That converse is *not*
formalized here: it is false as printed (see the file header), and restoring it needs the
nondegeneracy `g'(θ) ≠ 0` plus a `θ`-integration of this identity that is uniform in `x`. -/
theorem score_ae_eq_of_cramer_rao_attained (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    (θ : ℝ) (δ : 𝓧 → ℝ) (g' : ℝ)
    -- LEAN-ONLY: measurability of the score, which is built from a `deriv` in the parameter
    (hmeas : AEStronglyMeasurable (score M θ) μ)
    -- USER-INPUT: the statistic has a finite second moment at `θ`
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ))
    -- LEAN-ONLY: finiteness of the information as a Bochner integral
    (hscore_int : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ)
    -- USER-INPUT: the information is positive
    (hI : 0 < fisherInfo M μ θ)
    -- USER-INPUT: the score has mean zero; classical regularity condition
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0)
    -- USER-INPUT: `g'` is the covariance of `δ` with the score — the conclusion of
    -- differentiation under the integral sign, supplied here as data
    (hcov : ∫ x, δ x * score M θ x * M.density θ x ∂μ = g')
    -- USER-INPUT: the estimand really moves with the parameter
    (hg' : g' ≠ 0)
    -- USER-INPUT: the information bound is attained at `θ`
    (hattain : variance δ (M.toMeasure μ θ) = g' ^ 2 / fisherInfo M μ θ) :
    ∀ᵐ x ∂(M.toMeasure μ θ), score M θ x
      = fisherInfo M μ θ / g' * (δ x - ∫ y, δ y ∂(M.toMeasure μ θ)) := by
  haveI hP := isProbabilityMeasure_toMeasure M μ hpdf θ
  have hIne : fisherInfo M μ θ ≠ 0 := hI.ne'
  have hscoreL2 : MemLp (score M θ) 2 (M.toMeasure μ θ) := memLp_score M μ θ hmeas hscore_int
  have hscore_intP : Integrable (score M θ) (M.toMeasure μ θ) := hscoreL2.integrable one_le_two
  have hδ_intP : Integrable δ (M.toMeasure μ θ) := hδ2.integrable one_le_two
  have hmean0P : ∫ x, score M θ x ∂(M.toMeasure μ θ) = 0 := by
    rw [integral_toMeasure_eq M μ θ (score M θ)]; exact hmean0
  have hI_eq : fisherInfo M μ θ = ∫ x, score M θ x ^ 2 ∂(M.toMeasure μ θ) := by
    rw [fisherInfo]
    exact (integral_toMeasure_eq M μ θ fun x => score M θ x ^ 2).symm
  have hcovP : ∫ x, δ x * score M θ x ∂(M.toMeasure μ θ) = g' := by
    rw [integral_toMeasure_eq M μ θ fun x => δ x * score M θ x]; exact hcov
  set m := ∫ x, δ x ∂(M.toMeasure μ θ) with hm
  set c : ℝ := g' / fisherInfo M μ θ with hcdef
  have hδmL2 : MemLp (fun x => δ x - m) 2 (M.toMeasure μ θ) := hδ2.sub (memLp_const m)
  have hYL2 : MemLp (fun x => δ x - c * score M θ x) 2 (M.toMeasure μ θ) :=
    hδ2.sub (hscoreL2.const_mul c)
  have i1 : Integrable (fun x => (δ x - m) ^ 2) (M.toMeasure μ θ) := hδmL2.integrable_sq
  have i2 : Integrable (fun x => (δ x - m) * score M θ x) (M.toMeasure μ θ) :=
    memLp_one_iff_integrable.mp (hscoreL2.mul' hδmL2)
  have i3 : Integrable (fun x => score M θ x ^ 2) (M.toMeasure μ θ) := hscoreL2.integrable_sq
  have hEY : ∫ x, (δ x - c * score M θ x) ∂(M.toMeasure μ θ) = m := by
    rw [integral_sub hδ_intP (hscore_intP.const_mul c), integral_const_mul, hmean0P,
      mul_zero, sub_zero]
  have hvar : variance δ (M.toMeasure μ θ) = ∫ x, (δ x - m) ^ 2 ∂(M.toMeasure μ θ) := by
    rw [variance_eq_integral hδ2.aemeasurable, ← hm]
  have hvarδ : ∫ x, (δ x - m) ^ 2 ∂(M.toMeasure μ θ) = g' ^ 2 / fisherInfo M μ θ := by
    rw [← hvar, hattain]
  have hcross : ∫ x, (δ x - m) * score M θ x ∂(M.toMeasure μ θ) = g' := by
    have hsplit : (fun x => (δ x - m) * score M θ x)
        = fun x => δ x * score M θ x - m * score M θ x := by funext x; ring
    rw [hsplit, integral_sub (memLp_one_iff_integrable.mp (hscoreL2.mul' hδ2))
      (hscore_intP.const_mul m), integral_const_mul, hmean0P, mul_zero, sub_zero, hcovP]
  -- the residual `δ − c·ℓ̇` has zero variance
  have hvarY : variance (fun x => δ x - c * score M θ x) (M.toMeasure μ θ) = 0 := by
    rw [variance_eq_integral hYL2.aemeasurable, hEY]
    have hfun : (fun x => (δ x - c * score M θ x - m) ^ 2)
        = fun x => (δ x - m) ^ 2 - 2 * c * ((δ x - m) * score M θ x)
            + c ^ 2 * score M θ x ^ 2 := by funext x; ring
    have iC : Integrable (fun x => 2 * c * ((δ x - m) * score M θ x)) (M.toMeasure μ θ) :=
      i2.const_mul (2 * c)
    have iA : Integrable
        (fun x => (δ x - m) ^ 2 - 2 * c * ((δ x - m) * score M θ x)) (M.toMeasure μ θ) :=
      i1.sub iC
    have iB : Integrable (fun x => c ^ 2 * score M θ x ^ 2) (M.toMeasure μ θ) :=
      i3.const_mul (c ^ 2)
    rw [hfun, integral_add iA iB, integral_sub i1 iC, integral_const_mul, integral_const_mul,
      hvarδ, hcross, ← hI_eq, hcdef]
    field_simp
    try ring
  have hae := ae_eq_integral_of_variance_eq_zero hYL2 hvarY
  filter_upwards [hae] with x hx
  rw [hEY] at hx
  have h1 : c * score M θ x = δ x - m := by linarith
  have h2 : fisherInfo M μ θ / g' * (δ x - m)
      = fisherInfo M μ θ / g' * (c * score M θ x) := by rw [h1]
  rw [h2, hcdef]
  field_simp

end StatLean.PointEstimation
