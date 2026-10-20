module
public import StatLean.PointEstimation.InformationInequality.Defs
public import StatLean.PointEstimation.Model.Defs
public import StatLean.AsymptoticStatistics.ParametricFamily.FisherInformation
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Score identities and elementary properties of the Fisher information

The score of a dominated family is the logarithmic derivative of its density,
`ℓ̇_θ(x) = ∂_θ p_θ(x) / p_θ(x)`, and the information is its second moment. Under
differentiation under the integral sign in the normalisation identity
`∫ p_θ dμ = 1`, the score has mean zero, so the information is exactly the variance
of the score; with one more derivative it is also the negated expected curvature of
the log-likelihood:
$$ E_\theta\bigl[\ell̇_\theta(X)\bigr] = 0,\qquad
   I(\theta) = \operatorname{var}_\theta \ell̇_\theta(X)
             = -E_\theta\Bigl[\tfrac{\partial^2}{\partial\theta^2}\log p_\theta(X)\Bigr]. $$

Contents:
* `HasCommonSupport` — the regularity condition that the positivity set of the density
  does not depend on the parameter (used throughout to control the junk-safe score off
  the support);
* `score_mul_density_eq_deriv` — the identity `ℓ̇_θ · p_θ = ∂_θ p_θ` that makes the
  junk-safe score integrate correctly;
* `integral_score_eq_zero` — the score has mean zero;
* `fisherInfo_eq_variance_score` — the information is the variance of the score;
* `fisherInfo_eq_neg_integral_secondDeriv` — the negated-curvature expression;
* `reparam`, `fisherInfo_reparam` — the information transforms by the squared derivative
  of the reparametrization, `I^{*}(\xi) = I(h(\xi))\,h'(\xi)^2`;
* `fisherInfo_eq_asymptoticStatistics` — the bridge identifying the density-derived
  information with the bilinear Fisher-information form of the asymptotics area,
  evaluated on the derived score.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.5 (The
Information Inequality), the score identities (zero mean, information as the score variance).
(`TPE2 §2.5`.)

**Proof formalization notes.**
* The score is junk-safe (`0/0 = 0`), so off the support `ℓ̇_θ · p_θ = 0` while
  `∂_θ p_θ` need not vanish; the common-support condition repairs this, because it forces
  `t ↦ p_t(x)` to be identically zero at every `x` outside the support. This is why
  `HasCommonSupport` — a genuine condition of the classical theory, not a Lean artifact —
  appears in every statement that trades the score against the density derivative.
* Differentiation under the integral sign is never derived here: it is an explicit
  `HasDerivAt` hypothesis about the map `t ↦ ∫ p_t dμ` (respectively `t ↦ ∫ ∂_t p_t dμ`),
  which is exactly the classical regularity condition. Sufficient dominated-convergence
  conditions on the family alone are supplied in `InformationInequality.DensityRegularity`.
* `fisherInfo_eq_variance_score` is stated with the model measure `μ.withDensity p_θ`
  (`ParametricFamily.toMeasure`), so that the right-hand side is the variance of the score
  as a random variable under `P_θ`, matching the probabilistic reading.
* The bridge lemma evaluates the asymptotics-area bilinear form at the unit vectors of the
  one-dimensional parameter space; there the real inner product is multiplication, so the
  bilinear form reduces to the second moment of the derived score.

**Bibliographic comments.** The score function and the information it carries were
introduced by R. A. Fisher ("Theory of statistical estimation," *Proc. Camb. Phil. Soc.*
**22** (1925), 700–725), building on his earlier "On the mathematical foundations of
theoretical statistics," *Philos. Trans. Roy. Soc. London Ser. A* **222** (1922), 309–368.
The variance and negated-curvature expressions, and the transformation rule under
reparametrization, are part of the systematic treatment in H. Cramér (*Mathematical
Methods of Statistics*, Princeton University Press, 1946, §32.3) and C. R. Rao
("Information and the accuracy attainable in the estimation of statistical parameters,"
*Bull. Calcutta Math. Soc.* **37** (1945), 81–91).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-! ## The common-support condition -/

/-- The **common-support condition**: the positivity set `{x | p_θ(x) > 0}` of the density
is the same for every parameter value.

This formalizes the classical regularity requirement that the members of the family are
mutually absolutely continuous, so that likelihood ratios and logarithmic derivatives are
defined on one fixed set. Edge behavior: it is vacuously satisfied by families with
everywhere-positive densities, and it is a genuine restriction for families whose support
moves with the parameter (uniform-type families), which is precisely where the information
inequality fails. -/
def HasCommonSupport {Θ : Type*} (M : ParametricFamily 𝓧 Θ) : Prop :=
  ∀ θ θ' x, 0 < M.density θ x → 0 < M.density θ' x

/-- Contrapositive form of the common-support condition: where one density vanishes, they
all vanish. -/
lemma density_eq_zero_of_commonSupport {Θ : Type*} {M : ParametricFamily 𝓧 Θ}
    (hsupp : HasCommonSupport M) {θ θ' : Θ} {x : 𝓧} (h : M.density θ x = 0) :
    M.density θ' x = 0 := by
  by_contra hne
  have hpos : 0 < M.density θ' x := lt_of_le_of_ne (M.density_nonneg θ' x) (Ne.symm hne)
  have hcontra := hsupp θ' θ x hpos
  rw [h] at hcontra
  exact lt_irrefl 0 hcontra

/-- The junk-safe score integrates correctly: `ℓ̇_θ(x) · p_θ(x) = ∂_θ p_θ(x)` pointwise,
under the common-support condition. Off the support the parameter map `t ↦ p_t(x)` is
identically zero, so both sides vanish; on the support the division cancels. -/
lemma score_mul_density_eq_deriv {M : ParametricFamily 𝓧 ℝ}
    (hsupp : HasCommonSupport M) (θ : ℝ) (x : 𝓧) :
    score M θ x * M.density θ x = deriv (fun t => M.density t x) θ := by
  rcases eq_or_ne (M.density θ x) 0 with h | h
  · have hzero : (fun t => M.density t x) = fun _ => (0 : ℝ) :=
      funext fun _ => density_eq_zero_of_commonSupport hsupp h
    rw [show deriv (fun t => M.density t x) θ = 0 by rw [hzero]; simp]
    simp [score, h]
  · simp only [score]
    exact div_mul_cancel₀ _ h

/-! ## Auxiliary bridges between `μ` and the model measure `P_θ` -/

/-- Integration against the model measure `P_θ = μ.withDensity p_θ` is integration of
`g · p_θ` against `μ`. -/
lemma integral_toMeasure_eq (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧) (θ : ℝ)
    (g : 𝓧 → ℝ) :
    ∫ x, g x ∂(M.toMeasure μ θ) = ∫ x, g x * M.density θ x ∂μ := by
  rw [show M.toMeasure μ θ = μ.withDensity (fun x => ENNReal.ofReal (M.density θ x)) from rfl,
    integral_withDensity_eq_integral_toReal_smul (M.density_meas θ).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (M.density_nonneg θ x), smul_eq_mul]
  ring

/-- The model measure `P_θ` of a probability-density family is a probability measure. -/
lemma isProbabilityMeasure_toMeasure (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    (hpdf : IsPDFOf M μ) (θ : ℝ) : IsProbabilityMeasure (M.toMeasure μ θ) := by
  refine ⟨?_⟩
  rw [show M.toMeasure μ θ = μ.withDensity (fun x => ENNReal.ofReal (M.density θ x)) from rfl,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hpdf.density_integrable θ)
      (Filter.Eventually.of_forall (M.density_nonneg θ)), hpdf.density_integral_eq_one θ,
    ENNReal.ofReal_one]

/-- The score is square-integrable under the model measure `P_θ`, from measurability and
finiteness of the information. -/
lemma memLp_score (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧) (θ : ℝ)
    (hmeas : AEStronglyMeasurable (score M θ) μ)
    (hint : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ) :
    MemLp (score M θ) 2 (M.toMeasure μ θ) := by
  have hmeasP : AEStronglyMeasurable (score M θ) (M.toMeasure μ θ) :=
    hmeas.mono_ac (withDensity_absolutelyContinuous _ _)
  have hintP : Integrable (fun x => score M θ x ^ 2) (M.toMeasure μ θ) := by
    rw [show M.toMeasure μ θ = μ.withDensity (fun x => ENNReal.ofReal (M.density θ x)) from rfl,
      integrable_withDensity_iff (M.density_meas θ).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine (integrable_congr (Filter.Eventually.of_forall fun x => ?_)).2 hint
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ x)]
  exact (memLp_two_iff_integrable_sq hmeasP).2 hintP

/-! ## Mean-zero score and the two expressions for the information -/

/-- **The score has mean zero**: `E_θ[ℓ̇_θ(X)] = 0`.

Differentiating the normalisation identity `∫ p_t dμ = 1` under the integral sign gives
`∫ ∂_θ p_θ dμ = 0`, and the common-support condition identifies that integrand with
`ℓ̇_θ · p_θ`. -/
theorem integral_score_eq_zero (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities (normalisation and
    -- integrability); the standing assumption of the dominated-model setting
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ)
    -- USER-INPUT: differentiation under the integral sign is permitted in the
    -- normalisation identity; classical regularity condition
    (hswap : HasDerivAt (fun t => ∫ x, M.density t x ∂μ)
      (∫ x, deriv (fun t => M.density t x) θ ∂μ) θ) :
    ∫ x, score M θ x * M.density θ x ∂μ = 0 := by
  have hconst : (fun t => ∫ x, M.density t x ∂μ) = fun _ => (1 : ℝ) :=
    funext fun t => hpdf.density_integral_eq_one t
  have hderiv0 : HasDerivAt (fun t => ∫ x, M.density t x ∂μ) 0 θ := by
    rw [hconst]; exact hasDerivAt_const θ 1
  have hzero : (∫ x, deriv (fun t => M.density t x) θ ∂μ) = 0 := hswap.unique hderiv0
  rw [← hzero]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun x => score_mul_density_eq_deriv hsupp θ x)

/-- **The information is the variance of the score**: `I(θ) = var_θ ℓ̇_θ(X)`, the score
being centered by the previous theorem. -/
theorem fisherInfo_eq_variance_score (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ)
    -- USER-INPUT: differentiation under the integral sign in the normalisation identity
    (hswap : HasDerivAt (fun t => ∫ x, M.density t x ∂μ)
      (∫ x, deriv (fun t => M.density t x) θ ∂μ) θ)
    -- LEAN-ONLY: measurability of the score, which is built from a `deriv` in the
    -- parameter and therefore carries no measurability in `x` by construction
    (hmeas : AEStronglyMeasurable (score M θ) μ)
    -- USER-INPUT: the information is finite; the classical standing assumption making
    -- the second moment of the score a genuine variance
    (hint : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ) :
    fisherInfo M μ θ = variance (score M θ) (M.toMeasure μ θ) := by
  haveI hP := isProbabilityMeasure_toMeasure M μ hpdf θ
  have hmean : ∫ x, score M θ x ∂(M.toMeasure μ θ) = 0 := by
    rw [integral_toMeasure_eq]
    exact integral_score_eq_zero M μ hpdf hsupp θ hswap
  have hmeasP : AEStronglyMeasurable (score M θ) (M.toMeasure μ θ) :=
    hmeas.mono_ac (withDensity_absolutelyContinuous _ _)
  have hintP : Integrable (fun x => score M θ x ^ 2) (M.toMeasure μ θ) := by
    rw [show M.toMeasure μ θ = μ.withDensity (fun x => ENNReal.ofReal (M.density θ x)) from rfl,
      integrable_withDensity_iff (M.density_meas θ).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine (integrable_congr (Filter.Eventually.of_forall fun x => ?_)).2 hint
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ x)]
  have hL2 : MemLp (score M θ) 2 (M.toMeasure μ θ) :=
    (memLp_two_iff_integrable_sq hmeasP).2 hintP
  have hkey : (M.toMeasure μ θ)[score M θ ^ 2] = fisherInfo M μ θ := by
    rw [fisherInfo]
    simp_rw [Pi.pow_apply]
    exact integral_toMeasure_eq M μ θ (fun x => score M θ x ^ 2)
  rw [variance_eq_sub hL2, hmean, hkey]
  simp

/-- **Negated-curvature expression for the information**:
`I(θ) = -E_θ[∂²_θ log p_θ(X)]`.

Differentiating `log p_θ` twice splits the curvature into `(∂²_θ p_θ)/p_θ` minus the
squared score; the first term integrates to zero because the normalisation identity may be
differentiated twice under the integral sign. -/
theorem fisherInfo_eq_neg_integral_secondDeriv (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ)
    -- USER-INPUT: on the support, the density is differentiable in the parameter near `θ`;
    -- the first-order smoothness condition of the classical setting (off the support the
    -- parameter map is constant `0` by the common-support condition)
    (hdiff : ∀ x, 0 < M.density θ x →
      ∀ᶠ t in nhds θ, DifferentiableAt ℝ (fun s => M.density s x) t)
    -- USER-INPUT: on the support, the parameter derivative is again differentiable at `θ`;
    -- the classical second-order smoothness condition (equivalently, `∂²_θ log p_θ` exists
    -- on the common support)
    (hdiff2 : ∀ x, 0 < M.density θ x →
      DifferentiableAt ℝ (fun t => deriv (fun s => M.density s x) t) θ)
    -- USER-INPUT: differentiation under the integral sign in the normalisation identity, at
    -- every parameter value (needed here, not just at `θ`, so that the first derivative
    -- vanishes identically and may itself be differentiated)
    (hswap : ∀ t, HasDerivAt (fun u => ∫ x, M.density u x ∂μ)
      (∫ x, deriv (fun s => M.density s x) t ∂μ) t)
    -- USER-INPUT: the normalisation identity may be differentiated twice under the
    -- integral sign
    (hswap2 : HasDerivAt (fun t => ∫ x, deriv (fun s => M.density s x) t ∂μ)
      (∫ x, deriv (fun u => deriv (fun s => M.density s x) u) θ ∂μ) θ)
    -- LEAN-ONLY: integrability of the second parameter derivative, needed to split the
    -- integral of the curvature into its two terms
    (hint : Integrable (fun x => deriv (fun u => deriv (fun s => M.density s x) u) θ) μ)
    -- USER-INPUT: the information is finite
    (hI : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ) :
    fisherInfo M μ θ
      = -∫ x, deriv (fun u => deriv (fun s => Real.log (M.density s x)) u) θ
          * M.density θ x ∂μ := by
  -- pointwise: `∂²(log p)·p = ∂²p − (score)²·p`
  have hpt : ∀ x, deriv (fun u => deriv (fun s => Real.log (M.density s x)) u) θ * M.density θ x
      = deriv (fun u => deriv (fun s => M.density s x) u) θ - score M θ x ^ 2 * M.density θ x := by
    intro x
    rcases eq_or_lt_of_le (M.density_nonneg θ x) with hpx | hpos
    · have hz : (fun s => M.density s x) = fun _ => (0 : ℝ) :=
        funext fun s => density_eq_zero_of_commonSupport hsupp hpx.symm
      rw [← hpx, hz]
      simp
    · have hdiffθ : DifferentiableAt ℝ (fun s => M.density s x) θ := (hdiff x hpos).self_of_nhds
      have hcont : ContinuousAt (fun s => M.density s x) θ := hdiffθ.continuousAt
      have hlog_ev : (fun u => deriv (fun s => Real.log (M.density s x)) u)
          =ᶠ[nhds θ] fun u => deriv (fun s => M.density s x) u / M.density u x := by
        filter_upwards [hdiff x hpos, continuousAt_const.eventually_lt hcont hpos]
          with u hu hpu
        exact (hu.hasDerivAt.log hpu.ne').deriv
      rw [hlog_ev.deriv_eq,
        show (fun u => deriv (fun s => M.density s x) u / M.density u x)
            = (fun u => deriv (fun s => M.density s x) u) / fun u => M.density u x from rfl,
        deriv_div (hdiff2 x hpos) hdiffθ hpos.ne', score]
      have hne := hpos.ne'
      field_simp
  -- the first derivative of the normalisation vanishes at every parameter value
  have h1 : ∀ t, ∫ x, deriv (fun s => M.density s x) t ∂μ = 0 := by
    intro t
    refine (hswap t).unique ?_
    rw [show (fun u => ∫ x, M.density u x ∂μ) = fun _ => (1 : ℝ) from
      funext hpdf.density_integral_eq_one]
    exact hasDerivAt_const t 1
  -- hence the second derivative of the normalisation vanishes at `θ`
  have h2 : ∫ x, deriv (fun u => deriv (fun s => M.density s x) u) θ ∂μ = 0 := by
    refine hswap2.unique ?_
    rw [show (fun t => ∫ x, deriv (fun s => M.density s x) t ∂μ) = fun _ => (0 : ℝ) from
      funext h1]
    exact hasDerivAt_const θ 0
  -- split the curvature integral
  have key : ∫ x, deriv (fun u => deriv (fun s => Real.log (M.density s x)) u) θ
        * M.density θ x ∂μ
      = (∫ x, deriv (fun u => deriv (fun s => M.density s x) u) θ ∂μ) - fisherInfo M μ θ := by
    rw [fisherInfo, ← integral_sub hint hI]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [key, h2, zero_sub, neg_neg]

/-! ## Reparametrization -/

/-- The **reparametrized family** `ξ ↦ p_{h(ξ)}`: the same densities read along a
reparametrization `h` of the parameter. Measurability and non-negativity are inherited
pointwise; no regularity of `h` is required by the definition. -/
noncomputable def reparam (M : ParametricFamily 𝓧 ℝ) (h : ℝ → ℝ) : ParametricFamily 𝓧 ℝ where
  density ξ x := M.density (h ξ) x
  density_meas ξ := M.density_meas (h ξ)
  density_nonneg ξ x := M.density_nonneg (h ξ) x

/-- **Reparametrization rule for the information**: for `θ = h(ξ)` with `h` differentiable,
the information about `ξ` is `I^{*}(ξ) = I(h(ξ)) · h'(ξ)²`.

The information is therefore *not* a parametrization-invariant quantity — only the ratio
appearing in the information inequality is. -/
theorem fisherInfo_reparam (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧) (h : ℝ → ℝ)
    (ξ h' : ℝ)
    -- USER-INPUT: the reparametrization is differentiable at `ξ` with derivative `h'`
    (hh : HasDerivAt h h' ξ)
    -- USER-INPUT: on the support, the density is differentiable in the parameter at `h ξ`;
    -- the classical smoothness condition, needed for the chain rule (off the support both
    -- sides vanish, the junk-safe score being `0` there)
    (hdiff : ∀ x, 0 < M.density (h ξ) x → DifferentiableAt ℝ (fun t => M.density t x) (h ξ)) :
    fisherInfo (reparam M h) μ ξ = fisherInfo M μ (h ξ) * h' ^ 2 := by
  simp only [fisherInfo]
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  rcases eq_or_lt_of_le (M.density_nonneg (h ξ) x) with hden | hden
  · simp only [score, reparam]
    rw [← hden]; ring
  · have hf : HasDerivAt (fun s => M.density s x)
        (deriv (fun s => M.density s x) (h ξ)) (h ξ) := (hdiff x hden).hasDerivAt
    have hderiv : deriv (fun t => M.density (h t) x) ξ
        = deriv (fun s => M.density s x) (h ξ) * h' := (hf.comp ξ hh).deriv
    have hne : M.density (h ξ) x ≠ 0 := ne_of_gt hden
    simp only [score, reparam]
    rw [hderiv]
    field_simp

/-! ## Bridge to the bilinear Fisher information of the asymptotics area -/

/-- **Bridge lemma**: the density-derived information of this area is the bilinear
Fisher-information form of the asymptotics area, evaluated on the derived score at the unit
vectors of the one-dimensional parameter space.

The asymptotics-area form takes an arbitrary candidate score as an argument; here that
argument is instantiated with the score *computed from the densities*, which is what makes
the two notions comparable. -/
theorem fisherInfo_eq_asymptoticStatistics (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    (θ : ℝ) :
    fisherInfo M μ θ = AsymptoticStatistics.fisherInformation M μ θ (score M θ) 1 1 := by
  rw [fisherInfo, AsymptoticStatistics.fisherInformation]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  have h1 : inner ℝ (1 : ℝ) (score M θ x) = score M θ x := by
    rw [show inner ℝ (1 : ℝ) (score M θ x) = _ from RCLike.inner_apply 1 (score M θ x)]; simp
  rw [h1]; ring

end StatLean.PointEstimation
