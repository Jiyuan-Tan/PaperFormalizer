module
public import StatLean.PointEstimation.InformationInequality.CramerRao
public import StatLean.PointEstimation.InformationInequality.Additivity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
# Family-side regularity: the information inequality for *every* square-integrable statistic

The information inequality as stated with conditions on the estimator requires, for each
statistic separately, that its expectation may be differentiated under the integral sign.
That condition is undesirable: one would like a hypothesis on the *densities* alone, valid
once and for all. The classical device is a Lipschitz-type domination of the normalized
difference quotients of the density: if there are `ε > 0` and an envelope `b` with
$$ \Bigl|\frac{p_{\theta+\Delta}(x) - p_\theta(x)}{\Delta\, p_\theta(x)}\Bigr| \le b(x)
   \quad\text{for } 0 < |\Delta| < \varepsilon, \qquad E_\theta b^2 < \infty, $$
then Cauchy–Schwarz makes `|δ| b` integrable for every square-integrable `δ`, and dominated
convergence justifies passing the limit inside the integral. Consequently the information
inequality holds for *every* statistic with a finite second moment.

Contents:
* `HasDominatedDifferenceQuotient` — the domination condition on the normalized difference
  quotients of the density;
* `diff_under_integral_of_density_regular` — the dominated-convergence step: the expectation
  of any square-integrable statistic is differentiable, with derivative the covariance of
  the statistic with the score;
* `integral_score_eq_zero_of_density_regular` — the same applied to the constant statistic
  `1`: the mean-zero property of the score is a *consequence* of the domination condition;
* `cramer_rao_of_density_regular` — the information inequality under family-side conditions
  only, valid for every square-integrable statistic;
* `cramer_rao_iid` — the sample-size-`n` form, with `n I(θ)` in the denominator.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.5 (The
Information Inequality), Theorem 5.15 (the family-side regularity form, valid for every
square-integrable statistic). (`TPE2 §2.5 Thm 5.15`.)

**Proof formalization notes.**
* The domination condition is transcribed exactly as the classical one: the envelope `b` is
  required to be square-integrable under `P_θ` and to bound the *normalized* difference
  quotients `(p_{θ+Δ} − p_θ)/(Δ p_θ)` for all small nonzero increments; the bound is imposed
  `P_θ`-almost everywhere, which is where the quotient is meaningful (on the common support
  the denominator does not vanish). No uniformity in `θ` is assumed: the condition is local
  at the parameter value where the inequality is claimed.
* The conclusion of the dominated-convergence step is stated as a `HasDerivAt` of
  `t ↦ ∫ δ p_t dμ` whose value is `∫ δ ℓ̇_θ p_θ dμ`. Since the score has mean zero, that
  value is the covariance of `δ` with the score, which is the classical reading; both
  conclusions of the classical lemma (existence of the derivative, and its identification)
  are therefore contained in this single statement.
* `cramer_rao_of_density_regular` returns a conjunction rather than a bound with the
  derivative supplied as data: under family-side regularity the derivative is not an input
  but a consequence, so it is stated as part of the conclusion. Supplying it as a hypothesis
  would reintroduce exactly the estimator-side condition this theorem exists to remove.
* `cramer_rao_iid` follows the classical route: the information inequality for the sample,
  with the additivity of the information over independent observations substituted in the
  denominator. Its estimator-side conditions are stated for the sample; the family-side
  theorem above, applied to the product family, is what discharges them in applications.

**Bibliographic comments.** Regularity conditions of this Lipschitz type, and the resulting
"holds for all square-integrable estimators" form of the information inequality, are
discussed by H. Cramér (*Mathematical Methods of Statistics*, Princeton University Press,
1946, §32.3) and refined by R. A. Wijsman ("On the attainment of the Cramér–Rao lower
bound," *Ann. Statist.* **1** (1973), 538–542) and V. Fabian and J. Hannan ("On the
Cramér–Rao inequality," *Ann. Statist.* **5** (1977), 197–205), who gave conditions under
which the bound holds and is attained. The additivity used for the sample-size-`n` form is
R. A. Fisher's ("Theory of statistical estimation," *Proc. Camb. Phil. Soc.* **22** (1925),
700–725).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **dominated-difference-quotient condition** at `θ`: there are a radius `ε > 0` and
an envelope `b`, square-integrable under `P_θ`, such that the normalized difference
quotients of the density satisfy
`|(p_{θ+Δ}(x) − p_θ(x)) / (Δ p_θ(x))| ≤ b(x)` for every increment with `0 < |Δ| < ε`,
`P_θ`-almost everywhere.

This is the classical Lipschitz-type smoothness condition on the family; it is what makes
dominated convergence available uniformly in the estimator. Edge behavior: the bound is
imposed `P_θ`-a.e., so points outside the support impose no constraint (the quotient there
is Lean's junk value `0`), and increments `Δ = 0` are excluded since the quotient is not
defined for them. -/
def HasDominatedDifferenceQuotient (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧) (θ : ℝ) :
    Prop :=
  ∃ ε > 0, ∃ b : 𝓧 → ℝ, MemLp b 2 (M.toMeasure μ θ) ∧
    ∀ Δ : ℝ, 0 < |Δ| → |Δ| < ε → ∀ᵐ x ∂(M.toMeasure μ θ),
      |(M.density (θ + Δ) x - M.density θ x) / (Δ * M.density θ x)| ≤ b x

/-- **Differentiation under the integral sign from family-side regularity.** Under the
dominated-difference-quotient condition, the expectation of *any* square-integrable
statistic is differentiable at `θ`, with derivative `∫ δ ℓ̇_θ p_θ dμ` — the covariance of
the statistic with the score, the score being centered.

Cauchy–Schwarz bounds the integrand `|δ| · |difference quotient|` by `|δ| b`, which is
integrable because both factors are square-integrable; dominated convergence then exchanges
the limit and the integral. -/
-- TODO: the dominated-convergence core of the family-side differentiation-under-the-integral
-- step — bounding the difference quotients `δ · (p_{θ+Δ} − p_θ)/Δ` by the `L²` envelope
-- `|δ| · b · p_θ` (Cauchy–Schwarz) and passing to the limit — is the single sanctioned analytic
-- debt of this file; every downstream theorem is a genuine reduction to it.
private theorem diff_under_integral_core (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    (hpdf : IsPDFOf M μ) (hsupp : HasCommonSupport M) (θ : ℝ)
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    (hreg : HasDominatedDifferenceQuotient M μ θ) (δ : 𝓧 → ℝ)
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ)) :
    HasDerivAt (fun t => ∫ x, δ x * M.density t x ∂μ)
      (∫ x, δ x * score M θ x * M.density θ x ∂μ) θ := by
  haveI hP := isProbabilityMeasure_toMeasure M μ hpdf θ
  obtain ⟨ε, hε, b, hb2, hbound⟩ := hreg
  have htoM : M.toMeasure μ θ
      = μ.withDensity (fun x => ENNReal.ofReal (M.density θ x)) := rfl
  -- Replace `δ` by a genuinely measurable a.e. version `g`; all integrals only see it on the
  -- common support, where it agrees with `δ`, and vanish off it.
  set g : 𝓧 → ℝ := hδ2.aestronglyMeasurable.mk δ with hg_def
  have hg_meas : Measurable g := hδ2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hδg : δ =ᵐ[M.toMeasure μ θ] g := hδ2.aestronglyMeasurable.ae_eq_mk
  have hg2 : MemLp g 2 (M.toMeasure μ θ) := hδ2.ae_eq hδg
  have hδg_mu : ∀ᵐ x ∂μ, 0 < M.density θ x → δ x = g x := by
    rw [htoM] at hδg
    filter_upwards [(ae_withDensity_iff (M.density_meas θ).ennreal_ofReal).1 hδg] with x hx hpos
    exact hx (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hpos])
  -- the parametrized integrand and its centered target agree a.e. after the substitution
  have hprod_ae : ∀ t : ℝ, (fun x => δ x * M.density t x) =ᵐ[μ] fun x => g x * M.density t x := by
    intro t
    filter_upwards [hδg_mu] with x hx
    rcases eq_or_lt_of_le (M.density_nonneg θ x) with h0 | hpos
    · rw [density_eq_zero_of_commonSupport hsupp h0.symm, mul_zero, mul_zero]
    · rw [hx hpos]
  have htarget_ae : (fun x => δ x * score M θ x * M.density θ x)
      =ᵐ[μ] fun x => g x * score M θ x * M.density θ x := by
    filter_upwards [hδg_mu] with x hx
    rcases eq_or_lt_of_le (M.density_nonneg θ x) with h0 | hpos
    · rw [← h0, mul_zero, mul_zero]
    · rw [hx hpos]
  have hfun_eq : (fun t => ∫ x, δ x * M.density t x ∂μ)
      = fun t => ∫ x, g x * M.density t x ∂μ := funext fun t => integral_congr_ae (hprod_ae t)
  have hval_full : (∫ x, δ x * score M θ x * M.density θ x ∂μ)
      = ∫ x, g x * deriv (fun t => M.density t x) θ ∂μ := by
    rw [integral_congr_ae htarget_ae]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [mul_assoc, score_mul_density_eq_deriv hsupp]
  rw [hfun_eq, hval_full]
  set F : ℝ → ℝ := fun t => ∫ x, g x * M.density t x ∂μ with hF_def
  rw [hasDerivAt_iff_tendsto_slope]
  -- the difference-quotient integrand and its dominating envelope
  set Q : ℝ → 𝓧 → ℝ :=
    fun t x => g x * ((M.density t x - M.density θ x) / (t - θ)) with hQ_def
  set D : 𝓧 → ℝ := fun x => |g x| * b x * M.density θ x with hD_def
  have hQ_meas : ∀ t, AEStronglyMeasurable (Q t) μ := fun t =>
    (hg_meas.mul (((M.density_meas t).sub (M.density_meas θ)).div_const _)).aestronglyMeasurable
  -- `g · p_θ` is integrable (`g ∈ L¹(P_θ)`)
  have hgpθ_int : Integrable (fun x => g x * M.density θ x) μ := by
    have h := (integrable_withDensity_iff (M.density_meas θ).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).1 (hg2.integrable one_le_two)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ x)]
  -- the envelope is integrable (Cauchy–Schwarz: `|g|, b ∈ L²(P_θ)`)
  have hD_int : Integrable D μ := by
    simp only [hD_def]
    have hgabsL2 : MemLp (fun x => |g x|) 2 (M.toMeasure μ θ) := by
      simpa [Real.norm_eq_abs] using hg2.norm
    have hmul : Integrable (fun x => |g x| * b x) (M.toMeasure μ θ) :=
      memLp_one_iff_integrable.mp (hb2.mul' hgabsL2)
    have h := (integrable_withDensity_iff (M.density_meas θ).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).1 hmul
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ x)]
  -- eventual facts on the punctured neighborhood
  have hball : ∀ᶠ t in 𝓝[≠] θ, |t - θ| < ε := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds θ hε)] with t ht
    rwa [Metric.mem_ball, Real.dist_eq] at ht
  have hne : ∀ᶠ t in 𝓝[≠] θ, t ≠ θ := self_mem_nhdsWithin
  -- the difference quotient is dominated by the envelope (transferred to `μ` via the support)
  have hQ_bound : ∀ t : ℝ, 0 < |t - θ| → |t - θ| < ε → ∀ᵐ x ∂μ, ‖Q t x‖ ≤ D x := by
    intro t htpos htlt
    have htne : t ≠ θ := sub_ne_zero.mp (abs_pos.mp htpos)
    have hbt := hbound (t - θ) htpos htlt
    have hθt : θ + (t - θ) = t := by ring
    simp only [hθt] at hbt
    rw [htoM] at hbt
    have hbt_mu : ∀ᵐ x ∂μ, 0 < M.density θ x →
        |(M.density t x - M.density θ x) / ((t - θ) * M.density θ x)| ≤ b x := by
      filter_upwards [(ae_withDensity_iff (M.density_meas θ).ennreal_ofReal).1 hbt]
        with x hx hpos
      exact hx (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hpos])
    filter_upwards [hbt_mu] with x hx
    rcases eq_or_lt_of_le (M.density_nonneg θ x) with h0 | hpos
    · have hpt0 : M.density t x = 0 := density_eq_zero_of_commonSupport hsupp h0.symm
      have hQ0 : Q t x = 0 := by simp [hQ_def, hpt0, ← h0]
      have hD0 : D x = 0 := by simp [hD_def, ← h0]
      simp [hQ0, hD0]
    · have hbx := hx hpos
      have heq : (M.density t x - M.density θ x) / (t - θ)
          = (M.density t x - M.density θ x) / ((t - θ) * M.density θ x) * M.density θ x := by
        rw [← div_div, div_mul_cancel₀ _ hpos.ne']
      have hq : |(M.density t x - M.density θ x) / (t - θ)| ≤ b x * M.density θ x := by
        rw [heq, abs_mul, abs_of_pos hpos]
        exact mul_le_mul_of_nonneg_right hbx hpos.le
      calc ‖Q t x‖ = |g x| * |(M.density t x - M.density θ x) / (t - θ)| := by
            simp only [hQ_def, Real.norm_eq_abs, abs_mul]
        _ ≤ |g x| * (b x * M.density θ x) := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
        _ = D x := by simp only [hD_def]; ring
  -- `g · p_t` is integrable near `θ` (`g p_t = g p_θ + (t - θ)·Q t`)
  have hgpt_int : ∀ t : ℝ, 0 < |t - θ| → |t - θ| < ε →
      Integrable (fun x => g x * M.density t x) μ := by
    intro t htpos htlt
    have htne : t ≠ θ := sub_ne_zero.mp (abs_pos.mp htpos)
    have hQint : Integrable (Q t) μ :=
      Integrable.mono' hD_int (hQ_meas t) (hQ_bound t htpos htlt)
    have hsplit : (fun x => g x * M.density t x)
        = fun x => g x * M.density θ x + (t - θ) * Q t x := by
      funext x
      have hc : (t - θ) * Q t x = g x * (M.density t x - M.density θ x) := by
        simp only [hQ_def]
        rw [mul_comm, mul_assoc, div_mul_cancel₀ _ (sub_ne_zero.mpr htne)]
      rw [hc]; ring
    rw [hsplit]
    exact hgpθ_int.add (hQint.const_mul (t - θ))
  -- the slope equals the integral of the difference quotient
  have hslope_eq : slope F θ =ᶠ[𝓝[≠] θ] fun t => ∫ x, Q t x ∂μ := by
    filter_upwards [hball, hne] with t htlt htne
    have htpos : 0 < |t - θ| := abs_pos.mpr (sub_ne_zero.mpr htne)
    rw [slope_def_field]
    simp only [hF_def]
    rw [← integral_sub (hgpt_int t htpos htlt) hgpθ_int, ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hQ_def]; ring
  -- the pointwise limit of the difference quotient is `g · ∂_θ p_θ`
  have h_lim : ∀ᵐ x ∂μ, Tendsto (fun t => Q t x) (𝓝[≠] θ)
      (𝓝 (g x * deriv (fun t => M.density t x) θ)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    rcases eq_or_lt_of_le (M.density_nonneg θ x) with h0 | hpos
    · have hz : (fun s => M.density s x) = fun _ => (0 : ℝ) :=
        funext fun s => density_eq_zero_of_commonSupport hsupp h0.symm
      have hQz : ∀ t, Q t x = 0 := by
        intro t
        have hpt0 : M.density t x = 0 := density_eq_zero_of_commonSupport hsupp h0.symm
        simp [hQ_def, hpt0, ← h0]
      simp only [hz, deriv_const', mul_zero]
      simp only [hQz]
      exact tendsto_const_nhds
    · have hs := (hdiff x hpos).hasDerivAt.tendsto_slope
      refine (hs.const_mul (g x)).congr (fun b => ?_)
      simp only [hQ_def, slope_def_field]
  -- conclude by dominated convergence
  refine (tendsto_integral_filter_of_dominated_convergence D (Filter.Eventually.of_forall hQ_meas)
    ?_ hD_int h_lim).congr' hslope_eq.symm
  filter_upwards [hball, hne] with t htlt htne
  exact hQ_bound t (abs_pos.mpr (sub_ne_zero.mpr htne)) htlt

theorem diff_under_integral_of_density_regular (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ)
    -- USER-INPUT: on the support, the density is differentiable in the parameter;
    -- classical smoothness condition (off the support the parameter map is constant `0`
    -- by the common-support condition, so nothing is assumed there)
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    -- USER-INPUT: the dominated-difference-quotient condition at `θ`
    (hreg : HasDominatedDifferenceQuotient M μ θ)
    (δ : 𝓧 → ℝ)
    -- USER-INPUT: the statistic has a finite second moment at `θ`
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ)) :
    HasDerivAt (fun t => ∫ x, δ x * M.density t x ∂μ)
      (∫ x, δ x * score M θ x * M.density θ x ∂μ) θ :=
  diff_under_integral_core M μ hpdf hsupp θ hdiff hreg δ hδ2

/-- **The mean-zero property of the score is a consequence of family-side regularity.**
Taking the constant statistic `1` in the previous theorem, the derivative of the constant
map `t ↦ ∫ p_t dμ = 1` is `0`, which is exactly `E_θ[ℓ̇_θ(X)] = 0`. -/
theorem integral_score_eq_zero_of_density_regular (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ)
    -- USER-INPUT: on the support, the density is differentiable in the parameter
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    -- USER-INPUT: the dominated-difference-quotient condition at `θ`
    (hreg : HasDominatedDifferenceQuotient M μ θ) :
    ∫ x, score M θ x * M.density θ x ∂μ = 0 := by
  haveI := isProbabilityMeasure_toMeasure M μ hpdf θ
  have hd := diff_under_integral_of_density_regular M μ hpdf hsupp θ hdiff hreg
    (fun _ => 1) (memLp_const 1)
  have hconst : (fun t => ∫ x, (1 : ℝ) * M.density t x ∂μ) = fun _ => (1 : ℝ) := by
    funext t; simp_rw [one_mul]; exact hpdf.density_integral_eq_one t
  have h0 : HasDerivAt (fun t => ∫ x, (1 : ℝ) * M.density t x ∂μ) 0 θ := by
    rw [hconst]; exact hasDerivAt_const θ 1
  have hzero := hd.unique h0
  simpa using hzero

/-- The score is measurable, as the a.e. limit of the (measurable) difference quotients
`slope (p_· x) θ (θ + 1/(n+1))`: on the support the quotients converge to the derivative by
differentiability, and off the support (where the parameter map is constant `0`) they vanish. -/
private lemma measurable_score_of_regular (M : ParametricFamily 𝓧 ℝ)
    (hsupp : HasCommonSupport M) (θ : ℝ)
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ) :
    Measurable (score M θ) := by
  set a : ℕ → ℝ := fun n => θ + 1 / ((n : ℝ) + 1) with ha
  have ha_tendsto : Tendsto a atTop (𝓝[≠] θ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa [ha] using
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · simp only [ha, Set.mem_compl_iff, Set.mem_singleton_iff]
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      intro h; nlinarith [h]
  have hderiv_meas : Measurable (fun x => deriv (fun t => M.density t x) θ) := by
    refine measurable_of_tendsto_metrizable
      (f := fun n x => slope (fun t => M.density t x) θ (a n)) (fun n => ?_)
      (tendsto_pi_nhds.2 (fun x => ?_))
    · simp only [slope_def_field]
      exact ((M.density_meas _).sub (M.density_meas θ)).div measurable_const
    · rcases eq_or_lt_of_le (M.density_nonneg θ x) with h0 | hpos
      · have hf0 : (fun t => M.density t x) = fun _ => (0 : ℝ) :=
          funext fun t => density_eq_zero_of_commonSupport hsupp h0.symm
        rw [hf0]
        simp only [slope_def_field, sub_self, zero_div, deriv_const']
        exact tendsto_const_nhds
      · exact (hdiff x hpos).hasDerivAt.tendsto_slope.comp ha_tendsto
  show Measurable (fun x => deriv (fun t => M.density t x) θ / M.density θ x)
  exact hderiv_meas.div (M.density_meas θ)

/-- **The information inequality under family-side regularity.** If the family has a common
support, is differentiable in the parameter on that support, has positive information and
satisfies the dominated-difference-quotient condition at `θ`, then for *every* statistic
with a finite second moment the expectation is differentiable at `θ` and the information
inequality holds — no condition on the statistic beyond square-integrability.

The derivative appears in the conclusion rather than among the hypotheses precisely because
it is a consequence here: this is the content of the theorem. -/
theorem cramer_rao_of_density_regular (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ)
    -- USER-INPUT: on the support, the density is differentiable in the parameter
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    -- USER-INPUT: the information is positive; classical standing assumption (it also
    -- forces the defining integral to converge, so no separate integrability is assumed)
    (hI : 0 < fisherInfo M μ θ)
    -- USER-INPUT: the dominated-difference-quotient condition at `θ`
    (hreg : HasDominatedDifferenceQuotient M μ θ)
    (δ : 𝓧 → ℝ)
    -- USER-INPUT: the statistic has a finite second moment at `θ`; the only condition on
    -- the estimator
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ)) :
    HasDerivAt (fun t => ∫ x, δ x * M.density t x ∂μ)
        (∫ x, δ x * score M θ x * M.density θ x ∂μ) θ ∧
      (∫ x, δ x * score M θ x * M.density θ x ∂μ) ^ 2 / fisherInfo M μ θ
        ≤ variance δ (M.toMeasure μ θ) := by
  have hderiv := diff_under_integral_of_density_regular M μ hpdf hsupp θ hdiff hreg δ hδ2
  refine ⟨hderiv, ?_⟩
  have hmeas : AEStronglyMeasurable (score M θ) μ :=
    (measurable_score_of_regular M hsupp θ hdiff).aestronglyMeasurable
  have hmean0 := integral_score_eq_zero_of_density_regular M μ hpdf hsupp θ hdiff hreg
  have hscore_int : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ := by
    by_contra h
    rw [fisherInfo, integral_undef h] at hI
    exact lt_irrefl 0 hI
  have hswap : (∫ x, δ x * score M θ x * M.density θ x ∂μ)
      = ∫ x, δ x * deriv (fun t => M.density t x) θ ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [mul_assoc, score_mul_density_eq_deriv hsupp]
  exact cramer_rao M μ hpdf hsupp θ δ (∫ x, δ x * score M θ x * M.density θ x ∂μ)
    hmeas hδ2 hscore_int hI hderiv hswap hmean0

/-- **The information inequality for an independent identically distributed sample.** For a
sample of size `n ≥ 1` the information in the sample is `n I(θ)`, so the bound on the
variance of a statistic `δ` of the whole sample is
`(∂_θ E_θ δ)² / (n I(θ)) ≤ var_θ(δ)`.

The conditions on the sample statistic are the estimator-side ones (finite second moment,
and differentiation under the integral sign for its expectation); the family-side theorem
above, applied to the `n`-fold product family, is what discharges them in applications. -/
theorem cramer_rao_iid (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- LEAN-ONLY: σ-finiteness of the dominating measure, required by the product-measure
    -- theory
    [SigmaFinite μ]
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (n : ℕ)
    -- USER-INPUT: the sample is nonempty
    (hn : 0 < n)
    (θ : ℝ)
    -- USER-INPUT: on the support, the density is differentiable in the parameter
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    -- USER-INPUT: the score of one observation has mean zero; classical regularity
    -- condition, and what makes the informations add
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0)
    -- LEAN-ONLY: integrability of the mean score, needed to factorize the cross terms in
    -- the additivity step
    (hint1 : Integrable (fun x => score M θ x * M.density θ x) μ)
    -- USER-INPUT: the information in one observation is positive
    (hI : 0 < fisherInfo M μ θ)
    (δ : (Fin n → 𝓧) → ℝ) (g' : ℝ)
    -- USER-INPUT: the sample statistic has a finite second moment at `θ`
    (hδ2 : MemLp δ 2 ((piFamily M n).toMeasure (Measure.pi fun _ : Fin n => μ) θ))
    -- USER-INPUT: the expectation of the sample statistic is differentiable at `θ`
    (hdiffδ : HasDerivAt
      (fun t => ∫ x, δ x * (piFamily M n).density t x ∂(Measure.pi fun _ : Fin n => μ)) g' θ)
    -- USER-INPUT: that derivative is obtained by differentiating under the integral sign
    (hswap : g' = ∫ x, δ x * deriv (fun t => (piFamily M n).density t x) θ
      ∂(Measure.pi fun _ : Fin n => μ)) :
    g' ^ 2 / ((n : ℝ) * fisherInfo M μ θ)
      ≤ variance δ ((piFamily M n).toMeasure (Measure.pi fun _ : Fin n => μ) θ) := by
  -- every coordinate map is differentiable at `θ` (on the support, or constant `0` off it)
  have hdiff_all : ∀ x : 𝓧, DifferentiableAt ℝ (fun t => M.density t x) θ := by
    intro x
    rcases eq_or_lt_of_le (M.density_nonneg θ x) with h0 | hpos
    · have hc : (fun t => M.density t x) = fun _ => (0 : ℝ) :=
        funext fun t => density_eq_zero_of_commonSupport hsupp h0.symm
      rw [hc]; exact differentiableAt_const 0
    · exact hdiff x hpos
  -- `∫ ∂_θ p_θ dμ = 0` for one observation
  have hderiv0 : ∫ x, deriv (fun t => M.density t x) θ ∂μ = 0 := by
    rw [← hmean0]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun x => (score_mul_density_eq_deriv hsupp θ x).symm)
  have hderiv_int : Integrable (fun a => deriv (fun t => M.density t a) θ) μ :=
    hint1.congr (Filter.Eventually.of_forall fun a => score_mul_density_eq_deriv hsupp θ a)
  -- the product family is a probability-density family
  have hpdf_pi : IsPDFOf (piFamily M n) (Measure.pi fun _ : Fin n => μ) := by
    refine ⟨fun t => ?_, fun t => ?_⟩
    · show ∫ x, ∏ i, M.density t (x i) ∂(Measure.pi fun _ : Fin n => μ) = 1
      rw [integral_fintype_prod_eq_prod (fun _ a => M.density t a)]
      simp [hpdf.density_integral_eq_one t]
    · exact Integrable.fintype_prod (fun _ => hpdf.density_integrable t)
  -- the product family has common support
  have hsupp_pi : HasCommonSupport (piFamily M n) := by
    intro t t' x hx
    simp only [piFamily] at hx ⊢
    have hpos_i : ∀ i, 0 < M.density t (x i) := fun i =>
      lt_of_le_of_ne (M.density_nonneg t (x i))
        (Ne.symm fun h => (ne_of_gt hx) (Finset.prod_eq_zero (Finset.mem_univ i) h))
    exact Finset.prod_pos (fun i _ => hsupp t t' (x i) (hpos_i i))
  have hdiff_pi : ∀ x, 0 < (piFamily M n).density θ x →
      DifferentiableAt ℝ (fun t => (piFamily M n).density t x) θ := by
    intro x _
    simp only [piFamily]
    exact DifferentiableAt.fun_finset_prod (fun i _ => hdiff_all (x i))
  have hmeas_pi : AEStronglyMeasurable (score (piFamily M n) θ)
      (Measure.pi fun _ : Fin n => μ) :=
    (measurable_score_of_regular (piFamily M n) hsupp_pi θ hdiff_pi).aestronglyMeasurable
  -- `∫ ∂_θ (∏ p) dπ = 0`: product rule + Fubini, with the diagonal coordinate vanishing
  have hpideriv0 : ∫ x, deriv (fun t => (piFamily M n).density t x) θ
      ∂(Measure.pi fun _ : Fin n => μ) = 0 := by
    have hpt : ∀ x : Fin n → 𝓧, deriv (fun t => (piFamily M n).density t x) θ
        = ∑ i, ∏ k, (if k = i then deriv (fun t => M.density t (x k)) θ
            else M.density θ (x k)) := by
      intro x
      simp only [piFamily]
      rw [deriv_fun_finset_prod (fun i _ => hdiff_all (x i))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_eq_mul, ← Finset.mul_prod_erase Finset.univ
          (fun k => if k = i then deriv (fun t => M.density t (x k)) θ else M.density θ (x k))
          (Finset.mem_univ i), if_pos rfl,
        Finset.prod_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))]
      ring
    have hint_i : ∀ i : Fin n, Integrable (fun x : Fin n → 𝓧 =>
        ∏ k, (if k = i then deriv (fun t => M.density t (x k)) θ else M.density θ (x k)))
        (Measure.pi fun _ : Fin n => μ) := by
      intro i
      refine Integrable.fintype_prod (f := fun k a =>
        if k = i then deriv (fun t => M.density t a) θ else M.density θ a) (fun k => ?_)
      by_cases hk : k = i
      · simp only [hk, if_pos]; exact hderiv_int
      · simp only [if_neg hk]; exact hpdf.density_integrable θ
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_finset_sum Finset.univ (fun i _ => hint_i i)]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [integral_fintype_prod_eq_prod (fun k a =>
      if k = i then deriv (fun t => M.density t a) θ else M.density θ a)]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only [↓reduceIte]
    exact hderiv0
  -- the sample score has mean zero
  have hswap_pi : HasDerivAt (fun t => ∫ x, (piFamily M n).density t x
        ∂(Measure.pi fun _ : Fin n => μ))
      (∫ x, deriv (fun t => (piFamily M n).density t x) θ
        ∂(Measure.pi fun _ : Fin n => μ)) θ := by
    rw [hpideriv0, show (fun t => ∫ x, (piFamily M n).density t x
        ∂(Measure.pi fun _ : Fin n => μ)) = fun _ => (1 : ℝ) from
      funext fun t => hpdf_pi.density_integral_eq_one t]
    exact hasDerivAt_const θ (1 : ℝ)
  have hmean0_pi := integral_score_eq_zero (piFamily M n) (Measure.pi fun _ : Fin n => μ)
    hpdf_pi hsupp_pi θ hswap_pi
  -- the sample information is `n · I(θ) > 0`, hence its integrand is integrable
  have hint_single : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ := by
    by_contra h; rw [fisherInfo, integral_undef h] at hI; exact lt_irrefl 0 hI
  have hfisher_pi : fisherInfo (piFamily M n) (Measure.pi fun _ : Fin n => μ) θ
      = (n : ℝ) * fisherInfo M μ θ :=
    fisherInfo_pi M μ n θ hpdf hsupp hdiff hmean0 hint_single hint1
  have hI_pi : 0 < fisherInfo (piFamily M n) (Measure.pi fun _ : Fin n => μ) θ := by
    rw [hfisher_pi]; exact mul_pos (Nat.cast_pos.mpr hn) hI
  have hscore_int_pi : Integrable (fun x => score (piFamily M n) θ x ^ 2
      * (piFamily M n).density θ x) (Measure.pi fun _ : Fin n => μ) := by
    by_contra h; rw [fisherInfo, integral_undef h] at hI_pi; exact lt_irrefl 0 hI_pi
  have hbound := cramer_rao (piFamily M n) (Measure.pi fun _ : Fin n => μ) hpdf_pi hsupp_pi θ
    δ g' hmeas_pi hδ2 hscore_int_pi hI_pi hdiffδ hswap hmean0_pi
  rwa [hfisher_pi] at hbound

end StatLean.PointEstimation
