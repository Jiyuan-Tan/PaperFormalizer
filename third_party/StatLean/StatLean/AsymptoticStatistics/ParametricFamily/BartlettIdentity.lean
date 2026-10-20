module
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# The second Bartlett / information identity, derived (polarized form)

For a differentiable parametric family, differentiating the *first* Bartlett identity
`∫ ℓ_θ dP_θ = 0` (mean-zero of the score `ℓ` along the moving curve `θ ↦ P_θ`) under the
integral sign yields the **second Bartlett / information identity**. In its *polarized*
form — where the integrated score `f = ℓ̃_j` and the moving-direction score
`k = ℓ̃_k` may differ — it reads

  `∫ ḟ₀ dP = − ∫ f₀ · k₀ dP`

(with `ḟ₀ = ∂_direction f`). The **diagonal** case `k₀ = f₀` gives the classical
information equality `∫ ℓ̇₀ dP = − ∫ ℓ₀² dP` (`bartlett_identity_diag`); the **off-diagonal**
case is exactly the `(j,k)` entry of the matrix Bartlett identity
`E_P[∂_k ℓ̃_j] = − Ĩ_{jk}`, `Ĩ_{jk} = ∫ ℓ̃_j ℓ̃_k dP`, feeding the matrix-coupled vector
efficient influence function `Ĩ⁻¹ ℓ̃`.

The polarized identity supplies the matrix derivative condition used by smooth
vector Taylor/Z-estimator theorems. It is a consequence of differentiating the
moving-law score normalization, rather than a first-order QMD identity.

Note on QMDPath: `Core.QMDPath.QMDPath` is based at a *fixed* `P` (`curve 0 = P`) and
carries only the *first-order* score, not its θ-derivative; the second Bartlett needs the
*moving* measure `P_θ` and the θ-derivative of the score, so this is a distinct structure,
not an extension of `QMDPath`.

Reference: vdV §5.3 / §7.2; Mathlib
`Mathlib/Analysis/Calculus/ParametricIntegral.lean`
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`).

-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.ParametricFamily

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A *differentiable score submodel* at `P`, in polarized form: a dominated one-parameter
family with density curve `density θ = dP_θ/dμ`, an integrated score curve
`scoreCurve θ = f_θ`, the moving-direction score `densityScore = k₀ = ∂_θ log p₀`, and the
θ-derivative `scoreDot = ḟ₀` of `f` at `0`. It carries exactly the differentiability +
domination hypotheses Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
requires to differentiate `θ ↦ ∫ f_θ · p_θ dμ`, the moving-curve first Bartlett
`∫ f_θ p_θ dμ = 0`, and the product-rule value of the integrand's derivative at `0`,
`∂_θ(f_θ p_θ)|₀ = ḟ₀ p₀ + f₀ k₀ p₀` (using `ṗ₀ = k₀ p₀`).

Diagonal witness (`k₀ = f₀`): a 1-D location family `p_θ(ω) = φ(ω − θ)`, `ℓ_θ(ω) = ω − θ`,
`scoreDot = −1`, gives `∫ scoreDot dP = −1 = −∫ ω² dP = −Fisher`. -/
structure DifferentiableScoreSubmodel (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- Dominating measure `μ` (`P_θ ≪ μ`). -/
  μ : Measure Ω
  /-- Density curve `density θ = dP_θ/dμ`. -/
  density : ℝ → Ω → ℝ
  /-- Integrated score curve `scoreCurve θ = f_θ` (e.g. `ℓ̃_j` along the moving curve). -/
  scoreCurve : ℝ → Ω → ℝ
  /-- Moving-direction score `densityScore = k₀ = ∂_θ log p₀` (e.g. `ℓ̃_k`). -/
  densityScore : Ω → ℝ
  /-- θ-dependent derivative of the integrand `θ ↦ f_θ · p_θ` (needed in the neighborhood
  form of the Mathlib differentiation lemma). -/
  prodDeriv : ℝ → Ω → ℝ
  /-- The score derivative `ḟ₀` at `θ = 0`. -/
  scoreDot : Ω → ℝ
  /-- `P = p₀ · μ`. -/
  P_eq : P = μ.withDensity (fun ω => ENNReal.ofReal (density 0 ω))
  /-- `p₀` is measurable (for the withDensity ⇄ integral bridge). -/
  density0_meas : Measurable (density 0)
  /-- densities are nonnegative (`(ofReal p).toReal = p`). -/
  density_nonneg : ∀ᵐ ω ∂μ, 0 ≤ density 0 ω
  /-- The neighborhood of `0` on which differentiability + domination hold. -/
  s : Set ℝ
  hs_mem : s ∈ 𝓝 (0 : ℝ)
  /-- vdV §5/§7.2 (first Bartlett along the moving curve): `∫ f_θ dP_θ = 0`, written on
  the dominating measure as `∫ f_θ(ω) p_θ(ω) dμ = 0` for all θ. -/
  score_mean_zero : ∀ θ, ∫ ω, scoreCurve θ ω * density θ ω ∂μ = 0
  /-- ae-measurability of the integrand near `0` (Mathlib `hF_meas`). -/
  prod_aemeas : ∀ᶠ θ in 𝓝 (0 : ℝ),
    AEStronglyMeasurable (fun ω => scoreCurve θ ω * density θ ω) μ
  /-- integrability of the integrand at `0` (Mathlib `hF_int`). -/
  prod_int_zero : Integrable (fun ω => scoreCurve 0 ω * density 0 ω) μ
  /-- ae-measurability of the derivative at `0` (Mathlib `hF'_meas`). -/
  prodDeriv_aemeas : AEStronglyMeasurable (prodDeriv 0) μ
  /-- integrable domination bound on the derivative over `s` (Mathlib `bound`). -/
  bound : Ω → ℝ
  h_bound : ∀ᵐ ω ∂μ, ∀ θ ∈ s, ‖prodDeriv θ ω‖ ≤ bound ω
  bound_integrable : Integrable bound μ
  /-- the integrand is differentiable in θ over `s` with derivative `prodDeriv`
  (Mathlib `h_diff`). -/
  h_diff : ∀ᵐ ω ∂μ, ∀ θ ∈ s,
    HasDerivAt (fun t => scoreCurve t ω * density t ω) (prodDeriv θ ω) θ
  /-- product rule at `0`: `∂_θ(f_θ p_θ)|₀ = ḟ₀ p₀ + f₀ k₀ p₀` (using `ṗ₀ = k₀ p₀`).
  Model derivative structure, not the conclusion. -/
  prodDeriv_at_zero : ∀ ω,
    prodDeriv 0 ω = scoreDot ω * density 0 ω + scoreCurve 0 ω * densityScore ω * density 0 ω
  /-- the product `f₀ · k₀` is integrable on `μ` (finite off-diagonal information). -/
  product_integrable :
    Integrable (fun ω => scoreCurve 0 ω * densityScore ω * density 0 ω) μ

namespace DifferentiableScoreSubmodel

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Density-weighted `μ`-integral equals the `P`-integral: `∫ g · p₀ dμ = ∫ g dP`. -/
theorem integral_weighted_eq (M : DifferentiableScoreSubmodel P) (g : Ω → ℝ) :
    ∫ ω, g ω * M.density 0 ω ∂M.μ = ∫ ω, g ω ∂P := by
  conv_rhs => rw [M.P_eq]
  rw [integral_withDensity_eq_integral_toReal_smul
        (M.density0_meas.ennreal_ofReal)
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae ?_
  filter_upwards [M.density_nonneg] with ω hω
  rw [ENNReal.toReal_ofReal hω, smul_eq_mul, mul_comm]

/-- **Second Bartlett / information identity, polarized form (derived).**

`∫ ḟ₀ dP = − ∫ f₀ · k₀ dP`. Obtained by differentiating the constantly-zero map
`θ ↦ ∫ f_θ p_θ dμ` under the integral (Mathlib
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`): the derivative is `∫ prodDeriv 0 dμ`,
which by uniqueness of the derivative of a constant equals `0`; expanding
`prodDeriv 0 = ḟ₀ p₀ + f₀ k₀ p₀` and converting `∫ h p₀ dμ = ∫ h dP` gives
`∫ ḟ₀ dP + ∫ f₀ k₀ dP = 0`. -/
theorem bartlett_identity (M : DifferentiableScoreSubmodel P) :
    ∫ ω, M.scoreDot ω ∂P = - ∫ ω, M.scoreCurve 0 ω * M.densityScore ω ∂P := by
  -- differentiate under the integral
  obtain ⟨hF'_int, hHasDeriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      M.hs_mem M.prod_aemeas M.prod_int_zero M.prodDeriv_aemeas
      M.h_bound M.bound_integrable M.h_diff
  -- the integral map is constantly zero, so its derivative vanishes
  have hconst :
      (fun θ => ∫ ω, M.scoreCurve θ ω * M.density θ ω ∂M.μ) = fun _ => (0 : ℝ) := by
    funext θ; exact M.score_mean_zero θ
  rw [hconst] at hHasDeriv
  have hzero : ∫ ω, M.prodDeriv 0 ω ∂M.μ = 0 :=
    hHasDeriv.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  -- integrability of the score-derivative piece = (prodDeriv 0) − (product piece)
  have hfdot_int : Integrable (fun ω => M.scoreDot ω * M.density 0 ω) M.μ := by
    have heq : (fun ω => M.scoreDot ω * M.density 0 ω)
        = fun ω => M.prodDeriv 0 ω
            - M.scoreCurve 0 ω * M.densityScore ω * M.density 0 ω := by
      funext ω; rw [M.prodDeriv_at_zero ω]; ring
    rw [heq]; exact hF'_int.sub M.product_integrable
  -- expand prodDeriv 0 and split the integral
  have hpd : (fun ω => M.prodDeriv 0 ω)
      = fun ω => M.scoreDot ω * M.density 0 ω
          + M.scoreCurve 0 ω * M.densityScore ω * M.density 0 ω := by
    funext ω; exact M.prodDeriv_at_zero ω
  rw [hpd, integral_add hfdot_int M.product_integrable] at hzero
  -- convert both μ-integrals to P-integrals
  rw [M.integral_weighted_eq M.scoreDot,
      M.integral_weighted_eq (fun ω => M.scoreCurve 0 ω * M.densityScore ω)] at hzero
  linarith [hzero]

/-- **Diagonal information equality** `∫ ℓ̇₀ dP = − ∫ ℓ₀² dP` (Fisher information), the
`k₀ = f₀` specialization of `bartlett_identity`. -/
theorem bartlett_identity_diag (M : DifferentiableScoreSubmodel P)
    (h_diag : M.densityScore = M.scoreCurve 0) :
    ∫ ω, M.scoreDot ω ∂P = - ∫ ω, (M.scoreCurve 0 ω) ^ 2 ∂P := by
  rw [M.bartlett_identity, h_diag]
  congr 1
  refine integral_congr_ae (Eventually.of_forall (fun ω => ?_))
  ring

end DifferentiableScoreSubmodel

end AsymptoticStatistics.ParametricFamily
