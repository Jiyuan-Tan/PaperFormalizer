module
public import StatLean.AsymptoticStatistics.ParametricFamily.SubmodelFromScores
public import StatLean.AsymptoticStatistics.ParametricFamily.SubmodelDQM
public import StatLean.AsymptoticStatistics.DQM.Defs
public import StatLean.AsymptoticStatistics.DQM.Properties
public import StatLean.AsymptoticStatistics.ParametricFamily.FisherInformation
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Unbounded sigmoid parametric submodel

Implements van der Vaart Example 25.16: the sigmoid truncation
`k(x) := 2 / (1 + exp(-2x))` provides a normalisable parametric submodel
`p_θ(ω) = c(θ) · k(⟨θ, g(ω)⟩) · p_0(ω)` valid for **any** orthonormal family
`g_P : Fin m → L²₀(P)`, **without** requiring essential boundedness of the
scores. (The `1 + tg` density only stays non-negative when `g` is essentially
bounded; the sigmoid `0 < k < 2` makes the family well-defined unconditionally.)

vdV §25.16: *"For an unbounded function g, [the `1+tg` and `exp(tg)` submodels]
are not necessarily well-defined. However, the models have the common structure
`p_t(x) = c(t) k(t·g(x)) p_0(x)` for a nonnegative function k with
k(0)=k'(0)=1. The function k(x) = 2/(1+e^{-2x}) can be used with any g."*

Headline declarations:
* `kSigmoid` and its basic properties (positivity, boundedness, derivative,
  smoothness).
* `normalizer_c θ`: the normalising constant `c θ = (∫ kSigmoid(linPerturb θ) dP)⁻¹`.
* `unboundedParamSubmodel`: the resulting `ParametricFamily`, with
  density-at-zero = 1, `IsPDFOf`, and strict positivity.
* `unboundedParamSubmodel_DQM`: differentiability in quadratic mean at `θ = 0`.
* `unboundedParamSubmodel_fisher_info`: Fisher information at `θ = 0` is `I_m`.

The construction uses ONLY `g_P i ∈ ↥(L2ZeroMean P)`: no moment-strengthening
(L⁴, essential boundedness) is taken anywhere.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal BigOperators

namespace AsymptoticStatistics.ParametricFamily

open AsymptoticStatistics.Core.Hilbert

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## The sigmoid `kSigmoid` and its basic properties

`kSigmoid x := 2 / (1 + exp(-2x))` is the textbook
choice (vdV §25.16) for a strictly-positive, bounded `k` with
`k(0) = k'(0) = 1` (equivalently, `√k`'s derivative at 0 is `1/2`). -/

/-- vdV §25.16 sigmoid: `k(x) := 2 / (1 + exp(-2x))`. -/
noncomputable def kSigmoid (x : ℝ) : ℝ :=
  2 / (1 + Real.exp (-2 * x))

/-- Positivity of `kSigmoid`'s denominator. -/
lemma kSigmoid_denom_pos (x : ℝ) : 0 < 1 + Real.exp (-2 * x) := by
  have h := Real.exp_pos (-2 * x)
  linarith

lemma kSigmoid_denom_ne_zero (x : ℝ) : (1 + Real.exp (-2 * x)) ≠ 0 :=
  ne_of_gt (kSigmoid_denom_pos x)

/-- `kSigmoid` evaluated at `0` equals `1`. -/
@[simp] lemma kSigmoid_zero : kSigmoid 0 = 1 := by
  unfold kSigmoid
  rw [mul_zero, Real.exp_zero]
  norm_num

/-- `kSigmoid` is strictly positive. -/
lemma kSigmoid_pos (x : ℝ) : 0 < kSigmoid x := by
  unfold kSigmoid
  exact div_pos (by norm_num) (kSigmoid_denom_pos x)

lemma kSigmoid_nonneg (x : ℝ) : 0 ≤ kSigmoid x := (kSigmoid_pos x).le

/-- `kSigmoid` is strictly less than `2`. -/
lemma kSigmoid_lt_two (x : ℝ) : kSigmoid x < 2 := by
  unfold kSigmoid
  rw [div_lt_iff₀ (kSigmoid_denom_pos x)]
  have h := Real.exp_pos (-2 * x)
  nlinarith

/-- `kSigmoid` is bounded above by `2`. -/
lemma kSigmoid_le_two (x : ℝ) : kSigmoid x ≤ 2 := (kSigmoid_lt_two x).le

/-- The denominator `1 + exp(-2·)` has derivative `-2·exp(-2x)`. -/
lemma hasDerivAt_kSigmoid_denom (x : ℝ) :
    HasDerivAt (fun y => 1 + Real.exp (-2 * y)) (-2 * Real.exp (-2 * x)) x := by
  have h_id : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := hasDerivAt_id x
  have h_inner : HasDerivAt (fun y : ℝ => -2 * y) (-2 * 1 : ℝ) x :=
    h_id.const_mul (-2 : ℝ)
  -- Note: HasDerivAt.exp gives Real.exp (f x) * f'
  have h_exp : HasDerivAt (fun y => Real.exp (-2 * y))
      (Real.exp (-2 * x) * (-2 * 1)) x :=
    h_inner.exp
  have h_sum : HasDerivAt (fun y => 1 + Real.exp (-2 * y))
      (0 + Real.exp (-2 * x) * (-2 * 1)) x :=
    (hasDerivAt_const x (1 : ℝ)).add h_exp
  have h_eq : (0 : ℝ) + Real.exp (-2 * x) * (-2 * 1) = -2 * Real.exp (-2 * x) := by ring
  rw [← h_eq]
  exact h_sum

/-- `HasDerivAt kSigmoid` at any `x`: explicit derivative
`4·exp(-2x) / (1 + exp(-2x))²`. -/
lemma hasDerivAt_kSigmoid (x : ℝ) :
    HasDerivAt kSigmoid
      (4 * Real.exp (-2 * x) / (1 + Real.exp (-2 * x))^2) x := by
  have h_denom := hasDerivAt_kSigmoid_denom x
  have h_ne := kSigmoid_denom_ne_zero x
  have h_const : HasDerivAt (fun _ : ℝ => (2 : ℝ)) (0 : ℝ) x := hasDerivAt_const x 2
  -- HasDerivAt.fun_div: derivative of `c y / d y` is `(c' · d - c · d') / d²`.
  have h_div : HasDerivAt (fun y => (2 : ℝ) / (1 + Real.exp (-2 * y)))
      ((0 * (1 + Real.exp (-2 * x)) - 2 * (-2 * Real.exp (-2 * x))) /
        (1 + Real.exp (-2 * x))^2) x :=
    HasDerivAt.fun_div h_const h_denom h_ne
  have h_eq : (0 * (1 + Real.exp (-2 * x)) - 2 * (-2 * Real.exp (-2 * x))) /
        (1 + Real.exp (-2 * x))^2
      = 4 * Real.exp (-2 * x) / (1 + Real.exp (-2 * x))^2 := by ring
  rw [← h_eq]
  exact h_div

/-- `HasDerivAt kSigmoid 1 0`: the textbook-required `k'(0) = 1`. -/
lemma hasDerivAt_kSigmoid_zero : HasDerivAt kSigmoid 1 0 := by
  have h := hasDerivAt_kSigmoid 0
  have hexp : Real.exp (-2 * 0) = 1 := by rw [mul_zero, Real.exp_zero]
  rw [hexp] at h
  have h_eq : (4 * 1 / (1 + 1) ^ 2 : ℝ) = 1 := by norm_num
  rw [h_eq] at h
  exact h

/-- `kSigmoid` is `C^∞` on `ℝ`. -/
lemma contDiff_kSigmoid {n : WithTop ℕ∞} : ContDiff ℝ n kSigmoid := by
  unfold kSigmoid
  -- numerator is the constant `2`; denominator is `1 + exp(-2·)`.
  have h_inner : ContDiff ℝ n (fun y : ℝ => -2 * y) :=
    contDiff_const.mul contDiff_id
  have h_exp : ContDiff ℝ n (fun y => Real.exp (-2 * y)) :=
    h_inner.exp
  have h_denom : ContDiff ℝ n (fun y => 1 + Real.exp (-2 * y)) :=
    contDiff_const.add h_exp
  exact contDiff_const.div h_denom (fun y => kSigmoid_denom_ne_zero y)

/-- `kSigmoid` is continuous on `ℝ`. -/
lemma continuous_kSigmoid : Continuous kSigmoid :=
  (contDiff_kSigmoid (n := 0)).continuous

/-- The derivative of `kSigmoid` is bounded in absolute value by `1`.

Proof uses AM-GM `(a+b)² ≥ 4ab` with `a = 1, b = exp(-2x)`. -/
lemma abs_deriv_kSigmoid_le_one (x : ℝ) : |deriv kSigmoid x| ≤ 1 := by
  rw [(hasDerivAt_kSigmoid x).deriv]
  have hexp_pos := Real.exp_pos (-2 * x)
  have hden_pos := kSigmoid_denom_pos x
  have hden_sq_pos : 0 < (1 + Real.exp (-2 * x))^2 := by positivity
  -- numerator is non-negative.
  have h_num_nn : 0 ≤ 4 * Real.exp (-2 * x) := by positivity
  have h_quot_nn : 0 ≤ 4 * Real.exp (-2 * x) / (1 + Real.exp (-2 * x))^2 :=
    div_nonneg h_num_nn hden_sq_pos.le
  rw [abs_of_nonneg h_quot_nn]
  rw [div_le_one hden_sq_pos]
  -- (1+e)² ≥ 4e by AM-GM: (1+e)² - 4e = (1-e)² ≥ 0.
  nlinarith [sq_nonneg (1 - Real.exp (-2 * x)), hexp_pos]

/-! ## The normaliser `c(θ)` -/

section Normaliser

variable {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))

/-- Joint integrand of the sigmoid family:
`kSigmoid (linPerturb g_P θ ω)`. -/
noncomputable def normalizer_c_integrand
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) : ℝ :=
  kSigmoid (linPerturb g_P θ ω)

lemma normalizer_c_integrand_meas (θ : EuclideanSpace ℝ (Fin m)) :
    Measurable (normalizer_c_integrand g_P θ) :=
  continuous_kSigmoid.measurable.comp (linPerturb_meas g_P θ)

/-- Pointwise positivity. -/
lemma normalizer_c_integrand_pos
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    0 < normalizer_c_integrand g_P θ ω :=
  kSigmoid_pos _

lemma normalizer_c_integrand_nonneg
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    0 ≤ normalizer_c_integrand g_P θ ω :=
  (normalizer_c_integrand_pos g_P θ ω).le

/-- Pointwise upper bound: `kSigmoid ≤ 2`. -/
lemma normalizer_c_integrand_le_two
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    normalizer_c_integrand g_P θ ω ≤ 2 :=
  kSigmoid_le_two _

/-- Integrability of the sigmoid integrand against the probability
measure `P`. Follows from boundedness `0 ≤ k ≤ 2` and finiteness of
`P`. -/
lemma normalizer_c_integrand_integrable
    (θ : EuclideanSpace ℝ (Fin m)) :
    Integrable (normalizer_c_integrand g_P θ) P := by
  refine Integrable.of_bound
    (normalizer_c_integrand_meas g_P θ).aestronglyMeasurable 2 ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  rw [Real.norm_of_nonneg (normalizer_c_integrand_nonneg g_P θ ω)]
  exact normalizer_c_integrand_le_two g_P θ ω

/-- The integral of the sigmoid integrand is strictly positive. -/
lemma normalizer_c_integrand_integral_pos
    (θ : EuclideanSpace ℝ (Fin m)) :
    0 < ∫ ω, normalizer_c_integrand g_P θ ω ∂P := by
  -- Strategy: the integrand is `≥ 0` and its support is the whole
  -- space (strict positivity), with `P ≠ 0` (probability measure).
  refine (integral_pos_iff_support_of_nonneg
      (fun ω => normalizer_c_integrand_nonneg g_P θ ω)
      (normalizer_c_integrand_integrable g_P θ)).mpr ?_
  -- Support is the whole space, hence has measure 1.
  have hsupp :
      Function.support (fun ω => normalizer_c_integrand g_P θ ω) = Set.univ := by
    ext ω
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact ne_of_gt (normalizer_c_integrand_pos g_P θ ω)
  rw [hsupp, measure_univ]
  exact one_pos

/-- **Normaliser** for the sigmoid parametric submodel:
`c θ = (∫ k(linPerturb θ) dP)⁻¹`. -/
noncomputable def normalizer_c (θ : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (∫ ω, normalizer_c_integrand g_P θ ω ∂P)⁻¹

/-- The normaliser is strictly positive. -/
lemma normalizer_c_pos (θ : EuclideanSpace ℝ (Fin m)) :
    0 < normalizer_c g_P θ :=
  inv_pos.mpr (normalizer_c_integrand_integral_pos g_P θ)

lemma normalizer_c_nonneg (θ : EuclideanSpace ℝ (Fin m)) :
    0 ≤ normalizer_c g_P θ :=
  (normalizer_c_pos g_P θ).le

lemma normalizer_c_ne_zero (θ : EuclideanSpace ℝ (Fin m)) :
    normalizer_c g_P θ ≠ 0 :=
  ne_of_gt (normalizer_c_pos g_P θ)

/-- At `θ = 0`, `linPerturb g_P 0 ω = 0`, so the integrand is
identically `kSigmoid 0 = 1`. -/
lemma normalizer_c_integrand_at_zero (ω : Ω) :
    normalizer_c_integrand g_P (0 : EuclideanSpace ℝ (Fin m)) ω = 1 := by
  unfold normalizer_c_integrand
  have h_lin : linPerturb g_P (0 : EuclideanSpace ℝ (Fin m)) ω = 0 := by
    unfold linPerturb
    simp [zero_mul]
  rw [h_lin, kSigmoid_zero]

/-- **Normaliser at zero**: `c(0) = 1`. -/
@[simp] lemma normalizer_c_at_zero :
    normalizer_c g_P (0 : EuclideanSpace ℝ (Fin m)) = 1 := by
  unfold normalizer_c
  have h_integrand_eq :
      (fun ω => normalizer_c_integrand g_P (0 : EuclideanSpace ℝ (Fin m)) ω)
        = fun _ => (1 : ℝ) := by
    funext ω
    exact normalizer_c_integrand_at_zero g_P ω
  rw [h_integrand_eq]
  simp

end Normaliser

/-! ## The unbounded sigmoid parametric submodel -/

section UnboundedSubmodel

variable {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))

/-- Pointwise density of the sigmoid submodel:
`c(θ) · k(linPerturb θ)`. -/
noncomputable def unboundedSubmodelDensity
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) : ℝ :=
  normalizer_c g_P θ * normalizer_c_integrand g_P θ ω

lemma unboundedSubmodelDensity_meas
    (θ : EuclideanSpace ℝ (Fin m)) :
    Measurable (unboundedSubmodelDensity g_P θ) :=
  measurable_const.mul (normalizer_c_integrand_meas g_P θ)

lemma unboundedSubmodelDensity_pos
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    0 < unboundedSubmodelDensity g_P θ ω :=
  mul_pos (normalizer_c_pos g_P θ) (normalizer_c_integrand_pos g_P θ ω)

lemma unboundedSubmodelDensity_nonneg
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    0 ≤ unboundedSubmodelDensity g_P θ ω :=
  (unboundedSubmodelDensity_pos g_P θ ω).le

lemma unboundedSubmodelDensity_integrable
    (θ : EuclideanSpace ℝ (Fin m)) :
    Integrable (unboundedSubmodelDensity g_P θ) P :=
  (normalizer_c_integrand_integrable g_P θ).const_mul _

/-- Integral of the density equals `1` (the defining property of the
normalising constant `c`). -/
lemma integral_unboundedSubmodelDensity_eq_one
    (θ : EuclideanSpace ℝ (Fin m)) :
    ∫ ω, unboundedSubmodelDensity g_P θ ω ∂P = 1 := by
  unfold unboundedSubmodelDensity
  rw [integral_const_mul]
  unfold normalizer_c
  exact inv_mul_cancel₀ (ne_of_gt (normalizer_c_integrand_integral_pos g_P θ))

/-- **The unbounded sigmoid parametric submodel.** Works for ANY
orthonormal family `g_P : Fin m → ↥(L2ZeroMean P)` — no essential
boundedness required.

The orthonormality hypothesis is **not used** in the construction
itself (only in DQM / Fisher computation downstream), but we keep it
in the constructor signature so callers immediately have the joint
orthonormality fact available downstream. -/
noncomputable def unboundedParamSubmodel
    (_h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    ParametricFamily Ω (EuclideanSpace ℝ (Fin m)) where
  density := unboundedSubmodelDensity g_P
  density_meas := unboundedSubmodelDensity_meas g_P
  density_nonneg := unboundedSubmodelDensity_nonneg g_P

/-- The unbounded sigmoid submodel is a probability-density family
w.r.t. `P`. -/
theorem unboundedParamSubmodel_isPDFOf
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    IsPDFOf (unboundedParamSubmodel g_P h_orth) P where
  density_integral_eq_one := integral_unboundedSubmodelDensity_eq_one g_P
  density_integrable := unboundedSubmodelDensity_integrable g_P

/-- **Density at zero** equals `1` everywhere. -/
@[simp] theorem unboundedParamSubmodel_density_zero_eq_one
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ω : Ω) :
    (unboundedParamSubmodel g_P h_orth).density 0 ω = 1 := by
  change unboundedSubmodelDensity g_P 0 ω = 1
  unfold unboundedSubmodelDensity
  rw [normalizer_c_at_zero, normalizer_c_integrand_at_zero, mul_one]

/-- **Strict positivity** of the density at every `θ`, every `ω`.

This is **stronger** than the typical "same support as `P`" predicate:
the sigmoid density is positive *everywhere*, not just `P`-a.e. -/
theorem unboundedParamSubmodel_density_pos
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    0 < (unboundedParamSubmodel g_P h_orth).density θ ω :=
  unboundedSubmodelDensity_pos g_P θ ω

/-- **Same support as `P`**: the density is nonzero everywhere, so the
parametric measure `P.withDensity (density θ)` shares the support of
`P`. -/
theorem unboundedParamSubmodel_density_ne_zero
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    (unboundedParamSubmodel g_P h_orth).density θ ω ≠ 0 :=
  ne_of_gt (unboundedParamSubmodel_density_pos g_P h_orth θ ω)

end UnboundedSubmodel

/-! ## DQM proof for the unbounded sigmoid submodel

The central technical content is `unboundedParamSubmodel_DQM`, proved via L²-DCT
(not pointwise-squared, which would silently require an L⁴ hypothesis on the
scores).

The proof structure:
* `normalizer_c_integral_tendsto_one` — `c θ → 1` as `θ → 0`, by bounded
  convergence (`|k| ≤ 2`).
* `abs_linPerturb_le_jointPointwiseNorm` — `|linPerturb θ ω| ≤ ‖θ‖ · ‖g_P_total ω‖`
  pointwise (Cauchy-Schwarz in ℝᵐ).
* `sqrt_kSigmoid_lipschitz` / `hasDerivAt_sqrt_kSigmoid_zero` — `Real.sqrt ∘ kSigmoid`
  is `C¹` on ℝ with Lipschitz constant `1`, and has derivative `1/2` at `0`.
* `hellinger_residual_sq_integral_isLittleO` — the central L²-DCT computation,
  using only `g_P i ∈ L²(P)`.
* `unboundedParamSubmodel_DQM` — assembles these into the DQM structure.
* `unboundedParamSubmodel_fisher_info` — orthonormality ⇒ `I_m`.

References:
* vdV §25.16: sigmoid construction.
* vdV §7.2: DQM definition.
-/

section S2_DQM

variable {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))

/-! ### Continuity of the normaliser `c` at `0` -/

/-- The denominator `1 + exp(-2x)` of `kSigmoid` is `≥ 1`. -/
private lemma kSigmoid_denom_ge_one (x : ℝ) : 1 ≤ 1 + Real.exp (-2 * x) := by
  have := (Real.exp_pos (-2 * x)).le
  linarith

/-- A continuity helper: `kSigmoid (linPerturb g_P θ ω)` tends to `1` as
`θ → 0`, pointwise in `ω`. -/
private lemma kSigmoid_linPerturb_tendsto_one (ω : Ω) :
    Tendsto (fun θ : EuclideanSpace ℝ (Fin m) =>
      kSigmoid (linPerturb g_P θ ω)) (𝓝 0) (𝓝 1) := by
  classical
  -- linPerturb g_P · ω is continuous as a function of θ (linear).
  have h_lin_cont : Continuous (fun θ : EuclideanSpace ℝ (Fin m) =>
      linPerturb g_P θ ω) := by
    unfold linPerturb
    refine continuous_finset_sum _ (fun i _ => ?_)
    -- θ ↦ θ i is continuous (coordinate projection), so θ i * gMk g_P i ω is continuous.
    have h_proj : Continuous (fun θ : EuclideanSpace ℝ (Fin m) => θ i) := by
      exact (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
    exact h_proj.mul continuous_const
  -- At θ = 0, linPerturb = 0, so kSigmoid (linPerturb 0 ω) = kSigmoid 0 = 1.
  have h_lin_zero : linPerturb g_P (0 : EuclideanSpace ℝ (Fin m)) ω = 0 := by
    unfold linPerturb; simp [zero_mul]
  have h_compose : Tendsto (fun θ : EuclideanSpace ℝ (Fin m) =>
      kSigmoid (linPerturb g_P θ ω)) (𝓝 0) (𝓝 (kSigmoid 0)) := by
    have h_eval : Tendsto (fun θ : EuclideanSpace ℝ (Fin m) =>
        linPerturb g_P θ ω) (𝓝 0) (𝓝 (linPerturb g_P 0 ω)) :=
      h_lin_cont.tendsto _
    rw [h_lin_zero] at h_eval
    exact (continuous_kSigmoid.tendsto _).comp h_eval
  rw [kSigmoid_zero] at h_compose
  exact h_compose

/-- The integral `∫ k(linPerturb θ) dP` tends to `1 = ∫ k(0) dP` as `θ → 0`.
Hence `c θ = (∫ k(linPerturb θ) dP)⁻¹` tends to `1` as `θ → 0`. Proof: bounded
convergence (`|k| ≤ 2`, finite measure) applied to the pointwise convergence of
the integrand. -/
theorem normalizer_c_integral_tendsto_one :
    Tendsto (fun θ : EuclideanSpace ℝ (Fin m) =>
      ∫ ω, normalizer_c_integrand g_P θ ω ∂P) (𝓝 0) (𝓝 1) := by
  classical
  -- Sequential characterization (𝓝 0 in EuclideanSpace is countably generated).
  rw [Filter.tendsto_iff_seq_tendsto]
  intro θ_seq hθ_tendsto
  -- For each ω, pointwise: kSigmoid (linPerturb (θ_seq n) ω) → kSigmoid 0 = 1.
  have h_pt : ∀ ω, Tendsto (fun n : ℕ =>
      normalizer_c_integrand g_P (θ_seq n) ω) atTop (𝓝 1) := by
    intro ω
    have := (kSigmoid_linPerturb_tendsto_one g_P ω).comp hθ_tendsto
    exact this
  -- Dominated convergence with bound = 2.
  have h_meas : ∀ n, Measurable (normalizer_c_integrand g_P (θ_seq n)) :=
    fun n => normalizer_c_integrand_meas g_P _
  have h_bound : ∀ n, ∀ᵐ ω ∂P,
      ‖normalizer_c_integrand g_P (θ_seq n) ω‖ ≤ 2 := by
    intro n
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_of_nonneg (normalizer_c_integrand_nonneg _ _ _)]
    exact normalizer_c_integrand_le_two g_P _ _
  -- The constant function 2 is integrable (finite measure).
  have h_const_int : Integrable (fun _ : Ω => (2 : ℝ)) P := integrable_const _
  -- DCT: ∫ F_n dP → ∫ 1 dP = 1 (since P is a probability measure).
  have h_dct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun n ω => normalizer_c_integrand g_P (θ_seq n) ω)
    (f := fun _ => (1 : ℝ))
    (bound := fun _ => (2 : ℝ))
    (fun n => (h_meas n).aestronglyMeasurable) h_const_int h_bound
    (Filter.Eventually.of_forall h_pt)
  simpa using! h_dct

/-- The normaliser `c θ = (∫ k(linPerturb θ) dP)⁻¹` tends to `1` as `θ → 0`. -/
theorem normalizer_c_tendsto_one :
    Tendsto (fun θ : EuclideanSpace ℝ (Fin m) => normalizer_c g_P θ)
      (𝓝 0) (𝓝 1) := by
  unfold normalizer_c
  have h_int := normalizer_c_integral_tendsto_one g_P
  -- Inverse is continuous at 1 ≠ 0.
  have h_inv_cont : Tendsto (fun y : ℝ => y⁻¹) (𝓝 1) (𝓝 (1 : ℝ)⁻¹) :=
    tendsto_inv₀ one_ne_zero
  have := h_inv_cont.comp h_int
  simpa using! this

/-- Likewise `Real.sqrt (c θ) → 1` as `θ → 0`. -/
theorem sqrt_normalizer_c_tendsto_one :
    Tendsto (fun θ : EuclideanSpace ℝ (Fin m) => Real.sqrt (normalizer_c g_P θ))
      (𝓝 0) (𝓝 1) := by
  have h := normalizer_c_tendsto_one g_P
  have h_sqrt_cont : Tendsto (fun y : ℝ => Real.sqrt y) (𝓝 1) (𝓝 (Real.sqrt 1)) :=
    (Real.continuous_sqrt.tendsto _)
  rw [Real.sqrt_one] at h_sqrt_cont
  exact h_sqrt_cont.comp h

/-! ### L²-domination of the linear perturbation -/

/-- The non-negative "joint pointwise norm" `(∑_i (gMk g_P i ω)²)^{1/2}`,
which dominates `|linPerturb g_P θ ω|` via Cauchy-Schwarz. -/
noncomputable def jointPointwiseNorm (ω : Ω) : ℝ :=
  Real.sqrt (∑ i : Fin m, (gMk g_P i ω) ^ 2)

lemma jointPointwiseNorm_nonneg (ω : Ω) : 0 ≤ jointPointwiseNorm g_P ω :=
  Real.sqrt_nonneg _

lemma jointPointwiseNorm_meas : Measurable (jointPointwiseNorm g_P) := by
  unfold jointPointwiseNorm
  refine (Finset.measurable_sum _ ?_).sqrt
  intro i _; exact (gMk_meas g_P i).pow_const 2

/-- Pointwise Cauchy-Schwarz on the linear perturbation:
`|∑_i θ_i · gMk_i ω| ≤ ‖θ‖ · (∑_i (gMk_i ω)²)^{1/2}`. -/
theorem abs_linPerturb_le_jointPointwiseNorm
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    |linPerturb g_P θ ω| ≤ ‖θ‖ * jointPointwiseNorm g_P ω := by
  classical
  unfold linPerturb jointPointwiseNorm
  -- Cauchy-Schwarz: (∑ θ_i · x_i)² ≤ (∑ θ_i²)(∑ x_i²) via `Finset.sum_mul_sq_le_sq_mul_sq`.
  have h_cs_sq : (∑ i : Fin m, θ i * gMk g_P i ω) ^ 2 ≤
      (∑ i : Fin m, (θ i) ^ 2) * (∑ i : Fin m, (gMk g_P i ω) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) (fun i => θ i)
      (fun i => gMk g_P i ω)
  have h_sum_sq_θ_nn : 0 ≤ ∑ i : Fin m, (θ i) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_sum_sq_g_nn : 0 ≤ ∑ i : Fin m, (gMk g_P i ω) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- Take square roots of h_cs_sq.
  have h_lhs_eq : Real.sqrt ((∑ i : Fin m, θ i * gMk g_P i ω) ^ 2) =
      |∑ i : Fin m, θ i * gMk g_P i ω| :=
    Real.sqrt_sq_eq_abs _
  have h_rhs_eq : Real.sqrt ((∑ i : Fin m, (θ i) ^ 2) *
      (∑ i : Fin m, (gMk g_P i ω) ^ 2)) =
      Real.sqrt (∑ i : Fin m, (θ i) ^ 2) *
        Real.sqrt (∑ i : Fin m, (gMk g_P i ω) ^ 2) :=
    Real.sqrt_mul h_sum_sq_θ_nn _
  have h_sqrt_mono := Real.sqrt_le_sqrt h_cs_sq
  rw [h_lhs_eq, h_rhs_eq] at h_sqrt_mono
  -- Identify √(∑ θ_i²) = ‖θ‖ in EuclideanSpace.
  have h_norm_θ : Real.sqrt (∑ i : Fin m, (θ i) ^ 2) = ‖θ‖ := by
    rw [EuclideanSpace.norm_eq]
    apply congrArg
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_norm_θ] at h_sqrt_mono
  exact h_sqrt_mono

/-- The joint pointwise norm `(∑_i gMk_i ²)^{1/2}` is in `L²(P)` because
each `gMk_i` is in `L²(P)` and finite sums of L² functions are L² (the L²
norm of the joint pointwise norm equals the L² norm of the vector
function, which is bounded by `∑_i ‖g_P i‖_{L²}`). -/
lemma jointPointwiseNorm_memLp_two :
    MemLp (jointPointwiseNorm g_P) 2 P := by
  classical
  -- |jointPointwiseNorm ω|² = ∑ i, (gMk i ω)².
  -- The square is an a.e.-finite sum of integrable functions (gMk i is in L²,
  -- and L² norm closed under sums).
  -- Cleaner: show |jointPointwiseNorm| ≤ ∑ i |gMk i| pointwise (since for nonneg
  -- a_i, √(∑ a_i²) ≤ ∑ |a_i|), and each |gMk i| is in L². Then dominated by
  -- a finite sum of L² functions.
  have h_sum_memLp : MemLp (fun ω => ∑ i : Fin m, |gMk g_P i ω|) 2 P := by
    have h_each : ∀ i : Fin m, MemLp (fun ω => |gMk g_P i ω|) 2 P := by
      intro i
      have h_int : MemLp ((g_P i : Lp ℝ 2 P) : Ω → ℝ) 2 P := Lp.memLp _
      have h_mk : MemLp (gMk g_P i) 2 P :=
        MeasureTheory.MemLp.ae_eq (gMk_ae_eq g_P i).symm h_int
      exact h_mk.abs
    exact memLp_finset_sum _ (fun i _ => h_each i)
  refine MemLp.of_le_mul (c := 1) h_sum_memLp
    (jointPointwiseNorm_meas g_P).aestronglyMeasurable ?_
  · -- |jointPointwiseNorm ω| ≤ 1 * ∑ i |gMk i ω|.
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_of_nonneg (jointPointwiseNorm_nonneg g_P ω), one_mul,
        Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    unfold jointPointwiseNorm
    -- √(∑ a_i²) ≤ ∑ |a_i|: since (∑ |a_i|)² ≥ ∑ a_i² (cross terms nonneg).
    -- Prove: for each i, |aᵢ|² ≤ |aᵢ| · (∑ⱼ |aⱼ|), then sum.
    have h_each : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        (gMk g_P i ω) ^ 2 ≤ |gMk g_P i ω| * (∑ j : Fin m, |gMk g_P j ω|) := by
      intro i _
      have h_abs_le : |gMk g_P i ω| ≤ ∑ j : Fin m, |gMk g_P j ω| :=
        Finset.single_le_sum (f := fun j => |gMk g_P j ω|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      have h_abs_nn : 0 ≤ |gMk g_P i ω| := abs_nonneg _
      have h_pow_eq : (gMk g_P i ω) ^ 2 = |gMk g_P i ω| * |gMk g_P i ω| := by
        rw [← sq_abs, sq]
      rw [h_pow_eq]
      exact mul_le_mul_of_nonneg_left h_abs_le h_abs_nn
    have h_sum_le : ∑ i : Fin m, (gMk g_P i ω) ^ 2 ≤
        (∑ i : Fin m, |gMk g_P i ω|) * (∑ j : Fin m, |gMk g_P j ω|) := by
      calc ∑ i : Fin m, (gMk g_P i ω) ^ 2
          ≤ ∑ i : Fin m, |gMk g_P i ω| * (∑ j : Fin m, |gMk g_P j ω|) :=
            Finset.sum_le_sum h_each
        _ = (∑ i : Fin m, |gMk g_P i ω|) * (∑ j : Fin m, |gMk g_P j ω|) := by
            rw [← Finset.sum_mul]
    have h_target : ∑ i : Fin m, (gMk g_P i ω) ^ 2 ≤
        (∑ i : Fin m, |gMk g_P i ω|) ^ 2 := by
      rw [sq]; exact h_sum_le
    have h_rhs_nn : 0 ≤ ∑ i : Fin m, |gMk g_P i ω| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    calc Real.sqrt (∑ i : Fin m, (gMk g_P i ω) ^ 2)
        ≤ Real.sqrt ((∑ i : Fin m, |gMk g_P i ω|) ^ 2) := Real.sqrt_le_sqrt h_target
      _ = ∑ i : Fin m, |gMk g_P i ω| := by
          rw [Real.sqrt_sq h_rhs_nn]

/-! ### Lipschitz and Taylor properties of `Real.sqrt ∘ kSigmoid` -/

/-- Derivative of `Real.sqrt ∘ kSigmoid` at any `x : ℝ`. -/
private lemma hasDerivAt_sqrt_kSigmoid (x : ℝ) :
    HasDerivAt (fun y => Real.sqrt (kSigmoid y))
      (4 * Real.exp (-2 * x) / (1 + Real.exp (-2 * x))^2 /
        (2 * Real.sqrt (kSigmoid x))) x := by
  have h_k := hasDerivAt_kSigmoid x
  have h_kpos : 0 < kSigmoid x := kSigmoid_pos x
  exact h_k.sqrt (ne_of_gt h_kpos)

/-- Taylor at 0: `Real.sqrt ∘ kSigmoid` has derivative `1/2` at `0`. -/
theorem hasDerivAt_sqrt_kSigmoid_zero :
    HasDerivAt (fun y => Real.sqrt (kSigmoid y)) (1/2 : ℝ) 0 := by
  have h := hasDerivAt_sqrt_kSigmoid 0
  have hexp : Real.exp (-2 * 0) = 1 := by rw [mul_zero, Real.exp_zero]
  rw [hexp] at h
  have h_k0 : kSigmoid 0 = 1 := kSigmoid_zero
  rw [h_k0, Real.sqrt_one] at h
  have h_eq : (4 * 1 / (1 + 1) ^ 2 / (2 * 1) : ℝ) = 1/2 := by norm_num
  rw [h_eq] at h
  exact h

/-- The derivative of `Real.sqrt ∘ kSigmoid` is bounded in absolute value by `1`.

The key computation: letting `u = exp(-2x) > 0`,
`(√k)'(x) = 4u/((1+u)² · 2√(2/(1+u))) = √2 · u / (1+u)^{3/2}`.
The function `u ↦ u/(1+u)^{3/2}` on `(0, ∞)` attains its max at `u=2`,
giving `2/(3·√3)`, so the absolute value is bounded by `√2 · 2/(3√3) =
2√6/9 < 1`. -/
private lemma abs_deriv_sqrt_kSigmoid_le_one (x : ℝ) :
    |deriv (fun y => Real.sqrt (kSigmoid y)) x| ≤ 1 := by
  rw [(hasDerivAt_sqrt_kSigmoid x).deriv]
  set u := Real.exp (-2 * x) with hu_def
  have hu_pos : 0 < u := Real.exp_pos _
  have h_kpos : 0 < kSigmoid x := kSigmoid_pos x
  have h_sqrt_k_pos : 0 < Real.sqrt (kSigmoid x) := Real.sqrt_pos.mpr h_kpos
  have h_denom_pos : 0 < (1 + u)^2 := by positivity
  have h_2sqrtk_pos : 0 < 2 * Real.sqrt (kSigmoid x) := by positivity
  -- The expression is non-negative.
  have h_num_nn : 0 ≤ 4 * u / (1 + u)^2 := by positivity
  have h_quot_nn : 0 ≤ 4 * u / (1 + u)^2 / (2 * Real.sqrt (kSigmoid x)) := by
    positivity
  rw [abs_of_nonneg h_quot_nn]
  -- Compute kSigmoid x = 2/(1+u): so sqrt (kSigmoid x) = sqrt(2/(1+u)).
  have h_k_eq : kSigmoid x = 2 / (1 + u) := rfl
  -- The expression equals `sqrt 2 · u / (1+u)^{3/2}`. We bound it by squaring:
  -- prove `(4u/(1+u)²)² ≤ 4·kSigmoid(x)`, i.e. `2u² ≤ (1+u)³`, then take sqrt.
  -- Indeed `(1+u)³ - 2u² = 1 + 3u + u² + u³ ≥ 0` for `u ≥ 0`, so
  -- `4u/(1+u)² ≤ 2·sqrt(kSigmoid x)`, hence the quotient is `≤ 1`.
  have h_one_plus_u_pos : 0 < 1 + u := by linarith
  have h_squared_bound : (4 * u / (1 + u)^2)^2 ≤ 4 * kSigmoid x := by
    rw [h_k_eq]
    -- Want: (4u/(1+u)²)² ≤ 4·(2/(1+u)), i.e. 16u²/(1+u)⁴ ≤ 8/(1+u).
    -- Cross-multiplying (both denominators positive): 16u²·(1+u) ≤ 8·(1+u)⁴.
    -- Equivalently 2u² ≤ (1+u)³. Expanding: 1 + 3u + 3u² + u³ - 2u² = 1+3u+u²+u³ ≥ 0.
    have h_denom1_pos : (0 : ℝ) < (1 + u)^4 := by positivity
    have h_lhs_eq : (4 * u / (1 + u)^2)^2 = 16 * u^2 / (1 + u)^4 := by
      field_simp; ring
    have h_rhs_eq : 4 * (2 / (1 + u)) = 8 / (1 + u) := by ring
    rw [h_lhs_eq, h_rhs_eq]
    rw [div_le_div_iff₀ h_denom1_pos h_one_plus_u_pos]
    -- Now: 16 * u^2 * (1+u) ≤ 8 * (1+u)^4.
    nlinarith [hu_pos, sq_nonneg u, sq_nonneg (1+u), mul_pos hu_pos h_one_plus_u_pos]
  -- From a² ≤ b² with a, b ≥ 0, conclude a ≤ b.
  have h_4u_nn : 0 ≤ 4 * u / (1 + u)^2 := h_num_nn
  have h_2sqrtk_nn : 0 ≤ 2 * Real.sqrt (kSigmoid x) := h_2sqrtk_pos.le
  have h_2sqrtk_sq : (2 * Real.sqrt (kSigmoid x))^2 = 4 * kSigmoid x := by
    rw [mul_pow, Real.sq_sqrt h_kpos.le]; ring
  have h_4u_le : 4 * u / (1 + u)^2 ≤ 2 * Real.sqrt (kSigmoid x) := by
    have h1 : (4 * u / (1 + u)^2)^2 ≤ (2 * Real.sqrt (kSigmoid x))^2 := by
      rw [h_2sqrtk_sq]; exact h_squared_bound
    -- a² ≤ b² with a, b ≥ 0 ⇒ a ≤ b: take sqrt.
    have h_sqrt := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq h_4u_nn, Real.sqrt_sq h_2sqrtk_nn] at h_sqrt
    exact h_sqrt
  -- Conclude: quotient ≤ 1.
  rw [div_le_one h_2sqrtk_pos]
  exact h_4u_le

/-- Global Lipschitz bound on `√k`: for all `x, y : ℝ`,
`|√k(x) - √k(y)| ≤ 1 · |x - y|`.

This is via the mean-value theorem applied to `√k` on `ℝ`, using that
`(√k)'` is bounded by `1` (proved in `abs_deriv_sqrt_kSigmoid_le_one`). It is
the Lipschitz bound that lets L²-DCT apply without strengthening the moment
hypothesis. -/
theorem sqrt_kSigmoid_lipschitz (x y : ℝ) :
    |Real.sqrt (kSigmoid x) - Real.sqrt (kSigmoid y)| ≤ |x - y| := by
  -- Use Convex.norm_image_sub_le_of_norm_deriv_le on s = Set.univ.
  have h_diff : ∀ z ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (fun w => Real.sqrt (kSigmoid w)) z := by
    intro z _
    exact (hasDerivAt_sqrt_kSigmoid z).differentiableAt
  have h_bound : ∀ z ∈ (Set.univ : Set ℝ),
      ‖deriv (fun w => Real.sqrt (kSigmoid w)) z‖ ≤ 1 := by
    intro z _
    rw [Real.norm_eq_abs]
    exact abs_deriv_sqrt_kSigmoid_le_one z
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    h_diff h_bound (Set.mem_univ y) (Set.mem_univ x)
  -- h : ‖√k(x) - √k(y)‖ ≤ 1 * ‖x - y‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at h
  exact h

/-- Companion bound: `|k(x) - k(y)| ≤ |x - y|` (`kSigmoid` is also Lipschitz
with constant `1`, from `abs_deriv_kSigmoid_le_one`). -/
theorem kSigmoid_lipschitz (x y : ℝ) :
    |kSigmoid x - kSigmoid y| ≤ |x - y| := by
  have h_diff : ∀ z ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ kSigmoid z := by
    intro z _
    exact (hasDerivAt_kSigmoid z).differentiableAt
  have h_bound : ∀ z ∈ (Set.univ : Set ℝ),
      ‖deriv kSigmoid z‖ ≤ 1 := by
    intro z _
    rw [Real.norm_eq_abs]
    exact abs_deriv_kSigmoid_le_one z
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    h_diff h_bound (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at h
  exact h

/-! ### Strong Taylor for `c θ` and DCT helpers -/

/-- A DCT lemma: for any sequence `θ_n → 0` (in `EuclideanSpace ℝ (Fin m)`)
with eventually `‖θ_n‖ ≠ 0`, the rescaled "first-order error" of `kSigmoid`
along `linPerturb θ_n` integrates to 0:
`∫ ω, (k(Sθ_n ω) - 1 - Sθ_n ω) / ‖θ_n‖ dP → 0`.

This is the key Bochner-DCT application behind `(c θ - 1)/‖θ‖ → 0`. The
integrand is bounded a.e. by `2 · jointPointwiseNorm`, which is in `L¹(P)`
(since it's in `L²(P)` and `P` is a probability measure). -/
private lemma integral_kSigmoid_residual_div_norm_tendsto_zero
    {θ_n : ℕ → EuclideanSpace ℝ (Fin m)}
    (hθ_tendsto : Tendsto θ_n atTop (𝓝 0))
    (hθ_ne : ∀ n, θ_n n ≠ 0) :
    Tendsto (fun n : ℕ =>
      ∫ ω, (kSigmoid (linPerturb g_P (θ_n n) ω) - 1 - linPerturb g_P (θ_n n) ω) /
        ‖θ_n n‖ ∂P) atTop (𝓝 0) := by
  classical
  -- jointPointwiseNorm is in L²(P), hence L¹(P) (probability measure).
  have h_jpn_memLp : MemLp (jointPointwiseNorm g_P) 2 P :=
    jointPointwiseNorm_memLp_two g_P
  have h_jpn_int : Integrable (jointPointwiseNorm g_P) P :=
    h_jpn_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  -- Bound `2 * jointPointwiseNorm` is integrable.
  have h_bound_int : Integrable (fun ω => 2 * jointPointwiseNorm g_P ω) P :=
    h_jpn_int.const_mul 2
  -- Apply DCT to the sequence (k(Sθ_n) - 1 - Sθ_n)/‖θ_n‖.
  -- Pointwise: → 0. Dominated by 2·jointPointwiseNorm.
  set F : ℕ → Ω → ℝ := fun n ω =>
    (kSigmoid (linPerturb g_P (θ_n n) ω) - 1 - linPerturb g_P (θ_n n) ω) / ‖θ_n n‖
  have h_meas : ∀ n, Measurable (F n) := by
    intro n
    refine Measurable.div_const ?_ _
    refine (((continuous_kSigmoid.measurable.comp (linPerturb_meas g_P _)).sub
      measurable_const).sub (linPerturb_meas g_P _))
  have h_bd : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ 2 * jointPointwiseNorm g_P ω := by
    intro n
    have hθn_pos : 0 < ‖θ_n n‖ := norm_pos_iff.mpr (hθ_ne n)
    refine Filter.Eventually.of_forall (fun ω => ?_)
    -- |F n ω| = |k(Sθ_n ω) - 1 - Sθ_n ω| / ‖θ_n‖ ≤ 2 · |Sθ_n ω| / ‖θ_n‖
    --        ≤ 2 · jointPointwiseNorm ω.
    rw [Real.norm_eq_abs]
    have h_num : |kSigmoid (linPerturb g_P (θ_n n) ω) - 1 -
        linPerturb g_P (θ_n n) ω| ≤ 2 * |linPerturb g_P (θ_n n) ω| := by
      have h_k_lip : |kSigmoid (linPerturb g_P (θ_n n) ω) - 1| ≤
          |linPerturb g_P (θ_n n) ω| := by
        have := kSigmoid_lipschitz (linPerturb g_P (θ_n n) ω) 0
        rw [kSigmoid_zero, sub_zero] at this
        exact this
      calc |kSigmoid (linPerturb g_P (θ_n n) ω) - 1 - linPerturb g_P (θ_n n) ω|
          ≤ |kSigmoid (linPerturb g_P (θ_n n) ω) - 1| + |linPerturb g_P (θ_n n) ω| := by
            have h_sub : kSigmoid (linPerturb g_P (θ_n n) ω) - 1 -
                  linPerturb g_P (θ_n n) ω =
                (kSigmoid (linPerturb g_P (θ_n n) ω) - 1) +
                  (-linPerturb g_P (θ_n n) ω) := by ring
            rw [h_sub]
            calc |(kSigmoid (linPerturb g_P (θ_n n) ω) - 1) +
                  (-linPerturb g_P (θ_n n) ω)|
                ≤ |kSigmoid (linPerturb g_P (θ_n n) ω) - 1| +
                    |-linPerturb g_P (θ_n n) ω| := abs_add_le _ _
              _ = |kSigmoid (linPerturb g_P (θ_n n) ω) - 1| +
                    |linPerturb g_P (θ_n n) ω| := by rw [abs_neg]
        _ ≤ |linPerturb g_P (θ_n n) ω| + |linPerturb g_P (θ_n n) ω| := by linarith
        _ = 2 * |linPerturb g_P (θ_n n) ω| := by ring
    rw [abs_div, abs_of_pos hθn_pos]
    rw [div_le_iff₀ hθn_pos]
    -- Need: |numerator| ≤ 2 · jointPointwiseNorm · ‖θ_n‖.
    have h_lin : |linPerturb g_P (θ_n n) ω| ≤
        ‖θ_n n‖ * jointPointwiseNorm g_P ω :=
      abs_linPerturb_le_jointPointwiseNorm g_P (θ_n n) ω
    have h_jpn_nn : 0 ≤ jointPointwiseNorm g_P ω := jointPointwiseNorm_nonneg _ _
    calc |kSigmoid (linPerturb g_P (θ_n n) ω) - 1 - linPerturb g_P (θ_n n) ω|
        ≤ 2 * |linPerturb g_P (θ_n n) ω| := h_num
      _ ≤ 2 * (‖θ_n n‖ * jointPointwiseNorm g_P ω) := by
          have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
          exact mul_le_mul_of_nonneg_left h_lin h2_nn
      _ = 2 * jointPointwiseNorm g_P ω * ‖θ_n n‖ := by ring
  -- Pointwise convergence: for each ω, F n ω → 0.
  have h_pt : ∀ ω, Tendsto (fun n => F n ω) atTop (𝓝 0) := by
    intro ω
    -- `f(x) := k(x) - 1 - x` has `f(0) = f'(0) = 0`, so `f(x) = o(x)` via
    -- `HasDerivAt kSigmoid 1 0`: ∀ ε > 0, ∃ δ > 0, ∀ |x| < δ, |k(x) - 1 - x| ≤ ε · |x|.
    -- Hence |F n ω| ≤ ε · |Sθ_n ω| / ‖θ_n‖ ≤ ε · jointPointwiseNorm ω, and as
    -- ε → 0, F n ω → 0.
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    -- Get δ from HasDerivAt.
    have h_kderiv := hasDerivAt_kSigmoid_zero
    -- HasDerivAt k 1 0 means k(x) - k(0) - 1·x is o(x), i.e. (k(x) - 1 - x)/x → 0.
    have h_little_o :
        (fun x => kSigmoid x - 1 - x) =o[𝓝 0] fun x => x := by
      have := h_kderiv.isLittleO
      simpa [kSigmoid_zero, sub_zero] using this
    -- For ω with jointPointwiseNorm g_P ω = 0: linPerturb θ_n ω = 0 always,
    -- so kSigmoid - 1 - linPerturb = kSigmoid 0 - 1 - 0 = 0. F n ω = 0.
    by_cases h_jpn_zero : jointPointwiseNorm g_P ω = 0
    · refine ⟨0, fun n _ => ?_⟩
      have h_lin_zero : linPerturb g_P (θ_n n) ω = 0 := by
        have hbnd := abs_linPerturb_le_jointPointwiseNorm g_P (θ_n n) ω
        rw [h_jpn_zero, mul_zero] at hbnd
        have h_abs_nn : 0 ≤ |linPerturb g_P (θ_n n) ω| := abs_nonneg _
        have := le_antisymm hbnd h_abs_nn
        exact abs_eq_zero.mp this
      have hθn_pos : 0 < ‖θ_n n‖ := norm_pos_iff.mpr (hθ_ne n)
      have hF_zero : F n ω = 0 := by
        change (kSigmoid (linPerturb g_P (θ_n n) ω) - 1 -
            linPerturb g_P (θ_n n) ω) / ‖θ_n n‖ = 0
        rw [h_lin_zero, kSigmoid_zero, sub_self, zero_sub, neg_zero, zero_div]
      rw [Real.dist_eq, hF_zero, sub_zero, abs_zero]
      exact hε
    -- jointPointwiseNorm g_P ω > 0. Use the little-o bound with ε' = ε / jointNorm.
    have h_jpn_pos : 0 < jointPointwiseNorm g_P ω :=
      lt_of_le_of_ne (jointPointwiseNorm_nonneg g_P ω) (Ne.symm h_jpn_zero)
    set ε' := ε / (jointPointwiseNorm g_P ω + 1) with hε'_def
    have h_jpn_p1_pos : 0 < jointPointwiseNorm g_P ω + 1 := by linarith
    have hε'_pos : 0 < ε' := div_pos hε h_jpn_p1_pos
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      Metric.eventually_nhds_iff.mp (h_little_o.bound hε'_pos)
    -- Need linPerturb (θ_n n) ω → 0 to apply δ-bound eventually.
    have h_lin_tendsto : Tendsto (fun n => linPerturb g_P (θ_n n) ω) atTop (𝓝 0) := by
      have h_cont : Continuous (fun θ : EuclideanSpace ℝ (Fin m) =>
          linPerturb g_P θ ω) := by
        unfold linPerturb
        refine continuous_finset_sum _ (fun i _ => ?_)
        have h_proj : Continuous (fun θ : EuclideanSpace ℝ (Fin m) => θ i) :=
          (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
        exact h_proj.mul continuous_const
      have h_eval : Tendsto (fun n => linPerturb g_P (θ_n n) ω) atTop
          (𝓝 (linPerturb g_P 0 ω)) :=
        (h_cont.tendsto _).comp hθ_tendsto
      have h_lin0 : linPerturb g_P (0 : EuclideanSpace ℝ (Fin m)) ω = 0 := by
        unfold linPerturb; simp [zero_mul]
      rw [h_lin0] at h_eval
      exact h_eval
    -- Find N so that for n ≥ N, |linPerturb θ_n ω| < δ.
    have h_lin_eventually : ∀ᶠ n in atTop,
        |linPerturb g_P (θ_n n) ω| < δ := by
      rw [Metric.tendsto_atTop] at h_lin_tendsto
      obtain ⟨N, hN⟩ := h_lin_tendsto δ hδ_pos
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have := hN n hn
      rwa [Real.dist_eq, sub_zero] at this
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_lin_eventually
    refine ⟨N, fun n hn => ?_⟩
    have hθn_pos : 0 < ‖θ_n n‖ := norm_pos_iff.mpr (hθ_ne n)
    have h_lin_lt_δ := hN n hn
    -- Apply δ-bound.
    have h_in_ball : linPerturb g_P (θ_n n) ω ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact h_lin_lt_δ
    have h_bd_n := hδ (Metric.mem_ball.mp h_in_ball)
    -- h_bd_n : ‖kSigmoid (linPerturb θ_n ω) - 1 - linPerturb θ_n ω‖ ≤ ε' · ‖linPerturb θ_n ω‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h_bd_n
    -- Now bound F n ω.
    have h_lin_le_jpn : |linPerturb g_P (θ_n n) ω| ≤
        ‖θ_n n‖ * jointPointwiseNorm g_P ω :=
      abs_linPerturb_le_jointPointwiseNorm g_P (θ_n n) ω
    rw [Real.dist_eq, sub_zero]
    change |F n ω| < ε
    change |(kSigmoid (linPerturb g_P (θ_n n) ω) - 1 - linPerturb g_P (θ_n n) ω) /
        ‖θ_n n‖| < ε
    rw [abs_div, abs_of_pos hθn_pos, div_lt_iff₀ hθn_pos]
    -- Need: |...| < ε · ‖θ_n‖.
    have h_jpn_nn : 0 ≤ jointPointwiseNorm g_P ω := jointPointwiseNorm_nonneg _ _
    calc |kSigmoid (linPerturb g_P (θ_n n) ω) - 1 - linPerturb g_P (θ_n n) ω|
        ≤ ε' * |linPerturb g_P (θ_n n) ω| := h_bd_n
      _ ≤ ε' * (‖θ_n n‖ * jointPointwiseNorm g_P ω) :=
          mul_le_mul_of_nonneg_left h_lin_le_jpn hε'_pos.le
      _ = ε' * jointPointwiseNorm g_P ω * ‖θ_n n‖ := by ring
      _ < ε * ‖θ_n n‖ := by
          have h_factor : ε' * jointPointwiseNorm g_P ω < ε := by
            rw [hε'_def, div_mul_eq_mul_div]
            rw [div_lt_iff₀ h_jpn_p1_pos]
            nlinarith [h_jpn_pos, hε]
          have h_mul := mul_lt_mul_of_pos_right h_factor hθn_pos
          exact h_mul
  -- DCT.
  have h_dct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := F) (f := fun _ => (0 : ℝ))
    (bound := fun ω => 2 * jointPointwiseNorm g_P ω)
    (fun n => (h_meas n).aestronglyMeasurable) h_bound_int h_bd
    (Filter.Eventually.of_forall h_pt)
  simpa using h_dct

/-! ### `(c θ - 1) / ‖θ‖ → 0` -/

/-- `c(θ) = 1 + o(‖θ‖)` along sequences with `‖θ_n‖ ≠ 0`. -/
theorem normalizer_c_sub_one_div_norm_tendsto_zero_along_seq
    {θ_n : ℕ → EuclideanSpace ℝ (Fin m)}
    (hθ_tendsto : Tendsto θ_n atTop (𝓝 0))
    (hθ_ne : ∀ n, θ_n n ≠ 0) :
    Tendsto (fun n : ℕ => (normalizer_c g_P (θ_n n) - 1) / ‖θ_n n‖) atTop (𝓝 0) := by
  classical
  -- Let Ĉ(θ) := ∫ k(linPerturb θ ω) dP. Then c(θ) = 1/Ĉ(θ).
  -- (c - 1)/‖θ‖ = (1/Ĉ - 1)/‖θ‖ = (1 - Ĉ)/(Ĉ·‖θ‖)
  --             = -(Ĉ - 1)/(Ĉ·‖θ‖).
  -- (Ĉ - 1) = ∫ (k(Sθ) - 1) dP = ∫ (k(Sθ) - 1 - Sθ) dP + ∫ Sθ dP
  --        = ∫ (k(Sθ) - 1 - Sθ) dP + 0 = ∫ (k(Sθ) - 1 - Sθ) dP.
  -- (Ĉ - 1)/‖θ‖ = ∫ (k(Sθ) - 1 - Sθ)/‖θ‖ dP → 0 (by
  -- integral_kSigmoid_residual_div_norm_tendsto_zero).
  -- Ĉ → 1, so 1/Ĉ → 1, hence -(Ĉ - 1)/(Ĉ · ‖θ‖) → -(0)/(1) · ? ... need care.
  set Ĉ : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun θ => ∫ ω, normalizer_c_integrand g_P θ ω ∂P with hĈ_def
  -- c(θ) = 1/Ĉ(θ) [from definition of normalizer_c].
  have h_c_eq : ∀ θ, normalizer_c g_P θ = (Ĉ θ)⁻¹ := fun θ => rfl
  have h_Ĉ_tendsto : Tendsto (fun n => Ĉ (θ_n n)) atTop (𝓝 1) := by
    have := (normalizer_c_integral_tendsto_one g_P).comp hθ_tendsto
    exact this
  -- Step 1: prove (Ĉ θ_n - 1) / ‖θ_n‖ → 0.
  have h_Ĉ_sub_div : Tendsto (fun n => (Ĉ (θ_n n) - 1) / ‖θ_n n‖) atTop (𝓝 0) := by
    -- (Ĉ - 1) = ∫ (k(Sθ) - 1) dP = ∫ (k(Sθ) - 1 - Sθ) dP + ∫ Sθ dP = ∫ (...) dP.
    have h_step : ∀ n, (Ĉ (θ_n n) - 1) / ‖θ_n n‖ =
        ∫ ω, (kSigmoid (linPerturb g_P (θ_n n) ω) - 1 - linPerturb g_P (θ_n n) ω) /
          ‖θ_n n‖ ∂P := by
      intro n
      have hθn_pos : 0 < ‖θ_n n‖ := norm_pos_iff.mpr (hθ_ne n)
      have hθn_ne : ‖θ_n n‖ ≠ 0 := ne_of_gt hθn_pos
      -- Compute Ĉ(θ_n) - 1.
      have h_Ĉ : Ĉ (θ_n n) - 1 = ∫ ω,
          (kSigmoid (linPerturb g_P (θ_n n) ω) - 1) ∂P := by
        change ∫ ω, normalizer_c_integrand g_P (θ_n n) ω ∂P - 1 = _
        have h_one_int : (1 : ℝ) = ∫ _ω : Ω, (1 : ℝ) ∂P := by simp
        nth_rewrite 1 [h_one_int]
        rw [← integral_sub (normalizer_c_integrand_integrable g_P (θ_n n))
          (integrable_const _)]
        apply integral_congr_ae
        refine Filter.Eventually.of_forall (fun ω => ?_)
        rfl
      -- Now Ĉ - 1 = ∫ (k - 1) = ∫ (k - 1 - linPerturb) + ∫ linPerturb = ∫ (k - 1 - linPerturb).
      have h_Ĉ' : Ĉ (θ_n n) - 1 = ∫ ω,
          (kSigmoid (linPerturb g_P (θ_n n) ω) - 1 -
            linPerturb g_P (θ_n n) ω) ∂P := by
        rw [h_Ĉ]
        have h_split : ∫ ω, (kSigmoid (linPerturb g_P (θ_n n) ω) - 1) ∂P =
            (∫ ω, (kSigmoid (linPerturb g_P (θ_n n) ω) - 1 -
              linPerturb g_P (θ_n n) ω) ∂P) +
            (∫ ω, linPerturb g_P (θ_n n) ω ∂P) := by
          rw [← integral_add ?_ (linPerturb_integrable g_P _)]
          · apply integral_congr_ae
            refine Filter.Eventually.of_forall (fun ω => by ring)
          · -- Integrability of k(Sθ) - 1 - linPerturb θ.
            apply Integrable.sub
            · apply Integrable.sub (normalizer_c_integrand_integrable g_P (θ_n n))
              exact integrable_const _
            · exact linPerturb_integrable g_P _
        rw [h_split, integral_linPerturb_eq_zero, add_zero]
      rw [h_Ĉ']
      rw [integral_div]
    -- Apply the DCT helper.
    have h_dct := integral_kSigmoid_residual_div_norm_tendsto_zero g_P
      hθ_tendsto hθ_ne
    refine h_dct.congr ?_
    intro n; exact (h_step n).symm
  -- Step 2: (c - 1)/‖θ‖ = -(Ĉ - 1)/(Ĉ · ‖θ‖) → 0 since (Ĉ - 1)/‖θ‖ → 0 and Ĉ → 1 ≠ 0.
  have h_seq : ∀ n, (normalizer_c g_P (θ_n n) - 1) / ‖θ_n n‖ =
      -((Ĉ (θ_n n) - 1) / ‖θ_n n‖) / Ĉ (θ_n n) := by
    intro n
    have hθn_pos : 0 < ‖θ_n n‖ := norm_pos_iff.mpr (hθ_ne n)
    have hθn_ne : ‖θ_n n‖ ≠ 0 := ne_of_gt hθn_pos
    have h_Ĉ_pos : 0 < Ĉ (θ_n n) := normalizer_c_integrand_integral_pos g_P (θ_n n)
    have h_Ĉ_ne : Ĉ (θ_n n) ≠ 0 := ne_of_gt h_Ĉ_pos
    rw [h_c_eq]
    field_simp
    ring
  refine Tendsto.congr (fun n => (h_seq n).symm) ?_
  -- Tendsto: -(Ĉ - 1)/‖θ‖ / Ĉ → -0/1 = 0.
  have h_neg : Tendsto (fun n => -((Ĉ (θ_n n) - 1) / ‖θ_n n‖)) atTop (𝓝 (-0)) :=
    h_Ĉ_sub_div.neg
  rw [neg_zero] at h_neg
  have h_div := h_neg.div h_Ĉ_tendsto one_ne_zero
  simpa using! h_div

/-- Corollary: `(√(c(θ_n)) - 1) / ‖θ_n‖ → 0`. -/
theorem sqrt_normalizer_c_sub_one_div_norm_tendsto_zero_along_seq
    {θ_n : ℕ → EuclideanSpace ℝ (Fin m)}
    (hθ_tendsto : Tendsto θ_n atTop (𝓝 0))
    (hθ_ne : ∀ n, θ_n n ≠ 0) :
    Tendsto (fun n : ℕ =>
      (Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖) atTop (𝓝 0) := by
  classical
  -- (√c - 1) / ‖θ‖ = (c - 1) / ((√c + 1) · ‖θ‖) = ((c - 1)/‖θ‖) / (√c + 1).
  -- (c - 1)/‖θ‖ → 0 and √c + 1 → 2 ≠ 0.
  have h_c_div := normalizer_c_sub_one_div_norm_tendsto_zero_along_seq g_P
    hθ_tendsto hθ_ne
  have h_sqrt_c_tendsto :
      Tendsto (fun n => Real.sqrt (normalizer_c g_P (θ_n n)) + 1) atTop (𝓝 2) := by
    have h_c_tendsto := (normalizer_c_tendsto_one g_P).comp hθ_tendsto
    have h_sqrt_c : Tendsto (fun n => Real.sqrt (normalizer_c g_P (θ_n n)))
        atTop (𝓝 1) := by
      have := (Real.continuous_sqrt.tendsto _).comp h_c_tendsto
      simpa [Real.sqrt_one] using! this
    have h_add := h_sqrt_c.add_const (1 : ℝ)
    have h_eq : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h_eq] at h_add
    exact h_add
  have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_div : Tendsto (fun n =>
      ((normalizer_c g_P (θ_n n) - 1) / ‖θ_n n‖) /
        (Real.sqrt (normalizer_c g_P (θ_n n)) + 1)) atTop (𝓝 (0 / 2)) :=
    h_c_div.div h_sqrt_c_tendsto h_2_ne
  rw [zero_div] at h_div
  refine h_div.congr ?_
  intro n
  have hθn_pos : 0 < ‖θ_n n‖ := norm_pos_iff.mpr (hθ_ne n)
  have hθn_ne : ‖θ_n n‖ ≠ 0 := ne_of_gt hθn_pos
  have h_c_pos : 0 < normalizer_c g_P (θ_n n) := normalizer_c_pos g_P _
  have h_sqrt_c_pos : 0 < Real.sqrt (normalizer_c g_P (θ_n n)) :=
    Real.sqrt_pos.mpr h_c_pos
  have h_sum_pos : 0 < Real.sqrt (normalizer_c g_P (θ_n n)) + 1 := by linarith
  have h_sum_ne : Real.sqrt (normalizer_c g_P (θ_n n)) + 1 ≠ 0 := ne_of_gt h_sum_pos
  -- (√c - 1) / ‖θ‖ = ((√c - 1)(√c + 1)) / (‖θ‖(√c + 1)) = (c - 1) / (‖θ‖(√c + 1)).
  have h_sq : (Real.sqrt (normalizer_c g_P (θ_n n)) - 1) *
      (Real.sqrt (normalizer_c g_P (θ_n n)) + 1) =
      normalizer_c g_P (θ_n n) - 1 := by
    have h_sq_eq : Real.sqrt (normalizer_c g_P (θ_n n)) *
        Real.sqrt (normalizer_c g_P (θ_n n)) = normalizer_c g_P (θ_n n) :=
      Real.mul_self_sqrt h_c_pos.le
    nlinarith [h_sq_eq]
  field_simp
  linarith [h_sq]

/-! ### Central L²-DCT residual lemma -/

/-- The Hellinger residual of `unboundedParamSubmodel` at parameter `θ`,
written in unfolded form. This is the same expression that appears in the
`DifferentiableQuadraticMean` structure (with `θ₀ = 0`, `M.sqrtDensity 0
ω = 1`, and inner product = `linPerturb`). -/
noncomputable def hellinger_residual
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) : ℝ :=
  Real.sqrt (normalizer_c g_P θ * kSigmoid (linPerturb g_P θ ω)) - 1 -
    (1/2 : ℝ) * linPerturb g_P θ ω

/-- The residual is bounded a.e. by `(√2 · |√c - 1| + (3/2) · |Sθ|)`. -/
private lemma abs_hellinger_residual_bound
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    |hellinger_residual g_P θ ω| ≤
      Real.sqrt 2 * |Real.sqrt (normalizer_c g_P θ) - 1| +
        (3/2 : ℝ) * |linPerturb g_P θ ω| := by
  unfold hellinger_residual
  -- √(c · k(x)) = √c · √k(x), since both nonneg.
  have h_c_nn : 0 ≤ normalizer_c g_P θ := normalizer_c_nonneg g_P θ
  have h_k_nn : 0 ≤ kSigmoid (linPerturb g_P θ ω) := kSigmoid_nonneg _
  have h_sqrt_split : Real.sqrt (normalizer_c g_P θ * kSigmoid (linPerturb g_P θ ω))
      = Real.sqrt (normalizer_c g_P θ) * Real.sqrt (kSigmoid (linPerturb g_P θ ω)) :=
    Real.sqrt_mul h_c_nn _
  rw [h_sqrt_split]
  -- Split: √c · √k(Sθ) - 1 - Sθ/2 = (√c - 1)·√k(Sθ) + (√k(Sθ) - 1 - Sθ/2).
  set Sθ := linPerturb g_P θ ω
  set sqc := Real.sqrt (normalizer_c g_P θ)
  set sqk := Real.sqrt (kSigmoid Sθ)
  have h_decomp : sqc * sqk - 1 - (1/2 : ℝ) * Sθ =
      (sqc - 1) * sqk + (sqk - 1 - (1/2 : ℝ) * Sθ) := by ring
  rw [h_decomp]
  -- Bound: |A + B| ≤ |A| + |B|.
  calc |(sqc - 1) * sqk + (sqk - 1 - (1/2 : ℝ) * Sθ)|
      ≤ |(sqc - 1) * sqk| + |sqk - 1 - (1/2 : ℝ) * Sθ| := abs_add_le _ _
    _ ≤ Real.sqrt 2 * |sqc - 1| + (3/2 : ℝ) * |Sθ| := by
        gcongr
        · -- |(sqc - 1) * sqk| ≤ √2 · |sqc - 1| since |sqk| ≤ √2.
          rw [abs_mul]
          have h_sqk_le : |sqk| ≤ Real.sqrt 2 := by
            rw [abs_of_nonneg (Real.sqrt_nonneg _)]
            exact Real.sqrt_le_sqrt (kSigmoid_le_two _)
          have h_abs_nn : 0 ≤ |sqc - 1| := abs_nonneg _
          calc |sqc - 1| * |sqk|
              ≤ |sqc - 1| * Real.sqrt 2 :=
                mul_le_mul_of_nonneg_left h_sqk_le h_abs_nn
            _ = Real.sqrt 2 * |sqc - 1| := by ring
        · -- |sqk - 1 - Sθ/2| ≤ (3/2) |Sθ|.
          calc |sqk - 1 - (1/2 : ℝ) * Sθ|
              ≤ |sqk - 1| + |(1/2 : ℝ) * Sθ| := by
                have h_split : sqk - 1 - (1/2 : ℝ) * Sθ =
                    (sqk - 1) + (-((1/2 : ℝ) * Sθ)) := by ring
                rw [h_split]
                calc |(sqk - 1) + (-((1/2 : ℝ) * Sθ))|
                    ≤ |sqk - 1| + |-((1/2 : ℝ) * Sθ)| := abs_add_le _ _
                  _ = |sqk - 1| + |(1/2 : ℝ) * Sθ| := by rw [abs_neg]
            _ ≤ |Sθ| + (1/2 : ℝ) * |Sθ| := by
                have h_lip : |sqk - 1| ≤ |Sθ| := by
                  have := sqrt_kSigmoid_lipschitz Sθ 0
                  rw [kSigmoid_zero, Real.sqrt_one, sub_zero] at this
                  exact this
                have h_half : |(1/2 : ℝ) * Sθ| = (1/2 : ℝ) * |Sθ| := by
                  rw [abs_mul]; congr 1
                  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
                linarith [h_lip, h_half ▸ le_refl ((1/2 : ℝ) * |Sθ|)]
            _ = (3/2 : ℝ) * |Sθ| := by ring

/-- Sequential form of the L²-DCT estimate: for any sequence `θ_n → 0` with
`θ_n ≠ 0`, `∫ (hellinger_residual θ_n)² dP / ‖θ_n‖² → 0`. -/
theorem hellinger_residual_sq_div_norm_sq_tendsto_zero_along_seq
    {θ_n : ℕ → EuclideanSpace ℝ (Fin m)}
    (hθ_tendsto : Tendsto θ_n atTop (𝓝 0))
    (hθ_ne : ∀ n, θ_n n ≠ 0) :
    Tendsto (fun n : ℕ =>
      (∫ ω, (hellinger_residual g_P (θ_n n) ω) ^ 2 ∂P) / ‖θ_n n‖ ^ 2)
      atTop (𝓝 0) := by
  classical
  -- Define r_n(ω) := hellinger_residual θ_n ω / ‖θ_n‖.
  -- Then (∫ residual²) / ‖θ_n‖² = ∫ r_n² dP. Want this → 0.
  set r : ℕ → Ω → ℝ := fun n ω => hellinger_residual g_P (θ_n n) ω / ‖θ_n n‖
  set jpn : Ω → ℝ := jointPointwiseNorm g_P with hjpn_def
  -- jpn ∈ L²(P).
  have h_jpn_memLp : MemLp jpn 2 P := jointPointwiseNorm_memLp_two g_P
  have h_jpn_sq_int : Integrable (fun ω => jpn ω ^ 2) P := h_jpn_memLp.integrable_sq
  have h_jpn_int : Integrable jpn P :=
    h_jpn_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  -- Step 1: pointwise r_n ω → 0.
  -- |r_n ω| ≤ √2 · |√c(θ_n) - 1|/‖θ_n‖ + (3/2) · |Sθ_n ω|/‖θ_n‖
  --        ≤ √2 · |√c(θ_n) - 1|/‖θ_n‖ + (3/2) · jpn ω.
  -- The first term is independent of ω and → 0 by sqrt_normalizer_c_sub_one_div_norm.
  -- Second term: by Bochner DCT on r_n², need pointwise → 0 + L¹ domination.
  --
  -- For pointwise: r_n(ω) = (√c · √k(Sθ_n ω) - 1 - Sθ_n ω/2)/‖θ_n‖.
  -- Split: (√c · √k(Sθ_n ω) - √k(Sθ_n ω))/‖θ_n‖ + (√k(Sθ_n ω) - 1 - Sθ_n ω/2)/‖θ_n‖.
  -- = (√c - 1)/‖θ_n‖ · √k(Sθ_n ω) + (√k(Sθ_n ω) - 1 - Sθ_n ω/2)/‖θ_n‖.
  -- First term → 0 · √k(0) = 0 · 1 = 0 (√c → 1 and (√c - 1)/‖θ_n‖ → 0).
  -- Second term: by HasDerivAt sqrt_kSigmoid 1/2 0, (√k(x) - 1 - x/2)/x → 0 as x → 0.
  -- Multiply by |Sθ_n ω|/‖θ_n‖ which is bounded by jpn ω.
  -- Together r_n ω → 0.
  --
  -- For L¹ domination: r_n² ≤ 2 · (first part)² + 2 · (second part)²
  -- ≤ 2 · (√2 · |√c - 1|/‖θ_n‖)² + 2 · ((3/2) jpn)²/4 ... hmm let me just bound |r_n|.
  -- We have |r_n| ≤ √2 · |√c - 1|/‖θ_n‖ + (3/2) jpn.
  -- |r_n|² ≤ 2 · (√2 · |√c - 1|/‖θ_n‖)² + 2 · ((3/2) jpn)²
  --       = 4 · ((√c - 1)/‖θ_n‖)² + (9/2) · jpn².
  -- Domination by a sequence-dependent bound that itself converges.
  --
  -- Cleaner: use the fact that |√c - 1|/‖θ_n‖ → 0 so it's eventually bounded, say
  -- by 1. Then |r_n| ≤ √2 · 1 + (3/2) jpn for n large, in L¹.
  --
  -- Use this domination + DCT.
  have h_sqrt_c_seq := sqrt_normalizer_c_sub_one_div_norm_tendsto_zero_along_seq g_P
    hθ_tendsto hθ_ne
  -- Get eventual bound: |√c - 1|/‖θ_n‖ ≤ 1 for n large.
  have h_sqrt_c_bd : ∀ᶠ n in atTop,
      |Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖ ≤ 1 := by
    have h_abs : Tendsto (fun n =>
        |Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖) atTop (𝓝 0) := by
      have h_eq : ∀ n,
          |Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖ =
          |(Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖| := by
        intro n
        rw [abs_div]
        congr 1
        exact (abs_of_nonneg (norm_nonneg _)).symm
      rw [show (fun n => |Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖) =
        fun n => |(Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖| from
        funext h_eq]
      have := h_sqrt_c_seq.abs
      simpa using this
    rw [Metric.tendsto_atTop] at h_abs
    obtain ⟨N, hN⟩ := h_abs 1 (by norm_num : (0 : ℝ) < 1)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    have h_div_nn : 0 ≤ |Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖ :=
      div_nonneg (abs_nonneg _) (norm_nonneg _)
    have := abs_of_nonneg h_div_nn ▸ h
    linarith
  -- Define the bound function: bound n ω := (√2 + (3/2) · jpn ω)²  ... actually
  -- we'll use bound := 2 · (√2)² + 2 · ((3/2) jpn)² = 4 + (9/2) jpn².
  -- Then r_n² ≤ 4 + (9/2) jpn² eventually.
  -- But this is for n large. We need pointwise bound for ALL n on integrand.
  -- We have |r_n| ≤ √2 · |√c-1|/‖θ_n‖ + (3/2) jpn for all n, ω.
  -- (a + b)² ≤ 2a² + 2b², so r_n² ≤ 2(√2)²·(|√c-1|/‖θ_n‖)² + 2·(9/4)·jpn²
  --                                = 4 · (|√c-1|/‖θ_n‖)² + (9/2) · jpn².
  -- The first term depends on n but is bounded by 4 · 1² = 4 eventually.
  -- Hence eventually r_n² ≤ 4 + (9/2) · jpn², which is in L¹ (constant + L² · L² product).
  -- jpn² ∈ L¹ since jpn ∈ L².
  -- Pointwise convergence: r_n ω → 0 ⇒ r_n² ω → 0.
  --
  -- Use tendsto_integral_of_dominated_convergence with bound = (3/2)² jpn² + 4 (eventually).
  -- We need to restrict to a subsequence or use a stronger DCT variant.
  -- Simpler path: replace r_n by the eventually-bounded version.
  set bnd : Ω → ℝ := fun ω => 4 + (9/2 : ℝ) * (jpn ω)^2
  have h_bnd_int : Integrable bnd P := by
    refine Integrable.add (integrable_const _) ?_
    exact h_jpn_sq_int.const_mul _
  have h_r_meas : ∀ n, Measurable (r n) := by
    intro n
    change Measurable (fun ω => hellinger_residual g_P (θ_n n) ω / ‖θ_n n‖)
    refine Measurable.div_const ?_ _
    change Measurable (fun ω =>
      Real.sqrt (normalizer_c g_P (θ_n n) * kSigmoid (linPerturb g_P (θ_n n) ω)) - 1 -
        (1/2 : ℝ) * linPerturb g_P (θ_n n) ω)
    refine (((measurable_const.mul (continuous_kSigmoid.measurable.comp
      (linPerturb_meas g_P _))).sqrt).sub measurable_const).sub ?_
    exact measurable_const.mul (linPerturb_meas g_P _)
  -- Eventually bound: |r n ω|² ≤ bnd ω.
  have h_eventually_bound : ∀ᶠ n in atTop,
      ∀ᵐ ω ∂P, ‖r n ω ^ 2‖ ≤ bnd ω := by
    filter_upwards [h_sqrt_c_bd] with n h_n
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have hθn_pos : 0 < ‖θ_n n‖ := norm_pos_iff.mpr (hθ_ne n)
    have hθn_ne : ‖θ_n n‖ ≠ 0 := ne_of_gt hθn_pos
    -- |r n ω| ≤ √2 · |√c - 1|/‖θ_n‖ + (3/2) jpn ω.
    have h_bnd_r : |r n ω| ≤
        Real.sqrt 2 * (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖) +
          (3/2 : ℝ) * jpn ω := by
      change |hellinger_residual g_P (θ_n n) ω / ‖θ_n n‖| ≤ _
      rw [abs_div]
      have h_res_bd := abs_hellinger_residual_bound g_P (θ_n n) ω
      have h_div_bd : |hellinger_residual g_P (θ_n n) ω| / |‖θ_n n‖| ≤
          (Real.sqrt 2 * |Real.sqrt (normalizer_c g_P (θ_n n)) - 1| +
            (3/2 : ℝ) * |linPerturb g_P (θ_n n) ω|) / ‖θ_n n‖ := by
        rw [abs_of_pos hθn_pos]
        exact div_le_div_of_nonneg_right h_res_bd hθn_pos.le
      have h_split : (Real.sqrt 2 * |Real.sqrt (normalizer_c g_P (θ_n n)) - 1| +
            (3/2 : ℝ) * |linPerturb g_P (θ_n n) ω|) / ‖θ_n n‖ =
          Real.sqrt 2 * (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖) +
          (3/2 : ℝ) * (|linPerturb g_P (θ_n n) ω| / ‖θ_n n‖) := by
        field_simp
      rw [h_split] at h_div_bd
      -- Now show: (3/2) · |Sθ_n ω| / ‖θ_n‖ ≤ (3/2) · jpn ω.
      have h_lin_bd : |linPerturb g_P (θ_n n) ω| / ‖θ_n n‖ ≤ jpn ω := by
        have h_abs_le := abs_linPerturb_le_jointPointwiseNorm g_P (θ_n n) ω
        rw [div_le_iff₀ hθn_pos, mul_comm]
        exact h_abs_le
      calc |hellinger_residual g_P (θ_n n) ω| / |‖θ_n n‖|
          ≤ Real.sqrt 2 * (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖) +
              (3/2 : ℝ) * (|linPerturb g_P (θ_n n) ω| / ‖θ_n n‖) := h_div_bd
        _ ≤ Real.sqrt 2 * (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖) +
              (3/2 : ℝ) * jpn ω := by
            have h_3_2_nn : (0 : ℝ) ≤ 3/2 := by norm_num
            have := mul_le_mul_of_nonneg_left h_lin_bd h_3_2_nn
            linarith
    -- Use (a + b)² ≤ 2a² + 2b².
    have h_a_nn : 0 ≤ Real.sqrt 2 *
        (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖) := by
      apply mul_nonneg (Real.sqrt_nonneg _)
      exact div_nonneg (abs_nonneg _) (norm_nonneg _)
    have h_b_nn : 0 ≤ (3/2 : ℝ) * jpn ω := by
      apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 3/2)
      exact jointPointwiseNorm_nonneg g_P ω
    have h_apb_nn : 0 ≤ Real.sqrt 2 *
        (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖) +
          (3/2 : ℝ) * jpn ω := by linarith
    have h_sq_bd : (r n ω)^2 ≤ 2 * (Real.sqrt 2 *
        (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖))^2 +
        2 * ((3/2 : ℝ) * jpn ω)^2 := by
      have h_abs_sq_eq : (r n ω)^2 = |r n ω|^2 := by rw [sq_abs]
      rw [h_abs_sq_eq]
      have h_sq : |r n ω| ^ 2 ≤ (Real.sqrt 2 *
          (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖) +
          (3/2 : ℝ) * jpn ω) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h_bnd_r 2
      have h_ab_le : (Real.sqrt 2 *
          (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖) +
          (3/2 : ℝ) * jpn ω) ^ 2 ≤
        2 * (Real.sqrt 2 *
          (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖))^2 +
        2 * ((3/2 : ℝ) * jpn ω)^2 := by
        nlinarith [sq_nonneg (Real.sqrt 2 *
          (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖) -
          (3/2 : ℝ) * jpn ω)]
      linarith [h_sq, h_ab_le]
    -- Now use h_n: |√c-1|/‖θ_n‖ ≤ 1.
    -- 2 · (√2 · (|√c-1|/‖θ_n‖))² = 2 · 2 · (|√c-1|/‖θ_n‖)² ≤ 4 · 1 = 4.
    -- 2 · ((3/2) jpn)² = 2 · (9/4) · jpn² = (9/2) · jpn².
    have h_first_bd : 2 * (Real.sqrt 2 * (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| /
        ‖θ_n n‖))^2 ≤ 4 := by
      have h_sqrt2_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have h_div_nn : 0 ≤ |Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖ :=
        div_nonneg (abs_nonneg _) (norm_nonneg _)
      have h_div_sq_le : (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖)^2 ≤ 1 := by
        have : (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖)^2 ≤ 1^2 :=
          pow_le_pow_left₀ h_div_nn h_n 2
        linarith [this]
      calc 2 * (Real.sqrt 2 * (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖))^2
          = 2 * (Real.sqrt 2)^2 * (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖)^2 := by
              ring
        _ = 4 * (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖)^2 := by
            rw [h_sqrt2_sq]; ring
        _ ≤ 4 * 1 := by
            have h_4_nn : (0 : ℝ) ≤ 4 := by norm_num
            exact mul_le_mul_of_nonneg_left h_div_sq_le h_4_nn
        _ = 4 := by ring
    have h_second_eq : 2 * ((3/2 : ℝ) * jpn ω)^2 = (9/2 : ℝ) * (jpn ω)^2 := by
      ring
    -- Combine.
    change ‖r n ω ^ 2‖ ≤ bnd ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (r n ω)^2 ≤ 4 + (9/2 : ℝ) * (jpn ω)^2
    calc (r n ω)^2 ≤ 2 * (Real.sqrt 2 * (|Real.sqrt (normalizer_c g_P (θ_n n)) - 1| / ‖θ_n n‖))^2 +
              2 * ((3/2 : ℝ) * jpn ω)^2 := h_sq_bd
      _ ≤ 4 + (9/2 : ℝ) * (jpn ω)^2 := by
          rw [h_second_eq] at *
          linarith [h_first_bd]
  -- Pointwise convergence: r n ω → 0 for each ω.
  have h_pt : ∀ ω, Tendsto (fun n => r n ω ^ 2) atTop (𝓝 0) := by
    intro ω
    -- |r n ω| ≤ √2 · |√c - 1|/‖θ_n‖ + (3/2) · |Sθ_n ω|/‖θ_n‖ ... but we want → 0.
    -- Use the decomposition: r n ω = (√c - 1)/‖θ_n‖ · √k(Sθ_n ω) + (√k(Sθ_n ω) - 1 - Sθ_n
    -- ω/2)/‖θ_n‖.
    -- First term → 0 since (√c - 1)/‖θ_n‖ → 0 and √k bounded.
    -- Second term → 0 by HasDerivAt at 0 for √k.
    -- We prove (r n ω)² → 0 by Metric.tendsto.
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    -- Reduce to |r n ω| < √ε.
    have h_sqrt_ε_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    suffices h_r : ∃ N, ∀ n ≥ N, |r n ω| < Real.sqrt ε by
      obtain ⟨N, hN⟩ := h_r
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq, sub_zero]
      have h_abs_sq : |r n ω ^ 2| = (|r n ω|)^2 := by rw [sq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [h_abs_sq]
      have h_lt : |r n ω| < Real.sqrt ε := hN n hn
      have h_abs_nn : 0 ≤ |r n ω| := abs_nonneg _
      calc (|r n ω|)^2 < (Real.sqrt ε)^2 :=
            pow_lt_pow_left₀ h_lt h_abs_nn (by norm_num)
        _ = ε := Real.sq_sqrt hε.le
    -- Now show |r n ω| < √ε eventually.
    -- |r n ω| ≤ √2 · |√c - 1|/‖θ_n‖ + (3/2) · |√k(Sθ_n ω) - 1 - Sθ_n ω/2|/‖θ_n‖ · ?
    -- Actually use the decomposition directly:
    -- r n ω = (√c - 1)/‖θ_n‖ · √k(Sθ_n ω) + (√k(Sθ_n ω) - 1 - Sθ_n ω/2)/‖θ_n‖.
    -- |r n ω| ≤ |√c - 1|/‖θ_n‖ · √k(Sθ_n ω) + |√k(Sθ_n ω) - 1 - Sθ_n ω/2|/‖θ_n‖.
    -- First → 0 (first factor → 0 by sqrt_c_seq, second bounded by √2).
    -- Second: by HasDerivAt of √k at 0 with derivative 1/2.
    --
    -- We split ε/2 + ε/2.
    set δ := Real.sqrt ε / 2 with hδ_def
    have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
    -- Part 1: bound (√c - 1)/‖θ_n‖ · √k(Sθ_n ω) ≤ δ eventually.
    -- |√k(Sθ_n ω)| ≤ √2.
    have h_sqrt_c_seq' := sqrt_normalizer_c_sub_one_div_norm_tendsto_zero_along_seq g_P
      hθ_tendsto hθ_ne
    have h_sqrt_c_eventually : ∀ᶠ n in atTop,
        |(Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖| < δ / (Real.sqrt 2 + 1) := by
      have h_factor_pos : 0 < Real.sqrt 2 + 1 := by
        have := Real.sqrt_nonneg (2 : ℝ); linarith
      have hε_div : 0 < δ / (Real.sqrt 2 + 1) := div_pos hδ_pos h_factor_pos
      rw [Metric.tendsto_atTop] at h_sqrt_c_seq'
      obtain ⟨N, hN⟩ := h_sqrt_c_seq' (δ / (Real.sqrt 2 + 1)) hε_div
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have h := hN n hn
      rwa [Real.dist_eq, sub_zero] at h
    -- Part 2: bound |√k(Sθ_n ω) - 1 - Sθ_n ω/2|/‖θ_n‖ ≤ δ eventually.
    -- Linearize: (√k(Sθ_n ω) - 1 - Sθ_n ω/2)/‖θ_n‖ = ((√k(x) - 1 - x/2)/x) · (Sθ_n ω/‖θ_n‖)
    -- (when Sθ_n ω ≠ 0). First → 0 by HasDerivAt, second bounded by jpn ω.
    have h_jpn_nn : 0 ≤ jpn ω := jointPointwiseNorm_nonneg _ _
    by_cases h_jpn_zero : jpn ω = 0
    · -- jpn = 0 ⇒ linPerturb θ_n ω = 0 always, so the residual reduces.
      -- r n ω = (√c · √k(0) - 1 - 0)/‖θ_n‖ = (√c - 1)/‖θ_n‖.
      -- This → 0.
      have h_lin_zero : ∀ n, linPerturb g_P (θ_n n) ω = 0 := by
        intro n
        have hbnd := abs_linPerturb_le_jointPointwiseNorm g_P (θ_n n) ω
        rw [← hjpn_def] at hbnd
        rw [h_jpn_zero, mul_zero] at hbnd
        have h_abs_nn : 0 ≤ |linPerturb g_P (θ_n n) ω| := abs_nonneg _
        exact abs_eq_zero.mp (le_antisymm hbnd h_abs_nn)
      have h_r_simp : ∀ n, r n ω = (Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖ := by
        intro n
        change hellinger_residual g_P (θ_n n) ω / ‖θ_n n‖ = _
        unfold hellinger_residual
        rw [h_lin_zero, kSigmoid_zero, mul_one]
        have h_zero_half : (1/2 : ℝ) * 0 = 0 := by ring
        rw [h_zero_half, sub_zero]
      have h_seq_lim := h_sqrt_c_seq'
      rw [Metric.tendsto_atTop] at h_seq_lim
      obtain ⟨N, hN⟩ := h_seq_lim (Real.sqrt ε) h_sqrt_ε_pos
      refine ⟨N, fun n hn => ?_⟩
      rw [h_r_simp n]
      have := hN n hn
      rw [Real.dist_eq, sub_zero] at this
      exact this
    -- jpn ω > 0. Pointwise:
    have h_jpn_pos : 0 < jpn ω := lt_of_le_of_ne h_jpn_nn (Ne.symm h_jpn_zero)
    -- We need eventually: |√k(Sθ_n ω) - 1 - Sθ_n ω/2|/‖θ_n‖ < δ.
    -- Reduce to little-o of √k - 1 - x/2 at 0.
    have h_sqrt_k_deriv : (fun x => Real.sqrt (kSigmoid x) - 1 - (1/2 : ℝ) * x) =o[𝓝 0]
        fun x => x := by
      have h_o := hasDerivAt_sqrt_kSigmoid_zero.isLittleO
      -- HasDerivAt gives √k(x) - √k(0) - (1/2)·(x - 0) = o(x - 0).
      have h_eq : (fun x : ℝ => Real.sqrt (kSigmoid x) - 1 - (1/2 : ℝ) * x) =
          fun x' : ℝ => Real.sqrt (kSigmoid x') - 1 - x' * 2⁻¹ := by
        funext x; ring
      rw [h_eq]
      simpa [kSigmoid_zero, Real.sqrt_one, sub_zero] using h_o
    have hδ_jpn_pos : 0 < δ / (jpn ω + 1) := by
      have h_jpn_p1_pos : 0 < jpn ω + 1 := by linarith
      exact div_pos hδ_pos h_jpn_p1_pos
    -- Get δ' from little-o: ∀ |x| < δ', |√k(x) - 1 - x/2| ≤ (δ/(jpn+1)) · |x|.
    obtain ⟨δ', hδ'_pos, hδ'⟩ :=
      Metric.eventually_nhds_iff.mp (h_sqrt_k_deriv.bound hδ_jpn_pos)
    -- Get N₁ so Sθ_n ω stays within δ' for n ≥ N₁ (linPerturb is continuous → 0).
    have h_lin_tendsto : Tendsto (fun n => linPerturb g_P (θ_n n) ω) atTop (𝓝 0) := by
      have h_cont : Continuous (fun θ : EuclideanSpace ℝ (Fin m) =>
          linPerturb g_P θ ω) := by
        unfold linPerturb
        refine continuous_finset_sum _ (fun i _ => ?_)
        have h_proj : Continuous (fun θ : EuclideanSpace ℝ (Fin m) => θ i) :=
          (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
        exact h_proj.mul continuous_const
      have h_eval := (h_cont.tendsto _).comp hθ_tendsto
      have h_lin0 : linPerturb g_P (0 : EuclideanSpace ℝ (Fin m)) ω = 0 := by
        unfold linPerturb; simp [zero_mul]
      rw [h_lin0] at h_eval
      exact h_eval
    rw [Metric.tendsto_atTop] at h_lin_tendsto
    obtain ⟨N₁, hN₁⟩ := h_lin_tendsto δ' hδ'_pos
    -- Get N₂ from h_sqrt_c_eventually.
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp h_sqrt_c_eventually
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have h_n1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
    have h_n2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
    have h_lin_lt : |linPerturb g_P (θ_n n) ω| < δ' := by
      have := hN₁ n h_n1
      rwa [Real.dist_eq, sub_zero] at this
    have h_in_ball : linPerturb g_P (θ_n n) ω ∈ Metric.ball (0 : ℝ) δ' :=
      Metric.mem_ball.mpr (by rw [Real.dist_eq, sub_zero]; exact h_lin_lt)
    have h_taylor_bd := hδ' (Metric.mem_ball.mp h_in_ball)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h_taylor_bd
    -- Now construct |r n ω| < √ε = 2δ.
    -- r n ω = (√c · √k(Sθ_n ω) - √k(Sθ_n ω))/‖θ_n‖ + (√k(Sθ_n ω) - 1 - Sθ_n ω/2)/‖θ_n‖.
    -- = (√c - 1)/‖θ_n‖ · √k(Sθ_n ω) + (√k(Sθ_n ω) - 1 - Sθ_n ω/2)/‖θ_n‖.
    have hθn_pos : 0 < ‖θ_n n‖ := norm_pos_iff.mpr (hθ_ne n)
    have hθn_ne : ‖θ_n n‖ ≠ 0 := ne_of_gt hθn_pos
    have h_decomp_r : r n ω = (Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖ *
        Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω)) +
        (Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω)) - 1 -
          (1/2 : ℝ) * linPerturb g_P (θ_n n) ω) / ‖θ_n n‖ := by
      change hellinger_residual g_P (θ_n n) ω / ‖θ_n n‖ = _
      unfold hellinger_residual
      have h_sqrt_split : Real.sqrt (normalizer_c g_P (θ_n n) *
          kSigmoid (linPerturb g_P (θ_n n) ω)) =
          Real.sqrt (normalizer_c g_P (θ_n n)) *
          Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω)) :=
        Real.sqrt_mul (normalizer_c_nonneg _ _) _
      rw [h_sqrt_split]
      field_simp
      ring
    rw [h_decomp_r]
    -- Bound each piece.
    have h_part1 : |(Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖ *
        Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω))| ≤
        |(Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖| * Real.sqrt 2 := by
      rw [abs_mul]
      have h_sqrt_k_le : |Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω))| ≤ Real.sqrt 2 := by
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (kSigmoid_le_two _)
      have h_div_nn : 0 ≤ |(Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖| := abs_nonneg _
      exact mul_le_mul_of_nonneg_left h_sqrt_k_le h_div_nn
    have h_part1_bd := hN₂ n h_n2
    -- h_part1_bd : |(√c - 1)/‖θ_n‖| < δ / (√2 + 1).
    have h_sqrt2_p1_pos : 0 < Real.sqrt 2 + 1 := by
      have := Real.sqrt_nonneg (2 : ℝ); linarith
    have h_part1_final : |(Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖ *
        Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω))| < δ := by
      have h_sqrt2_pos : 0 < Real.sqrt 2 :=
        Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
      calc |(Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖ *
            Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω))|
          ≤ |(Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖| * Real.sqrt 2 := h_part1
        _ < (δ / (Real.sqrt 2 + 1)) * Real.sqrt 2 :=
            mul_lt_mul_of_pos_right h_part1_bd h_sqrt2_pos
        _ ≤ δ := by
            rw [div_mul_eq_mul_div, div_le_iff₀ h_sqrt2_p1_pos]
            nlinarith [hδ_pos.le, Real.sqrt_nonneg (2 : ℝ)]
    -- Part 2:
    have h_part2 : |(Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω)) - 1 -
        (1/2 : ℝ) * linPerturb g_P (θ_n n) ω) / ‖θ_n n‖| < δ := by
      rw [abs_div, abs_of_pos hθn_pos, div_lt_iff₀ hθn_pos]
      -- |√k(Sθ_n) - 1 - Sθ_n/2| ≤ (δ/(jpn+1)) · |Sθ_n|.
      -- And |Sθ_n| ≤ ‖θ_n‖ · jpn ω. So ≤ (δ/(jpn+1)) · ‖θ_n‖ · jpn ω < δ · ‖θ_n‖.
      have h_lin_bd := abs_linPerturb_le_jointPointwiseNorm g_P (θ_n n) ω
      change |Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω)) - 1 -
          (1/2 : ℝ) * linPerturb g_P (θ_n n) ω| < δ * ‖θ_n n‖
      have h_p2_taylor : |Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω)) - 1 -
          (1/2 : ℝ) * linPerturb g_P (θ_n n) ω| ≤
          (δ / (jpn ω + 1)) * |linPerturb g_P (θ_n n) ω| := h_taylor_bd
      have h_jpn_p1_pos : 0 < jpn ω + 1 := by linarith
      calc |Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω)) - 1 -
            (1/2 : ℝ) * linPerturb g_P (θ_n n) ω|
          ≤ (δ / (jpn ω + 1)) * |linPerturb g_P (θ_n n) ω| := h_p2_taylor
        _ ≤ (δ / (jpn ω + 1)) * (‖θ_n n‖ * jpn ω) :=
            mul_le_mul_of_nonneg_left h_lin_bd hδ_jpn_pos.le
        _ < δ * ‖θ_n n‖ := by
            rw [div_mul_eq_mul_div]
            rw [div_mul_eq_mul_div]
            rw [div_lt_iff₀ h_jpn_p1_pos]
            nlinarith [hδ_pos, h_jpn_pos, hθn_pos]
    -- Combine.
    have h_combine : |(Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖ *
        Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω)) +
        (Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω)) - 1 -
          (1/2 : ℝ) * linPerturb g_P (θ_n n) ω) / ‖θ_n n‖| <
        δ + δ := by
      have h_tri := abs_add_le ((Real.sqrt (normalizer_c g_P (θ_n n)) - 1) / ‖θ_n n‖ *
          Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω)))
        ((Real.sqrt (kSigmoid (linPerturb g_P (θ_n n) ω)) - 1 -
          (1/2 : ℝ) * linPerturb g_P (θ_n n) ω) / ‖θ_n n‖)
      linarith [h_part1_final, h_part2, h_tri]
    have h_2δ_eq : δ + δ = Real.sqrt ε := by rw [hδ_def]; ring
    rw [h_2δ_eq] at h_combine
    exact h_combine
  -- DCT (eventually bounded).
  have h_dct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (F := fun n ω => r n ω ^ 2) (f := fun _ => (0 : ℝ))
    (bound := bnd)
    (Filter.Eventually.of_forall
      (fun n => ((h_r_meas n).pow_const 2).aestronglyMeasurable))
    h_eventually_bound h_bnd_int
    (Filter.Eventually.of_forall h_pt)
  -- Now convert to (∫ residual²)/‖θ_n‖² → 0.
  have h_int_eq : ∀ n,
      ∫ ω, r n ω ^ 2 ∂P =
        (∫ ω, hellinger_residual g_P (θ_n n) ω ^ 2 ∂P) / ‖θ_n n‖ ^ 2 := by
    intro n
    have hθn_pos : 0 < ‖θ_n n‖ := norm_pos_iff.mpr (hθ_ne n)
    have hθn_ne : ‖θ_n n‖ ≠ 0 := ne_of_gt hθn_pos
    change ∫ ω, (hellinger_residual g_P (θ_n n) ω / ‖θ_n n‖) ^ 2 ∂P = _
    have h_pt_eq : ∀ ω, (hellinger_residual g_P (θ_n n) ω / ‖θ_n n‖) ^ 2 =
        (hellinger_residual g_P (θ_n n) ω) ^ 2 / ‖θ_n n‖ ^ 2 := by
      intro ω; rw [div_pow]
    simp_rw [h_pt_eq]
    rw [integral_div]
  have h_simp : ∫ _ω : Ω, (0 : ℝ) ∂P = 0 := by simp
  rw [h_simp] at h_dct
  refine h_dct.congr ?_
  intro n
  exact h_int_eq n

/-- Filter form (`isLittleO`): the L²-integrated Hellinger residual is
`o(‖θ‖²)` as `θ → 0`. This is the rate condition of DQM. -/
theorem hellinger_residual_sq_integral_isLittleO :
    (fun θ : EuclideanSpace ℝ (Fin m) =>
      ∫ ω, (hellinger_residual g_P θ ω) ^ 2 ∂P) =o[𝓝 0]
        (fun θ => ‖θ‖ ^ 2) := by
  classical
  -- Use sequential characterization (𝓝 0 is countably generated).
  rw [Asymptotics.isLittleO_iff]
  intro c hc_pos
  -- Want: ∀ᶠ θ in 𝓝 0, ‖∫ residual² dP‖ ≤ c · ‖‖θ‖²‖.
  -- ‖‖θ‖²‖ = ‖θ‖². ‖∫ residual²‖ = ∫ residual² (nonneg).
  -- Need: ∫ residual² ≤ c · ‖θ‖² eventually.
  -- Equivalent: ∫ residual² / ‖θ‖² ≤ c eventually (when ‖θ‖² > 0).
  -- Use sequential characterization.
  by_contra h
  push Not at h
  -- Negation: there exists a sequence θ_n → 0 (residual / ‖θ_n‖² > c).
  -- Specifically: not eventually ≤ ⇒ frequently > c.
  -- Find a sequence of "bad" θ in any neighborhood. Use Metric.nhds_basis.
  -- Sequential reduction:
  have h_seq : ∀ (k : ℕ), ∃ θ_k : EuclideanSpace ℝ (Fin m),
      θ_k ≠ 0 ∧ ‖θ_k‖ < 1/(k+1) ∧
      c * ‖‖θ_k‖ ^ 2‖ < ‖∫ ω, (hellinger_residual g_P θ_k ω) ^ 2 ∂P‖ := by
    intro k
    -- Combine: in Metric.ball 0 (1/(k+1)) ∩ {θ ≠ 0}, the bad condition holds frequently.
    have h_inv_pos : 0 < 1/((k : ℝ)+1) := by positivity
    have h_ball : Set.Ioo (-(1/((k : ℝ)+1))) (1/((k : ℝ)+1)) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) h_inv_pos
    -- The set {θ : ‖θ‖ < 1/(k+1)} is a neighborhood of 0.
    have h_nbhd : {θ : EuclideanSpace ℝ (Fin m) | ‖θ‖ < 1/((k : ℝ)+1)} ∈ 𝓝 (0 : EuclideanSpace ℝ
        (Fin m)) := by
      have h_cont : Continuous (fun θ : EuclideanSpace ℝ (Fin m) => ‖θ‖) := continuous_norm
      have h_norm_tendsto : Tendsto (fun θ : EuclideanSpace ℝ (Fin m) => ‖θ‖)
          (𝓝 0) (𝓝 0) := by
        have := h_cont.tendsto (0 : EuclideanSpace ℝ (Fin m))
        simpa [norm_zero] using this
      have h_lt : Set.Iio (1/((k : ℝ)+1)) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds h_inv_pos
      exact h_norm_tendsto h_lt
    -- Frequently in 𝓝 0: bad condition.
    have h_freq : ∃ᶠ θ in 𝓝 (0 : EuclideanSpace ℝ (Fin m)),
        c * ‖‖θ‖ ^ 2‖ < ‖∫ ω, (hellinger_residual g_P θ ω) ^ 2 ∂P‖ := h
    -- Combine frequently with neighborhood: ∃ θ in nbhd satisfying bad.
    rw [Filter.frequently_iff] at h_freq
    obtain ⟨θ_k', hθ_k'_nbhd, h_θ_k'⟩ := h_freq h_nbhd
    by_cases hθ_k'_zero : θ_k' = 0
    · -- If θ_k' = 0, then the residual is 0 (at θ = 0).
      rw [hθ_k'_zero] at h_θ_k'
      have h_res_zero : ∀ ω, hellinger_residual g_P (0 : EuclideanSpace ℝ (Fin m)) ω = 0 := by
        intro ω
        unfold hellinger_residual
        rw [normalizer_c_at_zero, one_mul]
        have h_lin : linPerturb g_P (0 : EuclideanSpace ℝ (Fin m)) ω = 0 := by
          unfold linPerturb; simp [zero_mul]
        rw [h_lin, kSigmoid_zero, Real.sqrt_one]
        ring
      have h_int_zero : ∫ ω, hellinger_residual g_P (0 : EuclideanSpace ℝ (Fin m)) ω ^ 2 ∂P = 0 :=
          by
        rw [show (fun ω => hellinger_residual g_P (0 : EuclideanSpace ℝ (Fin m)) ω ^ 2) =
            fun _ => (0 : ℝ) from funext (fun ω => by rw [h_res_zero ω]; ring)]
        simp
      rw [norm_zero] at h_θ_k'
      simp [h_int_zero] at h_θ_k'
    · refine ⟨θ_k', hθ_k'_zero, hθ_k'_nbhd, h_θ_k'⟩
  -- Construct the sequence.
  choose θ_seq hθ_seq_ne hθ_seq_small hθ_seq_bad using h_seq
  -- θ_seq k → 0 since ‖θ_seq k‖ < 1/(k+1) → 0.
  have hθ_seq_tendsto : Tendsto θ_seq atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 1/((N : ℝ)+1) < ε := by
      have h_arch := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h_arch
      exact ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have hN_nn : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    have hn_nn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hNp1_pos : 0 < (N : ℝ) + 1 := by linarith
    have h1 : 1/((n : ℝ)+1) ≤ 1/((N : ℝ)+1) := by
      apply one_div_le_one_div_of_le hNp1_pos
      have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h2 : ‖θ_seq n‖ < 1/((n : ℝ)+1) := hθ_seq_small n
    have h_ε_pos := hε
    have : dist ‖θ_seq n‖ 0 = ‖θ_seq n‖ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    rw [this]
    linarith
  -- Apply sequential lemma: ∫ residual² / ‖θ_seq n‖² → 0.
  have h_lim := hellinger_residual_sq_div_norm_sq_tendsto_zero_along_seq g_P
    hθ_seq_tendsto hθ_seq_ne
  -- But hθ_seq_bad says: c · ‖θ_seq n‖² < ∫ residual² for all n.
  -- So ∫ residual² / ‖θ_seq n‖² > c, contradicting → 0.
  rw [Metric.tendsto_atTop] at h_lim
  obtain ⟨N, hN⟩ := h_lim c hc_pos
  have h_bad := hθ_seq_bad N
  have h_lim_N := hN N (le_refl _)
  rw [Real.dist_eq, sub_zero] at h_lim_N
  have hθN_pos : 0 < ‖θ_seq N‖ := norm_pos_iff.mpr (hθ_seq_ne N)
  have hθN_sq_pos : 0 < ‖θ_seq N‖ ^ 2 := by positivity
  -- Normalize bad: c · ‖‖θ‖²‖ = c · ‖θ‖².
  have h_norm_sq : ‖‖θ_seq N‖ ^ 2‖ = ‖θ_seq N‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [h_norm_sq] at h_bad
  -- And ‖∫ res²‖ = ∫ res² since nonneg.
  have h_int_nn : 0 ≤ ∫ ω, (hellinger_residual g_P (θ_seq N) ω) ^ 2 ∂P :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg h_int_nn] at h_bad
  -- h_bad : c · ‖θ_seq N‖² < ∫ res²
  -- h_lim_N : |∫ res² / ‖θ_seq N‖²| < c
  -- ⟹ ∫ res² < c · ‖θ_seq N‖² (contradiction).
  have h_div_nn : 0 ≤ (∫ ω, (hellinger_residual g_P (θ_seq N) ω) ^ 2 ∂P) /
      ‖θ_seq N‖ ^ 2 := div_nonneg h_int_nn hθN_sq_pos.le
  rw [abs_of_nonneg h_div_nn] at h_lim_N
  have h_lt : ∫ ω, (hellinger_residual g_P (θ_seq N) ω) ^ 2 ∂P < c * ‖θ_seq N‖ ^ 2 := by
    rw [div_lt_iff₀ hθN_sq_pos] at h_lim_N
    linarith
  linarith [h_lt, h_bad]

/-! ### Assemble DQM at θ=0 -/

/-- Connection: the DQM-style residual at `θ = 0` with `θ + h = h`
unfolds to our `hellinger_residual`. -/
private lemma dqm_residual_eq_hellinger_residual
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    (unboundedParamSubmodel g_P h_orth).sqrtDensity (0 + h) ω
      - (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω
      - (1/2 : ℝ) * @inner ℝ _ _ h (g_P_total g_P ω)
          * (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω
    = hellinger_residual g_P h ω := by
  unfold ParametricFamily.sqrtDensity hellinger_residual
  -- sqrtDensity (0 + h) ω = √(density (0+h) ω) = √(density h ω) = √(c h · k(linPerturb h ω)).
  -- sqrtDensity 0 ω = √(density 0 ω) = √1 = 1.
  rw [zero_add]
  rw [unboundedParamSubmodel_density_zero_eq_one g_P h_orth ω, Real.sqrt_one,
      mul_one]
  rw [inner_g_P_total_eq_linPerturb]
  -- density h ω = unboundedSubmodelDensity g_P h ω = normalizer_c g_P h *
  --   normalizer_c_integrand g_P h ω = normalizer_c g_P h * kSigmoid (linPerturb g_P h ω)
  rfl

/-- Differentiability in quadratic mean of the sigmoid submodel at `θ = 0`
with score `g_P_total g_P`.

The Hellinger residual is `o(‖h‖²)` in `L²(P)`-norm-squared as `h → 0`,
by the L²-DCT argument (`hellinger_residual_sq_integral_isLittleO`). -/
theorem unboundedParamSubmodel_DQM
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    DifferentiableQuadraticMean
      (unboundedParamSubmodel g_P h_orth) P 0 (g_P_total g_P) := by
  refine ⟨?_, ?_⟩
  · -- mem: the residual is eventually in MemLp 2 P.
    -- We show it's always in MemLp 2 P (bounded by sum of L² functions).
    refine Filter.Eventually.of_forall (fun h => ?_)
    -- The residual = hellinger_residual g_P h ω (up to a.e.).
    have h_eq : (fun ω => (unboundedParamSubmodel g_P h_orth).sqrtDensity (0 + h) ω
              - (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω
              - (1/2 : ℝ) * @inner ℝ _ _ h (g_P_total g_P ω)
                  * (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω)
        = fun ω => hellinger_residual g_P h ω := by
      funext ω
      exact dqm_residual_eq_hellinger_residual g_P h_orth h ω
    rw [h_eq]
    -- |hellinger_residual h ω| ≤ √2 · |√c - 1| + (3/2) · |Sθ ω|.
    -- The first term is a constant; the second is bounded by (3/2) · ‖θ‖ · jpn ω.
    -- Both contributions are in L²(P).
    have h_bd_const : ∀ ω, |hellinger_residual g_P h ω| ≤
        Real.sqrt 2 * |Real.sqrt (normalizer_c g_P h) - 1| +
          (3/2 : ℝ) * |linPerturb g_P h ω| :=
      fun ω => abs_hellinger_residual_bound g_P h ω
    -- Build memLp of the dominating function.
    have h_const_memLp : MemLp (fun _ : Ω => Real.sqrt 2 *
        |Real.sqrt (normalizer_c g_P h) - 1|) 2 P :=
      memLp_const _
    have h_lin_memLp : MemLp (linPerturb g_P h) 2 P := by
      -- linPerturb = ∑ i, h i · gMk g_P i. Each component in L².
      classical
      unfold linPerturb
      refine memLp_finset_sum _ (fun i _ => ?_)
      have h_int : MemLp ((g_P i : Lp ℝ 2 P) : Ω → ℝ) 2 P := Lp.memLp _
      have h_mk : MemLp (gMk g_P i) 2 P :=
        MeasureTheory.MemLp.ae_eq (gMk_ae_eq g_P i).symm h_int
      exact h_mk.const_mul _
    have h_abs_lin_memLp : MemLp (fun ω => |linPerturb g_P h ω|) 2 P :=
      h_lin_memLp.abs
    have h_dom_memLp : MemLp (fun ω => Real.sqrt 2 *
        |Real.sqrt (normalizer_c g_P h) - 1| + (3/2 : ℝ) *
        |linPerturb g_P h ω|) 2 P :=
      h_const_memLp.add (h_abs_lin_memLp.const_mul _)
    -- hellinger_residual is measurable.
    have h_res_meas : Measurable (fun ω => hellinger_residual g_P h ω) := by
      unfold hellinger_residual
      refine (((measurable_const.mul (continuous_kSigmoid.measurable.comp
        (linPerturb_meas g_P h))).sqrt).sub measurable_const).sub ?_
      exact measurable_const.mul (linPerturb_meas g_P h)
    refine MemLp.of_le_mul (c := 1) h_dom_memLp h_res_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 2 *
          |Real.sqrt (normalizer_c g_P h) - 1| +
            (3/2 : ℝ) * |linPerturb g_P h ω|)]
    exact h_bd_const ω
  · -- isLittleO
    have h_lo := hellinger_residual_sq_integral_isLittleO g_P
    -- Need to congr through dqm_residual_eq_hellinger_residual.
    have h_funext : (fun h : EuclideanSpace ℝ (Fin m) => ∫ ω,
        ((unboundedParamSubmodel g_P h_orth).sqrtDensity (0 + h) ω
          - (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω
          - (1/2 : ℝ) * @inner ℝ _ _ h (g_P_total g_P ω)
              * (unboundedParamSubmodel g_P h_orth).sqrtDensity 0 ω) ^ 2 ∂P)
        = fun h => ∫ ω, (hellinger_residual g_P h ω) ^ 2 ∂P := by
      funext h
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun ω => ?_)
      simp only
      rw [dqm_residual_eq_hellinger_residual g_P h_orth h ω]
    rw [h_funext]
    exact h_lo

/-! ### Fisher information at θ=0 = I_m -/

/-- Fisher information of the sigmoid submodel at `θ = 0` is the identity
bilinear form.

Concretely: for all `u v : EuclideanSpace ℝ (Fin m)`,
`fisherInformation unboundedParamSubmodel P 0 g_P_total u v = ⟪u, v⟫_E`.

Proof: density at 0 is `1`, so the integrand reduces to
`⟪u, g_P_total ω⟫ · ⟪v, g_P_total ω⟫ = linPerturb u ω · linPerturb v ω`,
and `∫ gMk i · gMk j dP = δ_{ij}` by orthonormality. -/
theorem unboundedParamSubmodel_fisher_info
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    ∀ u v : EuclideanSpace ℝ (Fin m),
      fisherInformation (unboundedParamSubmodel g_P h_orth) P 0 (g_P_total g_P) u v
        = @inner ℝ _ _ u v := by
  classical
  intro u v
  unfold fisherInformation
  -- Density at 0 is identically 1.
  have h_dens_eq : ∀ ω, (unboundedParamSubmodel g_P h_orth).density 0 ω = 1 :=
    fun ω => unboundedParamSubmodel_density_zero_eq_one g_P h_orth ω
  have h_integrand_eq : ∀ ω,
      (@inner ℝ _ _ u (g_P_total g_P ω) * @inner ℝ _ _ v (g_P_total g_P ω))
        * (unboundedParamSubmodel g_P h_orth).density 0 ω
      = linPerturb g_P u ω * linPerturb g_P v ω := by
    intro ω
    rw [h_dens_eq ω, mul_one,
        inner_g_P_total_eq_linPerturb,
        inner_g_P_total_eq_linPerturb]
  rw [integral_congr_ae (Filter.Eventually.of_forall h_integrand_eq)]
  -- Expand product of sums. linPerturb u · linPerturb v = ∑ᵢⱼ u i · v j · gMk i · gMk j.
  have h_expand : ∀ ω, linPerturb g_P u ω * linPerturb g_P v ω
        = ∑ i, ∑ j, (u i * v j) * (gMk g_P i ω * gMk g_P j ω) := by
    intro ω
    unfold linPerturb
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_expand)]
  -- Swap integral with double sum.
  rw [integral_finset_sum]
  · -- ∫ ∑ⱼ (u i · v j) · (gMk i · gMk j) ∂P = ∑ⱼ (u i · v j) · ∫ gMk i · gMk j ∂P
    have h_inner_step : ∀ i,
        ∫ ω, ∑ j, (u i * v j) * (gMk g_P i ω * gMk g_P j ω) ∂P
        = ∑ j, (u i * v j) *
            ∫ ω, gMk g_P i ω * gMk g_P j ω ∂P := by
      intro i
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl; intro j _
        rw [integral_const_mul]
      · intro j _
        have h_int_lp : Integrable (fun ω => ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω
                                            * ((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω) P :=
          (Lp.memLp (g_P i : Lp ℝ 2 P)).integrable_mul (Lp.memLp (g_P j : Lp ℝ 2 P))
        have h_int_mk : Integrable (fun ω => gMk g_P i ω * gMk g_P j ω) P := by
          refine h_int_lp.congr ?_
          filter_upwards [gMk_ae_eq g_P i, gMk_ae_eq g_P j] with ω hi hj
          rw [hi, hj]
        exact h_int_mk.const_mul _
    rw [Finset.sum_congr rfl (fun i _ => h_inner_step i)]
    -- Now: ∑ᵢ ∑ⱼ (u i · v j) · δ_{ij} = ∑ᵢ u i · v i = ⟪u, v⟫_E.
    have h_int_gMk : ∀ i j : Fin m,
        ∫ ω, gMk g_P i ω * gMk g_P j ω ∂P = if i = j then 1 else 0 := by
      intro i j
      -- ⟨g_P i, g_P j⟩_Lp = ∫ (g_P i)·(g_P j) dP = δ_{ij} by orthonormality.
      have h_inner : @inner ℝ _ _ (g_P i : Lp ℝ 2 P) (g_P j : Lp ℝ 2 P)
            = if i = j then (1 : ℝ) else 0 := by
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl]
          have h_norm : ‖(g_P i : Lp ℝ 2 P)‖ = 1 := h_orth.norm_eq_one i
          rw [real_inner_self_eq_norm_mul_norm, h_norm]; norm_num
        · rw [if_neg hij]
          exact h_orth.inner_eq_zero hij
      rw [MeasureTheory.L2.inner_def] at h_inner
      have h_int_eq :
          ∫ ω, @inner ℝ _ _ (((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω)
                           (((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω) ∂P
            = ∫ ω, ((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω
                    * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω ∂P := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall (fun ω => ?_)
        rfl
      rw [h_int_eq] at h_inner
      have h_comm : ∫ ω, ((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω
                    * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω ∂P
                  = ∫ ω, ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω
                    * ((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω ∂P := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall (fun ω => mul_comm _ _)
      rw [h_comm] at h_inner
      have h_aei : gMk g_P i =ᵐ[P] ((g_P i : Lp ℝ 2 P) : Ω → ℝ) := gMk_ae_eq g_P i
      have h_aej : gMk g_P j =ᵐ[P] ((g_P j : Lp ℝ 2 P) : Ω → ℝ) := gMk_ae_eq g_P j
      have h_int_bridge :
          ∫ ω, gMk g_P i ω * gMk g_P j ω ∂P
            = ∫ ω, ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω
                    * ((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω ∂P := by
        apply integral_congr_ae
        filter_upwards [h_aei, h_aej] with ω hi hj
        rw [hi, hj]
      rw [h_int_bridge]
      exact h_inner
    have h_sum_eq : ∀ i,
        ∑ j, (u i * v j) * ∫ ω, gMk g_P i ω * gMk g_P j ω ∂P
        = u i * v i := by
      intro i
      have h_each : ∀ j, (u i * v j)
            * ∫ ω, gMk g_P i ω * gMk g_P j ω ∂P
            = if i = j then u i * v i else 0 := by
        intro j
        rw [h_int_gMk i j]
        by_cases hij : i = j
        · subst hij; simp
        · simp [if_neg hij]
      rw [Finset.sum_congr rfl (fun j _ => h_each j)]
      rw [Finset.sum_ite_eq_of_mem Finset.univ i (fun _ => u i * v i)
            (Finset.mem_univ i)]
    rw [Finset.sum_congr rfl (fun i _ => h_sum_eq i)]
    rw [show (@inner ℝ _ _ u v) = ∑ i, u i * v i by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change @inner ℝ _ _ (u i) (v i) = u i * v i
      change v i * u i = u i * v i
      ring]
  · intro i _
    refine integrable_finset_sum _ (fun j _ => ?_)
    have h_int_lp : Integrable (fun ω => ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω
                                        * ((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω) P :=
      (Lp.memLp (g_P i : Lp ℝ 2 P)).integrable_mul (Lp.memLp (g_P j : Lp ℝ 2 P))
    have h_int_mk : Integrable (fun ω => gMk g_P i ω * gMk g_P j ω) P := by
      refine h_int_lp.congr ?_
      filter_upwards [gMk_ae_eq g_P i, gMk_ae_eq g_P j] with ω hi hj
      rw [hi, hj]
    exact h_int_mk.const_mul _

end S2_DQM

end AsymptoticStatistics.ParametricFamily
