module
public import StatLean.AsymptoticStatistics.ParametricFamily.SubmodelFromScores
public import StatLean.AsymptoticStatistics.DQM.Defs
public import StatLean.AsymptoticStatistics.DQM.Properties
public import StatLean.AsymptoticStatistics.ParametricFamily.FisherInformation
public import StatLean.AsymptoticStatistics.Core.MassMethod
public import StatLean.AsymptoticStatistics.ForMathlib.L2

@[expose] public section

/-!
Differentiability-in-quadratic-mean (DQM), Fisher information, and mutual
absolute continuity for the multi-dim parametric submodel `paramSubmodel`
constructed in `Parametric/SubmodelFromScores.lean`.

These results supply the analytic submodel ingredients used by finite-dimensional
lower-bound arguments.

## Contents

* `g_P_total` — the multi-dim score `ω ↦ (gMk g_P i ω)ᵢ : EuclideanSpace ℝ (Fin m)`.
* `paramSubmodel_DQM` — DQM at `θ = 0` with score `g_P_total`. The Hellinger
  residual `√(p_θ) - 1 - ½⟨θ, g_P_total⟩` integrates to `o(‖θ‖²)` via the
  Taylor inequality `|√(1+u) - 1 - u/2| ≤ u²/2` for `0 ≤ 1+u`, lifted from the
  1-D template in `Core/MassMethod.boundedDensityPath`.
* `paramSubmodel_fisher_info` — Fisher info at `θ = 0` is the identity bilinear
  form `(u, v) ↦ ⟪u, v⟫`, by orthonormality of the `g_P i`.
* `paramSubmodel_h_same_support` — the density at `θ = 0` is positive
  everywhere; for perturbations within `truncRadius` it is positive a.e.;
  outside the radius the density is identically `1`.

References:
* van der Vaart §7.2 (DQM), §25.5 (parametric submodels through scores).
* `ref/mass/mass.tex` Lemma 1 (1-D analytic core).
-/

open MeasureTheory Filter Topology Asymptotics
open scoped InnerProductSpace ENNReal BigOperators

namespace AsymptoticStatistics.ParametricFamily

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.MassMethod

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## The multi-dim score function -/

/-- The multi-dim score: `g_P_total ω = (gMk g_P i ω)ᵢ : EuclideanSpace ℝ (Fin m)`,
built from the strongly-measurable representatives of the `g_P i`.

We construct it via `WithLp.toLp 2` to land in `EuclideanSpace ℝ (Fin m)`. -/
noncomputable def g_P_total {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)) :
    Ω → EuclideanSpace ℝ (Fin m) :=
  fun ω => WithLp.toLp 2 (fun i : Fin m => gMk g_P i ω)

/-- Componentwise: `(g_P_total g_P ω).ofLp i = gMk g_P i ω`. -/
@[simp] lemma g_P_total_ofLp {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (ω : Ω) (i : Fin m) :
    WithLp.ofLp (g_P_total g_P ω) i = gMk g_P i ω := rfl

/-- The inner product `⟪θ, g_P_total ω⟫_E` equals `linPerturb g_P θ ω`. -/
lemma inner_g_P_total_eq_linPerturb {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    @inner ℝ _ _ θ (g_P_total g_P ω) = linPerturb g_P θ ω := by
  classical
  -- ⟪θ, x⟫ = ∑ i, ⟪θ i, x i⟫ = ∑ i, x i * θ i = ∑ i, θ i * gMk i ω
  rw [PiLp.inner_apply]
  unfold linPerturb
  apply Finset.sum_congr rfl
  intro i _
  -- Goal: ⟪θ i, g_P_total g_P ω i⟫_ℝ = θ i * gMk g_P i ω
  -- where g_P_total g_P ω i = gMk g_P i ω (definitionally), and inner is reversed.
  change @inner ℝ _ _ (θ i) (gMk g_P i ω) = θ i * gMk g_P i ω
  change gMk g_P i ω * θ i = θ i * gMk g_P i ω
  ring

/-! ## Pointwise Taylor bound for the Hellinger residual

`|√(1+u) - 1 - u/2| ≤ u²/2` whenever `0 ≤ 1+u`. Lifted from the inline
helper inside `boundedDensityPath.qmd_limit`. -/

private lemma sqrt_one_add_residual_bound {u : ℝ} (h_nn : 0 ≤ 1 + u) :
    |Real.sqrt (1 + u) - 1 - u / 2| ≤ u ^ 2 / 2 := by
  set s := Real.sqrt (1 + u) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s * s = 1 + u := Real.mul_self_sqrt h_nn
  have h_lhs_eq : s - 1 - u / 2 = -((s - 1) ^ 2) / 2 := by
    have h_u : u = s * s - 1 := by linarith [hs_sq]
    nlinarith [h_u, sq_nonneg (s - 1)]
  rw [h_lhs_eq, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (sq_nonneg _)]
  have h_step : (s - 1) ^ 2 ≤ u ^ 2 := by
    have h_u_sq : u ^ 2 = (s - 1) ^ 2 * (s + 1) ^ 2 := by
      have h_u : u = s * s - 1 := by linarith [hs_sq]
      have hsq_factor : (s * s - 1) = (s - 1) * (s + 1) := by ring
      nlinarith [h_u, hsq_factor, sq_nonneg ((s - 1) * (s + 1))]
    rw [h_u_sq]
    have h_splus_one : (1 : ℝ) ≤ (s + 1) ^ 2 := by nlinarith [hs_nonneg]
    have h_lhs_nn : 0 ≤ (s - 1) ^ 2 := sq_nonneg _
    nlinarith [h_lhs_nn, h_splus_one]
  linarith [h_step]

/-! ## DQM theorem -/

section DQM

variable {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
variable (hg : IsBoundedMixtureScores g_P)
variable (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))

/-- For `‖θ‖ < truncRadius`, the Hellinger residual at `θ = 0`
`√(p_θ) - 1 - ½⟨θ, g_P_total⟩` agrees a.e. with
`√(1 + linPerturb θ) - 1 - ½ linPerturb θ`. -/
private lemma hellinger_residual_ae_eq
    (θ : EuclideanSpace ℝ (Fin m))
    (hθ : ‖θ‖ < truncRadius g_P hg) :
    (fun ω => (paramSubmodel g_P hg h_orth).sqrtDensity (0 + θ) ω
              - (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω
              - (1/2 : ℝ) * @inner ℝ _ _ θ (g_P_total g_P ω)
                  * (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω)
    =ᵐ[P]
    (fun ω => Real.sqrt (1 + linPerturb g_P θ ω) - 1
              - (1/2 : ℝ) * linPerturb g_P θ ω) := by
  classical
  have hθ' : ‖(0 : EuclideanSpace ℝ (Fin m)) + θ‖ < truncRadius g_P hg := by
    rwa [zero_add]
  have h_dens_θ := paramSubmodel_score_at_zero g_P hg h_orth (0 + θ) hθ'
  filter_upwards [h_dens_θ] with ω hω
  -- sqrtDensity is √density; density 0 ω = 1, density θ ω = 1 + linPerturb θ ω.
  unfold ParametricFamily.sqrtDensity
  rw [paramSubmodel_density_at_zero g_P hg h_orth ω, Real.sqrt_one]
  -- 0 + θ a.e. density: 1 + linPerturb (0+θ) ω. Note linPerturb is linear,
  -- so linPerturb (0+θ) = linPerturb θ.
  have h_lin_eq : linPerturb g_P (0 + θ) ω = linPerturb g_P θ ω := by
    rw [zero_add]
  rw [hω, h_lin_eq, mul_one]
  -- Inner product reduction.
  rw [inner_g_P_total_eq_linPerturb]

/-- Pointwise bound: under `‖θ‖ < truncRadius`, the Hellinger residual at
`θ` is bounded a.e. by `(linPerturb θ ω)² / 2`. -/
private lemma hellinger_residual_pointwise_bound
    (θ : EuclideanSpace ℝ (Fin m))
    (hθ : ‖θ‖ < truncRadius g_P hg) :
    ∀ᵐ ω ∂P,
      |Real.sqrt (1 + linPerturb g_P θ ω) - 1 - (1/2 : ℝ) * linPerturb g_P θ ω|
        ≤ (linPerturb g_P θ ω) ^ 2 / 2 := by
  classical
  have h_nn := linPerturb_truncated_nonneg g_P hg θ hθ
  filter_upwards [h_nn] with ω hω
  have h := sqrt_one_add_residual_bound (u := linPerturb g_P θ ω) hω
  -- Rewrite (1/2)·u = u/2.
  have heq : (1/2 : ℝ) * linPerturb g_P θ ω = linPerturb g_P θ ω / 2 := by ring
  rw [heq]; exact h

/-- Pointwise upper bound on `(linPerturb θ ω)²`: it is `≤ (‖θ‖·m·M)²`. -/
private lemma sq_linPerturb_le
    (θ : EuclideanSpace ℝ (Fin m)) :
    ∀ᵐ ω ∂P,
      (linPerturb g_P θ ω) ^ 2 ≤ (‖θ‖ * m * hg.uniformBound) ^ 2 := by
  filter_upwards [abs_linPerturb_le g_P hg θ] with ω hω
  have h_abs_nn : 0 ≤ |linPerturb g_P θ ω| := abs_nonneg _
  have h_rhs_nn : 0 ≤ ‖θ‖ * m * hg.uniformBound := by
    have : 0 ≤ ‖θ‖ * m := mul_nonneg (norm_nonneg _) (by positivity)
    exact mul_nonneg this hg.uniformBound_nonneg
  have h_abs_sq : |linPerturb g_P θ ω| ^ 2 ≤ (‖θ‖ * m * hg.uniformBound) ^ 2 :=
    pow_le_pow_left₀ h_abs_nn hω 2
  rwa [sq_abs] at h_abs_sq

/-- Membership of the squared Hellinger residual in `L¹(P)` (so the
Bochner integral is well-behaved). The residual is bounded a.e. by a
constant depending only on `‖θ‖, m, M`, hence is in `MemLp 2 P`. -/
private lemma hellinger_residual_memLp
    (θ : EuclideanSpace ℝ (Fin m))
    (hθ : ‖θ‖ < truncRadius g_P hg) :
    MemLp (fun ω => (paramSubmodel g_P hg h_orth).sqrtDensity (0 + θ) ω
              - (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω
              - (1/2 : ℝ) * @inner ℝ _ _ θ (g_P_total g_P ω)
                  * (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω) 2 P := by
  classical
  -- Get a.e.-equality with `√(1+linPerturb) - 1 - linPerturb/2` and prove
  -- MemLp on the latter.
  have h_ae_eq := hellinger_residual_ae_eq g_P hg h_orth θ hθ
  set f : Ω → ℝ := fun ω => Real.sqrt (1 + linPerturb g_P θ ω) - 1
                            - (1/2 : ℝ) * linPerturb g_P θ ω
  -- Bound for f: |f ω| ≤ (linPerturb θ ω)² / 2 ≤ (‖θ‖·m·M)² / 2.
  set C : ℝ := (‖θ‖ * m * hg.uniformBound) ^ 2 / 2
  have h_C_nn : 0 ≤ C := by
    apply div_nonneg (sq_nonneg _) (by norm_num)
  have h_f_bound : ∀ᵐ ω ∂P, f ω ∈ Set.Icc (-C) C := by
    have h1 := hellinger_residual_pointwise_bound g_P hg θ hθ
    have h2 := sq_linPerturb_le g_P hg θ
    filter_upwards [h1, h2] with ω hω1 hω2
    -- |f ω| ≤ (linPerturb θ ω)² / 2 ≤ (‖θ‖·m·M)² / 2 = C.
    have habs : |f ω| ≤ C := by
      have h_inner : |f ω| ≤ (linPerturb g_P θ ω) ^ 2 / 2 := hω1
      have h_step : (linPerturb g_P θ ω) ^ 2 / 2 ≤ C := by
        apply div_le_div_of_nonneg_right hω2 (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    exact ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩
  -- f is strongly measurable.
  have h_f_meas : Measurable f := by
    refine (((measurable_const).add (linPerturb_meas g_P θ)).sqrt.sub measurable_const).sub ?_
    exact measurable_const.mul (linPerturb_meas g_P θ)
  -- MemLp via bounded ae + finite measure.
  have h_f_memLp : MemLp f 2 P :=
    memLp_of_bounded h_f_bound h_f_meas.aestronglyMeasurable 2
  -- Transfer via a.e.-equality.
  exact MeasureTheory.MemLp.ae_eq h_ae_eq.symm h_f_memLp

/-- For `‖θ‖ < truncRadius`, the integral of the squared Hellinger residual
is `≤ (‖θ‖·m·M)⁴ / 4`. -/
private lemma integral_hellinger_residual_sq_le
    (θ : EuclideanSpace ℝ (Fin m))
    (hθ : ‖θ‖ < truncRadius g_P hg) :
    ∫ ω, ((paramSubmodel g_P hg h_orth).sqrtDensity (0 + θ) ω
            - (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω
            - (1/2 : ℝ) * @inner ℝ _ _ θ (g_P_total g_P ω)
                * (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω) ^ 2 ∂P
      ≤ (‖θ‖ * m * hg.uniformBound) ^ 4 / 4 := by
  classical
  have h_ae_eq := hellinger_residual_ae_eq g_P hg h_orth θ hθ
  -- Rewrite the integrand using the a.e.-equality.
  set R : Ω → ℝ := fun ω => (paramSubmodel g_P hg h_orth).sqrtDensity (0 + θ) ω
              - (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω
              - (1/2 : ℝ) * @inner ℝ _ _ θ (g_P_total g_P ω)
                  * (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω
  set R' : Ω → ℝ := fun ω => Real.sqrt (1 + linPerturb g_P θ ω) - 1
                              - (1/2 : ℝ) * linPerturb g_P θ ω
  have h_sq_eq : (fun ω => R ω ^ 2) =ᵐ[P] (fun ω => R' ω ^ 2) := by
    filter_upwards [h_ae_eq] with ω hω
    rw [hω]
  rw [integral_congr_ae h_sq_eq]
  -- Now bound ∫ R'² ≤ (‖θ‖·m·M)⁴ / 4.
  -- Pointwise: (R'(ω))² ≤ ((linPerturb θ ω)²/2)² = (linPerturb θ ω)⁴/4
  --                    ≤ (‖θ‖·m·M)⁴/4.
  set Bnd : ℝ := (‖θ‖ * m * hg.uniformBound) ^ 4 / 4
  have h_pt_bound : ∀ᵐ ω ∂P, R' ω ^ 2 ≤ Bnd := by
    have h1 := hellinger_residual_pointwise_bound g_P hg θ hθ
    have h2 := sq_linPerturb_le g_P hg θ
    filter_upwards [h1, h2] with ω hω1 hω2
    have hR'_abs : |R' ω| ≤ (linPerturb g_P θ ω) ^ 2 / 2 := hω1
    have hR'_abs_nn : 0 ≤ |R' ω| := abs_nonneg _
    have hu2_nn : 0 ≤ (linPerturb g_P θ ω) ^ 2 / 2 := by positivity
    -- (|R'|)² ≤ ((u²)/2)²
    have h_sq_abs : (|R' ω|) ^ 2 ≤ ((linPerturb g_P θ ω) ^ 2 / 2) ^ 2 :=
      pow_le_pow_left₀ hR'_abs_nn hR'_abs 2
    have h_sq_eq : (R' ω) ^ 2 = (|R' ω|) ^ 2 := by
      rw [sq_abs]
    -- ((u²)/2)² = u⁴/4 ≤ (‖θ‖·m·M)⁴/4.
    have h_eq2 : ((linPerturb g_P θ ω) ^ 2 / 2) ^ 2
                  = (linPerturb g_P θ ω) ^ 4 / 4 := by ring
    have h_u4 : (linPerturb g_P θ ω) ^ 4
                ≤ (‖θ‖ * m * hg.uniformBound) ^ 4 := by
      have : (linPerturb g_P θ ω) ^ 4
            = ((linPerturb g_P θ ω) ^ 2) ^ 2 := by ring
      rw [this]
      have h_rhs_eq : (‖θ‖ * m * hg.uniformBound) ^ 4
                    = ((‖θ‖ * m * hg.uniformBound) ^ 2) ^ 2 := by ring
      rw [h_rhs_eq]
      have h_u2_nn : 0 ≤ (linPerturb g_P θ ω) ^ 2 := sq_nonneg _
      exact pow_le_pow_left₀ h_u2_nn hω2 2
    rw [h_sq_eq]
    calc (|R' ω|) ^ 2
        ≤ ((linPerturb g_P θ ω) ^ 2 / 2) ^ 2 := h_sq_abs
      _ = (linPerturb g_P θ ω) ^ 4 / 4 := h_eq2
      _ ≤ (‖θ‖ * m * hg.uniformBound) ^ 4 / 4 :=
          div_le_div_of_nonneg_right h_u4 (by norm_num)
  -- Integrate the pointwise bound: ∫ R'² ≤ ∫ Bnd = Bnd · 1 = Bnd.
  have h_R'_meas : Measurable R' := by
    refine (((measurable_const).add (linPerturb_meas g_P θ)).sqrt.sub measurable_const).sub ?_
    exact measurable_const.mul (linPerturb_meas g_P θ)
  have h_R'_sq_int : Integrable (fun ω => R' ω ^ 2) P := by
    -- bounded by constant Bnd ≥ 0 a.e. on a finite measure ⇒ integrable.
    apply Integrable.mono' (g := fun _ => Bnd) (integrable_const _)
    · exact (h_R'_meas.pow_const 2).aestronglyMeasurable
    · filter_upwards [h_pt_bound] with ω hω
      have h_nn : 0 ≤ R' ω ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
      exact hω
  calc ∫ ω, R' ω ^ 2 ∂P
      ≤ ∫ _ω, Bnd ∂P := by
        apply integral_mono_ae h_R'_sq_int (integrable_const _) h_pt_bound
    _ = Bnd := by simp

/-- **Differentiability in quadratic mean of the parametric submodel at `θ = 0`.**

The Hellinger residual `√(p_θ) - √(p_0) - ½⟨θ, g_P_total⟩√(p_0)` integrates to
`o(‖θ‖²)` as `θ → 0`. The proof uses:
1. `paramSubmodel_density_at_zero` (`p_0 = 1`, so `√(p_0) = 1`),
2. `paramSubmodel_score_at_zero` (`p_θ = 1 + linPerturb θ` a.e. for `‖θ‖ < truncRadius`),
3. the Taylor inequality `|√(1+u) - 1 - u/2| ≤ u²/2` for `0 ≤ 1+u`,
4. the uniform bound `|linPerturb θ ω| ≤ ‖θ‖ · m · M` a.e..

The integrated squared residual is `≤ (‖θ‖·m·M)⁴ / 4 = O(‖θ‖⁴)`, which is
`=o[𝓝 0]` of `‖θ‖²`. -/
theorem paramSubmodel_DQM :
    DifferentiableQuadraticMean (paramSubmodel g_P hg h_orth) P 0 (g_P_total g_P) := by
  classical
  -- Membership: the residual is in MemLp 2 for ‖θ‖ < truncRadius.
  have h_pos : 0 < truncRadius g_P hg := truncRadius_pos g_P hg
  have h_nbhd : Set.Iio (truncRadius g_P hg) ∈ 𝓝 (0 : ℝ) :=
    Iio_mem_nhds h_pos
  refine ⟨?_, ?_⟩
  · -- mem: eventually in 𝓝 (0 : EuclideanSpace ℝ (Fin m)).
    have h_norm : Tendsto (fun θ : EuclideanSpace ℝ (Fin m) => ‖θ‖)
        (𝓝 0) (𝓝 0) := by
      have := (continuous_norm (E := EuclideanSpace ℝ (Fin m))).tendsto 0
      simpa [norm_zero] using this
    have h_ev : ∀ᶠ θ : EuclideanSpace ℝ (Fin m) in 𝓝 0,
        ‖θ‖ < truncRadius g_P hg := h_norm h_nbhd
    filter_upwards [h_ev] with θ hθ
    exact hellinger_residual_memLp g_P hg h_orth θ hθ
  · -- isLittleO: ∫ residual² ∂P =o[‖θ‖²].
    -- Bound: ∫ residual² ≤ (‖θ‖·m·M)⁴/4 = ‖θ‖⁴·(m·M)⁴/4.
    -- Hence (∫ residual²)/‖θ‖² ≤ ‖θ‖²·(m·M)⁴/4 → 0 as θ → 0.
    set C : ℝ := ((m : ℝ) * hg.uniformBound) ^ 4 / 4 with hC_def
    have hC_nn : 0 ≤ C := by
      have h_pow_nn : 0 ≤ ((m : ℝ) * hg.uniformBound) ^ 4 := by
        have : ((m : ℝ) * hg.uniformBound) ^ 4 = (((m : ℝ) * hg.uniformBound) ^ 2) ^ 2 := by ring
        rw [this]; exact sq_nonneg _
      exact div_nonneg h_pow_nn (by norm_num)
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    -- We need ∀ᶠ θ in 𝓝 0, ‖∫ res² dP‖ ≤ ε · ‖‖θ‖²‖.
    -- The integrand bound + nonnegativity of ‖θ‖² gives:
    -- ∫ res² dP ≤ ‖θ‖⁴ · (m·M)⁴/4 = ‖θ‖² · (‖θ‖² · C).
    -- So we want ‖θ‖² · C ≤ ε, i.e. ‖θ‖² ≤ ε/C (or C = 0 case).
    by_cases hC_zero : C = 0
    · -- C = 0 ⇒ ((m·M)⁴ = 0) ⇒ either m=0 or M=0; either way the integrand bound is 0.
      have h_mM_zero : (m : ℝ) * hg.uniformBound = 0 := by
        have hC_eq : ((m : ℝ) * hg.uniformBound) ^ 4 = 0 := by
          have h1 : ((m : ℝ) * hg.uniformBound) ^ 4 / 4 = 0 := hC_zero
          linarith [h1]
        exact (pow_eq_zero_iff (n := 4) (by norm_num)).mp hC_eq
      have h_norm : Tendsto (fun θ : EuclideanSpace ℝ (Fin m) => ‖θ‖)
          (𝓝 0) (𝓝 0) := by
        have := (continuous_norm (E := EuclideanSpace ℝ (Fin m))).tendsto 0
        simpa [norm_zero] using this
      have h_ev : ∀ᶠ θ : EuclideanSpace ℝ (Fin m) in 𝓝 0,
          ‖θ‖ < truncRadius g_P hg := h_norm h_nbhd
      filter_upwards [h_ev] with θ hθ
      have h_le := integral_hellinger_residual_sq_le g_P hg h_orth θ hθ
      have h_zero : (‖θ‖ * m * hg.uniformBound) ^ 4 / 4 = 0 := by
        have h_inner : ‖θ‖ * m * hg.uniformBound = 0 := by
          have h_assoc : ‖θ‖ * m * hg.uniformBound
                = ‖θ‖ * ((m : ℝ) * hg.uniformBound) := by ring
          rw [h_assoc, h_mM_zero, mul_zero]
        rw [h_inner]; ring
      rw [h_zero] at h_le
      set RES : Ω → ℝ := fun ω =>
        (paramSubmodel g_P hg h_orth).sqrtDensity (0 + θ) ω
        - (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω
        - (1/2 : ℝ) * @inner ℝ _ _ θ (g_P_total g_P ω)
            * (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω with hRES_def
      have h_int_nn : 0 ≤ ∫ ω, RES ω ^ 2 ∂P := by
        apply integral_nonneg
        intro ω; exact sq_nonneg _
      have h_int_zero : ∫ ω, RES ω ^ 2 ∂P = 0 := le_antisymm h_le h_int_nn
      rw [Real.norm_eq_abs, h_int_zero, abs_zero]
      apply mul_nonneg (le_of_lt hε) (norm_nonneg _)
    · -- C > 0: choose δ small.
      have hC_pos : 0 < C := lt_of_le_of_ne hC_nn (Ne.symm hC_zero)
      set δ : ℝ := min (truncRadius g_P hg) (Real.sqrt (ε / C)) with hδ_def
      have h_eC_pos : 0 < ε / C := div_pos hε hC_pos
      have h_sqrt_pos : 0 < Real.sqrt (ε / C) := Real.sqrt_pos.mpr h_eC_pos
      have hδ_pos : 0 < δ := lt_min h_pos h_sqrt_pos
      have h_norm : Tendsto (fun θ : EuclideanSpace ℝ (Fin m) => ‖θ‖)
          (𝓝 0) (𝓝 0) := by
        have := (continuous_norm (E := EuclideanSpace ℝ (Fin m))).tendsto 0
        simpa [norm_zero] using this
      have h_nbhd2 : Set.Iio δ ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hδ_pos
      have h_ev : ∀ᶠ θ : EuclideanSpace ℝ (Fin m) in 𝓝 0,
          ‖θ‖ < δ := h_norm h_nbhd2
      filter_upwards [h_ev] with θ hθ_lt
      have hθ_lt_trunc : ‖θ‖ < truncRadius g_P hg :=
        lt_of_lt_of_le hθ_lt (min_le_left _ _)
      have hθ_lt_sqrt : ‖θ‖ < Real.sqrt (ε / C) :=
        lt_of_lt_of_le hθ_lt (min_le_right _ _)
      have h_le := integral_hellinger_residual_sq_le g_P hg h_orth θ hθ_lt_trunc
      -- Convert (‖θ‖·m·M)⁴/4 = ‖θ‖⁴ · ((m·M)⁴/4) = ‖θ‖² · (‖θ‖² · C).
      have h_rewrite : (‖θ‖ * m * hg.uniformBound) ^ 4 / 4
            = ‖θ‖ ^ 2 * (‖θ‖ ^ 2 * C) := by
        rw [hC_def]; ring
      rw [h_rewrite] at h_le
      -- h_le : ∫ res² ≤ ‖θ‖² · (‖θ‖² · C). Now show ‖θ‖² · C ≤ ε.
      have h_norm_sq_le : ‖θ‖ ^ 2 ≤ ε / C := by
        have hθ_nn : 0 ≤ ‖θ‖ := norm_nonneg _
        have h_sqrt_nn : 0 ≤ Real.sqrt (ε / C) := Real.sqrt_nonneg _
        have h_sq : ‖θ‖ ^ 2 ≤ (Real.sqrt (ε / C)) ^ 2 :=
          pow_le_pow_left₀ hθ_nn (le_of_lt hθ_lt_sqrt) 2
        rw [Real.sq_sqrt (le_of_lt h_eC_pos)] at h_sq
        exact h_sq
      have h_norm_sq_C_le : ‖θ‖ ^ 2 * C ≤ ε := by
        have := mul_le_mul_of_nonneg_right h_norm_sq_le (le_of_lt hC_pos)
        rwa [div_mul_cancel₀ ε (ne_of_gt hC_pos)] at this
      have h_norm_sq_nn : 0 ≤ ‖θ‖ ^ 2 := sq_nonneg _
      set RES : Ω → ℝ := fun ω =>
        (paramSubmodel g_P hg h_orth).sqrtDensity (0 + θ) ω
        - (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω
        - (1/2 : ℝ) * @inner ℝ _ _ θ (g_P_total g_P ω)
            * (paramSubmodel g_P hg h_orth).sqrtDensity 0 ω with hRES_def
      have h_int_nn : 0 ≤ ∫ ω, RES ω ^ 2 ∂P := by
        apply integral_nonneg
        intro ω; exact sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h_int_nn,
          Real.norm_eq_abs, abs_of_nonneg h_norm_sq_nn]
      -- Goal: ∫ RES² dP ≤ ε · ‖θ‖²
      have h_step1 : ∫ ω, RES ω ^ 2 ∂P ≤ ‖θ‖ ^ 2 * (‖θ‖ ^ 2 * C) := h_le
      have h_step2 : ‖θ‖ ^ 2 * (‖θ‖ ^ 2 * C) ≤ ‖θ‖ ^ 2 * ε :=
        mul_le_mul_of_nonneg_left h_norm_sq_C_le h_norm_sq_nn
      have h_step3 : ‖θ‖ ^ 2 * ε = ε * ‖θ‖ ^ 2 := by ring
      linarith [h_step1, h_step2, h_step3]

end DQM

/-! ## Fisher information

At `θ = 0` with score `g_P_total`, density is identically `1`, so

  `fisher u v = ∫ ⟪u, g_P_total ω⟫ · ⟪v, g_P_total ω⟫ dP`
            `= ∫ (linPerturb u) · (linPerturb v) dP`
            `= ∑ᵢⱼ u i · v j · ∫ gMk i · gMk j dP`
            `= ∑ᵢⱼ u i · v j · ⟨g_P i, g_P j⟩_{L²(P)}`
            `= ∑ᵢ u i · v i = ⟪u, v⟫_E`  (by orthonormality).
-/

section FisherInfo

variable {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
variable (hg : IsBoundedMixtureScores g_P)
variable (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))

/-- `∫ gMk i · gMk j dP = δ_{ij}` from orthonormality of the `g_P i` in
`Lp ℝ 2 P` and the a.e.-equality `gMk i =ᵐ[P] (g_P i : Ω → ℝ)`. -/
private lemma integral_gMk_mul_gMk
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (i j : Fin m) :
    ∫ ω, gMk g_P i ω * gMk g_P j ω ∂P = if i = j then 1 else 0 := by
  classical
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
  -- Translate to integral via L².inner_def + RCLike.inner_apply.
  rw [MeasureTheory.L2.inner_def] at h_inner
  -- h_inner : ∫ ⟪(g_P i : Lp...) ω, (g_P j : Lp...) ω⟫_ℝ dP = δ_ij
  -- And ⟪a, b⟫_ℝ = b * a for reals.
  have h_int_eq :
      ∫ ω, @inner ℝ _ _ (((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω)
                       (((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω) ∂P
        = ∫ ω, ((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω
                * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω ∂P := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rfl
  rw [h_int_eq] at h_inner
  -- Move from (g_P j) * (g_P i) to (g_P i) * (g_P j) (commutative).
  have h_comm : ∫ ω, ((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω
                * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω ∂P
              = ∫ ω, ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω
                * ((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω ∂P := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun ω => mul_comm _ _)
  rw [h_comm] at h_inner
  -- Bridge to gMk via a.e.-equality.
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

/-- Integrability of `gMk i · gMk j`. -/
private lemma integrable_gMk_mul (i j : Fin m) :
    Integrable (fun ω => gMk g_P i ω * gMk g_P j ω) P := by
  -- Lift to (g_P i : Ω → ℝ) · (g_P j : Ω → ℝ) and use MemLp.integrable_mul.
  have hi_memLp : MemLp (((g_P i : Lp ℝ 2 P) : Ω → ℝ)) 2 P :=
    Lp.memLp _
  have hj_memLp : MemLp (((g_P j : Lp ℝ 2 P) : Ω → ℝ)) 2 P :=
    Lp.memLp _
  have h_int_lp : Integrable (fun ω => ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω
                                      * ((g_P j : Lp ℝ 2 P) : Ω → ℝ) ω) P :=
    hi_memLp.integrable_mul hj_memLp
  -- Bridge via a.e.-equality.
  refine h_int_lp.congr ?_
  filter_upwards [gMk_ae_eq g_P i, gMk_ae_eq g_P j] with ω hi hj
  rw [hi, hj]

/-- **Fisher information at `θ = 0` is the identity bilinear form.**

Concretely: for all `u v : EuclideanSpace ℝ (Fin m)`,
`fisherInformation paramSubmodel P 0 g_P_total u v = ⟪u, v⟫_E`.

Proof: the density at `0` is `1`, so the Fisher integrand is
`⟪u, g_P_total ω⟫ · ⟪v, g_P_total ω⟫ = (linPerturb u ω) · (linPerturb v ω)`.
Expanding the product of sums and using `∫ gMk i · gMk j dP = δ_{ij}` (from
orthonormality) gives `∑ᵢ u i · v i = ⟪u, v⟫_E`. -/
theorem paramSubmodel_fisher_info :
    ∀ u v : EuclideanSpace ℝ (Fin m),
      fisherInformation (paramSubmodel g_P hg h_orth) P 0 (g_P_total g_P) u v
        = @inner ℝ _ _ u v := by
  classical
  intro u v
  unfold fisherInformation
  -- Density at 0 is identically 1.
  have h_dens_eq : ∀ ω, (paramSubmodel g_P hg h_orth).density 0 ω = 1 :=
    fun ω => paramSubmodel_density_at_zero g_P hg h_orth ω
  have h_integrand_eq : ∀ ω,
      (@inner ℝ _ _ u (g_P_total g_P ω) * @inner ℝ _ _ v (g_P_total g_P ω))
        * (paramSubmodel g_P hg h_orth).density 0 ω
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
        exact (integrable_gMk_mul g_P i j).const_mul _
    rw [Finset.sum_congr rfl (fun i _ => h_inner_step i)]
    -- Now: ∑ᵢ ∑ⱼ (u i · v j) · δ_{ij} = ∑ᵢ u i · v i = ⟪u, v⟫_E.
    have h_sum_eq : ∀ i,
        ∑ j, (u i * v j) * ∫ ω, gMk g_P i ω * gMk g_P j ω ∂P
        = u i * v i := by
      intro i
      have h_each : ∀ j, (u i * v j)
            * ∫ ω, gMk g_P i ω * gMk g_P j ω ∂P
            = if i = j then u i * v i else 0 := by
        intro j
        rw [integral_gMk_mul_gMk g_P h_orth i j]
        by_cases hij : i = j
        · subst hij; simp
        · simp [if_neg hij]
      rw [Finset.sum_congr rfl (fun j _ => h_each j)]
      -- ∑ j, if i = j then u i * v i else 0 = u i * v i.
      rw [Finset.sum_ite_eq_of_mem Finset.univ i (fun _ => u i * v i)
            (Finset.mem_univ i)]
    rw [Finset.sum_congr rfl (fun i _ => h_sum_eq i)]
    -- ⟪u, v⟫_E = ∑ i, ⟪u i, v i⟫_ℝ = ∑ i, v i * u i (since real inner is reversed).
    -- We have ∑ i, u i * v i; use commutativity.
    rw [show (@inner ℝ _ _ u v) = ∑ i, u i * v i by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change @inner ℝ _ _ (u i) (v i) = u i * v i
      change v i * u i = u i * v i
      ring]
  · -- Integrability of ∑ⱼ (u i · v j) · (gMk i · gMk j) for each i.
    intro i _
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact (integrable_gMk_mul g_P i j).const_mul _

end FisherInfo

/-! ## Mutual absolute continuity (h_same_support)

The density at `θ = 0` is identically `1` (positive everywhere); the density
at any perturbation is positive a.e.. -/

section SameSupport

variable {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
variable (hg : IsBoundedMixtureScores g_P)
variable (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))

/-- Strict positivity of the density at any parameter `η`. For `‖η‖ <
truncRadius` strictly: `linPerturb η ω > -1` a.e., so `1 + linPerturb η ω > 0`
a.e.. For `‖η‖ ≥ truncRadius`: density is `max 0 1 = 1 > 0`. -/
private lemma paramSubmodel_density_pos (η : EuclideanSpace ℝ (Fin m)) :
    ∀ᵐ ω ∂P, 0 < (paramSubmodel g_P hg h_orth).density η ω := by
  classical
  by_cases hη : ‖η‖ < truncRadius g_P hg
  · -- ‖η‖ < truncRadius: |linPerturb η ω| ≤ ‖η‖·m·M < 1 strictly a.e..
    by_cases hm0 : m = 0
    · -- m = 0: linPerturb is the empty sum, identically 0.
      refine Filter.Eventually.of_forall (fun ω => ?_)
      change 0 < submodelDensityNN g_P hg η ω
      unfold submodelDensityNN submodelDensity
      rw [if_pos hη]
      have hempty : linPerturb g_P η ω = 0 := by
        unfold linPerturb
        subst hm0
        simp
      rw [hempty]
      norm_num
    · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
      have hm_nn : (0 : ℝ) ≤ m := by positivity
      have hM_nn : 0 ≤ hg.uniformBound := hg.uniformBound_nonneg
      have h_bound := abs_linPerturb_le g_P hg η
      filter_upwards [h_bound] with ω hω
      change 0 < submodelDensityNN g_P hg η ω
      unfold submodelDensityNN submodelDensity
      rw [if_pos hη]
      -- Strict bound: ‖η‖ * m * M < 1 (strictly less, by truncRadius_pos).
      have h_target : ‖η‖ * m * hg.uniformBound < 1 := by
        have htm_nn : 0 ≤ hg.uniformBound * m := mul_nonneg hM_nn hm_nn
        have hpos : (0 : ℝ) < hg.uniformBound * m + 1 := by linarith
        have hηlt : ‖η‖ < 1 / (hg.uniformBound * m + 1) := hη
        have hη_nn : 0 ≤ ‖η‖ := norm_nonneg _
        -- Same calculation as in linPerturb_truncated_nonneg.
        have h_step1 : ‖η‖ * m * hg.uniformBound ≤
            (1 / (hg.uniformBound * m + 1)) * m * hg.uniformBound := by
          have hmM_nn : 0 ≤ (m : ℝ) * hg.uniformBound := mul_nonneg hm_nn hM_nn
          have hηle : ‖η‖ ≤ 1 / (hg.uniformBound * m + 1) := le_of_lt hηlt
          nlinarith [hηle, hη_nn, hmM_nn,
            mul_nonneg hm_nn hM_nn, (one_div_pos.mpr hpos).le]
        have h_simp : (1 / (hg.uniformBound * m + 1)) * m * hg.uniformBound
            = (hg.uniformBound * m) / (hg.uniformBound * m + 1) := by
          field_simp
        rw [h_simp] at h_step1
        have h_lt_one : (hg.uniformBound * m) / (hg.uniformBound * m + 1) < 1 := by
          rw [div_lt_one hpos]; linarith
        exact lt_of_le_of_lt h_step1 h_lt_one
      have hbound : |linPerturb g_P η ω| < 1 := lt_of_le_of_lt hω h_target
      have hgt : -1 < linPerturb g_P η ω := (abs_lt.mp hbound).1
      have h1plus : 0 < 1 + linPerturb g_P η ω := by linarith
      change 0 < max 0 (1 + linPerturb g_P η ω)
      exact lt_max_of_lt_right h1plus
  · -- ‖η‖ ≥ truncRadius: density falls back to max 0 1 = 1.
    refine Filter.Eventually.of_forall (fun ω => ?_)
    change 0 < submodelDensityNN g_P hg η ω
    unfold submodelDensityNN submodelDensity
    rw [if_neg hη]
    norm_num

/-- **Mutual absolute continuity at `θ = 0`.**

For every `t : ℝ` and every `u : EuclideanSpace ℝ (Fin m)`, the densities at
`0` and `0 + t • u = t • u` agree on positivity a.e.. Since the density at
`0` is identically `1 > 0`, this reduces to a.e.-positivity of the density
at `t • u`, which follows from the truncated construction (positive a.e. for
parameters within `truncRadius` and identically `1` outside). -/
theorem paramSubmodel_h_same_support :
    ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin m), ∀ᵐ x ∂P,
      (0 < (paramSubmodel g_P hg h_orth).density 0 x ↔
       0 < (paramSubmodel g_P hg h_orth).density (0 + t • u) x) := by
  intro t u
  have h_dens_zero : ∀ ω, (paramSubmodel g_P hg h_orth).density 0 ω = 1 :=
    fun ω => paramSubmodel_density_at_zero g_P hg h_orth ω
  have h_dens_pert := paramSubmodel_density_pos g_P hg h_orth (0 + t • u)
  filter_upwards [h_dens_pert] with x hx
  rw [h_dens_zero x]
  refine ⟨fun _ => hx, fun _ => ?_⟩
  norm_num

end SameSupport

end AsymptoticStatistics.ParametricFamily
