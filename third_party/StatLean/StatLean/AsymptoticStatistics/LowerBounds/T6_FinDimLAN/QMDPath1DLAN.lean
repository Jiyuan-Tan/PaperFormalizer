module
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.Core.MassMethod
public import StatLean.AsymptoticStatistics.Core.Hilbert
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs
public import StatLean.AsymptoticStatistics.DQM.Defs
public import StatLean.AsymptoticStatistics.ParametricFamily.FisherInformation
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.LANExpansion
public import StatLean.AsymptoticStatistics.ForMathlib.QMDAnalytic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
# 1D LAN expansion adapter for `boundedDensityPath`-derived QMDPaths

This file bridges the project's `QMDPath` abstraction and Mathlib's
`ParametricFamily` / `LAN_expansion_iii` machinery, so that a genuine LAN
expansion of the log-likelihood ratio along a single score-direction
becomes available downstream.

The construction is specialised to `boundedDensityPath` rather than the
abstract `QMDPath` for two reasons:

1. `boundedDensityPath` gives the `∀ t` form of `MemLp` (not just
   `Eventually`) plus the explicit `eLpNorm` rate `≤ ofReal(t²·M²/2)`.
2. `QMDPath.score : ↥(L2ZeroMean P)` is L²(P)-integrable, but DQM's score
   `ℓ` must be L²(γ.dominating)-integrable; for `γ.dominating ≠ P` this can
   fail. `boundedDensityPath` hard-codes `dominating := P`, resolving the
   score-domain issue.

The headline chain is `boundedDensityPath_to1DParametricFamily` (the 1D
`ParametricFamily` adapter), `boundedDensityPath_isPDFOf` (`IsPDFOf` w.r.t.
`P`), `boundedDensityPath_dqm` (`DifferentiableQuadraticMean` at `θ = 0`),
and `boundedDensityPath_lanExpansion1D` (the genuine LAN expansion via
`LAN_expansion_iii` at `k = 1`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN

open AsymptoticStatistics.Core.Hilbert AsymptoticStatistics.Core.QMDPath
  AsymptoticStatistics.Core.MassMethod AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### D1. The 1D `ParametricFamily` adapter

For a bounded score `g : ↥(L2ZeroMean P)` with mass-method bound
`hg : IsBoundedMixtureScore g`, package the curve
`t ↦ (boundedDensityPath g hg).curve t` as a 1-parameter
`ParametricFamily` indexed by `EuclideanSpace ℝ (Fin 1)` (the parameter
type expected by `LAN_expansion_iii`, invoked at `k = 1`).

Density: `((curve θ).rnDeriv P).toReal`, with
`θ ∈ EuclideanSpace ℝ (Fin 1)` extracted as `θ 0 : ℝ`. -/
noncomputable def boundedDensityPath_to1DParametricFamily
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g) :
    ParametricFamily Ω (EuclideanSpace ℝ (Fin 1)) where
  density θ ω :=
    (((boundedDensityPath g hg).curve (θ 0)).rnDeriv P ω).toReal
  density_meas _ :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  density_nonneg _ _ := ENNReal.toReal_nonneg

/-! ### D2. `IsPDFOf` proof

The adapter satisfies the PDF axioms with respect to `P`:
the density integrates to 1 (since each `curve θ` is a probability
measure absolutely continuous w.r.t. `P`) and is `P`-integrable.

Both proofs lean on the `SigmaFinite` instance via
`Measure.integral_toReal_rnDeriv`, which requires `[SigmaFinite μ]
[SigmaFinite ν]` plus `μ ≪ ν`. -/
theorem boundedDensityPath_isPDFOf
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g) :
    IsPDFOf (boundedDensityPath_to1DParametricFamily g hg) P where
  density_integral_eq_one θ := by
    -- `(curve (θ 0))` is a probability measure, absolutely continuous
    -- w.r.t. `P`, and `P` is σ-finite (from `IsProbabilityMeasure`).
    have h_prob : IsProbabilityMeasure ((boundedDensityPath g hg).curve (θ 0)) :=
      (boundedDensityPath g hg).curve_isProbability (θ 0)
    have h_ac : (boundedDensityPath g hg).curve (θ 0) ≪ P := by
      -- `curve_absContinuous` references the structure's `dominating`
      -- field, which equals `P` by `boundedDensityPath`'s definition.
      have h_dom : (boundedDensityPath g hg).dominating = P := rfl
      have := (boundedDensityPath g hg).curve_absContinuous (θ 0)
      rwa [h_dom] at this
    -- Apply `Measure.integral_toReal_rnDeriv`:
    --   ∫ ω, ((μ.rnDeriv ν) ω).toReal ∂ν = μ.real univ.
    have h_int :=
      MeasureTheory.Measure.integral_toReal_rnDeriv
        (μ := (boundedDensityPath g hg).curve (θ 0)) (ν := P) h_ac
    -- For a probability measure, `μ.real Set.univ = 1`.
    have h_univ : ((boundedDensityPath g hg).curve (θ 0)).real Set.univ = 1 := by
      have := isProbabilityMeasure_iff.mp h_prob
      simp [Measure.real, this]
    -- Unfold the `density` in the goal — the family stores
    -- `density θ ω := ((curve (θ 0)).rnDeriv P ω).toReal`.
    change ∫ ω, (((boundedDensityPath g hg).curve (θ 0)).rnDeriv P ω).toReal ∂P = 1
    rw [h_int, h_univ]
  density_integrable θ := by
    -- The `.toReal`-rnDeriv is integrable under `P` iff the rnDeriv has
    -- finite integral. For probability measures + AC, finite by
    -- `integral_toReal_rnDeriv` evaluated above.
    have h_prob : IsProbabilityMeasure ((boundedDensityPath g hg).curve (θ 0)) :=
      (boundedDensityPath g hg).curve_isProbability (θ 0)
    have h_ac : (boundedDensityPath g hg).curve (θ 0) ≪ P := by
      have h_dom : (boundedDensityPath g hg).dominating = P := rfl
      have := (boundedDensityPath g hg).curve_absContinuous (θ 0)
      rwa [h_dom] at this
    -- `Measure.integrable_toReal_rnDeriv` for a finite μ + σ-finite ν.
    have h_int :=
      MeasureTheory.Measure.integrable_toReal_rnDeriv
        (μ := (boundedDensityPath g hg).curve (θ 0)) (ν := P)
    -- The family's `density θ ω` is definitionally
    -- `((curve (θ 0)).rnDeriv P ω).toReal`.
    change Integrable
      (fun ω => (((boundedDensityPath g hg).curve (θ 0)).rnDeriv P ω).toReal) P
    exact h_int

/-! ### D3. `DifferentiableQuadraticMean` proof — score and infrastructure

The DQM proof bridges the `(eLpNorm).toReal² → ∫ ()² ∂P` form change between
`boundedDensityPath`'s internal representation and
`DifferentiableQuadraticMean.isLittleO`'s Bochner-integral form. Supporting
infrastructure:

- `boundedDensityPath_score1D` — the score map into `EuclideanSpace ℝ (Fin 1)`.
- Norm/inner-product helpers for the singleton Euclidean space. -/

/-- The 1D score function as a `EuclideanSpace ℝ (Fin 1)`-valued map.
The singleton vector `EuclideanSpace.single 0 (g(ω))` packages the
scalar score `g(ω)` into the parameter type expected by
`LAN_expansion_iii`. -/
noncomputable def boundedDensityPath_score1D
    (g : ↥(L2ZeroMean P)) :
    Ω → EuclideanSpace ℝ (Fin 1) :=
  fun ω => EuclideanSpace.single 0 (((g : Lp ℝ 2 P) : Ω → ℝ) ω)

/-- For `θ : EuclideanSpace ℝ (Fin 1)`, `‖θ‖² = (θ 0)²`. -/
private lemma euclideanSpace_norm_sq_fin1 (θ : EuclideanSpace ℝ (Fin 1)) :
    ‖θ‖ ^ 2 = θ 0 ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  have hsum_nn : 0 ≤ ∑ i : Fin 1, ‖θ i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.sq_sqrt hsum_nn]
  simp

/-- For `θ : EuclideanSpace ℝ (Fin 1)`, `‖θ‖ = |θ 0|`. -/
private lemma euclideanSpace_norm_fin1 (θ : EuclideanSpace ℝ (Fin 1)) :
    ‖θ‖ = |θ 0| := by
  have h_sq := euclideanSpace_norm_sq_fin1 θ
  have h_norm_nn : 0 ≤ ‖θ‖ := norm_nonneg _
  have h_abs_nn : 0 ≤ |θ 0| := abs_nonneg _
  nlinarith [h_sq, sq_abs (θ 0), Real.sq_sqrt h_norm_nn,
    Real.sqrt_sq h_norm_nn, Real.sqrt_sq h_abs_nn]

/-- The pointwise Hellinger residual at shift `h ∈ EuclideanSpace ℝ (Fin 1)`
equals `boundedDensityPath_residual g hg (h 0) ω`. -/
private lemma dqm_residual_pointwise_eq
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g)
    (h : EuclideanSpace ℝ (Fin 1)) (ω : Ω) :
    (boundedDensityPath_to1DParametricFamily g hg).sqrtDensity (0 + h) ω
      - (boundedDensityPath_to1DParametricFamily g hg).sqrtDensity 0 ω
      - (1/2 : ℝ) * @inner ℝ _ _ h (boundedDensityPath_score1D g ω)
          * (boundedDensityPath_to1DParametricFamily g hg).sqrtDensity 0 ω
    = boundedDensityPath_residual g hg (h 0) ω := by
  unfold ParametricFamily.sqrtDensity boundedDensityPath_to1DParametricFamily
    boundedDensityPath_residual boundedDensityPath_score1D
  have h_inner :
      @inner ℝ _ _ h (EuclideanSpace.single 0 (((g : Lp ℝ 2 P) : Ω → ℝ) ω))
        = ((g : Lp ℝ 2 P) : Ω → ℝ) ω * h 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_one]
    -- Goal: ⟪h.ofLp 0, single 0 (g ω) 0⟫ = (g ω) * h.ofLp 0
    -- single 0 (g ω) 0 = g ω, then ⟪a, b⟫_ℝ = b * a defeq.
    have h_single : EuclideanSpace.single (0 : Fin 1)
        (((g : Lp ℝ 2 P) : Ω → ℝ) ω) (0 : Fin 1) = ((g : Lp ℝ 2 P) : Ω → ℝ) ω := by
      simp
    rw [h_single]
    -- Goal: ⟪h.ofLp 0, g ω⟫_ℝ = g ω * h.ofLp 0; both real, defeq.
    change ((g : Lp ℝ 2 P) : Ω → ℝ) ω * h 0 = ((g : Lp ℝ 2 P) : Ω → ℝ) ω * h 0
    rfl
  have h_zero_apply : ((0 : EuclideanSpace ℝ (Fin 1)) 0) = 0 := rfl
  have h_add_apply : ((0 + h) 0) = h 0 := by rw [zero_add]
  change Real.sqrt (((boundedDensityPath g hg).curve ((0 + h) 0)).rnDeriv P ω).toReal
        - Real.sqrt (((boundedDensityPath g hg).curve
            ((0 : EuclideanSpace ℝ (Fin 1)) 0)).rnDeriv P ω).toReal
        - (1/2 : ℝ) *
            @inner ℝ _ _ h (EuclideanSpace.single 0 (((g : Lp ℝ 2 P) : Ω → ℝ) ω))
            * Real.sqrt (((boundedDensityPath g hg).curve
                ((0 : EuclideanSpace ℝ (Fin 1)) 0)).rnDeriv P ω).toReal
      = Real.sqrt (((boundedDensityPath g hg).curve (h 0)).rnDeriv P ω).toReal
        - Real.sqrt (((boundedDensityPath g hg).curve 0).rnDeriv P ω).toReal
        - (h 0 / 2) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω
            * Real.sqrt (((boundedDensityPath g hg).curve 0).rnDeriv P ω).toReal
  rw [h_zero_apply, h_add_apply, h_inner]
  ring

/-- The DQM Hellinger residual function equals
`fun ω ↦ boundedDensityPath_residual g hg (h 0) ω`. -/
private lemma dqm_residual_funext
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g)
    (h : EuclideanSpace ℝ (Fin 1)) :
    (fun ω =>
      (boundedDensityPath_to1DParametricFamily g hg).sqrtDensity (0 + h) ω
        - (boundedDensityPath_to1DParametricFamily g hg).sqrtDensity 0 ω
        - (1/2 : ℝ) * @inner ℝ _ _ h (boundedDensityPath_score1D g ω)
            * (boundedDensityPath_to1DParametricFamily g hg).sqrtDensity 0 ω)
      = fun ω => boundedDensityPath_residual g hg (h 0) ω :=
  funext fun ω => dqm_residual_pointwise_eq g hg h ω

/-- Squared form of the DQM-residual function equality, for use under integrals. -/
private lemma dqm_residual_sq_funext
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g)
    (h : EuclideanSpace ℝ (Fin 1)) :
    (fun ω =>
      ((boundedDensityPath_to1DParametricFamily g hg).sqrtDensity (0 + h) ω
        - (boundedDensityPath_to1DParametricFamily g hg).sqrtDensity 0 ω
        - (1/2 : ℝ) * @inner ℝ _ _ h (boundedDensityPath_score1D g ω)
            * (boundedDensityPath_to1DParametricFamily g hg).sqrtDensity 0 ω) ^ 2)
      = fun ω => boundedDensityPath_residual g hg (h 0) ω ^ 2 := by
  funext ω
  rw [dqm_residual_pointwise_eq g hg h ω]

/-- 1D `DifferentiableQuadraticMean` for `boundedDensityPath`'s parametric
family at `θ = 0` with score `boundedDensityPath_score1D g`. -/
theorem boundedDensityPath_dqm
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g) :
    DifferentiableQuadraticMean
      (boundedDensityPath_to1DParametricFamily g hg) P
      (0 : EuclideanSpace ℝ (Fin 1))
      (boundedDensityPath_score1D g) := by
  set δ : ℝ := boundedDensityPath_truncRadius hg with hδ_def
  have hδ_pos : 0 < δ := boundedDensityPath_truncRadius_pos hg
  have h_norm_tendsto :
      Tendsto (fun θ : EuclideanSpace ℝ (Fin 1) => ‖θ‖) (𝓝 0) (𝓝 0) := by
    have := (continuous_norm (E := EuclideanSpace ℝ (Fin 1))).tendsto 0
    simpa [norm_zero] using this
  have h_nbhd : Set.Iio δ ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hδ_pos
  have h_ev_norm : ∀ᶠ θ : EuclideanSpace ℝ (Fin 1) in 𝓝 0,
      ‖θ‖ < δ := h_norm_tendsto h_nbhd
  refine ⟨?_, ?_⟩
  · -- mem field: eventually MemLp.
    filter_upwards [h_ev_norm] with h hh
    have ht : |h 0| < δ := by rw [← euclideanSpace_norm_fin1]; exact hh
    have h_residual_memLp := boundedDensityPath_residual_memLp g hg ht
    -- Transfer MemLp via the function-extensional equation.
    rw [dqm_residual_funext g hg h]
    exact h_residual_memLp
  · -- isLittleO field: ∫ residual² ∂P =o[𝓝 0] ‖h‖².
    set M : ℝ := hg.essBound with hM_def
    have hM_nn : 0 ≤ M := hg.essBound_nonneg
    set C : ℝ := M ^ 4 / 4 with hC_def
    have hC_nn : 0 ≤ C := by positivity
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    by_cases hC_zero : C = 0
    · -- Degenerate: M = 0 ⇒ residual ≡ 0 a.e.
      have hM_zero : M = 0 := by
        have hM4_zero : M ^ 4 = 0 := by
          have : M ^ 4 / 4 = 0 := hC_zero
          linarith [this]
        exact (pow_eq_zero_iff (n := 4) (by norm_num)).mp hM4_zero
      filter_upwards [h_ev_norm] with θ hθ
      have ht : |θ 0| < δ := by rw [← euclideanSpace_norm_fin1]; exact hθ
      have h_eLp_le := boundedDensityPath_residual_eLpNorm_le g hg ht
      rw [show hg.essBound = M from rfl, hM_zero] at h_eLp_le
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, zero_div, ENNReal.ofReal_zero] at h_eLp_le
      have h_eLp_zero : eLpNorm (boundedDensityPath_residual g hg (θ 0)) 2 P = 0 :=
        le_antisymm h_eLp_le (zero_le)
      have h_residual_memLp := boundedDensityPath_residual_memLp g hg ht
      have h_residual_zero_ae :
          boundedDensityPath_residual g hg (θ 0) =ᵐ[P] 0 :=
        (eLpNorm_eq_zero_iff h_residual_memLp.aestronglyMeasurable
          (by norm_num)).mp h_eLp_zero
      rw [dqm_residual_sq_funext g hg θ]
      have h_sq_zero_ae :
          (fun ω => boundedDensityPath_residual g hg (θ 0) ω ^ 2) =ᵐ[P] 0 := by
        filter_upwards [h_residual_zero_ae] with ω hω
        rw [hω]; simp
      have h_int_zero :
          ∫ ω, boundedDensityPath_residual g hg (θ 0) ω ^ 2 ∂P = 0 :=
        integral_eq_zero_of_ae h_sq_zero_ae
      have h_int_nn :
          0 ≤ ∫ ω, boundedDensityPath_residual g hg (θ 0) ω ^ 2 ∂P :=
        integral_nonneg fun _ => sq_nonneg _
      rw [Real.norm_eq_abs, h_int_zero, abs_zero]
      apply mul_nonneg (le_of_lt hε) (norm_nonneg _)
    · -- Non-degenerate: C > 0.
      have hC_pos : 0 < C := lt_of_le_of_ne hC_nn (Ne.symm hC_zero)
      set ρ : ℝ := min δ (Real.sqrt (ε / C)) with hρ_def
      have h_eC_pos : 0 < ε / C := div_pos hε hC_pos
      have h_sqrt_pos : 0 < Real.sqrt (ε / C) := Real.sqrt_pos.mpr h_eC_pos
      have hρ_pos : 0 < ρ := lt_min hδ_pos h_sqrt_pos
      have h_nbhd2 : Set.Iio ρ ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hρ_pos
      have h_ev2 : ∀ᶠ θ : EuclideanSpace ℝ (Fin 1) in 𝓝 0,
          ‖θ‖ < ρ := h_norm_tendsto h_nbhd2
      filter_upwards [h_ev2] with θ hθ_lt
      have hθ_lt_δ : ‖θ‖ < δ := lt_of_lt_of_le hθ_lt (min_le_left _ _)
      have hθ_lt_sqrt : ‖θ‖ < Real.sqrt (ε / C) :=
        lt_of_lt_of_le hθ_lt (min_le_right _ _)
      have ht_abs : |θ 0| < δ := by
        rw [← euclideanSpace_norm_fin1]; exact hθ_lt_δ
      have h_residual_memLp := boundedDensityPath_residual_memLp g hg ht_abs
      have h_eLp_le := boundedDensityPath_residual_eLpNorm_le g hg ht_abs
      have h_t2_M2_nn : 0 ≤ (θ 0) ^ 2 * M ^ 2 / 2 := by positivity
      have h_eLp_top :
          eLpNorm (boundedDensityPath_residual g hg (θ 0)) 2 P ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_eLp_le
      have h_eLp_toReal_le :
          (eLpNorm (boundedDensityPath_residual g hg (θ 0)) 2 P).toReal
            ≤ (θ 0) ^ 2 * M ^ 2 / 2 := by
        have h := (ENNReal.toReal_le_toReal h_eLp_top
          ENNReal.ofReal_ne_top).mpr h_eLp_le
        rwa [ENNReal.toReal_ofReal h_t2_M2_nn] at h
      -- Convert ∫ residual² to (eLpNorm).toReal² via the QMDAnalytic bridge.
      have h_int_eq_eLpNorm_sq :
          ∫ ω, boundedDensityPath_residual g hg (θ 0) ω ^ 2 ∂P
            = (eLpNorm (boundedDensityPath_residual g hg (θ 0)) 2 P).toReal ^ 2 := by
        have h_sqrt :=
          AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal
            h_residual_memLp
        have h_int_nn :
            0 ≤ ∫ ω, boundedDensityPath_residual g hg (θ 0) ω ^ 2 ∂P :=
          integral_nonneg fun _ => sq_nonneg _
        have := congrArg (fun x => x ^ 2) h_sqrt
        simp only at this
        rw [Real.sq_sqrt h_int_nn] at this
        exact this
      have h_eLp_toReal_nn : 0 ≤
          (eLpNorm (boundedDensityPath_residual g hg (θ 0)) 2 P).toReal :=
        ENNReal.toReal_nonneg
      have h_sq_le :
          (eLpNorm (boundedDensityPath_residual g hg (θ 0)) 2 P).toReal ^ 2
            ≤ ((θ 0) ^ 2 * M ^ 2 / 2) ^ 2 :=
        pow_le_pow_left₀ h_eLp_toReal_nn h_eLp_toReal_le 2
      have h_target_eq : ((θ 0) ^ 2 * M ^ 2 / 2) ^ 2
            = (θ 0) ^ 2 * ((θ 0) ^ 2 * C) := by rw [hC_def]; ring
      have h_int_le :
          ∫ ω, boundedDensityPath_residual g hg (θ 0) ω ^ 2 ∂P
            ≤ (θ 0) ^ 2 * ((θ 0) ^ 2 * C) := by
        rw [h_int_eq_eLpNorm_sq]
        linarith [h_sq_le, h_target_eq.le, h_target_eq.ge]
      have h_norm_sq_le : ‖θ‖ ^ 2 ≤ ε / C := by
        have h_sq : ‖θ‖ ^ 2 ≤ (Real.sqrt (ε / C)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hθ_lt_sqrt) 2
        rwa [Real.sq_sqrt (le_of_lt h_eC_pos)] at h_sq
      have h_norm_sq_C_le : ‖θ‖ ^ 2 * C ≤ ε := by
        have := mul_le_mul_of_nonneg_right h_norm_sq_le (le_of_lt hC_pos)
        rwa [div_mul_cancel₀ ε (ne_of_gt hC_pos)] at this
      have h_norm_sq_eq : ‖θ‖ ^ 2 = (θ 0) ^ 2 := euclideanSpace_norm_sq_fin1 θ
      have h_int_nn :
          0 ≤ ∫ ω, boundedDensityPath_residual g hg (θ 0) ω ^ 2 ∂P :=
        integral_nonneg fun _ => sq_nonneg _
      have h_norm_sq_nn : 0 ≤ ‖θ‖ ^ 2 := sq_nonneg _
      -- Goal becomes ‖∫ residual² ∂P‖ ≤ ε · ‖‖θ‖²‖ after rewriting integrand.
      rw [dqm_residual_sq_funext g hg θ]
      rw [Real.norm_eq_abs, abs_of_nonneg h_int_nn,
          Real.norm_eq_abs, abs_of_nonneg h_norm_sq_nn]
      have h_step1 :
          ∫ ω, boundedDensityPath_residual g hg (θ 0) ω ^ 2 ∂P
            ≤ ‖θ‖ ^ 2 * (‖θ‖ ^ 2 * C) := by
        rw [h_norm_sq_eq]; exact h_int_le
      have h_step2 : ‖θ‖ ^ 2 * (‖θ‖ ^ 2 * C) ≤ ‖θ‖ ^ 2 * ε :=
        mul_le_mul_of_nonneg_left h_norm_sq_C_le h_norm_sq_nn
      linarith [h_step1, h_step2]

/-! ### D4. LAN expansion wrapper

Compose `boundedDensityPath_isPDFOf` + `boundedDensityPath_dqm` with
Mathlib's `LAN_expansion_iii` to obtain the genuine LAN expansion of the
log-likelihood ratio along `boundedDensityPath g hg`. -/

/-- 1D LAN expansion for `boundedDensityPath`: applying
`Asymptotics.LAN.LAN_expansion_iii` at `k = 1` to the
`boundedDensityPath`-derived parametric family. The output is the
standard `TendstoInMeasure` form
`Σᵢ log(p_{h_n/√n}/p_0) − (1/√n)·Σᵢ ⟪h, ℓ Xᵢ⟫ + (1/2)·I(h,h) →_P 0`. -/
theorem boundedDensityPath_lanExpansion1D
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g)
    (h : EuclideanSpace ℝ (Fin 1)) (h_n : ℕ → EuclideanSpace ℝ (Fin 1))
    (hconv : Tendsto h_n atTop (𝓝 h))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω' → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) P')
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P' P')
    (hlaw : Measure.map (X 0) P'
              = P.withDensity (fun x => ENNReal.ofReal
                  ((boundedDensityPath_to1DParametricFamily g hg).density 0 x)))
    (hℓ_meas : Measurable (boundedDensityPath_score1D g)) :
    TendstoInMeasure P'
      (fun n ω =>
        (∑ i ∈ Finset.range n,
          Real.log
            ((boundedDensityPath_to1DParametricFamily g hg).density
                (0 + (Real.sqrt n)⁻¹ • h_n n) (X i ω) /
              (boundedDensityPath_to1DParametricFamily g hg).density 0 (X i ω)))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
            @inner ℝ _ _ h (boundedDensityPath_score1D g (X i ω))
        + (1/2 : ℝ) *
          fisherInformation (boundedDensityPath_to1DParametricFamily g hg) P 0
            (boundedDensityPath_score1D g) h h)
      Filter.atTop (fun _ => (0 : ℝ)) := by
  have h_pdf := boundedDensityPath_isPDFOf g hg
  have h_dqm := boundedDensityPath_dqm g hg
  exact AsymptoticStatistics.LANExpansion.LAN_expansion_iii
    P' (boundedDensityPath_to1DParametricFamily g hg) P
    0 (boundedDensityPath_score1D g) hℓ_meas
    (h_pdf.density_integral_eq_one 0)
    (h_pdf.density_integrable 0)
    (fun t u => h_pdf.density_integral_eq_one (0 + t • u))
    (fun t u => h_pdf.density_integrable (0 + t • u))
    h_dqm h h_n hconv X hX_meas hindep hident hlaw

end AsymptoticStatistics.LowerBounds.T6_FinDimLAN
