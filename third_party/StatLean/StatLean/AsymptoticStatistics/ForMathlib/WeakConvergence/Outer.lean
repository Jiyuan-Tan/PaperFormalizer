module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.ForMathlib.OuterIntegration.OuterExpectation
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section

/-!
# Weak convergence in outer expectation (`⇝ₒ`)

Convergence in law for sequences of (possibly **non-measurable**) maps
`Xₙ : Ω → D` into a metric space `D`, formulated via the **outer expectation**
`E*` (van der Vaart, *Asymptotic Statistics* §18.1; van der Vaart–Wellner,
*Weak Convergence and Empirical Processes*, Ch. 1.3). This is the convergence
notion the abstract-Donsker / empirical-process theory is built on: the
empirical process need not be Borel measurable, so the ordinary `∫ f` readout
is undefined and must be replaced by the outer integral `E*`.

## Design decisions (locked)

* **Single shared sample space `Ω`** for all `Xₙ` (not a dependent family
  `Ωₙ`). The limit is supplied directly as a **law** `νD : Measure D` on the
  target space (the tight Borel limit), matching the existing
  `AsymptoticStatistics.WeakConverges` law-formulation.

* **Real readout via the nonneg shift** (Option (a)). `E*` is only
  *subadditive*, so the naive `E*[f⁺] − E*[f⁻]` split is invalid. Instead, for
  `f : D →ᵇ ℝ` set `M := ‖f‖`; then `f (Xₙ ω) + M ≥ 0` pointwise (from
  `BoundedContinuousFunction.norm_coe_le_norm`), so
  `ENNReal.ofReal (f (Xₙ ω) + ‖f‖)` is a genuine `ℝ≥0∞`-valued integrand and
  the readout is
  `(E*[ofReal (f∘Xₙ + ‖f‖)]).toReal − ‖f‖ · (μₙ univ).toReal`.
  The subtraction is performed in `ℝ` *after* `.toReal`, avoiding `ℝ≥0∞`
  truncated subtraction.

## Main definitions

* `WeakConvergesOuter μ Xn νD` — weak convergence in outer expectation,
  notation `Xn ⇝ₒ[μ] νD` (scoped).

## Main results

* `weakConvergesOuter_of_measurable` — when each `Xₙ` is Borel measurable, the
  outer readout collapses to the ordinary integral and `⇝ₒ` is equivalent to
  the law-level `WeakConverges (fun n => (μ n).map (Xn n)) νD`.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-- **Weak convergence in outer expectation** (`⇝ₒ`). For a sequence of
(possibly non-measurable) maps `Xₙ : Ω → D` into a (pseudo)metric space `D`,
with measures `μₙ` on the common space `Ω`, convergence in law to the Borel law
`νD : Measure D` is: for every bounded continuous `f : D →ᵇ ℝ`, the shifted
outer-expectation readout converges to `∫ f dνD`.

The integrand `fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖)` is nonnegative
(`f (Xn n ω) ≥ -‖f‖`), so `E*` applies; subtracting `‖f‖ · (μₙ univ).toReal`
after `.toReal` undoes the shift in `ℝ`. (van der Vaart §18.1; van der
Vaart–Wellner Ch. 1.3.) -/
def WeakConvergesOuter {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
    [PseudoMetricSpace D]
    (μ : ℕ → Measure Ω) (Xn : ℕ → Ω → D) (νD : Measure D) : Prop :=
  ∀ f : D →ᵇ ℝ, Tendsto (fun n =>
      (outerExpectation (μ n) (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖))).toReal
        - ‖f‖ * (μ n Set.univ).toReal)
    atTop (𝓝 (∫ y, f y ∂νD))

@[inherit_doc]
scoped notation Xn " ⇝ₒ[" μ "] " νD => WeakConvergesOuter μ Xn νD

/-- **Measurable reduction.** When each `Xₙ` is Borel measurable, the
outer-expectation readout collapses to the ordinary integral, so `⇝ₒ` is
equivalent to ordinary weak convergence of the pushforward laws
`(μ n).map (Xn n)`.

For measurable `Xₙ`, `E*[g] = ∫⁻ g` (`outerExpectation_eq_lintegral`); the
lower integral pushes forward (`lintegral_map`); and on `D` the shifted
integrand `f + ‖f‖ ≥ 0` is a bounded continuous function whose
`(∫⁻ ofReal ·).toReal` equals `∫ ·` (`integral_eq_lintegral_of_nonneg_ae`).
Splitting `∫ (f + ‖f‖) = ∫ f + ‖f‖ · (νₙ univ).toReal` and using
`(νₙ univ) = (μₙ univ) = 1` (probability measures) cancels the shift, leaving
the readout equal to `∫ f d((μ n).map (Xn n))`. -/
theorem weakConvergesOuter_of_measurable {Ω D : Type*} [MeasurableSpace Ω]
    [MeasurableSpace D] [PseudoMetricSpace D] [OpensMeasurableSpace D]
    {μ : ℕ → Measure Ω} {Xn : ℕ → Ω → D} {νD : Measure D}
    [∀ n, IsProbabilityMeasure (μ n)] (hXn : ∀ n, Measurable (Xn n)) :
    WeakConvergesOuter μ Xn νD ↔
      WeakConverges (fun n => (μ n).map (Xn n)) νD := by
  -- The readout at each `n` equals `∫ f d((μ n).map (Xn n))`.
  have hreadout : ∀ (f : D →ᵇ ℝ) (n : ℕ),
      (outerExpectation (μ n)
          (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖))).toReal
        - ‖f‖ * (μ n Set.univ).toReal
        = ∫ y, f y ∂((μ n).map (Xn n)) := by
    intro f n
    -- The shifted bounded continuous function `g := f + ‖f‖ : D →ᵇ ℝ`.
    set g : D →ᵇ ℝ := f + BoundedContinuousFunction.const D ‖f‖ with hg
    have hg_apply : ∀ y, g y = f y + ‖f‖ := by
      intro y; simp [hg]
    -- `g ≥ 0` pointwise.
    have hg_nonneg : ∀ y, (0 : ℝ) ≤ g y := by
      intro y
      rw [hg_apply]
      have := (BoundedContinuousFunction.norm_coe_le_norm f y)
      -- `|f y| ≤ ‖f‖ ⇒ -‖f‖ ≤ f y ⇒ 0 ≤ f y + ‖f‖`.
      have := (abs_le.1 this).1
      linarith
    -- The integrand on `Ω`, and its measurability.
    have hmeas_comp : Measurable fun ω => g (Xn n ω) :=
      g.continuous.measurable.comp (hXn n)
    have hofReal_meas : Measurable fun ω => ENNReal.ofReal (g (Xn n ω)) :=
      ENNReal.measurable_ofReal.comp hmeas_comp
    -- `E*[ofReal (f∘Xn + ‖f‖)] = ∫⁻ ofReal (g ∘ Xn) = ∫⁻_D ofReal g d(map)`.
    have hstar : outerExpectation (μ n)
        (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖))
        = ∫⁻ y, ENNReal.ofReal (g y) ∂((μ n).map (Xn n)) := by
      have hfun : (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖))
          = fun ω => ENNReal.ofReal (g (Xn n ω)) := by
        funext ω; rw [hg_apply]
      rw [hfun, outerExpectation_eq_lintegral hofReal_meas]
      exact (lintegral_map
        (ENNReal.measurable_ofReal.comp g.continuous.measurable) (hXn n)).symm
    -- `(∫⁻_D ofReal g).toReal = ∫_D g` via the nonneg-ae integral identity.
    have hg_integrable : Integrable g ((μ n).map (Xn n)) :=
      haveI : IsProbabilityMeasure ((μ n).map (Xn n)) :=
        Measure.isProbabilityMeasure_map (hXn n).aemeasurable
      g.integrable _
    have htoReal : (∫⁻ y, ENNReal.ofReal (g y) ∂((μ n).map (Xn n))).toReal
        = ∫ y, g y ∂((μ n).map (Xn n)) := by
      rw [integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall hg_nonneg)
        g.continuous.measurable.aestronglyMeasurable]
    -- `∫_D g = ∫_D f + ‖f‖ · (νₙ univ).toReal`.
    haveI : IsProbabilityMeasure ((μ n).map (Xn n)) :=
      Measure.isProbabilityMeasure_map (hXn n).aemeasurable
    have hsplit : ∫ y, g y ∂((μ n).map (Xn n))
        = (∫ y, f y ∂((μ n).map (Xn n)))
          + ‖f‖ * ((μ n).map (Xn n) Set.univ).toReal := by
      have hf_int : Integrable f ((μ n).map (Xn n)) := f.integrable _
      have hc_int : Integrable (fun _ => ‖f‖) ((μ n).map (Xn n)) :=
        integrable_const _
      have hsumfun : (fun y => g y) = fun y => f y + ‖f‖ := by
        funext y; rw [hg_apply]
      rw [hsumfun, integral_add hf_int hc_int, integral_const]
      simp [Measure.real, mul_comm]
    -- Both `(μₙ univ).toReal` and `(νₙ univ).toReal` equal `1`.
    have hμ_univ : (μ n Set.univ).toReal = 1 := by
      simp
    have hν_univ : ((μ n).map (Xn n) Set.univ).toReal = 1 := by
      simp
    rw [hstar, htoReal, hsplit, hμ_univ, hν_univ]
    ring
  -- Conclude the equivalence by rewriting the readout sequence.
  constructor
  · intro h f
    have := h f
    simpa only [hreadout f] using this
  · intro h f
    have := h f
    simpa only [hreadout f] using this

/-- **`E*` subadditive readout-triangle bound** (theorem-agnostic outer-
expectation algebra). For a `Lip`-Lipschitz bounded continuous readout `f` and two
maps `X, Y : Ω → D`, the shifted outer-expectation readout of `f ∘ X` is bounded by
the readout of `f ∘ Y` plus `Lip · (E*[edist-error])`-style tail, using ONLY the
subadditivity of `E*` (`outerExpectation_add_le`) and monotonicity
(`outerExpectation_mono`) — never a `±`-split (`E*` is only subadditive, so
`E*[g] − E*[h]` has no sign control).

This is the core algebraic step of the ε/3 discretization assembly (vdV p.261): the
discretization error `‖X ω − Y ω‖` enters the readout only through a one-sided
subadditive majorant `f (X ω) + ‖f‖ ≤ (f (Y ω) + ‖f‖) + Lip · ‖X ω − Y ω‖`, whose
`E*` is `≤ E*[f∘Y + ‖f‖] + Lip · E*[error]`. Stated generically over
`outerExpectation`; concrete `D = LinfF F`, error `= ‖𝔾ₙ − π𝔾ₙ‖`, supplied at the
call site.

At call sites, `hmaj` is obtained from a Lipschitz bound for `f` and the metric
triangle inequality. -/
theorem outerExpectation_readout_triangle {Ω D : Type*} [MeasurableSpace Ω]
    [MeasurableSpace D] [PseudoMetricSpace D]
    (μ : Measure Ω) (f : D →ᵇ ℝ) (X Y : Ω → D) (Lip : ℝ) (err : Ω → ℝ≥0∞)
    (hmaj : ∀ ω, ENNReal.ofReal (f (X ω) + ‖f‖)
        ≤ ENNReal.ofReal (f (Y ω) + ‖f‖) + ENNReal.ofReal Lip * err ω) :
    outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))
      ≤ outerExpectation μ (fun ω => ENNReal.ofReal (f (Y ω) + ‖f‖))
        + ENNReal.ofReal Lip * outerExpectation μ err := by
  classical
  -- Abbreviations for the three integrands.
  set b : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (f (Y ω) + ‖f‖) with hb
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal Lip * err ω with hg
  -- Step 1: pass the pointwise majorant through `E*` (monotonicity).
  have hmono : outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))
      ≤ outerExpectation μ (b + g) := by
    refine outerExpectation_mono ?_
    intro ω
    simpa [hb, hg, Pi.add_apply] using hmaj ω
  -- Step 2: subadditivity splits `E*[b + g] ≤ E*[b] + E*[g]`.
  have hadd : outerExpectation μ (b + g)
      ≤ outerExpectation μ b + outerExpectation μ g :=
    outerExpectation_add_le b g
  -- Step 3: the scaled term `g = (ofReal Lip) • err`.
  have hsmul : outerExpectation μ g
      = ENNReal.ofReal Lip * outerExpectation μ err := by
    have hg' : g = (ENNReal.ofReal Lip) • err := by
      funext ω; simp [hg, Pi.smul_apply, smul_eq_mul]
    rw [hg', outerExpectation_const_smul _ ENNReal.ofReal_ne_top, smul_eq_mul]
  calc
    outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))
        ≤ outerExpectation μ (b + g) := hmono
    _ ≤ outerExpectation μ b + outerExpectation μ g := hadd
    _ = outerExpectation μ (fun ω => ENNReal.ofReal (f (Y ω) + ‖f‖))
          + ENNReal.ofReal Lip * outerExpectation μ err := by rw [hsmul]

end AsymptoticStatistics
