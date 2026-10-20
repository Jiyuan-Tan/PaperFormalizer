module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.Outer
public import StatLean.AsymptoticStatistics.ForMathlib.OuterIntegration.OuterExpectation
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

/-!
# Asymptotic tightness in outer probability (`⇝ₒ`-Prohorov, easy direction)

The **asymptotic-tightness** half of the outer-Prohorov correspondence (van der
Vaart, *Asymptotic Statistics* Theorem 18.12; van der Vaart–Wellner, *Weak
Convergence and Empirical Processes*, §1.5.7). For a sequence of (possibly
non-measurable) maps `Xₙ : Ω → D` into a (pseudo)metric space `D`, with measures
`μₙ` on the common space `Ω`, *asymptotic tightness* asks that for every `ε > 0`
there is a compact set `K ⊆ D` whose `δ`-thickenings `Kᵟ` eventually
outer-capture all but `ε` of the mass of `Xₙ`, uniformly along the sequence (in
the `limsup` sense).

This file is **theorem-agnostic** (generic pseudometric `D`); it depends only on
the outer-expectation primitives (`outerMeasureStar`, `outerExpectation`) and the
weak-convergence-in-outer-expectation predicate `WeakConvergesOuter`. It does NOT
import any empirical-process material — it is `ForMathlib`-layer infrastructure.

## Main definitions

* `IsAsymptoticallyTight μ Xn` — asymptotic tightness of `Xₙ` in outer
  probability: a compact `K` whose thickenings outer-capture all but `ε`.

## Main results

* `MeasureTheory.outerExpectation_add_const` — exact constant-shift identity for
  the outer expectation (`E*[A + c] = E*[A] + c·μ univ`, `c ≠ ⊤`).
* `limsup_outerMeasureStar_preimage_isClosed_le` — the closed-set
  outer-portmanteau inequality: for `Xₙ ⇝ₒ νD` (finite `μₙ`, `νD`) and closed
  `C`, `limsup (μ n)* (Xₙ ⁻¹ C) ≤ νD C`.
* `isAsymptoticallyTight_of_weakConvergesOuter` — the easy-Prohorov direction:
  weak convergence in outer expectation to a tight Borel limit `νD` implies
  asymptotic tightness (vdV 18.12 ⟸).
* `limsup_outerMeasureStar_preimage_isClosed_le_of_lipschitz` — the closed-set
  outer-portmanteau inequality from a **Lipschitz-only** readout hypothesis.
* `weakConvergesOuter_of_lipschitz_readout` — bounded-Lipschitz ⟹ bounded-continuous
  outer portmanteau: convergence of the outer readout against all bounded Lipschitz
  test functions upgrades to full `WeakConvergesOuter` in the setting of vdV
  Theorem 18.12.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Theorem
18.12; van der Vaart–Wellner §1.5.7.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace MeasureTheory

/-- **Exact constant-shift identity for outer expectation.** For a finite
constant `c ≠ ⊤`, shifting the integrand by `c` shifts the outer expectation by
`c · μ univ`. Unlike subadditivity (`outerExpectation_add_le`), this is an
*equality*: majorants `U ≥ A + c` correspond bijectively to majorants `U - c ≥ A`
(subtracting `c` preserves measurability, and `U - c ≥ A ≥ 0` is genuine since
`U ≥ c`), and `∫⁻ U = ∫⁻ (U - c) + c · μ univ`. -/
theorem outerExpectation_add_const {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (A : Ω → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    outerExpectation μ (fun ω => A ω + c) = outerExpectation μ A + c * μ Set.univ := by
  refine le_antisymm ?_ ?_
  · -- `≤` : every majorant `U ≥ A` gives the majorant `U + c ≥ A + c`.
    rw [outerExpectation]
    -- Pull the `+ c·μ univ` into the RHS infimum via `ENNReal.iInf_add`.
    rw [show outerExpectation μ A + c * μ Set.univ
        = ⨅ U : {U : Ω → ℝ≥0∞ // Measurable U ∧ A ≤ U},
            (∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ + c * μ Set.univ) from by
      rw [outerExpectation, ENNReal.iInf_add]]
    refine le_iInf fun U => ?_
    -- `U + c` is a measurable majorant of `A + c`, with `∫⁻ (U + c) = ∫⁻ U + c·μ univ`.
    refine le_trans (iInf_le _
      (⟨fun ω => (U : Ω → ℝ≥0∞) ω + c, U.2.1.add_const c,
        fun ω => by simp only; gcongr; exact U.2.2 ω⟩ :
        {V : Ω → ℝ≥0∞ // Measurable V ∧ (fun ω => A ω + c) ≤ V})) ?_
    simp only
    rw [lintegral_add_right _ measurable_const, lintegral_const]
  · -- `≥` : every majorant `U ≥ A + c` gives the majorant `U - c ≥ A`.
    -- Goal: `outerExpectation μ A + c·μ univ ≤ outerExpectation μ (A + c)`.
    conv_rhs => rw [outerExpectation]
    refine le_iInf fun U => ?_
    -- `U - c` is a measurable majorant of `A` (since `U ≥ A + c ≥ c`).
    have hUc_meas : Measurable (fun ω => (U : Ω → ℝ≥0∞) ω - c) := U.2.1.sub_const c
    have hUc_maj : A ≤ fun ω => (U : Ω → ℝ≥0∞) ω - c := by
      intro ω
      have hU : A ω + c ≤ (U : Ω → ℝ≥0∞) ω := U.2.2 ω
      -- `A ω + c ≤ U ω` ⟹ `A ω ≤ U ω - c`.
      change A ω ≤ (U : Ω → ℝ≥0∞) ω - c
      exact ENNReal.le_sub_of_add_le_right hc hU
    -- `outerExpectation A ≤ ∫⁻ (U - c)`, then `∫⁻ (U - c) + c·μ univ = ∫⁻ U`.
    calc outerExpectation μ A + c * μ Set.univ
        ≤ (∫⁻ ω, ((U : Ω → ℝ≥0∞) ω - c) ∂μ) + c * μ Set.univ :=
          add_le_add (iInf_le (fun V : {V : Ω → ℝ≥0∞ // Measurable V ∧ A ≤ V} =>
            ∫⁻ ω, (V : Ω → ℝ≥0∞) ω ∂μ)
            ⟨fun ω => (U : Ω → ℝ≥0∞) ω - c, hUc_meas, hUc_maj⟩) le_rfl
      _ = ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ := by
          rw [← lintegral_const c, ← lintegral_add_right _ measurable_const]
          refine lintegral_congr fun ω => ?_
          rw [tsub_add_cancel_of_le (le_trans le_add_self (U.2.2 ω))]

end MeasureTheory

namespace AsymptoticStatistics

/-- **Asymptotic tightness in outer probability.** For a sequence of (possibly
non-measurable) maps `Xₙ : Ω → D` into a pseudometric space `D` with measures
`μₙ` on the common space `Ω`: for every `ε > 0` there is a compact `K ⊆ D` such
that for every thickening radius `δ > 0` the outer-probability mass that `Xₙ`
places *outside* the `δ`-thickening `Kᵟ = Metric.thickening δ K` is, in the
`limsup` along `atTop`, at most `ε`.

This is the van der Vaart–Wellner asymptotic-tightness condition (§1.5.7,
Theorem 18.12): the "outer-probability Prohorov" tightness that pairs with weak
convergence in outer expectation. The outer mass is read through
`Measure.outerMeasureStar` (`P*(A) = E*[1_A]`) since `Xₙ` need not be Borel
measurable. (vdV §18.1 / 18.12.)

Constitutive (vdV §18.1 / 18.12): the thickening `Kᵟ` and the `limsup`-uniform
`≤ ε` bound are the definition of asymptotic tightness; weakening either yields a
different (non-Prohorov) notion. -/
def IsAsymptoticallyTight {Ω D : Type*} [MeasurableSpace Ω] [PseudoMetricSpace D]
    (μ : ℕ → Measure Ω) (Xn : ℕ → Ω → D) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : Set D, IsCompact K ∧
    ∀ δ : ℝ, 0 < δ →
      limsup (fun n => (μ n).outerMeasureStar
          (Xn n ⁻¹' (Metric.thickening δ K)ᶜ)) atTop
        ≤ ENNReal.ofReal ε

/-- **Closed-set outer-portmanteau** (the upper-semicontinuity half). For weak
convergence in outer expectation `Xₙ ⇝ₒ νD` and a **closed** set `C ⊆ D`, the
outer mass that `Xₙ` places on `C` has `limsup` along `atTop` bounded by the
limit mass `νD C`:

`limsup (fun n => (μ n)* (Xₙ ⁻¹ C)) ≤ νD C`.

This is the outer-probability analogue of the portmanteau theorem's
closed-set inequality (van der Vaart §18.1; van der Vaart–Wellner §1.3). The
proof Urysohn-sandwiches `1_C` from above by the bounded continuous
approximating sequence `gₖ ↓ 1_C` (`IsClosed.apprSeq`, coerced to `D →ᵇ ℝ`):
`(μ n)* (Xₙ ⁻¹ C) ≤ E*[ofReal (gₖ ∘ Xₙ)]`, the latter equals the `⇝ₒ` readout
`ofReal (R(gₖ, n))` (via the exact constant-shift `outerExpectation_add_const`,
the `μₙ`-mass cancelling), so the `limsup` is `≤ ofReal (∫ gₖ dνD)`; letting
`k → ∞` (`tendsto_lintegral_apprSeq`) drives `∫ gₖ dνD ↓ νD C`.

Finiteness of `μₙ` and `νD` is genuinely required: for an infinite measure the
`.toReal`-readout degenerates and the bound is false (mass can escape to the
complement of every compact set). -/
theorem limsup_outerMeasureStar_preimage_isClosed_le {Ω D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace D] [PseudoMetricSpace D]
    [OpensMeasurableSpace D] {μ : ℕ → Measure Ω} {Xn : ℕ → Ω → D} {νD : Measure D}
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure νD]
    (h : WeakConvergesOuter μ Xn νD) {C : Set D} (hC : IsClosed C) :
    limsup (fun n => (μ n).outerMeasureStar (Xn n ⁻¹' C)) atTop ≤ νD C := by
  -- The bounded continuous approximating sequence `gₖ ↓ 1_C`, coerced to `ℝ`.
  set g : ℕ → (D →ᵇ ℝ) := fun k =>
    (hC.apprSeq k).comp _ NNReal.isometry_coe.lipschitz with hg
  have hg_apply : ∀ k x, g k x = (hC.apprSeq k x : ℝ) := fun k x => rfl
  have hg_nonneg : ∀ k x, (0 : ℝ) ≤ g k x := fun k x => by
    rw [hg_apply]; positivity
  have hg_le_one : ∀ k x, g k x ≤ 1 := fun k x => by
    rw [hg_apply]; exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hC k x
  -- `‖g k‖ ≤ 1`.
  have hg_norm_le : ∀ k, ‖g k‖ ≤ 1 := by
    intro k
    rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hg_nonneg k x], hg_le_one k x⟩
  -- Step 1 : for each `k, n`, `(μ n)* (Xₙ⁻¹ C) ≤ E*[ofReal (g k ∘ Xₙ)]`.
  have hstep1 : ∀ k n, (μ n).outerMeasureStar (Xn n ⁻¹' C)
      ≤ outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω))) := by
    intro k n
    rw [Measure.outerMeasureStar]
    refine outerExpectation_mono fun ω => ?_
    -- `1_{Xₙ⁻¹C}(ω) ≤ ofReal (g k (Xₙ ω))`.
    by_cases hω : Xn n ω ∈ C
    · -- On `C`, `g k (Xₙ ω) ≥ 1`, so `ofReal (g k …) ≥ 1`.
      have h1 : (1 : ℝ) ≤ g k (Xn n ω) := by
        rw [hg_apply]
        have := HasOuterApproxClosed.apprSeq_apply_eq_one hC k hω
        rw [this]; norm_num
      simp only [Set.mem_preimage.2 hω, Set.indicator_of_mem, Pi.one_apply]
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal h1
    · have hω' : ω ∉ Xn n ⁻¹' C := by simpa using hω
      simp [Set.indicator_of_notMem hω']
  -- Step 2 : `E*[ofReal (g k ∘ Xₙ)] = ofReal (R(g k, n))` (the `⇝ₒ` readout).
  -- abbreviation for the readout sequence.
  set R : ℕ → ℕ → ℝ := fun k n =>
    (outerExpectation (μ n)
        (fun ω => ENNReal.ofReal (g k (Xn n ω) + ‖g k‖))).toReal
      - ‖g k‖ * (μ n Set.univ).toReal with hR
  -- `E*[ofReal (g k ∘ Xₙ)] ≤ μ n univ < ⊤` (integrand `≤ 1`).
  have hfin : ∀ k n,
      outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω))) ≤ μ n Set.univ := by
    intro k n
    calc outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω)))
        ≤ outerExpectation (μ n) (fun _ => 1) :=
          outerExpectation_mono fun ω => by
            rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
            exact ENNReal.ofReal_le_ofReal (hg_le_one k _)
      _ = μ n Set.univ := by rw [outerExpectation_const]; simp
  have hstep2 : ∀ k n,
      outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω)))
        = ENNReal.ofReal (R k n) := by
    intro k n
    -- `ofReal (g k ∘ Xₙ + ‖g k‖) = ofReal (g k ∘ Xₙ) + ofReal ‖g k‖`.
    have hsplit : (fun ω => ENNReal.ofReal (g k (Xn n ω) + ‖g k‖))
        = fun ω => ENNReal.ofReal (g k (Xn n ω)) + ENNReal.ofReal ‖g k‖ := by
      funext ω; rw [ENNReal.ofReal_add (hg_nonneg k _) (norm_nonneg _)]
    -- Exact constant-shift identity.
    have hshift : outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω) + ‖g k‖))
        = outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω)))
          + ENNReal.ofReal ‖g k‖ * μ n Set.univ := by
      rw [hsplit]; exact outerExpectation_add_const _ _ ENNReal.ofReal_ne_top
    -- Take `.toReal` of both sides; the shift cancels in `R`.
    have hμfin : μ n Set.univ ≠ ⊤ := measure_ne_top _ _
    have hEfin : outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω))) ≠ ⊤ :=
      ne_top_of_le_ne_top hμfin (hfin k n)
    simp only [hR]
    rw [hshift, ENNReal.toReal_add hEfin (by finiteness),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    rw [add_sub_cancel_right, ENNReal.ofReal_toReal hEfin]
  -- Step 3 : `limsup (μ n)* (Xₙ⁻¹ C) ≤ ofReal (∫ g k dνD)` for each `k`.
  have hstep3 : ∀ k, limsup (fun n => (μ n).outerMeasureStar (Xn n ⁻¹' C)) atTop
      ≤ ENNReal.ofReal (∫ y, g k y ∂νD) := by
    intro k
    -- `ofReal (R k ·) → ofReal (∫ g k dνD)`.
    have hRtendsto : Tendsto (fun n => ENNReal.ofReal (R k n)) atTop
        (𝓝 (ENNReal.ofReal (∫ y, g k y ∂νD))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (h (g k))
    -- the sequence is `≤ ofReal (R k n)` term-by-term.
    calc limsup (fun n => (μ n).outerMeasureStar (Xn n ⁻¹' C)) atTop
        ≤ limsup (fun n => ENNReal.ofReal (R k n)) atTop :=
          limsup_le_limsup (Eventually.of_forall fun n =>
            le_trans (hstep1 k n) (le_of_eq (hstep2 k n)))
      _ = ENNReal.ofReal (∫ y, g k y ∂νD) := hRtendsto.limsup_eq
  -- Step 4 : `∫ g k dνD → νD C`, so `limsup … ≤ νD C`.
  -- `ofReal (∫ g k dνD) → νD C` via `tendsto_lintegral_apprSeq`.
  have hlim : Tendsto (fun k => ∫⁻ y, (hC.apprSeq k y : ℝ≥0∞) ∂νD) atTop (𝓝 (νD C)) :=
    HasOuterApproxClosed.tendsto_lintegral_apprSeq hC νD
  have heq : ∀ k, ENNReal.ofReal (∫ y, g k y ∂νD)
      = ∫⁻ y, (hC.apprSeq k y : ℝ≥0∞) ∂νD := by
    intro k
    rw [ofReal_integral_eq_lintegral_ofReal
      (BoundedContinuousFunction.integrable νD (g k))
      (Eventually.of_forall fun y => hg_nonneg k y)]
    refine lintegral_congr fun y => ?_
    rw [hg_apply, ENNReal.ofReal_coe_nnreal]
  have hlim' : Tendsto (fun k => ENNReal.ofReal (∫ y, g k y ∂νD)) atTop (𝓝 (νD C)) := by
    simpa only [heq] using hlim
  exact ge_of_tendsto hlim' (Eventually.of_forall hstep3)

/-- **Closed-set limsup from a Lipschitz-only readout.** A weakening of
`limsup_outerMeasureStar_preimage_isClosed_le`: instead of the full
`WeakConvergesOuter` hypothesis (the readout converges for *every* bounded
continuous `f`), we only assume the readout converges for **bounded Lipschitz**
`f`. The conclusion is unchanged: for closed `C`,
`limsup (μ n)* (Xₙ ⁻¹ C) ≤ νD C`.

This works because the proof of the full version only ever evaluates the readout
at the Urysohn approximants `gₖ ↓ 1_C`; here we take those approximants to be the
**thickened indicators** `thickenedIndicator (1/(k+1)) C`, which are genuinely
bounded Lipschitz (`lipschitzWith_thickenedIndicator`). The `1/(k+1)`-thickening
radius shrinks to `0`, so `∫ gₖ dνD ↓ νD C` (`tendsto_lintegral_thickenedIndicator_of_isClosed`). -/
theorem limsup_outerMeasureStar_preimage_isClosed_le_of_lipschitz {Ω D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace D] [PseudoMetricSpace D]
    [OpensMeasurableSpace D] {μ : ℕ → Measure Ω} {Xn : ℕ → Ω → D} {νD : Measure D}
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure νD]
    (hlip : ∀ f : D →ᵇ ℝ, (∃ K, LipschitzWith K f) →
        Tendsto (fun n => (outerExpectation (μ n)
          (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖))).toReal
          - ‖f‖ * (μ n Set.univ).toReal) atTop (𝓝 (∫ y, f y ∂νD)))
    {C : Set D} (hC : IsClosed C) :
    limsup (fun n => (μ n).outerMeasureStar (Xn n ⁻¹' C)) atTop ≤ νD C := by
  -- The thickening radii `δ k = 1/(k+1) ↓ 0`.
  have hδ_pos : ∀ k : ℕ, (0 : ℝ) < 1 / (k + 1) := fun k => by positivity
  have hδ_lim : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- The bounded-Lipschitz approximating sequence `gₖ ↓ 1_C`, coerced to `ℝ`.
  set g : ℕ → (D →ᵇ ℝ) := fun k =>
    (thickenedIndicator (hδ_pos k) C).comp _ NNReal.isometry_coe.lipschitz with hg
  have hg_apply : ∀ k x, g k x = (thickenedIndicator (hδ_pos k) C x : ℝ) := fun k x => rfl
  -- Each `g k` is bounded Lipschitz.
  have hg_lip : ∀ k, ∃ K, LipschitzWith K (g k) := fun k =>
    ⟨1 * (1 / (k + 1 : ℝ)).toNNReal⁻¹,
      NNReal.isometry_coe.lipschitz.comp (lipschitzWith_thickenedIndicator (hδ_pos k) C)⟩
  have hg_nonneg : ∀ k x, (0 : ℝ) ≤ g k x := fun k x => by
    rw [hg_apply]; positivity
  have hg_le_one : ∀ k x, g k x ≤ 1 := fun k x => by
    rw [hg_apply]; exact_mod_cast thickenedIndicator_le_one (hδ_pos k) C x
  -- `‖g k‖ ≤ 1`.
  have hg_norm_le : ∀ k, ‖g k‖ ≤ 1 := by
    intro k
    rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hg_nonneg k x], hg_le_one k x⟩
  -- Step 1 : for each `k, n`, `(μ n)* (Xₙ⁻¹ C) ≤ E*[ofReal (g k ∘ Xₙ)]`.
  have hstep1 : ∀ k n, (μ n).outerMeasureStar (Xn n ⁻¹' C)
      ≤ outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω))) := by
    intro k n
    rw [Measure.outerMeasureStar]
    refine outerExpectation_mono fun ω => ?_
    by_cases hω : Xn n ω ∈ C
    · -- On `C`, `g k (Xₙ ω) ≥ 1`, so `ofReal (g k …) ≥ 1`.
      have h1 : (1 : ℝ) ≤ g k (Xn n ω) := by
        rw [hg_apply]
        exact_mod_cast one_le_thickenedIndicator_apply D (hδ_pos k) hω
      simp only [Set.mem_preimage.2 hω, Set.indicator_of_mem, Pi.one_apply]
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal h1
    · have hω' : ω ∉ Xn n ⁻¹' C := by simpa using hω
      simp [Set.indicator_of_notMem hω']
  -- Step 2 : `E*[ofReal (g k ∘ Xₙ)] = ofReal (R(g k, n))` (the `⇝ₒ` readout).
  set R : ℕ → ℕ → ℝ := fun k n =>
    (outerExpectation (μ n)
        (fun ω => ENNReal.ofReal (g k (Xn n ω) + ‖g k‖))).toReal
      - ‖g k‖ * (μ n Set.univ).toReal with hR
  have hfin : ∀ k n,
      outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω))) ≤ μ n Set.univ := by
    intro k n
    calc outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω)))
        ≤ outerExpectation (μ n) (fun _ => 1) :=
          outerExpectation_mono fun ω => by
            rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
            exact ENNReal.ofReal_le_ofReal (hg_le_one k _)
      _ = μ n Set.univ := by rw [outerExpectation_const]; simp
  have hstep2 : ∀ k n,
      outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω)))
        = ENNReal.ofReal (R k n) := by
    intro k n
    have hsplit : (fun ω => ENNReal.ofReal (g k (Xn n ω) + ‖g k‖))
        = fun ω => ENNReal.ofReal (g k (Xn n ω)) + ENNReal.ofReal ‖g k‖ := by
      funext ω; rw [ENNReal.ofReal_add (hg_nonneg k _) (norm_nonneg _)]
    have hshift : outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω) + ‖g k‖))
        = outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω)))
          + ENNReal.ofReal ‖g k‖ * μ n Set.univ := by
      rw [hsplit]; exact outerExpectation_add_const _ _ ENNReal.ofReal_ne_top
    have hμfin : μ n Set.univ ≠ ⊤ := measure_ne_top _ _
    have hEfin : outerExpectation (μ n) (fun ω => ENNReal.ofReal (g k (Xn n ω))) ≠ ⊤ :=
      ne_top_of_le_ne_top hμfin (hfin k n)
    simp only [hR]
    rw [hshift, ENNReal.toReal_add hEfin (by finiteness),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    rw [add_sub_cancel_right, ENNReal.ofReal_toReal hEfin]
  -- Step 3 : `limsup (μ n)* (Xₙ⁻¹ C) ≤ ofReal (∫ g k dνD)` for each `k`.
  have hstep3 : ∀ k, limsup (fun n => (μ n).outerMeasureStar (Xn n ⁻¹' C)) atTop
      ≤ ENNReal.ofReal (∫ y, g k y ∂νD) := by
    intro k
    have hRtendsto : Tendsto (fun n => ENNReal.ofReal (R k n)) atTop
        (𝓝 (ENNReal.ofReal (∫ y, g k y ∂νD))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hlip (g k) (hg_lip k))
    calc limsup (fun n => (μ n).outerMeasureStar (Xn n ⁻¹' C)) atTop
        ≤ limsup (fun n => ENNReal.ofReal (R k n)) atTop :=
          limsup_le_limsup (Eventually.of_forall fun n =>
            le_trans (hstep1 k n) (le_of_eq (hstep2 k n)))
      _ = ENNReal.ofReal (∫ y, g k y ∂νD) := hRtendsto.limsup_eq
  -- Step 4 : `∫ g k dνD → νD C`, so `limsup … ≤ νD C`.
  have hlim : Tendsto (fun k => ∫⁻ y, (thickenedIndicator (hδ_pos k) C y : ℝ≥0∞) ∂νD) atTop
      (𝓝 (νD C)) :=
    tendsto_lintegral_thickenedIndicator_of_isClosed νD hC hδ_pos hδ_lim
  have heq : ∀ k, ENNReal.ofReal (∫ y, g k y ∂νD)
      = ∫⁻ y, (thickenedIndicator (hδ_pos k) C y : ℝ≥0∞) ∂νD := by
    intro k
    rw [ofReal_integral_eq_lintegral_ofReal
      (BoundedContinuousFunction.integrable νD (g k))
      (Eventually.of_forall fun y => hg_nonneg k y)]
    refine lintegral_congr fun y => ?_
    rw [hg_apply, ENNReal.ofReal_coe_nnreal]
  have hlim' : Tendsto (fun k => ENNReal.ofReal (∫ y, g k y ∂νD)) atTop (𝓝 (νD C)) := by
    simpa only [heq] using hlim
  exact ge_of_tendsto hlim' (Eventually.of_forall hstep3)

/-- **Easy-Prohorov direction (vdV 18.12 ⟸).** Weak convergence in outer
expectation to a tight Borel limit law `νD` implies asymptotic tightness of the
sequence `Xₙ`.

Given `ε > 0`, take the compact `K` from tightness of `{νD}`
(`isTightMeasureSet_iff_exists_isCompact_measure_compl_le`) with `νD Kᶜ ≤ ε/2`,
then control `limsup (μ n)* (Xₙ ⁻¹ (Kᵟ)ᶜ)` by a portmanteau-style outer
lower-semicontinuity bound against the open thickening `Kᵟ` (whose complement is
closed): the outer mass of a closed-set preimage has `limsup ≤ νD` of that
closed set, which is `≤ νD Kᶜ + (thickening slack) ≤ ε`. Uses
`weakConvergesOuter_of_measurable` / the outer-portmanteau on closed sets.

The `OpensMeasurableSpace D` instance supplies the standard regularity making the
Borel structure agree with the metric topology for the portmanteau readout; `hνD` is the
tightness of the (genuine, Borel) limit measure supplied by the caller (a tight
limit always exists for a `⇝ₒ` limit in a Polish carrier). -/
theorem isAsymptoticallyTight_of_weakConvergesOuter {Ω D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace D] [PseudoMetricSpace D]
    [OpensMeasurableSpace D] {μ : ℕ → Measure Ω} {Xn : ℕ → Ω → D} {νD : Measure D}
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure νD]
    (h : WeakConvergesOuter μ Xn νD)
    (hνD : IsTightMeasureSet ({νD} : Set (Measure D))) :
    IsAsymptoticallyTight μ Xn := by
  intro ε hε
  -- Tightness of `{νD}`: a compact `K` with `νD Kᶜ ≤ ε/2`.
  obtain ⟨K, hK_compact, hK_mass⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hνD)
      (ENNReal.ofReal (ε / 2)) (by simp [hε])
  have hKmass : νD Kᶜ ≤ ENNReal.ofReal (ε / 2) := hK_mass νD rfl
  refine ⟨K, hK_compact, fun δ hδ => ?_⟩
  -- `(thickening δ K)ᶜ` is closed, with mass `≤ νD Kᶜ ≤ ε/2 ≤ ε`.
  have hclosed : IsClosed (Metric.thickening δ K)ᶜ := Metric.isOpen_thickening.isClosed_compl
  have hsubset : (Metric.thickening δ K)ᶜ ⊆ Kᶜ :=
    Set.compl_subset_compl.2 (Metric.self_subset_thickening hδ K)
  calc limsup (fun n => (μ n).outerMeasureStar
          (Xn n ⁻¹' (Metric.thickening δ K)ᶜ)) atTop
      ≤ νD (Metric.thickening δ K)ᶜ :=
        limsup_outerMeasureStar_preimage_isClosed_le h hclosed
    _ ≤ νD Kᶜ := measure_mono hsubset
    _ ≤ ENNReal.ofReal (ε / 2) := hKmass
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)

/-- **Monotonicity of the shifted outer readout in the function.** If `f₁ ≤ f₂`
pointwise then `R f₁ ≤ R f₂`, where `R f = (E*[ofReal (f∘X + ‖f‖)]).toReal − ‖f‖`
(probability measure, `(μ univ).toReal = 1`). The shift `‖f‖` differs between `f₁`
and `f₂`, so we pass through the **common** shift `M = ‖f₁‖ + ‖f₂‖`: re-shifting
each readout by `M` (`outerExpectation_add_const`) makes the integrands directly
comparable, and `E*` is monotone (`outerExpectation_mono`). -/
private theorem readout_mono {Ω D : Type*} [MeasurableSpace Ω]
    [MeasurableSpace D] [PseudoMetricSpace D] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f₁ f₂ : D →ᵇ ℝ) (X : Ω → D) (hle : ∀ x, f₁ x ≤ f₂ x) :
    (outerExpectation μ (fun ω => ENNReal.ofReal (f₁ (X ω) + ‖f₁‖))).toReal - ‖f₁‖
      ≤ (outerExpectation μ (fun ω => ENNReal.ofReal (f₂ (X ω) + ‖f₂‖))).toReal - ‖f₂‖ := by
  classical
  set M : ℝ := ‖f₁‖ + ‖f₂‖ with hM
  have hμ1 : (μ Set.univ).toReal = 1 := by simp
  have hreshift : ∀ (f : D →ᵇ ℝ), ‖f‖ ≤ M →
      (outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + M))).toReal
        = (outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))).toReal - ‖f‖ + M := by
    intro f hf
    have hsplit : (fun ω => ENNReal.ofReal (f (X ω) + M))
        = fun ω => ENNReal.ofReal (f (X ω) + ‖f‖) + ENNReal.ofReal (M - ‖f‖) := by
      funext ω
      rw [← ENNReal.ofReal_add (by have := (abs_le.1 (f.norm_coe_le_norm (X ω))).1; linarith)
        (by linarith)]
      congr 1; ring
    have hbound : outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))
        ≤ ENNReal.ofReal (2 * ‖f‖) := by
      calc outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))
          ≤ outerExpectation μ (fun _ => ENNReal.ofReal (2 * ‖f‖)) :=
            outerExpectation_mono (fun ω => ENNReal.ofReal_le_ofReal (by
              have := (abs_le.1 (f.norm_coe_le_norm (X ω))).2; linarith))
        _ = ENNReal.ofReal (2 * ‖f‖) := by rw [outerExpectation_const]; simp
    have hEtop : outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
    rw [hsplit, outerExpectation_add_const _ _ ENNReal.ofReal_ne_top,
      ENNReal.toReal_add hEtop (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), hμ1, mul_one]
    ring
  have hf1M : ‖f₁‖ ≤ M := by rw [hM]; linarith [norm_nonneg f₂]
  have hf2M : ‖f₂‖ ≤ M := by rw [hM]; linarith [norm_nonneg f₁]
  -- Monotone `E*` at common shift `M`.
  have hf2_top : outerExpectation μ (fun ω => ENNReal.ofReal (f₂ (X ω) + M)) ≠ ⊤ := by
    have hb : outerExpectation μ (fun ω => ENNReal.ofReal (f₂ (X ω) + M))
        ≤ ENNReal.ofReal (‖f₂‖ + M) := by
      calc outerExpectation μ (fun ω => ENNReal.ofReal (f₂ (X ω) + M))
          ≤ outerExpectation μ (fun _ => ENNReal.ofReal (‖f₂‖ + M)) :=
            outerExpectation_mono (fun ω => ENNReal.ofReal_le_ofReal (by
              have := (abs_le.1 (f₂.norm_coe_le_norm (X ω))).2; linarith))
        _ = ENNReal.ofReal (‖f₂‖ + M) := by rw [outerExpectation_const]; simp
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hmono : (outerExpectation μ (fun ω => ENNReal.ofReal (f₁ (X ω) + M))).toReal
      ≤ (outerExpectation μ (fun ω => ENNReal.ofReal (f₂ (X ω) + M))).toReal :=
    ENNReal.toReal_mono hf2_top (outerExpectation_mono (fun ω =>
      ENNReal.ofReal_le_ofReal (by linarith [hle (X ω)])))
  rw [hreshift f₁ hf1M, hreshift f₂ hf2M] at hmono; linarith

/-- **Lipschitz regularization of a bounded continuous function from below.** For
`g : D →ᵇ ℝ` there is a sequence `gₘ` of bounded Lipschitz functions with
`‖gₘ‖ ≤ ‖g‖`, `gₘ ≤ g` pointwise, and `gₘ x → g x` for every `x`.

This is the **inf-convolution (Lipschitz/Moreau–Yosida) regularization from below**.
The imported Mathlib API does not supply this properness-free form, so the proof
uses the standard construction
`gₘ x = ⨅_y (g y + m · dist x y)`. Each `gₘ` is `m`-Lipschitz (a pointwise `inf` of
`m`-Lipschitz functions `y ↦ g y + m·dist · y`), bounded with `−‖g‖ ≤ gₘ ≤ g ≤ ‖g‖`
(`g y ≥ −‖g‖`, and taking `y = x` gives `gₘ x ≤ g x`), and `gₘ x ↑ g x` as
`m → ∞` for each fixed `x` because `g` is continuous at `x` (the penalty
`m · dist x y → ∞` confines the minimiser to a shrinking ball around `x`). Bundling
each `gₘ` as a `D →ᵇ ℝ` (it is bounded continuous) gives the claimed sequence. NB:
no compactness or properness of `D` is used, which is essential since the empirical
process carrier `ℓ∞(F)` is not proper. -/
theorem exists_lipschitz_approx_le {D : Type*} [PseudoMetricSpace D]
    (g : D →ᵇ ℝ) :
    ∃ gm : ℕ → (D →ᵇ ℝ), (∀ m, ∃ K, LipschitzWith K (gm m)) ∧
      (∀ m, ‖gm m‖ ≤ ‖g‖) ∧ (∀ m x, gm m x ≤ g x) ∧
      (∀ x, Tendsto (fun m => gm m x) atTop (𝓝 (g x))) := by
  classical
  -- `g y ≥ -‖g‖` and `g y ≤ ‖g‖` for all `y`.
  have hg_lb : ∀ y, -‖g‖ ≤ g y := fun y => (abs_le.1 (g.norm_coe_le_norm y)).1
  have hg_ub : ∀ y, g y ≤ ‖g‖ := fun y => (abs_le.1 (g.norm_coe_le_norm y)).2
  -- The inf-convolution penalty function (raw, as a function `D → ℝ`).
  set F : ℕ → D → ℝ := fun m x => ⨅ y, (g y + (m : ℝ) * dist x y) with hFdef
  -- For each `m, x`, the set `{g y + m·dist x y : y}` is bounded below by `-‖g‖`.
  have hbdd : ∀ (m : ℕ) (x : D), BddBelow (Set.range (fun y => g y + (m : ℝ) * dist x y)) := by
    intro m x
    refine ⟨-‖g‖, ?_⟩
    rintro _ ⟨y, rfl⟩
    have : (0 : ℝ) ≤ (m : ℝ) * dist x y := by positivity
    linarith [hg_lb y]
  -- `F m x ≤ g x` (take `y = x`).
  have hFle : ∀ (m : ℕ) (x : D), F m x ≤ g x := by
    intro m x
    have := ciInf_le_of_le (hbdd m x) x (by simp : g x + (m : ℝ) * dist x x ≤ g x)
    simpa [hFdef] using this
  -- `-‖g‖ ≤ F m x`.
  have hFlb : ∀ (m : ℕ) (x : D), -‖g‖ ≤ F m x := by
    intro m x
    haveI : Nonempty D := ⟨x⟩
    refine le_ciInf (fun y => ?_)
    have : (0 : ℝ) ≤ (m : ℝ) * dist x y := by positivity
    linarith [hg_lb y]
  -- One-sided `m`-Lipschitz estimate: `F m x ≤ F m x' + m·dist x x'`.
  have hFstep : ∀ (m : ℕ) (x x' : D), F m x ≤ F m x' + (m : ℝ) * dist x x' := by
    intro m x x'
    haveI : Nonempty D := ⟨x⟩
    -- `F m x' + m·dist x x' = (⨅ y, g y + m·dist x' y) + m·dist x x'`; bound `F m x` below it
    -- term-by-term: `F m x ≤ g y + m·dist x y ≤ (g y + m·dist x' y) + m·dist x x'`.
    rw [show F m x' = ⨅ y, g y + (m : ℝ) * dist x' y from rfl]
    refine le_ciInf_add (fun y => ?_)
    have htri : dist x y ≤ dist x' y + dist x x' := by
      rw [add_comm]; exact dist_triangle x x' y
    have hxy : F m x ≤ g y + (m : ℝ) * dist x y := by
      simpa [hFdef] using ciInf_le (hbdd m x) y
    have hpen : g y + (m : ℝ) * dist x y ≤ (g y + (m : ℝ) * dist x' y) + (m : ℝ) * dist x x' := by
      nlinarith [Nat.cast_nonneg (α := ℝ) m, htri]
    linarith
  -- `F m` is `m`-Lipschitz (two-sided, from the one-sided estimate).
  have hFlip : ∀ m : ℕ, LipschitzWith (m : ℝ≥0) (F m) := by
    intro m
    refine LipschitzWith.of_dist_le_mul (fun x x' => ?_)
    rw [Real.dist_eq, abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · have := hFstep m x x'; push_cast; linarith
    · have := hFstep m x' x; rw [dist_comm] at this; push_cast; linarith
  -- Bundle each `F m` as a bounded continuous function via `mkOfBound`.
  set gm : ℕ → (D →ᵇ ℝ) := fun m =>
    BoundedContinuousFunction.mkOfBound
      ⟨F m, (hFlip m).continuous⟩ (2 * ‖g‖) (fun x x' => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
        constructor
        · linarith [hFlb m x, hFle m x', hg_ub x']
        · linarith [hFle m x, hg_ub x, hFlb m x']) with hgmdef
  have hgm_apply : ∀ m x, gm m x = F m x := fun m x => rfl
  refine ⟨gm, ?_, ?_, ?_, ?_⟩
  · -- Lipschitz.
    exact fun m => ⟨(m : ℝ≥0), LipschitzWith.of_dist_le_mul (fun x x' => by
      rw [hgm_apply, hgm_apply]; exact (hFlip m).dist_le_mul x x')⟩
  · -- `‖gm m‖ ≤ ‖g‖`.
    intro m
    rw [BoundedContinuousFunction.norm_le (norm_nonneg g)]
    intro x
    rw [Real.norm_eq_abs, abs_le, hgm_apply]
    exact ⟨hFlb m x, le_trans (hFle m x) (hg_ub x)⟩
  · -- `gm m x ≤ g x`.
    intro m x; rw [hgm_apply]; exact hFle m x
  · -- Pointwise convergence `gm m x → g x`.
    intro x
    haveI : Nonempty D := ⟨x⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Work with `ε/2`: continuity gives `δ > 0` with `|g y - g x| < ε/2` for `dist y x < δ`,
    -- and we'll prove `g x - ε/2 ≤ F m x`, which yields `g x - F m x ≤ ε/2 < ε`.
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    have hgcont : Continuous (g : D → ℝ) := g.continuous
    rw [Metric.continuous_iff] at hgcont
    obtain ⟨δ, hδ, hδbd⟩ := hgcont x (ε / 2) hε2
    -- For `m` large the minimiser is confined to the `δ`-ball, where `g y > g x − ε/2`.
    -- Choose `m ≥ (2‖g‖ + ε/2) / δ` so `dist y x ≥ δ ⟹ g y + m·dist x y ≥ g x − ε/2`.
    obtain ⟨N, hN⟩ := exists_nat_ge ((2 * ‖g‖ + ε / 2) / δ)
    refine ⟨N, fun m hm => ?_⟩
    rw [Real.dist_eq, abs_sub_lt_iff]
    refine ⟨?_, ?_⟩
    · -- `gm m x - g x < ε`: follows from `F m x ≤ g x`.
      rw [hgm_apply]; linarith [hFle m x]
    · -- `g x - gm m x < ε`: show `g x - ε/2 ≤ g y + m·dist x y` for all `y`.
      have hge : g x - ε / 2 ≤ F m x := by
        refine le_ciInf (fun y => ?_)
        by_cases hyx : dist x y < δ
        · -- close: continuity gives `g y > g x − ε/2`.
          have hlt : |g y - g x| < ε / 2 := by
            have hyx' : dist y x < δ := by rwa [dist_comm] at hyx
            simpa [Real.dist_eq] using hδbd y hyx'
          have hgt : g x - ε / 2 < g y := by
            have := (abs_lt.1 hlt).1; linarith
          have hpos : (0 : ℝ) ≤ (m : ℝ) * dist x y := by positivity
          linarith
        · -- far: penalty `m·dist x y ≥ m·δ` dominates.
          rw [not_lt] at hyx
          have hmδ : (2 * ‖g‖ + ε / 2) ≤ (m : ℝ) * dist x y := by
            have h1 : (2 * ‖g‖ + ε / 2) / δ ≤ (m : ℝ) := le_trans hN (by exact_mod_cast hm)
            have h2 : (2 * ‖g‖ + ε / 2) ≤ (m : ℝ) * δ := by
              rw [div_le_iff₀ hδ] at h1; linarith
            have h3 : (m : ℝ) * δ ≤ (m : ℝ) * dist x y :=
              mul_le_mul_of_nonneg_left hyx (Nat.cast_nonneg m)
            linarith
          -- `g y ≥ -‖g‖`, so `g y + m·dist x y ≥ -‖g‖ + 2‖g‖ + ε/2 = ‖g‖ + ε/2 ≥ g x - ε/2`.
          have := hg_lb y
          have := hg_ub x
          linarith
      rw [hgm_apply]; linarith

/-- **Bounded-Lipschitz ⟹ bounded-continuous outer portmanteau** (vdV Theorem
18.12). If the outer-expectation readout converges to `∫ f dνD` for every
*bounded Lipschitz* `f : D →ᵇ ℝ`, then the readout converges for every *bounded
continuous* `f`, i.e. `Xₙ ⇝ₒ νD`.

This upgrades a "tested only against bounded Lipschitz functions" hypothesis to full
weak convergence in outer expectation. The mechanism is the **inf-convolution
sandwich** (properness-free, valid on any pseudometric `D`): an arbitrary bounded
continuous `g` is squeezed between Lipschitz regularizations from below and above,
`gₘ ↑ g` and `Gₘ ↓ g` pointwise (`exists_lipschitz_approx_le`, applied to `g` and
`−g`), each a bounded Lipschitz `D →ᵇ ℝ`. The readout `R f n` is monotone in `f`
(common-shift `E*`-monotonicity argument, `readout_mono`), so
`R(gₘ,n) ≤ R(g,n) ≤ R(Gₘ,n)`; `hlip` makes the outer ends
converge to `∫ gₘ dνD` and `∫ Gₘ dνD`, which by dominated convergence both tend to
`∫ g dνD`. Hence `∫ g dνD ≤ liminfₙ R(g,n) ≤ limsupₙ R(g,n) ≤ ∫ g dνD`.
No tightness or properness assumption is required, so this applies to the
non-proper carrier `ℓ∞(F)`. -/
theorem weakConvergesOuter_of_lipschitz_readout {Ω D : Type*} [MeasurableSpace Ω]
    [MeasurableSpace D] [PseudoMetricSpace D] [OpensMeasurableSpace D]
    {μ : ℕ → Measure Ω} {Xn : ℕ → Ω → D} {νD : Measure D}
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure νD]
    (hlip : ∀ f : D →ᵇ ℝ, (∃ K, LipschitzWith K f) →
        Tendsto (fun n => (outerExpectation (μ n)
          (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖))).toReal
          - ‖f‖ * (μ n Set.univ).toReal) atTop (𝓝 (∫ y, f y ∂νD))) :
    WeakConvergesOuter μ Xn νD := by
  classical
  intro g
  -- Suppress the `(μ n univ).toReal = 1` factor in the goal.
  simp_rw [show ∀ n, (μ n Set.univ).toReal = 1 from fun n => by simp, mul_one]
  -- The shifted outer readout.
  set R : (D →ᵇ ℝ) → ℕ → ℝ := fun f n =>
    (outerExpectation (μ n) (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖))).toReal - ‖f‖
    with hRdef
  -- `hlip` in readout form (the `‖f‖·1` shift identified with `‖f‖`).
  have hlipR : ∀ f : D →ᵇ ℝ, (∃ K, LipschitzWith K f) →
      Tendsto (fun n => R f n) atTop (𝓝 (∫ y, f y ∂νD)) := by
    intro f hf
    have := hlip f hf
    simpa only [hRdef, (by simp : ∀ n, (μ n Set.univ).toReal = 1), mul_one] using this
  -- Readout monotone in the function: `f₁ ≤ f₂ → R f₁ ≤ R f₂`.
  have hRmono : ∀ (f₁ f₂ : D →ᵇ ℝ) n, (∀ x, f₁ x ≤ f₂ x) → R f₁ n ≤ R f₂ n := by
    intro f₁ f₂ n hle
    simpa only [hRdef] using readout_mono (μ n) f₁ f₂ (Xn n) hle
  -- DCT helper: a sequence of `D →ᵇ ℝ` bounded by `‖g‖`, tending pointwise to `F`,
  -- has its `νD`-integrals tending to `∫ F dνD`.
  have hDCT : ∀ (fm : ℕ → (D →ᵇ ℝ)) (F : D →ᵇ ℝ), (∀ m x, |fm m x| ≤ ‖g‖) →
      (∀ x, Tendsto (fun m => fm m x) atTop (𝓝 (F x))) →
      Tendsto (fun m => ∫ y, fm m y ∂νD) atTop (𝓝 (∫ y, F y ∂νD)) := by
    intro fm F hbd hptw
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
      (fun m => (fm m).continuous.aestronglyMeasurable)
      (integrable_const _) ?_ ?_
    · intro m
      exact Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hbd m x)
    · exact Eventually.of_forall (fun x => hptw x)
  -- Lower (inf-convolution) approximants `gm ↑ g`.
  obtain ⟨gm, hgm_lip, hgm_norm, hgm_le, hgm_tendsto⟩ := exists_lipschitz_approx_le g
  -- Upper approximants `Gm = −((−g)m) ↓ g`, from the lower approximants of `−g`.
  obtain ⟨Gm', hGm'_lip, hGm'_norm, hGm'_le, hGm'_tendsto⟩ := exists_lipschitz_approx_le (-g)
  set Gm : ℕ → (D →ᵇ ℝ) := fun m => -(Gm' m) with hGmdef
  -- Pointwise/norm facts for the upper approximants.
  have hGm_ge : ∀ m x, g x ≤ Gm m x := by
    intro m x
    have := hGm'_le m x
    simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply] at this ⊢
    simp only [hGmdef, BoundedContinuousFunction.coe_neg, Pi.neg_apply]; linarith
  have hGm_norm : ∀ m, ‖Gm m‖ ≤ ‖g‖ := by
    intro m; simp only [hGmdef, norm_neg]
    simpa only [norm_neg] using hGm'_norm m
  have hGm_lip : ∀ m, ∃ K, LipschitzWith K (Gm m) := by
    intro m; obtain ⟨K, hK⟩ := hGm'_lip m
    exact ⟨K, by simpa only [hGmdef] using! hK.neg⟩
  have hGm_tendsto : ∀ x, Tendsto (fun m => Gm m x) atTop (𝓝 (g x)) := by
    intro x
    have := (hGm'_tendsto x).neg
    simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply, neg_neg] at this
    simpa only [hGmdef, BoundedContinuousFunction.coe_neg, Pi.neg_apply] using this
  -- Norm bounds give `|gm m x| ≤ ‖g‖` and `|Gm m x| ≤ ‖g‖`.
  have hgm_abs : ∀ m x, |gm m x| ≤ ‖g‖ := fun m x => by
    have := (gm m).norm_coe_le_norm x; rw [Real.norm_eq_abs] at this
    exact le_trans this (hgm_norm m)
  have hGm_abs : ∀ m x, |Gm m x| ≤ ‖g‖ := fun m x => by
    have := (Gm m).norm_coe_le_norm x; rw [Real.norm_eq_abs] at this
    exact le_trans this (hGm_norm m)
  -- `∫ gm m dνD → ∫ g dνD` and `∫ Gm m dνD → ∫ g dνD` (DCT).
  have hint_gm : Tendsto (fun m => ∫ y, gm m y ∂νD) atTop (𝓝 (∫ y, g y ∂νD)) :=
    hDCT gm g hgm_abs hgm_tendsto
  have hint_Gm : Tendsto (fun m => ∫ y, Gm m y ∂νD) atTop (𝓝 (∫ y, g y ∂νD)) :=
    hDCT Gm g hGm_abs hGm_tendsto
  -- Boundedness of the readout `R g · ∈ [−‖g‖, ‖g‖]` (for liminf/limsup machinery).
  have hRg_bdd : ∀ n, |R g n| ≤ ‖g‖ := by
    intro n
    have hle : outerExpectation (μ n) (fun ω => ENNReal.ofReal (g (Xn n ω) + ‖g‖))
        ≤ ENNReal.ofReal (2 * ‖g‖) := by
      calc outerExpectation (μ n) (fun ω => ENNReal.ofReal (g (Xn n ω) + ‖g‖))
          ≤ outerExpectation (μ n) (fun _ => ENNReal.ofReal (2 * ‖g‖)) :=
            outerExpectation_mono (fun ω => ENNReal.ofReal_le_ofReal (by
              have := (abs_le.1 (g.norm_coe_le_norm (Xn n ω))).2; linarith))
        _ = ENNReal.ofReal (2 * ‖g‖) := by rw [outerExpectation_const]; simp
    have htop : outerExpectation (μ n) (fun ω => ENNReal.ofReal (g (Xn n ω) + ‖g‖)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    have hle' : (outerExpectation (μ n)
        (fun ω => ENNReal.ofReal (g (Xn n ω) + ‖g‖))).toReal ≤ 2 * ‖g‖ := by
      rw [show (2 * ‖g‖) = (ENNReal.ofReal (2 * ‖g‖)).toReal from
        (ENNReal.toReal_ofReal (by positivity)).symm]
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    have hnn := ENNReal.toReal_nonneg
      (a := outerExpectation (μ n) (fun ω => ENNReal.ofReal (g (Xn n ω) + ‖g‖)))
    rw [hRdef, abs_le]; exact ⟨by linarith, by linarith⟩
  have hRg_isBdd : IsBoundedUnder (· ≤ ·) atTop (R g) :=
    isBoundedUnder_of ⟨‖g‖, fun n => le_trans (le_abs_self _) (hRg_bdd n)⟩
  have hRg_isBddGe : IsBoundedUnder (· ≥ ·) atTop (R g) :=
    isBoundedUnder_of ⟨-‖g‖, fun n => by
      have := (abs_le.1 (hRg_bdd n)).1; exact this⟩
  -- Lower bound: `∫ g dνD ≤ liminfₙ R g n`. For each `m`,
  -- `∫ gm m dνD = limₙ R (gm m) n ≤ liminfₙ R g n`; let `m → ∞`.
  have hlower : (∫ y, g y ∂νD) ≤ liminf (R g) atTop := by
    refine le_of_tendsto hint_gm (Eventually.of_forall fun m => ?_)
    have h1 : Tendsto (R (gm m)) atTop (𝓝 (∫ y, gm m y ∂νD)) := hlipR (gm m) (hgm_lip m)
    calc ∫ y, gm m y ∂νD = liminf (R (gm m)) atTop := h1.liminf_eq.symm
      _ ≤ liminf (R g) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => hRmono (gm m) g n (fun x => hgm_le m x))
          h1.isBoundedUnder_ge hRg_isBdd.isCoboundedUnder_ge
  -- Upper bound: `limsupₙ R g n ≤ ∫ g dνD`. For each `m`,
  -- `limsupₙ R g n ≤ limₙ R (Gm m) n = ∫ Gm m dνD`; let `m → ∞`.
  have hupper : limsup (R g) atTop ≤ ∫ y, g y ∂νD := by
    refine ge_of_tendsto hint_Gm (Eventually.of_forall fun m => ?_)
    have h1 : Tendsto (R (Gm m)) atTop (𝓝 (∫ y, Gm m y ∂νD)) := hlipR (Gm m) (hGm_lip m)
    calc limsup (R g) atTop
        ≤ limsup (R (Gm m)) atTop :=
          limsup_le_limsup (Eventually.of_forall fun n => hRmono g (Gm m) n (fun x => hGm_ge m x))
            hRg_isBddGe.isCoboundedUnder_le h1.isBoundedUnder_le
      _ = ∫ y, Gm m y ∂νD := h1.limsup_eq
  -- Squeeze: `liminf ≥ ∫ g ≥ limsup ≥ liminf`, so `R g → ∫ g dνD`.
  exact tendsto_of_le_liminf_of_limsup_le hlower hupper hRg_isBdd hRg_isBddGe

end AsymptoticStatistics
