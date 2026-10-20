module
public import StatLean.AsymptoticStatistics.Core.Hilbert
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Likelihood-ratio factorisation under `Pⁿ`

This file proves the **likelihood-ratio factorisation** of the integral against
the perturbed product measure `Pⁿ_g := Measure.pi (fun _ => (γ g).curve t)`. For
any nonneg measurable integrand `f`,

    `∫⁻ X, f X ∂Pⁿ_g = ∫⁻ X, f X · L_{n,g}(X) ∂Pⁿ`,

where `L_{n,g}(X) := ∏ⱼ (d (γ g).curve t / d P)(X j)` is the per-`X`
likelihood ratio along the QMD path `γ g`.

## Hypothesis: per-coordinate absolute continuity

The factorisation takes a hypothesis `(γ.curve t) ≪ P` (vdV §25.6, LAN
regularity). The structure-level `QMDPath.curve_absContinuous` gives
`(γ.curve t) ≪ γ.dominating`, and `curve_at_zero` gives `P ≪ γ.dominating`, but
neither implies `(γ.curve t) ≪ P` without an extra full-support assumption on `P`
w.r.t. `γ.dominating`. The downstream consumer typically picks QMD paths whose
`dominating` is `P` itself; in that case the hypothesis is automatic via
`curve_absContinuous t`.

## Proof recipe

1. Define `L_n_g X := ∏ⱼ (γ.curve t).rnDeriv P (X j)`, measurable by
   `Measure.measurable_rnDeriv` + product on `Fin n`.
2. Establish the **measure equality**
       `Measure.pi (fun _ => γ.curve t)
         = (Measure.pi (fun _ => P)).withDensity L_n_g`
   via `Measure.pi_eq` (rectangle characterization). On a rectangle
   `univ.pi s` the RHS reduces, by `withDensity_apply` and a finite-
   product Tonelli (helper `lintegral_pi_finset_prod`), to
   `∏ⱼ ∫⁻ x in s_j, (γ.curve t).rnDeriv P x ∂P`, which equals
   `∏ⱼ (γ.curve t)(s_j)` by `setLIntegral_rnDeriv'` (using `hAC`).
3. Apply `lintegral_withDensity_eq_lintegral_mul` to convert the
   integral against `Pⁿ_g` to the integral against `Pⁿ` weighted by
   `L_n_g`, then transpose `*` to match the conclusion's `f X * L_n_g X`
   form.

## Headline declarations

`pi_curve_eq_pi_withDensity`, `lintegral_pi_curve_eq_lintegral_pi_lr`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace AsymptoticStatistics.LowerBounds.T7_AndersonClosure

namespace LRFactorization

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.QMDPath

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Finite-product Tonelli for `lintegral` against `Measure.pi`.**

For nonneg measurable `gⱼ : Ω → ℝ≥0∞` and σ-finite measures `μⱼ`
on a finite product `Fin n → Ω`,

    `∫⁻ X, ∏ⱼ gⱼ(X j) ∂(Measure.pi μ) = ∏ⱼ ∫⁻ x, gⱼ(x) ∂μⱼ`.

Proved by induction on `n` mirroring Mathlib's
`MeasureTheory.integral_fin_nat_prod_eq_prod` (Bochner version) using
`measurePreserving_piFinSuccAbove`, `MeasureTheory.lintegral_prod`, and
`MeasureTheory.lintegral_lintegral_mul`. -/
private lemma lintegral_pi_finset_prod :
    ∀ (n : ℕ) (μ : Fin n → Measure Ω) [∀ i, SigmaFinite (μ i)]
      (g : Fin n → Ω → ℝ≥0∞) (_ : ∀ i, Measurable (g i)),
      ∫⁻ X : Fin n → Ω, (∏ j : Fin n, g j (X j)) ∂Measure.pi μ
        = ∏ j : Fin n, ∫⁻ x, g j x ∂μ j := by
  intro n
  induction n with
  | zero =>
    intro μ _ g _hg
    -- `Fin 0 → Ω` is a singleton; `pi (Fin 0) μ` is a probability measure on it.
    haveI : IsProbabilityMeasure (Measure.pi μ) := ⟨by simp⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const, measure_univ,
      mul_one]
  | succ n IH =>
    intro μ _ g hg
    -- Mirror Mathlib's `integral_fin_nat_prod_eq_prod` (Bochner version).
    -- Step 1: Pull back along `(piFinSuccAbove μ 0).symm`.
    have hmp_symm := (MeasureTheory.measurePreserving_piFinSuccAbove μ 0).symm
    rw [← hmp_symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    -- Step 2: Unfold `e.symm (x, v) = Fin.cons x v` and split the prod over `Fin (n+1)`.
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    -- Step 3: Tonelli to nest the integrals, then `lintegral_lintegral_mul` to factor.
    rw [MeasureTheory.lintegral_prod _ (by
      refine Measurable.aemeasurable ?_
      exact ((hg 0).comp measurable_fst).mul
        (Finset.measurable_prod _ (fun i _ =>
          (hg _).comp ((measurable_pi_apply i).comp measurable_snd))))]
    -- Now: `∫⁻ x ∂μ 0, ∫⁻ v ∂(pi μ.succ), g 0 (x,v).1 * ∏ i, g i.succ ((x,v).2 i) = ...`.
    -- Provide the AEMeasurable hypothesis with the same shape as the integrand.
    have hg_succ_prod_meas :
        Measurable (fun y : Fin n → Ω => ∏ x : Fin n, g x.succ (y x)) :=
      Finset.measurable_prod _ (fun i _ =>
        (hg _).comp (measurable_pi_apply i))
    rw [MeasureTheory.lintegral_lintegral_mul (hg 0).aemeasurable
        hg_succ_prod_meas.aemeasurable]
    -- Step 4: Apply IH on the inner pi-integral. This closes the goal modulo
    -- a final `Fin.prod_univ_succ` re-folding which `rfl`/`rw` handles in one go.
    rw [IH (fun j => μ j.succ) (fun j => g j.succ) (fun j => hg j.succ)]

/-- **Per-coordinate measure equality** lifting `γ.curve t = P.withDensity ((γ.curve t).rnDeriv P)`
to the product measure, when `(γ.curve t) ≪ P`. -/
lemma pi_curve_eq_pi_withDensity {γ : QMDPath P} {t : ℝ}
    (hAC : γ.curve t ≪ P) (n : ℕ) :
    Measure.pi (fun _ : Fin n => γ.curve t)
      = (Measure.pi (fun _ : Fin n => P)).withDensity
          (fun X => ∏ j : Fin n, (γ.curve t).rnDeriv P (X j)) := by
  -- Local instance: `γ.curve t` is a probability measure.
  haveI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  have hmeas_d : Measurable ((γ.curve t).rnDeriv P) := Measure.measurable_rnDeriv _ _
  -- We use the rectangle characterization `Measure.pi_eq`.
  refine Measure.pi_eq (fun s hs => ?_)
  -- Goal: ((pi P).withDensity L) (univ.pi s) = ∏ j, (γ.curve t) (s j).
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  -- The indicator of a product set factorises per coordinate.
  have h_ind_factor : ∀ X : Fin n → Ω,
      (Set.univ.pi s).indicator
          (fun X' => ∏ j : Fin n, (γ.curve t).rnDeriv P (X' j)) X
        = ∏ j : Fin n, (s j).indicator ((γ.curve t).rnDeriv P) (X j) := by
    intro X
    classical
    by_cases hX : X ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hX]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Set.indicator_of_mem (hX j (Set.mem_univ _))]
    · rw [Set.indicator_of_notMem hX]
      simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, not_forall] at hX
      obtain ⟨j₀, hj₀⟩ := hX
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j₀) (Set.indicator_of_notMem hj₀ _)
  -- Convert the restricted integral to a regular integral via the indicator factorisation.
  rw [← MeasureTheory.lintegral_indicator (MeasurableSet.univ_pi hs)]
  rw [show
        (∫⁻ X : Fin n → Ω,
            (Set.univ.pi s).indicator
                (fun X' => ∏ j : Fin n, (γ.curve t).rnDeriv P (X' j)) X
              ∂Measure.pi fun _ : Fin n => P)
          = ∫⁻ X : Fin n → Ω,
              ∏ j : Fin n, (s j).indicator ((γ.curve t).rnDeriv P) (X j)
                ∂Measure.pi fun _ : Fin n => P
        from lintegral_congr h_ind_factor]
  -- Apply the finite-product Tonelli helper.
  rw [lintegral_pi_finset_prod n (fun _ : Fin n => P)
    (fun j => (s j).indicator ((γ.curve t).rnDeriv P))
    (fun j => hmeas_d.indicator (hs j))]
  -- Each factor: ∫⁻ x, (s j).indicator ((γ.curve t).rnDeriv P) x ∂P
  --            = ∫⁻ x in s j, (γ.curve t).rnDeriv P x ∂P
  --            = (γ.curve t) (s j)        [by setLIntegral_rnDeriv']
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [MeasureTheory.lintegral_indicator (hs j)]
  exact Measure.setLIntegral_rnDeriv' hAC (hs j)

/-- **LR factorisation of `∫⁻` against the perturbed product measure.**

For any QMD path `γ : QMDPath P`, dimension `n : ℕ`, parameter
`t : ℝ` (typically `t = 1/√n`) with `(γ.curve t) ≪ P`, and nonneg
measurable integrand `f : (Fin n → Ω) → ℝ≥0∞`, there exists an LR
vector `L_n_g : (Fin n → Ω) → ℝ≥0∞` (the product Radon-Nikodym density
of `Measure.pi (fun _ => γ.curve t)` w.r.t. `Measure.pi (fun _ => P)`)
such that

    `∫⁻ X, f X ∂Measure.pi (fun _ => γ.curve t)
        = ∫⁻ X, f X · L_n_g X ∂Measure.pi (fun _ => P)`.

**Hypotheses.**
* `(hAC : γ.curve t ≪ P)` — per-coordinate absolute continuity along the
  QMD path; vdV §25.6 (LAN regularity).
* `(hf : Measurable f)` — integrand measurability; standard in the
  Tonelli/Fubini context.

Witness: `L_n_g X := ∏ⱼ (γ.curve t).rnDeriv P (X j)`. -/
lemma lintegral_pi_curve_eq_lintegral_pi_lr
    (γ : QMDPath P) (n : ℕ) (t : ℝ)
    (hAC : γ.curve t ≪ P)
    (f : (Fin n → Ω) → ℝ≥0∞) (hf : Measurable f) :
    ∃ L_n_g : (Fin n → Ω) → ℝ≥0∞, Measurable L_n_g ∧
      ∫⁻ X : Fin n → Ω, f X
          ∂(Measure.pi (fun _ : Fin n => γ.curve t))
        = ∫⁻ X : Fin n → Ω, f X * L_n_g X
            ∂(Measure.pi (fun _ : Fin n => P)) := by
  haveI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  refine ⟨fun X => ∏ j : Fin n, (γ.curve t).rnDeriv P (X j),
    Finset.measurable_prod _ (fun j _ =>
      (Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply j)), ?_⟩
  -- Step 1: rewrite the LHS via the measure equality.
  rw [pi_curve_eq_pi_withDensity hAC n]
  -- Step 2: convert the withDensity-integral to a multiplied integral.
  -- The density function in `pi_curve_eq_pi_withDensity` is exactly our L_n_g.
  have hL_meas :
      Measurable (fun X : Fin n → Ω => ∏ j : Fin n, (γ.curve t).rnDeriv P (X j)) :=
    Finset.measurable_prod _ (fun j _ =>
      (Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply j))
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul _ hL_meas hf]
  -- Step 3: transpose `*` (integrand becomes `f X * L X` instead of `L X * f X`).
  refine lintegral_congr (fun X => ?_)
  simp only [Pi.mul_apply, mul_comm]

end LRFactorization

end AsymptoticStatistics.LowerBounds.T7_AndersonClosure
