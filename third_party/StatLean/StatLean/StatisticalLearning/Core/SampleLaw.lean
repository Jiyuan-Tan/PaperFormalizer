module
public import StatLean.StatisticalLearning.Core.Defs
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# The i.i.d. sample law — coordinate structure and unbiasedness

Working lemmas about `sampleLaw D n = Measure.pi (fun _ => D)`: the coordinate
evaluations are measure-preserving and jointly independent (the Lean form of
"`S ∼ D^m` i.i.d.", SSBD §2.1), the empirical risk of a fixed hypothesis is
measurable in the sample, unbiased for the true risk (the "preliminary
observation" of SSBD p. 33), and bounded when the loss is bounded.

**Reference.** SSBD §2.1, §4.2 (p. 33). Transcriptions:
`notes/statistical_learning/book_statements/ch2-5.md`.

**Formalization notes.** The independence/measure-preservation content is
Mathlib's (`ProbabilityTheory.iIndepFun_pi`, `Measure.pi` marginals); this file
only specializes it to the `sampleLaw` spelling so downstream files never touch
`Measure.pi` directly. Unbiasedness `E_{S∼Dⁿ}[L_S(h)] = L_D(h)` needs `1 ≤ n`
(at `n = 0` the LHS is junk `0`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {n : ℕ}

/-- Coordinate evaluation is measure-preserving from `sampleLaw D n` to `D`
(the marginal of `D^n` is `D`; SSBD §2.1). -/
theorem measurePreserving_eval_sampleLaw (i : Fin n) :
    MeasurePreserving (fun s : Sample Z n => s i) (sampleLaw D n) D :=
  MeasureTheory.measurePreserving_eval (fun _ : Fin n => D) i

/-- The coordinate evaluations of an i.i.d. sample are jointly independent
(SSBD §2.1, "independently ... distributed"). -/
theorem iIndepFun_eval_sampleLaw :
    iIndepFun (fun (i : Fin n) (s : Sample Z n) => s i) (sampleLaw D n) :=
  iIndepFun_pi (X := fun _ : Fin n => (id : Z → Z)) fun _ => aemeasurable_id

/-- Measurability of the empirical risk of a fixed hypothesis in the sample
(LEAN-ONLY regularity; SSBD Remark 3.1 supplies measurability of the loss). -/
theorem measurable_empRisk {ℓ : H → Z → ℝ} {h : H}
    -- USER-INPUT: measurability of the loss of `h`; SSBD Remark 3.1
    (hmeas : Measurable (ℓ h)) :
    Measurable fun s : Sample Z n => empRisk ℓ s h := by
  simp only [empRisk]
  exact measurable_const.mul
    (Finset.measurable_sum _ fun i _ => hmeas.comp (measurable_pi_apply i))

/-- **Unbiasedness of the empirical risk** (SSBD p. 33, "the expected value of
`L_S(h)` is `L_D(h)`"): for `1 ≤ n`, `E_{S∼Dⁿ}[L_S(h)] = L_D(h)`. -/
theorem integral_empRisk {ℓ : H → Z → ℝ} {h : H}
    -- USER-INPUT: integrability of the loss of `h`; SSBD Remark 3.1 (implicit)
    (hint : Integrable (ℓ h) D)
    -- USER-INPUT: at least one example; SSBD §2.1 (implicit in `S ≠ ∅`)
    (hn : 1 ≤ n) :
    ∫ s, empRisk ℓ s h ∂(sampleLaw D n) = risk D ℓ h := by
  -- Each coordinate slot integrates to the true risk (marginal = `D`).
  have hslot : ∀ i : Fin n,
      ∫ s : Sample Z n, ℓ h (s i) ∂(sampleLaw D n) = risk D ℓ h := by
    intro i
    have hmap := (measurePreserving_eval_sampleLaw (D := D) (n := n) i).map_eq
    have : ∫ z, ℓ h z ∂D = ∫ s : Sample Z n, ℓ h (s i) ∂(sampleLaw D n) := by
      conv_lhs => rw [← hmap]
      exact integral_map (measurable_pi_apply i).aemeasurable
        (by rw [hmap]; exact hint.1)
    exact this.symm
  -- Each slot is integrable, so the finite sum comes out of the integral.
  have hslot_int : ∀ i : Fin n, Integrable (fun s : Sample Z n => ℓ h (s i))
      (sampleLaw D n) := fun i =>
    (measurePreserving_eval_sampleLaw (D := D) (n := n) i).integrable_comp_of_integrable hint
  have hsum : ∫ s : Sample Z n, ∑ i, ℓ h (s i) ∂(sampleLaw D n)
      = ∑ i : Fin n, ∫ s : Sample Z n, ℓ h (s i) ∂(sampleLaw D n) :=
    integral_finset_sum _ fun i _ => hslot_int i
  have hconst : ∫ s : Sample Z n, (n : ℝ)⁻¹ * ∑ i, ℓ h (s i) ∂(sampleLaw D n)
      = (n : ℝ)⁻¹ * ∫ s : Sample Z n, ∑ i, ℓ h (s i) ∂(sampleLaw D n) :=
    integral_const_mul _ _
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [empRisk]
  rw [hconst, hsum]
  simp only [hslot, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Pointwise bounds on the empirical risk from bounds on the loss
(LEAN-ONLY convenience; used throughout the finite-class and Rademacher
lanes). -/
theorem empRisk_mem_Icc {ℓ : H → Z → ℝ} {h : H} {a b : ℝ}
    -- USER-INPUT: the loss of `h` has range in `[a,b]`; SSBD §4.2 / Ex. 4.2
    (hab : ∀ z, ℓ h z ∈ Set.Icc a b)
    -- LEAN-ONLY: `1 ≤ n` (at `n = 0` the empirical risk is junk `0`)
    (hn : 1 ≤ n)
    (s : Sample Z n) :
    empRisk ℓ s h ∈ Set.Icc a b := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlow : (n : ℝ) * a ≤ ∑ i, ℓ h (s i) := by
    have := Finset.sum_le_sum (f := fun _ : Fin n => a) (g := fun i => ℓ h (s i))
      (s := Finset.univ) fun i _ => (hab (s i)).1
    simpa [Finset.sum_const, Finset.card_univ, mul_comm] using this
  have hhigh : ∑ i, ℓ h (s i) ≤ (n : ℝ) * b := by
    have := Finset.sum_le_sum (f := fun i => ℓ h (s i)) (g := fun _ : Fin n => b)
      (s := Finset.univ) fun i _ => (hab (s i)).2
    simpa [Finset.sum_const, Finset.card_univ, mul_comm] using this
  have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hn0)
  have hn0' : (n : ℝ) ≠ 0 := ne_of_gt hn0
  refine ⟨?_, ?_⟩
  · rw [empRisk]
    calc a = (n : ℝ)⁻¹ * ((n : ℝ) * a) := by field_simp
      _ ≤ (n : ℝ)⁻¹ * ∑ i, ℓ h (s i) := mul_le_mul_of_nonneg_left hlow hinv
  · rw [empRisk]
    calc (n : ℝ)⁻¹ * ∑ i, ℓ h (s i)
        ≤ (n : ℝ)⁻¹ * ((n : ℝ) * b) := mul_le_mul_of_nonneg_left hhigh hinv
      _ = b := by field_simp

/-- Bounds on the true risk from bounds on the loss (LEAN-ONLY convenience). -/
theorem risk_mem_Icc {ℓ : H → Z → ℝ} {h : H} {a b : ℝ}
    -- USER-INPUT: the loss of `h` has range in `[a,b]`; SSBD §4.2 / Ex. 4.2
    (hab : ∀ z, ℓ h z ∈ Set.Icc a b)
    -- LEAN-ONLY: measurability, so that the risk integral is genuine
    (hmeas : Measurable (ℓ h)) :
    risk D ℓ h ∈ Set.Icc a b := by
  -- A bounded measurable function on a probability space is integrable.
  have hbound : ∀ z, ‖ℓ h z‖ ≤ |a| + |b| := by
    intro z
    obtain ⟨h1, h2⟩ := hab z
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have : -|a| ≤ a := neg_abs_le a
      have : (0 : ℝ) ≤ |b| := abs_nonneg b
      linarith [neg_abs_le a, abs_nonneg b]
    · linarith [le_abs_self b, abs_nonneg a]
  have hint : Integrable (ℓ h) D :=
    Integrable.mono' (integrable_const (|a| + |b|)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  refine ⟨?_, ?_⟩
  · have h1 : ∫ _z, a ∂D ≤ ∫ z, ℓ h z ∂D :=
      integral_mono (integrable_const a) hint fun z => (hab z).1
    simpa [risk] using h1
  · have h2 : ∫ z, ℓ h z ∂D ≤ ∫ _z, b ∂D :=
      integral_mono hint (integrable_const b) fun z => (hab z).2
    simpa [risk] using h2

/-- Nonnegativity of the true risk for a nonnegative loss (LEAN-ONLY; SSBD's
losses take values in `ℝ₊`, §3.2.1). Holds without integrability (junk `0`). -/
theorem risk_nonneg {ℓ : H → Z → ℝ} {h : H}
    -- USER-INPUT: nonnegative loss; SSBD §3.2.1 (`ℓ : 𝓗 × Z → ℝ₊`)
    (hpos : ∀ z, 0 ≤ ℓ h z) :
    0 ≤ risk D ℓ h :=
  integral_nonneg hpos

/-- The best-in-class risk is a lower bound: `bestRisk ≤ risk g` for `g ∈ 𝓗`,
provided the risk image is bounded below (LEAN-ONLY `sInf` regularity;
nonnegative losses give `BddBelow` via `risk_nonneg`). -/
theorem bestRisk_le_risk {𝓗 : Set H} {ℓ : H → Z → ℝ} {g : H}
    (hg : g ∈ 𝓗)
    -- LEAN-ONLY: bounded-below risk image (from loss nonnegativity)
    (hbdd : BddBelow (risk D ℓ '' 𝓗)) :
    bestRisk D 𝓗 ℓ ≤ risk D ℓ g :=
  csInf_le hbdd ⟨g, hg, rfl⟩

end StatLean.StatisticalLearning
