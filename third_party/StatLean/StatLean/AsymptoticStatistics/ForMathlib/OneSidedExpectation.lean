module
public import Mathlib.Data.EReal.Inv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

@[expose] public section

/-!
# One-sided expectations of extended-real functions

Reusable signed expectations for functions that may take `-∞`, but whose
positive part has finite integral.  This is the expectation convention used
in van der Vaart's Wald consistency theorem (Theorem 5.14, pp.47--48).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics

/-- The one-sided expectation of an `EReal`-valued function: positive-part
lintegral minus negative-part lintegral.

Edge behavior: if the positive part is finite and the negative part is
infinite, the value is `-∞`.  Callers exclude pointwise `⊤`; no totalized
Bochner integral is used for non-`L¹` functions. -/
noncomputable def extendedExpectation {X : Type*} [MeasurableSpace X]
    (Q : Measure X) (f : X → EReal) : EReal :=
  (↑(∫⁻ x, (f x).toENNReal ∂Q) : EReal) -
    (↑(∫⁻ x, (-f x).toENNReal ∂Q) : EReal)

/-- The one-sided extended-real empirical average of a finite sample.

It averages positive and negative parts separately in `ENNReal`, then takes
their signed difference.  Edge behavior: the empty sample (`n = 0`) is
defined to have average `0`. -/
noncomputable def extendedEmpiricalAvg {X : Type*} (f : X → EReal)
    (n : ℕ) (sample : Fin n → X) : EReal :=
  if n = 0 then 0 else
    (↑((n : ENNReal)⁻¹ * ∑ i, (f (sample i)).toENNReal) : EReal) -
      (↑((n : ENNReal)⁻¹ * ∑ i, (-f (sample i)).toENNReal) : EReal)

/-- Reverse monotone convergence for `extendedExpectation` under a finite
positive-part envelope.  This is the one-sided expectation step in the proof
of vdV Theorem 5.14, p.48. -/
theorem extendedExpectation_tendsto_of_antitone
    {X : Type*} [MeasurableSpace X] (Q : Measure X)
    (f : ℕ → X → EReal) (g : X → EReal)
    -- measurable local envelopes, as required by vdV (5.13), p.48.
    (hf_meas : ∀ n, Measurable (f n))
    -- explicit a.e. form of the decreasing-envelope construction.
    (hf_anti : ∀ᵐ x ∂Q, Antitone fun n => f n x)
    -- explicit a.e. pointwise limit supplied by the USC envelope theorem.
    (hf_lim : ∀ᵐ x ∂Q, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    -- finite positive part from vdV condition (5.13), p.48.
    (hpos : (∫⁻ x, (f 0 x).toENNReal ∂Q) ≠ ∞) :
    Tendsto (fun n => extendedExpectation Q (f n)) atTop
      (𝓝 (extendedExpectation Q g)) := by
  have hpos_meas : ∀ n, AEMeasurable (fun x => (f n x).toENNReal) Q := fun n =>
    (EReal.continuous_toENNReal.measurable.comp (hf_meas n)).aemeasurable
  have hneg_meas : ∀ n, AEMeasurable (fun x => (-f n x).toENNReal) Q := fun n =>
    (EReal.continuous_toENNReal.measurable.comp (hf_meas n).neg).aemeasurable
  have hpos_anti : ∀ᵐ x ∂Q, Antitone fun n => (f n x).toENNReal :=
    hf_anti.mono fun _ hx _ _ hnm => EReal.toENNReal_le_toENNReal (hx hnm)
  have hneg_mono : ∀ᵐ x ∂Q, Monotone fun n => (-f n x).toENNReal :=
    hf_anti.mono fun _ hx _ _ hnm =>
      EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hx hnm))
  have hpos_lim :
      ∀ᵐ x ∂Q, Tendsto (fun n => (f n x).toENNReal) atTop (𝓝 (g x).toENNReal) :=
    hf_lim.mono fun _ hx =>
      EReal.continuous_toENNReal.continuousAt.tendsto.comp hx
  have hneg_lim :
      ∀ᵐ x ∂Q, Tendsto (fun n => (-f n x).toENNReal) atTop (𝓝 (-g x).toENNReal) :=
    hf_lim.mono fun _ hx =>
      EReal.continuous_toENNReal.continuousAt.tendsto.comp
        (continuous_neg.continuousAt.tendsto.comp hx)
  have hpos_integral :=
    lintegral_tendsto_of_tendsto_of_antitone hpos_meas hpos_anti hpos hpos_lim
  have hneg_integral :=
    lintegral_tendsto_of_tendsto_of_monotone hneg_meas hneg_mono hneg_lim
  have hpos_limit_le :
      ∫⁻ x, (g x).toENNReal ∂Q ≤ ∫⁻ x, (f 0 x).toENNReal ∂Q :=
    le_of_tendsto' hpos_integral fun n =>
      lintegral_mono_ae <| hpos_anti.mono fun _ hx => hx (Nat.zero_le n)
  have hpos_limit_ne_top : (∫⁻ x, (g x).toENNReal ∂Q) ≠ ∞ :=
    ne_top_of_le_ne_top hpos hpos_limit_le
  have hpos_coe :
      Tendsto (fun n => (↑(∫⁻ x, (f n x).toENNReal ∂Q) : EReal)) atTop
        (𝓝 (↑(∫⁻ x, (g x).toENNReal ∂Q) : EReal)) :=
    EReal.tendsto_coe_ennreal.mpr hpos_integral
  have hneg_coe :
      Tendsto (fun n => (↑(∫⁻ x, (-f n x).toENNReal ∂Q) : EReal)) atTop
        (𝓝 (↑(∫⁻ x, (-g x).toENNReal ∂Q) : EReal)) :=
    EReal.tendsto_coe_ennreal.mpr hneg_integral
  unfold extendedExpectation
  rw [sub_eq_add_neg]
  simp_rw [sub_eq_add_neg]
  exact
    (EReal.continuousAt_add (Or.inl (by simpa using hpos_limit_ne_top))
        (Or.inl (EReal.coe_ennreal_ne_bot _))).tendsto.comp
      (hpos_coe.prodMk_nhds hneg_coe.neg)

end AsymptoticStatistics
