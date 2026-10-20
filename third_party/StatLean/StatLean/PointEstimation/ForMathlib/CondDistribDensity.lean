module
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Conditional distributions of a jointly absolutely continuous law

For a joint law on `S × ℝ` given by a density `p` against `ν ⊗ volume`, the conditional
distribution of the second coordinate given the first is the normalized slice
`y ↦ p (t, y) / ∫ p (t, ·)`. This file records the three steps:

* `map_fst_withDensity_prod` — the first marginal has density `t ↦ ∫⁻ p (t, y) dy` (Tonelli);
* `lintegral_withDensity_prod` — integration against the joint law is iterated integration
  against `ν` of slice integrals weighted by `p`;
* `condDistrib_withDensity_prod_ae_eq` — Mathlib's `ProbabilityTheory.condDistrib` for
  `(Prod.snd ∣ Prod.fst)` is almost everywhere the normalized-slice measure.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.6
(Sufficient Statistics), supporting material for Theorem 6.12 and Corollary 6.13: conditional
distributions of a jointly absolutely continuous law. (`TPE2 §1.6 Thm 6.12, Cor 6.13`.)

**Proof formalization notes.**
* **No `Kernel` is defined here.** Packaging `t ↦ (∫⁻ p (t, ·))⁻¹ • volume.withDensity (p (t, ·))`
  as a `MeasureTheory.Kernel` would require discharging the kernel measurability obligation as
  part of the *definition*, which is exactly the work the file is meant to postpone. Instead
  the identification is stated pointwise, almost everywhere in `t`, against Mathlib's
  already-constructed `condDistrib`. Callers needing a kernel use `condDistrib` itself and
  rewrite with this lemma where a formula is required.
* **The joint density enters as an equation hypothesis** `hρ : ρ = (ν.prod volume).withDensity p`
  rather than by substituting the right-hand side into the statement. This keeps
  `IsFiniteMeasure ρ` (needed by `condDistrib`) as a hypothesis on the object the caller
  actually holds, and lets the lemma be applied to a `ρ` obtained as a pushforward or a
  restriction that is only *afterwards* shown to have this form.
* **Route for the third statement.** By `map_fst_withDensity_prod` the first marginal is
  `ν.withDensity (t ↦ ∫⁻ p (t, ·))`; by `lintegral_withDensity_prod` the composition-product
  of that marginal with the normalized-slice family reproduces `ρ`. A.e.-uniqueness of the
  disintegration of a finite measure on a product with standard Borel second factor
  (`MeasureTheory.Measure.eq_condKernel_of_measure_eq_compProd` and its `condDistrib`
  wrapper) then identifies the two kernels almost everywhere.
* **Normalization side conditions.** Slices with `∫⁻ p (t, ·) = 0` are null for the first
  marginal, and slices with `∫⁻ p (t, ·) = ⊤` would give a non-probability normalization; both
  are excluded by explicit a.e. hypotheses rather than by a junk-value convention, because the
  conclusion is an equality of measures where the junk branch is genuinely different.
* The second factor is fixed to `(ℝ, volume)`, which is what the location/scale conditional
  risk arguments consume; the same statements hold verbatim for any σ-finite measure on a
  standard Borel space, at the cost of one more variable.

**Bibliographic comments.** Conditional distributions were introduced by A. N. Kolmogorov
(*Grundbegriffe der Wahrscheinlichkeitsrechnung*, Springer, 1933, Ch. V); their existence as
regular conditional probabilities on standard Borel spaces, and the disintegration theorem
used for the a.e. identification, are due to J. L. Doob (*Stochastic Processes*, Wiley, 1953,
Ch. I §9).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {S : Type*} [MeasurableSpace S]

/-- The first marginal of a jointly absolutely continuous law has the slice-integral
density. -/
theorem map_fst_withDensity_prod
    -- USER-INPUT: the reference measure on the first factor; free choice
    {ν : Measure S}
    -- USER-INPUT: s-finiteness, the standing hypothesis for products and Tonelli
    [SFinite ν]
    -- USER-INPUT: the joint density and its measurability
    {p : S × ℝ → ℝ≥0∞} (hp : Measurable p) :
    ((ν.prod volume).withDensity p).map Prod.fst
      = ν.withDensity fun t => ∫⁻ y, p (t, y) ∂volume := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, withDensity_apply p (measurable_fst hs),
      withDensity_apply _ hs, ← Set.prod_univ, ← Measure.restrict_prod_eq_prod_univ,
      lintegral_prod _ hp.aemeasurable]

/-- Integration against a jointly absolutely continuous law, written as an iterated integral
of density-weighted slices. -/
theorem lintegral_withDensity_prod
    -- USER-INPUT: the reference measure on the first factor; free choice
    {ν : Measure S}
    -- USER-INPUT: s-finiteness, the standing hypothesis for products and Tonelli
    [SFinite ν]
    -- USER-INPUT: the joint density and its measurability
    {p : S × ℝ → ℝ≥0∞} (hp : Measurable p)
    -- USER-INPUT: the integrand and its measurability
    {f : S × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂((ν.prod volume).withDensity p)
      = ∫⁻ t, (∫⁻ y, f (t, y) * p (t, y) ∂volume) ∂ν := by
  rw [lintegral_withDensity_eq_lintegral_mul (ν.prod volume) hp hf]
  simp only [Pi.mul_apply]
  rw [lintegral_prod (fun z => p z * f z) (hp.mul hf).aemeasurable]
  refine lintegral_congr fun t => lintegral_congr fun y => ?_
  rw [mul_comm]

/-- **Conditional distribution of a jointly absolutely continuous law.** The regular
conditional distribution of the second coordinate given the first is almost everywhere the
normalized slice of the joint density. -/
theorem condDistrib_withDensity_prod_ae_eq
    -- USER-INPUT: the first factor is standard Borel; needed for a.e. uniqueness of the
    -- disintegration
    [StandardBorelSpace S]
    -- USER-INPUT: the reference measure on the first factor; free choice
    {ν : Measure S}
    -- USER-INPUT: s-finiteness, the standing hypothesis for products and Tonelli
    [SFinite ν]
    -- USER-INPUT: the joint density and its measurability
    {p : S × ℝ → ℝ≥0∞} (hp : Measurable p)
    -- USER-INPUT: the joint law the caller actually holds
    {ρ : Measure (S × ℝ)}
    -- USER-INPUT: finiteness of the joint law; required by `condDistrib`
    [IsFiniteMeasure ρ]
    -- USER-INPUT: the joint law is the density `p` against `ν ⊗ volume`
    (hρ : ρ = (ν.prod volume).withDensity p)
    -- USER-INPUT: slice masses are finite a.e.; else the normalization is not a probability
    (hp_ne_top : ∀ᵐ t ∂ν, (∫⁻ y, p (t, y) ∂volume) ≠ ⊤)
    -- USER-INPUT: slice masses are nonzero a.e.; else the normalization is junk-valued
    (hp_ne_zero : ∀ᵐ t ∂ν, (∫⁻ y, p (t, y) ∂volume) ≠ 0) :
    ∀ᵐ t ∂(ρ.map Prod.fst),
      condDistrib Prod.snd Prod.fst ρ t
        = (∫⁻ y, p (t, y) ∂volume)⁻¹ • volume.withDensity fun y => p (t, y) := by
  -- The slice mass (normalizer) and its measurability.
  set g : S → ℝ≥0∞ := fun t => ∫⁻ y, p (t, y) ∂volume with hg_def
  have hpt : ∀ t : S, Measurable fun y => p (t, y) := fun t =>
    hp.comp (measurable_const.prodMk measurable_id)
  have hg : Measurable g := hp.lintegral_prod_right'
  -- The candidate kernel: `volume` tilted by the normalized slice density.
  set q : S → ℝ → ℝ≥0∞ := fun t y => (g t)⁻¹ * p (t, y) with hq_def
  have hq_uncurry : Measurable (Function.uncurry q) :=
    ((hg.inv).comp measurable_fst).mul hp
  set κ : Kernel S ℝ := Kernel.withDensity (Kernel.const S volume) q with hκ_def
  -- Every slice of the candidate is the normalized slice measure in the statement.
  have hκ_apply : ∀ t : S,
      κ t = (g t)⁻¹ • volume.withDensity fun y => p (t, y) := by
    intro t
    rw [hκ_def, Kernel.withDensity_apply _ hq_uncurry, Kernel.const_apply, hq_def,
        ← withDensity_smul _ (hpt t)]
    rfl
  -- The candidate is a finite kernel: its total mass is `(g t)⁻¹ * g t ≤ 1`.
  have hκ_fin : IsFiniteKernel κ := by
    refine ⟨1, ENNReal.one_lt_top, fun t => ?_⟩
    rw [hκ_apply t, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ, smul_eq_mul]
    exact ENNReal.inv_mul_le_one _
  haveI := hκ_fin
  -- The first marginal has the slice-mass density.
  have hmap : ρ.map Prod.fst = ν.withDensity g := by
    rw [hρ]; exact map_fst_withDensity_prod hp
  haveI : SFinite (ν.withDensity g) := by rw [← hmap]; infer_instance
  -- The defining composition-product identity for the candidate.
  have hcompProd : ρ.map (fun x => (Prod.fst x, Prod.snd x)) = ρ.map Prod.fst ⊗ₘ κ := by
    have hid : (fun x : S × ℝ => (Prod.fst x, Prod.snd x)) = id := by funext x; rfl
    rw [hid, Measure.map_id]
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    -- Left side: iterated integral of the density-weighted slices.
    have hL : ∫⁻ z, f z ∂ρ = ∫⁻ t, ∫⁻ y, p (t, y) * f (t, y) ∂volume ∂ν := by
      rw [hρ, lintegral_withDensity_prod hp hf]
      exact lintegral_congr fun t => lintegral_congr fun y => mul_comm _ _
    -- Inner kernel integral equals the normalized slice integral.
    have hft : ∀ t : S, Measurable fun y => f (t, y) := fun t =>
      hf.comp (measurable_const.prodMk measurable_id)
    have hker : ∀ t : S, ∫⁻ y, f (t, y) ∂(κ t)
        = (g t)⁻¹ * ∫⁻ y, p (t, y) * f (t, y) ∂volume := by
      intro t
      rw [hκ_def, Kernel.lintegral_withDensity _ hq_uncurry t (hft t), Kernel.const_apply,
          ← lintegral_const_mul _ ((hpt t).fun_mul (hft t))]
      exact lintegral_congr fun y => by rw [hq_def, mul_assoc]
    -- Right side: unfold the composition-product and the marginal density.
    have hJ : Measurable fun t => ∫⁻ y, p (t, y) * f (t, y) ∂volume :=
      (hp.mul hf).lintegral_prod_right'
    have hR : ∫⁻ z, f z ∂(ρ.map Prod.fst ⊗ₘ κ)
        = ∫⁻ t, g t * ((g t)⁻¹ * ∫⁻ y, p (t, y) * f (t, y) ∂volume) ∂ν := by
      rw [hmap, Measure.lintegral_compProd hf]
      have hcong : (fun t => ∫⁻ y, f (t, y) ∂(κ t))
          = fun t => (g t)⁻¹ * ∫⁻ y, p (t, y) * f (t, y) ∂volume := funext hker
      rw [hcong, lintegral_withDensity_eq_lintegral_mul ν hg ((hg.fun_inv).fun_mul hJ)]
      simp only [Pi.mul_apply]
    rw [hL, hR]
    refine lintegral_congr_ae ?_
    filter_upwards [hp_ne_top, hp_ne_zero] with t htop hzero
    rw [← mul_assoc, ENNReal.mul_inv_cancel hzero htop, one_mul]
  -- Conclude by a.e. uniqueness of the disintegration, then rewrite each fibre.
  have hae := condDistrib_ae_eq_of_measure_eq_compProd (μ := ρ) Prod.fst
    measurable_snd.aemeasurable (κ := κ) hcompProd
  filter_upwards [hae] with t ht
  rw [ht, hκ_apply t]

end StatLean.PointEstimation
