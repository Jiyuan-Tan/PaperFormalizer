module
public import StatLean.NonparametricStatistics.KernelDensity.Defs
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-!
# Law transfer for density-sampled observations

The bridge between sample-space expectations and Lebesgue integrals against the density: for
`X` with law `densityMeasure p`,

* `isProbabilityMeasure_densityMeasure` — a measurable density induces a probability measure;
* `integral_comp_law_densityMeasure` / `lintegral_comp_law_densityMeasure` — the change of
  variables `E_P[g(X)] = ∫ g(z)·p(z) dz` (Bochner and lower-Lebesgue forms);
* `kdeMeanAt_eq_integral_kernel` — the mean of the kernel estimator at `x` in the classical
  form `E[p̂ₙ(x)] = ∫ K(u)·p(x + uh) du`.

These lemmas are the only place where `HasLaw`/`withDensity` plumbing appears; all risk files
consume the clean integral forms.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2 (sampling-model bookkeeping for the i.i.d.
density model underlying Propositions 1.1–1.6).

**Proof formalization notes.** Bochner transfer: `HasLaw.integral_comp` +
`integral_withDensity_eq_integral_toReal_smul` (plus `ENNReal.toReal_ofReal` on the
nonnegative density). Lower-Lebesgue transfer: `HasLaw.lintegral_comp`-style map lemma +
`lintegral_withDensity_eq_lintegral_mul`. The mean formula composes the transfer with the
scaling change of variables `z = x + u·h` (`Measure.integral_comp_mul_left` family and
translation invariance); its integrability hypothesis is discharged by consumers
(`integrable_kernel_mul_holder` in `KernelDensity/Bias.lean` for Hölder densities).

**Bibliographic comments.** Routine measure-theoretic plumbing; no attribution applicable.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A measurable probability density induces a probability measure via `withDensity`. -/
theorem isProbabilityMeasure_densityMeasure {p : ℝ → ℝ}
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p)
    -- USER-INPUT: `p` is a probability density (nonnegative, unit mass)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∫ x, p x = 1) :
    IsProbabilityMeasure (densityMeasure p) := by
  have hint : Integrable p := by
    by_contra hni
    rw [integral_undef hni] at h1
    exact one_ne_zero h1.symm
  refine ⟨?_⟩
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0), h1, ENNReal.ofReal_one]

/-- **Law transfer, Bochner form**: for `X` with law `densityMeasure p` and integrable
`g·p`, `E_P[g(X)] = ∫ g(z)·p(z) dz`. -/
theorem integral_comp_law_densityMeasure {X : Ω → ℝ} {p : ℝ → ℝ}
    -- USER-INPUT: `X` has Lebesgue density `p`; the sampling model
    (hX : HasLaw X (densityMeasure p) P)
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    {g : ℝ → ℝ}
    -- LEAN-ONLY: measurability of the integrand; standard regularity
    (hg : Measurable g)
    -- LEAN-ONLY: integrability against the density; discharged by consumers
    (hint : Integrable fun z => g z * p z) :
    ∫ ω, g (X ω) ∂P = ∫ z, g z * p z := by
  have h1 : ∫ ω, g (X ω) ∂P = ∫ z, g z ∂(densityMeasure p) := by
    have := hX.integral_comp hg.aestronglyMeasurable
    simpa [Function.comp_def] using this
  rw [h1, densityMeasure, integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (h0 x)]
  ring

/-- **Law transfer, lower-Lebesgue form**: for `X` with law `densityMeasure p` and measurable
`g : ℝ → ℝ≥0∞`, `∫⁻ g(X) dP = ∫⁻ g(z)·ofReal (p z) dz`. -/
theorem lintegral_comp_law_densityMeasure {X : Ω → ℝ} {p : ℝ → ℝ}
    -- USER-INPUT: `X` has Lebesgue density `p`; the sampling model
    (hX : HasLaw X (densityMeasure p) P)
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p)
    {g : ℝ → ℝ≥0∞}
    -- LEAN-ONLY: measurability of the integrand; standard regularity
    (hg : Measurable g) :
    ∫⁻ ω, g (X ω) ∂P = ∫⁻ z, g z * ENNReal.ofReal (p z) := by
  rw [hX.lintegral_comp hg.aemeasurable, densityMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hp.ennreal_ofReal hg]
  exact lintegral_congr fun z => mul_comm _ _

/-- Affine change of variables `z = x + u·h` on the whole line (`h > 0`): translate then
scale, using additive-Haar invariance. -/
private lemma integral_scale_shift (F : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    (∫ z, F z) = h * ∫ u, F (x + u * h) := by
  have hstep : (∫ u, F (x + u * h)) = |h⁻¹| • ∫ y, F (x + y) :=
    Measure.integral_comp_mul_right (fun y => F (x + y)) h
  rw [hstep, integral_add_left_eq_self F x, smul_eq_mul, abs_of_pos (inv_pos.2 hh),
    ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]

/-- Integrability transfer: if `g·p` is integrable against Lebesgue measure and `X` has law
`densityMeasure p`, then `g ∘ X` is integrable against `P`. -/
private lemma integrable_comp_kernel {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p g : ℝ → ℝ} (hX : HasLaw X (densityMeasure p) P)
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x) (hg : Measurable g)
    (hint : Integrable fun z => g z * p z) :
    Integrable (fun ω => g (X ω)) P := by
  have h2 : Integrable g (densityMeasure p) := by
    rw [densityMeasure, integrable_withDensity_iff hp.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    exact hint.congr (ae_of_all _ fun z => by simp only [ENNReal.toReal_ofReal (h0 z)])
  have h3 := integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable
  rw [hX.map_eq] at h3
  exact h3.mp h2

/-- **Mean of the kernel estimator** at `x`, in the classical bias-analysis form:
`E_P[p̂ₙ(x)] = ∫ K(u)·p(x + u·h) du` (for a nonempty sample and positive bandwidth). -/
theorem kdeMeanAt_eq_integral_kernel {n : ℕ} [IsProbabilityMeasure P]
    {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ} {x : ℝ}
    -- LEAN-ONLY: nonempty sample; with `n = 0` the estimator is identically `0`
    (hn : 0 < n)
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability; standard regularity
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x) (hK : Measurable K)
    -- LEAN-ONLY: integrability of the transferred integrand; discharged by consumers via
    -- `integrable_kernel_mul_holder`
    (hint : Integrable fun u => K u * p (x + u * h)) :
    kdeMeanAt P X K h x = ∫ u, K u * p (x + u * h) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hgmeas : Measurable (fun z => K ((z - x) / h)) :=
    hK.comp ((measurable_id.sub_const x).div_const h)
  -- integrability of the transferred integrand `z ↦ K((z-x)/h)·p z`
  have hintz : Integrable (fun z => K ((z - x) / h) * p z) volume := by
    have hFdef : Integrable (fun y => K (((x + y) - x) / h) * p (x + y)) volume := by
      have hrw : (fun u => K u * p (x + u * h))
          = (fun y => K (((x + y) - x) / h) * p (x + y)) ∘ (fun u => u * h) := by
        funext u
        simp only [Function.comp_apply, add_sub_cancel_left, mul_div_cancel_right₀ _ hh.ne']
      rw [hrw] at hint
      exact (integrable_comp_mul_right_iff _ hh.ne').mp hint
    have hmp := (measurePreserving_add_left (volume : Measure ℝ) x).integrable_comp
      ((hgmeas.mul hp).aestronglyMeasurable)
    exact hmp.mp hFdef
  -- per-observation mean, via law transfer and the change of variables
  have hper : ∀ i, (∫ ω, K ((X i ω - x) / h) ∂P) = h * ∫ u, K u * p (x + u * h) := by
    intro i
    rw [integral_comp_law_densityMeasure (hs.law i) hp h0 hgmeas hintz,
      integral_scale_shift (fun z => K ((z - x) / h) * p z) hh x]
    refine congrArg (h * ·) (integral_congr_ae (ae_of_all _ fun u => ?_))
    simp only [add_sub_cancel_left, mul_div_cancel_right₀ _ hh.ne']
  have hintP : ∀ i, Integrable (fun ω => K ((X i ω - x) / h)) P :=
    fun i => integrable_comp_kernel (g := fun z => K ((z - x) / h)) (hs.law i) hp h0 hgmeas hintz
  -- assemble the sum
  have hmean : kdeMeanAt P X K h x
      = ((n : ℝ) * h)⁻¹ * ∑ i, ∫ ω, K ((X i ω - x) / h) ∂P := by
    unfold kdeMeanAt kde kdeData
    rw [integral_const_mul, integral_finset_sum _ (fun i _ => hintP i)]
  rw [hmean]
  simp_rw [hper]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end StatLean.NonparametricStatistics
