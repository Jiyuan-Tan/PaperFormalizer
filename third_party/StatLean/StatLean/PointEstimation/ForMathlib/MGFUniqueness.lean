module
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

/-!
# Laplace-transform uniqueness on a set with nonempty interior (one dimension)

Two finite measures on `ℝ` whose Laplace transforms `t ↦ ∫ e^{tx} dμ(x)` agree on a set `S`
with an interior point are equal. Mathlib knows the *probability-measure, global-`mgf`* form
(`ProbabilityTheory.eqOn_complexMGF_of_mgf` and its consequences); the statistical
applications need the **local** form, where equality of the transforms is only available on
the natural parameter set of an exponential family, and the measures are finite rather than
normalized.

This file provides:

* `ext_of_integral_exp_eqOn` — the measure-uniqueness statement;
* `ae_eq_zero_of_integral_exp_smul_eq_zero` — the **signed** corollary: a function whose
  `e^{tx}`-weighted integrals vanish on `S` is null. This is the analytic engine behind
  completeness of a full-rank exponential family (a candidate unbiased estimator of `0` has
  vanishing tilted integrals throughout the natural parameter set, hence vanishes a.e.).

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.5
(Exponential Families), supporting material for the identifiability of the canonical
parametrization (equation (5.2) and Definition 5.2): uniqueness of a Laplace transform on a
set with nonempty interior. (`TPE2 §1.5 (5.2), Def 5.2`.)

**Proof formalization notes.**
* **Route for `ext_of_integral_exp_eqOn`.** Pick `t₀ ∈ interior S`. Tilt both measures to
  `t₀` with `MeasureTheory.Measure.tilted`: the tilted measures are probability measures
  (or both zero, the degenerate branch handled separately, since `e^{t₀x} > 0` forces
  `∫ e^{t₀x} dμ = 0 ↔ μ = 0`). The tilted-mgf identity `integral_exp_tilted_mul` turns
  agreement of the two transforms on `S` into agreement of the two `mgf`s on the translate
  `S - t₀`, a set containing a neighbourhood of `0`. Strip analyticity of `complexMGF`
  (`ProbabilityTheory.analyticOnNhd_complexMGF`) plus the identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) — packaged here as
  `eqOn_complexMGF_of_mgf_eqOn` — propagate the equality from that real segment to the whole
  vertical strip, in particular to the imaginary axis. There `complexMGF` evaluated at `I·u`
  is the characteristic function, so `MeasureTheory.Measure.ext_of_charFun` identifies the
  two tilted measures. Untilting is `MeasureTheory.withDensity_inv_same` (the tilting density
  `e^{t₀x}/Z` is measurable, strictly positive and finite, so `withDensity` by it is
  injective on measures).
* **Why the local `eqOn` helper is genuinely needed.** Mathlib's
  `ProbabilityTheory.eqOn_complexMGF_of_mgf` demands *global* equality `mgf X μ = mgf Y μ'`
  of the two real `mgf`s (a `funext`-level hypothesis). Our data only gives a `Set.EqOn` on
  `S`, and outside the common integrability set the two `mgf`s are junk-valued `0`, so the
  global hypothesis is unavailable. `eqOn_complexMGF_of_mgf_eqOn` re-runs the same identity
  theorem argument from a `Set.EqOn` hypothesis on an open nonempty `S` contained in both
  integrability sets, concluding on the intersection strip (which is connected because
  `ProbabilityTheory.convex_integrableExpSet` makes each factor an interval).
* **Route for the signed corollary.** Split `f = f⁺ - f⁻` and form the two finite measures
  `dμ^± = f^± e^{t₀ x} dν` for an interior point `t₀` (finite exactly because of the
  integrability hypothesis at `t₀`). Their Laplace transforms agree on `S - t₀`, so
  `ext_of_integral_exp_eqOn` gives `μ⁺ = μ⁻`; `SigmaFinite ν` then upgrades equality of the
  two `withDensity`s to `f⁺ e^{t₀·} =ᵐ[ν] f⁻ e^{t₀·}`, and positivity of `e^{t₀·}` gives
  `f⁺ =ᵐ[ν] f⁻`, i.e. `f =ᵐ[ν] 0`.
* Both headline statements keep the integrability side conditions as explicit hypotheses:
  without them the Bochner integrals are junk-valued `0` and the conclusion is false.

**Bibliographic comments.** Uniqueness of the (two-sided) Laplace transform on a strip goes
back to M. Lerch ("Sur un point de la théorie des fonctions génératrices d'Abel," *Acta
Math.* **27** (1903), 339–351); the systematic theory, including analyticity in the strip of
convergence and the resulting identity-theorem argument used here, is D. V. Widder's (*The
Laplace Transform*, Princeton University Press, 1941, Ch. II and VI).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.PointEstimation

/-- Tilted-transform identity: the Laplace transform of an exponential tilt is a ratio of
Laplace transforms of the base measure. Both sides are `0` in the degenerate case `μ = 0`. -/
private theorem integral_exp_tilted_mul
    -- USER-INPUT: the base measure; free choice
    {μ : Measure ℝ}
    -- USER-INPUT: the tilting parameter; free choice of the recentering point
    {t₀ : ℝ}
    -- USER-INPUT: the tilt is well defined at `t₀`; otherwise `Measure.tilted` is junk `0`
    (h₀ : Integrable (fun x => Real.exp (t₀ * x)) μ)
    -- USER-INPUT: the evaluation point of the tilted transform
    {t : ℝ}
    -- USER-INPUT: the base transform is finite at `t₀ + t`; otherwise the RHS is junk
    (ht : Integrable (fun x => Real.exp ((t₀ + t) * x)) μ) :
    ∫ x, Real.exp (t * x) ∂(μ.tilted fun x => t₀ * x)
      = (∫ x, Real.exp ((t₀ + t) * x) ∂μ) / ∫ x, Real.exp (t₀ * x) ∂μ := by
  rw [integral_exp_tilted (fun x => t₀ * x) (fun x => t * x)]
  simp only [Pi.add_apply, add_mul]

/-- **Local `Set.EqOn` variant of `ProbabilityTheory.eqOn_complexMGF_of_mgf`.** Mathlib's
version requires the two real moment-generating functions to agree *globally*; here they are
only assumed to agree on an open nonempty set `S` contained in both integrability sets, which
is what the exponential-family applications supply. The conclusion is the equality of the two
`complexMGF`s on the vertical strip over the intersection of the two interiors. -/
private theorem eqOn_complexMGF_of_mgf_eqOn {Ω : Type*} [MeasurableSpace Ω]
    -- USER-INPUT: the two real random variables and their (possibly different) laws
    {X Y : Ω → ℝ} {μ μ' : Measure Ω}
    -- USER-INPUT: the comparison set; open and nonempty so that it accumulates in the strip
    {S : Set ℝ} (hS : IsOpen S) (hS' : S.Nonempty)
    -- USER-INPUT: `S` is inside the integrability set of `X`; makes `mgf X μ` honest on `S`
    (hX : S ⊆ integrableExpSet X μ)
    -- USER-INPUT: same for `Y`
    (hY : S ⊆ integrableExpSet Y μ')
    -- USER-INPUT: the two moment-generating functions agree on `S` (the local hypothesis)
    (hXY : Set.EqOn (mgf X μ) (mgf Y μ') S) :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ')
      {z : ℂ | z.re ∈ interior (integrableExpSet X μ) ∩ interior (integrableExpSet Y μ')} := by
  obtain ⟨s, hsS⟩ := hS'
  have hsX : s ∈ interior (integrableExpSet X μ) := interior_maximal hX hS hsS
  have hsY : s ∈ interior (integrableExpSet Y μ') := interior_maximal hY hS hsS
  have hXan : AnalyticOnNhd ℂ (complexMGF X μ)
      {z : ℂ | z.re ∈ interior (integrableExpSet X μ) ∩ interior (integrableExpSet Y μ')} :=
    analyticOnNhd_complexMGF.mono fun z hz => hz.1
  have hYan : AnalyticOnNhd ℂ (complexMGF Y μ')
      {z : ℂ | z.re ∈ interior (integrableExpSet X μ) ∩ interior (integrableExpSet Y μ')} :=
    analyticOnNhd_complexMGF.mono fun z hz => hz.2
  have hpre : IsPreconnected
      {z : ℂ | z.re ∈ interior (integrableExpSet X μ) ∩ interior (integrableExpSet Y μ')} :=
    (((convex_integrableExpSet (X := X) (μ := μ)).interior.inter
      (convex_integrableExpSet (X := Y) (μ := μ')).interior).linear_preimage
        Complex.reLm).isPreconnected
  have h₀ : (s : ℂ) ∈
      {z : ℂ | z.re ∈ interior (integrableExpSet X μ) ∩ interior (integrableExpSet Y μ')} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_re, Set.mem_inter_iff]
    exact ⟨hsX, hsY⟩
  refine hXan.eqOn_of_preconnected_of_frequently_eq hYan hpre h₀ ?_
  have hfreqR : ∃ᶠ (x : ℝ) in 𝓝[≠] s, complexMGF X μ ↑x = complexMGF Y μ' ↑x := by
    refine Filter.Eventually.frequently ?_
    filter_upwards [nhdsWithin_le_nhds (hS.mem_nhds hsS)] with x hx
    rw [complexMGF_ofReal, complexMGF_ofReal, hXY hx]
  rw [frequently_iff_seq_forall] at hfreqR
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := hfreqR
  rw [frequently_iff_seq_forall]
  refine ⟨fun n => (xs n : ℂ), ?_, fun n => ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  · exact hx_eq n

/-- **Laplace-transform uniqueness, local form.** Two finite measures on `ℝ` whose Laplace
transforms are finite and agree on a set `S` with an interior point coincide. -/
theorem ext_of_integral_exp_eqOn
    -- USER-INPUT: the two measures being compared; genuine external data
    {μ ν : Measure ℝ}
    -- USER-INPUT: both are finite; the conclusion is false for infinite measures with
    -- everywhere-infinite transforms, and `Measure.ext_of_charFun` needs finiteness
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    -- USER-INPUT: the set on which the two transforms are compared; free choice
    {S : Set ℝ}
    -- USER-INPUT: `S` has an interior point; supplies the analytic-continuation seed
    (hS : (interior S).Nonempty)
    -- USER-INPUT: finiteness of the transform of `μ` on `S`; else `∫` is junk-valued `0`
    (hμ : ∀ t ∈ S, Integrable (fun x => Real.exp (t * x)) μ)
    -- USER-INPUT: finiteness of the transform of `ν` on `S`
    (hν : ∀ t ∈ S, Integrable (fun x => Real.exp (t * x)) ν)
    -- USER-INPUT: the two Laplace transforms agree on `S`; the substantive hypothesis
    (h : ∀ t ∈ S, ∫ x, Real.exp (t * x) ∂μ = ∫ x, Real.exp (t * x) ∂ν) :
    μ = ν := by
  obtain ⟨η₀, hη₀⟩ := hS
  have hη₀S : η₀ ∈ S := interior_subset hη₀
  rcases eq_zero_or_neZero μ with hμ0 | hμne
  · have hν0 : ν = 0 := by
      by_contra hc
      have : NeZero ν := ⟨hc⟩
      have hpos := integral_exp_pos (μ := ν) (f := fun x => η₀ * x) (hν η₀ hη₀S)
      rw [← h η₀ hη₀S, hμ0, integral_zero_measure] at hpos
      exact lt_irrefl 0 hpos
    rw [hμ0, hν0]
  · have hνne : NeZero ν := by
      refine ⟨?_⟩
      intro hc
      have hpos := integral_exp_pos (μ := μ) (f := fun x => η₀ * x) (hμ η₀ hη₀S)
      rw [h η₀ hη₀S, hc, integral_zero_measure] at hpos
      exact lt_irrefl 0 hpos
    have hμint : Integrable (fun x => Real.exp (η₀ * x)) μ := hμ η₀ hη₀S
    have hνint : Integrable (fun x => Real.exp (η₀ * x)) ν := hν η₀ hη₀S
    haveI hpμ : IsProbabilityMeasure (μ.tilted fun x => η₀ * x) :=
      isProbabilityMeasure_tilted hμint
    haveI hpν : IsProbabilityMeasure (ν.tilted fun x => η₀ * x) :=
      isProbabilityMeasure_tilted hνint
    set S' : Set ℝ := (fun t => η₀ + t) ⁻¹' interior S with hS'def
    have hS'open : IsOpen S' := isOpen_interior.preimage (by fun_prop)
    have h0S' : (0 : ℝ) ∈ S' := by
      simp only [hS'def, Set.mem_preimage, add_zero]; exact hη₀
    have hS'ne : S'.Nonempty := ⟨0, h0S'⟩
    have hmemS : ∀ t ∈ S', η₀ + t ∈ S := fun t ht => interior_subset ht
    have hsubμ : S' ⊆ integrableExpSet id (μ.tilted fun x => η₀ * x) := by
      intro t ht
      have hmem := hmemS t ht
      change Integrable (fun x => Real.exp (t * id x)) (μ.tilted fun x => η₀ * x)
      rw [integrable_tilted_iff hμint]
      have heq : (fun x => Real.exp (η₀ * x) • Real.exp (t * id x))
          = fun x => Real.exp ((η₀ + t) * x) := by
        funext x; simp only [id_eq, smul_eq_mul, ← Real.exp_add, add_mul]
      rw [heq]; exact hμ _ hmem
    have hsubν : S' ⊆ integrableExpSet id (ν.tilted fun x => η₀ * x) := by
      intro t ht
      have hmem := hmemS t ht
      change Integrable (fun x => Real.exp (t * id x)) (ν.tilted fun x => η₀ * x)
      rw [integrable_tilted_iff hνint]
      have heq : (fun x => Real.exp (η₀ * x) • Real.exp (t * id x))
          = fun x => Real.exp ((η₀ + t) * x) := by
        funext x; simp only [id_eq, smul_eq_mul, ← Real.exp_add, add_mul]
      rw [heq]; exact hν _ hmem
    have hmgf : Set.EqOn (mgf id (μ.tilted fun x => η₀ * x))
        (mgf id (ν.tilted fun x => η₀ * x)) S' := by
      intro t ht
      have hmem := hmemS t ht
      simp only [mgf, id_eq]
      rw [integral_exp_tilted_mul hμint (hμ _ hmem),
        integral_exp_tilted_mul hνint (hν _ hmem), h _ hmem, h η₀ hη₀S]
    have hEq := eqOn_complexMGF_of_mgf_eqOn hS'open hS'ne hsubμ hsubν hmgf
    have hchar : charFun (μ.tilted fun x => η₀ * x) = charFun (ν.tilted fun x => η₀ * x) := by
      funext u
      have h0μ : (0 : ℝ) ∈ interior (integrableExpSet id (μ.tilted fun x => η₀ * x)) :=
        interior_maximal hsubμ hS'open h0S'
      have h0ν : (0 : ℝ) ∈ interior (integrableExpSet id (ν.tilted fun x => η₀ * x)) :=
        interior_maximal hsubν hS'open h0S'
      have hmemU : (↑u * Complex.I) ∈ {z : ℂ | z.re ∈
          interior (integrableExpSet id (μ.tilted fun x => η₀ * x)) ∩
          interior (integrableExpSet id (ν.tilted fun x => η₀ * x))} := by
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Complex.mul_I_re,
          Complex.ofReal_im, neg_zero]
        exact ⟨h0μ, h0ν⟩
      rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
      exact hEq hmemU
    have htilteq : (μ.tilted fun x => η₀ * x) = (ν.tilted fun x => η₀ * x) :=
      Measure.ext_of_charFun hchar
    have hZν : (∫ x, Real.exp (η₀ * x) ∂ν) = ∫ x, Real.exp (η₀ * x) ∂μ := (h η₀ hη₀S).symm
    set D : ℝ → ℝ≥0∞ :=
      fun x => ENNReal.ofReal (Real.exp (η₀ * x) / ∫ y, Real.exp (η₀ * y) ∂μ) with hD
    have hDmeas : Measurable D := by rw [hD]; fun_prop
    have hZpos : 0 < ∫ x, Real.exp (η₀ * x) ∂μ := integral_exp_pos hμint
    have hDne0 : ∀ x, D x ≠ 0 := by
      intro x
      simp only [hD, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact div_pos (Real.exp_pos _) hZpos
    have hDnetop : ∀ x, D x ≠ ∞ := fun x => by simp [hD]
    have hμD : (μ.tilted fun x => η₀ * x) = μ.withDensity D := rfl
    have hνD : (ν.tilted fun x => η₀ * x) = ν.withDensity D := by
      have hrfl : (ν.tilted fun x => η₀ * x)
          = ν.withDensity (fun x => ENNReal.ofReal
            (Real.exp (η₀ * x) / ∫ y, Real.exp (η₀ * y) ∂ν)) := rfl
      rw [hrfl, hD]
      refine withDensity_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      rw [hZν]
    have e1 : (μ.withDensity D).withDensity (fun x => (D x)⁻¹) = μ :=
      withDensity_inv_same hDmeas (Filter.Eventually.of_forall hDne0)
        (Filter.Eventually.of_forall hDnetop)
    have e2 : (ν.withDensity D).withDensity (fun x => (D x)⁻¹) = ν :=
      withDensity_inv_same hDmeas (Filter.Eventually.of_forall hDne0)
        (Filter.Eventually.of_forall hDnetop)
    calc μ = (μ.withDensity D).withDensity (fun x => (D x)⁻¹) := e1.symm
      _ = (ν.withDensity D).withDensity (fun x => (D x)⁻¹) := by
          rw [← hμD, ← hνD, htilteq]
      _ = ν := e2

/-- **Signed corollary.** If the `e^{tx}`-weighted integrals of a measurable `f` vanish for
every `t` in a set with an interior point, then `f` vanishes almost everywhere. This is the
analytic core of completeness for full-rank exponential families. -/
theorem ae_eq_zero_of_integral_exp_smul_eq_zero
    -- USER-INPUT: the reference measure; free choice
    {ν : Measure ℝ}
    -- USER-INPUT: σ-finiteness; needed to read an a.e. equality off equal `withDensity`s
    [SigmaFinite ν]
    -- USER-INPUT: the candidate function (an unbiased estimator of `0` in applications)
    {f : ℝ → ℝ} (hf : Measurable f)
    -- USER-INPUT: the parameter set; free choice
    {S : Set ℝ}
    -- USER-INPUT: `S` has an interior point; supplies the analytic-continuation seed
    (hS : (interior S).Nonempty)
    -- USER-INPUT: the weighted integrals exist on `S`; else `∫` is junk-valued `0`
    (hint : ∀ t ∈ S, Integrable (fun x => f x * Real.exp (t * x)) ν)
    -- USER-INPUT: the weighted integrals vanish on `S`; the substantive hypothesis
    (h : ∀ t ∈ S, ∫ x, f x * Real.exp (t * x) ∂ν = 0) :
    f =ᵐ[ν] 0 := by
  obtain ⟨η₀, hη₀⟩ := hS
  have hη₀S : η₀ ∈ S := interior_subset hη₀
  have hF : Integrable (fun x => f x * Real.exp (η₀ * x)) ν := hint η₀ hη₀S
  set Dp : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (max (f x * Real.exp (η₀ * x)) 0) with hDp
  set Dn : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (max (-(f x * Real.exp (η₀ * x))) 0) with hDn
  have hDpmeas : Measurable Dp := by rw [hDp]; fun_prop
  have hDnmeas : Measurable Dn := by rw [hDn]; fun_prop
  haveI hfinp : IsFiniteMeasure (ν.withDensity Dp) :=
    isFiniteMeasure_withDensity_ofReal hF.pos_part.2
  haveI hfinn : IsFiniteMeasure (ν.withDensity Dn) :=
    isFiniteMeasure_withDensity_ofReal hF.neg_part.2
  set S' : Set ℝ := (fun t => η₀ + t) ⁻¹' interior S with hS'def
  have hS'open : IsOpen S' := isOpen_interior.preimage (by fun_prop)
  have h0S' : (0 : ℝ) ∈ S' := by
    simp only [hS'def, Set.mem_preimage, add_zero]; exact hη₀
  have hintS' : (interior S').Nonempty := by rw [hS'open.interior_eq]; exact ⟨0, h0S'⟩
  have hpm : ∀ a : ℝ, max a 0 - max (-a) 0 = a := by
    intro a
    rcases le_total 0 a with ha | ha
    · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0)]; ring
    · rw [max_eq_right ha, max_eq_left (by linarith : (0 : ℝ) ≤ -a)]; ring
  have hIexp : ∀ t ∈ S', Integrable (fun x => Real.exp (t * x)) (ν.withDensity Dp) := by
    intro t ht
    have hmem : η₀ + t ∈ S := interior_subset ht
    rw [integrable_withDensity_iff_integrable_smul' hDpmeas
      (Filter.Eventually.of_forall fun x => by simp [hDp])]
    have hrw : (fun x => (Dp x).toReal • Real.exp (t * x))
        = fun x => max (f x * Real.exp ((η₀ + t) * x)) 0 := by
      funext x
      simp only [hDp, smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _)]
      rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _), zero_mul]
      congr 1; rw [mul_assoc, ← Real.exp_add, ← add_mul]
    rw [hrw]; exact (hint _ hmem).pos_part
  have hIexpn : ∀ t ∈ S', Integrable (fun x => Real.exp (t * x)) (ν.withDensity Dn) := by
    intro t ht
    have hmem : η₀ + t ∈ S := interior_subset ht
    rw [integrable_withDensity_iff_integrable_smul' hDnmeas
      (Filter.Eventually.of_forall fun x => by simp [hDn])]
    have hrw : (fun x => (Dn x).toReal • Real.exp (t * x))
        = fun x => max (-(f x * Real.exp ((η₀ + t) * x))) 0 := by
      funext x
      simp only [hDn, smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _)]
      rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _), zero_mul]
      congr 1; rw [neg_mul, mul_assoc, ← Real.exp_add, ← add_mul]
    rw [hrw]; exact (hint _ hmem).neg_part
  have htrans : ∀ t ∈ S', ∫ x, Real.exp (t * x) ∂(ν.withDensity Dp)
      = ∫ x, Real.exp (t * x) ∂(ν.withDensity Dn) := by
    intro t ht
    have hmem : η₀ + t ∈ S := interior_subset ht
    have hG : Integrable (fun x => f x * Real.exp ((η₀ + t) * x)) ν := hint _ hmem
    rw [integral_withDensity_eq_integral_toReal_smul hDpmeas
        (Filter.Eventually.of_forall fun x => by simp [hDp]),
      integral_withDensity_eq_integral_toReal_smul hDnmeas
        (Filter.Eventually.of_forall fun x => by simp [hDn])]
    have hp : (fun x => (Dp x).toReal • Real.exp (t * x))
        = fun x => max (f x * Real.exp ((η₀ + t) * x)) 0 := by
      funext x
      simp only [hDp, smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _)]
      rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _), zero_mul]
      congr 1; rw [mul_assoc, ← Real.exp_add, ← add_mul]
    have hn : (fun x => (Dn x).toReal • Real.exp (t * x))
        = fun x => max (-(f x * Real.exp ((η₀ + t) * x))) 0 := by
      funext x
      simp only [hDn, smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _)]
      rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _), zero_mul]
      congr 1; rw [neg_mul, mul_assoc, ← Real.exp_add, ← add_mul]
    rw [hp, hn]
    have hde : (fun x => f x * Real.exp ((η₀ + t) * x))
        = fun x => max (f x * Real.exp ((η₀ + t) * x)) 0
          - max (-(f x * Real.exp ((η₀ + t) * x))) 0 := by
      funext x; rw [hpm]
    have hz := h _ hmem
    rw [hde, integral_sub hG.pos_part hG.neg_part, sub_eq_zero] at hz
    exact hz
  have hμeq : ν.withDensity Dp = ν.withDensity Dn :=
    ext_of_integral_exp_eqOn hintS' hIexp hIexpn htrans
  have hDeq : Dp =ᵐ[ν] Dn :=
    (withDensity_eq_iff_of_sigmaFinite hDpmeas.aemeasurable hDnmeas.aemeasurable).mp hμeq
  filter_upwards [hDeq] with x hx
  have hxx : max (f x * Real.exp (η₀ * x)) 0 = max (-(f x * Real.exp (η₀ * x))) 0 := by
    have hct := congrArg ENNReal.toReal hx
    simpa only [hDp, hDn, ENNReal.toReal_ofReal (le_max_right _ _)] using hct
  have hF0 : f x * Real.exp (η₀ * x) = 0 := by
    rcases le_total 0 (f x * Real.exp (η₀ * x)) with hle | hle
    · rw [max_eq_left hle,
        max_eq_right (by linarith : -(f x * Real.exp (η₀ * x)) ≤ 0)] at hxx
      exact hxx
    · rw [max_eq_right hle,
        max_eq_left (by linarith : (0 : ℝ) ≤ -(f x * Real.exp (η₀ * x)))] at hxx
      linarith
  have hf0 : f x = 0 := by
    rcases mul_eq_zero.mp hF0 with h1 | h2
    · exact h1
    · exact absurd h2 (Real.exp_pos _).ne'
  simpa using hf0

end StatLean.PointEstimation
