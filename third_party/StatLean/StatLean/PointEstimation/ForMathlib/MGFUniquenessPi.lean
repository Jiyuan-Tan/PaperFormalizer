module
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import StatLean.PointEstimation.ForMathlib.MGFUniqueness

@[expose] public section

/-!
# Laplace-transform uniqueness on a set with nonempty interior (`s` dimensions)

The `s`-dimensional analogue of the one-dimensional statements: two finite measures on
`EuclideanSpace ℝ (Fin s)` whose Laplace transforms `t ↦ ∫ e^{⟪t, x⟫} dμ(x)` are finite and
agree on a set `S` with an interior point are equal, together with the signed corollary for a
function whose weighted integrals vanish on `S`.

* `ext_of_integral_exp_inner_eqOn` — measure uniqueness;
* `ae_eq_zero_of_integral_exp_inner_eq_zero` — the signed corollary.

The multivariate form is what completeness of an `s`-parameter full-rank exponential family
consumes: the natural parameter set has nonempty interior in `ℝ^s`, and the vanishing
condition on an unbiased estimator of `0` holds only there.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.5
(Exponential Families), supporting material for the identifiability of the canonical
parametrization in `s` dimensions (equation (5.2), Definition 5.2). (`TPE2 §1.5 (5.2), Def
5.2`.)

**Proof formalization notes.**
* **Route.** Fix `t₀ ∈ interior S` and a small box `t₀ + (-ε, ε)^s ⊆ S`. Recenter by tilting
  both measures at `t₀`, so that both become probability measures (the degenerate branch
  `μ = 0` is separated first, `e^{⟪t₀,x⟫} > 0` forcing `∫ e^{⟪t₀,x⟫} dμ = 0 ↔ μ = 0`). Then
  continue **one coordinate at a time**: with the other `s - 1` coordinates frozen at real
  values inside the box, `z ↦ ∫ exp(⟪t, x⟫ + z·xᵢ) dμ` is analytic on the vertical strip
  `|Re z| < ε` (dominated differentiation, as in `analyticOnNhd_complexMGF`), the two such
  functions agree on the real segment `(-ε, ε)`, hence agree on the whole strip by the
  identity theorem `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`; evaluating at
  `z = -I·vᵢ` moves coordinate `i` to the imaginary axis. Iterating over `i = 1, …, s` moves
  all coordinates, producing equality of the two characteristic functions at every
  `v ∈ ℝ^s`. `MeasureTheory.Measure.ext_of_charFun` (available since
  `EuclideanSpace ℝ (Fin s)` is a complete second-countable real inner-product space) closes,
  and untilting via `MeasureTheory.withDensity_inv_same` returns to the original measures.

  The formalization realizes this multi-coordinate continuation through the **one-dimensional
  projections**: for the tilted probability measures `μ' , ν'` (with `0` an interior point of
  the recentered parameter box), each direction `t` gives a pushforward `x ↦ ⟪t, x⟫` whose
  one-dimensional Laplace transforms agree on an interval around `0`; the already-proved
  one-dimensional uniqueness `ext_of_integral_exp_eqOn` forces the pushforwards equal, hence
  the two characteristic functions agree at `t`, and `Measure.ext_of_charFun` closes. This is
  the Cramér–Wold packaging of the same analytic continuation.
* The prose template for the per-coordinate strip continuation is
  `StatLean/AsymptoticStatistics/ForMathlib/BivariateMGFUniqueness.lean` (`s = 2` with one
  coordinate already on the imaginary axis). It is deliberately **not** imported: this file
  belongs to the `ForMathlib` layer, whose imports stay Mathlib-only, and the bivariate file
  is specialized to the Gaussian-marginal hypothesis it was written for.
* The carrier is `EuclideanSpace ℝ (Fin s)` rather than `Fin s → ℝ` so that `⟪·, ·⟫_ℝ` and
  `Measure.ext_of_charFun` are available without a `WithLp` transport step.
* The integrability side conditions are kept explicit: without them the Bochner integrals are
  junk-valued `0` and the conclusions are false.

**Bibliographic comments.** The one-dimensional statement is due to M. Lerch ("Sur un point
de la théorie des fonctions génératrices d'Abel," *Acta Math.* **27** (1903), 339–351); the
strip-analyticity technique and the multidimensional extension follow D. V. Widder (*The
Laplace Transform*, Princeton University Press, 1941, Ch. II and VI).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {s : ℕ}

/-- **Multivariate Laplace-transform uniqueness, local form.** Two finite measures on
`EuclideanSpace ℝ (Fin s)` whose Laplace transforms are finite and agree on a set `S` with an
interior point coincide. -/
theorem ext_of_integral_exp_inner_eqOn
    -- USER-INPUT: the two measures being compared; genuine external data
    {μ ν : Measure (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: both are finite; required by `Measure.ext_of_charFun` and by the tilt
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    -- USER-INPUT: the parameter set on which the transforms are compared; free choice
    {S : Set (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: `S` has an interior point; supplies the box for the coordinatewise
    -- analytic continuation
    (hS : (interior S).Nonempty)
    -- USER-INPUT: finiteness of the transform of `μ` on `S`; else `∫` is junk-valued `0`
    (hμ : ∀ t ∈ S, Integrable (fun x => Real.exp ⟪t, x⟫_ℝ) μ)
    -- USER-INPUT: finiteness of the transform of `ν` on `S`
    (hν : ∀ t ∈ S, Integrable (fun x => Real.exp ⟪t, x⟫_ℝ) ν)
    -- USER-INPUT: the two Laplace transforms agree on `S`; the substantive hypothesis
    (h : ∀ t ∈ S, ∫ x, Real.exp ⟪t, x⟫_ℝ ∂μ = ∫ x, Real.exp ⟪t, x⟫_ℝ ∂ν) :
    μ = ν := by
  obtain ⟨t₀, ht₀⟩ := hS
  have ht₀S : t₀ ∈ S := interior_subset ht₀
  set φ : EuclideanSpace ℝ (Fin s) → ℝ := fun x => ⟪t₀, x⟫_ℝ with hφ
  rcases eq_zero_or_neZero μ with hμ0 | hμne
  · have hν0 : ν = 0 := by
      by_contra hc
      have : NeZero ν := ⟨hc⟩
      have hpos := integral_exp_pos (μ := ν) (f := φ) (hν t₀ ht₀S)
      rw [← h t₀ ht₀S, hμ0, integral_zero_measure] at hpos
      exact lt_irrefl 0 hpos
    rw [hμ0, hν0]
  · have hνne : NeZero ν := by
      refine ⟨?_⟩
      intro hc
      have hpos := integral_exp_pos (μ := μ) (f := φ) (hμ t₀ ht₀S)
      rw [h t₀ ht₀S, hc, integral_zero_measure] at hpos
      exact lt_irrefl 0 hpos
    have hμint : Integrable (fun x => Real.exp (φ x)) μ := hμ t₀ ht₀S
    have hνint : Integrable (fun x => Real.exp (φ x)) ν := hν t₀ ht₀S
    haveI hpμ : IsProbabilityMeasure (μ.tilted φ) := isProbabilityMeasure_tilted hμint
    haveI hpν : IsProbabilityMeasure (ν.tilted φ) := isProbabilityMeasure_tilted hνint
    have hZ : (∫ x, Real.exp (φ x) ∂μ) = ∫ x, Real.exp (φ x) ∂ν := h t₀ ht₀S
    -- Tilted Laplace transforms agree on the recentered box.
    have htrans' : ∀ a, t₀ + a ∈ S →
        (∫ x, Real.exp ⟪a, x⟫_ℝ ∂(μ.tilted φ))
          = ∫ x, Real.exp ⟪a, x⟫_ℝ ∂(ν.tilted φ) := by
      intro a ha
      rw [integral_exp_tilted (μ := μ) φ (fun x => ⟪a, x⟫_ℝ),
          integral_exp_tilted (μ := ν) φ (fun x => ⟪a, x⟫_ℝ)]
      have hnumμ : (∫ x, Real.exp ((φ + fun x => ⟪a, x⟫_ℝ) x) ∂μ)
          = ∫ x, Real.exp ⟪t₀ + a, x⟫_ℝ ∂μ := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [Pi.add_apply, hφ, inner_add_left]
      have hnumν : (∫ x, Real.exp ((φ + fun x => ⟪a, x⟫_ℝ) x) ∂ν)
          = ∫ x, Real.exp ⟪t₀ + a, x⟫_ℝ ∂ν := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [Pi.add_apply, hφ, inner_add_left]
      rw [hnumμ, hnumν, h (t₀ + a) ha, hZ]
    -- Tilted transforms are integrable on the recentered box.
    have hintTilt : ∀ (ρ : Measure (EuclideanSpace ℝ (Fin s))),
        Integrable (fun x => Real.exp (φ x)) ρ →
        (∀ t ∈ S, Integrable (fun x => Real.exp ⟪t, x⟫_ℝ) ρ) →
        ∀ a, t₀ + a ∈ S → Integrable (fun x => Real.exp ⟪a, x⟫_ℝ) (ρ.tilted φ) := by
      intro ρ hρexp hρ a ha
      rw [integrable_tilted_iff hρexp]
      have heq : (fun x => Real.exp (φ x) • Real.exp ⟪a, x⟫_ℝ)
          = fun x => Real.exp ⟪t₀ + a, x⟫_ℝ := by
        funext x
        simp only [hφ, smul_eq_mul, ← Real.exp_add, inner_add_left]
      rw [heq]
      exact hρ _ ha
    have hμ'int := hintTilt μ hμint hμ
    have hν'int := hintTilt ν hνint hν
    -- The two tilted measures have equal characteristic functions.
    have hchar : charFun (μ.tilted φ) = charFun (ν.tilted φ) := by
      funext t
      have hgmeas : Measurable (fun x : EuclideanSpace ℝ (Fin s) => ⟪t, x⟫_ℝ) := by fun_prop
      -- recentered box, as a set of scalars along direction `t`
      set W : Set (EuclideanSpace ℝ (Fin s)) := (fun a => t₀ + a) ⁻¹' interior S with hW
      have hWopen : IsOpen W := isOpen_interior.preimage (by fun_prop)
      have h0W : (0 : EuclideanSpace ℝ (Fin s)) ∈ W := by
        simp only [hW, Set.mem_preimage, add_zero]; exact ht₀
      set St : Set ℝ := (fun r : ℝ => r • t) ⁻¹' W with hSt
      have hStopen : IsOpen St := hWopen.preimage (by fun_prop)
      have h0St : (0 : ℝ) ∈ St := by
        simp only [hSt, Set.mem_preimage, zero_smul]; exact h0W
      have hStint : (interior St).Nonempty := by
        rw [hStopen.interior_eq]; exact ⟨0, h0St⟩
      have hmemS : ∀ r ∈ St, t₀ + r • t ∈ S := fun r hr => interior_subset hr
      haveI : IsProbabilityMeasure ((μ.tilted φ).map (fun x => ⟪t, x⟫_ℝ)) :=
        Measure.isProbabilityMeasure_map hgmeas.aemeasurable
      haveI : IsProbabilityMeasure ((ν.tilted φ).map (fun x => ⟪t, x⟫_ℝ)) :=
        Measure.isProbabilityMeasure_map hgmeas.aemeasurable
      -- integrability of the pushforward Laplace transforms
      have hPint : ∀ (ρ : Measure (EuclideanSpace ℝ (Fin s))),
          (∀ a, t₀ + a ∈ S → Integrable (fun x => Real.exp ⟪a, x⟫_ℝ) (ρ.tilted φ)) →
          ∀ r ∈ St, Integrable (fun y => Real.exp (r * y))
            ((ρ.tilted φ).map (fun x => ⟪t, x⟫_ℝ)) := by
        intro ρ hρ r hr
        rw [integrable_map_measure (by fun_prop) hgmeas.aemeasurable]
        have hcomp : ((fun y => Real.exp (r * y)) ∘ fun x => ⟪t, x⟫_ℝ)
            = fun x => Real.exp ⟪r • t, x⟫_ℝ := by
          funext x
          simp only [Function.comp_apply, real_inner_smul_left]
        rw [hcomp]
        exact hρ (r • t) (hmemS r hr)
      -- pushforward Laplace transforms agree on `St`
      have hPtrans : ∀ r ∈ St, ∫ y, Real.exp (r * y) ∂((μ.tilted φ).map (fun x => ⟪t, x⟫_ℝ))
          = ∫ y, Real.exp (r * y) ∂((ν.tilted φ).map (fun x => ⟪t, x⟫_ℝ)) := by
        intro r hr
        rw [integral_map hgmeas.aemeasurable (by fun_prop),
            integral_map hgmeas.aemeasurable (by fun_prop)]
        have hcomp : ∀ x : EuclideanSpace ℝ (Fin s),
            Real.exp (r * ⟪t, x⟫_ℝ) = Real.exp ⟪r • t, x⟫_ℝ := by
          intro x; rw [real_inner_smul_left]
        simp only [hcomp]
        exact htrans' (r • t) (hmemS r hr)
      have hpush : (μ.tilted φ).map (fun x => ⟪t, x⟫_ℝ)
          = (ν.tilted φ).map (fun x => ⟪t, x⟫_ℝ) :=
        ext_of_integral_exp_eqOn hStint (hPint μ hμ'int) (hPint ν hν'int) hPtrans
      -- bridge the characteristic function through the pushforward
      have hbridge : ∀ (ρ : Measure (EuclideanSpace ℝ (Fin s))),
          charFun ρ t = ∫ y : ℝ, Complex.exp ((y : ℂ) * Complex.I)
            ∂(ρ.map (fun x => ⟪t, x⟫_ℝ)) := by
        intro ρ
        rw [charFun_apply, integral_map hgmeas.aemeasurable (by fun_prop)]
        refine integral_congr_ae (.of_forall fun x => ?_)
        change Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I)
          = Complex.exp ((⟪t, x⟫_ℝ : ℂ) * Complex.I)
        rw [real_inner_comm t x]
      rw [hbridge (μ.tilted φ), hbridge (ν.tilted φ), hpush]
    have htilteq : (μ.tilted φ) = (ν.tilted φ) := Measure.ext_of_charFun hchar
    -- Untilt: both tilted measures are `withDensity` by the same strictly positive density.
    set Dfun : EuclideanSpace ℝ (Fin s) → ℝ≥0∞ :=
      fun x => ENNReal.ofReal (Real.exp (φ x) / ∫ y, Real.exp (φ y) ∂μ) with hDfun
    have hDmeas : Measurable Dfun := by rw [hDfun]; fun_prop
    have hZpos : 0 < ∫ x, Real.exp (φ x) ∂μ := integral_exp_pos hμint
    have hDne0 : ∀ x, Dfun x ≠ 0 := by
      intro x
      simp only [hDfun, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact div_pos (Real.exp_pos _) hZpos
    have hDnetop : ∀ x, Dfun x ≠ ∞ := fun x => by simp [hDfun]
    have hμD : (μ.tilted φ) = μ.withDensity Dfun := rfl
    have hνD : (ν.tilted φ) = ν.withDensity Dfun := by
      have hrfl : (ν.tilted φ)
          = ν.withDensity (fun x => ENNReal.ofReal
            (Real.exp (φ x) / ∫ y, Real.exp (φ y) ∂ν)) := rfl
      rw [hrfl, hDfun]
      refine withDensity_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      rw [hZ]
    have e1 : (μ.withDensity Dfun).withDensity (fun x => (Dfun x)⁻¹) = μ :=
      withDensity_inv_same hDmeas (Filter.Eventually.of_forall hDne0)
        (Filter.Eventually.of_forall hDnetop)
    have e2 : (ν.withDensity Dfun).withDensity (fun x => (Dfun x)⁻¹) = ν :=
      withDensity_inv_same hDmeas (Filter.Eventually.of_forall hDne0)
        (Filter.Eventually.of_forall hDnetop)
    calc μ = (μ.withDensity Dfun).withDensity (fun x => (Dfun x)⁻¹) := e1.symm
      _ = (ν.withDensity Dfun).withDensity (fun x => (Dfun x)⁻¹) := by
          rw [← hμD, ← hνD, htilteq]
      _ = ν := e2

/-- **Multivariate signed corollary.** If the `e^{⟪t, x⟫}`-weighted integrals of a measurable
`f` vanish for every `t` in a set with an interior point, then `f` vanishes almost
everywhere. This is the analytic core of completeness for `s`-parameter full-rank exponential
families. -/
theorem ae_eq_zero_of_integral_exp_inner_eq_zero
    -- USER-INPUT: the reference measure; free choice
    {ν : Measure (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: σ-finiteness; needed to read an a.e. equality off equal `withDensity`s
    [SigmaFinite ν]
    -- USER-INPUT: the candidate function (an unbiased estimator of `0` in applications)
    {f : EuclideanSpace ℝ (Fin s) → ℝ} (hf : Measurable f)
    -- USER-INPUT: the parameter set; free choice
    {S : Set (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: `S` has an interior point; supplies the analytic-continuation box
    (hS : (interior S).Nonempty)
    -- USER-INPUT: the weighted integrals exist on `S`; else `∫` is junk-valued `0`
    (hint : ∀ t ∈ S, Integrable (fun x => f x * Real.exp ⟪t, x⟫_ℝ) ν)
    -- USER-INPUT: the weighted integrals vanish on `S`; the substantive hypothesis
    (h : ∀ t ∈ S, ∫ x, f x * Real.exp ⟪t, x⟫_ℝ ∂ν = 0) :
    f =ᵐ[ν] 0 := by
  obtain ⟨η₀, hη₀⟩ := hS
  have hη₀S : η₀ ∈ S := interior_subset hη₀
  have hF : Integrable (fun x => f x * Real.exp ⟪η₀, x⟫_ℝ) ν := hint η₀ hη₀S
  set Dp : EuclideanSpace ℝ (Fin s) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (max (f x * Real.exp ⟪η₀, x⟫_ℝ) 0) with hDp
  set Dn : EuclideanSpace ℝ (Fin s) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (max (-(f x * Real.exp ⟪η₀, x⟫_ℝ)) 0) with hDn
  have hDpmeas : Measurable Dp := by rw [hDp]; fun_prop
  have hDnmeas : Measurable Dn := by rw [hDn]; fun_prop
  haveI hfinp : IsFiniteMeasure (ν.withDensity Dp) :=
    isFiniteMeasure_withDensity_ofReal hF.pos_part.2
  haveI hfinn : IsFiniteMeasure (ν.withDensity Dn) :=
    isFiniteMeasure_withDensity_ofReal hF.neg_part.2
  set S' : Set (EuclideanSpace ℝ (Fin s)) := (fun t => η₀ + t) ⁻¹' interior S with hS'def
  have hS'open : IsOpen S' := isOpen_interior.preimage (by fun_prop)
  have h0S' : (0 : EuclideanSpace ℝ (Fin s)) ∈ S' := by
    simp only [hS'def, Set.mem_preimage, add_zero]; exact hη₀
  have hintS' : (interior S').Nonempty := by rw [hS'open.interior_eq]; exact ⟨0, h0S'⟩
  have hpm : ∀ a : ℝ, max a 0 - max (-a) 0 = a := by
    intro a
    rcases le_total 0 a with ha | ha
    · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0)]; ring
    · rw [max_eq_right ha, max_eq_left (by linarith : (0 : ℝ) ≤ -a)]; ring
  have hIexp : ∀ t ∈ S', Integrable (fun x => Real.exp ⟪t, x⟫_ℝ) (ν.withDensity Dp) := by
    intro t ht
    have hmem : η₀ + t ∈ S := interior_subset ht
    rw [integrable_withDensity_iff_integrable_smul' hDpmeas
      (Filter.Eventually.of_forall fun x => by simp [hDp])]
    have hrw : (fun x => (Dp x).toReal • Real.exp ⟪t, x⟫_ℝ)
        = fun x => max (f x * Real.exp ⟪η₀ + t, x⟫_ℝ) 0 := by
      funext x
      simp only [hDp, smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _)]
      rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _), zero_mul]
      congr 1; rw [mul_assoc, ← Real.exp_add, ← inner_add_left]
    rw [hrw]; exact (hint _ hmem).pos_part
  have hIexpn : ∀ t ∈ S', Integrable (fun x => Real.exp ⟪t, x⟫_ℝ) (ν.withDensity Dn) := by
    intro t ht
    have hmem : η₀ + t ∈ S := interior_subset ht
    rw [integrable_withDensity_iff_integrable_smul' hDnmeas
      (Filter.Eventually.of_forall fun x => by simp [hDn])]
    have hrw : (fun x => (Dn x).toReal • Real.exp ⟪t, x⟫_ℝ)
        = fun x => max (-(f x * Real.exp ⟪η₀ + t, x⟫_ℝ)) 0 := by
      funext x
      simp only [hDn, smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _)]
      rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _), zero_mul]
      congr 1; rw [neg_mul, mul_assoc, ← Real.exp_add, ← inner_add_left]
    rw [hrw]; exact (hint _ hmem).neg_part
  have htrans : ∀ t ∈ S', ∫ x, Real.exp ⟪t, x⟫_ℝ ∂(ν.withDensity Dp)
      = ∫ x, Real.exp ⟪t, x⟫_ℝ ∂(ν.withDensity Dn) := by
    intro t ht
    have hmem : η₀ + t ∈ S := interior_subset ht
    have hG : Integrable (fun x => f x * Real.exp ⟪η₀ + t, x⟫_ℝ) ν := hint _ hmem
    rw [integral_withDensity_eq_integral_toReal_smul hDpmeas
        (Filter.Eventually.of_forall fun x => by simp [hDp]),
      integral_withDensity_eq_integral_toReal_smul hDnmeas
        (Filter.Eventually.of_forall fun x => by simp [hDn])]
    have hp : (fun x => (Dp x).toReal • Real.exp ⟪t, x⟫_ℝ)
        = fun x => max (f x * Real.exp ⟪η₀ + t, x⟫_ℝ) 0 := by
      funext x
      simp only [hDp, smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _)]
      rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _), zero_mul]
      congr 1; rw [mul_assoc, ← Real.exp_add, ← inner_add_left]
    have hn : (fun x => (Dn x).toReal • Real.exp ⟪t, x⟫_ℝ)
        = fun x => max (-(f x * Real.exp ⟪η₀ + t, x⟫_ℝ)) 0 := by
      funext x
      simp only [hDn, smul_eq_mul, ENNReal.toReal_ofReal (le_max_right _ _)]
      rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _), zero_mul]
      congr 1; rw [neg_mul, mul_assoc, ← Real.exp_add, ← inner_add_left]
    rw [hp, hn]
    have hde : (fun x => f x * Real.exp ⟪η₀ + t, x⟫_ℝ)
        = fun x => max (f x * Real.exp ⟪η₀ + t, x⟫_ℝ) 0
          - max (-(f x * Real.exp ⟪η₀ + t, x⟫_ℝ)) 0 := by
      funext x; rw [hpm]
    have hz := h _ hmem
    rw [hde, integral_sub hG.pos_part hG.neg_part, sub_eq_zero] at hz
    exact hz
  have hμeq : ν.withDensity Dp = ν.withDensity Dn :=
    ext_of_integral_exp_inner_eqOn hintS' hIexp hIexpn htrans
  have hDeq : Dp =ᵐ[ν] Dn :=
    (withDensity_eq_iff_of_sigmaFinite hDpmeas.aemeasurable hDnmeas.aemeasurable).mp hμeq
  filter_upwards [hDeq] with x hx
  have hxx : max (f x * Real.exp ⟪η₀, x⟫_ℝ) 0 = max (-(f x * Real.exp ⟪η₀, x⟫_ℝ)) 0 := by
    have hct := congrArg ENNReal.toReal hx
    simpa only [hDp, hDn, ENNReal.toReal_ofReal (le_max_right _ _)] using hct
  have hF0 : f x * Real.exp ⟪η₀, x⟫_ℝ = 0 := by
    rcases le_total 0 (f x * Real.exp ⟪η₀, x⟫_ℝ) with hle | hle
    · rw [max_eq_left hle,
        max_eq_right (by linarith : -(f x * Real.exp ⟪η₀, x⟫_ℝ) ≤ 0)] at hxx
      exact hxx
    · rw [max_eq_right hle,
        max_eq_left (by linarith : (0 : ℝ) ≤ -(f x * Real.exp ⟪η₀, x⟫_ℝ))] at hxx
      linarith
  have hf0 : f x = 0 := by
    rcases mul_eq_zero.mp hF0 with h1 | h2
    · exact h1
    · exact absurd h2 (Real.exp_pos _).ne'
  simpa using hf0

end StatLean.PointEstimation
