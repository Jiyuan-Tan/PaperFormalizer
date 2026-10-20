module
public import StatLean.PointEstimation.ExponentialFamily.Basic
public import StatLean.PointEstimation.ForMathlib.IntegrationByPartsReal
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Probability.Notation

@[expose] public section

/-!
# Stein's identity for a one-parameter exponential family on the line

Let `X` have the one-parameter density `exp(η·T(x) − A(η))·h(x)` with respect to Lebesgue
measure on the line, and let `g` be differentiable with `E_η|g'(X)| < ∞`. Integration by
parts on the whole line gives
$$ E_\eta\Bigl[\Bigl(\tfrac{h'(X)}{h(X)} + \eta\,T'(X)\Bigr)\,g(X)\Bigr]
   \;=\; -\,E_\eta\bigl[g'(X)\bigr], $$
provided the boundary term `g(x)·e^{η T(x)}·h(x)` vanishes at both ends of the support. The
bracketed factor is the derivative of the log-density with respect to `x` — the "score in the
sample argument" — so the identity says that this score is orthogonal to differentiation.

* `ExpFamily.stein_identity` — the identity for a support equal to the whole line.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.5
(Exponential Families), Lemma 5.15 (Stein's identity). (`TPE2 §1.5 Lem 5.15`.)

**Proof formalization notes.**
* The setup is pinned by the hypothesis `E.base = volume.withDensity (ENNReal.ofReal ∘ h)`
  rather than by building the family with `ExpFamily.ofDensity`: this leaves the natural
  statistic `E.stat` as the family's own field, so the conclusion is stated directly about
  `E.P η` and composes with the rest of the area without a rewriting step.
* Nonnegativity of the carrier is a genuine requirement, not bookkeeping: `ENNReal.ofReal`
  truncates negative values, so without it `E.base` would not be the measure with density `h`
  and the logarithmic derivative `h'/h` would not describe it. On `{h = 0}` the quotient
  `h'/h` takes Lean's junk value `0`; that set is `E.base`-null, so the integrand is
  determined `P_η`-almost everywhere and the statement is unaffected.
* The boundary hypothesis is stated with the factor `g` included, i.e. as decay of
  `g·e^{⟨η,T⟩}·h` rather than of `e^{⟨η,T⟩}·h` alone. This is what integration by parts
  actually needs; the classical formulation, which asks only for decay of `e^{⟨η,T⟩}·h`,
  leaves the growth of `g` implicit. Ours is therefore the safe (weaker) form.
* The two integrability hypotheses are the classical `E_η|g'(X)| < ∞` together with the
  integrability of the left-hand integrand, which the classical statement leaves implicit.
  Without the latter Lean's Bochner integral would silently return `0` on the left and the
  identity would assert something false about a divergent expectation.
* The variant for a support equal to a bounded interval `(a, b)` — where the boundary
  condition becomes decay at `a` and `b` — is not formalized here; it is the same integration
  by parts with the limits taken along `𝓝[>] a` and `𝓝[<] b`.

**Bibliographic comments.** The identity for the normal distribution is due to C. Stein
("Estimation of the mean of a multivariate normal distribution," *Ann. Statist.* **9**
(1981), 1135–1151). Its extension to general exponential families, in the form used here, is
due to H. M. Hudson ("A natural identity for exponential families with applications in
multiparameter estimation," *Ann. Statist.* **6** (1978), 473–484).
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Topology

namespace StatLean.PointEstimation

namespace ExpFamily

/-- **Stein's identity** for a one-parameter exponential family on the line with carrier
`densityH` against Lebesgue measure and support the whole line. -/
theorem stein_identity (E : ExpFamily ℝ ℝ) (densityH g : ℝ → ℝ) (η : ℝ)
    -- USER-INPUT: the reference measure is Lebesgue measure weighted by the carrier `h`;
    -- this is the setting in which the identity is classically stated
    (hbase : E.base = volume.withDensity fun x => ENNReal.ofReal (densityH x))
    -- USER-INPUT: the carrier is nonnegative; a density
    (hH0 : ∀ x, 0 ≤ densityH x)
    -- USER-INPUT: nondegenerate reference measure, so that `E.P η` is a probability measure
    (hbase0 : E.base ≠ 0)
    -- USER-INPUT: the carrier is differentiable, so that `h'/h` is defined
    (hHdiff : Differentiable ℝ densityH)
    -- USER-INPUT: the natural statistic is differentiable, so that `T'` is defined
    (hTdiff : Differentiable ℝ E.stat)
    -- USER-INPUT: `g` is differentiable; the classical hypothesis on the test function
    (hgdiff : Differentiable ℝ g)
    -- USER-INPUT: the natural parameter lies where the family is defined
    (hη : η ∈ E.natSet)
    -- USER-INPUT: `E_η|g'(X)| < ∞`; the classical integrability hypothesis
    (hg' : Integrable (fun x => deriv g x) (E.P η))
    -- USER-INPUT: integrability of the left-hand integrand; left implicit in the classical
    -- statement but needed for the expectation on the left to be the stated one
    (hscore : Integrable
      (fun x => (deriv densityH x / densityH x + η * deriv E.stat x) * g x) (E.P η))
    -- USER-INPUT: the boundary term vanishes at `+∞`; the classical support condition
    (hTop : Tendsto (fun x => g x * Real.exp ⟪η, E.stat x⟫_ℝ * densityH x) atTop (𝓝 0))
    -- USER-INPUT: the boundary term vanishes at `−∞`; the classical support condition
    (hBot : Tendsto (fun x => g x * Real.exp ⟪η, E.stat x⟫_ℝ * densityH x) atBot (𝓝 0)) :
    ∫ x, (deriv densityH x / densityH x + η * deriv E.stat x) * g x ∂(E.P η)
      = -∫ x, deriv g x ∂(E.P η) := by
  -- inner product on ℝ is multiplication
  have hinner : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := fun a b => by rw [← real_inner_comm]; rfl
  have hHmeas : Measurable densityH := hHdiff.continuous.measurable
  have hexpmeas : Measurable
      (fun x => ENNReal.ofReal (Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η))) :=
    ((((continuous_const.inner continuous_id).measurable.comp E.stat_meas).sub
      measurable_const).exp).ennreal_ofReal
  -- the member measure as a Lebesgue density
  have hPwd : E.P η = volume.withDensity (fun x => ENNReal.ofReal (densityH x)
      * ENNReal.ofReal (Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η))) := by
    rw [E.P_eq_withDensity hη, hbase, ← withDensity_mul volume hHmeas.ennreal_ofReal hexpmeas]
    rfl
  have hDmeas : Measurable (fun x => ENNReal.ofReal (densityH x)
      * ENNReal.ofReal (Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η))) :=
    hHmeas.ennreal_ofReal.mul hexpmeas
  have hDlt : ∀ᵐ x ∂(volume : Measure ℝ), (ENNReal.ofReal (densityH x)
      * ENNReal.ofReal (Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η))) < ⊤ :=
    Filter.Eventually.of_forall fun _ =>
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- conversion of a `P_η`-integral into a Lebesgue integral against the weight
  have hconv : ∀ φ : ℝ → ℝ, ∫ x, φ x ∂(E.P η)
      = ∫ x, densityH x * Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η) * φ x ∂volume := by
    intro φ
    rw [hPwd, integral_withDensity_eq_integral_toReal_smul hDmeas hDlt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hH0 x),
      ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
  -- factor out the constant `exp(-A(η))`
  have hpull : ∀ φ : ℝ → ℝ,
      ∫ x, densityH x * Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η) * φ x ∂volume
      = Real.exp (-E.logPartition η)
        * ∫ x, densityH x * Real.exp ⟪η, E.stat x⟫_ℝ * φ x ∂volume := by
    intro φ
    rw [← integral_const_mul (Real.exp (-E.logPartition η))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [Real.exp_sub, Real.exp_neg]; ring
  -- integrability of the weighted integrands against Lebesgue measure
  have hDtoReal : ∀ x, (ENNReal.ofReal (densityH x)
      * ENNReal.ofReal (Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η))).toReal
      = densityH x * Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η) := fun x => by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hH0 x),
      ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  have hweight : ∀ φ : ℝ → ℝ, Integrable φ (E.P η) →
      Integrable (fun x => densityH x * Real.exp ⟪η, E.stat x⟫_ℝ * φ x) volume := by
    intro φ hφ
    have hiff := (integrable_withDensity_iff hDmeas hDlt).1 (hPwd ▸ hφ)
    have hc := hiff.const_mul (Real.exp (E.logPartition η))
    refine hc.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [hDtoReal x, Real.exp_sub]; field_simp [Real.exp_ne_zero]
  have hGL : Integrable (fun x => densityH x * Real.exp ⟪η, E.stat x⟫_ℝ
      * ((deriv densityH x / densityH x + η * deriv E.stat x) * g x)) volume := hweight _ hscore
  have hGR : Integrable (fun x => densityH x * Real.exp ⟪η, E.stat x⟫_ℝ * deriv g x) volume :=
    hweight _ hg'
  -- the anti-derivative and its derivative (the summed integrand)
  set G : ℝ → ℝ := fun x => g x * Real.exp ⟪η, E.stat x⟫_ℝ * densityH x with hG
  set S : ℝ → ℝ := fun x =>
    densityH x * Real.exp ⟪η, E.stat x⟫_ℝ * ((deriv densityH x / densityH x
        + η * deriv E.stat x) * g x)
    + densityH x * Real.exp ⟪η, E.stat x⟫_ℝ * deriv g x with hSdef
  have hderivG : ∀ x, HasDerivAt G (S x) x := by
    intro x
    have hu : HasDerivAt g (deriv g x) x := (hgdiff x).hasDerivAt
    have hw : HasDerivAt densityH (deriv densityH x) x := (hHdiff x).hasDerivAt
    have hv : HasDerivAt (fun y => Real.exp ⟪η, E.stat y⟫_ℝ)
        (Real.exp ⟪η, E.stat x⟫_ℝ * (η * deriv E.stat x)) x := by
      have := (((hTdiff x).hasDerivAt.const_mul η).exp)
      simpa only [hinner] using this
    have hGx := (hu.mul hv).mul hw
    convert! hGx using 1
    rcases eq_or_ne (densityH x) 0 with hx | hx
    · have hmin : deriv densityH x = 0 := by
        have hlm : IsLocalMin densityH x :=
          Filter.Eventually.of_forall fun y => by rw [hx]; exact hH0 y
        exact hlm.deriv_eq_zero
      simp only [hSdef, Pi.mul_apply, hx, hmin]; ring
    · simp only [hSdef, Pi.mul_apply]; field_simp; ring
  -- `S = G'` integrates to zero on the line
  have hboundary : ∫ x, S x = 0 :=
    integral_eq_zero_of_hasDerivAt_of_tendsto_zero hderivG (hGL.add hGR) hBot hTop
  have hsum : (∫ x, densityH x * Real.exp ⟪η, E.stat x⟫_ℝ
        * ((deriv densityH x / densityH x + η * deriv E.stat x) * g x) ∂volume)
      + ∫ x, densityH x * Real.exp ⟪η, E.stat x⟫_ℝ * deriv g x ∂volume = 0 := by
    rw [← integral_add hGL hGR]; exact hboundary
  -- assemble
  have hL : ∫ x, (deriv densityH x / densityH x + η * deriv E.stat x) * g x ∂(E.P η)
      = Real.exp (-E.logPartition η) * ∫ x, densityH x * Real.exp ⟪η, E.stat x⟫_ℝ
          * ((deriv densityH x / densityH x + η * deriv E.stat x) * g x) ∂volume := by
    rw [hconv, hpull]
  have hR : ∫ x, deriv g x ∂(E.P η) = Real.exp (-E.logPartition η)
      * ∫ x, densityH x * Real.exp ⟪η, E.stat x⟫_ℝ * deriv g x ∂volume := by
    rw [hconv, hpull]
  rw [hL, hR]
  linear_combination (Real.exp (-E.logPartition η)) * hsum

end ExpFamily

end StatLean.PointEstimation
