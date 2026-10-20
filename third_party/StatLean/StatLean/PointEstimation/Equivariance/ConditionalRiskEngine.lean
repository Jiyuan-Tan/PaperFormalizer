module
public import StatLean.PointEstimation.Equivariance.Defs
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

/-!
# The conditional-risk engine

Every minimum risk equivariant (MRE) construction in this development has the same shape.
After the equivariant class has been parametrised by a maximal invariant `Z` — the
differences for location, the coordinate ratios for scale, both for location-scale — the
competing estimators are exactly the members of a **template family** `F w x` indexed by
a real number `w` chosen as a function `w = v(Z x)` of the maximal invariant. Minimizing
the risk over the whole equivariant class then reduces to minimizing, separately inside
each fibre of `Z`, the conditional expected loss over the *constant* choices of `w`.

This file isolates that reduction once:

* `orbitCondKernel P₀ Z` — the conditional distribution of the data given the maximal
  invariant, i.e. the regular conditional probability of `X` given `Z(X)`;
* `lintegral_eq_lintegral_condDistrib` — the disintegration identity that expresses an
  integral of `g (Z x) x` as an iterated integral over the fibres;
* `lintegral_le_of_condMinimizer` — the engine proper: an almost-everywhere fibrewise
  minimizer `v*` beats every measurable competitor `v` globally.

The location instantiation uses `F w x = δ₀ x − w` (`LocationMRE`); the scale
instantiation uses `F w x = δ₀ x / w` (`ScaleMRE`).

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.1 (First
Examples), the conditional-minimization engine behind Theorem 1.10 (location) and Theorem 3.3
of §3.3 (scale). (`TPE2 §3.1 Thm 1.10; §3.3 Thm 3.3`.)

**Proof formalization notes.**
* **Argument order.** Mathlib's `condDistrib Y X μ` is the conditional law of `Y` *given*
  `X`: the conditioned variable comes first, the conditioning variable second. The
  conditional distribution of the data given the maximal invariant is therefore
  `condDistrib id Z P₀`, a `Kernel 𝓩 𝓧`. `orbitCondKernel` pins this order once so that
  the three instantiations cannot silently transpose it.
* The disintegration rests on `ProbabilityTheory.compProd_map_condDistrib`, which gives
  `(P₀.map Z) ⊗ₘ condDistrib id Z P₀ = P₀.map (fun x => (Z x, x))`; the iterated integral
  is then `MeasureTheory.lintegral_compProd` and the left-hand side is `lintegral_map`.
* The fibrewise hypothesis quantifies over **constant** `w`, while the conclusion
  compares against a competitor `v (Z x)` that varies across fibres. This is exactly
  right: inside the fibre `{Z = z}` the competitor takes the single value `v z`, so the
  hypothesis instantiated at `w := v z` is what the fibrewise comparison needs.
* Everything is stated in `ℝ≥0∞` through `ENNReal.ofReal ∘ ρ` (junk-value discipline),
  so no integrability side conditions are needed for the *statement*; a non-integrable
  loss records `∞` and the inequality still carries content.
* `StandardBorelSpace 𝓧` and `Nonempty 𝓧` are what make `condDistrib` a genuine kernel;
  `𝓩` needs only a measurable structure, but the instantiations supply standard Borel
  spaces there too.
* Existence of a fibrewise minimizer is *not* proved here — it is a hypothesis. Where it
  has to be produced (convex non-monotone losses) the intended route is the convex
  minimizer and measurable-argmin bricks in the `ForMathlib` layer of this area; this
  file deliberately does not depend on them.

**Bibliographic comments.** The conditioning-on-the-maximal-invariant derivation of best
equivariant estimators is due to E. J. G. Pitman, "The estimation of the location and
scale parameters of a continuous population of any given form," *Biometrika* **30**
(1939), 391–421, and in its general group-theoretic form to G. A. Hunt and C. Stein
(unpublished manuscript, 1946), reported in print by M. A. Girshick and L. J. Savage,
"Bayes and minimax estimates for quadratic loss functions," *Proc. Second Berkeley Symp.
Math. Statist. Probab.*, Univ. California Press, 1951, 53–73.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

section Engine

variable {𝓧 𝓩 : Type*} [MeasurableSpace 𝓧] [StandardBorelSpace 𝓧] [Nonempty 𝓧]
  [MeasurableSpace 𝓩]

/-- The **conditional distribution of the data given a maximal invariant**: the regular
conditional probability of `X` given `Z(X)`, as a Markov kernel `𝓩 ⇝ 𝓧`.

This is `condDistrib id Z P₀`; note that Mathlib's `condDistrib Y X μ` conditions the
*first* argument on the second, so the identity map (the data) comes first and the
statistic `Z` second. Edge behaviour: for a `Z` that is not almost-everywhere measurable
the underlying `condDistrib` falls back to Mathlib's junk value, so all theorems below
carry a measurability hypothesis on `Z`. -/
noncomputable def orbitCondKernel (P₀ : Measure 𝓧) [IsFiniteMeasure P₀] (Z : 𝓧 → 𝓩) :
    Kernel 𝓩 𝓧 :=
  condDistrib id Z P₀

instance (P₀ : Measure 𝓧) [IsFiniteMeasure P₀] (Z : 𝓧 → 𝓩) :
    IsMarkovKernel (orbitCondKernel P₀ Z) := by
  unfold orbitCondKernel; infer_instance

/-- **Disintegration along a statistic.** An integral of a jointly measurable integrand
`g (Z x) x` unfolds into the integral over the distribution of the statistic of the
conditional integrals over its fibres. -/
theorem lintegral_eq_lintegral_condDistrib (P₀ : Measure 𝓧) [IsProbabilityMeasure P₀]
    {Z : 𝓧 → 𝓩}
    -- LEAN-ONLY: measurability of the statistic; without it `condDistrib` degenerates
    (hZ : Measurable Z)
    {g : 𝓩 → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the integrand, required by `lintegral_compProd`
    (hg : Measurable fun p : 𝓩 × 𝓧 => g p.1 p.2) :
    ∫⁻ x, g (Z x) x ∂P₀ = ∫⁻ z, ∫⁻ x, g z x ∂(orbitCondKernel P₀ Z z) ∂(P₀.map Z) := by
  have hprod : Measurable (fun x => (Z x, x) : 𝓧 → 𝓩 × 𝓧) := hZ.prodMk measurable_id
  have h1 : ∫⁻ x, g (Z x) x ∂P₀
      = ∫⁻ p, g p.1 p.2 ∂(P₀.map (fun x => (Z x, x))) := by
    rw [lintegral_map hg hprod]
  rw [h1, show (fun x => (Z x, x) : 𝓧 → 𝓩 × 𝓧) = (fun x => (Z x, id x)) from rfl,
    ← compProd_map_condDistrib (μ := P₀) (X := Z) (Y := id) aemeasurable_id,
    Measure.lintegral_compProd hg]
  rfl

/-- The conditional mean of a measurable function against the fibre kernel is a
measurable function of the fibre index. This is what makes the explicit
conditional-expectation forms of the minimum risk equivariant estimators measurable, as
their definition requires. -/
theorem measurable_integral_orbitCondKernel (P₀ : Measure 𝓧) [IsProbabilityMeasure P₀]
    {Z : 𝓧 → 𝓩}
    -- LEAN-ONLY: measurability of the maximal invariant (see `orbitCondKernel`)
    (hZ : Measurable Z)
    {φ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the integrand
    (hφ : Measurable φ)
    -- USER-INPUT: the conditional mean exists in every fibre
    (hint : ∀ z, Integrable φ (orbitCondKernel P₀ Z z)) :
    Measurable fun z => ∫ x, φ x ∂(orbitCondKernel P₀ Z z) := by
  exact (hφ.stronglyMeasurable.integral_kernel (κ := orbitCondKernel P₀ Z)).measurable

/-- **The conditional-risk engine.** Let `F : ℝ → 𝓧 → ℝ` be a template family of
estimators indexed by a real parameter and let `ρ` be a loss. If a measurable `v*`
minimizes, for almost every value `z` of the statistic `Z` and over all *constant*
choices `w`, the conditional expected loss

`w ↦ ∫⁻ x, ENNReal.ofReal (ρ (F w x)) ∂(orbitCondKernel P₀ Z z)`,

then the estimator `x ↦ F (v* (Z x)) x` has the smallest overall expected loss among all
estimators of the form `x ↦ F (v (Z x)) x` with `v` measurable.

Instantiated at `F w x = δ₀ x − w` this is the location MRE construction, and at
`F w x = δ₀ x / w` the scale MRE construction; in both cases the class of competitors is
precisely the measurable equivariant class by the structure theorems. -/
theorem lintegral_le_of_condMinimizer (P₀ : Measure 𝓧) [IsProbabilityMeasure P₀]
    {Z : 𝓧 → 𝓩}
    -- LEAN-ONLY: measurability of the maximal invariant (see `orbitCondKernel`)
    (hZ : Measurable Z)
    {F : ℝ → 𝓧 → ℝ}
    -- LEAN-ONLY: joint measurability of the template in (index, data); the classical
    -- argument never mentions it, and it only feeds the disintegration
    (hF : Measurable fun p : ℝ × 𝓧 => F p.1 p.2)
    {ρ : ℝ → ℝ}
    -- LEAN-ONLY: measurability of the loss; same role, no scope change
    (hρ : Measurable ρ)
    {vStar : 𝓩 → ℝ}
    -- USER-INPUT: the fibrewise minimizer is supplied by the caller, measurably
    (hvStar : Measurable vStar)
    -- USER-INPUT: `v*` minimizes the conditional expected loss in almost every fibre
    (hmin : ∀ᵐ z ∂(P₀.map Z), ∀ w : ℝ,
      ∫⁻ x, ENNReal.ofReal (ρ (F (vStar z) x)) ∂(orbitCondKernel P₀ Z z) ≤
        ∫⁻ x, ENNReal.ofReal (ρ (F w x)) ∂(orbitCondKernel P₀ Z z))
    {v : 𝓩 → ℝ}
    -- USER-INPUT: an arbitrary competing choice of the index as a function of `Z`
    (hv : Measurable v) :
    ∫⁻ x, ENNReal.ofReal (ρ (F (vStar (Z x)) x)) ∂P₀ ≤
      ∫⁻ x, ENNReal.ofReal (ρ (F (v (Z x)) x)) ∂P₀ := by
  have hmeasP : Measurable (fun p : 𝓩 × 𝓧 => (vStar p.1, p.2)) :=
    (hvStar.comp measurable_fst).prodMk measurable_snd
  have hmeasPv : Measurable (fun p : 𝓩 × 𝓧 => (v p.1, p.2)) :=
    (hv.comp measurable_fst).prodMk measurable_snd
  have hg1 : Measurable
      (fun p : 𝓩 × 𝓧 => ENNReal.ofReal (ρ (F (vStar p.1) p.2))) :=
    ENNReal.measurable_ofReal.comp (hρ.comp (hF.comp hmeasP))
  have hg2 : Measurable
      (fun p : 𝓩 × 𝓧 => ENNReal.ofReal (ρ (F (v p.1) p.2))) :=
    ENNReal.measurable_ofReal.comp (hρ.comp (hF.comp hmeasPv))
  rw [lintegral_eq_lintegral_condDistrib P₀ hZ
        (g := fun z x => ENNReal.ofReal (ρ (F (vStar z) x))) hg1,
      lintegral_eq_lintegral_condDistrib P₀ hZ
        (g := fun z x => ENNReal.ofReal (ρ (F (v z) x))) hg2]
  apply lintegral_mono_ae
  filter_upwards [hmin] with z hz
  exact hz (v z)

end Engine

end StatLean.PointEstimation
