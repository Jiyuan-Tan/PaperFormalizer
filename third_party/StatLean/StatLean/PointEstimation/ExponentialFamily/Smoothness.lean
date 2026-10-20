module
public import StatLean.PointEstimation.ExponentialFamily.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Probability.Moments.MGFAnalytic

@[expose] public section

/-!
# Smoothness of weighted exponential integrals in the natural parameter

For an integrable weight `f` on the sample space, the map
$$ \eta \;\longmapsto\; \int f(x)\,e^{\langle \eta, T(x)\rangle}\,d\nu(x) $$
is continuous, differentiable to all orders, and in fact real-analytic on the interior of the
set of natural parameters at which the weighted integrand is absolutely integrable. This is
the analytic engine behind every moment formula for exponential families: the mean and
covariance identities for the natural statistic are what one gets by differentiating
`∫ exp(⟨η, T⟩ − A(η)) dν = 1` under the integral sign.

* `ExpFamily.weightedNatSet` — the `f`-weighted natural parameter set;
* `ExpFamily.continuousOn_integral_exp_inner` — continuity on its interior;
* `ExpFamily.hasFDerivAt_integral_exp_inner` — differentiability, with the derivative given
  by the integral of the differentiated integrand;
* `ExpFamily.iteratedDeriv_integral_exp_inner` — derivatives of every order along a fixed
  direction;
* `ExpFamily.analyticAt_integral_exp_mul` — real-analyticity in the one-dimensional case;
* `ExpFamily.analyticOnNhd_integral_exp_inner` — the full multivariate joint analyticity.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.5
(Exponential Families), Theorem 5.8 (continuity and infinite differentiability on the interior
of the natural parameter space; differentiation under the integral sign). (`TPE2 §1.5 Thm
5.8`.)

**Proof formalization notes.**
* The weighted parameter set is defined with `|f|` so that membership is a genuine absolute
  integrability statement and the set is convex by the same Hölder argument that gives
  `ExpFamily.natSet_convex`.
* The derivative is represented as `innerSL ℝ G` for the vector
  `G = ∫ (f x · e^{⟨η, T x⟩}) • T x dν`, i.e. as the Riesz representation of the differential.
  This is the honest "integral of the differentiated integrand": the directional derivative
  along `u` is `∫ f x · ⟨u, T x⟩ · e^{⟨η, T x⟩} dν = ⟪G, u⟫`. Representing the differential by
  a vector rather than by an abstract continuous linear map keeps the statement usable
  downstream (the gradient of the log-partition function is `G` with `f ≡ 1`).
* `analyticAt_integral_exp_mul` is not a literal instance of Mathlib's
  `ProbabilityTheory.analyticAt_mgf`, which only covers the unweighted case `f ≡ 1`. It does
  reduce to it: split `f = f⁺ − f⁻`, and note that `∫ f± e^{ηT} dν` is the moment generating
  function of `T` under the finite measure `ν.withDensity (ENNReal.ofReal ∘ f±)`, whose
  `integrableExpSet` contains the interior of the weighted parameter set. Analyticity is then
  `analyticAt_mgf` applied twice and subtracted.
* `analyticOnNhd_integral_exp_inner` is proved by exhibiting the Taylor series by hand rather
  than by invoking a Mathlib "smooth + local bounds ⇒ analytic" criterion, which the current
  pin does not provide in several variables. The `n`-th coefficient is the continuous
  multilinear map `m ↦ (n!)⁻¹ ∫ f e^{⟪η, T⟫} ∏ᵢ ⟪mᵢ, T⟫ dν`, obtained from the multilinear
  form `m ↦ ∏ᵢ ⟪mᵢ, T x⟫` (`MultilinearMap.mkPiAlgebra` composed with the Riesz maps) by
  integration and `MultilinearMap.mkContinuous`. The elementary inequality
  `‖v‖ⁿ ≤ (n!/cⁿ) e^{c‖v‖}` turns the sign-vector envelope
  `M = ∫ |f| e^{⟪η, T⟫ + c‖T‖} dν < ∞` of `integrable_abs_exp_inner_add_norm` into the
  geometric coefficient bound `M·c⁻ⁿ`, hence a radius of convergence at least `c`; on that
  ball the exponential series may be integrated termwise (`hasSum_integral_of_summable_
  integral_norm`, dominated by the same envelope) and sums to the function. Finite
  dimensionality enters only through the envelope, exactly as in the derivative theorem.

**Bibliographic comments.** Differentiation under the integral sign for exponential families,
and the resulting analyticity of the log-partition function on the interior of the natural
parameter set, go back to E. Sverdrup ("Similarity, unbiasedness, minimaxibility and
admissibility of statistical test procedures," *Skand. Aktuarietidskr.* **36** (1953),
64–86); systematic treatments are in O. Barndorff-Nielsen (*Information and Exponential
Families in Statistical Theory*, Wiley, 1978, §7.1) and L. D. Brown (*Fundamentals of
Statistical Exponential Families*, IMS Lecture Notes 9, 1986, Ch. 2).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

namespace ExpFamily

/-- The **`f`-weighted natural parameter set**: the natural parameters at which the weighted
integrand `|f|·e^{⟨η, T⟩}` is integrable against the reference measure. For `f ≡ 1` this is
`ExpFamily.natSet`. Like the natural parameter set it is a convex subset of `V`. -/
def weightedNatSet (E : ExpFamily 𝓧 V) (f : 𝓧 → ℝ) : Set V :=
  {η : V | Integrable (fun x => |f x| * Real.exp ⟪η, E.stat x⟫_ℝ) E.base}

section Differentiation

variable [BorelSpace V] [SecondCountableTopology V]

open Module in
/-- **Finite-dimensional local domination.** If a ball of parameters around `η` (of radius large
enough to contain the `2^s` sign vectors of an orthonormal basis) lies in the weighted natural
set, then the envelope `|f x|·e^{⟪η, T x⟩ + c‖T x‖}` is integrable. This is the analytic core of
the domination bounds for the derivative and continuity results: `e^{c‖v‖}` is controlled by the
finite sum `∑_S e^{⟪w_S, v⟫}` over the sign vectors `w_S` of an orthonormal basis. -/
private lemma integrable_abs_exp_inner_add_norm [FiniteDimensional ℝ V]
    (E : ExpFamily 𝓧 V) {f : 𝓧 → ℝ} (hf : Measurable f) {η : V} {c : ℝ} (hc : 0 ≤ c)
    (hball : ∀ w : V, ‖w‖ ≤ 2 * c * (finrank ℝ V) → η + w ∈ E.weightedNatSet f) :
    Integrable (fun x => |f x| * Real.exp (⟪η, E.stat x⟫_ℝ + c * ‖E.stat x‖)) E.base := by
  classical
  set N := finrank ℝ V with hN
  set b := stdOrthonormalBasis ℝ V with hb
  -- the `2^N` sign vectors of the orthonormal basis
  set w : Finset (Fin N) → V := fun t => (∑ i ∈ t, c • b i) - (∑ i ∈ tᶜ, c • b i) with hw
  -- each shifted parameter lies in the weighted natural set
  have hwmem : ∀ t, η + w t ∈ E.weightedNatSet f := by
    intro t
    apply hball
    calc ‖w t‖ ≤ ‖∑ i ∈ t, c • b i‖ + ‖∑ i ∈ tᶜ, c • b i‖ := norm_sub_le _ _
      _ ≤ (∑ i ∈ t, ‖c • b i‖) + (∑ i ∈ tᶜ, ‖c • b i‖) :=
            add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
      _ ≤ (∑ _i ∈ t, c) + (∑ _i ∈ tᶜ, c) := by
            gcongr with i _ i _ <;>
              simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, b.norm_eq_one]
      _ ≤ 2 * c * N := by
            rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
            have h1 : (t.card : ℝ) ≤ N := by
              exact_mod_cast (Finset.card_le_univ t).trans_eq (by simp)
            have h2 : (tᶜ.card : ℝ) ≤ N := by
              exact_mod_cast (Finset.card_le_univ tᶜ).trans_eq (by simp)
            nlinarith [hc, h1, h2]
  -- the sign-vector envelope: `e^{c‖v‖} ≤ ∑_t e^{⟪w t, v⟫}`
  have hkey : ∀ v : V, Real.exp (c * ‖v‖) ≤ ∑ t : Finset (Fin N), Real.exp ⟪w t, v⟫_ℝ := by
    intro v
    have hrepr : v = ∑ i, ⟪b i, v⟫_ℝ • b i := by
      conv_lhs => rw [← b.sum_repr v]
      simp_rw [b.repr_apply_apply]
    have hnorm : ‖v‖ ≤ ∑ i, |⟪b i, v⟫_ℝ| := by
      calc ‖v‖ = ‖∑ i, ⟪b i, v⟫_ℝ • b i‖ := by rw [← hrepr]
        _ ≤ ∑ i, ‖⟪b i, v⟫_ℝ • b i‖ := norm_sum_le _ _
        _ = ∑ i, |⟪b i, v⟫_ℝ| := by
              simp [norm_smul, Real.norm_eq_abs, b.norm_eq_one]
    have hexp1 : Real.exp (c * ‖v‖) ≤ ∏ i, Real.exp (c * |⟪b i, v⟫_ℝ|) := by
      rw [← Real.exp_sum]
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hnorm hc
    have hprod : ∏ i, Real.exp (c * |⟪b i, v⟫_ℝ|)
        ≤ ∏ i, (Real.exp (c * ⟪b i, v⟫_ℝ) + Real.exp (-(c * ⟪b i, v⟫_ℝ))) := by
      apply Finset.prod_le_prod (fun i _ => Real.exp_nonneg _)
      intro i _
      rcases le_total 0 (⟪b i, v⟫_ℝ) with h | h
      · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-(c * ⟪b i, v⟫_ℝ))]
      · rw [abs_of_nonpos h, show c * -(⟪b i, v⟫_ℝ) = -(c * ⟪b i, v⟫_ℝ) by ring]
        linarith [Real.exp_pos (c * ⟪b i, v⟫_ℝ)]
    have hexpand : ∏ i, (Real.exp (c * ⟪b i, v⟫_ℝ) + Real.exp (-(c * ⟪b i, v⟫_ℝ)))
        = ∑ t : Finset (Fin N), Real.exp ⟪w t, v⟫_ℝ := by
      rw [Finset.prod_add, Finset.powerset_univ]
      apply Finset.sum_congr rfl
      intro t _
      rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
      congr 1
      rw [hw]
      simp only [inner_sub_left, sum_inner, real_inner_smul_left]
      rw [Finset.compl_eq_univ_sdiff, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    calc Real.exp (c * ‖v‖) ≤ ∏ i, Real.exp (c * |⟪b i, v⟫_ℝ|) := hexp1
      _ ≤ ∏ i, (Real.exp (c * ⟪b i, v⟫_ℝ) + Real.exp (-(c * ⟪b i, v⟫_ℝ))) := hprod
      _ = ∑ t : Finset (Fin N), Real.exp ⟪w t, v⟫_ℝ := hexpand
  -- fold the envelope: `e^{⟪η,v⟫ + c‖v‖} ≤ ∑_t e^{⟪η + w t, v⟫}`
  have hpt : ∀ v : V, Real.exp (⟪η, v⟫_ℝ + c * ‖v‖)
      ≤ ∑ t : Finset (Fin N), Real.exp ⟪η + w t, v⟫_ℝ := by
    intro v
    rw [Real.exp_add]
    calc Real.exp ⟪η, v⟫_ℝ * Real.exp (c * ‖v‖)
        ≤ Real.exp ⟪η, v⟫_ℝ * ∑ t, Real.exp ⟪w t, v⟫_ℝ :=
          mul_le_mul_of_nonneg_left (hkey v) (Real.exp_nonneg _)
      _ = ∑ t : Finset (Fin N), Real.exp ⟪η + w t, v⟫_ℝ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          rw [← Real.exp_add, inner_add_left]
  -- the dominating function is a finite sum of integrable functions
  have hinner_meas : Measurable fun x => ⟪η, E.stat x⟫_ℝ :=
    (innerSL ℝ η).continuous.measurable.comp E.stat_meas
  have hg_int : Integrable
      (fun x => ∑ t : Finset (Fin N), |f x| * Real.exp ⟪η + w t, E.stat x⟫_ℝ) E.base :=
    integrable_finset_sum _ (fun t _ => hwmem t)
  refine hg_int.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hf.abs.aestronglyMeasurable).mul
      ((hinner_meas.add ((E.stat_meas.norm).const_mul c)).exp.aestronglyMeasurable)
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hpt (E.stat x)) (abs_nonneg _)

/-- **Differentiability**: on the interior of the weighted natural parameter set the weighted
exponential integral is Fréchet differentiable, and its differential is represented by the
vector `∫ (f x · e^{⟨η, T x⟩}) • T x dν` — the integral of the differentiated integrand. -/
theorem hasFDerivAt_integral_exp_inner
    -- LEAN-ONLY: `V` is finite-dimensional, so the `2^s` sign-vector envelope dominating the
    -- local integrand is available and the `V`-valued Bochner integral is meaningful (finite
    -- dimension gives `CompleteSpace V` for free). Every downstream consumer instantiates
    -- `V = EuclideanSpace ℝ (Fin k)`, the classical setting.
    [FiniteDimensional ℝ V] (E : ExpFamily 𝓧 V) {f : 𝓧 → ℝ}
    -- USER-INPUT: measurable weight; see `continuousOn_integral_exp_inner`
    (hf : Measurable f) {η : V}
    -- USER-INPUT: interior parameter; interiority is the classical hypothesis licensing
    -- differentiation under the integral sign
    (hη : η ∈ interior (E.weightedNatSet f)) :
    HasFDerivAt (fun ζ => ∫ x, f x * Real.exp ⟪ζ, E.stat x⟫_ℝ ∂E.base)
      (innerSL ℝ (∫ x, (f x * Real.exp ⟪η, E.stat x⟫_ℝ) • E.stat x ∂E.base)) η := by
  classical
  set N := Module.finrank ℝ V with hN
  -- a ball of radius `ρ` of parameters around `η` lies in the interior
  obtain ⟨ρ, hρ_pos, hρ⟩ := Metric.isOpen_iff.mp isOpen_interior η hη
  -- the domination ball radius, small enough to absorb the `2^s` sign vectors of scale `2r`
  set r : ℝ := ρ / (4 * (N : ℝ) + 2) with hrdef
  have hr : 0 < r := div_pos hρ_pos (by positivity)
  have h42 : (4 * (N : ℝ) + 2) ≠ 0 := by positivity
  have hrmul : r * (4 * (N : ℝ) + 2) = ρ := by rw [hrdef]; field_simp
  -- helper: `e·y ≤ e^y`
  have hey : ∀ y : ℝ, Real.exp 1 * y ≤ Real.exp y := by
    intro y
    calc Real.exp 1 * y ≤ Real.exp 1 * Real.exp (y - 1) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg 1)
          have := Real.add_one_le_exp (y - 1); linarith
      _ = Real.exp y := by rw [← Real.exp_add]; ring_nf
  -- helper: `s·e^{rs} ≤ (e·r)⁻¹·e^{2rs}` and `s ≤ (e·r)⁻¹·e^{2rs}` for `s ≥ 0`
  have her : (0 : ℝ) < Real.exp 1 * r := by positivity
  have habsorb : ∀ s : ℝ, 0 ≤ s →
      s * Real.exp (r * s) ≤ (Real.exp 1 * r)⁻¹ * Real.exp (2 * r * s) := by
    intro s hs
    rw [show (2 * r * s) = r * s + r * s by ring, Real.exp_add, inv_mul_eq_div, le_div_iff₀ her]
    have h1 : Real.exp 1 * (r * s) ≤ Real.exp (r * s) := hey (r * s)
    nlinarith [h1, Real.exp_pos (r * s), hs]
  have habsorb2 : ∀ s : ℝ, 0 ≤ s → s ≤ (Real.exp 1 * r)⁻¹ * Real.exp (2 * r * s) := by
    intro s hs
    have h1 := habsorb s hs
    have h2 : s ≤ s * Real.exp (r * s) := by
      nlinarith [Real.one_le_exp_iff.mpr (by positivity : (0:ℝ) ≤ r * s), hs]
    linarith
  -- the dominating bound
  set bound : 𝓧 → ℝ := fun x =>
    (Real.exp 1 * r)⁻¹ * (|f x| * Real.exp (⟪η, E.stat x⟫_ℝ + 2 * r * ‖E.stat x‖)) with hbound_def
  have hinner_meas : ∀ ζ : V, Measurable fun x => ⟪ζ, E.stat x⟫_ℝ :=
    fun ζ => (innerSL ℝ ζ).continuous.measurable.comp E.stat_meas
  have hexp_asm : ∀ ζ : V, AEStronglyMeasurable (fun x => f x * Real.exp ⟪ζ, E.stat x⟫_ℝ) E.base :=
    fun ζ => hf.aestronglyMeasurable.mul ((hinner_meas ζ).exp.aestronglyMeasurable)
  -- `bound` is integrable via the sign-vector envelope (with `c = 2r`)
  have henv : Integrable
      (fun x => |f x| * Real.exp (⟪η, E.stat x⟫_ℝ + 2 * r * ‖E.stat x‖)) E.base := by
    apply integrable_abs_exp_inner_add_norm E hf (by positivity : (0:ℝ) ≤ 2 * r)
    intro ww hww
    have hlt : ‖ww‖ < ρ := by
      calc ‖ww‖ ≤ 2 * (2 * r) * (N : ℝ) := hww
        _ = ρ - 2 * r := by linear_combination hrmul
        _ < ρ := by linarith
    have hmem : η + ww ∈ Metric.ball η ρ := by
      rw [Metric.mem_ball, dist_eq_norm]; simpa [add_sub_cancel_left] using hlt
    exact interior_subset (hρ hmem)
  have bound_int : Integrable bound E.base := henv.const_mul _
  -- the domination bound absorbs the `‖T‖` factor of the differentiated integrand
  have hbound_ge : ∀ x, |f x| * Real.exp ⟪η, E.stat x⟫_ℝ * ‖E.stat x‖ ≤ bound x := by
    intro x
    simp only [hbound_def, Real.exp_add]
    calc |f x| * Real.exp ⟪η, E.stat x⟫_ℝ * ‖E.stat x‖
        ≤ |f x| * Real.exp ⟪η, E.stat x⟫_ℝ
            * ((Real.exp 1 * r)⁻¹ * Real.exp (2 * r * ‖E.stat x‖)) := by
          gcongr; exact habsorb2 _ (norm_nonneg _)
      _ = (Real.exp 1 * r)⁻¹ * (|f x| * (Real.exp ⟪η, E.stat x⟫_ℝ
            * Real.exp (2 * r * ‖E.stat x‖))) := by ring
  -- integrability of the `V`-valued and CLM-valued differentiated integrands
  have hstat_asm : AEStronglyMeasurable (fun x => E.stat x) E.base :=
    E.stat_meas.aestronglyMeasurable
  have hgT_int : Integrable (fun x => (f x * Real.exp ⟪η, E.stat x⟫_ℝ) • E.stat x) E.base := by
    refine bound_int.mono' ((hexp_asm η).smul hstat_asm) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact hbound_ge x
  have hFη_int : Integrable
      (fun x => (f x * Real.exp ⟪η, E.stat x⟫_ℝ) • innerSL ℝ (E.stat x)) E.base := by
    refine bound_int.mono' ((hexp_asm η).smul
      ((innerSL ℝ).continuous.comp_aestronglyMeasurable hstat_asm))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact hbound_ge x
  -- differentiation under the integral sign
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := E.base) (bound := bound) (s := Metric.ball η r) (x₀ := η)
    (F := fun ζ x => f x * Real.exp ⟪ζ, E.stat x⟫_ℝ)
    (F' := fun ζ x => (f x * Real.exp ⟪ζ, E.stat x⟫_ℝ) • innerSL ℝ (E.stat x))
    (Metric.ball_mem_nhds η hr)
    (Filter.Eventually.of_forall hexp_asm)
    (by
      have hηmem : η ∈ E.weightedNatSet f := interior_subset hη
      have hη' : Integrable (fun x => |f x| * Real.exp ⟪η, E.stat x⟫_ℝ) E.base := hηmem
      refine hη'.mono' (hexp_asm η) (Filter.Eventually.of_forall fun x => ?_)
      exact le_of_eq (by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]))
    ((hexp_asm η).smul ((innerSL ℝ).continuous.comp_aestronglyMeasurable hstat_asm))
    (Filter.Eventually.of_forall fun x ζ hζ => by
      rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.exp_nonneg _)]
      simp only [hbound_def]
      have hζr : ‖ζ - η‖ ≤ r := le_of_lt (by rwa [Metric.mem_ball, dist_eq_norm] at hζ)
      have hinner_le : ⟪ζ, E.stat x⟫_ℝ ≤ ⟪η, E.stat x⟫_ℝ + r * ‖E.stat x‖ := by
        have hsplit : ⟪ζ, E.stat x⟫_ℝ = ⟪η, E.stat x⟫_ℝ + ⟪ζ - η, E.stat x⟫_ℝ := by
          rw [← inner_add_left]; congr 1; abel
        rw [hsplit]
        gcongr
        calc ⟪ζ - η, E.stat x⟫_ℝ ≤ ‖ζ - η‖ * ‖E.stat x‖ := real_inner_le_norm _ _
          _ ≤ r * ‖E.stat x‖ := by gcongr
      have hexpζ : Real.exp ⟪ζ, E.stat x⟫_ℝ
          ≤ Real.exp ⟪η, E.stat x⟫_ℝ * Real.exp (r * ‖E.stat x‖) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hinner_le
      calc |f x| * Real.exp ⟪ζ, E.stat x⟫_ℝ * ‖E.stat x‖
          ≤ |f x| * (Real.exp ⟪η, E.stat x⟫_ℝ * Real.exp (r * ‖E.stat x‖)) * ‖E.stat x‖ := by
            gcongr
        _ = Real.exp ⟪η, E.stat x⟫_ℝ * |f x|
              * (‖E.stat x‖ * Real.exp (r * ‖E.stat x‖)) := by ring
        _ ≤ Real.exp ⟪η, E.stat x⟫_ℝ * |f x|
              * ((Real.exp 1 * r)⁻¹ * Real.exp (2 * r * ‖E.stat x‖)) :=
            mul_le_mul_of_nonneg_left (habsorb _ (norm_nonneg _)) (by positivity)
        _ = (Real.exp 1 * r)⁻¹ * (|f x|
              * Real.exp (⟪η, E.stat x⟫_ℝ + 2 * r * ‖E.stat x‖)) := by
            rw [Real.exp_add]; ring)
    bound_int
    (Filter.Eventually.of_forall fun x ζ _ => by
      have hL : HasFDerivAt (fun ζ' : V => ⟪ζ', E.stat x⟫_ℝ) (innerSL ℝ (E.stat x)) ζ := by
        have hfun : (fun ζ' : V => ⟪ζ', E.stat x⟫_ℝ) = fun ζ' => innerSL ℝ (E.stat x) ζ' := by
          funext ζ'; rw [innerSL_apply_apply]; exact real_inner_comm _ _
        rw [hfun]; exact (innerSL ℝ (E.stat x)).hasFDerivAt
      have h2 := (hL.exp.const_mul (f x))
      rwa [smul_smul] at h2)
  -- rewrite the derivative into `innerSL ℝ` of the integrated integrand
  have hcomm : (∫ x, (f x * Real.exp ⟪η, E.stat x⟫_ℝ) • innerSL ℝ (E.stat x) ∂E.base)
      = innerSL ℝ (∫ x, (f x * Real.exp ⟪η, E.stat x⟫_ℝ) • E.stat x ∂E.base) := by
    ext v
    rw [ContinuousLinearMap.integral_apply hFη_int, innerSL_apply_apply,
      real_inner_comm, ← integral_inner hgT_int v]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, real_inner_smul_right,
      real_inner_comm (E.stat x) v, smul_eq_mul]
  rw [hcomm] at key
  exact key

/-- **Continuity** of the weighted exponential integral on the interior of the weighted
natural parameter set. -/
theorem continuousOn_integral_exp_inner
    -- LEAN-ONLY: finite dimension, inherited from `hasFDerivAt_integral_exp_inner` (of which this
    -- is a corollary: differentiability at each interior point gives continuity there).
    [FiniteDimensional ℝ V] (E : ExpFamily 𝓧 V) {f : 𝓧 → ℝ}
    -- USER-INPUT: the weight is a measurable function on the sample space; this is the
    -- classical "integrable function `f`" of the differentiation theorem
    (hf : Measurable f) :
    ContinuousOn (fun η => ∫ x, f x * Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base)
      (interior (E.weightedNatSet f)) :=
  -- differentiability at each interior point gives continuity within the interior there
  fun _ hη => (hasFDerivAt_integral_exp_inner E hf hη).continuousAt.continuousWithinAt

/-- **Derivatives of all orders** along a fixed direction: the `n`-th derivative of
`t ↦ ∫ f(x) e^{⟨η + t·u, T x⟩} dν` at `t = 0` is obtained by differentiating under the
integral sign `n` times. -/
theorem iteratedDeriv_integral_exp_inner (E : ExpFamily 𝓧 V) {f : 𝓧 → ℝ}
    -- USER-INPUT: measurable weight; see `continuousOn_integral_exp_inner`
    (hf : Measurable f) {η : V}
    -- USER-INPUT: interior parameter; see `hasFDerivAt_integral_exp_inner`
    (hη : η ∈ interior (E.weightedNatSet f)) (u : V) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => ∫ x, f x * Real.exp ⟪η + t • u, E.stat x⟫_ℝ ∂E.base) 0
      = ∫ x, f x * ⟪u, E.stat x⟫_ℝ ^ n * Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base := by
  classical
  -- Reduce to the one-parameter moment generating function of `Y = ⟪u, T⟫` under the tilted
  -- measure `μof w = ν.withDensity (w · e^{⟪η,T⟫})`, then invoke `iteratedDeriv_mgf`.
  set Y : 𝓧 → ℝ := fun x => ⟪u, E.stat x⟫_ℝ with hYdef
  have hYmeas : Measurable Y := (innerSL ℝ u).continuous.measurable.comp E.stat_meas
  have hinner_meas : Measurable fun x => ⟪η, E.stat x⟫_ℝ :=
    (innerSL ℝ η).continuous.measurable.comp E.stat_meas
  have hline : ∀ (t : ℝ) (x : 𝓧), ⟪η + t • u, E.stat x⟫_ℝ = ⟪η, E.stat x⟫_ℝ + t * Y x := by
    intro t x; rw [hYdef]; simp only [inner_add_left, real_inner_smul_left]
  set μof : (𝓧 → ℝ) → Measure 𝓧 :=
    fun w => E.base.withDensity (fun x => ENNReal.ofReal (w x * Real.exp ⟪η, E.stat x⟫_ℝ))
    with hμof
  have hdmeas : ∀ (w : 𝓧 → ℝ), Measurable w →
      Measurable fun x => w x * Real.exp ⟪η, E.stat x⟫_ℝ := fun w hw => hw.mul hinner_meas.exp
  -- (a) the mgf of `Y` under `μof w` is the weighted line integral
  have hmgf : ∀ (w : 𝓧 → ℝ), Measurable w → (∀ x, 0 ≤ w x) → ∀ t : ℝ,
      mgf Y (μof w) t = ∫ x, w x * Real.exp ⟪η + t • u, E.stat x⟫_ℝ ∂E.base := by
    intro w hw hwnn t
    simp only [mgf, hμof]
    rw [integral_withDensity_eq_integral_toReal_smul (hdmeas w hw).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (mul_nonneg (hwnn x) (Real.exp_nonneg _)), smul_eq_mul,
      hline t x, Real.exp_add]
    ring
  -- (b) `0` lies in the interior of the integrable-exp set of `μof w`
  have hcont : Continuous fun t : ℝ => η + t • u :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : ∀ (w : 𝓧 → ℝ), Measurable w → (∀ x, 0 ≤ w x) → (∀ x, w x ≤ |f x|) →
      (0 : ℝ) ∈ interior (integrableExpSet Y (μof w)) := by
    intro w hw hwnn hwle
    have hsub : {t : ℝ | η + t • u ∈ interior (E.weightedNatSet f)} ⊆
        integrableExpSet Y (μof w) := by
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      have htmem : η + t • u ∈ E.weightedNatSet f := interior_subset ht
      have hint : Integrable (fun x => |f x| * Real.exp ⟪η + t • u, E.stat x⟫_ℝ) E.base := htmem
      simp only [integrableExpSet, Set.mem_setOf_eq, hμof]
      rw [integrable_withDensity_iff (hdmeas w hw).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine hint.mono' (((hYmeas.const_mul t).exp.aestronglyMeasurable).mul
        ((hdmeas w hw).ennreal_ofReal.ennreal_toReal).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs,
        ENNReal.toReal_ofReal (mul_nonneg (hwnn x) (Real.exp_nonneg _)),
        abs_of_nonneg (mul_nonneg (Real.exp_nonneg _)
          (mul_nonneg (hwnn x) (Real.exp_nonneg _))),
        show Real.exp (t * Y x) * (w x * Real.exp ⟪η, E.stat x⟫_ℝ)
            = w x * Real.exp ⟪η + t • u, E.stat x⟫_ℝ by rw [hline t x, Real.exp_add]; ring]
      exact mul_le_mul_of_nonneg_right (hwle x) (Real.exp_nonneg _)
    have hUopen : IsOpen {t : ℝ | η + t • u ∈ interior (E.weightedNatSet f)} :=
      isOpen_interior.preimage hcont
    have h0U : (0 : ℝ) ∈ {t : ℝ | η + t • u ∈ interior (E.weightedNatSet f)} := by
      simp only [Set.mem_setOf_eq, zero_smul, add_zero]; exact hη
    exact interior_maximal hsub hUopen h0U
  -- (c) the `n`-th derivative of the mgf at `0` is the `n`-th `Y`-moment of `μof w`
  have hiter : ∀ (w : 𝓧 → ℝ), Measurable w → (∀ x, 0 ≤ w x) → (∀ x, w x ≤ |f x|) →
      iteratedDeriv n (mgf Y (μof w)) 0
        = ∫ x, w x * ⟪u, E.stat x⟫_ℝ ^ n * Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base := by
    intro w hw hwnn hwle
    rw [iteratedDeriv_mgf (hmem w hw hwnn hwle) n]
    simp only [hμof, hYdef]
    rw [integral_withDensity_eq_integral_toReal_smul (hdmeas w hw).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (mul_nonneg (hwnn x) (Real.exp_nonneg _)), smul_eq_mul,
      zero_mul, Real.exp_zero]
    ring
  -- integrability of the `n`-th moment integrand, for the split into positive/negative parts
  have hiterInt : ∀ (w : 𝓧 → ℝ), Measurable w → (∀ x, 0 ≤ w x) → (∀ x, w x ≤ |f x|) →
      Integrable (fun x => w x * ⟪u, E.stat x⟫_ℝ ^ n * Real.exp ⟪η, E.stat x⟫_ℝ) E.base := by
    intro w hw hwnn hwle
    have hI : Integrable (fun x => Y x ^ n * Real.exp (0 * Y x)) (μof w) := by
      rw [hμof]
      exact integrable_pow_mul_exp_of_mem_interior_integrableExpSet (hmem w hw hwnn hwle) n
    rw [hμof, integrable_withDensity_iff (hdmeas w hw).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hI
    refine hI.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (mul_nonneg (hwnn x) (Real.exp_nonneg _)), zero_mul, Real.exp_zero]
    ring
  -- weighted line-integrals for the two parts are integrable on the interior line
  have hintw : ∀ (w : 𝓧 → ℝ), Measurable w → (∀ x, 0 ≤ w x) → (∀ x, w x ≤ |f x|) → ∀ t : ℝ,
      η + t • u ∈ interior (E.weightedNatSet f) →
      Integrable (fun x => w x * Real.exp ⟪η + t • u, E.stat x⟫_ℝ) E.base := by
    intro w hw hwnn hwle t ht
    have htmem : η + t • u ∈ E.weightedNatSet f := interior_subset ht
    have hint : Integrable (fun x => |f x| * Real.exp ⟪η + t • u, E.stat x⟫_ℝ) E.base := htmem
    refine hint.mono' ((hw.aestronglyMeasurable).mul
      (((innerSL ℝ (η + t • u)).continuous.measurable.comp E.stat_meas).exp.aestronglyMeasurable))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwnn x), abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hwle x) (Real.exp_nonneg _)
  -- the positive and negative parts of the weight
  have hfp : Measurable fun x => max (f x) 0 := hf.max measurable_const
  have hfm : Measurable fun x => max (-f x) 0 := hf.neg.max measurable_const
  have hfp_nn : ∀ x, 0 ≤ max (f x) 0 := fun x => le_max_right _ _
  have hfm_nn : ∀ x, 0 ≤ max (-f x) 0 := fun x => le_max_right _ _
  have hfp_le : ∀ x, max (f x) 0 ≤ |f x| := fun x => max_le (le_abs_self _) (abs_nonneg _)
  have hfm_le : ∀ x, max (-f x) 0 ≤ |f x| := fun x => max_le (neg_le_abs _) (abs_nonneg _)
  -- near `0` the line integral splits as a difference of the two mgfs
  have hΦeq : (fun t : ℝ => ∫ x, f x * Real.exp ⟪η + t • u, E.stat x⟫_ℝ ∂E.base)
      =ᶠ[nhds 0] (mgf Y (μof fun x => max (f x) 0) - mgf Y (μof fun x => max (-f x) 0)) := by
    have hUopen : IsOpen {t : ℝ | η + t • u ∈ interior (E.weightedNatSet f)} :=
      isOpen_interior.preimage hcont
    have h0U : (0 : ℝ) ∈ {t : ℝ | η + t • u ∈ interior (E.weightedNatSet f)} := by
      simp only [Set.mem_setOf_eq, zero_smul, add_zero]; exact hη
    filter_upwards [hUopen.mem_nhds h0U] with t ht
    rw [Pi.sub_apply, hmgf _ hfp hfp_nn t, hmgf _ hfm hfm_nn t,
      ← integral_sub (hintw _ hfp hfp_nn hfp_le t ht) (hintw _ hfm hfm_nn hfm_le t ht)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    have hfsub : max (f x) 0 - max (-f x) 0 = f x := by
      rcases le_total (f x) 0 with h | h
      · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
      · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    rw [← sub_mul, hfsub]
  -- assemble: differentiate the difference termwise
  rw [hΦeq.iteratedDeriv_eq n,
    iteratedDeriv_sub (analyticAt_mgf (hmem _ hfp hfp_nn hfp_le)).contDiffAt
      (analyticAt_mgf (hmem _ hfm hfm_nn hfm_le)).contDiffAt,
    hiter _ hfp hfp_nn hfp_le, hiter _ hfm hfm_nn hfm_le,
    ← integral_sub (hiterInt _ hfp hfp_nn hfp_le) (hiterInt _ hfm hfm_nn hfm_le)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have hfsub : max (f x) 0 - max (-f x) 0 = f x := by
    rcases le_total (f x) 0 with h | h
    · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  rw [← sub_mul, ← sub_mul, hfsub]

/-- **Real-analyticity, one-dimensional case**: for a real natural statistic the weighted
exponential integral is analytic at every interior point of the weighted natural parameter
set. -/
theorem analyticAt_integral_exp_mul (E : ExpFamily 𝓧 ℝ) {f : 𝓧 → ℝ}
    -- USER-INPUT: measurable weight; see `continuousOn_integral_exp_inner`
    (hf : Measurable f) {η : ℝ}
    -- USER-INPUT: interior parameter; see `hasFDerivAt_integral_exp_inner`
    (hη : η ∈ interior (E.weightedNatSet f)) :
    AnalyticAt ℝ (fun ζ : ℝ => ∫ x, f x * Real.exp ⟪ζ, E.stat x⟫_ℝ ∂E.base) η := by
  have hinner : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := fun a b => by rw [← real_inner_comm]; rfl
  -- the positive and negative parts of the weight
  have hfp : Measurable fun x => max (f x) 0 := hf.max measurable_const
  have hfm : Measurable fun x => max (-f x) 0 := hf.neg.max measurable_const
  have hfp_nn : ∀ x, 0 ≤ max (f x) 0 := fun x => le_max_right _ _
  have hfm_nn : ∀ x, 0 ≤ max (-f x) 0 := fun x => le_max_right _ _
  have hfp_le : ∀ x, max (f x) 0 ≤ |f x| := fun x => max_le (le_abs_self _) (abs_nonneg _)
  have hfm_le : ∀ x, max (-f x) 0 ≤ |f x| := fun x => max_le (neg_le_abs _) (abs_nonneg _)
  -- `mgf` of the tilted measure equals the weighted integral
  have hmgf : ∀ (w : 𝓧 → ℝ), Measurable w → (∀ x, 0 ≤ w x) → ∀ ζ : ℝ,
      mgf E.stat (E.base.withDensity fun x => ENNReal.ofReal (w x)) ζ
        = ∫ x, w x * Real.exp (ζ * E.stat x) ∂E.base := by
    intro w hw hwnn ζ
    simp only [mgf]
    rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (hwnn x), smul_eq_mul]
  -- weighted integrand is integrable on the weighted natural set
  have hintw : ∀ (w : 𝓧 → ℝ), Measurable w → (∀ x, 0 ≤ w x) → (∀ x, w x ≤ |f x|) →
      ∀ ζ ∈ E.weightedNatSet f, Integrable (fun x => w x * Real.exp (ζ * E.stat x)) E.base := by
    intro w hw hwnn hwle ζ hζ
    have hζI : Integrable (fun x => |f x| * Real.exp ⟪ζ, E.stat x⟫_ℝ) E.base := hζ
    refine hζI.mono' ((hw.aestronglyMeasurable).mul
      (((measurable_const.mul E.stat_meas).exp).aestronglyMeasurable))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwnn x),
      abs_of_nonneg (Real.exp_nonneg _), hinner ζ (E.stat x)]
    exact mul_le_mul_of_nonneg_right (hwle x) (Real.exp_nonneg _)
  -- membership in the interior of the integrable-exp set of each tilted measure
  have hsub : ∀ (w : 𝓧 → ℝ), Measurable w → (∀ x, 0 ≤ w x) → (∀ x, w x ≤ |f x|) →
      E.weightedNatSet f ⊆ integrableExpSet E.stat (E.base.withDensity
        fun x => ENNReal.ofReal (w x)) := by
    intro w hw hwnn hwle ζ hζ
    simp only [integrableExpSet, Set.mem_setOf_eq]
    rw [integrable_withDensity_iff hw.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine ((hintw w hw hwnn hwle ζ hζ).congr (Filter.Eventually.of_forall fun x => ?_))
    dsimp only
    rw [ENNReal.toReal_ofReal (hwnn x), mul_comm]
  have hmemp : η ∈ interior (integrableExpSet E.stat
      (E.base.withDensity fun x => ENNReal.ofReal (max (f x) 0))) :=
    interior_mono (hsub _ hfp hfp_nn hfp_le) hη
  have hmemm : η ∈ interior (integrableExpSet E.stat
      (E.base.withDensity fun x => ENNReal.ofReal (max (-f x) 0))) :=
    interior_mono (hsub _ hfm hfm_nn hfm_le) hη
  have ha := (analyticAt_mgf hmemp).sub (analyticAt_mgf hmemm)
  refine ha.congr ?_
  have hnhd : interior (E.weightedNatSet f) ∈ nhds η := isOpen_interior.mem_nhds hη
  filter_upwards [hnhd] with ζ hζ
  have hζ' : ζ ∈ E.weightedNatSet f := interior_subset hζ
  simp only [Pi.sub_apply]
  rw [hmgf _ hfp hfp_nn ζ, hmgf _ hfm hfm_nn ζ,
    ← integral_sub (hintw _ hfp hfp_nn hfp_le ζ hζ') (hintw _ hfm hfm_nn hfm_le ζ hζ')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [hinner ζ (E.stat x)]
  rcases le_total (f x) 0 with h | h
  · simp only [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
  · simp only [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring

/-- **Joint real-analyticity in several natural parameters.**

The Taylor series at an interior point `η` is obtained by expanding `e^{⟪v, T x⟫}` under the
integral sign: its `n`-th coefficient is the continuous multilinear map
`m ↦ (n!)⁻¹ ∫ f(x) e^{⟪η, T x⟫} ∏ᵢ ⟪mᵢ, T x⟫ dν`. The sign-vector envelope of
`integrable_abs_exp_inner_add_norm` supplies a radius `c > 0` with
`∫ |f| e^{⟪η, T⟫ + c‖T‖} dν = M < ∞`, and `‖T‖ⁿ ≤ (n!/cⁿ) e^{c‖T‖}` then bounds the `n`-th
coefficient by `M·c⁻ⁿ`. That geometric bound gives radius of convergence at least `c`, and the
termwise integration of the exponential series (dominated by the same envelope) identifies the
sum with the function on the ball of radius `c`. -/
theorem analyticOnNhd_integral_exp_inner
    -- LEAN-ONLY: `V` is finite-dimensional, exactly as in `hasFDerivAt_integral_exp_inner`:
    -- it is what makes the `2^s` sign-vector envelope — and hence the geometric bound on the
    -- Taylor coefficients — available. Every downstream consumer instantiates
    -- `V = EuclideanSpace ℝ (Fin k)`, the classical setting.
    [FiniteDimensional ℝ V] (E : ExpFamily 𝓧 V) {f : 𝓧 → ℝ}
    -- USER-INPUT: measurable weight; see `continuousOn_integral_exp_inner`
    (hf : Measurable f) :
    AnalyticOnNhd ℝ (fun η => ∫ x, f x * Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base)
      (interior (E.weightedNatSet f)) := by
  classical
  intro η hη
  have hinner : ∀ ζ : V, Measurable fun x => ⟪ζ, E.stat x⟫_ℝ :=
    fun ζ => (innerSL ℝ ζ).continuous.measurable.comp E.stat_meas
  -- the exponential series, and the resulting single-term bound `yⁿ/n! ≤ e^y` for `y ≥ 0`
  have hexpsum : ∀ y : ℝ, HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
    intro y
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp y
  have hpow : ∀ (n : ℕ) (y : ℝ), 0 ≤ y → y ^ n / (n.factorial : ℝ) ≤ Real.exp y := by
    intro n y hy
    exact le_hasSum (hexpsum y) n fun b _ => by positivity
  -- a radius `c > 0` for which the sign-vector envelope is integrable
  obtain ⟨ρ, hρ_pos, hρ⟩ := Metric.isOpen_iff.mp isOpen_interior η hη
  have h4 : (0 : ℝ) < 4 * (Module.finrank ℝ V : ℝ) + 4 := by positivity
  set c : ℝ := ρ / (4 * (Module.finrank ℝ V : ℝ) + 4) with hcdef
  have hc : 0 < c := div_pos hρ_pos h4
  have hcmul : c * (4 * (Module.finrank ℝ V : ℝ) + 4) = ρ := by
    rw [hcdef]; field_simp
  have hcpow : ∀ n : ℕ, (0 : ℝ) < c ^ n := fun n => pow_pos hc n
  have hfac : ∀ n : ℕ, (0 : ℝ) < (n.factorial : ℝ) := fun n => by
    exact_mod_cast n.factorial_pos
  have henv : Integrable
      (fun x => |f x| * Real.exp (⟪η, E.stat x⟫_ℝ + c * ‖E.stat x‖)) E.base := by
    refine integrable_abs_exp_inner_add_norm E hf hc.le fun ww hww => ?_
    have hNn : (0 : ℝ) ≤ (Module.finrank ℝ V : ℝ) := Nat.cast_nonneg _
    have hlt : ‖ww‖ < ρ := lt_of_le_of_lt hww (by nlinarith [hc, hcmul, hNn])
    have hmem : η + ww ∈ Metric.ball η ρ := by
      rw [Metric.mem_ball, dist_eq_norm]; simpa [add_sub_cancel_left] using hlt
    exact interior_subset (hρ hmem)
  set M : ℝ := ∫ x, |f x| * Real.exp (⟪η, E.stat x⟫_ℝ + c * ‖E.stat x‖) ∂E.base with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]; exact integral_nonneg fun x => by positivity
  -- `‖v‖ⁿ ≤ (n!/cⁿ) e^{c‖v‖}`
  have hTn : ∀ (n : ℕ) (v : V),
      ‖v‖ ^ n ≤ (n.factorial : ℝ) / c ^ n * Real.exp (c * ‖v‖) := by
    intro n v
    have h := hpow n (c * ‖v‖) (by positivity)
    rw [div_le_iff₀ (hfac n), mul_pow] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ (hcpow n)]
    nlinarith [h]
  -- the tilted weight and the coefficient integrands
  set w : 𝓧 → ℝ := fun x => f x * Real.exp ⟪η, E.stat x⟫_ℝ with hwdef
  have hwmeas : Measurable w := hf.mul (hinner η).exp
  have hbound : ∀ (n : ℕ) (m : Fin n → V) (x : 𝓧),
      ‖w x * ∏ i, ⟪m i, E.stat x⟫_ℝ‖
        ≤ ((∏ i, ‖m i‖) * ((n.factorial : ℝ) / c ^ n))
          * (|f x| * Real.exp (⟪η, E.stat x⟫_ℝ + c * ‖E.stat x‖)) := by
    intro n m x
    have hprodle : |∏ i, ⟪m i, E.stat x⟫_ℝ| ≤ (∏ i, ‖m i‖) * ‖E.stat x‖ ^ n := by
      rw [Finset.abs_prod]
      calc ∏ i, |⟪m i, E.stat x⟫_ℝ|
          ≤ ∏ i : Fin n, ‖m i‖ * ‖E.stat x‖ :=
            Finset.prod_le_prod (fun i _ => abs_nonneg _)
              (fun i _ => abs_real_inner_le_norm _ _)
        _ = (∏ i, ‖m i‖) * ‖E.stat x‖ ^ n := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
              Fintype.card_fin]
    have hnormeq : ‖w x * ∏ i, ⟪m i, E.stat x⟫_ℝ‖
        = |f x| * Real.exp ⟪η, E.stat x⟫_ℝ * |∏ i, ⟪m i, E.stat x⟫_ℝ| := by
      simp only [hwdef, Real.norm_eq_abs, abs_mul, Real.abs_exp]
    rw [hnormeq, Real.exp_add]
    calc |f x| * Real.exp ⟪η, E.stat x⟫_ℝ * |∏ i, ⟪m i, E.stat x⟫_ℝ|
        ≤ |f x| * Real.exp ⟪η, E.stat x⟫_ℝ * ((∏ i, ‖m i‖) * ‖E.stat x‖ ^ n) := by
          gcongr
      _ ≤ |f x| * Real.exp ⟪η, E.stat x⟫_ℝ
            * ((∏ i, ‖m i‖)
              * ((n.factorial : ℝ) / c ^ n * Real.exp (c * ‖E.stat x‖))) := by
          gcongr
          exact hTn n (E.stat x)
      _ = ((∏ i, ‖m i‖) * ((n.factorial : ℝ) / c ^ n))
            * (|f x| * (Real.exp ⟪η, E.stat x⟫_ℝ * Real.exp (c * ‖E.stat x‖))) := by ring
  have hint : ∀ (n : ℕ) (m : Fin n → V),
      Integrable (fun x => w x * ∏ i, ⟪m i, E.stat x⟫_ℝ) E.base := by
    intro n m
    refine (henv.const_mul ((∏ i, ‖m i‖) * ((n.factorial : ℝ) / c ^ n))).mono' ?_
      (Filter.Eventually.of_forall (hbound n m))
    exact (hwmeas.mul
      (Finset.measurable_prod _ fun i _ => hinner (m i))).aestronglyMeasurable
  -- the pointwise multilinear form `m ↦ ∏ᵢ ⟪mᵢ, T x⟫`
  set Q : ∀ n : ℕ, 𝓧 → MultilinearMap ℝ (fun _ : Fin n => V) ℝ := fun n x =>
    (MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap
      fun _ => (innerSL ℝ (E.stat x)).toLinearMap with hQdef
  have hQ : ∀ (n : ℕ) (x : 𝓧) (m : Fin n → V),
      Q n x m = ∏ i, ⟪m i, E.stat x⟫_ℝ := by
    intro n x m
    rw [hQdef]
    simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    exact Finset.prod_congr rfl fun i _ => real_inner_comm _ _
  -- the Taylor coefficients as multilinear maps
  set L : ∀ n : ℕ, MultilinearMap ℝ (fun _ : Fin n => V) ℝ := fun n =>
    { toFun := fun m => ((n.factorial : ℝ))⁻¹ * ∫ x, w x * ∏ i, ⟪m i, E.stat x⟫_ℝ ∂E.base
      map_update_add' := by
        intro _ m i z₁ z₂
        have key : ∀ x : 𝓧,
            w x * ∏ j, ⟪Function.update m i (z₁ + z₂) j, E.stat x⟫_ℝ
              = w x * ∏ j, ⟪Function.update m i z₁ j, E.stat x⟫_ℝ
                + w x * ∏ j, ⟪Function.update m i z₂ j, E.stat x⟫_ℝ := by
          intro x
          have h := (Q n x).map_update_add m i z₁ z₂
          simp only [hQ] at h
          rw [h, mul_add]
        rw [integral_congr_ae (Filter.Eventually.of_forall key),
          integral_add (hint n (Function.update m i z₁)) (hint n (Function.update m i z₂)),
          mul_add]
      map_update_smul' := by
        intro _ m i a z
        have key : ∀ x : 𝓧,
            w x * ∏ j, ⟪Function.update m i (a • z) j, E.stat x⟫_ℝ
              = a * (w x * ∏ j, ⟪Function.update m i z j, E.stat x⟫_ℝ) := by
          intro x
          have h := (Q n x).map_update_smul m i a z
          simp only [hQ] at h
          rw [h, smul_eq_mul]; ring
        rw [integral_congr_ae (Filter.Eventually.of_forall key), integral_const_mul,
          smul_eq_mul]
        ring } with hLdef
  have hLapply : ∀ (n : ℕ) (m : Fin n → V),
      L n m = ((n.factorial : ℝ))⁻¹ * ∫ x, w x * ∏ i, ⟪m i, E.stat x⟫_ℝ ∂E.base :=
    fun _ _ => rfl
  have hLbound : ∀ (n : ℕ) (m : Fin n → V),
      ‖L n m‖ ≤ M * (c⁻¹) ^ n * ∏ i, ‖m i‖ := by
    intro n m
    have h1 : ‖∫ x, w x * ∏ i, ⟪m i, E.stat x⟫_ℝ ∂E.base‖
        ≤ ((∏ i, ‖m i‖) * ((n.factorial : ℝ) / c ^ n)) * M := by
      calc ‖∫ x, w x * ∏ i, ⟪m i, E.stat x⟫_ℝ ∂E.base‖
          ≤ ∫ x, ‖w x * ∏ i, ⟪m i, E.stat x⟫_ℝ‖ ∂E.base :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x, ((∏ i, ‖m i‖) * ((n.factorial : ℝ) / c ^ n))
              * (|f x| * Real.exp (⟪η, E.stat x⟫_ℝ + c * ‖E.stat x‖)) ∂E.base :=
            integral_mono (hint n m).norm (henv.const_mul _) (hbound n m)
        _ = ((∏ i, ‖m i‖) * ((n.factorial : ℝ) / c ^ n)) * M := by
            rw [hMdef, integral_const_mul]
    rw [hLapply, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (le_of_lt (inv_pos.mpr (hfac n)))]
    have h2 : |∫ x, w x * ∏ i, ⟪m i, E.stat x⟫_ℝ ∂E.base|
        ≤ ((∏ i, ‖m i‖) * ((n.factorial : ℝ) / c ^ n)) * M := by
      rwa [← Real.norm_eq_abs]
    calc ((n.factorial : ℝ))⁻¹ * |∫ x, w x * ∏ i, ⟪m i, E.stat x⟫_ℝ ∂E.base|
        ≤ ((n.factorial : ℝ))⁻¹ * (((∏ i, ‖m i‖) * ((n.factorial : ℝ) / c ^ n)) * M) := by
          gcongr
      _ = M * (c⁻¹) ^ n * ∏ i, ‖m i‖ := by
          rw [inv_pow]
          field_simp
          try ring
  -- the formal power series
  set p : FormalMultilinearSeries ℝ V ℝ := fun n =>
    (L n).mkContinuous (M * (c⁻¹) ^ n) (hLbound n) with hpdef
  have hpapply : ∀ (n : ℕ) (m : Fin n → V), p n m = L n m := fun _ _ => rfl
  have hrad : ENNReal.ofReal c ≤ p.radius := by
    have hbd : ∀ n : ℕ, ‖p n‖ * (Real.toNNReal c : ℝ) ^ n ≤ M := by
      intro n
      have hn : ‖p n‖ ≤ M * (c⁻¹) ^ n :=
        (L n).mkContinuous_norm_le (mul_nonneg hM0 (by positivity)) (hLbound n)
      rw [Real.coe_toNNReal c hc.le]
      calc ‖p n‖ * c ^ n ≤ (M * (c⁻¹) ^ n) * c ^ n :=
            mul_le_mul_of_nonneg_right hn (le_of_lt (hcpow n))
        _ = M := by
            rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hc.ne', one_pow, mul_one]
    exact p.le_radius_of_bound M hbd
  refine ⟨p, ENNReal.ofReal c, hrad, ENNReal.ofReal_pos.mpr hc, ?_⟩
  intro y hy
  have hyc : ‖y‖ < c := by
    have h := Metric.mem_eball.mp hy
    rw [edist_zero_right, ← ofReal_norm_eq_enorm] at h
    exact (ENNReal.ofReal_lt_ofReal_iff hc).mp h
  -- the termwise integrands
  set F : ℕ → 𝓧 → ℝ :=
    fun n x => w x * ⟪y, E.stat x⟫_ℝ ^ n / (n.factorial : ℝ) with hFdef
  have hconst : ∀ n : ℕ, (fun x => w x * ∏ _i : Fin n, ⟪y, E.stat x⟫_ℝ)
      = fun x => w x * ⟪y, E.stat x⟫_ℝ ^ n := by
    intro n
    funext x
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hFint : ∀ n : ℕ, Integrable (F n) E.base := by
    intro n
    have h := hint n (fun _ => y)
    rw [hconst n] at h
    exact h.div_const _
  have hFbound : ∀ (n : ℕ) (x : 𝓧),
      ‖F n x‖ ≤ (‖y‖ / c) ^ n
        * (|f x| * Real.exp (⟪η, E.stat x⟫_ℝ + c * ‖E.stat x‖)) := by
    intro n x
    have h := hbound n (fun _ => y) x
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    have hfacpos := hfac n
    have hFx : ‖F n x‖ = ‖w x * ⟪y, E.stat x⟫_ℝ ^ n‖ / (n.factorial : ℝ) := by
      simp only [hFdef, norm_div, Real.norm_eq_abs, Nat.abs_cast]
    have hkey : (‖y‖ / c) ^ n
        * (|f x| * Real.exp (⟪η, E.stat x⟫_ℝ + c * ‖E.stat x‖)) * (n.factorial : ℝ)
        = (‖y‖ ^ n * ((n.factorial : ℝ) / c ^ n))
          * (|f x| * Real.exp (⟪η, E.stat x⟫_ℝ + c * ‖E.stat x‖)) := by
      rw [div_pow]
      field_simp
      try ring
    rw [hFx, div_le_iff₀ hfacpos, hkey]
    exact h
  have hFsum : Summable fun n : ℕ => ∫ x, ‖F n x‖ ∂E.base := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun x => norm_nonneg _) (fun n => ?_)
      (((summable_geometric_of_lt_one (by positivity)
        ((div_lt_one hc).mpr hyc)).mul_left M))
    calc ∫ x, ‖F n x‖ ∂E.base
        ≤ ∫ x, (‖y‖ / c) ^ n
            * (|f x| * Real.exp (⟪η, E.stat x⟫_ℝ + c * ‖E.stat x‖)) ∂E.base :=
          integral_mono (hFint n).norm (henv.const_mul _) (hFbound n)
      _ = M * (‖y‖ / c) ^ n := by rw [hMdef, integral_const_mul]; ring
  have hHS := hasSum_integral_of_summable_integral_norm hFint hFsum
  -- identify the terms with the coefficients of `p` and the sum with the function
  have hterm : ∀ n : ℕ, (p n fun _ : Fin n => y) = ∫ x, F n x ∂E.base := by
    intro n
    rw [hpapply, hLapply]
    simp only [hFdef]
    rw [integral_div, hconst n, inv_mul_eq_div]
  have htsum : ∀ x : 𝓧, ∑' n : ℕ, F n x = w x * Real.exp ⟪y, E.stat x⟫_ℝ := by
    intro x
    have h := (hexpsum ⟪y, E.stat x⟫_ℝ).mul_left (w x)
    have heq : (fun n : ℕ => w x * (⟪y, E.stat x⟫_ℝ ^ n / (n.factorial : ℝ)))
        = fun n : ℕ => F n x := by
      funext n; rw [hFdef]; ring
    rw [heq] at h
    exact h.tsum_eq
  have hsumfun : (∫ x, ∑' n : ℕ, F n x ∂E.base)
      = ∫ x, f x * Real.exp ⟪η + y, E.stat x⟫_ℝ ∂E.base := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [htsum x, hwdef, inner_add_left, Real.exp_add]
    try ring
  have hfun : (fun n : ℕ => p n fun _ : Fin n => y) = fun n : ℕ => ∫ x, F n x ∂E.base :=
    funext hterm
  change HasSum (fun n : ℕ => p n fun _ : Fin n => y)
    (∫ x, f x * Real.exp ⟪η + y, E.stat x⟫_ℝ ∂E.base)
  rw [hfun, ← hsumfun]
  exact hHS

end Differentiation

end ExpFamily

end StatLean.PointEstimation

