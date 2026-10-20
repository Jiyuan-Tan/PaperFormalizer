module
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimator
public import StatLean.AsymptoticStatistics.LowerBounds.UnboundedSubmodelQMDPath
public import StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct

@[expose] public section

/-!
# Narrow (chosen-family) form of the regular-estimator predicate

The Hájek-style regular-estimator predicate in **chosen-family** form.

vdV's prose reads "for every `g ∈ Ṗ_P`, **write `P_{t,g}` for a
submodel**": a single chosen submodel per score direction. The broad-form
predicate `IsRegularEstimator` quantifies over **all** realizing QMDPaths
per direction; this file ships the parallel `∃ chosenFamily` narrow form,
with the same per-`g` weak-convergence conclusion.

## Scope choice (closure, not carrier)

This narrow form indexes `chosenFamily` over `tangentSpace T_set` (the
L²-closed linear span), parallel to the broad form. This is the scope
where the Theorem 25.20 proof picks orthonormal bases.

## Why both flavours

The two forms agree mathematically: the broad form's `∀ curve` is no
strengthening over the narrow form's `∃ chosenFamily`. The unconditional
equivalence `IsRegularEstimator_narrow ⟺ IsRegularEstimator` is proved via
LAN-locality plus the Hellinger/TV bridge.

## Why no `QMDPath.ofScore` wrapper

The realiser `unboundedParamSubmodel_oneDimPath` already realises any
`g ∈ ↥(L2ZeroMean P)` as a `QMDPath` score (via `m = 1`,
`g_P := fun _ => g / ‖g‖`). The forward direction instantiates
`chosenFamily` inline; a thin wrapper would only repackage the same
construction, so this file deliberately ships only the definition.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998),
§25.3.2 (regular-estimator definition, paragraph preceding Theorem 25.20).
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal MeasureTheory

namespace AsymptoticStatistics.LowerBounds.RegularEstimator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- *Narrow (chosen-family) form of `IsRegularEstimator`.*

A sequence of scalar estimators `T_n : (Fin n → Ω) → ℝ` is *narrow*-regular
at `P` relative to the tangent set `T_set`, with limit law `L`, iff there
exists a chosen family of QMDPaths — one per score direction
`g ∈ tangentSpace T_set` (closure) — such that for each direction the
rescaled estimator computed along the chosen path and recentered at the
perturbed truth converges weakly to `L`:

```
√n · (T_n − ψ((chosenFamily g hg).curve ((√n)⁻¹)))  ⇀  L .
```

Parallel to `IsRegularEstimator` (the production broad form), differing
**only** in the quantifier shape on the realising path: narrow asks
`∃ chosenFamily`, broad asks `∀ curve`. The conclusion clause is
identical to the broad form's per-`g`-and-`curve` conclusion.

## Scope (closure, not carrier)

The chosen family is indexed over `tangentSpace T_set` (the L²-closed
linear span), matching the scope where the broad form quantifies. This is
the scope where the Theorem 25.20 proof picks orthonormal bases.

## Equivalence with the broad form

The equivalence `IsRegularEstimator_narrow ⟺ IsRegularEstimator` holds
**unconditionally** (no extra hypothesis on `T_set` required), via
LAN-locality plus the Hellinger/TV bridge: the chosen-family and all-paths
formulations agree mathematically.

Reference: vdV §25.3.2 (paragraph preceding Theorem 25.20); same
canonical recentering-at-perturbed-truth form as the broad
`IsRegularEstimator`. -/
def IsRegularEstimator_narrow
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    (ψ : Measure Ω → ℝ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (L : Measure ℝ) [IsProbabilityMeasure L] : Prop :=
  ∃ chosenFamily :
      ∀ (g : ↥(L2ZeroMean P)),
        (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier → QMDPath P,
    (∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
      (chosenFamily g hg).score = g) ∧
    (∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
      WeakConverges
        (fun n : ℕ =>
          (MeasureTheory.Measure.pi
              (fun _ : Fin n => (chosenFamily g hg).curve ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω =>
              Real.sqrt n *
                (T_n n X - ψ ((chosenFamily g hg).curve ((Real.sqrt n)⁻¹)))))
        L)

/-! ## LAN-locality (Hellinger route) for same-score QMDPaths

Two `QMDPath`s with identical scores have product-Hellinger residual tending to `0`
at scale `t = 1/√n`. This is the central technical lemma used in the reverse
direction `IsRegularEstimator_narrow ⟹ IsRegularEstimator`, where it implies
product TV → 0 and hence the weak-convergence transfer between the two same-score
paths.

### Mathematical content

DQM (`QMDPath.qmd_limit`) gives, for each γᵢ and common dominator `λ`:
```
√(dγᵢ(t)/dλ).toReal = √(dP/dλ).toReal + (t/2) · scoreᵢ · √(dP/dλ).toReal + rᵢ(t)
```
with `‖rᵢ(t)‖_{L²(λ)} = o(t)` (`ℝ≥0∞`-form, see `qmd_limit`).

Same-score subtraction (under `h_dom : γ₁.dominating = γ₂.dominating` and
`h_score : γ₁.score = γ₂.score`):
```
√(dγ₁(t)/dλ).toReal - √(dγ₂(t)/dλ).toReal = r₁(t) - r₂(t)  (μ-a.e.)
```
with L²-norm `o(t)`.

Per-sample squared Hellinger eLpNorm at `t`:
```
‖√(dγ₁(t)/dλ).toReal - √(dγ₂(t)/dλ).toReal‖_{L²(λ)} = o(t)
```

Product Hellinger via the affinity-multiplicativity step (`HellingerProduct`):
```
‖√(∏ dγ₁(t)/dλ).toReal - √(∏ dγ₂(t)/dλ).toReal‖_{L²(λ^n)} ≤ √n · o(t)
```

At `t = 1/√n` this is `√n · o(1/√n) = o(1) → 0`.

### Structure of the proof

The deepest analytic step, the affinity-multiplicativity to product `L²`-bound,
is the named inner lemma `hellinger_product_eLpNorm_le_sqrt_n_per_sample`. The
per-sample step and the final composition (this theorem's body) assemble it with
the per-sample residual estimate. Beyond `QMDPath P` the only hypothesis is
`h_dom` (common dominator), which for the actual call sites is `dominating := P`
on both sides. -/

/-! ### Structural sub-lemmas for `hellinger_locality_for_qmdpath_same_score` -/

/-- Step (i): per-sample Hellinger residual at scale `t` for same-score paths.

Under same dominator + same score, the per-sample `L²(λ)` norm of the difference
of square-root densities is `o(t)` as `t → 0` (in particular, the squared norm
divided by `t²` tends to `0`).

Mathematical content: from `QMDPath.qmd_limit` applied to each γᵢ and the
ℝ≥0∞-form L²-norm, the residual `rᵢ(t) := √dγᵢ(t)/dλ - √dP/dλ - (t/2)·g·√dP/dλ`
has `‖rᵢ(t)‖_{L²(λ)} / |t| → 0`. Under `score₁ = score₂ = g` and
`dominating₁ = dominating₂ = λ`, the linear terms cancel:
  `√dγ₁(t)/dλ - √dγ₂(t)/dλ = r₁(t) - r₂(t)  (λ-a.e.)`.
Hence `‖√dγ₁(t) - √dγ₂(t)‖_{L²(λ)} ≤ ‖r₁(t)‖ + ‖r₂(t)‖ = o(t)`.

The proof assembles the QMD limits of both paths via the triangle inequality
(`MeasureTheory.eLpNorm_sub_le`), the pointwise cancellation
`√dγ₁(t)/dλ - √dγ₂(t)/dλ = r₁(t) - r₂(t)` (which holds everywhere, not just
a.e., since `γᵢ.curve 0 = P` is constitutive and `γ₁.dominating = γ₂.dominating`,
`γ₁.score = γ₂.score` are hypotheses), and converts the ℝ≥0∞-form quotient to the
ℝ-form via `residual_memLp_eventually` to get eventual finiteness. -/
lemma hellinger_per_sample_residual_isLittleO
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (γ₁ γ₂ : QMDPath P)
    (h_dom : γ₁.dominating = γ₂.dominating)
    (h_score : γ₁.score = γ₂.score) :
    Tendsto
      (fun t : ℝ =>
        (eLpNorm
          (fun ω : Ω =>
            Real.sqrt ((γ₁.curve t).rnDeriv γ₁.dominating ω).toReal
            - Real.sqrt ((γ₂.curve t).rnDeriv γ₂.dominating ω).toReal)
          2 γ₁.dominating).toReal / |t|)
      (𝓝[≠] 0) (𝓝 0) := by
  -- Strategy:
  -- Define rᵢ(t,ω) := √dγᵢ(t)/dξ - √dP/dξ - (t/2)·gᵢ·√dP/dξ  (ξ := γ₁.dominating).
  -- Pointwise (everywhere, using h_dom + γ.curve_at_zero + h_score):
  --   √dγ₁(t)/dξ - √dγ₂(t)/dξ = r₁(t) - r₂(t).
  -- Triangle in ℝ≥0∞: eLpNorm (LHS) ≤ eLpNorm (r₁) + eLpNorm (r₂).
  -- Divide by ofReal|t|: ratio (LHS) ≤ ratio (r₁) + ratio (r₂).
  -- Each RHS-ratio → 0 in ℝ≥0∞ by qmd_limit.
  -- Take .toReal: convert to (ℝ valued) Tendsto using residual_memLp_eventually.
  set ξ : Measure Ω := γ₁.dominating
  -- Score-coercion equality: from h_score : γ₁.score = γ₂.score, the underlying
  -- functions are pointwise equal (Lp coercion is functional).
  have h_score_fn : ((γ₁.score : Ω → ℝ)) = ((γ₂.score : Ω → ℝ)) := by
    rw [h_score]
  -- Pointwise residual identity (everywhere, no a.e. needed).
  have h_pointwise : ∀ t : ℝ, ∀ ω : Ω,
      Real.sqrt ((γ₁.curve t).rnDeriv ξ ω).toReal
        - Real.sqrt ((γ₂.curve t).rnDeriv ξ ω).toReal
      = (Real.sqrt ((γ₁.curve t).rnDeriv ξ ω).toReal
          - Real.sqrt ((γ₁.curve 0).rnDeriv ξ ω).toReal
          - (t / 2) * (γ₁.score : Ω → ℝ) ω
              * Real.sqrt ((γ₁.curve 0).rnDeriv ξ ω).toReal)
        - (Real.sqrt ((γ₂.curve t).rnDeriv γ₂.dominating ω).toReal
            - Real.sqrt ((γ₂.curve 0).rnDeriv γ₂.dominating ω).toReal
            - (t / 2) * (γ₂.score : Ω → ℝ) ω
                * Real.sqrt ((γ₂.curve 0).rnDeriv γ₂.dominating ω).toReal) := by
    intro t ω
    -- Use γ₁.curve_at_zero, γ₂.curve_at_zero, h_dom (ξ = γ₂.dominating), h_score_fn.
    have hc1 : γ₁.curve 0 = P := γ₁.curve_at_zero
    have hc2 : γ₂.curve 0 = P := γ₂.curve_at_zero
    have h_dom' : γ₂.dominating = ξ := h_dom.symm
    rw [hc1, hc2, h_dom', h_score_fn]
    ring
  -- Define residuals.
  set R₁ : ℝ → Ω → ℝ := fun t ω =>
    Real.sqrt ((γ₁.curve t).rnDeriv ξ ω).toReal
      - Real.sqrt ((γ₁.curve 0).rnDeriv ξ ω).toReal
      - (t / 2) * (γ₁.score : Ω → ℝ) ω
          * Real.sqrt ((γ₁.curve 0).rnDeriv ξ ω).toReal
  set R₂ : ℝ → Ω → ℝ := fun t ω =>
    Real.sqrt ((γ₂.curve t).rnDeriv γ₂.dominating ω).toReal
      - Real.sqrt ((γ₂.curve 0).rnDeriv γ₂.dominating ω).toReal
      - (t / 2) * (γ₂.score : Ω → ℝ) ω
          * Real.sqrt ((γ₂.curve 0).rnDeriv γ₂.dominating ω).toReal
  -- ℝ≥0∞ form: from qmd_limit, eLpNorm (Rᵢ t) / ofReal|t| → 0 as t → 0 (𝓝[≠]0).
  have hQ₁ :
      Tendsto (fun t : ℝ =>
          eLpNorm (R₁ t) 2 ξ / ENNReal.ofReal |t|)
        (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)) := γ₁.qmd_limit
  have hQ₂ :
      Tendsto (fun t : ℝ =>
          eLpNorm (R₂ t) 2 γ₂.dominating / ENNReal.ofReal |t|)
        (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)) := γ₂.qmd_limit
  -- Rewrite hQ₂'s measure via h_dom.
  have hQ₂' :
      Tendsto (fun t : ℝ =>
          eLpNorm (R₂ t) 2 ξ / ENNReal.ofReal |t|)
        (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)) := by
    have h_dom' : γ₂.dominating = ξ := h_dom.symm
    convert hQ₂ using 1
    funext t
    rw [h_dom']
  -- Sum: eLpNorm(R₁ t)/ofReal|t| + eLpNorm(R₂ t)/ofReal|t| → 0.
  have h_sum :
      Tendsto (fun t : ℝ =>
          eLpNorm (R₁ t) 2 ξ / ENNReal.ofReal |t|
            + eLpNorm (R₂ t) 2 ξ / ENNReal.ofReal |t|)
        (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)) := by
    have := hQ₁.add hQ₂'
    simpa using this
  -- Pointwise: eLpNorm (√dγ₁/dξ - √dγ₂/dξ) ≤ eLpNorm(R₁) + eLpNorm(R₂).
  -- Use eLpNorm_sub_le (with f := R₁, g := R₂) + congr_ae for LHS.
  -- LHS as function of t.
  set H : ℝ → Ω → ℝ := fun t ω =>
    Real.sqrt ((γ₁.curve t).rnDeriv ξ ω).toReal
      - Real.sqrt ((γ₂.curve t).rnDeriv ξ ω).toReal
  have h_H_eq_sub : ∀ t, H t = R₁ t - R₂ t := by
    intro t
    funext ω
    have hp := h_pointwise t ω
    -- Need to map γ₂.dominating to ξ in R₂ t ω.
    -- R₂ t ω is defined with γ₂.dominating; H t ω uses ξ.
    -- h_pointwise gives: H t ω = (rhs with γ₂.dominating) = R₁ t ω - R₂ t ω.
    simp only [H, R₁, R₂, Pi.sub_apply]
    exact hp
  -- eLpNorm bound (ℝ≥0∞), eventually wrt 𝓝[≠] 0.
  -- We use residual_memLp_eventually to get AEStronglyMeasurable for both rᵢ
  -- at small t.
  have h_mem₁ := γ₁.residual_memLp_eventually
  have h_mem₂ := γ₂.residual_memLp_eventually
  -- Rewrite h_mem₂'s measure via h_dom.
  have h_mem₂' : ∀ᶠ t : ℝ in 𝓝[≠] 0, MemLp (R₂ t) 2 ξ := by
    have h_dom' : γ₂.dominating = ξ := h_dom.symm
    filter_upwards [h_mem₂] with t ht
    convert ht using 2
  have h_triangle : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      eLpNorm (H t) 2 ξ ≤ eLpNorm (R₁ t) 2 ξ + eLpNorm (R₂ t) 2 ξ := by
    filter_upwards [h_mem₁, h_mem₂'] with t hM₁ hM₂
    have h₁_aes : AEStronglyMeasurable (R₁ t) ξ := hM₁.1
    have h₂_aes : AEStronglyMeasurable (R₂ t) ξ := hM₂.1
    calc eLpNorm (H t) 2 ξ
        = eLpNorm (R₁ t - R₂ t) 2 ξ := by rw [h_H_eq_sub]
      _ ≤ eLpNorm (R₁ t) 2 ξ + eLpNorm (R₂ t) 2 ξ :=
          eLpNorm_sub_le h₁_aes h₂_aes (by norm_num)
  -- Divide by ofReal|t|: ratio bound.
  have h_div_bound : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      eLpNorm (H t) 2 ξ / ENNReal.ofReal |t|
        ≤ eLpNorm (R₁ t) 2 ξ / ENNReal.ofReal |t|
          + eLpNorm (R₂ t) 2 ξ / ENNReal.ofReal |t| := by
    filter_upwards [h_triangle] with t ht
    rw [← ENNReal.add_div]
    exact ENNReal.div_le_div_right ht _
  -- LHS in ℝ≥0∞ tends to 0 by squeeze.
  have h_H_ratio :
      Tendsto (fun t : ℝ => eLpNorm (H t) 2 ξ / ENNReal.ofReal |t|)
        (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => (0 : ℝ≥0∞))
      (h := fun t : ℝ =>
        eLpNorm (R₁ t) 2 ξ / ENNReal.ofReal |t|
          + eLpNorm (R₂ t) 2 ξ / ENNReal.ofReal |t|)
      tendsto_const_nhds h_sum
      (Filter.Eventually.of_forall (fun _ => zero_le))
      h_div_bound
  -- Convert to ℝ via .toReal, using eventual finiteness from MemLp(H t).
  -- Step: eLpNorm(H t) is finite for t in 𝓝[≠] 0 (from h_triangle + h_mem).
  have h_H_memLp : ∀ᶠ t : ℝ in 𝓝[≠] 0, MemLp (H t) 2 ξ := by
    filter_upwards [h_mem₁, h_mem₂'] with t hM₁ hM₂
    have h₁_aes : AEStronglyMeasurable (R₁ t) ξ := hM₁.1
    have h₂_aes : AEStronglyMeasurable (R₂ t) ξ := hM₂.1
    have h_H_aes : AEStronglyMeasurable (H t) ξ := by
      rw [h_H_eq_sub]
      exact h₁_aes.sub h₂_aes
    refine ⟨h_H_aes, ?_⟩
    have h_sub_le : eLpNorm (H t) 2 ξ ≤ eLpNorm (R₁ t) 2 ξ + eLpNorm (R₂ t) 2 ξ := by
      calc eLpNorm (H t) 2 ξ
          = eLpNorm (R₁ t - R₂ t) 2 ξ := by rw [h_H_eq_sub]
        _ ≤ eLpNorm (R₁ t) 2 ξ + eLpNorm (R₂ t) 2 ξ :=
            eLpNorm_sub_le h₁_aes h₂_aes (by norm_num)
    exact lt_of_le_of_lt h_sub_le (ENNReal.add_lt_top.mpr ⟨hM₁.2, hM₂.2⟩)
  -- Convert ℝ≥0∞ tendsto to ℝ tendsto via .toReal.
  have h_toReal :
      Tendsto (fun t : ℝ =>
          (eLpNorm (H t) 2 ξ / ENNReal.ofReal |t|).toReal)
        (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    have h_cont : ContinuousAt ENNReal.toReal (0 : ℝ≥0∞) :=
      ENNReal.continuousAt_toReal (by norm_num)
    exact h_cont.tendsto.comp h_H_ratio
  -- Identify (eLpNorm / ofReal|t|).toReal with (eLpNorm).toReal / |t| eventually.
  have h_self_ne : {x : ℝ | x ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := self_mem_nhdsWithin
  have h_ratio_eq : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      (eLpNorm (H t) 2 ξ / ENNReal.ofReal |t|).toReal
        = (eLpNorm (H t) 2 ξ).toReal / |t| := by
    filter_upwards [h_self_ne, h_H_memLp] with t ht_ne ht_mem
    have habs : 0 < |t| := abs_pos.mpr ht_ne
    have h_eLp_ne_top : eLpNorm (H t) 2 ξ ≠ ⊤ := ht_mem.2.ne
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal habs.le]
  have h_final :
      Tendsto (fun t : ℝ => (eLpNorm (H t) 2 ξ).toReal / |t|)
        (𝓝[≠] 0) (𝓝 (0 : ℝ)) := h_toReal.congr' h_ratio_eq
  -- Bridge: the goal uses `γ₂.dominating` for γ₂'s rnDeriv argument; we used ξ.
  have h_bridge : (fun t : ℝ => (eLpNorm (H t) 2 ξ).toReal / |t|)
      = (fun t : ℝ =>
          (eLpNorm
            (fun ω : Ω =>
              Real.sqrt ((γ₁.curve t).rnDeriv γ₁.dominating ω).toReal
              - Real.sqrt ((γ₂.curve t).rnDeriv γ₂.dominating ω).toReal)
            2 γ₁.dominating).toReal / |t|) := by
    funext t
    have h_dom' : γ₂.dominating = ξ := h_dom.symm
    simp only [H]
    rw [h_dom']
  rw [h_bridge] at h_final
  exact h_final

/-- Step (ii): tensorisation — product Hellinger eLpNorm is bounded by `√n` times
the per-sample Hellinger eLpNorm.

Mathematical content (the affinity-multiplicativity step lives in
`HellingerProduct`): for probability densities `p, q : Ω → ℝ≥0∞` w.r.t. λ, the
affinity `A := ∫ √(p · q).toReal dλ` satisfies `A ≤ 1` (Cauchy-Schwarz) and
multiplies under iid products `A_n = A^n` (`lintegral_prod_iid_eq_pow`).
Combined with the Bernoulli bound `1 - A^n ≤ n(1 - A)`
(`one_sub_pow_le_nsmul_one_sub`):
  `‖√∏p - √∏q‖²_{L²(λ^n)} = 2(1 - A^n) ≤ 2n(1 - A) = n · ‖√p - √q‖²`.

The bound assembles those bricks via Cauchy-Schwarz and the
`‖f - g‖² = ∫f² + ∫g² - 2∫fg` identity; the analytic core lives in the
`HellingerProduct` development. -/
lemma hellinger_product_eLpNorm_le_sqrt_n_per_sample
    {Ω : Type*} [MeasurableSpace Ω]
    (ξ : Measure Ω) [SigmaFinite ξ]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) (n : ℕ) :
    (eLpNorm
      (fun X : Fin n → Ω =>
        Real.sqrt (∏ j, μ.rnDeriv ξ (X j)).toReal
        - Real.sqrt (∏ j, ν.rnDeriv ξ (X j)).toReal)
      2 (Measure.pi (fun _ : Fin n => ξ))).toReal
      ≤ Real.sqrt n *
          (eLpNorm
            (fun ω : Ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
              - Real.sqrt (ν.rnDeriv ξ ω).toReal)
            2 ξ).toReal :=
  -- Affinity-route proof from the `HellingerProduct` development.
  AsymptoticStatistics.ForMathlib.HellingerProduct.hellinger_product_eLpNorm_le_sqrt_n_per_sample
    (μ := μ) (ν := ν) (ξ := ξ) hμ hν n

/-- **LAN-locality (Hellinger route) for same-score `QMDPath`s.**

Two `QMDPath`s `γ₁, γ₂` at the same probability measure `P`, with the same
dominator (`h_dom`) and the same score (`h_score`), have their `n`-fold
product-Hellinger eLpNorm tending to `0` at scale `t = 1/√n`. Used in the
reverse direction `IsRegularEstimator_narrow ⟹ IsRegularEstimator` to transfer
weak convergence between same-score realising paths via the TV-Hellinger
inequality.

The hypothesis `h_dom : γ₁.dominating = γ₂.dominating` is essential; it is
satisfied for every natural construction (including
`unboundedParamSubmodel_oneDimPath` and any path with `dominating := P`).

Proof route (vdV §25.3 plus standard Hellinger product calculus, since no
Mathlib Hellinger API is available): the proof composes
* `hellinger_per_sample_residual_isLittleO` — per-sample residual is `o(t)`,
* `hellinger_product_eLpNorm_le_sqrt_n_per_sample` — tensorisation `× √n`,
* multiplication by `√n` at scale `t = 1/√n` gives `√n · o(1/√n) = o(1) → 0`.

The proof body composes the two structural sub-lemmas above; the deep analytic
content lives in those two named lemmas and the `HellingerProduct` development. -/
theorem hellinger_locality_for_qmdpath_same_score
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (γ₁ γ₂ : QMDPath P)
    (h_dom : γ₁.dominating = γ₂.dominating)
    (h_score : γ₁.score = γ₂.score) :
    Tendsto
      (fun n : ℕ =>
        (eLpNorm
          (fun X : Fin n → Ω =>
            Real.sqrt
              (∏ j, (γ₁.curve ((Real.sqrt n)⁻¹)).rnDeriv γ₁.dominating (X j)).toReal
            - Real.sqrt
              (∏ j, (γ₂.curve ((Real.sqrt n)⁻¹)).rnDeriv γ₂.dominating (X j)).toReal)
          2 (Measure.pi (fun _ : Fin n => γ₁.dominating))).toReal)
      atTop (𝓝 (0 : ℝ)) := by
  -- Composition: at scale t_n = (√n)⁻¹,
  --   Tgt n := target above,
  --   PerSample n := per-sample (eLpNorm sqrt-diff at t_n).toReal,
  -- Step (ii):   0 ≤ Tgt n ≤ √n · PerSample n            (for all n with the inst)
  -- Step (i):    PerSample n / |t_n| → 0  along atTop    (per-sample residual + composition)
  -- For n ≥ 1:   √n · t_n = 1   so   √n · PerSample n = PerSample n / t_n
  --             = PerSample n / |t_n|.
  -- Squeeze: Tgt n → 0.
  --
  -- Notation
  set t : ℕ → ℝ := fun n => (Real.sqrt n)⁻¹ with ht_def
  set Tgt : ℕ → ℝ := fun n =>
    (eLpNorm
      (fun X : Fin n → Ω =>
        Real.sqrt
          (∏ j, (γ₁.curve (t n)).rnDeriv γ₁.dominating (X j)).toReal
        - Real.sqrt
          (∏ j, (γ₂.curve (t n)).rnDeriv γ₂.dominating (X j)).toReal)
      2 (Measure.pi (fun _ : Fin n => γ₁.dominating))).toReal with hTgt_def
  set PerSample : ℕ → ℝ := fun n =>
    (eLpNorm
      (fun ω : Ω =>
        Real.sqrt ((γ₁.curve (t n)).rnDeriv γ₁.dominating ω).toReal
        - Real.sqrt ((γ₂.curve (t n)).rnDeriv γ₂.dominating ω).toReal)
      2 γ₁.dominating).toReal with hPerSample_def
  -- Step A: t n > 0 for n ≥ 1.
  have h_t_pos : ∀ n : ℕ, 1 ≤ n → 0 < t n := by
    intro n hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpos : 0 < (n : ℝ) := lt_of_lt_of_le one_pos h1
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hpos
    exact inv_pos.mpr hsq
  -- Step B: 0 ≤ Tgt n  (toReal of an ENNReal is ≥ 0).
  have h_Tgt_nn : ∀ n : ℕ, 0 ≤ Tgt n := fun n => ENNReal.toReal_nonneg
  -- Step C: Tgt n ≤ √n · PerSample n  (tensorisation bound, Step (ii)).
  have h_bound : ∀ n : ℕ, Tgt n ≤ Real.sqrt n * PerSample n := by
    intro n
    have hinst₁ : IsProbabilityMeasure (γ₁.curve (t n)) :=
      γ₁.curve_isProbability _
    have hinst₂ : IsProbabilityMeasure (γ₂.curve (t n)) :=
      γ₂.curve_isProbability _
    have hac₁ : γ₁.curve (t n) ≪ γ₁.dominating := γ₁.curve_absContinuous _
    have hac₂ : γ₂.curve (t n) ≪ γ₁.dominating := by
      rw [h_dom]; exact γ₂.curve_absContinuous _
    have h_step :=
      hellinger_product_eLpNorm_le_sqrt_n_per_sample
        (ξ := γ₁.dominating) (μ := γ₁.curve (t n)) (ν := γ₂.curve (t n))
        hac₁ hac₂ n
    -- Rewrite the goal so γ₂.dominating becomes γ₁.dominating via h_dom.
    have h_eqfun :
        (fun X : Fin n → Ω =>
            Real.sqrt
              (∏ j, (γ₁.curve (t n)).rnDeriv γ₁.dominating (X j)).toReal
            - Real.sqrt
              (∏ j, (γ₂.curve (t n)).rnDeriv γ₂.dominating (X j)).toReal)
          =
        (fun X : Fin n → Ω =>
            Real.sqrt
              (∏ j, (γ₁.curve (t n)).rnDeriv γ₁.dominating (X j)).toReal
            - Real.sqrt
              (∏ j, (γ₂.curve (t n)).rnDeriv γ₁.dominating (X j)).toReal) := by
      funext X
      rw [h_dom]
    have h_per_eqfun :
        (fun ω : Ω =>
            Real.sqrt ((γ₁.curve (t n)).rnDeriv γ₁.dominating ω).toReal
            - Real.sqrt ((γ₂.curve (t n)).rnDeriv γ₂.dominating ω).toReal)
          =
        (fun ω : Ω =>
            Real.sqrt ((γ₁.curve (t n)).rnDeriv γ₁.dominating ω).toReal
            - Real.sqrt ((γ₂.curve (t n)).rnDeriv γ₁.dominating ω).toReal) := by
      funext ω
      rw [h_dom]
    rw [hTgt_def, hPerSample_def]
    change
      (eLpNorm
        (fun X : Fin n → Ω =>
          Real.sqrt
            (∏ j, (γ₁.curve (t n)).rnDeriv γ₁.dominating (X j)).toReal
          - Real.sqrt
            (∏ j, (γ₂.curve (t n)).rnDeriv γ₂.dominating (X j)).toReal)
        2 (Measure.pi (fun _ : Fin n => γ₁.dominating))).toReal
        ≤ Real.sqrt n *
            (eLpNorm
              (fun ω : Ω =>
                Real.sqrt ((γ₁.curve (t n)).rnDeriv γ₁.dominating ω).toReal
                - Real.sqrt ((γ₂.curve (t n)).rnDeriv γ₂.dominating ω).toReal)
              2 γ₁.dominating).toReal
    rw [h_eqfun, h_per_eqfun]
    exact h_step
  -- Step D: PerSample n / |t n| → 0 along atTop. Per-sample residual composed with t n → 0.
  have h_t_to_zero : Tendsto t atTop (𝓝[≠] (0 : ℝ)) := by
    -- t n = (Real.sqrt n)⁻¹: positive for n ≥ 1, tends to 0.
    -- Use tendsto_nhdsWithin_iff to split into 'tends to 0 along atTop' and
    -- 'eventually ≠ 0'.
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · -- Tendsto t atTop (𝓝 0)
      have h_sqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop := by
        exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      simpa [ht_def] using! h_sqrt.inv_tendsto_atTop
    · -- ∀ᶠ n in atTop, t n ∈ {≠ 0}
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      exact (h_t_pos n hn).ne'
  have h_per_div : Tendsto (fun n : ℕ => PerSample n / |t n|) atTop (𝓝 (0 : ℝ)) := by
    have h_sub := hellinger_per_sample_residual_isLittleO P γ₁ γ₂ h_dom h_score
    -- The function inside `Tendsto` of `h_sub` is exactly (PerSample n)/|t n| under
    -- substitution s := t n.
    have h_comp := h_sub.comp h_t_to_zero
    -- After composition: Tendsto (PerSample n / |t n|) atTop (𝓝 0).
    convert! h_comp using 1
  -- Step E: For n ≥ 1, √n · PerSample n = PerSample n / t n = PerSample n / |t n|.
  have h_id : ∀ n : ℕ, 1 ≤ n → Real.sqrt n * PerSample n = PerSample n / |t n| := by
    intro n hn
    have hpos := h_t_pos n hn
    have habs : |t n| = t n := abs_of_pos hpos
    rw [habs]
    -- t n = (√n)⁻¹; so PerSample n / t n = PerSample n * √n.
    have h_t_eq : t n = (Real.sqrt n)⁻¹ := rfl
    rw [h_t_eq]
    have hsq_pos : 0 < Real.sqrt n :=
      Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le one_pos hn))
    field_simp
  -- Step F: combine. From PerSample n / |t n| → 0 and the identity for n ≥ 1,
  -- we get Real.sqrt n * PerSample n → 0.
  have h_sqrt_per : Tendsto (fun n : ℕ => Real.sqrt n * PerSample n) atTop (𝓝 (0 : ℝ)) := by
    apply h_per_div.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (h_id n hn).symm
  -- Step G: squeeze 0 ≤ Tgt n ≤ Real.sqrt n * PerSample n → 0.
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_sqrt_per
    (Filter.Eventually.of_forall h_Tgt_nn)
    (Filter.Eventually.of_forall h_bound)

/-! ## Forward direction: `IsRegularEstimator ⟹ IsRegularEstimator_narrow`

The easy direction of the narrow/broad equivalence: every realising QMDPath in
the broad form's `∀ curve` quantifier supplies, in particular, a *chosen*
representative for the narrow form's `∃ chosenFamily`.

For each score direction `g ∈ tangentSpace T_set` we instantiate the chosen
family via `unboundedParamSubmodel_oneDimPath`, which realises *any*
`g ∈ ↥(L2ZeroMean P)` as a `QMDPath` score. The `g = 0` edge case is handled
separately via the constant-`P` `boundedDensityPath 0` (whose score is `0` by
`boundedDensityPath_score`).

The weak-convergence conclusion follows by direct application of the broad
hypothesis to the chosen family entry. -/

/-- **Canonical-path API**: for each score direction `g : ↥(L2ZeroMean P)`,
returns a `QMDPath P` whose score equals `g` exactly:

* `g = 0`: the constant-`P` path `boundedDensityPath 0 hg0_ess`, with score `0`.
* `g ≠ 0`: the 1-direction sigmoid path with normalised seed `(1/‖g‖) • g`
  (whose `L²`-norm is `1`, so orthonormality holds trivially) and scaling
  `h := EuclideanSpace.single 0 ‖g‖`; the resulting `linPerturbScore` then
  collapses to `‖g‖ • ((1/‖g‖) • g) = g`.

This is the public canonical-path realiser used both by
`isRegularEstimator_implies_narrow` (the chosen family in the narrow/broad
equivalence) and by Theorem 25.21's local-asymptotic-minimax route, which needs
a `g ↦ QMDPath P` with `score = g` to feed the LAM and Theorem 8.11 lower-bound
chain. -/
noncomputable def canonicalPath
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (g : ↥(L2ZeroMean P)) : QMDPath P := by
  classical
  by_cases hg : g = 0
  · -- Zero score: constant-P path.
    refine AsymptoticStatistics.Core.MassMethod.boundedDensityPath
      (0 : ↥(L2ZeroMean P)) ?_
    refine ⟨0, ?_⟩
    have h_ae :
        (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] (fun _ => (0 : ℝ)) :=
      Lp.coeFn_zero _ _ _
    filter_upwards [h_ae] with ω hω
    rw [hω]; simp
  · -- Nonzero score: sigmoid path with normalised seed.
    refine unboundedParamSubmodel_oneDimPath
      (g_P := fun _ : Fin 1 => (1 / ‖g‖) • g)
      ?_
      (EuclideanSpace.single (0 : Fin 1) ‖g‖)
    -- Orthonormal for `Fin 1`: norm-1 on each index + trivially-pairwise (Fin 1 is
    -- a subsingleton).
    have h_norm_g_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg
    have h_norm_ne : ‖g‖ ≠ 0 := h_norm_g_pos.ne'
    have h_norm_one :
        ∀ i : Fin 1, ‖(((1 / ‖g‖) • g : ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖ = 1 := by
      intro _
      -- The L2ZeroMean → Lp coercion is norm-preserving on smul.
      have h_coe_smul :
          (((1 / ‖g‖) • g : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
            = (1 / ‖g‖) • ((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) := rfl
      rw [h_coe_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / ‖g‖)]
      have h_coe_norm :
          ‖((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖ = ‖g‖ := rfl
      rw [h_coe_norm]
      field_simp
    refine ⟨h_norm_one, ?_⟩
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij

/-- Score of `canonicalPath g` is `g`. -/
theorem canonicalPath_score
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (g : ↥(L2ZeroMean P)) :
    (canonicalPath g).score = g := by
  classical
  unfold canonicalPath
  by_cases hg : g = 0
  · -- Zero branch: score = 0 = g.
    simp only [hg, dif_pos]
    -- The body is `boundedDensityPath 0 ⟨0, …⟩`; its score is `0`.
    exact (AsymptoticStatistics.Core.MassMethod.boundedDensityPath_score
      (0 : ↥(L2ZeroMean P)) _)
  · -- Nonzero branch: score = linPerturbScore g_P h = ‖g‖ • ((1/‖g‖) • g) = g.
    simp only [hg, dif_neg, not_false_eq_true]
    refine Eq.trans (unboundedParamSubmodel_oneDimPath_score _ _ _) ?_
    -- Goal: `linPerturbScore (fun _ => (1/‖g‖) • g) (single 0 ‖g‖) = g`.
    unfold linPerturbScore
    -- ∑ i : Fin 1, (single 0 ‖g‖) i • ((1/‖g‖) • g)
    rw [Fin.sum_univ_one]
    -- Now goal: (single 0 ‖g‖) 0 • ((1/‖g‖) • g) = g.
    have h_single :
        (EuclideanSpace.single (0 : Fin 1) ‖g‖) 0 = ‖g‖ := by
      simp
    rw [h_single]
    -- Goal: ‖g‖ • ((1/‖g‖) • g) = g.
    rw [smul_smul]
    have h_norm_g_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg
    have h_norm_ne : ‖g‖ ≠ 0 := h_norm_g_pos.ne'
    have h_one : ‖g‖ * (1 / ‖g‖) = 1 := by field_simp
    rw [h_one, one_smul]

/-- The dominating measure of `canonicalPath g` is `P`, for every `g`. Both
branches of `canonicalPath` (`boundedDensityPath 0` for `g = 0`,
`unboundedParamSubmodel_oneDimPath` for `g ≠ 0`) set `dominating := P`. This
lets downstream consumers synthesize `[SigmaFinite (canonicalPath g).dominating]`
as `[SigmaFinite P]` without case-splitting on `g`. -/
theorem canonicalPath_dominating
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (g : ↥(L2ZeroMean P)) :
    (canonicalPath g).dominating = P := by
  classical
  unfold canonicalPath
  by_cases hg : g = 0
  · simp only [hg, dif_pos]
    rfl
  · simp only [hg, dif_neg, not_false_eq_true]
    rfl

/-- **Forward direction of the narrow/broad equivalence.**

If `T_n` is *broadly* regular, i.e. for every `g ∈ tangentSpace T_set` and every
realising `QMDPath` with score `g` the rescaled estimator weakly converges to
`L`, then `T_n` is *narrowly* regular: there exists a chosen family of
`QMDPath`s (one per direction) along which the rescaled estimator weakly
converges to `L`.

The chosen family is built via `canonicalPath`, which uses
`unboundedParamSubmodel_oneDimPath` for non-zero scores and the constant-`P`
`boundedDensityPath 0` for the zero score. The conclusion drops out by direct
application of the broad assumption at the chosen family entry.

Reference: vdV §25.3.2; same hypothesis as the broad form, with this lemma
extracting a witness for the narrow form. -/
theorem isRegularEstimator_implies_narrow
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P}
    {ψ : Measure Ω → ℝ}
    {IF_eff : ↥(L2ZeroMean P)}
    {hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ}
    {hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff}
    {T_n : ∀ n, (Fin n → Ω) → ℝ}
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (h_broad : IsRegularEstimator P T_set ψ hψ hEIF T_n L) :
    IsRegularEstimator_narrow P T_set ψ hψ hEIF T_n L := by
  refine ⟨fun g _hg => canonicalPath g, ?_, ?_⟩
  · -- Score equation: `(canonicalPath g).score = g`.
    intro g _hg
    exact canonicalPath_score g
  · -- Per-direction weak convergence: apply `h_broad` at the chosen family entry.
    intro g hg
    exact h_broad g hg (canonicalPath g) (canonicalPath_score g)

end AsymptoticStatistics.LowerBounds.RegularEstimator
