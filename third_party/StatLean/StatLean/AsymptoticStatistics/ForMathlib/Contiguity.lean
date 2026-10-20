module
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

@[expose] public section

/-!
# Contiguity of sequences of probability measures

Contiguity (van der Vaart §6.3-§6.7) and Le Cam's first and third lemmas as
general probability-theoretic results.

Main declarations:
* `WeakConverges` — test-function-based weak convergence of measures.
* `Contiguous`, `MutuallyContiguous` — the two notions.
* `contiguous_of_asymptotically_log_normal` — vdV Example 6.5, direction `Q ⊲ P`.
* `mutuallyContiguous_of_asymptotically_log_normal` — mutual-contiguity version.
* `weak_limit_under_Q_of_lecam_third` — Le Cam's third lemma (vdV Theorem 6.6).
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-- Weak convergence of a sequence of probability measures (convergence in law).

Test-function characterization: for every bounded continuous real-valued `f`, the
`f`-integrals converge. Equivalent to convergence in the weak topology on
`MeasureTheory.ProbabilityMeasure E`, but given in unpacked form for convenience. -/
def WeakConverges {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (μ : ℕ → Measure E) (ν : Measure E) : Prop :=
  ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))

/-- **Continuous mapping theorem for weak convergence**: if `μ_n` weakly converges to
`ν` on `E` and `f : E → F` is continuous and measurable, then the pushforwards by `f`
weakly converge to the pushforward of the limit. Standard application of
`BoundedContinuousFunction.compContinuous` + `integral_map`. -/
lemma WeakConverges.map {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [MeasurableSpace F] [TopologicalSpace F] [PseudoMetricSpace F]
    [OpensMeasurableSpace F]
    {μ : ℕ → Measure E} {ν : Measure E}
    (hμν : WeakConverges μ ν) {f : E → F}
    (hf_cont : Continuous f) (hf_meas : Measurable f) :
    WeakConverges (fun n => (μ n).map f) (ν.map f) := by
  intro g
  -- `g ∘ f` is a bounded continuous function on `E`.
  let g_comp_f : E →ᵇ ℝ := g.compContinuous ⟨f, hf_cont⟩
  -- Both `∫ g d(μ.map f)` and `∫ g d(ν.map f)` rewrite to `∫ (g ∘ f) dμ` / `∫ (g ∘ f) dν`.
  have h_rewrite : ∀ ρ : Measure E,
      ∫ y, g y ∂(ρ.map f) = ∫ x, g_comp_f x ∂ρ := by
    intro ρ
    rw [MeasureTheory.integral_map hf_meas.aemeasurable
      g.continuous.aestronglyMeasurable]
    rfl
  simp_rw [h_rewrite]
  exact hμν g_comp_f

/-- **Subsequence preservation** of weak convergence. If `μ_n ⇝ ν` and `φ : ℕ → ℕ`
is strictly monotone, then `μ_{φ k} ⇝ ν`. -/
lemma WeakConverges.comp {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    {μ : ℕ → Measure E} {ν : Measure E}
    (h : WeakConverges μ ν) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WeakConverges (fun k => μ (φ k)) ν :=
  fun f => (h f).comp hφ.tendsto_atTop

/-- **Weak-limit uniqueness** on a Polish-adjacent Borel space. If a sequence of
measures weakly converges to two finite measures, they agree. Pure consequence of
`ext_of_forall_integral_eq_of_IsFiniteMeasure` + `tendsto_nhds_unique`. -/
lemma WeakConverges.unique
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    [HasOuterApproxClosed E]
    {μ : ℕ → Measure E} {ν ν' : Measure E}
    [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h₁ : WeakConverges μ ν) (h₂ : WeakConverges μ ν') :
    ν = ν' :=
  MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
    (fun f => tendsto_nhds_unique (h₁ f) (h₂ f))

/-- **Marginal weak-limit identification**. If `μ_n ⇝ π` jointly on `E × F` and
`(μ_n.map snd) ⇝ ν` on `F`, then `π.map Prod.snd = ν`. Proof: continuous-mapping
gives `(μ_n.map snd) ⇝ π.map snd`, then apply weak-limit uniqueness. -/
lemma WeakConverges.snd_eq
    {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [MeasurableSpace F] [TopologicalSpace F] [PseudoMetricSpace F]
    [BorelSpace F] [HasOuterApproxClosed F]
    {μ : ℕ → Measure (E × F)} {π : Measure (E × F)} [IsFiniteMeasure π]
    {ν : Measure F} [IsFiniteMeasure ν]
    (hπ : WeakConverges μ π)
    (hν : WeakConverges (fun n => (μ n).map Prod.snd) ν) :
    π.map Prod.snd = ν :=
  have : IsFiniteMeasure (π.map Prod.snd) :=
    MeasureTheory.Measure.isFiniteMeasure_map π Prod.snd
  WeakConverges.unique (hπ.map continuous_snd measurable_snd) hν

/-- **Weak-conv composition with a Feller Markov kernel** (vdV §8.5, Le Cam
representation, kernel form).

If a sequence of probability measures `μ_n` on `α` weakly converges to `ν` on
`α`, and `κ : Kernel α β` is a Markov kernel that is *Feller continuous* (i.e.
the map `a ↦ (κ a : ProbabilityMeasure β)` is continuous from the topology of
`α` to the weak topology on `ProbabilityMeasure β`), then the measure-kernel
binds `μ_n.bind κ` weakly converge to `ν.bind κ` on `β`.

The Markov typeclass `hκ_Markov` keeps `bind` of a probability measure a probability
measure. The bundled `ProbabilityMeasure`-valued map `κPM` (with agreement `hκPM`)
lets the Feller continuity hypothesis live on the bundled subtype without per-call
coercion gymnastics. Feller continuity `hκ_feller` is the canonical formulation as
continuity into the weak topology of `ProbabilityMeasure`. -/
lemma WeakConverges.bind_kernel
    {α β : Type*}
    [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [PseudoMetricSpace β]
    [OpensMeasurableSpace β] [HasOuterApproxClosed β]
    {μ_n : ℕ → Measure α} {ν : Measure α}
    [∀ n, IsProbabilityMeasure (μ_n n)] [IsProbabilityMeasure ν]
    (hμν : WeakConverges μ_n ν)
    (κ : ProbabilityTheory.Kernel α β) [ProbabilityTheory.IsMarkovKernel κ]
    (κPM : α → ProbabilityMeasure β)
    (hκPM : ∀ a, (κPM a : Measure β) = κ a)
    (hκ_feller : Continuous κPM) :
    WeakConverges (fun n => (μ_n n).bind κ) (ν.bind κ) := by
  intro f
  -- Define g(a) := ∫ x, f x ∂(κ a). We will show that g is bounded continuous and
  -- ∫ f d(ρ.bind κ) = ∫ g dρ for any probability ρ. Then weak convergence of μ_n → ν
  -- applied to g gives the result.
  -- Continuity of g via Feller hypothesis: by
  -- `ProbabilityMeasure.continuous_iff_forall_continuous_integral`, `Continuous κPM`
  -- gives `Continuous (fun a => ∫ x, f x ∂(κPM a : Measure β))`, and `hκPM` rewrites
  -- the underlying measure to `κ a`.
  have hg_cont : Continuous (fun a : α => ∫ x, f x ∂(κ a)) := by
    have := (ProbabilityMeasure.continuous_iff_forall_continuous_integral.mp hκ_feller) f
    -- `this : Continuous (fun a => ∫ x, f x ∂((κPM a) : Measure β))`
    -- Rewrite the integrand using `hκPM`.
    have heq : (fun a : α => ∫ x, f x ∂((κPM a : ProbabilityMeasure β) : Measure β))
        = (fun a : α => ∫ x, f x ∂(κ a)) := by
      funext a; rw [hκPM a]
    rw [heq] at this
    exact this
  -- Pointwise bound: |g a| ≤ ‖f‖ since κ a is a probability measure.
  have hg_bound : ∀ a : α, ‖∫ x, f x ∂(κ a)‖ ≤ ‖f‖ := by
    intro a
    have hμ : IsProbabilityMeasure (κ a) := inferInstance
    have h := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := κ a) (f := fun x => f x) (C := ‖f‖)
      (Filter.Eventually.of_forall (fun x => BoundedContinuousFunction.norm_coe_le_norm f x))
    simpa [measureReal_def, measure_univ] using h
  -- Build the bounded continuous function g : α →ᵇ ℝ.
  let g : α →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨_, hg_cont⟩ (2 * ‖f‖) (fun x y => by
      have hx := hg_bound x
      have hy := hg_bound y
      have : |(∫ z, f z ∂(κ x)) - (∫ z, f z ∂(κ y))| ≤
          |∫ z, f z ∂(κ x)| + |∫ z, f z ∂(κ y)| := abs_sub _ _
      have h1 : |∫ z, f z ∂(κ x)| ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using hx
      have h2 : |∫ z, f z ∂(κ y)| ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using hy
      have := this.trans (add_le_add h1 h2)
      simpa [Real.dist_eq, two_mul] using this)
  -- Rewrite the integrals against `ρ.bind κ` as integrals of `g` against `ρ`.
  -- Step: ρ.bind κ = (ρ ⊗ₘ κ).snd = (ρ ⊗ₘ κ).map Prod.snd, then `integral_map`
  -- + `Measure.integral_compProd` reduces it to ∫ a, ∫ b, f b ∂(κ a) ∂ρ = ∫ a, g a ∂ρ.
  have h_rewrite : ∀ ρ : Measure α, [IsProbabilityMeasure ρ] →
      ∫ y, f y ∂(ρ.bind κ) = ∫ a, g a ∂ρ := by
    intro ρ _
    -- `ρ.bind κ = (ρ ⊗ₘ κ).snd`
    rw [show ρ.bind (κ : α → Measure β) = (ρ.compProd κ).snd from
      (MeasureTheory.Measure.snd_compProd ρ κ).symm]
    -- `(ρ ⊗ₘ κ).snd = (ρ ⊗ₘ κ).map Prod.snd`
    rw [MeasureTheory.Measure.snd]
    -- `∫ y, f y d(ρ ⊗ₘ κ).map snd = ∫ z, f z.2 d(ρ ⊗ₘ κ)`
    rw [MeasureTheory.integral_map measurable_snd.aemeasurable
      f.continuous.aestronglyMeasurable]
    -- The bounded integrand is integrable against the product probability measure.
    have hfmeas : Measurable (fun z : α × β => f z.2) := by
      exact f.continuous.measurable.comp measurable_snd
    have hinteg : Integrable (fun z : α × β => f z.2) (ρ.compProd κ) := by
      refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
      -- Bounded by ‖f‖ on a finite (probability) measure.
      have : IsProbabilityMeasure (ρ.compProd κ) := by
        have hρ : SFinite ρ := by infer_instance
        infer_instance
      exact MeasureTheory.HasFiniteIntegral.of_bounded
        (C := ‖f‖)
        (Filter.Eventually.of_forall
          (fun z => BoundedContinuousFunction.norm_coe_le_norm f z.2))
    rw [MeasureTheory.Measure.integral_compProd hinteg]
    -- The iterated integral is `∫ a, g a ∂ρ` by definition of `g`.
    rfl
  -- Apply weak convergence to g.
  have htendsto : Tendsto (fun n => ∫ a, g a ∂(μ_n n)) atTop (𝓝 (∫ a, g a ∂ν)) := hμν g
  simp_rw [h_rewrite] at *
  exact htendsto

/-- **Commuting `withDensity` past `Measure.map`**:
`(μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ`, for measurable `φ` and `h`.

Useful for pushing a density through a measurable pushforward — e.g., when a joint
law `π_tilted = π.map φ` is `withDensity`-ed against a function `h` that factors
through `φ`, the calculation can be pulled back to `π` under the composed density. -/
lemma Measure.withDensity_map_eq_map_withDensity
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : MeasureTheory.Measure α) (φ : α → β) (hφ : Measurable φ)
    (h : β → ℝ≥0∞) (hh : Measurable h) :
    (μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ := by
  refine MeasureTheory.Measure.ext (fun A hA => ?_)
  rw [MeasureTheory.withDensity_apply _ hA,
      MeasureTheory.Measure.map_apply hφ hA,
      MeasureTheory.withDensity_apply _ (hφ hA),
      MeasureTheory.setLIntegral_map hA hh hφ]
  rfl

/-- **Reparametrization of a measure-kernel bind**:
`(μ.map f).bind κ = μ.bind (κ.comap f hf)`.

Pushing forward `μ` by `f` and then averaging `κ` over it is the same as composing
`κ ∘ f` (via `Kernel.comap`) and averaging over the original `μ`. The identity is a
direct consequence of `Measure.bind_apply` + `lintegral_map` + `Kernel.comap_apply'`. -/
lemma Measure.bind_map_eq_bind_comap
    {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ}
    (μ : MeasureTheory.Measure α) (f : α → β) (hf : Measurable f)
    (κ : ProbabilityTheory.Kernel β γ) :
    (μ.map f).bind κ = μ.bind (κ.comap f hf) := by
  refine MeasureTheory.Measure.ext (fun s hs => ?_)
  rw [MeasureTheory.Measure.bind_apply hs κ.aemeasurable,
      MeasureTheory.Measure.bind_apply hs (κ.comap f hf).aemeasurable,
      MeasureTheory.lintegral_map (κ.measurable_coe hs) hf]
  simp_rw [ProbabilityTheory.Kernel.comap_apply' κ hf]

/-- **Tilted-marginal bind through conditional distribution**.

For a joint law `π` on `α × β` with first marginal analyzed conditionally on the
second, let `ν := π.map snd` and `κ := condDistrib fst snd π` (so `κ y` is the
conditional law of the first coordinate given `snd = y`). Then reweighting `ν` by
a density `f : β → ℝ≥0∞` and binding with `κ` equals marginalising the joint tilt:

`(ν.withDensity f).bind κ = (π.withDensity (fun p ↦ f p.2)).map fst`.

This is the measure-theoretic core of vdV §7.10 Step 7 — pushing a density through
the second marginal of a joint law factors through the tilted joint + marginalisation.
It sees use whenever a tilted Gaussian-shift law is re-expressed through a conditional
distribution kernel. -/
theorem Measure.withDensity_bind_condDistrib
    {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace β]
    (π : MeasureTheory.Measure (α × β)) [MeasureTheory.IsFiniteMeasure π]
    (f : β → ℝ≥0∞) (hf : Measurable f) :
    ((π.map Prod.snd).withDensity f).bind
        (ProbabilityTheory.condDistrib Prod.fst Prod.snd π) =
      (π.withDensity (fun p => f p.2)).map Prod.fst := by
  set κ := ProbabilityTheory.condDistrib (Prod.fst : α × β → α) Prod.snd π with hκ_def
  set ν := π.map Prod.snd with hν_def
  haveI : MeasureTheory.IsFiniteMeasure ν := by
    rw [hν_def]; exact MeasureTheory.Measure.isFiniteMeasure_map _ _
  refine MeasureTheory.Measure.ext (fun s hs => ?_)
  -- Measurability utilities.
  have h_κs_meas : Measurable (fun y => κ y s) := κ.measurable_coe hs
  have h_fκs_meas : Measurable (fun y : β => f y * κ y s) := hf.mul h_κs_meas
  -- Compute LHS as a `π`-integral.
  -- `bind_apply` + `lintegral_withDensity_eq_lintegral_mul` gives
  -- `∫⁻ y, f y * κ y s ∂ν`, then `lintegral_map` pulls back to `π`.
  have h_lhs :
      (((ν.withDensity f).bind κ)) s =
        ∫⁻ p : α × β, f p.2 * κ p.2 s ∂π := by
    rw [MeasureTheory.Measure.bind_apply hs κ.aemeasurable,
        MeasureTheory.lintegral_withDensity_eq_lintegral_mul _ hf h_κs_meas,
        hν_def]
    -- The integrand `(f * (κ · s)) y` is definitionally `f y * κ y s`; force the
    -- β-reduction via `change` so `lintegral_map` can match the measurable integrand.
    change ∫⁻ (y : β), f y * κ y s ∂(π.map Prod.snd) =
      ∫⁻ (p : α × β), f p.2 * κ p.2 s ∂π
    rw [MeasureTheory.lintegral_map h_fκs_meas measurable_snd]
  -- Compute RHS as a `π`-integral (order: `f p.2 * indicator`, matches compProd output).
  have h_rhs :
      ((π.withDensity (fun p : α × β => f p.2)).map Prod.fst) s =
        ∫⁻ p : α × β, f p.2 * s.indicator (1 : α → ℝ≥0∞) p.1 ∂π := by
    rw [MeasureTheory.Measure.map_apply measurable_fst hs,
        MeasureTheory.withDensity_apply _ (measurable_fst hs),
        ← MeasureTheory.lintegral_indicator (measurable_fst hs)]
    apply MeasureTheory.lintegral_congr
    intro p
    by_cases h_in : p.1 ∈ s
    · rw [Set.indicator_of_mem (show p ∈ Prod.fst ⁻¹' s from h_in),
          Set.indicator_of_mem h_in]
      simp
    · rw [Set.indicator_of_notMem (show p ∉ Prod.fst ⁻¹' s from h_in),
          Set.indicator_of_notMem h_in]
      simp
  -- Bridge via `compProd`: key identity `(π.map snd).compProd κ = π.map swap`.
  have h_compProd :
      ν.compProd κ = π.map (fun p : α × β => (p.2, p.1)) := by
    rw [hν_def, hκ_def]
    exact ProbabilityTheory.compProd_map_condDistrib measurable_fst.aemeasurable
  -- Build the common value `∫⁻ q : β × α, f q.1 * s.indicator 1 q.2 ∂(ν.compProd κ)`.
  have h_bridge :
      ∫⁻ p : α × β, f p.2 * κ p.2 s ∂π =
        ∫⁻ p : α × β, f p.2 * s.indicator (1 : α → ℝ≥0∞) p.1 ∂π := by
    -- Define `g : β × α → ℝ≥0∞` to be `fun q ↦ f q.1 * s.indicator 1 q.2`.
    set g : β × α → ℝ≥0∞ := fun q => f q.1 * s.indicator (1 : α → ℝ≥0∞) q.2 with hg_def
    have hg_meas : Measurable g := by
      refine Measurable.mul (hf.comp measurable_fst) ?_
      exact ((measurable_one.indicator hs).comp measurable_snd)
    -- LHS, expressed as a compProd integral.
    have h_L :
        ∫⁻ p : α × β, f p.2 * κ p.2 s ∂π =
          ∫⁻ q : β × α, g q ∂(ν.compProd κ) := by
      rw [MeasureTheory.Measure.lintegral_compProd hg_meas]
      -- RHS: ∫⁻ y, ∫⁻ x, g (y, x) dκ y ∂ν = ∫⁻ y, ∫⁻ x, f y * s.indicator 1 x dκ y ∂ν
      have h1 : (fun y : β =>
          ∫⁻ x : α, g (y, x) ∂κ y) = fun y => f y * κ y s := by
        funext y
        simp only [hg_def]
        rw [MeasureTheory.lintegral_const_mul _ ((measurable_one.indicator hs))]
        rw [MeasureTheory.lintegral_indicator_one hs]
      rw [h1]
      -- Pulling back along the second projection gives the desired integral over `π`.
      rw [hν_def, MeasureTheory.lintegral_map h_fκs_meas measurable_snd]
    -- RHS, via the compProd → π.map swap substitution. After map-pullback the
    -- integrand evaluates to `g (p.2, p.1) = f p.2 * s.indicator 1 p.1`, matching RHS.
    have h_R :
        ∫⁻ p : α × β, f p.2 * s.indicator (1 : α → ℝ≥0∞) p.1 ∂π =
          ∫⁻ q : β × α, g q ∂(ν.compProd κ) := by
      rw [h_compProd,
          MeasureTheory.lintegral_map hg_meas
            (measurable_snd.prodMk measurable_fst)]
    rw [h_L, ← h_R]
  rw [h_lhs, h_rhs, h_bridge]

namespace Contiguity

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- **Contiguity** (van der Vaart §6.3). A family `Q` is contiguous with respect to `P`
along filter `l` (written informally `Q ⊲ P`) if any sequence of measurable events whose
`P`-probabilities tend to 0 also has `Q`-probabilities tending to 0. -/
def Contiguous (l : Filter ι) (P Q : ∀ i, Measure (Ω i)) : Prop :=
  ∀ A : ∀ i, Set (Ω i), (∀ i, MeasurableSet (A i)) →
    Tendsto (fun i => (P i) (A i)) l (𝓝 0) →
    Tendsto (fun i => (Q i) (A i)) l (𝓝 0)

/-- **Mutual contiguity**: both directions. -/
def MutuallyContiguous (l : Filter ι) (P Q : ∀ i, Measure (Ω i)) : Prop :=
  Contiguous l P Q ∧ Contiguous l Q P

lemma Contiguous.refl (l : Filter ι) (P : ∀ i, Measure (Ω i)) :
    Contiguous l P P := fun _ _ h => h

lemma Contiguous.trans {l : Filter ι} {P Q R : ∀ i, Measure (Ω i)}
    (h₁ : Contiguous l P Q) (h₂ : Contiguous l Q R) :
    Contiguous l P R := fun A hA hP => h₂ A hA (h₁ A hA hP)

lemma MutuallyContiguous.symm {l : Filter ι} {P Q : ∀ i, Measure (Ω i)}
    (h : MutuallyContiguous l P Q) : MutuallyContiguous l Q P :=
  ⟨h.2, h.1⟩

/-! ## Subsequences -/

/-- Transport a set along an equality between indices of a dependent family. -/
private def transportSet (α : ℕ → Type*) {a b : ℕ} (h : a = b)
    (s : Set (α a)) : Set (α b) :=
  h ▸ s

private lemma measurableSet_transportSet
    {α : ℕ → Type*} [∀ n, MeasurableSpace (α n)]
    {a b : ℕ} (h : a = b) {s : Set (α a)} (hs : MeasurableSet s) :
    MeasurableSet (transportSet α h s) := by
  subst h
  exact hs

private lemma transportSet_comp
    {α : ℕ → Type*} {ψ : ℕ → ℕ} (hψ : Function.Injective ψ)
    {k n : ℕ} (h : ψ k = ψ n) (A : ∀ m, Set (α (ψ m))) :
    transportSet α h (A k) = A n := by
  have hkn : k = n := hψ h
  subst hkn
  rfl

/-- Contiguity is preserved by restriction to a strictly monotone subsequence,
including when the sample space depends on the index. -/
theorem Contiguous.comp_subseq
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P Q : ∀ n, Measure (Ω n)}
    (hPQ : Contiguous (ι := ℕ) (Ω := Ω) atTop P Q) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) :
    Contiguous (ι := ℕ) (Ω := fun n => Ω (φ n)) atTop
      (fun n => P (φ n)) (fun n => Q (φ n)) := by
  classical
  intro A hA_meas hA_tendsto
  obtain ⟨B, hB_def⟩ : ∃ B : ∀ m, Set (Ω m), ∀ m, B m =
      if h : ∃ n, φ n = m then transportSet Ω h.choose_spec (A h.choose) else ∅ :=
    ⟨_, fun _ => rfl⟩
  have hB_at : ∀ n, B (φ n) = A n := by
    intro n
    have hex : ∃ k, φ k = φ n := ⟨n, rfl⟩
    rw [hB_def, dif_pos hex, transportSet_comp hφ.injective]
  have hB_meas : ∀ m, MeasurableSet (B m) := by
    intro m
    rw [hB_def]
    by_cases h : ∃ n, φ n = m
    · rw [dif_pos h]
      exact measurableSet_transportSet _ (hA_meas _)
    · rw [dif_neg h]
      exact MeasurableSet.empty
  have hB_empty : ∀ m, (¬ ∃ n, φ n = m) → B m = ∅ := by
    intro m h
    rw [hB_def, dif_neg h]
  have hP_tendsto : Tendsto (fun m => (P m) (B m)) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero] at hA_tendsto
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hA_tendsto ε hε)
    refine Filter.eventually_atTop.mpr ⟨φ N, fun m hm => ?_⟩
    by_cases h : ∃ n, φ n = m
    · obtain ⟨n, rfl⟩ := h
      rw [hB_at n]
      exact hN n (hφ.le_iff_le.mp hm)
    · rw [hB_empty m h]
      simp
  have hQB := hPQ B hB_meas hP_tendsto
  have hcomp := hQB.comp hφ.tendsto_atTop
  simpa [Function.comp_def, hB_at] using hcomp

/-! ## Le Cam's first lemma — asymptotic log normality criterion

vdV Example 6.5. If the log-likelihood ratio `log dQ_n/dP_n` is asymptotically normal
under `P_n` with mean `-σ²/2` and variance `σ²`, then `P_n ⊲⊳ Q_n`.

The direction `Q ⊲ P` is proved via a uniform-integrability argument; the
mutual-contiguity version follows by applying the same machinery to `(-log dQ/dP)`
under `Q`.
-/

section LeCamFirst

/-- **Gaussian mgf at 1**: `∫ exp(x) dN(-v/2, v) = 1`. This is the multiplicative
normalization underlying Le Cam 1 — if `W ~ N(-v/2, v)`, then `E[exp W] = 1`, which is
exactly what keeps the likelihood ratio's mass normalized. -/
private lemma integral_exp_gaussianReal_neg_half_var (v : NNReal) :
    ∫ x, Real.exp x ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) = 1 := by
  have hX :
      Measure.map (id : ℝ → ℝ) (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)
        = ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v :=
    Measure.map_id
  have h := ProbabilityTheory.mgf_gaussianReal hX 1
  rw [ProbabilityTheory.mgf] at h
  simp only [one_mul, id_eq] at h
  rw [show (-(v : ℝ) / 2 * 1 + (v : ℝ) * 1 ^ 2 / 2 : ℝ) = 0 by ring, Real.exp_zero] at h
  exact h

/-- Truncated exponential `min(exp x, M)` as a bounded continuous function, for `M ≥ 0`. -/
private noncomputable def truncExpBCF (M : ℝ) (hM : 0 ≤ M) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min (Real.exp x) M)
    (Real.continuous_exp.min continuous_const)
    M
    (fun x => by
      rw [Real.norm_eq_abs]
      have h_nonneg : 0 ≤ min (Real.exp x) M :=
        le_min (Real.exp_pos x).le hM
      rw [abs_of_nonneg h_nonneg]
      exact min_le_right _ _)

@[simp] private lemma truncExpBCF_apply (M : ℝ) (hM : 0 ≤ M) (x : ℝ) :
    truncExpBCF M hM x = min (Real.exp x) M := rfl

/-- As `M → ∞` (over naturals), `∫ min(exp x, M) dN(-v/2, v) → 1`.

Dominated convergence: `min(exp x, M) ↑ exp x` pointwise, dominated by `exp x` which is
integrable under the log-normal-tilt Gaussian (mgf exists at 1). The limit equals
`∫ exp = 1` by the Gaussian mgf. -/
private lemma tendsto_integral_truncExp_gaussianReal (v : NNReal) :
    Tendsto
      (fun M : ℕ =>
        ∫ x, min (Real.exp x) (M : ℝ) ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))
      atTop (𝓝 1) := by
  set ν : Measure ℝ := ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v with hν_def
  have h_exp_int : Integrable (fun x => Real.exp x) ν := by
    have := ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := -(v : ℝ) / 2) (v := v) 1
    simpa using this
  have h_lim : ∀ᵐ x ∂ν,
      Tendsto (fun M : ℕ => min (Real.exp x) (M : ℝ)) atTop (𝓝 (Real.exp x)) := by
    refine Eventually.of_forall (fun x => ?_)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌈Real.exp x⌉₊] with M hM
    have : Real.exp x ≤ (M : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hM)
    exact (min_eq_left this).symm
  have h_dom : ∀ M : ℕ, ∀ᵐ x ∂ν, ‖min (Real.exp x) (M : ℝ)‖ ≤ Real.exp x := by
    intro M
    refine Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs]
    have h_nonneg : 0 ≤ min (Real.exp x) (M : ℝ) :=
      le_min (Real.exp_pos x).le (Nat.cast_nonneg _)
    rw [abs_of_nonneg h_nonneg]
    exact min_le_left _ _
  have h_meas : ∀ M : ℕ, AEStronglyMeasurable (fun x => min (Real.exp x) (M : ℝ)) ν :=
    fun M => (Real.continuous_exp.min continuous_const).aestronglyMeasurable
  have h_tendsto :=
    MeasureTheory.tendsto_integral_of_dominated_convergence (F := fun M x =>
      min (Real.exp x) (M : ℝ)) (f := fun x => Real.exp x) (bound := fun x => Real.exp x)
      h_meas h_exp_int h_dom h_lim
  rw [integral_exp_gaussianReal_neg_half_var] at h_tendsto
  exact h_tendsto

/-- Under `P_n`, `exp(L n)` is integrable, because `(P n).withDensity (exp ∘ L n)` is a
probability measure. -/
private lemma exp_L_integrable
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (n : ℕ) :
    Integrable (fun ω => Real.exp (L n ω)) (P n) := by
  -- `∫⁻ ofReal (exp L) dP = Q n (univ) = 1 < ∞`, so `exp L` is integrable.
  refine ⟨(Real.continuous_exp.measurable.comp (hL_meas n)).aestronglyMeasurable, ?_⟩
  have h_univ : Q n Set.univ = 1 := measure_univ
  rw [hL_is_log_ratio n, MeasureTheory.withDensity_apply _ MeasurableSet.univ] at h_univ
  simp only [Measure.restrict_univ] at h_univ
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal]
  · rw [h_univ]; exact ENNReal.one_lt_top
  · exact Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)

/-- The Bochner integral `∫ exp(L n) dP_n = 1`. -/
private lemma integral_exp_L_eq_one
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (n : ℕ) :
    ∫ ω, Real.exp (L n ω) ∂(P n) = 1 := by
  have h_lintegral : ∫⁻ ω, ENNReal.ofReal (Real.exp (L n ω)) ∂(P n) = 1 := by
    have h_univ : Q n Set.univ = 1 := measure_univ
    rw [hL_is_log_ratio n, MeasureTheory.withDensity_apply _ MeasurableSet.univ] at h_univ
    simpa using h_univ
  have h_integral_eq := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (μ := P n) (f := fun ω => Real.exp (L n ω))
    (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))
    (Real.continuous_exp.measurable.comp (hL_meas n)).aestronglyMeasurable
  rw [h_integral_eq, h_lintegral]
  simp

/-- **For fixed `M ≥ 0`, weak convergence transfers to integrals of the truncated
exponential**: `∫ min(exp(L n), M) dP_n → ∫ min(exp, M) dN(-v/2, v)` as `n → ∞`.

Follows from `WeakConverges` applied to `truncExpBCF M`, after rewriting the map-integral
via `MeasureTheory.integral_map`. -/
private lemma tendsto_integral_truncExp_L
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))
    (M : ℝ) (hM : 0 ≤ M) :
    Tendsto
      (fun n => ∫ ω, min (Real.exp (L n ω)) M ∂(P n)) atTop
      (𝓝 (∫ x, min (Real.exp x) M ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))) := by
  have h_bcf := h_weak (truncExpBCF M hM)
  -- Use `integral_map` to swap `(P n).map (L n)` integrals back to integrals in `P n`.
  have h_map_n : ∀ n,
      ∫ x, truncExpBCF M hM x ∂((P n).map (L n))
        = ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    intro n
    rw [MeasureTheory.integral_map (hL_meas n).aemeasurable
        (truncExpBCF M hM).continuous.aestronglyMeasurable]
    simp
  simp only [h_map_n] at h_bcf
  simpa using h_bcf

/-- **Uniform-integrability bound on `exp(L n)` under `P_n`**: for every `ε > 0` there
exist a truncation level `M` and an index `N₀` such that `∫ (exp(L n) - M)⁺ dP_n ≤ ε`
for all `n ≥ N₀`, where `(·)⁺ x = max 0 x`.

Proof idea: by `tendsto_integral_truncExp_gaussianReal` pick a natural `M` so that
`∫ min(exp, M) dN > 1 - ε/2`; by `tendsto_integral_truncExp_L` pick `N₀` so that for
`n ≥ N₀`, `∫ min(exp(L n), M) dP_n > 1 - ε`; and use `∫ exp(L n) dP_n = 1` to rearrange.

Thus log-normal weak convergence implies the uniform-integrability estimate
used in Le Cam's third lemma. -/
lemma uniform_integrability_exp_L
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε := by
  intro ε hε
  -- Step 1: pick a natural M₀ with `∫ min(exp, M₀) dN ≥ 1 - ε/2`.
  have h_gaussian := tendsto_integral_truncExp_gaussianReal v
  have h_ev :
      ∀ᶠ M : ℕ in atTop,
        1 - ε / 2 ≤
          ∫ x, min (Real.exp x) (M : ℝ)
            ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
    have h_mem : Set.Ici (1 - ε / 2) ∈ 𝓝 (1 : ℝ) :=
      Ici_mem_nhds (by linarith)
    exact h_gaussian h_mem
  obtain ⟨M₀, hM₀⟩ := h_ev.exists
  set M : ℝ := (M₀ : ℝ) with hM_def
  have hM_nonneg : 0 ≤ M := Nat.cast_nonneg _
  refine ⟨M, hM_nonneg, ?_⟩
  -- Step 2: for fixed M, get `∫ min(exp(L n), M) dP_n → ∫ min(exp, M) dN`.
  have h_trunc_tendsto :=
    tendsto_integral_truncExp_L P L hL_meas v h_weak M hM_nonneg
  -- Step 3: pick N₀ so that for n ≥ N₀, `∫ min(exp(L n), M) dP_n > 1 - ε`.
  have h_target :
      ∀ᶠ n : ℕ in atTop,
        1 - ε ≤ ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    have h_mem : Set.Ioi (1 - ε) ∈ 𝓝 (∫ x, min (Real.exp x) M
        ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) := by
      apply Ioi_mem_nhds
      linarith [hM₀]
    filter_upwards [h_trunc_tendsto h_mem] with n hn
    exact le_of_lt (Set.mem_Ioi.mp hn)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_target
  refine ⟨N₀, ?_⟩
  intro n hn
  -- Step 4: rearrange using `∫ exp(L n) = 1`.
  have h_exp_int := exp_L_integrable P Q L hL_meas hL_is_log_ratio n
  have h_trunc_int : Integrable (fun ω => min (Real.exp (L n ω)) M) (P n) := by
    refine h_exp_int.mono' ?_ ?_
    · exact ((Real.continuous_exp.measurable.comp
        (hL_meas n)).min measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact min_le_left _ _
      · exact le_min (Real.exp_pos _).le hM_nonneg
  have h_diff_eq :
      ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
        = 1 - ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    rw [MeasureTheory.integral_sub h_exp_int h_trunc_int,
      integral_exp_L_eq_one P Q L hL_meas hL_is_log_ratio]
  rw [h_diff_eq]
  linarith [hN₀ n hn]

/-- **Contiguity from asymptotic log-normality** (vdV Example 6.5, direction `Q ⊲ P`).

If `L n = log dQ_n/dP_n` is asymptotically `N(-σ²/2, σ²)` under `P n`, then for any
sequence of measurable events `A n` with `P_n(A_n) → 0`, we also have `Q_n(A_n) → 0`. -/
theorem contiguous_of_asymptotically_log_normal
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    Contiguous (ι := ℕ) (Ω := Ω) atTop P Q := by
  intro A hA_meas hA_tendsto
  -- Step 0: reduce to real-valued convergence via `.toReal`.
  -- `Q_n`, `P_n` are prob measures so `(Q n)(A n), (P n)(A n) < ⊤` always.
  have h_Q_lt_top : ∀ n, (Q n) (A n) ≠ ⊤ := fun n => (measure_lt_top (Q n) _).ne
  have h_P_lt_top : ∀ n, (P n) (A n) ≠ ⊤ := fun n => (measure_lt_top (P n) _).ne
  have hA_real : Tendsto (fun n => ((P n) (A n)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hA_tendsto
    simpa using! this
  suffices h : Tendsto (fun n => ((Q n) (A n)).toReal) atTop (𝓝 0) by
    have h_of_real :
        Tendsto (fun n => ENNReal.ofReal ((Q n) (A n)).toReal) atTop (𝓝 0) := by
      have h_comp := (ENNReal.continuous_ofReal.tendsto 0).comp h
      simp only [ENNReal.ofReal_zero] at h_comp
      exact h_comp
    have h_eq : (fun n => ENNReal.ofReal ((Q n) (A n)).toReal) = fun n => (Q n) (A n) := by
      funext n; rw [ENNReal.ofReal_toReal (h_Q_lt_top n)]
    rw [h_eq] at h_of_real
    exact h_of_real
  -- It remains to prove convergence of the real-valued measures.
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- UI: get M and N₁ with `∫ (exp(L n) - min(exp(L n), M)) dP_n ≤ ε/2` for `n ≥ N₁`.
  obtain ⟨M, hM_nonneg, N₁, hN₁⟩ :=
    uniform_integrability_exp_L P Q L hL_meas hL_is_log_ratio v h_weak (ε / 2) (by linarith)
  have hM1_pos : 0 < M + 1 := by linarith
  -- Pick `N₂` so for `n ≥ N₂`, `((P n) (A n)).toReal < ε / (2·(M+1))`.
  rw [Metric.tendsto_nhds] at hA_real
  have h_threshold : 0 < ε / (2 * (M + 1)) := by positivity
  have hA_ev := hA_real (ε / (2 * (M + 1))) h_threshold
  rw [Filter.eventually_atTop] at hA_ev
  obtain ⟨N₂, hN₂⟩ := hA_ev
  rw [Filter.eventually_atTop]
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  -- Unfold `dist (·) 0` for the nonneg real `((Q n)(A n)).toReal`.
  have hQ_nonneg : 0 ≤ ((Q n) (A n)).toReal := ENNReal.toReal_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hQ_nonneg]
  -- Express `((Q n) (A n)).toReal` as a set Bochner integral of `exp(L n)`.
  have h_Q_eq : ((Q n) (A n)).toReal = ∫ ω in A n, Real.exp (L n ω) ∂(P n) := by
    rw [hL_is_log_ratio n, MeasureTheory.withDensity_apply _ (hA_meas n)]
    exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
      (Real.continuous_exp.measurable.comp (hL_meas n)).aestronglyMeasurable).symm
  -- Integrability of `exp(L n)` and its truncation / residue.
  have h_exp_int := exp_L_integrable P Q L hL_meas hL_is_log_ratio n
  have h_min_meas : Measurable (fun ω => min (Real.exp (L n ω)) M) :=
    (Real.continuous_exp.measurable.comp (hL_meas n)).min measurable_const
  have h_min_int : Integrable (fun ω => min (Real.exp (L n ω)) M) (P n) := by
    refine h_exp_int.mono' h_min_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.exp_pos _).le hM_nonneg)]
    exact min_le_left _ _
  have h_diff_int : Integrable
      (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M) (P n) :=
    h_exp_int.sub h_min_int
  have h_diff_nonneg :
      0 ≤ᵐ[P n] fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M :=
    Filter.Eventually.of_forall
      (fun ω => sub_nonneg.mpr (min_le_left _ _))
  -- Decompose the set integral.
  have h_int_decomp :
      ∫ ω in A n, Real.exp (L n ω) ∂(P n)
        = ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n)
          + ∫ ω in A n, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) := by
    rw [← MeasureTheory.integral_add h_min_int.restrict h_diff_int.restrict]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    ring
  -- Bound Term 1: `∫ in A n, min(exp, M) ≤ M · P_n(A_n).real`.
  have h_T1_bound :
      ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n) ≤ M * ((P n) (A n)).toReal := by
    calc ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n)
        ≤ ∫ _ in A n, M ∂(P n) := by
          refine MeasureTheory.setIntegral_mono_on h_min_int.restrict
            (integrable_const M).restrict (hA_meas n) (fun ω _ => ?_)
          exact min_le_right _ _
      _ = ((P n) (A n)).toReal * M := by
          rw [MeasureTheory.setIntegral_const]
          rfl
      _ = M * ((P n) (A n)).toReal := by ring
  -- Bound Term 2: restrict ≤ full, then UI.
  have h_T2_bound :
      ∫ ω in A n, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε / 2 :=
    le_trans (MeasureTheory.setIntegral_le_integral h_diff_int h_diff_nonneg) (hN₁ n hn₁)
  -- Convert hN₂ from dist form to a direct inequality.
  have hP_A_real_lt : ((P n) (A n)).toReal < ε / (2 * (M + 1)) := by
    have := hN₂ n hn₂
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at this
    exact this
  -- Assemble: `((Q n)(A n)).toReal ≤ M · P_n(A_n).real + ε/2`, then show this is `< ε`.
  have h_total_le :
      ((Q n) (A n)).toReal ≤ M * ((P n) (A n)).toReal + ε / 2 := by
    calc ((Q n) (A n)).toReal
        = ∫ ω in A n, Real.exp (L n ω) ∂(P n) := h_Q_eq
      _ = ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n)
            + ∫ ω in A n, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) :=
            h_int_decomp
      _ ≤ M * ((P n) (A n)).toReal + ε / 2 := by
            linarith [h_T1_bound, h_T2_bound]
  -- The final strict bound follows by separating the cases `M = 0` and `M > 0`.
  rcases eq_or_lt_of_le hM_nonneg with hM_eq | hM_pos
  · -- `M = 0`: LHS = ε/2 < ε.
    have : M * ((P n) (A n)).toReal = 0 := by rw [← hM_eq]; ring
    linarith
  · -- `M > 0`: use strict `hP_A_real_lt` and the `M/(M+1) ≤ 1` bound.
    have h_strict_T1 : M * ((P n) (A n)).toReal < M * (ε / (2 * (M + 1))) :=
      mul_lt_mul_of_pos_left hP_A_real_lt hM_pos
    have h_factor_le_half : M * (ε / (2 * (M + 1))) ≤ ε / 2 := by
      have h_ratio : M / (M + 1) ≤ 1 := (div_le_one hM1_pos).mpr (by linarith)
      have hε2_nonneg : 0 ≤ ε / 2 := by linarith
      calc M * (ε / (2 * (M + 1)))
          = (M / (M + 1)) * (ε / 2) := by field_simp
        _ ≤ 1 * (ε / 2) := mul_le_mul_of_nonneg_right h_ratio hε2_nonneg
        _ = ε / 2 := one_mul _
    linarith

end LeCamFirst

section ReverseDirection

/-- **Inverse-density identity**: if `Q = P.withDensity (ofReal ∘ exp ∘ L)` with
`exp ∘ L > 0` pointwise, then `P = Q.withDensity (ofReal ∘ exp ∘ (-L))`.

Follows from `MeasureTheory.withDensity_inv_same` applied to `f = ofReal ∘ exp ∘ L`,
using that `exp > 0` (so `f` is nonzero a.e.) and `ofReal r < ⊤` (so `f ≠ ⊤` a.e.),
plus `(ofReal (exp x))⁻¹ = ofReal (exp (-x))`. -/
private lemma P_eq_Q_withDensity_neg
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (n : ℕ) :
    P n = (Q n).withDensity (fun ω => ENNReal.ofReal (Real.exp (-L n ω))) := by
  have hf_meas : Measurable (fun ω => ENNReal.ofReal (Real.exp (L n ω))) :=
    (Real.continuous_exp.measurable.comp (hL_meas n)).ennreal_ofReal
  have hf_ne_zero : ∀ᵐ ω ∂(P n), ENNReal.ofReal (Real.exp (L n ω)) ≠ 0 := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  have hf_ne_top : ∀ᵐ ω ∂(P n), ENNReal.ofReal (Real.exp (L n ω)) ≠ ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_ne_top)
  have h_inv := MeasureTheory.withDensity_inv_same hf_meas hf_ne_zero hf_ne_top
  -- `h_inv : ((P n).withDensity f).withDensity (fun ω => (f ω)⁻¹) = P n`
  rw [← hL_is_log_ratio n] at h_inv
  rw [← h_inv]
  congr 1
  funext ω
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), Real.exp_neg]

/-! ### Gaussian shift identity

The algebraic backbone of the reverse direction. Tilting `N(-v/2, v)` by `exp` yields
`N(v/2, v)`; reflecting `N(v/2, v)` through 0 yields `N(-v/2, v)` back. The net effect
is the integral identity `∫ f(-x) · exp(x) dN(-v/2, v) = ∫ f(y) dN(-v/2, v)`.
-/

/-- **Gaussian PDF multiplicative shift by `exp`**.

`gaussianPDFReal (-v/2) v x · exp(x) = gaussianPDFReal (v/2) v x`.

This is the pointwise algebraic identity underlying the measure identity
`N(-v/2, v).withDensity (exp) = N(v/2, v)`. Proved by expanding both sides to the
common form `(2πv)^{-1/2} · exp(-x²/(2v) + x/2 - v/8)` via `Real.exp_add` + field algebra. -/
private lemma gaussianPDFReal_neg_half_mul_exp_eq (v : NNReal) (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal (-(v : ℝ) / 2) v x * Real.exp x
      = ProbabilityTheory.gaussianPDFReal ((v : ℝ) / 2) v x := by
  by_cases hv : v = 0
  · subst hv
    simp [ProbabilityTheory.gaussianPDFReal_zero_var]
  have hv_pos : (0 : ℝ) < (v : ℝ) := by
    refine lt_of_le_of_ne v.coe_nonneg (Ne.symm ?_)
    intro h
    exact hv (NNReal.coe_injective h)
  have h2v_ne : (2 : ℝ) * (v : ℝ) ≠ 0 := by positivity
  simp only [ProbabilityTheory.gaussianPDFReal]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  field_simp
  ring

/-- **Gaussian tilting by `exp`**:
`(N(-v/2, v)).withDensity (x ↦ ofReal (exp x)) = N(v/2, v)`.

For `v = 0`, both sides reduce to `dirac 0` (using `dirac_withDensity` + `exp 0 = 1`).
For `v > 0`, unfold `gaussianReal` to `volume.withDensity (gaussianPDF …)`, combine the
two `withDensity` layers via `withDensity_mul`, and close by the pointwise PDF identity. -/
private lemma gaussianReal_neg_half_withDensity_exp (v : NNReal) :
    (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v).withDensity
        (fun x => ENNReal.ofReal (Real.exp x)) =
      ProbabilityTheory.gaussianReal ((v : ℝ) / 2) v := by
  by_cases hv : v = 0
  · subst hv
    simp only [NNReal.coe_zero, neg_zero, zero_div, ProbabilityTheory.gaussianReal_zero_var,
      MeasureTheory.dirac_withDensity, Real.exp_zero, ENNReal.ofReal_one, one_smul]
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ hv,
      ProbabilityTheory.gaussianReal_of_var_ne_zero _ hv]
  rw [← MeasureTheory.withDensity_mul _
      (ProbabilityTheory.measurable_gaussianPDF _ _)
      Real.continuous_exp.measurable.ennreal_ofReal]
  congr 1
  ext x
  simp only [Pi.mul_apply, ProbabilityTheory.gaussianPDF]
  rw [← ENNReal.ofReal_mul (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)]
  congr 1
  exact gaussianPDFReal_neg_half_mul_exp_eq v x

/-- **Gaussian shift integral identity**:
`∫ f(-x) · exp(x) dN(-v/2, v) = ∫ f dN(-v/2, v)` for bounded continuous `f`.

Chain: tilt `N(-v/2, v)` by `exp` → `N(v/2, v)` (via `gaussianReal_neg_half_withDensity_exp`);
reflect `N(v/2, v)` through 0 → `N(-v/2, v)` (via `gaussianReal_map_neg`). -/
private lemma integral_gaussianReal_neg_half_shift (v : NNReal) (f : ℝ →ᵇ ℝ) :
    ∫ x, f (-x) * Real.exp x ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)
      = ∫ x, f x ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
  set ν_neg := ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v with hν_neg
  set ν_pos := ProbabilityTheory.gaussianReal ((v : ℝ) / 2) v with hν_pos
  have hexp_meas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp x)) :=
    Real.continuous_exp.measurable.ennreal_ofReal
  have hexp_lt_top : ∀ᵐ x ∂ν_neg, ENNReal.ofReal (Real.exp x) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  calc ∫ x, f (-x) * Real.exp x ∂ν_neg
      = ∫ x, (ENNReal.ofReal (Real.exp x)).toReal • f (-x) ∂ν_neg := by
        refine integral_congr_ae ?_
        refine Filter.Eventually.of_forall (fun x => ?_)
        change f (-x) * Real.exp x = (ENNReal.ofReal (Real.exp x)).toReal • f (-x)
        rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
    _ = ∫ x, f (-x) ∂(ν_neg.withDensity (fun x => ENNReal.ofReal (Real.exp x))) :=
        (integral_withDensity_eq_integral_toReal_smul hexp_meas hexp_lt_top
          (fun x => f (-x))).symm
    _ = ∫ x, f (-x) ∂ν_pos := by
        rw [hν_neg, hν_pos, gaussianReal_neg_half_withDensity_exp]
    _ = ∫ y, f y ∂(ν_pos.map (fun x => -x)) :=
        (MeasureTheory.integral_map measurable_neg.aemeasurable
          f.continuous.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(ProbabilityTheory.gaussianReal (-((v : ℝ) / 2)) v) := by
        rw [hν_pos, ProbabilityTheory.gaussianReal_map_neg]
    _ = ∫ x, f x ∂ν_neg := by
        rw [hν_neg, neg_div]

/-- **Change of measure helper**: `∫ f ∂(Q.map (-L)) = ∫ f(-x)·exp x ∂(P.map L)`,
using `Q = P.withDensity (exp ∘ L)` plus `integral_map` on both ends. -/
private lemma integral_f_neg_Q_eq_f_neg_exp_P
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω)
    (L : Ω → ℝ) (hL_meas : Measurable L)
    (hL_is_log_ratio :
        Q = P.withDensity (fun ω => ENNReal.ofReal (Real.exp (L ω))))
    (f : ℝ →ᵇ ℝ) :
    ∫ x, f x ∂(Q.map (fun ω => -L ω))
      = ∫ x, f (-x) * Real.exp x ∂(P.map L) := by
  have h_exp_meas : Measurable (fun ω => ENNReal.ofReal (Real.exp (L ω))) :=
    (Real.continuous_exp.measurable.comp hL_meas).ennreal_ofReal
  have h_exp_lt_top : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (L ω)) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have h_integrand_meas :
      AEStronglyMeasurable (fun x : ℝ => f (-x) * Real.exp x) (P.map L) :=
    ((f.continuous.comp continuous_neg).mul Real.continuous_exp).aestronglyMeasurable
  calc ∫ x, f x ∂(Q.map (fun ω => -L ω))
      = ∫ ω, f (-L ω) ∂Q :=
        MeasureTheory.integral_map hL_meas.neg.aemeasurable
          f.continuous.aestronglyMeasurable
    _ = ∫ ω, f (-L ω)
          ∂(P.withDensity (fun ω => ENNReal.ofReal (Real.exp (L ω)))) := by
        rw [← hL_is_log_ratio]
    _ = ∫ ω, (ENNReal.ofReal (Real.exp (L ω))).toReal • f (-L ω) ∂P :=
        integral_withDensity_eq_integral_toReal_smul h_exp_meas h_exp_lt_top
          (fun ω => f (-L ω))
    _ = ∫ ω, f (-L ω) * Real.exp (L ω) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
        change (ENNReal.ofReal (Real.exp (L ω))).toReal • f (-L ω)
          = f (-L ω) * Real.exp (L ω)
        rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
    _ = ∫ x, f (-x) * Real.exp x ∂(P.map L) :=
        (MeasureTheory.integral_map hL_meas.aemeasurable h_integrand_meas).symm

/-- **Tilted weak convergence**: under the tilted measure `Q n = P n.withDensity (exp ∘ L n)`,
the law of `-L n` weakly converges to `N(-v/2, v)`.

**Strategy** (the analytical content, broken into steps):

1. `integral_f_neg_Q_eq_f_neg_exp_P` rewrites `∫ f d((Q n).map (-L n))` as
   `∫ f(-x)·exp x d((P n).map L n)` (change of measure + `integral_map`).
2. `integral_gaussianReal_neg_half_shift` rewrites the target
   `∫ f dN(-v/2, v)` as `∫ f(-x)·exp x dN(-v/2, v)` — the Gaussian shift identity
   (derived from the PDF identity `gaussianPDFReal_neg_half_mul_exp_eq` +
   `gaussianReal_neg_half_withDensity_exp` + `gaussianReal_map_neg`).
3. Convergence of `∫ f(-x)·exp x dν_n → ∫ f(-x)·exp x dν` for `ν_n := (P n).map L n`
   follows from the truncation+UI argument: let
   `g_M(x) := f(-x) · min(exp x, M)` (bounded continuous),
   then
   - `|∫ f(-x)·exp x dν_n - ∫ g_M dν_n| ≤ ‖f‖ · ∫ (exp x - min(exp x, M)) dν_n`
     = `‖f‖ · ∫ (exp(L n) - min(exp(L n), M)) dP_n`, ≤ `ε/(3C)` by `uniform_integrability_exp_L`;
   - `|∫ g_M dν_n - ∫ g_M dν| < ε/3` by weak convergence of `ν_n ⇝ ν` applied to `g_M`;
   - `|∫ g_M dν - ∫ f(-x)·exp x dν| ≤ ‖f‖ · (1 - ∫ min(exp x, M) dν)`,
     ≤ `ε/(3C)` by `tendsto_integral_truncExp_gaussianReal` + choice of `M`.

   Triangle inequality closes with total `< ε`. -/
private lemma weakConverges_Q_neg_L_gaussianReal_neg_half
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    WeakConverges (fun n => (Q n).map (fun ω => -L n ω))
      (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
  intro f
  set ν := ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v with hν_def
  -- Rewrite target via Gaussian shift identity, each LHS term via change-of-measure.
  rw [← integral_gaussianReal_neg_half_shift v f]
  have h_rewrite : ∀ n, ∫ x, f x ∂((Q n).map (fun ω => -L n ω))
      = ∫ x, f (-x) * Real.exp x ∂((P n).map (L n)) := fun n =>
    integral_f_neg_Q_eq_f_neg_exp_P (P n) (Q n) (L n) (hL_meas n) (hL_is_log_ratio n) f
  simp_rw [h_rewrite]
  -- Continuity + norm bounds used throughout.
  have hfneg_cont : Continuous (fun x : ℝ => f (-x)) := f.continuous.comp continuous_neg
  have hfneg_bound : ∀ x : ℝ, ‖f (-x)‖ ≤ ‖f‖ := fun x => f.norm_coe_le_norm _
  have h_exp_nonneg : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos _).le
  -- Gaussian side: `∫ exp dν = 1`, `exp` integrable, and `tendsto ∫ min(exp, M) → 1` as M → ∞.
  have h_exp_int_ν : Integrable (fun x : ℝ => Real.exp x) ν := by
    rw [hν_def]
    have := ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := -(v : ℝ) / 2) (v := v) 1
    simpa using this
  have h_exp_int_ν_eq_one : ∫ x, Real.exp x ∂ν = 1 := by
    rw [hν_def]; exact integral_exp_gaussianReal_neg_half_var v
  -- Helper: residue bound for `|∫ f(-x) · exp x ∂μ - ∫ f(-x) · min(exp, M) ∂μ|`,
  -- `≤ ‖f‖ · ∫ (exp - min) dμ`, for any `μ` on ℝ with `exp` integrable under `μ`.
  have h_residue :
      ∀ (μ : Measure ℝ) (M : ℝ), 0 ≤ M →
        Integrable (fun x : ℝ => Real.exp x) μ →
        |∫ x, f (-x) * Real.exp x ∂μ - ∫ x, f (-x) * min (Real.exp x) M ∂μ|
          ≤ ‖f‖ * ∫ x, (Real.exp x - min (Real.exp x) M) ∂μ := by
    intro μ M hM h_exp_int
    have h_min_nn : ∀ x, 0 ≤ min (Real.exp x) M := fun x =>
      le_min (h_exp_nonneg x) hM
    have h_min_le : ∀ x, min (Real.exp x) M ≤ Real.exp x := fun x => min_le_left _ _
    have h_min_meas : Measurable (fun x : ℝ => min (Real.exp x) M) :=
      Real.continuous_exp.measurable.min measurable_const
    have h_min_int : Integrable (fun x : ℝ => min (Real.exp x) M) μ := by
      refine h_exp_int.mono' h_min_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun x => ?_))
      simp only [Real.norm_eq_abs, abs_of_nonneg (h_min_nn x)]
      exact h_min_le x
    have h_fneg_bound_ae : ∀ᵐ x ∂μ, ‖f (-x)‖ ≤ ‖f‖ :=
      Filter.Eventually.of_forall hfneg_bound
    have h_fneg_ae : AEStronglyMeasurable (fun x : ℝ => f (-x)) μ :=
      hfneg_cont.aestronglyMeasurable
    have h_fexp_int : Integrable (fun x : ℝ => f (-x) * Real.exp x) μ :=
      h_exp_int.bdd_mul h_fneg_ae h_fneg_bound_ae
    have h_fmin_int : Integrable (fun x : ℝ => f (-x) * min (Real.exp x) M) μ :=
      h_min_int.bdd_mul h_fneg_ae h_fneg_bound_ae
    rw [← integral_sub h_fexp_int h_fmin_int]
    have h_diff_eq : (fun x : ℝ => f (-x) * Real.exp x - f (-x) * min (Real.exp x) M)
        = fun x => f (-x) * (Real.exp x - min (Real.exp x) M) := by
      funext x; ring
    rw [h_diff_eq]
    have h_diff_int : Integrable
        (fun x : ℝ => f (-x) * (Real.exp x - min (Real.exp x) M)) μ := by
      have : (fun x : ℝ => f (-x) * (Real.exp x - min (Real.exp x) M))
          = fun x => f (-x) * Real.exp x - f (-x) * min (Real.exp x) M := by
        funext x; ring
      rw [this]; exact h_fexp_int.sub h_fmin_int
    calc |∫ x, f (-x) * (Real.exp x - min (Real.exp x) M) ∂μ|
        ≤ ∫ x, |f (-x) * (Real.exp x - min (Real.exp x) M)| ∂μ :=
          abs_integral_le_integral_abs
      _ = ∫ x, |f (-x)| * (Real.exp x - min (Real.exp x) M) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          change |f (-x) * (Real.exp x - min (Real.exp x) M)|
            = |f (-x)| * (Real.exp x - min (Real.exp x) M)
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (h_min_le x))]
      _ ≤ ∫ x, ‖f‖ * (Real.exp x - min (Real.exp x) M) ∂μ := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall
              (fun x => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (h_min_le x))))
            ((h_exp_int.sub h_min_int).const_mul ‖f‖)
            (Filter.Eventually.of_forall (fun x => ?_))
          refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr (h_min_le x))
          rw [← Real.norm_eq_abs]; exact hfneg_bound x
      _ = ‖f‖ * ∫ x, (Real.exp x - min (Real.exp x) M) ∂μ := integral_const_mul _ _
  -- Setup for ε argument.
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C : ℝ := ‖f‖ + 1 with hC_def
  have hC_pos : 0 < C := by positivity
  have hnorm_le_C : ‖f‖ ≤ C := by simp [hC_def]
  have hthresh_pos : 0 < ε / (3 * C) := by positivity
  -- (A) UI on sequence side.
  obtain ⟨M_UI, hM_UI_nonneg, N_UI, hN_UI⟩ :=
    uniform_integrability_exp_L P Q L hL_meas hL_is_log_ratio v h_weak
      (ε / (3 * C)) hthresh_pos
  -- (B) Pick M_target : ℕ so that `∫ min(exp, M_target) dν > 1 - ε/(3C)`.
  have h_ev_gauss : ∀ᶠ M : ℕ in atTop,
      (1 : ℝ) - ε / (3 * C) < ∫ x, min (Real.exp x) (M : ℝ) ∂ν := by
    have h_mem : Set.Ioi ((1 : ℝ) - ε / (3 * C)) ∈ 𝓝 (1 : ℝ) :=
      Ioi_mem_nhds (by linarith)
    exact tendsto_integral_truncExp_gaussianReal v h_mem
  obtain ⟨M_target, hM_target⟩ := h_ev_gauss.exists
  -- Take `M := max M_UI (M_target : ℝ) ≥ 0`.
  set M : ℝ := max M_UI (M_target : ℝ) with hM_def
  have hM_nonneg : 0 ≤ M := le_max_of_le_left hM_UI_nonneg
  have hM_ge_UI : M_UI ≤ M := le_max_left _ _
  have hM_ge_target : (M_target : ℝ) ≤ M := le_max_right _ _
  -- BCF `g_M(x) := f(-x) · min(exp x, M)`.
  let g_M : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f (-x) * min (Real.exp x) M)
    (hfneg_cont.mul (Real.continuous_exp.min continuous_const))
    (‖f‖ * M)
    (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : 0 ≤ min (Real.exp x) M := le_min (h_exp_nonneg x) hM_nonneg
      rw [abs_of_nonneg h2]
      refine mul_le_mul ?_ (min_le_right _ _) h2 (norm_nonneg _)
      rw [← Real.norm_eq_abs]; exact hfneg_bound x)
  have hg_M_apply : ∀ x, g_M x = f (-x) * min (Real.exp x) M := fun _ => rfl
  -- (D) Weak convergence at `g_M`.
  have h_weak_gM := h_weak g_M
  rw [Metric.tendsto_nhds] at h_weak_gM
  have hε3_pos : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨N_weak, hN_weak⟩ :=
    Filter.eventually_atTop.mp (h_weak_gM (ε / 3) hε3_pos)
  rw [Filter.eventually_atTop]
  refine ⟨max N_UI N_weak, fun n hn => ?_⟩
  have hn_UI : N_UI ≤ n := le_of_max_le_left hn
  have hn_weak : N_weak ≤ n := le_of_max_le_right hn
  -- Sequence-side residue bound needs `exp` integrable under `(P n).map L n`.
  have h_exp_int_Pn : Integrable (fun ω => Real.exp (L n ω)) (P n) :=
    exp_L_integrable P Q L hL_meas hL_is_log_ratio n
  have h_exp_int_map_n : Integrable (fun x : ℝ => Real.exp x) ((P n).map (L n)) := by
    rw [MeasureTheory.integrable_map_measure Real.continuous_exp.aestronglyMeasurable
        (hL_meas n).aemeasurable]
    exact h_exp_int_Pn
  -- UI bound at enlarged M: monotonicity of `min(exp, ·)` in M.
  have h_min_mono_M : ∀ ω, min (Real.exp (L n ω)) M_UI ≤ min (Real.exp (L n ω)) M :=
    fun ω => min_le_min_left _ hM_ge_UI
  have h_int_trunc_UI : Integrable
      (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI) (P n) := by
    refine h_exp_int_Pn.sub ?_
    refine h_exp_int_Pn.mono'
      ((Real.continuous_exp.measurable.comp (hL_meas n)).min
        measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_UI_nonneg)]
    exact min_le_left _ _
  have h_int_trunc_M : Integrable
      (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M) (P n) := by
    refine h_exp_int_Pn.sub ?_
    refine h_exp_int_Pn.mono'
      ((Real.continuous_exp.measurable.comp (hL_meas n)).min
        measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_nonneg)]
    exact min_le_left _ _
  have h_UI_bound_Pn :
      ∫ ω, (Real.exp (L n ω) - min (Real.exp (L n ω)) M) ∂(P n) ≤ ε / (3 * C) :=
    calc ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
        ≤ ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI ∂(P n) :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall
              (fun ω => sub_nonneg.mpr (min_le_left _ _)))
            h_int_trunc_UI
            (Filter.Eventually.of_forall
              (fun ω => by linarith [h_min_mono_M ω]))
      _ ≤ ε / (3 * C) := hN_UI n hn_UI
  have h_UI_bound_map_n :
      ∫ x, (Real.exp x - min (Real.exp x) M) ∂((P n).map (L n))
        ≤ ε / (3 * C) := by
    rw [MeasureTheory.integral_map (hL_meas n).aemeasurable]
    · exact h_UI_bound_Pn
    · exact (Real.continuous_exp.sub
        (Real.continuous_exp.min continuous_const)).aestronglyMeasurable
  -- Target-side residue bound: `∫ (exp - min(exp, M)) dν ≤ ε/(3C)`.
  have h_trunc_int_ν : Integrable (fun x : ℝ => min (Real.exp x) M) ν := by
    refine h_exp_int_ν.mono'
      (Real.continuous_exp.min continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_nonneg)]
    exact min_le_left _ _
  have h_target_trunc_M_lb :
      (1 : ℝ) - ε / (3 * C) ≤ ∫ x, min (Real.exp x) M ∂ν := by
    have h_mono :
        ∫ x, min (Real.exp x) (M_target : ℝ) ∂ν ≤ ∫ x, min (Real.exp x) M ∂ν := by
      have h_trunc_target_int : Integrable (fun x : ℝ => min (Real.exp x) (M_target : ℝ)) ν := by
        refine h_exp_int_ν.mono'
          (Real.continuous_exp.min continuous_const).aestronglyMeasurable
          (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) (Nat.cast_nonneg _))]
        exact min_le_left _ _
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall
          (fun x => le_min (h_exp_nonneg _) (Nat.cast_nonneg _)))
        h_trunc_int_ν
        (Filter.Eventually.of_forall (fun x => min_le_min_left _ hM_ge_target))
    linarith [hM_target]
  have h_target_bound_ν :
      ∫ x, (Real.exp x - min (Real.exp x) M) ∂ν ≤ ε / (3 * C) := by
    rw [integral_sub h_exp_int_ν h_trunc_int_ν, h_exp_int_ν_eq_one]
    linarith [h_target_trunc_M_lb]
  -- Apply residue bound on both sides.
  have h_res_map_n := h_residue ((P n).map (L n)) M hM_nonneg h_exp_int_map_n
  have h_res_ν := h_residue ν M hM_nonneg h_exp_int_ν
  -- Build the three pieces of the triangle inequality.
  rw [Real.dist_eq]
  have h_weak_bound : |∫ x, g_M x ∂((P n).map (L n)) - ∫ x, g_M x ∂ν| < ε / 3 := by
    have := hN_weak n hn_weak
    rwa [Real.dist_eq] at this
  have h_res_nonneg : 0 ≤ ‖f‖ := norm_nonneg _
  have h_seq_piece : |∫ x, f (-x) * Real.exp x ∂((P n).map (L n))
        - ∫ x, g_M x ∂((P n).map (L n))| ≤ ε / 3 := by
    have h_gM_eq : ∫ x, g_M x ∂((P n).map (L n))
        = ∫ x, f (-x) * min (Real.exp x) M ∂((P n).map (L n)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => hg_M_apply x))
    rw [h_gM_eq]
    calc |∫ x, f (-x) * Real.exp x ∂((P n).map (L n))
            - ∫ x, f (-x) * min (Real.exp x) M ∂((P n).map (L n))|
        ≤ ‖f‖ * ∫ x, (Real.exp x - min (Real.exp x) M) ∂((P n).map (L n)) := h_res_map_n
      _ ≤ ‖f‖ * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_left h_UI_bound_map_n h_res_nonneg
      _ ≤ C * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
      _ = ε / 3 := by field_simp
  have h_target_piece : |∫ x, g_M x ∂ν - ∫ x, f (-x) * Real.exp x ∂ν| ≤ ε / 3 := by
    have h_gM_eq : ∫ x, g_M x ∂ν = ∫ x, f (-x) * min (Real.exp x) M ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => hg_M_apply x))
    rw [h_gM_eq, abs_sub_comm]
    calc |∫ x, f (-x) * Real.exp x ∂ν - ∫ x, f (-x) * min (Real.exp x) M ∂ν|
        ≤ ‖f‖ * ∫ x, (Real.exp x - min (Real.exp x) M) ∂ν := h_res_ν
      _ ≤ ‖f‖ * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_left h_target_bound_ν h_res_nonneg
      _ ≤ C * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
      _ = ε / 3 := by field_simp
  -- Triangle inequality: split A - E = (A - B) + (B - D) + (D - E).
  set A := ∫ x, f (-x) * Real.exp x ∂((P n).map (L n))
  set B := ∫ x, g_M x ∂((P n).map (L n))
  set D := ∫ x, g_M x ∂ν
  set E := ∫ x, f (-x) * Real.exp x ∂ν
  have h_split : A - E = (A - B) + (B - D) + (D - E) := by ring
  rw [h_split]
  calc |(A - B) + (B - D) + (D - E)|
      ≤ |(A - B) + (B - D)| + |D - E| := abs_add_le _ _
    _ ≤ |A - B| + |B - D| + |D - E| := by linarith [abs_add_le (A - B) (B - D)]
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith [h_seq_piece, h_weak_bound, h_target_piece]
    _ = ε := by ring

end ReverseDirection

/-- **Le Cam's first lemma** (vdV Example 6.5, mutual-contiguity form).

If the log-likelihood ratio `L n = log dQ_n/dP_n` is asymptotically `N(-σ²/2, σ²)` under
`P n`, then `P n ⊲⊳ Q n`.

The reverse direction `P ⊲ Q` is obtained by applying the forward direction with `P` and
`Q` swapped and `L` negated:
* the inverse-density identity `P = Q.withDensity (exp ∘ (-L))` (from
  `P_eq_Q_withDensity_neg`);
* the tilted weak convergence `(Q n).map (-L n) → N(-v/2, v)` (from
  `weakConverges_Q_neg_L_gaussianReal_neg_half`). -/
theorem mutuallyContiguous_of_asymptotically_log_normal
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    MutuallyContiguous (ι := ℕ) (Ω := Ω) atTop P Q := by
  refine ⟨contiguous_of_asymptotically_log_normal P Q L hL_meas hL_is_log_ratio v h_weak, ?_⟩
  -- Reverse direction: apply the forward direction with `P` ↔ `Q` and `L ↦ -L`.
  have h_inv : ∀ n, P n = (Q n).withDensity (fun ω => ENNReal.ofReal (Real.exp (-L n ω))) :=
    P_eq_Q_withDensity_neg P Q L hL_meas hL_is_log_ratio
  have h_weak_neg :
      WeakConverges (fun n => (Q n).map (fun ω => -L n ω))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) :=
    weakConverges_Q_neg_L_gaussianReal_neg_half P Q L hL_meas hL_is_log_ratio v h_weak
  exact contiguous_of_asymptotically_log_normal Q P (fun n ω => -L n ω)
    (fun n => (hL_meas n).neg) h_inv v h_weak_neg

/-! ## Le Cam's third lemma -/

/-- **Le Cam's third lemma** (vdV Theorem 6.6).

`P_n ⊲⊳ Q_n`, together with joint weak convergence of `(X_n, L_n)` under `P_n` to the
law `π` on `E × ℝ` (the law of `(X, V)`), yields that `X_n` converges weakly under `Q_n`
to the tilted marginal `Measure.map Prod.fst (π.withDensity (exp ∘ Prod.snd))`.

This formulation takes the sequence-side UI (`h_UI`) and the target-side integrability
(`h_exp_int_π` + `h_exp_int_π_eq_one`) as explicit hypotheses, rather than deriving them
from `hcont`. In the log-normal log-likelihood setting (the main application, Step 5 of
Theorem 7.10), `h_UI` is discharged via `uniform_integrability_exp_L`, and the target-side
facts follow from weak convergence + sequence-side integral normalization. -/
theorem weak_limit_under_Q_of_lecam_third
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (X : ∀ n, Ω n → E) (L : ∀ n, Ω n → ℝ)
    (hX_meas : ∀ n, Measurable (X n)) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (π : Measure (E × ℝ)) [IsProbabilityMeasure π]
    (h_joint_weak :
      WeakConverges (fun n => (P n).map (fun ω => (X n ω, L n ω))) π)
    (h_UI : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε)
    (h_exp_int_π : Integrable (fun p : E × ℝ => Real.exp p.2) π)
    (h_exp_int_π_eq_one : ∫ p, Real.exp p.2 ∂π = 1) :
    WeakConverges (fun n => (Q n).map (X n))
      ((π.withDensity (fun p => ENNReal.ofReal (Real.exp p.2))).map Prod.fst) := by
  intro f
  -- Rewrite RHS (target integral over tilted marginal) as ∫ f(p.1)·exp(p.2) dπ.
  have h_target_rewrite : ∫ x, f x ∂((π.withDensity
        (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2))).map Prod.fst)
      = ∫ p, f p.1 * Real.exp p.2 ∂π := by
    have h_exp_meas_snd : Measurable (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2)) :=
      (Real.continuous_exp.measurable.comp measurable_snd).ennreal_ofReal
    have h_exp_lt_top : ∀ᵐ p ∂π, ENNReal.ofReal (Real.exp p.2) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable
        f.continuous.aestronglyMeasurable]
    rw [integral_withDensity_eq_integral_toReal_smul h_exp_meas_snd h_exp_lt_top
        (fun p => f p.1)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    change (ENNReal.ofReal (Real.exp p.2)).toReal • f p.1 = f p.1 * Real.exp p.2
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
  rw [h_target_rewrite]
  -- Rewrite each LHS term: ∫ f d((Q n).map X_n) = ∫ p, f(p.1)·exp(p.2) d((P n).map (X_n, L_n)).
  have h_seq_rewrite : ∀ n, ∫ x, f x ∂((Q n).map (X n))
      = ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω))) := by
    intro n
    have h_exp_meas_Ln : Measurable (fun ω => ENNReal.ofReal (Real.exp (L n ω))) :=
      (Real.continuous_exp.measurable.comp (hL_meas n)).ennreal_ofReal
    have h_exp_lt_top : ∀ᵐ ω ∂(P n), ENNReal.ofReal (Real.exp (L n ω)) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
      (hX_meas n).prodMk (hL_meas n)
    have h_integrand_meas :
        AEStronglyMeasurable (fun p : E × ℝ => f p.1 * Real.exp p.2)
          ((P n).map (fun ω => (X n ω, L n ω))) :=
      ((f.continuous.comp continuous_fst).mul
        (Real.continuous_exp.comp continuous_snd)).aestronglyMeasurable
    calc ∫ x, f x ∂((Q n).map (X n))
        = ∫ ω, f (X n ω) ∂(Q n) :=
          MeasureTheory.integral_map (hX_meas n).aemeasurable
            f.continuous.aestronglyMeasurable
      _ = ∫ ω, f (X n ω)
            ∂((P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω)))) := by
          rw [← hL_is_log_ratio n]
      _ = ∫ ω, (ENNReal.ofReal (Real.exp (L n ω))).toReal • f (X n ω) ∂(P n) :=
          integral_withDensity_eq_integral_toReal_smul h_exp_meas_Ln h_exp_lt_top
            (fun ω => f (X n ω))
      _ = ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
          change (ENNReal.ofReal (Real.exp (L n ω))).toReal • f (X n ω)
            = f (X n ω) * Real.exp (L n ω)
          rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
      _ = ∫ p, f p.1 * Real.exp p.2
            ∂((P n).map (fun ω => (X n ω, L n ω))) :=
          (MeasureTheory.integral_map h_joint_meas.aemeasurable h_integrand_meas).symm
  simp_rw [h_seq_rewrite]
  -- Residue bound on both sides via BCF truncation + triangle inequality.
  have hfbound : ∀ p : E × ℝ, |f p.1| ≤ ‖f‖ := fun p => f.norm_coe_le_norm _
  have h_exp_nonneg : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos _).le
  -- Generic helper: |∫ f(p.1)·exp(p.2) dμ - ∫ f(p.1)·min(exp(p.2), M) dμ|
  --  ≤ ‖f‖ · ∫ (exp p.2 - min(exp p.2, M)) dμ, for any measure μ on E × ℝ with `exp p.2`
  -- integrable.
  have h_residue_EℝR :
      ∀ (μ : Measure (E × ℝ)) (M : ℝ), 0 ≤ M →
        Integrable (fun p : E × ℝ => Real.exp p.2) μ →
        |∫ p, f p.1 * Real.exp p.2 ∂μ - ∫ p, f p.1 * min (Real.exp p.2) M ∂μ|
          ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
    intro μ M hM h_exp_int
    have h_min_nn : ∀ p : E × ℝ, 0 ≤ min (Real.exp p.2) M := fun p =>
      le_min (h_exp_nonneg _) hM
    have h_min_le : ∀ p : E × ℝ, min (Real.exp p.2) M ≤ Real.exp p.2 :=
      fun p => min_le_left _ _
    have h_min_meas : Measurable (fun p : E × ℝ => min (Real.exp p.2) M) :=
      (Real.continuous_exp.measurable.comp measurable_snd).min measurable_const
    have h_min_int : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) μ := by
      refine h_exp_int.mono' h_min_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Real.norm_eq_abs, abs_of_nonneg (h_min_nn p)]
      exact h_min_le p
    have hf_ae :
        AEStronglyMeasurable (fun p : E × ℝ => f p.1) μ :=
      (f.continuous.comp continuous_fst).aestronglyMeasurable
    have hf_bound_ae : ∀ᵐ p ∂μ, ‖f p.1‖ ≤ ‖f‖ :=
      Filter.Eventually.of_forall (fun p => f.norm_coe_le_norm _)
    have h_fexp_int : Integrable (fun p : E × ℝ => f p.1 * Real.exp p.2) μ :=
      h_exp_int.bdd_mul hf_ae hf_bound_ae
    have h_fmin_int :
        Integrable (fun p : E × ℝ => f p.1 * min (Real.exp p.2) M) μ :=
      h_min_int.bdd_mul hf_ae hf_bound_ae
    rw [← integral_sub h_fexp_int h_fmin_int]
    have h_diff_eq :
        (fun p : E × ℝ => f p.1 * Real.exp p.2 - f p.1 * min (Real.exp p.2) M)
          = fun p => f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) := by
      funext p; ring
    rw [h_diff_eq]
    calc |∫ p, f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ|
        ≤ ∫ p, |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)| ∂μ :=
          abs_integral_le_integral_abs
      _ = ∫ p, |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
          change |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)|
            = |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M)
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (h_min_le p))]
      _ ≤ ∫ p, ‖f‖ * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall
              (fun p => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (h_min_le p))))
            ((h_exp_int.sub h_min_int).const_mul ‖f‖)
            (Filter.Eventually.of_forall (fun p => ?_))
          refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr (h_min_le p))
          exact hfbound p
      _ = ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ :=
          integral_const_mul _ _
  -- Target-side tendsto: as M → ∞, ∫ min(exp p.2, M) dπ → ∫ exp p.2 dπ = 1 (DCT under π).
  have h_target_tendsto : Tendsto
      (fun M : ℕ => ∫ p, min (Real.exp p.2) (M : ℝ) ∂π) atTop (𝓝 1) := by
    have h_lim : ∀ᵐ p ∂π,
        Tendsto (fun M : ℕ => min (Real.exp p.2) (M : ℝ)) atTop (𝓝 (Real.exp p.2)) := by
      refine Filter.Eventually.of_forall (fun p => ?_)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ⌈Real.exp p.2⌉₊] with M hM
      have : Real.exp p.2 ≤ (M : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hM)
      exact (min_eq_left this).symm
    have h_dom : ∀ M : ℕ, ∀ᵐ p ∂π,
        ‖min (Real.exp p.2) (M : ℝ)‖ ≤ Real.exp p.2 := by
      intro M
      refine Filter.Eventually.of_forall (fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) (Nat.cast_nonneg _))]
      exact min_le_left _ _
    have h_meas : ∀ M : ℕ,
        AEStronglyMeasurable (fun p : E × ℝ => min (Real.exp p.2) (M : ℝ)) π :=
      fun M => ((Real.continuous_exp.comp continuous_snd).min
        continuous_const).aestronglyMeasurable
    have h_conv := MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun (M : ℕ) (p : E × ℝ) => min (Real.exp p.2) (M : ℝ))
      (f := fun p : E × ℝ => Real.exp p.2) (bound := fun p : E × ℝ => Real.exp p.2)
      h_meas h_exp_int_π h_dom h_lim
    rw [h_exp_int_π_eq_one] at h_conv
    exact h_conv
  -- Start ε argument.
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C : ℝ := ‖f‖ + 1 with hC_def
  have hC_pos : 0 < C := by positivity
  have hnorm_le_C : ‖f‖ ≤ C := by simp [hC_def]
  have hthresh_pos : 0 < ε / (3 * C) := by positivity
  -- UI threshold on sequence side.
  obtain ⟨M_UI, hM_UI_nonneg, N_UI, hN_UI⟩ :=
    h_UI (ε / (3 * C)) hthresh_pos
  -- Target-side pick M_target so `1 - ε/(3C) < ∫ min(exp, M_target) dπ`.
  have h_ev_target : ∀ᶠ M : ℕ in atTop,
      (1 : ℝ) - ε / (3 * C) < ∫ p, min (Real.exp p.2) (M : ℝ) ∂π := by
    have h_mem : Set.Ioi ((1 : ℝ) - ε / (3 * C)) ∈ 𝓝 (1 : ℝ) :=
      Ioi_mem_nhds (by linarith)
    exact h_target_tendsto h_mem
  obtain ⟨M_target, hM_target⟩ := h_ev_target.exists
  -- Take M := max M_UI (M_target : ℝ).
  set M : ℝ := max M_UI (M_target : ℝ) with hM_def
  have hM_nonneg : 0 ≤ M := le_max_of_le_left hM_UI_nonneg
  have hM_ge_UI : M_UI ≤ M := le_max_left _ _
  have hM_ge_target : (M_target : ℝ) ≤ M := le_max_right _ _
  -- BCF `g_M(p) := f(p.1) · min(exp(p.2), M)`, norm ≤ ‖f‖ · M.
  let g_M : E × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => f p.1 * min (Real.exp p.2) M)
    ((f.continuous.comp continuous_fst).mul
      ((Real.continuous_exp.comp continuous_snd).min continuous_const))
    (‖f‖ * M)
    (fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : 0 ≤ min (Real.exp p.2) M :=
        le_min (h_exp_nonneg _) hM_nonneg
      rw [abs_of_nonneg h2]
      refine mul_le_mul ?_ (min_le_right _ _) h2 (norm_nonneg _)
      exact hfbound p)
  have hg_M_apply : ∀ p, g_M p = f p.1 * min (Real.exp p.2) M := fun _ => rfl
  -- Weak convergence at g_M.
  have h_weak_gM := h_joint_weak g_M
  rw [Metric.tendsto_nhds] at h_weak_gM
  have hε3_pos : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨N_weak, hN_weak⟩ :=
    Filter.eventually_atTop.mp (h_weak_gM (ε / 3) hε3_pos)
  rw [Filter.eventually_atTop]
  refine ⟨max N_UI N_weak, fun n hn => ?_⟩
  have hn_UI : N_UI ≤ n := le_of_max_le_left hn
  have hn_weak : N_weak ≤ n := le_of_max_le_right hn
  -- Sequence-side: `exp` integrable under `(P n).map (X_n, L_n)`.
  have h_exp_int_Pn : Integrable (fun ω => Real.exp (L n ω)) (P n) :=
    exp_L_integrable P Q L hL_meas hL_is_log_ratio n
  have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
    (hX_meas n).prodMk (hL_meas n)
  have h_exp_int_map_n :
      Integrable (fun p : E × ℝ => Real.exp p.2)
        ((P n).map (fun ω => (X n ω, L n ω))) :=
    (MeasureTheory.integrable_map_measure
      (Real.continuous_exp.comp continuous_snd).aestronglyMeasurable
      h_joint_meas.aemeasurable).mpr h_exp_int_Pn
  -- UI bound at enlarged M: monotonicity of min(exp, ·) in M.
  have h_min_mono_M : ∀ ω,
      min (Real.exp (L n ω)) M_UI ≤ min (Real.exp (L n ω)) M :=
    fun ω => min_le_min_left _ hM_ge_UI
  have h_int_trunc_UI : Integrable
      (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI) (P n) := by
    refine h_exp_int_Pn.sub ?_
    refine h_exp_int_Pn.mono'
      ((Real.continuous_exp.measurable.comp (hL_meas n)).min
        measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (le_min (h_exp_nonneg _) hM_UI_nonneg)]
    exact min_le_left _ _
  have h_UI_bound_Pn :
      ∫ ω, (Real.exp (L n ω) - min (Real.exp (L n ω)) M) ∂(P n) ≤ ε / (3 * C) :=
    calc ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
        ≤ ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI ∂(P n) :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall
              (fun ω => sub_nonneg.mpr (min_le_left _ _)))
            h_int_trunc_UI
            (Filter.Eventually.of_forall
              (fun ω => by linarith [h_min_mono_M ω]))
      _ ≤ ε / (3 * C) := hN_UI n hn_UI
  have h_UI_bound_map_n :
      ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
          ∂((P n).map (fun ω => (X n ω, L n ω)))
        ≤ ε / (3 * C) := by
    rw [MeasureTheory.integral_map h_joint_meas.aemeasurable]
    · exact h_UI_bound_Pn
    · exact ((Real.continuous_exp.comp continuous_snd).sub
        ((Real.continuous_exp.comp continuous_snd).min
          continuous_const)).aestronglyMeasurable
  -- Target-side residue bound:
  have h_trunc_int_π : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) π := by
    refine h_exp_int_π.mono'
      ((Real.continuous_exp.comp continuous_snd).min
        continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_nonneg)]
    exact min_le_left _ _
  have h_target_trunc_M_lb :
      (1 : ℝ) - ε / (3 * C) ≤ ∫ p, min (Real.exp p.2) M ∂π := by
    have h_mono :
        ∫ p, min (Real.exp p.2) (M_target : ℝ) ∂π
          ≤ ∫ p, min (Real.exp p.2) M ∂π := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall
          (fun p => le_min (h_exp_nonneg _) (Nat.cast_nonneg _)))
        h_trunc_int_π
        (Filter.Eventually.of_forall (fun p => min_le_min_left _ hM_ge_target))
    linarith [hM_target]
  have h_target_bound_π :
      ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π ≤ ε / (3 * C) := by
    rw [integral_sub h_exp_int_π h_trunc_int_π, h_exp_int_π_eq_one]
    linarith [h_target_trunc_M_lb]
  -- Apply residue bound on both sides.
  have h_res_map_n := h_residue_EℝR ((P n).map (fun ω => (X n ω, L n ω))) M hM_nonneg
    h_exp_int_map_n
  have h_res_π := h_residue_EℝR π M hM_nonneg h_exp_int_π
  -- Triangle inequality.
  rw [Real.dist_eq]
  have h_weak_bound :
      |∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω))) - ∫ p, g_M p ∂π| < ε / 3 := by
    have := hN_weak n hn_weak
    rwa [Real.dist_eq] at this
  have h_res_nonneg : 0 ≤ ‖f‖ := norm_nonneg _
  have h_seq_piece :
      |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
        - ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))| ≤ ε / 3 := by
    have h_gM_eq :
        ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
          = ∫ p, f p.1 * min (Real.exp p.2) M
              ∂((P n).map (fun ω => (X n ω, L n ω))) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
    rw [h_gM_eq]
    calc |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
            - ∫ p, f p.1 * min (Real.exp p.2) M
                ∂((P n).map (fun ω => (X n ω, L n ω)))|
        ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
              ∂((P n).map (fun ω => (X n ω, L n ω))) := h_res_map_n
      _ ≤ ‖f‖ * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_left h_UI_bound_map_n h_res_nonneg
      _ ≤ C * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
      _ = ε / 3 := by field_simp
  have h_target_piece :
      |∫ p, g_M p ∂π - ∫ p, f p.1 * Real.exp p.2 ∂π| ≤ ε / 3 := by
    have h_gM_eq :
        ∫ p, g_M p ∂π = ∫ p, f p.1 * min (Real.exp p.2) M ∂π :=
      integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
    rw [h_gM_eq, abs_sub_comm]
    calc |∫ p, f p.1 * Real.exp p.2 ∂π - ∫ p, f p.1 * min (Real.exp p.2) M ∂π|
        ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π := h_res_π
      _ ≤ ‖f‖ * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_left h_target_bound_π h_res_nonneg
      _ ≤ C * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
      _ = ε / 3 := by field_simp
  set A := ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
  set B := ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
  set D := ∫ p, g_M p ∂π
  set E' := ∫ p, f p.1 * Real.exp p.2 ∂π
  have h_split : A - E' = (A - B) + (B - D) + (D - E') := by ring
  rw [h_split]
  calc |(A - B) + (B - D) + (D - E')|
      ≤ |(A - B) + (B - D)| + |D - E'| := abs_add_le _ _
    _ ≤ |A - B| + |B - D| + |D - E'| := by linarith [abs_add_le (A - B) (B - D)]
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith [h_seq_piece, h_weak_bound, h_target_piece]
    _ = ε := by ring

/-- ENNReal-density form of Le Cam's third lemma (vdV Example 6.7).

For an almost everywhere positive finite density `ρ_n : Ω → ℝ≥0∞`, set
`L_n := log (ρ_n).toReal` and apply the exponential-density form of the
theorem. The joint weak-convergence hypothesis is stated directly for
`(X n ω, Real.log (ρ n ω).toReal)`. -/
theorem weak_limit_under_Q_of_lecam_third_ennreal
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (X : ∀ n, Ω n → E) (ρ : ∀ n, Ω n → ℝ≥0∞)
    (hX_meas : ∀ n, Measurable (X n)) (hρ_meas : ∀ n, Measurable (ρ n))
    (hQ_density : ∀ n, Q n = (P n).withDensity (ρ n))
    (hρ_AE_pos : ∀ n, ∀ᵐ ω ∂(P n), 0 < ρ n ω ∧ ρ n ω < ⊤)
    (π : Measure (E × ℝ)) [IsProbabilityMeasure π]
    (h_joint_weak :
      WeakConverges
        (fun n => (P n).map
          (fun ω => (X n ω, Real.log (ρ n ω).toReal))) π)
    (h_UI : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (Real.log (ρ n ω).toReal)
              - min (Real.exp (Real.log (ρ n ω).toReal)) M ∂(P n) ≤ ε)
    (h_exp_int_π : Integrable (fun p : E × ℝ => Real.exp p.2) π)
    (h_exp_int_π_eq_one : ∫ p, Real.exp p.2 ∂π = 1) :
    WeakConverges (fun n => (Q n).map (X n))
      ((π.withDensity (fun p => ENNReal.ofReal (Real.exp p.2))).map Prod.fst) := by
  set L_n : ∀ n, Ω n → ℝ := fun n ω => Real.log (ρ n ω).toReal with hL_n_def
  have hL_n_meas : ∀ n, Measurable (L_n n) := fun n =>
    ((hρ_meas n).ennreal_toReal).log
  have hρ_eq_exp : ∀ n, ρ n =ᵐ[P n]
      fun ω => ENNReal.ofReal (Real.exp (L_n n ω)) := by
    intro n
    filter_upwards [hρ_AE_pos n] with ω hω
    obtain ⟨hpos, hfin⟩ := hω
    have h_toReal_pos : (0 : ℝ) < (ρ n ω).toReal :=
      ENNReal.toReal_pos hpos.ne' hfin.ne
    rw [hL_n_def]
    rw [Real.exp_log h_toReal_pos]
    exact (ENNReal.ofReal_toReal hfin.ne).symm
  have hQ_via_exp : ∀ n,
      Q n = (P n).withDensity
              (fun ω => ENNReal.ofReal (Real.exp (L_n n ω))) := by
    intro n
    rw [hQ_density]
    exact MeasureTheory.withDensity_congr_ae (hρ_eq_exp n)
  exact weak_limit_under_Q_of_lecam_third
    (Ω := Ω) (E := E) (P := P) (Q := Q) (X := X) (L := L_n)
    hX_meas hL_n_meas hQ_via_exp π h_joint_weak h_UI
    h_exp_int_π h_exp_int_π_eq_one

/-! ## Le Cam variants under asymptotic density comparison

The two lemmas below are asymptotic-footing reformulations of `uniform_integrability_exp_L`
and `weak_limit_under_Q_of_lecam_third`. They replace the **exact** change-of-measure
hypothesis `hL_is_log_ratio` (`Q n = (P n).withDensity (exp ∘ L n)`, which forces absolute
continuity hence common support) by asymptotic data: an integral-comparison bound with
vanishing slack and a mass hypothesis `∫ exp(L n) dP_n → 1`. Their conclusions agree
with the exact-density formulations. -/

/-- **Uniform-integrability of `exp(L n)` from `∫ exp(L n) dP_n → 1`.**

The exact identity `hL_is_log_ratio` is replaced by integrability of
`exp(L n)` and the asymptotic normalization `∫ exp(L n) dP_n → 1`.

The proof follows the Gaussian truncation argument of
`uniform_integrability_exp_L`. The exact term `1 − ∫min` becomes
`(∫ exp(L n) dP_n) − ∫min = (1 + δₙ) − ∫min`. Split ε across the `δₙ` slack and the
truncation gap; `δₙ = o(1)` is absorbable but must be carried explicitly (UI only needs
`≤ ε` eventually). -/
lemma uniform_integrability_exp_L_of_integral_tendsto_one
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    -- measure `P_n.withDensity (exp(L n))` is a finite sub-probability measure (mass ≤ 1).
    (h_exp_int : ∀ n, Integrable (fun ω => Real.exp (L n ω)) (P n))
    -- asymptotic singular-mass control (not common support).
    (h_mass : Tendsto (fun n => ∫ ω, Real.exp (L n ω) ∂(P n)) atTop (𝓝 1))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε := by
  intro ε hε
  -- Step 1: pick a natural M₀ with `∫ min(exp, M₀) dN ≥ 1 - ε/4`.
  have h_gaussian := tendsto_integral_truncExp_gaussianReal v
  have h_ev :
      ∀ᶠ M : ℕ in atTop,
        1 - ε / 4 ≤
          ∫ x, min (Real.exp x) (M : ℝ)
            ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
    have h_mem : Set.Ici (1 - ε / 4) ∈ 𝓝 (1 : ℝ) :=
      Ici_mem_nhds (by linarith)
    exact h_gaussian h_mem
  obtain ⟨M₀, hM₀⟩ := h_ev.exists
  set M : ℝ := (M₀ : ℝ) with hM_def
  have hM_nonneg : 0 ≤ M := Nat.cast_nonneg _
  refine ⟨M, hM_nonneg, ?_⟩
  -- Step 2: for fixed M, get `∫ min(exp(L n), M) dP_n → ∫ min(exp, M) dN`.
  have h_trunc_tendsto :=
    tendsto_integral_truncExp_L P L hL_meas v h_weak M hM_nonneg
  -- Step 3a: pick N₁ so that for n ≥ N₁, `∫ min(exp(L n), M) dP_n ≥ 1 - ε/2`.
  have h_target :
      ∀ᶠ n : ℕ in atTop,
        1 - ε / 2 ≤ ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    have h_mem : Set.Ioi (1 - ε / 2) ∈ 𝓝 (∫ x, min (Real.exp x) M
        ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) := by
      apply Ioi_mem_nhds
      linarith [hM₀]
    filter_upwards [h_trunc_tendsto h_mem] with n hn
    exact le_of_lt (Set.mem_Ioi.mp hn)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h_target
  -- Step 3b: from `h_mass`, pick N₂ so that for n ≥ N₂, `∫ exp(L n) dP_n ≤ 1 + ε/2`.
  have h_mass_ub :
      ∀ᶠ n : ℕ in atTop,
        ∫ ω, Real.exp (L n ω) ∂(P n) ≤ 1 + ε / 2 := by
    have h_mem : Set.Iic (1 + ε / 2) ∈ 𝓝 (1 : ℝ) :=
      Iic_mem_nhds (by linarith)
    filter_upwards [h_mass h_mem] with n hn
    exact Set.mem_Iic.mp hn
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp h_mass_ub
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  -- Step 4: rearrange using `∫ exp(L n) dP_n ≤ 1 + ε/2` and `∫min ≥ 1 - ε/2`.
  have h_exp_int_n := h_exp_int n
  have h_trunc_int : Integrable (fun ω => min (Real.exp (L n ω)) M) (P n) := by
    refine h_exp_int_n.mono' ?_ ?_
    · exact ((Real.continuous_exp.measurable.comp
        (hL_meas n)).min measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact min_le_left _ _
      · exact le_min (Real.exp_pos _).le hM_nonneg
  have h_diff_eq :
      ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
        = (∫ ω, Real.exp (L n ω) ∂(P n))
          - ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    rw [MeasureTheory.integral_sub h_exp_int_n h_trunc_int]
  rw [h_diff_eq]
  linarith [hN₁ n hn₁, hN₂ n hn₂]

/-- **Le Cam's third lemma from an integral-comparison bound.**

Assume the integral-comparison hypothesis `h_integral_comparison`:
for some `ρ → 0` and every bounded continuous `f`,
`|∫ f(X n) dQ_n − ∫ f(X n)·exp(L n) dP_n| ≤ ‖f‖·ρ_n`. The vanishing
slack does not affect the weak limit.

The proof combines bounded-continuous truncation, the residue estimate, the
target-side dominated-convergence argument, and an ε/4 bound for the
integral-comparison error. -/
theorem weak_limit_under_Q_of_lecam_third_of_integral_comparison
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (X : ∀ n, Ω n → E) (L : ∀ n, Ω n → ℝ)
    (hX_meas : ∀ n, Measurable (X n)) (hL_meas : ∀ n, Measurable (L n))
    -- Asymptotic integral comparison without a common-support assumption.
    (h_integral_comparison :
      ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧
        ∀ (f : E →ᵇ ℝ) (n : ℕ),
          |∫ ω, f (X n ω) ∂(Q n)
            - ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)| ≤ ‖f‖ * ρ n)
    (π : Measure (E × ℝ)) [IsProbabilityMeasure π]
    (h_joint_weak :
      WeakConverges (fun n => (P n).map (fun ω => (X n ω, L n ω))) π)
    (h_UI : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε)
    (h_exp_int_π : Integrable (fun p : E × ℝ => Real.exp p.2) π)
    (h_exp_int_π_eq_one : ∫ p, Real.exp p.2 ∂π = 1) :
    WeakConverges (fun n => (Q n).map (X n))
      ((π.withDensity (fun p => ENNReal.ofReal (Real.exp p.2))).map Prod.fst) := by
  intro f
  -- Rewrite RHS (target integral over tilted marginal) as ∫ f(p.1)·exp(p.2) dπ.
  have h_target_rewrite : ∫ x, f x ∂((π.withDensity
        (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2))).map Prod.fst)
      = ∫ p, f p.1 * Real.exp p.2 ∂π := by
    have h_exp_meas_snd : Measurable (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2)) :=
      (Real.continuous_exp.measurable.comp measurable_snd).ennreal_ofReal
    have h_exp_lt_top : ∀ᵐ p ∂π, ENNReal.ofReal (Real.exp p.2) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable
        f.continuous.aestronglyMeasurable]
    rw [integral_withDensity_eq_integral_toReal_smul h_exp_meas_snd h_exp_lt_top
        (fun p => f p.1)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    change (ENNReal.ofReal (Real.exp p.2)).toReal • f p.1 = f p.1 * Real.exp p.2
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
  rw [h_target_rewrite]
  -- Map-integral identities: `bₙ` (under `Q n`) and `aₙ` (under `P n`, tilted).
  have h_bn_map : ∀ n, ∫ x, f x ∂((Q n).map (X n)) = ∫ ω, f (X n ω) ∂(Q n) := fun n =>
    MeasureTheory.integral_map (hX_meas n).aemeasurable f.continuous.aestronglyMeasurable
  have h_an_map : ∀ n,
      ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
        = ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n) := by
    intro n
    have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
      (hX_meas n).prodMk (hL_meas n)
    have h_integrand_meas :
        AEStronglyMeasurable (fun p : E × ℝ => f p.1 * Real.exp p.2)
          ((P n).map (fun ω => (X n ω, L n ω))) :=
      ((f.continuous.comp continuous_fst).mul
        (Real.continuous_exp.comp continuous_snd)).aestronglyMeasurable
    rw [MeasureTheory.integral_map h_joint_meas.aemeasurable h_integrand_meas]
  -- ── Slack data from the integral comparison. ─────────────────────────────────────────
  obtain ⟨ρ, hρ_tendsto, hρ_bound⟩ := h_integral_comparison
  -- Eventual integrability of `exp(L n)` under `P n`, recovered from the comparison applied
  -- to the constant `1` BCF: `|1 - ∫ exp(L n) dP_n| ≤ ‖(1 : E →ᵇ ℝ)‖ · ρ n`, and the RHS → 0.
  have h_eventually_int :
      ∀ᶠ n in atTop, Integrable (fun ω => Real.exp (L n ω)) (P n) := by
    have hg1_bound := hρ_bound (1 : E →ᵇ ℝ)
    -- `∫ (1 : E →ᵇ ℝ)(X n) dQ_n = 1` and `(1 : E →ᵇ ℝ)(X n ω)·exp(L n ω) = exp(L n ω)`.
    have h_one_apply : ∀ n ω, ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) = 1 := by
      intro n ω; rw [BoundedContinuousFunction.coe_one]; rfl
    have hg1_simp : ∀ n,
        |(1 : ℝ) - ∫ ω, Real.exp (L n ω) ∂(P n)| ≤ ‖(1 : E →ᵇ ℝ)‖ * ρ n := by
      intro n
      have hb := hg1_bound n
      have h1 : ∫ ω, ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) ∂(Q n) = 1 := by
        simp only [h_one_apply, integral_const, smul_eq_mul, mul_one, probReal_univ]
      have h2 : (fun ω => ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) * Real.exp (L n ω))
          = fun ω => Real.exp (L n ω) := by
        funext ω; rw [h_one_apply]; ring
      rw [h1, h2] at hb
      exact hb
    -- `‖(1 : E →ᵇ ℝ)‖ · ρ n → 0`, so eventually `< 1`.
    have h_slack_zero : Tendsto (fun n => ‖(1 : E →ᵇ ℝ)‖ * ρ n) atTop (𝓝 0) := by
      have := hρ_tendsto.const_mul ‖(1 : E →ᵇ ℝ)‖
      simpa using this
    have h_ev_lt_one : ∀ᶠ n in atTop, ‖(1 : E →ᵇ ℝ)‖ * ρ n < 1 := by
      have h_mem : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by norm_num)
      filter_upwards [h_slack_zero h_mem] with n hn using Set.mem_Iio.mp hn
    filter_upwards [h_ev_lt_one] with n hn
    by_contra h_not_int
    have h_zero : ∫ ω, Real.exp (L n ω) ∂(P n) = 0 := integral_undef h_not_int
    have hb := hg1_simp n
    rw [h_zero, sub_zero, abs_one] at hb
    linarith
  -- The residue estimate applies after enlarging the threshold so that
  -- `exp(L n)` is integrable under `P n`.
  have h_map_tendsto : Tendsto
      (fun n => ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω))))
      atTop (𝓝 (∫ p, f p.1 * Real.exp p.2 ∂π)) := by
    -- Residue bound on both sides via BCF truncation + triangle inequality.
    have hfbound : ∀ p : E × ℝ, |f p.1| ≤ ‖f‖ := fun p => f.norm_coe_le_norm _
    have h_exp_nonneg : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos _).le
    have h_residue_EℝR :
        ∀ (μ : Measure (E × ℝ)) (M : ℝ), 0 ≤ M →
          Integrable (fun p : E × ℝ => Real.exp p.2) μ →
          |∫ p, f p.1 * Real.exp p.2 ∂μ - ∫ p, f p.1 * min (Real.exp p.2) M ∂μ|
            ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
      intro μ M hM h_exp_int
      have h_min_nn : ∀ p : E × ℝ, 0 ≤ min (Real.exp p.2) M := fun p =>
        le_min (h_exp_nonneg _) hM
      have h_min_le : ∀ p : E × ℝ, min (Real.exp p.2) M ≤ Real.exp p.2 :=
        fun p => min_le_left _ _
      have h_min_meas : Measurable (fun p : E × ℝ => min (Real.exp p.2) M) :=
        (Real.continuous_exp.measurable.comp measurable_snd).min measurable_const
      have h_min_int : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) μ := by
        refine h_exp_int.mono' h_min_meas.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun p => ?_))
        simp only [Real.norm_eq_abs, abs_of_nonneg (h_min_nn p)]
        exact h_min_le p
      have hf_ae :
          AEStronglyMeasurable (fun p : E × ℝ => f p.1) μ :=
        (f.continuous.comp continuous_fst).aestronglyMeasurable
      have hf_bound_ae : ∀ᵐ p ∂μ, ‖f p.1‖ ≤ ‖f‖ :=
        Filter.Eventually.of_forall (fun p => f.norm_coe_le_norm _)
      have h_fexp_int : Integrable (fun p : E × ℝ => f p.1 * Real.exp p.2) μ :=
        h_exp_int.bdd_mul hf_ae hf_bound_ae
      have h_fmin_int :
          Integrable (fun p : E × ℝ => f p.1 * min (Real.exp p.2) M) μ :=
        h_min_int.bdd_mul hf_ae hf_bound_ae
      rw [← integral_sub h_fexp_int h_fmin_int]
      have h_diff_eq :
          (fun p : E × ℝ => f p.1 * Real.exp p.2 - f p.1 * min (Real.exp p.2) M)
            = fun p => f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) := by
        funext p; ring
      rw [h_diff_eq]
      calc |∫ p, f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ|
          ≤ ∫ p, |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)| ∂μ :=
            abs_integral_le_integral_abs
        _ = ∫ p, |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
            change |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)|
              = |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M)
            rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (h_min_le p))]
        _ ≤ ∫ p, ‖f‖ * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall
                (fun p => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (h_min_le p))))
              ((h_exp_int.sub h_min_int).const_mul ‖f‖)
              (Filter.Eventually.of_forall (fun p => ?_))
            refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr (h_min_le p))
            exact hfbound p
        _ = ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ :=
            integral_const_mul _ _
    -- Target-side tendsto: as M → ∞, ∫ min(exp p.2, M) dπ → ∫ exp p.2 dπ = 1 (DCT under π).
    have h_target_tendsto : Tendsto
        (fun M : ℕ => ∫ p, min (Real.exp p.2) (M : ℝ) ∂π) atTop (𝓝 1) := by
      have h_lim : ∀ᵐ p ∂π,
          Tendsto (fun M : ℕ => min (Real.exp p.2) (M : ℝ)) atTop (𝓝 (Real.exp p.2)) := by
        refine Filter.Eventually.of_forall (fun p => ?_)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ⌈Real.exp p.2⌉₊] with M hM
        have : Real.exp p.2 ≤ (M : ℝ) :=
          (Nat.le_ceil _).trans (by exact_mod_cast hM)
        exact (min_eq_left this).symm
      have h_dom : ∀ M : ℕ, ∀ᵐ p ∂π,
          ‖min (Real.exp p.2) (M : ℝ)‖ ≤ Real.exp p.2 := by
        intro M
        refine Filter.Eventually.of_forall (fun p => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) (Nat.cast_nonneg _))]
        exact min_le_left _ _
      have h_meas : ∀ M : ℕ,
          AEStronglyMeasurable (fun p : E × ℝ => min (Real.exp p.2) (M : ℝ)) π :=
        fun M => ((Real.continuous_exp.comp continuous_snd).min
          continuous_const).aestronglyMeasurable
      have h_conv := MeasureTheory.tendsto_integral_of_dominated_convergence
        (F := fun (M : ℕ) (p : E × ℝ) => min (Real.exp p.2) (M : ℝ))
        (f := fun p : E × ℝ => Real.exp p.2) (bound := fun p : E × ℝ => Real.exp p.2)
        h_meas h_exp_int_π h_dom h_lim
      rw [h_exp_int_π_eq_one] at h_conv
      exact h_conv
    -- Start ε argument.
    rw [Metric.tendsto_nhds]
    intro ε hε
    set C : ℝ := ‖f‖ + 1 with hC_def
    have hC_pos : 0 < C := by positivity
    have hnorm_le_C : ‖f‖ ≤ C := by simp [hC_def]
    have hthresh_pos : 0 < ε / (3 * C) := by positivity
    -- UI threshold on sequence side.
    obtain ⟨M_UI, hM_UI_nonneg, N_UI, hN_UI⟩ :=
      h_UI (ε / (3 * C)) hthresh_pos
    -- Target-side pick M_target so `1 - ε/(3C) < ∫ min(exp, M_target) dπ`.
    have h_ev_target : ∀ᶠ M : ℕ in atTop,
        (1 : ℝ) - ε / (3 * C) < ∫ p, min (Real.exp p.2) (M : ℝ) ∂π := by
      have h_mem : Set.Ioi ((1 : ℝ) - ε / (3 * C)) ∈ 𝓝 (1 : ℝ) :=
        Ioi_mem_nhds (by linarith)
      exact h_target_tendsto h_mem
    obtain ⟨M_target, hM_target⟩ := h_ev_target.exists
    -- Take M := max M_UI (M_target : ℝ).
    set M : ℝ := max M_UI (M_target : ℝ) with hM_def
    have hM_nonneg : 0 ≤ M := le_max_of_le_left hM_UI_nonneg
    have hM_ge_UI : M_UI ≤ M := le_max_left _ _
    have hM_ge_target : (M_target : ℝ) ≤ M := le_max_right _ _
    -- BCF `g_M(p) := f(p.1) · min(exp(p.2), M)`, norm ≤ ‖f‖ · M.
    let g_M : E × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p => f p.1 * min (Real.exp p.2) M)
      ((f.continuous.comp continuous_fst).mul
        ((Real.continuous_exp.comp continuous_snd).min continuous_const))
      (‖f‖ * M)
      (fun p => by
        rw [Real.norm_eq_abs, abs_mul]
        have h2 : 0 ≤ min (Real.exp p.2) M :=
          le_min (h_exp_nonneg _) hM_nonneg
        rw [abs_of_nonneg h2]
        refine mul_le_mul ?_ (min_le_right _ _) h2 (norm_nonneg _)
        exact hfbound p)
    have hg_M_apply : ∀ p, g_M p = f p.1 * min (Real.exp p.2) M := fun _ => rfl
    -- Weak convergence at g_M.
    have h_weak_gM := h_joint_weak g_M
    rw [Metric.tendsto_nhds] at h_weak_gM
    have hε3_pos : (0 : ℝ) < ε / 3 := by linarith
    obtain ⟨N_weak, hN_weak⟩ :=
      Filter.eventually_atTop.mp (h_weak_gM (ε / 3) hε3_pos)
    -- Eventual-integrability threshold.
    obtain ⟨N_int, hN_int⟩ := Filter.eventually_atTop.mp h_eventually_int
    rw [Filter.eventually_atTop]
    refine ⟨max (max N_UI N_weak) N_int, fun n hn => ?_⟩
    have hn_UI : N_UI ≤ n := le_of_max_le_left (le_of_max_le_left hn)
    have hn_weak : N_weak ≤ n := le_of_max_le_right (le_of_max_le_left hn)
    have hn_int : N_int ≤ n := le_of_max_le_right hn
    -- Sequence-side: `exp` integrable under `P n` (eventual) and under `(P n).map (X_n, L_n)`.
    have h_exp_int_Pn : Integrable (fun ω => Real.exp (L n ω)) (P n) := hN_int n hn_int
    have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
      (hX_meas n).prodMk (hL_meas n)
    have h_exp_int_map_n :
        Integrable (fun p : E × ℝ => Real.exp p.2)
          ((P n).map (fun ω => (X n ω, L n ω))) :=
      (MeasureTheory.integrable_map_measure
        (Real.continuous_exp.comp continuous_snd).aestronglyMeasurable
        h_joint_meas.aemeasurable).mpr h_exp_int_Pn
    -- UI bound at enlarged M: monotonicity of min(exp, ·) in M.
    have h_min_mono_M : ∀ ω,
        min (Real.exp (L n ω)) M_UI ≤ min (Real.exp (L n ω)) M :=
      fun ω => min_le_min_left _ hM_ge_UI
    have h_int_trunc_UI : Integrable
        (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI) (P n) := by
      refine h_exp_int_Pn.sub ?_
      refine h_exp_int_Pn.mono'
        ((Real.continuous_exp.measurable.comp (hL_meas n)).min
          measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      simp only [Real.norm_eq_abs,
        abs_of_nonneg (le_min (h_exp_nonneg _) hM_UI_nonneg)]
      exact min_le_left _ _
    have h_UI_bound_Pn :
        ∫ ω, (Real.exp (L n ω) - min (Real.exp (L n ω)) M) ∂(P n) ≤ ε / (3 * C) :=
      calc ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
          ≤ ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI ∂(P n) :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall
                (fun ω => sub_nonneg.mpr (min_le_left _ _)))
              h_int_trunc_UI
              (Filter.Eventually.of_forall
                (fun ω => by linarith [h_min_mono_M ω]))
        _ ≤ ε / (3 * C) := hN_UI n hn_UI
    have h_UI_bound_map_n :
        ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
            ∂((P n).map (fun ω => (X n ω, L n ω)))
          ≤ ε / (3 * C) := by
      rw [MeasureTheory.integral_map h_joint_meas.aemeasurable]
      · exact h_UI_bound_Pn
      · exact ((Real.continuous_exp.comp continuous_snd).sub
          ((Real.continuous_exp.comp continuous_snd).min
            continuous_const)).aestronglyMeasurable
    -- Target-side residue bound:
    have h_trunc_int_π : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) π := by
      refine h_exp_int_π.mono'
        ((Real.continuous_exp.comp continuous_snd).min
          continuous_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_nonneg)]
      exact min_le_left _ _
    have h_target_trunc_M_lb :
        (1 : ℝ) - ε / (3 * C) ≤ ∫ p, min (Real.exp p.2) M ∂π := by
      have h_mono :
          ∫ p, min (Real.exp p.2) (M_target : ℝ) ∂π
            ≤ ∫ p, min (Real.exp p.2) M ∂π := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall
            (fun p => le_min (h_exp_nonneg _) (Nat.cast_nonneg _)))
          h_trunc_int_π
          (Filter.Eventually.of_forall (fun p => min_le_min_left _ hM_ge_target))
      linarith [hM_target]
    have h_target_bound_π :
        ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π ≤ ε / (3 * C) := by
      rw [integral_sub h_exp_int_π h_trunc_int_π, h_exp_int_π_eq_one]
      linarith [h_target_trunc_M_lb]
    -- Apply residue bound on both sides.
    have h_res_map_n := h_residue_EℝR ((P n).map (fun ω => (X n ω, L n ω))) M hM_nonneg
      h_exp_int_map_n
    have h_res_π := h_residue_EℝR π M hM_nonneg h_exp_int_π
    -- Triangle inequality.
    rw [Real.dist_eq]
    have h_weak_bound :
        |∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω))) - ∫ p, g_M p ∂π| < ε / 3 := by
      have := hN_weak n hn_weak
      rwa [Real.dist_eq] at this
    have h_res_nonneg : 0 ≤ ‖f‖ := norm_nonneg _
    have h_seq_piece :
        |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
          - ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))| ≤ ε / 3 := by
      have h_gM_eq :
          ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
            = ∫ p, f p.1 * min (Real.exp p.2) M
                ∂((P n).map (fun ω => (X n ω, L n ω))) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
      rw [h_gM_eq]
      calc |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
              - ∫ p, f p.1 * min (Real.exp p.2) M
                  ∂((P n).map (fun ω => (X n ω, L n ω)))|
          ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
                ∂((P n).map (fun ω => (X n ω, L n ω))) := h_res_map_n
        _ ≤ ‖f‖ * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_left h_UI_bound_map_n h_res_nonneg
        _ ≤ C * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
        _ = ε / 3 := by field_simp
    have h_target_piece :
        |∫ p, g_M p ∂π - ∫ p, f p.1 * Real.exp p.2 ∂π| ≤ ε / 3 := by
      have h_gM_eq :
          ∫ p, g_M p ∂π = ∫ p, f p.1 * min (Real.exp p.2) M ∂π :=
        integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
      rw [h_gM_eq, abs_sub_comm]
      calc |∫ p, f p.1 * Real.exp p.2 ∂π - ∫ p, f p.1 * min (Real.exp p.2) M ∂π|
          ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π := h_res_π
        _ ≤ ‖f‖ * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_left h_target_bound_π h_res_nonneg
        _ ≤ C * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
        _ = ε / 3 := by field_simp
    set A := ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
    set B := ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
    set D := ∫ p, g_M p ∂π
    set E' := ∫ p, f p.1 * Real.exp p.2 ∂π
    have h_split : A - E' = (A - B) + (B - D) + (D - E') := by ring
    rw [h_split]
    calc |(A - B) + (B - D) + (D - E')|
        ≤ |(A - B) + (B - D)| + |D - E'| := abs_add_le _ _
      _ ≤ |A - B| + |B - D| + |D - E'| := by linarith [abs_add_le (A - B) (B - D)]
      _ < ε / 3 + ε / 3 + ε / 3 := by linarith [h_seq_piece, h_weak_bound, h_target_piece]
      _ = ε := by ring
  -- ── Bridge `aₙ` (map form → `P n` form) to `bₙ = ∫ f d((Q n).map X)` via the slack. ───
  have h_a_tendsto : Tendsto
      (fun n => ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)) atTop
      (𝓝 (∫ p, f p.1 * Real.exp p.2 ∂π)) :=
    h_map_tendsto.congr h_an_map
  -- Slack `bₙ - aₙ → 0` from `|bₙ - aₙ| ≤ ‖f‖·ρ n` and `‖f‖·ρ n → 0`.
  have h_slack_tendsto : Tendsto
      (fun n => (∫ ω, f (X n ω) ∂(Q n))
        - ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)) atTop (𝓝 0) := by
    have h_norm_zero : Tendsto (fun n => ‖f‖ * ρ n) atTop (𝓝 0) := by
      have := hρ_tendsto.const_mul ‖f‖
      simpa using this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h_norm_zero
    rw [Real.norm_eq_abs]
    exact hρ_bound f n
  -- Conclude: `bₙ = aₙ + (bₙ - aₙ) → target + 0 = target`.
  have h_sum := h_a_tendsto.add h_slack_tendsto
  rw [add_zero] at h_sum
  refine (h_sum.congr (fun n => ?_)).congr (fun n => (h_bn_map n).symm)
  ring

/-! ## Le Cam's first lemma — full four-way equivalence (vdV Lemma 6.4)

We package the four equivalent characterizations of contiguity from van der Vaart
Lemma 6.4. The notion `Contiguous atTop P Q` (`Q ⊲ P`) is the book's statement (i)
in event form; its statistic form is statement (iv). Statements (ii) and (iii)
concern the weak limit points of the likelihood ratios `dPₙ/dQₙ` (under `Qₙ`) and
`dQₙ/dPₙ` (under `Pₙ`).

Throughout, `Measure.rnDeriv (P n) (Q n)` is `dPₙ/dQₙ`, mapped to `ℝ` via `.toReal`
and pushed forward to its law via `.map`.
-/

section LeCamFirstEquivalence

/-- **(i) ⟺ (iv): event form ⟺ statistic form** (vdV Lemma 6.4, equivalence of (i) and
(iv)).

The event-form contiguity `Contiguous atTop P Q` (`Q ⊲ P`: events with vanishing
`P`-probability have vanishing `Q`-probability) is equivalent to the statistic form: for
every sequence of measurable real-valued statistics `T n : Ω n → ℝ` that converges to `0`
in `P`-probability (`∀ ε > 0, (P n) {|T n| ≥ ε} → 0`), it also converges to `0` in
`Q`-probability.

Book reduction: events `Aₙ = {|Tₙ| ≥ ε}` (statistic ⟹ event), and statistics
`Tₙ = 1_{Aₙ}` (event ⟹ statistic). Pure measure theory. -/
theorem contiguous_iff_tendsto_zero_statistics
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n)) :
    Contiguous (ι := ℕ) (Ω := Ω) atTop P Q ↔
      ∀ (T : ∀ n, Ω n → ℝ), (∀ n, Measurable (T n)) →
        (∀ ε : ℝ, 0 < ε →
          Tendsto (fun n => (P n) {ω | ε ≤ |T n ω|}) atTop (𝓝 0)) →
        ∀ ε : ℝ, 0 < ε →
          Tendsto (fun n => (Q n) {ω | ε ≤ |T n ω|}) atTop (𝓝 0) := by
  constructor
  · -- (i) ⟹ (iv): events `Aₙ = {|Tₙ| ≥ ε}`.
    intro hcont T hT_meas hTP ε hε
    refine hcont (fun n => {ω | ε ≤ |T n ω|}) (fun n => ?_) (hTP ε hε)
    exact measurableSet_le measurable_const (hT_meas n).norm
  · -- (iv) ⟹ (i): statistics `Tₙ = 1_{Aₙ}`.
    intro h A hA_meas hP_A
    -- Use `T n = (A n).indicator (fun _ => (1 : ℝ))` and threshold `ε = 1/2`.
    set T : ∀ n, Ω n → ℝ := fun n => (A n).indicator (fun _ => (1 : ℝ)) with hT_def
    have hT_meas : ∀ n, Measurable (T n) := fun n =>
      (measurable_const.indicator (hA_meas n))
    -- `{ω | (1/2 : ℝ) ≤ |T n ω|} = A n`.
    have h_event : ∀ n, {ω | (1 / 2 : ℝ) ≤ |T n ω|} = A n := by
      intro n
      ext ω
      simp only [Set.mem_setOf_eq, hT_def]
      by_cases hω : ω ∈ A n
      · rw [Set.indicator_of_mem hω, abs_one]
        simp only [hω, iff_true]; norm_num
      · rw [Set.indicator_of_notMem hω, abs_zero]
        simp only [hω, iff_false, not_le]; norm_num
    have h_half : (0 : ℝ) < 1 / 2 := by norm_num
    -- Statistic form: `P{|T|≥ε} → 0` for all ε, since `{|T|≥ε} ⊆ A n` and `P(A)→0`.
    have hTP : ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => (P n) {ω | ε ≤ |T n ω|}) atTop (𝓝 0) := by
      intro ε hε
      -- `{ω | ε ≤ |T n ω|} ⊆ A n` for any `ε > 0`.
      have h_sub : ∀ n, {ω | ε ≤ |T n ω|} ⊆ A n := by
        intro n ω hω
        simp only [Set.mem_setOf_eq, hT_def] at hω
        by_contra hωA
        rw [Set.indicator_of_notMem hωA] at hω
        simp only [abs_zero] at hω
        linarith
      -- Squeeze: `0 ≤ P{|T|≥ε} ≤ P(A) → 0` (ENNReal-valued).
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hP_A
        (Eventually.of_forall (fun n => zero_le))
        (Eventually.of_forall (fun n => measure_mono (h_sub n)))
    have hTQ := h (fun n => T n) hT_meas hTP (1 / 2) h_half
    -- Rewrite the `Q`-events back to `A n`.
    have h_eq : (fun n => (Q n) {ω | (1 / 2 : ℝ) ≤ |T n ω|}) = fun n => (Q n) (A n) := by
      funext n; rw [h_event n]
    rwa [h_eq] at hTQ

/-- **(i) ⟹ (ii)**: contiguity forces the weak limit points of `dPₙ/dQₙ` (under `Qₙ`)
to give mass `0` to `0` (vdV Lemma 6.4, (i) ⟹ (ii)).

If `Contiguous atTop P Q` (`Q ⊲ P`) and `U` is a weak limit (along a subsequence `φ`) of
the laws of `(dP_{φk}/dQ_{φk})` under `Q_{φk}`, then `U {x | 0 < x} = 1`.

Book: `gₙ(c) = Qₙ(dPₙ/dQₙ < c) − U(< c)`; portmanteau `liminf gₙ(c) ≥ 0` on the open
set `{· < c}`; a slowly decreasing `εₙ ↓ 0`; contiguity kills `Qₙ(dPₙ/dQₙ < εₙ) → 0`.

The hypothesis `hac : ∀ k, P (φ k) ≪ Q (φ k)` makes the real-valued density
`(dPₙ/dQₙ).toReal` honest (it captures all of `Pₙ`): without it the claim is false (take
`Pₙ ⊥ Qₙ`, then `dPₙ/dQₙ = 0` `Qₙ`-a.e. so `U = δ₀`, yet contiguity `Q ⊲ P` can hold).
This is van der Vaart's implicit likelihood-ratio convention. -/
theorem contiguous_imp_limit_pos
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hcont : Contiguous (ι := ℕ) (Ω := Ω) atTop P Q)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hac : ∀ k, (P (φ k)).AbsolutelyContinuous (Q (φ k)))
    (U : Measure ℝ) [IsProbabilityMeasure U]
    (hU : WeakConverges
      (fun k => (Q (φ k)).map (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal)) U) :
    U {x : ℝ | 0 < x} = 1 := by
  -- Abbreviations: real-valued density `r k`, its law `μ' k` under `Q (φ k)`.
  set r : ∀ k, Ω (φ k) → ℝ := fun k ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal with hr_def
  have hr_meas : ∀ k, Measurable (r k) := fun k =>
    ((P (φ k)).measurable_rnDeriv (Q (φ k))).ennreal_toReal
  have hr_nonneg : ∀ k ω, 0 ≤ r k ω := fun k ω => ENNReal.toReal_nonneg
  -- The pushforward law as a `ProbabilityMeasure`, and `Tendsto` in the weak topology.
  set μ' : ℕ → ProbabilityMeasure ℝ :=
    fun k => ⟨(Q (φ k)).map (r k), by
      have : IsProbabilityMeasure ((Q (φ k)).map (r k)) :=
        Measure.isProbabilityMeasure_map (hr_meas k).aemeasurable
      exact this⟩ with hμ'_def
  set U' : ProbabilityMeasure ℝ := ⟨U, inferInstance⟩ with hU'_def
  have h_tendsto : Tendsto μ' atTop (𝓝 U') :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hU
  -- Measure-level value of `μ' k` on a measurable set: `μ' k s = Q(φk) (r k ⁻¹' s)`.
  have hμ'_coe : ∀ k, ((μ' k : Measure ℝ)) = (Q (φ k)).map (r k) := fun k => rfl
  have hU'_coe : ((U' : Measure ℝ)) = U := rfl
  have hμ'_apply : ∀ k {s : Set ℝ}, MeasurableSet s →
      ((μ' k : Measure ℝ)) s = (Q (φ k)) (r k ⁻¹' s) := by
    intro k s hs
    rw [hμ'_coe k, Measure.map_apply (hr_meas k) hs]
  -- ── Crux pointwise bound: `P(φk){r k < c} ≤ ofReal c` for `c > 0`. ──────────────────────
  have h_crux : ∀ (k : ℕ) (c : ℝ), 0 < c →
      (P (φ k)) {ω | r k ω < c} ≤ ENNReal.ofReal c := by
    intro k c hc
    set ν := Q (φ k) with hν
    set μ := P (φ k) with hμ
    set C : Set (Ω (φ k)) := {ω | r k ω < c} with hC
    have hC_meas : MeasurableSet C :=
      measurableSet_lt (hr_meas k) measurable_const
    -- `μ = ν.withDensity (rnDeriv μ ν)` via absolute continuity.
    have h_wd : ν.withDensity (μ.rnDeriv ν) = μ :=
      Measure.withDensity_rnDeriv_eq μ ν (hac k)
    -- `μ C = ∫⁻ ω in C, rnDeriv μ ν ω ∂ν`.
    have h_μC : μ C = ∫⁻ ω in C, μ.rnDeriv ν ω ∂ν := by
      conv_lhs => rw [← h_wd]
      rw [withDensity_apply _ hC_meas]
    rw [h_μC]
    -- On `C`, `ν`-a.e. `rnDeriv μ ν ω ≤ ofReal c`.
    have h_rn_lt_top : ∀ᵐ ω ∂ν, μ.rnDeriv ν ω < ⊤ := Measure.rnDeriv_lt_top μ ν
    have h_bound_ae : ∀ᵐ ω ∂(ν.restrict C), μ.rnDeriv ν ω ≤ ENNReal.ofReal c := by
      rw [ae_restrict_iff' hC_meas]
      filter_upwards [h_rn_lt_top] with ω hω_lt_top hω_in
      -- `ω ∈ C` means `(rnDeriv μ ν ω).toReal < c`; with finiteness, `rnDeriv < ofReal c`.
      have hω_mem : (μ.rnDeriv ν ω).toReal < c := hω_in
      rw [← ENNReal.ofReal_toReal hω_lt_top.ne]
      exact ENNReal.ofReal_le_ofReal hω_mem.le
    calc ∫⁻ ω in C, μ.rnDeriv ν ω ∂ν
        ≤ ∫⁻ _ in C, ENNReal.ofReal c ∂ν := lintegral_mono_ae h_bound_ae
      _ = ENNReal.ofReal c * ν C := by rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal c * 1 := by
          gcongr; exact prob_le_one
      _ = ENNReal.ofReal c := mul_one _
  -- ── Step A: `U` puts no mass below 0. ───────────────────────────────────────────────────
  -- The open set `{x < 0}` has `μ' k`-mass 0 (densities are `≥ 0`), so by portmanteau
  -- `U {x < 0} ≤ liminf 0 = 0`.
  have h_neg_open : IsOpen {x : ℝ | x < 0} := isOpen_lt continuous_id continuous_const
  have h_below_zero : U {x : ℝ | x < 0} = 0 := by
    -- Portmanteau (Measure/ENNReal form): `U {x<0} ≤ liminf (μ' k {x<0})`.
    have h_le := MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      h_tendsto h_neg_open
    rw [hU'_coe] at h_le
    -- Each `(μ' k : Measure ℝ) {x < 0} = 0` since densities are `≥ 0`.
    have h_each : ∀ k, ((μ' k : Measure ℝ)) {x : ℝ | x < 0} = 0 := by
      intro k
      have h_pre : r k ⁻¹' {x : ℝ | x < 0} = (∅ : Set (Ω (φ k))) := by
        ext ω; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_lt]
        exact hr_nonneg k ω
      rw [hμ'_apply k h_neg_open.measurableSet, h_pre, measure_empty]
    simp only [h_each, Filter.liminf_const] at h_le
    exact le_antisymm h_le (zero_le)
  -- ── Step B: `U {x ≤ 0} = 0` via slow-threshold contiguity. ──────────────────────────────
  have h_at_zero : U {x : ℝ | x ≤ 0} = 0 := by
    by_contra h_ne
    -- `δ := U {x ≤ 0} > 0` (in ℝ≥0∞).
    set δ : ℝ≥0∞ := U {x : ℝ | x ≤ 0} with hδ_def
    have hδ_pos : 0 < δ := pos_iff_ne_zero.mpr h_ne
    have hδ_lt_top : δ < ⊤ := lt_of_le_of_lt prob_le_one ENNReal.one_lt_top
    have hδ2_lt : δ / 2 < δ := ENNReal.half_lt_self hδ_pos.ne' hδ_lt_top.ne
    -- For each `m`, the open set `Gₘ = {x < 1/(m+1)}` contains `{x ≤ 0}`, and portmanteau gives
    -- `δ ≤ U Gₘ ≤ liminf_k μ'ₖ Gₘ`, hence `∀ᶠ k, δ/2 < μ'ₖ Gₘ = Q(φk){r k < 1/(m+1)}`.
    have h_event_each : ∀ m : ℕ, ∀ᶠ k in atTop,
        δ / 2 < (Q (φ k)) {ω | r k ω < 1 / (m + 1 : ℝ)} := by
      intro m
      have hc_pos : (0 : ℝ) < 1 / (m + 1 : ℝ) := by positivity
      set G : Set ℝ := {x : ℝ | x < 1 / (m + 1 : ℝ)} with hG_def
      have hG_open : IsOpen G := isOpen_lt continuous_id continuous_const
      have h_subset : {x : ℝ | x ≤ 0} ⊆ G := by
        intro x hx; simp only [hG_def, Set.mem_setOf_eq]; exact lt_of_le_of_lt hx hc_pos
      have h_portmanteau :=
        MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto h_tendsto hG_open
      rw [hU'_coe] at h_portmanteau
      have h_δ_le : δ ≤ U G := by rw [hδ_def]; exact measure_mono h_subset
      have h_δ_le_liminf : δ ≤ Filter.liminf (fun k => ((μ' k : Measure ℝ)) G) atTop :=
        le_trans h_δ_le h_portmanteau
      have h_lt_liminf : δ / 2 < Filter.liminf (fun k => ((μ' k : Measure ℝ)) G) atTop :=
        lt_of_lt_of_le hδ2_lt h_δ_le_liminf
      have h_ev := Filter.eventually_lt_of_lt_liminf h_lt_liminf
      filter_upwards [h_ev] with k hk
      have h_μ'G : ((μ' k : Measure ℝ)) G = (Q (φ k)) {ω | r k ω < 1 / (m + 1 : ℝ)} := by
        rw [hμ'_apply k hG_open.measurableSet]; rfl
      rwa [h_μ'G] at hk
    -- Extract a strictly increasing threshold-index `N : ℕ → ℕ`.
    choose N₀ hN₀ using fun m => Filter.eventually_atTop.mp (h_event_each m)
    -- Strictly monotone version: `N m := (running max of N₀) + m`.
    set N : ℕ → ℕ := fun m => (Finset.range (m + 1)).sup N₀ + m with hN_def
    have hN_ge : ∀ m, N₀ m ≤ N m := by
      intro m
      have : N₀ m ≤ (Finset.range (m + 1)).sup N₀ :=
        Finset.le_sup (Finset.self_mem_range_succ m)
      simp only [hN_def]; omega
    have hN_strictMono : StrictMono N := by
      intro a b hab
      have hab1 : a + 1 ≤ b + 1 := by omega
      have h_sup_mono : (Finset.range (a + 1)).sup N₀ ≤ (Finset.range (b + 1)).sup N₀ :=
        Finset.sup_mono (Finset.range_mono hab1)
      simp only [hN_def]
      omega
    have hN_ge_self : ∀ m, m ≤ N m := fun m => hN_strictMono.le_apply
    -- The guarantee at the monotone threshold: `∀ k ≥ N m, δ/2 < Q(φk){r k < 1/(m+1)}`.
    have hN_guar : ∀ m, ∀ k, N m ≤ k → δ / 2 < (Q (φ k)) {ω | r k ω < 1 / (m + 1 : ℝ)} :=
      fun m k hk => hN₀ m k (le_trans (hN_ge m) hk)
    -- Slow threshold: `g k = largest m ≤ k with N m ≤ k`; `c k = 1/(g k + 1)`.
    set g : ℕ → ℕ := fun k => Nat.findGreatest (fun m => N m ≤ k) k with hg_def
    set c : ℕ → ℝ := fun k => 1 / (g k + 1 : ℝ) with hc_def
    have hc_pos : ∀ k, 0 < c k := fun k => by simp only [hc_def]; positivity
    -- `g k → ∞`: for any `m`, once `k ≥ N m`, `g k ≥ m`.
    have hg_tendsto : Tendsto g atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro m
      refine ⟨N m, fun k hk => ?_⟩
      have hm_le_k : m ≤ k := le_trans (hN_ge_self m) hk
      exact Nat.le_findGreatest hm_le_k hk
    -- hence `c k → 0`.
    have hc_tendsto : Tendsto c atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => (g k : ℝ) + 1) atTop atTop := by
        have := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hg_tendsto
        exact this.atTop_add tendsto_const_nhds
      simpa [hc_def, one_div] using! h1.inv_tendsto_atTop
    -- For `k` with a witness (i.e. `N 0 ≤ k`), `N (g k) ≤ k`, giving the mass lower bound.
    have h_mass_lb : ∀ k, N 0 ≤ k →
        δ / 2 < (Q (φ k)) {ω | r k ω < c k} := by
      intro k hk
      have h_spec : N (g k) ≤ k :=
        Nat.findGreatest_spec (m := 0) (P := fun m => N m ≤ k) (Nat.zero_le k) hk
      have := hN_guar (g k) k h_spec
      -- `1/(g k + 1) = c k`.
      simpa [hc_def] using this
    -- ── Build the contiguity event family along the full index. ──────────────────────────
    -- `A i := {ω | (dPᵢ/dQᵢ).toReal < c (φ⁻¹ i)}` for `i ∈ range φ`, else `∅`.
    classical
    set A : ∀ i : ℕ, Set (Ω i) := fun i =>
      if h : ∃ k, φ k = i then
        {ω | ((P i).rnDeriv (Q i) ω).toReal < c (Classical.choose h)}
      else ∅ with hA_def
    have hA_meas : ∀ i, MeasurableSet (A i) := by
      intro i
      simp only [hA_def]
      by_cases h : ∃ k, φ k = i
      · rw [dif_pos h]
        exact measurableSet_lt
          (((P i).measurable_rnDeriv (Q i)).ennreal_toReal) measurable_const
      · rw [dif_neg h]; exact MeasurableSet.empty
    -- At `i = φ k`, `A (φ k) = {ω | r k ω < c k}` (uses injectivity of `φ`).
    have hA_at_φ : ∀ k, A (φ k) = {ω | r k ω < c k} := by
      intro k
      have h_ex : ∃ j, φ j = φ k := ⟨k, rfl⟩
      simp only [hA_def, dif_pos h_ex]
      have h_choose : Classical.choose h_ex = k :=
        hφ.injective (Classical.choose_spec h_ex)
      rw [h_choose]
    -- `P i (A i) → 0` over all `i`.
    have hP_tendsto : Tendsto (fun i => (P i) (A i)) atTop (𝓝 0) := by
      -- For `ε > 0`, pick `K` with `c k < ε` for `k ≥ K`; then for `i ≥ φ K`, `P i (A i) ≤ ε`.
      rw [ENNReal.tendsto_atTop_zero]
      intro ε hε
      -- choose real threshold `ε' > 0` with `ofReal ε' ≤ ε`.
      obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ENNReal.ofReal ε' ≤ ε := by
        rcases eq_or_lt_of_le (le_top (a := ε)) with h | h
        · exact ⟨1, one_pos, by rw [h]; exact le_top⟩
        · refine ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h.ne, ?_⟩
          rw [ENNReal.ofReal_toReal h.ne]
      have hc_lt : ∀ᶠ k in atTop, c k < ε' := by
        have := hc_tendsto
        rw [Metric.tendsto_nhds] at this
        filter_upwards [this ε' hε'_pos] with k hk
        rw [Real.dist_eq, sub_zero, abs_of_pos (hc_pos k)] at hk
        exact hk
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hc_lt
      refine ⟨φ K, fun i hi => ?_⟩
      by_cases h_ex : ∃ k, φ k = i
      · obtain ⟨k, hk_eq⟩ := h_ex
        subst hk_eq
        -- `φ K ≤ φ k ⟹ K ≤ k` (φ mono).
        have hKk : K ≤ k := by
          by_contra hlt
          push_neg at hlt
          exact absurd (hφ hlt) (not_lt.mpr hi)
        rw [hA_at_φ k]
        calc (P (φ k)) {ω | r k ω < c k}
            ≤ ENNReal.ofReal (c k) := h_crux k (c k) (hc_pos k)
          _ ≤ ENNReal.ofReal ε' := ENNReal.ofReal_le_ofReal (hK k hKk).le
          _ ≤ ε := hε'_le
      · have hAi : A i = ∅ := by simp only [hA_def, dif_neg h_ex]
        rw [hAi, measure_empty]; exact (zero_le (a := ε))
    -- Contiguity ⟹ `Q i (A i) → 0`.
    have hQ_tendsto : Tendsto (fun i => (Q i) (A i)) atTop (𝓝 0) :=
      hcont A hA_meas hP_tendsto
    -- But along `φ`, `Q (φ k)(A (φ k)) = Q(φk){r k < c k} > δ/2` eventually — contradiction.
    have hQ_sub : Tendsto (fun k => (Q (φ k)) (A (φ k))) atTop (𝓝 0) :=
      hQ_tendsto.comp hφ.tendsto_atTop
    -- Lower bound `δ/2 < Q(φk)(A(φk))` for `k ≥ N 0`.
    have h_contra : ∀ᶠ k in atTop, δ / 2 < (Q (φ k)) (A (φ k)) := by
      refine Filter.eventually_atTop.mpr ⟨N 0, fun k hk => ?_⟩
      rw [hA_at_φ k]
      exact h_mass_lb k hk
    -- Upper bound `Q(φk)(A(φk)) < δ/2` eventually, from convergence to 0.
    have h_ev_lt : ∀ᶠ k in atTop, (Q (φ k)) (A (φ k)) < δ / 2 := by
      have h_mem : Set.Iio (δ / 2) ∈ 𝓝 (0 : ℝ≥0∞) :=
        Iio_mem_nhds (ENNReal.half_pos hδ_pos.ne')
      filter_upwards [hQ_sub h_mem] with k hk using Set.mem_Iio.mp hk
    obtain ⟨k, hk1, hk2⟩ := (h_contra.and h_ev_lt).exists
    exact absurd hk1 (not_lt.mpr hk2.le)
  -- ── Step C: conclude `U {0 < x} = 1`. ───────────────────────────────────────────────────
  have h_compl : {x : ℝ | 0 < x}ᶜ = {x : ℝ | x ≤ 0} := by
    ext x; simp [not_lt]
  have h_meas_pos : MeasurableSet {x : ℝ | (0 : ℝ) < x} :=
    measurableSet_lt measurable_const measurable_id
  have h_compl_zero : U {x : ℝ | 0 < x}ᶜ = 0 := by rw [h_compl]; exact h_at_zero
  have h_eq := prob_compl_eq_one_sub (μ := U) h_meas_pos
  rw [h_compl_zero] at h_eq
  -- `0 = 1 - U {0<x}`, and `U {0<x} ≤ 1`, so `U {0<x} = 1`.
  have h_le_one : U {x : ℝ | 0 < x} ≤ 1 := prob_le_one
  rw [eq_comm, tsub_eq_zero_iff_le] at h_eq
  exact le_antisymm h_le_one h_eq

/-- **Marginal tightness implies joint tightness.** -/
private theorem tight_prod_of_tight_marginals_local
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (S : Set (Measure (X × Y)))
    (hX : IsTightMeasureSet ((fun μ : Measure (X × Y) => μ.map Prod.fst) '' S))
    (hY : IsTightMeasureSet ((fun μ : Measure (X × Y) => μ.map Prod.snd) '' S)) :
    IsTightMeasureSet S := by
  rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hX hY ⊢
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := by
    rw [ENNReal.div_pos_iff]; exact ⟨hε.ne', by norm_num⟩
  obtain ⟨K_X, hK_X_compact, hK_X⟩ := hX (ε / 2) hε2
  obtain ⟨K_Y, hK_Y_compact, hK_Y⟩ := hY (ε / 2) hε2
  refine ⟨K_X ×ˢ K_Y, hK_X_compact.prod hK_Y_compact, ?_⟩
  intro μ hμ
  rw [Set.compl_prod_eq_union]
  calc μ ((K_X)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (K_Y)ᶜ)
      ≤ μ ((K_X)ᶜ ×ˢ Set.univ) + μ (Set.univ ×ˢ (K_Y)ᶜ) := measure_union_le _ _
    _ = (μ.map Prod.fst) (K_X)ᶜ + (μ.map Prod.snd) (K_Y)ᶜ := by
        rw [Set.prod_univ, Set.univ_prod,
            Measure.map_apply measurable_fst hK_X_compact.measurableSet.compl,
            Measure.map_apply measurable_snd hK_Y_compact.measurableSet.compl]
    _ ≤ ε / 2 + ε / 2 :=
        add_le_add (hK_X _ ⟨μ, hμ, rfl⟩) (hK_Y _ ⟨μ, hμ, rfl⟩)
    _ = ε := ENNReal.add_halves _

/-- **A tight sequence of probability measures has a weakly convergent subsequence.** -/
private theorem extract_weak_subseq_local
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (h_tight : IsTightMeasureSet (Set.range μ)) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (μ_lim : Measure E) (_ : IsProbabilityMeasure μ_lim),
      WeakConverges (fun k => μ (φ k)) μ_lim := by
  set P : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, inferInstance⟩ with hP_def
  have h_tight_P :
      IsTightMeasureSet {(↑(ν : ProbabilityMeasure E) : Measure E) | ν ∈ Set.range P} := by
    have : {(↑(ν : ProbabilityMeasure E) : Measure E) | ν ∈ Set.range P} = Set.range μ := by
      ext ρ
      constructor
      · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩; exact ⟨P n, ⟨n, rfl⟩, rfl⟩
    rw [this]; exact h_tight
  have h_compact : IsCompact (closure (Set.range P)) :=
    isCompact_closure_of_isTightMeasureSet h_tight_P
  have h_P_in : ∀ n, P n ∈ closure (Set.range P) := fun n => subset_closure ⟨n, rfl⟩
  have h_seqcompact : IsSeqCompact (closure (Set.range P)) := h_compact.isSeqCompact
  obtain ⟨P_lim, _hP_lim_in, φ, hφ_mono, hφ_conv⟩ := h_seqcompact h_P_in
  refine ⟨φ, hφ_mono, (P_lim : Measure E), inferInstance, ?_⟩
  intro f
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hφ_conv) f

/-- **(iii) ⟹ (i)**: if every subsequential weak limit `V` of `dQₙ/dPₙ` (under `Pₙ`) has
mean `1`, then `Q ⊲ P` (vdV Lemma 6.4, (iii) ⟹ (i)).

Book: to show `Pₙ(Aₙ) → 0 ⟹ Qₙ(Aₙ) → 0`, pass to a subsequence along which
`(dQₙ/dPₙ, 1_{Aₙᶜ}) ⇝ (V, 1)` jointly under `Pₙ` (Prohorov), then portmanteau on the
continuous nonnegative `(v, t) ↦ v·t` gives `liminf Qₙ(Aₙᶜ) ≥ EV = 1`, so `Qₙ(Aₙ) → 0`.

The hypothesis `hac : ∀ n, Q n ≪ P n` makes `(dQₙ/dPₙ).toReal` honest as the `Pₙ`-density
of `Qₙ`, so `Qₙ(B) = ∫_B (dQₙ/dPₙ) dPₙ`; this is van der Vaart's likelihood-ratio
convention. -/
theorem mean_one_imp_contiguous
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hac : ∀ n, (Q n).AbsolutelyContinuous (P n))
    (hV : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (V : Measure ℝ), IsProbabilityMeasure V →
      WeakConverges
        (fun k => (P (φ k)).map (fun ω => ((Q (φ k)).rnDeriv (P (φ k)) ω).toReal)) V →
      ∫ x, x ∂V = 1) :
    Contiguous (ι := ℕ) (Ω := Ω) atTop P Q := by
  -- Real-valued density of `Q n` w.r.t. `P n`, and the change-of-measure identity.
  set q : ∀ n, Ω n → ℝ := fun n ω => ((Q n).rnDeriv (P n) ω).toReal with hq_def
  have hq_meas : ∀ n, Measurable (q n) := fun n =>
    ((Q n).measurable_rnDeriv (P n)).ennreal_toReal
  have hq_nonneg : ∀ n ω, 0 ≤ q n ω := fun n ω => ENNReal.toReal_nonneg
  -- `Q n B = ∫⁻ ω in B, (Q n).rnDeriv (P n) ω ∂(P n)` (change of measure, `Q n ≪ P n`).
  have hQ_change : ∀ n {B : Set (Ω n)}, MeasurableSet B →
      (Q n) B = ∫⁻ ω in B, (Q n).rnDeriv (P n) ω ∂(P n) :=
    fun n {B} hB => (Measure.setLIntegral_rnDeriv' (hac n) hB).symm
  -- `∫⁻ (Q n).rnDeriv (P n) ∂(P n) = 1`.
  have hQ_total : ∀ n, ∫⁻ ω, (Q n).rnDeriv (P n) ω ∂(P n) = 1 := by
    intro n; rw [Measure.lintegral_rnDeriv (hac n)]; simp
  classical
  -- Suppose, for contradiction, that `Q n (A n)` does not tend to 0.
  intro A hA_meas hPA
  by_contra h_not
  -- Extract `δ > 0` and a strictly monotone subsequence with `δ ≤ Q (ψ m) (A (ψ m))`.
  -- Since `Q n (A n) ∈ [0, 1]`, failure of convergence gives a frequently-`≥ δ` event.
  obtain ⟨δ, hδ_pos, hψ_freq⟩ :
      ∃ δ : ℝ≥0∞, 0 < δ ∧ ∃ᶠ n in atTop, δ ≤ (Q n) (A n) := by
    by_contra h_all
    push_neg at h_all
    -- `∀ δ > 0, ∀ᶠ n, Q n (A n) < δ`, i.e. `Q n (A n) → 0`.
    apply h_not
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    rcases eq_or_lt_of_le (le_top (a := ε)) with hε_top | hε_lt
    · exact ⟨0, fun n _ => hε_top ▸ le_top⟩
    · have hε2_pos : (0 : ℝ≥0∞) < ε := hε
      obtain ⟨N, hN⟩ := (h_all ε hε2_pos).exists_forall_of_atTop
      exact ⟨N, fun n hn => (hN n hn).le⟩
  obtain ⟨ψ, hψ_mono, hψ_ge⟩ := extraction_of_frequently_atTop hψ_freq
  -- ── Joint laws of `(q, 1_{Aᶜ})` under `P` along `ψ`. ───────────────────────────────────
  -- Indicator of the complement of the event.
  set s : ∀ n, Ω n → ℝ := fun n => (A n)ᶜ.indicator (fun _ => (1 : ℝ)) with hs_def
  have hs_meas : ∀ n, Measurable (s n) := fun n =>
    (measurable_const.indicator (hA_meas n).compl)
  have hs01 : ∀ n ω, s n ω = 0 ∨ s n ω = 1 := by
    intro n ω; by_cases h : ω ∈ (A n)ᶜ
    · right; simp only [hs_def, Set.indicator_of_mem h]
    · left; simp only [hs_def, Set.indicator_of_notMem h]
  have hs_nonneg : ∀ n ω, 0 ≤ s n ω := by
    intro n ω; rcases hs01 n ω with h | h
    · rw [h]
    · rw [h]; exact zero_le_one

  -- Joint map `ω ↦ (q (ψ m) ω, s (ψ m) ω)` and its pushforward under `P (ψ m)`.
  set pair : ∀ m, Ω (ψ m) → ℝ × ℝ := fun m ω => (q (ψ m) ω, s (ψ m) ω) with hpair_def
  have hpair_meas : ∀ m, Measurable (pair m) := fun m =>
    (hq_meas (ψ m)).prodMk (hs_meas (ψ m))
  set J : ℕ → Measure (ℝ × ℝ) := fun m => (P (ψ m)).map (pair m) with hJ_def
  haveI hJ_prob : ∀ m, IsProbabilityMeasure (J m) := fun m =>
    Measure.isProbabilityMeasure_map (hpair_meas m).aemeasurable
  -- ── Tightness of the joint laws (via tight marginals). ──────────────────────────────────
  -- First marginal: law of `q (ψ m)` under `P (ψ m)`.
  have hcomp_fst : ∀ m, Prod.fst ∘ pair m = q (ψ m) := fun m => by
    funext ω; simp only [hpair_def, Function.comp_apply]
  have hcomp_snd : ∀ m, Prod.snd ∘ pair m = s (ψ m) := fun m => by
    funext ω; simp only [hpair_def, Function.comp_apply]
  have hJ_fst : ∀ m, (J m).map Prod.fst = (P (ψ m)).map (q (ψ m)) := by
    intro m
    rw [hJ_def, Measure.map_map measurable_fst (hpair_meas m), hcomp_fst m]
  have hJ_snd : ∀ m, (J m).map Prod.snd = (P (ψ m)).map (s (ψ m)) := by
    intro m
    rw [hJ_def, Measure.map_map measurable_snd (hpair_meas m), hcomp_snd m]
  -- Tightness of the first marginals via Markov on the uniform first-moment bound.
  have h_tight_fst : IsTightMeasureSet (Set.range (fun m => (J m).map Prod.fst)) := by
    refine MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt ?_
    -- Uniform Markov bound: `⨆ m, ((J m).map fst) {x | r < |x|} ≤ ofReal (1 / r)` for `r > 0`.
    have h_bound : ∀ r : ℝ, 0 < r →
        (⨆ μ' ∈ Set.range (fun m => (J m).map Prod.fst), μ' {x : ℝ | r < ‖x‖})
          ≤ (ENNReal.ofReal r)⁻¹ := by
      intro r hr
      refine iSup₂_le ?_
      rintro μ' ⟨m, rfl⟩
      simp only [hJ_fst m]
      -- Pull back: `{x | r < |x|}` under `q (ψ m)` is `{ω | r < q (ψ m) ω}` (since `q ≥ 0`).
      rw [Measure.map_apply (hq_meas (ψ m))
        (measurableSet_lt measurable_const measurable_norm)]
      have h_sub : (q (ψ m)) ⁻¹' {x : ℝ | r < ‖x‖}
          ⊆ {ω | ENNReal.ofReal r ≤ (Q (ψ m)).rnDeriv (P (ψ m)) ω} := by
        intro ω hω
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Real.norm_eq_abs,
          abs_of_nonneg (hq_nonneg (ψ m) ω)] at hω
        simp only [Set.mem_setOf_eq, hq_def] at hω ⊢
        -- `r < (rnDeriv ω).toReal` with `r > 0` forces `rnDeriv ω ≠ ∞`.
        have h_ne_top : (Q (ψ m)).rnDeriv (P (ψ m)) ω ≠ ∞ := by
          intro h_top; rw [h_top, ENNReal.toReal_top] at hω; linarith
        rw [← ENNReal.ofReal_toReal h_ne_top]
        exact ENNReal.ofReal_le_ofReal hω.le
      calc (P (ψ m)) ((q (ψ m)) ⁻¹' {x : ℝ | r < ‖x‖})
          ≤ (P (ψ m)) {ω | ENNReal.ofReal r ≤ (Q (ψ m)).rnDeriv (P (ψ m)) ω} :=
            measure_mono h_sub
        _ ≤ (∫⁻ ω, (Q (ψ m)).rnDeriv (P (ψ m)) ω ∂(P (ψ m))) / ENNReal.ofReal r :=
            meas_ge_le_lintegral_div ((Q (ψ m)).measurable_rnDeriv (P (ψ m))).aemeasurable
              (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
        _ = (ENNReal.ofReal r)⁻¹ := by rw [hQ_total (ψ m), one_div]
    -- `(ofReal r)⁻¹ → 0`, and the iSup is squeezed below it.
    have h_lim : Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹) atTop (𝓝 0) := by
      have h := tendsto_inv_iff.2 ENNReal.tendsto_ofReal_atTop
      rw [ENNReal.inv_top] at h
      exact h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
      (Filter.Eventually.of_forall (fun _ => zero_le)) ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr using h_bound r hr
  -- Tightness of the second marginals (they live in `[0,1]`, hence in a compact set).
  have h_tight_snd : IsTightMeasureSet (Set.range (fun m => (J m).map Prod.snd)) := by
    refine MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt ?_
    -- For `r ≥ 1`, `{x | r < |x|}` has zero mass (`s ∈ {0,1}`, so `|s| ≤ 1`).
    have h_zero : ∀ r : ℝ, 1 ≤ r →
        (⨆ μ' ∈ Set.range (fun m => (J m).map Prod.snd), μ' {x : ℝ | r < ‖x‖}) = 0 := by
      intro r hr
      refine le_antisymm (iSup₂_le ?_) (zero_le)
      rintro μ' ⟨m, rfl⟩
      simp only [hJ_snd m]
      rw [Measure.map_apply (hs_meas (ψ m))
        (measurableSet_lt measurable_const measurable_norm)]
      have h_empty : (s (ψ m)) ⁻¹' {x : ℝ | r < ‖x‖} = (∅ : Set (Ω (ψ m))) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        rcases hs01 (ψ m) ω with h | h <;> rw [h] <;> simp only [Real.norm_eq_abs] <;>
          [(rw [abs_zero]; linarith); (rw [abs_one]; exact hr)]
      rw [h_empty, measure_empty]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_const_nhds
      (Filter.Eventually.of_forall (fun _ => zero_le)) ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr using (h_zero r hr).le
  -- Joint tightness.
  have h_tight_J : IsTightMeasureSet (Set.range J) := by
    apply tight_prod_of_tight_marginals_local (Set.range J)
    · convert h_tight_fst using 2
      ext ρ; constructor
      · rintro ⟨_, ⟨m, rfl⟩, rfl⟩; exact ⟨m, rfl⟩
      · rintro ⟨m, rfl⟩; exact ⟨J m, ⟨m, rfl⟩, rfl⟩
    · convert h_tight_snd using 2
      ext ρ; constructor
      · rintro ⟨_, ⟨m, rfl⟩, rfl⟩; exact ⟨m, rfl⟩
      · rintro ⟨m, rfl⟩; exact ⟨J m, ⟨m, rfl⟩, rfl⟩
  -- ── Extract a further weakly-convergent subsequence of the joints. ──────────────────────
  obtain ⟨φ, hφ_mono, Jlim, hJlim_prob, hJlim_conv⟩ :=
    extract_weak_subseq_local J h_tight_J
  -- The composite subsequence index into the original `P, Q`.
  set χ : ℕ → ℕ := fun k => ψ (φ k) with hχ_def
  have hχ_mono : StrictMono χ := hψ_mono.comp hφ_mono
  -- ── First marginal weak-limit: feed `hV` to get its mean is 1. ──────────────────────────
  set V : Measure ℝ := Jlim.map Prod.fst with hV_def
  haveI hV_prob : IsProbabilityMeasure V := by
    rw [hV_def]; exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- `(J (φ k)).map fst ⇝ V` (continuous mapping on the joint convergence).
  have hfst_conv : WeakConverges (fun k => (J (φ k)).map Prod.fst) V :=
    hJlim_conv.map continuous_fst measurable_fst
  -- Rewrite the first marginals as the `hV`-shaped sequence (law of `q (χ k)` under `P (χ k)`).
  have hfst_eq : (fun k => (J (φ k)).map Prod.fst)
      = fun k => (P (χ k)).map (fun ω => ((Q (χ k)).rnDeriv (P (χ k)) ω).toReal) := by
    funext k
    rw [hJ_fst (φ k)]
  rw [hfst_eq] at hfst_conv
  have hV_mean : ∫ x, x ∂V = 1 := hV (fun k => χ k) hχ_mono V hV_prob hfst_conv
  -- ── Second marginal weak-limit is `δ₁` (since `1_{Aᶜ} → 1` in `P`-probability). ─────────
  have hP_A_χ : Tendsto (fun k => (P (χ k)) (A (χ k))) atTop (𝓝 0) :=
    hPA.comp hχ_mono.tendsto_atTop
  have hsnd_dirac : WeakConverges (fun k => (P (χ k)).map (s (χ k))) (Measure.dirac 1) := by
    intro g
    -- `∫ g d((P).map s) = g 1 + (g 0 - g 1) · (P (A (χ k))).toReal`.
    have h_int_eq : ∀ k, ∫ x, g x ∂((P (χ k)).map (s (χ k)))
        = g 1 + (g 0 - g 1) * ((P (χ k)) (A (χ k))).toReal := by
      intro k
      rw [MeasureTheory.integral_map (hs_meas (χ k)).aemeasurable
        g.continuous.aestronglyMeasurable]
      -- `g (s ω) = g 1 + (g 0 - g 1) · 1_{A} ω`.
      have h_pt : (fun ω => g (s (χ k) ω))
          = fun ω => g 1 + (g 0 - g 1) * (A (χ k)).indicator (fun _ => (1 : ℝ)) ω := by
        funext ω
        by_cases hω : ω ∈ A (χ k)
        · have hs0 : s (χ k) ω = 0 := by
            have : ω ∉ (A (χ k))ᶜ := fun hc => hc hω
            simp only [hs_def, Set.indicator_of_notMem this]
          rw [hs0, Set.indicator_of_mem hω]
          show g 0 = g 1 + (g 0 - g 1) * 1
          ring
        · have hs1 : s (χ k) ω = 1 := by
            have : ω ∈ (A (χ k))ᶜ := hω
            simp only [hs_def, Set.indicator_of_mem this]
          rw [hs1, Set.indicator_of_notMem hω]
          show g 1 = g 1 + (g 0 - g 1) * 0
          ring
      rw [h_pt]
      rw [MeasureTheory.integral_add (integrable_const _)
        (((integrable_const (1 : ℝ)).indicator (hA_meas (χ k))).const_mul (g 0 - g 1))]
      rw [MeasureTheory.integral_const, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_indicator (hA_meas (χ k))]
      simp only [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def, measure_univ, ENNReal.toReal_one]
      ring
    -- `∫ g d(dirac 1) = g 1`.
    rw [show (∫ x, g x ∂(Measure.dirac (1 : ℝ))) = g 1 from by
      rw [MeasureTheory.integral_dirac]]
    simp_rw [h_int_eq]
    -- The added term tends to `0`.
    have h_tendsto0 : Tendsto (fun k => (g 0 - g 1) * ((P (χ k)) (A (χ k))).toReal)
        atTop (𝓝 0) := by
      have h_toReal : Tendsto (fun k => ((P (χ k)) (A (χ k))).toReal) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal (by simp)).comp hP_A_χ
        simpa using! this
      simpa using h_toReal.const_mul (g 0 - g 1)
    simpa using (tendsto_const_nhds (x := g 1)).add h_tendsto0
  -- Identify `Jlim.map snd = δ₁`.
  have hJlim_snd_eq : Jlim.map Prod.snd = Measure.dirac (1 : ℝ) := by
    have hsnd_conv : WeakConverges (fun k => (J (φ k)).map Prod.snd) (Measure.dirac 1) := by
      have : (fun k => (J (φ k)).map Prod.snd)
          = fun k => (P (χ k)).map (s (χ k)) := by
        funext k; rw [hJ_snd (φ k)]
      rw [this]; exact hsnd_dirac
    exact WeakConverges.snd_eq hJlim_conv hsnd_conv
  -- ── Portmanteau lower bound on the nonnegative continuous `(v, t) ↦ max v 0 * max t 0`. ──
  -- Nonnegative continuous test function on `ℝ × ℝ` agreeing with `v · t` on the support.
  set F : ℝ × ℝ → ℝ := fun p => max p.1 0 * max p.2 0 with hF_def
  have hF_cont : Continuous F :=
    (continuous_fst.max continuous_const).mul (continuous_snd.max continuous_const)
  have hF_nonneg : 0 ≤ F := fun p => mul_nonneg (le_max_right _ _) (le_max_right _ _)
  -- On each joint law, `∫⁻ ofReal (F p) ∂(J m) = Q (ψ m) (A (ψ m))ᶜ`.
  have hF_on_J : ∀ m, ∫⁻ p, ENNReal.ofReal (F p) ∂(J m)
      = (Q (ψ m)) (A (ψ m))ᶜ := by
    intro m
    -- Pull back through the pushforward `pair m`.
    rw [hJ_def, lintegral_map (by
      exact (ENNReal.measurable_ofReal.comp (hF_cont.measurable))) (hpair_meas m)]
    -- `ofReal (F (pair m ω)) = 1_{Aᶜ} ω · rnDeriv ω` `P (ψ m)`-a.e. (rnDeriv finite a.e.).
    have h_int_eq : (fun ω => ENNReal.ofReal (F (pair m ω)))
        =ᵐ[P (ψ m)] fun ω => (A (ψ m))ᶜ.indicator
          (fun ω' => (Q (ψ m)).rnDeriv (P (ψ m)) ω') ω := by
      filter_upwards [Measure.rnDeriv_ne_top (Q (ψ m)) (P (ψ m))] with ω hω_fin
      simp only [hF_def, hpair_def]
      rw [max_eq_left (hq_nonneg (ψ m) ω), max_eq_left (hs_nonneg (ψ m) ω)]
      by_cases hω : ω ∈ (A (ψ m))ᶜ
      · have hs1 : s (ψ m) ω = 1 := by simp only [hs_def, Set.indicator_of_mem hω]
        rw [hs1, Set.indicator_of_mem hω]
        simp only [mul_one, hq_def]
        rw [ENNReal.ofReal_toReal hω_fin]
      · have hs0 : s (ψ m) ω = 0 := by simp only [hs_def, Set.indicator_of_notMem hω]
        rw [hs0, Set.indicator_of_notMem hω]
        simp only [mul_zero, ENNReal.ofReal_zero]
    rw [lintegral_congr_ae h_int_eq, lintegral_indicator (hA_meas (ψ m)).compl,
        ← hQ_change (ψ m) (hA_meas (ψ m)).compl]
  -- `V` is supported on `[0, ∞)` (weak limit of laws of nonnegative `q`).
  have hV_supp : V {x : ℝ | x < 0} = 0 := by
    have h_neg_open : IsOpen {x : ℝ | x < 0} := isOpen_lt continuous_id continuous_const
    -- Bundle the first-marginal laws as probability measures.
    haveI hfst_prob : ∀ k, IsProbabilityMeasure
        ((P (χ k)).map (fun ω => ((Q (χ k)).rnDeriv (P (χ k)) ω).toReal)) :=
      fun k => Measure.isProbabilityMeasure_map (hq_meas (χ k)).aemeasurable
    set PM : ℕ → ProbabilityMeasure ℝ := fun k =>
      ⟨(P (χ k)).map (fun ω => ((Q (χ k)).rnDeriv (P (χ k)) ω).toReal), hfst_prob k⟩ with hPM_def
    have h_tendsto_V : Tendsto PM atTop (𝓝 (⟨V, hV_prob⟩ : ProbabilityMeasure ℝ)) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hfst_conv
    have h_le := MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      h_tendsto_V h_neg_open
    have h_each : ∀ k, ((PM k : Measure ℝ)) {x : ℝ | x < 0} = 0 := by
      intro k
      have hcoe : (PM k : Measure ℝ)
          = (P (χ k)).map (fun ω => ((Q (χ k)).rnDeriv (P (χ k)) ω).toReal) := rfl
      rw [hcoe, Measure.map_apply (hq_meas (χ k)) h_neg_open.measurableSet]
      convert measure_empty (μ := P (χ k))
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hq_nonneg (χ k) ω
    simp only [h_each, Filter.liminf_const] at h_le
    exact le_antisymm h_le (zero_le)
  -- On the limit, `∫⁻ ofReal (F p) ∂Jlim = ∫ x ∂V = 1`.
  have hF_on_Jlim : ∫⁻ p, ENNReal.ofReal (F p) ∂Jlim = 1 := by
    -- `snd = 1` `Jlim`-a.e. (from `Jlim.map snd = dirac 1`).
    have h_snd_ae : ∀ᵐ p ∂Jlim, p.2 = 1 := by
      have h_map_ae : ∀ᵐ y ∂(Jlim.map Prod.snd), y = 1 := by
        rw [hJlim_snd_eq]
        rw [MeasureTheory.ae_dirac_iff
          (show MeasurableSet {y : ℝ | y = 1} from measurableSet_singleton (1 : ℝ))]
      exact (MeasureTheory.ae_map_iff measurable_snd.aemeasurable
        (p := fun y : ℝ => y = 1) (measurableSet_singleton (1 : ℝ))).mp h_map_ae
    -- Replace `F p` by `max p.1 0` `Jlim`-a.e.
    have h_ae_eq : (fun p : ℝ × ℝ => ENNReal.ofReal (F p))
        =ᵐ[Jlim] fun p => ENNReal.ofReal (max p.1 0) := by
      filter_upwards [h_snd_ae] with p hp
      simp only [hF_def, hp]; norm_num
    rw [MeasureTheory.lintegral_congr_ae h_ae_eq]
    -- Push to first marginal `V`.
    have h_map : ∫⁻ p, ENNReal.ofReal (max p.1 0) ∂Jlim
        = ∫⁻ x, ENNReal.ofReal (max x 0) ∂V := by
      rw [hV_def]
      exact (lintegral_map
        (ENNReal.measurable_ofReal.comp (continuous_id.max continuous_const).measurable)
        measurable_fst).symm
    rw [h_map]
    -- `ofReal (max x 0) = ofReal x` pointwise.
    have h_ofReal : (fun x : ℝ => ENNReal.ofReal (max x 0)) = fun x => ENNReal.ofReal x := by
      funext x; rcases le_total 0 x with hx | hx
      · rw [max_eq_left hx]
      · rw [max_eq_right hx, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hx]
    rw [h_ofReal]
    -- `(∫⁻ ofReal x dV).toReal = ∫ x dV = 1`, and `1 ≠ 0` forces the value to be `1`.
    have h_nonneg_ae : 0 ≤ᵐ[V] (fun x : ℝ => x) := by
      rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
      simp only [Pi.zero_apply, not_le]
      exact hV_supp
    have h_bridge := MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nonneg_ae
      (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable
    rw [hV_mean] at h_bridge
    -- `h_bridge : 1 = (∫⁻ x, ofReal x ∂V).toReal`.
    have h_ne_top : (∫⁻ x, ENNReal.ofReal x ∂V) ≠ ⊤ := by
      intro h_top; rw [h_top, ENNReal.toReal_top] at h_bridge; exact one_ne_zero h_bridge
    rw [← ENNReal.ofReal_toReal h_ne_top, ← h_bridge, ENNReal.ofReal_one]
  -- Portmanteau (open-set liminf) for the joint convergence `J (φ k) ⇝ Jlim`.
  set PMJ : ℕ → ProbabilityMeasure (ℝ × ℝ) :=
    fun k => ⟨J (φ k), hJ_prob (φ k)⟩ with hPMJ_def
  set PMlim : ProbabilityMeasure (ℝ × ℝ) := ⟨Jlim, hJlim_prob⟩ with hPMlim_def
  have hPMJ_tendsto : Tendsto PMJ atTop (𝓝 PMlim) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hJlim_conv
  have h_open_liminf : ∀ G : Set (ℝ × ℝ), IsOpen G →
      Jlim G ≤ Filter.liminf (fun k => (J (φ k)) G) atTop := fun G hG =>
    MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto hPMJ_tendsto hG
  -- Apply the nonneg-continuous portmanteau liminf integral bound.
  have h_liminf_int :
      ∫⁻ p, ENNReal.ofReal (F p) ∂Jlim
        ≤ Filter.liminf (fun k => ∫⁻ p, ENNReal.ofReal (F p) ∂(J (φ k))) atTop :=
    MeasureTheory.lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      hF_cont hF_nonneg h_open_liminf
  -- Rewrite both sides: LHS = 1, RHS-integrands = `Q (χ k) (A (χ k))ᶜ`.
  rw [hF_on_Jlim] at h_liminf_int
  have h_rhs_eq : (fun k => ∫⁻ p, ENNReal.ofReal (F p) ∂(J (φ k)))
      = fun k => (Q (χ k)) (A (χ k))ᶜ := by
    funext k; rw [hF_on_J (φ k)]
  rw [h_rhs_eq] at h_liminf_int
  -- `Q (χ k) (A (χ k))ᶜ = 1 - Q (χ k) (A (χ k)) ≤ 1 - δ` eventually (since `δ ≤ Q (χ k) (A (χ k))`).
  have hχ_ge : ∀ k, δ ≤ (Q (χ k)) (A (χ k)) := fun k => hψ_ge (φ k)
  have hcompl_le : ∀ k, (Q (χ k)) (A (χ k))ᶜ ≤ 1 - δ := by
    intro k
    have h_eq : (Q (χ k)) (A (χ k))ᶜ = 1 - (Q (χ k)) (A (χ k)) := by
      rw [measure_compl (hA_meas (χ k)) (measure_ne_top _ _), measure_univ]
    rw [h_eq]; exact tsub_le_tsub_left (hχ_ge k) 1
  -- Hence `liminf ≤ 1 - δ`, contradicting `1 ≤ liminf`.
  have h_liminf_le : Filter.liminf (fun k => (Q (χ k)) (A (χ k))ᶜ) atTop ≤ 1 - δ := by
    calc Filter.liminf (fun k => (Q (χ k)) (A (χ k))ᶜ) atTop
        ≤ Filter.liminf (fun _ : ℕ => (1 : ℝ≥0∞) - δ) atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hcompl_le)
      _ = 1 - δ := Filter.liminf_const _
  have h_one_le : (1 : ℝ≥0∞) ≤ 1 - δ := le_trans h_liminf_int h_liminf_le
  -- `1 ≤ 1 - δ` with `δ > 0` is a contradiction.
  have hδ_le_one : δ ≤ 1 := le_trans (hχ_ge 0) prob_le_one
  have hδ_ne_top : δ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hδ_le_one
  rw [ENNReal.le_sub_iff_add_le_left hδ_ne_top hδ_le_one] at h_one_le
  -- `δ + 1 ≤ 1` contradicts `1 < δ + 1` (since `δ > 0`).
  have h_lt : (1 : ℝ≥0∞) < δ + 1 := by
    rw [add_comm]; exact ENNReal.lt_add_right ENNReal.one_ne_top hδ_pos.ne'
  exact absurd h_one_le (not_le.mpr h_lt)

/-- **Mixture-dominating-measure densities** (foundation for vdV Lemma 6.4, (ii) ⟹ (iii)).

For probability measures `P Q` on `α`, the half-sum `μ = ½P + ½Q` dominates both, and the
real densities `W := (dP/dμ).toReal`, `2 - W = (dQ/dμ).toReal` take values in `[0, 2]`.
This packages the four facts needed by the book proof: absolute continuity of `P` and `Q`
to `μ`, the bound `W ∈ [0, 2]` (`μ`-a.e.), and the complementary identity
`(dQ/dμ).toReal = 2 - (dP/dμ).toReal` (`μ`-a.e.).

The key brick is `Measure.rnDeriv_self` for `μ = ½P + ½Q`: `dμ/dμ = 1` `μ`-a.e., and the
linearity `d(½P+½Q)/dμ = ½ dP/dμ + ½ dQ/dμ`, giving `dP/dμ + dQ/dμ = 2`. -/
private lemma mixture_rnDeriv_facts {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    letI μ := ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • P + ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • Q
    (P.AbsolutelyContinuous μ) ∧ (Q.AbsolutelyContinuous μ) ∧
      IsProbabilityMeasure μ ∧
      (∀ᵐ x ∂μ, (Q.rnDeriv μ x).toReal = 2 - (P.rnDeriv μ x).toReal) ∧
      (∀ᵐ x ∂μ, (P.rnDeriv μ x).toReal ≤ 2) := by
  set c : ℝ≥0∞ := ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) with hc_def
  have hc_ne : c ≠ 0 := by simp [hc_def]
  have hc_ne_top : c ≠ ∞ := by simp [hc_def]
  have hc_eq : c = (2 : ℝ≥0∞)⁻¹ := by simp [hc_def]
  set μ : Measure α := c • P + c • Q with hμ_def
  have hPμ : P.AbsolutelyContinuous μ :=
    (Measure.absolutelyContinuous_smul hc_ne).add_right _
  have hQμ : Q.AbsolutelyContinuous μ :=
    (Measure.absolutelyContinuous_smul hc_ne).add_right' _
  -- `μ` is a probability measure: `μ univ = c·1 + c·1 = 2c = 1`.
  have hμ_prob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    rw [hμ_def]
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    rw [hc_eq, ← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  haveI hcP_fin : IsFiniteMeasure (c • P) := by
    constructor; rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]; exact hc_ne_top.lt_top
  haveI hcQ_fin : IsFiniteMeasure (c • Q) := by
    constructor; rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]; exact hc_ne_top.lt_top
  -- Linearity of the RN derivative: `dμ/dμ = c·dP/dμ + c·dQ/dμ`, and `dμ/dμ = 1` μ-a.e.
  have h_lin : μ.rnDeriv μ =ᵐ[μ] fun x => c * P.rnDeriv μ x + c * Q.rnDeriv μ x := by
    have h1 : (c • P).rnDeriv μ =ᵐ[μ] c • P.rnDeriv μ :=
      Measure.rnDeriv_smul_left_of_ne_top' P μ hc_ne_top
    have h2 : (c • Q).rnDeriv μ =ᵐ[μ] c • Q.rnDeriv μ :=
      Measure.rnDeriv_smul_left_of_ne_top' Q μ hc_ne_top
    have h_add : (c • P + c • Q).rnDeriv μ =ᵐ[μ] (c • P).rnDeriv μ + (c • Q).rnDeriv μ :=
      Measure.rnDeriv_add' (c • P) (c • Q) μ
    filter_upwards [h_add, h1, h2] with x hx hx1 hx2
    rw [hμ_def] at hx ⊢
    rw [hx, Pi.add_apply, hx1, hx2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  have h_self : μ.rnDeriv μ =ᵐ[μ] 1 := μ.rnDeriv_self
  -- Hence `c·(dP/dμ + dQ/dμ) = 1`, i.e. `dP/dμ + dQ/dμ = 2` μ-a.e.
  have h_sum : ∀ᵐ x ∂μ, P.rnDeriv μ x + Q.rnDeriv μ x = 2 := by
    filter_upwards [h_lin, h_self, P.rnDeriv_lt_top μ, Q.rnDeriv_lt_top μ]
      with x hx hx_self hP_top hQ_top
    rw [hx] at hx_self
    simp only [Pi.one_apply] at hx_self
    -- `c·a + c·b = 1` with `c = 2⁻¹`, so `a + b = 2`.
    have hmul : c * (P.rnDeriv μ x + Q.rnDeriv μ x) = 1 := by
      rw [mul_add]; exact hx_self
    have hsum_eq : P.rnDeriv μ x + Q.rnDeriv μ x = c⁻¹ * 1 := by
      rw [← hmul, ← mul_assoc, ENNReal.inv_mul_cancel hc_ne hc_ne_top, one_mul]
    rw [hsum_eq, mul_one, hc_eq, inv_inv]
  refine ⟨hPμ, hQμ, hμ_prob, ?_, ?_⟩
  · -- `(dQ/dμ).toReal = 2 - (dP/dμ).toReal`.
    filter_upwards [h_sum, P.rnDeriv_lt_top μ, Q.rnDeriv_lt_top μ]
      with x hx hP_top hQ_top
    have hQ_eq : Q.rnDeriv μ x = 2 - P.rnDeriv μ x := by
      rw [← hx, ENNReal.add_sub_cancel_left hP_top.ne]
    rw [hQ_eq, ENNReal.toReal_sub_of_le (by rw [← hx]; exact le_add_right le_rfl) (by simp)]
    norm_num
  · -- `(dP/dμ).toReal ≤ 2`.
    filter_upwards [h_sum, P.rnDeriv_lt_top μ] with x hx hP_top
    have hle : P.rnDeriv μ x ≤ 2 := by rw [← hx]; exact le_add_right le_rfl
    calc (P.rnDeriv μ x).toReal ≤ ((2 : ℝ≥0∞)).toReal :=
          ENNReal.toReal_mono (by simp) hle
      _ = 2 := by simp

/-- **Change-of-variable bridge** (foundation for vdV Lemma 6.4, (ii) ⟹ (iii)).

For probability measures `R S` on `α`, set `μ = ½R + ½S` and `W ω = (R.rnDeriv μ ω).toReal`,
the `μ`-density of `R` (taking values in `[0, 2]`, with `(S.rnDeriv μ).toReal = 2 - W`).
Along `R`, the likelihood ratio is `(S.rnDeriv R).toReal = (2 - W)/W`; hence for a bounded
continuous `g`,
`∫ g((S.rnDeriv R ω).toReal) ∂R = ∫ w, (w * g ((2 - w)/w)) ∂(μ.map W)`,
the integrand on the right understood as `0` at `w = 0` (which it is, since the factor `w`
vanishes there). This is the engine for both the `V`-side (`R = P, S = Q`) and the
`U`-side (`R = Q, S = P`) change-of-variables in the book proof.

We require `g` to be honest-bounded and continuous via the bounded-continuous bundle. -/
private lemma cov_ratio_integral {α : Type*} [MeasurableSpace α]
    (R S : Measure α) [IsProbabilityMeasure R] [IsProbabilityMeasure S]
    (g : ℝ →ᵇ ℝ) :
    letI μ := ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • R + ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • S
    ∫ ω, g ((S.rnDeriv R ω).toReal) ∂R
      = ∫ w, (w * g ((2 - w) / w))
          ∂(μ.map (fun ω => (R.rnDeriv μ ω).toReal)) := by
  classical
  set c : ℝ≥0∞ := ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) with hc_def
  set μ : Measure α := c • R + c • S with hμ_def
  -- The packaged mixture facts (apply with `P := R, Q := S`).
  obtain ⟨hRμ, hSμ, hμ_prob, h2W, _hW2⟩ := mixture_rnDeriv_facts R S
  -- `W` is the real `μ`-density of `R`; it is measurable.
  set W : α → ℝ := fun ω => (R.rnDeriv μ ω).toReal with hW_def
  have hW_meas : Measurable W := (R.measurable_rnDeriv μ).ennreal_toReal
  -- The function `Ψ w = w * g ((2 - w)/w)`.
  set Ψ : ℝ → ℝ := fun w => w * g ((2 - w) / w) with hΨ_def
  have hratio_meas : Measurable fun w : ℝ => (2 - w) / w :=
    (measurable_const.sub measurable_id).div measurable_id
  have hΨ_meas : Measurable Ψ :=
    measurable_id.mul (g.continuous.measurable.comp hratio_meas)
  -- ── RHS: push the law `μ.map W` back to `μ`. ──
  have hRHS : ∫ w, Ψ w ∂(μ.map W) = ∫ ω, Ψ (W ω) ∂μ := by
    rw [MeasureTheory.integral_map hW_meas.aemeasurable hΨ_meas.aestronglyMeasurable]
  -- ── LHS: change of measure `∫ · ∂R = ∫ W · · ∂μ`. ──
  have hLHS : ∫ ω, g ((S.rnDeriv R ω).toReal) ∂R
      = ∫ ω, W ω * g ((S.rnDeriv R ω).toReal) ∂μ := by
    rw [← integral_toReal_rnDeriv_mul hRμ (f := fun ω => g ((S.rnDeriv R ω).toReal))]
  -- ── R-a.e. chain rule: `(dS/dR).toReal = (2 - W)/W`. ──
  -- `W > 0` `R`-a.e. and the ennreal chain rule `(dS/dR)·(dR/dμ) = dS/dμ` `R`-a.e.
  have hW_pos_R : ∀ᵐ ω ∂R, 0 < W ω := by
    filter_upwards [Measure.rnDeriv_pos hRμ, hRμ.ae_le (R.rnDeriv_lt_top μ)]
      with ω hpos hlt
    simpa [hW_def] using! ENNReal.toReal_pos hpos.ne' hlt.ne
  have h2W_R : ∀ᵐ ω ∂R, (S.rnDeriv μ ω).toReal = 2 - W ω := hRμ.ae_le h2W
  have h_chain_ennR : S.rnDeriv R * R.rnDeriv μ =ᵐ[R] S.rnDeriv μ :=
    Measure.rnDeriv_mul_rnDeriv' hRμ
  have h_ratio_R : ∀ᵐ ω ∂R, (S.rnDeriv R ω).toReal = (2 - W ω) / W ω := by
    filter_upwards [hW_pos_R, h2W_R, h_chain_ennR, S.rnDeriv_lt_top R,
      hRμ.ae_le (R.rnDeriv_lt_top μ)] with ω hWpos h2 hchain hSR_lt hR_lt
    -- toReal of the ennreal chain rule: `(dS/dR).toReal * W ω = (dS/dμ).toReal = 2 - W ω`.
    have hmul : (S.rnDeriv R ω).toReal * W ω = 2 - W ω := by
      have hc := congrArg ENNReal.toReal hchain
      simp only [Pi.mul_apply, ENNReal.toReal_mul] at hc
      change (S.rnDeriv R ω).toReal * (R.rnDeriv μ ω).toReal = 2 - W ω
      rw [hc, h2]
    -- divide by `W ω > 0`.
    rw [eq_div_iff hWpos.ne', hmul]
  -- Transfer to `μ`-a.e. on `{W ≠ 0}`.
  have h_ratio_μ : ∀ᵐ ω ∂μ, R.rnDeriv μ ω ≠ 0 →
      (S.rnDeriv R ω).toReal = (2 - W ω) / W ω :=
    Measure.ae_rnDeriv_ne_zero_imp_of_ae (μ := R) (ν := μ) h_ratio_R
  -- ── Integrands agree `μ`-a.e. ──
  have h_integrand : (fun ω => W ω * g ((S.rnDeriv R ω).toReal)) =ᵐ[μ] fun ω => Ψ (W ω) := by
    filter_upwards [h_ratio_μ] with ω hω
    by_cases hW0 : W ω = 0
    · simp [hΨ_def, hW0]
    · have hne : R.rnDeriv μ ω ≠ 0 := by
        intro h; apply hW0; simp [hW_def, h]
      rw [hΨ_def]
      simp only []
      rw [hω hne]
  calc ∫ ω, g ((S.rnDeriv R ω).toReal) ∂R
      = ∫ ω, W ω * g ((S.rnDeriv R ω).toReal) ∂μ := hLHS
    _ = ∫ ω, Ψ (W ω) ∂μ := integral_congr_ae h_integrand
    _ = ∫ w, Ψ w ∂(μ.map W) := hRHS.symm

/-- **(ii) ⟹ (iii)** (vdV Lemma 6.4, (ii) ⟹ (iii)).

If every subsequential weak limit `U` of `dPₙ/dQₙ` (under `Qₙ`) gives mass `0` to `0`,
then every subsequential weak limit `V` of `dQₙ/dPₙ` (under `Pₙ`) has mean `1`.

Book proof: dominate `Pₙ, Qₙ` by `μₙ = ½(Pₙ + Qₙ)`; the density `Wₙ = (dPₙ/dμₙ).toReal`
takes values in `[0, 2]`, with `(dQₙ/dμₙ).toReal = 2 − Wₙ`. Along the given subsequence
`φ`, extract (Prohorov, twice) a sub-subsequence `χ = φ ∘ ρ` along which the law of
`dPₙ/dQₙ` under `Qₙ` weakly converges to some `U` (Markov-tight) **and** the law `LWₙ` of
`Wₙ` under `μₙ` weakly converges to `LW` (compact-support tight). The change-of-variables
bridge `cov_ratio_integral` (with `g(w) = w·f((2−w)/w)`) turns `dPₙ/dQₙ`- and
`dQₙ/dPₙ`-integrals into `LWₙ`-integrals of explicit bounded continuous test functions:
- `EV = ∫ (2−w) dLW = 2 − ∫ w dLW = 1` (Fact C: `∫ w dLW = 1` from `EWₙ = 1`), using
- `LW{0} = 0` (Fact B: `U{0} = 2·LW{0}` and `U{0} = 0` from (ii)).
The monotone/antitone Bochner convergence theorems supply the truncation limits. -/
theorem limit_pos_imp_mean_one
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hU : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (U : Measure ℝ), IsProbabilityMeasure U →
      WeakConverges
        (fun k => (Q (φ k)).map (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal)) U →
      U {x : ℝ | 0 < x} = 1)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (V : Measure ℝ) [IsProbabilityMeasure V]
    (hVconv : WeakConverges
      (fun k => (P (φ k)).map (fun ω => ((Q (φ k)).rnDeriv (P (φ k)) ω).toReal)) V) :
    ∫ x, x ∂V = 1 := by
  classical
  -- ══ Setup along the given subsequence `φ`. ══
  -- Mixture `μ k = ½ P(φk) + ½ Q(φk)`, real density `W k = (dP(φk)/dμk).toReal ∈ [0,2]`.
  set μ : ∀ k, Measure (Ω (φ k)) := fun k =>
    ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • P (φ k) + ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • Q (φ k) with hμ_def
  set W : ∀ k, Ω (φ k) → ℝ := fun k ω => ((P (φ k)).rnDeriv (μ k) ω).toReal with hW_def
  have hW_meas : ∀ k, Measurable (W k) := fun k =>
    ((P (φ k)).measurable_rnDeriv (μ k)).ennreal_toReal
  -- Mixture facts for each `k`.
  have hmix : ∀ k, (P (φ k)).AbsolutelyContinuous (μ k) ∧
      (Q (φ k)).AbsolutelyContinuous (μ k) ∧ IsProbabilityMeasure (μ k) ∧
      (∀ᵐ x ∂(μ k), ((Q (φ k)).rnDeriv (μ k) x).toReal = 2 - W k x) ∧
      (∀ᵐ x ∂(μ k), W k x ≤ 2) := fun k => mixture_rnDeriv_facts (P (φ k)) (Q (φ k))
  have hμ_prob : ∀ k, IsProbabilityMeasure (μ k) := fun k => (hmix k).2.2.1
  have hPμ : ∀ k, (P (φ k)).AbsolutelyContinuous (μ k) := fun k => (hmix k).1
  have hQμ : ∀ k, (Q (φ k)).AbsolutelyContinuous (μ k) := fun k => (hmix k).2.1
  have hW_le2 : ∀ k, ∀ᵐ x ∂(μ k), W k x ≤ 2 := fun k => (hmix k).2.2.2.2
  have hW_nonneg : ∀ k ω, 0 ≤ W k ω := fun k ω => ENNReal.toReal_nonneg
  -- Law of `W k` under `μ k`, a probability measure on `ℝ` supported in `[0,2]`.
  set LW : ℕ → Measure ℝ := fun k => (μ k).map (W k) with hLW_def
  haveI hLW_prob : ∀ k, IsProbabilityMeasure (LW k) := fun k => by
    haveI := hμ_prob k
    exact Measure.isProbabilityMeasure_map (hW_meas k).aemeasurable
  -- `LW k` is supported in `[0,2]`.
  have hLW_supp : ∀ k, (LW k) {x : ℝ | x < 0 ∨ 2 < x} = 0 := by
    intro k
    haveI := hμ_prob k
    have hSmeas : MeasurableSet {x : ℝ | x < 0 ∨ 2 < x} :=
      (measurableSet_lt measurable_id measurable_const).union
        (measurableSet_lt measurable_const measurable_id)
    rw [hLW_def, Measure.map_apply (hW_meas k) hSmeas]
    have : (∀ᵐ ω ∂(μ k), ω ∉ W k ⁻¹' {x : ℝ | x < 0 ∨ 2 < x}) := by
      filter_upwards [hW_le2 k] with ω hω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, not_or, not_lt]
      exact ⟨hW_nonneg k ω, hω⟩
    rw [ae_iff] at this
    simpa only [not_not] using! this
  -- ══ Extraction 1: weak limit `U` of `dP/dQ`-laws under `Q` (Markov-tight). ══
  set LdPdQ : ℕ → Measure ℝ :=
    fun k => (Q (φ k)).map (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal) with hLdPdQ_def
  have hdPdQ_meas : ∀ k, Measurable (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal) :=
    fun k => ((P (φ k)).measurable_rnDeriv (Q (φ k))).ennreal_toReal
  haveI hLdPdQ_prob : ∀ k, IsProbabilityMeasure (LdPdQ k) := fun k =>
    Measure.isProbabilityMeasure_map (hdPdQ_meas k).aemeasurable
  -- `∫⁻ dP/dQ dQ ≤ 1` (it is `P_a(univ) ≤ 1`).
  have hdPdQ_total : ∀ k, ∫⁻ ω, (P (φ k)).rnDeriv (Q (φ k)) ω ∂(Q (φ k)) ≤ 1 := by
    intro k
    calc ∫⁻ ω, (P (φ k)).rnDeriv (Q (φ k)) ω ∂(Q (φ k))
        ≤ (P (φ k)) Set.univ := Measure.lintegral_rnDeriv_le
      _ = 1 := by simp
  have h_tight_LdPdQ : IsTightMeasureSet (Set.range LdPdQ) := by
    refine MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt ?_
    have h_bound : ∀ r : ℝ, 0 < r →
        (⨆ μ' ∈ Set.range LdPdQ, μ' {x : ℝ | r < ‖x‖}) ≤ (ENNReal.ofReal r)⁻¹ := by
      intro r hr
      refine iSup₂_le ?_
      rintro μ' ⟨k, rfl⟩
      rw [hLdPdQ_def, Measure.map_apply (hdPdQ_meas k)
        (measurableSet_lt measurable_const measurable_norm)]
      have h_sub : (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal) ⁻¹' {x : ℝ | r < ‖x‖}
          ⊆ {ω | ENNReal.ofReal r ≤ (P (φ k)).rnDeriv (Q (φ k)) ω} := by
        intro ω hω
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg] at hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        have h_ne_top : (P (φ k)).rnDeriv (Q (φ k)) ω ≠ ∞ := by
          intro h_top; rw [h_top, ENNReal.toReal_top] at hω; linarith
        rw [← ENNReal.ofReal_toReal h_ne_top]
        exact ENNReal.ofReal_le_ofReal hω.le
      calc (Q (φ k)) ((fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal) ⁻¹' {x : ℝ | r < ‖x‖})
          ≤ (Q (φ k)) {ω | ENNReal.ofReal r ≤ (P (φ k)).rnDeriv (Q (φ k)) ω} :=
            measure_mono h_sub
        _ ≤ (∫⁻ ω, (P (φ k)).rnDeriv (Q (φ k)) ω ∂(Q (φ k))) / ENNReal.ofReal r :=
            meas_ge_le_lintegral_div ((P (φ k)).measurable_rnDeriv (Q (φ k))).aemeasurable
              (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
        _ ≤ (1 : ℝ≥0∞) / ENNReal.ofReal r :=
            ENNReal.div_le_div_right (hdPdQ_total k) _
        _ = (ENNReal.ofReal r)⁻¹ := by rw [one_div]
    have h_lim : Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹) atTop (𝓝 0) := by
      have h := tendsto_inv_iff.2 ENNReal.tendsto_ofReal_atTop
      rw [ENNReal.inv_top] at h
      exact h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
      (Filter.Eventually.of_forall (fun _ => zero_le)) ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr using h_bound r hr
  obtain ⟨σ₁, hσ₁_mono, U, hU_prob, hU_conv⟩ := extract_weak_subseq_local LdPdQ h_tight_LdPdQ
  -- ══ Extraction 2: weak limit `LW_lim` of the bounded `LW ∘ σ₁` (compact support tight). ══
  haveI hLWσ₁_prob : ∀ k, IsProbabilityMeasure ((LW ∘ σ₁) k) := fun k => hLW_prob (σ₁ k)
  have h_tight_LW : IsTightMeasureSet (Set.range (LW ∘ σ₁)) := by
    refine MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt ?_
    -- For `r ≥ 2`, `{|x| > r}` has zero `LW`-mass (support ⊆ [0,2]).
    have h_zero : ∀ r : ℝ, 2 ≤ r →
        (⨆ μ' ∈ Set.range (LW ∘ σ₁), μ' {x : ℝ | r < ‖x‖}) = 0 := by
      intro r hr
      refine le_antisymm (iSup₂_le ?_) (zero_le)
      rintro μ' ⟨k, rfl⟩
      refine le_of_eq ?_
      refine measure_mono_null ?_ (hLW_supp (σ₁ k))
      intro x hx
      simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at hx ⊢
      rcases lt_or_ge x 0 with hx0 | hx0
      · left; rw [abs_of_neg hx0] at hx; linarith
      · right; rw [abs_of_nonneg hx0] at hx; linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_const_nhds
      (Filter.Eventually.of_forall (fun _ => zero_le)) ?_
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr using (h_zero r hr).le
  obtain ⟨σ₂, hσ₂_mono, LW_lim, hLW_lim_prob, hLW_lim_conv⟩ :=
    extract_weak_subseq_local (LW ∘ σ₁) h_tight_LW
  -- ══ Combined subsequence. ══
  set ρ : ℕ → ℕ := σ₁ ∘ σ₂ with hρ_def
  have hρ_mono : StrictMono ρ := hσ₁_mono.comp hσ₂_mono
  set χ : ℕ → ℕ := φ ∘ ρ with hχ_def
  have hχ_mono : StrictMono χ := hφ.comp hρ_mono
  -- `LW (ρ ·) ⇝ LW_lim`.
  have hLW_conv : WeakConverges (fun j => LW (ρ j)) LW_lim := by
    intro f
    have := hLW_lim_conv f
    simpa only [Function.comp_apply, hρ_def] using this
  -- `LdPdQ (ρ ·) ⇝ U` (subsequence of the `σ₁`-convergence).
  have hU_conv' : WeakConverges (fun j => LdPdQ (ρ j)) U := by
    intro f
    have := (hU_conv f).comp hσ₂_mono.tendsto_atTop
    simpa only [Function.comp_apply, hρ_def] using! this
  -- `hU` applies along `χ = φ ∘ ρ`: `U {0 < x} = 1`.
  have hU_pos : U {x : ℝ | 0 < x} = 1 := by
    refine hU χ hχ_mono U hU_prob ?_
    intro f
    have := hU_conv' f
    simpa only [hLdPdQ_def, hχ_def, Function.comp_apply] using! this
  -- `V`-law convergence along `ρ` (subsequence of the given `hVconv`).
  set LdQdP : ℕ → Measure ℝ :=
    fun k => (P (φ k)).map (fun ω => ((Q (φ k)).rnDeriv (P (φ k)) ω).toReal) with hLdQdP_def
  have hdQdP_meas : ∀ k, Measurable (fun ω => ((Q (φ k)).rnDeriv (P (φ k)) ω).toReal) :=
    fun k => ((Q (φ k)).measurable_rnDeriv (P (φ k))).ennreal_toReal
  haveI hLdQdP_prob : ∀ k, IsProbabilityMeasure (LdQdP k) := fun k =>
    Measure.isProbabilityMeasure_map (hdQdP_meas k).aemeasurable
  have hV_conv : WeakConverges (fun j => LdQdP (ρ j)) V := by
    intro f; exact (hVconv f).comp hρ_mono.tendsto_atTop
  -- ── `LW_lim` is supported in `[0,2]`; `V` is supported in `[0,∞)`. ──
  have hLW_lim_supp : LW_lim {x : ℝ | x < 0 ∨ 2 < x} = 0 := by
    have hSopen : IsOpen {x : ℝ | x < 0 ∨ 2 < x} :=
      (isOpen_lt continuous_id continuous_const).union (isOpen_lt continuous_const continuous_id)
    set PMW : ℕ → ProbabilityMeasure ℝ := fun j => ⟨LW (ρ j), hLW_prob (ρ j)⟩ with hPMW_def
    have h_tend : Tendsto PMW atTop (𝓝 (⟨LW_lim, hLW_lim_prob⟩ : ProbabilityMeasure ℝ)) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hLW_conv
    have h_le := MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto h_tend hSopen
    have h_each : ∀ j, ((PMW j : Measure ℝ)) {x : ℝ | x < 0 ∨ 2 < x} = 0 := fun j => hLW_supp (ρ j)
    simp only [h_each, Filter.liminf_const] at h_le
    exact le_antisymm h_le (zero_le)
  have hV_supp : V {x : ℝ | x < 0} = 0 := by
    have h_neg_open : IsOpen {x : ℝ | x < 0} := isOpen_lt continuous_id continuous_const
    set PMV : ℕ → ProbabilityMeasure ℝ := fun j => ⟨LdQdP (ρ j), hLdQdP_prob (ρ j)⟩ with hPMV_def
    have h_tend : Tendsto PMV atTop (𝓝 (⟨V, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hV_conv
    have h_le := MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      h_tend h_neg_open
    have h_each : ∀ j, ((PMV j : Measure ℝ)) {x : ℝ | x < 0} = 0 := by
      intro j
      change (LdQdP (ρ j)) {x : ℝ | x < 0} = 0
      rw [hLdQdP_def, Measure.map_apply (hdQdP_meas (ρ j)) h_neg_open.measurableSet]
      have : (fun ω => ((Q (φ (ρ j))).rnDeriv (P (φ (ρ j))) ω).toReal) ⁻¹' {x : ℝ | x < 0}
          = (∅ : Set (Ω (φ (ρ j)))) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact ENNReal.toReal_nonneg
      rw [this, measure_empty]
    simp only [h_each, Filter.liminf_const] at h_le
    exact le_antisymm h_le (zero_le)
  -- ── Bounded-continuous clamp `cl w = min (max w 0) 2 ∈ [0,2]`, equal to `id` on `[0,2]`. ──
  set clampBdd : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun w => min (max w 0) 2)
    ((continuous_id.max continuous_const).min continuous_const) 2
    (fun w => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have : (0 : ℝ) ≤ min (max w 0) 2 := le_min (le_max_right _ _) (by norm_num)
        linarith
      · exact min_le_right _ _) with hclamp_def
  have hclamp_apply : ∀ w, clampBdd w = min (max w 0) 2 := fun _ => rfl
  -- On `[0,2]`, `clampBdd = id`.
  have hclamp_id : ∀ w : ℝ, 0 ≤ w → w ≤ 2 → clampBdd w = w := by
    intro w hw0 hw2
    rw [hclamp_apply, max_eq_left hw0, min_eq_left hw2]
  -- ── Fact C: `∫ w ∂LW_lim = 1`. ──
  have hFactC : ∫ w, w ∂LW_lim = 1 := by
    -- Replace `id` by `clampBdd` under `LW_lim` (supported in `[0,2]`).
    have hC_lim : ∫ w, w ∂LW_lim = ∫ w, clampBdd w ∂LW_lim := by
      refine integral_congr_ae ?_
      have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
        rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
      filter_upwards [h_compl] with w hw
      simp only [not_or, not_lt] at hw
      exact (hclamp_id w hw.1 hw.2).symm
    -- Each `∫ clampBdd ∂LW (ρ j) = 1` exactly.
    have hC_each : ∀ j, ∫ w, clampBdd w ∂(LW (ρ j)) = 1 := by
      intro j
      haveI := hμ_prob (ρ j)
      -- Push to `μ (ρ j)` via `integral_map`, then `clampBdd (W) = W` `μ`-a.e.
      rw [hLW_def, MeasureTheory.integral_map (hW_meas (ρ j)).aemeasurable
        clampBdd.continuous.aestronglyMeasurable]
      have h_clW : (fun ω => clampBdd (W (ρ j) ω)) =ᵐ[μ (ρ j)] fun ω => W (ρ j) ω := by
        filter_upwards [hW_le2 (ρ j)] with ω hω
        exact hclamp_id (W (ρ j) ω) (hW_nonneg (ρ j) ω) hω
      rw [integral_congr_ae h_clW]
      -- `∫ W ∂μ = ∫ (dP/dμ).toReal ∂μ = P(univ) = 1`.
      have : ∫ ω, W (ρ j) ω ∂(μ (ρ j)) = ∫ ω, (1 : ℝ) ∂(P (φ (ρ j))) := by
        rw [hW_def]
        rw [← integral_toReal_rnDeriv_mul (hPμ (ρ j)) (f := fun _ => (1 : ℝ))]
        simp
      rw [this]
      simp
    -- `∫ clampBdd ∂LW (ρ j) → ∫ clampBdd ∂LW_lim` by weak convergence; the LHS is constant 1.
    have h_tendsto : Tendsto (fun j => ∫ w, clampBdd w ∂(LW (ρ j))) atTop
        (𝓝 (∫ w, clampBdd w ∂LW_lim)) := hLW_conv clampBdd
    rw [hC_lim]
    have h_const : Tendsto (fun j => ∫ w, clampBdd w ∂(LW (ρ j))) atTop (𝓝 (1 : ℝ)) := by
      simp only [hC_each]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h_tendsto h_const
  -- ── Portmanteau transfer helpers: equal `j`-integrals ⟹ equal limit integrals. ──
  -- `U`-side: `dP/dQ`-law `⇝ U`, so equality with `LW`-integrals lifts to the limits.
  have transfer_U : ∀ (b cc : ℝ →ᵇ ℝ),
      (∀ j, ∫ x, b x ∂(LdPdQ (ρ j)) = ∫ x, cc x ∂(LW (ρ j))) →
      ∫ x, b x ∂U = ∫ x, cc x ∂LW_lim := by
    intro b cc hbc
    have hb := hU_conv' b
    have hc := hLW_conv cc
    have : (fun j => ∫ x, b x ∂(LdPdQ (ρ j))) = fun j => ∫ x, cc x ∂(LW (ρ j)) := funext hbc
    rw [this] at hb
    exact tendsto_nhds_unique hb hc
  -- `V`-side: `dQ/dP`-law `⇝ V`.
  have transfer_V : ∀ (b cc : ℝ →ᵇ ℝ),
      (∀ j, ∫ x, b x ∂(LdQdP (ρ j)) = ∫ x, cc x ∂(LW (ρ j))) →
      ∫ x, b x ∂V = ∫ x, cc x ∂LW_lim := by
    intro b cc hbc
    have hb := hV_conv b
    have hc := hLW_conv cc
    have : (fun j => ∫ x, b x ∂(LdQdP (ρ j))) = fun j => ∫ x, cc x ∂(LW (ρ j)) := funext hbc
    rw [this] at hb
    exact tendsto_nhds_unique hb hc
  -- ── Per-`j` change-of-variable identity, `V`-side (`R = P, S = Q`). ──
  -- `∫ g ∂LdQdP(ρj) = ∫ cc ∂LW(ρj)` when `cc` agrees with `w ↦ w·g((2-w)/w)` on `[0,2]`.
  have vIdent : ∀ (g cc : ℝ →ᵇ ℝ),
      (∀ w, 0 ≤ w → w ≤ 2 → w * g ((2 - w) / w) = cc w) →
      ∀ j, ∫ x, g x ∂(LdQdP (ρ j)) = ∫ x, cc x ∂(LW (ρ j)) := by
    intro g cc hagree j
    haveI := hμ_prob (ρ j)
    -- LHS = `∫ g((dQ/dP).toReal) ∂P(φ(ρj))`.
    rw [hLdQdP_def, MeasureTheory.integral_map (hdQdP_meas (ρ j)).aemeasurable
      g.continuous.aestronglyMeasurable]
    -- bridge: `= ∫ w·g((2-w)/w) ∂(μ(ρj).map W(ρj)) = ∫ w·g((2-w)/w) ∂LW(ρj)`.
    rw [cov_ratio_integral (P (φ (ρ j))) (Q (φ (ρ j))) g]
    -- The pushforward law is `LW (ρ j)` (defeq); replace `Ψ_g` by `cc` on the support `[0,2]`.
    have h_meas_eq : (μ (ρ j)).map (fun ω => ((P (φ (ρ j))).rnDeriv (μ (ρ j)) ω).toReal)
        = LW (ρ j) := rfl
    rw [h_meas_eq]
    refine integral_congr_ae ?_
    have h_compl : ∀ᵐ w ∂(LW (ρ j)), w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
      rw [ae_iff]; simpa only [not_not] using! hLW_supp (ρ j)
    filter_upwards [h_compl] with w hw
    simp only [not_or, not_lt] at hw
    exact hagree w hw.1 hw.2
  -- ── Per-`j` change-of-variable identity, `U`-side (`R = Q, S = P`). ──
  -- `∫ g ∂LdPdQ(ρj) = ∫ cc ∂LW(ρj)` when `cc` agrees with `(2-w)·g(w/(2-w))` on `[0,2]`.
  have uIdent : ∀ (g cc : ℝ →ᵇ ℝ),
      (∀ w, 0 ≤ w → w ≤ 2 → (2 - w) * g (w / (2 - w)) = cc w) →
      ∀ j, ∫ x, g x ∂(LdPdQ (ρ j)) = ∫ x, cc x ∂(LW (ρ j)) := by
    intro g cc hagree j
    haveI := hμ_prob (ρ j)
    rw [hLdPdQ_def, MeasureTheory.integral_map (hdPdQ_meas (ρ j)).aemeasurable
      g.continuous.aestronglyMeasurable]
    -- bridge with `R = Q, S = P`: `= ∫ v·g((2-v)/v) ∂(μ(ρj).map ((Q.rnDeriv μ).toReal))`.
    rw [cov_ratio_integral (Q (φ (ρ j))) (P (φ (ρ j))) g]
    -- Identify the lemma's mixture with our `μ (ρ j)` (sum is commutative).
    rw [show (((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • Q (φ (ρ j)) + ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • P (φ (ρ j)))
        = μ (ρ j) from by rw [hμ_def]; exact add_comm _ _]
    -- Push the law `μ.map K` back to `μ` (`K = (Q.rnDeriv μ).toReal`).
    set K : Ω (φ (ρ j)) → ℝ := fun ω => ((Q (φ (ρ j))).rnDeriv (μ (ρ j)) ω).toReal with hK_def
    have hK_meas : Measurable K := ((Q (φ (ρ j))).measurable_rnDeriv (μ (ρ j))).ennreal_toReal
    have hΨg_meas : Measurable (fun w : ℝ => w * g ((2 - w) / w)) :=
      measurable_id.mul (g.continuous.measurable.comp
        ((measurable_const.sub measurable_id).div measurable_id))
    rw [MeasureTheory.integral_map (f := fun w : ℝ => w * g ((2 - w) / w))
      hK_meas.aemeasurable hΨg_meas.aestronglyMeasurable]
    -- `∫ ω, K ω·g((2-Kω)/Kω) ∂μ`. Replace `K` by `2 - W` `μ`-a.e., giving `Hbc(W)`.
    -- Then push `Hbc(W)` to `LW(ρj)` and replace `Hbc` by `cc` on `[0,2]`.
    have hHbc_meas : Measurable (fun w : ℝ => (2 - w) * g (w / (2 - w))) :=
      (measurable_const.sub measurable_id).mul (g.continuous.measurable.comp
        (measurable_id.div (measurable_const.sub measurable_id)))
    rw [show (∫ w, cc w ∂(LW (ρ j))) = ∫ ω, (fun w : ℝ => (2 - w) * g (w / (2 - w))) (W (ρ j) ω)
        ∂(μ (ρ j)) from ?_]
    · refine integral_congr_ae ?_
      filter_upwards [(hmix (ρ j)).2.2.2.1, hW_le2 (ρ j)] with ω hKeq hW2
      simp only [hK_def] at hKeq ⊢
      rw [hKeq]
      -- `(2 - (2-W))/(2-W) = W/(2-W)`.
      have : (2 - (2 - W (ρ j) ω)) / (2 - W (ρ j) ω) = W (ρ j) ω / (2 - W (ρ j) ω) := by ring_nf
      rw [this]
    · -- `∫ cc ∂LW = ∫ cc(W) ∂μ = ∫ Hbc(W) ∂μ` (`W ∈ [0,2]` `μ`-a.e. and `hagree`).
      change ∫ w, cc w ∂((μ (ρ j)).map (W (ρ j))) = _
      rw [MeasureTheory.integral_map (f := fun w : ℝ => cc w)
        (hW_meas (ρ j)).aemeasurable cc.continuous.aestronglyMeasurable]
      refine integral_congr_ae ?_
      filter_upwards [hW_le2 (ρ j)] with ω hW2
      exact (hagree (W (ρ j) ω) (hW_nonneg (ρ j) ω) hW2).symm
  -- ══ Fact B: `LW_lim {0} = 0` (from `hU_pos` via the `U`-side change of variable). ══
  -- `U {0} = 0`: `U` is a probability measure with `U {0 < x} = 1`.
  have hU_zero : U {(0 : ℝ)} = 0 := by
    have hmeas : MeasurableSet {x : ℝ | 0 < x} := measurableSet_lt measurable_const measurable_id
    have h1 : U {x : ℝ | 0 < x}ᶜ = 0 := by
      have := prob_compl_eq_one_sub (μ := U) hmeas
      rw [hU_pos, tsub_self] at this
      exact this
    refine measure_mono_null ?_ h1
    intro x hx; simp only [Set.mem_singleton_iff] at hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, hx, le_refl]
  -- `f_m(x) = max 0 (1 - (m+1)|x|)`, bounded continuous in `[0,1]`, `↓ 1_{x=0}`.
  set fB : ℕ → (ℝ →ᵇ ℝ) := fun m => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max 0 (1 - (m + 1 : ℝ) * |x|))
    (continuous_const.max (continuous_const.sub (continuous_const.mul continuous_abs))) 1
    (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      refine ⟨by have : (0:ℝ) ≤ max 0 (1 - (m + 1 : ℝ) * |x|) := le_max_left _ _; linarith, ?_⟩
      rw [max_le_iff]
      refine ⟨by norm_num, ?_⟩
      have : (0:ℝ) ≤ (m + 1 : ℝ) * |x| := by positivity
      linarith) with hfB_def
  have hfB_apply : ∀ m x, fB m x = max 0 (1 - (m + 1 : ℝ) * |x|) := fun _ _ => rfl
  -- `ccB_m(w) = max 0 (2 - (m+2)·w)`, bounded continuous (`[0,2]` on the support), `↓ 2·1_{0}`.
  set ccB : ℕ → (ℝ →ᵇ ℝ) := fun m => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun w => max 0 (min (2 - (m + 2 : ℝ) * w) 2))
    (continuous_const.max ((continuous_const.sub (continuous_const.mul continuous_id)).min
      continuous_const)) 2
    (fun w => by
      rw [Real.norm_eq_abs, abs_le]
      have h0 : (0:ℝ) ≤ max 0 (min (2 - (m + 2 : ℝ) * w) 2) := le_max_left _ _
      refine ⟨by linarith, ?_⟩
      rw [max_le_iff]
      exact ⟨by norm_num, min_le_right _ _⟩) with hccB_def
  have hccB_apply : ∀ m w, ccB m w = max 0 (min (2 - (m + 2 : ℝ) * w) 2) := fun _ _ => rfl
  -- Agreement on `[0,2]`: `(2-w)·fB m (w/(2-w)) = ccB m w`.
  have hB_agree : ∀ m w, 0 ≤ w → w ≤ 2 → (2 - w) * fB m (w / (2 - w)) = ccB m w := by
    intro m w hw0 hw2
    rw [hfB_apply, hccB_apply]
    have hmin : min (2 - (m + 2 : ℝ) * w) 2 = 2 - (m + 2 : ℝ) * w := by
      apply min_eq_left; nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (m + 2 : ℝ)) hw0]
    rw [hmin]
    rcases eq_or_lt_of_le hw2 with hw | hw
    · -- `w = 2`: both sides `0`.
      subst hw
      rw [sub_self, zero_mul, max_eq_left]
      have : (2 : ℝ) - (m + 2 : ℝ) * 2 ≤ 0 := by
        have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith
      linarith
    · -- `w < 2`: `2 - w > 0`, `w/(2-w) ≥ 0`.
      have h2w : (0:ℝ) < 2 - w := by linarith
      have hratio : (0:ℝ) ≤ w / (2 - w) := div_nonneg hw0 h2w.le
      rw [abs_of_nonneg hratio]
      rw [mul_max_of_nonneg _ _ h2w.le, mul_zero]
      congr 1
      field_simp
      ring
  -- Per-`m` identity: `∫ fB m ∂U = ∫ ccB m ∂LW_lim`.
  have hB_ident : ∀ m, ∫ x, fB m x ∂U = ∫ w, ccB m w ∂LW_lim := fun m =>
    transfer_U (fB m) (ccB m) (uIdent (fB m) (ccB m) (hB_agree m))
  -- Antitone limits (`m → ∞`).
  have hfB_int : ∀ m, Integrable (fun x => fB m x) U := fun m => (fB m).integrable U
  have hccB_int : ∀ m, Integrable (fun w => ccB m w) LW_lim := fun m => (ccB m).integrable LW_lim
  -- `fB m x ↓ 1_{x=0}`.
  have hfB_anti : ∀ x : ℝ, Antitone (fun m => fB m x) := by
    intro x m n hmn
    simp only [hfB_apply]
    apply max_le_max le_rfl
    have : (m + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hmn 1
    nlinarith [abs_nonneg x]
  have hfB_tendsto : ∀ x : ℝ,
      Tendsto (fun m => fB m x) atTop (𝓝 (Set.indicator {(0:ℝ)} (fun _ => (1:ℝ)) x)) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [Set.indicator_of_mem (Set.mem_singleton 0)]
      have : (fun m => fB m (0:ℝ)) = fun _ => (1:ℝ) := by
        funext m; rw [hfB_apply]; simp
      rw [this]; exact tendsto_const_nhds
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      -- Eventually zero: once `(m+1)|x| ≥ 1`, `fB m x = 0`.
      have habs : (0:ℝ) < |x| := abs_pos.mpr hx
      have h_ev : (fun m => fB m x) =ᶠ[atTop] fun _ => (0:ℝ) := by
        filter_upwards [Filter.eventually_atTop.mpr ⟨Nat.ceil (1 / |x|), fun m hm => hm⟩]
          with m hm
        rw [hfB_apply, max_eq_left]
        have h1 : (1 : ℝ) / |x| ≤ m := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
        rw [div_le_iff₀ habs] at h1
        nlinarith [habs]
      rw [tendsto_congr' h_ev]
      exact tendsto_const_nhds
  -- `∫ fB m ∂U → (U {0}).toReal = 0`.
  have hfB_lim : Tendsto (fun m => ∫ x, fB m x ∂U) atTop (𝓝 (0 : ℝ)) := by
    have hint_ind : Integrable (Set.indicator {(0:ℝ)} (fun _ => (1:ℝ))) U :=
      (integrable_const (1:ℝ)).indicator (measurableSet_singleton (0:ℝ))
    have h := integral_tendsto_of_tendsto_of_antitone hfB_int hint_ind
      (Filter.Eventually.of_forall hfB_anti) (Filter.Eventually.of_forall hfB_tendsto)
    rwa [MeasureTheory.integral_indicator (measurableSet_singleton (0:ℝ)),
      MeasureTheory.setIntegral_const, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def, hU_zero, ENNReal.toReal_zero] at h
  -- `ccB m w ↓ 2·1_{w=0}` `LW_lim`-a.e. (support `[0,2]`); hence `∫ ccB m → 2·(LW_lim{0}).toReal`.
  have hccB_anti : ∀ᵐ w ∂LW_lim, Antitone (fun m => ccB m w) := by
    have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
      rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
    filter_upwards [h_compl] with w hw
    simp only [not_or, not_lt] at hw
    intro m n hmn
    simp only [hccB_apply]
    apply max_le_max le_rfl
    apply min_le_min _ le_rfl
    have hmn' : (m + 2 : ℝ) ≤ (n + 2 : ℝ) := by exact_mod_cast Nat.add_le_add_right hmn 2
    nlinarith [hw.1]
  have hccB_tendsto : ∀ᵐ w ∂LW_lim,
      Tendsto (fun m => ccB m w) atTop (𝓝 (Set.indicator {(0:ℝ)} (fun _ => (2:ℝ)) w)) := by
    have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
      rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
    filter_upwards [h_compl] with w hw
    simp only [not_or, not_lt] at hw
    by_cases hw0 : w = 0
    · subst hw0
      rw [Set.indicator_of_mem (Set.mem_singleton 0)]
      have : (fun m => ccB m (0:ℝ)) = fun _ => (2:ℝ) := by
        funext m; rw [hccB_apply]; simp
      rw [this]; exact tendsto_const_nhds
    · rw [Set.indicator_of_notMem (by simpa using hw0)]
      have hwpos : 0 < w := lt_of_le_of_ne hw.1 (Ne.symm hw0)
      have h_ev : (fun m => ccB m w) =ᶠ[atTop] fun _ => (0:ℝ) := by
        filter_upwards [Filter.eventually_atTop.mpr ⟨Nat.ceil (2 / w), fun m hm => hm⟩] with m hm
        rw [hccB_apply, max_eq_left]
        apply min_le_of_left_le
        have h1 : (2 : ℝ) / w ≤ m := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
        rw [div_le_iff₀ hwpos] at h1
        nlinarith [hwpos]
      rw [tendsto_congr' h_ev]; exact tendsto_const_nhds
  have hccB_lim : Tendsto (fun m => ∫ w, ccB m w ∂LW_lim) atTop
      (𝓝 (2 * (LW_lim {(0:ℝ)}).toReal)) := by
    have hint_ind : Integrable (Set.indicator {(0:ℝ)} (fun _ => (2:ℝ))) LW_lim :=
      (integrable_const (2:ℝ)).indicator (measurableSet_singleton (0:ℝ))
    have h := integral_tendsto_of_tendsto_of_antitone hccB_int hint_ind
      hccB_anti hccB_tendsto
    rw [MeasureTheory.integral_indicator (measurableSet_singleton (0:ℝ)),
      MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def] at h
    rwa [mul_comm] at h
  -- Combine: `2·(LW_lim{0}).toReal = 0`, hence `LW_lim {0} = 0`.
  have hFactB : LW_lim {(0:ℝ)} = 0 := by
    have heq : Tendsto (fun m => ∫ w, ccB m w ∂LW_lim) atTop (𝓝 (0:ℝ)) := by
      have : (fun m => ∫ w, ccB m w ∂LW_lim) = fun m => ∫ x, fB m x ∂U := by
        funext m; exact (hB_ident m).symm
      rw [this]; exact hfB_lim
    have h2 : 2 * (LW_lim {(0:ℝ)}).toReal = 0 := tendsto_nhds_unique hccB_lim heq
    have h3 : (LW_lim {(0:ℝ)}).toReal = 0 := by linarith
    exact (ENNReal.toReal_eq_zero_iff _).mp h3 |>.resolve_right (measure_ne_top _ _)
  -- ══ Fact A: `∫ x ∂V = ∫ (2-w)·1_{0<w} ∂LW_lim = 1`. ══
  -- `hA m(x) = min (max x 0) m`, bounded continuous, `↑ max x 0`.
  set hA : ℕ → (ℝ →ᵇ ℝ) := fun m => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min (max x 0) (m : ℝ))
    ((continuous_id.max continuous_const).min continuous_const) (m : ℝ)
    (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      have h0 : (0:ℝ) ≤ min (max x 0) (m : ℝ) := le_min (le_max_right _ _) (by positivity)
      have hm0 : (0:ℝ) ≤ (m : ℝ) := by positivity
      exact ⟨by linarith, min_le_right _ _⟩) with hA_def
  have hA_apply : ∀ m x, hA m x = min (max x 0) (m : ℝ) := fun _ _ => rfl
  -- `ccA m(w) = min (2 - cl w) (m · cl w)`, `cl = clamp [0,2]`; bdd-cont, `↑ (2-w)1_{0<w}`.
  set ccA : ℕ → (ℝ →ᵇ ℝ) := fun m => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun w => min (2 - min (max w 0) 2) ((m : ℝ) * min (max w 0) 2))
    ((continuous_const.sub ((continuous_id.max continuous_const).min continuous_const)).min
      (continuous_const.mul ((continuous_id.max continuous_const).min continuous_const))) 2
    (fun w => by
      have hcl0 : (0:ℝ) ≤ min (max w 0) 2 := le_min (le_max_right _ _) (by norm_num)
      have hcl2 : min (max w 0) 2 ≤ 2 := min_le_right _ _
      rw [Real.norm_eq_abs, abs_le]
      refine ⟨?_, ?_⟩
      · have : (0:ℝ) ≤ min (2 - min (max w 0) 2) ((m : ℝ) * min (max w 0) 2) :=
          le_min (by linarith) (by positivity)
        linarith
      · exact le_trans (min_le_left _ _) (by linarith)) with hccA_def
  have hccA_apply : ∀ m w, ccA m w = min (2 - min (max w 0) 2) ((m : ℝ) * min (max w 0) 2) :=
    fun _ _ => rfl
  -- Agreement on `[0,2]`: `w·hA m ((2-w)/w) = ccA m w`.
  have hA_agree : ∀ m w, 0 ≤ w → w ≤ 2 → w * hA m ((2 - w) / w) = ccA m w := by
    intro m w hw0 hw2
    rw [hA_apply, hccA_apply, max_eq_left hw0, min_eq_left hw2]
    rcases eq_or_lt_of_le hw0 with hw | hw
    · -- `w = 0`: both `0`.
      rw [← hw]; simp
    · -- `w > 0`: `(2-w)/w ≥ 0`.
      have hratio : (0:ℝ) ≤ (2 - w) / w := div_nonneg (by linarith) hw.le
      rw [max_eq_left hratio, mul_min_of_nonneg _ _ hw.le]
      congr 1
      · field_simp
      · ring
  -- Per-`m` identity: `∫ hA m ∂V = ∫ ccA m ∂LW_lim`.
  have hA_ident : ∀ m, ∫ x, hA m x ∂V = ∫ w, ccA m w ∂LW_lim := fun m =>
    transfer_V (hA m) (ccA m) (vIdent (hA m) (ccA m) (hA_agree m))
  -- Uniform bound: `∫ ccA m ∂LW_lim ≤ 2` (since `ccA m ≤ 2`); hence `∫ hA m ∂V ≤ 2`.
  have hccA_le2 : ∀ m w, ccA m w ≤ 2 := by
    intro m w
    rw [hccA_apply]
    have hcl0 : (0:ℝ) ≤ min (max w 0) 2 := le_min (le_max_right _ _) (by norm_num)
    exact le_trans (min_le_left _ _) (by linarith)
  have hccA_nonneg : ∀ m w, 0 ≤ ccA m w := by
    intro m w
    rw [hccA_apply]
    have hcl0 : (0:ℝ) ≤ min (max w 0) 2 := le_min (le_max_right _ _) (by norm_num)
    have hcl2 : min (max w 0) 2 ≤ 2 := min_le_right _ _
    exact le_min (by linarith) (by positivity)
  have hA_le2 : ∀ m, ∫ x, hA m x ∂V ≤ 2 := by
    intro m
    rw [hA_ident m]
    calc ∫ w, ccA m w ∂LW_lim ≤ ∫ _, (2:ℝ) ∂LW_lim :=
          integral_mono ((ccA m).integrable LW_lim) (integrable_const _)
            (fun w => hccA_le2 m w)
      _ = 2 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  -- `max · 0` is `V`-integrable (uniform bound on the truncations + monotone convergence).
  have hA_apply_nonneg : ∀ m x, 0 ≤ hA m x := by
    intro m x; rw [hA_apply]; exact le_min (le_max_right _ _) (by positivity)
  -- pointwise sup `ofReal (max x 0) = ⨆ m, ofReal (hA m x)`.
  have hA_iSup : ∀ x : ℝ, ⨆ m, ENNReal.ofReal (hA m x) = ENNReal.ofReal (max x 0) := by
    intro x
    refine le_antisymm (iSup_le (fun m => ENNReal.ofReal_le_ofReal ?_)) ?_
    · rw [hA_apply]; exact min_le_left _ _
    · -- pick `m ≥ max x 0`; then `ofReal (hA m x) = ofReal (max x 0)`.
      obtain ⟨m, hm⟩ := exists_nat_ge (max x 0)
      refine le_iSup_of_le m ?_
      rw [hA_apply, min_eq_left hm]
  have hVmax_int : Integrable (fun x => max x 0) V := by
    have hmeas : AEStronglyMeasurable (fun x : ℝ => max x 0) V :=
      (continuous_id.max continuous_const).aestronglyMeasurable
    have h0 : 0 ≤ᵐ[V] fun x : ℝ => max x 0 :=
      Filter.Eventually.of_forall (fun x => le_max_right _ _)
    refine ⟨hmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal h0]
    have hmono : Monotone (fun m => fun x => ENNReal.ofReal (hA m x)) := by
      intro m n hmn x
      exact ENNReal.ofReal_le_ofReal (by
        rw [hA_apply, hA_apply]; exact min_le_min le_rfl (by exact_mod_cast hmn))
    have hmeas_m : ∀ m, Measurable (fun x => ENNReal.ofReal (hA m x)) :=
      fun m => (hA m).continuous.measurable.ennreal_ofReal
    calc ∫⁻ x, ENNReal.ofReal (max x 0) ∂V
        = ∫⁻ x, ⨆ m, ENNReal.ofReal (hA m x) ∂V := by
          simp_rw [hA_iSup]
      _ = ⨆ m, ∫⁻ x, ENNReal.ofReal (hA m x) ∂V :=
          lintegral_iSup hmeas_m hmono
      _ ≤ 2 := by
          refine iSup_le (fun m => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal ((hA m).integrable V)
            (Filter.Eventually.of_forall (fun x => hA_apply_nonneg m x))]
          exact le_trans (ENNReal.ofReal_le_ofReal (hA_le2 m)) (by norm_num)
      _ < ⊤ := by norm_num
  -- Monotone limits (`m → ∞`).
  have hA_mono : ∀ x : ℝ, Monotone (fun m => hA m x) := by
    intro x m n hmn
    change hA m x ≤ hA n x
    rw [hA_apply, hA_apply]; exact min_le_min le_rfl (by exact_mod_cast hmn)
  have hA_tendsto : ∀ x : ℝ, Tendsto (fun m => hA m x) atTop (𝓝 (max x 0)) := by
    intro x
    have h_ev : (fun m => hA m x) =ᶠ[atTop] fun _ => max x 0 := by
      obtain ⟨M, hM⟩ := exists_nat_ge (max x 0)
      filter_upwards [Filter.eventually_atTop.mpr ⟨M, fun m hm => hm⟩] with m hm
      rw [hA_apply, min_eq_left (le_trans hM (by exact_mod_cast hm))]
    rw [tendsto_congr' h_ev]; exact tendsto_const_nhds
  have hA_lim : Tendsto (fun m => ∫ x, hA m x ∂V) atTop (𝓝 (∫ x, max x 0 ∂V)) :=
    integral_tendsto_of_tendsto_of_monotone (fun m => (hA m).integrable V) hVmax_int
      (Filter.Eventually.of_forall hA_mono) (Filter.Eventually.of_forall hA_tendsto)
  -- `ccA m w ↑ 2 - w` `LW_lim`-a.e. (`w ∈ (0,2]` a.e.).
  have hccA_mono : ∀ᵐ w ∂LW_lim, Monotone (fun m => ccA m w) := by
    have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
      rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
    filter_upwards [h_compl] with w hw
    simp only [not_or, not_lt] at hw
    intro m n hmn
    change ccA m w ≤ ccA n w
    rw [hccA_apply, hccA_apply]
    apply min_le_min le_rfl
    have hcl0 : (0:ℝ) ≤ min (max w 0) 2 := le_min (le_max_right _ _) (by norm_num)
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    nlinarith
  have hccA_tendsto : ∀ᵐ w ∂LW_lim,
      Tendsto (fun m => ccA m w) atTop (𝓝 (2 - w)) := by
    have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
      rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
    have h_zero : ∀ᵐ w ∂LW_lim, w ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, Decidable.not_not]
      have : {w : ℝ | w = 0} = {(0:ℝ)} := by ext w; simp
      rw [this]; exact hFactB
    filter_upwards [h_compl, h_zero] with w hw hw0
    simp only [not_or, not_lt] at hw
    have hwpos : 0 < w := lt_of_le_of_ne hw.1 (Ne.symm hw0)
    -- For `m` large, `ccA m w = 2 - w` (since `m·w ≥ 2 - w`).
    have h_ev : (fun m => ccA m w) =ᶠ[atTop] fun _ => 2 - w := by
      obtain ⟨M, hM⟩ := exists_nat_ge ((2 - w) / w)
      filter_upwards [Filter.eventually_atTop.mpr ⟨M, fun m hm => hm⟩] with m hm
      rw [hccA_apply, max_eq_left hw.1, min_eq_left hw.2, min_eq_left]
      have h1 : (2 - w) / w ≤ m := le_trans hM (by exact_mod_cast hm)
      rw [div_le_iff₀ hwpos] at h1; linarith
    rw [tendsto_congr' h_ev]; exact tendsto_const_nhds
  have hF_int : Integrable (fun w => 2 - w) LW_lim := by
    have : Integrable (fun w : ℝ => w) LW_lim := by
      have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
        rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
      refine (integrable_const (2:ℝ)).mono' measurable_id.aestronglyMeasurable ?_
      filter_upwards [h_compl] with w hw
      simp only [not_or, not_lt] at hw
      rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2
    exact (integrable_const (2:ℝ)).sub this
  have hccA_lim : Tendsto (fun m => ∫ w, ccA m w ∂LW_lim) atTop (𝓝 (∫ w, (2 - w) ∂LW_lim)) :=
    integral_tendsto_of_tendsto_of_monotone (fun m => (ccA m).integrable LW_lim) hF_int
      hccA_mono hccA_tendsto
  -- Combine: `∫ max x 0 ∂V = ∫ (2 - w) ∂LW_lim`.
  have hA_combine : ∫ x, max x 0 ∂V = ∫ w, (2 - w) ∂LW_lim := by
    have heq : (fun m => ∫ x, hA m x ∂V) = fun m => ∫ w, ccA m w ∂LW_lim := funext hA_ident
    rw [heq] at hA_lim
    exact tendsto_nhds_unique hA_lim hccA_lim
  -- `∫ x ∂V = ∫ max x 0 ∂V` (`V` supported in `[0,∞)`).
  have hV_id_eq : ∫ x, x ∂V = ∫ x, max x 0 ∂V := by
    refine integral_congr_ae ?_
    have h_compl : ∀ᵐ x ∂V, x ∉ {y : ℝ | y < 0} := by
      rw [ae_iff]; simpa only [not_not] using! hV_supp
    filter_upwards [h_compl] with x hx
    simp only [not_lt] at hx
    rw [max_eq_left hx]
  -- `∫ (2 - w) ∂LW_lim = 2 - 1 = 1` (probability + Fact C).
  have hF_eval : ∫ w, (2 - w) ∂LW_lim = 1 := by
    rw [integral_sub (integrable_const _) (by
      -- `id` integrable (shown above inside hF_int's proof; reprove quickly).
      have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
        rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
      refine (integrable_const (2:ℝ)).mono' measurable_id.aestronglyMeasurable ?_
      filter_upwards [h_compl] with w hw
      simp only [not_or, not_lt] at hw
      rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2)]
    rw [integral_const, probReal_univ, smul_eq_mul, one_mul, hFactC]
    norm_num
  rw [hV_id_eq, hA_combine, hF_eval]

/-- **Le Cam's first lemma** (vdV Lemma 6.4): the four-way equivalence packaged as a
`TFAE`, in the order (i) [`Contiguous`, event form], (iv) [statistic form], (ii) [limit
points of `dPₙ/dQₙ` give mass `0` to `0`], (iii) [limit points of `dQₙ/dPₙ` have mean
`1`].

Mutual absolute continuity `hac_PQ : ∀ n, P n ≪ Q n` and `hac_QP : ∀ n, Q n ≪ P n` makes
the two likelihood ratios honest (van der Vaart's convention); it is genuinely needed for
directions (i) ⟹ (ii) and (iii) ⟹ (i) (see those lemmas for the singular counterexample).

Mutual absolute continuity is essential for the directions (i) ⟹ (ii) and
(iii) ⟹ (i); the corresponding lemmas record singular counterexamples. -/
theorem leCam_first_tfae
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hac_PQ : ∀ n, (P n).AbsolutelyContinuous (Q n))
    (hac_QP : ∀ n, (Q n).AbsolutelyContinuous (P n)) :
    List.TFAE
      [ Contiguous (ι := ℕ) (Ω := Ω) atTop P Q,
        ∀ (T : ∀ n, Ω n → ℝ), (∀ n, Measurable (T n)) →
          (∀ ε : ℝ, 0 < ε →
            Tendsto (fun n => (P n) {ω | ε ≤ |T n ω|}) atTop (𝓝 0)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun n => (Q n) {ω | ε ≤ |T n ω|}) atTop (𝓝 0),
        ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (U : Measure ℝ), IsProbabilityMeasure U →
          WeakConverges
            (fun k => (Q (φ k)).map (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal)) U →
          U {x : ℝ | 0 < x} = 1,
        ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (V : Measure ℝ), IsProbabilityMeasure V →
          WeakConverges
            (fun k => (P (φ k)).map (fun ω => ((Q (φ k)).rnDeriv (P (φ k)) ω).toReal)) V →
          ∫ x, x ∂V = 1 ] := by
  tfae_have 1 ↔ 2 := contiguous_iff_tendsto_zero_statistics P Q
  tfae_have 1 → 3 := by
    intro hcont φ hφ U _ hU
    exact contiguous_imp_limit_pos P Q hcont φ hφ (fun k => hac_PQ (φ k)) U hU
  tfae_have 3 → 4 := by
    intro hU φ hφ V _ hV
    exact limit_pos_imp_mean_one P Q hU φ hφ V hV
  tfae_have 4 → 1 := mean_one_imp_contiguous P Q hac_QP
  tfae_finish

end LeCamFirstEquivalence

end Contiguity
end AsymptoticStatistics
