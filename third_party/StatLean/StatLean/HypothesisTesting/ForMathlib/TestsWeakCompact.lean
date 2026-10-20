module
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Weak compactness of the class of `[0,1]`-valued functions — ForMathlib brick

Over a **finite** measure `μ`, the set of (a.e.) `[0,1]`-valued elements of `L²(μ)` is convex,
norm-bounded and norm-closed, hence **weakly compact**; intersecting it with finitely many
linear (moment) constraints `⟪gᵢ, f⟫ = cᵢ` keeps it compact, and a linear functional therefore
attains its maximum on the constrained class. That existence statement is the analytic engine
behind every "there exists an optimal test subject to `m` side conditions" argument.

This file provides:

* `testClassL2 μ` — the `[0,1]`-valued elements of `L²(μ)`;
* `constrainedTestClassL2 μ g c` — the same, cut by the constraints `⟪gᵢ, f⟫ = cᵢ`;
* `toWeakDualL2 μ` — the Fréchet–Riesz embedding `f ↦ ⟪f, ·⟫` of `L²(μ)` into
  `WeakDual ℝ (L²(μ))`, in which the weak topology of `L²` is the ambient weak-* topology;
* compactness of the images of the two classes, and `exists_max_inner_of_constraints`.

**Packaging note.** Mathlib has the Banach–Alaoglu theorem for the weak-* topology on a dual
space (`WeakDual.isCompact_closedBall`), but no separate carrier for "the weak topology on a
Hilbert space". We therefore transport the class along the Fréchet–Riesz isometry
`InnerProductSpace.toDual` and state compactness of the *image* in `WeakDual ℝ (L²(μ))`. Since
`InnerProductSpace.toDual` and `StrongDual.toWeakDual` are both bijections, this loses nothing:
the image determines the class, and `exists_max_inner_of_constraints` — the statement the
consumers actually use — is phrased back in `L²` with no weak-dual vocabulary at all.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.6 (A Generalization of the Fundamental Lemma), supporting material for
Theorem 3.6.1: weak compactness of the class of `[0,1]`-valued test functions. (`TSH4 §3.6 Thm
3.6.1`.)

**Proof formalization notes.**
* Intended route for `isCompact_toWeakDualL2_image_testClass`: (i) `μ` finite gives
  `‖f‖₂ ≤ √(μ univ)` for every `f` in the class, so the image sits inside a closed ball, which
  is weak-* compact by `WeakDual.isCompact_closedBall` (`ProperSpace ℝ`); (ii) the image is
  weak-* closed, because `toWeakDualL2` is *surjective* (Fréchet–Riesz) and the class is cut
  out by the weak-* closed conditions `0 ≤ L h` and `L h ≤ ⟪1, h⟫` ranging over the nonnegative
  `h ∈ L²(μ)` — each an intersection of preimages of closed half-lines under the continuous
  evaluations `L ↦ L h` (note `1 ∈ L²(μ)` because `μ` is finite); (iii) conclude with
  `IsCompact.of_isClosed_subset`. This avoids needing Mazur's theorem ("convex + norm-closed
  ⇒ weakly closed") explicitly.
* The constrained class adds `⋂ i, {L | L (g i) = c i}`, closed for the same reason; the index
  type is arbitrary (no finiteness needed for compactness — finiteness enters only when the
  constraints are produced by a finite family of moment conditions).
* `exists_max_inner_of_constraints` then applies `IsCompact.exists_isMaxOn` to the continuous
  evaluation at `h` and transports the maximizer back along the injective `toWeakDualL2`.
* Everything is stated for the real field; `⟪·,·⟫_ℝ` is the `InnerProductSpace`-scoped
  notation, and on real `L²` it reduces to `∫ f·g dμ` (see `toWeakDualL2_apply_eq_integral`;
  recall that `RCLike.inner_apply` produces the factors in the opposite order).

**Bibliographic comments.** Weak-* compactness of the closed unit ball of a dual space is the
Banach–Alaoglu theorem (S. Banach, *Théorie des opérations linéaires*, Warszawa, 1932, for the
separable case; L. Alaoglu, "Weak topologies of normed linear spaces," *Ann. of Math.* **41**
(1940), 252–267, in general). The self-duality of Hilbert space used to transport it is the
Fréchet–Riesz representation theorem (F. Riesz, *C. R. Acad. Sci. Paris* **144** (1907),
1409–1411; M. Fréchet, *ibid.*, 1414–1416). Its use to produce optimal tests under finitely
many side conditions is the generalized-fundamental-lemma argument of J. Neyman and
E. S. Pearson ("On the problem of the most efficient tests of statistical hypotheses,"
*Phil. Trans. R. Soc. A* **231** (1933), 289–337).
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- On the real field, the inner product is the product (the RCLike inner
`⟪a, b⟫ = b * conj a` reduces definitionally to `b * a`). -/
private lemma real_inner_eq_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  change b * a = a * b; ring

/-- The **`L²` test class**: the (a.e.) `[0,1]`-valued elements of `L²(μ)`. These are exactly
the critical functions of the testing theory, viewed in `L²`. -/
def testClassL2 (μ : Measure 𝓧) : Set (Lp ℝ 2 μ) :=
  {f | (0 : 𝓧 → ℝ) ≤ᵐ[μ] ⇑f ∧ ⇑f ≤ᵐ[μ] (1 : 𝓧 → ℝ)}

/-- The **constrained `L²` test class**: `[0,1]`-valued elements of `L²(μ)` satisfying the
linear (moment) side conditions `⟪gᵢ, f⟫ = cᵢ`. The index type is arbitrary. -/
def constrainedTestClassL2 (μ : Measure 𝓧) {ι : Type*} (g : ι → Lp ℝ 2 μ) (c : ι → ℝ) :
    Set (Lp ℝ 2 μ) :=
  testClassL2 μ ∩ {f | ∀ i, ⟪g i, f⟫_ℝ = c i}

/-- The **Fréchet–Riesz embedding** of `L²(μ)` into its weak dual, `f ↦ ⟪f, ·⟫`. The weak
topology of `L²(μ)` is the topology induced from `WeakDual ℝ (L²(μ))` along this map. -/
noncomputable def toWeakDualL2 (μ : Measure 𝓧) (f : Lp ℝ 2 μ) : WeakDual ℝ (Lp ℝ 2 μ) :=
  StrongDual.toWeakDual (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) f)

/-- The embedding evaluates as the inner product. -/
theorem toWeakDualL2_apply (μ : Measure 𝓧) (f g : Lp ℝ 2 μ) :
    toWeakDualL2 μ f g = ⟪f, g⟫_ℝ := by
  simp only [toWeakDualL2, StrongDual.toWeakDual_apply, InnerProductSpace.toDual_apply_apply]

/-- On real `L²` the embedding evaluates as an integral: the moment functionals
`f ↦ ∫ f·g dμ` are exactly the evaluations of the weak dual. -/
theorem toWeakDualL2_apply_eq_integral (μ : Measure 𝓧) (f g : Lp ℝ 2 μ) :
    toWeakDualL2 μ f g = ∫ x, f x * g x ∂μ := by
  rw [toWeakDualL2_apply, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact real_inner_eq_mul _ _

/-- On real `L²` the inner product is the integral of the pointwise product. -/
private lemma inner_L2_eq_integral (μ : Measure 𝓧) (f g : Lp ℝ 2 μ) :
    ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂μ :=
  (toWeakDualL2_apply μ f g).symm.trans (toWeakDualL2_apply_eq_integral μ f g)

/-- The pointwise product of two `L²` functions is integrable. -/
private lemma integrable_L2_mul (μ : Measure 𝓧) (f g : Lp ℝ 2 μ) :
    Integrable (fun x => f x * g x) μ :=
  (L2.integrable_inner f g).congr (Filter.Eventually.of_forall fun x => real_inner_eq_mul _ _)

/-- Pairing an `L²` function against the indicator of a measurable set is its set-integral. -/
private lemma inner_indicator_eq_setIntegral (μ : Measure 𝓧) [IsFiniteMeasure μ]
    (f : Lp ℝ 2 μ) {s : Set 𝓧} (hs : MeasurableSet s) :
    ⟪f, indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)⟫_ℝ = ∫ x in s, f x ∂μ := by
  rw [inner_L2_eq_integral, ← integral_indicator hs]
  refine integral_congr_ae ?_
  have hcoe : ⇑(indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)) =ᵐ[μ]
      s.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
  filter_upwards [hcoe] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · simp [Set.indicator_of_mem hxs]
  · simp [Set.indicator_of_notMem hxs]

/-- The indicator of a finite-measure set is `≥ 0` almost everywhere. -/
private lemma indicatorConstLp_one_nonneg (μ : Measure 𝓧) [IsFiniteMeasure μ]
    {s : Set 𝓧} (hs : MeasurableSet s) :
    (0 : 𝓧 → ℝ) ≤ᵐ[μ] ⇑(indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)) := by
  have hcoe : ⇑(indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)) =ᵐ[μ]
      s.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
  filter_upwards [hcoe] with x hx
  rw [Pi.zero_apply, hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- **Weak continuity of the moment functionals**: `f ↦ ⟪g, f⟫` is continuous for the weak
topology, in the weak-dual packaging. -/
theorem continuous_eval_weakDual (μ : Measure 𝓧) (g : Lp ℝ 2 μ) :
    Continuous fun L : WeakDual ℝ (Lp ℝ 2 μ) => L g :=
  WeakDual.eval_continuous g

/-- **Moment-constraint slices are closed**: a level set of a moment functional is weakly
closed. -/
theorem isClosed_setOf_eval_eq (μ : Measure 𝓧) (g : Lp ℝ 2 μ) (c : ℝ) :
    IsClosed {L : WeakDual ℝ (Lp ℝ 2 μ) | L g = c} :=
  isClosed_singleton.preimage (continuous_eval_weakDual μ g)

/-- **Weak compactness of the test class** over a finite measure. -/
theorem isCompact_toWeakDualL2_image_testClass (μ : Measure 𝓧)
    -- USER-INPUT: the dominating measure is finite; without it the class is unbounded in `L²`
    [IsFiniteMeasure μ] :
    IsCompact (toWeakDualL2 μ '' testClassL2 μ) := by
  -- The constant-`1` element of `L²(μ)` (available since `μ` is finite).
  set one : Lp ℝ 2 μ := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ) (1 : ℝ)
    with hone_def
  have hone : ⇑one =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    have hcoe : ⇑one =ᵐ[μ] Set.univ.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
    simpa [Set.indicator_univ] using hcoe
  -- The image is cut out by the weak-* closed order conditions.
  have himg : toWeakDualL2 μ '' testClassL2 μ =
      {L : WeakDual ℝ (Lp ℝ 2 μ) | ∀ h : Lp ℝ 2 μ, (0 : 𝓧 → ℝ) ≤ᵐ[μ] ⇑h → 0 ≤ L h}
        ∩ {L | ∀ h : Lp ℝ 2 μ, (0 : 𝓧 → ℝ) ≤ᵐ[μ] ⇑h → L h ≤ toWeakDualL2 μ one h} := by
    ext L
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_image, testClassL2]
    constructor
    · rintro ⟨f, ⟨hf0, hf1⟩, rfl⟩
      refine ⟨fun h hh => ?_, fun h hh => ?_⟩
      · rw [toWeakDualL2_apply_eq_integral]
        refine integral_nonneg_of_ae ?_
        filter_upwards [hf0, hh] with x hx0 hxh
        exact mul_nonneg hx0 hxh
      · rw [toWeakDualL2_apply_eq_integral, toWeakDualL2_apply_eq_integral]
        refine integral_mono_ae (integrable_L2_mul μ f h) (integrable_L2_mul μ one h) ?_
        filter_upwards [hf1, hh, hone] with x hx1 hxh hxone
        rw [hxone, one_mul]
        exact mul_le_of_le_one_left hxh hx1
    · rintro ⟨hpos, hle⟩
      set f : Lp ℝ 2 μ :=
        (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm (WeakDual.toStrongDual L) with hf_def
      have hLf : ∀ g, ⟪f, g⟫_ℝ = L g := by
        intro g
        rw [hf_def, InnerProductSpace.toDual_symm_apply, WeakDual.toStrongDual_apply]
      have hInt : Integrable (⇑f) μ := (Lp.memLp f).integrable (by norm_num)
      have hf0 : (0 : 𝓧 → ℝ) ≤ᵐ[μ] ⇑f := by
        refine ae_nonneg_of_forall_setIntegral_nonneg hInt fun s hs _ => ?_
        have h1 : 0 ≤ L (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)) :=
          hpos _ (indicatorConstLp_one_nonneg μ hs)
        rwa [← hLf, inner_indicator_eq_setIntegral] at h1
      have hf1 : ⇑f ≤ᵐ[μ] (1 : 𝓧 → ℝ) := by
        refine ae_le_of_forall_setIntegral_le hInt (integrable_const 1) fun s hs _ => ?_
        have h2 : L (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ))
            ≤ toWeakDualL2 μ one (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)) :=
          hle _ (indicatorConstLp_one_nonneg μ hs)
        rw [← hLf, inner_indicator_eq_setIntegral, toWeakDualL2_apply,
          inner_indicator_eq_setIntegral] at h2
        have hone_s : ∫ x in s, (one : 𝓧 → ℝ) x ∂μ = ∫ x in s, (1 : ℝ) ∂μ :=
          setIntegral_congr_ae hs (hone.mono fun x hx _ => hx)
        rw [hone_s] at h2
        simpa using h2
      refine ⟨f, ⟨hf0, hf1⟩, ?_⟩
      apply DFunLike.ext
      intro g
      rw [toWeakDualL2_apply, hLf]
  -- Closedness of the cut-out set.
  have hclosed : IsClosed
      ({L : WeakDual ℝ (Lp ℝ 2 μ) | ∀ h : Lp ℝ 2 μ, (0 : 𝓧 → ℝ) ≤ᵐ[μ] ⇑h → 0 ≤ L h}
        ∩ {L | ∀ h : Lp ℝ 2 μ, (0 : 𝓧 → ℝ) ≤ᵐ[μ] ⇑h → L h ≤ toWeakDualL2 μ one h}) := by
    refine IsClosed.inter ?_ ?_
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun h => isClosed_iInter fun _ =>
        isClosed_Ici.preimage (continuous_eval_weakDual μ h)
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun h => isClosed_iInter fun _ =>
        isClosed_Iic.preimage (continuous_eval_weakDual μ h)
  -- The image lies in a weak-* compact closed ball.
  have hsub : toWeakDualL2 μ '' testClassL2 μ ⊆
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ (Lp ℝ 2 μ)) ‖one‖ := by
    rintro L ⟨f, ⟨hf0, hf1⟩, rfl⟩
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    have hts : WeakDual.toStrongDual (toWeakDualL2 μ f)
        = InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) f := rfl
    rw [hts, LinearIsometryEquiv.norm_map]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hf0, hf1, hone] with x hx0 hx1 hxone
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hxone, abs_of_nonneg hx0, abs_one]
    exact hx1
  exact IsCompact.of_isClosed_subset (WeakDual.isCompact_closedBall 0 ‖one‖)
    (himg ▸ hclosed) hsub

/-- **Weak compactness of the constrained test class** over a finite measure: the moment
constraints cut a closed subset out of a compact set. -/
theorem isCompact_toWeakDualL2_image_constrained (μ : Measure 𝓧)
    -- USER-INPUT: the dominating measure is finite; without it the class is unbounded in `L²`
    [IsFiniteMeasure μ] {ι : Type*} (g : ι → Lp ℝ 2 μ) (c : ι → ℝ) :
    IsCompact (toWeakDualL2 μ '' constrainedTestClassL2 μ g c) := by
  have hset : toWeakDualL2 μ '' constrainedTestClassL2 μ g c
      = (toWeakDualL2 μ '' testClassL2 μ)
        ∩ ⋂ i, {L : WeakDual ℝ (Lp ℝ 2 μ) | L (g i) = c i} := by
    ext L
    constructor
    · rintro ⟨f, ⟨hf, hcon⟩, rfl⟩
      refine ⟨⟨f, hf, rfl⟩, ?_⟩
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro i
      rw [toWeakDualL2_apply, real_inner_comm]
      exact hcon i
    · rintro ⟨⟨f, hf, rfl⟩, hcon⟩
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at hcon
      refine ⟨f, ⟨hf, fun i => ?_⟩, rfl⟩
      have hi := hcon i
      rw [toWeakDualL2_apply] at hi
      rw [real_inner_comm]
      exact hi
  rw [hset]
  exact (isCompact_toWeakDualL2_image_testClass μ).inter_right
    (isClosed_iInter fun i => isClosed_setOf_eval_eq μ (g i) (c i))

/-- **Existence of an optimal constrained test**: a linear functional attains its maximum over
the (nonempty) class of `[0,1]`-valued `L²` functions meeting the moment constraints.

Stated entirely inside `L²`: the weak-dual packaging is an implementation detail of the
proof. -/
theorem exists_max_inner_of_constraints (μ : Measure 𝓧)
    -- USER-INPUT: the dominating measure is finite; without it the class is unbounded in `L²`
    [IsFiniteMeasure μ] {ι : Type*} (g : ι → Lp ℝ 2 μ) (c : ι → ℝ) (h : Lp ℝ 2 μ)
    -- USER-INPUT: the constraints are attainable; Neyman–Pearson (1933)
    (hne : (constrainedTestClassL2 μ g c).Nonempty) :
    ∃ f ∈ constrainedTestClassL2 μ g c,
      ∀ f' ∈ constrainedTestClassL2 μ g c, ⟪h, f'⟫_ℝ ≤ ⟪h, f⟫_ℝ := by
  have hKcompact : IsCompact (toWeakDualL2 μ '' constrainedTestClassL2 μ g c) :=
    isCompact_toWeakDualL2_image_constrained μ g c
  have hKne : (toWeakDualL2 μ '' constrainedTestClassL2 μ g c).Nonempty := hne.image _
  obtain ⟨L₀, hL₀K, hL₀max⟩ :=
    hKcompact.exists_isMaxOn hKne (continuous_eval_weakDual μ h).continuousOn
  obtain ⟨f₀, hf₀, rfl⟩ := hL₀K
  refine ⟨f₀, hf₀, fun f' hf' => ?_⟩
  have hle : toWeakDualL2 μ f' h ≤ toWeakDualL2 μ f₀ h :=
    hL₀max (Set.mem_image_of_mem (toWeakDualL2 μ) hf')
  rw [toWeakDualL2_apply, toWeakDualL2_apply, ← real_inner_comm f' h, ← real_inner_comm f₀ h] at hle
  exact hle

end StatLean.HypothesisTesting
