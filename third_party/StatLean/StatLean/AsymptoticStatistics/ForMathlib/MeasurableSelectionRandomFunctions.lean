module
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section

/-!
# Measurable selection for random functions in a function class

Theorem-agnostic API exposing the abstract closure-of-measurability
predicate `MeasurablySelectsRandomFunctions F` plus two consumer endpoints:

* `measurableSet_of_random_function_in_class` — given `hF`, the parameter-
  space event `{ξ | fhat ξ ∈ F}` is measurable.
* `exists_measurable_surrogate` — replace `fhat ξ` by a fixed `f₀ ∈ F`
  outside the membership event, preserving joint measurability.

The headline theorem `measurablySelectsRandomFunctions_of_l2_closed` proves
that every L²(P)-norm-closed admissible class measurably selects random
functions (Vaart–Wellner, *Weak Convergence and Empirical Processes*,
§2.10.1 Theorem 2.10.1), via the named sub-auxiliaries below.

Reference: Vaart–Wellner, *Weak Convergence and Empirical Processes*,
§2.10.1; see also van der Vaart, *Asymptotic Statistics*, §19.4 (the union
closure step in the proof of Theorem 19.23).
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace AsymptoticStatistics.ForMathlib
namespace MeasurableSelection

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A class `F` of functions `Ω → ℝ` **measurably selects random functions**
if for every measurable parameter space `Ξ` and every jointly measurable
random function `fhat : Ξ → (Ω → ℝ)` (joint measurability =
`Measurable (Function.uncurry fhat)`), the parameter-space event
`{ξ | fhat ξ ∈ F}` is measurable in `Ξ`.

This is the *abstract conclusion* of Vaart–Wellner Theorem 2.10.1, stripped
of its textbook hypotheses. The closure-of-measurability flavour is what
downstream lemmas actually consume; the textbook theorem
(`measurablySelectsRandomFunctions_of_l2_closed`, below) gives the
canonical sufficient hypothesis (L²(P)-norm-closed + admissibility).

We restrict `Ξ` to universe 0 (`Type`) to match the consuming
`IsAsymptoticallyEquicontinuous` definition. -/
def MeasurablySelectsRandomFunctions (F : Set (Ω → ℝ)) : Prop :=
  ∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (fhat : Ξ → (Ω → ℝ)),
    Measurable (Function.uncurry fhat) → MeasurableSet {ξ | fhat ξ ∈ F}

/-- **Measurable membership predicate** (thin wrapper).

Given the abstract closure hypothesis `hF : MeasurablySelectsRandomFunctions F`
and a jointly measurable random function `fhat : Ξ → (Ω → ℝ)`, the event
`{ξ | fhat ξ ∈ F}` is measurable in `Ξ`. -/
lemma measurableSet_of_random_function_in_class
    {Ξ : Type} [MeasurableSpace Ξ]
    (F : Set (Ω → ℝ))
    (hF : MeasurablySelectsRandomFunctions F)
    (fhat : Ξ → (Ω → ℝ))
    (h_meas : Measurable (Function.uncurry fhat)) :
    MeasurableSet {ξ | fhat ξ ∈ F} :=
  hF fhat h_meas

/-- **Measurable surrogate construction — direct flavour.**

Given a fixed `f₀ ∈ F` with `Measurable f₀`, a jointly measurable random
function `fhat : Ξ → (Ω → ℝ)`, and a *measurable* membership event
`{ξ | fhat ξ ∈ F}`, the modified random function

  `fhat_F ξ ω := if fhat ξ ∈ F then fhat ξ ω else f₀ ω`

is jointly measurable, takes values in `F`, and agrees with `fhat ξ` on the
membership event. -/
lemma exists_measurable_surrogate_of_measurableSet
    {Ξ : Type} [MeasurableSpace Ξ]
    (F : Set (Ω → ℝ))
    {f₀ : Ω → ℝ} (hf₀_F : f₀ ∈ F) (hf₀_meas : Measurable f₀)
    (fhat : Ξ → (Ω → ℝ))
    (h_meas : Measurable (Function.uncurry fhat))
    (hF_meas_set : MeasurableSet {ξ | fhat ξ ∈ F}) :
    ∃ fhat_F : Ξ → (Ω → ℝ),
      Measurable (Function.uncurry fhat_F) ∧
      (∀ ξ, fhat_F ξ ∈ F) ∧
      (∀ ξ, fhat ξ ∈ F → fhat_F ξ = fhat ξ) := by
  classical
  refine ⟨fun ξ => if fhat ξ ∈ F then fhat ξ else f₀, ?_, ?_, ?_⟩
  · -- Joint measurability: `Function.uncurry fhat_F` rewrites to an
    -- `if`-piecewise function of two measurable branches over the measurable
    -- product subset `{ξ | fhat ξ ∈ F} ×ˢ univ`.
    have h_eq :
        (Function.uncurry fun ξ => if fhat ξ ∈ F then fhat ξ else f₀)
          = fun p : Ξ × Ω =>
              if fhat p.1 ∈ F then Function.uncurry fhat p else f₀ p.2 := by
      funext p
      rcases p with ⟨ξ, ω⟩
      change (if fhat ξ ∈ F then fhat ξ else f₀) ω
          = if fhat ξ ∈ F then fhat ξ ω else f₀ ω
      split_ifs <;> rfl
    rw [h_eq]
    have hS : MeasurableSet {p : Ξ × Ω | fhat p.1 ∈ F} := by
      have hprod : MeasurableSet ({ξ | fhat ξ ∈ F} ×ˢ (Set.univ : Set Ω)) :=
        hF_meas_set.prod MeasurableSet.univ
      have h_set_eq :
          {p : Ξ × Ω | fhat p.1 ∈ F} = {ξ | fhat ξ ∈ F} ×ˢ (Set.univ : Set Ω) := by
        ext p; simp
      rw [h_set_eq]
      exact hprod
    exact Measurable.ite hS h_meas (hf₀_meas.comp measurable_snd)
  · intro ξ
    change (if fhat ξ ∈ F then fhat ξ else f₀) ∈ F
    split_ifs with h
    · exact h
    · exact hf₀_F
  · intro ξ hξ
    change (if fhat ξ ∈ F then fhat ξ else f₀) = fhat ξ
    rw [if_pos hξ]

/-- **Measurable surrogate construction — closure-predicate flavour.**

Given the abstract closure hypothesis `hF : MeasurablySelectsRandomFunctions F`
and a fixed `f₀ ∈ F` with `Measurable f₀`, every jointly measurable random
function `fhat` admits a measurable surrogate `fhat_F` taking values in `F`
and agreeing with `fhat` wherever `fhat ξ ∈ F`. -/
lemma exists_measurable_surrogate
    {Ξ : Type} [MeasurableSpace Ξ]
    (F : Set (Ω → ℝ))
    (hF : MeasurablySelectsRandomFunctions F)
    {f₀ : Ω → ℝ} (hf₀_F : f₀ ∈ F) (hf₀_meas : Measurable f₀)
    (fhat : Ξ → (Ω → ℝ))
    (h_meas : Measurable (Function.uncurry fhat)) :
    ∃ fhat_F : Ξ → (Ω → ℝ),
      Measurable (Function.uncurry fhat_F) ∧
      (∀ ξ, fhat_F ξ ∈ F) ∧
      (∀ ξ, fhat ξ ∈ F → fhat_F ξ = fhat ξ) :=
  exists_measurable_surrogate_of_measurableSet F hf₀_F hf₀_meas fhat h_meas
    (hF fhat h_meas)

/-! ## Vaart–Wellner Theorem 2.10.1 — structural decomposition

The content of V-W Thm 2.10.1 ("every L²(P)-norm-closed admissible
class measurably selects random functions") is factored into named
sub-auxiliary claims, each capturing a distinct mathematical piece of the
proof.

* `vw_polish_l2_space` — *L²(P) is Polish*: under
  `[MeasurableSpace.CountablyGenerated Ω]`, derived from the Mathlib
  `Lp.SecondCountableTopology` instance chain.

* `vw_random_function_to_l2_measurable` — packages the conclusion
  `MeasurableSet {ξ | fhat ξ ∈ F}`, delegating to
  `vw_l2_class_event_measurable` via the `Set.ext`+`hF_ae_invariant` bridge
  identifying the function-level event with the L²-class event.

* `vw_l2_class_event_measurable` — *L²-class event measurability*: the L²-
  side of V-W §2.10.1, stating that the L²-class event
  `{ξ | ∃ f ∈ F, fhat ξ =ᵃᵉ[P] f}` is `Ξ`-measurable.

* `vw_l2_closed_borel` — *closed L²-subset is Borel*. A norm-closed subset
  of `Lp ℝ 2 P` is Borel-measurable (via `IsClosed.measurableSet`).

* `vw_random_function_lp_lift_measurable` — *measurable lift* `Φ : Ξ → Lp ℝ 2 P`
  with measurable L²-locus `S ⊆ Ξ`.
  * `vw_random_function_lp_locus_measurable` — L²-locus
    measurability `S = {ξ | MemLp (fhat ξ) 2 P} ⊆ Ξ` via Fubini
    (`Measurable.lintegral_prod_right'`).
  * `vw_random_function_lp_lift_inner_measurable` — Lp-valued
    Borel-measurability of the canonical lift
    `Φ ξ := if h : MemLp (fhat ξ) 2 P then MemLp.toLp (fhat ξ) h else 0`,
    via `measurable_of_pointwise_dist_measurable` + per-`g` piecewise dist
    measurability.
  * `measurable_of_pointwise_dist_measurable` (ForMathlib helper) —
    *backwards companion to `Measurable.dist`*: in a second-countable Borel
    pseudo-metric target, pointwise dist measurability ⟹ Borel
    measurability, via `isOpen_sUnion_countable` ball cover.

* `vw_function_class_l2_image_closed` — *L²-image of `F` is closed in `Lp ℝ 2 P`*:
  the closure-transfer step from function-level L²-norm closedness of `F`
  (`hF_l2_closed`) to Lp-quotient closedness of the image, via
  `IsSeqClosed.isClosed` + `tendsto_Lp_iff_tendsto_eLpNorm'`.

The top-level theorem `measurablySelectsRandomFunctions_of_l2_closed`
assembles these via direct delegation to
`vw_random_function_to_l2_measurable`. -/

/-- **L²(P) is Polish / standard-Borel.**

The space `Lp ℝ 2 P` is a separable Banach space, hence Polish, when the
σ-algebra on `Ω` is countably generated. We expose the separability fragment
(`SecondCountableTopology`), which combined with `Lp`'s existing complete
metric structure yields the Polish space property used by the V-W §2.10.1
measurable-selection argument.

The proof assembles the Mathlib instance chain
`IsProbabilityMeasure P → IsFiniteMeasure → SigmaFinite → SFinite`
together with `[MeasurableSpace.CountablyGenerated Ω]` to derive
`[IsSeparable P]` and then `[Lp.SecondCountableTopology]` since `ℝ` is
separable.

`[MeasurableSpace.CountablyGenerated Ω]` is the standard textbook hypothesis
(vdV §19; V-W §2.10.1 takes the underlying sample space to be standard Borel
= Polish, which implies countably generated).

Reference: V-W *Weak Convergence and Empirical Processes*, §2.10.1; also
vdV §19 (function classes are typically given over standard probability
spaces where this is automatic). -/
theorem vw_polish_l2_space (P : Measure Ω) [IsProbabilityMeasure P]
    [MeasurableSpace.CountablyGenerated Ω] :
    SecondCountableTopology (Lp ℝ 2 P) := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  exact inferInstance

/-- **Closed L²-subset is Borel.**

A norm-closed subset of `Lp ℝ 2 P` is Borel-measurable. Specialisation of
`IsClosed.measurableSet` for a topological space with the Borel σ-algebra of
opens.

Used internally by `vw_random_function_to_l2_measurable` to upgrade the
L²-image of `F` from "norm-closed" (provided by the hypothesis
`hF_l2_closed`) to "Borel-measurable" (consumed by `measurable_preimage`). -/
theorem vw_l2_closed_borel
    {P : Measure Ω}
    [MeasurableSpace (Lp ℝ 2 P)] [BorelSpace (Lp ℝ 2 P)]
    {S : Set (Lp ℝ 2 P)} (hS : IsClosed S) :
    MeasurableSet S :=
  hS.measurableSet

/-- **L²-locus measurability** (V-W §2.10.1).

The L²-locus `S := {ξ | MemLp (fhat ξ) 2 P}` is `Ξ`-measurable when `fhat`
is jointly measurable.

Proof: unfold `MemLp` to `AEStronglyMeasurable ∧ eLpNorm < ∞`.
For real-valued `fhat`, each marginal `fhat ξ` is measurable (hence
strongly measurable since ℝ is second-countable), so the first conjunct
is automatic. For the second, rewrite `eLpNorm (fhat ξ) 2 P < ∞` as
`∫⁻ x, ‖fhat ξ x‖ₑ ^ 2 ∂P < ∞` (via `eLpNorm_nnreal_pow_eq_lintegral`) and
apply `Measurable.lintegral_prod_right'` to the jointly measurable
non-negative integrand.

Reference: standard Fubini-style locus measurability; instance of the
"product measurable ⟹ marginal-functional measurable" pattern. -/
theorem vw_random_function_lp_locus_measurable
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type} [MeasurableSpace Ξ] (fhat : Ξ → (Ω → ℝ))
    (h_meas : Measurable (Function.uncurry fhat)) :
    MeasurableSet {ξ | MemLp (fhat ξ) 2 P} := by
  -- AEStronglyMeasurable is automatic: each `fhat ξ` is measurable, hence
  -- strongly measurable since `ℝ` is second-countable, hence aestronglyMeasurable.
  have h_marginal : ∀ ξ, Measurable (fhat ξ) := fun ξ =>
    h_meas.comp measurable_prodMk_left
  have h_ae_sm : ∀ ξ, AEStronglyMeasurable (fhat ξ) P := fun ξ =>
    (h_marginal ξ).stronglyMeasurable.aestronglyMeasurable
  -- The L²-norm-finiteness piece: `eLpNorm (fhat ξ) 2 P < ∞` is measurable.
  -- Rewrite via `eLpNorm h 2 μ ^ 2 = ∫⁻ ‖h x‖ₑ ^ 2 ∂μ` (squaring is monotone, so
  -- finiteness is equivalent). Map measurability follows from
  -- `Measurable.lintegral_prod_right`.
  set ψ : Ξ → ℝ≥0∞ := fun ξ => ∫⁻ x, ‖fhat ξ x‖ₑ ^ (2 : ℝ) ∂P
  have h_uncurry_enorm_pow : Measurable
      (fun p : Ξ × Ω => ‖Function.uncurry fhat p‖ₑ ^ (2 : ℝ)) :=
    h_meas.enorm.pow_const _
  have h_ψ_meas : Measurable ψ :=
    h_uncurry_enorm_pow.lintegral_prod_right'
  have h_set_eq :
      {ξ | MemLp (fhat ξ) 2 P} = ψ ⁻¹' {a : ℝ≥0∞ | a < ∞} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ψ]
    refine ⟨fun hξ => ?_, fun hξ => ⟨h_ae_sm ξ, ?_⟩⟩
    · have h_sq := eLpNorm_nnreal_pow_eq_lintegral (f := fhat ξ) (μ := P)
        (p := (2 : ℝ≥0)) (by norm_num)
      have hp_cast : ((2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) := by norm_num
      have hp_real : ((2 : ℝ≥0) : ℝ) = (2 : ℝ) := by norm_num
      rw [hp_cast, hp_real] at h_sq
      rw [← h_sq]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hξ.2.ne
    · -- Goal: eLpNorm (fhat ξ) 2 P < ⊤
      have h_sq := eLpNorm_nnreal_pow_eq_lintegral (f := fhat ξ) (μ := P)
        (p := (2 : ℝ≥0)) (by norm_num)
      have hp_cast : ((2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) := by norm_num
      have hp_real : ((2 : ℝ≥0) : ℝ) = (2 : ℝ) := by norm_num
      rw [hp_cast, hp_real] at h_sq
      have h_sq_lt : eLpNorm (fhat ξ) 2 P ^ (2 : ℝ) < ⊤ := h_sq ▸ hξ
      exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).mp h_sq_lt
  rw [h_set_eq]
  exact h_ψ_meas measurableSet_Iio

/-- **ForMathlib helper — measurable from pointwise distance measurability.**

In a second-countable Borel pseudo-metric space `Y`, a function `f : X → Y`
from a measurable space `X` is measurable provided that for every `y : Y`
the real-valued function `x ↦ dist (f x) y` is `X`-measurable.

This is the backwards companion to `Measurable.dist` (the forward direction
gives dist measurability from measurability of both arguments). The
standard textbook fact used in the V-W §2.10.1 Lp-valued measurable-
selection argument: to show a candidate lift `Φ : Ξ → Lp ℝ 2 P` is Borel-
measurable, it suffices to check `ξ ↦ dist (Φ ξ) g` is `Ξ`-measurable for
every `g : Lp ℝ 2 P`.

**Proof**: in a metric space the open balls form a topological subbasis
for the topology, so any open set is a union of balls. By second-
countability (`isOpen_sUnion_countable`), the union can be taken countable.
Each ball preimage `f ⁻¹' Metric.ball y r = (dist (f ·) y) ⁻¹' Iio r` is
measurable from the pointwise dist hypothesis, and countable unions of
measurable sets are measurable. -/
theorem measurable_of_pointwise_dist_measurable
    {X : Type*} [MeasurableSpace X]
    {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {f : X → Y}
    (hf : ∀ y : Y, Measurable (fun x => dist (f x) y)) : Measurable f := by
  apply measurable_of_isOpen
  intro U hU
  -- Cover U by all balls contained in it.
  set S : Set (Set Y) := {B | (∃ y r, B = Metric.ball y r) ∧ B ⊆ U} with hS_def
  have hS_open : ∀ s ∈ S, IsOpen s := by
    rintro s ⟨⟨y, r, rfl⟩, _⟩
    exact Metric.isOpen_ball
  have hS_union : ⋃₀ S = U := by
    apply Set.Subset.antisymm
    · rintro x ⟨B, ⟨⟨_, _, rfl⟩, hBU⟩, hxB⟩
      exact hBU hxB
    · intro x hxU
      obtain ⟨ε, hε_pos, hε⟩ := Metric.isOpen_iff.mp hU x hxU
      exact ⟨Metric.ball x ε, ⟨⟨x, ε, rfl⟩, hε⟩, Metric.mem_ball_self hε_pos⟩
  obtain ⟨T, hT_count, hTS, hT_eq⟩ := TopologicalSpace.isOpen_sUnion_countable S hS_open
  have hU_eq : U = ⋃₀ T := by rw [hT_eq, hS_union]
  rw [hU_eq, Set.preimage_sUnion]
  apply MeasurableSet.biUnion hT_count
  intro B hB
  obtain ⟨⟨y, r, rfl⟩, _⟩ := hTS hB
  have h_eq : f ⁻¹' Metric.ball y r = (fun x => dist (f x) y) ⁻¹' Set.Iio r := by
    ext x; simp [Metric.mem_ball, Set.mem_Iio]
  rw [h_eq]
  exact (hf y) measurableSet_Iio

/-- **Inner measurable lift** (V-W §2.10.1).

Given a jointly measurable random function `fhat : Ξ × Ω → ℝ`, there exists a
Borel-measurable lift `Φ : Ξ → Lp ℝ 2 P` such that on the L²-locus
`{ξ | MemLp (fhat ξ) 2 P}`, `Φ ξ = MemLp.toLp (fhat ξ) h`.

This is the deep content of V-W §2.10.1's measurable-selection argument: the
bridge from Ω-joint measurability of `fhat` to Lp-valued Borel-measurability
of the lifted family.

Construct

  `Φ ξ := if h : MemLp (fhat ξ) 2 P then MemLp.toLp (fhat ξ) h else 0`

(under `Classical.propDecidable`). `Lp ℝ 2 P` is separable Polish via
`vw_polish_l2_space` (Mathlib's `Lp.SecondCountableTopology` under
`[CountablyGenerated Ω]`); apply the helper
`measurable_of_pointwise_dist_measurable` and reduce to showing, for each
fixed `g : Lp ℝ 2 P`, that `ξ ↦ dist (Φ ξ) g` is `Ξ`-measurable.

Per-`g` measurability via a `Set.piecewise` split on the L²-locus
`S := {ξ | MemLp (fhat ξ) 2 P}` (via
`vw_random_function_lp_locus_measurable`):

* On `S`, `dist (Φ ξ) g = (eLpNorm (fhat ξ - ⇑g) 2 P).toReal`, expressible
  as `((∫⁻ x, ‖fhat ξ x - g x‖ₑ ^ 2 ∂P) ^ (1/2)).toReal`, measurable by
  `Measurable.lintegral_prod_right'` applied to the jointly measurable
  non-negative integrand `‖fhat ξ x - g x‖ₑ ^ 2`.
* On `Sᶜ`, `Φ ξ = 0`, so `dist (Φ ξ) g = ‖g‖` (constant).

Reference: V-W *Weak Convergence and Empirical Processes*, §2.10.1. -/
theorem vw_random_function_lp_lift_inner_measurable
    (P : Measure Ω) [IsProbabilityMeasure P]
    [MeasurableSpace.CountablyGenerated Ω]
    [MeasurableSpace (Lp ℝ 2 P)] [BorelSpace (Lp ℝ 2 P)]
    {Ξ : Type} [MeasurableSpace Ξ] (fhat : Ξ → (Ω → ℝ))
    (h_meas : Measurable (Function.uncurry fhat)) :
    ∃ Φ : Ξ → Lp ℝ 2 P, Measurable Φ ∧
      ∀ ξ (h : MemLp (fhat ξ) 2 P), Φ ξ = MemLp.toLp (fhat ξ) h := by
  classical
  haveI : SecondCountableTopology (Lp ℝ 2 P) := vw_polish_l2_space P
  refine ⟨fun ξ => if h : MemLp (fhat ξ) 2 P then MemLp.toLp (fhat ξ) h else 0,
    ?_, fun ξ h => dif_pos h⟩
  -- Measurability via pointwise distance criterion.
  apply measurable_of_pointwise_dist_measurable
  intro g
  -- Per-`g` distance measurability via piecewise split on the L²-locus.
  have h_locus_meas : MeasurableSet {ξ | MemLp (fhat ξ) 2 P} :=
    vw_random_function_lp_locus_measurable P fhat h_meas
  -- Jointly measurable integrand `(ξ, x) ↦ ‖fhat ξ x - g x‖ₑ ^ 2`.
  have h_uncurry_diff : Measurable
      (fun p : Ξ × Ω => Function.uncurry fhat p - g p.2) :=
    h_meas.sub ((Lp.stronglyMeasurable g).measurable.comp measurable_snd)
  have h_uncurry_enorm_pow : Measurable
      (fun p : Ξ × Ω => ‖Function.uncurry fhat p - g p.2‖ₑ ^ (2 : ℝ)) :=
    h_uncurry_diff.enorm.pow_const _
  -- The squared-L²-norm function `ξ ↦ ∫⁻ x, ‖fhat ξ x - g x‖ₑ ^ 2 ∂P`,
  -- well-defined (in ℝ≥0∞) on all of Ξ.
  set ψ : Ξ → ℝ≥0∞ := fun ξ => ∫⁻ x, ‖fhat ξ x - g x‖ₑ ^ (2 : ℝ) ∂P with hψ_def
  have h_ψ_meas : Measurable ψ := h_uncurry_enorm_pow.lintegral_prod_right'
  -- Two measurable branches.
  have h_locus_branch : Measurable (fun ξ => ((ψ ξ) ^ ((1 : ℝ) / 2)).toReal) :=
    (h_ψ_meas.pow_const _).ennreal_toReal
  have h_complement_branch : Measurable (fun _ : Ξ => (‖g‖ : ℝ)) := measurable_const
  -- Piecewise equality with `dist (Φ ξ) g`.
  have h_dist_eq : (fun ξ => dist (if h : MemLp (fhat ξ) 2 P
        then MemLp.toLp (fhat ξ) h else (0 : Lp ℝ 2 P)) g)
      = Set.piecewise {ξ | MemLp (fhat ξ) 2 P}
          (fun ξ => ((ψ ξ) ^ ((1 : ℝ) / 2)).toReal)
          (fun _ => (‖g‖ : ℝ)) := by
    ext ξ
    by_cases hξ : MemLp (fhat ξ) 2 P
    · have hξ_mem : ξ ∈ {ξ : Ξ | MemLp (fhat ξ) 2 P} := hξ
      rw [Set.piecewise_eq_of_mem _ _ _ hξ_mem]
      have h_Φ : (if h : MemLp (fhat ξ) 2 P
            then MemLp.toLp (fhat ξ) h else (0 : Lp ℝ 2 P))
          = MemLp.toLp (fhat ξ) hξ := dif_pos hξ
      rw [h_Φ, Lp.dist_def]
      have h_eLpNorm_ae : eLpNorm (⇑(MemLp.toLp (fhat ξ) hξ) - ⇑g) 2 P
          = eLpNorm (fhat ξ - ⇑g) 2 P := by
        apply eLpNorm_congr_ae
        filter_upwards [hξ.coeFn_toLp] with x hx
        simp [Pi.sub_apply, hx]
      rw [h_eLpNorm_ae]
      -- Relate `eLpNorm (fhat ξ - ⇑g) 2 P` to `(ψ ξ)^(1/2)`.
      have h_sq := eLpNorm_nnreal_pow_eq_lintegral
        (f := fhat ξ - ⇑g) (μ := P) (p := (2 : ℝ≥0)) (by norm_num)
      have hp_cast : ((2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) := by norm_num
      have hp_real : ((2 : ℝ≥0) : ℝ) = (2 : ℝ) := by norm_num
      rw [hp_cast, hp_real] at h_sq
      have h_sq' : (eLpNorm (fhat ξ - ⇑g) 2 P) ^ (2 : ℝ) = ψ ξ := by
        simp only [ψ, Pi.sub_apply] at h_sq ⊢
        exact h_sq
      have h_eLpNorm_eq : eLpNorm (fhat ξ - ⇑g) 2 P = (ψ ξ) ^ ((1 : ℝ) / 2) := by
        rw [← h_sq', ← ENNReal.rpow_mul]
        norm_num
      rw [h_eLpNorm_eq]
    · have hξ_nmem : ξ ∉ {ξ : Ξ | MemLp (fhat ξ) 2 P} := hξ
      rw [Set.piecewise_eq_of_notMem _ _ _ hξ_nmem]
      have h_Φ : (if h : MemLp (fhat ξ) 2 P
            then MemLp.toLp (fhat ξ) h else (0 : Lp ℝ 2 P))
          = 0 := dif_neg hξ
      rw [h_Φ, dist_zero_left]
  rw [h_dist_eq]
  exact Measurable.piecewise h_locus_meas h_locus_branch h_complement_branch

/-- **Measurable lift** (V-W §2.10.1).

Given a jointly measurable random function `fhat : Ξ × Ω → ℝ`, there exists a
Borel-measurable lift `Φ : Ξ → Lp ℝ 2 P` together with a `Ξ`-measurable
L²-locus `S ⊆ Ξ` such that:

* `ξ ∈ S ↔ MemLp (fhat ξ) 2 P` (the L²-locus is the set of L² fibers);
* for every `ξ` and every proof `h : MemLp (fhat ξ) 2 P`,
  `Φ ξ = MemLp.toLp (fhat ξ) h` (so on the L²-locus the lift is the
  canonical L²-class of the fiber).

The body constructs the explicit witnesses

  `Φ ξ := if h : MemLp (fhat ξ) 2 P then MemLp.toLp (fhat ξ) h else 0`,
  `S := {ξ | MemLp (fhat ξ) 2 P}`

and delegates the three measurability/structural conjuncts to:

* `vw_random_function_lp_locus_measurable` — Fubini-style `S` measurability.
* `vw_random_function_lp_lift_inner_measurable` — `Φ` Borel-measurability
  via separable Polish + Fubini.

The `iff` and `eq` conjuncts are trivial (`rfl` and `dif_pos`).

Reference: V-W *Weak Convergence and Empirical Processes*, §2.10.1. -/
theorem vw_random_function_lp_lift_measurable
    (P : Measure Ω) [IsProbabilityMeasure P]
    [MeasurableSpace.CountablyGenerated Ω]
    [MeasurableSpace (Lp ℝ 2 P)] [BorelSpace (Lp ℝ 2 P)]
    {Ξ : Type} [MeasurableSpace Ξ] (fhat : Ξ → (Ω → ℝ))
    (h_meas : Measurable (Function.uncurry fhat)) :
    ∃ (Φ : Ξ → Lp ℝ 2 P) (S : Set Ξ),
      Measurable Φ ∧ MeasurableSet S ∧
      (∀ ξ, ξ ∈ S ↔ MemLp (fhat ξ) 2 P) ∧
      (∀ ξ (h : MemLp (fhat ξ) 2 P), Φ ξ = MemLp.toLp (fhat ξ) h) := by
  obtain ⟨Φ, hΦ_meas, hΦ_eq⟩ :=
    vw_random_function_lp_lift_inner_measurable P fhat h_meas
  refine ⟨Φ, {ξ | MemLp (fhat ξ) 2 P}, hΦ_meas,
    vw_random_function_lp_locus_measurable P fhat h_meas, ?_, hΦ_eq⟩
  intro ξ
  rfl

/-- **L²-image of `F` is closed in `Lp ℝ 2 P`** (V-W §2.10.1).

The L²-image of an L²-norm-closed function class `F ⊆ L²(P)` is closed in
`Lp ℝ 2 P`. Specifically, given `hF_lp : F ⊆ L²(P)` and the function-level
closure hypothesis `hF_l2_closed`, the set

  F_lp := {g : Lp ℝ 2 P | ∃ (f : Ω → ℝ) (hf : f ∈ F),
                          g = MemLp.toLp f (hF_lp f hf)}

is closed in `Lp ℝ 2 P`.

This is the closure-transfer step from the function-level L²-norm
closedness of `F` (`hF_l2_closed`: any L²-Cauchy sequence in `F` has an
a.e. limit in `F`) to the Lp-quotient-level closedness of the image
`F_lp ⊆ Lp ℝ 2 P`.

Proof: sequential closedness. Extract representatives `fₙ ∈ F` of the Lp
sequence `gₙ`, convert Lp convergence to function-level
`∫ (fₙ - g_func)² ∂P → 0` via `MemLp.eLpNorm_eq_integral_rpow_norm` (plus
the L²-norm-squared formula `‖h‖² = ∫ h² ∂P`), apply `hF_l2_closed` to get
`f ∈ F` with `f =ᵃᵉ g_func`, then close via `MemLp.toLp_eq_toLp_iff` +
`Lp.toLp_coeFn`.

Reference: V-W *Weak Convergence and Empirical Processes*, §2.10.1 (and the
surrounding §2.3 admissibility discussion). -/
theorem vw_function_class_l2_image_closed
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ))
    (hF_lp : ∀ f ∈ F, MemLp f 2 P)
    (hF_l2_closed : ∀ (g : Ω → ℝ), MemLp g 2 P →
      (∀ ε : ℝ, 0 < ε → ∃ f ∈ F, (∫ x, (f x - g x) ^ 2 ∂P) < ε) →
      ∃ f ∈ F, ∀ᵐ x ∂P, f x = g x) :
    IsClosed
      {g : Lp ℝ 2 P | ∃ (f : Ω → ℝ) (hf : f ∈ F), g = MemLp.toLp f (hF_lp f hf)} := by
  -- Helper: for real-valued h with MemLp 2 P, ‖h‖²_Lp = ∫ h² ∂P.
  have hL2sq : ∀ (h : Ω → ℝ) (hh : MemLp h 2 P),
      (eLpNorm h 2 P).toReal ^ 2 = ∫ x, (h x) ^ 2 ∂P := by
    intro h hh
    have h_eq := hh.eLpNorm_eq_integral_rpow_norm
      (show (2 : ℝ≥0∞) ≠ 0 by norm_num) (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num)
    have h2 : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h2] at h_eq
    have h_int_nn : (0 : ℝ) ≤ ∫ x, ‖h x‖ ^ (2 : ℝ) ∂P :=
      integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    have h_inner_eq : (∫ x, ‖h x‖ ^ (2 : ℝ) ∂P) = ∫ x, (h x) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards with x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
        Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
    have h_int_nn' : (0 : ℝ) ≤ ∫ x, (h x) ^ 2 ∂P := h_inner_eq ▸ h_int_nn
    rw [h_eq, ENNReal.toReal_ofReal (Real.rpow_nonneg h_int_nn _), h_inner_eq]
    rw [show ((2 : ℝ)⁻¹) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow h_int_nn' (by norm_num : (2 : ℕ) ≠ 0)
  rw [← isSeqClosed_iff_isClosed]
  intro gn g hgn_F hgn_g
  classical
  -- Extract representatives.
  choose fseq hfseq_F hfseq_eq using hgn_F
  -- g viewed as a function (via Lp coercion).
  have hg_lp : MemLp (⇑g : Ω → ℝ) 2 P := Lp.memLp g
  -- Lp convergence ⟹ eLpNorm convergence.
  have hLp_tendsto : Tendsto (fun n => eLpNorm (⇑(gn n) - ⇑g) 2 P) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' gn g).mp hgn_g
  -- Approximation hypothesis input to `hF_l2_closed`.
  have h_approx : ∀ ε : ℝ, 0 < ε →
      ∃ f ∈ F, (∫ x, (f x - ⇑g x) ^ 2 ∂P) < ε := by
    intro ε hε
    -- Bound: pick `δ := ENNReal.ofReal (√ε)`, then eventually eLpNorm < δ.
    have hδ_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (Real.sqrt ε) :=
      ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hε)
    obtain ⟨n, hn⟩ : ∃ n, eLpNorm (⇑(gn n) - ⇑g) 2 P < ENNReal.ofReal (Real.sqrt ε) :=
      ((hLp_tendsto.eventually (gt_mem_nhds hδ_pos)).exists)
    refine ⟨fseq n, hfseq_F n, ?_⟩
    -- Translate via toReal and the helper.
    have h_sub_lp : MemLp (⇑(gn n) - ⇑g) 2 P :=
      (Lp.memLp (gn n)).sub hg_lp
    have h_eLpNorm_lt_top : eLpNorm (⇑(gn n) - ⇑g) 2 P < ⊤ := h_sub_lp.2
    have h_toReal_lt : (eLpNorm (⇑(gn n) - ⇑g) 2 P).toReal < Real.sqrt ε := by
      rw [← ENNReal.toReal_ofReal (Real.sqrt_nonneg ε)]
      exact (ENNReal.toReal_lt_toReal h_eLpNorm_lt_top.ne ENNReal.ofReal_ne_top).mpr hn
    have h_toReal_nn : 0 ≤ (eLpNorm (⇑(gn n) - ⇑g) 2 P).toReal := ENNReal.toReal_nonneg
    have h_sq_lt : (eLpNorm (⇑(gn n) - ⇑g) 2 P).toReal ^ 2 < ε := by
      have h_sqr : (eLpNorm (⇑(gn n) - ⇑g) 2 P).toReal ^ 2 < Real.sqrt ε ^ 2 := by
        have := mul_lt_mul'' h_toReal_lt h_toReal_lt h_toReal_nn h_toReal_nn
        simpa [sq] using this
      rwa [Real.sq_sqrt hε.le] at h_sqr
    have h_int_eq : (∫ x, ((gn n) x - ⇑g x) ^ 2 ∂P)
        = (eLpNorm (⇑(gn n) - ⇑g) 2 P).toReal ^ 2 := by
      rw [hL2sq _ h_sub_lp]
      simp [Pi.sub_apply]
    have h_int_fseq : ∫ x, (fseq n x - ⇑g x) ^ 2 ∂P
        = ∫ x, ((gn n) x - ⇑g x) ^ 2 ∂P := by
      apply integral_congr_ae
      have hgn_eq : ⇑(gn n) =ᵐ[P] fseq n := by
        rw [hfseq_eq n]
        exact (hF_lp (fseq n) (hfseq_F n)).coeFn_toLp
      filter_upwards [hgn_eq] with x hx
      rw [hx]
    rw [h_int_fseq, h_int_eq]
    exact h_sq_lt
  obtain ⟨f, hfF, hae⟩ := hF_l2_closed (⇑g) hg_lp h_approx
  refine ⟨f, hfF, ?_⟩
  -- Goal: g = MemLp.toLp f (hF_lp f hfF)
  rw [← Lp.toLp_coeFn g hg_lp]
  exact (MemLp.toLp_eq_toLp_iff hg_lp (hF_lp f hfF)).mpr (hae.mono (fun _ h => h.symm))

/-- **L²-class event measurability** (V-W §2.10.1).

Isolates the *L²-side* content of V-W Thm 2.10.1: given a jointly measurable
random function `fhat : Ξ × Ω → ℝ` and an L²-closed function class `F`, the
**L²-class event** `{ξ | ∃ f ∈ F, fhat ξ =ᵃᵉ[P] f}` is `Ξ`-measurable. This
event captures L²-membership up to a.e.-equality; the bridge to the
function-level event `{ξ | fhat ξ ∈ F}` is handled separately by the a.e.-
invariance hypothesis on the consumer side (see
`vw_random_function_to_l2_measurable`).

The body delegates to:

* `vw_random_function_lp_lift_measurable` — the measurable lift
  `Ξ → Lp ℝ 2 P` from joint measurability of `fhat`, with measurable
  L²-locus.
* `vw_function_class_l2_image_closed` — closure of the L²-image of `F` in
  `Lp ℝ 2 P` (closure transfer from the function-level `hF_l2_closed`).
* `vw_polish_l2_space` — supplies the Polish/standard-Borel structure on
  `Lp ℝ 2 P` via `[CountablyGenerated Ω]` (used implicitly through
  `borelize`).
* `vw_l2_closed_borel` — upgrades the closed L²-image to a Borel set, ready
  for `Measurable.preimage`.

The body assembles the four pieces via a `Set.ext` rewrite identifying the
L²-class event with the intersection `S ∩ Φ ⁻¹' F_lp`, then applies
`MeasurableSet.inter` and `Measurable.preimage`.

Reference: V-W *Weak Convergence and Empirical Processes*, Theorem 2.10.1. -/
theorem vw_l2_class_event_measurable
    (P : Measure Ω) [IsProbabilityMeasure P]
    [MeasurableSpace.CountablyGenerated Ω]
    (F : Set (Ω → ℝ))
    (hF_lp : ∀ f ∈ F, MemLp f 2 P)
    (hF_l2_closed : ∀ (g : Ω → ℝ), MemLp g 2 P →
      (∀ ε : ℝ, 0 < ε → ∃ f ∈ F, (∫ x, (f x - g x) ^ 2 ∂P) < ε) →
      ∃ f ∈ F, ∀ᵐ x ∂P, f x = g x)
    {Ξ : Type} [MeasurableSpace Ξ] (fhat : Ξ → (Ω → ℝ))
    (h_meas : Measurable (Function.uncurry fhat)) :
    MeasurableSet {ξ | ∃ f ∈ F, ∀ᵐ x ∂P, fhat ξ x = f x} := by
  -- Equip `Lp ℝ 2 P` with the Borel σ-algebra (Polish via `vw_polish_l2_space`).
  letI : MeasurableSpace (Lp ℝ 2 P) := borel (Lp ℝ 2 P)
  haveI : BorelSpace (Lp ℝ 2 P) := ⟨rfl⟩
  -- from the jointly measurable random function, with the L²-locus
  -- `S ⊆ Ξ` measurable and `Φ ξ = MemLp.toLp (fhat ξ) h` on `S`.
  obtain ⟨Φ, S, hΦ_meas, hS_meas, hS_iff, hΦ_eq⟩ :=
    vw_random_function_lp_lift_measurable P fhat h_meas
  -- `Lp ℝ 2 P` (closure transfer from function-level `hF_l2_closed`).
  have hF_lp_closed : IsClosed
      {g : Lp ℝ 2 P | ∃ (f : Ω → ℝ) (hf : f ∈ F), g = MemLp.toLp f (hF_lp f hf)} :=
    vw_function_class_l2_image_closed F hF_lp hF_l2_closed
  -- Closed ⟹ Borel (via `vw_l2_closed_borel`).
  have hF_lp_meas : MeasurableSet
      {g : Lp ℝ 2 P | ∃ (f : Ω → ℝ) (hf : f ∈ F), g = MemLp.toLp f (hF_lp f hf)} :=
    vw_l2_closed_borel hF_lp_closed
  -- Rewrite the L²-class event as the intersection `S ∩ Φ ⁻¹' F_lp`.
  have h_eq : {ξ | ∃ f ∈ F, ∀ᵐ x ∂P, fhat ξ x = f x} =
      S ∩ Φ ⁻¹' {g : Lp ℝ 2 P |
        ∃ (f : Ω → ℝ) (hf : f ∈ F), g = MemLp.toLp f (hF_lp f hf)} := by
    ext ξ
    refine ⟨?_, ?_⟩
    · rintro ⟨f, hf, hae⟩
      have hae' : f =ᵐ[P] fhat ξ := Filter.EventuallyEq.symm hae
      have hξ_lp : MemLp (fhat ξ) 2 P := MemLp.ae_eq hae' (hF_lp f hf)
      refine ⟨(hS_iff ξ).mpr hξ_lp, f, hf, ?_⟩
      rw [hΦ_eq ξ hξ_lp]
      exact (MemLp.toLp_eq_toLp_iff hξ_lp (hF_lp f hf)).mpr hae
    · rintro ⟨hξS, f, hf, hΦξ⟩
      have hξ_lp : MemLp (fhat ξ) 2 P := (hS_iff ξ).mp hξS
      refine ⟨f, hf, ?_⟩
      have h1 : Φ ξ = MemLp.toLp (fhat ξ) hξ_lp := hΦ_eq ξ hξ_lp
      rw [h1] at hΦξ
      exact (MemLp.toLp_eq_toLp_iff hξ_lp (hF_lp f hf)).mp hΦξ
  rw [h_eq]
  exact hS_meas.inter (hΦ_meas hF_lp_meas)

/-- **Joint measurability ⟹ measurable membership event** (V-W §2.10.1).

This packages the conclusion of V-W Theorem 2.10.1: given a jointly
measurable random function `fhat : Ξ × Ω → ℝ` and an L²-closed function
class `F` that is **closed under a.e. equality** (`hF_ae_invariant`, the
Vaart–Wellner §2.3 admissibility hypothesis), the function-level membership
event `{ξ | fhat ξ ∈ F}` is `Ξ`-measurable.

The body delegates to two pieces:

* `vw_l2_class_event_measurable` — measurability of the L²-class event
  `{ξ | ∃ f ∈ F, fhat ξ =ᵃᵉ[P] f}`.
* a `Set.ext` rewrite using `hF_ae_invariant` to identify the function-
  level event with the L²-class event; the admissibility hypothesis is
  exactly what makes the two events agree.

Hypotheses:

* `[MeasurableSpace.CountablyGenerated Ω]` — needed for `vw_polish_l2_space`
  to deliver the Polish structure on `Lp ℝ 2 P` (V-W §2.10.1 takes the
  underlying sample space to be standard Borel).
* `hF_ae_invariant` — `F` is invariant under a.e.-equality of P-functions;
  this is the V-W §2.3 admissibility content (every Donsker class is
  admissible — vdV §19.4).

Reference: V-W *Weak Convergence and Empirical Processes*, Theorem 2.10.1;
also vdV §19.4 (the union-closure step in the proof of Theorem 19.23). -/
theorem vw_random_function_to_l2_measurable
    (P : Measure Ω) [IsProbabilityMeasure P]
    [MeasurableSpace.CountablyGenerated Ω]
    (F : Set (Ω → ℝ))
    (hF_lp : ∀ f ∈ F, MemLp f 2 P)
    (hF_l2_closed : ∀ (g : Ω → ℝ), MemLp g 2 P →
      (∀ ε : ℝ, 0 < ε → ∃ f ∈ F, (∫ x, (f x - g x) ^ 2 ∂P) < ε) →
      ∃ f ∈ F, ∀ᵐ x ∂P, f x = g x)
    -- Standard Donsker-class regularity (every Donsker class is admissible,
    -- vdV §19.4).
    (hF_ae_invariant : ∀ {f g : Ω → ℝ}, (∀ᵐ x ∂P, f x = g x) → f ∈ F → g ∈ F)
    {Ξ : Type} [MeasurableSpace Ξ] (fhat : Ξ → (Ω → ℝ))
    (h_meas : Measurable (Function.uncurry fhat)) :
    MeasurableSet {ξ | fhat ξ ∈ F} := by
  have h_eq : {ξ | fhat ξ ∈ F} = {ξ | ∃ f ∈ F, ∀ᵐ x ∂P, fhat ξ x = f x} := by
    ext ξ
    refine ⟨fun hξ => ⟨fhat ξ, hξ, ae_of_all _ (fun _ => rfl)⟩, ?_⟩
    rintro ⟨f, hf, hae⟩
    exact hF_ae_invariant (hae.mono (fun _ h => h.symm)) hf
  rw [h_eq]
  exact vw_l2_class_event_measurable P F hF_lp hF_l2_closed fhat h_meas

/-- **Vaart–Wellner Theorem 2.10.1** — *measurable selection of random
functions*.

Every L²(P)-norm-closed admissible class `F` of L²(P)-integrable functions
measurably selects random functions: the parameter-space event
`{ξ | fhat ξ ∈ F}` is measurable for every jointly measurable
`fhat : Ξ → (Ω → ℝ)`.

**Hypotheses** (matching Vaart–Wellner §2.10.1):

* `hF_lp` — `F ⊆ L²(P)`: every `f ∈ F` is L²(P)-integrable.
* `hF_l2_closed` — the image of `F` in `Lp ℝ 2 P` under the canonical
  L²-class map is closed (norm-closed in `Lp ℝ 2 P`).
* `hF_ae_invariant` — `F` is closed under a.e. equality of P-functions
  (V-W §2.3 admissibility; every Donsker class is admissible, vdV §19.4).
* `[MeasurableSpace.CountablyGenerated Ω]` — the underlying sample space
  is countably generated (V-W §2.10.1's standard-Borel setup), used to
  derive separability of `Lp ℝ 2 P`.

The content is factored into named sub-auxes:

* `vw_polish_l2_space` — Polish structure on L²(P) under
  `[CountablyGenerated Ω]`.
* `vw_random_function_to_l2_measurable` — bridges the function-level event
  to the L²-class event via `hF_ae_invariant`.
* `vw_l2_class_event_measurable` — the L²-side content packaged as
  `MeasurableSet {ξ | ∃ f ∈ F, fhat ξ =ᵃᵉ[P] f}`.
* `vw_l2_closed_borel` — closed ⟹ Borel.

The top-level body delegates to `vw_random_function_to_l2_measurable`,
which in turn delegates to `vw_l2_class_event_measurable`.

Reference: Vaart–Wellner, *Weak Convergence and Empirical Processes*,
Theorem 2.10.1 (and the surrounding §2.3 admissibility discussion). -/
theorem measurablySelectsRandomFunctions_of_l2_closed
    (P : Measure Ω) [IsProbabilityMeasure P]
    [MeasurableSpace.CountablyGenerated Ω]
    (F : Set (Ω → ℝ))
    (hF_lp : ∀ f ∈ F, MemLp f 2 P)
    (hF_l2_closed : ∀ (g : Ω → ℝ), MemLp g 2 P →
      (∀ ε : ℝ, 0 < ε → ∃ f ∈ F, (∫ x, (f x - g x) ^ 2 ∂P) < ε) →
      ∃ f ∈ F, ∀ᵐ x ∂P, f x = g x)
    (hF_ae_invariant : ∀ {f g : Ω → ℝ}, (∀ᵐ x ∂P, f x = g x) → f ∈ F → g ∈ F) :
    MeasurablySelectsRandomFunctions F := by
  intro Ξ _inst fhat h_meas
  exact vw_random_function_to_l2_measurable P F hF_lp hF_l2_closed
    hF_ae_invariant fhat h_meas

end MeasurableSelection
end AsymptoticStatistics.ForMathlib
