module
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorNarrow
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorNarrowReverse

@[expose] public section

/-!
# Linear-tangent-space case of the narrow/broad equivalence

This file defines the strict vdV-prose carrier-scoped narrow form of
`IsRegularEstimator`, the predicate `IsLinearTangentSpace T_set`
(carrier = L²-closed linear span), and the equivalence

  `IsRegularEstimator_narrow_carrier ⟺ IsRegularEstimator_narrow`
    (under `IsLinearTangentSpace`)

Composing this with the forward `isRegularEstimator_implies_narrow` and the
reverse `isRegularEstimator_of_narrow` yields the narrow ↔ broad pair for the
linear-tangent-space case vdV writes a full proof for: vdV §25.3.2 quantifies
the chosen submodel over the tangent set's carrier `Ṗ_P`, while vdV's proof
("Assume first that the tangent set is a linear space") works in the
linear-tangent-space case where the carrier coincides with its L²-closed linear
span.

Headline declarations: `IsLinearTangentSpace`,
`IsRegularEstimator_narrow_carrier`,
`narrow_carrier_iff_narrow_tangentSpace_of_linear`,
`isRegularEstimator_implies_narrow_carrier_of_linear`,
`isRegularEstimator_narrow_carrier_implies_broad_of_linear`.

Reference: vdV §25.3.2.
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

/-! ## The `IsLinearTangentSpace` predicate -/

/-- *Linear-tangent-space hypothesis.*

The tangent set's carrier `T_set.carrier` coincides with its L²-closed linear
span `tangentSpace T_set` (as subsets of `↥(L2ZeroMean P)`). Formalises vdV's
"Assume first that the tangent set is a linear space".

Under this hypothesis the carrier-scoped narrow form
`IsRegularEstimator_narrow_carrier` and the closure-scoped narrow form
`IsRegularEstimator_narrow` coincide: both quantify the chosen family over
the same set.

A predicate rather than a structure field, so callers supplying their own
`T_set` who happen to know it is a linear space (e.g. semiparametric models
with closed linear tangent space) can supply it as a separate hypothesis.

Reference: vdV §25.3 (paragraph after Lemma 25.14): tangent sets that are
linear subspaces of `L²₀(P)` are a special case of the general tangent-set
notion. -/
def IsLinearTangentSpace {P : Measure Ω} [IsProbabilityMeasure P]
    (T_set : TangentSpec P) : Prop :=
  (↑(tangentSpace T_set) : Set ↥(L2ZeroMean P)) = T_set.carrier

/-- Under `IsLinearTangentSpace T_set`, membership in `tangentSpace T_set` is
equivalent to membership in `T_set.carrier`. -/
lemma IsLinearTangentSpace.mem_iff {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P} (h : IsLinearTangentSpace T_set)
    (g : ↥(L2ZeroMean P)) :
    g ∈ tangentSpace T_set ↔ g ∈ T_set.carrier := by
  -- `g ∈ tangentSpace T_set` unfolds (via `SetLike`) to
  -- `g ∈ (↑(tangentSpace T_set) : Set _)`; `h` rewrites that set to `T_set.carrier`.
  constructor
  · intro hg
    have hg' : g ∈ (↑(tangentSpace T_set) : Set ↥(L2ZeroMean P)) := hg
    rw [h] at hg'
    exact hg'
  · intro hg
    have hg' : g ∈ T_set.carrier := hg
    rw [← h] at hg'
    exact hg'

/-- Under `IsLinearTangentSpace T_set`, membership in the *algebraic* span
`Submodule.span ℝ T_set.carrier` is equivalent to membership in `T_set.carrier`.
When the carrier equals its L²-closed linear span it equals its algebraic span
too (`carrier ⊆ span ⊆ closure(span) = carrier`), so all three coincide. Used to
transport the (now span-scoped) narrow form against the carrier-scoped form. -/
lemma IsLinearTangentSpace.span_mem_iff {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P} (h : IsLinearTangentSpace T_set)
    (g : ↥(L2ZeroMean P)) :
    g ∈ Submodule.span ℝ T_set.carrier ↔ g ∈ T_set.carrier := by
  constructor
  · intro hg
    exact (h.mem_iff g).mp (span_carrier_le_tangentSpace _ hg)
  · intro hg
    exact Submodule.subset_span hg

/-! ## The `IsRegularEstimator_narrow_carrier` def

Strict vdV-prose form: chosenFamily indexed over `T_set.carrier` only. Body
otherwise identical to `IsRegularEstimator_narrow`. -/

/-- *Strict vdV-prose carrier-scoped narrow form of `IsRegularEstimator`.*

Identical to `IsRegularEstimator_narrow` except that the chosen family is
indexed over `T_set.carrier` (the tangent set proper) rather than over the
L²-closed linear span `tangentSpace T_set`. Matches vdV's prose

  "for every g ∈ Ṗ_P, write P_{t,g} for a submodel".

The conclusion clause (per-direction weak convergence of the rescaled
estimator) is verbatim identical to the closure-scoped narrow form.

# Equivalence under linear-tangent-space hypothesis

Under `IsLinearTangentSpace T_set` (vdV's "linear tangent space" case), the
carrier-scoped form and the closure-scoped form coincide; see
`narrow_carrier_iff_narrow_tangentSpace_of_linear`. Composing with
`isRegularEstimator_implies_narrow` and the reverse
`isRegularEstimator_of_narrow` gives
`isRegularEstimator_narrow_carrier_implies_broad_of_linear` and its converse
`isRegularEstimator_implies_narrow_carrier_of_linear`, the narrow ↔ broad pair
for the case vdV writes a full proof for.

Reference: vdV §25.3.2 (paragraph preceding Theorem 25.20). -/
def IsRegularEstimator_narrow_carrier
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
        (g : ↥(L2ZeroMean P)) ∈ T_set.carrier → QMDPath P,
    (∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ T_set.carrier),
      (chosenFamily g hg).score = g) ∧
    (∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ T_set.carrier),
      WeakConverges
        (fun n : ℕ =>
          (MeasureTheory.Measure.pi
              (fun _ : Fin n => (chosenFamily g hg).curve ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω =>
              Real.sqrt n *
                (T_n n X - ψ ((chosenFamily g hg).curve ((Real.sqrt n)⁻¹)))))
        L)

/-! ## narrow_carrier ⟺ narrow_tangentSpace under the linear hypothesis -/

/-- Under the linear-tangent-space hypothesis, the carrier-scoped narrow form
and the closure-scoped narrow form are equivalent.

Mathematical content: when `↑(tangentSpace T_set) = T_set.carrier` as sets,
the two `∃ chosenFamily` quantifications range over the same indexing set;
the per-direction inner `∀ g hg, …` clauses likewise range over the same set;
the bodies are byte-identical. The equivalence amounts to transporting
membership predicates along `h_linear.span_mem_iff`.

Reference: vdV §25.3; §25.3.2 (Hájek-style regularity at chosen submodels,
under the "linear tangent space" assumption). -/
theorem narrow_carrier_iff_narrow_tangentSpace_of_linear
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P}
    {ψ : Measure Ω → ℝ}
    {IF_eff : ↥(L2ZeroMean P)}
    {hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ}
    {hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff}
    {T_n : ∀ n, (Fin n → Ω) → ℝ}
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (h_linear : IsLinearTangentSpace T_set) :
    IsRegularEstimator_narrow_carrier P T_set ψ hψ hEIF T_n L ↔
    IsRegularEstimator_narrow P T_set ψ hψ hEIF T_n L := by
  classical
  constructor
  · -- Forward: carrier-scoped ⟹ closure-scoped.
    -- Given chosenFamily indexed over carrier, build one indexed over tangentSpace
    -- by transporting along h_linear.span_mem_iff.
    rintro ⟨chosenFamily_C, h_score_C, h_regular_C⟩
    refine ⟨fun g hg => chosenFamily_C g ((h_linear.span_mem_iff g).mp hg), ?_, ?_⟩
    · intro g hg
      exact h_score_C g ((h_linear.span_mem_iff g).mp hg)
    · intro g hg
      exact h_regular_C g ((h_linear.span_mem_iff g).mp hg)
  · -- Reverse: closure-scoped ⟹ carrier-scoped.
    -- Given chosenFamily indexed over tangentSpace, restrict to carrier
    -- by transporting back along h_linear.span_mem_iff.
    rintro ⟨chosenFamily_T, h_score_T, h_regular_T⟩
    refine ⟨fun g hg => chosenFamily_T g ((h_linear.span_mem_iff g).mpr hg), ?_, ?_⟩
    · intro g hg
      exact h_score_T g ((h_linear.span_mem_iff g).mpr hg)
    · intro g hg
      exact h_regular_T g ((h_linear.span_mem_iff g).mpr hg)

/-! ## Main corollary: narrow ↔ broad (linear case)

Composes `narrow_carrier_iff_narrow_tangentSpace_of_linear` with the forward
`isRegularEstimator_implies_narrow` (unconditional) and the reverse
`isRegularEstimator_of_narrow` (dominator-scoped). The narrow ⟹ broad direction
inherits the reverse map's `h_chosen_dom`, `hT_meas`, `h_dom_γ` restrictions;
the broad ⟹ narrow direction is clean.

Closes both the chosen-vs-all-paths and carrier-vs-closure scope questions for
the linear case vdV proves in full. -/

/-- **Main corollary** (clean direction): under the linear-tangent-space
hypothesis, the broad form of `IsRegularEstimator` implies the strict
vdV-prose carrier-scoped narrow form. No extra hypothesis beyond
`IsLinearTangentSpace` and the broad assumption.

Proof: compose the forward `isRegularEstimator_implies_narrow` with the reverse
arrow of `narrow_carrier_iff_narrow_tangentSpace_of_linear`.

Reference: vdV §25.3.2 (Hájek-style regularity). -/
theorem isRegularEstimator_implies_narrow_carrier_of_linear
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P}
    {ψ : Measure Ω → ℝ}
    {IF_eff : ↥(L2ZeroMean P)}
    {hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ}
    {hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff}
    {T_n : ∀ n, (Fin n → Ω) → ℝ}
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (h_linear : IsLinearTangentSpace T_set)
    (h_broad : IsRegularEstimator P T_set ψ hψ hEIF T_n L) :
    IsRegularEstimator_narrow_carrier P T_set ψ hψ hEIF T_n L :=
  (narrow_carrier_iff_narrow_tangentSpace_of_linear h_linear).mpr
    (isRegularEstimator_implies_narrow h_broad)

/-- **Main corollary** (dominator-restricted direction): under the
linear-tangent-space hypothesis, the strict vdV-prose carrier-scoped narrow
form of `IsRegularEstimator` implies the broad form, restricted to realising
`QMDPath`s `γ` with `γ.dominating = P` (matching the reverse map's dominator
scope).

### Hypotheses

* `h_linear : IsLinearTangentSpace T_set`: carrier coincides with L²-closed
  linear span.
* `h_narrow_C : IsRegularEstimator_narrow_carrier …`: the carrier-scoped
  narrow regularity.
* `h_chosen_dom`: every entry of the chosen family obtained from `h_narrow_C`
  (i.e. the closure-extended chosen family produced by
  `narrow_carrier_iff_narrow_tangentSpace_of_linear.mp`) has `dominating := P`.
* `hT_meas`: the estimator sequence is measurable.

### Conclusion (one-sided implication, parameterised by γ)

For every `g ∈ tangentSpace T_set`, every `γ : QMDPath P` realising `g` with
`γ.dominating = P`, the rescaled estimator computed along `γ` and recentered
at the perturbed truth converges weakly to `L`.

### Why parameterised, not packaged as `IsRegularEstimator`

`IsRegularEstimator`'s broad form quantifies `∀ curve : QMDPath P` (no
dominator restriction). The reverse direction `isRegularEstimator_of_narrow`
only closes the `γ.dominating = P` slice (see `RegularEstimatorNarrowReverse`
docstring on "Dominator-scope restriction"). We expose the slice directly
rather than packaging it as the full broad form.

Reference: vdV §25.3.2 (chosen-vs-all-paths LAN-locality argument). -/
theorem isRegularEstimator_narrow_carrier_implies_broad_of_linear
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P}
    {ψ : Measure Ω → ℝ}
    {IF_eff : ↥(L2ZeroMean P)}
    {hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ}
    {hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff}
    {T_n : ∀ n, (Fin n → Ω) → ℝ}
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (h_linear : IsLinearTangentSpace T_set)
    (h_narrow_C : IsRegularEstimator_narrow_carrier P T_set ψ hψ hEIF T_n L)
    (h_chosen_dom : ∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
        ((Classical.choose
            ((narrow_carrier_iff_narrow_tangentSpace_of_linear (hEIF := hEIF)
              (T_n := T_n) (L := L) h_linear).mp h_narrow_C)) g hg).dominating = P)
    (hT_meas : ∀ n, Measurable (T_n n))
    (g : ↥(L2ZeroMean P))
    (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (γ : QMDPath P)
    (hscore : γ.score = g)
    (h_dom_γ : γ.dominating = P) :
    WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => γ.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n * (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹)))))
      L := by
  -- Step 1: transport carrier-narrow ⟹ closure-narrow via
  -- `narrow_carrier_iff_narrow_tangentSpace_of_linear`.
  have h_narrow_T : IsRegularEstimator_narrow P T_set ψ hψ hEIF T_n L :=
    (narrow_carrier_iff_narrow_tangentSpace_of_linear h_linear).mp h_narrow_C
  -- Step 2: apply the reverse map (closure-narrow ⟹ broad, restricted to γ.dom = P).
  exact isRegularEstimator_of_narrow h_narrow_T h_chosen_dom hT_meas g hg γ hscore h_dom_γ

end AsymptoticStatistics.LowerBounds.RegularEstimator
