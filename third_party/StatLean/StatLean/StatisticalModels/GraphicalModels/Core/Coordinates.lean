module
public import StatLean.StatisticalModels.GraphicalModels.Core.CondIndep
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

/-!
# Coordinate subvectors — conditional independence between blocks of variables

A graphical model is a statement about a random vector `X : Ω → V → α` indexed by the vertex
set `V`: the blocks `X_A`, `X_B`, `X_C` for finite vertex sets `A`, `B`, `C`. This file fixes
the subvector operation and specialises `CondIndep` to it, so that everything downstream
(separation, the Markov properties, the discrete and Gaussian characterisations) speaks a
single vocabulary.

* `coords A X` — the subvector `X_A = (X_v)_{v ∈ A}`, a random element of `A → α`;
* `measurable_coords` — a subvector of a measurable vector is measurable
  (`Finset.measurable_restrict`);
* `coords_apply`, `restrict₂_comp_coords` — the two rewriting facts the later files need:
  a coordinate of a subvector is a coordinate, and restricting a bigger subvector to a smaller
  index set gives the smaller subvector;
* `CondIndepCoords μ X A B C` — `X_A ⫫ X_B ∣ X_C`;
* `CondIndepCoords.symm` / `CondIndepCoords.decomposition_of_sfinite` — the two graphoid
  properties that are structural at this level, inherited from `CondIndep.symm` /
  `CondIndep.comp_of_sfinite`. The statement `CondIndepCoords.decomposition`, which carried no
  s-finiteness hypothesis, was **false** and has been **deleted**, exactly as `CondIndep.comp`
  was — see the section *"(C2) without s-finiteness — deleted, and why"* below and the
  machine-checked `CondIndepCoords.DecompositionCounterexample.decomposition_is_false`;
* `CondIndepCoords.of_isEmpty_left` — the `A = ∅` edge case, a theorem rather than a remark:
  the subvector on an empty block is conditionally independent of everything.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, 1996, §3.1, pp. 28–30 — conditional independence between blocks of a
random vector, and the properties (C1)–(C2) used here (`Lauritzen §3.1`).

**Proof formalization notes.** *Book vs Lean:* Lauritzen writes `X_A` for the restriction of a
vector indexed by a finite vertex set; the Lean carrier is `Finset.restrict`, whose value type
`↥A → α` is indexed by the coercion of the `Finset` to a subtype. Consequently the *type* of
`X_A` depends on `A`, and set-level manipulations (`A ⊆ B`, `A ∪ B`) become explicit transport
maps `Finset.restrict₂` rather than silent equalities — this is why `restrict₂_comp_coords` is
load-bearing and why decomposition at this level is an instance of `CondIndep.comp_of_sfinite`
rather than a rewriting step.

The index type `V` is *not* assumed finite here: only the three blocks are finite sets, so the
vocabulary also covers infinite graphs. Finiteness of `V` enters only where the complement
`Finset.univ \ A` is formed (the Markov properties).

**Bibliographic comments.** The block notation `X_A` and the reading of a graphical model as a
family of conditional independence statements between blocks is Lauritzen's throughout;
the names for the properties (C1)–(C5) are J. Pearl's, *Probabilistic Reasoning in Intelligent
Systems*, Morgan Kaufmann, 1988.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels.GraphicalModels

variable {V α Ω : Type*}

/-- The **subvector** `X_A = (X_v)_{v ∈ A}` of the random vector `X` on the coordinates in `A`
(Lauritzen §3.1). Edge behaviour: for `A = ∅` the value type `↥(∅ : Finset V) → α` is a
singleton, so `coords ∅ X` is the (a.s. constant) trivial variable — conditioning on it is
conditioning on nothing, which is what the `∅`-conditioning corollaries in
`Core.Semigraphoid` rely on. -/
def coords (A : Finset V) (X : Ω → V → α) : Ω → (A → α) := fun ω => A.restrict (X ω)

@[simp]
theorem coords_apply (A : Finset V) (X : Ω → V → α) (ω : Ω) (i : A) :
    coords A X ω i = X ω i := rfl

/-- Restricting the subvector on `B` to the smaller index set `A` gives the subvector on `A`.
This is the transport map that makes the graphoid *decomposition* property available at the
coordinate level. -/
theorem restrict₂_comp_coords {A B : Finset V}
    -- USER-INPUT: the smaller index block; Lauritzen §3.1
    (hAB : A ⊆ B) (X : Ω → V → α) :
    (fun ω => Finset.restrict₂ (π := fun _ => α) hAB (coords B X ω)) = coords A X := rfl

section Measurability

variable [MeasurableSpace α] [MeasurableSpace Ω]

/-- A subvector of a measurable random vector is measurable. -/
theorem measurable_coords (A : Finset V) {X : Ω → V → α}
    -- LEAN-ONLY: measurability of the ambient random vector (product σ-algebra on `V → α`);
    -- Lauritzen works with random variables, for which this is part of the definition
    (hX : Measurable X) :
    Measurable (coords A X) :=
  (Finset.measurable_restrict (X := fun _ => α) A).comp hX

end Measurability

variable [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → V → α}
  {A B C D : Finset V}

/-- **Conditional independence between coordinate blocks**: `X_A ⫫ X_B ∣ X_C`
(Lauritzen §3.1, p. 28). Edge behaviour: with `C = ∅` this is unconditional independence of
the two blocks in the sense of `CondIndep` with a degenerate conditioning variable (see
`CondIndep.const_right`); with `A = ∅` or `B = ∅` it holds for every law. -/
def CondIndepCoords (μ : Measure Ω) (X : Ω → V → α) (A B C : Finset V) : Prop :=
  CondIndep μ (coords A X) (coords B X) (coords C X)

/-- **(C1), symmetry** at the coordinate level (Lauritzen p. 29). -/
theorem CondIndepCoords.symm
    -- USER-INPUT: the block conditional independence to be reversed; Lauritzen §3.1 (C1)
    (hci : CondIndepCoords μ X A B C) :
    CondIndepCoords μ X B A C :=
  CondIndep.symm hci

/-! ### (C2) without s-finiteness — deleted, and why

There used to be a declaration `CondIndepCoords.decomposition` here: Lauritzen (C2) at the
coordinate level, stated with **no** hypothesis on the conditioning law.
**That statement is false, and has been deleted.** What was deleted is exactly

```
theorem CondIndepCoords.decomposition (hBD : B ⊆ D) (hci : CondIndepCoords μ X A D C) :
    CondIndepCoords μ X A B C
```

and `CondIndepCoords.DecompositionCounterexample.decomposition_is_false` below derives `False`
from precisely that statement, so the refutation is machine-checked, not narrative.

*Why it is false.* Being an instance of the (likewise deleted, likewise false) `CondIndep.comp`,
it inherits that theorem's falsity: `⊗ₘ` is `0` by fiat when the conditioning law is not
s-finite (`MeasureTheory.Measure.compProd_of_not_sfinite`), so the statement equates a possibly
nonzero law with `0`. The witness is `V := Bool`, `α := Ω := CondIndep.CompCounterexample.Pt`,
`μ := mu`, with the random vector `XX` whose coordinate `false` is the identity (measurable, and
with a non-s-finite law) and whose coordinate `true` reads the invisible second coordinate of
`Pt` (not a.e. measurable), and with the blocks `A = B = ∅ ⊆ D = {true}`, `C = {false}`.

`CondIndepCoords.decomposition_of_sfinite` below is the same theorem with the one missing
hypothesis `[SFinite (μ.map (coords C X))]` restored, and is fully proved; it is free at every
intended instance, since `SFinite (μ.map _)` is an instance whenever `μ` is s-finite (in
particular for any probability measure). -/

/-- **(C2), decomposition** at the coordinate level (Lauritzen p. 29): dropping variables from
the second block preserves conditional independence. An instance of `CondIndep.comp_of_sfinite`
with the transport map `Finset.restrict₂`, whose defining equation is `restrict₂_comp_coords`.

This is the **repaired** form of the deleted `CondIndepCoords.decomposition`: identical to it
except for the one hypothesis that makes it true; see the section above. -/
theorem CondIndepCoords.decomposition_of_sfinite
    -- LEAN-ONLY: the hypothesis missing from the deleted `CondIndepCoords.decomposition`,
    -- which is false without it; see `CondIndep.comp_of_sfinite`
    [SFinite (μ.map (coords C X))]
    -- USER-INPUT: the block to be kept is part of the block that is independent;
    -- Lauritzen §3.1 (C2)
    (hBD : B ⊆ D)
    -- USER-INPUT: the block conditional independence to be weakened; Lauritzen §3.1 (C2)
    (hci : CondIndepCoords μ X A D C) :
    CondIndepCoords μ X A B C :=
  CondIndep.comp_of_sfinite (φ := id) (ψ := Finset.restrict₂ (π := fun _ => α) hBD)
    measurable_id (Finset.measurable_restrict₂ (X := fun _ => α) hBD) hci

/-- **The `A = ∅` edge case is a theorem, not a convention**: the subvector on an empty index
block takes values in a singleton type, so it is conditionally independent of every other block
given every third block. Together with `CondIndepCoords.symm` this covers both degenerate blocks
of `Undirected.Markov.IsGlobalMarkov`, whose definition quantifies over *all* disjoint triples —
which is what lets a model class supply (G) from Theorem 3.7's nonempty-blocks form.

An instance of `condIndep_of_subsingleton_left`: `↥(∅ : Finset V) → α` is a singleton type
(`IsEmpty` domain), and the other block's subvector is measurable by `measurable_coords`. -/
theorem CondIndepCoords.of_isEmpty_left
    -- LEAN-ONLY: `condDistrib` supplies the disintegration only for a finite measure
    [IsFiniteMeasure μ]
    -- LEAN-ONLY: `condDistrib` needs a standard Borel nonempty target; for `α = ℝ` (the
    -- Gaussian and the discrete-on-`ℝ` consumers) both are instances
    [StandardBorelSpace α] [Nonempty α]
    -- LEAN-ONLY: measurability of the ambient random vector, inherited by its subvectors
    (hX : Measurable X) (B C : Finset V) :
    CondIndepCoords μ X ∅ B C :=
  condIndep_of_subsingleton_left (measurable_coords B hX).aemeasurable

namespace CondIndepCoords.DecompositionCounterexample

/-! ### Refutation of the deleted `CondIndepCoords.decomposition`

The coordinate-level instance of the counterexample in `Core.CondIndep`: a random vector on the
plane `Pt` whose conditioning coordinate is rich (its law is not s-finite) and whose other
coordinate is invisible to the σ-algebra. -/

open CondIndep.CompCounterexample

/-- The bad coordinate: it reads the second coordinate of `Pt`, which the σ-algebra cannot
see. -/
def badCoord : Pt → Pt := fun p => pt (bif snd' p then 1 else 0) true

theorem not_aemeasurable_badCoord : ¬ AEMeasurable badCoord mu := by
  intro h
  have hm := measurable_of_aemeasurable h
  refine not_measurableSet_snd'_true ?_
  have hpre : badCoord ⁻¹' (fst' ⁻¹' {(1 : ℝ)}) = snd' ⁻¹' {true} := by
    ext p
    cases hb : snd' p <;> simp [badCoord, hb, Set.mem_preimage]
  rw [← hpre]
  exact hm (measurableSet_iff.2 ⟨{(1 : ℝ)}, rfl⟩)

/-- The random vector: coordinate `false` is the identity, coordinate `true` is the bad map. -/
def XX : Pt → Bool → Pt := fun p i => bif i then badCoord p else p

theorem coords_false_eq : coords ({false} : Finset Bool) XX = fun p _ => p := by
  funext p i
  have hi : (i : Bool) = false := Finset.mem_singleton.1 i.2
  simp [coords, Finset.restrict, XX, hi]

theorem measurable_coords_false : Measurable (coords ({false} : Finset Bool) XX) := by
  rw [coords_false_eq]
  exact measurable_pi_lambda _ fun _ => measurable_id

theorem measurable_coords_empty : Measurable (coords (∅ : Finset Bool) XX) :=
  measurable_pi_lambda _ fun i => absurd i.2 (Finset.notMem_empty _)

/-- The conditioning block's law is not s-finite: evaluation at the single index is a measurable
left inverse, and it carries that law back to `mu`. -/
theorem not_sfinite_map_coords_false :
    ¬ SFinite (mu.map (coords ({false} : Finset Bool) XX)) := by
  intro hs
  have hL : Measurable (fun F : ({false} : Finset Bool) → Pt => F ⟨false, by simp⟩) :=
    measurable_pi_apply _
  have hmap : (mu.map (coords ({false} : Finset Bool) XX)).map
      (fun F : ({false} : Finset Bool) → Pt => F ⟨false, by simp⟩) = mu := by
    rw [Measure.map_map hL measurable_coords_false, coords_false_eq]
    exact Measure.map_id
  exact not_sfinite_mu (hmap ▸ inferInstance)

/-- The (C2) **hypothesis** at the coordinate level: the triple's law is the junk `0` (the block
`{true}` is not a.e. measurable) and so is the right-hand side (the conditioning law is not
s-finite). -/
theorem condIndepCoords_holds : CondIndepCoords mu XX ∅ {true} {false} := by
  refine ⟨Kernel.const _ (Measure.dirac (fun _ => pt 0 true)),
    Kernel.const _ (Measure.dirac (fun _ => pt 0 true)), inferInstance, inferInstance, ?_⟩
  rw [Measure.compProd_of_not_sfinite _ _ not_sfinite_map_coords_false]
  refine Measure.map_of_not_aemeasurable ?_
  intro hc
  have h1 : AEMeasurable (coords ({true} : Finset Bool) XX) mu :=
    measurable_snd.comp_aemeasurable (measurable_snd.comp_aemeasurable hc)
  exact not_aemeasurable_badCoord
    ((measurable_pi_apply (⟨true, by simp⟩ : ({true} : Finset Bool))).comp_aemeasurable h1)

/-- Its (C2) **conclusion** at the smaller block `∅ ⊆ {true}` fails: every remaining block is
measurable, so the law on the left has mass `mu Set.univ ≠ 0`, while the right-hand side is
still `0`. -/
theorem not_condIndepCoords : ¬ CondIndepCoords mu XX ∅ ∅ {false} := by
  rintro ⟨κ, η, -, -, hmap⟩
  have hm : Measurable (fun p : Pt => (coords ({false} : Finset Bool) XX p,
      (coords (∅ : Finset Bool) XX p, coords (∅ : Finset Bool) XX p))) :=
    measurable_coords_false.prodMk (measurable_coords_empty.prodMk measurable_coords_empty)
  rw [Measure.compProd_of_not_sfinite _ _ not_sfinite_map_coords_false,
    Measure.map_eq_zero_iff hm.aemeasurable] at hmap
  exact mu_ne_zero' hmap

/-- **The deleted `CondIndepCoords.decomposition` is false**: its statement, taken as a
hypothesis, yields `False`. The missing hypothesis is `SFinite (μ.map (coords C X))`; with it the
theorem is true, and proved, as `CondIndepCoords.decomposition_of_sfinite`. -/
theorem decomposition_is_false
    (decomposition : ∀ {V α Ω : Type} [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω}
      {X : Ω → V → α} {A B C D : Finset V},
      B ⊆ D → CondIndepCoords μ X A D C → CondIndepCoords μ X A B C) :
    False :=
  not_condIndepCoords (decomposition (Finset.empty_subset _) condIndepCoords_holds)

end CondIndepCoords.DecompositionCounterexample

end StatLean.StatisticalModels.GraphicalModels
