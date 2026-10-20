module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Lemmas

@[expose] public section

/-!
# Semi-graphoids and graphoids — the abstract conditional-independence calculus

Lauritzen's properties (C1)–(C5) of conditional independence, abstracted away from probability
and stated for an **arbitrary ternary relation** `ci : Finset V → Finset V → Finset V → Prop`
on index blocks. Reading `ci A B C` as "`X_A ⫫ X_B ∣ X_C`":

* `IsSemigraphoid ci` — (C1) symmetry, (C2) decomposition, (C3) weak union, (C4) contraction;
* `IsGraphoid ci` — a semi-graphoid that also satisfies (C5) intersection;
* the derived combinators — left-handed versions of each axiom, the monotone form of
  decomposition, the `∅`-conditioning corollaries, and the block-splitting equivalence
  `IsSemigraphoid.union_iff`, which packages (C2)+(C3)+(C4) into a single `↔`.

**Why an abstract relation.** This is Lauritzen's own observation, not an invention of ours:
the remark following Proposition 3.4 (p. 33) states that the implications
global ⇒ local ⇒ pairwise Markov "only depend on the properties (C1)–(C4) of conditional
independence and hence hold for any semi-graphoid", and the remark following Theorem 3.7 says
its proof "applies to any graphoid". Abstracting therefore lets the Markov hierarchy be proved
**once**, with each model class (discrete masses, Gaussian precision, our general
`CondIndep`) supplying an instance.

**Disjointness is the book's convention, not a Lean artefact.** Lauritzen states (C1)–(C5)
for *disjoint* subsets of the variable set, and Pearl's semi-graphoid is likewise a relation on
disjoint triples; every axiom field below therefore carries pairwise disjointness of the blocks
occurring in it. This makes `IsSemigraphoid` **faithful** to the book rather than a weakened
version of it — a disjointness-free structure would demand strictly more of every instance than
Lauritzen, Pearl, or our two intended instances (the discrete mass relation and the Gaussian
precision relation) can deliver, since overlapping `A ∩ B ≠ ∅` forces the shared coordinates to
be degenerate given `C`. The hypotheses are payable by the consumer: for the `local ⇒ pairwise`
implication the instantiation is `A = {i}`, `B = {j}`, `C = ne(i)`,
`D = univ \ ({i, j} ∪ ne(i))`, pairwise disjoint precisely because `j ∉ ne(i)` is
non-adjacency, with `C ∪ D = univ \ {i, j}`.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, 1996: the properties (C1)–(C4) are the unnumbered labelled list on
p. 29 and (C5) is on p. 30; the terms *semi-graphoid* ((C1)–(C4)) and *graphoid* ((C1)–(C5))
are defined in prose on p. 30. Proposition 3.1 (p. 29) is the sufficient condition for (C5):
a strictly positive continuous joint density with respect to a product measure. The
justification for abstracting is the remark after Proposition 3.4 (p. 33) and the remark after
Theorem 3.7 (`Lauritzen §3.1`).

**Proof formalization notes.** *Book vs Lean, three deliberate differences.*

1. **Names.** Lauritzen never uses the words *symmetry*, *decomposition*, *weak union*,
   *contraction*, *intersection* — those are Pearl's (1988). We use Pearl's names for the
   fields, because they are the standard ones, and attribute the content to Lauritzen
   (C1)–(C5).
2. **Disjointness spelled out.** Lauritzen carries "disjoint subsets" as a standing convention
   in the surrounding prose; Lean has no standing conventions, so each field lists the
   `Disjoint` facts it needs, in alphabetical pair order `hAB, hAC, hAD, hBC, hBD, hCD`.
   Only what a field actually needs is required — `decomposition` omits `hBD`, since dropping
   `D` from `B ∪ D` never produces a triple in which `B` and `D` both occur.
3. **Functional versus set form of (C2)/(C3).** Lauritzen phrases (C2)/(C3) with a function
   `U = h(X)`; on index blocks the corresponding statement is the set form
   `ci A (B ∪ D) C → ci A B C`, which is what the coordinate-level `CondIndepCoords`
   decomposition delivers.

`IsGraphoid` extends `IsSemigraphoid`, so `hci.toIsSemigraphoid` gives access to every derived
combinator below from a graphoid.

**Bibliographic comments.** The names of the five properties, and the terms *semi-graphoid* and
*graphoid*, are J. Pearl's, *Probabilistic Reasoning in Intelligent Systems*, Morgan Kaufmann,
1988 (Lauritzen credits him on p. 30); the axiomatic study of conditional independence as a
relation goes back to A. P. Dawid, "Conditional independence in statistical theory,"
*J. Roy. Statist. Soc. Ser. B* **41** (1979), 1–31. Two facts justify keeping `IsGraphoid` a
separate, strictly stronger structure. First, (C5) genuinely fails in general: Lauritzen's
counterexample (p. 30) takes `X = Y = Z` with `P{X = 1} = P{X = 0} = 1/2`, where `X ⫫ Y ∣ Z`
and `X ⫫ Z ∣ Y` both hold but `X ⫫ (Y, Z)` does not; Proposition 3.1 recovers (C5) under a
strictly positive density. Second, (C1)–(C4) are sound but **not complete** for probabilistic
conditional independence: M. Studený, "Conditional independence relations have no finite
complete characterization," in *Information Theory, Statistical Decision Functions and Random
Processes* (Trans. 11th Prague Conf., vol. B), Kluwer, 1992, 377–396, shows no finite
axiomatisation exists. So `IsSemigraphoid` is a genuine abstraction of a *sufficient* calculus,
never a characterisation.
-/

namespace StatLean.StatisticalModels.GraphicalModels

variable {V : Type*} [DecidableEq V]

/-- A **semi-graphoid** (Lauritzen p. 30, crediting Pearl 1988): a ternary relation on index
blocks satisfying (C1)–(C4) on pairwise disjoint blocks. Read `ci A B C` as
`X_A ⫫ X_B ∣ X_C`. Edge behaviour: nothing is asserted about `ci` on overlapping blocks —
that regime is outside both Lauritzen's and Pearl's definitions. -/
structure IsSemigraphoid (ci : Finset V → Finset V → Finset V → Prop) : Prop where
  /-- Constitutive (Lauritzen §3.1 (C1), p. 29): `X ⫫ Y ∣ Z ⇒ Y ⫫ X ∣ Z`, for disjoint
  `X, Y, Z` — the book's standing disjointness convention. Pearl's *symmetry*. -/
  symm : ∀ {A B C}, Disjoint A B → Disjoint A C → Disjoint B C → ci A B C → ci B A C
  /-- Constitutive (Lauritzen §3.1 (C2), p. 29): `X ⫫ Y ∣ Z` and `U = h(X)` imply
  `U ⫫ Y ∣ Z`; in block form, shrinking the second block preserves independence. Stated for
  disjoint blocks, per the book. `Disjoint B D` is *not* required: the discarded block `D`
  never co-occurs with `B` in a triple here. Pearl's *decomposition*. -/
  decomposition : ∀ {A B D C}, Disjoint A B → Disjoint A C → Disjoint A D → Disjoint B C →
    Disjoint C D → ci A (B ∪ D) C → ci A B C
  /-- Constitutive (Lauritzen §3.1 (C3), p. 29): `X ⫫ Y ∣ Z` and `U = h(X)` imply
  `X ⫫ Y ∣ (Z, U)`; in block form, a discarded sub-block may be moved into the conditioning
  set. Stated for pairwise disjoint blocks, per the book — here `Disjoint B D` *is* needed,
  since the conclusion's triple `(A, B, C ∪ D)` contains both. Pearl's *weak union*. -/
  weakUnion : ∀ {A B D C}, Disjoint A B → Disjoint A C → Disjoint A D → Disjoint B C →
    Disjoint B D → Disjoint C D → ci A (B ∪ D) C → ci A B (C ∪ D)
  /-- Constitutive (Lauritzen §3.1 (C4), p. 29): `X ⫫ Y ∣ Z` and `X ⫫ W ∣ (Y, Z)` imply
  `X ⫫ (W, Y) ∣ Z`, for pairwise disjoint blocks, per the book. Pearl's *contraction*. -/
  contraction : ∀ {A B D C}, Disjoint A B → Disjoint A C → Disjoint A D → Disjoint B C →
    Disjoint B D → Disjoint C D → ci A B (C ∪ D) → ci A D C → ci A (B ∪ D) C

/-- A **graphoid** (Lauritzen p. 30, crediting Pearl 1988): a semi-graphoid that also satisfies
(C5). (C5) is *not* a consequence of (C1)–(C4) — Lauritzen's counterexample on p. 30 takes
`X = Y = Z` uniform on `{0, 1}` — but holds whenever the joint density is strictly positive
and continuous with respect to a product measure (Lauritzen, Proposition 3.1, p. 29). -/
structure IsGraphoid (ci : Finset V → Finset V → Finset V → Prop) : Prop
    extends IsSemigraphoid ci where
  /-- Constitutive (Lauritzen §3.1 (C5), p. 30): `X ⫫ Y ∣ Z` and `X ⫫ Z ∣ Y` imply
  `X ⫫ (Y, Z)`, for pairwise disjoint blocks, per the book. Pearl's *intersection*. -/
  intersection : ∀ {A B D C}, Disjoint A B → Disjoint A C → Disjoint A D → Disjoint B C →
    Disjoint B D → Disjoint C D → ci A B (C ∪ D) → ci A D (C ∪ B) → ci A (B ∪ D) C

variable {ci : Finset V → Finset V → Finset V → Prop} {A B C D B' : Finset V}

/-- **(C1) as an equivalence.** -/
theorem IsSemigraphoid.comm
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C1), p. 29
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the book's disjointness convention on the triple; Lauritzen §3.1
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    ci A B C ↔ ci B A C :=
  ⟨hci.symm hAB hAC hBC, hci.symm hAB.symm hBC hAC⟩

/-- **(C2) on the other summand**: `X_A ⫫ (X_B, X_D) ∣ X_C ⇒ X_A ⫫ X_D ∣ X_C`. -/
theorem IsSemigraphoid.decomposition_right
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C2), p. 29
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the book's disjointness convention on the blocks; Lauritzen §3.1
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D) (hBC : Disjoint B C)
    (hCD : Disjoint C D)
    -- USER-INPUT: the independence to be weakened; Lauritzen §3.1 (C2)
    (h : ci A (B ∪ D) C) :
    ci A D C :=
  hci.decomposition hAD hAC hAB hCD.symm hBC.symm (by rwa [Finset.union_comm D B])

/-- **(C2) on the left factor**, via (C1): `(X_A, X_D) ⫫ X_B ∣ X_C ⇒ X_A ⫫ X_B ∣ X_C`.
`Disjoint A D` is not needed. -/
theorem IsSemigraphoid.decomposition_left
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C1)+(C2), p. 29
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the book's disjointness convention on the blocks; Lauritzen §3.1
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hBD : Disjoint B D)
    (hCD : Disjoint C D)
    -- USER-INPUT: the independence to be weakened; Lauritzen §3.1 (C2)
    (h : ci (A ∪ D) B C) :
    ci A B C := by
  have hADB : Disjoint (A ∪ D) B := Finset.disjoint_union_left.2 ⟨hAB, hBD.symm⟩
  have hADC : Disjoint (A ∪ D) C := Finset.disjoint_union_left.2 ⟨hAC, hCD.symm⟩
  -- (C1) to put the union on the right, (C2) to drop `D`, (C1) back
  have h' : ci B (A ∪ D) C := hci.symm hADB hADC hBC h
  exact hci.symm hAB.symm hBC hAC (hci.decomposition hAB.symm hBC hBD hAC hCD h')

/-- **Monotone form of (C2)**: independence of a block passes to every sub-block. The
disjointness of the *smaller* block follows from that of the larger one by
`Disjoint.mono_right` / `Disjoint.mono_left`, so only the larger block's facts are required. -/
theorem IsSemigraphoid.decomposition_subset
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C2), p. 29
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the sub-block; Lauritzen states (C2) as `U = h(X)`, of which a sub-block is
    -- the index-set instance
    (hBB' : B ⊆ B')
    -- USER-INPUT: the book's disjointness convention on the triple `(A, B', C)`;
    -- Lauritzen §3.1
    (hAB' : Disjoint A B') (hAC : Disjoint A C) (hB'C : Disjoint B' C)
    -- USER-INPUT: the independence to be weakened; Lauritzen §3.1 (C2)
    (h : ci A B' C) :
    ci A B C := by
  -- split `B' = B ∪ (B' \ B)` and drop the second summand by (C2)
  refine hci.decomposition (D := B' \ B) (hAB'.mono_right hBB') hAC
    (hAB'.mono_right Finset.sdiff_subset) (hB'C.mono_left hBB')
    (hB'C.symm.mono_right Finset.sdiff_subset) ?_
  rwa [Finset.union_sdiff_of_subset hBB']

/-- **(C3) on the left factor**, via (C1). -/
theorem IsSemigraphoid.weakUnion_left
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C1)+(C3), p. 29
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the book's disjointness convention on the four blocks; Lauritzen §3.1
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (hCD : Disjoint C D)
    -- USER-INPUT: the independence to be weakened; Lauritzen §3.1 (C3)
    (h : ci (A ∪ D) B C) :
    ci A B (C ∪ D) := by
  have hADB : Disjoint (A ∪ D) B := Finset.disjoint_union_left.2 ⟨hAB, hBD.symm⟩
  have hADC : Disjoint (A ∪ D) C := Finset.disjoint_union_left.2 ⟨hAC, hCD.symm⟩
  have hACD : Disjoint A (C ∪ D) := Finset.disjoint_union_right.2 ⟨hAC, hAD⟩
  have hBCD : Disjoint B (C ∪ D) := Finset.disjoint_union_right.2 ⟨hBC, hBD⟩
  -- (C1), then (C3) with the roles of `A` and `B` swapped, then (C1) back
  have h' : ci B (A ∪ D) C := hci.symm hADB hADC hBC h
  exact hci.symm hAB.symm hBCD hACD (hci.weakUnion hAB.symm hBC hBD hAC hAD hCD h')

/-- **(C3) in "move a sub-block into the conditioning set" form**: this is the shape the
local ⇒ pairwise Markov implication needs. `Disjoint (B \ D) D` is
`Finset.sdiff_disjoint`, and the disjointness facts about `D` follow from those about `B` by
`Disjoint.mono_right`, so only `A`, `B`, `C` facts are required. -/
theorem IsSemigraphoid.weakUnion_sdiff
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C3), p. 29
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the sub-block to be moved into the conditioning set; Lauritzen §3.1 (C3)
    (hDB : D ⊆ B)
    -- USER-INPUT: the book's disjointness convention on the triple `(A, B, C)`;
    -- Lauritzen §3.1
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    -- USER-INPUT: the independence to be weakened; Lauritzen §3.1 (C3)
    (h : ci A B C) :
    ci A (B \ D) (C ∪ D) := by
  refine hci.weakUnion (hAB.mono_right Finset.sdiff_subset) hAC (hAB.mono_right hDB)
    (hBC.mono_left Finset.sdiff_subset) (Finset.sdiff_disjoint) (hBC.symm.mono_right hDB) ?_
  rwa [Finset.sdiff_union_of_subset hDB]

/-- **(C4) on the left factor**, via (C1). -/
theorem IsSemigraphoid.contraction_left
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C1)+(C4), p. 29
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the book's disjointness convention on the four blocks; Lauritzen §3.1
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (hCD : Disjoint C D)
    -- USER-INPUT: first premise of contraction; Lauritzen §3.1 (C4)
    (h₁ : ci B A (C ∪ D))
    -- USER-INPUT: second premise of contraction; Lauritzen §3.1 (C4)
    (h₂ : ci D A C) :
    ci (B ∪ D) A C := by
  have hACD : Disjoint A (C ∪ D) := Finset.disjoint_union_right.2 ⟨hAC, hAD⟩
  have hBCD : Disjoint B (C ∪ D) := Finset.disjoint_union_right.2 ⟨hBC, hBD⟩
  have hABD : Disjoint A (B ∪ D) := Finset.disjoint_union_right.2 ⟨hAB, hAD⟩
  have hBDC : Disjoint (B ∪ D) C := Finset.disjoint_union_left.2 ⟨hBC, hCD.symm⟩
  -- (C1) on both premises, (C4), then (C1) back
  have h₁' : ci A B (C ∪ D) := hci.symm hAB.symm hBCD hACD h₁
  have h₂' : ci A D C := hci.symm hAD.symm hCD.symm hAC h₂
  exact hci.symm hABD hAC hBDC (hci.contraction hAB hAC hAD hBC hBD hCD h₁' h₂')

/-- **Block splitting**: (C2)+(C3)+(C4) packaged as a single equivalence. Independence of a
union is the conjunction of "one part, given more" and "the other part, given less". This is
the workhorse form for the Markov hierarchy. -/
theorem IsSemigraphoid.union_iff
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C2)–(C4), p. 29
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the book's disjointness convention on the four blocks; Lauritzen §3.1
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (hCD : Disjoint C D) :
    ci A (B ∪ D) C ↔ ci A B (C ∪ D) ∧ ci A D C :=
  ⟨fun h => ⟨hci.weakUnion hAB hAC hAD hBC hBD hCD h,
      hci.decomposition_right hAB hAC hAD hBC hCD h⟩,
    fun h => hci.contraction hAB hAC hAD hBC hBD hCD h.1 h.2⟩

/-- **`∅`-conditioning corollary of (C3)**: unconditional independence of a union splits into
a conditional statement. -/
theorem IsSemigraphoid.weakUnion_empty
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C3), p. 29
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the book's disjointness convention on the three nonempty blocks;
    -- Lauritzen §3.1
    (hAB : Disjoint A B) (hAD : Disjoint A D) (hBD : Disjoint B D)
    -- USER-INPUT: unconditional independence of the union; Lauritzen §3.1 (C3)
    (h : ci A (B ∪ D) ∅) :
    ci A B D := by
  have := hci.weakUnion hAB (Finset.disjoint_empty_right A) hAD
    (Finset.disjoint_empty_right B) hBD (Finset.disjoint_empty_left D) h
  rwa [Finset.empty_union] at this

/-- **`∅`-conditioning corollary of (C4)**: the converse assembly. Together with
`IsSemigraphoid.weakUnion_empty` and `IsSemigraphoid.decomposition_right` this is
`IsSemigraphoid.union_iff` at `C = ∅`. -/
theorem IsSemigraphoid.contraction_empty
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C4), p. 29
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the book's disjointness convention on the three nonempty blocks;
    -- Lauritzen §3.1
    (hAB : Disjoint A B) (hAD : Disjoint A D) (hBD : Disjoint B D)
    -- USER-INPUT: first premise; Lauritzen §3.1 (C4)
    (h₁ : ci A B D)
    -- USER-INPUT: second premise; Lauritzen §3.1 (C4)
    (h₂ : ci A D ∅) :
    ci A (B ∪ D) ∅ := by
  refine hci.contraction hAB (Finset.disjoint_empty_right A) hAD
    (Finset.disjoint_empty_right B) hBD (Finset.disjoint_empty_left D) ?_ h₂
  rwa [Finset.empty_union]

/-- **(C5) on the left factor**, via (C1). -/
theorem IsGraphoid.intersection_left
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C1)+(C5), pp. 29–30
    (hci : IsGraphoid ci)
    -- USER-INPUT: the book's disjointness convention on the four blocks; Lauritzen §3.1
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (hCD : Disjoint C D)
    -- USER-INPUT: first premise of intersection; Lauritzen §3.1 (C5)
    (h₁ : ci B A (C ∪ D))
    -- USER-INPUT: second premise of intersection; Lauritzen §3.1 (C5)
    (h₂ : ci D A (C ∪ B)) :
    ci (B ∪ D) A C := by
  have hACD : Disjoint A (C ∪ D) := Finset.disjoint_union_right.2 ⟨hAC, hAD⟩
  have hBCD : Disjoint B (C ∪ D) := Finset.disjoint_union_right.2 ⟨hBC, hBD⟩
  have hACB : Disjoint A (C ∪ B) := Finset.disjoint_union_right.2 ⟨hAC, hAB⟩
  have hDCB : Disjoint D (C ∪ B) := Finset.disjoint_union_right.2 ⟨hCD.symm, hBD.symm⟩
  have hABD : Disjoint A (B ∪ D) := Finset.disjoint_union_right.2 ⟨hAB, hAD⟩
  have hBDC : Disjoint (B ∪ D) C := Finset.disjoint_union_left.2 ⟨hBC, hCD.symm⟩
  -- (C1) on both premises, (C5), then (C1) back
  have h₁' : ci A B (C ∪ D) := hci.symm hAB.symm hBCD hACD h₁
  have h₂' : ci A D (C ∪ B) := hci.symm hAD.symm hDCB hACB h₂
  exact hci.symm hABD hAC hBDC (hci.intersection hAB hAC hAD hBC hBD hCD h₁' h₂')

/-- **(C5) verbatim** (Lauritzen p. 30): `X ⫫ Y ∣ Z` and `X ⫫ Z ∣ Y` imply `X ⫫ (Y, Z)`, for
pairwise disjoint `X, Y, Z`. -/
theorem IsGraphoid.intersection_empty
    -- USER-INPUT: the ambient calculus; Lauritzen §3.1 (C5), p. 30
    (hci : IsGraphoid ci)
    -- USER-INPUT: the book's disjointness convention on the triple; Lauritzen §3.1
    (hAB : Disjoint A B) (hAD : Disjoint A D) (hBD : Disjoint B D)
    -- USER-INPUT: `X ⫫ Y ∣ Z`; Lauritzen §3.1 (C5)
    (h₁ : ci A B D)
    -- USER-INPUT: `X ⫫ Z ∣ Y`; Lauritzen §3.1 (C5)
    (h₂ : ci A D B) :
    ci A (B ∪ D) ∅ := by
  refine hci.intersection hAB (Finset.disjoint_empty_right A) hAD
    (Finset.disjoint_empty_right B) hBD (Finset.disjoint_empty_left D) ?_ ?_
  · rwa [Finset.empty_union]
  · rwa [Finset.empty_union]

end StatLean.StatisticalModels.GraphicalModels
