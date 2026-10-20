module
public import StatLean.StatisticalModels.GraphicalModels.Core.Separation
public import StatLean.StatisticalModels.GraphicalModels.Core.Semigraphoid
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.List.TFAE

@[expose] public section

/-!
# The undirected Markov properties — pairwise, local, global

Lauritzen's three Markov properties of a probability law relative to an undirected graph `G`,
stated over an **abstract** conditional-independence relation
`ci : Finset V → Finset V → Finset V → Prop` (read `ci A B C` as `X_A ⫫ X_B ∣ X_C`):

* `IsPairwiseMarkov G ci` — (P): non-adjacent `i`, `j` are independent given everything else;
* `IsLocalMarkov G ci` — (L): a vertex is independent of the rest given its neighbourhood;
* `IsGlobalMarkov G ci` — (G): separated blocks are independent given the separator.

and the hierarchy (Lauritzen **Proposition 3.4**, p. 32): (G) ⇒ (L) ⇒ (P), plus its converse
under (C5) (Lauritzen **Theorem 3.7**, Pearl and Paz, p. 34).

* `separates_neighborFinset`, `separates_sdiff_pair` — the two purely graph-theoretic facts
  that carry (G) ⇒ (L) and (G) ⇒ (P): the neighbourhood of `v` separates `{v}` from the rest,
  and the complement of a non-adjacent pair separates the pair;
* `notMem_neighborFinset_of_not_adj`, `disjoint_singleton_neighborFinset_of_not_adj`,
  `disjoint_closedNeighborhood_sdiff`, `disjoint_pairNeighborhood_sdiff` — the disjointness
  obligations that `IsSemigraphoid`'s axioms and `IsGlobalMarkov` demand of their blocks,
  isolated as named lemmas rather than buried in a proof;
* `sdiff_closedNeighborhood_eq_union_far`, `neighborFinset_union_far_eq_sdiff_pair` — the two
  set identities that make the weak-union instantiation land on the nose;
* `globalMarkov_implies_localMarkov`, `localMarkov_implies_pairwiseMarkov`,
  `globalMarkov_implies_pairwiseMarkov` — Proposition 3.4;
* `pairwiseMarkov_implies_globalMarkov_of_nonempty` — Theorem 3.7 (Pearl–Paz), proved by the
  book's downward induction on the separator;
* `markov_tfae_of_nonempty` — Theorem 3.7 as a cycle, each property read on nonempty blocks.
  The statements `pairwiseMarkov_implies_globalMarkov` and `markov_tfae`, which quantified over
  *all* disjoint triples, were **false** and have been **deleted**;
  `not_forall_pairwiseMarkov_implies_globalMarkov` and `not_forall_markov_tfae` are the
  machine-checked counterexamples, kept. The gap is the empty-block regime only —
  `IsGlobalMarkov` demands `ci ∅ ∅ ∅` of every instance (via `separates_empty_left`) whereas
  `IsPairwiseMarkov` says nothing about empty blocks, and every semi-graphoid axiom is a
  `ci → ci` implication, so the empty relation `ci ≡ False` is a graphoid satisfying (P) but not
  (G). Lauritzen's own blocks are nonempty, which is why the book is unaffected; a model class
  whose relation *does* hold at empty blocks (as the Gaussian's does) recovers the full
  `IsGlobalMarkov` by supplying those cases directly.

**Why an abstract `ci`.** This is the book's own observation. Lauritzen remarks immediately
after Proposition 3.4 (p. 33) that the implications (G) ⇒ (L) ⇒ (P) "only depend on the
properties (C1)–(C4) of conditional independence and hence hold for any semi-graphoid", and
the remark after Theorem 3.7 says the same of that theorem for graphoids. Abstracting
therefore proves the hierarchy **once**, with the discrete-mass relation, the Gaussian
precision relation, and our general `CondIndep` each supplying an instance.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, 1996: the properties (P), (L), (G) are the **unnumbered** labelled
definitions on p. 32 (there is no "Definition 3.x" to cite); **Proposition 3.4** (p. 32,
with eq. (3.9)) is (G) ⇒ (L) ⇒ (P); condition **(3.10)** (p. 34) is the intersection property
(C5); **Theorem 3.7** (p. 34), credited to Pearl and Paz, is the converse under (3.10). The
justification for the abstract relation is the remark following Proposition 3.4 (p. 33)
(`Lauritzen §3.2` in tags).

**Proof formalization notes.** *Book vs Lean, four deliberate differences.*

1. **Disjointness is carried by `IsGlobalMarkov`, not by its consumers.** Lauritzen states (G)
   "for any triple `(A, B, S)` of **disjoint** subsets of `V`". We put the three `Disjoint`
   hypotheses into the definition, matching the book and matching the amended
   `IsSemigraphoid`, whose axiom fields likewise range over disjoint blocks. This makes (G) a
   *weaker* assertion, hence easier for a model class to supply and harder to consume — and
   both consumers here instantiate it at genuinely disjoint blocks, so nothing is lost:
   `{v}`, `V ∖ cl(v)`, `ne(v)` are pairwise disjoint, and so are `{i}`, `{j}`, `V ∖ {i, j}`.
   (P) and (L) need no such hypothesis: their blocks are disjoint by construction.
2. **(G) ⇒ (P) is proved directly, not through (L).** Lauritzen's Proposition 3.4 routes
   (G) ⇒ (L) ⇒ (P), where the second step needs weak union. But `V ∖ {i, j}` separates `{i}`
   from `{j}` outright when `i` and `j` are non-adjacent (`separates_sdiff_pair`), so
   `globalMarkov_implies_pairwiseMarkov` needs **no** `IsSemigraphoid` hypothesis at all. We
   state it in that hypothesis-free form rather than as the composite, per the project's
   minimal-hypothesis rule; the composite route remains available via
   `localMarkov_implies_pairwiseMarkov ∘ globalMarkov_implies_localMarkov`.
3. **`ne(v)` and `cl(v)` are `Finset`s.** Lauritzen's `bd(α)` (boundary) is `G.neighborFinset
   v` and his `cl(α)` (closure) is `insert v (G.neighborFinset v)`; `V ∖ cl(α)` is
   `Finset.univ \ insert v (G.neighborFinset v)`. This needs `[Fintype V]` and
   `[DecidableRel G.Adj]`; the book works with a finite variable set throughout.
4. **The weak-union instantiation.** (L) ⇒ (P) applies (C3) at `A = {i}`, `B = {j}`,
   `C = ne(i)`, `D = V ∖ ({i, j} ∪ ne(i))`. The four blocks are pairwise disjoint — `i ≠ j`;
   `i ∉ ne(i)` because a `SimpleGraph` is loopless; `j ∉ ne(i)` is *exactly* the non-adjacency
   hypothesis of (P); and `D` excludes all three by construction — and `{j} ∪ D = V ∖ cl(i)`,
   `ne(i) ∪ D = V ∖ {i, j}`. The four obligations are the named lemmas listed above, so the
   set algebra stays visible instead of hidden inside one large proof.

**Bibliographic comments.** The three Markov properties and their hierarchy are due to the
Markov-random-field literature of the 1970s (Hammersley–Clifford 1971 unpublished;
J. Besag, "Spatial interaction and the statistical analysis of lattice systems," *J. Roy.
Statist. Soc. Ser. B* **36** (1974), 192–236; F. Speed and H. Kiiveri). The converse under the
intersection property is J. Pearl and A. Paz, "Graphoids: a graph-based logic for reasoning
about relevance relations," in *Advances in Artificial Intelligence II*, North-Holland, 1987,
357–363 — Lauritzen's Theorem 3.7. That (P) alone does **not** imply (G) without (C5) is
Lauritzen's Example 3.10 (pp. 37–38, Moussouris).
-/

namespace StatLean.StatisticalModels.GraphicalModels

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  (ci : Finset V → Finset V → Finset V → Prop)

/-! ### The three Markov properties -/

/-- **(P) The pairwise Markov property** (Lauritzen p. 32, unnumbered): for every pair of
distinct non-adjacent vertices `i`, `j`, the relation holds for `{i}`, `{j}` conditionally on
all remaining vertices, `V ∖ {i, j}`.

*Edge behaviour.* The condition is vacuous on adjacent pairs and on `i = j`; the blocks
`{i}`, `{j}`, `V ∖ {i, j}` are pairwise disjoint whenever `i ≠ j`, so no disjointness
hypothesis is needed (contrast `IsGlobalMarkov`). Reading `ci A B C` as `X_A ⫫ X_B ∣ X_C`,
this is Lauritzen's `α ⫫ β ∣ V ∖ {α, β}`. -/
def IsPairwiseMarkov : Prop :=
  ∀ i j : V, i ≠ j → ¬ G.Adj i j → ci {i} {j} (Finset.univ \ {i, j})

/-- **(L) The local Markov property** (Lauritzen p. 32, unnumbered): every vertex `v` is
independent of the vertices outside its closure `cl(v) = {v} ∪ ne(v)`, conditionally on its
boundary `bd(v) = ne(v)`.

*Edge behaviour.* At an isolated vertex `ne(v) = ∅` this asserts unconditional independence of
`{v}` from `V ∖ {v}`; at a dominating vertex the "rest" block is empty and the condition is
whatever `ci A ∅ C` means for the instance — nothing here forces it to be trivially true. The
three blocks are pairwise disjoint by construction. -/
def IsLocalMarkov [DecidableRel G.Adj] : Prop :=
  ∀ v : V, ci {v} (Finset.univ \ insert v (G.neighborFinset v)) (G.neighborFinset v)

/-- **(G) The global Markov property** (Lauritzen p. 32, unnumbered): for every triple of
**disjoint** blocks `A`, `B`, `S` with `S` separating `A` from `B` in `G`, the relation holds
for `A`, `B` given `S`.

*Book vs Lean.* Lauritzen quantifies over disjoint triples, and so do we — the three
`Disjoint` hypotheses are part of the definition rather than of its consumers. This matches
the amended `IsSemigraphoid`, whose axiom fields also range over disjoint blocks, and keeps
(G) supplyable by model classes for which overlapping blocks would force degenerate
coordinates. *Edge behaviour.* Vacuously satisfiable content when `A` or `B` is empty is not
automatic: `Separates G S ∅ B` holds (`separates_empty_left`), so (G) demands `ci ∅ B S` of
every instance. -/
def IsGlobalMarkov : Prop :=
  ∀ A B S : Finset V, Disjoint A B → Disjoint A S → Disjoint B S →
    Separates G S A B → ci A B S

/-! ### Graph-side and set-algebra obligations

Everything in this section is graph theory or `Finset` algebra: no `ci` occurs. These are the
lemmas the hierarchy proofs need, kept named so the obligations stay visible. -/

/-- **The graph fact behind (G) ⇒ (P)**: for distinct non-adjacent `i`, `j`, the complement
`V ∖ {i, j}` separates `{i}` from `{j}`. A walk from `i` to `j` is non-`nil`; its second
vertex differs from `i` (looplessness) and from `j` (non-adjacency), so it lies in
`V ∖ {i, j}`. Stated outside the locally-finite section: no `[DecidableRel G.Adj]` is
involved, so `globalMarkov_implies_pairwiseMarkov` needs none either. -/
theorem separates_sdiff_pair (i j : V)
    -- USER-INPUT: distinctness of the pair; Lauritzen §3.2 (P), p. 32 (at `i = j` the `nil`
    -- walk defeats separation, so the hypothesis is genuinely needed)
    (hij : i ≠ j)
    -- USER-INPUT: the non-adjacency of the pair; Lauritzen §3.2 (P), p. 32
    (hadj : ¬ G.Adj i j) :
    Separates G (Finset.univ \ {i, j}) {i} {j} := by
  intro a ha b hb w
  rw [Finset.mem_singleton] at ha hb
  subst ha; subst hb
  cases w with
  | nil => exact absurd rfl hij
  | @cons _ x _ hax p =>
    refine ⟨x, ?_, ?_⟩
    · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨(G.ne_of_adj hax).symm, fun hxb => hadj (hxb ▸ hax)⟩
    · exact List.mem_cons_of_mem _ p.start_mem_support

section GraphSide

variable [DecidableRel G.Adj]

/-- A vertex not adjacent to `i` is not in `i`'s neighbourhood — the `Finset` reading of the
non-adjacency hypothesis of (P). -/
theorem notMem_neighborFinset_of_not_adj (i j : V)
    -- USER-INPUT: the non-adjacency of the pair; Lauritzen §3.2 (P), p. 32
    (hadj : ¬ G.Adj i j) :
    j ∉ G.neighborFinset i := by
  simpa using hadj

/-- **First disjointness obligation** of the weak-union instantiation: the block `{j}` is
disjoint from the conditioning block `ne(i)`. This is *precisely* the non-adjacency
hypothesis of (P) — it is the reason (L) ⇒ (P) works only at non-adjacent pairs. -/
theorem disjoint_singleton_neighborFinset_of_not_adj (i j : V)
    -- USER-INPUT: the non-adjacency of the pair; Lauritzen §3.2 (P), p. 32
    (hadj : ¬ G.Adj i j) :
    Disjoint ({j} : Finset V) (G.neighborFinset i) :=
  Finset.disjoint_singleton_left.mpr (notMem_neighborFinset_of_not_adj G i j hadj)

/-- **Second disjointness obligation**: the closure `cl(v) = {v} ∪ ne(v)` is disjoint from its
complement `V ∖ cl(v)`. Supplies the `Disjoint` arguments of `IsGlobalMarkov` at
`A = {v}`, `B = V ∖ cl(v)`, `S = ne(v)` after `Finset.disjoint_of_subset_left/right`. -/
theorem disjoint_closedNeighborhood_sdiff (v : V) :
    Disjoint (insert v (G.neighborFinset v)) (Finset.univ \ insert v (G.neighborFinset v)) :=
  Finset.disjoint_sdiff

/-- **Third disjointness obligation**: the block `{i, j} ∪ ne(i)` is disjoint from the "far"
block `D = V ∖ ({i, j} ∪ ne(i))`. Supplies, after `Finset.disjoint_of_subset_left`, all three
of `Disjoint {i} D`, `Disjoint {j} D` and `Disjoint (ne i) D` in the weak-union
instantiation. -/
theorem disjoint_pairNeighborhood_sdiff (i j : V) :
    Disjoint ({i, j} ∪ G.neighborFinset i)
      (Finset.univ \ ({i, j} ∪ G.neighborFinset i)) :=
  Finset.disjoint_sdiff

/-- **First set identity**: the "rest" block of (L) at `i` splits off `{j}`,
`V ∖ cl(i) = {j} ∪ D` with `D = V ∖ ({i, j} ∪ ne(i))`. This is the shape (C3) needs: the
union whose second summand is moved into the conditioning set. -/
theorem sdiff_closedNeighborhood_eq_union_far (i j : V)
    -- USER-INPUT: distinctness of the pair; Lauritzen §3.2 (P), p. 32 — needed so that
    -- `j ∉ cl(i)` on the `i` side
    (hij : i ≠ j)
    -- USER-INPUT: the non-adjacency of the pair; Lauritzen §3.2 (P), p. 32 — needed so that
    -- `j ∉ ne(i)`
    (hadj : ¬ G.Adj i j) :
    Finset.univ \ insert i (G.neighborFinset i)
      = {j} ∪ (Finset.univ \ ({i, j} ∪ G.neighborFinset i)) := by
  have hjn : j ∉ G.neighborFinset i := notMem_neighborFinset_of_not_adj G i j hadj
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · rintro ⟨hxi, hxn⟩
    by_cases hxj : x = j
    · exact Or.inl hxj
    · exact Or.inr ⟨⟨hxi, hxj⟩, hxn⟩
  · rintro (rfl | ⟨⟨hxi, _⟩, hxn⟩)
    · exact ⟨fun h => hij h.symm, hjn⟩
    · exact ⟨hxi, hxn⟩

/-- **Second set identity**: after weak union the conditioning set is `ne(i) ∪ D`, and that is
exactly `V ∖ {i, j}`, the conditioning set (P) asks for. Uses `i ∉ ne(i)` (a `SimpleGraph` is
loopless) and `j ∉ ne(i)` (non-adjacency). -/
theorem neighborFinset_union_far_eq_sdiff_pair (i j : V)
    -- USER-INPUT: the non-adjacency of the pair; Lauritzen §3.2 (P), p. 32 — needed so that
    -- `ne(i) ⊆ V ∖ {i, j}`
    (hadj : ¬ G.Adj i j) :
    G.neighborFinset i ∪ (Finset.univ \ ({i, j} ∪ G.neighborFinset i))
      = Finset.univ \ {i, j} := by
  have hjn : j ∉ G.neighborFinset i := notMem_neighborFinset_of_not_adj G i j hadj
  have hin : i ∉ G.neighborFinset i := G.notMem_neighborFinset_self i
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · rintro (hxn | ⟨hx, _⟩)
    · exact ⟨fun h => hin (h ▸ hxn), fun h => hjn (h ▸ hxn)⟩
    · exact hx
  · rintro ⟨hxi, hxj⟩
    by_cases hxn : x ∈ G.neighborFinset i
    · exact Or.inl hxn
    · exact Or.inr ⟨⟨hxi, hxj⟩, hxn⟩

/-- **The graph fact behind (G) ⇒ (L)**: the boundary `ne(v)` separates `{v}` from everything
outside the closure `cl(v)`. A walk leaving `v` and ending outside `cl(v)` is non-`nil`, so
its second vertex is a neighbour of `v` lying on it. -/
theorem separates_neighborFinset (v : V) :
    Separates G (G.neighborFinset v) {v} (Finset.univ \ insert v (G.neighborFinset v)) := by
  intro a ha b hb w
  rw [Finset.mem_singleton] at ha
  subst ha
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or] at hb
  cases w with
  | nil => exact absurd rfl hb.1
  | @cons _ x _ hax p =>
    exact ⟨x, by simpa using hax, List.mem_cons_of_mem _ p.start_mem_support⟩

end GraphSide

/-! ### Proposition 3.4 — the hierarchy (G) ⇒ (L) ⇒ (P) -/

variable {ci}

/-- **(G) ⇒ (L)** (Lauritzen Proposition 3.4, p. 32). Pure graph separation: instantiate (G)
at `A = {v}`, `B = V ∖ cl(v)`, `S = ne(v)`, which are pairwise disjoint and separated by the
boundary of `v`. **No** property of `ci` is used. -/
theorem globalMarkov_implies_localMarkov [DecidableRel G.Adj]
    -- USER-INPUT: the global Markov property of the law; Lauritzen §3.2 (G), p. 32
    (h : IsGlobalMarkov G ci) :
    IsLocalMarkov G ci := by
  intro v
  refine h {v} (Finset.univ \ insert v (G.neighborFinset v)) (G.neighborFinset v)
    (Finset.disjoint_of_subset_left (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
      (disjoint_closedNeighborhood_sdiff G v))
    (G.singleton_disjoint_neighborFinset v)
    ((Finset.disjoint_of_subset_left (Finset.subset_insert v (G.neighborFinset v))
      (disjoint_closedNeighborhood_sdiff G v)).symm)
    (separates_neighborFinset G v)

/-- **(L) ⇒ (P), with (L) used only where the "rest" block is nonempty** (Lauritzen
Proposition 3.4, p. 32, eq. (3.9)). The one step that needs the calculus: weak union (C3)
applied at `A = {i}`, `B = {j}`, `C = ne(i)`, `D = V ∖ ({i, j} ∪ ne(i))`, presenting the "rest"
block of (L) as `{j} ∪ D` and recognising `ne(i) ∪ D` as `V ∖ {i, j}`. The pairwise
disjointness that (C3) demands of its blocks comes from `i ≠ j`, from looplessness, and from
the non-adjacency of `i` and `j`.

The nonemptiness side condition on the hypothesis is **free at the point of use**: the rest
block `V ∖ cl(i)` is presented as `{j} ∪ D`, so it contains `j`. It is stated this way only so
that `markov_tfae_of_nonempty` — whose (L) is restricted to non-dominating vertices, the
empty-block regime being refuted by `not_forall_markov_tfae` — can use it;
`localMarkov_implies_pairwiseMarkov` is the corollary at the unrestricted (L). -/
theorem localMarkovNonempty_implies_pairwiseMarkov [DecidableRel G.Adj]
    -- USER-INPUT: the ambient conditional-independence calculus; Lauritzen §3.1 (C1)–(C4),
    -- p. 29, abstracted per the remark after Proposition 3.4, p. 33
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the local Markov property of the law, at every vertex that does not dominate
    -- the graph; Lauritzen §3.2 (L), p. 32
    (h : ∀ v : V, (Finset.univ \ insert v (G.neighborFinset v)).Nonempty →
      ci {v} (Finset.univ \ insert v (G.neighborFinset v)) (G.neighborFinset v)) :
    IsPairwiseMarkov G ci := by
  intro i j hij hadj
  -- the "far" block `D = V ∖ ({i, j} ∪ ne(i))`
  set D : Finset V := Finset.univ \ ({i, j} ∪ G.neighborFinset i) with hD
  have hfar : Disjoint ({i, j} ∪ G.neighborFinset i) D := disjoint_pairNeighborhood_sdiff G i j
  have hiD : Disjoint ({i} : Finset V) D :=
    Finset.disjoint_of_subset_left
      (Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ (Finset.mem_insert_self i {j})))
      hfar
  have hjD : Disjoint ({j} : Finset V) D :=
    Finset.disjoint_of_subset_left
      (Finset.singleton_subset_iff.mpr
        (Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))))
      hfar
  have hnD : Disjoint (G.neighborFinset i) D :=
    Finset.disjoint_of_subset_left Finset.subset_union_right hfar
  -- the rest block of (L) at `i` is `{j} ∪ D`, and in particular it contains `j`
  have hrest : Finset.univ \ insert i (G.neighborFinset i) = {j} ∪ D :=
    sdiff_closedNeighborhood_eq_union_far G i j hij hadj
  have hstart : ci {i} ({j} ∪ D) (G.neighborFinset i) := by
    have := h i (by rw [hrest]; exact ⟨j, Finset.mem_union_left _ (Finset.mem_singleton_self j)⟩)
    rwa [hrest] at this
  have := hci.weakUnion (Finset.disjoint_singleton.mpr hij)
    (G.singleton_disjoint_neighborFinset i) hiD
    (disjoint_singleton_neighborFinset_of_not_adj G i j hadj) hjD hnD hstart
  rwa [neighborFinset_union_far_eq_sdiff_pair G i j hadj] at this

/-- **(L) ⇒ (P)** (Lauritzen Proposition 3.4, p. 32, eq. (3.9)) — the corollary of
`localMarkovNonempty_implies_pairwiseMarkov` at the unrestricted local Markov property, where
the nonemptiness side condition is discharged by ignoring it. -/
theorem localMarkov_implies_pairwiseMarkov [DecidableRel G.Adj]
    -- USER-INPUT: the ambient conditional-independence calculus; Lauritzen §3.1 (C1)–(C4),
    -- p. 29, abstracted per the remark after Proposition 3.4, p. 33
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the local Markov property of the law; Lauritzen §3.2 (L), p. 32
    (h : IsLocalMarkov G ci) :
    IsPairwiseMarkov G ci :=
  localMarkovNonempty_implies_pairwiseMarkov G hci fun v _ => h v

/-- **(G) ⇒ (P)** (Lauritzen Proposition 3.4, p. 32). Stated **without** any property of `ci`:
`separates_sdiff_pair` gives the separation directly, so the composite route through (L) —
which would need weak union — is unnecessary. See the module docstring, note 2. -/
theorem globalMarkov_implies_pairwiseMarkov
    -- USER-INPUT: the global Markov property of the law; Lauritzen §3.2 (G), p. 32
    (h : IsGlobalMarkov G ci) :
    IsPairwiseMarkov G ci := by
  intro i j hij hadj
  refine h {i} {j} (Finset.univ \ {i, j}) (Finset.disjoint_singleton.mpr hij) ?_ ?_
    (separates_sdiff_pair G i j hij hadj)
  · exact Finset.disjoint_singleton_left.mpr (by simp)
  · exact Finset.disjoint_singleton_left.mpr (by simp)

/-! ### Theorem 3.7 (Pearl–Paz) — the converse under (C5)

The book's proof is a backward induction on `#(V ∖ (A ∪ B ∪ S))` that repeatedly applies (C5)
together with (C1)–(C4); it is the one place in this file where `IsGraphoid` rather than
`IsSemigraphoid` is required, and Lauritzen remarks (p. 34) that it "applies to any graphoid".

**The induction is carried out here in `pairwiseMarkov_implies_globalMarkov_of_nonempty`, which
is Theorem 3.7 restricted to nonempty `A` and `B`.** That restriction is not a shortcut: the
statement `pairwiseMarkov_implies_globalMarkov`, which quantifies over *all* disjoint
triples including empty blocks, is **false**, and
`not_forall_pairwiseMarkov_implies_globalMarkov` is a machine-checked counterexample. See that
declaration's docstring for the analysis; the short version is that `IsGlobalMarkov` demands
`ci ∅ ∅ ∅` of every instance (`separates_empty_left`) while `IsPairwiseMarkov` says nothing
whatever about empty blocks, and the semi-graphoid axioms cannot manufacture a first
`ci`-statement out of nothing. -/

/-- **(P) ⇒ (G) under the intersection property, on nonempty blocks** — Lauritzen
**Theorem 3.7** (p. 34), credited to Pearl and Paz; condition (3.10) of the book is exactly
`IsGraphoid.intersection`. This is the full mathematical content of Theorem 3.7; only the
degenerate empty-block regime, which the book excludes and which is genuinely unprovable
(`not_forall_pairwiseMarkov_implies_globalMarkov`), is missing relative to
`IsGlobalMarkov`.

**Proof.** Induction on `#(V ∖ S)`, i.e. downward induction on the separator, exactly as in the
book. Every step absorbs a nonempty block disjoint from `S` into the separator, so the measure
strictly drops. Four cases.

* `1 < #A`: pick `α ∈ A`. Then `S ∪ {α}` separates `A ∖ {α}` from `B` and `S ∪ (A ∖ {α})`
  separates `{α}` from `B` (both from the given separation, by monotonicity in the separator
  and in the separated block). The induction hypothesis gives
  `X_{A∖{α}} ⫫ X_B ∣ X_{S ∪ {α}}` and `X_{α} ⫫ X_B ∣ X_{S ∪ (A∖{α})}`; (C5) applied on the left
  factor `B` glues them to `X_B ⫫ X_A ∣ X_S`, and (C1) finishes.
* `1 < #B`: the mirror image, with (C5) applied directly (no (C1) needed).
* `A ∪ B ∪ S ≠ V`: pick `α` outside. Then `A ⫫ B ∣ S ∪ {α}` by induction, and **either**
  `S ∪ A` separates `{α}` from `B` **or** `S ∪ B` separates `{α}` from `A` — otherwise a walk
  from `A` to `α` avoiding `B ∪ S` concatenated with one from `α` to `B` avoiding `A ∪ S`
  would be an `S`-avoiding `A`–`B` walk (`Walk.reverse`, `Walk.append`,
  `Walk.mem_support_append_iff`). Either way (C5) then (C2) gives `A ⫫ B ∣ S`.
* otherwise `#A = #B = 1` and `A ∪ B ∪ S = V`, so `A = {a}`, `B = {b}`, `S = V ∖ {a, b}`, and
  `a`, `b` are non-adjacent (the one-edge walk `a–b` has support `[a, b]`, which misses `S`).
  This is (P) verbatim.

Note the empty-block regime cannot be patched by an extra case: it is the *base* of nothing —
see `not_forall_pairwiseMarkov_implies_globalMarkov`. -/
theorem pairwiseMarkov_implies_globalMarkov_of_nonempty
    -- USER-INPUT: the ambient calculus *with* intersection; Lauritzen §3.1 (C5), p. 30, and
    -- condition (3.10), p. 34
    (hci : IsGraphoid ci)
    -- USER-INPUT: the pairwise Markov property of the law; Lauritzen §3.2 (P), p. 32
    (h : IsPairwiseMarkov G ci) :
    ∀ A B S : Finset V, A.Nonempty → B.Nonempty → Disjoint A B → Disjoint A S → Disjoint B S →
      Separates G S A B → ci A B S := by
  -- the induction measure strictly drops when a nonempty block is absorbed into the separator
  have hmeas : ∀ T U : Finset V, U.Nonempty → Disjoint U T →
      (Finset.univ \ (T ∪ U)).card < (Finset.univ \ T).card := by
    intro T U hU hUT
    obtain ⟨u, hu⟩ := hU
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset
      (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.subset_union_left)).mpr
      ⟨u, ?_, ?_⟩)
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, Finset.disjoint_left.mp hUT hu⟩
    · exact fun hc => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union_right _ hu)
  have key : ∀ n : ℕ, ∀ A B S : Finset V, (Finset.univ \ S).card ≤ n →
      A.Nonempty → B.Nonempty → Disjoint A B → Disjoint A S → Disjoint B S →
      Separates G S A B → ci A B S := by
    intro n
    induction n with
    | zero =>
      -- `#(V ∖ S) = 0` forces `S = V`, contradicting `A` nonempty and disjoint from `S`
      intro A B S hcard hA _ _ hAS _ _
      obtain ⟨a, ha⟩ := hA
      have hmem : a ∈ Finset.univ \ S :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, Finset.disjoint_left.mp hAS ha⟩
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at hmem
      exact absurd hmem (Finset.notMem_empty a)
    | succ n ih =>
      intro A B S hcard hA hB hAB hAS hBS hsep
      -- the induction hypothesis, packaged at the enlarged separator `S ∪ U`
      have step : ∀ A' B' U : Finset V, A'.Nonempty → B'.Nonempty → U.Nonempty →
          Disjoint U S → Disjoint A' B' → Disjoint A' (S ∪ U) → Disjoint B' (S ∪ U) →
          Separates G (S ∪ U) A' B' → ci A' B' (S ∪ U) := fun A' B' U hA' hB' hU hUS =>
        ih A' B' (S ∪ U) (Nat.lt_succ_iff.mp (lt_of_lt_of_le (hmeas S U hU hUS) hcard)) hA' hB'
      by_cases hA2 : 1 < A.card
      · -- split the first block: `A = (A ∖ {α}) ∪ {α}`
        obtain ⟨α, hα⟩ := hA
        have hA'ne : (A.erase α).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hα]; omega
        have hA'sub : A.erase α ⊆ A := Finset.erase_subset _ _
        have hαA : ({α} : Finset V) ⊆ A := Finset.singleton_subset_iff.mpr hα
        have hA'α : Disjoint (A.erase α) ({α} : Finset V) :=
          Finset.disjoint_singleton_right.mpr (Finset.notMem_erase α A)
        have hA'S : Disjoint (A.erase α) S := Finset.disjoint_of_subset_left hA'sub hAS
        have hαS : Disjoint ({α} : Finset V) S := Finset.disjoint_of_subset_left hαA hAS
        have hSα : Disjoint S ({α} : Finset V) := hαS.symm
        have hA'B : Disjoint (A.erase α) B := Finset.disjoint_of_subset_left hA'sub hAB
        have hαB : Disjoint ({α} : Finset V) B := Finset.disjoint_of_subset_left hαA hAB
        have hBA' : Disjoint B (A.erase α) := hA'B.symm
        have hBα : Disjoint B ({α} : Finset V) := hαB.symm
        have dA'Sα : Disjoint (A.erase α) (S ∪ {α}) :=
          Finset.disjoint_union_right.mpr ⟨hA'S, hA'α⟩
        have dBSα : Disjoint B (S ∪ {α}) := Finset.disjoint_union_right.mpr ⟨hBS, hBα⟩
        have dαSA' : Disjoint ({α} : Finset V) (S ∪ A.erase α) :=
          Finset.disjoint_union_right.mpr ⟨hαS, hA'α.symm⟩
        have dBSA' : Disjoint B (S ∪ A.erase α) := Finset.disjoint_union_right.mpr ⟨hBS, hBA'⟩
        have h1 : ci (A.erase α) B (S ∪ {α}) :=
          step _ _ _ hA'ne hB (Finset.singleton_nonempty α) hαS hA'B dA'Sα dBSα
            (separates_mono_left G hA'sub (separates_of_subset_sep G Finset.subset_union_left hsep))
        have h2 : ci ({α} : Finset V) B (S ∪ A.erase α) :=
          step _ _ _ (Finset.singleton_nonempty α) hB hA'ne hA'S hαB dαSA' dBSA'
            (separates_mono_left G hαA (separates_of_subset_sep G Finset.subset_union_left hsep))
        have hunion : A.erase α ∪ ({α} : Finset V) = A := by
          rw [Finset.union_comm, Finset.singleton_union, Finset.insert_erase hα]
        have h3 := hci.intersection hBA' hBS hBα hA'S hA'α hSα
          (hci.symm hA'B dA'Sα dBSα h1) (hci.symm hαB dαSA' dBSA' h2)
        rw [hunion] at h3
        exact hci.symm hAB.symm hBS hAS h3
      · by_cases hB2 : 1 < B.card
        · -- split the second block: `B = (B ∖ {β}) ∪ {β}`
          obtain ⟨β, hβ⟩ := hB
          have hB'ne : (B.erase β).Nonempty := by
            rw [← Finset.card_pos, Finset.card_erase_of_mem hβ]; omega
          have hB'sub : B.erase β ⊆ B := Finset.erase_subset _ _
          have hβB : ({β} : Finset V) ⊆ B := Finset.singleton_subset_iff.mpr hβ
          have hB'β : Disjoint (B.erase β) ({β} : Finset V) :=
            Finset.disjoint_singleton_right.mpr (Finset.notMem_erase β B)
          have hB'S : Disjoint (B.erase β) S := Finset.disjoint_of_subset_left hB'sub hBS
          have hβS : Disjoint ({β} : Finset V) S := Finset.disjoint_of_subset_left hβB hBS
          have hSβ : Disjoint S ({β} : Finset V) := hβS.symm
          have hAB' : Disjoint A (B.erase β) := Finset.disjoint_of_subset_right hB'sub hAB
          have hAβ : Disjoint A ({β} : Finset V) := Finset.disjoint_of_subset_right hβB hAB
          have dASβ : Disjoint A (S ∪ {β}) := Finset.disjoint_union_right.mpr ⟨hAS, hAβ⟩
          have hunion : B.erase β ∪ ({β} : Finset V) = B := by
            rw [Finset.union_comm, Finset.singleton_union, Finset.insert_erase hβ]
          have h1 : ci A (B.erase β) (S ∪ {β}) :=
            step _ _ _ hA hB'ne (Finset.singleton_nonempty β) hβS hAB' dASβ
              (Finset.disjoint_union_right.mpr ⟨hB'S, hB'β⟩)
              (separates_mono_right G hB'sub
                (separates_of_subset_sep G Finset.subset_union_left hsep))
          have h2 : ci A ({β} : Finset V) (S ∪ B.erase β) :=
            step _ _ _ hA (Finset.singleton_nonempty β) hB'ne hB'S hAβ
              (Finset.disjoint_union_right.mpr ⟨hAS, hAB'⟩)
              (Finset.disjoint_union_right.mpr ⟨hβS, hB'β.symm⟩)
              (separates_mono_right G hβB
                (separates_of_subset_sep G Finset.subset_union_left hsep))
          have h3 := hci.intersection hAB' hAS hAβ hB'S hB'β hSβ h1 h2
          rwa [hunion] at h3
        · by_cases hfree : (Finset.univ \ (A ∪ B ∪ S)).Nonempty
          · -- a free vertex `α` outside `A ∪ B ∪ S`
            obtain ⟨α, hαfree⟩ := hfree
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
              not_or] at hαfree
            obtain ⟨⟨hαA, hαB⟩, hαS⟩ := hαfree
            have hSα : Disjoint S ({α} : Finset V) := Finset.disjoint_singleton_right.mpr hαS
            have hαSd : Disjoint ({α} : Finset V) S := hSα.symm
            have hAα : Disjoint A ({α} : Finset V) := Finset.disjoint_singleton_right.mpr hαA
            have hBα : Disjoint B ({α} : Finset V) := Finset.disjoint_singleton_right.mpr hαB
            have dASα : Disjoint A (S ∪ {α}) := Finset.disjoint_union_right.mpr ⟨hAS, hAα⟩
            have dBSα : Disjoint B (S ∪ {α}) := Finset.disjoint_union_right.mpr ⟨hBS, hBα⟩
            have hmain : ci A B (S ∪ {α}) :=
              step _ _ _ hA hB (Finset.singleton_nonempty α) hαSd hAB dASα dBSα
                (separates_of_subset_sep G Finset.subset_union_left hsep)
            by_cases hcase : Separates G (S ∪ A) ({α} : Finset V) B
            · have dαSA : Disjoint ({α} : Finset V) (S ∪ A) :=
                Finset.disjoint_union_right.mpr ⟨hαSd, hAα.symm⟩
              have dBSA : Disjoint B (S ∪ A) := Finset.disjoint_union_right.mpr ⟨hBS, hAB.symm⟩
              have hαBd : Disjoint ({α} : Finset V) B := Finset.disjoint_singleton_left.mpr hαB
              have h2 : ci ({α} : Finset V) B (S ∪ A) :=
                step _ _ _ (Finset.singleton_nonempty α) hB hA hAS hαBd dαSA dBSA hcase
              have h3 := hci.intersection hAB.symm hBS hBα hAS hAα hSα
                (hci.symm hAB dASα dBSα hmain) (hci.symm hαBd dαSA dBSA h2)
              exact hci.symm hAB.symm hBS hAS
                (hci.decomposition hAB.symm hBS hBα hAS hSα h3)
            · -- otherwise `S ∪ B` separates `{α}` from `A`: splice the two escaping walks
              have hcase2 : Separates G (S ∪ B) ({α} : Finset V) A := by
                simp only [Separates, not_forall] at hcase
                obtain ⟨a', ha', b, hb, w, hw⟩ := hcase
                rw [Finset.mem_singleton] at ha'
                subst ha'
                simp only [not_exists, not_and] at hw
                intro x hx a ha w'
                rw [Finset.mem_singleton] at hx
                subst hx
                obtain ⟨s, hsS, hsw⟩ := hsep a ha b hb (w'.reverse.append w)
                rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
                  List.mem_reverse] at hsw
                rcases hsw with hsw | hsw
                · exact ⟨s, Finset.mem_union_left _ hsS, hsw⟩
                · exact absurd hsw (hw s (Finset.mem_union_left _ hsS))
              have dαSB : Disjoint ({α} : Finset V) (S ∪ B) :=
                Finset.disjoint_union_right.mpr ⟨hαSd, hBα.symm⟩
              have dASB : Disjoint A (S ∪ B) := Finset.disjoint_union_right.mpr ⟨hAS, hAB⟩
              have hαAd : Disjoint ({α} : Finset V) A := Finset.disjoint_singleton_left.mpr hαA
              have h2 : ci ({α} : Finset V) A (S ∪ B) :=
                step _ _ _ (Finset.singleton_nonempty α) hA hB hBS hαAd dαSB dASB hcase2
              have h3 := hci.intersection hAB hAS hAα hBS hBα hSα hmain
                (hci.symm hαAd dαSB dASB h2)
              exact hci.decomposition hAB hAS hAα hBS hSα h3
          · -- base case: `A = {a}`, `B = {b}`, `S = V ∖ {a, b}`; apply (P) verbatim
            rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hfree
            obtain ⟨a, rfl⟩ :=
              Finset.card_eq_one.mp (le_antisymm (not_lt.mp hA2) (Finset.card_pos.mpr hA))
            obtain ⟨b, rfl⟩ :=
              Finset.card_eq_one.mp (le_antisymm (not_lt.mp hB2) (Finset.card_pos.mpr hB))
            have hab : a ≠ b := Finset.disjoint_singleton.mp hAB
            have haS : a ∉ S := Finset.disjoint_left.mp hAS (Finset.mem_singleton_self a)
            have hbS : b ∉ S := Finset.disjoint_left.mp hBS (Finset.mem_singleton_self b)
            have hSeq : S = Finset.univ \ {a, b} := by
              ext x
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
                Finset.mem_singleton, not_or]
              constructor
              · intro hxS
                exact ⟨fun hxa => haS (hxa ▸ hxS), fun hxb => hbS (hxb ▸ hxS)⟩
              · rintro ⟨hxa, hxb⟩
                have hx := hfree (Finset.mem_univ x)
                simp only [Finset.mem_union, Finset.mem_singleton] at hx
                tauto
            have hnadj : ¬ G.Adj a b := by
              intro hadj
              obtain ⟨s, hsS, hsw⟩ := hsep a (Finset.mem_singleton_self a) b
                (Finset.mem_singleton_self b) (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
              simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
                List.mem_cons, List.not_mem_nil, or_false] at hsw
              rcases hsw with rfl | rfl
              · exact haS hsS
              · exact hbS hsS
            rw [hSeq]
            exact h a b hab hnadj
  exact fun A B S => key ((Finset.univ \ S).card) A B S le_rfl

/-- **The deleted `pairwiseMarkov_implies_globalMarkov` is false — machine-checked
counterexample.** Take `V = Fin 1`, `G = ⊥`, and the everywhere-false relation
`ci A B C := False`.

* `ci` is a **graphoid**: every field of `IsSemigraphoid`/`IsGraphoid` is an implication whose
  premises include a `ci`-statement, hence is vacuously true for the empty relation.
* `IsPairwiseMarkov ⊥ ci` **holds**: `Fin 1` is a subsingleton, so the hypothesis `i ≠ j` is
  never satisfiable and (P) is vacuous. (Any graph with no distinct non-adjacent pair works —
  a complete graph on any `V` does equally well.)
* `IsGlobalMarkov ⊥ ci` **fails**: `separates_empty_left` gives `Separates G ∅ ∅ ∅`, and the
  three `Disjoint` obligations are trivial at `∅`, so (G) demands `ci ∅ ∅ ∅`, i.e. `False`.

The obstruction is exactly the empty-block regime the module docstring already flags under
`IsGlobalMarkov`'s *edge behaviour*: (G) as stated asserts something at empty blocks, (P)
asserts nothing there, and no semi-graphoid axiom can produce a first `ci`-statement out of
nothing (all five are `ci → ci` implications). It is **not** a defect of the induction: the
whole of Lauritzen's Theorem 3.7 is proved above in
`pairwiseMarkov_implies_globalMarkov_of_nonempty`, and Lauritzen's own blocks are nonempty by
the standing convention of §3.2. Two ways to repair the statement: add
`A.Nonempty`/`B.Nonempty` to `IsGlobalMarkov` (matching the book), or make `IsGlobalMarkov`
demand nothing at empty blocks. -/
theorem not_forall_pairwiseMarkov_implies_globalMarkov :
    ¬ ∀ (c : Finset (Fin 1) → Finset (Fin 1) → Finset (Fin 1) → Prop),
        IsGraphoid c → IsPairwiseMarkov (⊥ : SimpleGraph (Fin 1)) c →
        IsGlobalMarkov (⊥ : SimpleGraph (Fin 1)) c := fun hcontra =>
  hcontra (fun _ _ _ => False)
    { symm := fun _ _ _ hf => hf
      decomposition := fun _ _ _ _ _ hf => hf
      weakUnion := fun _ _ _ _ _ _ hf => hf
      contraction := fun _ _ _ _ _ _ hf _ => hf
      intersection := fun _ _ _ _ _ _ hf _ => hf }
    (fun i j hij _ => hij (Subsingleton.elim i j))
    ∅ ∅ ∅ (by simp) (by simp) (by simp) (separates_empty_left _)

/-- **The deleted `markov_tfae` is false** — same witness as
`not_forall_pairwiseMarkov_implies_globalMarkov`. The forward implications (G) ⇒ (L) ⇒ (P) do
hold (they are proved above); it is the closing implication (P) ⇒ (G) that the TFAE asserts and
that fails at empty blocks. -/
theorem not_forall_markov_tfae :
    ¬ ∀ (c : Finset (Fin 1) → Finset (Fin 1) → Finset (Fin 1) → Prop), IsGraphoid c →
        [IsGlobalMarkov (⊥ : SimpleGraph (Fin 1)) c, IsLocalMarkov (⊥ : SimpleGraph (Fin 1)) c,
          IsPairwiseMarkov (⊥ : SimpleGraph (Fin 1)) c].TFAE := by
  intro hcontra
  refine not_forall_pairwiseMarkov_implies_globalMarkov fun c hc hP => ?_
  exact ((hcontra c hc).out 2 0).mp hP

/-! ### Theorem 3.7 over *all* blocks — deleted, and why

There used to be two more declarations here:

```
theorem pairwiseMarkov_implies_globalMarkov (hci : IsGraphoid ci) (h : IsPairwiseMarkov G ci) :
    IsGlobalMarkov G ci

theorem markov_tfae [DecidableRel G.Adj] (hci : IsGraphoid ci) :
    [IsGlobalMarkov G ci, IsLocalMarkov G ci, IsPairwiseMarkov G ci].TFAE
```

**Both are false, and have been deleted.** The refutations are machine-checked and are kept
above:
`not_forall_pairwiseMarkov_implies_globalMarkov` and `not_forall_markov_tfae`, both witnessed by
`V = Fin 1`, `G = ⊥`, `ci ≡ False`.

*Where the gap is, and where it is not.* `IsGlobalMarkov` demands `ci ∅ ∅ ∅` of every instance
(`separates_empty_left` gives `Separates G ∅ ∅ ∅`, and the three `Disjoint` obligations are
trivial at `∅`), whereas `IsPairwiseMarkov` says nothing whatever about empty blocks and every
semi-graphoid axiom is a `ci → ci` implication — so the empty relation is a graphoid satisfying
(P) but not (G). The gap is **only** the empty-block regime: Lauritzen's own blocks are
nonempty, and the whole mathematical content of Theorem 3.7 is proved above in
`pairwiseMarkov_implies_globalMarkov_of_nonempty`. The two forward implications that
`markov_tfae` also contained, (G) ⇒ (L) and (L) ⇒ (P), are `globalMarkov_implies_localMarkov`
and `localMarkov_implies_pairwiseMarkov`, likewise proved above.

*The replacements.* `markov_tfae_of_nonempty` below is the cycle over the three properties each
read on nonempty blocks — no extra hypotheses. A model class that can also discharge the
degenerate blocks directly (the Gaussian can: see
`Core.Coordinates.CondIndepCoords.of_isEmpty_left`) gets the full `IsGlobalMarkov` by combining
that with `pairwiseMarkov_implies_globalMarkov_of_nonempty`. -/

/-- **The three Markov properties coincide over a graphoid, on nonempty blocks** — Lauritzen
**Theorem 3.7** (p. 34, Pearl and Paz), the repaired form of the deleted `markov_tfae`.

Each of the three properties is read on the blocks the book actually uses:

1. (G) on **nonempty** `A`, `B` — `IsGlobalMarkov` with `A.Nonempty`, `B.Nonempty` added, i.e.
   the conclusion of `pairwiseMarkov_implies_globalMarkov_of_nonempty`;
2. (L) at those vertices whose closure is not all of `V` — `IsLocalMarkov` with the "rest"
   block required nonempty;
3. (P) verbatim: its blocks `{i}`, `{j}` are nonempty by construction, so nothing is restricted.

The restriction in (1) and (2) is exactly the empty-block regime refuted by
`not_forall_markov_tfae`, and nothing more. Consumers holding the *unrestricted*
`IsGlobalMarkov`/`IsLocalMarkov` get (1)/(2) for free by dropping the extra hypothesis. -/
theorem markov_tfae_of_nonempty [DecidableRel G.Adj]
    -- USER-INPUT: the ambient calculus *with* intersection; Lauritzen §3.1 (C5), p. 30, and
    -- condition (3.10), p. 34
    (hci : IsGraphoid ci) :
    [∀ A B S : Finset V, A.Nonempty → B.Nonempty → Disjoint A B → Disjoint A S → Disjoint B S →
        Separates G S A B → ci A B S,
      ∀ v : V, (Finset.univ \ insert v (G.neighborFinset v)).Nonempty →
        ci {v} (Finset.univ \ insert v (G.neighborFinset v)) (G.neighborFinset v),
      IsPairwiseMarkov G ci].TFAE := by
  tfae_have 1 → 2 := by
    intro h v hv
    exact h {v} (Finset.univ \ insert v (G.neighborFinset v)) (G.neighborFinset v)
      (Finset.singleton_nonempty v) hv
      (Finset.disjoint_of_subset_left (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
        (disjoint_closedNeighborhood_sdiff G v))
      (G.singleton_disjoint_neighborFinset v)
      ((Finset.disjoint_of_subset_left (Finset.subset_insert v (G.neighborFinset v))
        (disjoint_closedNeighborhood_sdiff G v)).symm)
      (separates_neighborFinset G v)
  tfae_have 2 → 3 := localMarkovNonempty_implies_pairwiseMarkov G hci.toIsSemigraphoid
  tfae_have 3 → 1 := pairwiseMarkov_implies_globalMarkov_of_nonempty G hci
  tfae_finish

end StatLean.StatisticalModels.GraphicalModels
