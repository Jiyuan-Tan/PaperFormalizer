module
public import StatLean.StatisticalModels.GraphicalModels.Directed.DAG
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

/-!
# Moralization — the undirected graph `G^m` of a directed acyclic graph

Lauritzen's *moral graph* (§2.1.1, p. 7, unnumbered): marry the parents — join every pair of
vertices with a common child — and then drop the directions. The result is an **undirected**
graph, so the undirected vocabulary (`Core.Separation.Separates`,
`Undirected.Markov.IsGlobalMarkov`, `Discrete.Factorization.FactorizesOver`) applies to a
directed model, and the directed theorems are proved by **transport** to `G^m` rather than by a
parallel directed development.

* `DAG.moralRel` — the relation "edge, or common child", the input to `SimpleGraph.fromRel`;
* `DAG.moralGraph` — the moral graph `G^m`, with its adjacency characterisation
  `DAG.moralGraph_adj` and a `DecidableRel` instance (needed because `IsLocalMarkov`,
  `completeSubsets` and `neighborFinset` all demand one);
* `DAG.skeleton` — the underlying undirected graph obtained by dropping directions **only**, and
  `DAG.skeleton_le_moralGraph`: moralization only adds edges;
* `DAG.moralGraph_adj_of_adj` — an edge of the DAG survives moralization;
  `DAG.moralGraph_adj_of_common_child`, `DAG.moralGraph_adj_of_mem_parents` — two parents of a
  common child become adjacent;
* `DAG.isClique_insert_parents` — the *family* `fa(v) = {v} ∪ pa(v)` is complete in `G^m`. This
  is the ingredient of Lauritzen's Lemma 3.21 (p. 47): a recursive factorization is a product of
  factors supported on the sets `fa(v)`, each of which is a clique of `G^m`, hence a
  factorization over `G^m` in the sense of `Discrete.Factorization.FactorizesOver`;
* `DAG.moralGraph_mono` — monotonicity in the DAG;
* `DAG.moralGraph_induce_adj`, `DAG.moralGraph_induce_le`,
  `DAG.isClique_insert_parents_induce` — moralization of the sub-DAG induced on a block, i.e.
  `(G_A)^m`. Lauritzen's Corollary 3.23 and Proposition 3.25 are stated at
  `A = An(A ∪ B ∪ S)`, so `(G_{An(A∪B∪S)})^m` is *the* object of interest.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996**, §2.1.1, p. 7: the moral graph `G^m` of a directed acyclic
graph `G` is obtained "by first *marrying the parents*, i.e. adding undirected edges between
unmarried parents with a common child, and then dropping directions". This is an **unnumbered**
definition — there is no "Definition 2.x" to cite. The uses this file is built for are
**Lemma 3.21** and **Corollary 3.23** (p. 47, a recursive factorization factorizes over the
moral graph, hence property (DG)) and **Proposition 3.25** (p. 48, d-separation is separation in
`(G_{An(A∪B∪S)})^m`); the notation `An(·)` and `G_A` is §2.1.1, p. 7
(`Lauritzen §2.1.1` in tags).

**Proof formalization notes.** *Book vs Lean, four deliberate differences.*

1. **"Unmarried parents" versus all parents.** Lauritzen adds edges between parents that are
   *not already adjacent*; we take the union of the edge relation with the common-child relation
   in one step. The two graphs are identical — adding an edge that is already present is a
   no-op — and the one-step form is the input `SimpleGraph.fromRel` takes.
2. **`SimpleGraph.fromRel` supplies symmetry and looplessness.** `fromRel r` has
   `Adj a b ↔ a ≠ b ∧ (r a b ∨ r b a)`, which is exactly "symmetrize, then delete the
   diagonal". Deleting the diagonal is faithful, not a repair: the marriage relation is between
   *pairs* of parents, so a vertex is never married to itself, and `D.Adj u u` is impossible in
   a DAG anyway (`DAG.irrefl`).
3. **`(G_A)^m` is not `G^m` restricted to `A`, and the order of operations matters.** Two
   vertices of `A` whose only common child lies *outside* `A` are married in `G^m` but not in
   `(G_A)^m`. `DAG.moralGraph_induce_adj` makes the difference visible (the witness `w` is
   quantified over `A`), and `DAG.moralGraph_induce_le` records that only the one inclusion
   holds. This is precisely why Lauritzen restricts to an ancestral set *before* moralizing in
   Corollary 3.23 — and why `DAG.parents_induce_of_isAncestralSet` (in `Directed.DAG`) is the
   load-bearing lemma: on an ancestral set the parent sets, hence the families `fa(v)` and hence
   the clique structure of `DAG.isClique_insert_parents_induce`, are unchanged.
4. **Vertices outside `A` survive as isolated points.** Since `DAG.induce` keeps the vertex type
   `V` fixed (see `Directed.DAG`, note 5), so does `(G_A)^m`: `DAG.moralGraph_induce_adj` shows
   every edge of it has both endpoints in `A`. Separation statements about blocks inside `A` are
   therefore unaffected, and `Separates`, `IsGlobalMarkov` and the clique vocabulary apply
   without any subtype transport.

**Bibliographic comments.** Moralization is due to S. L. Lauritzen and D. J. Spiegelhalter,
"Local computations with probabilities on graphical structures and their application to expert
systems," *J. Roy. Statist. Soc. Ser. B* **50** (1988), 157–224, where it is the first step of
the junction-tree construction; the equivalence of d-separation (J. Pearl, *Probabilistic
Reasoning in Intelligent Systems*, Morgan Kaufmann, 1988) with separation in the moralized
ancestral subgraph is Lauritzen's Proposition 3.25, and is the reason this file exists.
-/

namespace StatLean.StatisticalModels.GraphicalModels

variable {V : Type*}

namespace DAG

/-! ### The moral graph -/

/-- The relation moralization symmetrizes: `u` is either a **parent** of `v`, or a **co-parent**
of `v` — the two share a child. Feeding this to `SimpleGraph.fromRel` performs the book's two
steps ("marry the parents", "drop directions") at once.

*Edge behaviour.* `moralRel D v v` may hold (a vertex with a child is trivially its own
co-parent); the diagonal is deleted by `SimpleGraph.fromRel`, which is faithful to the book
since marriage is a relation between *pairs* of parents. -/
def moralRel (D : DAG V) (u v : V) : Prop :=
  D.Adj u v ∨ ∃ w : V, D.Adj u w ∧ D.Adj v w

/-- The marriage relation is decidable on a finite vertex set: the common child is an existential
over `V`, discharged by `Fintype.decidableExistsFintype`. -/
instance instDecidableRelMoralRel [Fintype V] (D : DAG V) [DecidableRel D.Adj] :
    DecidableRel D.moralRel := fun u v =>
  inferInstanceAs (Decidable (D.Adj u v ∨ ∃ w : V, D.Adj u w ∧ D.Adj v w))

/-- The **moral graph** `G^m` of a directed acyclic graph (Lauritzen §2.1.1, p. 7, unnumbered):
join every pair of vertices sharing a child ("marry the parents"), then drop the directions.

Built through `SimpleGraph.fromRel`, so the result is a genuine `SimpleGraph V` — symmetric and
loopless by construction — and the undirected vocabulary (`Separates`, the three Markov
properties, clique factorization) applies to it. The directed theorems of Lauritzen §3.2.2 are
proved by moving to `G^m`, not by redeveloping separation for directed graphs.

*Edge behaviour.* Moralization only adds edges (`DAG.skeleton_le_moralGraph`); it is idempotent
in the informal sense that marrying already-adjacent parents changes nothing (module docstring,
note 1). On a DAG with no vertex having two distinct parents, `G^m` is exactly the skeleton. -/
def moralGraph (D : DAG V) : SimpleGraph V :=
  SimpleGraph.fromRel D.moralRel

/-- Adjacency in `G^m` is decidable — required, not optional: `Undirected.Markov.IsLocalMarkov`,
`Discrete.Factorization.completeSubsets` and `SimpleGraph.neighborFinset` all carry a
`[DecidableRel G.Adj]` binder, so without this instance none of them could be instantiated at the
moral graph. Inherited from `SimpleGraph.fromRel`'s own instance. -/
instance instDecidableRelMoralGraphAdj [Fintype V] [DecidableEq V] (D : DAG V)
    [DecidableRel D.Adj] : DecidableRel D.moralGraph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel D.moralRel).Adj)

/-- **Adjacency in `G^m`, unfolded to `SimpleGraph.fromRel`'s shape.** True by `rfl`; the usable
characterisation is `DAG.moralGraph_adj`. -/
theorem moralGraph_adj_iff (D : DAG V) (u v : V) :
    D.moralGraph.Adj u v ↔ u ≠ v ∧ (D.moralRel u v ∨ D.moralRel v u) := Iff.rfl

/-- **Adjacency in the moral graph** (Lauritzen §2.1.1, p. 7): distinct `u` and `v` are adjacent
in `G^m` exactly when there is an edge between them in either direction, or they have a common
child. The two co-parent disjuncts of `DAG.moralGraph_adj_iff` collapse into one because the
common-child relation is already symmetric. -/
theorem moralGraph_adj (D : DAG V) (u v : V) :
    D.moralGraph.Adj u v ↔
      u ≠ v ∧ (D.Adj u v ∨ D.Adj v u ∨ ∃ w : V, D.Adj u w ∧ D.Adj v w) := by
  rw [moralGraph_adj_iff]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ((h | ⟨w, hw₁, hw₂⟩) | (h | ⟨w, hw₁, hw₂⟩))
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨w, hw₁, hw₂⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨w, hw₂, hw₁⟩)
  · rintro (h | h | ⟨w, hw₁, hw₂⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr ⟨w, hw₁, hw₂⟩)

/-- **An edge of the DAG survives moralization** — "dropping directions" keeps every edge. The
distinctness side condition is free: `DAG.ne_of_adj`. -/
theorem moralGraph_adj_of_adj {D : DAG V} {u v : V}
    -- USER-INPUT: the directed edge; Lauritzen §2.1.1, p. 5
    (h : D.Adj u v) :
    D.moralGraph.Adj u v :=
  (moralGraph_adj D u v).2 ⟨D.ne_of_adj h, Or.inl h⟩

/-- **Two parents of a common child are adjacent in `G^m`** — the "marry the parents" step
(Lauritzen §2.1.1, p. 7). The distinctness hypothesis is genuine: a single parent is not married
to itself, and `SimpleGraph` has no loops. -/
theorem moralGraph_adj_of_common_child {D : DAG V} {u v w : V}
    -- USER-INPUT: the two parents are distinct; Lauritzen §2.1.1, p. 7 (marriage is a relation
    -- between *pairs* of parents; without it the conclusion is a loop, which no `SimpleGraph`
    -- has)
    (huv : u ≠ v)
    -- USER-INPUT: the first parent edge; Lauritzen §2.1.1, p. 7
    (hu : D.Adj u w)
    -- USER-INPUT: the second parent edge; Lauritzen §2.1.1, p. 7
    (hv : D.Adj v w) :
    D.moralGraph.Adj u v :=
  (moralGraph_adj D u v).2 ⟨huv, Or.inr (Or.inr ⟨w, hu, hv⟩)⟩

/-- `DAG.moralGraph_adj_of_common_child` in the `Finset` vocabulary of `DAG.parents`. -/
theorem moralGraph_adj_of_mem_parents [Fintype V] {D : DAG V} [DecidableRel D.Adj] {u v w : V}
    -- USER-INPUT: the two parents are distinct; Lauritzen §2.1.1, p. 7
    (huv : u ≠ v)
    -- USER-INPUT: the first vertex is a parent of `w`; Lauritzen §2.1.1, p. 7
    (hu : u ∈ D.parents w)
    -- USER-INPUT: the second vertex is a parent of `w`; Lauritzen §2.1.1, p. 7
    (hv : v ∈ D.parents w) :
    D.moralGraph.Adj u v :=
  moralGraph_adj_of_common_child huv (mem_parents.1 hu) (mem_parents.1 hv)

/-- **The family `fa(v) = {v} ∪ pa(v)` is complete in `G^m`** (Lauritzen §2.1.1, p. 7, and the
key step of Lemma 3.21, p. 47). Two distinct parents are married; a parent and the child are
joined by the surviving directed edge. This is the lemma that turns a recursive factorization —
a product of factors each supported on some `fa(v)` — into a factorization over the cliques of
the moral graph, i.e. into `Discrete.Factorization.FactorizesOver D.moralGraph`. -/
theorem isClique_insert_parents [Fintype V] [DecidableEq V] (D : DAG V) [DecidableRel D.Adj]
    (v : V) :
    D.moralGraph.IsClique ((insert v (D.parents v) : Finset V) : Set V) := by
  intro a ha b hb hab
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, mem_parents] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact (moralGraph_adj_of_adj hb).symm
  · rcases hb with rfl | hb
    · exact moralGraph_adj_of_adj ha
    · exact moralGraph_adj_of_common_child hab ha hb

/-- **Monotonicity**: adding edges to the DAG only adds edges to its moral graph — both the
surviving directed edges and the marriages are monotone in the edge relation. Stated as an
implication between adjacency relations because `DAG` carries no order of its own (unlike
`SimpleGraph`, whose lattice we use for the conclusion). -/
theorem moralGraph_mono {D₁ D₂ : DAG V}
    -- USER-INPUT: the edge inclusion; free choice of the caller (the instance we need is
    -- `D.induce A ≤ D`, Lauritzen §2.1.1, p. 7)
    (h : ∀ u v : V, D₁.Adj u v → D₂.Adj u v) :
    D₁.moralGraph ≤ D₂.moralGraph := by
  rw [SimpleGraph.le_iff_adj]
  intro a b hab
  rw [moralGraph_adj] at hab ⊢
  obtain ⟨hne, hd⟩ := hab
  refine ⟨hne, ?_⟩
  rcases hd with hd | hd | ⟨w, hw₁, hw₂⟩
  · exact Or.inl (h a b hd)
  · exact Or.inr (Or.inl (h b a hd))
  · exact Or.inr (Or.inr ⟨w, h a w hw₁, h b w hw₂⟩)

/-! ### The undirected skeleton

The "drop directions" half of moralization on its own. -/

/-- The **skeleton** of a DAG: forget the orientations, keep no other edge. Not Lauritzen's moral
graph — the marriages are missing — but the natural reference point for it
(`DAG.skeleton_le_moralGraph`), and the graph Lauritzen's *unmarried* parents are unmarried in.
-/
def skeleton (D : DAG V) : SimpleGraph V :=
  SimpleGraph.fromRel D.Adj

theorem skeleton_adj (D : DAG V) (u v : V) :
    D.skeleton.Adj u v ↔ u ≠ v ∧ (D.Adj u v ∨ D.Adj v u) := Iff.rfl

/-- **Moralization only adds edges.** -/
theorem skeleton_le_moralGraph (D : DAG V) : D.skeleton ≤ D.moralGraph := by
  rw [SimpleGraph.le_iff_adj]
  intro a b hab
  rw [skeleton_adj] at hab
  rw [moralGraph_adj]
  exact ⟨hab.1, hab.2.imp id Or.inl⟩

/-! ### The moral graph of an induced sub-DAG — `(G_A)^m`

The object Lauritzen's Corollary 3.23 and Proposition 3.25 are stated at, with
`A = An(A ∪ B ∪ S)`. See the module docstring, note 3: this is **not** the restriction of `G^m`
to `A`, and the difference is exactly why the book moralizes *after* restricting. -/

section Induce

variable [Fintype V] [DecidableEq V]

/-- **Adjacency in `(G_A)^m`**: both endpoints lie in `A`, and the witness of a marriage must
itself lie in `A`. Contrast `DAG.moralGraph_adj`, where the common child ranges over all of `V` —
this is the whole content of the module docstring's note 3. -/
theorem moralGraph_induce_adj (D : DAG V) (A : Finset V) (u v : V) :
    (D.induce A).moralGraph.Adj u v ↔
      u ≠ v ∧ u ∈ A ∧ v ∈ A ∧
        (D.Adj u v ∨ D.Adj v u ∨ ∃ w ∈ A, D.Adj u w ∧ D.Adj v w) := by
  rw [moralGraph_adj]
  simp only [induce_adj]
  constructor
  · rintro ⟨hne, ⟨hu, hv, huv⟩ | ⟨hv, hu, hvu⟩ | ⟨w, ⟨hu, hw, huw⟩, hv, -, hvw⟩⟩
    · exact ⟨hne, hu, hv, Or.inl huv⟩
    · exact ⟨hne, hu, hv, Or.inr (Or.inl hvu)⟩
    · exact ⟨hne, hu, hv, Or.inr (Or.inr ⟨w, hw, huw, hvw⟩)⟩
  · rintro ⟨hne, hu, hv, huv | hvu | ⟨w, hw, huw, hvw⟩⟩
    · exact ⟨hne, Or.inl ⟨hu, hv, huv⟩⟩
    · exact ⟨hne, Or.inr (Or.inl ⟨hv, hu, hvu⟩)⟩
    · exact ⟨hne, Or.inr (Or.inr ⟨w, ⟨hu, hw, huw⟩, hv, hw, hvw⟩)⟩

/-- Every edge of `(G_A)^m` has both endpoints in `A` — the vertices outside `A`, which
`DAG.induce` keeps as isolated points, take part in no walk of the moralized restriction, so
`Separates` on `(G_A)^m` sees exactly the book's vertex-deleted `G_A`. -/
theorem mem_of_moralGraph_induce_adj {D : DAG V} {A : Finset V} {u v : V}
    -- USER-INPUT: the edge of the moralized restriction; Lauritzen §2.1.1, p. 7
    (h : (D.induce A).moralGraph.Adj u v) :
    u ∈ A ∧ v ∈ A :=
  let h' := (moralGraph_induce_adj D A u v).1 h
  ⟨h'.2.1, h'.2.2.1⟩

/-- **Only one inclusion holds**: `(G_A)^m ≤ G^m`. The reverse fails — two vertices of `A` whose
only common child lies outside `A` are married in `G^m` but not in `(G_A)^m` — which is why
Lauritzen restricts to an *ancestral* set before moralizing. Corollary of `DAG.moralGraph_mono`
applied to `DAG.adj_of_induce_adj`. -/
theorem moralGraph_induce_le (D : DAG V) (A : Finset V) :
    (D.induce A).moralGraph ≤ D.moralGraph :=
  moralGraph_mono fun _ _ h => adj_of_induce_adj h

/-- Restricting to everything changes nothing. -/
theorem moralGraph_induce_univ (D : DAG V) :
    (D.induce Finset.univ).moralGraph = D.moralGraph := by
  ext u v
  rw [moralGraph_induce_adj, moralGraph_adj]
  simp

/-- **The families of an ancestral set are complete in `(G_A)^m`.** For `v` in an ancestral block
`A`, the family `fa(v) = {v} ∪ pa(v)` — computed in the *original* DAG, since ancestral sets have
`pa_{G_A}(v) = pa_G(v)` (`DAG.parents_induce_of_isAncestralSet`) — is a clique of the moralized
restriction. This is the exact form Lauritzen's Corollary 3.23 (p. 47) needs: it is what lets a
recursive factorization of the full DAG be read as a `FactorizesOver (D.induce A).moralGraph`
statement, and hence lets the global Markov property be applied to `(G_{An(A∪B∪S)})^m`. -/
theorem isClique_insert_parents_induce (D : DAG V) [DecidableRel D.Adj] {A : Finset V}
    -- USER-INPUT: the block is ancestral; Lauritzen §2.1.1, p. 7 — the hypothesis of Cor. 3.23
    -- (p. 47), where the block is `An(A ∪ B ∪ S)`. Without it `pa_{G_A}(v)` is a proper subset
    -- of `pa_G(v)` and the statement is false as written.
    (hA : D.IsAncestralSet A) {v : V}
    -- USER-INPUT: the vertex lies in the block; Lauritzen §2.1.1, p. 7
    (hv : v ∈ A) :
    (D.induce A).moralGraph.IsClique ((insert v (D.parents v) : Finset V) : Set V) := by
  have hmem : ∀ x : V, x = v ∨ D.Adj x v → x ∈ A := by
    rintro x (rfl | hx)
    · exact hv
    · exact hA hx hv
  intro a ha b hb hab
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, mem_parents] at ha hb
  rw [moralGraph_induce_adj]
  refine ⟨hab, hmem a ha, hmem b hb, ?_⟩
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact Or.inr (Or.inl hb)
  · rcases hb with rfl | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inr ⟨v, hv, ha, hb⟩)

end Induce

end DAG

end StatLean.StatisticalModels.GraphicalModels
