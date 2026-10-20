module
public import Mathlib.Combinatorics.SimpleGraph.Walks.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
public import Mathlib.Combinatorics.SimpleGraph.Ends.Defs

@[expose] public section

/-!
# Graph separation — the combinatorial side of the Markov properties

`Separates G S A B` says that the vertex set `S` **separates** `A` from `B` in the simple
graph `G`: every walk that starts in `A` and ends in `B` visits a vertex of `S`. This is the
only graph-theoretic input the undirected Markov properties need, and it is the object whose
graphoid calculus mirrors the probabilistic one (Lauritzen's Example 3.2).

* `Separates` — the definition, as a `∀`-statement over `SimpleGraph.Walk`;
* `separates_symm` — separation is symmetric in the two separated blocks;
* `separates_mono_left` / `separates_mono_right` — shrinking either separated block preserves
  separation;
* `separates_of_subset_sep` — growing the separator preserves separation;
* `separates_empty_left` / `separates_empty_right` / `separates_self_left` /
  `separates_self_right` — the degenerate cases (an empty block is separated from anything; a
  block already inside the separator is separated from anything);
* `separates_iff_forall_path` — the bridge to the book's *path*-phrased definition;
* `separates_iff_not_reachable_deleteVerts` and `separates_iff_componentComplMk_ne` — the
  bridge into Mathlib's connectivity API: separation is exactly non-reachability in the graph
  with `S` deleted, equivalently "different connected components outside `S`". These are the
  hinges through which any future connectivity-flavoured result (menger-type statements,
  decomposable graphs) will be proved.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, 1996, §2.1.1, p. 6: an *(α, β)-separator* is a set `S` such that
every path from `α` to `β` intersects `S`, and `S` *separates* `A` from `B` when it is an
`(α, β)`-separator for every `α ∈ A`, `β ∈ B`. Both are **unnumbered** definitions in that
section — there is no "Definition 2.x" to cite. Example 3.2 (p. 31) records that graph
separation, read as the ternary relation `(A, B, S) ↦ S` separates `A` from `B`, satisfies the
graphoid axioms; that is the reason this file's API is shaped like `IsSemigraphoid`'s
(`Lauritzen §2.1.1` / `Lauritzen Ex. 3.2` in tags).

**Proof formalization notes.** *Book vs Lean, three deliberate differences.*

1. **Walks, not paths.** Lauritzen quantifies over *paths*. On a `SimpleGraph` the two
   quantifications define the same relation: a walk contains a path with the same endpoints
   and a smaller support (`SimpleGraph.Walk.bypass`, `Walk.bypass_isPath`,
   `Walk.support_bypass_subset`), and a path is a walk. `separates_iff_forall_path` records
   this equivalence. We take walks as primitive because `SimpleGraph.Walk` is the type
   carrying the induction principle and the `support` / `takeUntil` / `induce` API that every
   proof here runs on; `SimpleGraph.Path` is a subtype of it.
2. **`S` may meet `A` or `B`.** No disjointness is assumed in the definition. If `a ∈ A ∩ S`
   then every walk out of `a` already meets `S` at its own start, so `Separates` holds
   vacuously in that direction — that is `separates_self_left`. The book's blocks are
   disjoint; the disjointness is carried by the *consumers*
   (`GraphicalModels.IsGlobalMarkov`), never by this definition, so that the monotonicity
   lemmas below need no side conditions.
3. **Finsets, not sets.** `S A B : Finset V`, matching the index-block vocabulary of
   `IsSemigraphoid` and `CondIndepCoords`. The separated vertices themselves range over all of
   `V`; nothing here needs `V` finite or `G` locally finite.

The two Mathlib bridges are stated with **no** disjointness or non-membership side conditions
and are genuinely unconditional: if `a ∈ S` then no element of the deleted-vertex subtype lies
over `a`, so the right-hand sides quantify vacuously exactly where `Separates` is vacuous.

**Bibliographic comments.** Separation of vertex sets is classical graph theory (Menger 1927);
its use as the combinatorial carrier of conditional independence is due to the
Markov-field literature — J. M. Hammersley and P. Clifford's unpublished 1971 manuscript,
and in the form used here Lauritzen's book, which credits the graphoid reading to J. Pearl,
*Probabilistic Reasoning in Intelligent Systems*, Morgan Kaufmann, 1988.
-/

namespace StatLean.StatisticalModels.GraphicalModels

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V) {S S' A A' B B' : Finset V}

/-- `S` **separates** `A` from `B` in `G`: every walk from a vertex of `A` to a vertex of `B`
visits a vertex of `S` (Lauritzen §2.1.1, p. 6, unnumbered).

*Edge behaviour.* Vacuously true when `A = ∅` or `B = ∅` (`separates_empty_left`,
`separates_empty_right`), and — because a walk contains its own endpoints — automatically
true when `A ⊆ S` or `B ⊆ S` (`separates_self_left`, `separates_self_right`), *including*
when `A` and `S` overlap, which the book excludes by fiat. No disjointness of `A`, `B`, `S`
is assumed; consumers that need the book's disjoint regime carry it themselves. -/
def Separates (S A B : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ w : G.Walk a b, ∃ s ∈ S, s ∈ w.support

/-- **Symmetry.** `S` separates `A` from `B` iff it separates `B` from `A` — reverse the
walk (`SimpleGraph.Walk.reverse`, `Walk.support_reverse`). -/
theorem separates_symm
    -- USER-INPUT: the separation to be flipped; Lauritzen §2.1.1, p. 6 (the book's
    -- definition is visibly symmetric, being phrased on undirected paths)
    (h : Separates G S A B) :
    Separates G S B A := by
  intro a ha b hb w
  obtain ⟨s, hsS, hsw⟩ := h b hb a ha w.reverse
  refine ⟨s, hsS, ?_⟩
  rwa [Walk.support_reverse, List.mem_reverse] at hsw

/-- **Symmetry, as an equivalence.** -/
theorem separates_comm : Separates G S A B ↔ Separates G S B A :=
  ⟨separates_symm G, separates_symm G⟩

/-- **Monotone in the first block**: shrinking `A` preserves separation. -/
theorem separates_mono_left
    -- USER-INPUT: the smaller first block; free choice of the caller (Lauritzen §2.1.1
    -- separates *every* pair `α ∈ A`, `β ∈ B`, so a sub-block inherits it)
    (hA : A' ⊆ A)
    -- USER-INPUT: the separation to be weakened; Lauritzen §2.1.1, p. 6
    (h : Separates G S A B) :
    Separates G S A' B :=
  fun a ha b hb w => h a (hA ha) b hb w

/-- **Monotone in the second block**: shrinking `B` preserves separation. -/
theorem separates_mono_right
    -- USER-INPUT: the smaller second block; free choice of the caller (Lauritzen §2.1.1)
    (hB : B' ⊆ B)
    -- USER-INPUT: the separation to be weakened; Lauritzen §2.1.1, p. 6
    (h : Separates G S A B) :
    Separates G S A B' :=
  fun a ha b hb w => h a ha b (hB hb) w

/-- **Monotone in the separator**: growing `S` preserves separation. -/
theorem separates_of_subset_sep
    -- USER-INPUT: the larger separator; free choice of the caller (Lauritzen §2.1.1: a
    -- superset of an `(α, β)`-separator is an `(α, β)`-separator)
    (hS : S ⊆ S')
    -- USER-INPUT: the separation to be weakened; Lauritzen §2.1.1, p. 6
    (h : Separates G S A B) :
    Separates G S' A B :=
  fun a ha b hb w =>
    let ⟨s, hsS, hsw⟩ := h a ha b hb w
    ⟨s, hS hsS, hsw⟩

/-- **Degenerate case**: nothing to separate on the left. -/
theorem separates_empty_left : Separates G S ∅ B :=
  fun a ha _ _ _ => absurd ha (Finset.notMem_empty a)

/-- **Degenerate case**: nothing to separate on the right. -/
theorem separates_empty_right : Separates G S A ∅ :=
  fun _ _ b hb _ => absurd hb (Finset.notMem_empty b)

/-- **Degenerate case**: a block contained in the separator is separated from everything —
every walk out of `a ∈ A ⊆ S` meets `S` at its own first vertex. This is the reason the
book's disjointness assumption is not needed in the definition. -/
theorem separates_self_left
    -- USER-INPUT: the first block sits inside the separator; the book excludes this case by
    -- assuming `A`, `B`, `S` disjoint, so this is a Lean-side completion of the definition
    (hAS : A ⊆ S) :
    Separates G S A B :=
  fun a ha _ _ w => ⟨a, hAS ha, w.start_mem_support⟩

/-- **Degenerate case**: dual of `separates_self_left`, via the last vertex of the walk. -/
theorem separates_self_right
    -- USER-INPUT: the second block sits inside the separator; see `separates_self_left`
    (hBS : B ⊆ S) :
    Separates G S A B :=
  fun _ _ b hb w => ⟨b, hBS hb, w.end_mem_support⟩

/-- **The book's phrasing.** Lauritzen (§2.1.1, p. 6) quantifies over *paths*, not walks. The
two agree: a path is a walk, and every walk contains a path with the same endpoints whose
support is contained in the walk's (`SimpleGraph.Walk.bypass`,
`SimpleGraph.Walk.support_bypass_subset`). -/
theorem separates_iff_forall_path (S A B : Finset V) :
    Separates G S A B ↔
      ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Path a b,
        ∃ s ∈ S, s ∈ (p : G.Walk a b).support := by
  -- LEAN-ONLY: `Walk.bypass` needs `DecidableEq V`, which the statement does not carry;
  -- supplied classically, so the statement is unchanged
  classical
  refine ⟨fun h a ha b hb p => h a ha b hb (p : G.Walk a b), fun h a ha b hb w => ?_⟩
  -- a walk contains a path with the same endpoints and a smaller support
  obtain ⟨s, hsS, hsw⟩ := h a ha b hb ⟨w.bypass, w.bypass_isPath⟩
  exact ⟨s, hsS, w.support_bypass_subset hsw⟩

/-- **Bridge to Mathlib's vertex deletion.** `S` separates `A` from `B` exactly when no
vertex of `A` is reachable from a vertex of `B` in `G` with the vertices of `S` removed.

The subtype `((⊤ : G.Subgraph).deleteVerts S).verts` is `Set.univ \ S` by
`Subgraph.deleteVerts_verts` (`rfl`), so quantifying over it *is* quantifying over the
vertices outside `S`; vertices of `A ∩ S` are excluded on the right-hand side and vacuous on
the left (`separates_self_left`), which is why no disjointness hypothesis appears.

This is the hinge into Mathlib's connectivity API. -/
theorem separates_iff_not_reachable_deleteVerts (S A B : Finset V) :
    Separates G S A B ↔
      ∀ a b : ((⊤ : G.Subgraph).deleteVerts (S : Set V)).verts,
        (a : V) ∈ A → (b : V) ∈ B →
          ¬ ((⊤ : G.Subgraph).deleteVerts (S : Set V)).coe.Reachable a b := by
  -- the deleted-vertex subgraph, coerced, *is* the induced graph on its own vertex set:
  -- the extra conjuncts of `deleteVerts_adj` are discharged by the subtype's own proof
  have hgraph : ((⊤ : G.Subgraph).deleteVerts (S : Set V)).coe
      = G.induce (((⊤ : G.Subgraph).deleteVerts (S : Set V)).verts) := by
    ext u v
    have hu := u.2
    have hv := v.2
    simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_diff, Set.mem_univ,
      true_and, Finset.mem_coe] at hu hv
    simp [hu, hv]
  constructor
  · intro h a b ha hb hreach
    obtain ⟨w'⟩ := hreach
    -- stated at the walk's own endpoint indices `⇑hom a`, so that `support_map` matches
    have key : ∀ x ∈ (w'.map ((⊤ : G.Subgraph).deleteVerts (S : Set V)).hom).support,
        x ∉ (S : Set V) := by
      intro x hx
      rw [Walk.support_map, List.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2.2
    obtain ⟨s, hsS, hsw⟩ := h (a : V) ha (b : V) hb (w'.map (Subgraph.hom _))
    exact key s hsw (Finset.mem_coe.2 hsS)
  · intro h a ha b hb w
    by_contra hcon
    push Not at hcon
    have hw : ∀ x ∈ w.support, x ∈ ((⊤ : G.Subgraph).deleteVerts (S : Set V)).verts :=
      fun x hx => ⟨Set.mem_univ x, fun hxS => hcon x (Finset.mem_coe.1 hxS) hx⟩
    refine h ⟨a, hw a w.start_mem_support⟩ ⟨b, hw b w.end_mem_support⟩ ha hb ?_
    rw [hgraph]
    exact ⟨w.induce _ hw⟩

/-- **Bridge to `SimpleGraph.ComponentCompl`.** Separation says that no vertex of `A` and no
vertex of `B` lie in a common connected component of the complement of `S`. Stated with
`SimpleGraph.componentComplMk`, whose hypothesis `a ∉ (S : Set V)` supplies the
outside-the-separator side condition, so again nothing is assumed about `A ∩ S`.

Equivalent to `separates_iff_not_reachable_deleteVerts` via
`SimpleGraph.ConnectedComponent.eq`; kept separate because `ComponentCompl` is the form the
`Ends` API and any future decomposable-graph result needs. -/
theorem separates_iff_componentComplMk_ne (S A B : Finset V) :
    Separates G S A B ↔
      ∀ a ∈ A, ∀ b ∈ B, ∀ (ha : a ∉ (S : Set V)) (hb : b ∉ (S : Set V)),
        G.componentComplMk ha ≠ G.componentComplMk hb := by
  constructor
  · intro h a ha b hb haS hbS hEq
    rw [ConnectedComponent.eq] at hEq
    obtain ⟨w'⟩ := hEq
    have key : ∀ x ∈ (w'.map (Embedding.induce ((S : Set V))ᶜ).toHom).support,
        x ∉ (S : Set V) := by
      intro x hx
      rw [Walk.support_map, List.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    obtain ⟨s, hsS, hsw⟩ := h a ha b hb (w'.map (Embedding.induce _).toHom)
    exact key s hsw (Finset.mem_coe.2 hsS)
  · intro h a ha b hb w
    by_contra hcon
    push Not at hcon
    have hw : ∀ x ∈ w.support, x ∈ ((S : Set V))ᶜ :=
      fun x hx hxS => hcon x (Finset.mem_coe.1 hxS) hx
    exact h a ha b hb (hw a w.start_mem_support) (hw b w.end_mem_support)
      (ConnectedComponent.eq.2 ⟨w.induce _ hw⟩)

end StatLean.StatisticalModels.GraphicalModels
