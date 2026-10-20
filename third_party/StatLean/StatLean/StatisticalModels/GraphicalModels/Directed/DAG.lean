module
public import Mathlib.Logic.Relation
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Order.Extension.Linear

@[expose] public section

/-!
# Directed acyclic graphs — parents, ancestors, ancestral sets, topological order

The directed side of the graphical-model vocabulary: Lauritzen's `pa`, `ch`, `an`, `de`, `nd`,
his *ancestral sets* and the ancestral closure `An(·)`, the induced sub-DAG `G_A`, and the
existence of a topological (linear) extension in which every parent precedes its child.

* `IsAcyclicRel r` — no vertex reaches itself along a nonempty directed chain, stated with
  `Relation.TransGen`; `IsAcyclicRel.mono` — a sub-relation of an acyclic relation is acyclic;
* `DAG V` — the bundled carrier: an edge relation together with its acyclicity;
  `DAG.irrefl`, `DAG.ne_of_adj` — irreflexivity, **derived** rather than assumed;
* `DAG.reflTransGen_antisymm`, `DAG.isPartialOrder_reflTransGen` — reachability
  `Relation.ReflTransGen D.Adj` is a partial order, the fact that carries the topological order;
* `DAG.parents`, `DAG.children`, `DAG.ancestors`, `DAG.descendants`, `DAG.nonDescendants` —
  the five neighbourhoods as `Finset`s, with their membership characterisations;
* `DAG.parents_subset_nonDescendants`, `DAG.notMem_ancestors_self`,
  `DAG.disjoint_singleton_nonDescendants` — the sanity lemmas the directed local Markov
  property needs (`v ⫫ nd(v) ∖ pa(v) ∣ pa(v)` needs exactly these disjointnesses);
* `DAG.IsAncestralSet`, `DAG.ancestralClosure` — closure under parents, and the smallest
  ancestral set containing a given block, with monotonicity, extensivity, idempotence, and
  minimality;
* `DAG.exists_linearOrder_extending`, `DAG.exists_topologicalOrder` — a linear extension of
  reachability, and (on a finite vertex set) an enumeration `V ≃ Fin (card V)` in which every
  ancestor precedes its descendant;
* `DAG.induce` — the sub-DAG induced on a vertex block `A`, together with
  `DAG.parents_induce_of_isAncestralSet`: on an **ancestral** set the induced parent sets are
  unchanged. This is the construction Lauritzen's Corollary 3.23 restricts to before moralizing.

**Acyclicity and reachability via `Relation.(Refl)TransGen`.** The directed theory is built on a
bare edge relation `Adj : V → V → Prop`: acyclicity is `∀ v, ¬ Relation.TransGen Adj v v`, and
reachability is `Relation.ReflTransGen Adj`. The closure API of these two — `trans`, `head`,
`tail`, `single`, `mono`, `lift`, `head_induction_on`, `trans_induction_on`, `cases_head`,
`reflTransGen_iff_eq_or_transGen` — is the induction principle every proof below runs on.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996**, §2.1.1, pp. 5–7. Every notion in this file is an
**unnumbered** definition of that section — there is no "Definition 2.x" to cite. In the book's
notation: `pa(α)` the parents, `ch(α)` the children, `an(β)` the ancestors (`α` leads to `β`
along a directed path), `de(α)` the descendants, `nd(α) = V ∖ (de(α) ∪ {α})` the
non-descendants; a subset is *ancestral* when it contains the parents of each of its elements,
and `An(A)` is the smallest ancestral set containing `A`. `G_A` denotes the subgraph induced on
`A` (`Lauritzen §2.1.1` in tags).

**Proof formalization notes.** *Book vs Lean, six deliberate differences.*

1. **`an(β)` excludes `β`, `An(A)` includes `A` — and we follow the book exactly.** Lauritzen's
   `an(β)` is the set of vertices from which `β` is reachable along a **nonempty** directed
   path, so `β ∉ an(β)`; correspondingly `DAG.ancestors` is cut out by `Relation.TransGen`, not
   `Relation.ReflTransGen`, and `DAG.notMem_ancestors_self` records that this is automatic in a
   DAG. `An(A)`, being the smallest ancestral set *containing* `A`, does contain `A`; so
   `DAG.ancestralClosure A = A ∪ ⋃_{v ∈ A} an(v)` and `DAG.subset_ancestralClosure` is a
   theorem. The same asymmetry governs `de` versus `nd`: `nd(α)` removes `α` explicitly because
   `de(α)` does not contain it.
2. **Irreflexivity is derived, not a field.** Lauritzen's directed graphs have no loops. A loop
   `α → α` is a directed cycle, so acyclicity already forbids it (`DAG.irrefl`, via
   `Relation.TransGen.single`); a separate `loopless` field would be redundant, and by the
   constitutive-versus-regularity test a redundant field does not belong in the structure. This
   is the one place where we deviate from `SimpleGraph`'s shape, which *does* carry `loopless`
   because there is no stronger field to derive it from.
3. **Structure *and* predicate.** `IsAcyclicRel` is the predicate on a bare relation; `DAG` is
   the bundled carrier. Both are wanted: the bundle gives dot notation and lets `moralGraph`
   and `DAG.induce` be honest functions `DAG V → _`, matching the `SimpleGraph`-shaped
   vocabulary of the undirected side; the predicate lets us say
   "this sub-relation is still acyclic" (`IsAcyclicRel.mono`) without building a structure.
4. **The neighbourhoods are `Finset`s, and their decidability is explicit.** `Finset V` is the
   index-block vocabulary of `Core.Separation`, `Core.Semigraphoid` and `Core.Coordinates`, so
   the directed neighbourhoods must be `Finset`s to fit there. That forces
   `[Fintype V]` plus a `Decidable` instance for the predicate being filtered:
   `[DecidableRel D.Adj]` for `parents`/`children`, and
   `[DecidableRel (Relation.TransGen D.Adj)]` for `ancestors`/`descendants`/`nonDescendants`/
   `ancestralClosure`. Deciding `Relation.TransGen` is a genuine transitive-closure computation
   that is out of scope here, so we take it as an instance **argument** rather than hiding it
   behind `Classical.dec`: it can always be discharged with `classical`, and any two choices
   give equal `Finset`s by `Finset.filter_congr_decidable`.
5. **`DAG.induce A` keeps the vertex type `V`** and merely restricts the edge relation to `A`,
   leaving vertices outside `A` isolated, rather than moving to the subtype `↥A`. Lauritzen's
   `G_A` is the subgraph on the vertex set `A`; the two agree on everything we ask of them,
   because every edge of `DAG.induce A` has both endpoints in `A`, so every directed chain and
   (after moralization) every walk between vertices of `A` stays inside `A`. Keeping `V` fixed
   lets the `Separates`/`IsGlobalMarkov` vocabulary, which is phrased on `Finset V` for a single
   `V`, apply to the moralized restriction — the alternative would drag a subtype transport
   through every statement of Corollary 3.23.
6. **The topological order is stated as an existence theorem, not a sort.** Mathlib's
   `extend_partialOrder` (`Order/Extension/Linear.lean`, the Szpilrajn extension theorem) turns
   the partial order `Relation.ReflTransGen D.Adj` into a linear one, and on a finite type
   `monoEquivOfFin` converts a linear order into an enumeration by `Fin (Fintype.card V)`.

**Bibliographic comments.** Directed graphical models and their ancestral vocabulary are due to
the recursive-model literature — T. Speed and H. Kiiveri, "Gaussian Markov distributions over
finite graphs," *Ann. Statist.* **14** (1986), 138–150; S. L. Lauritzen and D. J. Spiegelhalter,
"Local computations with probabilities on graphical structures," *J. Roy. Statist. Soc. Ser. B*
**50** (1988), 157–224; and J. Pearl, *Probabilistic Reasoning in Intelligent Systems*, Morgan
Kaufmann, 1988. The linear-extension theorem behind `DAG.exists_linearOrder_extending` is
E. Szpilrajn, "Sur l'extension de l'ordre partiel," *Fund. Math.* **16** (1930), 386–389, which
Mathlib proves via Zorn's lemma.
-/

namespace StatLean.StatisticalModels.GraphicalModels

variable {V : Type*}

/-! ### Acyclicity and the `DAG` carrier -/

/-- A relation is **acyclic** when no vertex reaches itself along a nonempty directed chain
(Lauritzen §2.1.1, p. 6, unnumbered: a directed graph has "no directed cycles").

*Edge behaviour.* This already forbids loops: `r v v` gives `Relation.TransGen r v v` through
`Relation.TransGen.single`, so an acyclic relation is irreflexive (`DAG.irrefl`). The empty
relation and the relation on an empty type are acyclic. -/
def IsAcyclicRel (r : V → V → Prop) : Prop :=
  ∀ v : V, ¬ Relation.TransGen r v v

/-- A sub-relation of an acyclic relation is acyclic — the fact that makes every restriction of
a DAG (in particular `DAG.induce`) a DAG again. -/
theorem IsAcyclicRel.mono {r p : V → V → Prop}
    -- USER-INPUT: the ambient acyclic relation; Lauritzen §2.1.1, p. 6
    (hp : IsAcyclicRel p)
    -- USER-INPUT: the sub-relation; free choice of the caller (Lauritzen's `G_A` is the
    -- instance we care about, §2.1.1, p. 7)
    (hle : ∀ a b : V, r a b → p a b) :
    IsAcyclicRel r :=
  fun v hv => hp v (Relation.TransGen.mono hle _ _ hv)

/-- A **directed acyclic graph** on the vertex set `V` (Lauritzen §2.1.1, pp. 5–6, unnumbered):
an edge relation with no directed cycles. Read `D.Adj u v` as the directed edge `u → v`, so that
`u` is a *parent* of `v`.

*Edge behaviour.* Irreflexivity is **not** a field: it follows from `acyclic` (`DAG.irrefl`), so
a `loopless` field would be redundant. The empty graph on any `V`, and any graph on an empty
`V`, are `DAG`s. -/
@[ext]
structure DAG (V : Type*) where
  /-- Constitutive (Lauritzen §2.1.1, p. 5): the directed edge relation, `Adj u v` meaning
  `u → v`. Removing it leaves no graph at all. -/
  Adj : V → V → Prop
  /-- Constitutive (Lauritzen §2.1.1, p. 6): the graph is **acyclic** — no vertex reaches itself
  along a nonempty directed chain. Removing it makes the object a general directed graph, for
  which none of the recursive-factorization theory holds. -/
  acyclic : IsAcyclicRel Adj

namespace DAG

/-- A DAG has no loops: `α → α` would be a directed cycle of length one. Lauritzen's directed
graphs are loopless by fiat; here it is a theorem, which is why the structure carries no
`loopless` field. -/
theorem irrefl (D : DAG V) (v : V) : ¬ D.Adj v v :=
  fun h => D.acyclic v (Relation.TransGen.single h)

/-- The two endpoints of a directed edge are distinct — the `Ne` form of `DAG.irrefl`, which is
what the moral graph's `SimpleGraph.fromRel` constructor asks for. -/
theorem ne_of_adj (D : DAG V) {u v : V}
    -- USER-INPUT: the edge; Lauritzen §2.1.1, p. 5
    (h : D.Adj u v) :
    u ≠ v := by
  rintro rfl
  exact D.irrefl _ h

/-- **Reachability is antisymmetric**: two vertices each reachable from the other are equal.
This is the content of acyclicity in order-theoretic form — a genuine two-way chain between
distinct vertices splices (`Relation.ReflTransGen.trans`, then
`Relation.reflTransGen_iff_eq_or_transGen`) into a directed cycle. -/
theorem reflTransGen_antisymm (D : DAG V) {u v : V}
    -- USER-INPUT: `u` reaches `v`; Lauritzen §2.1.1, p. 6 ("`u` leads to `v`")
    (huv : Relation.ReflTransGen D.Adj u v)
    -- USER-INPUT: `v` reaches `u`; Lauritzen §2.1.1, p. 6
    (hvu : Relation.ReflTransGen D.Adj v u) :
    u = v := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp huv with h | h
  · exact h.symm
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hvu with h' | h'
    · exact h'
    · exact absurd (h.trans h') (D.acyclic u)

/-- **Reachability is a partial order** — reflexivity and transitivity are
`Relation.ReflTransGen.refl` / `.trans`, antisymmetry is `DAG.reflTransGen_antisymm`. Deliberately
*not* an `instance`: it is supplied by hand (`haveI := D.isPartialOrder_reflTransGen`) at the one
place that needs it, `DAG.exists_linearOrder_extending`, rather than firing on every
`Relation.ReflTransGen` goal in the library. -/
theorem isPartialOrder_reflTransGen (D : DAG V) :
    IsPartialOrder V (Relation.ReflTransGen D.Adj) :=
  { refl := fun _ => Relation.ReflTransGen.refl
    trans := fun _ _ _ h₁ h₂ => h₁.trans h₂
    antisymm := fun _ _ h₁ h₂ => D.reflTransGen_antisymm h₁ h₂ }

/-! ### The five neighbourhoods

Lauritzen's `pa`, `ch`, `an`, `de`, `nd` (§2.1.1, pp. 6–7), as `Finset`s over a finite vertex
set. See the module docstring, note 4, for why the `Decidable` instances are explicit arguments
rather than classical. -/

section Neighbourhoods

variable [Fintype V]

/-- The **parents** `pa(v)` of `v` (Lauritzen §2.1.1, p. 6, unnumbered): the vertices with an
edge into `v`. Edge behaviour: `v ∉ pa(v)` by `DAG.irrefl`
(`DAG.notMem_parents_self`); `pa(v) = ∅` at a source. -/
def parents (D : DAG V) [DecidableRel D.Adj] (v : V) : Finset V :=
  Finset.univ.filter fun u => D.Adj u v

@[simp]
theorem mem_parents {D : DAG V} [DecidableRel D.Adj] {u v : V} :
    u ∈ D.parents v ↔ D.Adj u v := by
  simp [parents]

/-- The **children** `ch(v)` of `v` (Lauritzen §2.1.1, p. 6, unnumbered): the vertices with an
edge out of `v`. Edge behaviour: `v ∉ ch(v)`; `ch(v) = ∅` at a sink. -/
def children (D : DAG V) [DecidableRel D.Adj] (v : V) : Finset V :=
  Finset.univ.filter fun u => D.Adj v u

@[simp]
theorem mem_children {D : DAG V} [DecidableRel D.Adj] {u v : V} :
    u ∈ D.children v ↔ D.Adj v u := by
  simp [children]

/-- The **ancestors** `an(v)` of `v` (Lauritzen §2.1.1, p. 6, unnumbered): the vertices that
*lead to* `v`, i.e. reach it along a **nonempty** directed chain.

*Book vs Lean.* Cut out by `Relation.TransGen`, not `Relation.ReflTransGen`, because Lauritzen's
`an(β)` does **not** contain `β` — contrast `An(A) = DAG.ancestralClosure A`, which does contain
`A`. In a DAG the exclusion is automatic (`DAG.notMem_ancestors_self`), so no vertex is lost by
either reading; we follow the book. -/
def ancestors (D : DAG V) [DecidableRel (Relation.TransGen D.Adj)] (v : V) : Finset V :=
  Finset.univ.filter fun u => Relation.TransGen D.Adj u v

@[simp]
theorem mem_ancestors {D : DAG V} [DecidableRel (Relation.TransGen D.Adj)] {u v : V} :
    u ∈ D.ancestors v ↔ Relation.TransGen D.Adj u v := by
  simp [ancestors]

/-- The **descendants** `de(v)` of `v` (Lauritzen §2.1.1, p. 6, unnumbered): the vertices `v`
leads to. As with `ancestors`, `v ∉ de(v)` — see `DAG.notMem_descendants_self`. -/
def descendants (D : DAG V) [DecidableRel (Relation.TransGen D.Adj)] (v : V) : Finset V :=
  Finset.univ.filter fun u => Relation.TransGen D.Adj v u

@[simp]
theorem mem_descendants {D : DAG V} [DecidableRel (Relation.TransGen D.Adj)] {u v : V} :
    u ∈ D.descendants v ↔ Relation.TransGen D.Adj v u := by
  simp [descendants]

/-- The **non-descendants** `nd(v) = V ∖ (de(v) ∪ {v})` of `v` (Lauritzen §2.1.1, p. 6,
unnumbered). The `{v}` is removed explicitly, exactly as in the book, because `de(v)` does not
contain `v`. Edge behaviour: `v ∉ nd(v)` by construction
(`DAG.notMem_nonDescendants_self`), and `pa(v) ⊆ nd(v)`
(`DAG.parents_subset_nonDescendants`) — the two facts the directed local Markov property
`X_v ⫫ X_{nd(v) ∖ pa(v)} ∣ X_{pa(v)}` needs of its blocks. -/
def nonDescendants (D : DAG V) [DecidableEq V] [DecidableRel (Relation.TransGen D.Adj)]
    (v : V) : Finset V :=
  Finset.univ \ insert v (D.descendants v)

@[simp]
theorem mem_nonDescendants {D : DAG V} [DecidableEq V]
    [DecidableRel (Relation.TransGen D.Adj)] {u v : V} :
    u ∈ D.nonDescendants v ↔ u ≠ v ∧ ¬ Relation.TransGen D.Adj v u := by
  simp [nonDescendants, not_or]

/-! #### Sanity lemmas -/

/-- No vertex is its own ancestor — Lauritzen's `an(β)` excludes `β`, and in a DAG this needs no
convention: `Relation.TransGen D.Adj v v` is exactly what acyclicity forbids. -/
theorem notMem_ancestors_self (D : DAG V) [DecidableRel (Relation.TransGen D.Adj)] (v : V) :
    v ∉ D.ancestors v := by
  simpa using D.acyclic v

/-- No vertex is its own descendant. -/
theorem notMem_descendants_self (D : DAG V) [DecidableRel (Relation.TransGen D.Adj)] (v : V) :
    v ∉ D.descendants v := by
  simpa using D.acyclic v

/-- No vertex is its own parent (`DAG.irrefl`). -/
theorem notMem_parents_self (D : DAG V) [DecidableRel D.Adj] (v : V) : v ∉ D.parents v := by
  simpa using D.irrefl v

/-- Every parent is an ancestor — `Relation.TransGen.single`. -/
theorem parents_subset_ancestors (D : DAG V) [DecidableRel D.Adj]
    [DecidableRel (Relation.TransGen D.Adj)] (v : V) :
    D.parents v ⊆ D.ancestors v := by
  intro u hu
  simp only [mem_parents] at hu
  simpa using Relation.TransGen.single hu

/-- Every child is a descendant. -/
theorem children_subset_descendants (D : DAG V) [DecidableRel D.Adj]
    [DecidableRel (Relation.TransGen D.Adj)] (v : V) :
    D.children v ⊆ D.descendants v := by
  intro u hu
  simp only [mem_children] at hu
  simpa using Relation.TransGen.single hu

/-- **`pa(v) ⊆ nd(v)`**: a parent of `v` is neither `v` (irreflexivity) nor a descendant of `v`
(a parent that were also a descendant would close a directed cycle through `v`). This is the
inclusion that makes the directed local Markov property well posed — its "rest" block is
`nd(v) ∖ pa(v)`. -/
theorem parents_subset_nonDescendants (D : DAG V) [DecidableEq V] [DecidableRel D.Adj]
    [DecidableRel (Relation.TransGen D.Adj)] (v : V) :
    D.parents v ⊆ D.nonDescendants v := by
  intro u hu
  simp only [mem_parents] at hu
  refine mem_nonDescendants.mpr ⟨D.ne_of_adj hu, fun h => ?_⟩
  exact D.acyclic v (h.tail hu)

/-- `v ∉ nd(v)`, by construction of `nonDescendants`. -/
theorem notMem_nonDescendants_self (D : DAG V) [DecidableEq V]
    [DecidableRel (Relation.TransGen D.Adj)] (v : V) :
    v ∉ D.nonDescendants v := by
  simp

/-- The disjointness obligation of the directed local Markov property: `{v}` is disjoint from
`nd(v)`, hence from `nd(v) ∖ pa(v)` and from `pa(v)` (the latter via
`DAG.parents_subset_nonDescendants`). -/
theorem disjoint_singleton_nonDescendants (D : DAG V) [DecidableEq V]
    [DecidableRel (Relation.TransGen D.Adj)] (v : V) :
    Disjoint ({v} : Finset V) (D.nonDescendants v) :=
  Finset.disjoint_singleton_left.mpr (D.notMem_nonDescendants_self v)

end Neighbourhoods

/-! ### Ancestral sets and the ancestral closure -/

/-- A block `A` is an **ancestral set** (Lauritzen §2.1.1, p. 7, unnumbered) when it contains the
parents of each of its elements. Stated on the bare relation, so no decidability is involved;
`DAG.isAncestralSet_iff_parents_subset` is the `Finset` reading `∀ v ∈ A, pa(v) ⊆ A`, and
`DAG.IsAncestralSet.reflTransGen_mem` upgrades "closed under parents" to "closed under
ancestors", which is the form the book uses interchangeably.

*Edge behaviour.* `∅` and `Finset.univ` are ancestral. -/
def IsAncestralSet (D : DAG V) (A : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, D.Adj u v → v ∈ A → u ∈ A

/-- The `Finset` reading of `DAG.IsAncestralSet`: an ancestral set contains the parent block of
each of its elements. -/
theorem isAncestralSet_iff_parents_subset [Fintype V] (D : DAG V) [DecidableRel D.Adj]
    (A : Finset V) :
    D.IsAncestralSet A ↔ ∀ v ∈ A, D.parents v ⊆ A := by
  constructor
  · intro h v hv u hu
    exact h (mem_parents.mp hu) hv
  · intro h u v huv hv
    exact h v hv (mem_parents.mpr huv)

/-- An ancestral set is closed under **ancestors**, not merely under parents — induct along the
chain with `Relation.ReflTransGen.head_induction_on`. Lauritzen uses the two formulations
interchangeably on p. 7. -/
theorem IsAncestralSet.reflTransGen_mem {D : DAG V} {A : Finset V}
    -- USER-INPUT: the ancestral set; Lauritzen §2.1.1, p. 7
    (hA : D.IsAncestralSet A) {u v : V}
    -- USER-INPUT: `u` leads to `v`; Lauritzen §2.1.1, p. 6
    (huv : Relation.ReflTransGen D.Adj u v)
    -- USER-INPUT: the endpoint lies in the set; Lauritzen §2.1.1, p. 7
    (hv : v ∈ A) :
    u ∈ A :=
  huv.head_induction_on hv fun h' _ ih => hA h' ih

/-- The whole vertex set is ancestral. -/
theorem isAncestralSet_univ [Fintype V] (D : DAG V) : D.IsAncestralSet Finset.univ :=
  fun _ _ _ _ => Finset.mem_univ _

/-- The empty set is ancestral. -/
theorem isAncestralSet_empty (D : DAG V) : D.IsAncestralSet (∅ : Finset V) :=
  fun _ _ _ hv => absurd hv (Finset.notMem_empty _)

/-- The **ancestral closure** `An(A)` (Lauritzen §2.1.1, p. 7, unnumbered): the smallest
ancestral set containing `A`, realised as `A ∪ ⋃_{v ∈ A} an(v)`.

*Book vs Lean.* Lauritzen defines `An(A)` by the minimality property and uses
`An(A) = A ∪ an(A)` freely; we take the union as the **definition** — so that
`DAG.subset_ancestralClosure` is immediate and no choice principle is involved — and prove the
book's characterisation as `DAG.isAncestralSet_ancestralClosure` (it *is* ancestral) together
with `DAG.ancestralClosure_subset_of_isAncestralSet` (it is contained in every ancestral
superset of `A`). *Edge behaviour.* `An(∅) = ∅`, and `An(A) = A` exactly when `A` is ancestral
(`DAG.ancestralClosure_eq_self_iff`). Note the contrast with `DAG.ancestors`: `A ⊆ An(A)`
whereas `v ∉ an(v)`. -/
def ancestralClosure [Fintype V] [DecidableEq V] (D : DAG V)
    [DecidableRel (Relation.TransGen D.Adj)] (A : Finset V) : Finset V :=
  A ∪ A.biUnion D.ancestors

section AncestralClosure

variable [Fintype V] [DecidableEq V]

/-- Membership in `An(A)`: `u ∈ An(A)` exactly when `u` reaches some element of `A`, the
reflexive reading (`Relation.ReflTransGen`) capturing both `u ∈ A` and `u ∈ an(v)` for some
`v ∈ A`. -/
theorem mem_ancestralClosure {D : DAG V} [DecidableRel (Relation.TransGen D.Adj)]
    {A : Finset V} {u : V} :
    u ∈ D.ancestralClosure A ↔ ∃ v ∈ A, Relation.ReflTransGen D.Adj u v := by
  simp only [ancestralClosure, Finset.mem_union, Finset.mem_biUnion, mem_ancestors]
  constructor
  · rintro (h | ⟨v, hv, h⟩)
    · exact ⟨u, h, Relation.ReflTransGen.refl⟩
    · exact ⟨v, hv, h.to_reflTransGen⟩
  · rintro ⟨v, hv, h⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | h
    · exact Or.inl hv
    · exact Or.inr ⟨v, hv, h⟩

/-- **Extensivity**: `A ⊆ An(A)`. Immediate from the definition as a union. -/
theorem subset_ancestralClosure (D : DAG V) [DecidableRel (Relation.TransGen D.Adj)]
    (A : Finset V) :
    A ⊆ D.ancestralClosure A :=
  Finset.subset_union_left

/-- **`An(A)` is ancestral** — the first half of Lauritzen's characterisation. -/
theorem isAncestralSet_ancestralClosure (D : DAG V) [DecidableRel (Relation.TransGen D.Adj)]
    (A : Finset V) :
    D.IsAncestralSet (D.ancestralClosure A) := by
  intro u v huv hv
  obtain ⟨w, hw, h⟩ := mem_ancestralClosure.mp hv
  exact mem_ancestralClosure.mpr ⟨w, hw, Relation.ReflTransGen.head huv h⟩

/-- **Minimality**: `An(A)` is contained in every ancestral set containing `A` — the second half
of Lauritzen's characterisation, and the form Corollary 3.23 needs. -/
theorem ancestralClosure_subset_of_isAncestralSet {D : DAG V}
    [DecidableRel (Relation.TransGen D.Adj)] {A B : Finset V}
    -- USER-INPUT: the ancestral superset; Lauritzen §2.1.1, p. 7 ("the smallest ancestral set
    -- containing `A`")
    (hB : D.IsAncestralSet B)
    -- USER-INPUT: the containment; Lauritzen §2.1.1, p. 7
    (hAB : A ⊆ B) :
    D.ancestralClosure A ⊆ B := by
  intro u hu
  obtain ⟨v, hv, h⟩ := mem_ancestralClosure.mp hu
  exact hB.reflTransGen_mem h (hAB hv)

/-- **Monotonicity** of the ancestral closure. -/
theorem ancestralClosure_mono {D : DAG V} [DecidableRel (Relation.TransGen D.Adj)]
    {A B : Finset V}
    -- USER-INPUT: the containment of blocks; free choice of the caller (Lauritzen §2.1.1, p. 7)
    (hAB : A ⊆ B) :
    D.ancestralClosure A ⊆ D.ancestralClosure B :=
  ancestralClosure_subset_of_isAncestralSet (D.isAncestralSet_ancestralClosure B)
    (hAB.trans (D.subset_ancestralClosure B))

/-- **`An(A) = A` characterises ancestral sets.** -/
theorem ancestralClosure_eq_self_iff (D : DAG V) [DecidableRel (Relation.TransGen D.Adj)]
    (A : Finset V) :
    D.ancestralClosure A = A ↔ D.IsAncestralSet A := by
  constructor
  · intro h
    rw [← h]
    exact D.isAncestralSet_ancestralClosure A
  · intro h
    exact Finset.Subset.antisymm
      (ancestralClosure_subset_of_isAncestralSet h (Finset.Subset.refl A))
      (D.subset_ancestralClosure A)

/-- **Idempotence**: `An(An(A)) = An(A)`, i.e. `An` is a closure operator. Corollary of
`DAG.isAncestralSet_ancestralClosure` and `DAG.ancestralClosure_eq_self_iff`. -/
theorem ancestralClosure_idem (D : DAG V) [DecidableRel (Relation.TransGen D.Adj)]
    (A : Finset V) :
    D.ancestralClosure (D.ancestralClosure A) = D.ancestralClosure A :=
  (D.ancestralClosure_eq_self_iff _).mpr (D.isAncestralSet_ancestralClosure A)

end AncestralClosure

/-! ### Topological order

Lauritzen uses a *well-ordering* of the vertices compatible with the edges throughout the
recursive-factorization theory (§3.2.2, p. 46): the recursive factorization `(DF)` is stated
relative to an ordering in which the parents of a vertex precede it. On a finite vertex set the
two statements below supply such an ordering. -/

/-- **Szpilrajn for a DAG**: reachability extends to a linear order, so every ancestor precedes
its descendants. -/
theorem exists_linearOrder_extending (D : DAG V) :
    ∃ s : V → V → Prop, IsLinearOrder V s ∧
      ∀ ⦃u v : V⦄, Relation.ReflTransGen D.Adj u v → s u v := by
  haveI := D.isPartialOrder_reflTransGen
  obtain ⟨s, hs, hle⟩ := extend_partialOrder (Relation.ReflTransGen D.Adj)
  exact ⟨s, hs, fun _ _ h => hle _ _ h⟩

/-- **Topological order on a finite vertex set**: an enumeration of `V` by
`Fin (Fintype.card V)` in which every ancestor precedes its descendant — in particular every
parent precedes its child (take `Relation.TransGen.single`).

*Edge behaviour.* On the empty vertex type the equivalence is the empty one and the statement is
vacuous. -/
theorem exists_topologicalOrder [Fintype V] (D : DAG V) :
    ∃ f : V ≃ Fin (Fintype.card V), ∀ ⦃u v : V⦄, Relation.TransGen D.Adj u v → f u < f v := by
  classical
  obtain ⟨s, hs, hle⟩ := D.exists_linearOrder_extending
  letI : LinearOrder V :=
    { le := s
      le_refl := hs.1.1.1.1
      le_trans := hs.1.1.2.1
      le_antisymm := hs.1.2.1
      le_total := hs.2.1
      toDecidableLE := Classical.decRel _ }
  refine ⟨(monoEquivOfFin V (rfl : Fintype.card V = Fintype.card V)).symm.toEquiv,
    fun u v h => ?_⟩
  have hlt : u < v := by
    refine lt_of_le_of_ne (hle h.to_reflTransGen) ?_
    rintro rfl
    exact D.acyclic u h
  exact (monoEquivOfFin V (rfl : Fintype.card V = Fintype.card V)).symm.lt_iff_lt.mpr hlt

/-! ### The induced sub-DAG

Lauritzen's `G_A` (§2.1.1, p. 7). See the module docstring, note 5, for why the vertex type is
kept fixed. -/

/-- The **sub-DAG induced on `A`** (Lauritzen `G_A`, §2.1.1, p. 7): keep exactly the edges with
both endpoints in `A`.

*Book vs Lean.* The vertex type stays `V`; vertices outside `A` survive as isolated points
rather than being deleted. Every edge of `D.induce A` has both endpoints in `A`
(`DAG.mem_of_induce_adj`), so the isolated points take part in no directed chain and, after
moralization, in no walk — which is why this presentation proves the same theorems as the book's
vertex-deleting `G_A` while keeping the `Finset V`-indexed vocabulary applicable.
Acyclicity is inherited by `IsAcyclicRel.mono`. *Edge behaviour.* `D.induce Finset.univ = D`
(`DAG.induce_univ`) and `D.induce ∅` is the empty graph. -/
def induce (D : DAG V) (A : Finset V) : DAG V where
  Adj u v := u ∈ A ∧ v ∈ A ∧ D.Adj u v
  acyclic := IsAcyclicRel.mono D.acyclic fun _ _ h => h.2.2

/-- Edge-decidability is inherited by the induced sub-DAG (`Finset` membership is decidable), so
`DAG.parents` and the moral graph of `D.induce A` are available without a fresh assumption. -/
instance instDecidableRelInduceAdj (D : DAG V) [DecidableEq V] [DecidableRel D.Adj]
    (A : Finset V) : DecidableRel (D.induce A).Adj := fun u v =>
  inferInstanceAs (Decidable (u ∈ A ∧ v ∈ A ∧ D.Adj u v))

@[simp]
theorem induce_adj (D : DAG V) (A : Finset V) (u v : V) :
    (D.induce A).Adj u v ↔ u ∈ A ∧ v ∈ A ∧ D.Adj u v := Iff.rfl

/-- Both endpoints of an induced edge lie in `A` — the fact that keeps the isolated vertices of
`DAG.induce` harmless. -/
theorem mem_of_induce_adj {D : DAG V} {A : Finset V} {u v : V}
    -- USER-INPUT: the induced edge; Lauritzen §2.1.1, p. 7 (`G_A`)
    (h : (D.induce A).Adj u v) :
    u ∈ A ∧ v ∈ A :=
  ⟨h.1, h.2.1⟩

/-- An induced edge is an edge. -/
theorem adj_of_induce_adj {D : DAG V} {A : Finset V} {u v : V}
    -- USER-INPUT: the induced edge; Lauritzen §2.1.1, p. 7 (`G_A`)
    (h : (D.induce A).Adj u v) :
    D.Adj u v :=
  h.2.2

/-- **Monotonicity in the vertex block**: enlarging `A` only adds edges. -/
theorem induce_adj_mono {D : DAG V} {A B : Finset V}
    -- USER-INPUT: the containment of vertex blocks; free choice of the caller
    -- (Lauritzen §2.1.1, p. 7)
    (hAB : A ⊆ B) {u v : V}
    -- USER-INPUT: the smaller induced edge; Lauritzen §2.1.1, p. 7
    (h : (D.induce A).Adj u v) :
    (D.induce B).Adj u v :=
  ⟨hAB h.1, hAB h.2.1, h.2.2⟩

/-- Inducing on everything changes nothing. -/
theorem induce_univ [Fintype V] (D : DAG V) : D.induce Finset.univ = D := by
  ext u v
  simp

/-- **Parents in the induced sub-DAG**: for a vertex of `A`, they are the parents that lie in
`A`. -/
theorem parents_induce_of_mem [Fintype V] [DecidableEq V] (D : DAG V) [DecidableRel D.Adj]
    {A : Finset V} {v : V}
    -- USER-INPUT: the vertex lies in the induced block; Lauritzen §2.1.1, p. 7
    (hv : v ∈ A) :
    (D.induce A).parents v = D.parents v ∩ A := by
  ext u
  simp only [mem_parents, induce_adj, Finset.mem_inter]
  exact ⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, hv, h.1⟩⟩

/-- **On an ancestral set the parent sets are unchanged** — `pa_{G_A}(v) = pa_G(v)` for `v ∈ A`.
This is the load-bearing property of ancestral sets: it is why Lauritzen's Corollary 3.23 may
restrict a recursive factorization to `An(A ∪ B ∪ S)` without changing any of the conditional
distributions, and hence why d-separation may be read off the moral graph of the induced
sub-DAG. -/
theorem parents_induce_of_isAncestralSet [Fintype V] [DecidableEq V] (D : DAG V)
    [DecidableRel D.Adj] {A : Finset V}
    -- USER-INPUT: the block is ancestral; Lauritzen §2.1.1, p. 7 (the hypothesis of Cor. 3.23,
    -- p. 47, where the block is `An(A ∪ B ∪ S)`)
    (hA : D.IsAncestralSet A) {v : V}
    -- USER-INPUT: the vertex lies in the block; Lauritzen §2.1.1, p. 7
    (hv : v ∈ A) :
    (D.induce A).parents v = D.parents v := by
  rw [D.parents_induce_of_mem hv, Finset.inter_eq_left]
  intro u hu
  exact hA (mem_parents.mp hu) hv

end DAG

end StatLean.StatisticalModels.GraphicalModels
