module
public import StatLean.StatisticalModels.GraphicalModels.Core.Separation
public import StatLean.StatisticalModels.GraphicalModels.Directed.DAG
public import StatLean.StatisticalModels.GraphicalModels.Directed.Moralization
public import StatLean.StatisticalModels.GraphicalModels.Directed.Markov
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# d-separation — Pearl's criterion, and its equivalence with moral-graph separation

Lauritzen's *chain* criterion for reading conditional independence off a directed acyclic
graph (p. 48, an **unnumbered** definition), together with the theorem that makes the whole
undirected layer of this area available to the directed theory: d-separation in `G` is
*exactly* separation in the moral graph of the smallest ancestral set containing the three
blocks (**Proposition 3.25**, p. 48).

* `ArrowDir`, `IsCollider` — the orientation vocabulary. `ArrowDir` records how one arrow of a
  chain sits relative to a vertex it is incident to (`into` / `outOf`); `Option ArrowDir` adds
  `none` for "there is no arrow on that side", which happens exactly at the two ends of the
  chain. `IsCollider din dout` is Lauritzen's "arrows of the chain **meet head-to-head**": both
  incident arrows point into the vertex. Endpoints are never colliders
  (`not_isCollider_none_left`, `not_isCollider_none_right`);
* `Chain` — a chain from `u` to `w`: a sequence of vertices in which consecutive vertices are
  joined by an arrow **in either direction**, the direction of each step being recorded by the
  constructor used (`fwd` / `bwd`). See *"Book vs Lean"* note 1 below for why this rather than
  a walk in the underlying undirected graph. `Chain.support`, `Chain.reverse` mirror
  `SimpleGraph.Walk`;
* `NoDescendantIn`, `BlocksAt` — the two clauses of Lauritzen's blocking rule at a single
  vertex occurrence: a **non-collider** blocks when it lies in `S`; a **collider** blocks when
  neither it nor any of its descendants lies in `S`;
* `Chain.BlockedFrom`, `Chain.Blocked`, `Chain.Active` — blocking of a whole chain, defined by
  structural recursion that carries the direction of the incoming arrow along;
* `DSeparated r S A B` — every chain from a vertex of `A` to a vertex of `B` is blocked by `S`;
* `dSeparated_symm`, `dSeparated_mono_left` / `_right`, `dSeparated_empty_left` / `_right`,
  `dSeparated_self_left` / `_right` — the API mirroring `Core.Separation`. **There is no
  monotonicity in the separator**: enlarging `S` can *unblock* a collider, and
  `not_forall_dSeparated_of_subset_sep` is the machine-checkable refutation, witnessed by the
  three-vertex collider `0 → 2 ← 1`. This is the one structural difference between
  d-separation and `Separates`;
* the graph `(G_{An(A ∪ B ∪ S)})^m` in which Proposition 3.25 reads is
  `Markov.ancestralMoralGraph`;
* `dSeparated_iff_separates_moralGraph_ancestralClosure` — **Proposition 3.25**, the headline:
  for disjoint `A`, `B`, `S` in a DAG, `S` d-separates `A` from `B` **iff** `S` separates `A`
  from `B` in `(G_{An(A ∪ B ∪ S)})^m`;
* `dSeparated_iff_forall_nodup` — the book's own phrasing, over chains with *distinct* vertices
  (see note 1); **not** a corollary of Proposition 3.25 — proved by shortening a chain of
  minimal length, over `Chain.exists_shorter_of_not_nodup` and `Chain.forward_run`;
* `condIndep_of_dSeparated` — the consequence: under the **directed global Markov property**,
  d-separation implies conditional independence. Cited as **Proposition 3.25 + Corollary
  3.23**; see the reference block for why there is no single theorem number for it.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, 1996:

* *chain*: §2.1.1, p. 6, **unnumbered** — "a chain of length `n` from `α` to `β` is a sequence
  `α = α₀, …, αₙ = β` of distinct vertices such that `αᵢ₋₁ → αᵢ` or `αᵢ → αᵢ₋₁` for all `i`";
* *blocked / active / d-separated*: §3.2.2, p. 48, **unnumbered**, credited to Pearl (1986) with
  the formal treatment in Verma and Pearl (1990) — "a chain `π` from `a` to `b` is said to be
  blocked by `S` if it contains a vertex `γ ∈ π` such that either `γ ∈ S` and arrows of `π` do
  not meet head-to-head at `γ`, or `γ ∉ S` nor has `γ` any descendants in `S`, and arrows of `π`
  do meet head-to-head at `γ`. A chain that is not blocked by `S` is said to be active. Two
  subsets `A` and `B` are now said to be d-separated by `S` if all chains from `A` to `B` are
  blocked by `S`";
* **Proposition 3.25**, p. 48 — for **disjoint** `A`, `B`, `S`, `S` d-separates `A` from `B` iff
  `S` separates `A` from `B` in `(G_{An(A∪B∪S)})^m`;
* **Corollary 3.23**, p. 47 — the conditional independence `A ⫫ B ∣ S` holds whenever `A` and
  `B` are separated by `S` in `(G_{An(A∪B∪S)})^m`; "the property in Corollary 3.23 will be
  referred to as the **directed global Markov property (DG)**".

⚠️ **There is no single numbered theorem "d-separation ⟺ directed global Markov".** The book
gives (DG) a *moral-graph* definition (Cor. 3.23) and then proves separately that d-separation
is equivalent to it (Prop. 3.25). `condIndep_of_dSeparated` is therefore tagged with **both**
numbers, and its proof is literally "Prop. 3.25, then (DG)". Citing it as one theorem would
misattribute (`Lauritzen §3.2.2` in tags).

**Proof formalization notes.** *Book vs Lean, four deliberate differences.*

1. **Chains are oriented walks; the book's chains have distinct vertices.** Lauritzen's chain
   (p. 6) is a sequence of *distinct* vertices. `Chain` drops the distinctness, exactly as
   `Core.Separation.Separates` is phrased over `SimpleGraph.Walk` rather than
   `SimpleGraph.Path`: `Chain` is the type carrying the induction principle that
   `Chain.BlockedFrom` and every proof below run on, and adding a `Nodup` side condition to the
   *definition* would make the recursion carry a proof obligation it does not need. The two
   readings of d-separation agree — `dSeparated_iff_forall_nodup` — but, unlike in the
   undirected case, this is **not** `Walk.bypass`: shortening a chain can turn a non-collider
   into a **collider**, and a collider is exactly what blocks when nothing below it lies in `S`.
   ⚠️ The equivalence is also **not** a corollary of Proposition 3.25: that proposition is
   proved here only for the walk reading, and the chain its proof builds out of a moral walk
   need not have distinct vertices. It is proved directly instead, by shortening a chain of
   **minimal length**: `Chain.exists_shorter_of_not_nodup` shows the merged occurrence cannot
   block, the one dangerous configuration being ruled out by acyclicity (`Chain.forward_run`).
   Consequently the proof uses only the DAG hypothesis, **not** the disjointness of the three
   blocks, which the statement nevertheless carries.
2. **Orientation is data, not a proposition.** The direction of each step is recorded by the
   constructor used (`fwd`/`bwd`), so "arrows meet head-to-head at `γ`" is a *structural*
   condition of the recursion rather than a proposition recovered by case analysis on which of
   `r u v`, `r v u` holds. It needs no decidability of `r` and no acyclicity — so the vocabulary
   is available for an arbitrary relation, and the DAG hypotheses appear only where they are
   genuinely used (Proposition 3.25 and below). The moral graph is *not* the underlying
   undirected graph anyway (it has extra marriage edges), so the two sides of Proposition 3.25
   are walks in different graphs.
3. **Blocking is evaluated at vertex *occurrences*.** Lauritzen writes "it contains a vertex
   `γ ∈ π`"; a chain that repeats a vertex meets it with different pairs of incident arrows
   each time, and the same vertex may be a collider at one occurrence and not at another. The
   recursion visits occurrences, which is the reading the book's proof uses.
4. **The blocking rule is stated over a bare relation, and `S`-monotonicity is refuted rather
   than proved.** `Chain`, `BlocksAt`, `Blocked` and `DSeparated` take `r : V → V → Prop`;
   a DAG-level consumer writes `DSeparated D.Adj S A B`. Nothing in these definitions uses
   acyclicity. Compared with `Separates`, exactly one API lemma is missing and cannot be added:
   `separates_of_subset_sep` has **no** d-separation analogue, because conditioning on a
   collider opens the chain through it. `not_forall_dSeparated_of_subset_sep` records this.

**Bibliographic comments.** The criterion is J. Pearl's, "Fusion, propagation, and structuring
in belief networks", *Artificial Intelligence* **29** (1986), 241–288, with the full formal
treatment in T. Verma and J. Pearl, "Causal networks: semantics and expressiveness", in
*Uncertainty in Artificial Intelligence 4*, North-Holland, 1990, 69–76; Lauritzen presents it
as "an alternative formulation of the directed global Markov property" (p. 48). Lauritzen's
remark following Proposition 3.25 (p. 50, equation **(3.22)**) records that **the criterion
cannot be improved**: D. Geiger and J. Pearl, "On the logic of causal models", in *Uncertainty
in Artificial Intelligence 4*, North-Holland, 1990, show in their Theorem 5 that for any
directed acyclic graph `G` one can choose state spaces and a probability `P` for which
`A ⫫ B ∣ S ⟺ S` d-separates `A` from `B` — so no strictly finer graphical rule reads more
conditional independences out of the graph than d-separation does. That is a statement about
the *existence of a law*, quantified over state spaces, and is recorded here as a remark only:
it is far outside this file's scope and is deliberately **not** stated in Lean.
-/

namespace StatLean.StatisticalModels.GraphicalModels

universe u

variable {V : Type u}

/-! ### Orientation vocabulary -/

/-- The direction of one arrow of a chain, **read from a vertex it is incident to**: `into` if
the arrow points at that vertex, `outOf` if it points away from it.

*Edge behaviour.* The two ends of a chain have an arrow on one side only; the missing side is
represented by `none : Option ArrowDir` rather than by a third constructor, so that
`IsCollider` can be stated uniformly at every vertex occurrence of a chain, endpoints
included. -/
inductive ArrowDir where
  /-- The arrow points at the vertex. -/
  | into : ArrowDir
  /-- The arrow points away from the vertex. -/
  | outOf : ArrowDir
  deriving DecidableEq

/-- **Arrows meet head-to-head** (Lauritzen p. 48): the two arrows of a chain incident to a
vertex both point *into* it. `din` is the direction of the arrow on the near side of the chain
and `dout` the direction of the arrow on the far side, each `none` when there is no such arrow.

*Edge behaviour.* At an end of the chain one of the two is `none`, so `IsCollider` is false
there (`not_isCollider_none_left`, `not_isCollider_none_right`): only *interior* vertex
occurrences can be colliders, which is what Lauritzen's phrase "arrows of `π` meet head-to-head
at `γ`" means. Symmetric in its two arguments (`isCollider_comm`), so the notion does not
depend on which end of the chain one starts from. -/
def IsCollider (din dout : Option ArrowDir) : Prop :=
  din = some ArrowDir.into ∧ dout = some ArrowDir.into

/-- An end of the chain on the near side is never a collider. -/
@[simp]
theorem not_isCollider_none_left (dout : Option ArrowDir) : ¬ IsCollider none dout := by
  simp [IsCollider]

/-- An end of the chain on the far side is never a collider. -/
@[simp]
theorem not_isCollider_none_right (din : Option ArrowDir) : ¬ IsCollider din none := by
  simp [IsCollider]

/-- An arrow pointing *away* from the vertex on the near side rules out a head-to-head meeting. -/
@[simp]
theorem not_isCollider_outOf_left (dout : Option ArrowDir) :
    ¬ IsCollider (some ArrowDir.outOf) dout := by
  simp [IsCollider]

/-- An arrow pointing *away* from the vertex on the far side rules out a head-to-head meeting. -/
@[simp]
theorem not_isCollider_outOf_right (din : Option ArrowDir) :
    ¬ IsCollider din (some ArrowDir.outOf) := by
  simp [IsCollider]

/-- Two arrows pointing into the vertex **do** meet head-to-head — the only positive instance of
`IsCollider`. -/
theorem isCollider_into_into : IsCollider (some ArrowDir.into) (some ArrowDir.into) :=
  ⟨rfl, rfl⟩

/-- Being a collider does not depend on the direction the chain is traversed in. -/
theorem isCollider_comm (din dout : Option ArrowDir) :
    IsCollider din dout ↔ IsCollider dout din :=
  and_comm

/-! ### Chains -/

/-- A **chain** from `u` to `w` for the relation `r`: a sequence of vertices in which
consecutive vertices are joined by an arrow, traversed in either direction, **together with the
direction of each step**. `fwd h c` prepends a step `u → v` (so `h : r u v`) and `bwd h c`
prepends a step `u ← v` (so `h : r v u`), in both cases continuing along `c` from `v`.

This is Lauritzen's chain (§2.1.1, p. 6) *without* the requirement that the vertices be
distinct — i.e. an oriented walk. See the module docstring, note 1, for why, and
`dSeparated_iff_forall_nodup` for the book's phrasing. Modelled on `SimpleGraph.Walk`, whose
`support` / `reverse` API is mirrored below.

*Edge behaviour.* `Chain.nil v : Chain r v v` is the chain of length `0`; it has one vertex, no
arrows, and is blocked by `S` exactly when `v ∈ S`. Nothing here assumes `r` irreflexive or
acyclic: a self-loop `r v v` yields chains, and `Chain` is well-defined for any relation. -/
inductive Chain (r : V → V → Prop) : V → V → Type u
  /-- The chain of length `0` at `v`. -/
  | nil (v : V) : Chain r v v
  /-- Prepend a step traversed **along** its arrow: `u → v`, then continue from `v`. -/
  | fwd {u v w : V} (h : r u v) (c : Chain r v w) : Chain r u w
  /-- Prepend a step traversed **against** its arrow: `u ← v`, then continue from `v`. -/
  | bwd {u v w : V} (h : r v u) (c : Chain r v w) : Chain r u w

namespace Chain

variable {r : V → V → Prop}

/-- The vertices a chain visits, in order, with multiplicity — the analogue of
`SimpleGraph.Walk.support`. -/
def support : ∀ {u w : V}, Chain r u w → List V
  | u, _, nil _ => [u]
  | u, _, fwd _ c => u :: c.support
  | u, _, bwd _ c => u :: c.support

@[simp]
theorem support_nil (v : V) : (nil v : Chain r v v).support = [v] := rfl

@[simp]
theorem support_fwd {u v w : V} (h : r u v) (c : Chain r v w) :
    (fwd h c).support = u :: c.support := rfl

@[simp]
theorem support_bwd {u v w : V} (h : r v u) (c : Chain r v w) :
    (bwd h c).support = u :: c.support := rfl

/-- The number of arrows of a chain — the analogue of `SimpleGraph.Walk.length`, and the measure
`dSeparated_iff_forall_nodup` inducts on. -/
def length : ∀ {u w : V}, Chain r u w → ℕ
  | _, _, nil _ => 0
  | _, _, fwd _ c => c.length + 1
  | _, _, bwd _ c => c.length + 1

@[simp]
theorem length_nil (v : V) : (nil v : Chain r v v).length = 0 := rfl

@[simp]
theorem length_fwd {u v w : V} (h : r u v) (c : Chain r v w) :
    (fwd h c).length = c.length + 1 := rfl

@[simp]
theorem length_bwd {u v w : V} (h : r v u) (c : Chain r v w) :
    (bwd h c).length = c.length + 1 := rfl

theorem start_mem_support {u w : V} (c : Chain r u w) : u ∈ c.support := by
  cases c <;> simp

theorem end_mem_support {u w : V} (c : Chain r u w) : w ∈ c.support := by
  induction c with
  | nil v => simp
  | fwd _ _ ih => simp [ih]
  | bwd _ _ ih => simp [ih]

/-- Concatenate the reverse of the first chain with the second — the engine of `Chain.reverse`,
modelled on `SimpleGraph.Walk.reverseAux`. Reversing swaps the roles of `fwd` and `bwd`, which
is the whole content of "a chain may be traversed from either end". -/
def reverseAux : ∀ {u v w : V}, Chain r u v → Chain r u w → Chain r v w
  | _, _, _, nil _, q => q
  | _, _, _, fwd h p, q => reverseAux p (bwd h q)
  | _, _, _, bwd h p, q => reverseAux p (fwd h q)

/-- A chain read from its far end. Each step keeps its arrow and changes its traversal
direction. -/
def reverse {u w : V} (c : Chain r u w) : Chain r w u := c.reverseAux (nil u)

/-- The direction, **read at the first vertex of the chain**, of the arrow leaving it — `none`
for the chain of length `0`, which has no arrow at all.

This is the bookkeeping device of `Chain.blocked_reverse`: it names the `dout` argument that the
recursion of `Chain.BlockedFrom` reads off the constructor at the chain's own first vertex, so
that gluing two chains at a common first vertex (which is exactly what `Chain.reverseAux` does)
can be stated without unfolding the recursion. -/
def headDir : ∀ {u w : V}, Chain r u w → Option ArrowDir
  | _, _, nil _ => none
  | _, _, fwd _ _ => some ArrowDir.outOf
  | _, _, bwd _ _ => some ArrowDir.into

@[simp]
theorem headDir_nil (v : V) : (nil v : Chain r v v).headDir = none := rfl

@[simp]
theorem headDir_fwd {u v w : V} (h : r u v) (c : Chain r v w) :
    (fwd h c).headDir = some ArrowDir.outOf := rfl

@[simp]
theorem headDir_bwd {u v w : V} (h : r v u) (c : Chain r v w) :
    (bwd h c).headDir = some ArrowDir.into := rfl

end Chain

/-! ### Blocking -/

/-- `γ` has **no descendant in `S`**, counting `γ` itself among its own descendants.

This is the second clause of Lauritzen's blocking rule (p. 48), "`γ ∉ S` nor has `γ` any
descendants in `S`", read as the single condition `De(γ) ∩ S = ∅` with
`De(γ) = {γ} ∪ de(γ)`: Lauritzen's `de(γ)` (§2.1.1, p. 6) excludes `γ`, and the reflexivity of
`Relation.ReflTransGen` puts it back, which is exactly the conjunction the book states.

*Book vs Lean.* Stated with `Relation.ReflTransGen` on a bare relation rather than with
`Directed.DAG.descendants`, so that `BlocksAt` is available before any DAG structure is fixed;
for `r = D.Adj` the two agree by unfolding `descendants`. *Edge behaviour.* Vacuously true for
`S = ∅`, so over an empty separator a chain is blocked exactly when it has a collider. -/
def NoDescendantIn (r : V → V → Prop) (S : Finset V) (γ : V) : Prop :=
  ∀ d : V, Relation.ReflTransGen r γ d → d ∉ S

/-- **Lauritzen's blocking rule at one vertex occurrence** (p. 48, unnumbered). The vertex `γ`
of a chain, met with incident arrow directions `din` (near side) and `dout` (far side), blocks
the chain relative to `S` when either

* the arrows do **not** meet head-to-head at `γ` and `γ ∈ S`, or
* they **do** meet head-to-head at `γ` and neither `γ` nor any descendant of `γ` is in `S`.

*Edge behaviour.* At an end of the chain (`din = none` or `dout = none`) the vertex is never a
collider, so the rule reduces to `γ ∈ S`; in particular a chain that starts or ends inside `S`
is blocked, which is what makes `dSeparated_self_left` / `_right` true and mirrors
`separates_self_left` / `_right`. The two clauses are mutually exclusive and exhaust the cases,
so `BlocksAt` is the negation of "`γ` leaves the chain open at this occurrence". -/
def BlocksAt (r : V → V → Prop) (S : Finset V) (din dout : Option ArrowDir) (γ : V) : Prop :=
  (¬ IsCollider din dout ∧ γ ∈ S) ∨ (IsCollider din dout ∧ NoDescendantIn r S γ)

/-- **Blocking at a vertex occurrence does not depend on which side the chain is entered from.**
Both clauses of `BlocksAt` mention the two arrow directions only through `IsCollider`, which is
symmetric (`isCollider_comm`); this is the pointwise content of `Chain.blocked_reverse`. -/
theorem blocksAt_comm {r : V → V → Prop} {S : Finset V} {din dout : Option ArrowDir} {γ : V} :
    BlocksAt r S din dout γ ↔ BlocksAt r S dout din γ := by
  unfold BlocksAt
  rw [isCollider_comm din dout]

/-- **At a non-collider the rule is "lie in the separator"** — the first clause of `BlocksAt`,
isolated. -/
theorem blocksAt_iff_mem_of_not_isCollider {r : V → V → Prop} {S : Finset V}
    {din dout : Option ArrowDir} {γ : V} (h : ¬ IsCollider din dout) :
    BlocksAt r S din dout γ ↔ γ ∈ S := by
  simp [BlocksAt, h]

/-- **At a collider the rule is "have no descendant in the separator"** — the second clause of
`BlocksAt`, isolated. -/
theorem blocksAt_iff_noDescendantIn_of_isCollider {r : V → V → Prop} {S : Finset V}
    {din dout : Option ArrowDir} {γ : V} (h : IsCollider din dout) :
    BlocksAt r S din dout γ ↔ NoDescendantIn r S γ := by
  simp [BlocksAt, h]

/-- An end of the chain on the near side blocks exactly when it lies in the separator. -/
theorem blocksAt_none_left {r : V → V → Prop} {S : Finset V} {dout : Option ArrowDir} {γ : V} :
    BlocksAt r S none dout γ ↔ γ ∈ S :=
  blocksAt_iff_mem_of_not_isCollider (not_isCollider_none_left dout)

/-- An end of the chain on the far side blocks exactly when it lies in the separator. -/
theorem blocksAt_none_right {r : V → V → Prop} {S : Finset V} {din : Option ArrowDir} {γ : V} :
    BlocksAt r S din none γ ↔ γ ∈ S :=
  blocksAt_iff_mem_of_not_isCollider (not_isCollider_none_right din)

namespace Chain

variable {r : V → V → Prop}

/-- **A chain is blocked by `S`**, given the direction `din` of the arrow entering its first
vertex from the part of the chain already traversed (`none` at the start of the whole chain).

Structural recursion on the chain: at each vertex the recursion knows the direction of the
arrow behind it (`din`, the accumulator) and reads the direction of the arrow ahead of it off
the constructor — `fwd` means the next arrow points *out of* the current vertex and *into* the
next one, `bwd` the other way round. The chain is blocked when *some* occurrence blocks
(`BlocksAt`), which is Lauritzen's "it contains a vertex `γ ∈ π` such that …".

*Edge behaviour.* On `nil` the far side is `none`, so the last vertex blocks exactly when it
lies in `S`. The accumulator is an implementation detail of the recursion; the user-facing
predicate is `Chain.Blocked`, which starts it at `none`. -/
def BlockedFrom (S : Finset V) : ∀ {u w : V}, Option ArrowDir → Chain r u w → Prop
  | γ, _, din, nil _ => BlocksAt r S din none γ
  | γ, _, din, fwd _ c =>
      BlocksAt r S din (some ArrowDir.outOf) γ ∨ BlockedFrom S (some ArrowDir.into) c
  | γ, _, din, bwd _ c =>
      BlocksAt r S din (some ArrowDir.into) γ ∨ BlockedFrom S (some ArrowDir.outOf) c

/-- **A chain is blocked by `S`** (Lauritzen p. 48): some vertex occurrence of it blocks. The
first vertex has no arrow behind it, whence the `none`. -/
def Blocked {u w : V} (c : Chain r u w) (S : Finset V) : Prop :=
  BlockedFrom S none c

/-- **A chain is active** (Lauritzen p. 48): "a chain that is not blocked by `S` is said to be
active". Definitionally the negation of `Chain.Blocked`; kept as a name because the book's
proofs, and the informal reading of d-separation, are phrased in terms of active chains. -/
def Active {u w : V} (c : Chain r u w) (S : Finset V) : Prop :=
  ¬ c.Blocked S

theorem active_iff_not_blocked {u w : V} (c : Chain r u w) (S : Finset V) :
    c.Active S ↔ ¬ c.Blocked S := Iff.rfl

/-! #### The recursion of `Chain.BlockedFrom`, as rewrite rules -/

@[simp]
theorem blockedFrom_nil {S : Finset V} {din : Option ArrowDir} (v : V) :
    BlockedFrom S din (nil v : Chain r v v) = BlocksAt r S din none v := rfl

@[simp]
theorem blockedFrom_fwd {S : Finset V} {din : Option ArrowDir} {u v w : V} (h : r u v)
    (c : Chain r v w) :
    BlockedFrom S din (fwd h c) =
      (BlocksAt r S din (some ArrowDir.outOf) u ∨ BlockedFrom S (some ArrowDir.into) c) := rfl

@[simp]
theorem blockedFrom_bwd {S : Finset V} {din : Option ArrowDir} {u v w : V} (h : r v u)
    (c : Chain r v w) :
    BlockedFrom S din (bwd h c) =
      (BlocksAt r S din (some ArrowDir.into) u ∨ BlockedFrom S (some ArrowDir.outOf) c) := rfl

/-- **Blocking at the first vertex already blocks the whole chain.** The only fact about the
recursion of `Chain.BlockedFrom` that the reversal argument needs: the recursion evaluates
`BlocksAt` at the first vertex with far-side direction `Chain.headDir`, and puts that disjunct
first. -/
theorem blockedFrom_of_blocksAt_headDir {S : Finset V} {din : Option ArrowDir} {u w : V}
    (c : Chain r u w) (h : BlocksAt r S din c.headDir u) : BlockedFrom S din c := by
  cases c with
  | nil v => exact h
  | fwd _ _ => exact Or.inl h
  | bwd _ _ => exact Or.inl h

/-- **The reversal identity for `Chain.reverseAux`.** `p.reverseAux q` glues the reverse of `p`
to `q` at their common first vertex `u`; a vertex occurrence of the glued chain blocks exactly
when it blocks in `p` — read from `u` with the arrow of `q` behind it — or in `q`, read from `u`
with the arrow of `p` behind it. The junction `u` itself is counted by *both* disjuncts, which is
harmless: `blocksAt_comm` says the two readings of it agree.

This is the statement that carries `Chain.blocked_reverse`: the two accumulators are exchanged,
which is exactly "reversing a chain exchanges the near and far side at every occurrence". -/
theorem blockedFrom_reverseAux {S : Finset V} {w : V} :
    ∀ {u v : V} (p : Chain r u v) (q : Chain r u w),
      BlockedFrom S none (p.reverseAux q) ↔
        BlockedFrom S q.headDir p ∨ BlockedFrom S p.headDir q := by
  intro u v p
  induction p with
  | nil x =>
      intro q
      simp only [reverseAux, headDir_nil, blockedFrom_nil]
      refine ⟨fun h => Or.inr h, ?_⟩
      rintro (h | h)
      · exact blockedFrom_of_blocksAt_headDir q (blocksAt_comm.mp h)
      · exact h
  | @fwd x y v hh p ih =>
      intro q
      have hp : BlocksAt r S p.headDir (some ArrowDir.into) y →
          BlockedFrom S (some ArrowDir.into) p := fun h =>
        blockedFrom_of_blocksAt_headDir p (blocksAt_comm.mp h)
      have hq : BlocksAt r S q.headDir (some ArrowDir.outOf) x →
          BlockedFrom S (some ArrowDir.outOf) q := fun h =>
        blockedFrom_of_blocksAt_headDir q (blocksAt_comm.mp h)
      change BlockedFrom S none (p.reverseAux (bwd hh q)) ↔ _
      rw [ih (bwd hh q)]
      simp only [headDir_bwd, headDir_fwd, blockedFrom_bwd, blockedFrom_fwd]
      tauto
  | @bwd x y v hh p ih =>
      intro q
      have hp : BlocksAt r S p.headDir (some ArrowDir.outOf) y →
          BlockedFrom S (some ArrowDir.outOf) p := fun h =>
        blockedFrom_of_blocksAt_headDir p (blocksAt_comm.mp h)
      have hq : BlocksAt r S q.headDir (some ArrowDir.into) x →
          BlockedFrom S (some ArrowDir.into) q := fun h =>
        blockedFrom_of_blocksAt_headDir q (blocksAt_comm.mp h)
      change BlockedFrom S none (p.reverseAux (fwd hh q)) ↔ _
      rw [ih (fwd hh q)]
      simp only [headDir_bwd, headDir_fwd, blockedFrom_bwd, blockedFrom_fwd]
      tauto

/-- **Blocking does not depend on the direction of traversal.** Reversing a chain exchanges the
near and far side at every vertex occurrence, and `IsCollider` is symmetric
(`isCollider_comm`), so the set of blocking occurrences is unchanged. This is what makes
d-separation symmetric in `A` and `B`, and it is the directed counterpart of
`Walk.support_reverse` in `separates_symm`.

The intended proof generalises over the accumulator: `BlockedFrom S din (p.reverseAux q)` is
`BlockedFrom` of `p` and of `q` glued at their common endpoint, with the two accumulators
exchanged. -/
theorem blocked_reverse {u w : V} (c : Chain r u w) (S : Finset V) :
    c.reverse.Blocked S ↔ c.Blocked S := by
  change BlockedFrom S none (c.reverseAux (nil u)) ↔ BlockedFrom S none c
  rw [blockedFrom_reverseAux c (nil u)]
  simp only [headDir_nil, blockedFrom_nil]
  refine ⟨?_, Or.inl⟩
  rintro (h | h)
  · exact h
  · exact blockedFrom_of_blocksAt_headDir c (blocksAt_comm.mp h)

/-- A chain that **starts** inside the separator is blocked: its first vertex has no arrow
behind it, hence is not a collider, hence blocks as soon as it lies in `S`. The directed
counterpart of the fact that a walk meets `S` at its own first vertex. -/
theorem blocked_of_start_mem {u w : V} (c : Chain r u w) {S : Finset V}
    -- USER-INPUT: the first vertex lies in the separator; Lauritzen p. 48 excludes this by
    -- assuming `A`, `B`, `S` disjoint, so this is a Lean-side completion of the definition
    (hu : u ∈ S) :
    c.Blocked S :=
  blockedFrom_of_blocksAt_headDir c (Or.inl ⟨not_isCollider_none_left _, hu⟩)

/-- A chain that **ends** inside the separator is blocked — the mirror image of
`blocked_of_start_mem`, via the last vertex. -/
theorem blocked_of_end_mem {u w : V} (c : Chain r u w) {S : Finset V}
    -- USER-INPUT: the last vertex lies in the separator; see `blocked_of_start_mem`
    (hw : w ∈ S) :
    c.Blocked S :=
  (blocked_reverse c S).mp (c.reverse.blocked_of_start_mem hw)

/-! #### Chains along a line of descent

The two constructions Proposition 3.25 reroutes through. Both are stated as *existence*
statements rather than as functions `Relation.ReflTransGen D.Adj x t → Chain D.Adj x t`, because
`Relation.ReflTransGen` is `Prop`-valued and `Chain` is `Type`-valued: a directed path is not
data here, so no chain can be *computed* from one. Every consumer below only ever needs the
chain to exist, so nothing is lost. -/

/-- **The accumulator matters only through `IsCollider`.** Two accumulators that both fail to
make the first vertex of a chain a collider give the same blocking: at a non-collider the rule is
membership of the separator, which does not mention the arrows at all. -/
theorem blockedFrom_congr_din {S : Finset V} {din din' : Option ArrowDir} {u w : V}
    (c : Chain r u w) (h : ¬ IsCollider din c.headDir) (h' : ¬ IsCollider din' c.headDir) :
    BlockedFrom S din c ↔ BlockedFrom S din' c := by
  cases c with
  | nil v => simp only [blockedFrom_nil, blocksAt_none_right]
  | fwd hh c' =>
      simp only [headDir_fwd] at h h'
      simp only [blockedFrom_fwd, blocksAt_iff_mem_of_not_isCollider h,
        blocksAt_iff_mem_of_not_isCollider h']
  | bwd hh c' =>
      simp only [headDir_bwd] at h h'
      simp only [blockedFrom_bwd, blocksAt_iff_mem_of_not_isCollider h,
        blocksAt_iff_mem_of_not_isCollider h']

/-- **A line of descent, read forwards, blocks nowhere.** If no descendant of `x` — `x` included
— lies in `S`, the directed path `x → ⋯ → t` is a chain on which every occurrence has an arrow
pointing *away* from it, hence is a non-collider, hence blocks only if it lies in `S`, which it
does not. The accumulator is arbitrary: the first vertex is a non-collider whatever sits behind
it, because the arrow ahead of it points away. -/
theorem exists_chain_of_reflTransGen {S : Finset V} {x t : V}
    (h : Relation.ReflTransGen r x t) :
    NoDescendantIn r S x → ∀ din : Option ArrowDir, ∃ c : Chain r x t, ¬ BlockedFrom S din c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro hnd din
      refine ⟨nil _, ?_⟩
      rw [blockedFrom_nil, blocksAt_none_right]
      exact hnd _ Relation.ReflTransGen.refl
  | head h1 h2 ih =>
      intro hnd din
      obtain ⟨c, hc⟩ :=
        ih (fun d hd => hnd d (Relation.ReflTransGen.head h1 hd)) (some ArrowDir.into)
      refine ⟨fwd h1 c, ?_⟩
      rw [blockedFrom_fwd]
      rintro (hb | hb)
      · exact hnd _ Relation.ReflTransGen.refl
          ((blocksAt_iff_mem_of_not_isCollider (not_isCollider_outOf_right din)).mp hb)
      · exact hc hb

/-- **A line of descent, read backwards, blocks nowhere either.** Prepending the reversed
descent `t ← ⋯ ← x` to a chain out of `x` keeps every new occurrence a non-collider — the arrow
behind points away, the arrow ahead points in — and every new vertex is a descendant of `x`,
hence outside `S`. The accumulator `outOf` is the one the junction `x` is left with, which is
exactly what `dSeparated_iff_separates_moralGraph_ancestralClosure` needs at a rerouted
collider. -/
theorem exists_chain_prepend_of_reflTransGen {S : Finset V} {x t : V}
    (h : Relation.ReflTransGen r x t) (hnd : NoDescendantIn r S x) {z : V} (c : Chain r x z)
    (hc : ¬ BlockedFrom S (some ArrowDir.outOf) c) :
    ∃ c' : Chain r t z, ¬ BlockedFrom S (some ArrowDir.outOf) c' := by
  induction h with
  | refl => exact ⟨c, hc⟩
  | tail h1 h2 ih =>
      obtain ⟨c'', hc''⟩ := ih
      refine ⟨bwd h2 c'', ?_⟩
      rw [blockedFrom_bwd]
      rintro (hb | hb)
      · exact hnd _ (h1.tail h2)
          ((blocksAt_iff_mem_of_not_isCollider (not_isCollider_outOf_left _)).mp hb)
      · exact hc'' hb

/-! #### Shortening a chain that repeats a vertex

The machinery of `dSeparated_iff_forall_nodup`. The book's chains have *distinct* vertices;
`Chain` does not (module docstring, note 1), and the two readings of d-separation are reconciled
here directly, not by a corollary of Proposition 3.25 — see `dSeparated_iff_forall_nodup` for
why that route does not close. -/

/-- **The accumulator matters only through the blocking of the first vertex.** Strengthens
`blockedFrom_congr_din`: it is enough that neither accumulator makes the *first occurrence*
block, whether or not it is a collider. -/
theorem blockedFrom_congr_din' {S : Finset V} {din din' : Option ArrowDir} {u w : V}
    (c : Chain r u w) (h : ¬ BlocksAt r S din c.headDir u)
    (h' : ¬ BlocksAt r S din' c.headDir u) :
    BlockedFrom S din c ↔ BlockedFrom S din' c := by
  cases c with
  | nil v => exact iff_of_false h h'
  | fwd hh c' =>
      simp only [headDir_fwd] at h h'
      simp only [blockedFrom_fwd, or_iff_right h, or_iff_right h']
  | bwd hh c' =>
      simp only [headDir_bwd] at h h'
      simp only [blockedFrom_bwd, or_iff_right h, or_iff_right h']

/-- **A chain entered along an arrow, out of a vertex with no descendant in `S`, runs forward
all the way.** Under `din = into`, a `bwd` step would make the first vertex a collider and — the
descendant clause being satisfied — block; so an unblocked chain can only take `fwd` steps, and
every vertex it visits is a descendant of its first one.

This is the observation that makes the shortening argument below work, and it is where
acyclicity enters `dSeparated_iff_forall_nodup`: a chain that comes back to its own starting
vertex under these conditions would close a directed cycle. -/
theorem forward_run {S : Finset V} : ∀ {x y : V} (c : Chain r x y), NoDescendantIn r S x →
    ¬ BlockedFrom S (some ArrowDir.into) c → ∀ z ∈ c.support, Relation.ReflTransGen r x z := by
  intro x y c
  induction c with
  | nil v =>
      intro _ _ z hz
      rw [support_nil, List.mem_singleton] at hz
      exact hz ▸ Relation.ReflTransGen.refl
  | @fwd x v y h c ih =>
      intro hnd hact z hz
      rw [blockedFrom_fwd, not_or] at hact
      rw [support_fwd, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.head h
          (ih (fun d hd => hnd d (Relation.ReflTransGen.head h hd)) hact.2 z hz)
  | @bwd x v y h c ih =>
      intro hnd hact _ _
      rw [blockedFrom_bwd, not_or] at hact
      exact absurd ((blocksAt_iff_noDescendantIn_of_isCollider isCollider_into_into).mpr hnd)
        hact.1

/-- **Every vertex a chain visits starts an unblocked tail of it.** Cutting a chain at an
occurrence of `z` leaves a chain from `z` to the same endpoint, no longer, which is unblocked for
the accumulator that occurrence carried. -/
theorem exists_suffix {S : Finset V} : ∀ {x y : V} (c : Chain r x y) (din : Option ArrowDir),
    ¬ BlockedFrom S din c → ∀ z ∈ c.support,
      ∃ (d : Option ArrowDir) (Q : Chain r z y), Q.length ≤ c.length ∧
        ¬ BlockedFrom S d Q := by
  intro x y c
  induction c with
  | nil v =>
      intro din hact z hz
      rw [support_nil, List.mem_singleton] at hz
      subst hz
      exact ⟨din, nil z, le_rfl, hact⟩
  | @fwd x v y h c ih =>
      intro din hact z hz
      rw [support_fwd, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨din, fwd h c, le_rfl, hact⟩
      · rw [blockedFrom_fwd, not_or] at hact
        obtain ⟨d, Q, hQ, hQb⟩ := ih (some ArrowDir.into) hact.2 z hz
        exact ⟨d, Q, hQ.trans (Nat.le_succ _), hQb⟩
  | @bwd x v y h c ih =>
      intro din hact z hz
      rw [support_bwd, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨din, bwd h c, le_rfl, hact⟩
      · rw [blockedFrom_bwd, not_or] at hact
        obtain ⟨d, Q, hQ, hQb⟩ := ih (some ArrowDir.outOf) hact.2 z hz
        exact ⟨d, Q, hQ.trans (Nat.le_succ _), hQb⟩

/-- **An unblocked chain that repeats a vertex can be shortened without becoming blocked.**

Deleting the stretch between two occurrences of `x` changes the blocking rule *only at `x`*,
whose two incident arrows are now the near one of the first occurrence and the far one of the
second. The surviving occurrence can therefore be a collider where neither of the original ones
was, which is exactly why `SimpleGraph.Walk.bypass` has no analogue here. It does not block all
the same:

* if the chain leaves `x` **along** an arrow at the first occurrence (`fwd`), then `x` cannot
  have all its descendants outside `S`: `Chain.forward_run` would make the second occurrence of
  `x` a descendant of `x`, i.e. a directed cycle. So the collider clause is satisfied;
* if it leaves `x` **against** an arrow (`bwd`) and the first occurrence is a collider, activity
  there already supplies a descendant in `S`; and if it is not a collider, neither is the merged
  occurrence, and `x ∉ S`. -/
theorem exists_shorter_of_not_nodup {S : Finset V} (hacyc : IsAcyclicRel r) :
    ∀ {x y : V} (c : Chain r x y) (din : Option ArrowDir), ¬ BlockedFrom S din c →
      ¬ c.support.Nodup →
      ∃ c' : Chain r x y, c'.length < c.length ∧ ¬ BlockedFrom S din c' := by
  intro x y c
  induction c with
  | nil v => intro _ _ hdup; exact absurd (by simp) hdup
  | @fwd x v y h c ih =>
      intro din hact hdup
      rw [blockedFrom_fwd, not_or] at hact
      have hxS : x ∉ S := fun hm =>
        hact.1 ((blocksAt_iff_mem_of_not_isCollider (not_isCollider_outOf_right din)).mpr hm)
      rw [support_fwd, List.nodup_cons, not_and_or, not_not] at hdup
      rcases hdup with hmem | hdup
      · -- `x` occurs again: it has a descendant in `S`, else the chain would close a cycle
        have hnd : ¬ NoDescendantIn r S x := fun hn =>
          hacyc x (Relation.TransGen.head' h
            (forward_run c (fun d hd => hn d (Relation.ReflTransGen.head h hd)) hact.2 x hmem))
        obtain ⟨d, Q, hQlen, hQb⟩ := exists_suffix c (some ArrowDir.into) hact.2 x hmem
        have hnew : ¬ BlocksAt r S din Q.headDir x := by
          rintro (⟨-, hm⟩ | ⟨-, hn⟩)
          · exact hxS hm
          · exact hnd hn
        refine ⟨Q, by simp only [length_fwd]; exact Nat.lt_succ_of_le hQlen, ?_⟩
        exact fun hb => hQb ((blockedFrom_congr_din' Q hnew
          (fun hb' => hQb (blockedFrom_of_blocksAt_headDir Q hb'))).mp hb)
      · obtain ⟨c', hlt, hb⟩ := ih (some ArrowDir.into) hact.2 hdup
        exact ⟨fwd h c', by simpa using hlt, by rw [blockedFrom_fwd, not_or]; exact ⟨hact.1, hb⟩⟩
  | @bwd x v y h c ih =>
      intro din hact hdup
      rw [blockedFrom_bwd, not_or] at hact
      rw [support_bwd, List.nodup_cons, not_and_or, not_not] at hdup
      rcases hdup with hmem | hdup
      · obtain ⟨d, Q, hQlen, hQb⟩ := exists_suffix c (some ArrowDir.outOf) hact.2 x hmem
        have hQhead : ¬ BlocksAt r S d Q.headDir x := fun hb' =>
          hQb (blockedFrom_of_blocksAt_headDir Q hb')
        have hnew : ¬ BlocksAt r S din Q.headDir x := by
          by_cases hcol : IsCollider din (some ArrowDir.into)
          · have hnd : ¬ NoDescendantIn r S x := fun hn =>
              hact.1 ((blocksAt_iff_noDescendantIn_of_isCollider hcol).mpr hn)
            rintro (⟨hnc, hm⟩ | ⟨-, hn⟩)
            · exact hQhead (Or.inl ⟨fun hc2 => hnc ⟨hcol.1, hc2.2⟩, hm⟩)
            · exact hnd hn
          · have hxS : x ∉ S := fun hm =>
              hact.1 ((blocksAt_iff_mem_of_not_isCollider hcol).mpr hm)
            rintro (⟨-, hm⟩ | ⟨hc2, -⟩)
            · exact hxS hm
            · exact hcol ⟨hc2.1, rfl⟩
        refine ⟨Q, by simp only [length_bwd]; exact Nat.lt_succ_of_le hQlen, ?_⟩
        exact fun hb => hQb ((blockedFrom_congr_din' Q hnew hQhead).mp hb)
      · obtain ⟨c', hlt, hb⟩ := ih (some ArrowDir.outOf) hact.2 hdup
        exact ⟨bwd h c', by simpa using hlt, by rw [blockedFrom_bwd, not_or]; exact ⟨hact.1, hb⟩⟩

end Chain

/-! ### d-separation -/

/-- `S` **d-separates** `A` from `B` for the relation `r` (Lauritzen p. 48, unnumbered): every
chain from a vertex of `A` to a vertex of `B` is blocked by `S`.

*Book vs Lean.* Stated for a bare relation `r : V → V → Prop`; a consumer holding a
`D : DAG V` writes `DSeparated D.Adj S A B`. Nothing in the definition uses acyclicity — it is
needed only from `dSeparated_iff_separates_moralGraph_ancestralClosure` onwards — and stating
it here would make every basic lemma below carry a hypothesis it does not use. The argument
order `S A B` matches `Core.Separation.Separates`.

*Edge behaviour.* Vacuously true when `A = ∅` or `B = ∅` (`dSeparated_empty_left`,
`dSeparated_empty_right`), and automatically true when `A ⊆ S` or `B ⊆ S`
(`dSeparated_self_left`, `dSeparated_self_right`) since an endpoint of a chain is never a
collider. No disjointness of `A`, `B`, `S` is assumed, exactly as in `Separates`; Lauritzen's
disjointness is carried by the consumers that need it (Proposition 3.25 below). Unlike
`Separates`, this is **not** monotone in `S`: see `not_forall_dSeparated_of_subset_sep`. -/
def DSeparated (r : V → V → Prop) (S A B : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ c : Chain r a b, c.Blocked S

variable {r : V → V → Prop} {S A A' B B' : Finset V}

/-- **Symmetry.** d-separation is symmetric in the two separated blocks: reverse the chain
(`Chain.reverse`, `Chain.blocked_reverse`). -/
theorem dSeparated_symm
    -- USER-INPUT: the d-separation to be flipped; Lauritzen p. 48 (the book's definition is
    -- visibly symmetric, being phrased on chains, which have no preferred direction)
    (h : DSeparated r S A B) :
    DSeparated r S B A :=
  fun a ha b hb c => (Chain.blocked_reverse c S).mp (h b hb a ha c.reverse)

/-- **Symmetry, as an equivalence.** -/
theorem dSeparated_comm : DSeparated r S A B ↔ DSeparated r S B A :=
  ⟨dSeparated_symm, dSeparated_symm⟩

/-- **Monotone in the first block**: shrinking `A` preserves d-separation. -/
theorem dSeparated_mono_left
    -- USER-INPUT: the smaller first block; free choice of the caller (Lauritzen p. 48 blocks
    -- *all* chains from `A` to `B`, so a sub-block inherits it)
    (hA : A' ⊆ A)
    -- USER-INPUT: the d-separation to be weakened; Lauritzen p. 48
    (h : DSeparated r S A B) :
    DSeparated r S A' B :=
  fun a ha b hb c => h a (hA ha) b hb c

/-- **Monotone in the second block**: shrinking `B` preserves d-separation. -/
theorem dSeparated_mono_right
    -- USER-INPUT: the smaller second block; free choice of the caller (Lauritzen p. 48)
    (hB : B' ⊆ B)
    -- USER-INPUT: the d-separation to be weakened; Lauritzen p. 48
    (h : DSeparated r S A B) :
    DSeparated r S A B' :=
  fun a ha b hb c => h a ha b (hB hb) c

/-- **Degenerate case**: nothing to d-separate on the left. -/
theorem dSeparated_empty_left : DSeparated r S ∅ B :=
  fun a ha _ _ _ => absurd ha (Finset.notMem_empty a)

/-- **Degenerate case**: nothing to d-separate on the right. -/
theorem dSeparated_empty_right : DSeparated r S A ∅ :=
  fun _ _ b hb _ => absurd hb (Finset.notMem_empty b)

/-- **Degenerate case**: a block contained in the separator is d-separated from everything —
the first vertex of a chain is never a collider, so it blocks as soon as it lies in `S`. This
is the reason the book's disjointness assumption is not needed in the definition. -/
theorem dSeparated_self_left
    -- USER-INPUT: the first block sits inside the separator; the book excludes this case by
    -- assuming `A`, `B`, `S` disjoint, so this is a Lean-side completion of the definition
    (hAS : A ⊆ S) :
    DSeparated r S A B :=
  fun a ha _ _ c => c.blocked_of_start_mem (hAS ha)

/-- **Degenerate case**: dual of `dSeparated_self_left`, via the last vertex of the chain. -/
theorem dSeparated_self_right
    -- USER-INPUT: the second block sits inside the separator; see `dSeparated_self_left`
    (hBS : B ⊆ S) :
    DSeparated r S A B :=
  fun _ _ b hb c => c.blocked_of_end_mem (hBS hb)

/-- **Adjacent vertices are never d-separated.** The one-arrow chain `a → b` has two vertices,
both ends, hence both non-colliders; if neither lies in `S` the chain is active. The directed
counterpart of the fact that an edge defeats every separator disjoint from its endpoints. -/
theorem not_dSeparated_of_rel {a b : V}
    -- USER-INPUT: the arrow; Lauritzen §2.1.1, p. 5
    (hab : r a b)
    -- USER-INPUT: the tail is outside the separator; Lauritzen p. 48 assumes `A`, `S` disjoint
    (haS : a ∉ S)
    -- USER-INPUT: the head is outside the separator; Lauritzen p. 48 assumes `B`, `S` disjoint
    (hbS : b ∉ S) :
    ¬ DSeparated r S {a} {b} := by
  intro h
  have hb := h a (Finset.mem_singleton_self a) b (Finset.mem_singleton_self b)
    (Chain.fwd hab (Chain.nil b))
  -- the two vertices of a one-arrow chain are both *ends*, hence both non-colliders
  have hb' : BlocksAt r S none (some ArrowDir.outOf) a ∨
      BlocksAt r S (some ArrowDir.into) none b := hb
  rcases hb' with h1 | h1
  · exact haS (blocksAt_none_left.mp h1)
  · exact hbS (blocksAt_none_right.mp h1)

/-! ### The separator is not monotone — refutation

`Core.Separation.separates_of_subset_sep` says that growing the separator preserves undirected
separation. **The d-separation analogue is false**, and this section refutes it rather than
leaving a plausible-looking lemma unstated. The obstruction is the second clause of the
blocking rule: a collider blocks only while neither it nor any of its descendants lies in `S`,
so putting the collider *into* `S` opens the chain. This is the whole point of Pearl's
criterion — "explaining away" — and it is why `IsDirectedGlobalMarkov` cannot be obtained from
the undirected global Markov property of any single fixed graph. -/

/-- The three-vertex collider `0 → 2 ← 1` on `Fin 3`, as a bare relation. It is acyclic (every
arrow ends at `2`, which has no outgoing arrow) and loopless, so it is the adjacency relation of
a genuine directed acyclic graph; it is used only to refute monotonicity of d-separation in the
separator. -/
def colliderRel : Fin 3 → Fin 3 → Prop := fun a b => (a = 0 ∨ a = 1) ∧ b = 2

/-- Every arrow of `colliderRel` ends at `2` — the structural fact both collider statements run
on. Together with `colliderRel_not_two_left` it says that a chain alternates between `{0, 1}` and
`2`, meeting `2` head-to-head every time. -/
theorem colliderRel_eq_two {a b : Fin 3} (h : colliderRel a b) : b = 2 := h.2

/-- `2` has no outgoing arrow. -/
theorem colliderRel_not_two_left {b : Fin 3} : ¬ colliderRel 2 b := by
  rintro ⟨h, -⟩
  revert h
  decide

/-- **Every interior meeting at `2` is a collider that blocks over the empty separator.** A chain
*starting* at `2` can only leave it against an arrow (`bwd`), so if it was entered along one
(`din = into`) the arrows meet head-to-head; and over `S = ∅` the descendant clause is vacuous.
The hypothesis `y ≠ 2` rules out the chain of length `0`, whose far side is `none`. -/
theorem blockedFrom_of_start_eq_two {x y : Fin 3} (c : Chain colliderRel x y) (hx : x = 2)
    (hy : y ≠ 2) : Chain.BlockedFrom ∅ (some ArrowDir.into) c := by
  induction c with
  | nil v => exact absurd hx hy
  | fwd h _ _ => exact absurd (hx ▸ h) colliderRel_not_two_left
  | bwd _ _ _ =>
      exact Or.inl (Or.inr ⟨⟨rfl, rfl⟩, fun d _ => Finset.notMem_empty d⟩)

/-- Over the empty separator the collider blocks: every chain from `0` to `1` must leave `0`
along `0 → 2` and arrive at `1` against `1 → 2`, so it meets `2` head-to-head, and with `S = ∅`
the descendant condition is vacuous. -/
theorem dSeparated_collider_empty : DSeparated colliderRel ∅ {0} {1} := by
  have key : ∀ {x y : Fin 3} (c : Chain colliderRel x y), x ≠ 2 → y ≠ 2 → x ≠ y →
      Chain.BlockedFrom ∅ none c := by
    intro x y c
    induction c with
    | nil v => exact fun _ _ h => absurd rfl h
    | fwd h c _ => exact fun _ hy _ => Or.inr (blockedFrom_of_start_eq_two c h.2 hy)
    | bwd h _ _ => exact fun hx _ _ => absurd h.2 hx
  intro a ha b hb c
  rw [Finset.mem_singleton] at ha hb
  subst ha; subst hb
  exact key c (by decide) (by decide) (by decide)

/-- Conditioning **on** the collider opens the chain `0 → 2 ← 1`: at `2` the arrows meet
head-to-head and `2` is one of its own descendants, so `2` does not block; the two ends `0` and
`1` are not colliders and are not in `{2}`, so they do not block either. -/
theorem not_dSeparated_collider_singleton : ¬ DSeparated colliderRel {2} {0} {1} := by
  intro h
  have h02 : colliderRel 0 2 := ⟨Or.inl rfl, rfl⟩
  have h12 : colliderRel 1 2 := ⟨Or.inr rfl, rfl⟩
  -- the chain `0 → 2 ← 1`
  have hb := h 0 (Finset.mem_singleton_self 0) 1 (Finset.mem_singleton_self 1)
    (Chain.fwd h02 (Chain.bwd h12 (Chain.nil 1)))
  have hb' : BlocksAt colliderRel {2} none (some ArrowDir.outOf) 0 ∨
      BlocksAt colliderRel {2} (some ArrowDir.into) (some ArrowDir.into) 2 ∨
      BlocksAt colliderRel {2} (some ArrowDir.outOf) none 1 := hb
  rcases hb' with h1 | h1 | h1
  · exact absurd (blocksAt_none_left.mp h1) (by decide)
  · -- `2` is one of its own descendants, so the collider does not block
    exact (blocksAt_iff_noDescendantIn_of_isCollider ⟨rfl, rfl⟩).mp h1 2
      Relation.ReflTransGen.refl (Finset.mem_singleton_self 2)
  · exact absurd (blocksAt_none_right.mp h1) (by decide)

/-- **d-separation is not monotone in the separator.** The undirected `separates_of_subset_sep`
has no analogue here: `∅ ⊆ {2}` d-separates `{0}` from `{1}` in `0 → 2 ← 1` while `{2}` does
not. -/
theorem not_forall_dSeparated_of_subset_sep :
    ¬ ∀ (W : Type) (r : W → W → Prop) (S S' A B : Finset W), S ⊆ S' →
        DSeparated r S A B → DSeparated r S' A B := fun h =>
  not_dSeparated_collider_singleton
    (h (Fin 3) colliderRel ∅ {2} {0} {1} (Finset.empty_subset _) dSeparated_collider_empty)

/-! ### Proposition 3.25 — d-separation is moral-graph separation

From here on the statements are about a `DAG` and its moral graph; everything above is stated
for a bare relation. -/

section Prop325

variable [Fintype V] [DecidableEq V]

open SimpleGraph in
/-- **Contracting the colliders of an active chain into marriage edges** — the construction
behind the first half of Proposition 3.25, and the only place where "every vertex of an active
chain lies in `An(A ∪ B ∪ S)`" is proved.

Both statements are made in one structural recursion on the chain, because they need each other:
the walk is built out of the non-collider occurrences, which must be shown to lie in `T` before
they can carry a moral edge, and a non-collider's membership of `T` is read off the *rest* of the
chain, not off the part already traversed. The three conclusions are, in order:

* `x ∈ T`. At a collider this is Lauritzen's "activity forces a descendant in `S`", i.e.
  `x ∈ An(S)`; at a vertex whose arrow ahead points away it follows from the next vertex by
  ancestrality; at the last vertex it is `y ∈ B ⊆ T`. The one case it cannot supply — the arrow
  behind points away *and* the arrow ahead points in — is exactly the hypothesis `hTx`, which the
  caller discharges (in the recursion, from `x ∈ T` by ancestrality; at the top level, from
  `a ∈ A ⊆ T`).
* At a **collider** occurrence the walk cannot pass through `x`, so the conclusion names the next
  vertex `z` of the chain instead: it is a second parent of `x`, and the two parents are the two
  ends of the marriage edge the caller installs.
* At a **non-collider** occurrence `x` is on the walk, and is outside `S` because the chain is
  active there.

The graph is abstracted to any `M` with the adjacency of `(𝒢_T)^m` (`DAG.moralGraph_induce_adj`),
so that this recursion is stated once and instantiated at `T = An(A ∪ B ∪ S)`. -/
private theorem exists_moralWalk_of_active {D : DAG V} {B S T : Finset V} {M : SimpleGraph V}
    (hTanc : D.IsAncestralSet T) (hBT : B ⊆ T) (hST : S ⊆ T)
    (hMadj : ∀ u v : V, M.Adj u v ↔ u ≠ v ∧ u ∈ T ∧ v ∈ T ∧
      (D.Adj u v ∨ D.Adj v u ∨ ∃ w ∈ T, D.Adj u w ∧ D.Adj v w)) :
    ∀ (x y : V) (c : Chain D.Adj x y) (din : Option ArrowDir),
      ¬ Chain.BlockedFrom S din c → y ∈ B → (din ≠ some ArrowDir.into → x ∈ T) →
      x ∈ T ∧
        (IsCollider din c.headDir →
          ∃ z, D.Adj z x ∧ z ∈ T ∧ z ∉ S ∧ ∃ w : M.Walk z y, ∀ s ∈ S, s ∉ w.support) ∧
        (¬ IsCollider din c.headDir →
          x ∉ S ∧ ∃ w : M.Walk x y, ∀ s ∈ S, s ∉ w.support) := by
  intro x y c
  induction c with
  | nil v =>
      intro din hact hy _
      rw [Chain.blockedFrom_nil, blocksAt_none_right] at hact
      refine ⟨hBT hy, ?_, fun _ => ⟨hact, Walk.nil, ?_⟩⟩
      · simp only [Chain.headDir_nil]
        exact fun hcol => absurd hcol (not_isCollider_none_right din)
      · intro s hs hmem
        rw [Walk.support_nil, List.mem_singleton] at hmem
        exact hact (hmem ▸ hs)
  | @fwd x v y h c ih =>
      intro din hact hy _
      rw [Chain.blockedFrom_fwd, not_or] at hact
      obtain ⟨hxb, hcb⟩ := hact
      have hxS : x ∉ S :=
        fun hm => hxb ((blocksAt_iff_mem_of_not_isCollider (not_isCollider_outOf_right din)).mpr hm)
      obtain ⟨hvT, ihcol, ihnc⟩ := ih (some ArrowDir.into) hcb hy (fun hne => absurd rfl hne)
      have hxT : x ∈ T := hTanc h hvT
      refine ⟨hxT, fun hcol => absurd hcol (not_isCollider_outOf_right din), fun _ => ⟨hxS, ?_⟩⟩
      by_cases hcol : IsCollider (some ArrowDir.into) c.headDir
      · -- the next vertex is a collider: the walk jumps over it along a marriage edge
        obtain ⟨z, hzv, hzT, hzS, wk, hwk⟩ := ihcol hcol
        rcases eq_or_ne x z with rfl | hxz
        · exact ⟨wk, hwk⟩
        · refine ⟨Walk.cons ((hMadj x z).mpr
            ⟨hxz, hxT, hzT, Or.inr (Or.inr ⟨v, hvT, h, hzv⟩)⟩) wk, ?_⟩
          intro s hs hmem
          rw [Walk.support_cons, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hxS hs
          · exact hwk s hs hmem
      · -- the next vertex is on the walk, and the arrow `x → v` survives moralization
        obtain ⟨hvS, wk, hwk⟩ := ihnc hcol
        refine ⟨Walk.cons ((hMadj x v).mpr ⟨D.ne_of_adj h, hxT, hvT, Or.inl h⟩) wk, ?_⟩
        intro s hs hmem
        rw [Walk.support_cons, List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact hxS hs
        · exact hwk s hs hmem
  | @bwd x v y h c ih =>
      intro din hact hy hTx
      rw [Chain.blockedFrom_bwd, not_or] at hact
      obtain ⟨hxb, hcb⟩ := hact
      -- `x ∈ T`: at a collider from activity (`x ∈ An(S)`), otherwise from the caller
      have hxT : x ∈ T := by
        by_cases hcol : IsCollider din (some ArrowDir.into)
        · have hnd : ¬ NoDescendantIn D.Adj S x := fun hn =>
            hxb ((blocksAt_iff_noDescendantIn_of_isCollider hcol).mpr hn)
          simp only [NoDescendantIn, not_forall, not_not] at hnd
          obtain ⟨d, hd, hdS⟩ := hnd
          exact hTanc.reflTransGen_mem hd (hST hdS)
        · exact hTx (fun hd => hcol (hd ▸ isCollider_into_into))
      obtain ⟨hvT, -, ihnc⟩ :=
        ih (some ArrowDir.outOf) hcb hy (fun _ => hTanc h hxT)
      obtain ⟨hvS, wk, hwk⟩ := ihnc (not_isCollider_outOf_left _)
      refine ⟨hxT, ?_, ?_⟩
      · -- `x` is a collider: hand the caller the second parent `v`
        simp only [Chain.headDir_bwd]
        exact fun _ => ⟨v, h, hvT, hvS, wk, hwk⟩
      · simp only [Chain.headDir_bwd]
        intro hcol
        have hxS : x ∉ S :=
          fun hm => hxb ((blocksAt_iff_mem_of_not_isCollider hcol).mpr hm)
        refine ⟨hxS, Walk.cons ((hMadj x v).mpr
          ⟨(D.ne_of_adj h).symm, hxT, hvT, Or.inr (Or.inl h)⟩) wk, ?_⟩
        intro s hs hmem
        rw [Walk.support_cons, List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact hxS hs
        · exact hwk s hs hmem

open SimpleGraph in
/-- **Turning a moral walk that circumvents `S` into an active chain** — the construction behind
the second half of Proposition 3.25.

The recursion walks along `w` and assembles the chain, replacing each **marriage** edge by the
two arrows into its witness `γ`. Every witness is a collider, and so are the vertices of `w` that
two arrows of `w` point into; such a collider *blocks* exactly when neither it nor a descendant
of it lies in `S`, and that is the case the book reroutes. The reroute uses the minimality of the
ancestral set: a blocking collider `γ` lies in `T` and has no descendant in `S`, so it must reach
a vertex `t` of `A ∪ B`, along a line of descent that avoids `S`
(`Chain.exists_chain_of_reflTransGen`, `Chain.exists_chain_prepend_of_reflTransGen`). Which
half of the walk survives depends on which block `t` lands in, and that is why the conclusion
is a **disjunction**:

* the first disjunct hands the caller a chain out of `x` that is unblocked *for every*
  accumulator, so that the caller may prepend its own arrow to it whichever way that arrow points
  — this is the `t ∈ B` reroute, which keeps the walk's prefix and discards its suffix;
* the second disjunct is a finished answer: the `t ∈ A` reroute keeps the walk's **suffix** and
  discards the prefix, so it produces a complete active chain from `A` to `B` and the recursion
  simply propagates it outwards.

Having both disjuncts is what removes the need for an outer induction on the number of blocking
colliders: each reroute is taken at the first collider that blocks, and it finishes one of the
two disjuncts outright. -/
private theorem exists_active_chain_of_moralWalk {D : DAG V} {A B S T : Finset V}
    {M : SimpleGraph V}
    (hmemT : ∀ u : V, u ∈ T → ∃ t ∈ A ∪ B ∪ S, Relation.ReflTransGen D.Adj u t)
    (hMadj : ∀ u v : V, M.Adj u v ↔ u ≠ v ∧ u ∈ T ∧ v ∈ T ∧
      (D.Adj u v ∨ D.Adj v u ∨ ∃ w ∈ T, D.Adj u w ∧ D.Adj v w)) :
    ∀ (x y : V) (w : M.Walk x y), (∀ s ∈ S, s ∉ w.support) → y ∈ B →
      (∀ din : Option ArrowDir, ∃ b'' ∈ B, ∃ c : Chain D.Adj x b'',
          ¬ Chain.BlockedFrom S din c) ∨
      (∃ a' ∈ A, ∃ b' ∈ B, ∃ c : Chain D.Adj a' b', ¬ c.Blocked S) := by
  classical
  intro x y w
  induction w with
  | nil =>
      intro hS hy
      refine Or.inl fun din => ⟨_, hy, Chain.nil _, ?_⟩
      rw [Chain.blockedFrom_nil, blocksAt_none_right]
      exact fun hm => hS _ hm (by simp)
  | @cons x v y hadj w' ih =>
      intro hS hy
      have hxS : x ∉ S := fun hm => hS x hm (by rw [Walk.support_cons]; exact List.mem_cons_self ..)
      have hS' : ∀ s ∈ S, s ∉ w'.support := fun s hs hm =>
        hS s hs (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hm)
      obtain ⟨-, hxT, -, hcase⟩ := (hMadj x v).mp hadj
      rcases ih hS' hy with hIH | hdone
      swap
      · exact Or.inr hdone
      -- the rerouting device, used at both kinds of blocking collider
      have reroute : ∀ (γ : V), γ ∈ T → NoDescendantIn D.Adj S γ →
          ∀ (b'' : V), b'' ∈ B → ∀ (rest : Chain D.Adj γ b''),
            ¬ Chain.BlockedFrom S (some ArrowDir.outOf) rest →
          (∀ din : Option ArrowDir, ∃ t ∈ B, ∃ c : Chain D.Adj γ t,
              ¬ Chain.BlockedFrom S din c) ∨
          (∃ a' ∈ A, ∃ b' ∈ B, ∃ c : Chain D.Adj a' b', ¬ c.Blocked S) := by
        intro γ hγT hnd b'' hb'' rest hrest
        obtain ⟨t, htU, hrt⟩ := hmemT γ hγT
        have htS : t ∉ S := hnd t hrt
        have ht : t ∈ A ∨ t ∈ B := by
          rcases Finset.mem_union.mp htU with hm | hm
          · exact Finset.mem_union.mp hm
          · exact absurd hm htS
        rcases ht with htA | htB
        · -- the line of descent lands in `A`: keep the suffix, discard the prefix
          obtain ⟨c', hc'⟩ := Chain.exists_chain_prepend_of_reflTransGen hrt hnd rest hrest
          exact Or.inr ⟨t, htA, b'', hb'', c', fun hb => hc'
            ((Chain.blockedFrom_congr_din c' (not_isCollider_none_left _)
              (not_isCollider_outOf_left _)).mp hb)⟩
        · -- the line of descent lands in `B`: keep the prefix, discard the suffix
          exact Or.inl fun din => ⟨t, htB, Chain.exists_chain_of_reflTransGen hrt hnd din⟩
      rcases hcase with hxv | hvx | ⟨γ, hγT, hxγ, hvγ⟩
      · -- an arrow `x → v` of the DAG
        obtain ⟨b'', hb'', c'', hc''⟩ := hIH (some ArrowDir.into)
        refine Or.inl fun din => ⟨b'', hb'', Chain.fwd hxv c'', ?_⟩
        rw [Chain.blockedFrom_fwd]
        rintro (hb | hb)
        · exact hxS ((blocksAt_iff_mem_of_not_isCollider (not_isCollider_outOf_right din)).mp hb)
        · exact hc'' hb
      · -- an arrow `v → x` of the DAG: `x` may be a collider of the chain
        obtain ⟨b'', hb'', c'', hc''⟩ := hIH (some ArrowDir.outOf)
        have hrest : ¬ Chain.BlockedFrom S (some ArrowDir.outOf) (Chain.bwd hvx c'') := by
          rw [Chain.blockedFrom_bwd]
          rintro (hb | hb)
          · exact hxS ((blocksAt_iff_mem_of_not_isCollider (not_isCollider_outOf_left _)).mp hb)
          · exact hc'' hb
        by_cases hnd : NoDescendantIn D.Adj S x
        · exact reroute x hxT hnd b'' hb'' _ hrest
        · refine Or.inl fun din => ⟨b'', hb'', Chain.bwd hvx c'', ?_⟩
          rw [Chain.blockedFrom_bwd]
          rintro (hb | hb)
          · rcases hb with ⟨-, hm⟩ | ⟨-, hn⟩
            · exact hxS hm
            · exact hnd hn
          · exact hc'' hb
      · -- a marriage edge: install its witness `γ` as a collider
        obtain ⟨b'', hb'', c'', hc''⟩ := hIH (some ArrowDir.outOf)
        by_cases hnd : NoDescendantIn D.Adj S γ
        · have hrest : ¬ Chain.BlockedFrom S (some ArrowDir.outOf) (Chain.bwd hvγ c'') := by
            rw [Chain.blockedFrom_bwd]
            rintro (hb | hb)
            · exact hnd _ Relation.ReflTransGen.refl
                ((blocksAt_iff_mem_of_not_isCollider (not_isCollider_outOf_left _)).mp hb)
            · exact hc'' hb
          rcases reroute γ hγT hnd b'' hb'' _ hrest with hL | hR
          · refine Or.inl fun din => ?_
            obtain ⟨t, htB, desc, hdesc⟩ := hL (some ArrowDir.into)
            refine ⟨t, htB, Chain.fwd hxγ desc, ?_⟩
            rw [Chain.blockedFrom_fwd]
            rintro (hb | hb)
            · exact hxS
                ((blocksAt_iff_mem_of_not_isCollider (not_isCollider_outOf_right din)).mp hb)
            · exact hdesc hb
          · exact Or.inr hR
        · refine Or.inl fun din => ⟨b'', hb'', Chain.fwd hxγ (Chain.bwd hvγ c''), ?_⟩
          rw [Chain.blockedFrom_fwd, Chain.blockedFrom_bwd]
          rintro (hb | hb | hb)
          · exact hxS ((blocksAt_iff_mem_of_not_isCollider (not_isCollider_outOf_right din)).mp hb)
          · exact hnd ((blocksAt_iff_noDescendantIn_of_isCollider isCollider_into_into).mp hb)
          · exact hc'' hb

/-- **Lauritzen Proposition 3.25** (p. 48) — *the headline of this file*. For **disjoint**
blocks `A`, `B`, `S` of a directed acyclic graph `D`, the separator `S` d-separates `A` from `B`
**iff** `S` separates `A` from `B` in `(G_{An(A∪B∪S)})^m`.

This is the bridge that lets the undirected separation theory serve the directed one: the
left-hand side is Pearl's local, chain-by-chain criterion, the right-hand side is a single
application of `Separates` to one explicitly constructed undirected graph.

*Edge behaviour.* `ancestralClosure ∅ = ∅` and moralization of the empty sub-DAG is the empty
graph, so at `A = B = S = ∅` the graph is `⊥` and `Separates ⊥ ∅ ∅ ∅` holds vacuously, matching
`dSeparated_empty_left`. The vertex type stays `V`: the induced sub-DAG keeps `V` and merely
deletes arrows leaving the ancestral set, so `Separates` and `DSeparated` speak about the same
blocks with no subtype transport.

**Proof (the book's, p. 48–49).** Both directions are contrapositives.

* *Not d-separated ⇒ not separated in the moral graph.* Take an active chain `π` from `A` to
  `B`. Every vertex of `π` lies in `An(A ∪ B ∪ S)`: at a head-to-head vertex `γ` activity forces
  `γ ∈ S` or `γ` to have a descendant in `S`, so `γ ∈ An(S)`; and any other vertex leads, along
  the arrows of `π`, either to a head-to-head vertex or all the way to an endpoint in `A ∪ B`.
  Each head-to-head meeting marries its two neighbours on `π` in the moral graph, so deleting
  the head-to-head vertices from `π` leaves a walk in `(G_{An(A∪B∪S)})^m` from `A` to `B`; its
  vertices are the non-head-to-head vertices of `π`, none of which lies in `S`, since `π` is
  active. (When the two neighbours of a head-to-head vertex coincide, no marriage edge is
  needed and the walk simply stays put — this is where allowing repeated vertices in `Chain`
  costs nothing.)
* *Not separated in the moral graph ⇒ not d-separated.* A walk in `(G_{An(A∪B∪S)})^m`
  circumventing `S` has pieces that are arrows of `D` and pieces that are marriages. Each
  marriage comes from a head-to-head meeting at some `γ`. If `γ ∈ S`, or `γ` has a descendant
  in `S`, the meeting does not block. If not, then `γ` must have a descendant in `A ∪ B` —
  *because the ancestral set was the smallest one* — and rerouting along that line of descent
  produces a chain with one head-to-head meeting fewer. Iterating terminates in an active chain
  from `A` to `B`.

Note where acyclicity is used: in "the ancestral set was smallest", i.e. in the fact that a
vertex of `An(A ∪ B ∪ S)` which is not an ancestor of `S` must be an ancestor of `A ∪ B`.

**As formalized.** Each contrapositive is a single structural recursion —
`exists_moralWalk_of_active` and `exists_active_chain_of_moralWalk` above — and neither
*iterates*. In particular the book's "rerouting produces a chain with one head-to-head meeting
fewer, and iterating terminates" is replaced by a disjunctive conclusion: the reroute at the
first blocking collider either keeps the walk's prefix (`t ∈ B`) and hands the caller a chain to
extend, or keeps its suffix (`t ∈ A`) and is already a finished answer. So no well-founded
measure on the number of blocking colliders is needed.

*The three disjointness hypotheses are not used.* Both constructions are local — activity of the
chain, respectively `S`-avoidance of the walk, supplies every non-membership of `S` that is
needed — so the equivalence holds for arbitrary `A`, `B`, `S`. They are kept because the book
assumes them: its blocking rule is stated for disjoint blocks. -/
theorem dSeparated_iff_separates_moralGraph_ancestralClosure (D : DAG V) [DecidableRel D.Adj] [DecidableRel (Relation.TransGen D.Adj)] (A B S : Finset V)
    -- USER-INPUT: the two separated blocks are disjoint; Lauritzen Proposition 3.25, p. 48
    -- ("let `A`, `B` and `S` be disjoint subsets")
    (hAB : Disjoint A B)
    -- USER-INPUT: the first block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hAS : Disjoint A S)
    -- USER-INPUT: the second block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hBS : Disjoint B S) :
    DSeparated D.Adj S A B ↔ Separates (ancestralMoralGraph D (A ∪ B ∪ S)) S A B := by
  classical
  have hsub : A ∪ B ∪ S ⊆ D.ancestralClosure (A ∪ B ∪ S) := D.subset_ancestralClosure _
  have hAT : A ⊆ D.ancestralClosure (A ∪ B ∪ S) := fun _ ha =>
    hsub (Finset.mem_union_left _ (Finset.mem_union_left _ ha))
  have hBT : B ⊆ D.ancestralClosure (A ∪ B ∪ S) := fun _ hb =>
    hsub (Finset.mem_union_left _ (Finset.mem_union_right _ hb))
  have hST : S ⊆ D.ancestralClosure (A ∪ B ∪ S) := fun _ hs => hsub (Finset.mem_union_right _ hs)
  have hMadj := DAG.moralGraph_induce_adj D (D.ancestralClosure (A ∪ B ∪ S))
  constructor
  · -- d-separated ⇒ separated: an `S`-avoiding moral walk would produce an active chain
    intro hd a ha b hb w
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    rcases exists_active_chain_of_moralWalk (A := A) (B := B)
      (fun _ hu => DAG.mem_ancestralClosure.mp hu) hMadj a b w hcon hb with
      hL | ⟨a', ha', b', hb', c, hc⟩
    · obtain ⟨b'', hb'', c, hc⟩ := hL none
      exact hc (hd a ha b'' hb'' c)
    · exact hc (hd a' ha' b' hb' c)
  · -- separated ⇒ d-separated: an active chain would produce an `S`-avoiding moral walk
    intro hs a ha b hb c
    by_contra hact
    obtain ⟨-, -, h3⟩ := exists_moralWalk_of_active (B := B)
      (D.isAncestralSet_ancestralClosure _) hBT hST hMadj a b c none hact hb (fun _ => hAT ha)
    obtain ⟨-, w, hw⟩ := h3 (not_isCollider_none_left _)
    obtain ⟨s, hsS, hsw⟩ := hs a ha b hb w
    exact hw s hsS hsw

/-- **The book's phrasing of d-separation**, over chains whose vertices are *distinct*.
Lauritzen's chains (§2.1.1, p. 6) are vertex-distinct sequences; `Chain` drops that requirement
(module docstring, note 1). The two readings of d-separation agree.

*This is not the undirected argument.* `separates_iff_forall_path` follows from
`SimpleGraph.Walk.bypass`, which shortens a walk to a path with smaller support; the same move
is **unavailable** here, because deleting a repeated section of a chain can turn a non-collider
into a **collider** and so turn an active chain into a blocked one.

⚠️ **Nor does it follow from Proposition 3.25 applied twice.** Nothing here proves
Proposition 3.25 *for the vertex-distinct reading*, and the equivalence cannot be obtained from
`dSeparated_iff_separates_moralGraph_ancestralClosure` by rewriting, because the chain that
`exists_active_chain_of_moralWalk` builds out of a moral walk need not have distinct vertices
(two marriage edges may share a witness, and a rerouting line of descent may re-meet the walk).
Getting a *vertex-distinct* chain out of that construction is a strictly stronger statement than
the one proved above.

**What is proved instead: bypass, repaired.** Take an active chain from `a` to `b` of **minimal
length**. If it repeated a vertex `x`, deleting the stretch between two occurrences would leave a
shorter chain, and `Chain.exists_shorter_of_not_nodup` shows that chain is still active — the
merged occurrence of `x` cannot block. The one configuration in which it could — `x` becoming a
collider with no descendant in `S` — is impossible on an active chain: if the chain leaves `x`
*along* an arrow at the first occurrence, `Chain.forward_run` forces every later vertex, the
second occurrence of `x` included, to be a descendant of `x`, i.e. a **directed cycle**; and if
it leaves against an arrow, the first occurrence is already a collider (so activity supplies the
descendant in `S`) or is not one (so neither is the merged occurrence). Minimality therefore
forces distinct vertices, and the two readings agree.

*Consequences for the signature.* Acyclicity is genuinely used — it is what kills the cycle
above, and `Chain.exists_shorter_of_not_nodup` carries it as `IsAcyclicRel`. The three
**disjointness hypotheses are not used at all**: the argument is chain-local and never looks at
where `A`, `B` and `S` meet. They are kept to match Proposition 3.25's statement. -/
theorem dSeparated_iff_forall_nodup (D : DAG V) [DecidableRel D.Adj] [DecidableRel (Relation.TransGen D.Adj)] (A B S : Finset V)
    -- USER-INPUT: the two separated blocks are disjoint; Lauritzen Proposition 3.25, p. 48
    (hAB : Disjoint A B)
    -- USER-INPUT: the first block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hAS : Disjoint A S)
    -- USER-INPUT: the second block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hBS : Disjoint B S) :
    DSeparated D.Adj S A B ↔
      ∀ a ∈ A, ∀ b ∈ B, ∀ c : Chain D.Adj a b, c.support.Nodup → c.Blocked S := by
  refine ⟨fun h a ha b hb c _ => h a ha b hb c, fun h a ha b hb c => ?_⟩
  by_contra hact
  -- induct on a bound for the length: a shortest active chain from `a` to `b` has no repeats
  have key : ∀ n : ℕ, ∀ c : Chain D.Adj a b, c.length ≤ n → ¬ c.Blocked S → False := by
    intro n
    induction n with
    | zero =>
        intro c hlen hactc
        by_cases hnodup : c.support.Nodup
        · exact hactc (h a ha b hb c hnodup)
        · obtain ⟨c', hlt, -⟩ := Chain.exists_shorter_of_not_nodup D.acyclic c none hactc hnodup
          omega
    | succ n ih =>
        intro c hlen hactc
        by_cases hnodup : c.support.Nodup
        · exact hactc (h a ha b hb c hnodup)
        · obtain ⟨c', hlt, hb'⟩ := Chain.exists_shorter_of_not_nodup D.acyclic c none hactc hnodup
          exact ih c' (by omega) hb'
  exact key c.length c le_rfl hact

/-- **d-separation implies conditional independence** — Lauritzen **Proposition 3.25** (p. 48)
composed with **Corollary 3.23** (p. 47).

⚠️ *Two citations, deliberately.* The book **defines** the directed global Markov property (DG)
by the moral-graph criterion of Corollary 3.23 and proves *separately*, in Proposition 3.25,
that d-separation is the same relation. There is no single numbered result in Lauritzen saying
"d-separation ⟹ conditional independence", and citing one number for this theorem would
misattribute it. The Lean proof is the composition: rewrite along
`dSeparated_iff_separates_moralGraph_ancestralClosure`, then apply the hypothesis.

Stated against the **abstract** relation `ci : Finset V → Finset V → Finset V → Prop` (read
`ci A B S` as `X_A ⫫ X_B ∣ X_S`), as everything in `Undirected.Markov` is, so that every model
class — the discrete mass relation, the Gaussian precision relation, the general `CondIndep` —
gets the criterion once (Lauritzen's own remark after Proposition 3.4, p. 33, that these
arguments depend only on the calculus). -/
theorem condIndep_of_dSeparated (D : DAG V) [DecidableRel D.Adj] [DecidableRel (Relation.TransGen D.Adj)] (ci : Finset V → Finset V → Finset V → Prop)
    -- USER-INPUT: the directed global Markov property of the law; Lauritzen Corollary 3.23,
    -- p. 47, which is where (DG) is defined
    (hDG : IsDirectedGlobalMarkov D ci) (A B S : Finset V)
    -- USER-INPUT: the two separated blocks are disjoint; Lauritzen Proposition 3.25, p. 48
    (hAB : Disjoint A B)
    -- USER-INPUT: the first block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hAS : Disjoint A S)
    -- USER-INPUT: the second block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hBS : Disjoint B S)
    -- USER-INPUT: the graphical criterion, read off the DAG; Lauritzen p. 48
    (hd : DSeparated D.Adj S A B) :
    ci A B S :=
  hDG A B S hAB hAS hBS
    ((dSeparated_iff_separates_moralGraph_ancestralClosure D A B S hAB hAS hBS).mp hd)

end Prop325

end StatLean.StatisticalModels.GraphicalModels
