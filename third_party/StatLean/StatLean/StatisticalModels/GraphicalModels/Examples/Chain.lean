module
public import StatLean.StatisticalModels.GraphicalModels.Undirected.Markov
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

/-!
# The three-variable chain `0 — 1 — 2` — the smoke test for the graphical layer

The smallest undirected graph in which the Markov properties have non-vacuous content: the
middle vertex **screens off** the two ends.

* `chainGraph` — the chain on `Fin 3` with edges `{0, 1}` and `{1, 2}`, defined so that its
  adjacency relation is transparently decidable (`decide` closes every adjacency question
  below); `chainGraph_eq_pathGraph` identifies it with Mathlib's `SimpleGraph.pathGraph 3`;
* `chain_adj_zero_one`, `chain_adj_one_two`, `chain_not_adj_zero_two` — the adjacency table;
* `chain_neighborFinset_zero`, `chain_neighborFinset_one` — the neighbourhoods, i.e. the data
  the local Markov property is phrased with;
* `chain_sdiff_pair_eq_middle` — `V ∖ {0, 2} = {1}`: on three vertices, "condition on
  everything else" and "condition on the middle vertex" are the same instruction. This is why
  the chain is the example where the pairwise and global properties visibly coincide;
* **`chain_separates_middle`** — `{1}` separates `{0}` from `{2}`;
* `chain_not_separates_empty` — the empty set does **not**: the two ends are connected, so the
  middle vertex is genuinely doing the work;
* `chain_ends_no_admissible_blocks` — the two ends `{0, 2}` cannot serve as a separator in any
  statement the book allows: their complement is the single vertex `1`, so no *disjoint*
  non-empty pair of blocks survives outside them;
* **`chain_condIndep_of_isGlobalMarkov`** and `chain_condIndep_of_isLocalMarkov` — the moral:
  for **any** relation `ci` satisfying the global (resp. local) Markov property for this graph,
  `ci {0} {2} {1}` — reading `ci A B C` as `X_A ⫫ X_B ∣ X_C`, the middle variable screens the
  two ends off from one another.

Because `Undirected.Markov` states the Markov properties over an *abstract* ternary relation,
these consequences apply verbatim to every model class of the area — the discrete mass
relation, the Gaussian precision relation, and the general `Core.CondIndep` — with no further
work. That is exactly what this file is here to demonstrate.

**A note on colliders.** The chain's behaviour is not the only one
available on three variables. In the *directed* graph `0 → 1 ← 2` — a **collider**, or
v-structure, at `1` — the pattern is reversed: the two ends are independent *marginally* and
become dependent once the middle variable is conditioned on. Nothing in this file expresses
that: `SimpleGraph` is undirected, and `chainGraph` is the undirected skeleton shared by the
chain `0 → 1 → 2`, the chain `0 ← 1 ← 2`, the fork `0 ← 1 → 2` **and** the collider. The
distinction lives in Lauritzen's d-separation (Proposition 3.25, p. 48, together with
Corollary 3.23, p. 47: d-separation is separation in the moralised graph of the ancestral set,
and it is precisely *moralisation* that joins the two parents of a collider). **No directed
vocabulary is defined here.**

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996 (first edition)**: §2.1.1, p. 6, for separators (unnumbered);
the properties (P), (L), (G), p. 32, unnumbered; **Proposition 3.4**, p. 32, for the hierarchy
(G) ⇒ (L) ⇒ (P); Example 3.2, p. 31, for graph separation as a graphoid; **Proposition 3.25**,
p. 48, and **Corollary 3.23**, p. 47, for the d-separation theory referred to in the collider
note (`Lauritzen §2.1.1`, `Lauritzen §3.2`). The three-vertex chain itself is **not** a
numbered item of the book — it is our smoke test, and nothing below claims book authority for
the example, only for the definitions and the Markov properties it instantiates.

**Proof formalization notes.**

*The shape of the definition.* `SimpleGraph.pathGraph n` is `hasse (Fin n)`, whose adjacency is
`a ⋖ b ∨ b ⋖ a` in the covering relation. `chainGraph` is instead defined with the arithmetic
adjacency `i + 1 = j ∨ j + 1 = i` — which is `pathGraph_adj`'s right-hand side verbatim, so
`chainGraph_eq_pathGraph` is a `rfl`-level identification — together with the corresponding
decidability instance. Every adjacency fact below is then a one-line `decide`.

*What is and is not decidable here.* Adjacency, `Finset` identities on `Fin 3` and disjointness
of explicit blocks are decidable, and are proved by `decide`. `Separates` is **not**: it
quantifies over the type `SimpleGraph.Walk`, which is infinite (a walk may repeat vertices
arbitrarily often). `chain_separates_middle` is therefore *not* a `decide`; it is the general
fact that the complement of a non-adjacent pair separates that pair, at `i = 0`, `j = 2`,
rewritten along `chain_sdiff_pair_eq_middle`. The negative statement
`chain_not_separates_empty` is proved the other way, by exhibiting the explicit walk
`chainWalk : chainGraph.Walk 0 2`.

**Bibliographic comments.** The chain, the fork and the collider are the three elementary
"connection types" of J. Pearl, *Probabilistic Reasoning in Intelligent Systems*, Morgan
Kaufmann, 1988, ch. 3 — serial, diverging and converging connections — whose different
conditioning behaviour is the whole content of d-separation. The undirected chain, where only
the serial/diverging behaviour is visible, is the standard first example in every treatment of
Markov random fields, going back to J. Besag, "Spatial interaction and the statistical analysis
of lattice systems," *J. Roy. Statist. Soc. Ser. B* **36** (1974), 192–236.
-/

namespace StatLean.StatisticalModels.GraphicalModels

open SimpleGraph

/-! ### The chain graph -/

/-- The **three-variable chain** `0 — 1 — 2` on `Fin 3` (the running example of the undirected
theory; not a numbered item of Lauritzen). The adjacency relation is spelled out arithmetically
rather than through `SimpleGraph.pathGraph`, so that it is transparently decidable — see the
module docstring.

*Edge behaviour:* the relation is symmetric and irreflexive by construction, so `chainGraph` is
a genuine `SimpleGraph`; `0` and `2` are the only non-adjacent distinct pair. -/
def chainGraph : SimpleGraph (Fin 3) where
  Adj i j := (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel chainGraph.Adj := fun i j =>
  inferInstanceAs (Decidable (((i : ℕ) + 1 = (j : ℕ)) ∨ ((j : ℕ) + 1 = (i : ℕ))))

/-- `chainGraph` **is** Mathlib's path graph on three vertices — the definition above only
replaces the covering relation of `SimpleGraph.pathGraph` by the arithmetic condition that
`SimpleGraph.pathGraph_adj` proves equivalent to it, so that `decide` applies. -/
theorem chainGraph_eq_pathGraph : chainGraph = SimpleGraph.pathGraph 3 := by
  ext i j
  exact SimpleGraph.pathGraph_adj.symm

/-! ### The adjacency table -/

/-- The first edge of the chain. -/
theorem chain_adj_zero_one : chainGraph.Adj 0 1 := by decide

/-- The second edge of the chain. -/
theorem chain_adj_one_two : chainGraph.Adj 1 2 := by decide

/-- The two **ends of the chain are non-adjacent** — the missing edge that gives the example its
content. This is the hypothesis of the pairwise Markov property at the pair `(0, 2)`. -/
theorem chain_not_adj_zero_two : ¬ chainGraph.Adj 0 2 := by decide

/-! ### Neighbourhoods and the block algebra of `Fin 3` -/

/-- The neighbourhood of the end `0` is the middle vertex. This is the conditioning block of the
local Markov property at `0`. -/
theorem chain_neighborFinset_zero : chainGraph.neighborFinset 0 = {1} := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  revert v
  decide

/-- The neighbourhood of the middle vertex is the pair of ends — so the local Markov property at
`1` conditions on *both* ends and is degenerate (its "rest" block `V ∖ cl(1)` is empty). The
content of the chain sits at the ends, not at the middle. -/
theorem chain_neighborFinset_one : chainGraph.neighborFinset 1 = {0, 2} := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  revert v
  decide

/-- On three vertices, **"all the remaining variables" is the middle vertex**:
`V ∖ {0, 2} = {1}`. This identity is what makes the pairwise Markov property at `(0, 2)` and
the global Markov property at the separator `{1}` say the same thing here. -/
theorem chain_sdiff_pair_eq_middle :
    (Finset.univ \ ({0, 2} : Finset (Fin 3))) = {1} := by decide

/-! ### Separation -/

/-- The explicit walk `0 — 1 — 2`, used to *refute* separation by the empty set. -/
def chainWalk : chainGraph.Walk 0 2 :=
  SimpleGraph.Walk.cons (show chainGraph.Adj 0 1 by decide)
    (SimpleGraph.Walk.cons (show chainGraph.Adj 1 2 by decide) SimpleGraph.Walk.nil)

/-- **The middle vertex separates the two ends** (Lauritzen §2.1.1, p. 6): every walk from `0`
to `2` in the chain visits `1`.

Not a `decide` — `Separates` quantifies over the infinite type `SimpleGraph.Walk`. It is the
separation of a distinct non-adjacent pair by the complement of that pair, rewritten along
`chain_sdiff_pair_eq_middle`. -/
theorem chain_separates_middle : Separates chainGraph {1} {0} {2} := by
  have hsep := separates_sdiff_pair chainGraph 0 2 (by decide) chain_not_adj_zero_two
  rwa [chain_sdiff_pair_eq_middle] at hsep

/-- **The middle vertex is genuinely needed**: the empty set does not separate the two ends,
because `chainWalk` joins them without meeting it. Together with `chain_separates_middle` this
is the whole combinatorial content of the example. -/
theorem chain_not_separates_empty : ¬ Separates chainGraph ∅ {0} {2} := by
  intro h
  obtain ⟨s, hs, -⟩ :=
    h 0 (Finset.mem_singleton_self 0) 2 (Finset.mem_singleton_self 2) chainWalk
  exact absurd hs (Finset.notMem_empty s)

/-- **The two ends are not an admissible separator.** Lauritzen's global Markov property ranges
over *disjoint* triples `(A, B, S)`; at `S = {0, 2}` the blocks `A`, `B` must live in the single
remaining vertex `{1}` and be disjoint from each other, so one of them is empty and the
instance is vacuous. This is the precise sense in which `{0, 2}` "separates nothing relevant":
not that separation fails, but that there is no admissible pair of blocks to separate. -/
theorem chain_ends_no_admissible_blocks {A B : Finset (Fin 3)}
    -- USER-INPUT: `A` is disjoint from the separator; Lauritzen §3.2 (G), p. 32
    (hA : Disjoint A ({0, 2} : Finset (Fin 3)))
    -- USER-INPUT: `B` is disjoint from the separator; Lauritzen §3.2 (G), p. 32
    (hB : Disjoint B ({0, 2} : Finset (Fin 3)))
    -- USER-INPUT: the two separated blocks are disjoint; Lauritzen §3.2 (G), p. 32
    (hAB : Disjoint A B) :
    A = ∅ ∨ B = ∅ := by
  revert hA hB hAB
  revert A B
  decide

/-! ### The moral — the middle variable screens off the ends

Both statements below are about an **arbitrary** ternary relation `ci` on index blocks, read as
`ci A B C ↔ X_A ⫫ X_B ∣ X_C`. They therefore apply to every model class of the area at once:
whatever supplies the Markov property — a discrete mass function, a Gaussian precision matrix,
or the general `Core.CondIndep` — inherits the conclusion. -/

variable (ci : Finset (Fin 3) → Finset (Fin 3) → Finset (Fin 3) → Prop)

/-- **The chain moral, from the global Markov property** (Lauritzen §3.2 (G), p. 32): any law
that is globally Markov with respect to the chain satisfies `X₀ ⫫ X₂ ∣ X₁` — the middle
variable screens the two ends off from one another. This is `IsGlobalMarkov` instantiated at the
disjoint triple `({0}, {2}, {1})`, whose separation is `chain_separates_middle`. -/
theorem chain_condIndep_of_isGlobalMarkov
    -- USER-INPUT: the global Markov property of the law relative to the chain;
    -- Lauritzen §3.2 (G), p. 32
    (h : IsGlobalMarkov chainGraph ci) :
    ci {0} {2} {1} :=
  h {0} {2} {1} (Finset.disjoint_singleton.mpr (by decide))
    (Finset.disjoint_singleton.mpr (by decide))
    (Finset.disjoint_singleton.mpr (by decide)) chain_separates_middle

/-- **The chain moral, from the local Markov property** (Lauritzen §3.2 (L), p. 32): the same
conclusion from the *weaker* hypothesis, because on the chain the local property at the end `0`
already says `X₀ ⫫ X_{V ∖ cl(0)} ∣ X_{ne(0)}`, and `ne(0) = {1}`, `V ∖ cl(0) = {2}`. No
property of `ci` is needed — unlike the general `local ⇒ pairwise` implication, which requires
weak union. -/
theorem chain_condIndep_of_isLocalMarkov
    -- USER-INPUT: the local Markov property of the law relative to the chain;
    -- Lauritzen §3.2 (L), p. 32
    (h : IsLocalMarkov chainGraph ci) :
    ci {0} {2} {1} := by
  have h0 := h 0
  rw [chain_neighborFinset_zero,
    show (Finset.univ \ insert (0 : Fin 3) ({1} : Finset (Fin 3))) = {2} by decide] at h0
  exact h0

end StatLean.StatisticalModels.GraphicalModels
