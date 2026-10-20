module
public import StatLean.StatisticalModels.GraphicalModels.Discrete.CondIndep
public import StatLean.StatisticalModels.GraphicalModels.Undirected.Markov
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

/-!
# Factorization over the cliques of a graph — property (F)

Lauritzen's fourth Markov-type property: a mass function **factorizes** over an undirected
graph `G` when it is a product of non-negative factors, one for each complete vertex set, each
depending on the configuration only through its own coordinates. Together with
`Discrete/CondIndep.lean` (which supplies the graphoid calculus) this closes the discrete
chain (F) ⇒ (G) ⇒ (L) ⇒ (P) of Lauritzen's Proposition 3.8, and carries the
Hammersley–Clifford theorem.

* `completeSubsets G` — the `Finset` of complete vertex sets, assembled from Mathlib's
  `SimpleGraph.IsClique`;
* `IsCliquePotential G ψ` — a family of **clique potentials**: `ψ c` depends only on `x_c`;
* `FactorizesOver G p` — property **(F)**, Lauritzen eqs. **(3.11)/(3.12)**, pp. 34–35;
* `isClique_subset_or_of_separates` — the one graph-theoretic fact behind (F) ⇒ (G): a complete
  set cannot straddle a separator;
* `exists_factorization_of_separates` — the product splits across a separator into a factor on
  `A ∪ S` and a factor on `B ∪ S`;
* **`factorizesOver_implies_globalMarkov`** — Lauritzen **Proposition 3.8**, p. 35, (F) ⇒ (G),
  stated against the abstract `IsGlobalMarkov` of `Undirected/Markov.lean` instantiated at
  `CondIndepMass`;
* `factorizesOver_implies_localMarkov` / `factorizesOver_implies_pairwiseMarkov` — the rest of
  Proposition 3.8, by composition with the hierarchy;
* **`hammersleyClifford`** — Lauritzen **Theorem 3.9**, p. 36: for a *strictly positive* mass
  function, (P) ⟺ (F). Proved, by Möbius inversion of `log p` over the subset lattice; the
  private scaffolding is `sum_powerset_moebius`, `hcSub`/`hcH`/`hcPhi`,
  `crossRatio_of_condIndepMass` and `hcPhi_eq_zero_of_not_isClique`.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996**: property (F) is the unnumbered definition on pp. 34–35 with
equations **(3.11)** (product over complete subsets) and **(3.12)** (product over cliques);
**Proposition 3.8** (p. 35) is (F) ⇒ (G) ⇒ (L) ⇒ (P); **Theorem 3.9** (p. 36) is the
Hammersley–Clifford theorem, that a positive and continuous density satisfies (P) iff it
factorizes; **Example 3.10** (pp. 37–38) is Moussouris's counterexample. Lauritzen remarks on
p. 28 that on a discrete space every function is continuous (`Lauritzen §3.2`).

**Proof formalization notes.** *Book vs Lean, four deliberate differences.*

1. **Complete subsets, not maximal cliques.** Lauritzen's (3.11) is a product over complete
   subsets and his (3.12) is the same product regrouped over the *maximal* complete subsets,
   which he calls cliques; the two properties are equivalent, since a potential attached to a
   complete set can be absorbed into any maximal complete set containing it. Mathlib's
   `SimpleGraph.IsClique` means *complete*, not maximal, so `FactorizesOver` is (3.11)
   verbatim, with `completeSubsets` — the filter of `Finset.univ : Finset (Finset V)` by
   `IsClique` — as its index family.
2. **The potentials are functions of the whole configuration.** As in `Discrete/CondIndep.lean`,
   `ψ c : (V → α) → ℝ≥0∞` with the constraint `DependsOn (ψ c) ↑c` (Mathlib's `DependsOn`),
   rather than a function on the subtype `↥c → α`. The two readings are interchangeable by
   `dependsOn_iff_exists_comp`; keeping a single type is what makes the product
   `∏ c ∈ completeSubsets G, ψ c x` a plain `Finset.prod` in `ℝ≥0∞`.
3. **No normalisation, no finiteness in (F) ⇒ (G).** Lauritzen's `f` is a density; ours is a
   bare `ℝ≥0∞`-valued mass. `factorizesOver_implies_globalMarkov` needs neither: it splits a
   product and then applies the division-free half of the criterion (3.6).
   Finiteness reappears only in
   `hammersleyClifford`, whose reverse implication runs through the graphoid calculus.
4. **The extension step in (F) ⇒ (G) is explicit.** The product only splits when the three
   blocks *cover* `V`. For a general separated triple `(A, B, S)` one first enlarges `A` to the
   union of the connected components of `G ∖ S` meeting `A`, sets `B'` to the rest, splits
   there, and then shrinks back with (C2), which needs neither finiteness nor positivity. The
   enlargement is spelled *with walks* —
   `A' = {v ∉ S | some walk from `A` to `v` avoids `S`}` — which is the same set as the union
   of the connected components of `G ∖ S` meeting `A`.

**Moussouris's example — why Theorem 3.9 needs positivity** (Lauritzen **Example 3.10**,
pp. 37–38). On the four-cycle `1 − 2 − 3 − 4 − 1` with binary states there is a mass function
that is globally Markov, hence pairwise Markov, but does **not** factorize: its support is a
set of eight configurations chosen so that every attempt to write `p` as a product over the
four edges forces a potential to vanish somewhere it must not. The example is *not* formalized
here, and deliberately so — it is a counterexample, not a reusable theorem, and stating it
would require pinning a concrete `V = Fin 4`, `α = Fin 2` model. Its role in this file is
documentary: it is the reason `hammersleyClifford` carries `hpos`, and the reason
`Undirected/Markov.pairwiseMarkov_implies_globalMarkov_of_nonempty` carries `IsGraphoid`
rather than `IsSemigraphoid`.

**Bibliographic comments.** The equivalence of the Markov property and factorization for
strictly positive distributions is the Hammersley–Clifford theorem: J. M. Hammersley and
P. E. Clifford, "Markov fields on finite graphs and lattices," 1971, unpublished; the first
published proofs are J. Besag, "Spatial interaction and the statistical analysis of lattice
systems," *J. Roy. Statist. Soc. Ser. B* **36** (1974), 192–236, and G. R. Grimmett, "A theorem
about random fields," *Bull. London Math. Soc.* **5** (1973), 81–84. The necessity of
positivity is J. Moussouris, "Gibbs and Markov random systems with constraints," *J. Statist.
Phys.* **10** (1974), 11–33 — Lauritzen's Example 3.10.
-/

open SimpleGraph
open scoped ENNReal

namespace StatLean.StatisticalModels.GraphicalModels

variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]

/-! ### Complete subsets and clique potentials -/

/-- The **complete vertex sets** of `G` — Lauritzen's index family for eq. (3.11), p. 34.

Assembled from Mathlib's `SimpleGraph.IsClique` (which means *complete*, not maximal) by
filtering `Finset.univ : Finset (Finset V)`.

Edge behaviour: `∅` and every singleton are complete (`SimpleGraph.IsClique.of_subsingleton`),
so `completeSubsets G` always contains `∅` and all `{v}`; for the complete graph it is all of
`Finset.univ`, and for the empty graph it is `{∅} ∪ {{v} | v}`. -/
def completeSubsets (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.filter fun c : Finset V => G.IsClique (c : Set V)

@[simp]
theorem mem_completeSubsets {G : SimpleGraph V} [DecidableRel G.Adj] {c : Finset V} :
    c ∈ completeSubsets G ↔ G.IsClique (c : Set V) := by
  simp [completeSubsets]

/-- A family of **clique potentials** for `G` (Lauritzen eq. (3.11), p. 34): for every complete
set `c`, the factor `ψ c` depends on the configuration only through the coordinates in `c`.

Edge behaviour: nothing is required of `ψ c` for a non-complete `c` — those factors never enter
the product in `FactorizesOver`. The potentials are `ℝ≥0∞`-valued and are *not* required to be
finite, positive, or normalised; Lauritzen's are non-negative measurable functions. -/
def IsCliquePotential (G : SimpleGraph V) (ψ : Finset V → (V → α) → ℝ≥0∞) : Prop :=
  ∀ c : Finset V, G.IsClique (c : Set V) → DependsOn (ψ c) (c : Set V)

/-- **Property (F): `p` factorizes over `G`** — Lauritzen eqs. **(3.11)/(3.12)**, pp. 34–35:
`p(x) = ∏_{c complete} ψ_c(x_c)` for some family of clique potentials.

*Book vs Lean.* This is (3.11), the product over **complete** subsets. Lauritzen's (3.12) is
the same property with the product taken over the maximal complete subsets ("cliques"); the two
are equivalent, since each potential may be absorbed into a maximal complete set containing its
index, and we state (3.11) because Mathlib's `IsClique` is completeness rather than maximality.

Edge behaviour: the empty set and all singletons are complete, so `FactorizesOver G p` always
permits a global constant and an arbitrary product of one-vertex factors; in particular every
`p` of the form `∏ v, f v (x v)` factorizes over the **empty** graph, and every `p` whatsoever
factorizes over the **complete** graph (take `ψ Finset.univ := p` and all other factors `1`),
which is the degenerate case in which (F) says nothing. -/
def FactorizesOver (G : SimpleGraph V) [DecidableRel G.Adj] (p : (V → α) → ℝ≥0∞) : Prop :=
  ∃ ψ : Finset V → (V → α) → ℝ≥0∞, IsCliquePotential G ψ ∧
    ∀ x, p x = ∏ c ∈ completeSubsets G, ψ c x

/-! ### (F) ⇒ (G) — Lauritzen Proposition 3.8 -/

variable (G : SimpleGraph V)

/-- **A complete set cannot straddle a separator.** If `S` separates `A` from `B` and the three
blocks cover `V`, then every complete set lies entirely inside `A ∪ S` or entirely inside
`B ∪ S`.

This is the only graph theory in the file. If a complete `c` met both `A ∖ S` and
`B ∖ S` at two distinct vertices they would be adjacent, and the one-edge walk between them has
support contained in `{a, b}`, which is disjoint from `S` — contradicting `hsep`; if it met
them at the *same* vertex, the `nil` walk at that vertex gives the same contradiction. The
cover hypothesis is what turns "`c` misses `A ∖ S`" into "`c ⊆ B ∪ S`". -/
theorem isClique_subset_or_of_separates {A B S c : Finset V}
    -- USER-INPUT: the separation hypothesis of (G); Lauritzen §3.2, p. 32
    (hsep : Separates G S A B)
    -- USER-INPUT: the book's disjointness convention on the triple; Lauritzen §3.2
    (hAS : Disjoint A S) (hBS : Disjoint B S)
    -- LEAN-ONLY: the two sides together with the separator must exhaust the vertex set, else a
    -- complete set may live entirely outside all three blocks; the enlargement step of
    -- `factorizesOver_implies_globalMarkov` is what supplies this
    (hcover : A ∪ B ∪ S = Finset.univ)
    -- USER-INPUT: completeness of the set being placed; Lauritzen eq. (3.11), p. 34
    (hc : G.IsClique (c : Set V)) :
    c ⊆ A ∪ S ∨ c ⊆ B ∪ S := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Finset.not_subset] at h1 h2
  obtain ⟨u, huc, huAS⟩ := h1
  obtain ⟨v, hvc, hvBS⟩ := h2
  simp only [Finset.mem_union, not_or] at huAS hvBS
  -- the cover hypothesis places `u` in `B` and `v` in `A`
  have huB : u ∈ B := by
    have : u ∈ A ∪ B ∪ S := hcover ▸ Finset.mem_univ u
    simp only [Finset.mem_union] at this; tauto
  have hvA : v ∈ A := by
    have : v ∈ A ∪ B ∪ S := hcover ▸ Finset.mem_univ v
    simp only [Finset.mem_union] at this; tauto
  rcases eq_or_ne v u with rfl | hne
  · -- the same vertex lies in `A` and in `B`: the `nil` walk already defeats separation
    obtain ⟨s, hsS, hsw⟩ := hsep _ hvA _ huB SimpleGraph.Walk.nil
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hsw
    exact hvBS.2 (hsw ▸ hsS)
  · -- distinct vertices of a complete set are adjacent: the one-edge walk misses `S`
    have hadj : G.Adj v u := hc (by simpa using hvc) (by simpa using huc) hne
    obtain ⟨s, hsS, hsw⟩ := hsep v hvA u huB (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hsw
    rcases hsw with rfl | rfl
    · exact hvBS.2 hsS
    · exact huAS.2 hsS

/-- **The product splits across a separator.** For a factorizing `p` and a separated triple
covering `V`, the product over complete sets breaks into the complete sets inside `A ∪ S` and
those inside `B ∪ S`, giving Lauritzen's criterion **(3.6)** at the blocks `A`, `B`, `S`.

Since no complete set straddles the separator, the predicate "`c ⊆ A ∪ S`" partitions
`completeSubsets G` into a part on which it holds and a part contained in `B ∪ S`; take
`h := ∏` over the first part and `k := ∏` over the second, whose dependence on the respective
blocks is that of the clique potentials indexed by their subsets. -/
theorem exists_factorization_of_separates [DecidableRel G.Adj] {p : (V → α) → ℝ≥0∞}
    {A B S : Finset V}
    -- USER-INPUT: property (F); Lauritzen eqs. (3.11)/(3.12), pp. 34–35
    (hfac : FactorizesOver G p)
    -- USER-INPUT: the separation hypothesis of (G); Lauritzen §3.2, p. 32
    (hsep : Separates G S A B)
    -- USER-INPUT: the book's disjointness convention on the triple; Lauritzen §3.2
    (hAS : Disjoint A S) (hBS : Disjoint B S)
    -- LEAN-ONLY: the covering hypothesis; see `isClique_subset_or_of_separates`
    (hcover : A ∪ B ∪ S = Finset.univ) :
    ∃ h k : (V → α) → ℝ≥0∞, DependsOn h ((A ∪ S : Finset V) : Set V) ∧
      DependsOn k ((B ∪ S : Finset V) : Set V) ∧ ∀ x, p x = h x * k x := by
  classical
  obtain ⟨ψ, hψ, hprod⟩ := hfac
  refine ⟨fun x => ∏ c ∈ (completeSubsets G).filter (fun c => c ⊆ A ∪ S), ψ c x,
    fun x => ∏ c ∈ (completeSubsets G).filter (fun c => ¬ (c ⊆ A ∪ S)), ψ c x, ?_, ?_, ?_⟩
  · intro y z hyz
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_filter] at hc
    exact DependsOn.mono (Finset.coe_subset.mpr hc.2)
      (hψ c (mem_completeSubsets.mp hc.1)) hyz
  · intro y z hyz
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_filter] at hc
    have hcl := mem_completeSubsets.mp hc.1
    -- a complete set that is not inside `A ∪ S` must be inside `B ∪ S`
    have hsub : c ⊆ B ∪ S :=
      (isClique_subset_or_of_separates G hsep hAS hBS hcover hcl).resolve_left hc.2
    exact DependsOn.mono (Finset.coe_subset.mpr hsub) (hψ c hcl) hyz
  · intro x
    rw [hprod x]
    exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm

/-- **Lauritzen Proposition 3.8**, p. 35: **(F) ⇒ (G)**. A mass function that factorizes over
`G` is globally Markov with respect to `G`.

Stated against the abstract `IsGlobalMarkov` of `Undirected/Markov.lean` instantiated at the
discrete relation `CondIndepMass p`, so that the rest of the hierarchy — (G) ⇒ (L) ⇒ (P),
Lauritzen Proposition 3.4 — is obtained by composition.

*No finiteness or positivity hypothesis.* Both halves of the argument are division-free — the
product split and the `mpr` half of the criterion (3.6) — and the final shrinking step, (C2),
is a pure sum rearrangement.

Given a disjoint separated triple `(A, B, S)`: enlarge `A` to `A'`, the union of `A`
with all connected components of `G` minus `S` that meet `A`, and set `B' := V ∖ (A' ∪ S)`.
Then `A ⊆ A'`, `B ⊆ B'`, the triple `(A', B', S)` is disjoint, covers `V`, and `S` still
separates `A'` from `B'`. Split the product there, feed it to the criterion (3.6) after
rewriting `p` as `blockMarginal (A' ∪ B' ∪ S) p`, and shrink `A' ↝ A`, `B' ↝ B` with (C2)
(using symmetry on the left-hand block). -/
theorem factorizesOver_implies_globalMarkov [DecidableRel G.Adj] (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (F); Lauritzen eqs. (3.11)/(3.12), pp. 34–35
    (hfac : FactorizesOver G p) :
    IsGlobalMarkov G (CondIndepMass p) := by
  classical
  intro A B S hAB hAS hBS hsep
  -- **The enlargement.** `A'` is everything reachable from `A` by a walk that never meets `S`
  -- (Lauritzen's "components of `G ∖ S` meeting `A`", spelled with walks rather than
  -- `ComponentCompl`, so that the argument is self-contained); `B'` is all the rest.
  obtain ⟨A', hA'⟩ : ∃ T : Finset V, T = Finset.univ.filter
      (fun v => v ∉ S ∧ ∃ a ∈ A, ∃ w : G.Walk a v, ∀ s ∈ S, s ∉ w.support) := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ T : Finset V, T = Finset.univ \ (A' ∪ S) := ⟨_, rfl⟩
  have hmemA' : ∀ v, v ∈ A' ↔
      (v ∉ S ∧ ∃ a ∈ A, ∃ w : G.Walk a v, ∀ s ∈ S, s ∉ w.support) := by
    intro v; rw [hA']; simp
  have hmemB' : ∀ v, v ∈ B' ↔ (v ∉ A' ∧ v ∉ S) := by
    intro v; rw [hB']; simp
  -- the enlarged triple is disjoint, covers `V`, and still contains the original blocks
  have hA'S : Disjoint A' S := Finset.disjoint_left.mpr fun v hv => ((hmemA' v).mp hv).1
  have hB'S : Disjoint B' S := Finset.disjoint_left.mpr fun v hv => ((hmemB' v).mp hv).2
  have hA'B' : Disjoint A' B' := Finset.disjoint_right.mpr fun v hv => ((hmemB' v).mp hv).1
  have hcover : A' ∪ B' ∪ S = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hvS : v ∈ S
    · exact Or.inr hvS
    by_cases hvA' : v ∈ A'
    · exact Or.inl (Or.inl hvA')
    · exact Or.inl (Or.inr ((hmemB' v).mpr ⟨hvA', hvS⟩))
  have hAA' : A ⊆ A' := by
    intro a ha
    refine (hmemA' a).mpr ⟨Finset.disjoint_left.mp hAS ha, a, ha, SimpleGraph.Walk.nil, ?_⟩
    intro s hs hsw
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hsw
    exact Finset.disjoint_left.mp hAS ha (hsw ▸ hs)
  have hBB' : B ⊆ B' := by
    intro b hb
    refine (hmemB' b).mpr ⟨?_, Finset.disjoint_left.mp hBS hb⟩
    intro hbA'
    obtain ⟨-, a, haA, w, hw⟩ := (hmemA' b).mp hbA'
    obtain ⟨s, hsS, hsw⟩ := hsep a haA b hb w
    exact hw s hsS hsw
  -- `S` still separates the enlarged blocks: appending an `S`-avoiding walk to an
  -- `S`-avoiding walk out of `A` would put its endpoint into `A'`.
  have hsep' : Separates G S A' B' := by
    intro a' ha' b' hb' w
    by_contra hno
    simp only [not_exists, not_and] at hno
    obtain ⟨-, a, haA, w₀, hw₀⟩ := (hmemA' a').mp ha'
    refine ((hmemB' b').mp hb').1
      ((hmemA' b').mpr ⟨((hmemB' b').mp hb').2, a, haA, w₀.append w, ?_⟩)
    intro s hs hmem
    rw [SimpleGraph.Walk.mem_support_append_iff] at hmem
    exact hmem.elim (hw₀ s hs) (hno s hs)
  -- **The split.** The product breaks across the separator, and (3.6) turns it into (3.2).
  obtain ⟨h, k, hh, hk, hpk⟩ :=
    exists_factorization_of_separates G hfac hsep' hA'S hB'S hcover
  have hci : CondIndepMass p A' B' S :=
    condIndepMass_of_exists_factorization hA'B' hA'S hB'S hh hk (fun x => by
      rw [hcover, blockMarginal_univ]; exact hpk x)
  -- **The shrinking**, by (C2) on each side in turn.
  have hci2 : CondIndepMass p A' B S := by
    refine CondIndepMass.decomposition (D := B' \ B) (hA'B'.mono_right Finset.sdiff_subset) ?_
    rwa [Finset.union_sdiff_of_subset hBB']
  have hci3 : CondIndepMass p B A' S := hci2.symm
  refine (CondIndepMass.decomposition (A := B) (B := A) (D := A' \ A)
    ((hA'B'.mono_right hBB').symm.mono_right Finset.sdiff_subset) ?_).symm
  rwa [Finset.union_sdiff_of_subset hAA']

/-- **(F) ⇒ (L)** — the second link of Lauritzen Proposition 3.8, p. 35, by composition with
`globalMarkov_implies_localMarkov`. -/
theorem factorizesOver_implies_localMarkov [DecidableRel G.Adj] (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (F); Lauritzen eqs. (3.11)/(3.12), pp. 34–35
    (hfac : FactorizesOver G p) :
    IsLocalMarkov G (CondIndepMass p) :=
  globalMarkov_implies_localMarkov G (factorizesOver_implies_globalMarkov G p hfac)

/-- **(F) ⇒ (P)** — the last link of Lauritzen Proposition 3.8, p. 35. Composition with
`globalMarkov_implies_pairwiseMarkov`, which needs no property of the relation at all (the
complement of a non-adjacent pair separates it outright). -/
theorem factorizesOver_implies_pairwiseMarkov [DecidableRel G.Adj] (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (F); Lauritzen eqs. (3.11)/(3.12), pp. 34–35
    (hfac : FactorizesOver G p) :
    IsPairwiseMarkov G (CondIndepMass p) :=
  globalMarkov_implies_pairwiseMarkov G (factorizesOver_implies_globalMarkov G p hfac)

/-! ### Theorem 3.9 — Hammersley–Clifford

The forward implication is Proposition 3.8 above composed with the hierarchy; the reverse is the
substantive half, and the proof is the classical Möbius inversion of `log p` over the subset
lattice (Besag 1974; Grimmett 1973; Lauritzen Appendix A.3): define the interaction terms
`φ_a(x) := ∑_{b ⊆ a} (−1)^{|a ∖ b|} log p(x_b, x*_{V ∖ b})` at a fixed reference configuration
`x*`, show by the pairwise Markov property that `φ_a ≡ 0` for every non-complete `a`, and read
off the factorization. Positivity is used twice: to take logarithms at all, and to run the
cancellation in the vanishing argument.

*Sign convention.* The scaffolding below writes the sign as `(−1)^{|a| + |b|}`, which for
`b ⊆ a` equals `(−1)^{|a ∖ b|}` but interacts far better with
`Finset.card_insert_of_notMem` — the lemma that drives the vanishing argument. -/

/-! #### The subset-lattice (Möbius) machinery

Everything in this block is private scaffolding for `hammersleyClifford`. The declarations are
stated over fresh type variables `W`, `β` wherever
they are pure combinatorics, so that none of the file's `Fintype`/`DecidableEq` section
variables leak into them. -/

/-- The alternating sum of `(-1)^{|t|}` over the subset lattice of `u`, in `ℝ`. This is the real
cast of Mathlib's `Finset.sum_powerset_neg_one_pow_card`; it is the only combinatorial input to
the Möbius inversion `sum_powerset_moebius`. -/
private theorem sum_powerset_neg_one_pow_card_real {W : Type*} [DecidableEq W] (u : Finset W) :
    ∑ t ∈ u.powerset, (-1 : ℝ) ^ t.card = if u = ∅ then 1 else 0 := by
  have h : ((∑ t ∈ u.powerset, (-1 : ℤ) ^ t.card : ℤ) : ℝ)
      = ∑ t ∈ u.powerset, (-1 : ℝ) ^ t.card := by push_cast; ring
  rw [← h, Finset.sum_powerset_neg_one_pow_card]
  split <;> simp

/-- **Möbius inversion over the subset lattice** — Lauritzen **Lemma A.2**, Appendix A.3. For any
`F : Finset W → ℝ`,
`∑_{a ⊆ s} ∑_{b ⊆ a} (-1)^{|a|+|b|} F b = F s`.

The inner sum is Lauritzen's interaction term `φ_a` (his eq. (3.14)); the identity says that
summing the interactions over all subsets of `s` recovers `F s`.

*Sign convention.* The exponent is `|a| + |b|` rather than the more familiar `|a ∖ b|`: for
`b ⊆ a` the two agree, and `|a| + |b|` behaves far better under `Finset.card_insert_of_notMem`,
which is what the vanishing argument below needs.

Exchange the two sums, after replacing the inner index set `a.powerset` by `s.powerset` guarded
by `b ⊆ a`; reindex the resulting inner sum `∑_{b ⊆ a ⊆ s}` by `a ↦ a ∖ b` onto
`(s ∖ b).powerset`, and collapse it with the alternating sum over a subset lattice: it vanishes
unless `s ∖ b = ∅`, i.e. unless `b = s`. -/
private theorem sum_powerset_moebius {W : Type*} (F : Finset W → ℝ) (s : Finset W) :
    ∑ a ∈ s.powerset, ∑ b ∈ a.powerset, (-1 : ℝ) ^ (a.card + b.card) * F b = F s := by
  classical
  have step1 : ∀ a ∈ s.powerset,
      (∑ b ∈ a.powerset, (-1 : ℝ) ^ (a.card + b.card) * F b)
        = ∑ b ∈ s.powerset, if b ⊆ a then (-1 : ℝ) ^ (a.card + b.card) * F b else 0 := by
    intro a ha
    rw [Finset.mem_powerset] at ha
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => ⟨h.trans ha, h⟩, fun h => h.2⟩
  have H1 : (∑ a ∈ s.powerset, ∑ b ∈ a.powerset, (-1 : ℝ) ^ (a.card + b.card) * F b)
      = ∑ a ∈ s.powerset, ∑ b ∈ s.powerset,
          if b ⊆ a then (-1 : ℝ) ^ (a.card + b.card) * F b else 0 :=
    Finset.sum_congr rfl step1
  have step2 : ∀ b ∈ s.powerset,
      (∑ a ∈ s.powerset, if b ⊆ a then (-1 : ℝ) ^ (a.card + b.card) * F b else 0)
        = if b = s then F s else 0 := by
    intro b hb
    rw [Finset.mem_powerset] at hb
    rw [← Finset.sum_filter]
    have hre : (∑ a ∈ s.powerset.filter (fun a => b ⊆ a), (-1 : ℝ) ^ (a.card + b.card) * F b)
        = ∑ t ∈ (s \ b).powerset, (-1 : ℝ) ^ t.card * F b := by
      refine Finset.sum_nbij' (fun a => a \ b) (fun t => t ∪ b) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_powerset] at ha
        rw [Finset.mem_powerset]
        intro v hv
        rw [Finset.mem_sdiff] at hv ⊢
        exact ⟨ha.1 hv.1, hv.2⟩
      · intro t ht
        rw [Finset.mem_powerset] at ht
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.union_subset (ht.trans Finset.sdiff_subset) hb, Finset.subset_union_right⟩
      · intro a ha
        rw [Finset.mem_filter] at ha
        exact Finset.sdiff_union_of_subset ha.2
      · intro t ht
        rw [Finset.mem_powerset] at ht
        change (t ∪ b) \ b = t
        rw [Finset.union_sdiff_self,
          Finset.sdiff_eq_self_of_disjoint
            (Finset.disjoint_of_subset_left ht Finset.sdiff_disjoint)]
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_powerset] at ha
        have h1 : (a \ b).card + b.card = a.card := Finset.card_sdiff_add_card_eq_card ha.2
        have hsign : (-1 : ℝ) ^ (a.card + b.card) = (-1 : ℝ) ^ (a \ b).card := by
          have h2 : a.card + b.card = (a \ b).card + (b.card + b.card) := by omega
          rw [h2, pow_add, Even.neg_one_pow ⟨b.card, rfl⟩, mul_one]
        rw [hsign]
    rw [hre, ← Finset.sum_mul, sum_powerset_neg_one_pow_card_real]
    by_cases h : b = s
    · subst h; simp
    · have hne : s \ b ≠ ∅ := by
        rw [Ne, Finset.sdiff_eq_empty_iff_subset]
        exact fun hsb => h (Finset.Subset.antisymm hb hsb)
      rw [if_neg hne, if_neg h, zero_mul]
  have H2 : (∑ b ∈ s.powerset, ∑ a ∈ s.powerset,
        if b ⊆ a then (-1 : ℝ) ^ (a.card + b.card) * F b else 0)
      = ∑ b ∈ s.powerset, if b = s then F s else 0 :=
    Finset.sum_congr rfl step2
  rw [H1, Finset.sum_comm, H2]
  simp

/-- **Substitution into a reference configuration** — Lauritzen's `x^b` (Appendix A.3, p. 259):
`hcSub xs b x` agrees with `x` on `b` and with the reference configuration `xs` off `b`. -/
private def hcSub {W β : Type*} [DecidableEq W] (xs : W → β) (b : Finset W) (x : W → β) : W → β :=
  fun v => if v ∈ b then x v else xs v

private theorem hcSub_of_mem {W β : Type*} [DecidableEq W] (xs : W → β) (b : Finset W)
    (x : W → β) {v : W} (h : v ∈ b) : hcSub xs b x v = x v := if_pos h

private theorem hcSub_of_notMem {W β : Type*} [DecidableEq W] (xs : W → β) (b : Finset W)
    (x : W → β) {v : W} (h : v ∉ b) : hcSub xs b x v = xs v := if_neg h

/-- Lauritzen's `H_b(x) = log f(x^b)` — the logarithm of the mass at the configuration that
agrees with `x` on `b` and with the reference configuration off `b`.

*Real-valued, not `ℝ≥0∞`-valued, and deliberately so.* The Möbius sum below is **alternating**,
so it cannot live in `ℝ≥0∞`, which has no subtraction; and the multiplicative form of the
inversion would need `ℝ≥0∞`-division, whose junk values at `0` and `∞` would have to be excluded
by hand at every step. Strict positivity (`hpos`) and finiteness (`hp`) make `(p ·).toReal`
strictly positive and finite, so `Real.log` is honest and the whole inversion runs in the
ordered field `ℝ`; the exponential at the very end converts back. -/
private noncomputable def hcH {W β : Type*} [DecidableEq W] (p : (W → β) → ℝ≥0∞) (xs : W → β)
    (b : Finset W) (x : W → β) : ℝ :=
  Real.log (p (hcSub xs b x)).toReal

/-- Lauritzen's **interaction term** `φ_a`, his eq. **(3.14)**: the Möbius (alternating) sum of
`hcH` over the subsets of `a`. See `sum_powerset_moebius` for the sign convention. -/
private noncomputable def hcPhi {W β : Type*} [DecidableEq W] (p : (W → β) → ℝ≥0∞) (xs : W → β)
    (a : Finset W) (x : W → β) : ℝ :=
  ∑ b ∈ a.powerset, (-1 : ℝ) ^ (a.card + b.card) * hcH p xs b x

/-- `φ_a` depends on the configuration only through its `a`-coordinates: every `hcSub xs b x`
entering the sum has `b ⊆ a`, and `hcSub xs b` only reads `x` on `b`. This is what makes the
surviving terms genuine **clique potentials**. -/
private theorem dependsOn_hcPhi {W β : Type*} [DecidableEq W] (p : (W → β) → ℝ≥0∞) (xs : W → β)
    (a : Finset W) : DependsOn (hcPhi p xs a) (a : Set W) := by
  intro x y hxy
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_powerset] at hb
  have hsub : hcSub xs b x = hcSub xs b y := by
    funext v
    by_cases hv : v ∈ b
    · rw [hcSub_of_mem _ _ _ hv, hcSub_of_mem _ _ _ hv,
        hxy v (Finset.mem_coe.mpr (hb hv))]
    · rw [hcSub_of_notMem _ _ _ hv, hcSub_of_notMem _ _ _ hv]
  rw [hcH, hcH, hsub]

/-! #### The cross-ratio form of pairwise conditional independence -/

/-- **The cross-ratio identity.** For a strictly positive finite mass function, `X_i ⫫ X_j` given
all the remaining coordinates is equivalent to the vanishing of the `2 × 2` "interaction"
`p(s,t,r) · p(s',t',r) = p(s',t,r) · p(s,t',r)` — the four configurations differing only in the
`i`- and `j`-coordinates.

Here `y₀ = (s,t,r)`, `y₁ = (s',t,r)`, `y₂ = (s,t',r)`, `y₃ = (s',t',r)`.

Write `M := p_{V ∖ {i,j}}`, `A := p_{V ∖ {j}}`, `B := p_{V ∖ {i}}`. Lauritzen's identity
(3.2) at the blocks `{i}`, `{j}`, `V ∖ {i,j}` reads `p · M = A · B` (the joint block is all of
`V`), and `M` is common to all four configurations while `A` is common to `y₀, y₂` and to
`y₁, y₃`, and `B` to `y₀, y₁` and to `y₂, y₃`. Multiplying the four instances pairwise gives
the claim after cancelling `M²`, which is legitimate because `M` is nonzero and finite. -/
private theorem crossRatio_of_condIndepMass {p : (V → α) → ℝ≥0∞}
    -- LEAN-ONLY: finiteness of the mass function — the `ℝ≥0∞` cancellation of `M²` is invalid
    -- at `∞`; Lauritzen's `f` is a density
    (hp : ∀ y, p y ≠ ∞)
    -- USER-INPUT: strict positivity; Lauritzen Theorem 3.9, p. 36 (it makes `M ≠ 0`)
    (hpos : ∀ y, p y ≠ 0)
    {i j : V} (hij : i ≠ j)
    -- USER-INPUT: the pairwise conditional independence at the pair `(i, j)`; Lauritzen p. 32
    (hci : CondIndepMass p {i} {j} (Finset.univ \ {i, j}))
    {y₀ y₁ y₂ y₃ : V → α}
    -- LEAN-ONLY: `y₁` differs from `y₀` only in the `i`-coordinate
    (h₁ : ∀ v, v ≠ i → y₁ v = y₀ v)
    -- LEAN-ONLY: `y₂` differs from `y₀` only in the `j`-coordinate
    (h₂ : ∀ v, v ≠ j → y₂ v = y₀ v)
    -- LEAN-ONLY: `y₃` carries the `i`-coordinate of `y₁`, the `j`-coordinate of `y₂`, and
    -- agrees with `y₀` elsewhere
    (h₃i : y₃ i = y₁ i) (h₃j : y₃ j = y₂ j) (h₃ : ∀ v, v ≠ i → v ≠ j → y₃ v = y₀ v) :
    p y₀ * p y₃ = p y₁ * p y₂ := by
  classical
  have hU : ({i} ∪ {j} ∪ (Finset.univ \ {i, j}) : Finset V) = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_univ,
      Finset.mem_insert, true_and, iff_true, not_or]
    by_cases hvi : v = i
    · exact Or.inl (Or.inl hvi)
    by_cases hvj : v = j
    · exact Or.inl (Or.inr hvj)
    · exact Or.inr ⟨hvi, hvj⟩
  -- membership in the three conditioning blocks, spelled as coordinate constraints
  have hmemC : ∀ v : V, v ∈ ((Finset.univ \ {i, j} : Finset V) : Set V) → v ≠ i ∧ v ≠ j := by
    intro v hv
    simpa only [Finset.coe_sdiff, Set.mem_diff, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff, not_or, Finset.coe_univ, Set.mem_univ,
      true_and] using hv
  have hmemA : ∀ v : V, v ∈ (({i} ∪ (Finset.univ \ {i, j}) : Finset V) : Set V) → v ≠ j := by
    intro v hv
    simp only [Finset.coe_union, Set.mem_union, Finset.coe_singleton, Set.mem_singleton_iff,
      Finset.coe_sdiff, Set.mem_diff, Finset.coe_insert, Set.mem_insert_iff, not_or,
      Finset.coe_univ, Set.mem_univ, true_and] at hv
    rcases hv with rfl | hv
    · exact hij
    · exact hv.2
  have hmemB : ∀ v : V, v ∈ (({j} ∪ (Finset.univ \ {i, j}) : Finset V) : Set V) → v ≠ i := by
    intro v hv
    simp only [Finset.coe_union, Set.mem_union, Finset.coe_singleton, Set.mem_singleton_iff,
      Finset.coe_sdiff, Set.mem_diff, Finset.coe_insert, Set.mem_insert_iff, not_or,
      Finset.coe_univ, Set.mem_univ, true_and] at hv
    rcases hv with rfl | hv
    · exact hij.symm
    · exact hv.1
  -- the four instances of (3.2), with `p` in place of the joint marginal
  have hinst : ∀ y : V → α, p y * blockMarginal (Finset.univ \ {i, j}) p y
      = blockMarginal ({i} ∪ (Finset.univ \ {i, j})) p y
        * blockMarginal ({j} ∪ (Finset.univ \ {i, j})) p y := by
    intro y
    have := hci y
    rwa [hU, blockMarginal_univ] at this
  -- the marginals that coincide
  have hM : ∀ y : V → α, (∀ v, v ≠ i → v ≠ j → y v = y₀ v) →
      blockMarginal (Finset.univ \ {i, j}) p y = blockMarginal (Finset.univ \ {i, j}) p y₀ :=
    fun y hy => dependsOn_blockMarginal _ p fun v hv => hy v (hmemC v hv).1 (hmemC v hv).2
  have hA₀₂ : blockMarginal ({i} ∪ (Finset.univ \ {i, j})) p y₀
      = blockMarginal ({i} ∪ (Finset.univ \ {i, j})) p y₂ :=
    dependsOn_blockMarginal _ p fun v hv => (h₂ v (hmemA v hv)).symm
  have hA₁₃ : blockMarginal ({i} ∪ (Finset.univ \ {i, j})) p y₁
      = blockMarginal ({i} ∪ (Finset.univ \ {i, j})) p y₃ :=
    dependsOn_blockMarginal _ p fun v hv => by
      rcases eq_or_ne v i with rfl | hvi
      · exact h₃i.symm
      · rw [h₁ v hvi, h₃ v hvi (hmemA v hv)]
  have hB₀₁ : blockMarginal ({j} ∪ (Finset.univ \ {i, j})) p y₀
      = blockMarginal ({j} ∪ (Finset.univ \ {i, j})) p y₁ :=
    dependsOn_blockMarginal _ p fun v hv => (h₁ v (hmemB v hv)).symm
  have hB₂₃ : blockMarginal ({j} ∪ (Finset.univ \ {i, j})) p y₂
      = blockMarginal ({j} ∪ (Finset.univ \ {i, j})) p y₃ :=
    dependsOn_blockMarginal _ p fun v hv => by
      rcases eq_or_ne v j with rfl | hvj
      · exact h₃j.symm
      · rw [h₂ v hvj, h₃ v (hmemB v hv) hvj]
  -- all four configurations share the conditioning marginal
  have hM₀ := hM y₀ fun v _ _ => rfl
  have hM₁ := hM y₁ fun v hvi _ => h₁ v hvi
  have hM₂ := hM y₂ fun v _ hvj => h₂ v hvj
  have hM₃ := hM y₃ h₃
  have e₀ := hinst y₀
  have e₁ := hinst y₁
  have e₂ := hinst y₂
  have e₃ := hinst y₃
  rw [hM₁] at e₁
  rw [hM₂] at e₂
  rw [hM₃] at e₃
  rw [hM₀] at e₀
  -- multiply the four instances pairwise and cancel `M²`
  obtain ⟨M, hMdef⟩ : ∃ M, M = blockMarginal (Finset.univ \ {i, j}) p y₀ := ⟨_, rfl⟩
  rw [← hMdef] at e₀ e₁ e₂ e₃
  have hM0 : M ≠ 0 := hMdef ▸ blockMarginal_ne_zero _ _ hpos
  have hMt : M ≠ ∞ := hMdef ▸ blockMarginal_ne_top _ _ hp
  refine (ENNReal.mul_left_inj (mul_ne_zero hM0 hM0) (ENNReal.mul_ne_top hMt hMt)).mp ?_
  calc p y₀ * p y₃ * (M * M) = (p y₀ * M) * (p y₃ * M) := by ring
    _ = (blockMarginal ({i} ∪ (Finset.univ \ {i, j})) p y₀
          * blockMarginal ({j} ∪ (Finset.univ \ {i, j})) p y₀)
        * (blockMarginal ({i} ∪ (Finset.univ \ {i, j})) p y₃
          * blockMarginal ({j} ∪ (Finset.univ \ {i, j})) p y₃) := by rw [e₀, e₃]
    _ = (blockMarginal ({i} ∪ (Finset.univ \ {i, j})) p y₁
          * blockMarginal ({j} ∪ (Finset.univ \ {i, j})) p y₁)
        * (blockMarginal ({i} ∪ (Finset.univ \ {i, j})) p y₂
          * blockMarginal ({j} ∪ (Finset.univ \ {i, j})) p y₂) := by
          rw [← hA₁₃, ← hB₀₁, hA₀₂, ← hB₂₃]; ring
    _ = (p y₁ * M) * (p y₂ * M) := by rw [e₁, e₂]
    _ = p y₁ * p y₂ * (M * M) := by ring

/-! #### Vanishing of the interaction terms at non-complete sets -/

/-- **The crux of Hammersley–Clifford**: the interaction term `φ_a` vanishes identically whenever
`a` is **not** complete — Lauritzen **Theorem 3.9**, p. 36.

Pick non-adjacent `i ≠ j` in `a` and write `a = insert i (insert j c)` with
`c = (a.erase i).erase j`. Splitting `a.powerset` twice regroups the alternating sum as
`∑_{b ⊆ c} ±(H_b − H_{b ∪ i} − H_{b ∪ j} + H_{b ∪ {i,j}})`,
and each bracket vanishes: the four configurations `x^b`, `x^{b ∪ i}`, `x^{b ∪ j}`,
`x^{b ∪ {i,j}}` differ only in the `i`- and `j`-coordinates, so the cross-ratio identity — fed
by the pairwise Markov property at `(i, j)` — makes their masses satisfy `p·p = p·p`, hence
their logarithms cancel. -/
private theorem hcPhi_eq_zero_of_not_isClique {p : (V → α) → ℝ≥0∞}
    -- LEAN-ONLY: finiteness of the mass function; needed by `crossRatio_of_condIndepMass`
    (hp : ∀ y, p y ≠ ∞)
    -- USER-INPUT: strict positivity; Lauritzen Theorem 3.9, p. 36
    (hpos : ∀ y, p y ≠ 0)
    -- USER-INPUT: property (P); Lauritzen p. 32
    (hpm : IsPairwiseMarkov G (CondIndepMass p))
    (xs : V → α) {a : Finset V}
    -- USER-INPUT: `a` is not complete — the hypothesis under which the interaction dies
    (hna : ¬ G.IsClique (a : Set V)) (x : V → α) :
    hcPhi p xs a x = 0 := by
  classical
  -- two non-adjacent vertices inside `a`
  obtain ⟨i, hia, j, hja, hij, hadj⟩ : ∃ i ∈ a, ∃ j ∈ a, i ≠ j ∧ ¬ G.Adj i j := by
    by_contra hcon
    push Not at hcon
    exact hna fun u hu v hv huv => hcon u (by simpa using hu) v (by simpa using hv) huv
  have hja' : j ∈ a.erase i := Finset.mem_erase.mpr ⟨hij.symm, hja⟩
  obtain ⟨c, hcdef⟩ : ∃ c : Finset V, c = (a.erase i).erase j := ⟨_, rfl⟩
  have hjc : j ∉ c := hcdef ▸ Finset.notMem_erase j _
  have hic : i ∉ insert j c := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hij, fun hmem => Finset.notMem_erase i a
      (Finset.mem_of_mem_erase (hcdef ▸ hmem))⟩
  have hins : insert i (insert j c) = a := by
    rw [hcdef, Finset.insert_erase hja', Finset.insert_erase hia]
  -- the pairwise conditional independence at `(i, j)`
  have hci : CondIndepMass p {i} {j} (Finset.univ \ {i, j}) := hpm i j hij hadj
  -- the four-term identity, for every `b ⊆ c`
  have hbracket : ∀ b : Finset V, i ∉ b → j ∉ b →
      hcH p xs b x - hcH p xs (insert j b) x - hcH p xs (insert i b) x
        + hcH p xs (insert i (insert j b)) x = 0 := by
    intro b hib hjb
    have hcross : p (hcSub xs b x) * p (hcSub xs (insert i (insert j b)) x)
        = p (hcSub xs (insert i b) x) * p (hcSub xs (insert j b) x) := by
      refine crossRatio_of_condIndepMass hp hpos hij hci ?_ ?_ ?_ ?_ ?_
      · intro v hvi
        by_cases hvb : v ∈ b
        · rw [hcSub_of_mem _ _ _ (Finset.mem_insert_of_mem hvb), hcSub_of_mem _ _ _ hvb]
        · rw [hcSub_of_notMem _ _ _ (by simp [hvi, hvb]), hcSub_of_notMem _ _ _ hvb]
      · intro v hvj
        by_cases hvb : v ∈ b
        · rw [hcSub_of_mem _ _ _ (Finset.mem_insert_of_mem hvb), hcSub_of_mem _ _ _ hvb]
        · rw [hcSub_of_notMem _ _ _ (by simp [hvj, hvb]), hcSub_of_notMem _ _ _ hvb]
      · rw [hcSub_of_mem _ _ _ (Finset.mem_insert_self i _),
          hcSub_of_mem _ _ _ (Finset.mem_insert_self i b)]
      · rw [hcSub_of_mem _ _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self j b)),
          hcSub_of_mem _ _ _ (Finset.mem_insert_self j b)]
      · intro v hvi hvj
        by_cases hvb : v ∈ b
        · rw [hcSub_of_mem _ _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hvb)),
            hcSub_of_mem _ _ _ hvb]
        · rw [hcSub_of_notMem _ _ _ (by simp [hvi, hvj, hvb]), hcSub_of_notMem _ _ _ hvb]
    -- take `toReal` and logarithms
    have hne : ∀ y : V → α, (p y).toReal ≠ 0 := fun y =>
      ENNReal.toReal_ne_zero.mpr ⟨hpos y, hp y⟩
    have hreal : (p (hcSub xs b x)).toReal * (p (hcSub xs (insert i (insert j b)) x)).toReal
        = (p (hcSub xs (insert i b) x)).toReal * (p (hcSub xs (insert j b) x)).toReal := by
      rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul, hcross]
    have hlog := congrArg Real.log hreal
    rw [Real.log_mul (hne _) (hne _), Real.log_mul (hne _) (hne _)] at hlog
    simp only [hcH]
    linarith
  -- split the alternating sum along `i` and then `j`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = a.card := ⟨_, rfl⟩
  rw [hcPhi, ← hN, ← hins]
  simp only [Finset.sum_powerset_insert hic, Finset.sum_powerset_insert hjc]
  have hsplit : (∑ b ∈ c.powerset,
        ((-1 : ℝ) ^ (N + b.card) * hcH p xs b x
          + (-1 : ℝ) ^ (N + (insert j b).card) * hcH p xs (insert j b) x
          + ((-1 : ℝ) ^ (N + (insert i b).card) * hcH p xs (insert i b) x
            + (-1 : ℝ) ^ (N + (insert i (insert j b)).card)
              * hcH p xs (insert i (insert j b)) x)))
      = ((∑ b ∈ c.powerset, (-1 : ℝ) ^ (N + b.card) * hcH p xs b x)
          + ∑ b ∈ c.powerset, (-1 : ℝ) ^ (N + (insert j b).card) * hcH p xs (insert j b) x)
        + ((∑ b ∈ c.powerset, (-1 : ℝ) ^ (N + (insert i b).card) * hcH p xs (insert i b) x)
          + ∑ b ∈ c.powerset, (-1 : ℝ) ^ (N + (insert i (insert j b)).card)
              * hcH p xs (insert i (insert j b)) x) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← hsplit]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [Finset.mem_powerset] at hb
  have hjb : j ∉ b := fun h => hjc (hb h)
  have hib : i ∉ b := fun h => hic (Finset.mem_insert_of_mem (hb h))
  have hcj : (insert j b).card = b.card + 1 := Finset.card_insert_of_notMem hjb
  have hcii : (insert i b).card = b.card + 1 := Finset.card_insert_of_notMem hib
  have hcij : (insert i (insert j b)).card = b.card + 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hij, hib]), hcj]
  rw [hcj, hcii, hcij]
  have e1 : (-1 : ℝ) ^ (N + (b.card + 1)) = -(-1 : ℝ) ^ (N + b.card) := by
    rw [show N + (b.card + 1) = (N + b.card) + 1 by omega, pow_succ]; ring
  have e2 : (-1 : ℝ) ^ (N + (b.card + 2)) = (-1 : ℝ) ^ (N + b.card) := by
    rw [show N + (b.card + 2) = (N + b.card) + 2 by omega, pow_add]; ring
  rw [e1, e2]
  linear_combination ((-1 : ℝ) ^ (N + b.card)) * hbracket b hib hjb

/-- **The Hammersley–Clifford theorem** — Lauritzen **Theorem 3.9**, p. 36. For a *strictly
positive* mass function on a finite configuration space, the pairwise Markov property (P) and
the factorization property (F) are equivalent.

*Book vs Lean.* Lauritzen's hypotheses are that the density be **positive and continuous** with
respect to a product measure. Here the dominating product measure is counting measure on
`V → α`, and continuity is vacuous: Lauritzen himself notes on p. 28 that on a discrete space
every function is continuous. Positivity is `hpos`, and finiteness (`hp`) is the `ℝ≥0∞`-side
counterpart of "`f` is a density", needed so that the graphoid calculus
(`isGraphoid_condIndepMass_of_pos`) applies.

*Positivity is not removable.* Without it, (P) — indeed even (G) — fails to imply (F):
Lauritzen's **Example 3.10** (Moussouris, pp. 37–38); see the module docstring.

**Proof.** The `mp` direction is `factorizesOver_implies_pairwiseMarkov`.

The `mpr` direction is the Möbius inversion of `log p` over the subset lattice (Besag 1974;
Grimmett 1973; Lauritzen Appendix A.3). Fix a reference configuration `x✶` — legitimate because
`V → α` is either empty, in which case (F) is vacuous, or inhabited. Write `x^b` for the
configuration agreeing with `x` on `b` and with `x✶` off `b` (`hcSub`), set
`H_b(x) = log p(x^b)` (`hcH`) and let `φ_a` be the alternating sum of `H_b` over `b ⊆ a`
(`hcPhi`). Then:

* `sum_powerset_moebius` gives `∑_{a ⊆ V} φ_a(x) = H_V(x) = log p(x)`;
* `hcPhi_eq_zero_of_not_isClique` — the crux — gives `φ_a ≡ 0` for every non-complete `a`, by
  the cross-ratio form of the pairwise Markov property (`crossRatio_of_condIndepMass`);
* so `log p(x) = ∑_{c complete} φ_c(x)`, and exponentiating gives (F) with the clique potentials
  `ψ_c := exp ∘ φ_c`, whose `DependsOn` is `dependsOn_hcPhi`.

*Why `ℝ` and not `ℝ≥0∞`.* The Möbius sum is alternating, so it needs subtraction, and the
multiplicative form would need `ℝ≥0∞`-division with its junk values at `0` and `∞`. Positivity
and finiteness make `(p ·).toReal` a strictly positive real, so `Real.log` is faithful and the
whole inversion runs in `ℝ`; `ENNReal.ofReal ∘ Real.exp` converts back, and
`ENNReal.ofReal_prod_of_nonneg` turns the sum into the required product. This is the one place
in the area where the `ℝ≥0∞` mass algebra is deliberately left for `ℝ`.

*Positivity is used twice*, exactly as Lauritzen says: to take logarithms at all, and — through
`blockMarginal_ne_zero` — to cancel the conditioning marginal in the cross-ratio step. -/
theorem hammersleyClifford [DecidableRel G.Adj] (p : (V → α) → ℝ≥0∞)
    -- LEAN-ONLY: finiteness of the mass function — the `ℝ≥0∞` counterpart of "`f` is a
    -- density"; needed for the graphoid calculus in the reverse direction
    (hp : ∀ x, p x ≠ ∞)
    -- USER-INPUT: strict positivity of the mass function; Lauritzen Theorem 3.9, p. 36. The
    -- theorem is false without it (Example 3.10, Moussouris, pp. 37–38)
    (hpos : ∀ x, p x ≠ 0) :
    FactorizesOver G p ↔ IsPairwiseMarkov G (CondIndepMass p) := by
  classical
  refine ⟨factorizesOver_implies_pairwiseMarkov G p, fun hpm => ?_⟩
  -- the degenerate case: with no configurations at all, (F) is vacuous
  rcases isEmpty_or_nonempty (V → α) with hE | hN
  · exact ⟨fun _ _ => 1, fun _ _ _ _ _ => rfl, fun x => (hE.false x).elim⟩
  obtain ⟨xs⟩ := hN
  refine ⟨fun c x => ENNReal.ofReal (Real.exp (hcPhi p xs c x)), ?_, ?_⟩
  · intro c _ x y hxy
    change ENNReal.ofReal (Real.exp (hcPhi p xs c x))
      = ENNReal.ofReal (Real.exp (hcPhi p xs c y))
    rw [dependsOn_hcPhi p xs c hxy]
  · intro x
    -- Möbius inversion at the full vertex set
    have hpow : (Finset.univ : Finset V).powerset = (Finset.univ : Finset (Finset V)) := by
      ext b; simp
    have hsubuniv : hcSub xs (Finset.univ : Finset V) x = x := by
      funext v; exact hcSub_of_mem _ _ _ (Finset.mem_univ v)
    have hinv : ∑ a ∈ (Finset.univ : Finset (Finset V)), hcPhi p xs a x
        = Real.log (p x).toReal := by
      rw [← hpow]
      have := sum_powerset_moebius (fun b => hcH p xs b x) (Finset.univ : Finset V)
      simpa only [hcPhi, hcH, hsubuniv] using this
    -- the non-complete terms die
    have hsum : ∑ c ∈ completeSubsets G, hcPhi p xs c x = Real.log (p x).toReal := by
      rw [← hinv]
      have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset V))
        (fun c : Finset V => G.IsClique (c : Set V)) (fun c => hcPhi p xs c x)
      have hzero : ∑ c ∈ (Finset.univ : Finset (Finset V)).filter
          (fun c : Finset V => ¬ G.IsClique (c : Set V)), hcPhi p xs c x = 0 :=
        Finset.sum_eq_zero fun c hc =>
          hcPhi_eq_zero_of_not_isClique G hp hpos hpm xs (Finset.mem_filter.mp hc).2 x
      rw [completeSubsets, ← hsplit, hzero, add_zero]
    -- exponentiate
    have hposR : 0 < (p x).toReal := ENNReal.toReal_pos (hpos x) (hp x)
    calc p x = ENNReal.ofReal (p x).toReal := (ENNReal.ofReal_toReal (hp x)).symm
      _ = ENNReal.ofReal (Real.exp (Real.log (p x).toReal)) := by rw [Real.exp_log hposR]
      _ = ENNReal.ofReal (Real.exp (∑ c ∈ completeSubsets G, hcPhi p xs c x)) := by rw [hsum]
      _ = ENNReal.ofReal (∏ c ∈ completeSubsets G, Real.exp (hcPhi p xs c x)) := by
            rw [Real.exp_sum]
      _ = ∏ c ∈ completeSubsets G, ENNReal.ofReal (Real.exp (hcPhi p xs c x)) :=
            ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le

end StatLean.StatisticalModels.GraphicalModels
