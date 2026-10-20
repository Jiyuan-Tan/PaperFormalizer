module
public import StatLean.StatisticalModels.GraphicalModels.Directed.DAG
public import StatLean.StatisticalModels.GraphicalModels.Directed.Moralization
public import StatLean.StatisticalModels.GraphicalModels.Discrete.Factorization

@[expose] public section

/-!
# Recursive factorization over a DAG — property (DF)

Lauritzen's factorization property for **directed** acyclic graphs (p. 46, unnumbered): a mass
function factorizes recursively according to `D` when it is a product of one *kernel* per
vertex,
`p(x) = ∏_{v ∈ V} k_v(x_v, x_{pa(v)})`,
each `k_v` non-negative and normalised to `1` in its first argument. The whole point of the
property is **Lemma 3.21**: it transports into the undirected setting, because `{v} ∪ pa(v)` is a
*clique* of the moral graph — that is exactly what marrying the parents of a common child buys.

The setting is the discrete one — `V` and `α` finite, `p : (V → α) → ℝ≥0∞`, marginals
`blockMarginal`, conditional independence `CondIndepMass` — in which the undirected
factorization theory and the graphoid calculus of `Discrete/CondIndep.lean` are stated, so the
directed theory is obtained from the undirected one by transport.

* `IsLocalKernelOn` / `IsLocalKernel` — Lauritzen's kernels `k^α(·, ·)` on
  `𝒳_α × 𝒳_{pa(α)}`: each depends only on the coordinates of `{v} ∪ pa(v)` and sums to `1`
  over its own coordinate;
* `RecursivelyFactorizesOn` / `RecursivelyFactorizes` — property **(DF)**, p. 46, in a
  block form and its `V`-wide instance;
* `inducedMoralGraph` — the moral graph of the sub-DAG induced on a vertex block, i.e.
  Lauritzen's `(𝒢_A)^m`; a one-line composite of `DAG.induce` and `DAG.moralGraph`;
* `factorizesOver_of_recursivelyFactorizesOn` — the graph-free hinge: any undirected graph in
  which every `{v} ∪ pa(v)` is complete receives the factorization;
* **`recursivelyFactorizes_implies_factorizesOver_moralGraph`** — Lauritzen **Lemma 3.21**,
  p. 47, and `recursivelyFactorizes_implies_globalMarkov_moralGraph` its second half
  ("and obeys therefore the global Markov property relative to `𝒢^m`");
* `recursivelyFactorizesOn_implies_factorizesOver_inducedMoralGraph` — Lemma 3.21 read on the
  sub-DAG induced on an ancestral set, the form needed for Corollary 3.23;
* `sum_update_prod_of_notMem_parents` — the induction step of everything below: summing a
  childless vertex out of the product telescopes, *because* the kernels are normalised;
* **`blockMarginal_recursivelyFactorizesOn_of_ancestralSet`** — Lauritzen **Proposition 3.22**,
  p. 47: the marginal on an ancestral set factorizes recursively over the induced sub-DAG;
* `sum_eq_one_of_recursivelyFactorizes` — a recursively factorizing mass has total mass `1`
  (the "easy induction argument" of p. 46).

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996**, §3.2.2: the recursive factorization property (DF) is the
**unnumbered** display on p. 46 (`∫ k^α(y_α, x_{pa(α)}) μ_α(dy_α) = 1` and
`f(x) = ∏_{α ∈ V} k^α(x_α, x_{pa(α)})`); **Lemma 3.21** (p. 47) is "if `P` admits a recursive
factorization according to `𝒢`, it factorizes according to the moral graph `𝒢^m` and obeys
therefore the global Markov property relative to `𝒢^m`"; **Proposition 3.22** (p. 47) is "if `P`
admits a recursive factorization according to `𝒢` and `A` is an ancestral set, then the marginal
`P_A` admits a recursive factorization according to `𝒢_A`". The remark that the kernels are the
conditional densities of `X_α` given `X_{pa(α)}` is on p. 46 (`Lauritzen §3.2.2` in tags).

**Proof formalization notes.** *Book vs Lean, five deliberate differences.*

1. **Counting measure, so the integral is a sum.** Lauritzen's normalisation is
   `∫ k^α(y_α, x_{pa(α)}) μ_α(dy_α) = 1` for a σ-finite `μ_α`; here `μ_α` is counting measure on
   the finite `α`, so it reads `∑ a : α, k_v (Function.update x v a) = 1`. Varying `x` at the
   single coordinate `v` is exactly varying `y_α` — `k_v` does not see any other coordinate of
   the update because it depends only on `{v} ∪ pa(v)` and `v ∉ pa(v)` (acyclicity).
2. **Kernels are functions of the whole configuration.** As in `Discrete/CondIndep.lean` and
   `Discrete/Factorization.lean`, `k v : (V → α) → ℝ≥0∞` constrained by
   `DependsOn (k v) ↑(insert v (D.parents v))`, rather than a function on
   `α × (↥(D.parents v) → α)`. The two readings are interchangeable
   (`dependsOn_iff_exists_comp`); a single type is what makes `∏ v, k v x` a plain
   `Finset.prod`.
3. **A block form, `…On`, is primitive.** Lauritzen's Proposition 3.22 says the *marginal on an
   ancestral set `A`* factorizes recursively "according to `𝒢_A`". In a formalisation where the
   sub-DAG `𝒢_A` still lives on the full vertex type `V`, "recursive factorization according to
   `𝒢_A`" cannot be the product over **all** of `V`: that product is a probability mass on
   `V → α`, whereas the marginal is constant in the coordinates outside `A` and hence has total
   mass `#α ^ #(V ∖ A)`. The faithful statement is the product over `A`, which is precisely
   `RecursivelyFactorizesOn D A`. Because `A` is ancestral, `pa_{𝒢_A}(v) = pa_𝒢(v)` for every
   `v ∈ A`, so a `D`-local kernel family *is* a `𝒢_A`-local one on `A` and no separate notion is
   needed. `RecursivelyFactorizes D = RecursivelyFactorizesOn D Finset.univ` recovers (DF).
4. **No positivity, no finiteness anywhere in this file.** Lemma 3.21 and Proposition 3.22 are
   identities between products and sums; positivity enters only in `Directed/Markov.lean`, at
   Theorem 3.27's reverse implication.
5. **`sum_eq_one_of_recursivelyFactorizes` needs `[Nonempty α]`, and the book's setting supplies
   it.** If `α` is empty and `V` is not, then `V → α` is empty, every `∀ x`-condition is vacuous,
   (DF) holds of *every* `p`, and the total mass is `0`. Lauritzen's state spaces `𝒳_α` are
   sample spaces of random variables and are never empty. No other statement in the file needs
   the hypothesis: they are all `∀ x` statements, hence vacuously true in that degenerate regime.

**On `inducedMoralGraph`.** The intended reading of `inducedMoralGraph D T` is Lauritzen's
`(𝒢_T)^m`: keep only the vertices of `T` and the arrows between them, marry parents-within-`T` of
a common child in `T`, then drop directions. It is *not* the same as `(D.moralGraph)` restricted
to `T` — a marriage created by a child outside `T` survives in the latter and must not survive in
the former, and that difference is exactly what makes the directed global Markov property sharp.

**Bibliographic comments.** Recursive factorization on a DAG and its equivalence with the
directed Markov properties are due to H. Kiiveri, T. P. Speed and J. B. Carlin, "Recursive causal
models," *J. Austral. Math. Soc. Ser. A* **36** (1984), 30–52 — Lauritzen's own attribution on
p. 46 — with the moralization device and the global reading developed by J. Pearl and
T. Verma (1987), T. Verma and J. Pearl (1990), and S. L. Lauritzen, A. P. Dawid, B. N. Larsen and
H.-G. Leimer, "Independence properties of directed Markov fields," *Networks* **20** (1990),
491–505.
-/

open SimpleGraph
open scoped ENNReal

namespace StatLean.StatisticalModels.GraphicalModels

variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]

/-! ### Local kernels -/

/-- **Lauritzen's kernels** `k^α(·, ·)` (p. 46, unnumbered), restricted to a block `A`: for every
`v ∈ A` the factor `k v` depends on the configuration only through the coordinates of
`{v} ∪ pa(v)`, and it is a probability mass function in its own coordinate — summing it over the
`v`-coordinate, with all other coordinates held fixed, gives `1`.

*Book vs Lean.* The book's normalisation `∫ k^α(y_α, x_{pa(α)}) μ_α(dy_α) = 1` is a sum here,
counting measure being the dominating measure of the discrete setting; and `y_α ↦ ·` is realised
as `Function.update x v ·`, which by the dependence condition moves exactly the argument `y_α`.

*Edge behaviour.* Nothing is required of `k v` for `v ∉ A` — those factors never enter the
products below. Kernels are `ℝ≥0∞`-valued and are not required to be finite pointwise, only
summable to `1`, which does force each value to be `≤ 1`. On a vertex with no parents the
condition says `k v` is a probability mass function on `α` alone. -/
def IsLocalKernelOn (D : DAG V) [DecidableRel D.Adj] (A : Finset V)
    (k : V → (V → α) → ℝ≥0∞) : Prop :=
  ∀ v ∈ A, DependsOn (k v) ((insert v (D.parents v) : Finset V) : Set V) ∧
    ∀ x : V → α, ∑ a : α, k v (Function.update x v a) = 1

/-- **Lauritzen's kernel family** `{k^α}_{α ∈ V}` (p. 46, unnumbered) — `IsLocalKernelOn` at the
full vertex set. -/
def IsLocalKernel (D : DAG V) [DecidableRel D.Adj] (k : V → (V → α) → ℝ≥0∞) : Prop :=
  IsLocalKernelOn D Finset.univ k

/-- A kernel family that is local on a block is local on every sub-block. -/
theorem IsLocalKernelOn.mono {D : DAG V} [DecidableRel D.Adj] {A B : Finset V}
    {k : V → (V → α) → ℝ≥0∞}
    -- LEAN-ONLY: the block inclusion along which the (purely pointwise) condition restricts
    (hAB : A ⊆ B)
    -- USER-INPUT: the kernel family; Lauritzen §3.2.2, p. 46
    (hk : IsLocalKernelOn D B k) :
    IsLocalKernelOn D A k :=
  fun v hv => hk v (hAB hv)

/-- A `V`-wide kernel family is local on every block. -/
theorem IsLocalKernel.isLocalKernelOn {D : DAG V} [DecidableRel D.Adj]
    {k : V → (V → α) → ℝ≥0∞}
    -- USER-INPUT: the kernel family; Lauritzen §3.2.2, p. 46
    (hk : IsLocalKernel D k) (A : Finset V) :
    IsLocalKernelOn D A k :=
  IsLocalKernelOn.mono (Finset.subset_univ A) hk

/-! ### Property (DF) -/

/-- **Recursive factorization over a block** — the shape Lauritzen's Proposition 3.22 (p. 47)
produces: `p(x) = ∏_{v ∈ A} k_v(x_v, x_{pa(v)})` for a kernel family local on `A`.

*Book vs Lean.* For an **ancestral** `A` this *is* the book's "admits a recursive factorization
according to `𝒢_A`": the induced sub-DAG has `pa_{𝒢_A}(v) = pa_𝒢(v)` for every `v ∈ A`, so the
kernel family of `𝒢_A` and that of `𝒢` are the same object read on `A`. Taking the product over
`A` rather than over `V` is forced: a marginal on `A` does not depend on the coordinates outside
`A`, so it cannot be a product of `#V` normalised kernels (see module docstring, note 3).

*Edge behaviour.* `RecursivelyFactorizesOn D ∅ p` says `p ≡ 1`, the empty product — the
degenerate marginal "on no variables" of a probability mass function. -/
def RecursivelyFactorizesOn (D : DAG V) [DecidableRel D.Adj] (A : Finset V)
    (p : (V → α) → ℝ≥0∞) : Prop :=
  ∃ k : V → (V → α) → ℝ≥0∞, IsLocalKernelOn D A k ∧ ∀ x, p x = ∏ v ∈ A, k v x

/-- **Property (DF), recursive factorization** — Lauritzen p. 46, unnumbered:
`p(x) = ∏_{v ∈ V} k_v(x_v, x_{pa(v)})` for a family of normalised kernels.

*Edge behaviour.* A recursively factorizing mass automatically has total mass `1`
(`sum_eq_one_of_recursivelyFactorizes`), so — unlike `FactorizesOver` in the undirected file —
(DF) is *not* invariant under rescaling `p`. That asymmetry is the book's: Lauritzen's `f` is the
density of a probability distribution and his kernels are conditional densities. On the empty DAG
(no arrows) it says `p` is a product of one-dimensional probability mass functions, i.e. the
coordinates are independent; on a complete DAG it says nothing beyond `∑ p = 1`. -/
def RecursivelyFactorizes (D : DAG V) [DecidableRel D.Adj] (p : (V → α) → ℝ≥0∞) : Prop :=
  RecursivelyFactorizesOn D Finset.univ p

/-- (DF) is the block form at the full vertex set — definitionally. -/
theorem recursivelyFactorizes_iff_on_univ (D : DAG V) [DecidableRel D.Adj]
    (p : (V → α) → ℝ≥0∞) :
    RecursivelyFactorizes D p ↔ RecursivelyFactorizesOn D Finset.univ p :=
  Iff.rfl

/-! ### The moral graph of an induced sub-DAG -/

/-- **Lauritzen's `(𝒢_T)^m`** (p. 47, Corollary 3.23): moralize the sub-DAG induced on `T`.

*Not* `D.moralGraph` restricted to `T` — a marriage of two vertices of `T` created by a common
child *outside* `T` belongs to the latter and must be absent from the former. That difference is
what makes the directed global Markov property sharp, and it is why the ancestral closure appears
in Corollary 3.23 at all. -/
abbrev inducedMoralGraph (D : DAG V) (T : Finset V) : SimpleGraph V :=
  (D.induce T).moralGraph

/-! ### Lemma 3.21 — into the undirected layer -/

/-- **The hinge, stated without any moral vocabulary.** If every set `{v} ∪ pa(v)`, `v ∈ A`, is
*complete* in an undirected graph `G`, then a mass function that factorizes recursively over `A`
factorizes over `G` in the undirected sense (F).

This is the content of Lauritzen's proof of Lemma 3.21 — "the sets `{α} ∪ pa(α)` are complete in
`𝒢^m` and we can therefore let `ψ_{{α}∪pa(α)} = k^α`" — isolated from moralization, so that both
Lemma 3.21 and its ancestral-restriction form below are instantiations. The construction: send
`v` to the complete set `insert v (D.parents v)` and let `ψ c` be the product of the `k v` in
that fibre; `DependsOn (ψ c) ↑c` because every factor in the fibre depends on `c` on the nose,
and the potentials of the complete sets that receive no vertex are the empty product `1`. -/
theorem factorizesOver_of_recursivelyFactorizesOn (D : DAG V) [DecidableRel D.Adj]
    (A : Finset V) (G : SimpleGraph V) [DecidableRel G.Adj] (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: `{v} ∪ pa(v)` is complete in `G` — for `G = 𝒢^m` this is exactly what
    -- moralization is built to deliver; Lauritzen Lemma 3.21, p. 47
    (hclique : ∀ v ∈ A, G.IsClique ((insert v (D.parents v) : Finset V) : Set V))
    -- USER-INPUT: property (DF) on the block; Lauritzen §3.2.2, p. 46
    (hp : RecursivelyFactorizesOn D A p) :
    FactorizesOver G p := by
  classical
  obtain ⟨k, hk, hprod⟩ := hp
  -- send `v ↦ fa(v) = {v} ∪ pa(v)`; the potential of a complete set is the product of the
  -- kernels in its fibre, and the fibres of the complete sets receiving no vertex are empty
  refine ⟨fun c x => ∏ v ∈ Finset.filter (fun v => insert v (D.parents v) = c) A, k v x, ?_, ?_⟩
  · intro c _ y z hyz
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [Finset.mem_filter] at hv
    have hdep : DependsOn (k v) ((c : Finset V) : Set V) := hv.2 ▸ (hk v hv.1).1
    exact hdep hyz
  · intro x
    rw [hprod x]
    exact (Finset.prod_fiberwise_of_maps_to
      (fun v hv => mem_completeSubsets.mpr (hclique v hv)) _).symm

/-- **Lauritzen Lemma 3.21**, p. 47, first half: a mass function admitting a recursive
factorization according to the DAG `D` **factorizes according to the moral graph** `𝒢^m`.

This is the hinge of the entire directed theory: it is the only place where a directed statement
becomes an undirected one, and everything downstream — Corollary 3.23, the directed hierarchy,
Theorem 3.27 — rests on it. The clique hypothesis is precisely the defining property of
moralization: marrying the parents of a common child makes `{v} ∪ pa(v)` complete. -/
theorem recursivelyFactorizes_implies_factorizesOver_moralGraph (D : DAG V)
    [DecidableRel D.Adj] (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (DF); Lauritzen §3.2.2, p. 46
    (hp : RecursivelyFactorizes D p) :
    FactorizesOver D.moralGraph p :=
  factorizesOver_of_recursivelyFactorizesOn D Finset.univ D.moralGraph p
    (fun v _ => D.isClique_insert_parents v) hp

/-- **Lauritzen Lemma 3.21**, p. 47, second half: "…and obeys therefore the global Markov
property relative to `𝒢^m`" — the first half followed by the undirected (F) ⇒ (G) (Lauritzen
Proposition 3.8). -/
theorem recursivelyFactorizes_implies_globalMarkov_moralGraph (D : DAG V)
    [DecidableRel D.Adj] (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (DF); Lauritzen §3.2.2, p. 46
    (hp : RecursivelyFactorizes D p) :
    IsGlobalMarkov D.moralGraph (CondIndepMass p) :=
  factorizesOver_implies_globalMarkov D.moralGraph p
    (recursivelyFactorizes_implies_factorizesOver_moralGraph D p hp)

/-- **Lemma 3.21 on an induced sub-DAG** — the form Corollary 3.23 needs. For an **ancestral**
`T`, a mass function factorizing recursively over `T` factorizes, in the undirected sense, over
`(𝒢_T)^m`.

Ancestrality is what makes the clique hypothesis of `factorizesOver_of_recursivelyFactorizesOn`
payable: for `v ∈ T` it gives `pa(v) ⊆ T`, hence `pa_{𝒢_T}(v) = pa(v)`, hence
`{v} ∪ pa(v)` is a set of vertices of `𝒢_T` married by the moralization of `𝒢_T` itself. Without
it, `{v} ∪ pa(v)` need not even be contained in `T`. -/
theorem recursivelyFactorizesOn_implies_factorizesOver_inducedMoralGraph (D : DAG V)
    [DecidableRel D.Adj] (T : Finset V) (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: `T` is an ancestral set; Lauritzen §2.1.1, p. 6, and Proposition 3.22, p. 47
    (hT : D.IsAncestralSet T)
    -- USER-INPUT: property (DF) on the block; Lauritzen §3.2.2, p. 46
    (hp : RecursivelyFactorizesOn D T p) :
    FactorizesOver (inducedMoralGraph D T) p :=
  factorizesOver_of_recursivelyFactorizesOn D T (inducedMoralGraph D T) p
    (fun _ hv => D.isClique_insert_parents_induce hT hv) hp

/-! ### Proposition 3.22 — restriction to an ancestral set -/

/-- **The induction step of the directed theory: summing out a childless vertex telescopes.**
If `v ∈ A` has no children inside `A`, then summing the product `∏_{u ∈ A} k_u` over the
`v`-coordinate deletes exactly the factor `k_v`.

Two facts do the work, and they are the two halves of `IsLocalKernelOn`: every other factor
`k_u`, `u ∈ A ∖ {v}`, is *constant* along the `v`-coordinate, since it depends only on
`{u} ∪ pa(u)`, which misses `v` (that is the childlessness hypothesis); and the factor `k_v`
sums to `1`, which is the normalisation. This lemma is Lauritzen's "easy induction argument"
(p. 46) in one line, and both `blockMarginal_recursivelyFactorizesOn_of_ancestralSet` and
`sum_eq_one_of_recursivelyFactorizes` are inductions on it. -/
theorem sum_update_prod_of_notMem_parents (D : DAG V) [DecidableRel D.Adj] (A : Finset V)
    (k : V → (V → α) → ℝ≥0∞)
    -- USER-INPUT: the kernel family; Lauritzen §3.2.2, p. 46
    (hk : IsLocalKernelOn D A k) {v : V}
    -- USER-INPUT: the vertex being summed out lies in the block
    (hvA : v ∈ A)
    -- USER-INPUT: it has no children inside the block — the "terminal vertex" of Lauritzen's
    -- induction, p. 51 (proof of Theorem 3.27) and p. 47 (Proposition 3.22)
    (hv : ∀ u ∈ A, u ≠ v → v ∉ D.parents u) (x : V → α) :
    ∑ a : α, ∏ u ∈ A, k u (Function.update x v a) = ∏ u ∈ A.erase v, k u x := by
  classical
  -- every factor other than `k v` is constant along the `v`-coordinate …
  have hconst : ∀ a : α, ∏ u ∈ A.erase v, k u (Function.update x v a)
      = ∏ u ∈ A.erase v, k u x := by
    intro a
    refine Finset.prod_congr rfl fun u hu => ?_
    have huA : u ∈ A := Finset.mem_of_mem_erase hu
    have hune : u ≠ v := Finset.ne_of_mem_erase hu
    refine (hk u huA).1 ?_
    intro i hi
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi
    have hiv : i ≠ v := by
      rcases hi with rfl | hi
      · exact hune
      · rintro rfl; exact hv u huA hune hi
    exact Function.update_of_ne hiv a x
  -- … and `k v` sums to `1`.
  calc ∑ a : α, ∏ u ∈ A, k u (Function.update x v a)
      = ∑ a : α, k v (Function.update x v a) *
          ∏ u ∈ A.erase v, k u (Function.update x v a) :=
        Finset.sum_congr rfl fun a _ =>
          (Finset.mul_prod_erase A (fun u => k u (Function.update x v a)) hvA).symm
    _ = ∑ a : α, k v (Function.update x v a) * ∏ u ∈ A.erase v, k u x :=
        Finset.sum_congr rfl fun a _ => by rw [hconst a]
    _ = (∑ a : α, k v (Function.update x v a)) * ∏ u ∈ A.erase v, k u x := by
        rw [Finset.sum_mul]
    _ = ∏ u ∈ A.erase v, k u x := by rw [(hk v hvA).2 x, one_mul]

/-- **Summing out one coordinate of a marginal.** Marginalising on `C` is the same as
marginalising on the one-vertex-larger block `insert u C` and then summing over the
`u`-coordinate.

Spelled with `Function.update` rather than `Function.updateFinset` so that it composes on the
nose with `sum_update_prod_of_notMem_parents` (whose normalisation is a sum over `α`, not over
`↥{u} → α`). The fibres `agreeOn (insert u C) (Function.update x u a)`, as `a` ranges over `α`,
are exactly the fibres of `y ↦ y u` on `agreeOn C x`. -/
theorem blockMarginal_eq_sum_update (p : (V → α) → ℝ≥0∞) {C : Finset V} {u : V}
    -- LEAN-ONLY: the fresh coordinate must not already be marginalised on, else the fibres below
    -- are not a partition
    (hu : u ∉ C) (x : V → α) :
    blockMarginal C p x = ∑ a : α, blockMarginal (insert u C) p (Function.update x u a) := by
  classical
  have key : ∀ a : α, agreeOn (insert u C) (Function.update x u a)
      = Finset.filter (fun y : V → α => y u = a) (agreeOn C x) := by
    intro a
    ext y
    simp only [Finset.mem_filter, mem_agreeOn, Finset.mem_insert]
    constructor
    · intro hy
      refine ⟨fun i hi => ?_, ?_⟩
      · have hiv : i ≠ u := by rintro rfl; exact hu hi
        simpa [Function.update_of_ne hiv] using hy i (Or.inr hi)
      · simpa using hy u (Or.inl rfl)
    · rintro ⟨h1, h2⟩ i (rfl | hi)
      · simpa using h2
      · have hiv : i ≠ u := by rintro rfl; exact hu hi
        simpa [Function.update_of_ne hiv] using h1 i hi
  simp only [blockMarginal, key]
  exact (Finset.sum_fiberwise (agreeOn C x) (fun y : V → α => y u) p).symm

/-- **Lauritzen Proposition 3.22**, p. 47: if `P` admits a recursive factorization according to
`𝒢` and `A` is an **ancestral** set, then the marginal `P_A` admits a recursive factorization
according to `𝒢_A`.

*Book vs Lean.* "According to `𝒢_A`" is `RecursivelyFactorizesOn D A`: the same kernel family,
multiplied over `A` only. Ancestrality gives `pa(v) ⊆ A` for `v ∈ A`, so the `𝒢`-kernels *are*
the `𝒢_A`-kernels there, and the product over `A` depends on `x` only through `x_A`, as a
marginal must. See module docstring, note 3, for why the product cannot run over all of `V`.

*Proof idea.* Induct on `A`'s complement. Ancestrality of `A` makes `V ∖ A` closed under
children, so the induced sub-DAG on `V ∖ A` — finite and acyclic — has a vertex `u` with no
children at all; summing out its coordinate deletes `k_u` from the product
(`sum_update_prod_of_notMem_parents`), and `A ∪ (V ∖ A ∖ {u})` is again ancestral.

*Degenerate regime.* With `α` empty and `V` nonempty both sides quantify over an empty
configuration space, so the statement is vacuously true; no `[Nonempty α]` is needed. -/
theorem blockMarginal_recursivelyFactorizesOn_of_ancestralSet (D : DAG V) [DecidableRel D.Adj]
    (A : Finset V)
    -- USER-INPUT: `A` is an ancestral set; Lauritzen §2.1.1, p. 6, and Proposition 3.22, p. 47
    (hA : D.IsAncestralSet A) (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (DF); Lauritzen §3.2.2, p. 46
    (hp : RecursivelyFactorizes D p) :
    RecursivelyFactorizesOn D A (blockMarginal A p) := by
  classical
  obtain ⟨k, hk, hprod⟩ := hp
  refine ⟨k, IsLocalKernelOn.mono (Finset.subset_univ A) hk, ?_⟩
  -- A topological order supplies, at every proper ancestral block, a vertex outside it all of
  -- whose parents are inside it — the vertex whose coordinate is summed out next.
  obtain ⟨f, hf⟩ := D.exists_topologicalOrder
  have key : ∀ n : ℕ, ∀ C : Finset V, (Finset.univ \ C).card = n → D.IsAncestralSet C →
      ∀ x, blockMarginal C p x = ∏ v ∈ C, k v x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro C hcard hC x
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · -- `C = Finset.univ`: the marginal is `p` itself
        have hCuniv : C = Finset.univ :=
          Finset.univ_subset_iff.mp
            (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard))
        rw [hCuniv, blockMarginal_univ]
        exact hprod x
      · -- pick the topologically first vertex outside `C`; its parents all lie in `C`
        have hne : (Finset.univ \ C).Nonempty := Finset.card_pos.mp (hcard ▸ hn)
        obtain ⟨u, huS, humin⟩ := Finset.exists_min_image (Finset.univ \ C) f hne
        have huC : u ∉ C := (Finset.mem_sdiff.mp huS).2
        have hpa : ∀ w, D.Adj w u → w ∈ C := by
          intro w hw
          by_contra hwC
          exact absurd (hf (Relation.TransGen.single hw))
            (not_lt.mpr (humin w (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwC⟩)))
        have hC' : D.IsAncestralSet (insert u C) := by
          intro a b hab hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact Finset.mem_insert_of_mem (hpa a hab)
          · exact Finset.mem_insert_of_mem (hC hab hb)
        have hsdiff : Finset.univ \ insert u C = (Finset.univ \ C).erase u := by
          ext w
          simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, Finset.mem_univ,
            true_and, not_or]
        have hcard' : (Finset.univ \ insert u C).card = n - 1 := by
          rw [hsdiff, Finset.card_erase_of_mem huS, hcard]
        have IH := ih (n - 1) (by omega) (insert u C) hcard' hC'
        -- sum out the `u`-coordinate: `blockMarginal` gains a vertex, the product loses `k u`
        have hchild : ∀ w ∈ insert u C, w ≠ u → u ∉ D.parents w := by
          intro w hw hwu hmem
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hwu rfl
          · exact huC (hC (DAG.mem_parents.mp hmem) hw)
        rw [blockMarginal_eq_sum_update p huC x]
        simp only [fun a : α => IH (Function.update x u a)]
        rw [sum_update_prod_of_notMem_parents D (insert u C) k
            (IsLocalKernelOn.mono (Finset.subset_univ _) hk) (Finset.mem_insert_self u C)
            hchild x,
          Finset.erase_insert huC]
  exact key _ A rfl hA

/-- **A recursively factorizing mass is a probability mass function** — Lauritzen's remark on
p. 46 that "it is an easy induction argument to show that … the kernels `k^α(·, x_{pa(α)})` are
densities for the conditional distribution of `X_α` given `X_{pa(α)}`", of which total mass `1`
is the first consequence.

This is the reason (DF) is *not* scale-invariant, unlike the undirected `FactorizesOver`, and
therefore the reason Theorem 3.27 carries an explicit normalisation hypothesis on `p` in the
direction that produces (DF).

*Proof idea.* Marginalise on the ancestral set `A = ∅`: the marginal is the total mass and the
empty product is `1`; equivalently, sum out the coordinates in reverse topological order,
deleting one normalised kernel at a time. -/
theorem sum_eq_one_of_recursivelyFactorizes
    -- LEAN-ONLY: a nonempty state space. With `α` empty and `V` nonempty the configuration space
    -- `V → α` is empty, every hypothesis of (DF) is vacuous and the total mass is `0`;
    -- Lauritzen's state spaces `𝒳_α` are sample spaces of random variables, hence never empty
    [Nonempty α] (D : DAG V) [DecidableRel D.Adj] (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (DF); Lauritzen §3.2.2, p. 46
    (hp : RecursivelyFactorizes D p) :
    ∑ x : V → α, p x = 1 := by
  obtain ⟨k, _, hprod⟩ :=
    blockMarginal_recursivelyFactorizesOn_of_ancestralSet D ∅ (D.isAncestralSet_empty) p hp
  have h := hprod (fun _ => Classical.arbitrary α)
  rw [blockMarginal_empty] at h
  simpa using h

/-- A recursively factorizing mass is pointwise finite — the hypothesis `hp : ∀ y, p y ≠ ∞` that
every lemma of `Discrete/CondIndep.lean` carries, obtained from
`sum_eq_one_of_recursivelyFactorizes` by `Finset.single_le_sum`. -/
theorem ne_top_of_recursivelyFactorizes
    -- LEAN-ONLY: a nonempty state space; see `sum_eq_one_of_recursivelyFactorizes`
    [Nonempty α] (D : DAG V) [DecidableRel D.Adj] (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (DF); Lauritzen §3.2.2, p. 46
    (hp : RecursivelyFactorizes D p) (x : V → α) :
    p x ≠ ∞ := by
  have h : p x ≤ ∑ y : V → α, p y :=
    Finset.single_le_sum (f := p) (fun i _ => zero_le) (Finset.mem_univ x)
  rw [sum_eq_one_of_recursivelyFactorizes D p hp] at h
  exact ne_top_of_le_ne_top ENNReal.one_ne_top h

end StatLean.StatisticalModels.GraphicalModels
