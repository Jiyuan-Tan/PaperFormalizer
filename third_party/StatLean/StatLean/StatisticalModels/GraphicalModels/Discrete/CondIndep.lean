module
public import StatLean.StatisticalModels.GraphicalModels.Core.Coordinates
public import StatLean.StatisticalModels.GraphicalModels.Core.Semigraphoid
public import Mathlib.Data.Finset.Update
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Data.ENNReal.Operations
public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Conditional independence of a discrete mass function — Lauritzen's identity (3.2)

The finite-state model class: a vertex set `V`, a state space `α`, both finite, configurations
`V → α`, and a **mass function** `p : (V → α) → ℝ≥0∞`. This is the layer where the whole
graphoid calculus becomes elementary algebra of finite sums and products, and it is the layer
the factorization theory (`Discrete/Factorization.lean`) is built on.

* `agreeOn A x` — the configurations that agree with `x` on the block `A`;
* `blockMarginal A p` — the **marginal mass on `A`**, `p_A(x) = ∑ p(y)` over `y ∈ agreeOn A x`;
  the file's workhorse, together with its API (`dependsOn_blockMarginal`,
  `blockMarginal_univ`, `blockMarginal_antitone`, `blockMarginal_ne_top`, and the
  block-splitting identity `blockMarginal_eq_sum_updateFinset`);
* `CondIndepMass p A B C` — Lauritzen's **eq. (3.2)**, `p_{A∪B∪C}·p_C = p_{A∪C}·p_{B∪C}`;
* `CondIndepMass.symm` / `.decomposition` / `.weakUnion` / `.contraction` / `.intersection` —
  the five properties (C1)–(C5), each stated with exactly the hypotheses it needs;
* **`isSemigraphoid_condIndepMass`** — the headline: (C1)–(C4) hold for **every** finite mass
  function, so the abstract Markov hierarchy of `Undirected/Markov.lean` instantiates here;
* **`isGraphoid_condIndepMass_of_pos`** — (C5) as well, under strict positivity: Lauritzen
  **Proposition 3.1**, p. 29;
* `condIndepMass_of_exists_factorization` / `condIndepMass_iff_exists_factorization` —
  Lauritzen's **eq. (3.6)**, `f(x, y, z) = h(x, z) k(y, z)`; the `mpr` half is deliberately
  separated out because it needs neither finiteness nor positivity;
* `condIndepMass_of_condIndepCoords` — the bridge from the general measure-theoretic
  `CondIndepCoords` of `Core/Coordinates.lean` down to the mass identity.

**Carrier choice.** `p : (V → α) → ℝ≥0∞`, a bare function with **no** normalisation built in.
Three reasons. (i) Lauritzen's identity (3.2) is homogeneous of degree two in `p` — replacing
`p` by `c·p` scales both sides by `c²` — so normalisation is genuinely irrelevant to (C1)–(C5)
and putting it in the carrier would be a hypothesis nobody uses. (ii) `ℝ≥0∞` is a complete
commutative semiring in which every finite sum and product is defined and no subtraction is ever
needed, so each axiom is a rearrangement of sums and products; a `PMF` carrier would add a
coercion to every algebraic step, and a `Measure (V → α)` carrier would route the same algebra
through `lintegral`/`Measure.map`. (iii) The `Measure` reading is recovered exactly once, in
`condIndepMass_of_condIndepCoords`, at `p := fun x => μ (X ⁻¹' {x})`.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996**, §3.1: the density identity **(3.2)**
`f_{XYZ}(x,y,z) f_Z(z) = f_{XZ}(x,z) f_{YZ}(y,z)` is on p. 28, the equivalent factorisation
criterion **(3.6)** `f(x,y,z) = h(x,z) k(y,z)` on p. 29, the properties **(C1)–(C4)** are the
unnumbered labelled list on p. 29 and **(C5)** is on p. 30, and **Proposition 3.1** (p. 29) is
the statement that a strictly positive continuous density satisfies (C5). Lauritzen remarks on
p. 28 that on a discrete space every function is continuous, so the continuity hypothesis of
Proposition 3.1 is vacuous here (`Lauritzen §3.1`).

**Proof formalization notes.** *Book vs Lean, four deliberate differences.*

1. **Marginals are functions of the whole configuration.** Lauritzen's `f_A` is a function of
   `x_A`; ours is a function of the full `x : V → α` that happens to depend only on the
   coordinates in `A` (`dependsOn_blockMarginal`, using Mathlib's `DependsOn`). This keeps
   every quantity in (3.2) in a *single* type, so the identity is a plain equation in `ℝ≥0∞`
   rather than a statement modulo the transport maps `Finset.restrict₂` that a subtype-indexed
   marginal would force. It costs nothing: the two readings are interchangeable through
   `dependsOn_iff_exists_comp`.
2. **`ℝ≥0∞` cancellation is not free, and the axioms are stated accordingly.** (C1) and (C2)
   are pure sum rearrangements and hold for an arbitrary `p`. (C3), (C4) and (C5) all divide by
   a marginal, which in `ℝ≥0∞` is legitimate only away from `0` and `∞`. The `0` case is
   *derivable* — `blockMarginal_antitone` makes every marginal over a larger block vanish with
   the smaller one, and both sides of the conclusion then collapse to `0` — so the only genuine
   side condition is `hp : ∀ x, p x ≠ ∞`, which for a finite `V` and finite `α` is exactly
   finiteness of the total mass. It is carried by (C3), (C4), (C5) and by nothing else. (C5)
   additionally needs `hpos`, per Proposition 3.1.
3. **Positivity is an assumption of Proposition 3.1, not a convenience.** (C5) is *false* for
   general masses: Lauritzen's counterexample (p. 30) takes `X = Y = Z` uniform on `{0, 1}`.
   So `isGraphoid_condIndepMass_of_pos` carries `hpos : ∀ x, p x ≠ 0` and
   `isSemigraphoid_condIndepMass` does not claim intersection.
4. **Disjointness.** `IsSemigraphoid`/`IsGraphoid` state (C1)–(C5) for pairwise disjoint blocks,
   matching the book. The standalone lemmas below record the *minimal* disjointness each
   identity actually uses — (C2) needs only `Disjoint A D`, (C4) needs none at all — so the
   bundling theorems discard the unused fields rather than the lemmas silently assuming them.

**Bibliographic comments.** The discrete factorisation criterion (3.6) is the working form of
conditional independence used throughout the Markov-random-field literature since
J. Besag, "Spatial interaction and the statistical analysis of lattice systems," *J. Roy.
Statist. Soc. Ser. B* **36** (1974), 192–236; the axiomatic reading of (C1)–(C5) is
A. P. Dawid, "Conditional independence in statistical theory," *ibid.* **41** (1979), 1–31,
with the names *symmetry / decomposition / weak union / contraction / intersection* due to
J. Pearl, *Probabilistic Reasoning in Intelligent Systems*, Morgan Kaufmann, 1988. That
(C1)–(C4) are sound but not complete for probabilistic conditional independence is
M. Studený's theorem (1992); see the `Core/Semigraphoid.lean` docstring.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.StatisticalModels.GraphicalModels

variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]

/-! ### The marginal on a block -/

/-- The configurations that **agree with `x` on the block `A`**, i.e. the fibre of
`Finset.restrict A` through `x`. Summing `p` over this set is the marginal on `A`.

Edge behaviour: `agreeOn ∅ x = Finset.univ` (no constraint) and `agreeOn Finset.univ x = {x}`;
`x ∈ agreeOn A x` always, so the set is never empty — this is what makes a strictly positive
mass function have strictly positive marginals. -/
def agreeOn (A : Finset V) (x : V → α) : Finset (V → α) :=
  Finset.univ.filter fun y => ∀ i ∈ A, y i = x i

@[simp]
theorem mem_agreeOn {A : Finset V} {x y : V → α} :
    y ∈ agreeOn A x ↔ ∀ i ∈ A, y i = x i := by
  simp [agreeOn]

/-- The **marginal mass on the block `A`** (Lauritzen §3.1, p. 28, his `f_A`): sum the mass
over all coordinates *outside* `A`, i.e. over all configurations agreeing with `x` on `A`.

Edge behaviour: `blockMarginal Finset.univ p = p` (`blockMarginal_univ`) and
`blockMarginal ∅ p x = ∑ y, p y`, the total mass, for every `x`. The value at `x` depends only
on the coordinates of `x` inside `A` (`dependsOn_blockMarginal`), which is how it plays the
role of Lauritzen's function of `x_A`. No normalisation of `p` is assumed anywhere; the
marginal of an unnormalised mass is the corresponding unnormalised marginal. -/
noncomputable def blockMarginal (A : Finset V) (p : (V → α) → ℝ≥0∞) (x : V → α) : ℝ≥0∞ :=
  ∑ y ∈ agreeOn A x, p y

/-- The marginal on `A` depends on the configuration only through the coordinates in `A` —
Lauritzen's `f_A` is a function of `x_A`. Indeed `agreeOn A x = agreeOn A y` whenever `x` and
`y` agree on `A`. -/
theorem dependsOn_blockMarginal (A : Finset V) (p : (V → α) → ℝ≥0∞) :
    DependsOn (blockMarginal A p) (A : Set V) := by
  intro x y hxy
  have hset : agreeOn A x = agreeOn A y := by
    ext z
    simp only [mem_agreeOn]
    exact ⟨fun hz i hi => (hz i hi).trans (hxy i (by simpa using hi)),
      fun hz i hi => (hz i hi).trans (hxy i (by simpa using hi)).symm⟩
  simp only [blockMarginal, hset]

/-- Marginalising over the full vertex set is the identity: `agreeOn univ x = {x}`. This is the
identity that lets the factorization file feed a factorisation of `p` itself into the
criterion (3.6), whose subject is `blockMarginal (A ∪ B ∪ C) p`. -/
theorem blockMarginal_univ (p : (V → α) → ℝ≥0∞) :
    blockMarginal Finset.univ p = p := by
  funext x
  have hset : agreeOn Finset.univ x = {x} := by
    ext y
    simp [mem_agreeOn, funext_iff]
  simp [blockMarginal, hset]

/-- Marginalising over the empty block gives the total mass, independently of `x`. -/
theorem blockMarginal_empty (p : (V → α) → ℝ≥0∞) (x : V → α) :
    blockMarginal ∅ p x = ∑ y, p y := by
  have hset : agreeOn (∅ : Finset V) x = Finset.univ := by
    ext y; simp [mem_agreeOn]
  simp [blockMarginal, hset]

/-- Marginals are **antitone** in the block: enlarging the block shrinks the index set of the
sum, since `agreeOn B x ⊆ agreeOn A x` for `A ⊆ B`. This is the lemma that discharges the
`p_C = 0` branch of every cancellation below. -/
theorem blockMarginal_antitone {A B : Finset V} (p : (V → α) → ℝ≥0∞) (x : V → α)
    -- LEAN-ONLY: the block inclusion along which the marginal decreases; Lauritzen's marginals
    -- are indexed by subsets and this monotonicity is implicit in his §3.1 manipulations
    (hAB : A ⊆ B) :
    blockMarginal B p x ≤ blockMarginal A p x := by
  refine Finset.sum_le_sum_of_subset ?_
  intro y hy
  simp only [mem_agreeOn] at hy ⊢
  exact fun i hi => hy i (hAB hi)

/-- A vanishing marginal forces every finer marginal to vanish — `blockMarginal_antitone` in
the form the `ℝ≥0∞` cancellation branches need. -/
theorem blockMarginal_eq_zero_of_subset {A B : Finset V} (p : (V → α) → ℝ≥0∞) (x : V → α)
    -- LEAN-ONLY: the block inclusion; see `blockMarginal_antitone`
    (hAB : A ⊆ B)
    -- LEAN-ONLY: vanishing of the coarser marginal
    (h : blockMarginal A p x = 0) :
    blockMarginal B p x = 0 := by
  simpa [h] using blockMarginal_antitone p x hAB

/-- A finite mass function has finite marginals — the side condition that makes `ℝ≥0∞`
cancellation legitimate in (C3), (C4) and (C5). -/
theorem blockMarginal_ne_top {p : (V → α) → ℝ≥0∞} (A : Finset V) (x : V → α)
    -- LEAN-ONLY: finiteness of the mass function. On a finite configuration space this is
    -- equivalent to finiteness of the total mass; Lauritzen's `f` is a density, hence finite
    (hp : ∀ y, p y ≠ ∞) :
    blockMarginal A p x ≠ ∞ :=
  ENNReal.sum_ne_top.mpr fun y _ => hp y

/-- A strictly positive mass function has strictly positive marginals: `x ∈ agreeOn A x`, so
every marginal sum has a positive summand. The hypothesis of Lauritzen's Proposition 3.1
(p. 29) in the form (C5) needs it. -/
theorem blockMarginal_ne_zero {p : (V → α) → ℝ≥0∞} (A : Finset V) (x : V → α)
    -- USER-INPUT: strict positivity of the mass function; Lauritzen Proposition 3.1, p. 29
    (hpos : ∀ y, p y ≠ 0) :
    blockMarginal A p x ≠ 0 := by
  intro hz
  rw [blockMarginal, Finset.sum_eq_zero_iff] at hz
  exact hpos x (hz x (by simp [mem_agreeOn]))

/-- **The block-splitting identity** — the workhorse of every proof in this file. Marginalising
on `S` is the same as marginalising on the larger block `S ∪ T` and then summing the result
over all configurations of the extra block `T`.

The sum on the right is over `↥T → α`, and `Function.updateFinset x T b` is `x` with its
`T`-coordinates replaced by `b`. Disjointness of `T` from `S` is essential: it is what makes
the fibres `agreeOn (S ∪ T) (Function.updateFinset x T b)`, as `b` varies, a *partition* of
`agreeOn S x`. -/
theorem blockMarginal_eq_sum_updateFinset (p : (V → α) → ℝ≥0∞) (S T : Finset V) (x : V → α)
    -- LEAN-ONLY: the extra block must not meet the block being marginalised on, else the
    -- fibres below are not a partition; Lauritzen's marginalisation is always over fresh
    -- coordinates
    (hTS : Disjoint T S) :
    blockMarginal S p x
      = ∑ b : ↥T → α,
          blockMarginal (S ∪ T) p (Function.updateFinset (π := fun _ => α) x T b) := by
  classical
  have key : ∀ b : ↥T → α,
      agreeOn (S ∪ T) (Function.updateFinset (π := fun _ => α) x T b)
        = {y ∈ agreeOn S x | (fun i : ↥T => y (i : V)) = b} := by
    intro b
    ext y
    simp only [Finset.mem_filter, mem_agreeOn, Finset.mem_union, Function.updateFinset,
      funext_iff]
    constructor
    · intro hy
      refine ⟨fun i hi => ?_, fun i => ?_⟩
      · simpa [dif_neg (Finset.disjoint_right.mp hTS hi)] using hy i (Or.inl hi)
      · simpa [dif_pos i.2] using hy (i : V) (Or.inr i.2)
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · simpa [dif_neg (Finset.disjoint_right.mp hTS hi)] using h1 i hi
      · simpa [dif_pos hi] using h2 ⟨i, hi⟩
  rw [blockMarginal,
    ← Finset.sum_fiberwise (agreeOn S x) (fun y : V → α => fun i : ↥T => y (i : V)) p]
  exact Finset.sum_congr rfl fun b _ => by rw [blockMarginal, key b]

/-! ### Lauritzen's identity (3.2) -/

/-- **Conditional independence of a discrete mass function**, Lauritzen **eq. (3.2)**, p. 28:
`X_A ⫫ X_B ∣ X_C` iff, for every configuration `x`,
`p_{A∪B∪C}(x) · p_C(x) = p_{A∪C}(x) · p_{B∪C}(x)`.

Edge behaviour and scope. Both sides depend on `x` only through `x_{A∪B∪C}`, so the universal
quantifier over the full configuration space is Lauritzen's quantifier over `(x_A, x_B, x_C)`.
No normalisation of `p` is required: the identity is homogeneous of degree two, so it holds for
`p` iff it holds for `c · p` for any `0 < c < ∞`. With `A = ∅` it is a tautology
(`∅ ∪ B ∪ C = B ∪ C` and `∅ ∪ C = C`), and likewise with `B = ∅`; with `C = ∅` it is
unconditional independence of the two blocks scaled by the total mass. For `p ≡ 0` it holds
vacuously, and for a `p` taking the value `∞` it is still a well-formed statement but the
cancellation lemmas below no longer apply — see `blockMarginal_ne_top`. -/
def CondIndepMass (p : (V → α) → ℝ≥0∞) (A B C : Finset V) : Prop :=
  ∀ x : V → α,
    blockMarginal (A ∪ B ∪ C) p x * blockMarginal C p x
      = blockMarginal (A ∪ C) p x * blockMarginal (B ∪ C) p x

/-- **(C1), symmetry** (Lauritzen p. 29; Pearl's *symmetry*). Pure commutativity: `A ∪ B = B ∪ A`
and multiplication in `ℝ≥0∞` commutes. No hypothesis of any kind — in particular neither
finiteness nor disjointness. -/
theorem CondIndepMass.symm {p : (V → α) → ℝ≥0∞} {A B C : Finset V}
    -- USER-INPUT: the conditional independence to be reversed; Lauritzen §3.1 (C1), p. 29
    (h : CondIndepMass p A B C) :
    CondIndepMass p B A C := by
  intro x
  rw [Finset.union_comm B A]
  exact (h x).trans (mul_comm _ _)

/-- **(C2), decomposition** (Lauritzen p. 29; Pearl's *decomposition*): if `X_A` is independent
of the joint block `X_{B ∪ D}` given `X_C`, then it is independent of `X_B` given `X_C`.

*Hypotheses.* Only `Disjoint A D`, and **no finiteness**: the proof sums Lauritzen's identity
over the extra coordinates `T = D ∖ (A ∪ B ∪ C)` on both sides and never divides. The factors
`p_C` and `p_{A∪C}` are constant along `T`, and the two set identities
`(A ∪ (B ∪ D) ∪ C) \ T = A ∪ B ∪ C` and `((B ∪ D) ∪ C) \ T = B ∪ C` — the second is
where `Disjoint A D` is used — put the summed factors back in place. -/
theorem CondIndepMass.decomposition {p : (V → α) → ℝ≥0∞} {A B C D : Finset V}
    -- USER-INPUT: the book's disjointness convention, in the one instance the identity uses:
    -- the discarded block must not meet the first block; Lauritzen §3.1 (C2), p. 29
    (hAD : Disjoint A D)
    -- USER-INPUT: the independence to be weakened; Lauritzen §3.1 (C2), p. 29
    (h : CondIndepMass p A (B ∪ D) C) :
    CondIndepMass p A B C := by
  classical
  intro x
  -- The fresh coordinates summed over: the part of `D` not already covered by `A ∪ B ∪ C`.
  obtain ⟨T, hTdef⟩ : ∃ T : Finset V, T = D \ (A ∪ B ∪ C) := ⟨_, rfl⟩
  have hTW : Disjoint T (A ∪ B ∪ C) := hTdef ▸ Finset.sdiff_disjoint
  have hTBC : Disjoint T (B ∪ C) :=
    hTW.mono_right (fun v hv => by
      simp only [Finset.mem_union] at hv ⊢; tauto)
  have hTC : Disjoint T C := hTBC.mono_right (fun v hv => by simp [hv])
  have hTAC : Disjoint T (A ∪ C) :=
    hTW.mono_right (fun v hv => by
      simp only [Finset.mem_union] at hv ⊢; tauto)
  -- The two set identities that put the summed blocks back in place.
  have hU : A ∪ B ∪ C ∪ T = A ∪ (B ∪ D) ∪ C := by
    subst hTdef
    rw [Finset.union_sdiff_self_eq_union]
    ext v; simp only [Finset.mem_union]; tauto
  have hV : B ∪ C ∪ T = B ∪ D ∪ C := by
    subst hTdef
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((hv | hv) | ⟨hv, -⟩) <;> tauto
    · rintro ((hv | hv) | hv)
      · tauto
      · by_cases hvA : v ∈ A ∪ B ∪ C
        · simp only [Finset.mem_union] at hvA
          rcases hvA with (hvA | hvB) | hvC
          · exact absurd hv (Finset.disjoint_left.mp hAD hvA)
          · tauto
          · tauto
        · exact Or.inr ⟨hv, by simpa only [Finset.mem_union] using hvA⟩
      · tauto
  -- Every factor free of the `T`-coordinates is constant along the sum.
  have hoff : ∀ (E : Finset V) (b : ↥T → α), Disjoint T E →
      blockMarginal E p (Function.updateFinset (π := fun _ => α) x T b)
        = blockMarginal E p x := by
    intro E b hTE
    refine dependsOn_blockMarginal E p fun i hi => ?_
    have hiT : i ∉ T := Finset.disjoint_right.mp hTE (by simpa using hi)
    simp [Function.updateFinset, dif_neg hiT]
  have e1 := blockMarginal_eq_sum_updateFinset p (A ∪ B ∪ C) T x hTW
  have e2 := blockMarginal_eq_sum_updateFinset p (B ∪ C) T x hTBC
  rw [hU] at e1
  rw [hV] at e2
  rw [e1, e2, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← hoff C b hTC, h _, hoff (A ∪ C) b hTAC]

/-- The single `ℝ≥0∞` cancellation shared by (C3) and (C4): from `a·b = c·d` and `c·e = f·b`,
divide out the invertible `b` to get `a·e = f·d`. (C3) and (C4) are *the same* algebraic step,
run in opposite directions — (C4) cancels the marginal on `C ∪ D` and (C3) the one on `C` — so
they are both instances of this lemma. -/
private theorem mul_cancel_cross {a b c d e f : ℝ≥0∞} (hb0 : b ≠ 0) (hbt : b ≠ ∞)
    (H₁ : a * b = c * d) (H₂ : c * e = f * b) :
    a * e = f * d := by
  refine (ENNReal.mul_left_inj hb0 hbt).mp ?_
  calc a * e * b = a * b * e := by ring
    _ = c * d * e := by rw [H₁]
    _ = c * e * d := by ring
    _ = f * b * d := by rw [H₂]
    _ = f * d * b := by ring

/-- **(C3), weak union** (Lauritzen p. 29; Pearl's *weak union*): a discarded sub-block may be
moved into the conditioning set.

*Hypotheses.* `Disjoint A B` (to extract `X_A ⫫ X_D ∣ X_C` from the premise by (C2)) and
finiteness. Multiply the goal through by `p_C`; the premise rewrites the left-hand side and
(C2), applied at `A`, `D`, `C` after commuting the union, rewrites the right-hand side, and
both land on `p_{A∪C} · p_{B∪C∪D} · p_{C∪D}`. Cancelling `p_C` is legitimate away from `0` and
`∞`; on the branch `p_C x = 0` both sides of the conclusion collapse to `0`. -/
theorem CondIndepMass.weakUnion {p : (V → α) → ℝ≥0∞} {A B C D : Finset V}
    -- LEAN-ONLY: finiteness of the mass function — `ℝ≥0∞` cancellation is invalid at `∞`;
    -- Lauritzen's `f` is a density and this hypothesis is vacuous for him
    (hp : ∀ y, p y ≠ ∞)
    -- USER-INPUT: the book's disjointness convention, in the instance the identity uses;
    -- Lauritzen §3.1 (C3), p. 29
    (hAB : Disjoint A B)
    -- USER-INPUT: the independence to be weakened; Lauritzen §3.1 (C3), p. 29
    (h : CondIndepMass p A (B ∪ D) C) :
    CondIndepMass p A B (C ∪ D) := by
  intro x
  have hs1 : A ∪ (B ∪ D) ∪ C = A ∪ B ∪ (C ∪ D) := by
    ext v; simp only [Finset.mem_union]; tauto
  have hs2 : B ∪ D ∪ C = B ∪ (C ∪ D) := by
    ext v; simp only [Finset.mem_union]; tauto
  have hs3 : A ∪ D ∪ C = A ∪ (C ∪ D) := by
    ext v; simp only [Finset.mem_union]; tauto
  -- (C2) at the blocks `A`, `D`, `C`, discarding `B`: this is where `Disjoint A B` is used.
  have h' : CondIndepMass p A (D ∪ B) C := by rwa [Finset.union_comm D B]
  have H₂ := CondIndepMass.decomposition hAB h' x
  rw [hs3, Finset.union_comm D C] at H₂
  have H₁ := h x
  rw [hs1, hs2] at H₁
  by_cases hz : blockMarginal C p x = 0
  · have z1 : blockMarginal (C ∪ D) p x = 0 :=
      blockMarginal_eq_zero_of_subset p x Finset.subset_union_left hz
    have z2 : blockMarginal (A ∪ (C ∪ D)) p x = 0 :=
      blockMarginal_eq_zero_of_subset p x
        (Finset.subset_union_left.trans Finset.subset_union_right) hz
    rw [z1, z2, mul_zero, zero_mul]
  · exact mul_cancel_cross hz (blockMarginal_ne_top _ _ hp) H₁ H₂.symm

/-- **(C4), contraction** (Lauritzen p. 29; Pearl's *contraction*): independence given a larger
conditioning set, together with independence of the extra block given the smaller one,
recombines into independence of the union.

*Hypotheses.* Finiteness only — **no disjointness at all**; the identity is a rearrangement of
the two premises followed by one cancellation. Multiply the goal by `p_{C∪D}`, rewrite
the left-hand side by the first premise and then by the second, and observe that both sides
become `p_{A∪C} · p_{B∪C∪D} · p_{C∪D}`. Cancelling `p_{C∪D}` is legitimate away from `0` and
`∞`; on the branch `p_{C∪D} x = 0` both `p_{A∪B∪D∪C} x` and `p_{B∪D∪C} x` vanish and the
conclusion reads `0 = 0`. -/
theorem CondIndepMass.contraction {p : (V → α) → ℝ≥0∞} {A B C D : Finset V}
    -- LEAN-ONLY: finiteness of the mass function; see `CondIndepMass.weakUnion`
    (hp : ∀ y, p y ≠ ∞)
    -- USER-INPUT: independence given the larger conditioning set; Lauritzen §3.1 (C4), p. 29
    (h₁ : CondIndepMass p A B (C ∪ D))
    -- USER-INPUT: independence of the extra block given the smaller one; Lauritzen §3.1 (C4)
    (h₂ : CondIndepMass p A D C) :
    CondIndepMass p A (B ∪ D) C := by
  intro x
  have hs1 : A ∪ (B ∪ D) ∪ C = A ∪ B ∪ (C ∪ D) := by
    ext v; simp only [Finset.mem_union]; tauto
  have hs2 : B ∪ D ∪ C = B ∪ (C ∪ D) := by
    ext v; simp only [Finset.mem_union]; tauto
  have hs3 : A ∪ D ∪ C = A ∪ (C ∪ D) := by
    ext v; simp only [Finset.mem_union]; tauto
  rw [hs1, hs2]
  have H₁ := h₁ x
  have H₂ := h₂ x
  rw [hs3, Finset.union_comm D C] at H₂
  by_cases hz : blockMarginal (C ∪ D) p x = 0
  · have z1 : blockMarginal (A ∪ B ∪ (C ∪ D)) p x = 0 :=
      blockMarginal_eq_zero_of_subset p x Finset.subset_union_right hz
    have z2 : blockMarginal (B ∪ (C ∪ D)) p x = 0 :=
      blockMarginal_eq_zero_of_subset p x Finset.subset_union_right hz
    rw [z1, z2, zero_mul, mul_zero]
  · exact mul_cancel_cross hz (blockMarginal_ne_top _ _ hp) H₁ H₂

/-! ### Helpers for (C5)

Lauritzen's Proposition 3.1 runs through the factorisation criterion (3.6), which is stated
below as `condIndepMass_of_exists_factorization`; since (C5) precedes it in this file, the
content of that `mpr` half lives here as a private lemma, and the public theorem is its
instance. The rest of this section is the four-point identity that turns each premise of
(C5) into a statement free of the block it does not see. -/

/-- The content of `condIndepMass_of_exists_factorization` (Lauritzen eq. (3.6) ⇒ (3.2)),
placed early so that `CondIndepMass.intersection` can use it. See the public theorem below
for the statement's provenance. -/
private theorem condIndepMass_of_factorization {p : (V → α) → ℝ≥0∞} {A B C : Finset V}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {h k : (V → α) → ℝ≥0∞}
    (hh : DependsOn h ((A ∪ C : Finset V) : Set V))
    (hk : DependsOn k ((B ∪ C : Finset V) : Set V))
    (hfac : ∀ x, blockMarginal (A ∪ B ∪ C) p x = h x * k x) :
    CondIndepMass p A B C := by
  intro x
  -- The three ways of writing the joint block, as they come out of the splitting identity.
  have hs1 : A ∪ C ∪ B = A ∪ B ∪ C := by ext v; simp only [Finset.mem_union]; tauto
  have hs2 : B ∪ C ∪ A = A ∪ B ∪ C := by ext v; simp only [Finset.mem_union]; tauto
  have hs3 : C ∪ A ∪ B = A ∪ B ∪ C := by ext v; simp only [Finset.mem_union]; tauto
  have hBAC : Disjoint B (A ∪ C) := Finset.disjoint_union_right.mpr ⟨hAB.symm, hBC⟩
  have hABC : Disjoint A (B ∪ C) := Finset.disjoint_union_right.mpr ⟨hAB, hAC⟩
  have hBCA : Disjoint B (C ∪ A) := Finset.disjoint_union_right.mpr ⟨hBC, hAB.symm⟩
  -- A factor free of the updated block is constant along the sum.
  have hoff : ∀ (f : (V → α) → ℝ≥0∞) (E T : Finset V), DependsOn f (E : Set V) →
      Disjoint T E → ∀ (y : V → α) (b : ↥T → α),
        f (Function.updateFinset (π := fun _ => α) y T b) = f y := by
    intro f E T hf hTE y b
    refine hf fun i hi => ?_
    have hiT : i ∉ T := Finset.disjoint_right.mp hTE (by simpa using hi)
    simp [Function.updateFinset, dif_neg hiT]
  -- `k` sees the `B`-update but not the `A`-update underneath it.
  have hk2 : ∀ (a : ↥A → α) (b : ↥B → α),
      k (Function.updateFinset (π := fun _ => α)
          (Function.updateFinset (π := fun _ => α) x A a) B b)
        = k (Function.updateFinset (π := fun _ => α) x B b) := by
    intro a b
    refine hk fun i hi => ?_
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hi
    by_cases hiB : i ∈ B
    · simp [Function.updateFinset, dif_pos hiB]
    · have hiA : i ∉ A := Finset.disjoint_right.mp hAC (by tauto)
      simp [Function.updateFinset, dif_neg hiB, dif_neg hiA]
  -- Marginal on `A ∪ C`: sum the factorisation over `B`.
  have eAC : blockMarginal (A ∪ C) p x
      = h x * ∑ b : ↥B → α, k (Function.updateFinset (π := fun _ => α) x B b) := by
    rw [blockMarginal_eq_sum_updateFinset p (A ∪ C) B x hBAC, hs1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [hfac _, hoff h (A ∪ C) B hh hBAC x b]
  -- Marginal on `B ∪ C`: sum the factorisation over `A`.
  have eBC : blockMarginal (B ∪ C) p x
      = (∑ a : ↥A → α, h (Function.updateFinset (π := fun _ => α) x A a)) * k x := by
    rw [blockMarginal_eq_sum_updateFinset p (B ∪ C) A x hABC, hs2, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by
      rw [hfac _, hoff k (B ∪ C) A hk hABC x a]
  -- Marginal on `C`: sum over `A`, then over `B`.
  have eC : blockMarginal C p x
      = (∑ a : ↥A → α, h (Function.updateFinset (π := fun _ => α) x A a))
        * ∑ b : ↥B → α, k (Function.updateFinset (π := fun _ => α) x B b) := by
    rw [blockMarginal_eq_sum_updateFinset p C A x hAC, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [blockMarginal_eq_sum_updateFinset p (C ∪ A) B _ hBCA, hs3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hfac _, hoff h (A ∪ C) B hh hBAC _ b, hk2 a b]
  rw [hfac x, eC, eAC, eBC]
  ring

/-- `z` with its `E`-coordinates replaced by those of the reference configuration `x₀`. The
`ℝ≥0∞` bookkeeping of (C5) needs a *named* configuration in which one block has been fixed at
a reference value, and this is it. -/
private def substOn (x₀ : V → α) (E : Finset V) (z : V → α) : V → α :=
  fun i => if i ∈ E then x₀ i else z i

omit [Fintype V] [Fintype α] [DecidableEq α] in
private theorem substOn_of_mem {x₀ : V → α} {E : Finset V} {z : V → α} {i : V} (hi : i ∈ E) :
    substOn x₀ E z i = x₀ i := if_pos hi

omit [Fintype V] [Fintype α] [DecidableEq α] in
private theorem substOn_of_notMem {x₀ : V → α} {E : Finset V} {z : V → α} {i : V} (hi : i ∉ E) :
    substOn x₀ E z i = z i := if_neg hi

/-- The `ℝ≥0∞` half of the four-point identity: four evaluations of (3.2) at configurations
that pair up in the two blocks give `g₁·g₄ = g₂·g₃` after cancelling `m²`. -/
private theorem mul_cancel_four {g₁ g₂ g₃ g₄ n₂ n₃ r₂ r₃ m : ℝ≥0∞}
    (hm0 : m ≠ 0) (hmt : m ≠ ∞)
    (e₁ : g₁ * m = n₃ * r₂) (e₂ : g₂ * m = n₂ * r₂)
    (e₃ : g₃ * m = n₃ * r₃) (e₄ : g₄ * m = n₂ * r₃) :
    g₁ * g₄ = g₂ * g₃ := by
  refine (ENNReal.mul_left_inj hm0 hmt).mp ((ENNReal.mul_left_inj hm0 hmt).mp ?_)
  calc g₁ * g₄ * m * m = g₁ * m * (g₄ * m) := by ring
    _ = n₃ * r₂ * (n₂ * r₃) := by rw [e₁, e₄]
    _ = g₂ * m * (g₃ * m) := by rw [e₂, e₃]; ring
    _ = g₂ * g₃ * m * m := by ring

/-- The chaining step of (C5): the two four-point identities, one per premise, compose into the
one that exhibits the conditional mass as a function of the second block alone. -/
private theorem mul_cancel_chain {g₁ g₂ g₃ g₄ g₅ g₆ : ℝ≥0∞}
    (h30 : g₃ ≠ 0) (h3t : g₃ ≠ ∞) (h40 : g₄ ≠ 0) (h4t : g₄ ≠ ∞)
    (hα : g₁ * g₄ = g₂ * g₃) (hβ : g₃ * g₆ = g₄ * g₅) :
    g₁ * g₆ = g₂ * g₅ := by
  refine (ENNReal.mul_left_inj h30 h3t).mp ((ENNReal.mul_left_inj h40 h4t).mp ?_)
  calc g₁ * g₆ * g₃ * g₄ = g₁ * g₄ * (g₃ * g₆) := by ring
    _ = g₂ * g₃ * (g₄ * g₅) := by rw [hα, hβ]
    _ = g₂ * g₅ * g₃ * g₄ := by ring

/-- **The four-point identity.** Take four configurations that agree on the conditioning block
`C`, pair up on `A` (`x₁ ~ x₃`, `x₂ ~ x₄`) and pair up the other way on `B` (`x₁ ~ x₂`,
`x₃ ~ x₄`). Evaluating (3.2) at each of them and cancelling `p_C²` — this is where strict
positivity is spent — gives a *multiplicative* four-point relation on the joint marginal, free
of the two conditional factors. Running it once per premise of (C5) is Lauritzen's argument
that the conditional mass of `A` given the rest does not in fact depend on `B` or `D`. -/
private theorem condIndepMass_four_point {p : (V → α) → ℝ≥0∞} {A B C : Finset V}
    (hp : ∀ y, p y ≠ ∞) (hpos : ∀ y, p y ≠ 0) (hci : CondIndepMass p A B C)
    {x₁ x₂ x₃ x₄ : V → α}
    (hC₂ : ∀ i ∈ C, x₁ i = x₂ i) (hC₃ : ∀ i ∈ C, x₁ i = x₃ i) (hC₄ : ∀ i ∈ C, x₁ i = x₄ i)
    (hA₁₃ : ∀ i ∈ A, x₁ i = x₃ i) (hA₂₄ : ∀ i ∈ A, x₂ i = x₄ i)
    (hB₁₂ : ∀ i ∈ B, x₁ i = x₂ i) (hB₃₄ : ∀ i ∈ B, x₃ i = x₄ i) :
    blockMarginal (A ∪ B ∪ C) p x₁ * blockMarginal (A ∪ B ∪ C) p x₄
      = blockMarginal (A ∪ B ∪ C) p x₂ * blockMarginal (A ∪ B ∪ C) p x₃ := by
  have dep : ∀ (E : Finset V) (y z : V → α), (∀ i ∈ E, y i = z i) →
      blockMarginal E p y = blockMarginal E p z :=
    fun E y z hyz => dependsOn_blockMarginal E p fun i hi => hyz i (by simpa using hi)
  have depU : ∀ (E F : Finset V) (y z : V → α), (∀ i ∈ E, y i = z i) → (∀ i ∈ F, y i = z i) →
      blockMarginal (E ∪ F) p y = blockMarginal (E ∪ F) p z := by
    intro E F y z hE hF
    refine dep (E ∪ F) y z fun i hi => ?_
    rcases Finset.mem_union.mp hi with h | h
    · exact hE i h
    · exact hF i h
  have e₁ := hci x₁
  have e₂ := hci x₂
  have e₃ := hci x₃
  have e₄ := hci x₄
  rw [← dep C x₁ x₂ hC₂] at e₂
  rw [← dep C x₁ x₃ hC₃] at e₃
  rw [← dep C x₁ x₄ hC₄] at e₄
  rw [depU A C x₁ x₃ hA₁₃ hC₃, depU B C x₁ x₂ hB₁₂ hC₂] at e₁
  rw [← depU A C x₂ x₄ hA₂₄ fun i hi => (hC₂ i hi).symm.trans (hC₄ i hi),
    ← depU B C x₃ x₄ hB₃₄ fun i hi => (hC₃ i hi).symm.trans (hC₄ i hi)] at e₄
  exact mul_cancel_four (blockMarginal_ne_zero C x₁ hpos) (blockMarginal_ne_top C x₁ hp)
    e₁ e₂ e₃ e₄

/-- **(C5), intersection, under strict positivity** — Lauritzen **Proposition 3.1**, p. 29.

*Hypotheses.* Finiteness, strict positivity, and the book's full pairwise-disjointness
convention on the four blocks. Positivity is **not** removable: Lauritzen's counterexample on
p. 30 takes `X = Y = Z` uniform on `{0, 1}`, where both premises hold and the conclusion fails.
Continuity, the book's other hypothesis, is vacuous here — Lauritzen notes on p. 28 that every
function on a discrete space is continuous.

Under `hpos` every marginal lies in `(0, ∞)`, so both premises may be solved for the
conditional masses; the first exhibits `p_{A∪B∪C∪D}` as a product of a factor free of `x_D` and
one free of `x_A`, the second as a product of a factor free of `x_B` and one free of `x_A`, and
combining them gives a factorisation `h(x_{A∪C}) · k(x_{B∪D∪C})`, which is the criterion
(3.6). -/
theorem CondIndepMass.intersection {p : (V → α) → ℝ≥0∞} {A B C D : Finset V}
    -- LEAN-ONLY: finiteness of the mass function; see `CondIndepMass.weakUnion`
    (hp : ∀ y, p y ≠ ∞)
    -- USER-INPUT: strict positivity of the mass function — the hypothesis of Lauritzen
    -- Proposition 3.1, p. 29; (C5) is false without it (his counterexample, p. 30)
    (hpos : ∀ y, p y ≠ 0)
    -- USER-INPUT: the book's disjointness convention on the four blocks; Lauritzen §3.1
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (hCD : Disjoint C D)
    -- USER-INPUT: `X ⫫ Y ∣ (Z, W)`; Lauritzen §3.1 (C5), p. 30
    (h₁ : CondIndepMass p A B (C ∪ D))
    -- USER-INPUT: `X ⫫ W ∣ (Z, Y)`; Lauritzen §3.1 (C5), p. 30
    (h₂ : CondIndepMass p A D (C ∪ B)) :
    CondIndepMass p A (B ∪ D) C := by
  classical
  -- With no configuration at all there is nothing to prove; otherwise fix a reference one.
  rcases isEmpty_or_nonempty (V → α) with hE | hne
  · exact fun x => (hE.false x).elim
  obtain ⟨x₀⟩ := hne
  -- The joint block, as each premise spells it.
  have hW₁ : A ∪ B ∪ (C ∪ D) = A ∪ (B ∪ D) ∪ C := by
    ext v; simp only [Finset.mem_union]; tauto
  have hW₂ : A ∪ D ∪ (C ∪ B) = A ∪ (B ∪ D) ∪ C := by
    ext v; simp only [Finset.mem_union]; tauto
  have hg0 : ∀ z : V → α, blockMarginal (A ∪ (B ∪ D) ∪ C) p z ≠ 0 :=
    fun z => blockMarginal_ne_zero _ z hpos
  have hgt : ∀ z : V → α, blockMarginal (A ∪ (B ∪ D) ∪ C) p z ≠ ∞ :=
    fun z => blockMarginal_ne_top _ z hp
  -- Membership facts used to evaluate `substOn`.
  have hCD' : ∀ i ∈ C, i ∉ D := fun i hi => Finset.disjoint_left.mp hCD hi
  have hBD' : ∀ i ∈ B, i ∉ D := fun i hi => Finset.disjoint_left.mp hBD hi
  have hAD' : ∀ i ∈ A, i ∉ D := fun i hi => Finset.disjoint_left.mp hAD hi
  have hCB' : ∀ i ∈ C, i ∉ B := fun i hi => Finset.disjoint_right.mp hBC hi
  have hAB' : ∀ i ∈ A, i ∉ B := fun i hi => Finset.disjoint_left.mp hAB hi
  refine condIndepMass_of_factorization
    (Finset.disjoint_union_right.mpr ⟨hAB, hAD⟩) hAC
    (Finset.disjoint_union_left.mpr ⟨hBC, hCD.symm⟩)
    (h := fun z => blockMarginal (A ∪ (B ∪ D) ∪ C) p (substOn x₀ (B ∪ D) z))
    (k := fun z => blockMarginal (A ∪ (B ∪ D) ∪ C) p z /
      blockMarginal (A ∪ (B ∪ D) ∪ C) p (substOn x₀ (B ∪ D) z)) ?_ ?_ ?_
  · -- The first factor sees only `A ∪ C`: outside `B ∪ D` it is the reference configuration.
    intro y z hyz
    refine dependsOn_blockMarginal _ p fun i hi => ?_
    by_cases hiBD : i ∈ B ∪ D
    · rw [substOn_of_mem hiBD, substOn_of_mem hiBD]
    · rw [substOn_of_notMem hiBD, substOn_of_notMem hiBD]
      refine hyz i ?_
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hi ⊢
      simp only [Finset.mem_union, not_or] at hiBD
      tauto
  · -- The second factor sees only `(B ∪ D) ∪ C`: Lauritzen's argument, run through the
    -- four-point identity once per premise.
    intro x y hxy
    have hmem : ∀ i : V, i ∈ B ∨ i ∈ D ∨ i ∈ C → x i = y i := by
      intro i hi
      refine hxy i ?_
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      tauto
    have hxyB : ∀ i ∈ B, x i = y i := fun i hi => hmem i (Or.inl hi)
    have hxyD : ∀ i ∈ D, x i = y i := fun i hi => hmem i (Or.inr (Or.inl hi))
    have hxyC : ∀ i ∈ C, x i = y i := fun i hi => hmem i (Or.inr (Or.inr hi))
    -- (α) from `h₂`: swap the `A`-block against the `D`-block, at fixed `B`, `C`.
    have hα := condIndepMass_four_point (A := A) (B := D) (C := C ∪ B) hp hpos h₂
      (x₁ := x) (x₂ := y) (x₃ := substOn x₀ D x) (x₄ := substOn x₀ D y)
      (fun i hi => by
        rcases Finset.mem_union.mp hi with h | h
        · exact hxyC i h
        · exact hxyB i h)
      (fun i hi => by
        rcases Finset.mem_union.mp hi with h | h
        · rw [substOn_of_notMem (hCD' i h)]
        · rw [substOn_of_notMem (hBD' i h)])
      (fun i hi => by
        rcases Finset.mem_union.mp hi with h | h
        · rw [substOn_of_notMem (hCD' i h)]; exact hxyC i h
        · rw [substOn_of_notMem (hBD' i h)]; exact hxyB i h)
      (fun i hi => by rw [substOn_of_notMem (hAD' i hi)])
      (fun i hi => by rw [substOn_of_notMem (hAD' i hi)])
      hxyD
      (fun i hi => by rw [substOn_of_mem hi, substOn_of_mem hi])
    rw [hW₂] at hα
    -- (β) from `h₁`: swap the `A`-block against the `B`-block, at fixed `C`, `D`.
    have hβ := condIndepMass_four_point (A := A) (B := B) (C := C ∪ D) hp hpos h₁
      (x₁ := substOn x₀ D x) (x₂ := substOn x₀ D y)
      (x₃ := substOn x₀ (B ∪ D) x) (x₄ := substOn x₀ (B ∪ D) y)
      (fun i hi => by
        rcases Finset.mem_union.mp hi with h | h
        · rw [substOn_of_notMem (hCD' i h), substOn_of_notMem (hCD' i h)]; exact hxyC i h
        · rw [substOn_of_mem h, substOn_of_mem h])
      (fun i hi => by
        rcases Finset.mem_union.mp hi with h | h
        · rw [substOn_of_notMem (hCD' i h),
            substOn_of_notMem (by simp [Finset.mem_union, hCB' i h, hCD' i h])]
        · rw [substOn_of_mem h, substOn_of_mem (Finset.mem_union_right B h)])
      (fun i hi => by
        rcases Finset.mem_union.mp hi with h | h
        · rw [substOn_of_notMem (hCD' i h),
            substOn_of_notMem (by simp [Finset.mem_union, hCB' i h, hCD' i h])]
          exact hxyC i h
        · rw [substOn_of_mem h, substOn_of_mem (Finset.mem_union_right B h)])
      (fun i hi => by
        rw [substOn_of_notMem (hAD' i hi),
          substOn_of_notMem (by simp [Finset.mem_union, hAB' i hi, hAD' i hi])])
      (fun i hi => by
        rw [substOn_of_notMem (hAD' i hi),
          substOn_of_notMem (by simp [Finset.mem_union, hAB' i hi, hAD' i hi])])
      (fun i hi => by
        rw [substOn_of_notMem (hBD' i hi), substOn_of_notMem (hBD' i hi)]; exact hxyB i hi)
      (fun i hi => by
        rw [substOn_of_mem (Finset.mem_union_left D hi),
          substOn_of_mem (Finset.mem_union_left D hi)])
    rw [hW₁] at hβ
    have key := mul_cancel_chain (hg0 _) (hgt _) (hg0 _) (hgt _) hα hβ
    exact (ENNReal.div_eq_div_iff (hg0 _) (hgt _) (hg0 _) (hgt _)).mpr
      ((mul_comm _ _).trans (key.trans (mul_comm _ _)))
  · intro x
    exact (ENNReal.mul_div_cancel (hg0 _) (hgt _)).symm

/-! ### The graphoid instances -/

/-- **The headline of the file.** Every finite discrete mass function satisfies Lauritzen's
(C1)–(C4), so `CondIndepMass p` is a semi-graphoid and the abstract Markov hierarchy of
`Undirected/Markov.lean` — (G) ⇒ (L) ⇒ (P), Lauritzen Proposition 3.4 — instantiates at it
without further work.

The structure's disjointness hypotheses are strictly more than the four identities need, and
are simply discarded. Only `hp` is needed, and only by (C3) and (C4). -/
theorem isSemigraphoid_condIndepMass {p : (V → α) → ℝ≥0∞}
    -- LEAN-ONLY: finiteness of the mass function; needed by (C3) and (C4) only, and vacuous
    -- for Lauritzen, whose `f` is a density
    (hp : ∀ y, p y ≠ ∞) :
    IsSemigraphoid (CondIndepMass p) := by
  exact ⟨fun _ _ _ h => h.symm,
    fun _ _ hAD _ _ h => CondIndepMass.decomposition hAD h,
    fun hAB _ _ _ _ _ h => CondIndepMass.weakUnion hp hAB h,
    fun _ _ _ _ _ _ h₁ h₂ => CondIndepMass.contraction hp h₁ h₂⟩

/-- **Lauritzen Proposition 3.1**, p. 29: a strictly positive (and, on a discrete space,
automatically continuous — Lauritzen p. 28) mass function satisfies (C5) as well, hence is a
**graphoid**. This is what makes Theorem 3.7 (Pearl–Paz, `pairwiseMarkov_implies_globalMarkov`)
available for strictly positive discrete models, and it is the calculus half of
Hammersley–Clifford. -/
theorem isGraphoid_condIndepMass_of_pos {p : (V → α) → ℝ≥0∞}
    -- LEAN-ONLY: finiteness of the mass function; see `isSemigraphoid_condIndepMass`
    (hp : ∀ y, p y ≠ ∞)
    -- USER-INPUT: strict positivity — the hypothesis of Lauritzen Proposition 3.1, p. 29
    (hpos : ∀ y, p y ≠ 0) :
    IsGraphoid (CondIndepMass p) := by
  exact ⟨isSemigraphoid_condIndepMass hp,
    fun hAB hAC hAD hBC hBD hCD h₁ h₂ =>
      CondIndepMass.intersection hp hpos hAB hAC hAD hBC hBD hCD h₁ h₂⟩

/-! ### The factorisation criterion (3.6) -/

/-- **Lauritzen eq. (3.6) ⇒ (3.2)**, p. 29: if the joint marginal on `A ∪ B ∪ C` factors as
`h(x_{A∪C}) · k(x_{B∪C})`, then `X_A ⫫ X_B ∣ X_C`.

Stated separately from the equivalence below because this half needs **neither finiteness nor
positivity**: summing the factorisation over `A`, over `B`, and over `A ∪ B` gives
`p_{B∪C} = H·k`, `p_{A∪C} = h·K` and `p_C = H·K`, whence both sides of (3.2) equal
`h·k·H·K` by commutativity alone. -/
theorem condIndepMass_of_exists_factorization {p : (V → α) → ℝ≥0∞} {A B C : Finset V}
    -- USER-INPUT: the book's disjointness convention on the triple; Lauritzen §3.1
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {h k : (V → α) → ℝ≥0∞}
    -- USER-INPUT: the first factor depends only on `(x_A, x_C)`; Lauritzen eq. (3.6), p. 29
    (hh : DependsOn h ((A ∪ C : Finset V) : Set V))
    -- USER-INPUT: the second factor depends only on `(x_B, x_C)`; Lauritzen eq. (3.6), p. 29
    (hk : DependsOn k ((B ∪ C : Finset V) : Set V))
    -- USER-INPUT: the factorisation itself; Lauritzen eq. (3.6), p. 29
    (hfac : ∀ x, blockMarginal (A ∪ B ∪ C) p x = h x * k x) :
    CondIndepMass p A B C :=
  condIndepMass_of_factorization hAB hAC hBC hh hk hfac

/-- **Lauritzen eq. (3.6)**, p. 29, as an equivalence: for a finite mass function,
`X_A ⫫ X_B ∣ X_C` holds **iff** the joint marginal factors as `h(x_{A∪C}) · k(x_{B∪C})`.

The `mpr` half needs no side conditions. The `mp` half takes `h := p_{A∪C}` and
`k := p_{B∪C} / p_C`, whose dependence on `(x_B, x_C)` is that of the two marginals (the
denominator's block `C` sits inside `B ∪ C`); finiteness is what makes
`p_{A∪C} · (p_{B∪C} / p_C) = p_{A∪B∪C}` on `{p_C ≠ 0}`, and on `{p_C = 0}` both sides vanish —
note that in `ℝ≥0∞` the junk value `0 / 0 = 0` makes that branch work without a case split in
the formula itself. -/
theorem condIndepMass_iff_exists_factorization {p : (V → α) → ℝ≥0∞} {A B C : Finset V}
    -- LEAN-ONLY: finiteness of the mass function, used only by the forward direction, where a
    -- division by `p_C` must be undone; Lauritzen's `f` is a density
    (hp : ∀ y, p y ≠ ∞)
    -- USER-INPUT: the book's disjointness convention on the triple; Lauritzen §3.1
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    CondIndepMass p A B C ↔
      ∃ h k : (V → α) → ℝ≥0∞, DependsOn h ((A ∪ C : Finset V) : Set V) ∧
        DependsOn k ((B ∪ C : Finset V) : Set V) ∧
        ∀ x, blockMarginal (A ∪ B ∪ C) p x = h x * k x := by
  constructor
  · intro hci
    refine ⟨blockMarginal (A ∪ C) p,
      fun x => blockMarginal (B ∪ C) p x / blockMarginal C p x,
      dependsOn_blockMarginal (A ∪ C) p, ?_, ?_⟩
    · -- numerator on `B ∪ C`, denominator on `C ⊆ B ∪ C`
      intro y z hyz
      change blockMarginal (B ∪ C) p y / blockMarginal C p y
        = blockMarginal (B ∪ C) p z / blockMarginal C p z
      rw [dependsOn_blockMarginal (B ∪ C) p hyz,
        dependsOn_blockMarginal C p (fun i hi => hyz i (by
          simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hi ⊢; tauto))]
    · intro x
      change blockMarginal (A ∪ B ∪ C) p x
        = blockMarginal (A ∪ C) p x * (blockMarginal (B ∪ C) p x / blockMarginal C p x)
      by_cases hz : blockMarginal C p x = 0
      · have z1 : blockMarginal (A ∪ B ∪ C) p x = 0 :=
          blockMarginal_eq_zero_of_subset p x Finset.subset_union_right hz
        have z2 : blockMarginal (B ∪ C) p x = 0 :=
          blockMarginal_eq_zero_of_subset p x Finset.subset_union_right hz
        rw [z1, z2, hz]
        simp
      · rw [← mul_div_assoc, ← hci x,
          ENNReal.mul_div_cancel_right hz (blockMarginal_ne_top _ _ hp)]
  · rintro ⟨h, k, hh, hk, hfac⟩
    exact condIndepMass_of_factorization hAB hAC hBC hh hk hfac

/-! ### Bridge to the general conditional-independence predicate -/

/-- **Bridge: `CondIndepCoords ⇒ CondIndepMass`.** If the random vector `X` satisfies the
measure-theoretic conditional independence `X_A ⫫ X_B ∣ X_C` of `Core/Coordinates.lean`, then
its mass function `p x = μ (X ⁻¹' {x})` satisfies Lauritzen's identity (3.2).

Evaluate the disintegration identity
`μ.map (X_C, (X_A, X_B)) = (μ.map X_C) ⊗ₘ (κ ×ₖ η)` at the singleton `(x_C, (x_A, x_B))`,
obtaining `p_{A∪B∪C}(x) = p_C(x) · κ(x_C){x_A} · η(x_C){x_B}`. Summing over the `B`-block and
using `IsMarkovKernel η` gives `p_{A∪C} = p_C · κ(x_C){x_A}`, and symmetrically for `p_{B∪C}`;
multiplying the two recovers (3.2). No disjointness of the blocks is used: agreement on
`A ∪ B ∪ C` is agreement on each of `A`, `B`, `C` whether or not they overlap.

**The converse direction is deliberately not stated here.** It is true, but it is a
*construction* rather than an identity: the witnessing kernels are the normalised conditional
masses `κ(z){a} = p_{A∪C}/p_C`, which need a junk fallback on the null set `{p_C = 0}` (hence a
`[Nonempty α]` hypothesis) and a `Kernel` packaging with its measurability proof. It belongs
with the discrete-kernel machinery, not with the mass algebra. -/
theorem condIndepMass_of_condIndepCoords {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    -- LEAN-ONLY: singletons of `α` must be measurable for the singleton evaluation above to be
    -- meaningful; on Lauritzen's finite state space this is automatic
    [MeasurableSingletonClass α]
    {μ : Measure Ω}
    -- LEAN-ONLY: `⊗ₘ` degenerates to `0` without an `SFinite` outer measure, so the
    -- disintegration identity is only informative for a finite `μ`
    [IsFiniteMeasure μ] {X : Ω → V → α}
    -- LEAN-ONLY: measurability of the random vector, needed to identify the pushforward of `μ`
    -- with the mass function; part of "random variable" for Lauritzen
    (hX : Measurable X) (A B C : Finset V)
    -- USER-INPUT: conditional independence of the coordinate blocks; Lauritzen §3.1, p. 28
    (hci : CondIndepCoords μ X A B C) :
    CondIndepMass (fun x => μ (X ⁻¹' {x})) A B C := by
  classical
  obtain ⟨κ, η, _, _, hdis⟩ := hci
  haveI : IsFiniteMeasure (μ.map (coords C X)) :=
    Measure.isFiniteMeasure_map μ (coords C X)
  intro x
  -- The mass of a `Finset` of configurations is the measure of the corresponding fibre.
  have hsum : ∀ F : Finset (V → α), ∑ y ∈ F, μ (X ⁻¹' {y}) = μ (X ⁻¹' (F : Set (V → α))) := by
    intro F
    have hunion : X ⁻¹' (F : Set (V → α)) = ⋃ y ∈ F, X ⁻¹' {y} := by ext ω; simp
    rw [hunion]
    exact (measure_biUnion_finset
      (fun y _ z _ hyz => Disjoint.preimage X (Set.disjoint_singleton.mpr hyz))
      (fun y _ => hX (measurableSet_singleton y))).symm
  have hbm : ∀ E : Finset V,
      blockMarginal E (fun y => μ (X ⁻¹' {y})) x = μ {ω | ∀ i ∈ E, X ω i = x i} := by
    intro E
    rw [blockMarginal, hsum]
    congr 1
    ext ω
    simp [agreeOn]
  -- Agreement on a block is equality of the corresponding subvector.
  have hres : ∀ (E : Finset V) (y : V → α),
      E.restrict y = E.restrict x ↔ ∀ i ∈ E, y i = x i :=
    fun E y => ⟨fun h i hi => congrFun h ⟨i, hi⟩, fun h => funext fun i => h i i.2⟩
  have hT : Measurable fun ω => (coords C X ω, (coords A X ω, coords B X ω)) :=
    (measurable_coords C hX).prodMk ((measurable_coords A hX).prodMk (measurable_coords B hX))
  -- **The rectangle computation.** Evaluate the disintegration identity at
  -- `{x_C} ×ˢ (s ×ˢ t)`: `compProd_apply_prod` turns it into an integral over a singleton,
  -- `lintegral_singleton` evaluates that, and `Kernel.prod_apply_prod` splits the kernel.
  have key : ∀ (s : Set (↥A → α)) (t : Set (↥B → α)) (E : Finset V), MeasurableSet s →
      MeasurableSet t →
      (∀ ω : Ω, (∀ i ∈ E, X ω i = x i) ↔
        (C.restrict (X ω) = C.restrict x ∧ A.restrict (X ω) ∈ s ∧ B.restrict (X ω) ∈ t)) →
      blockMarginal E (fun y => μ (X ⁻¹' {y})) x
        = κ (C.restrict x) s * η (C.restrict x) t * (μ.map (coords C X)) {C.restrict x} := by
    intro s t E hs ht hiff
    have hEq : {ω | ∀ i ∈ E, X ω i = x i}
        = (fun ω => (coords C X ω, (coords A X ω, coords B X ω))) ⁻¹'
          (({C.restrict x} : Set (↥C → α)) ×ˢ (s ×ˢ t)) := by
      ext ω
      simpa only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
        and_assoc] using! hiff ω
    rw [hbm E, hEq, ← Measure.map_apply hT ((measurableSet_singleton _).prod (hs.prod ht)),
      hdis, Measure.compProd_apply_prod (measurableSet_singleton _) (hs.prod ht),
      lintegral_singleton, Kernel.prod_apply_prod]
  -- The four blocks, as four rectangles.
  have hABC := key {A.restrict x} {B.restrict x} (A ∪ B ∪ C) (measurableSet_singleton _)
    (measurableSet_singleton _) (fun ω => by
      simp only [Set.mem_singleton_iff, hres, Finset.mem_union]
      constructor
      · exact fun h => ⟨fun i hi => h i (Or.inr hi), fun i hi => h i (Or.inl (Or.inl hi)),
          fun i hi => h i (Or.inl (Or.inr hi))⟩
      · rintro ⟨hC, hA, hB⟩ i ((hi | hi) | hi)
        exacts [hA i hi, hB i hi, hC i hi])
  have hAC := key {A.restrict x} Set.univ (A ∪ C) (measurableSet_singleton _)
    MeasurableSet.univ (fun ω => by
      simp only [Set.mem_singleton_iff, Set.mem_univ, and_true, hres, Finset.mem_union]
      constructor
      · exact fun h => ⟨fun i hi => h i (Or.inr hi), fun i hi => h i (Or.inl hi)⟩
      · rintro ⟨hC, hA⟩ i (hi | hi)
        exacts [hA i hi, hC i hi])
  have hBC := key Set.univ {B.restrict x} (B ∪ C) MeasurableSet.univ
    (measurableSet_singleton _) (fun ω => by
      simp only [Set.mem_singleton_iff, Set.mem_univ, true_and, hres, Finset.mem_union]
      constructor
      · exact fun h => ⟨fun i hi => h i (Or.inr hi), fun i hi => h i (Or.inl hi)⟩
      · rintro ⟨hC, hB⟩ i (hi | hi)
        exacts [hB i hi, hC i hi])
  have hC := key Set.univ Set.univ C MeasurableSet.univ MeasurableSet.univ (fun ω => by
    simp only [Set.mem_univ, and_true, hres])
  -- Both sides are `κ{x_A} · η{x_B} · κ(univ) · η(univ) · p_C²`; no Markov property is needed.
  rw [hABC, hAC, hBC, hC]
  ring

end StatLean.StatisticalModels.GraphicalModels
