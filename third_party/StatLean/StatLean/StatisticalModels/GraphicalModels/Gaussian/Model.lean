module
public import StatLean.StatisticalModels.GraphicalModels.Gaussian.Regression
public import StatLean.StatisticalModels.GraphicalModels.Gaussian.PartialCorrelation
public import StatLean.StatisticalModels.GraphicalModels.Undirected.Markov
public import StatLean.StatisticalModels.Constraint.Defs

@[expose] public section

/-!
# Covariance selection models — the Gaussian graphical model

Lauritzen §5.2, p. 131: "the Gaussian graphical model or covariance selection model for `Y` with
graph `G` is given by assuming that `Y` follows a multivariate normal distribution which obeys
the undirected pairwise Markov property with respect to `G`. Since the density is positive and
continuous, this implies the global and local Markov properties and the density factorizes. It
follows from Proposition 5.2 that this is equivalent to assuming the quadratic interactions
`k_{γμ}` to be equal to zero for all pairs `γ, μ` which are not adjacent in `G`."

And its compact form, p. 132: let `S⁺(G)` be the set of positive definite symmetric matrices `A`
with `a_{γμ} = 0` whenever `γ ≠ μ` are non-adjacent; then the model is
`Y ∼ N_{|Γ|}(ξ, Σ)` with `Σ⁻¹ ∈ S⁺(G)`.

* `concentrationSet G` — Lauritzen's `S⁺(G)`;
* `gaussianGraphicalModel G` — the **family of laws** `{N(m, Σ) : Σ⁻¹ ∈ S⁺(G)}`, transcribed
  verbatim from the p. 132 compact form; viewed as the fiber map of a
  `StatisticalModels.Constraint` model indexed by `Θ := SimpleGraph ι`;
* `fibersNonempty_gaussianGraphicalModel`, `fibersProbability_gaussianGraphicalModel`,
  `gaussianGraphicalModel_mono` — the constraint-model hygiene;
* `gaussianGraphicalModelExact` + `separatesTarget_gaussianGraphicalModelExact` — the *saturated*
  fibers, for which the graph **is** identified (`SeparatesTarget`); see the note below on why
  the book's own model does not separate its graph;
* **`isPairwiseMarkov_of_mem_gaussianGraphicalModel` (HEADLINE)** — a law in the model satisfies
  `Undirected.Markov.IsPairwiseMarkov G` for the relation `CondIndepCoords P gaussianCoords`;
* `multivariateGaussian_mem_gaussianGraphicalModel_iff_pairwise` — and conversely, so that
  Lauritzen's *definition* (pairwise Markov) and the p. 132 *parametrisation* (zeros of `K`) are
  one and the same model;
* **`isGraphoid_condIndepCoords_multivariateGaussian`** — Lauritzen **Proposition 3.1 at the
  Gaussian**: the density is positive and continuous, so the conditional-independence relation of
  a regular normal is a **graphoid**, i.e. an instance of `Core.Semigraphoid.IsGraphoid`. This is
  the Gaussian's contribution to the abstraction, and it is what turns pairwise into local and
  global through `Undirected.Markov`;
* `condIndepCoords_weakUnion_of_disjoint`, `condIndepCoords_contraction_of_disjoint`,
  `condIndepCoords_intersection_of_disjoint` — the three named sub-lemmas that instance needs
  ((C3), (C4), (C5)); symmetry and decomposition hold for the coordinate relation in general;
* `isGlobalMarkov_of_mem_gaussianGraphicalModel` — `IsGlobalMarkov`, i.e. (G), obtained from the
  graphoid instance through Theorem 3.7 on nonempty blocks, plus
  `CondIndepCoords.of_isEmpty_left` for the degenerate blocks Theorem 3.7 provably cannot reach;
* `isLocalMarkov_of_mem_gaussianGraphicalModel` — `IsLocalMarkov`, i.e. (L)
  `Y_γ ⫫ Y_{Γ∖cl(γ)} ∣ Y_{bd(γ)}`, obtained from (G) by pure graph separation. It is stated
  *after* (G) because that is the direction of the dependency: `IsGlobalMarkov ⇒ IsLocalMarkov`.

## Note: `SeparatesTarget` and why the book's model does not identify its graph

`gaussianGraphicalModel` is monotone in `G` (a zero constraint is a *restriction*), so
`gaussianGraphicalModel G ⊆ gaussianGraphicalModel H` whenever `G ≤ H`, and in particular every
model is contained in the saturated one. Hence `SeparatesTarget gaussianGraphicalModel id` is
**false** for `|Γ| ≥ 2` and is deliberately not stated. What *is* true — and is the
identifiability content of covariance selection — is that the *exact* zero pattern determines the
graph: `SeparatesTarget gaussianGraphicalModelExact id`. This is the honest reading of "the
conditional independence graph of a regular Gaussian is identified from its law".

## Note: why `IsGraphoid`'s disjointness hypotheses are constitutive, not bureaucracy

`Core.Semigraphoid`'s axiom fields each carry pairwise disjointness of the blocks occurring in
them, matching Lauritzen, who states (C1)–(C5) for *disjoint* subsets. That is not a stylistic
choice, and the Gaussian is the witness: **without** the disjointness the structure is
unsatisfiable here. Take `B = D` and `C = ∅` in the intersection field; the disjointness-free
version would read `ci A B B → ci A B B → ci A B ∅`, whose premises hold trivially (conditioning
on `X_B` makes `X_B` degenerate) while the conclusion asserts *unconditional* independence of
`X_A` and `X_B` — false for any regular Gaussian with a nonzero covariance entry. The amended
field blocks this: `Disjoint B D` at `B = D` forces `B = D = ∅`, and `ci A ∅ ∅` is harmless. So
`isGraphoid_condIndepCoords_multivariateGaussian` below is stateable exactly because the
disjointness is part of the axioms — the counterexample is the reason it must stay there.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996 (first edition)**: §5.2 "Covariance selection models", pp. 131–132
(the definition, the equivalence with zero concentration entries via Proposition 5.2, and the
compact description `Σ⁻¹ ∈ S⁺(G)`); Proposition 3.1, p. 29 (a strictly positive continuous joint
density satisfies (C5)); §3.2, p. 32 — the pairwise (P), local (L) and global (G) Markov
properties, all three **unnumbered** definitions; and Proposition 3.4 / Theorem 3.7, pp. 33–35
(the hierarchy, and its collapse for a positive density) (`Lauritzen §5.2`, `Lauritzen §3.1`,
`Lauritzen §3.2`). Page numbers and item kinds follow `notes/factor_graphical/books.md`.

**Proof formalization notes.**

*Book vs Lean, symmetry.* Lauritzen's `S(G)` requires the matrices to be symmetric and `S⁺(G)`
additionally positive definite. Over `ℝ`, `Matrix.PosDef` already carries
`Matrix.IsHermitian`, which is symmetry (`Matrix.conjTranspose_eq_transpose_of_trivial`), so
`concentrationSet` states positive definiteness plus the zero pattern and the symmetry is
inherited — not dropped.

*Book vs Lean, the graph.* `SimpleGraph ι` is irreflexive and symmetric, matching Lauritzen's
undirected `G = (Γ, E)`; the zero constraint is quantified over `γ ≠ μ` so the diagonal — where
`k_{γγ} > 0` always — is untouched, exactly as in the book ("for all pairs `γ, μ` which are not
adjacent").

*Disjointness in the Markov properties.* The three `Disjoint` hypotheses that `IsGlobalMarkov`
carries are part of its definition, so its Gaussian instance takes no `Disjoint` arguments of its
own.

*Landing on the nose.* `IsPairwiseMarkov` conditions on `Finset.univ \ {i, j}`, so Proposition
5.2 is stated with that same expression rather than `({i, j} : Finset ι)ᶜ`; the instantiation is
then syntactic, with no `Finset.compl_eq_univ_sdiff` rewriting in between.

**Bibliographic comments.** Covariance selection is A. P. Dempster's, "Covariance selection,"
*Biometrics* **28** (1972), 157–175 — the name, the model class `S⁺(G)` and the maximum
likelihood theory. The Markov-property hierarchy for undirected graphs and its collapse under a
positive density is J. N. Darroch, S. L. Lauritzen and T. P. Speed, "Markov fields and log-linear
interaction models for contingency tables," *Ann. Statist.* **8** (1980), 522–539, and
J. M. Hammersley and P. Clifford's unpublished 1971 manuscript; the graphoid axiomatics is
J. Pearl's, *Probabilistic Reasoning in Intelligent Systems*, Morgan Kaufmann, 1988.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.GraphicalModels

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section ConcentrationSet

/-- **Lauritzen's `S⁺(G)`** (§5.2, p. 132): the positive definite matrices whose off-diagonal
entries vanish at every non-edge of `G`.

The book asks for `S(G)` to consist of *symmetric* matrices and takes `S⁺(G)` to be its positive
definite elements; over `ℝ`, `Matrix.PosDef` already includes `Matrix.IsHermitian`, which is
symmetry, so nothing is dropped. The constraint is quantified over `γ ≠ μ`, leaving the diagonal
free — as in the book.

Edge behaviour: for the complete graph this is all of the positive definite cone (the saturated
model); for the empty graph it is the diagonal positive definite matrices. -/
def concentrationSet (G : SimpleGraph ι) : Set (Matrix ι ι ℝ) :=
  {A | A.PosDef ∧ ∀ i j, i ≠ j → ¬ G.Adj i j → A i j = 0}

omit [Fintype ι] [DecidableEq ι] in
/-- Adding edges enlarges `S⁺(G)`: fewer zero constraints. -/
theorem concentrationSet_mono {G H : SimpleGraph ι}
    -- USER-INPUT: `G` is a subgraph of `H`; Lauritzen §5.2, p. 132
    (hGH : G ≤ H) :
    concentrationSet G ⊆ concentrationSet H := by
  rintro A ⟨hA, hz⟩
  exact ⟨hA, fun i j hij hH => hz i j hij fun hG => hH (hGH hG)⟩

/-- A regular concentration matrix comes from a regular covariance matrix. -/
theorem posDef_of_precisionMatrix_posDef {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: `Matrix.inv` is junk-valued at singular matrices, so this is the statement that
    -- the junk value `0` is not positive definite; `Matrix.posDef_inv_iff`
    (h : (precisionMatrix S).PosDef) :
    S.PosDef :=
  Matrix.posDef_inv_iff.mp h

end ConcentrationSet

section Model

/-- **The Gaussian graphical model / covariance selection model** with graph `G` (Lauritzen §5.2,
pp. 131–132), in the book's own compact form: `Y ∼ N_{|Γ|}(ξ, Σ)` with `Σ⁻¹ ∈ S⁺(G)`.

This is the fiber of a `StatisticalModels.Constraint` model with parameter space
`Θ := SimpleGraph ι` and sample space `𝓧 := EuclideanSpace ℝ ι`: it is a *set* of laws, one
constraint per graph, not a single law per parameter.

Edge behaviour: the membership condition is stated on `precisionMatrix S`, which forces `S` to be
regular (`posDef_of_precisionMatrix_posDef`), so the junk regimes of both `Matrix.inv` and
`multivariateGaussian` (a Dirac mass off the positive semidefinite cone) are excluded — a Dirac
law is never a member. -/
def gaussianGraphicalModel (G : SimpleGraph ι) : Set (Measure (EuclideanSpace ℝ ι)) :=
  {P | ∃ (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ),
        precisionMatrix S ∈ concentrationSet G ∧ P = multivariateGaussian m S}

/-- Unfolded membership: a law is in the model iff it is a regular Gaussian whose concentration
matrix has the prescribed zeros. -/
theorem mem_gaussianGraphicalModel_iff {G : SimpleGraph ι}
    {P : Measure (EuclideanSpace ℝ ι)} :
    P ∈ gaussianGraphicalModel G
      ↔ ∃ (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ), S.PosDef ∧
          (∀ i j, i ≠ j → ¬ G.Adj i j → precisionMatrix S i j = 0) ∧
          P = multivariateGaussian m S := by
  constructor
  · rintro ⟨m, S, ⟨hK, hz⟩, rfl⟩
    exact ⟨m, S, posDef_of_precisionMatrix_posDef hK, hz, rfl⟩
  · rintro ⟨m, S, hS, hz, rfl⟩
    exact ⟨m, S, ⟨precisionMatrix_posDef hS, hz⟩, rfl⟩

/-- LEAN-ONLY (`private`, file-scope): a regular Gaussian law determines its covariance
parameter — the covariance of `N(m, Σ)` is `Σ`. It is what lets a membership hypothesis stated
for *some* `(m', S')` be transported back to the given `S`. -/
private theorem posDef_eq_of_multivariateGaussian_eq {m m' : EuclideanSpace ℝ ι}
    {S S' : Matrix ι ι ℝ} (hS : S.PosDef) (hS' : S'.PosDef)
    (h : multivariateGaussian m S = multivariateGaussian m' S') : S = S' := by
  have h1 := covMatrix_multivariateGaussian m S hS.posSemidef
  rw [h, covMatrix_multivariateGaussian m' S' hS'.posSemidef] at h1
  exact h1.symm

/-- Membership for an explicitly given regular Gaussian. -/
theorem multivariateGaussian_mem_gaussianGraphicalModel_iff {G : SimpleGraph ι}
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen §5.2, p. 131
    (hS : S.PosDef) :
    multivariateGaussian m S ∈ gaussianGraphicalModel G
      ↔ ∀ i j, i ≠ j → ¬ G.Adj i j → precisionMatrix S i j = 0 := by
  constructor
  · rintro ⟨m', S', ⟨hK', hz'⟩, heq⟩
    rw [posDef_eq_of_multivariateGaussian_eq hS (posDef_of_precisionMatrix_posDef hK') heq]
    exact hz'
  · intro hz
    exact ⟨m, S, ⟨precisionMatrix_posDef hS, hz⟩, rfl⟩

/-- Adding edges enlarges the model — a covariance selection model is a *restriction*. This
monotonicity is why the book's model does not identify its own graph; see the module docstring. -/
theorem gaussianGraphicalModel_mono {G H : SimpleGraph ι}
    -- USER-INPUT: `G` is a subgraph of `H`; Lauritzen §5.2, p. 132
    (hGH : G ≤ H) :
    gaussianGraphicalModel G ⊆ gaussianGraphicalModel H := by
  rintro P ⟨m, S, hK, rfl⟩
  exact ⟨m, S, concentrationSet_mono hGH hK, rfl⟩

/-- Feasibility of the constraint model: every graph admits a compatible law (take `Σ = I`, whose
concentration matrix `I` satisfies every zero constraint). -/
theorem fibersNonempty_gaussianGraphicalModel :
    FibersNonempty (gaussianGraphicalModel (ι := ι)) := by
  intro G
  refine ⟨multivariateGaussian 0 1, 0, 1, ⟨?_, ?_⟩, rfl⟩
  · rw [precisionMatrix_def, inv_one]
    exact Matrix.PosDef.one
  · intro i j hij _
    rw [precisionMatrix_def, inv_one]
    exact Matrix.one_apply_ne hij

/-- Every compatible law is a probability measure. -/
theorem fibersProbability_gaussianGraphicalModel :
    FibersProbability (gaussianGraphicalModel (ι := ι)) := by
  rintro G Q ⟨m, S, -, rfl⟩
  infer_instance

/-- The **saturated** fibers: the laws whose concentration zero pattern is *exactly* the
non-edge set of `G`. Lauritzen's model asks for `⊆`; this asks for `=`.

Edge behaviour: the fibers are pairwise disjoint and each is nonempty, so this is the constraint
model whose parameter — the graph — is identified (`separatesTarget_gaussianGraphicalModelExact`).
It is *not* the book's model class: it is not closed under limits and is not a natural object for
maximum likelihood, which is exactly why Lauritzen states the model with `⊆`. -/
def gaussianGraphicalModelExact (G : SimpleGraph ι) : Set (Measure (EuclideanSpace ℝ ι)) :=
  {P | ∃ (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ), S.PosDef ∧
        (∀ i j, i ≠ j → (precisionMatrix S i j = 0 ↔ ¬ G.Adj i j)) ∧
        P = multivariateGaussian m S}

theorem gaussianGraphicalModelExact_subset (G : SimpleGraph ι) :
    gaussianGraphicalModelExact G ⊆ gaussianGraphicalModel G := by
  rintro P ⟨m, S, hS, hz, rfl⟩
  exact ⟨m, S, ⟨precisionMatrix_posDef hS, fun i j hij hadj => (hz i j hij).mpr hadj⟩, rfl⟩

/-- **The conditional independence graph is identified.** Two graphs whose saturated fibers share
a law are equal: by Proposition 5.2 the law's concentration zero pattern is its set of
conditional independences, and the saturated fiber pins the graph to be exactly that pattern.

Stated with the `Constraint` carrier of `StatisticalModels.Constraint.Defs`, with `Θ` the graphs
and the target `ψ = id`. Compare `gaussianGraphicalModel_mono`: the *book's* model is monotone
and hence does **not** separate its graph. -/
theorem separatesTarget_gaussianGraphicalModelExact :
    SeparatesTarget (gaussianGraphicalModelExact (ι := ι))
      (id : SimpleGraph ι → SimpleGraph ι) := by
  rintro G H ⟨P, ⟨m, S, hS, hzG, rfl⟩, ⟨m', S', hS', hzH, heq⟩⟩
  have hSS' : S = S' := posDef_eq_of_multivariateGaussian_eq hS hS' heq
  subst hSS'
  simp only [id_eq]
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [← not_iff_not, ← hzG i j hij, ← hzH i j hij]

end Model

section MarkovProperties

/-- **HEADLINE — the pairwise Markov property** (Lauritzen §5.2, p. 131: the covariance selection
model "is given by assuming that `Y` follows a multivariate normal distribution which obeys the
undirected pairwise Markov property with respect to `G`"; §3.2, p. 32, property (P)).

Stated as an instance of `Undirected.Markov.IsPairwiseMarkov` at the abstract relation
`ci := CondIndepCoords P gaussianCoords`. Immediate from Proposition 5.2 — this is the sense in
which the zero pattern of `K` *is* the graph. `IsPairwiseMarkov` already quantifies over distinct
non-adjacent pairs and conditions on `Finset.univ \ {i, j}`, which is exactly the shape
`condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero` produces. -/
theorem isPairwiseMarkov_of_mem_gaussianGraphicalModel {G : SimpleGraph ι}
    {P : Measure (EuclideanSpace ℝ ι)}
    -- USER-INPUT: a law of the covariance selection model; Lauritzen §5.2, p. 131
    (hP : P ∈ gaussianGraphicalModel G) :
    IsPairwiseMarkov G (CondIndepCoords P gaussianCoords) := by
  obtain ⟨m, S, hS, hz, rfl⟩ := mem_gaussianGraphicalModel_iff.mp hP
  intro i j hij hadj
  exact (condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero m hS hij).mpr
    (hz i j hij hadj)

/-- **The definition and the parametrisation agree** (Lauritzen §5.2, p. 131: "It follows from
Proposition 5.2 that this is equivalent to assuming the quadratic interactions `k_{γμ}` to be
equal to zero for all pairs `γ, μ` which are not adjacent in `G`").

A regular Gaussian belongs to the covariance selection model of `G` **iff** it is pairwise Markov
with respect to `G`. The `←` direction is the one that needs Proposition 5.2 in its nontrivial
direction. Together with `isPairwiseMarkov_of_mem_gaussianGraphicalModel` this says the model
class is *defined* by (P), which is how Lauritzen introduces it. -/
theorem multivariateGaussian_mem_gaussianGraphicalModel_iff_pairwise {G : SimpleGraph ι}
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen §5.2, p. 131
    (hS : S.PosDef) :
    multivariateGaussian m S ∈ gaussianGraphicalModel G
      ↔ IsPairwiseMarkov G (CondIndepCoords (multivariateGaussian m S) gaussianCoords) := by
  rw [multivariateGaussian_mem_gaussianGraphicalModel_iff m hS]
  exact ⟨fun hz i j hij hadj =>
      (condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero m hS hij).mpr (hz i j hij hadj),
    fun hM i j hij hadj =>
      (condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero m hS hij).mp (hM i j hij hadj)⟩

/-! ### Lauritzen Proposition 3.1 at the Gaussian — the graphoid instance

The Gaussian's contribution to the `Core.Semigraphoid` abstraction. (C1) and (C2) hold for the
coordinate relation in general; the three sub-lemmas below are the ones that need the Gaussian,
and are stated separately rather than inline in the instance. All three carry the book's pairwise
disjointness of the blocks.

### The reduction

Write `K^E := (Σ_E)⁻¹` for the concentration matrix of the **principal submatrix** of `Σ` on a
block `E ⊆ Γ` — equivalently of the marginal law of `Y_E`, a Gaussian marginal being the
principal submatrix. The block form of Proposition 5.2 reads

`Y_A ⫫ Y_B ∣ Y_C  ⟺  (K^{A ∪ B ∪ C})_{AB} = 0`   (†)

for pairwise disjoint `A`, `B`, `C`: conditioning on `Y_C` leaves `(Y_A, Y_B)` jointly normal
with covariance the Schur complement `Σ_{AB} − Σ_{AB,C}Σ_{CC}⁻¹Σ_{C,AB}`; two blocks of a regular
normal are independent iff that cross-block vanishes (Corollary C.6), and (C.3) identifies the
*inverse* of that Schur complement with the `A ∪ B` principal block of `K^{A ∪ B ∪ C}`, whose
off-diagonal block vanishes exactly when the Schur complement's does.

(†) is `condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero`. Note that it takes the
index block `E` as a *parameter* with `hE : A ∪ B ∪ C = E`: the type of `K^E`
depends on `E`, so a literal union would force a dependent transport every time two blocks were
presented differently. All three sub-lemmas below exploit this by fixing **one**
`E := A ∪ B ∪ C ∪ D` and reading every premise and the conclusion on it.

*The three sub-lemmas then go as follows.* Every statement of (C3) and (C5), and the conclusion
of (C4), lives on that same `E`, since `A ∪ (B ∪ D) ∪ C = A ∪ B ∪ (C ∪ D) = E`.

* **(C3)** is pure bookkeeping: `(K^E)_{A, B ∪ D} = 0` gives `(K^E)_{AB} = 0`.
* **(C5)** is pure bookkeeping too: its second premise's index block is `A ∪ D ∪ (C ∪ B) = E` as
  well, so the two premises are `(K^E)_{AB} = 0` and `(K^E)_{AD} = 0`, which together *are* the
  conclusion `(K^E)_{A, B ∪ D} = 0`.
* **(C4) is not bookkeeping**, and it is the one that also needs marginalisation. Its second
  premise `Y_A ⫫ Y_D ∣ Y_C` lives on the strictly smaller block `F := A ∪ D ∪ C`, so it delivers
  `(K^F)_{AD} = 0` and **not** `(K^E)_{AD} = 0`. The two are linked by marginalisation: deleting
  `B` from `E` replaces `K^E` by its Schur complement,
  `K^F = (K^E)_{F} − (K^E)_{F,B}((K^E)_{BB})⁻¹(K^E)_{B,F}`, whose `(A, D)` entry is
  `(K^E)_{AD} − (K^E)_{AB}((K^E)_{BB})⁻¹(K^E)_{BD}`. The *first* premise `(K^E)_{AB} = 0` kills
  the correction term, so `(K^E)_{AD} = (K^F)_{AD} = 0`. That marginalisation step is the **dual
  of (C.3)** — marginalisation being Schur complementation of `K` just as conditioning is
  principal submatrixing of `K` — in the sharp form "a row of `K` that already vanishes on the
  deleted block survives marginalisation". -/

/-- **(C3), weak union, for the Gaussian** (Lauritzen §3.1, p. 29): `X_A ⫫ (X_B, X_D) ∣ X_C`
implies `X_A ⫫ X_B ∣ (X_C, X_D)`.

In full generality only (C1)–(C2) are available — weak union needs essential uniqueness of
disintegrations — so the Gaussian supplies this itself, by block splitting rather than through
the general calculus.

*Proof.* Bookkeeping on top of the block form (†) of Proposition 5.2
(`condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero`): premise and conclusion live
on the **same** index block `E := A ∪ B ∪ C ∪ D`, since `A ∪ (B ∪ D) ∪ C = A ∪ B ∪ (C ∪ D) = E`,
and read `(K^E)_{A, B ∪ D} = 0` and `(K^E)_{AB} = 0`. The second is the first restricted along
`B ⊆ B ∪ D`. Taking `E` as a *parameter* of (†) rather than the literal union is what makes this
a restriction rather than a dependent transport. -/
theorem condIndepCoords_weakUnion_of_disjoint
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen §5.2, p. 131
    (hS : S.PosDef) {A B C D : Finset ι}
    -- USER-INPUT: Lauritzen states (C1)–(C5) for disjoint subsets; §3.1, p. 29
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    -- USER-INPUT: the independence to be weakened; Lauritzen §3.1 (C3), p. 29
    (h : CondIndepCoords (multivariateGaussian m S) gaussianCoords A (B ∪ D) C) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords A B (C ∪ D) := by
  classical
  set E : Finset ι := A ∪ B ∪ C ∪ D with hEdef
  have hE₁ : A ∪ (B ∪ D) ∪ C = E := by
    rw [hEdef]; ext x; simp only [Finset.mem_union]; tauto
  have hE₂ : A ∪ B ∪ (C ∪ D) = E := by
    rw [hEdef]; ext x; simp only [Finset.mem_union]; tauto
  rw [condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero m hS
      (Finset.disjoint_union_right.mpr ⟨hAB, hAD⟩) hAC
      (Finset.disjoint_union_left.mpr ⟨hBC, hCD.symm⟩) hE₁] at h
  rw [condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero m hS hAB
      (Finset.disjoint_union_right.mpr ⟨hAC, hAD⟩)
      (Finset.disjoint_union_right.mpr ⟨hBC, hBD⟩) hE₂]
  exact fun a b ha hb => h a b ha (Finset.mem_union_left _ hb)

/-- **(C4), contraction, for the Gaussian** (Lauritzen §3.1, p. 29): `X_A ⫫ X_B ∣ (X_C, X_D)`
together with `X_A ⫫ X_D ∣ X_C` implies `X_A ⫫ (X_B, X_D) ∣ X_C`.

*Proof.* The only one of the three whose two premises genuinely interact, because they live on
**different** index blocks: the conclusion and the first premise on `E := A ∪ B ∪ C ∪ D`, the
second premise on the strictly smaller `F := A ∪ D ∪ C`. For a target index `b ∈ B` the first
premise is already the conclusion. For `b ∈ D` the two are linked by marginalisation: deleting
`B` from `E` replaces `K^E` by its Schur complement
`(K^E)_{F} − (K^E)_{F,B}((K^E)_{BB})⁻¹(K^E)_{B,F}`, and the first premise `(K^E)_{AB} = 0` says
precisely that row `a` of the correction term vanishes, so `(K^E)_{ab} = (K^F)_{ab} = 0` by the
second premise. That step is `precisionMatrix_principalSubmatrix_apply_of_row_eq_zero`, the
`Finset` form of the dual of Lauritzen (C.3). -/
theorem condIndepCoords_contraction_of_disjoint
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen §5.2, p. 131
    (hS : S.PosDef) {A B C D : Finset ι}
    -- USER-INPUT: Lauritzen states (C1)–(C5) for disjoint subsets; §3.1, p. 29
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    -- USER-INPUT: first premise of (C4); Lauritzen §3.1, p. 29
    (h₁ : CondIndepCoords (multivariateGaussian m S) gaussianCoords A B (C ∪ D))
    -- USER-INPUT: second premise of (C4); Lauritzen §3.1, p. 29
    (h₂ : CondIndepCoords (multivariateGaussian m S) gaussianCoords A D C) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords A (B ∪ D) C := by
  classical
  set E : Finset ι := A ∪ B ∪ C ∪ D with hEdef
  set F : Finset ι := A ∪ D ∪ C with hFdef
  have hE₁ : A ∪ B ∪ (C ∪ D) = E := by
    rw [hEdef]; ext x; simp only [Finset.mem_union]; tauto
  have hE₃ : A ∪ (B ∪ D) ∪ C = E := by
    rw [hEdef]; ext x; simp only [Finset.mem_union]; tauto
  have hFE : F ⊆ E := by
    rw [hFdef, hEdef]; intro x hx; simp only [Finset.mem_union] at hx ⊢; tauto
  -- what `E` has and `F` does not is exactly `B`
  have hmemF : ∀ x ∈ E, x ∉ F → x ∈ B := by
    intro x hx hxF
    rw [hEdef] at hx; rw [hFdef] at hxF
    simp only [Finset.mem_union] at hx hxF
    tauto
  rw [condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero m hS hAB
      (Finset.disjoint_union_right.mpr ⟨hAC, hAD⟩)
      (Finset.disjoint_union_right.mpr ⟨hBC, hBD⟩) hE₁] at h₁
  rw [condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero m hS hAD hAC hCD.symm
      (rfl : A ∪ D ∪ C = F)] at h₂
  rw [condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero m hS
      (Finset.disjoint_union_right.mpr ⟨hAB, hAD⟩) hAC
      (Finset.disjoint_union_left.mpr ⟨hBC, hCD.symm⟩) hE₃]
  intro a b ha hb
  rcases Finset.mem_union.mp hb with hb | hb
  · exact h₁ a b ha hb
  -- the interesting case: `b ∈ D`, where the second premise lives on the smaller block `F`
  have haF : (a : ι) ∈ F := by rw [hFdef]; simp only [Finset.mem_union]; tauto
  have hbF : (b : ι) ∈ F := by rw [hFdef]; simp only [Finset.mem_union]; tauto
  -- the first premise says row `a` of `K^E` already vanishes on the block to be deleted
  have hrow : ∀ c : ↥E, (c : ι) ∉ F →
      precisionMatrix (principalSubmatrix S E) ⟨(a : ι), hFE haF⟩ c = 0 := by
    intro c hc
    have hca : (⟨(a : ι), hFE haF⟩ : ↥E) = a := Subtype.ext rfl
    rw [hca]
    exact h₁ a c ha (hmemF c c.2 hc)
  have hmarg := precisionMatrix_principalSubmatrix_apply_of_row_eq_zero hS hFE haF hrow hbF
  have hzero : precisionMatrix (principalSubmatrix S F) ⟨(a : ι), haF⟩ ⟨(b : ι), hbF⟩ = 0 :=
    h₂ ⟨(a : ι), haF⟩ ⟨(b : ι), hbF⟩ ha hb
  rw [hzero] at hmarg
  have hca : (⟨(a : ι), hFE haF⟩ : ↥E) = a := Subtype.ext rfl
  have hcb : (⟨(b : ι), hFE hbF⟩ : ↥E) = b := Subtype.ext rfl
  rw [hca, hcb] at hmarg
  exact hmarg.symm

/-- **(C5), intersection, for the Gaussian — Lauritzen Proposition 3.1** (p. 29): a strictly
positive continuous joint density satisfies intersection. A regular multivariate normal has such
a density (Lauritzen §5.2, p. 131: "Since the density is positive and continuous, this implies
the global and local Markov properties"), so

`X_A ⫫ X_B ∣ (X_C, X_D)` and `X_A ⫫ X_D ∣ (X_C, X_B)` ⟹ `X_A ⫫ (X_B, X_D) ∣ X_C`

for **pairwise disjoint** blocks. Two hypotheses do real work and neither is removable. The
disjointness is Lauritzen's own standing convention — see the module docstring for the
`B = D`, `C = ∅` counterexample that makes it constitutive. Regularity is what supplies the
positive density: (C5) fails outright for a degenerate law, by Lauritzen's `X = Y = Z`
counterexample on p. 30.

*Proof.* Bookkeeping on top of the block form (†) of Proposition 5.2: both premises live on the
same index block `E := A ∪ B ∪ C ∪ D` (the second because `A ∪ D ∪ (C ∪ B) = E`) and read
`(K^E)_{AB} = 0`, `(K^E)_{AD} = 0`, which together are the conclusion `(K^E)_{A, B ∪ D} = 0`.
Note where the regularity actually enters on this route: it is `Σ.PosDef` that makes `K^E` exist
at all, which is the matrix shadow of "the density is positive". -/
theorem condIndepCoords_intersection_of_disjoint
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular — this is what makes the density positive and continuous;
    -- Lauritzen Prop. 3.1, p. 29 and §5.2, p. 131
    (hS : S.PosDef) {A B C D : Finset ι}
    -- USER-INPUT: Lauritzen states (C1)–(C5) for disjoint subsets; §3.1, p. 29
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    -- USER-INPUT: first premise of (C5); Lauritzen §3.1, p. 30
    (h₁ : CondIndepCoords (multivariateGaussian m S) gaussianCoords A B (C ∪ D))
    -- USER-INPUT: second premise of (C5); Lauritzen §3.1, p. 30
    (h₂ : CondIndepCoords (multivariateGaussian m S) gaussianCoords A D (C ∪ B)) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords A (B ∪ D) C := by
  classical
  set E : Finset ι := A ∪ B ∪ C ∪ D with hEdef
  have hE₁ : A ∪ B ∪ (C ∪ D) = E := by
    rw [hEdef]; ext x; simp only [Finset.mem_union]; tauto
  have hE₂ : A ∪ D ∪ (C ∪ B) = E := by
    rw [hEdef]; ext x; simp only [Finset.mem_union]; tauto
  have hE₃ : A ∪ (B ∪ D) ∪ C = E := by
    rw [hEdef]; ext x; simp only [Finset.mem_union]; tauto
  rw [condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero m hS hAB
      (Finset.disjoint_union_right.mpr ⟨hAC, hAD⟩)
      (Finset.disjoint_union_right.mpr ⟨hBC, hBD⟩) hE₁] at h₁
  rw [condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero m hS hAD
      (Finset.disjoint_union_right.mpr ⟨hAC, hAB⟩)
      (Finset.disjoint_union_right.mpr ⟨hCD.symm, hBD.symm⟩) hE₂] at h₂
  rw [condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero m hS
      (Finset.disjoint_union_right.mpr ⟨hAB, hAD⟩) hAC
      (Finset.disjoint_union_left.mpr ⟨hBC, hCD.symm⟩) hE₃]
  intro a b ha hb
  rcases Finset.mem_union.mp hb with hb | hb
  · exact h₁ a b ha hb
  · exact h₂ a b ha hb

/-- **The conditional-independence relation of a regular Gaussian is a graphoid** — the Gaussian
instance of `Core.Semigraphoid.IsGraphoid`, i.e. Lauritzen **Proposition 3.1** (p. 29) applied to
the normal density, which §5.2 (p. 131) invokes when it says "since the density is positive and
continuous, this implies the global and local Markov properties".

This is the single object the Markov hierarchy needs from the Gaussian side: with it,
Theorem 3.7 (Pearl–Paz) and the equivalence of the three Markov properties apply to this model
class.

The fields are `symm := CondIndepCoords.symm`,
`decomposition := CondIndepCoords.decomposition_of_sfinite` at `B ⊆ B ∪ D` (a decomposition
without the s-finiteness hypothesis is false; here that hypothesis is an instance, a Gaussian
being a probability measure), and the three named sub-lemmas above for `weakUnion`,
`contraction` and `intersection`. -/
theorem isGraphoid_condIndepCoords_multivariateGaussian
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular — positivity and continuity of the density; Lauritzen Prop. 3.1,
    -- p. 29, and §5.2, p. 131
    (hS : S.PosDef) :
    IsGraphoid (CondIndepCoords (multivariateGaussian m S) gaussianCoords) := by
  refine ⟨⟨fun _ _ _ h => h.symm, fun _ _ _ _ _ h =>
      CondIndepCoords.decomposition_of_sfinite Finset.subset_union_left h, ?_, ?_⟩, ?_⟩
  · intro A B D C hAB hAC hAD hBC hBD hCD h
    exact condIndepCoords_weakUnion_of_disjoint m hS hAB hAC hAD hBC hBD hCD h
  · intro A B D C hAB hAC hAD hBC hBD hCD h₁ h₂
    exact condIndepCoords_contraction_of_disjoint m hS hAB hAC hAD hBC hBD hCD h₁ h₂
  · intro A B D C hAB hAC hAD hBC hBD hCD h₁ h₂
    exact condIndepCoords_intersection_of_disjoint m hS hAB hAC hAD hBC hBD hCD h₁ h₂

/-- **The global Markov property** (Lauritzen §3.2, p. 32, property (G); §5.2, p. 131: "Since the
density is positive and continuous, this implies the global and local Markov properties"), as an
instance of `Undirected.Markov.IsGlobalMarkov`. Separation is `Core.Separation.Separates` and the
three disjointness conditions are part of that definition.

*Proof.* Destructure `hP` into a regular `multivariateGaussian m S`, then apply Theorem 3.7 to
the pairwise Markov property through the graphoid instance above — which is exactly Lauritzen's
own argument.

**Why the `_of_nonempty` form, and why no hypothesis is added.** Theorem 3.7 over *all* disjoint
triples is false (`not_forall_pairwiseMarkov_implies_globalMarkov`): `IsGlobalMarkov` demands
`ci ∅ B S` of every instance while (P) says nothing about empty blocks, and no graphoid axiom
can manufacture a first `ci`-statement. The Gaussian, however, *can* supply those degenerate
cases directly — `CondIndepCoords.of_isEmpty_left`, the subvector on an empty block taking
values in a singleton type — so the empty-block regime is discharged here rather than assumed. -/
theorem isGlobalMarkov_of_mem_gaussianGraphicalModel {G : SimpleGraph ι}
    {P : Measure (EuclideanSpace ℝ ι)}
    -- USER-INPUT: a law of the covariance selection model; Lauritzen §5.2, p. 131
    (hP : P ∈ gaussianGraphicalModel G) :
    IsGlobalMarkov G (CondIndepCoords P gaussianCoords) := by
  obtain ⟨m, S, hS, hz, rfl⟩ := mem_gaussianGraphicalModel_iff.mp hP
  intro A B T hAB hAT hBT hsep
  -- the two degenerate blocks, which Theorem 3.7 cannot reach but the Gaussian supplies itself
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact CondIndepCoords.of_isEmpty_left measurable_gaussianCoords B T
  rcases B.eq_empty_or_nonempty with rfl | hB
  · exact (CondIndepCoords.of_isEmpty_left measurable_gaussianCoords A T).symm
  -- and Theorem 3.7 (Pearl–Paz) on the book's own nonempty blocks
  exact pairwiseMarkov_implies_globalMarkov_of_nonempty G
    (isGraphoid_condIndepCoords_multivariateGaussian m hS)
    (isPairwiseMarkov_of_mem_gaussianGraphicalModel hP) A B T hA hB hAB hAT hBT hsep

/-- **The local Markov property** (Lauritzen §3.2, p. 32, property (L)):
`Y_γ ⫫ Y_{Γ∖cl(γ)} ∣ Y_{bd(γ)}`, as an instance of `Undirected.Markov.IsLocalMarkov`.

It is `globalMarkov_implies_localMarkov` applied to
`isGlobalMarkov_of_mem_gaussianGraphicalModel`, a step that is pure graph separation and uses no
property of `ci` at all. -/
theorem isLocalMarkov_of_mem_gaussianGraphicalModel {G : SimpleGraph ι}
    -- LEAN-ONLY: `IsLocalMarkov` is stated through `G.neighborFinset`, which needs the
    -- neighbourhoods to be `Finset`s
    [DecidableRel G.Adj] {P : Measure (EuclideanSpace ℝ ι)}
    -- USER-INPUT: a law of the covariance selection model; Lauritzen §5.2, p. 131
    (hP : P ∈ gaussianGraphicalModel G) :
    IsLocalMarkov G (CondIndepCoords P gaussianCoords) :=
  globalMarkov_implies_localMarkov G (isGlobalMarkov_of_mem_gaussianGraphicalModel hP)

end MarkovProperties

end StatLean.StatisticalModels.GraphicalModels
