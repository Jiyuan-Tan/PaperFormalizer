module
public import StatLean.AsymptoticStatistics.Core.Hilbert
public import StatLean.AsymptoticStatistics.Core.QMDPath

@[expose] public section

/-!
# Tangent set and tangent space (abstract Hilbert version)

Fix a probability measure $P$ and work in the Hilbert space $L^2_0(P)$ of
square-integrable functions with mean zero (the scores). A *tangent set* at $P$
is a collection $\dot{\mathcal{P}}_P \subseteq L^2_0(P)$ of score functions, each
arising as the score $g$ at $t = 0$ of some one-dimensional submodel
$t \mapsto P_t$ that is differentiable in quadratic mean and passes through $P$
($P_0 = P$). The *tangent space* is the closed linear span of the tangent set
inside $L^2_0(P)$.

We separate the two notions: `TangentSpec P` bundles the set of admissible score
directions together with the requirement that each one be realized by a
quadratic-mean-differentiable path, while `tangentSpace T` is the derived closed
linear span (`Submodule.span` followed by topological closure). The realizing-path
requirement is imposed only on carrier elements, not on the limits that the
closure introduces, mirroring the book: the closed span may contain directions
not witnessed by any submodel. Closure of the tangent set under scaling or
addition is treated as a regularity property, not part of the definition (vdV
also studies one-sided tangent *cones* where additive closure fails), so it is
not a field here.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.3 (the unlabeled definitions in the
paragraph following Lemma 25.14, p. 362), with the regularity discussion of the
tangent span on p. 366 (§25.3.2).

**Proof formalization notes.** These are definitions plus three elementary
lemmas, so there is little proof content. `tangentSpace T` is built as
`(Submodule.span ℝ T.carrier).topologicalClosure`. Edge behavior: when
`T.carrier = ∅`, the algebraic span is `⊥` and its closure is again `⊥`, so a
vacuous tangent set yields the trivial tangent space — matching the book's
convention that "no admissible directions" means "no nontrivial tangent space".
`span_carrier_le_tangentSpace` records that the algebraic span (over which vdV's
regularity hypothesis on score directions is quantified, p. 366) sits inside the
closure (where the efficient influence function and pathwise differentiability
live). `exists_seq_span_tendsto_of_mem_tangentSpace` is the sequential
characterization of closure membership in the metric space `L²₀(P)`: every
element of the tangent space is an $L^2(P)$-limit of a sequence drawn from the
algebraic span, the analytic core of vdV's finite-span approximation argument
for the efficient influence function (§25.3.2).

**Bibliographic comments.** The tangent-space / score-path machinery for
semiparametric efficiency originates with C. Stein, "Efficient nonparametric
testing and estimation", *Proc. Third Berkeley Symp. Math. Statist. Probab.*,
vol. 1 (1956), 187–195, who first used one-dimensional parametric submodels to
bound attainable accuracy. It was developed into the geometric "tangent space"
formulation by J. M. Begun, W. J. Hall, W.-M. Huang and J. A. Wellner,
"Information and asymptotic efficiency in parametric–nonparametric models",
*Ann. Statist.* **11** (1983), 432–452, and given its canonical book-length
treatment in P. J. Bickel, C. A. J. Klaassen, Y. Ritov and J. A. Wellner,
*Efficient and Adaptive Estimation for Semiparametric Models*, Johns Hopkins
University Press, 1993 (reprinted Springer, 1998), Chapter 3, where the tangent
set/space and projected score directions are defined essentially as here. The
abstract Hilbert-space packaging — tangent set as a subset of $L^2_0(P)$, tangent
space as its closed linear span — follows van der Vaart's textbook synthesis of
that literature rather than any single seminal equation.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.TangentAbstract

open AsymptoticStatistics.Core.Hilbert

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A *tangent specification* at a probability measure `P`: a set of score
functions in `↥(L2ZeroMean P)`, each realized as the score of a
quadratic-mean-differentiable submodel passing through `P`.

vdV §25.3 (paragraph after Lemma 25.14): a tangent set is, by definition, just a
subset of `L²₀(P)`. Closure under scaling, addition, or convex combinations is a
regularity property, not part of the definition: vdV §25.3 considers tangent
cones (one-sided submodels) where additive closure fails, so those properties do
not live as fields here. -/
structure TangentSpec (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- vdV §25.3: the set of admissible score directions at `P`. -/
  carrier : Set ↥(L2ZeroMean P)
  /-- vdV §25.3.1: every `g ∈ carrier` is the score of a
  quadratic-mean-differentiable submodel `t ↦ Pₜ` at `t = 0`. Per vdV's
  definition "we obtain a collection of score functions, which we call a
  tangent set", membership IS witnessed by a realizing path.

  Carrier-scoped (not `tangentSpace`-scoped): vdV asserts the realizing
  path only for carrier elements; the L²-closure `tangentSpace T_set`
  may contain limits not realized by any QMD path. -/
  submodelOf : ∀ g ∈ carrier, ∃ γ : AsymptoticStatistics.Core.QMDPath.QMDPath P,
    γ.score = g

/-- The *tangent space* at `P` associated to a tangent specification `T`: the
closed linear span of `T.carrier` inside `↥(L2ZeroMean P)`.

Reference: vdV §25.3 — "the closed linear span of the tangent set".

Edge behavior: when `T.carrier = ∅`, `Submodule.span ℝ ∅ = ⊥`, and the
topological closure of `⊥` (the singleton at `0`) is `⊥`. So a vacuous tangent
set yields the trivial tangent space, matching the book's convention that
"no admissible directions" means "no nontrivial tangent space". -/
noncomputable def tangentSpace
    {P : Measure Ω} [IsProbabilityMeasure P] (T : TangentSpec P) :
    Submodule ℝ ↥(L2ZeroMean P) :=
  (Submodule.span ℝ T.carrier).topologicalClosure

/-- The *algebraic* span of the tangent set's carrier is contained in the tangent
space (its L²-closed linear span). vdV §25.3.2's regularity hypothesis quantifies
score directions over the algebraic span `Submodule.span ℝ T.carrier` ("for every
`g ∈ lin g_p`", p.366), while the efficient influence function and pathwise
differentiability live over the closure `tangentSpace T`. This coercion lifts
span-membership to closure-membership where the latter is needed. -/
theorem span_carrier_le_tangentSpace
    {P : Measure Ω} [IsProbabilityMeasure P] (T : TangentSpec P) :
    Submodule.span ℝ T.carrier ≤ tangentSpace T :=
  (Submodule.span ℝ T.carrier).le_topologicalClosure

/-- Every element of the tangent space (the L²-closed linear span) is the
L²(P)-limit of a sequence drawn from the *algebraic* span `Submodule.span ℝ
T.carrier`. This is the sequential characterization of closure membership in the
first-countable (metric) space `↥(L2ZeroMean P)`. It is the analytic core of
vdV's argument that the efficient influence function — which lies in the closed
span — can be approximated arbitrarily well by its projections onto finite
algebraic spans of tangent-set elements (vdV §25.3.2, p.366). -/
theorem exists_seq_span_tendsto_of_mem_tangentSpace
    {P : Measure Ω} [IsProbabilityMeasure P] (T : TangentSpec P)
    {g : ↥(L2ZeroMean P)} (hg : g ∈ tangentSpace T) :
    ∃ a : ℕ → ↥(L2ZeroMean P),
      (∀ n, a n ∈ Submodule.span ℝ T.carrier) ∧
      Filter.Tendsto a Filter.atTop (nhds g) := by
  have hg' : g ∈ closure (↑(Submodule.span ℝ T.carrier) : Set ↥(L2ZeroMean P)) := hg
  exact mem_closure_iff_seq_limit.mp hg'

end AsymptoticStatistics.Core.TangentAbstract
