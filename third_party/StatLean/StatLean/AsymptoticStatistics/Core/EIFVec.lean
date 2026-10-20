module
public import StatLean.AsymptoticStatistics.Core.EIF
public import StatLean.AsymptoticStatistics.Core.PathwiseVec
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian

@[expose] public section

/-!
# Vector-valued efficient influence functions

For a functional $\psi : \mathcal P \to \mathbb R^k$ whose derivative is a continuous
linear map $\dot\psi : T \to \mathbb R^k$ on the tangent space $T$ (a closed subspace of
mean-zero, square-integrable functions $L^2_0(P)$), a tuple of influence functions
$\tilde\psi = (\tilde\psi_1, \dots, \tilde\psi_k)$, each $\tilde\psi_i \in L^2_0(P)$, is the
**efficient influence function** for $\psi$ exactly when it is efficient coordinatewise:
for every coordinate $i$, the function $\tilde\psi_i$ is the (real-valued) efficient
influence function for the scalar functional $e_i \circ \dot\psi$, the composition of the
derivative with projection onto the $i$-th coordinate.

In other words, $k$-dimensional efficiency reduces to $k$ separate one-dimensional efficiency
conditions, one per coordinate. This file packages that componentwise definition
(`IsEfficientInfluenceFunction_vec`) and the immediate extraction of a single coordinate's
efficient influence function from the vector version
(`IsEfficientInfluenceFunction_vec_componentwise`).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998. Chapter 25 (Semiparametric
Models), §25.3 (Tangent Spaces and Information) — the efficient influence function of an
$\mathbb R^k$-valued functional, defined through its coordinate functionals.

**Proof formalization notes.** The vector predicate is defined componentwise: it asserts that
each component `IF i` satisfies the scalar `IsEfficientInfluenceFunction` predicate (from
`Core.EIF`) for the projected derivative `EuclideanSpace.proj i ∘L Dψ`. The extraction lemma
is then definitional — applying the universally quantified hypothesis at a fixed coordinate
`i`. No book constants are involved; this is the structural bridge between the scalar EIF
theory and its vector-valued use elsewhere in the chapter.

**Bibliographic comments.** The reduction of vector-valued semiparametric efficiency to a
collection of coordinatewise efficiency statements is standard in the modern semiparametric
efficiency literature and has no single seminal origin; it is folklore in the sense of vdV
§25.3. The systematic development of efficient and efficient-influence-function theory for
(possibly infinite-dimensional) parameters is given in P. J. Bickel, C. A. J. Klaassen,
Y. Ritov and J. A. Wellner, *Efficient and Adaptive Estimation for Semiparametric Models*,
Johns Hopkins University Press, Baltimore, 1993 (reprinted Springer, 1998), where the
efficient influence function of a Euclidean parameter is characterized through its components
and the projection onto the tangent space.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.EIFVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.PathwiseVec
open AsymptoticStatistics.Core.EIF

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {T : Submodule ℝ ↥(L2ZeroMean P)}
variable {k : ℕ}

/-- An efficient influence function tuple `IF : Fin k → L²₀(P)` for a vector
derivative `Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin k)` is defined componentwise:
each `IF i` is the efficient influence function for the i-th coordinate
functional.
-/
def IsEfficientInfluenceFunction_vec
    (Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin k))
    (IF : Fin k → ↥(L2ZeroMean P)) : Prop :=
  ∀ i, IsEfficientInfluenceFunction P T
    (EuclideanSpace.proj i ∘L Dψ) (IF i)

/-- Component extraction from vector EIF. -/
theorem IsEfficientInfluenceFunction_vec_componentwise
    {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin k)}
    {IF : Fin k → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec Dψ IF) (i : Fin k) :
    IsEfficientInfluenceFunction P T (EuclideanSpace.proj i ∘L Dψ) (IF i) :=
  hEIF i

end AsymptoticStatistics.Core.EIFVec
