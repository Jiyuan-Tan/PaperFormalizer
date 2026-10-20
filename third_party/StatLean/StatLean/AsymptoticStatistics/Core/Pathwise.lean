module
public import StatLean.AsymptoticStatistics.Core.TangentAbstract
public import StatLean.AsymptoticStatistics.Core.QMDPath

@[expose] public section

/-!
# Influence functions, efficient influence functions, and pathwise differentiability

Let $\psi : \mathcal{P} \to \mathbb{R}$ be a statistical functional defined on a set
of probability measures, and let $P$ be a fixed probability measure with tangent set
$\dot{\mathcal{P}}_P \subseteq L^2_0(P)$ (the mean-zero, square-integrable score
directions). We formalize three concepts.

* **Pathwise differentiability.** $\psi$ is *pathwise differentiable at $P$ relative to
  the tangent space $T$* if there is a continuous linear functional
  $\dot{\psi}_P : T \to \mathbb{R}$ such that, along every quadratic-mean-differentiable
  submodel $t \mapsto P_t$ through $P$ with score $g \in T$,
  $$\frac{\psi(P_t) - \psi(P)}{t} \longrightarrow \dot{\psi}_P(g) \qquad (t \to 0).$$

* **Influence function.** A function $\tilde{\psi}_P \in L^2_0(P)$ is an *influence
  function* for the derivative $\dot{\psi}_P$ if, for every tangent direction $g \in T$,
  $$\langle \tilde{\psi}_P,\, g \rangle_{L^2(P)} = \dot{\psi}_P(g).$$
  Equivalently $\mathbb{E}_P[\tilde{\psi}_P\, g] = \dot{\psi}_P(g)$.

* **Efficient influence function.** An influence function that additionally lies in the
  (closed) tangent space, $\tilde{\psi}_P \in \overline{T}$. When it exists, it is the
  orthogonal projection of any influence function onto $T$, and hence is unique.

The first two notions (`IsInfluenceFunction`, `IsEfficientInfluenceFunction`) are stated
purely in Hilbert-space terms: they take an abstract derivative
$\dot{\psi}_P : T \to \mathbb{R}$ and do not mention curves. The third
(`PathwiseDifferentiableAt`) is the curve-based assertion built on the `QMDPath`
machinery of `Core/QMDPath.lean`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 25
(Semiparametric Models), §25.3 (Tangent Spaces and Information) — the definitions of
influence function, efficient influence function, and pathwise differentiability given
in the paragraphs immediately following Lemma 25.14.

**Proof formalization notes.** These are definitions, not theorems; there is no proof
obligation here. Two modeling choices are worth recording. (i) The book writes the
defining identity for the influence function as $\mathbb{E}_P[\tilde{\psi}_P\, g] =
\dot{\psi}_P(g)$; in Lean we use the $L^2(P)$ inner-product form
$\langle \tilde{\psi}_P, g \rangle = \dot{\psi}_P(g)$, which is definitionally equal.
(ii) The efficiency/projection statement (the EIF is the orthogonal projection of any
influence function onto the closed tangent space, hence unique) is not part of these
definitions; it is proved separately in `Core/EIF` (`eif_eq_orthogonalProjection`).
Edge behavior is documented per declaration: when $T = \bot$ the universal quantifiers
range over $\{0\}$, so every $\tilde{\psi}_P$ is trivially an influence function, the
only EIF is $0$, and pathwise differentiability forces $\psi$ to be locally constant
along admissible paths through $P$ — matching the book's convention that a degenerate
tangent space imposes no constraint.

**Bibliographic comments.** The influence function originates in robustness theory:
F. R. Hampel, "The Influence Curve and Its Role in Robust Estimation," *Journal of the
American Statistical Association* 69 (1974), 383–393, where it measures the
infinitesimal effect of contamination on an estimator. Its role as the
pathwise-derivative representer in efficiency theory, together with the efficient
influence function and the tangent-space geometry, was developed in the
local-asymptotic-minimax program of J. Hájek and L. Le Cam and crystallized in
P. J. Bickel, C. A. J. Klaassen, Y. Ritov, and J. A. Wellner, *Efficient and Adaptive
Estimation for Semiparametric Models*, Johns Hopkins University Press, Baltimore, 1993
(reprinted Springer, 1998) — see their Chapter 3 for the convex-geometry treatment of
influence functions and efficient influence functions in tangent spaces. Earlier
contributions to the pathwise-differentiability / "differentiable functional" viewpoint
include Yu. A. Koshevnik and B. Ya. Levit, "On a Non-parametric Analogue of the
Information Matrix," *Theory of Probability and Its Applications* 21 (1976), 738–753, and
J. Pfanzagl (with W. Wefelmeyer), *Contributions to a General Asymptotic Statistical
Theory*, Lecture Notes in Statistics 13, Springer, 1982. The presentation formalized
here follows van der Vaart's §25.3, which synthesizes these sources.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.Pathwise

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (T : Submodule ℝ ↥(L2ZeroMean P))

/-- An *influence function* at `P` for a pathwise derivative `dψ : T →L[ℝ] ℝ`
is an element `IF ∈ ↥(L2ZeroMean P)` whose `L²(P)` inner product against any
tangent direction `g ∈ T` recovers `dψ g`.

Reference: vdV §25.3, definition of influence function (paragraph after the
definition of pathwise differentiability). The book states it as
`IF ∈ L²₀(P)` with `PIFg = ψ̇_P(g)` for all `g ∈ 𝒫̇_P`; in Lean we use the
inner-product form which is definitionally equal.

Edge behavior: when `T = ⊥`, the universal quantifier is over the singleton
`{0}` and `dψ 0 = 0 = ⟪IF, 0⟫`, so every `IF` is trivially an influence
function. Matches the book's convention that a degenerate tangent space
imposes no constraint. -/
def IsInfluenceFunction (dψ : T →L[ℝ] ℝ) (IF : ↥(L2ZeroMean P)) : Prop :=
  ∀ g : T, ⟪IF, (g : ↥(L2ZeroMean P))⟫_ℝ = dψ g

/-- An *efficient influence function* at `P` for a derivative `dψ : T →L[ℝ] ℝ`
is an influence function that lies inside the tangent space `T`.

Reference: vdV §25.3, definition of efficient influence function (paragraph
following the definition of influence function). The book observes that the
EIF, when it exists, is the orthogonal projection of any influence function
onto the (closed) tangent space — that uniqueness/projection theorem is
`Core/EIF.eif_eq_orthogonalProjection`.

Edge behavior: when `T = ⊥`, the only EIF is `0`, and `0` is an influence
function iff `dψ` is identically zero. -/
def IsEfficientInfluenceFunction
    (dψ : T →L[ℝ] ℝ) (IF : ↥(L2ZeroMean P)) : Prop :=
  IsInfluenceFunction P T dψ IF ∧ IF ∈ T

/-- A statistical functional `ψ : Measure Ω → ℝ` is *pathwise differentiable*
at `P` relative to the tangent space `T` iff there exists a continuous-linear
derivative `dψ : T →L[ℝ] ℝ` such that for every `QMDPath` at `P` whose
score lies in `T`, the difference quotient `(ψ(γ.curve t) - ψ P)/t`
converges to `dψ ⟨γ.score, _⟩` as `t → 0`.

Reference: vdV §25.3, definition immediately following lem:25.14 (curve-based).
Its faithful formulation depends on the QMD curves of `Core/QMDPath.lean`.

Edge behavior: when `T = ⊥`, the only QMDPath with score in `T` has score
`0`, and the difference quotient must tend to `dψ 0 = 0` — which forces
`ψ` to be locally constant along any such path through `P`. -/
structure PathwiseDifferentiableAt
    (ψ : Measure Ω → ℝ) where
  /-- vdV §25.3: the pathwise derivative as a continuous
  linear functional on the tangent space. -/
  derivative : T →L[ℝ] ℝ
  /-- vdV §25.3: the difference-quotient limit holds along
  every QMDPath at `P` whose score lies in `T`. -/
  derivative_spec :
    ∀ (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P),
      ∀ (h_in_T : (γ.score : ↥(L2ZeroMean P)) ∈ T),
        Filter.Tendsto (fun t : ℝ => (ψ (γ.curve t) - ψ P) / t)
          (nhdsWithin 0 {0}ᶜ) (nhds (derivative ⟨γ.score, h_in_T⟩))

end AsymptoticStatistics.Core.Pathwise
