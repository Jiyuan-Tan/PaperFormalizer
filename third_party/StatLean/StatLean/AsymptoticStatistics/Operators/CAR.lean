module
public import StatLean.AsymptoticStatistics.Operators.InformationLoss
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.Composition.CompNotation

@[expose] public section

/-!
# Coarsening At Random (CAR)

We observe not the full data $X$ but a coarsened version $Y = M(X)$, where the
coarsening map $M$ is *at random*: conditionally on the observed level $Y = y$,
the full datum $X$ is distributed over the fibre $\{x : M(x) = y\}$ by a law that
does not further depend on the (unobserved) value of $X$. Equivalently, the full
law $P_{\mathrm{full}}$ disintegrates over the observed marginal
$P_{\mathrm{full}} \circ M^{-1}$ through a Markov kernel concentrated on the
$M$-fibres.

This file collects the three observed-data semiparametric results under CAR,
all built on the information-loss (orthogonal projection / conditional
expectation) operator $\Pi = \Pi_{M, P_{\mathrm{full}}}$ from
`Operators/InformationLoss.lean`:

* **Observed tangent space (Theorem 25.40).** Under CAR, the tangent space of
  the observed-data model equals the image $\Pi(\dot{\mathcal P})$ of the
  full-data tangent space $\dot{\mathcal P}$ under $\Pi$.
* **Influence-function lift (Lemma 25.41).** If $\varphi_{\mathrm{full}}$ is an
  influence function for the parameter in the full-data model, then its
  projection $\Pi\,\varphi_{\mathrm{full}}$ is an influence function for the
  same parameter in the observed-data model.
* **Efficiency-loss decomposition (Corollary 25.42).** The efficient influence
  function of the observed-data problem decomposes so that the asymptotic
  variance increases by an explicit nonnegative *information-loss* term
  measuring the part of $\varphi_{\mathrm{full}}$ annihilated by passing to the
  observed data.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.6, Theorem 25.40, Lemma 25.41,
Corollary 25.42.

**Proof formalization notes.** Builds on the information-loss operator
`Π = informationLossOperator M hM P_full` from `Operators/InformationLoss.lean`.
The CAR predicate `IsCoarseningAtRandom` uses the kernel-disintegration form: an
existential of a `ProbabilityTheory.Kernel Ω_obs Ω_full` disintegrating
`P_full` over `P_full.map M`, together with the regularity clause that the
kernel is concentrated on the `M`-fibre (`κ y` lives on `{x | M x = y}`, a.e.).
For deterministic coarsenings on standard Borel spaces, CAR is essentially
automatic via Mathlib's `ProbabilityTheory.Kernel.condDistrib` disintegration;
the substantive content of CAR appears at the *family* level (independence of
the kernel from the unobserved coordinate across submodels), so theorems
requiring CAR list it as an explicit hypothesis.

**Bibliographic comments.** The term *coarsening at random* was coined by
D. F. Heitjan and D. B. Rubin, "Ignorability and coarse data", *The Annals of
Statistics* **19** (1991), no. 4, 2244–2253, generalizing Rubin's
missing-at-random condition to grouped, censored, and rounded data. The
continuous-data theory underlying van der Vaart's §25.6 treatment is developed
in R. D. Gill, M. J. van der Laan and J. M. Robins, "Coarsening at random:
characterizations, conjectures, counter-examples", in *Proceedings of the First
Seattle Symposium in Biostatistics* (D.-Y. Lin and T. R. Fleming, eds.),
Springer Lecture Notes in Statistics **123**, 1997, pp. 255–294, which gives
the disintegration characterization used here and the semiparametric
information calculus for the observed-data model.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

set_option linter.dupNamespace false

namespace AsymptoticStatistics.Operators.CAR

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Operators.InformationLoss
open AsymptoticStatistics.ForMathlib.CondExpL2
open ProbabilityTheory

variable {Ω_full Ω_obs : Type*}
  [MeasurableSpace Ω_full] [MeasurableSpace Ω_obs]

variable {Ω_Y : Type*} [MeasurableSpace Ω_Y]

/-- *Coarsening At Random.* The coarsening map `M : Ω_full → Ω_obs` is
*at random* under `P_full` if `P_full` factors as the bind
`(P_full.map M).bind κ` for some kernel `κ : Ω_obs → Measure Ω_full`
that is concentrated on the `M`-fibres (`κ y` lives on `{x | M x = y}`,
a.e.).

Reference: vdV §25.6 (definition leading to thm:25.40).

CAR is a genuine restriction: many real-world coarsenings are **not**
CAR (e.g. outcome-dependent missingness in medical trials), so theorems
requiring CAR list it as an explicit hypothesis.

For deterministic coarsenings on standard Borel spaces, CAR is
essentially automatic via Mathlib's `ProbabilityTheory.Kernel.condDistrib`
disintegration; the substantive content of CAR appears at the *family*
level: independence of the kernel from the unobserved coordinate across
submodels. -/
def IsCoarseningAtRandom
    (M : Ω_full → Ω_obs) (P_full : Measure Ω_full) : Prop :=
  ∃ κ : Kernel Ω_obs Ω_full,
    P_full = (P_full.map M).bind κ ∧
    ∀ᵐ y ∂(P_full.map M), ∀ᵐ x ∂(κ y), M x = y

/-! ## The observed-data tangent space (vdV thm:25.40)

vdV §25.6, thm:25.40. Under CAR, the observed-data tangent set
`Ṗ_{P_{Q,R}}` for the model of `X` is obtained from the full-data tangent
set by taking conditional expectations under the coarsening σ-algebra
`M⁻¹(σ_obs)`, i.e. by applying the information-loss operator
`Π = informationLossOperator hM P_full`. We *define* the observed-data
tangent space as the `Π`-image of a supplied full-data tangent space; this
is the constructive content of the "⊆" half of the theorem, and `Π a` for a
full-data score `a` is the conditional expectation `E_{Q,R}(a(Y) | X = x)`. -/

open AsymptoticStatistics.Operators.InformationLoss in
/-- *Observed-data tangent space* (vdV thm:25.40).

Given the full-data tangent space `fullTangent : Submodule ℝ ↥(L²₀(P_full))`
and a measurable coarsening map `M`, the observed-data tangent space is the
image of `fullTangent` under the information-loss operator
`Π = informationLossOperator hM P_full`, i.e. `Π '' fullTangent`, viewed as a
submodule of `↥(L²₀(P_full.map M))`.

This is the book-faithful definition under CAR: thm:25.40 states that the
observed tangent set is obtained from the full-data tangent set "by taking
conditional expectations" (lem:25.34), which is exactly the action of `Π`.
The element `Π a = E_{Q,R}(a(Y) | X = x)` is the conditional-expectation
piece of the orthogonal decomposition in the theorem.

We take the bare algebraic `Submodule.map` (not its `topologicalClosure`):
thm:25.40 distinguishes the *tangent set* `Ṗ_{P_{Q,R}}` from its closure, and
downstream consumers (lem:25.41, cor:25.42) work with the image directly. The
closed tangent space is `(observedTangent …).topologicalClosure` when needed,
matching `Core.TangentAbstract.tangentSpace`. -/
noncomputable def observedTangent
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    (fullTangent : Submodule ℝ ↥(L2ZeroMean P_full)) :
    Submodule ℝ ↥(L2ZeroMean (P_full.map M)) :=
  Submodule.map (informationLossOperator hM P_full).toLinearMap fullTangent

open AsymptoticStatistics.Operators.InformationLoss in
/-- *Π-image characterization of `observedTangent`* (the constructive "⊆" half
of vdV thm:25.40). An observed score `g` lies in the observed
tangent space iff it is `Π a` for some full-data score `a ∈ fullTangent`. This
is true by definition of `observedTangent` as `Submodule.map Π fullTangent`,
and is used in the formalizations of lem:25.41 and cor:25.42. -/
theorem mem_observedTangent_iff
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    (fullTangent : Submodule ℝ ↥(L2ZeroMean P_full))
    (g : ↥(L2ZeroMean (P_full.map M))) :
    g ∈ observedTangent hM P_full fullTangent
      ↔ ∃ a ∈ fullTangent, informationLossOperator hM P_full a = g := by
  simp only [observedTangent, Submodule.mem_map, ContinuousLinearMap.coe_coe]

open AsymptoticStatistics.Operators.InformationLoss in
/-- *`Π` maps full-data scores into the observed tangent space* (vdV thm:25.40,
the forward inclusion `Π a ∈ Ṗ_X` for `a ∈ Ṗ_full`). -/
theorem informationLossOperator_mem_observedTangent
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    (fullTangent : Submodule ℝ ↥(L2ZeroMean P_full))
    {a : ↥(L2ZeroMean P_full)} (ha : a ∈ fullTangent) :
    informationLossOperator hM P_full a ∈ observedTangent hM P_full fullTangent :=
  (mem_observedTangent_iff hM P_full fullTangent _).mpr ⟨a, ha, rfl⟩

open AsymptoticStatistics.Operators.InformationLoss in
/-- *Tower identity for the observed tangent piece* (vdV §25.6, lem:25.34 +
thm:25.40). For a full-data score `a` and any observed test function `t`, the
`L²(P_obs)`-inner product of the conditional-expectation piece `Π a` against
`t` equals the `L²(P_full)`-inner product of `a` against the `M`-measurable
Doob pullback of `t`. This is the self-adjointness of the information-loss
operator transported through the Doob isometry; it is the orthogonality
engine behind the decomposition `g = Π a + b` (the `b` piece pairs to zero
against any `Π a` once `E_R(b | Y) = 0`). It is
`inner_informationLossRaw` lifted to the mean-zero subspaces via the clean
defining identity `informationLossOperator_coe_eq`. -/
theorem inner_observedTangent_piece
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    (a : ↥(L2ZeroMean P_full)) (t : Lp ℝ 2 (P_full.map M)) :
    ⟪(informationLossOperator hM P_full a : Lp ℝ 2 (P_full.map M)), t⟫_ℝ
      = ⟪(a : Lp ℝ 2 P_full),
          (((doobL2Equiv hM).symm t : lpMeas ℝ ℝ
              (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›) 2 P_full) :
              Lp ℝ 2 P_full)⟫_ℝ := by
  rw [informationLossOperator_coe_eq hM P_full a,
    ← informationLossRaw_apply hM P_full (a : Lp ℝ 2 P_full)]
  exact inner_informationLossRaw hM P_full (a : Lp ℝ 2 P_full) t

/-! ### The observed-tangent Hilbert decomposition (vdV thm:25.40)

The CAR-free geometry underlying thm:25.40. The book decomposes any mean-zero
observed score `g ∈ L²₀(P_obs)` orthogonally as `g = Π a + b`, where `Π a` is
the conditional-expectation image of a full-data score of `Y` and `b` is a
*coarsening score* satisfying `E_R(b(X) | Y) = 0`, and asserts the join is
dense (`closure = all mean-zero observed functions`). We render this
*conclusion* faithfully by the abstract-Hilbert route:

  * the observed Y-tangent is `observedTangent … (nonparametricYTangent …)`,
    the `Π`-image of the maximal nonparametric mean-zero `σ(πY)`-measurable
    scores of the full observation `Y = πY`;
  * the coarsening-score space `Ṙ = coarseningScoreSpace …` is `{b :
    E(doobSymm b | Y) = 0}`, the kernel of `b ↦ E(·|Y)` composed with the
    Doob pullback;
  * the organizing fact `coarseningScoreSpace = (observedTangent …)ᗮ`
    (`coarseningScoreSpace_eq_observedTangent_orthogonal`): `⊆` is
    orthogonality via the adjoint identity `inner_observedTangent_piece`, `⊇`
    is density via `condExpL2` self-adjointness. Everything (orthogonality +
    `closure = ⊤`) follows.

CAR is *not* a hypothesis of the Hilbert-geometric statements below. Its
constructive role is instead to identify `Ṙ = coarseningScoreSpace` with the
actual `R`-model conditional-density scores through the
score-of-conditional-density-submodel argument of vdV p.380. Such an
identification requires conditional-density QMD paths `t ↦ rₜ(· | y)`, whereas
the definitions here concern full-data laws `t ↦ Pₜ`. The
`IsCoarseningAtRandom` predicate records the family-level condition needed for
that separate identification. -/

open AsymptoticStatistics.ForMathlib.CondExpL2 in
/-- *Coarsening lift* of an observed function `b ∈ L²₀(P_obs)`: the Doob
pullback `(doobL2Equiv hM).symm b`, viewed as an `M`-measurable element of
`Lp ℝ 2 P_full`. This is the `doobSymm` map: it is the inverse of the Doob
isometry that `inner_observedTangent_piece` pairs against, packaged as a
continuous linear map so its kernel below is a submodule. -/
noncomputable def coarseningLift
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full] :
    ↥(L2ZeroMean (P_full.map M)) →L[ℝ] Lp ℝ 2 P_full :=
  (lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›) 2 P_full).subtypeL.comp
    ((doobL2Equiv hM).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (L2ZeroMean (P_full.map M)).subtypeL)

set_option linter.unusedVariables false in
/-- *Nonparametric observed Y-tangent* (vdV §25.5.3 / thm:25.40).

The mean-zero `σ(πY)`-measurable full-data scores, i.e. the intersection of
`L²₀(P_full)` with the `σ(πY)`-measurable subspace
`lpMeas ℝ ℝ (comap πY) 2 P_full`, pulled back to `↥(L²₀(P_full))` along the
subtype embedding.

Constitutive (vdV §25.5.3, p.379): when the distribution `Q` of the full
observation `Y = πY` is left "completely unspecified", the `Y`-tangent set is
the maximal nonparametric set of mean-zero functions of `Y`; taking `E(·|X)` of
it (`observedTangent`) produces the observed conditional-expectation piece
`Π a = E_{Q,R}(a(Y) | X = x)` of thm:25.40. The observed-Y coordinate is encoded
by the measurable projection `πY : Ω_full → Ω_Y`; its σ-algebra
`σ(πY) = MeasurableSpace.comap πY _` is a genuine sub-σ-algebra of the ambient
one (`hπY.comap_le`). -/
noncomputable def nonparametricYTangent
    {πY : Ω_full → Ω_Y} (hπY : Measurable πY)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full] :
    Submodule ℝ ↥(L2ZeroMean P_full) :=
  (lpMeas ℝ ℝ (MeasurableSpace.comap πY ‹MeasurableSpace Ω_Y›) 2 P_full).comap
    (L2ZeroMean P_full).subtype

open AsymptoticStatistics.ForMathlib.CondExpL2 in
/-- *Coarsening-score space `Ṙ`* (vdV thm:25.40 conclusion).

The kernel of the continuous linear map `b ↦ E(doobSymm b | Y)`, where
`doobSymm b = coarseningLift hM P_full b` is the `M`-measurable Doob lift and
`E(· | Y) = condExpL2 ℝ ℝ hπY.comap_le` is the conditional expectation onto
`σ(πY)`. So `b ∈ coarseningScoreSpace ↔ E_R(doobSymm b | Y) = 0`.

Constitutive (vdV thm:25.40, p.380): the theorem's coarsening scores are the
`b ∈ L²(P_{Q,R})` with `E_R(b(X) | Y) = 0`. Here `E_R(b(X) | Y) = 0` is
rendered as `condExpL2 ℝ ℝ hπY.comap_le (doobSymm b) = 0`.

Identifying this abstract Hilbert space with the actual `R`-model
conditional-density scores requires a conditional-density QMD model; that
identification, rather than this definition, is where CAR does its constructive
work. -/
noncomputable def coarseningScoreSpace
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    {πY : Ω_full → Ω_Y} (hπY : Measurable πY)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full] :
    Submodule ℝ ↥(L2ZeroMean (P_full.map M)) :=
  LinearMap.ker
    (((lpMeas ℝ ℝ (MeasurableSpace.comap πY ‹MeasurableSpace Ω_Y›) 2 P_full).subtypeL.comp
        ((condExpL2 ℝ ℝ hπY.comap_le).comp (coarseningLift hM P_full))).toLinearMap)

/-- Membership in the coarsening-score space unfolds to
`E_R(doobSymm b | Y) = 0` at the `Lp` level. -/
theorem mem_coarseningScoreSpace_iff
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    {πY : Ω_full → Ω_Y} (hπY : Measurable πY)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    (b : ↥(L2ZeroMean (P_full.map M))) :
    b ∈ coarseningScoreSpace hM hπY P_full
      ↔ (condExpL2 ℝ ℝ hπY.comap_le (coarseningLift hM P_full b) : Lp ℝ 2 P_full) = 0 := by
  rw [coarseningScoreSpace, LinearMap.mem_ker]
  rfl

open AsymptoticStatistics.ForMathlib.CondExpL2 in
/-- *Adjoint identity in `coarseningLift` form.* The `L²(P_obs)`-pairing of the
conditional-expectation piece `Π a` against an observed function `b` equals the
`L²(P_full)`-pairing of `a` against the Doob lift `coarseningLift hM P_full b`.
This is `inner_observedTangent_piece` folded through the definition of
`coarseningLift`. -/
theorem inner_observedTangent_coarseningLift
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    (a : ↥(L2ZeroMean P_full)) (b : ↥(L2ZeroMean (P_full.map M))) :
    ⟪(informationLossOperator hM P_full a : Lp ℝ 2 (P_full.map M)),
        (b : Lp ℝ 2 (P_full.map M))⟫_ℝ
      = ⟪(a : Lp ℝ 2 P_full), coarseningLift hM P_full b⟫_ℝ := by
  rw [inner_observedTangent_piece hM P_full a (b : Lp ℝ 2 (P_full.map M))]
  rfl

open AsymptoticStatistics.ForMathlib.CondExpL2 in
/-- *The central organizing fact of vdV thm:25.40 (CAR-free).*

The coarsening-score space equals the orthogonal complement of the observed
Y-tangent:
`coarseningScoreSpace = (observedTangent hM P_full (nonparametricYTangent hπY P_full))ᗮ`.

`⊆` is the orthogonality `⟪Π a, b⟫ = ⟪E(doobSymm b | Y), a⟫ = 0` (adjoint
identity `inner_observedTangent_coarseningLift` + `condExpL2` self-adjointness
`inner_condExpL2_eq_inner_fun`); `⊇` is density: if `b ⊥ Π a` for all `a`,
taking `a = E(doobSymm b | Y)` (mean-zero, `σ(πY)`-measurable) forces
`⟪E(doobSymm b | Y), E(doobSymm b | Y)⟫ = 0`, hence `E(doobSymm b | Y) = 0`.
-/
theorem coarseningScoreSpace_eq_observedTangent_orthogonal
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    {πY : Ω_full → Ω_Y} (hπY : Measurable πY)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full] :
    coarseningScoreSpace hM hπY P_full
      = (observedTangent hM P_full (nonparametricYTangent hπY P_full))ᗮ := by
  haveI : IsProbabilityMeasure (P_full.map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  apply Submodule.ext
  intro b
  -- The adjoint identity `⟪Π a, b⟫ = ⟪E(doobSymm b | Y), a⟫` for any `σ(πY)`-measurable `a`.
  have star : ∀ a : ↥(L2ZeroMean P_full),
      (a : Lp ℝ 2 P_full) ∈
          lpMeas ℝ ℝ (MeasurableSpace.comap πY ‹MeasurableSpace Ω_Y›) 2 P_full →
      ⟪(informationLossOperator hM P_full a : Lp ℝ 2 (P_full.map M)),
          (b : Lp ℝ 2 (P_full.map M))⟫_ℝ
        = ⟪(condExpL2 ℝ ℝ hπY.comap_le (coarseningLift hM P_full b) : Lp ℝ 2 P_full),
            (a : Lp ℝ 2 P_full)⟫_ℝ := by
    intro a ha
    rw [inner_observedTangent_coarseningLift hM P_full a b,
      inner_condExpL2_eq_inner_fun hπY.comap_le (coarseningLift hM P_full b) (a : Lp ℝ 2 P_full)
        (mem_lpMeas_iff_aestronglyMeasurable.mp ha)]
    exact real_inner_comm (coarseningLift hM P_full b) (a : Lp ℝ 2 P_full)
  constructor
  · -- `⊆`: coarsening scores are orthogonal to the observed Y-tangent.
    intro hb
    rw [Submodule.mem_orthogonal]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_observedTangent_iff hM P_full _ x).mp hx
    rw [Submodule.coe_inner]
    have ha' : (a : Lp ℝ 2 P_full) ∈
        lpMeas ℝ ℝ (MeasurableSpace.comap πY ‹MeasurableSpace Ω_Y›) 2 P_full :=
      Submodule.mem_comap.mp ha
    rw [star a ha', (mem_coarseningScoreSpace_iff hM hπY P_full b).mp hb]
    exact inner_zero_left _
  · -- `⊇`: anything orthogonal to the observed Y-tangent is a coarsening score.
    intro hb
    rw [mem_coarseningScoreSpace_iff]
    have hmz : (condExpL2 ℝ ℝ hπY.comap_le (coarseningLift hM P_full b) : Lp ℝ 2 P_full)
        ∈ L2ZeroMean P_full := by
      rw [mem_L2ZeroMean_iff]
      have h1 : ∫ a, (condExpL2 ℝ ℝ hπY.comap_le (coarseningLift hM P_full b)
              : Lp ℝ 2 P_full) a ∂P_full
          = ∫ a, (coarseningLift hM P_full b) a ∂P_full := by
        simpa using integral_condExpL2_eq hπY.comap_le (coarseningLift hM P_full b)
          MeasurableSet.univ (measure_ne_top P_full Set.univ)
      rw [h1]
      have hbe : (fun a => (b : Lp ℝ 2 (P_full.map M)) (M a)) =ᵐ[P_full]
          (coarseningLift hM P_full b) := by
        have hsymm := doobL2Equiv_comp_apply hM
          ((doobL2Equiv hM).symm (b : Lp ℝ 2 (P_full.map M)))
        rw [LinearIsometryEquiv.apply_symm_apply] at hsymm
        exact hsymm
      rw [integral_congr_ae hbe.symm,
        ← integral_map hM.aemeasurable (Lp.aestronglyMeasurable _)]
      exact (mem_L2ZeroMean_iff (P_full.map M) (b : Lp ℝ 2 (P_full.map M))).mp b.2
    have hlpm : (condExpL2 ℝ ℝ hπY.comap_le (coarseningLift hM P_full b) : Lp ℝ 2 P_full)
        ∈ lpMeas ℝ ℝ (MeasurableSpace.comap πY ‹MeasurableSpace Ω_Y›) 2 P_full :=
      SetLike.coe_mem _
    have ha_h_np :
        (⟨(condExpL2 ℝ ℝ hπY.comap_le (coarseningLift hM P_full b) : Lp ℝ 2 P_full), hmz⟩ :
            ↥(L2ZeroMean P_full)) ∈ nonparametricYTangent hπY P_full := by
      rw [nonparametricYTangent, Submodule.mem_comap]
      exact hlpm
    have hstar := star
      (⟨(condExpL2 ℝ ℝ hπY.comap_le (coarseningLift hM P_full b) : Lp ℝ 2 P_full), hmz⟩ :
        ↥(L2ZeroMean P_full)) hlpm
    have hPi0 :
        ⟪(informationLossOperator hM P_full
            (⟨(condExpL2 ℝ ℝ hπY.comap_le (coarseningLift hM P_full b) : Lp ℝ 2 P_full), hmz⟩ :
              ↥(L2ZeroMean P_full)) : Lp ℝ 2 (P_full.map M)),
            (b : Lp ℝ 2 (P_full.map M))⟫_ℝ = 0 := by
      have hmem := (Submodule.mem_orthogonal _ _).mp hb _
        (informationLossOperator_mem_observedTangent hM P_full _ ha_h_np)
      rwa [Submodule.coe_inner] at hmem
    rw [hPi0] at hstar
    exact inner_self_eq_zero.mp hstar.symm

open AsymptoticStatistics.ForMathlib.CondExpL2 in
/-- *Orthogonality half of vdV thm:25.40.* The observed conditional-expectation
pieces `Π a` (`a` a nonparametric Y-score) are orthogonal to every coarsening
score. Derived from the central identity via `Submodule.mem_orthogonal`. -/
theorem inner_observedTangent_coarseningScore_eq_zero
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    {πY : Ω_full → Ω_Y} (hπY : Measurable πY)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full] :
    ∀ a ∈ nonparametricYTangent hπY P_full, ∀ b ∈ coarseningScoreSpace hM hπY P_full,
      ⟪(informationLossOperator hM P_full a : Lp ℝ 2 (P_full.map M)),
          (b : Lp ℝ 2 (P_full.map M))⟫_ℝ = 0 := by
  intro a ha b hb
  have hbperp : b ∈ (observedTangent hM P_full (nonparametricYTangent hπY P_full))ᗮ := by
    rw [← coarseningScoreSpace_eq_observedTangent_orthogonal hM hπY P_full]
    exact hb
  have hmem := (Submodule.mem_orthogonal _ _).mp hbperp (informationLossOperator hM P_full a)
    (informationLossOperator_mem_observedTangent hM P_full _ ha)
  rwa [Submodule.coe_inner] at hmem

open AsymptoticStatistics.ForMathlib.CondExpL2 in
/-- *vdV thm:25.40 — observed-tangent orthogonal decomposition + density (CAR-free).*

The content of thm:25.40 at the Hilbert-closure level:

  1. **Orthogonality.** Every observed conditional-expectation piece `Π a`
     (`a` a nonparametric Y-score) is orthogonal to every coarsening score `b`
     (`E_R(doobSymm b | Y) = 0`).
  2. **Density.** The join of the observed Y-tangent and the coarsening-score
     space is dense: its topological closure is all of `L²₀(P_obs)` (vdV's
     "the closure consists of all mean-zero functions"). This is automatic from
     the central fact `coarseningScoreSpace = (observedTangent …)ᗮ`, since
     `V ⊔ Vᗮ` is dense in a Hilbert space.

The Hilbert geometry is CAR-free, so no CAR hypothesis is needed. CAR's
constructive content is the separate identification of `coarseningScoreSpace`
with actual `R`-model conditional-density scores. The observed-Y coordinate
`πY : Ω_full → Ω_Y` (with
`hπY : Measurable πY`) is a genuine model-structure input: `σ(πY)` is the "full
observation `Y`" σ-algebra. -/
theorem observedTangent_carScore_factors
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    {πY : Ω_full → Ω_Y} (hπY : Measurable πY)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full] :
    (∀ a ∈ nonparametricYTangent hπY P_full, ∀ b ∈ coarseningScoreSpace hM hπY P_full,
       ⟪(informationLossOperator hM P_full a : Lp ℝ 2 (P_full.map M)),
           (b : Lp ℝ 2 (P_full.map M))⟫_ℝ = 0)
    ∧ (observedTangent hM P_full (nonparametricYTangent hπY P_full)
         ⊔ coarseningScoreSpace hM hπY P_full).topologicalClosure = ⊤ := by
  haveI : IsProbabilityMeasure (P_full.map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  haveI hcsE : CompleteSpace ↥(L2ZeroMean (P_full.map M)) :=
    (L2ZeroMean_isClosed (P_full.map M)).completeSpace_coe
  refine ⟨inner_observedTangent_coarseningScore_eq_zero hM hπY P_full, ?_⟩
  -- Density: `closure (V ⊔ Vᗮ) = ⊤ ↔ (V ⊔ Vᗮ)ᗮ = ⊥`, and `(V ⊔ Vᗮ)ᗮ = Vᗮ ⊓ Vᗮᗮ = ⊥`.
  -- The ambient `CompleteSpace` is supplied explicitly (`hcsE`): the submodule-subtype
  -- instance is not recovered by search in this file's instance environment.
  rw [coarseningScoreSpace_eq_observedTangent_orthogonal hM hπY P_full]
  refine (@Submodule.topologicalClosure_eq_top_iff ℝ _ _ _ _ _ hcsE).mpr ?_
  rw [← Submodule.inf_orthogonal]
  exact Submodule.inf_orthogonal_eq_bot
    (observedTangent hM P_full (nonparametricYTangent hπY P_full))ᗮ

open AsymptoticStatistics.ForMathlib.CondExpL2 in
/-- *Explicit per-`g` orthogonal decomposition* (vdV thm:25.40, closure
form). Every observed score `g ∈ L²₀(P_obs)` splits as `g = p + b` with `p` in
the closure of the observed Y-tangent, `b` a coarsening score, and `p ⊥ b`.

`p` is `g` minus its orthogonal projection onto the (closed) coarsening-score
space `Ṙ = Vᗮ`; then `p ∈ Vᗮᗮ = closure V`. -/
theorem observedTangent_decomp
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    {πY : Ω_full → Ω_Y} (hπY : Measurable πY)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    (g : ↥(L2ZeroMean (P_full.map M))) :
    ∃ p ∈ (observedTangent hM P_full (nonparametricYTangent hπY P_full)).topologicalClosure,
      ∃ b ∈ coarseningScoreSpace hM hπY P_full,
      g = p + b ∧
      ⟪(p : Lp ℝ 2 (P_full.map M)), (b : Lp ℝ 2 (P_full.map M))⟫_ℝ = 0 := by
  haveI : IsProbabilityMeasure (P_full.map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  haveI hcsE : CompleteSpace ↥(L2ZeroMean (P_full.map M)) :=
    (L2ZeroMean_isClosed (P_full.map M)).completeSpace_coe
  -- `coarseningScoreSpace` is the kernel of a continuous linear map, hence closed,
  -- hence complete in the complete ambient. The submodule-subtype `CompleteSpace`
  -- and the induced `HasOrthogonalProjection` are supplied explicitly (`hcsop`),
  -- since search does not recover them in this file's instance environment; the
  -- projection lemmas below are then applied with the instance passed by `@`.
  have hclosed : IsClosed (↑(coarseningScoreSpace hM hπY P_full) :
      Set ↥(L2ZeroMean (P_full.map M))) := by
    rw [coarseningScoreSpace]
    exact ContinuousLinearMap.isClosed_ker _
  haveI hcs_complete : CompleteSpace ↥(coarseningScoreSpace hM hπY P_full) :=
    @IsClosed.completeSpace_coe _ _ hcsE _ hclosed
  haveI hcsop : (coarseningScoreSpace hM hπY P_full).HasOrthogonalProjection :=
    @Submodule.HasOrthogonalProjection.ofCompleteSpace ℝ _ _ _ _
      (coarseningScoreSpace hM hπY P_full) hcs_complete
  refine ⟨g - @Submodule.starProjection ℝ _ _ _ _
        (coarseningScoreSpace hM hπY P_full) hcsop g, ?_,
    @Submodule.starProjection ℝ _ _ _ _ (coarseningScoreSpace hM hπY P_full) hcsop g,
    @Submodule.starProjection_apply_mem ℝ _ _ _ _
      (coarseningScoreSpace hM hπY P_full) hcsop g, ?_, ?_⟩
  · -- `g - proj g ∈ Vᗮᗮ = closure V`.  Rewrite only the *ambient* `Ṙᗮ` set to
    -- `closure V`, leaving the `starProjection`'s `coarseningScoreSpace` untouched.
    have horth := @Submodule.sub_starProjection_mem_orthogonal ℝ _ _ _ _
      (coarseningScoreSpace hM hπY P_full) hcsop g
    have hcl : (coarseningScoreSpace hM hπY P_full)ᗮ
        = (observedTangent hM P_full (nonparametricYTangent hπY P_full)).topologicalClosure := by
      rw [coarseningScoreSpace_eq_observedTangent_orthogonal hM hπY P_full]
      exact @Submodule.orthogonal_orthogonal_eq_closure ℝ _ _ _ _
        (observedTangent hM P_full (nonparametricYTangent hπY P_full)) hcsE
    rwa [hcl] at horth
  · -- `g = (g - proj g) + proj g`.
    abel
  · -- `⟪g - proj g, proj g⟫ = 0`: `g - proj g ∈ Ṙᗮ` and `proj g ∈ Ṙ`.
    have horth := @Submodule.sub_starProjection_mem_orthogonal ℝ _ _ _ _
      (coarseningScoreSpace hM hπY P_full) hcsop g
    have h0 := (Submodule.mem_orthogonal' _ _).mp horth
      (@Submodule.starProjection ℝ _ _ _ _ (coarseningScoreSpace hM hπY P_full) hcsop g)
      (@Submodule.starProjection_apply_mem ℝ _ _ _ _
        (coarseningScoreSpace hM hπY P_full) hcsop g)
    rwa [Submodule.coe_inner] at h0

/-! ## Observed-data efficient-influence decomposition (vdV cor:25.42)

vdV §25.6, cor:25.42 (book p.382). In the observed-data problem under CAR, any
observed-data influence function equals (the IPW form, lem:25.41) minus its
orthogonal projection onto the nuisance coarsening-score space `lin Ṙ_{Q,R}`.
The Hilbert content is the abstract subtract-projection-onto-observed-nuisance engine
(`Core.EIF.influence_on_sup_of_subtract_proj_nuisance`) instantiated at the
*observed* measure `P_full.map M` and the *observed* tangent spaces: the observed
main tangent `T_main_obs` and the observed nuisance (coarsening-score) tangent
`T_nuis_obs`. The IPW-specific influence form (lem:25.41) and the explicit
variance-loss term of cor:25.42 additionally require conditional-density-score
machinery. -/

open AsymptoticStatistics.Operators.InformationLoss in
/-- *Observed-data efficient-influence decomposition* (vdV cor:25.42, observed-data
Hilbert form).

Work in the observed `L²₀(P_obs)` with `P_obs = P_full.map M`. Suppose the observed
tangent splits as `T_main_obs ⊔ T_nuis_obs`, where `T_nuis_obs` is the observed
*nuisance* (coarsening-score) space `lin Ṙ_{Q,R}` and `T_main_obs ⊥ T_nuis_obs`. If
the observed representer `φ₀_obs` represents the observed derivative `dψ_obs` on
`T_main_obs`, and `dψ_obs` vanishes on `T_nuis_obs`, then subtracting the
projection of `φ₀_obs` onto the nuisance space yields an influence function for
`dψ_obs` on the whole observed tangent `T_main_obs ⊔ T_nuis_obs`:

  `φ₀_obs - T_nuis_obs.starProjection φ₀_obs`  is an influence function.

This is `Core.EIF.influence_on_sup_of_subtract_proj_nuisance` instantiated at the
observed measure `P_full.map M`. It ties the abstract subtract-projection engine to
the CAR observed-data setting and captures cor:25.42's Hilbert content.

The IPW-specific form of the influence function (lem:25.41, identifying
`φ₀_obs` with `Π φ_full` for a full-data influence function `φ_full`), and the
explicit variance-loss term of cor:25.42 (`‖projection onto Ṙ_{Q,R}‖²`), require
the additional conditional-density-score theory.

The `[T_nuis_obs.HasOrthogonalProjection]` hypothesis is the standard
orthogonal-projection side-condition (automatic when `T_nuis_obs` is closed in the
complete space `↥(L²₀(P_obs))`); the observed measure `P_full.map M` is a
probability measure by `Measure.isProbabilityMeasure_map`. -/
theorem observedData_influence_subtract_proj
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    -- `IsProbabilityMeasure (P_full.map M)` is forced by `hM` (via
    -- `Measure.isProbabilityMeasure_map`); it is taken as a local instance with
    -- `letI` so the conclusion `IsInfluenceFunction (P_full.map M) …` elaborates,
    -- but it is NOT a free input — it is discharged from `hM` below.
    {T_main_obs T_nuis_obs : Submodule ℝ ↥(L2ZeroMean (P_full.map M))}
    [T_nuis_obs.HasOrthogonalProjection]
    {dψ_obs :
      (T_main_obs ⊔ T_nuis_obs : Submodule ℝ ↥(L2ZeroMean (P_full.map M))) →L[ℝ] ℝ}
    {φ₀_obs : ↥(L2ZeroMean (P_full.map M))}
    (hOrth : ∀ u ∈ T_main_obs, ∀ v ∈ T_nuis_obs, ⟪u, v⟫_ℝ = (0 : ℝ))
    (hMain : ∀ (u : ↥(L2ZeroMean (P_full.map M))) (hu : u ∈ T_main_obs),
        ⟪φ₀_obs, u⟫_ℝ = dψ_obs ⟨u, Submodule.mem_sup_left hu⟩)
    (hZero : ∀ (v : ↥(L2ZeroMean (P_full.map M))) (hv : v ∈ T_nuis_obs),
        dψ_obs ⟨v, Submodule.mem_sup_right hv⟩ = 0) :
    letI : IsProbabilityMeasure (P_full.map M) :=
      Measure.isProbabilityMeasure_map hM.aemeasurable
    AsymptoticStatistics.Core.Pathwise.IsInfluenceFunction (P_full.map M)
      (T_main_obs ⊔ T_nuis_obs) dψ_obs
      (φ₀_obs - T_nuis_obs.starProjection φ₀_obs) := by
  haveI hp : IsProbabilityMeasure (P_full.map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  exact @AsymptoticStatistics.Core.EIF.influence_on_sup_of_subtract_proj_nuisance
    _ _ (P_full.map M) hp T_main_obs T_nuis_obs _ dψ_obs φ₀_obs hOrth hMain hZero

end AsymptoticStatistics.Operators.CAR
