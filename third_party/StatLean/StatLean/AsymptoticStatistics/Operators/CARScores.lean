module
public import StatLean.AsymptoticStatistics.Operators.CAR
public import StatLean.AsymptoticStatistics.Operators.CoarsenedQMD

@[expose] public section

/-!
# CAR observed-tangent decomposition and IPW influence functions (vdV §25.5.3)

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.5.3:
thm:25.40 (book p.380 — observed tangent = Q-score images ⊕ coarsening scores)
and lem:25.41 (book p.381-382 — the IPW form of an observed influence function).

Here `b` is constrained to the *coarsening-score space* `coarseningScores`, the
orthogonal complement of the observed image of the Q-model tangent.

## Why the complement is taken against the *Q-model* image, not all of `Π`

Over a generic `P_full`, `Π = informationLossOperator hM P_full` is **surjective**
(pull an observed `g` back to the `M`-measurable full-data function `g ∘ M`, whose
`Π`-image is `g`), so `(range Π)ᗮ = {0}` — the coarsening piece would be trivial.
The book's non-trivial `b` piece arises because `Π` is applied to the **Q-model
tangent** `fullTangent` (scores that are functions of `Y` with `Qa = 0`), a proper
subspace. Hence `coarseningScores := (observedTangent hM P_full fullTangent)ᗮ`.

## Why closure enters the decomposition

The observed tangent *set* `Π '' fullTangent` need not be closed; thm:25.40 is a
statement about its **closure** being all mean-zero `L²(P_obs)`. The exact
orthogonal decomposition therefore splits `g` against the closed subspace
`(observedTangent …).topologicalClosure`, matching vdV's "the closure consists of
all mean-zero functions".

Headline declarations: `coarseningScores`, `observedTangent_orthogonal_decomposition`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

set_option linter.dupNamespace false

namespace AsymptoticStatistics.Operators.CARScores

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Operators.InformationLoss
open AsymptoticStatistics.Operators.CAR
open ProbabilityTheory

variable {Ω_full Ω_obs : Type*}
  [MeasurableSpace Ω_full] [MeasurableSpace Ω_obs]

/-- *Coarsening-score space* `Ṙ_{Q,R}` (vdV §25.5.3, book p.380).

The observed scores orthogonal to the whole observed image of the Q-model tangent,
`coarseningScores := (observedTangent hM P_full fullTangent)ᗮ`. Under CAR (bridged
by `ParametricFamily.CARScore.conditionalScore_factorsThrough` +
`ForMathlib.ConditionalQMD.conditionalScore_fibre_mean_zero`) these are exactly the
scores `b(x)` that are functions of the observed data with `E_R(b(X) | Y) = 0` a.s.
— the orthogonality `⟪E(a(Y)|X), b⟫ = E[a(Y)·E_R(b|Y)] = 0` is the abstract shadow
of `E_R(b | Y) = 0`. -/
noncomputable def coarseningScores {M : Ω_full → Ω_obs} (hM : Measurable M)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    (fullTangent : Submodule ℝ ↥(L2ZeroMean P_full)) :
    Submodule ℝ ↥(L2ZeroMean (P_full.map M)) :=
  (observedTangent hM P_full fullTangent)ᗮ

/-! ### Orthogonality of the two pieces -/

/-- *Coarsening scores are orthogonal to the observed Q-score image* (vdV
§25.5.3, the orthogonality engine of thm:25.40).

For a Q-model score `a ∈ fullTangent`, the conditional-expectation piece
`Π a = E_{Q,R}(a(Y) | X)` pairs to zero with every coarsening score `b`. This is
the abstract form of vdV's tower identity `⟪E(a(Y)|X), b⟫ = E[a(Y)·E_R(b|Y)] = 0`;
it follows from `b ∈ (observedTangent fullTangent)ᗮ` together with
`Operators.CAR.inner_observedTangent_piece`, and supplies the orthogonality used
in the decomposition `g = Π a + b`. -/
theorem inner_observedTangent_coarseningScore_eq_zero
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    (fullTangent : Submodule ℝ ↥(L2ZeroMean P_full))
    {a : ↥(L2ZeroMean P_full)} (ha : a ∈ fullTangent)
    {b : ↥(L2ZeroMean (P_full.map M))}
    (hb : b ∈ coarseningScores hM P_full fullTangent) :
    ⟪(informationLossOperator hM P_full a : Lp ℝ 2 (P_full.map M)),
        (b : Lp ℝ 2 (P_full.map M))⟫_ℝ = 0 := by
  -- `Π a ∈ observedTangent`; `b ∈ (observedTangent)ᗮ = coarseningScores`.
  -- The `L²`-inner and the subtype inner agree definitionally (`Submodule.coe_inner`).
  rw [← Submodule.coe_inner]
  exact Submodule.inner_right_of_mem_orthogonal
    (informationLossOperator_mem_observedTangent hM P_full fullTangent ha) hb

/-! ### Density and closure via orthogonality -/

/-- *An observed score orthogonal to both pieces is zero* (vdV §25.5.3, thm:25.40
¶2 density half).

If a mean-zero observed score `g` is orthogonal to the whole observed Q-score image
(`observedTangent hM P_full fullTangent`) and to every coarsening score, then
`g = 0`. This is the closure statement of thm:25.40: the observed image of the
Q-model tangent together with the coarsening scores spans a dense subspace, so
nothing nonzero is orthogonal to both. Self-contained: `g ⊥ observedTangent`
places `g ∈ (observedTangent)ᗮ = coarseningScores`, and then `g ⊥ coarseningScores`
forces `⟪g, g⟫ = 0`. -/
theorem observedScore_eq_zero_of_orthogonal
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    (fullTangent : Submodule ℝ ↥(L2ZeroMean P_full))
    (g : ↥(L2ZeroMean (P_full.map M)))
    (h_tangent : ∀ p ∈ observedTangent hM P_full fullTangent,
        ⟪(p : Lp ℝ 2 (P_full.map M)), (g : Lp ℝ 2 (P_full.map M))⟫_ℝ = 0)
    (h_coarse : ∀ b ∈ coarseningScores hM P_full fullTangent,
        ⟪(b : Lp ℝ 2 (P_full.map M)), (g : Lp ℝ 2 (P_full.map M))⟫_ℝ = 0) :
    g = 0 := by
  -- `g ⊥ observedTangent` places `g ∈ (observedTangent)ᗮ = coarseningScores`.
  have hg_mem : g ∈ coarseningScores hM P_full fullTangent := by
    rw [coarseningScores, Submodule.mem_orthogonal]
    intro u hu
    -- goal `⟪u, g⟫` is the subtype inner; `h_tangent` is stated at the `Lp` level.
    rw [Submodule.coe_inner]
    exact h_tangent u hu
  -- Then `g ⊥ coarseningScores` at `b := g` forces `⟪g, g⟫ = 0`, hence `g = 0`.
  have hgg : (g : Lp ℝ 2 (P_full.map M)) = 0 :=
    inner_self_eq_zero.mp (h_coarse g hg_mem)
  exact Submodule.coe_eq_zero.mp hgg

/-! ### Orthogonal decomposition -/

/-- *vdV thm:25.40 — observed-tangent orthogonal decomposition* (book p.380).

Every mean-zero observed score `g ∈ L²₀(P_obs)` decomposes orthogonally as
`g = p + b`, where:
  * `p ∈ (observedTangent hM P_full fullTangent).topologicalClosure` — a limit of
    conditional-expectation images `E_{Q,R}(a(Y) | X)` of Q-model scores
    `a ∈ fullTangent` (the closure is genuine: the tangent *set* need not be
    closed, exactly as vdV states the theorem for the closure), and
  * `b ∈ coarseningScores hM P_full fullTangent` — a coarsening score,

with `p ⊥ b`. Both witnesses are constrained: `p` belongs to the closed observed
Q-score image and `b` to its orthogonal complement. This is the
orthogonal-decomposition theorem for the
closed subspace `(observedTangent …).topologicalClosure`; the identification of `p`
with a genuine `E(a(Y)|X)` and of `b` with a genuine `E_R(b|Y)=0` coarsening score
is delivered by the conditional-density bridge and the choice of
`fullTangent` as the Q-model tangent.

CAR does not appear as a hypothesis here: over the abstract `(P_full, M)` this is a
pure Hilbert-space decomposition. CAR is what makes `fullTangent` the Q-model
tangent and `coarseningScores` the `E_R(b|Y)=0` scores — that content lives in the
conditional layer (`ParametricFamily.CARScore`). -/
theorem observedTangent_orthogonal_decomposition
    {M : Ω_full → Ω_obs} (hM : Measurable M)
    (P_full : Measure Ω_full) [IsProbabilityMeasure P_full]
    (fullTangent : Submodule ℝ ↥(L2ZeroMean P_full))
    (g : ↥(L2ZeroMean (P_full.map M))) :
    ∃ p ∈ (observedTangent hM P_full fullTangent).topologicalClosure,
      ∃ b ∈ coarseningScores hM P_full fullTangent,
        g = p + b ∧
        ⟪(p : Lp ℝ 2 (P_full.map M)), (b : Lp ℝ 2 (P_full.map M))⟫_ℝ = 0 := by
  -- The observed space `↥(L²₀(P_obs))` is complete (closed subspace of `Lp`),
  -- so the closed subspace `S̄ := (observedTangent …).topologicalClosure`
  -- admits an orthogonal projection.
  haveI : IsProbabilityMeasure (P_full.map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  haveI : CompleteSpace ↥(L2ZeroMean (P_full.map M)) := by
    haveI := L2ZeroMean_isClosed (P_full.map M)
    exact IsClosed.completeSpace_coe
  -- `S̄ := (observedTangent …).topologicalClosure` is closed, hence complete,
  -- hence admits an orthogonal projection.
  haveI hcs : CompleteSpace
      ↥((observedTangent hM P_full fullTangent).topologicalClosure) := by
    haveI := Submodule.isClosed_topologicalClosure (observedTangent hM P_full fullTangent)
    exact IsClosed.completeSpace_coe
  haveI hproj :
      (observedTangent hM P_full fullTangent).topologicalClosure.HasOrthogonalProjection :=
    @Submodule.HasOrthogonalProjection.ofCompleteSpace ℝ _ _ _ _
      (observedTangent hM P_full fullTangent).topologicalClosure hcs
  -- `p := S̄.starProjection g ∈ S̄`, `b := g - p ∈ S̄ᗮ ⊆ (observedTangent)ᗮ`.
  set S := (observedTangent hM P_full fullTangent).topologicalClosure with hS
  refine ⟨S.starProjection g, S.starProjection_apply_mem g,
    g - S.starProjection g, ?_, ?_, ?_⟩
  · -- `S̄ᗮ ≤ (observedTangent)ᗮ = coarseningScores` since `observedTangent ≤ S̄`.
    exact Submodule.orthogonal_le (Submodule.le_topologicalClosure _)
      (S.sub_starProjection_mem_orthogonal g)
  · -- `g = p + (g - p)`.
    abel
  · -- Projection orthogonality: `p ∈ S̄`, `g - p ∈ S̄ᗮ`.
    rw [← Submodule.coe_inner]
    exact Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem g)
      (S.sub_starProjection_mem_orthogonal g)

end AsymptoticStatistics.Operators.CARScores
