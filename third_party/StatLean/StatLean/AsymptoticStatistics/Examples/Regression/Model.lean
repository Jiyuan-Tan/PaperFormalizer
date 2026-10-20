module
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScore

@[expose] public section

/-!
# The regression observation type, ordinary score, and error-shape geometry

The model-setup half of the concrete-EIF verification for the **regression
model** of van der Vaart, *Asymptotic Statistics* (Cambridge, 1998),
Example 25.28 (§25.4, p.370-371).

## The book model (vdV Example 25.28)

Let `g_θ` be a family of regression functions indexed by `θ ∈ ℝ^k`, and let a
typical observation `(X, Y)` follow

    Y = g_θ(X) + e,     E(e | X) = 0.

`X` and the error `e` need not be independent; only `E(e | X) = 0` and
qualitative smoothness/moment conditions are assumed. Writing `(X, e)` with a
density `η`, the observation `(X, Y)` has density `η(x, y − g_θ(x))`, where `η`
is (essentially) only restricted by `∫ e·η(x, e) de = 0`.

The nuisance scores are the mean-zero functions `a(x, y − g_θ(x))` with
`E(e·a(X, e) | X) = 0`, i.e. the orthocomplement (up to centering) of the
**error-shape** space `ēH = { (x,y) ↦ (y − g_θ(x))·h(x) }` inside
`L²(P_{θ,η})`. The ordinary θ-score is `ℓ̇_{θ,η}(x, y) = −(η₂/η)(x, e)·ġ_θ(x)`
with `e = y − g_θ(x)`. Its efficient part (the component in `ēH`) is obtained
by the integration-by-parts identity `∫ η₂(x,e)·e de = −∫ η(x,e) de`, which
yields the **efficient score**

    ℓ̃_{θ,η}(X, Y) = (Y − g_θ(X))·ġ_θ(X) / E(e² | X),

with **efficient information** `Ĩ_{θ,η} = E( ġ_θ ġ_θᵀ(X) / E(e² | X) )`.

This file fixes the scalar case `k = 1`, so `ġ_θ(X)` is a real number.

This file defines the observation type, the residual, the efficient-score
formula, the error-shape raw function, the ordinary-score operator (from a
user-supplied `L²₀(P)` score `ℓ̇`), and the model tangent space
`Ṗ = lin(ℓ̇) ⊔ T_nuis`. The efficient-influence-function claim is *derived* in
`EIF.lean` via `StrictModel.EfficientScore.eif_from_efficientScore'` (the
derived form of vdV Lemma 25.25); the integration-by-parts content enters as
named analytic identities (`hEmean`, `hSigma`, `hIBP` — vdV's "qualitative
smoothness conditions"), from which the efficient score `ℓ̃ = ℓ̇ − Π_nuis ℓ̇` is
*computed* to equal the display above.

Headline declarations: `RegObs`, `regression_error`,
`regression_efficientScore`, `regression_errorShape`, `regression_ordinaryScore`,
`regression_tangent`.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal
open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.StrictModel.EfficientScore

namespace AsymptoticStatistics.Examples.Regression

/-- The regression observation pair `(X, Y)`.

Fields:
- `x` — the covariate. Without it the regression function `g_θ(X)` cannot
  be evaluated.
- `y` — the real-valued response `Y = g_θ(X) + e`. Without it the outcome
  is unrecorded.

Reference: vdV Example 25.28 (the observation `(X, Y)` with
`Y = g_θ(X) + e`, `E(e | X) = 0`). -/
structure RegObs (X : Type*) where
  x : X
  y : ℝ

/-- The σ-algebra on `RegObs X` is the pullback of the product σ-algebra
under the projection `o ↦ (o.x, o.y)`. Makes the field accessors `x`, `y`
measurable from the product instances on `X` and `ℝ`. -/
instance instMeasurableSpaceRegObs
    {X : Type*} [MeasurableSpace X] : MeasurableSpace (RegObs X) :=
  MeasurableSpace.comap (fun o : RegObs X => (o.x, o.y))
    (inferInstance : MeasurableSpace (X × ℝ))

variable {X : Type*} [MeasurableSpace X]
variable {P : Measure (RegObs X)} [IsProbabilityMeasure P]

/-- The regression residual `e = Y − g_θ(X)` of an observation, given the
regression function `g = g_θ`.

Reference: vdV Example 25.28 (`e = Y − g_θ(X)`; the model imposes
`E(e | X) = 0`). -/
def regression_error (g : X → ℝ) (o : RegObs X) : ℝ := o.y - g o.x

/-- The **efficient score function** for `θ` in the regression model
(scalar `k = 1`):

    ℓ̃_{θ,η}(X, Y) = (Y − g_θ(X))·ġ_θ(X) / E(e² | X).

Here `g = g_θ` is the regression function, `gdot = ġ_θ` its derivative with
respect to `θ`, and `sigma2 = E(e² | X = ·)` the conditional error variance.

This is the ordinary θ-score minus its projection onto the nuisance tangent
space (the error-shape scores `ēH`), computed in vdV Example 25.28 by the
projection operator `Π_{ēH} b(X,e) = e · E(b(X,e)·e | X) / E(e² | X)` applied to
the ordinary score `−(η₂/η)(x,e)·ġ_θ(x)`; integration by parts in `e` collapses
the `η`-dependence, leaving the display above. It has mean zero because
`E[(Y − g_θ(X))·ġ_θ(X)/σ²(X)] = E[E(e | X)·ġ_θ(X)/σ²(X)] = 0`.

Reference: vdV Example 25.28, §25.4 p.370, the efficient score `ℓ̃_{θ,η}`. -/
noncomputable def regression_efficientScore
    (g gdot sigma2 : X → ℝ) (o : RegObs X) : ℝ :=
  (o.y - g o.x) * gdot o.x / sigma2 o.x

/-- An **error-shape function** `(x, y) ↦ (y − g_θ(x))·h(x) = e·h(X)`, the
generic member of the space `ēH`. The nuisance tangent space of the regression
model is the orthocomplement of the span of these functions.

Reference: vdV Example 25.28 — `ēH = { (x,y) ↦ (y − g_θ(x))·h(x) }`. -/
def regression_errorShape (g : X → ℝ) (h : X → ℝ) (o : RegObs X) : ℝ :=
  regression_error g o * h o.x

omit [MeasurableSpace X] in
/-- The efficient score is the error-shape function with `h = ġ/σ²`. -/
lemma regression_efficientScore_eq_errorShape (g gdot sigma2 : X → ℝ) (o : RegObs X) :
    regression_efficientScore g gdot sigma2 o
      = regression_errorShape g (fun x => gdot x / sigma2 x) o := by
  simp only [regression_efficientScore, regression_errorShape, regression_error]
  ring

/-- The **ordinary score operator** `S_θ : ℝ →L[ℝ] ↥(L²₀(P))`, `v ↦ v • ℓ̇`,
sending the θ-direction `v` to `v` times the ordinary θ-score
`ℓ̇ = −(η₂/η)·ġ_θ`. The score `ℓ̇` is supplied by the caller (it is the QMD
score of the parametric θ-submodel), exactly as in vdV §25.4.

Reference: vdV §25.4 / Example 25.28 — the ordinary score for `θ`. -/
noncomputable def regression_ordinaryScore (lscore : ↥(L2ZeroMean P)) :
    OrdinaryScore P ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ lscore

@[simp] lemma regression_ordinaryScore_one (lscore : ↥(L2ZeroMean P)) :
    regression_ordinaryScore lscore (1 : ℝ) = lscore :=
  ContinuousLinearMap.toSpanSingleton_apply_one ℝ lscore

@[simp] lemma regression_ordinaryScore_apply (lscore : ↥(L2ZeroMean P)) (v : ℝ) :
    regression_ordinaryScore lscore v = v • lscore :=
  ContinuousLinearMap.toSpanSingleton_apply ℝ lscore v

/-- The **model tangent space** `Ṗ = lin(ℓ̇) ⊔ T_nuis`: the span of the
ordinary θ-score together with the nuisance tangent space.

Reference: vdV §25.4, p.368 — the tangent set
`Ṗ_{P_{θ,η}} = lin(ℓ̇_θ) + η̇Ṗ`. -/
noncomputable def regression_tangent (lscore : ↥(L2ZeroMean P))
    (T_nuis : Submodule ℝ ↥(L2ZeroMean P)) :
    Submodule ℝ ↥(L2ZeroMean P) :=
  (ℝ ∙ lscore) ⊔ T_nuis

end AsymptoticStatistics.Examples.Regression
