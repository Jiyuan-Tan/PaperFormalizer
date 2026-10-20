module
public import StatLean.AsymptoticStatistics.Core.BoundedLinearFunctional

@[expose] public section

/-!
# The MAR observation type and the MAR-mean parameter functional

This file defines the `(X, R, RY)` observation tuple for missing-at-random data, the
inverse-probability-weighted (IPW) mean functional `marMean_Ψ`, and the raw
`MARObs X → ℝ` functions of Example 25.43 (the IPW representer, the MAR coarsening
scores, and the AIPW efficient influence function).

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.5.3 (CAR / MAR);
the observation tuple appears in lem:25.41 and ex:25.43.

Main declarations: `MARObs`, `marMean_Ψ`, `marMean_ipwRep`,
`marMean_coarseningScore`, `marMean_eif`.
-/

open MeasureTheory
open scoped InnerProductSpace
open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.MassMethod

namespace AsymptoticStatistics.Examples.MARMean

/-- The MAR observation tuple `(X, R, RY)`.

Fields:
- `x` — the always-observed covariate. Without it, no auxiliary
  information is captured.
- `r` — the response indicator (`true` if the response is observed,
  `false` otherwise). Without it, the observed/missing distinction
  is lost.
- `ry` — the partial response `R · Y`: equals `Y` when `r = true`,
  arbitrary (and unused by any well-posed estimator) when `r = false`.
  Without it, the actual outcome data is unrecorded.

Reference: vdV §25.6 (the `(X, Δ, ΔY)` tuple, with `Δ ∈ {0, 1}` the
missingness indicator). -/
structure MARObs (X : Type*) where
  x : X
  r : Bool
  ry : ℝ

/-- Boolean-to-real indicator: `ind true = 1`, `ind false = 0`. Used
to lift the observation indicator `r : Bool` into the AIPW formula
and the IPW functional. -/
def ind : Bool → ℝ
  | true => 1
  | false => 0

@[simp] theorem ind_true : ind true = (1 : ℝ) := rfl
@[simp] theorem ind_false : ind false = (0 : ℝ) := rfl

/-- The σ-algebra on `MARObs X` is the pullback of the product
σ-algebra under the obvious projection. Makes the field accessors
`x`, `r`, `ry` measurable from the product instances on `X`, `Bool`,
and `ℝ`. -/
instance instMeasurableSpaceMARObs
    {X : Type*} [MeasurableSpace X] : MeasurableSpace (MARObs X) :=
  MeasurableSpace.comap (fun o : MARObs X => (o.x, o.r, o.ry))
    (inferInstance : MeasurableSpace (X × Bool × ℝ))

variable {X : Type*} [MeasurableSpace X]
variable {P : Measure (MARObs X)} [IsProbabilityMeasure P]
variable {π : X → ℝ}

/-- The MAR-mean parameter functional: `Q ↦ ∫ (R · Y / π(X)) ∂Q`.

Under MAR with propensity `π(x) = P(R = 1 | X = x)`, this equals
`E_Q[Y]` — the inverse-probability-weighted estimand. The user
proves this identification separately if needed; the present file
only uses the IPW form because it is well-defined for any `Q`. -/
noncomputable def marMean_Ψ (π : X → ℝ) : Measure (MARObs X) → ℝ :=
  fun Q => ∫ o, ind o.r * o.ry / π o.x ∂Q

/-- The globally bounded extension of the MAR IPW mean functional used by the
bounded public EIF theorem.

On a MAR model law where `|R·Y/π(X)| ≤ C` almost everywhere, this
agrees with `marMean_Ψ π`.  Away from that model law it applies
`Core.MassMethod.clippedFunction` at radius `C + 1`, so unrestricted QMD paths
cannot visit arbitrarily large response values.  Edge behavior for `C < 0` is
the literal Mathlib truncation at radius `C + 1`. -/
noncomputable def marMeanBounded_Ψ (π : X → ℝ) (C : ℝ) : Measure (MARObs X) → ℝ :=
  clippedMeanFunctional (fun o : MARObs X => ind o.r * o.ry / π o.x) C

omit [IsProbabilityMeasure P] in
/-- On the bounded MAR model, the globally clipped functional agrees with the
raw IPW estimand at the observed law. -/
theorem marMeanBounded_Ψ_eq_marMean_Ψ (π : X → ℝ) (C : ℝ)
    -- explicit stronger bounded-response restriction under the model law.
    (h_ipwBddAE : ∀ᵐ o ∂P, |ind o.r * o.ry / π o.x| ≤ C) :
    marMeanBounded_Ψ π C P = marMean_Ψ π P := by
  exact clippedMeanFunctional_eq_meanFunctional h_ipwBddAE

/-! ### Example 25.43 raw functions (IPW representer, coarsening scores, AIPW EIF) -/

/-- The **IPW representer** `φ_IPW = (R/π(X))·(Y − ψ)` of vdV Lemma 25.41 / Example
25.43: the influence function obtained by "ignoring incomplete observations
altogether but reweighting the influence function `χ_Q(Y) = Y − ψ` for the full
model to eliminate the bias" (vdV p.381). In observed coordinates `R·Y = ry`, so
this is `ind(R)·(ry − ψ)/π(X)` (the `ind R` factor zeroes out the arbitrary `ry`
on `{R = false}`).

Reference: vdV §25.5.3, Example 25.43 / Lemma 25.41 (book p.381), `1{δ∈C}/R(C|y)·χ_Q(Y)`. -/
noncomputable def marMean_ipwRep (π : X → ℝ) (ψ : ℝ) (o : MARObs X) : ℝ :=
  ind o.r * (o.ry - ψ) / π o.x

/-- The **MAR coarsening score** `b_c = ((R − π(X))/π(X))·c(X)` of vdV Example 25.43:
the general form of the functions `b(x)` of Lemma 25.41 in the MAR case, obtained
by differentiating the likelihood of the missingness mechanism. Here `c : X → ℝ`
is an arbitrary (square-integrable) function of the always-observed covariate `X`.

Reference: vdV §25.5.3, Example 25.43 (book p.383), `((δ − π(y))/π(y))·c(y)` with
`c` depending on `y` through `x = ξ(y,δ)` only. -/
noncomputable def marMean_coarseningScore (π c : X → ℝ) (o : MARObs X) : ℝ :=
  (ind o.r - π o.x) / π o.x * c o.x

/-- The **AIPW efficient influence function** `φ = (R/π(X))·(Y − m(X)) + m(X) − ψ`
of vdV Example 25.43, where `m(X) = E(Y | X)` is the outcome regression and
`ψ = E(Y)` is the mean. In observed coordinates this is
`ind(R)·ry/π(X) − ((R − π(X))/π(X))·m(X) − ψ`, which equals the IPW representer
minus the coarsening score at the variance-minimizing choice `c = m − ψ`
(`marMean_eif_eq_ipw_sub_coarsening`).

Reference: vdV §25.5.3, Example 25.43 (book p.383), the efficient influence
function `(δ/π)·χ_Q(Y) − ((δ − π)/π)·c(y)` with `c(Y) = E(χ_Q(Y) | ξ(Y,δ))`. -/
noncomputable def marMean_eif (π m : X → ℝ) (ψ : ℝ) (o : MARObs X) : ℝ :=
  ind o.r * o.ry / π o.x - (ind o.r - π o.x) / π o.x * m o.x - ψ

omit [MeasurableSpace X] in
/-- The AIPW efficient influence function decomposes as the IPW representer minus
the coarsening score at the variance-minimizing `c = m − ψ` (vdV Example 25.43,
the "slight change of notation" identity):
`φ = φ_IPW − b_{m−ψ}`. Pure pointwise algebra (needs `π(X) ≠ 0`). -/
lemma marMean_eif_eq_ipw_sub_coarsening (π m : X → ℝ) (ψ : ℝ)
    (o : MARObs X) (hπ : π o.x ≠ 0) :
    marMean_eif π m ψ o
      = marMean_ipwRep π ψ o - marMean_coarseningScore π (fun x => m x - ψ) o := by
  simp only [marMean_eif, marMean_ipwRep, marMean_coarseningScore]
  field_simp
  ring

omit [MeasurableSpace X] in
/-- The AIPW efficient influence function decomposes as the **centered IPW representer**
`(R·Y/π − ψ)` minus the coarsening score at `c = m`:
`φ = (R·Y/π − ψ) − b_m`. The centered IPW representer `R·Y/π − ψ` is the canonical
influence function of the *linear* functional `Q ↦ ∫ R·Y/π dQ` (the mass-method
representer `centeredCandidate (R·Y/π)`); it differs from `marMean_ipwRep` by a
coarsening score, so both project to `φ` on the observed tangent. Pure pointwise
algebra (needs `π(X) ≠ 0`). -/
lemma marMean_eif_eq_centeredIpw_sub_coarsening (π m : X → ℝ) (ψ : ℝ)
    (o : MARObs X) (hπ : π o.x ≠ 0) :
    marMean_eif π m ψ o
      = (ind o.r * o.ry / π o.x - ψ) - marMean_coarseningScore π m o := by
  simp only [marMean_eif, marMean_coarseningScore]
  field_simp
  ring

end AsymptoticStatistics.Examples.MARMean
