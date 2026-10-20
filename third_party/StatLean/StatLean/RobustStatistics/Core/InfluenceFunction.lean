module
public import StatLean.RobustStatistics.Core.Contamination
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# The influence function — one-sided contamination derivative

The influence function of a statistical functional `T` at `P` (`MMY §3.1`, eq. (3.4)–(3.5);
Hampel 1974) measures the first-order effect of an infinitesimal point-mass contamination:

$$\operatorname{IF}(x; T, P) = \lim_{\varepsilon \downarrow 0}
  \frac{T((1-\varepsilon)P + \varepsilon\delta_x) - T(P)}{\varepsilon}.$$

The limit is *one-sided* because negative `ε` does not produce a probability measure — the
definition here uses the right filter `𝓝[>] 0`, matching both the book's `ε ↓ 0` and the
pathwise-derivative convention of
`StatLean/AsymptoticStatistics/Core/MassMethod.lean` (`Has1DPathwiseDeriv`), whose
von Mises machinery (`vonMises_pointMass_derivative`) concludes exactly this predicate.

* `HasInfluenceAt T P x v` — the one-sided derivative at contamination point `x` exists
  and equals `v`.
* `hasInfluenceAt_iff_hasDerivWithinAt` — bridge to Mathlib's `HasDerivWithinAt` on
  `Set.Ici 0`.
* `IsInfluenceFunction T P IF` — `IF` is a full influence function of `T` at `P`.
* `grossErrorSensitivity` — `γ*(T,P) = sup_x |IF(x)|` (`MMY §3.3`, eq. (3.29)); junk value
  `0` when the influence is unbounded (real-`iSup` convention).

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §3.1 (eq.
(3.4)–(3.5)), §3.3 (eq. (3.29)–(3.30)).

**Bibliographic comments.** F. R. Hampel, "The influence curve and its role in robust
estimation," *Journal of the American Statistical Association* **69**(346), 1974,
pp. 383–393.
-/

open MeasureTheory Filter Topology

namespace StatLean.RobustStatistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Influence value** (`MMY §3.1`, eq. (3.4)): the functional `T` has one-sided
contamination derivative `v` at `P` in the direction of the point mass `δ_x`. -/
def HasInfluenceAt (T : Measure Ω → ℝ) (P : Measure Ω) (x : Ω) (v : ℝ) : Prop :=
  Tendsto (fun t : ℝ => (T (contaminate P (Measure.dirac x) t) - T P) / t)
    (𝓝[>] (0 : ℝ)) (𝓝 v)

/-- The influence value is the right derivative at `0` of the contamination curve
`t ↦ T((1-t)P + tδ_x)` (`MMY §3.1`, eq. (3.5)). -/
theorem hasInfluenceAt_iff_hasDerivWithinAt {T : Measure Ω → ℝ} {P : Measure Ω} {x : Ω}
    {v : ℝ} :
    HasInfluenceAt T P x v ↔
      HasDerivWithinAt (fun t : ℝ => T (contaminate P (Measure.dirac x) t)) v
        (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.Ici_sdiff_left]
  have hslope : slope (fun t : ℝ => T (contaminate P (Measure.dirac x) t)) 0 =
      fun t : ℝ => (T (contaminate P (Measure.dirac x) t) - T P) / t := by
    funext t
    rw [slope_def_field, contaminate_zero, sub_zero]
  rw [HasInfluenceAt, ← hslope]

/-- Influence values are unique. -/
theorem HasInfluenceAt.unique {T : Measure Ω → ℝ} {P : Measure Ω} {x : Ω} {v w : ℝ}
    (hv : HasInfluenceAt T P x v) (hw : HasInfluenceAt T P x w) : v = w :=
  tendsto_nhds_unique hv hw

/-- **Influence function** (`MMY §3.1`): `IF` records the influence value of `T` at `P`
for every contamination point. -/
def IsInfluenceFunction (T : Measure Ω → ℝ) (P : Measure Ω) (IF : Ω → ℝ) : Prop :=
  ∀ x : Ω, HasInfluenceAt T P x (IF x)

/-- **Gross-error sensitivity** `γ*(T,P) = sup_x |IF(x)|` (`MMY §3.3`, eq. (3.29)),
computed from a given influence function. Junk value `0` when `|IF|` is unbounded or `Ω`
is empty (real-`iSup` convention); the boundedness theorems are stated as explicit
`∀ x, |IF x| ≤ c` bounds instead. -/
noncomputable def grossErrorSensitivity (IF : Ω → ℝ) : ℝ :=
  ⨆ x : Ω, |IF x|

omit [MeasurableSpace Ω] in
/-- The gross-error sensitivity is the least upper bound: any pointwise bound on `|IF|`
bounds `γ*` (`MMY §3.3`). -/
theorem grossErrorSensitivity_le [Nonempty Ω] {IF : Ω → ℝ} {c : ℝ}
    (h : ∀ x, |IF x| ≤ c) : grossErrorSensitivity IF ≤ c :=
  ciSup_le h

end StatLean.RobustStatistics
