module
public import StatLean.RobustStatistics.Core.Contamination

@[expose] public section

/-!
# Contamination bias — worst-case perturbation of a functional

The asymptotic bias of a functional `T` at a contaminated distribution is
`T((1-ε)P + εQ) - T(P)`, and the *maximum bias* is its supremum over all contaminating
`Q` (`MMY §3.3`). Following the statement-first design, the primitive here is the bounded
form: `ContaminationBiasLE T P ε b` says every contamination of size `ε` moves `T` by at
most `b`. Unbounded maximum bias (the mean, `LocationScale/Mean.lean`) is the negation
`∀ b, ¬ ContaminationBiasLE …`; the extended-real supremum can be layered on later without
touching consumers.

* `ContaminationBiasLE T P ε b` — every `ε`-contamination moves `T` by at most `b`.
* monotonicity in the bound, the `ε = 0` degenerate case, and the point-mass specialization.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §3.3 (maximum
asymptotic bias, contamination sensitivity).

**Bibliographic comments.** The bias caused by contamination — as opposed to the variance
studied by classical asymptotics — is the organizing quantity of P. J. Huber, "Robust
estimation of a location parameter," *Ann. Math. Statist.* **35** (1964), 73–101; the
systematic study of maximum-bias curves is R. D. Martin, V. J. Yohai and R. H. Zamar,
"Min–max bias robust regression," *Ann. Statist.* **17** (1989), 1608–1630.
-/

open MeasureTheory

namespace StatLean.RobustStatistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Bounded contamination bias** (`MMY §3.3`): every contamination of `P` at level `ε`
by a probability measure moves the functional `T` by at most `b`. -/
def ContaminationBiasLE (T : Measure Ω → ℝ) (P : Measure Ω) (ε b : ℝ) : Prop :=
  ∀ Q : Measure Ω, IsProbabilityMeasure Q → |T (contaminate P Q ε) - T P| ≤ b

/-- A bias bound remains valid for any larger bound. -/
theorem ContaminationBiasLE.mono {T : Measure Ω → ℝ} {P : Measure Ω} {ε b b' : ℝ}
    (h : ContaminationBiasLE T P ε b) (hb : b ≤ b') : ContaminationBiasLE T P ε b' :=
  fun Q hQ => (h Q hQ).trans hb

/-- At contamination level `0` the bias vanishes. -/
theorem contaminationBiasLE_zero (T : Measure Ω → ℝ) (P : Measure Ω) :
    ContaminationBiasLE T P 0 0 := by
  intro Q _
  rw [contaminate_zero, sub_self, abs_zero]

/-- A bias bound specializes to point-mass contamination. -/
theorem ContaminationBiasLE.dirac [MeasurableSingletonClass Ω] {T : Measure Ω → ℝ}
    {P : Measure Ω} {ε b : ℝ} (h : ContaminationBiasLE T P ε b) (x : Ω) :
    |T (contaminate P (Measure.dirac x) ε) - T P| ≤ b :=
  h (Measure.dirac x) Measure.dirac.isProbabilityMeasure

end StatLean.RobustStatistics
