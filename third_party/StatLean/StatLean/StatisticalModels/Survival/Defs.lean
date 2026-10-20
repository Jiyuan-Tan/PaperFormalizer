module
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-!
# Survival analysis — event-time laws, survival functions, cumulative-hazard measures

The primitive objects of the survival / event-history slice. An **event-time law** is a
probability measure on `ℝ` supported on `[0, ∞)`; a **sub-event-time law** relaxes total mass
to `≤ 1`, the mass defect being the *cure fraction*. From an event-time law we define:

* `survival μ t = μ (t, ∞)` — the survival function `S(t)`;
* `survivalLeft μ t = μ [t, ∞)` — the left limit `S(t−)`, **defined as a measure value**,
  never as a filter limit (the bridge to `Function.leftLim` is a lemma in
  `Survival.Survival`, not the definition — this removes càdlàg bookkeeping from every
  downstream proof);
* `survivalReal` — the real-valued survival function, for the CDF bridge;
* `cumHazard μ = μ.withDensity (t ↦ (μ [t, ∞))⁻¹)` — the **cumulative-hazard measure**
  `Λ(dt) = F(dt)/S(t−)`, fully distribution-agnostic: continuous, discrete and mixed laws are
  all covered, with no differentiability and no atomlessness assumed;
* `cumHazardJump μ t = Λ{t}` — the hazard jump `ΔΛ(t)`.

**Reference.** P. K. Andersen, Ø. Borgan, R. D. Gill, and N. Keiding, *Statistical Models
Based on Counting Processes*, Springer Series in Statistics, Springer, 1993
(ISBN 0-387-97872-0), §II.1 (verify §): the integrated (cumulative) hazard
`Λ(t) = ∫₀ᵗ dF/S(s−)` as the primitive, with `ΔΛ = ΔF/S(−)` at atoms. (`ABGK §II.1`.)

**Proof formalization notes.** Laptop-only data model — definitions only; all lemmas live in
`Survival.Survival` and `Survival.CumulativeHazard`. *Book vs Lean:* ABGK work on `[0, ∞]`
allowing a defect (mass at `+∞`); we encode the defect as **sub-probability total mass**
(`IsSubEventTimeLaw`), not as a point at infinity — `Measure ℝ` keeps the entire Stieltjes /
CDF / `withDensity` toolchain available. The ENNReal inverse in `cumHazard` junk-values to `∞`
where `S(t−) = 0`; the hygiene lemma `Survival.CumulativeHazard.measure_survivalLeft_zero`
shows that region is `μ`-null, so the density is a.e. finite and the junk never carries
weight.

**Bibliographic comments.** The hazard (force of mortality) goes back to actuarial science
(Gompertz 1825, Makeham 1860); the modern measure-theoretic cumulative hazard and its role as
the compensator of the one-jump counting process are due to O. O. Aalen ("Nonparametric
inference for a family of counting processes," *Ann. Statist.* **6** (1978), 701–726) and the
ABGK synthesis.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StatLean.StatisticalModels.Survival

/-- **Event-time law**: a probability measure on `ℝ` supported on `[0, ∞)` (ABGK §II.1
(verify §); *Book vs Lean:* ABGK's `[0, ∞]` carrier is encoded on `ℝ`, cf. module notes). -/
def IsEventTimeLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Iio 0) = 0

/-- **Sub-event-time law**: total mass `≤ 1`, supported on `[0, ∞)`; the defect `1 − μ(ℝ)` is
the cure fraction (ABGK §II.1's defective distributions (verify §)). -/
def IsSubEventTimeLaw (μ : Measure ℝ) : Prop :=
  μ univ ≤ 1 ∧ μ (Iio 0) = 0

/-- The **survival function** `S(t) = P(T > t)` (ABGK §II.1). -/
noncomputable def survival (μ : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  μ (Ioi t)

/-- The **left limit of the survival function** `S(t−) = P(T ≥ t)`, defined directly as a
measure value (never as a filter limit — see module notes). -/
noncomputable def survivalLeft (μ : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  μ (Ici t)

/-- The real-valued survival function, for the CDF bridge. -/
noncomputable def survivalReal (μ : Measure ℝ) (t : ℝ) : ℝ :=
  (survival μ t).toReal

/-- The **cumulative-hazard measure** `Λ(dt) = F(dt)/S(t−)` (ABGK §II.1 (verify §)):
distribution-agnostic — continuous, discrete and mixed event-time laws are all covered.
Where `S(t−) = 0` the ENNReal inverse junk-values to `∞`; that region is `μ`-null
(`CumulativeHazard.measure_survivalLeft_zero`). -/
noncomputable def cumHazard (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity fun t => (μ (Ici t))⁻¹

/-- The **hazard jump** `ΔΛ(t) = Λ{t}` (ABGK §II.1: `ΔΛ = ΔF/S(−)` at atoms). -/
noncomputable def cumHazardJump (μ : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  cumHazard μ {t}

end StatLean.StatisticalModels.Survival
