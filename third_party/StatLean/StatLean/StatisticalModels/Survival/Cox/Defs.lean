module
public import StatLean.StatisticalModels.Survival.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# The Cox proportional-hazards model — structure

Cox's model as a *structure on covariate-indexed families of event-time laws*, agnostic to
the baseline class — the baseline cumulative hazard ranges over an **arbitrary user-supplied
class of measures** (finite-dimensional for parametric survival, the full nonparametric class
for Cox's semiparametric model): the model structure is the proportionality, never a
parametric family.

* `IsProportionalHazards P β Λ₀` — the covariate-indexed family `P : z ↦ (law of T given z)`
  has cumulative hazards `e^{β᾿z} · Λ₀`: Cox's structural assumption as a predicate;
* `CoxModel p` — the model's constitutive index data: a baseline class and a covariate
  region (so `Θ = ℝᵖ × baselineClass` with the semiparametric split of the Core layer);
* `coxSurvival β Λ₀ z t = exp(−e^{β᾿z} Λ₀(0, t])` — the canonical construction realizing
  the structure for a continuous baseline (its law, well-formedness and the
  realization theorem are in `Cox.Basic`).

**Reference.** D. R. Cox, "Regression models and life-tables," *J. Roy. Statist. Soc. B*
**34** (1972), 187–220, §1–2 (`Cox72`); ABGK §III.1.2 (the multiplicative intensity/hazard
form) (verify §).

**Proof formalization notes.** Laptop-only data model — definitions only. The
proportionality predicate is stated on cumulative-hazard *measures* (`cumHazard`, S-B1) —
fully distribution-agnostic, no hazard densities. The `ENNReal.ofReal ∘ exp` coefficient is
strictly positive, so no degenerate-scaling corner. Baseline conventions (mass on `(0, ∞)`,
local finiteness, no atoms for the canonical construction) enter as hypotheses in `Cox.Basic`
— regularity, not structure fields.

**Bibliographic comments.** Cox (1972) introduced both the model and (in §5–6) the partial/
conditional likelihood; the measure-hazard formulation is the counting-process reading of
Aalen (1978) and ABGK. The "parametric baseline vs nonparametric baseline" unification as one
structure over a baseline *class* follows the semiparametric literature (e.g. Tsiatis,
*Semiparametric Theory and Missing Data*, Springer, 2006, Ch. 5 (verify §)).
-/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.Survival

variable {p : ℕ}

/-- **Cox's proportional-hazards structure** (`Cox72 §2`; ABGK §III.1.2): the covariate-
indexed family `P` of event-time laws has cumulative hazard `e^{⟪β, z⟫} · Λ₀` at covariate
`z` — proportionality as a predicate on families, with the baseline `Λ₀` an arbitrary
measure. -/
def IsProportionalHazards (P : EuclideanSpace ℝ (Fin p) → Measure ℝ)
    (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ) : Prop :=
  ∀ z, cumHazard (P z) = ENNReal.ofReal (Real.exp ⟪β, z⟫_ℝ) • Λ₀

/-- The **Cox model's constitutive index data** (`Cox72 §2`): a class of admissible baseline
cumulative-hazard measures (finite-dimensional ⇒ parametric survival; all measures ⇒ the
semiparametric Cox model) and a covariate design region. The parameter space is
`ℝᵖ × baselineClass` — the semiparametric split `Θ = Ψ × Η` of the Core layer. -/
structure CoxModel (p : ℕ) where
  /-- Constitutive (Cox72 §2): the admissible baseline class — the model's nuisance space. -/
  baselineClass : Set (Measure ℝ)
  /-- Constitutive (Cox72 §2): the covariate design region. -/
  covariates : Set (EuclideanSpace ℝ (Fin p))

/-- The canonical **Cox survival function** for a continuous baseline:
`S(t ∣ z) = exp(−e^{⟪β,z⟫} Λ₀(0, t])` (`Cox72 §2`). Its law and the theorem that it
realizes `IsProportionalHazards` are in `Cox.Basic`. -/
noncomputable def coxSurvival (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p)) (t : ℝ) : ℝ :=
  Real.exp (-(Real.exp ⟪β, z⟫_ℝ * (Λ₀ (Ioc 0 t)).toReal))

end StatLean.StatisticalModels.Survival
