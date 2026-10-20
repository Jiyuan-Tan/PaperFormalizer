module
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-!
# Partially specified models — constraint (moment) models

A fully specified model assigns each parameter one law; a **partially specified model** assigns
each parameter the *set* of laws compatible with a restriction — a conditional-moment
restriction (GEE marginal mean models), a covariance restriction, or any estimating-equation
model. The carrier is deliberately the bare set-valued map `C : Θ → Set (Measure 𝓧)`
(recall `Set X = X → Prop`, so this subsumes a `Holds : Θ → Measure 𝓧 → Prop` field):

* `singletonFibers P` — a fully specified model viewed as a constraint model with singleton
  fibers;
* `FibersNonempty C` — the compatibility (feasibility) *predicate*: every fiber is nonempty.
  Deliberately a predicate and **not** a structure field — feasibility of, say, a mean model
  is a theorem about laws with a prescribed conditional mean, and misspecified (empty-fiber)
  models are legitimate objects of identification analysis;
* `FibersProbability C` — every compatible law is a probability measure;
* `SeparatesTarget C ψ` — the constraint identifies the target: parameters whose fibers
  overlap have equal targets (the partial-identification notion of point identification of
  `ψ`).

**Reference.** Moment-restriction models: L. P. Hansen, "Large sample properties of
generalized method of moments estimators," *Econometrica* **50** (1982), 1029–1054, §2
(verify §); marginal mean models specified only through estimating equations: K.-Y. Liang and
S. L. Zeger, "Longitudinal data analysis using generalized linear models," *Biometrika* **73**
(1986), 13–22, §2. Identified sets and point identification of functionals: C. F. Manski,
*Partial Identification of Probability Distributions*, Springer, 2003, Ch. 1 (verify §).

**Proof formalization notes.** Laptop-only data model — definitions only. The relations to the
fully specified theory (`SeparatesTarget (singletonFibers P) ψ ↔ IdentifiesTarget P ψ`,
monotonicity of separation under observation) live in `Identifiability.Transfer`. Substantive
constraint-model theorems (GEE unbiasedness under a conditional-mean restriction) arrive with
the Longitudinal slice.

**Bibliographic comments.** Estimating-function models without full likelihoods originate with
V. P. Godambe, "An optimum property of regular maximum likelihood estimation," *Ann. Math.
Statist.* **31** (1960), 1208–1211; the identified-set viewpoint on partially specified models
is Manski's.
-/

open MeasureTheory

namespace StatLean.StatisticalModels

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- A fully specified model as a constraint model: each fiber is the singleton of the
assigned law. -/
def singletonFibers (P : Θ → Measure 𝓧) : Θ → Set (Measure 𝓧) :=
  fun θ => {P θ}

/-- **Feasibility**: every fiber of the constraint model is nonempty (there exists a law
compatible with the restriction at every parameter). A predicate, not a field. -/
def FibersNonempty (C : Θ → Set (Measure 𝓧)) : Prop :=
  ∀ θ, (C θ).Nonempty

/-- Every law compatible with the constraint is a probability measure. -/
def FibersProbability (C : Θ → Set (Measure 𝓧)) : Prop :=
  ∀ θ, ∀ Q ∈ C θ, IsProbabilityMeasure Q

/-- **The constraint identifies the target `ψ`**: parameters whose fibers share a compatible
law have equal targets. For singleton fibers this is exactly target identifiability of the
fully specified model (`Identifiability.Transfer.separatesTarget_singletonFibers`). -/
def SeparatesTarget {Γ : Type*} (C : Θ → Set (Measure 𝓧)) (ψ : Θ → Γ) : Prop :=
  ∀ ⦃θ₁ θ₂⦄, (C θ₁ ∩ C θ₂).Nonempty → ψ θ₁ = ψ θ₂

end StatLean.StatisticalModels
