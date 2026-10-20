module
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.MapComap

@[expose] public section

/-!
# Coarsened data — missingness mechanisms for a single outcome

The model-level layer for missing data with one always-observed covariate `x : 𝓧` and one
possibly-missing real outcome `y : ℝ`. Carriers, fixed once for the whole slice:

* full data `𝓧 × ℝ × Bool` — covariate, outcome, response indicator `r`;
* observed data `𝓧 × Bool × ℝ` — covariate, indicator, masked outcome `r·y` (matching the
  field order of the semiparametric example `AsymptoticStatistics.Examples.MARMean.MARObs`).

Objects:

* `fullLaw Q ρ` — the joint full-data law of `(x, y, r)` from the outcome law `Q` on
  `𝓧 × ℝ` and the missingness kernel `ρ : (𝓧 × ℝ) ⇝ Bool`;
* `missingObserve` — the coarsening map `(x, y, r) ↦ (x, r, if r then y else 0)` (unobserved
  outcomes zeroed);
* `observedLaw Q ρ` — the observed-data law;
* `IsMCAR ρ` — missing completely at random: the mechanism is a constant kernel;
* `IsMAR ρ` — missing at random (this monotone single-outcome pattern): the mechanism factors
  through the always-observed coordinate, `P(R = 1 ∣ x, y) = π(x)`;
* `propensity ρ' x` — the response probability `π(x)`; `HasPositivity ρ' δ` — the uniform
  overlap condition `π ≥ δ`;
* `ind` — the `Bool → ℝ` indicator used in IPW integrands.

**Reference.** D. B. Rubin, "Inference and missing data," *Biometrika* **63** (1976),
581–592, §2 (the MCAR/MAR taxonomy); R. J. A. Little and D. B. Rubin, *Statistical Analysis
with Missing Data*, 3rd ed., Wiley, 2019, §1.3 (verify §). (`Rubin76`, `LR §1.3`.)

**Proof formalization notes.** Laptop-only data model — definitions only. *Book vs Lean:*
Rubin's general MAR ("missingness depends only on observed components") specializes, for a
single-outcome monotone pattern, to exactly the kernel factorization `ρ = ρ' ∘ comap fst`
used here; the general multi-pattern formulation is a designated future milestone. Masking
with the junk value `0` (not an `Option`) keeps the observed space standard Borel and matches
`MARObs`'s `ry = r·y` encoding; nothing downstream reads the outcome slot when `r = false`.

**Bibliographic comments.** MCAR/MAR are Rubin's (1976); the coarsening-kernel view is
D. F. Heitjan and D. B. Rubin, "Ignorability and coarse data," *Ann. Statist.* **19** (1991),
2244–2253. The propensity/overlap vocabulary is from P. R. Rosenbaum and D. B. Rubin, "The
central role of the propensity score in observational studies," *Biometrika* **70** (1983),
41–55.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels.Coarsening

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The joint full-data law of `(x, y, r)`: outcome law `Q` on `𝓧 × ℝ` composed with the
missingness kernel `ρ`, reassociated to the fixed full-data carrier (Rubin76 §2). -/
noncomputable def fullLaw (Q : Measure (𝓧 × ℝ)) (ρ : Kernel (𝓧 × ℝ) Bool) :
    Measure (𝓧 × ℝ × Bool) :=
  (Q ⊗ₘ ρ).map fun p => (p.1.1, p.1.2, p.2)

/-- The coarsening map: `(x, y, r) ↦ (x, r, if r then y else 0)` — the outcome is revealed
exactly when `r = true`, otherwise masked by the junk value `0` (cf. `MARObs.ry`). -/
def missingObserve : 𝓧 × ℝ × Bool → 𝓧 × Bool × ℝ :=
  fun p => (p.1, p.2.2, if p.2.2 then p.2.1 else 0)

/-- The observed-data law: the full-data law pushed through the coarsening map. -/
noncomputable def observedLaw (Q : Measure (𝓧 × ℝ)) (ρ : Kernel (𝓧 × ℝ) Bool) :
    Measure (𝓧 × Bool × ℝ) :=
  (fullLaw Q ρ).map missingObserve

/-- **MCAR** (Rubin76 §2): the missingness mechanism ignores the data entirely — a constant
kernel. -/
def IsMCAR (ρ : Kernel (𝓧 × ℝ) Bool) : Prop :=
  ∃ ν : Measure Bool, ρ = Kernel.const _ ν

/-- **MAR**, monotone single-outcome pattern (Rubin76 §2; LR §1.3 (verify §)): the mechanism
factors through the always-observed covariate — `P(R ∈ · ∣ x, y)` depends only on `x`. -/
def IsMAR (ρ : Kernel (𝓧 × ℝ) Bool) : Prop :=
  ∃ ρ' : Kernel 𝓧 Bool, ρ = ρ'.comap Prod.fst measurable_fst

/-- The **propensity** (response probability) `π(x) = P(R = true ∣ x)`
(Rosenbaum–Rubin 1983). -/
noncomputable def propensity (ρ' : Kernel 𝓧 Bool) (x : 𝓧) : ℝ :=
  (ρ' x {true}).toReal

/-- **Uniform positivity / overlap**: the response probability is bounded below by `δ`. -/
def HasPositivity (ρ' : Kernel 𝓧 Bool) (δ : ℝ) : Prop :=
  ∀ x, δ ≤ propensity ρ' x

/-- The real-valued indicator of a Boolean (the `R` factor in IPW integrands; mirrors
`MARMean.ind`). -/
def ind (b : Bool) : ℝ :=
  if b then 1 else 0

end StatLean.StatisticalModels.Coarsening
