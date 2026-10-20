module
public import StatLean.CausalInference.Core.FiniteDefs
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Potential outcomes on a population — estimands, propensity score, and the assumptions

The population (superpopulation) half of causal inference: a probability space `(Ω, μ)`
carries the treatment indicator `Z`, the two potential outcomes `y1, y0`, and a covariate
`X` taking values in a **finite** type `𝒳`.

* `obs Z y1 y0` — the observed outcome `Y = Z·Y(1) + (1-Z)·Y(0)`.
* `cell X x`, `armCell Z X z x` — the events `{X = x}` and `{Z = z, X = x}`.
* `ate`, `att`, `atc`, `cate` — the average causal effect, the effects on the treated and
  on the controls, and the conditional (covariate-specific) effect.
* `cellMean μ Z X Y z x` — the regression function `m_z(x) = E[Y | Z = z, X = x]`.
* `propensity μ Z X x` — the propensity score `e(x) = P(Z = 1 | X = x)`.
* `Unconfounded`, `Ignorable`, `MeanIgnorable`, `Positive`, `StronglyOverlapping` — the
  identification assumptions.
* `ipwTreated`, `ipwControl`, `ipwATE` — the inverse-probability-weighting functionals.
* `aipwTreated`, `aipwControl`, `aipwATE` — the augmented (doubly robust) functionals for
  user-supplied working models.

**Scope (discrete covariates).** `𝒳` is finite with measurable singletons, so
conditioning is on events of positive probability via `ProbabilityTheory.cond`
(`μ[|s]`) and every identification formula is a finite sum over covariate cells. This is
the setting in which Ding states the identification results concretely (e.g. eq. (10.8));
the general-covariate versions replace finite sums by integrals against the law of `X`
and conditional expectations, with no change in statistical content.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §10.2 (the prima facie effect and selection
bias), §10.3 and Assumptions 10.1–10.2 (ignorability and strong ignorability),
Definition 11.1 and §11.2.1 (the propensity score, and the overlap/positivity condition
`0 < e(X) < 1`), §11.2.1–11.2.2 (inverse-probability weighting), §12.1 eqs. (12.3)–(12.6)
(the doubly robust functionals), ch. 13 (the effect on the treated). (`Ding §10.2–10.3;
§11.1–11.2; §12.1; ch. 13`.) The unconfoundedness formulation follows G. W. Imbens and
D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*,
Cambridge University Press, 2015, Part III. (`IR Part III`.)

**Proof formalization notes.**

* **Unconfoundedness is cell-wise independence.** For discrete `X`, the textbook
  `{Y(1), Y(0)} ⫫ Z | X` (Ding Assumption 10.2) says exactly that `(y1, y0)` and `Z` are
  independent under each conditional measure `μ[|{X = x}]`; that is the definition used
  here. Mathlib's `CondIndepFun` (σ-algebra form) would require standard-Borel machinery
  and is not used anywhere in StatLean.
* All estimands are Bochner integrals against conditional measures. On a null cell,
  `ProbabilityTheory.cond` returns the zero measure, so cell quantities are `0` there and
  the identification theorems carry an explicit "positive cell" hypothesis where the
  value matters. `propensity` returns `0` on a null cell for the same reason.
* Working models (`ebar`, `m1bar`, `m0bar`) are *arbitrary user-supplied functions* of the
  covariate, not required to be the truth — that is the whole point of double robustness.

**Bibliographic comments.** Unconfoundedness and the propensity score are due to
P. R. Rosenbaum and D. B. Rubin, "The central role of the propensity score in
observational studies for causal effects," *Biometrika* **70** (1983), 41–55.
Inverse-probability weighting goes back to D. G. Horvitz and D. J. Thompson, "A
generalization of sampling without replacement from a finite universe," *J. Amer. Statist.
Assoc.* **47** (1952), 663–685; the augmented (doubly robust) form is J. M. Robins,
A. Rotnitzky and L. P. Zhao, "Estimation of regression coefficients when some regressors
are not always observed," *J. Amer. Statist. Assoc.* **89** (1994), 846–866.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ### Observed data -/

/-- The **observed outcome** `Y = Z·Y(1) + (1 - Z)·Y(0)` (Ding eq. (2.2)). -/
def obs (Z : Ω → Bool) (y1 y0 : Ω → ℝ) : Ω → ℝ := fun ω => if Z ω then y1 ω else y0 ω

/-- The **covariate cell** `{X = x}`. -/
def cell (X : Ω → 𝒳) (x : 𝒳) : Set Ω := X ⁻¹' {x}

/-- The **arm cell** `{Z = z, X = x}`. -/
def armCell (Z : Ω → Bool) (X : Ω → 𝒳) (z : Bool) (x : 𝒳) : Set Ω :=
  {ω | Z ω = z} ∩ X ⁻¹' {x}

/-- The **treated event** `{Z = 1}`. -/
def treatedEvent (Z : Ω → Bool) : Set Ω := {ω | Z ω = true}

/-! ### Estimands -/

/-- The **average causal effect** `τ = E[Y(1) - Y(0)]` (Ding §2.2). -/
noncomputable def ate (μ : Measure Ω) (y1 y0 : Ω → ℝ) : ℝ := ∫ ω, (y1 ω - y0 ω) ∂μ

/-- The **average causal effect on the treated** `τ_T = E[Y(1) - Y(0) | Z = 1]`
(Ding §10.2, ch. 13). -/
noncomputable def att (μ : Measure Ω) (Z : Ω → Bool) (y1 y0 : Ω → ℝ) : ℝ :=
  ∫ ω, (y1 ω - y0 ω) ∂(μ[|treatedEvent Z])

/-- The **average causal effect on the controls** `τ_C = E[Y(1) - Y(0) | Z = 0]`
(Ding §10.2). -/
noncomputable def atc (μ : Measure Ω) (Z : Ω → Bool) (y1 y0 : Ω → ℝ) : ℝ :=
  ∫ ω, (y1 ω - y0 ω) ∂(μ[|{ω | Z ω = false}])

/-- The **conditional average causal effect** `τ(x) = E[Y(1) - Y(0) | X = x]`
(Ding §10.3.1). -/
noncomputable def cate (μ : Measure Ω) (X : Ω → 𝒳) (y1 y0 : Ω → ℝ) (x : 𝒳) : ℝ :=
  ∫ ω, (y1 ω - y0 ω) ∂(μ[|cell X x])

/-- The **prima facie effect** `τ_PF = E[Y | Z = 1] - E[Y | Z = 0]` (Ding §10.2): the
naive comparison of observed outcomes between the arms. -/
noncomputable def primaFacie (μ : Measure Ω) (Z : Ω → Bool) (Y : Ω → ℝ) : ℝ :=
  ∫ ω, Y ω ∂(μ[|treatedEvent Z]) - ∫ ω, Y ω ∂(μ[|{ω | Z ω = false}])

/-- The **arm regression function** `m_z(x) = E[Y | Z = z, X = x]` (Ding §10.3.1). -/
noncomputable def cellMean (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ)
    (z : Bool) (x : 𝒳) : ℝ :=
  ∫ ω, Y ω ∂(μ[|armCell Z X z x])

/-- The **propensity score** `e(x) = P(Z = 1 | X = x)` (Ding Definition 11.1). Junk value
`0` on a null cell. -/
noncomputable def propensity (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (x : 𝒳) : ℝ :=
  ((μ[|cell X x]) (treatedEvent Z)).toReal

/-! ### Identification assumptions -/

/-- **Strong ignorability / unconfoundedness** `{Y(1), Y(0)} ⫫ Z | X`
(Ding Assumption 10.2), in the cell-wise form appropriate to a discrete covariate: under
the conditional law given each covariate cell, the pair of potential outcomes is
independent of the treatment. -/
def Unconfounded (μ : Measure Ω) (Z : Ω → Bool) (y1 y0 : Ω → ℝ) (X : Ω → 𝒳) : Prop :=
  ∀ x : 𝒳, IndepFun (fun ω => (y1 ω, y0 ω)) Z (μ[|cell X x])

/-- **Ignorability for a single arm** `Y(z) ⫫ Z | X` (Ding Assumption 10.1). -/
def Ignorable (μ : Measure Ω) (Z : Ω → Bool) (y : Ω → ℝ) (X : Ω → 𝒳) : Prop :=
  ∀ x : 𝒳, IndepFun y Z (μ[|cell X x])

/-- **Mean ignorability** for the potential outcome `y`: the two arms have the same
conditional mean of `y` in every covariate cell (Ding eqs. (10.3)–(10.4), the hypothesis
of Theorem 10.1 — weaker than Assumption 10.1). -/
def MeanIgnorable (μ : Measure Ω) (Z : Ω → Bool) (y : Ω → ℝ) (X : Ω → 𝒳) : Prop :=
  ∀ x : 𝒳, ∫ ω, y ω ∂(μ[|armCell Z X true x]) = ∫ ω, y ω ∂(μ[|armCell Z X false x])

/-- **Positivity / overlap** `0 < e(X) < 1` (Ding §11.2.1; not a numbered assumption in
the book — it is the hypothesis of Theorem 11.2). Required only on cells of positive
probability. -/
def Positive (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) : Prop :=
  ∀ x : 𝒳, μ (cell X x) ≠ 0 → 0 < propensity μ Z X x ∧ propensity μ Z X x < 1

/-- **Strong overlap** `α ≤ e(X) ≤ 1 - α` (Ding §11.2.3): the quantitative form of
positivity that bounds the inverse-probability weights. -/
def StronglyOverlapping (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (α : ℝ) : Prop :=
  ∀ x : 𝒳, μ (cell X x) ≠ 0 → α ≤ propensity μ Z X x ∧ propensity μ Z X x ≤ 1 - α

/-! ### Inverse-probability weighting -/

/-- The **inverse-probability-weighted treated functional** `E[Z·Y/e(X)]`
(Ding Theorem 11.2). -/
noncomputable def ipwTreated (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ) : ℝ :=
  ∫ ω, ind (Z ω) * Y ω / propensity μ Z X (X ω) ∂μ

/-- The **inverse-probability-weighted control functional** `E[(1-Z)·Y/(1-e(X))]`
(Ding Theorem 11.2). -/
noncomputable def ipwControl (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ) : ℝ :=
  ∫ ω, (1 - ind (Z ω)) * Y ω / (1 - propensity μ Z X (X ω)) ∂μ

/-- The **inverse-probability-weighting functional for the average causal effect**
(Ding Theorem 11.2). -/
noncomputable def ipwATE (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ) : ℝ :=
  ipwTreated μ Z X Y - ipwControl μ Z X Y

/-! ### Augmented inverse-probability weighting (doubly robust) -/

/-- The **augmented IPW functional for `E[Y(1)]`** with working propensity `ebar` and
working outcome model `m1bar` (Ding eq. (12.3)):
`E[ m̄₁(X) + Z(Y - m̄₁(X))/ē(X) ]`. -/
noncomputable def aipwTreated (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ)
    (ebar m1bar : 𝒳 → ℝ) : ℝ :=
  ∫ ω, (m1bar (X ω) + ind (Z ω) * (Y ω - m1bar (X ω)) / ebar (X ω)) ∂μ

/-- The **augmented IPW functional for `E[Y(0)]`** (Ding eq. (12.4)):
`E[ m̄₀(X) + (1-Z)(Y - m̄₀(X))/(1-ē(X)) ]`. -/
noncomputable def aipwControl (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ)
    (ebar m0bar : 𝒳 → ℝ) : ℝ :=
  ∫ ω, (m0bar (X ω) + (1 - ind (Z ω)) * (Y ω - m0bar (X ω)) / (1 - ebar (X ω))) ∂μ

/-- The **doubly robust functional for the average causal effect** (Ding §12.1). -/
noncomputable def aipwATE (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ)
    (ebar m1bar m0bar : 𝒳 → ℝ) : ℝ :=
  aipwTreated μ Z X Y ebar m1bar - aipwControl μ Z X Y ebar m0bar

end StatLean.CausalInference
