module
public import StatLean.PointEstimation.Model.Defs
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Equivariant estimation — core data model

An estimation problem is **invariant** under a group `G` when `G` acts on the sample
space, on the parameter space, and on the decision space in a compatible way: the model
maps `g`-shifted data to `g`-shifted parameters, and the loss is unchanged by the
simultaneous action. An estimator is **equivariant** when it intertwines the sample- and
decision-space actions. This file fixes:

* general theory — `IsInvariantModel`, `IsInvariantLoss`, `IsEquivariant`,
  `IsRiskUnbiased` (all over `[Group G]` with `MulAction`s on `𝓧`, `Θ`, `D`);
* the concrete **location model** on `Fin n → ℝ` — `locationBase f` (the `ξ = 0`
  member), `locationFamily f ξ` (its translate), `IsLocInvariantLoss`,
  `IsLocEquivariant`, the maximal-invariant `diffs` statistic, location risk
  `locRisk`, and `IsLocMRE` (minimum risk equivariant);
* the concrete **scale model** — `scaleFamily`, `IsScaleEquivariant` (of degree `r`),
  the maximal-invariant `scaleZ` statistic, `scaleRisk`, `IsScaleMRE`;
* the **Pitman estimator** in closed form.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.1 (First
Examples), Definitions 1.2, 1.3 and 1.5 (the location-invariant problem, equivariant
estimators, and the MRE estimator), together with Definitions 2.1, 2.4 and 2.5 of §3.2
(`G`-invariant model, invariant loss, equivariant estimator). (`TPE2 §3.1 Def 1.2–1.5; §3.2
Def 2.1–2.5`.)

**Proof formalization notes.**
* The induced parameter action is *data* (a `MulAction G Θ` instance), with the
  intertwining law `(P θ).map (g • ·) = P (g • θ)` as the constitutive property
  (`IsInvariantModel`); identifiability makes the induced action unique, which is a
  lemma, not a definition.
* The location theory is developed concretely (additive translations on `Fin n → ℝ`)
  rather than through `Multiplicative ℝ`, matching the classical development; bridge
  lemmas identify it as an instance of the general framework.
* Losses are real functions composed with `ENNReal.ofReal` inside `∫⁻`-risks
  (junk-value discipline); convexity hypotheses (`ConvexOn ℝ`) apply to the real loss.
* Degenerate inputs: `locationBase f = 0` measure when `f` is not a.e.-nonneg-integrable
  in the intended way is *not* guarded here; theorems carry the pdf hypotheses.
* `scaleZ` records both the coordinate ratios and the sign of the last coordinate —
  the full maximal invariant of the scale group on `ℝⁿ ∖ {xₙ = 0}`.

**Bibliographic comments.** Equivariant ("invariant") estimation of location and scale
parameters is due to E. J. G. Pitman ("The estimation of the location and scale
parameters of a continuous population of any given form," *Biometrika* **30** (1939),
391–421); the general group-theoretic formulation was developed by C. Stein and
G. A. Hunt (unpublished, 1946) and systematized in E. L. Lehmann's lecture-note
tradition. Risk-unbiasedness as the decision-theoretic extension of unbiasedness is due
to E. L. Lehmann ("A general concept of unbiasedness," *Ann. Math. Statist.* **22**
(1951), 587–592).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

/-! ## General invariant estimation problems -/

section General

variable {G Θ 𝓧 D : Type*} [Group G] [MeasurableSpace 𝓧]
  [MulAction G 𝓧] [MulAction G Θ] [MulAction G D]

/-- **Invariant model**: the group action on data induces the given action on
parameters, `(P θ) ∘ g⁻¹ = P (g • θ)`. -/
def IsInvariantModel (P : Θ → Measure 𝓧) : Prop :=
  ∀ (g : G) (θ : Θ), (P θ).map (g • ·) = P (g • θ)

/-- **Invariant loss**: unchanged under the simultaneous action on parameters and
decisions. -/
def IsInvariantLoss (L : Θ → D → ℝ≥0∞) : Prop :=
  ∀ (g : G) (θ : Θ) (d : D), L (g • θ) (g • d) = L θ d

/-- **Equivariant estimator**: intertwines the sample- and decision-space actions. -/
def IsEquivariant (δ : 𝓧 → D) : Prop :=
  ∀ (g : G) (x : 𝓧), δ (g • x) = g • δ x

variable (G) in
/-- `IsEquivariant` with the group made explicit (for statements quantifying over the
acting group). -/
def IsEquivariantUnder (δ : 𝓧 → D) : Prop :=
  ∀ (g : G) (x : 𝓧), δ (g • x) = g • δ x

/-- **Risk-unbiased estimator**: for every true `θ`, the expected loss against the true
value is no larger than against any false value `θ'`. -/
def IsRiskUnbiased [MeasurableSpace D] (P : Θ → Measure 𝓧) (L : Θ → D → ℝ≥0∞)
    (δ : 𝓧 → D) : Prop :=
  ∀ θ θ', crossRisk P L δ θ θ ≤ crossRisk P L δ θ θ'

end General

/-! ## The location model on `Fin n → ℝ` -/

section Location

variable {n : ℕ}

/-- The base member (`ξ = 0`) of a location family with joint density `f` on
`Fin n → ℝ`. -/
noncomputable def locationBase (f : (Fin n → ℝ) → ℝ) : Measure (Fin n → ℝ) :=
  (volume : Measure (Fin n → ℝ)).withDensity fun x => ENNReal.ofReal (f x)

/-- The location family: the base density translated by `ξ` in every coordinate,
`X + ξ·𝟙 ∼ locationFamily f ξ` for `X ∼ locationBase f`. -/
noncomputable def locationFamily (f : (Fin n → ℝ) → ℝ) (ξ : ℝ) : Measure (Fin n → ℝ) :=
  (locationBase f).map (· + ξ • (1 : Fin n → ℝ))

/-- **Location-equivariant estimator**: `δ(x + a·𝟙) = δ(x) + a`. -/
def IsLocEquivariant (δ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (a : ℝ) (x : Fin n → ℝ), δ (x + a • (1 : Fin n → ℝ)) = δ x + a

/-- **Location-invariant function** (of the data): `u(x + a·𝟙) = u(x)`. -/
def IsLocInvariant (u : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (a : ℝ) (x : Fin n → ℝ), u (x + a • (1 : Fin n → ℝ)) = u x

/-- The **difference statistic** `y = (x₁ − xₙ, …, x_{n−1} − xₙ)`, the maximal invariant
of the translation group (`m + 1` observations reduce to `m` differences). -/
def diffs {m : ℕ} (x : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun i => x i.castSucc - x (Fin.last m)

/-- Location risk of an estimator at the base parameter (`ξ = 0`) for loss
`ρ(d − ξ)`; for equivariant estimators the risk is this constant. -/
noncomputable def locRisk (f : (Fin n → ℝ) → ℝ) (ρ : ℝ → ℝ) (δ : (Fin n → ℝ) → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (ρ (δ x)) ∂(locationBase f)

/-- **Minimum risk equivariant (MRE)** location estimator: measurable, equivariant, and
of minimal (constant) risk among all such. -/
def IsLocMRE (f : (Fin n → ℝ) → ℝ) (ρ : ℝ → ℝ) (δ : (Fin n → ℝ) → ℝ) : Prop :=
  Measurable δ ∧ IsLocEquivariant δ ∧
    ∀ δ', Measurable δ' → IsLocEquivariant δ' → locRisk f ρ δ ≤ locRisk f ρ δ'

/-- The **Pitman estimator** of location under squared error, in closed form:
`δ*(x) = (∫ u·f(x − u·𝟙) du) / (∫ f(x − u·𝟙) du)`. -/
noncomputable def pitmanEstimator (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∫ u : ℝ, u * f (x - u • (1 : Fin n → ℝ))) / (∫ u : ℝ, f (x - u • (1 : Fin n → ℝ)))

end Location

/-! ## The scale model on `Fin n → ℝ` -/

section Scale

variable {n : ℕ}

/-- The scale family generated by a base measure `P₀` on `Fin n → ℝ`: the law of
`τ • X` for `X ∼ P₀`, indexed by `τ > 0` (junk for `τ ≤ 0` — theorems carry `0 < τ`). -/
noncomputable def scaleFamily (P₀ : Measure (Fin n → ℝ)) (τ : ℝ) :
    Measure (Fin n → ℝ) :=
  P₀.map (τ • ·)

/-- **Scale-equivariant estimator of degree `r`** (estimand `τʳ`):
`δ(τ·x) = τʳ·δ(x)` for `τ > 0`. -/
def IsScaleEquivariant (r : ℕ) (δ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ⦃τ : ℝ⦄, 0 < τ → ∀ x, δ (τ • x) = τ ^ r * δ x

/-- The **scale-invariant statistic** `z = ((x₁/xₙ, …, x_{m}/xₙ), xₙ/|xₙ|)`: coordinate
ratios plus the sign of the last coordinate — the maximal invariant of the scale
group off `{xₙ = 0}`. -/
noncomputable def scaleZ {m : ℕ} (x : Fin (m + 1) → ℝ) : (Fin m → ℝ) × ℝ :=
  (fun i => x i.castSucc / x (Fin.last m), x (Fin.last m) / |x (Fin.last m)|)

/-- Scale risk at the base parameter (`τ = 1`) for loss `γ(d/τʳ)`; constant for
equivariant estimators. -/
noncomputable def scaleRisk (P₀ : Measure (Fin n → ℝ)) (γ : ℝ → ℝ)
    (δ : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (γ (δ x)) ∂P₀

/-- **MRE scale estimator** of degree `r`. -/
def IsScaleMRE (P₀ : Measure (Fin n → ℝ)) (γ : ℝ → ℝ) (r : ℕ)
    (δ : (Fin n → ℝ) → ℝ) : Prop :=
  Measurable δ ∧ IsScaleEquivariant r δ ∧
    ∀ δ', Measurable δ' → IsScaleEquivariant r δ' →
      scaleRisk P₀ γ δ ≤ scaleRisk P₀ γ δ'

end Scale

end StatLean.PointEstimation
