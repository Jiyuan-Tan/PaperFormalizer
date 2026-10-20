module
public import StatLean.PointEstimation.Model.Defs

@[expose] public section

/-!
# Identifiability of targets — estimands as functionals of the law

`StatLean.PointEstimation.Identifiable` (`Function.Injective P`) is the library's notion of
model identifiability; this file adds the two target-level notions the model calculus needs:

* `IdentifiesTarget P ψ` — the estimand `ψ : Θ → Γ` is **identified** by the model: it factors
  through the law map (`P θ₁ = P θ₂ → ψ θ₁ = ψ θ₂`). Definitionally
  `Function.FactorsThrough ψ P`. Target identifiability is weaker than `Identifiable P` and is
  the operative notion for semiparametric models `Θ = Ψ × Η` with target `ψ = Prod.fst`;
* `lawFunctional P ψ` — the estimand realized as a **functional of the law**
  `Measure 𝓧 → Γ` via `Function.extend`, well-defined on the model range exactly when
  `IdentifiesTarget P ψ` (`Identifiability.Transfer.lawFunctional_comp`).

No `Estimand` structure: a bare function `ψ : Θ → Γ` carries no constitutive content beyond
its values, so bundling it would violate the area's hypothesis discipline.

**Reference.** Identifiability of a parametrization and of functions of the parameter:
E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998, §1.5,
Definition 5.2 and the surrounding discussion (`TPE2 §1.5`).

**Proof formalization notes.** Laptop-only — definitions only; the characterizations and the
transfer theorems under the model calculus live in `Identifiability.Transfer`. `lawFunctional`
junk-values to `Classical.arbitrary Γ` off the model range (`Function.extend`'s fallback);
statements about it therefore always carry the `IdentifiesTarget` hypothesis. The import of
`PointEstimation.Model.Defs` is this area's one deliberate concept-layer dependency (precedent:
that file itself imports `AsymptoticStatistics.ParametricFamily.Defs`).

**Bibliographic comments.** Identification of structural characteristics is due to
T. C. Koopmans and O. Reiersøl, "The identification of structural characteristics," *Ann.
Math. Statist.* **21** (1950), 165–181; estimands as functionals of the underlying law go back
to R. von Mises, "On the asymptotic distribution of differentiable statistical functions,"
*Ann. Math. Statist.* **18** (1947), 309–348.
-/

open MeasureTheory

namespace StatLean.StatisticalModels

variable {Θ Γ : Type*} {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **Target identifiability**: the estimand `ψ` factors through the law map — laws determine
target values (TPE2 §1.5; Koopmans–Reiersøl 1950). Definitionally
`Function.FactorsThrough ψ P`. -/
def IdentifiesTarget (P : Θ → Measure 𝓧) (ψ : Θ → Γ) : Prop :=
  Function.FactorsThrough ψ P

/-- Unfolding characterization of `IdentifiesTarget` (definitional). -/
theorem identifiesTarget_iff {P : Θ → Measure 𝓧} {ψ : Θ → Γ} :
    IdentifiesTarget P ψ ↔ ∀ ⦃θ₁ θ₂⦄, P θ₁ = P θ₂ → ψ θ₁ = ψ θ₂ :=
  Iff.rfl

/-- The estimand as a **functional of the law**, via `Function.extend`; well-defined on the
model range when `IdentifiesTarget P ψ`, junk (`Classical.arbitrary`) off it (von Mises 1947
statistical functionals). -/
noncomputable def lawFunctional (P : Θ → Measure 𝓧) (ψ : Θ → Γ) [Nonempty Γ] :
    Measure 𝓧 → Γ :=
  Function.extend P ψ fun _ => Classical.arbitrary Γ

end StatLean.StatisticalModels
