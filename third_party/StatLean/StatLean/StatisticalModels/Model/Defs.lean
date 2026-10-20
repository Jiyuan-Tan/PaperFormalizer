module
public import Mathlib.Probability.Kernel.Basic

@[expose] public section

/-!
# Statistical models — the carrier conventions and the kernel bridge

The `StatisticalModels` area works over the library's canonical model carrier: a **bare family
of probability measures** `P : Θ → Measure 𝓧` indexed by an arbitrary parameter type `Θ`, with
`IsProbabilityMeasure (P θ)` carried as an instance argument by consumers (the convention fixed
in `StatLean.PointEstimation.Model.Defs`). Because `Θ` is unconstrained, parametric models
(`Θ` finite-dimensional), nonparametric models (`Θ` a class of functions or measures) and
semiparametric models (`Θ = Ψ × Η`) are *instantiations* of the same definitions, never separate
structures.

This file supplies the **bridge to Mathlib's measurable carrier** `Kernel Θ 𝓧` — a Markov kernel
*is* a measurably-parameterized bare family — plus the Halmos–Savage domination predicate:

* `toKernel P hP` — bundle a bare family with a measurability proof as a `Kernel Θ 𝓧`; the
  reverse direction is the kernel's coercion `⇑κ`. Round trips are definitional.
* `IsDominatedFamily P μ` — every member of the family is absolutely continuous with respect to
  the σ-finite reference measure `μ` (the dominated-model hypothesis of classical statistics).

**Reference.** E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.1 (the model
as a family of distributions) and §1.4 (dominated families). (`TPE2 §1.1`, `TPE2 §1.4`.)

**Proof formalization notes.** Laptop-only data model — definitions and `rfl`-level lemmas only.
We deliberately introduce **no new structure**: the bare-family convention is already canonized
by `PointEstimation.Model.Defs`, and `ProbabilityTheory.Kernel` together with `[IsMarkovKernel]`
already *is* the bundled measurable model, so a wrapper structure would only orphan the existing
consuming API (`Identifiable`, risks, sufficiency, tests). The measurability proof `hP` demanded
by `toKernel` is Lean-side plumbing for the Giry-monad σ-algebra on `Measure 𝓧`; it has no
counterpart in the books, which never parameterize measurably in `θ`. Substantive lemmas about
the bridge (Markov ↔ pointwise-probability, agreement of the model calculus with Mathlib's
kernel algebra) live in `Model.KernelAgreement`.

**Bibliographic comments.** The formulation of a statistical model as an indexed family of
probability measures is due to A. Wald (*Statistical Decision Functions*, Wiley, 1950); the
kernel (transition-probability) presentation is standard in the decision-theoretic literature
following L. Le Cam (*Asymptotic Methods in Statistical Decision Theory*, Springer, 1986, Ch. 1)
and N. N. Chentsov (*Statistical Decision Rules and Optimal Inference*, Nauka, 1972). Domination
of a family by a single σ-finite measure is the framework of P. R. Halmos and L. J. Savage,
"Application of the Radon–Nikodym theorem to the theory of sufficient statistics," *Ann. Math.
Statist.* **20** (1949), 225–241.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- Bundle a measurably-parameterized bare family `P : Θ → Measure 𝓧` as a Mathlib kernel.
The reverse direction is the coercion `⇑κ : Θ → Measure 𝓧`; both round trips are `rfl`. -/
def toKernel (P : Θ → Measure 𝓧) (hP : Measurable P) : Kernel Θ 𝓧 :=
  ⟨P, hP⟩

@[simp]
theorem toKernel_apply (P : Θ → Measure 𝓧)
    -- LEAN-ONLY: measurability in θ, the datum `toKernel` bundles; no scope change
    (hP : Measurable P) (θ : Θ) :
    toKernel P hP θ = P θ := rfl

@[simp]
theorem coe_toKernel (P : Θ → Measure 𝓧)
    -- LEAN-ONLY: measurability in θ, the datum `toKernel` bundles; no scope change
    (hP : Measurable P) : ⇑(toKernel P hP) = P := rfl

@[simp]
theorem toKernel_coe (κ : Kernel Θ 𝓧) : toKernel ⇑κ κ.measurable = κ := rfl

/-- **Dominated family** (Halmos–Savage): every member of the model is absolutely continuous
with respect to the reference measure `μ`. This is the measure-level counterpart of the
density-based carrier `AsymptoticStatistics.ParametricFamily` + `IsPDFOf`; the two are
interconverted in `Adapters.ParametricFamily`. -/
def IsDominatedFamily {Θ' : Type*} (P : Θ' → Measure 𝓧) (μ : Measure 𝓧) : Prop :=
  ∀ θ, P θ ≪ μ

end StatLean.StatisticalModels
