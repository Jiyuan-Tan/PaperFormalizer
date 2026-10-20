module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Complete and ancillary statistics — core data model

A family of laws `Q : Θ → Measure S` is **complete** when the only (integrable, real)
functions with identically vanishing mean are a.e. zero, and **boundedly complete** when
the same holds among bounded functions. A statistic `T` is complete for a model `P` when
the family of its laws is; a statistic `V` is **ancillary** when its law does not depend
on `θ`, and **first-order ancillary** when its mean does not.

* `IsCompleteFamily Q`, `IsBoundedlyCompleteFamily Q` — family-of-laws forms;
* `IsCompleteStat P T`, `IsBoundedlyCompleteStat P T` — statistic forms (laws of `T`);
* `IsAncillary P V`, `IsFirstOrderAncillary P V`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.6
(Sufficient Statistics), the definitions of a complete statistic and of an ancillary
statistic. (`TPE2 §1.6`.)

**Proof formalization notes.**
* Completeness is stated family-first so that it applies uniformly to laws of
  statistics, to exponential families on their natural statistic scale, and to the
  bounded variant needed by similar-test theory.
* `IsCompleteFamily → IsBoundedlyCompleteFamily` for probability families (bounded ⇒
  integrable) is proved in `Completeness.Basic` lemmas where needed; the two predicates
  are kept independent here.
* The full (unbounded) variant quantifies over measurable, everywhere-integrable `f`;
  conclusions are `f =ᵐ[Q θ] 0` for every `θ` (the classical "a.e. 𝒫" conclusion).

**Bibliographic comments.** Completeness and its use for unbiased estimation and
similar tests are due to E. L. Lehmann and H. Scheffé ("Completeness, similar regions,
and unbiased estimation," *Sankhyā* **10** (1950), 305–340; **15** (1955), 219–236).
Ancillarity goes back to R. A. Fisher (*Statistical Methods and Scientific Inference*,
Oliver & Boyd, 1956); the independence theorem linking the two notions is due to
D. Basu ("On statistics independent of a complete sufficient statistic," *Sankhyā*
**15** (1955), 377–380).
-/

open MeasureTheory

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- **Complete family of laws**: every measurable, everywhere-integrable `f : S → ℝ`
with `∫ f dQ_θ = 0` for all `θ` vanishes `Q θ`-a.e. for all `θ`. -/
def IsCompleteFamily (Q : Θ → Measure S) : Prop :=
  ∀ f : S → ℝ, Measurable f → (∀ θ, Integrable f (Q θ)) →
    (∀ θ, ∫ s, f s ∂(Q θ) = 0) → ∀ θ, f =ᵐ[Q θ] 0

/-- **Boundedly complete family of laws**: the completeness test restricted to
uniformly bounded measurable functions. -/
def IsBoundedlyCompleteFamily (Q : Θ → Measure S) : Prop :=
  ∀ f : S → ℝ, Measurable f → (∃ C, ∀ s, |f s| ≤ C) →
    (∀ θ, ∫ s, f s ∂(Q θ) = 0) → ∀ θ, f =ᵐ[Q θ] 0

/-- A statistic `T` is **complete** for the model `P` when the family of its laws is. -/
def IsCompleteStat (P : Θ → Measure 𝓧) (T : 𝓧 → S) : Prop :=
  IsCompleteFamily fun θ => (P θ).map T

/-- A statistic `T` is **boundedly complete** for `P` when the family of its laws is. -/
def IsBoundedlyCompleteStat (P : Θ → Measure 𝓧) (T : 𝓧 → S) : Prop :=
  IsBoundedlyCompleteFamily fun θ => (P θ).map T

/-- A statistic `V` is **ancillary**: its law is the same under every parameter. -/
def IsAncillary (P : Θ → Measure 𝓧) (V : 𝓧 → S) : Prop :=
  ∀ θ θ', (P θ).map V = (P θ').map V

/-- A real statistic `V` is **first-order ancillary**: its mean is the same under every
parameter. -/
def IsFirstOrderAncillary (P : Θ → Measure 𝓧) (V : 𝓧 → ℝ) : Prop :=
  ∀ θ θ', ∫ x, V x ∂(P θ) = ∫ x, V x ∂(P θ')

end StatLean.PointEstimation
