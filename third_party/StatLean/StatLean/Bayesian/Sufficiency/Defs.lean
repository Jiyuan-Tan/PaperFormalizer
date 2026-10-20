module
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Basic

@[expose] public section

/-!
# Sufficiency — core data model (statistic kernels, sufficiency, factorized likelihoods)

Data model for statistical sufficiency:

* `statKernel K T hT` — the **statistic-induced experiment** `K_T = T_\# K`, sending `θ` to the
  law of `T(x)` under `K(θ, ·)`;
* `IsSufficient` — sufficiency as kernel factorization: a reconstruction kernel `Q : S ⇝ 𝓧` with
  `K = Q ∘ₖ K_T` (the prior-free, Halmos–Savage-style definition, recorded for the library — the
  theorems of this area use the dominated form below);
* `IsFactorizedLikelihood` — the **Fisher–Neyman factorization** `p(θ, x) = g(θ, T x) · h(x)` of a
  dominated model's density, the criterion every conjugacy argument consumes.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.3.1, Definition 1.3.1 (sufficient statistic) and the
factorization theorem (stated inline, p. 14).

**Proof formalization notes.** Laptop-only data model — definitions only. `statKernel` is
`Kernel.deterministic T hT ∘ₖ K`, so `statKernel K T hT θ = (K θ).map T` (proved in
`Sufficiency.Factorization`). `IsSufficient` is the existence of a Markov reconstruction kernel
factorizing `K` through `K_T`; the fiber-support refinement (`Q(s, {x | T x = s}) = 1`) and the
equivalence with the factorization criterion (Halmos–Savage) are deliberately out of scope for
this batch (recorded in `notes/bayesian/roadmap.md`). `IsFactorizedLikelihood` is a plain
pointwise equation in `ℝ≥0∞`.

**Bibliographic comments.** Sufficiency is due to R. A. Fisher ("On the mathematical foundations
of theoretical statistics," *Philosophical Transactions of the Royal Society A* 222 (1922),
309–368); the factorization criterion was formalized by J. Neyman ("Sur un teorema concernente le
cosiddette statistiche sufficienti," *Giorn. Ist. Ital. Attuari* 6 (1935), 320–334) and given its
measure-theoretic form by P. R. Halmos and L. J. Savage ("Application of the Radon–Nikodym theorem
to the theory of sufficient statistics," *Ann. Math. Statist.* 20 (1949), 225–241).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 S : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  [mS : MeasurableSpace S]

/-- The **statistic-induced experiment** `K_T = T_# K`: the kernel sending `θ` to the law of
`T(x)` for `x ~ K(θ, ·)` (Robert §1.3.1). -/
@[reducible]
noncomputable def statKernel (K : Kernel Θ 𝓧) {T : 𝓧 → S} (hT : Measurable T) : Kernel Θ S :=
  Kernel.deterministic T hT ∘ₖ K

/-- **Sufficiency as kernel factorization** (prior-free form): there is a Markov reconstruction
kernel `Q : S ⇝ 𝓧` with `K = Q ∘ₖ K_T` (Robert §1.3.1, Definition 1.3.1; Halmos–Savage 1949).
Recorded for the library; the Batch-2 theorems use the dominated Fisher–Neyman form
`IsFactorizedLikelihood`. -/
def IsSufficient (K : Kernel Θ 𝓧) {T : 𝓧 → S} (hT : Measurable T) : Prop :=
  ∃ Q : Kernel S 𝓧, IsMarkovKernel Q ∧ K = Q ∘ₖ statKernel K hT

/-- **Fisher–Neyman factorized likelihood**: the density splits as
`p(θ, x) = g(θ, T x) · h(x)` (Robert §1.3.1, the factorization theorem, p. 14). -/
def IsFactorizedLikelihood (p : Θ → 𝓧 → ℝ≥0∞) (T : 𝓧 → S)
    (g : Θ → S → ℝ≥0∞) (h : 𝓧 → ℝ≥0∞) : Prop :=
  ∀ θ x, p θ x = g θ (T x) * h x

end StatLean.Bayesian
