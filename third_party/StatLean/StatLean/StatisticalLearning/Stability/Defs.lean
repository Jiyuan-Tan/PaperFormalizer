module
public import StatLean.StatisticalLearning.Core.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# Algorithmic stability — replace-one data model

The replace-one sample `S^{(i)}` (SSBD §13.2), the averaged replace-one
stability gap of a learning rule (the right-hand side of SSBD Theorem 13.2),
on-average-replace-one stability (SSBD Definition 13.3), and the regularized
loss minimization (RLM/Tikhonov) objective and minimizer predicate
(SSBD Eqs. (13.1)–(13.2)).

**Reference.** SSBD Ch. 13. Transcriptions:
`notes/statistical_learning/book_statements/ch12-13.md`.

**Formalization notes.**
* The joint law of `(S, z')` is `(sampleLaw D n).prod D` and the uniform index
  average is the explicit `n⁻¹ ∑ᵢ` — no `[m]`-valued random variable.
* Stability is defined **on-average** exactly as the book's only formal notion
  (Definition 13.3); the Lipschitz analysis later proves the stronger
  pointwise bound and relaxes it.
* The RLM *minimizer* is a predicate (`IsRLMMin`); the selector is data
  downstream, per the hypothesis discipline for argmins.
* This file is a laptop-only Defs surface: definitions only, 0-sorry.

**Bibliographic comments.** Uniform stability and its generalization bounds
are due to O. Bousquet & A. Elisseeff, "Stability and generalization," *JMLR*
2 (2002), 499–526; the on-average form and the fitting-stability tradeoff
follow SSBD Ch. 13.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z H : Type*} {n : ℕ}

/-- The replace-one sample `S^{(i)}` (SSBD §13.2): replace the `i`-th example
of `s` by `z`. -/
def replaceOne (s : Sample Z n) (i : Fin n) (z : Z) : Sample Z n :=
  Function.update s i z

/-- **Averaged replace-one stability gap** of a learning rule `A` at sample
size `n` (SSBD Theorem 13.2 RHS):
`E_{(S,z')∼D^{n+1}} n⁻¹ ∑ᵢ [ℓ(A(S^{(i)}), zᵢ) − ℓ(A(S), zᵢ)]`. Edge behavior:
junk `0` at `n = 0` or non-integrable integrands. -/
noncomputable def stabilityGap [MeasurableSpace Z] (D : Measure Z)
    (ℓ : H → Z → ℝ) (A : Sample Z n → H) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n,
    ∫ p : Sample Z n × Z,
      (ℓ (A (replaceOne p.1 i p.2)) (p.1 i) - ℓ (A p.1) (p.1 i))
      ∂((sampleLaw D n).prod D)

/-- **On-average-replace-one stability with rate `rate`** (SSBD Definition
13.3, one size class per `n`): for every distribution the averaged replace-one
gap is at most `rate n`. -/
def OnAvgReplaceOneStableWith [MeasurableSpace Z] (ℓ : H → Z → ℝ)
    (A : ∀ m : ℕ, Sample Z m → H) (rate : ℕ → ℝ) : Prop :=
  ∀ (D : Measure Z), IsProbabilityMeasure D →
    ∀ m : ℕ, stabilityGap D ℓ (A m) ≤ rate m

section RLM

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **`λ`-strong convexity** (SSBD Definition 13.4), inequality form on the
whole space:
`f(aw + bu) ≤ a f(w) + b f(u) − (λ/2)·ab·‖w − u‖²` for every convex
combination. `StronglyConvexWith 0 f` is plain (midpoint-free) convexity. -/
def StronglyConvexWith (lam : ℝ) (f : W → ℝ) : Prop :=
  ∀ w u : W, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • w + b • u) ≤ a * f w + b * f u - lam / 2 * (a * b) * ‖w - u‖ ^ 2

/-- **The RLM (Tikhonov) objective** (SSBD Eqs. (13.1)–(13.2)):
`L_S(w) + λ‖w‖²`. -/
noncomputable def rlmObjective (ℓ : W → Z → ℝ) (lam : ℝ) (s : Sample Z n)
    (w : W) : ℝ :=
  empRisk ℓ s w + lam * ‖w‖ ^ 2

/-- **RLM minimizer, predicate form** (SSBD Eq. (13.2)): `w` globally
minimizes the Tikhonov objective (the book's RLM is improper — the argmin
ranges over the whole space). -/
def IsRLMMin (ℓ : W → Z → ℝ) (lam : ℝ) (s : Sample Z n) (w : W) : Prop :=
  ∀ v : W, rlmObjective ℓ lam s w ≤ rlmObjective ℓ lam s v

end RLM

end StatLean.StatisticalLearning
