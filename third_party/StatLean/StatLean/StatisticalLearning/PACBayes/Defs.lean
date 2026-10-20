module
public import StatLean.StatisticalLearning.Core.Defs

@[expose] public section

/-!
# PAC-Bayes — Gibbs risks

The randomized-predictor data model of SSBD Ch. 31: a prior `P` and posterior
`Q` over a hypothesis index, and the Gibbs (posterior-averaged) true and
empirical risks `L_D(Q) = E_{h∼Q}[L_D(h)]`, `L_S(Q) = E_{h∼Q}[L_S(h)]`.

**Reference.** SSBD §31.1 (p. 364). Transcription:
`notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** Round 1 works over a **countable** hypothesis index
`ι` with the discrete σ-algebra (`DiscreteMeasurableSpace`), priors/posteriors
as probability `Measure ι`, and KL divergence as Mathlib's
`InformationTheory.klDiv`. The Gibbs average is a plain Bochner integral over
`ι` — junk `0` when not integrable (bounded losses make it genuine). This
file is a laptop-only Defs surface: definitions only, 0-sorry.

**Bibliographic comments.** PAC-Bayes bounds originate with D. A. McAllester,
"Some PAC-Bayesian theorems," *Machine Learning* 37 (1999), 355–363; the form
proved here follows SSBD Theorem 31.1.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {ι : Type*} [MeasurableSpace ι]

/-- **Gibbs average** (SSBD p. 364): the posterior expectation `E_{k∼Q}[r k]`
of an index functional — instantiated at `r = risk D F` for `L_D(Q)` and at
`r = empRisk F s` for `L_S(Q)`. -/
noncomputable def gibbsAvg (Q : Measure ι) (r : ι → ℝ) : ℝ :=
  ∫ k, r k ∂Q

end StatLean.StatisticalLearning
