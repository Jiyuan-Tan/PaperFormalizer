module
public import StatLean.StatisticalModels.Model.KernelAgreement
public import StatLean.Bayesian.Experiment.Defs
public import StatLean.Bayesian.Hierarchical.Defs
public import StatLean.Bayesian.ForMathlib.IIDKernel
public import StatLean.Bayesian.ForMathlib.IIDSeqKernel

@[expose] public section

/-!
# Adapter: the model calculus and the Bayesian area

Bridges to `StatLean.Bayesian` (imported, never redefined):

* `experimentOf` — a measurably-parameterized probability model plus a prior is a
  `BayesExperiment` (Robert Def 1.2.1), with `predictive` agreeing with the model-side
  observation of the prior;
* `iid_coe` — the area's `iid` agrees with the Bayesian area's `iidKernel` on kernel models
  (tying down that idiom; no fourth iid encoding is introduced);
* `dataMarginal_eq_bind_observe` — the hierarchical prior predictive
  (`HierBayesExperiment.dataMarginal`) is the hyperprior bound through the model-calculus
  observation of the prior kernel by the likelihood: **latent-variable marginalization on the
  Bayes side is the calculus' `observe` composed with the hyperprior** — one bridge, no
  duplication.

**Reference.** C. P. Robert, *The Bayesian Choice*, 2nd ed., Springer, 2007, §1.2
Definition 1.2.1 and §1.4 (joint, marginal, posterior); A. Gelman et al., *Bayesian Data
Analysis*, 3rd ed., 2014, §5.2 (hierarchical models).

**Proof formalization notes.** `experimentOf` is definitional assembly (`toKernel` +
`isMarkovKernel_toKernel_iff`); `iid_coe` is `funext` + `iidKernel_apply` (both sides are
`Measure.pi` of the kernel member — `rfl`-level), and likewise `iidSeq_coe` via
`iidSeqKernel_apply` (the Bayesian sequence kernel is itself `Measure.infinitePi`-based, so
the agreement is definitional, not a projective-limit argument).

**Bibliographic comments.** The kernel formulation of the Bayesian model is the
regular-conditional-distribution tradition of Doob; see the bibliographic notes of
`Bayesian.Experiment.Defs`.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

open StatLean.Bayesian

variable {Θ : Type*} [MeasurableSpace Θ] {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- A measurably-parameterized probability model plus a prior is a Bayesian statistical model
(Robert Def 1.2.1). -/
noncomputable def experimentOf (P : Θ → Measure 𝓧) (hP : Measurable P)
    -- USER-INPUT: the model members are probability laws (constitutive for Robert Def 1.2.1)
    [∀ θ, IsProbabilityMeasure (P θ)]
    (π : Measure Θ)
    -- USER-INPUT: the prior is a probability distribution (constitutive, Robert Def 1.2.1)
    [IsProbabilityMeasure π] :
    BayesExperiment Θ 𝓧 where
  prior := π
  likelihood := toKernel P hP
  priorIsProbability := ‹_›
  likelihoodIsMarkov := (isMarkovKernel_toKernel_iff P hP).mpr ‹_›

/-- The prior predictive of `experimentOf` is the model-side mixture of the model over the
prior (Robert §1.4 (b)). -/
-- LEAN-ONLY: measurability in θ of the family; kernel-side plumbing
theorem predictive_experimentOf (P : Θ → Measure 𝓧) (hP : Measurable P)
    -- USER-INPUT: the model members are probability laws and the prior is a probability
    -- distribution (constitutive, Robert Def 1.2.1)
    [∀ θ, IsProbabilityMeasure (P θ)] (π : Measure Θ) [IsProbabilityMeasure π] :
    (experimentOf P hP π).predictive = (toKernel P hP) ∘ₘ π := rfl

/-- The area's `iid` agrees with the Bayesian `iidKernel` on kernel models. -/
-- LEAN-ONLY: Markov-kernel instance needed to elaborate iidKernel; no scope change
theorem iid_coe (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (n : ℕ) :
    iid ⇑κ n = ⇑(Bayesian.iidKernel κ n) := rfl

/-- **Latent marginalization agreement**: the hierarchical prior predictive is the hyperprior
bound through the observation of the prior kernel by the likelihood (Gelman §5.2). -/
theorem dataMarginal_eq_bind_observe {Λ : Type*} [MeasurableSpace Λ]
    (H : HierBayesExperiment Λ Θ 𝓧) :
    H.dataMarginal = Measure.bind H.hyperPrior (observe ⇑H.priorKernel H.likelihood) := by
  rw [observe_coe]
  rfl

/-- The area's `iidSeq` agrees with the Bayesian `iidSeqKernel` on kernel models
(definitional through `iidSeqKernel_apply`). -/
-- LEAN-ONLY: Markov-kernel instance needed to elaborate iidKernel; no scope change
theorem iidSeq_coe (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] :
    iidSeq ⇑κ = ⇑(Bayesian.iidSeqKernel κ) := rfl

end StatLean.StatisticalModels
