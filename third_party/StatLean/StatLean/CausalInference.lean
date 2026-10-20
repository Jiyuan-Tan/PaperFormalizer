module
public import StatLean.CausalInference.ForMathlib.CondAlgebra
public import StatLean.CausalInference.Core.FiniteDefs
public import StatLean.CausalInference.Core.FinitePopulation
public import StatLean.CausalInference.Core.PopulationDefs
public import StatLean.CausalInference.Randomized.CompleteRandomization
public import StatLean.CausalInference.Randomized.DifferenceInMeans
public import StatLean.CausalInference.Randomized.Neyman
public import StatLean.CausalInference.Randomized.VarianceEstimator
public import StatLean.CausalInference.Randomized.Fisher
public import StatLean.CausalInference.Randomized.Stratified
public import StatLean.CausalInference.Randomized.MatchedPairs
public import StatLean.CausalInference.Randomized.RegressionAdjustment
public import StatLean.CausalInference.Randomized.SuperPopulationBridge
public import StatLean.CausalInference.Observational.Ignorability
public import StatLean.CausalInference.Observational.SelectionBias
public import StatLean.CausalInference.Observational.Standardization
public import StatLean.CausalInference.Observational.PropensityScore
public import StatLean.CausalInference.Observational.IPW
public import StatLean.CausalInference.Observational.AIPW
public import StatLean.CausalInference.Observational.ATT
public import StatLean.CausalInference.Observational.Subclassification
public import StatLean.CausalInference.Observational.Matching
public import StatLean.CausalInference.Observational.Trimming
public import StatLean.CausalInference.Sensitivity.ManskiBounds
public import StatLean.CausalInference.Sensitivity.EValue
public import StatLean.CausalInference.Sensitivity.Rosenbaum
public import StatLean.CausalInference.IV.Defs
public import StatLean.CausalInference.IV.ComplianceTypes
public import StatLean.CausalInference.IV.LATE
public import StatLean.CausalInference.IV.InstrumentalInequalities
public import StatLean.CausalInference.IV.LinearIV

@[expose] public section

/-!
# StatLean.CausalInference — area umbrella

Causal inference in the **potential-outcomes framework**, after P. Ding, *A First Course in
Causal Inference* (arXiv:2305.18793v2, 2023; published by Chapman & Hall/CRC, 2024) — `Ding`
in tags — and G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and
Biomedical Sciences* (Cambridge University Press, 2015) — `IR` in tags.

The area has two halves, matching the two halves of the subject.

* **Design-based (finite population).** `Core/FiniteDefs` fixes the science table of a
  finite population and models an assignment mechanism as a uniform distribution on a
  finite set of assignment vectors. On this base: the fundamental problem of causal
  inference (`Core/FinitePopulation`), the complete-randomization assignment moments
  (`Randomized/CompleteRandomization`), Fisher's randomization test and its exact validity
  (`Randomized/Fisher`), Neyman's unbiasedness and exact variance
  (`Randomized/DifferenceInMeans`, `Randomized/Neyman`) with the conservativeness of his
  variance estimator (`Randomized/VarianceEstimator`), stratified and matched-pair
  experiments (`Randomized/Stratified`, `Randomized/MatchedPairs`), regression adjustment
  (`Randomized/RegressionAdjustment`) and the bridge to a superpopulation
  (`Randomized/SuperPopulationBridge`). No measure theory is used at this layer.
* **Population (observational).** `Core/PopulationDefs` places the treatment, the two
  potential outcomes and a **discrete** covariate on a probability space, with conditioning
  by `ProbabilityTheory.cond`. On this base: selection bias
  (`Observational/SelectionBias`), what unconfoundedness buys
  (`Observational/Ignorability`), identification by standardization
  (`Observational/Standardization`), the propensity score and its balancing property
  (`Observational/PropensityScore`), inverse-probability weighting (`Observational/IPW`),
  the doubly robust functional (`Observational/AIPW`), the effect on the treated and the
  weighted estimands (`Observational/ATT`), and the design-of-observational-studies layer
  — subclassification, matching, overlap and trimming
  (`Observational/{Subclassification, Matching, Trimming}`).

Two further groups sit on top: **sensitivity analysis** (`Sensitivity/ManskiBounds`,
`Sensitivity/EValue`, `Sensitivity/Rosenbaum`) — what can still be said when
unconfoundedness fails — and **instrumental variables** (`IV/*`), where noncompliance is
handled through compliance types, culminating in the LATE/CACE theorem, the testable
instrumental inequalities, and the equivalence with the linear-IV covariance ratio.

**Scope.** Releases 1–6 of `Causal_plan.md`: randomized experiments, observational
identification, design of observational studies, sensitivity analysis and instrumental
variables. Regression discontinuity, principal stratification, mediation and time-varying
treatments (Release 7) are out of scope for this batch, as are general graphical
identification, interference and modern semiparametric efficiency theory. The observational
half is formalized for a **finite covariate type**, which is the setting in which Ding
states the identification formulas concretely (e.g. eq. (10.8)). Scope revisions and the
statement repairs made during the batch are recorded in `notes/causal_inference/roadmap.md`.

**Relation to `StatLean.ExperimentalDesign`.** That area models randomization and sampling
designs as `PMF`s and develops Horvitz–Thompson estimation for *survey sampling*; this area
models designs as uniform distributions on assignment vectors and develops *causal*
estimands (potential outcomes, science tables, the sharp null). The two are deliberately
independent: the shared combinatorial content — the moments of simple random sampling — is
taken by both from `StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments`.

Laptop-only file: edited by the laptop session at wave merges.
-/
