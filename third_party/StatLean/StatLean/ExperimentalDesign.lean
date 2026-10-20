module
public import StatLean.ExperimentalDesign.ForMathlib.PMFExpectation
public import StatLean.ExperimentalDesign.Core.FinitePopulation
public import StatLean.ExperimentalDesign.Core.Design
public import StatLean.ExperimentalDesign.Core.Contrast
public import StatLean.ExperimentalDesign.Core.Stratification
public import StatLean.ExperimentalDesign.Randomization.CompleteRandomization
public import StatLean.ExperimentalDesign.Randomization.SamplingEquivalence
public import StatLean.ExperimentalDesign.Randomization.Blocked
public import StatLean.ExperimentalDesign.SurveySampling.InclusionProbability
public import StatLean.ExperimentalDesign.SurveySampling.HorvitzThompson
public import StatLean.ExperimentalDesign.SurveySampling.SimpleRandomSampling
public import StatLean.ExperimentalDesign.Factorial.TwoLevel
public import StatLean.ExperimentalDesign.Analysis.OneWayANOVA
public import StatLean.ExperimentalDesign.Stratified.ProductDesign
public import StatLean.ExperimentalDesign.Stratified.StratifiedEstimator

@[expose] public section

/-!
# StatLean.ExperimentalDesign — area umbrella

Design of experiments and design-based survey sampling in the finite randomisation
model: finite populations, randomization/sampling designs as `PMF`s, completely
randomised and blocked designs, inclusion probabilities and Horvitz–Thompson
estimation, contrast algebra, two-level factorial characters, and the one-way ANOVA
identity.  Reference: R. Mead, *The Design of Experiments: Statistical Principles for
Practical Applications*, Cambridge University Press, 1988 (`Mead §X.Y` in tags);
survey-sampling results follow Horvitz–Thompson (1952) and Cochran (1977).
-/
