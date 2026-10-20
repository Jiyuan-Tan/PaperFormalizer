module
public import StatLean.StatisticalLearning.Core.Defs
public import StatLean.StatisticalLearning.Core.SampleLaw
public import StatLean.StatisticalLearning.Core.ERM
public import StatLean.StatisticalLearning.FiniteClass.UniformConvergence
public import StatLean.StatisticalLearning.FiniteClass.AgnosticPAC
public import StatLean.StatisticalLearning.FiniteClass.RealizablePAC
public import StatLean.StatisticalLearning.Rademacher.Defs
public import StatLean.StatisticalLearning.Rademacher.Structural
public import StatLean.StatisticalLearning.Rademacher.Contraction
public import StatLean.StatisticalLearning.Rademacher.Symmetrization
public import StatLean.StatisticalLearning.Rademacher.Generalization
public import StatLean.StatisticalLearning.VC.Bridge
public import StatLean.StatisticalLearning.VC.AgnosticPAC
public import StatLean.StatisticalLearning.Stability.Defs
public import StatLean.StatisticalLearning.Stability.ReplaceOne
public import StatLean.StatisticalLearning.Stability.Generalization
public import StatLean.StatisticalLearning.Stability.RegularizedERM
public import StatLean.StatisticalLearning.PACBayes.Defs
public import StatLean.StatisticalLearning.PACBayes.ChangeOfMeasure
public import StatLean.StatisticalLearning.PACBayes.Generalization

@[expose] public section

/-!
# StatisticalLearning

Statistical learning theory — the formal mathematical theory of why
data-dependent predictors generalize. Reference: Shalev-Shwartz & Ben-David,
*Understanding Machine Learning* (Cambridge, 2014) (`SSBD §X.Y` in tags).

* `Core/` — risk, empirical risk, ERM predicates, `ε`-representative samples,
  PAC/uniform-convergence learnability (SSBD Ch. 2–4).
* `FiniteClass/` — finite classes: uniform convergence, agnostic PAC,
  realizable PAC (SSBD Cor. 2.3, 3.2, 4.6).
* `Rademacher/` — Rademacher complexity: Massart, contraction,
  symmetrization, generalization bounds (SSBD Ch. 26).
* `VC/` — the agnostic upper bound of the Fundamental Theorem via the
  set-class VC machinery of `ConcentrationInequalities/VC/` (SSBD Ch. 6, 28).
* `Stability/` — replace-one stability, stable-rules-do-not-overfit, Tikhonov
  regularization (SSBD Ch. 13).
* `PACBayes/` — change of measure and the PAC-Bayes bound (SSBD Ch. 31).

Concentration machinery is imported from `StatLean.ConcentrationInequalities`
— never re-proven here.
-/
