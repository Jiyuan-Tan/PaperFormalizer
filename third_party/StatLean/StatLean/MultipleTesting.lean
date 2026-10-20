module
public import StatLean.MultipleTesting.FDP.Defs
public import StatLean.MultipleTesting.PValues.Defs
public import StatLean.MultipleTesting.EValues.Defs
public import StatLean.MultipleTesting.Knockoff.Defs
public import StatLean.MultipleTesting.ForMathlib.OrderStatistics
public import StatLean.MultipleTesting.ForMathlib.OptionalStopping
public import StatLean.MultipleTesting.ForMathlib.BinomialRatio
public import StatLean.MultipleTesting.ForMathlib.SymmetricCondExp
public import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
public import StatLean.MultipleTesting.ForMathlib.GaussianMoments
public import StatLean.MultipleTesting.ForMathlib.GammaMoments
public import StatLean.MultipleTesting.ForMathlib.GaussianSquareMGF
public import StatLean.MultipleTesting.ForMathlib.ChiSquared
public import StatLean.MultipleTesting.ForMathlib.RankUniform
public import StatLean.MultipleTesting.ForMathlib.EmpiricalProcessSup
public import StatLean.MultipleTesting.BenjaminiHochberg
public import StatLean.MultipleTesting.BHDependence
public import StatLean.MultipleTesting.BHMartingale
public import StatLean.MultipleTesting.HolmBonferroni
public import StatLean.MultipleTesting.Knockoff.Procedure
public import StatLean.MultipleTesting.Knockoff.FdpBound
public import StatLean.MultipleTesting.Knockoff.Initial
public import StatLean.MultipleTesting.Knockoff.Supermartingale
public import StatLean.MultipleTesting.Knockoff
public import StatLean.MultipleTesting.EValues.Conversion
public import StatLean.MultipleTesting.EmpiricalBayes.BayesRisk
public import StatLean.MultipleTesting.ChiSquaredTest.Distribution
public import StatLean.MultipleTesting.Conformal.Coverage
public import StatLean.MultipleTesting.GoodnessOfFit.KolmogorovSmirnov

@[expose] public section

/-!
# MultipleTesting — area umbrella

Multiple hypothesis testing: false discovery rate and family-wise error rate control, formalized
from Lu, *Big Data Analysis* ch. 18–19 (Holm–Bonferroni from Holm 1979):

* **Concepts**: `FDP` / `FDR` / `FWER` (`FDP/Defs.lean`); `SuperUniform` null p-values
  (`PValues/Defs.lean`); `KnockoffScore` (`Knockoff/Defs.lean`).
* **ForMathlib**: order statistics of a real tuple (`OrderStatistics.lean`); the optional
  stopping theorem `thm:optstop` as a supermartingale bridge to Mathlib (`OptionalStopping.lean`);
  the binomial-ratio inequalities (`BinomialRatio.lean`); the exchangeable conditional expectation
  `E[𝟙(σᵢ)|count] = count/k` for i.i.d. fair Bool variables (`SymmetricCondExp.lean`).
* **Benjamini–Hochberg** (§18): `benjamini_hochberg_fdr_le` — `FDR ≤ (N₀/N)·α`.
* **Holm–Bonferroni** (Holm 1979; §17 Bonferroni): `holm_fwer_le`, `bonferroni_fwer_le` —
  `FWER ≤ α`.
* **Knock-off** (§19): `knockoff_fdr_le` — `FDR ≤ α`.

**Batch 8 — Candès STAT 300C** (large-scale inference; this area is the library's catch-all
testing area). Landing incrementally:

* **E-values** (Candès L15, Defs. 3–4, Prop. 3): `IsEVariable` / `IsPVariable`
  (`EValues/Defs.lean`); `isPVariable_inv_of_isEVariable`, `superUniform_inv_of_isEVariable`
  (`EValues/Conversion.lean`) — `1/E` is a (super-uniform) p-value.

Modules are imported above as each lands.
-/
