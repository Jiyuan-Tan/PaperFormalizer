module
public import StatLean.RobustStatistics.ForMathlib.OrderStatPerturb
public import StatLean.RobustStatistics.Core.Contamination
public import StatLean.RobustStatistics.Core.Equivariance
public import StatLean.RobustStatistics.Core.InfluenceFunction
public import StatLean.RobustStatistics.Core.Bias
public import StatLean.RobustStatistics.Core.BreakdownPoint
public import StatLean.RobustStatistics.LocationScale.Huber
public import StatLean.RobustStatistics.LocationScale.Mean
public import StatLean.RobustStatistics.LocationScale.Median
public import StatLean.RobustStatistics.LocationScale.MedianBreakdown
public import StatLean.RobustStatistics.LocationScale.MLocation
public import StatLean.RobustStatistics.LocationScale.MAD
public import StatLean.RobustStatistics.LocationScale.TrimmedMean
public import StatLean.RobustStatistics.MEstimation.MLocationFunctional
public import StatLean.RobustStatistics.MEstimation.Influence
public import StatLean.RobustStatistics.MEstimation.AsymptoticBreakdown
public import StatLean.RobustStatistics.MEstimation.Asymptotics
public import StatLean.RobustStatistics.Regression.MRegression
public import StatLean.RobustStatistics.Multivariate.AffineEquivariance
public import StatLean.RobustStatistics.Multivariate.BallMoM
public import StatLean.RobustStatistics.HeavyTails.EmpiricalMeanBaseline
public import StatLean.RobustStatistics.HeavyTails.MedianOfMeans
public import StatLean.RobustStatistics.HeavyTails.Catoni
public import StatLean.RobustStatistics.HeavyTails.TrimmedMean
public import StatLean.RobustStatistics.HeavyTails.DeviationLowerBound
public import StatLean.RobustStatistics.Scale.MScale
public import StatLean.RobustStatistics.Scale.DispersionBreakdown
public import StatLean.RobustStatistics.MaxBias.MaxBiasLocation
public import StatLean.RobustStatistics.MaxBias.MedianMinimaxBias

@[expose] public section

/-!
# StatLean.RobustStatistics — area umbrella

Robust statistics: measuring the sensitivity of estimators to contamination, and the
estimators built to withstand it. The organizing spine is

contamination → equivariance → statistical functionals →
{influence function, breakdown point, maximum bias} → robust estimators.

* `ForMathlib/` — `OrderStatPerturb` (order statistics under affine maps and coordinate
  replacement; the combinatorial engine of finite-sample breakdown).
* `Core/` — the robustness diagnostics: `Contamination` (the ε-mixture `(1-ε)P + εQ` and
  gross-error neighbourhoods), `Equivariance` (location/scale/dispersion predicates),
  `InfluenceFunction` (one-sided contamination derivative), `Bias` (bounded contamination
  bias), `BreakdownPoint` (finite-sample replacement breakdown, maximal-breakdown bound
  for location-equivariant estimators).
* `LocationScale/` — the concrete estimators: `Huber` (loss and clipped score), `Mean`
  (the fragile pole: unbounded IF, breakdown count 0, infinite maximum bias), `Median` and
  `MedianBreakdown` (the robust pole: breakdown count `⌊(n-1)/2⌋`, the equivariant
  maximum), `MLocation` (M-estimates: objective ↔ estimating equation), `MAD`,
  `TrimmedMean`.
* `MEstimation/` — the population theory: `MLocationFunctional` (roots of
  `E_P ψ(x-θ) = 0`), `Influence` (the flagship IF formula `ψ(x₀-θ₀)/A`; bounded score ⟹
  bounded influence), `AsymptoticBreakdown` (`ε* = min(k₁,k₂)/(k₁+k₂)`, `1/2` for Huber),
  `Asymptotics` (consistency and √n-normality by reuse of
  `StatLean/AsymptoticStatistics` Z-estimation theory).
* `Regression/` — `MRegression` (objective, M-normal equations, Huber convexity,
  regression equivariance, the leverage counterexample, and regression quantiles —
  the check loss and the Koenker–Bassett regression α-quantile).
* `Multivariate/` — `AffineEquivariance` (location/scatter equivariance interface; mean
  and covariance sanity checks); `BallMoM` (the dimension-free minimal-radius-ball
  median-of-means, LM Proposition 1).
* `HeavyTails/` — modern sub-Gaussian mean estimation under two moments (LM 2019):
  `EmpiricalMeanBaseline` (the Chebyshev baseline), `MedianOfMeans` (LM Thm 2),
  `Catoni` (LM Thm 5), `TrimmedMean` (LM Thm 6, two-sample quantile trimming),
  `DeviationLowerBound` (LM Thm 1 — no estimator beats σ√(log(1/δ)/n)).
* `Scale/` — `MScale` (scale M-functionals, the log-scale reduction, breakdown point
  min(δ, 1−δ)); `DispersionBreakdown` (implosion-aware finite-sample breakdown: SD = 0,
  MAD → 1/2).
* `MaxBias/` — `MaxBiasLocation` (the sharp maximum-bias bound b_ε and the median's
  quantile formula, MMY (3.66)–(3.68)); `MedianMinimaxBias` (Huber's minimax-bias
  property of the median, MMY §3.8.5).

**Scope.** Round 1: measuring robustness (MMY ch. 2–3) plus the reuse-driven asymptotics
(MMY ch. 10) and the foundational regression/multivariate layer (MMY §4.4, §6.17.1).
Round 2 (breadth + modern): sub-Gaussian mean estimation under heavy tails (LM 2019 —
median-of-means, Catoni, trimmed mean, the deviation lower bound, the dimension-free
multivariate ball-MoM), scale M-functionals and dispersion breakdown, maximum-bias
theory with the median's minimax-bias property, and regression quantiles.
Deferred: LM Thm 3 (1+α moments) and Thm 7 (multiple-δ impossibility, after
Devroye–Lerasle–Lugosi–Oliveira 2016), the Catoni–Giulini thresholding estimator and
median-of-means tournaments (LM §3.3–3.4), the geometric median-of-means (Minsker
2015), contamination-robust trimmed means (Lugosi–Mendelson 2021), the median influence
function, Hampel optimality (MMY §3.8.6–3.8.7), S/MM/LTS regression, high-breakdown
multivariate estimators.

**Relation to other areas.** Imports `StatLean.MultipleTesting.ForMathlib.OrderStatistics`
(order statistics), `StatLean.PointEstimation.Equivariance.Defs` (finite-sample
equivariance), and the `StatLean.AsymptoticStatistics` consistency/empirical-process
layers (Z-estimator asymptotics); the DAG direction is strictly downward into
RobustStatistics.

**References.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera,
*Robust Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019 (`MMY §X.Y` in
tags) — the classical spine; G. Lugosi and S. Mendelson, *Mean estimation and
regression under heavy-tailed distributions — a survey*, Found. Comput. Math. (2019),
arXiv:1906.04280v1 (`LM Thm N` / `LM (x.y)` in tags) — the modern spine.

Laptop-only file: edited by the laptop session at wave merges.

**Bibliographic comments.** The subject begins with Tukey's contaminated-normal alarm ("A
survey of sampling from contaminated distributions," in *Contributions to Probability and
Statistics: Essays in Honor of Harold Hotelling*, Stanford Univ. Press, 1960, pp. 448–485),
becomes a theory in Huber's minimax paper ("Robust estimation of a location parameter," *Ann.
Math. Statist.* **35** (1964), 73–101), and acquires its diagnostic vocabulary in Hampel's
thesis and papers — qualitative robustness and the breakdown point ("A general qualitative
definition of robustness," *Ann. Math. Statist.* **42** (1971), 1887–1896) and the influence
curve ("The influence curve and its role in robust estimation," *J. Amer. Statist. Assoc.*
**69** (1974), 383–393); the finite-sample replacement breakdown point is Donoho and Huber
("The notion of breakdown point," in *A Festschrift for Erich L. Lehmann*, Wadsworth, 1983,
pp. 157–184). The monographs are Huber (*Robust Statistics*, Wiley, 1981; 2nd ed. with
Ronchetti, 2009), Hampel, Ronchetti, Rousseeuw and Stahel (*Robust Statistics: The Approach
Based on Influence Functions*, Wiley, 1986), and MMY 2019 (the area's spine). The modern
heavy-tails program formalized in `HeavyTails/` runs from the median-of-means of
Nemirovsky–Yudin (*Problem Complexity and Method Efficiency in Optimization*, Wiley, 1983),
Jerrum–Valiant–Vazirani (*Theoret. Comput. Sci.* **43** (1986), 169–188) and
Alon–Matias–Szegedy (*J. Comput. System Sci.* **58** (1999), 137–147) through Catoni (*Ann.
Inst. Henri Poincaré Probab. Stat.* **48** (2012), 1148–1185) to the sub-Gaussian-estimator
framework of Devroye, Lerasle, Lugosi and Oliveira (*Ann. Statist.* **44** (2016),
2695–2725) and the LM survey; the multivariate story continues with Minsker (*Bernoulli*
**21** (2015), 2308–2335) and Lugosi–Mendelson (*Ann. Statist.* **47** (2019), 783–794).
-/
