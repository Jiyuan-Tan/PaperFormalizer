module
public import StatLean.AsymptoticStatistics
public import StatLean.ConcentrationInequalities
public import StatLean.HighDimensionalStatistics
public import StatLean.Optimization
public import StatLean.MultipleTesting
public import StatLean.Minimaxity
public import StatLean.Bayesian
public import StatLean.NonparametricStatistics
public import StatLean.PointEstimation
public import StatLean.HypothesisTesting
public import StatLean.StatisticalModels
public import StatLean.TimeSeries
public import StatLean.CausalInference
public import StatLean.ExperimentalDesign
public import StatLean.StatisticalLearning
public import StatLean.ComputationalStatistics
public import StatLean.RobustStatistics

@[expose] public section

/-!
# StatLean

Root module of the StatLean library: a Lean 4 formalization of statistical
theory, organized into per-area sublibraries.

* `StatLean.AsymptoticStatistics` — asymptotic statistics (van der Vaart).
* `StatLean.ConcentrationInequalities` — sub-Gaussian / sub-exponential / Bernstein
  / maximal inequalities (Lu, *Big Data Analysis* ch. 2–4).
* `StatLean.HighDimensionalStatistics` — OLS MSE and Lasso rates (Lu, *Big Data
  Analysis* ch. 5, 8).
* `StatLean.Optimization` — convex optimization: subgradients, gradient descent,
  Frank–Wolfe, proximal / accelerated proximal gradient (Lu, *Big Data Analysis*
  ch. 10–12).
* `StatLean.MultipleTesting` — multiple hypothesis testing: Benjamini–Hochberg
  and knock-off FDR control, Holm–Bonferroni FWER control (Lu, *Big Data
  Analysis* ch. 18–19; Holm 1979).
* `StatLean.Minimaxity` — minimax lower bounds: divergences, Le Cam / Fano /
  local-packing / Yang–Barron methods (Wainwright, *High-Dimensional Statistics*,
  ch. 15).
* `StatLean.Bayesian` — Bayesian statistics: dominated Bayes, sufficiency,
  updating/prediction, conjugacy (incl. Dirichlet–Multinomial), generalized Bayes,
  model choice, MCMC correctness, decision theory / minimax bridge, hierarchical +
  empirical Bayes (Robert, *The Bayesian Choice*; Gelman et al., *Bayesian Data
  Analysis*, 3rd ed.).
* `StatLean.StatisticalModels` — statistical models as compositional structures:
  the model calculus (observation/coarsening, latent marginalization, replication)
  over bare families of laws, identifiability transfer, survival / event-history
  (censoring, crude-vs-net hazards, Kaplan–Meier, Cox), Gaussian substrate
  (covariance calculus, block conditioning), mixed effects, longitudinal / GEE,
  and missing data (MAR, IPW, ignorability) with adapters to the other areas
  (Andersen–Borgan–Gill–Keiding; Liang–Zeger; Rubin; Anderson).
* `StatLean.TimeSeries` — time series: stationarity, autocovariance/autocorrelation,
  the Herglotz theorem and spectral bricks on the circle, Markov-kernel ergodicity,
  linear and nonlinear model classes (ARMA/ARIMA, ARCH/GARCH, TAR, SV), and MA(∞)
  linear processes (Fan & Yao, *Nonlinear Time Series*).
* `StatLean.NonparametricStatistics` — nonparametric estimation: kernel density
  estimation (pointwise and integrated risk, exact asymptotic MISE), local
  polynomial regression (pointwise/L²/sup-norm rates over Hölder classes), and
  projection estimators on the trigonometric basis (exact MISE decomposition and
  Sobolev-ellipsoid rates).
* `StatLean.ExperimentalDesign` — design of experiments and design-based survey
  sampling in the finite randomisation model: finite-population summaries,
  randomization/sampling designs as PMFs, the completely randomised design with
  exact assignment probabilities, arm means as simple random samples, blocked
  randomization, inclusion probabilities and Horvitz–Thompson estimation,
  stratified estimators, contrast algebra, two-level factorial characters, and
  the one-way ANOVA identity (Mead, *The Design of Experiments*; Horvitz–Thompson
  1952; Cochran 1977).
* `StatLean.PointEstimation` — point estimation: exponential families (natural
  parameters, differentiability of the log-partition function), sufficiency,
  minimal sufficiency and completeness, unbiased estimation and UMVU
  (Rao–Blackwell, Lehmann–Scheffé), the information inequality (Fisher
  information, Cramér–Rao), equivariance (location and scale minimum-risk
  equivariant estimators, Pitman's estimator), and normal linear models.

* `StatLean.CausalInference` — causal inference in the potential-outcomes framework:
  the design-based half (science tables, assignment designs, complete randomization,
  Fisher's randomization test, Neyman's unbiasedness/variance, stratified and
  matched-pair experiments, regression adjustment, the superpopulation bridge) and the
  observational half over a discrete covariate (selection bias, unconfoundedness,
  standardization, the propensity score, IPW, the doubly robust AIPW functional, the
  effect on the treated, subclassification/matching/trimming), plus sensitivity analysis
  (Manski bounds, the E-value, Rosenbaum's model) and instrumental variables (compliance
  types, LATE/CACE, the instrumental inequalities, linear IV) — Ding, *A First Course in
  Causal Inference*; Imbens & Rubin, *Causal Inference for Statistics, Social, and
  Biomedical Sciences*.
* `StatLean.StatisticalLearning` — statistical learning theory: risk, empirical
  risk minimization and the PAC / agnostic-PAC / uniform-convergence models,
  finite-class bounds, Rademacher complexity (Massart, contraction,
  symmetrization, generalization bounds), the agnostic upper bound of the
  fundamental theorem for finite VC dimension, algorithmic stability with
  Tikhonov regularization, and PAC-Bayes (Shalev-Shwartz & Ben-David,
  *Understanding Machine Learning*).
* `StatLean.ComputationalStatistics` — correctness of sampling and resampling
  algorithms: empirical/weighted/categorical measures, Monte Carlo estimation,
  importance sampling (with the optimal importance function), rejection
  sampling, multinomial particle resampling and the multinomial-counts bridge,
  finite-sample bootstrap identities, the jackknife with exact first-order
  bias annihilation, and holdout / K-fold / leave-one-out cross validation
  (Gentle, *Elements of Computational Statistics*).
* `StatLean.RobustStatistics` — robust statistics: how estimators respond to
  contamination, and the estimators built to withstand it. Gross-error
  contamination and its neighbourhoods, equivariance of functionals, the
  finite-sample replacement breakdown point (exact values for the mean, the
  median — attaining the maximum for location-equivariant estimators — and the
  trimmed mean), the one-sided influence function with the general M-functional
  formula and its bounded-score corollary, maximum contamination bias, Huber's
  loss and score, location M-estimators and M-functionals (existence,
  uniqueness, consistency, asymptotic normality), the MAD, M-regression with the
  leverage counterexample, and affine equivariance of multivariate location and
  scatter (Maronna, Martin, Yohai & Salibián-Barrera, *Robust Statistics: Theory
  and Methods*, 2nd ed.).

Per-area umbrellas are imported above as each area lands.
-/
