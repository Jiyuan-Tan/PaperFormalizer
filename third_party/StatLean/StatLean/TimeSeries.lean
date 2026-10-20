module
public import StatLean.TimeSeries.ForMathlib.PosSemidefSequence
public import StatLean.TimeSeries.ForMathlib.Fourier.FejerKernel
public import StatLean.TimeSeries.ForMathlib.Fourier.MeasureFourierCoeff
public import StatLean.TimeSeries.ForMathlib.Fourier.HerglotzBochner
public import StatLean.TimeSeries.ForMathlib.Markov.Chain
public import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity
public import StatLean.TimeSeries.ForMathlib.Markov.HarrisTheorem
public import StatLean.TimeSeries.ForMathlib.Ergodic.Birkhoff
public import StatLean.TimeSeries.ForMathlib.Markov.IFSMinorization
public import StatLean.TimeSeries.ForMathlib.Markov.TwoSidedChain
public import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
public import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.Defs
public import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.CondCharFun
public import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.BrownCLT
public import StatLean.TimeSeries.Process.Defs
public import StatLean.TimeSeries.Process.Stationary
public import StatLean.TimeSeries.Process.SecondOrder
public import StatLean.TimeSeries.Process.Autocovariance
public import StatLean.TimeSeries.Process.LinearProcess
public import StatLean.TimeSeries.Models.Defs
public import StatLean.TimeSeries.Models.WhiteNoise
public import StatLean.TimeSeries.Models.Linear
public import StatLean.TimeSeries.Process.PartialAutocorrelation
public import StatLean.TimeSeries.Process.SampleACF
public import StatLean.TimeSeries.Stationarity.ARMAExistence
public import StatLean.TimeSeries.Stationarity.Gaussian
public import StatLean.TimeSeries.Stationarity.ARCH
public import StatLean.TimeSeries.Spectral.SpectralMeasure
public import StatLean.TimeSeries.Spectral.SpectralDensity
public import StatLean.TimeSeries.Spectral.LinearFilter
public import StatLean.TimeSeries.Spectral.ARMASpectral
public import StatLean.TimeSeries.Spectral.DFT
public import StatLean.TimeSeries.Spectral.Periodogram
public import StatLean.TimeSeries.Spectral.PeriodogramAsymptotics
public import StatLean.TimeSeries.Mixing.Defs
public import StatLean.TimeSeries.Mixing.Relations
public import StatLean.TimeSeries.Mixing.Inequalities
public import StatLean.TimeSeries.Mixing.MarkovBridge
public import StatLean.TimeSeries.Mixing.LimitTheorems
public import StatLean.TimeSeries.Mixing.KernelRegressionCLT
public import StatLean.TimeSeries.ARMA.Prediction
public import StatLean.TimeSeries.ARMA.Likelihood
public import StatLean.TimeSeries.ARMA.OrderSelection
public import StatLean.TimeSeries.ARMA.ScoreAnalysis
public import StatLean.TimeSeries.ARMA.Consistency
public import StatLean.TimeSeries.ARMA.MLEAsymptotics
public import StatLean.TimeSeries.ARMA.Diagnostics
public import StatLean.TimeSeries.Threshold.TAR
public import StatLean.TimeSeries.Threshold.Estimation
public import StatLean.TimeSeries.Threshold.LinearityTest
public import StatLean.TimeSeries.GARCH.ARCHBasic
public import StatLean.TimeSeries.GARCH.GARCHBasic
public import StatLean.TimeSeries.GARCH.Estimation
public import StatLean.TimeSeries.GARCH.ARCHTest
public import StatLean.TimeSeries.GARCH.StochasticVolatility

@[expose] public section

/-!
# StatLean.TimeSeries — area umbrella

Time series analysis after J. Fan and Q. Yao, *Nonlinear Time Series: Nonparametric and
Parametric Methods*, Springer, 2003 (`FY` in tags). Scope: FY ch. 1 model definitions;
§2.1–§2.4 and §2.6 (skipping §2.1.4, with §2.7 proofs); §3.1–§3.5; §4.1–§4.2.
Roadmap and status: `notes/time_series/` (laptop-local).

Laptop-only file: edited by the laptop session at wave merges.
-/
