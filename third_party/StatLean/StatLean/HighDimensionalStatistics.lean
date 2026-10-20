module
public import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
public import StatLean.HighDimensionalStatistics.ForMathlib.TopK
public import StatLean.HighDimensionalStatistics.ForMathlib.PsiTaylor
public import StatLean.HighDimensionalStatistics.LinearModel.Defs
public import StatLean.HighDimensionalStatistics.Lasso.Defs
public import StatLean.HighDimensionalStatistics.Lasso.DeterministicRate
public import StatLean.HighDimensionalStatistics.Lasso.RandomNoise
public import StatLean.HighDimensionalStatistics.OLS.MSEExpectation
public import StatLean.HighDimensionalStatistics.OLS.MSEHighProb
public import StatLean.HighDimensionalStatistics.CompressedSensing.Defs
public import StatLean.HighDimensionalStatistics.CompressedSensing.BasisPursuit
public import StatLean.HighDimensionalStatistics.CompressedSensing.ConeTheorem
public import StatLean.HighDimensionalStatistics.CompressedSensing.RIPRecovery
public import StatLean.HighDimensionalStatistics.CompressedSensing.GaussianChiSquared
public import StatLean.HighDimensionalStatistics.CompressedSensing.RandomRIP
public import StatLean.HighDimensionalStatistics.ForMathlib.SupportSubmatrix
public import StatLean.HighDimensionalStatistics.ForMathlib.GramMatrix
public import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Defs
public import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Subgradient
public import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.DualCertificate
public import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.DeterministicGuarantee
public import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.SubGaussianNoise
public import StatLean.HighDimensionalStatistics.MEstimator.Defs
public import StatLean.HighDimensionalStatistics.MEstimator.Deviation
public import StatLean.HighDimensionalStatistics.MEstimator.SubspaceLip
public import StatLean.HighDimensionalStatistics.MEstimator.Bound
public import StatLean.HighDimensionalStatistics.MEstimator.DualBound
public import StatLean.HighDimensionalStatistics.MEstimator.GLMDefs
public import StatLean.HighDimensionalStatistics.MEstimator.L1Decomposable
public import StatLean.HighDimensionalStatistics.MEstimator.ScoreSubGaussian
public import StatLean.HighDimensionalStatistics.MEstimator.GoodEvent
public import StatLean.HighDimensionalStatistics.MEstimator.GLMCorollaries

@[expose] public section

/-!
# HighDimensionalStatistics — area umbrella

OLS mean-squared-error, Lasso statistical rates, and compressed sensing,
formalized from Lu, *Big Data Analysis*, ch. 5, 6, 7 and 8. Consumes the
`ConcentrationInequalities` sub-Gaussian / sub-exponential / covering bricks and
the `AsymptoticStatistics` Gaussian-MGF bricks for the noise and random-matrix
bounds. Compressed sensing (ch. 6–7): the cone theorem (`thm:cone`), perfect
recovery under RIP (`thm:rip`), and the random-Gaussian RIP guarantee
(`thm:3s-rip`). Modules are imported above as each lands.
-/
