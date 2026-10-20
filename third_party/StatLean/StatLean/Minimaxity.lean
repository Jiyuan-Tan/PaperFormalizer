module
public import StatLean.Minimaxity.Defs
public import StatLean.Minimaxity.ForMathlib.KLDivergence
public import StatLean.Minimaxity.ForMathlib.KLDataProcessing
public import StatLean.Minimaxity.ForMathlib.TotalVariation
public import StatLean.Minimaxity.ForMathlib.HellingerDivergence
public import StatLean.Minimaxity.ForMathlib.PinskerInequality
public import StatLean.Minimaxity.ForMathlib.LeCamInequality
public import StatLean.Minimaxity.ForMathlib.Entropy
public import StatLean.Minimaxity.ForMathlib.GaussianKL
public import StatLean.Minimaxity.ForMathlib.GaussianKLMulti
public import StatLean.Minimaxity.ForMathlib.GaussianMaxEntropy
public import StatLean.Minimaxity.ForMathlib.Packing.HammingPacking
public import StatLean.Minimaxity.ForMathlib.Packing.SpherePacking
public import StatLean.Minimaxity.ForMathlib.Packing.SparsePacking
public import StatLean.Minimaxity.ForMathlib.Packing.SobolevEntropy
public import StatLean.Minimaxity.EstimationToTesting
public import StatLean.Minimaxity.LeCam.TwoPoint
public import StatLean.Minimaxity.LeCam.Functional
public import StatLean.Minimaxity.LeCam.ConvexHull
public import StatLean.Minimaxity.Fano.MutualInformation
public import StatLean.Minimaxity.Fano.FanoLowerBound
public import StatLean.Minimaxity.Fano.LocalPacking
public import StatLean.Minimaxity.Fano.YangBarron
public import StatLean.Minimaxity.Examples.GaussianLocation
public import StatLean.Minimaxity.Examples.UniformLocation
public import StatLean.Minimaxity.Examples.LinearRegression
public import StatLean.Minimaxity.Examples.SparseLinearRegression
public import StatLean.Minimaxity.Examples.PCA
public import StatLean.Minimaxity.Examples.LipschitzDensity
public import StatLean.Minimaxity.Examples.DensityEstimation
public import StatLean.Minimaxity.Examples.Sobolev

@[expose] public section

/-!
# Minimaxity — area umbrella

Minimax lower bounds, formalized from Wainwright, *High-Dimensional Statistics:
A Non-Asymptotic Viewpoint* (Cambridge University Press, 2019), Chapter 15.

The area develops, on top of Mathlib's decision-theoretic risk framework
(`ProbabilityTheory.minimaxRisk` / `bayesRisk`):

* **Core (`Defs`)**: Wainwright's minimax risk `M(θ(𝒫); Φ∘ρ)`, the M-ary testing
  error, the mixture distribution, and `2δ`-separated families.
* **Divergences (`ForMathlib/`)**: total variation, Kullback–Leibler (bridged to
  Mathlib `klDiv`), squared Hellinger (bridged to the StatLean Hellinger-product
  tensorization), Shannon/conditional entropy, Fano's inequality, with the
  Pinsker (Lemma 15.2) and Le Cam (Lemma 15.3) comparison inequalities; plus the
  Chapter-5 metric-entropy bricks (Hamming / sphere / sparse packing, Sobolev entropy).
* **Estimation → testing (`EstimationToTesting`)**: Proposition 15.1.
* **Le Cam's method (`LeCam/`)**: the two-point bound (Eq. (15.14)), the functional
  modulus form (Corollary 15.6), and the convex-hull bound (Lemma 15.9).
* **Fano's method (`Fano/`)**: mutual information, the Fano lower bound (Prop. 15.12),
  the local-packing proposition (§15.3.3), and the Yang–Barron bound (Lemma 15.21).
* **Examples (`Examples/`)**: the worked minimax-rate calculations of §15.2–15.3.

Modules are imported below as each lands.
-/

