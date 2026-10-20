module
public import StatLean.NonparametricStatistics.SmoothnessClasses.Defs

@[expose] public section

/-!
# Nonparametric regression — model and linear estimators

The nonparametric regression model `Y i = f (x i) + ξ i` (deterministic design `x`, centered
noise `ξ`) and the two basic estimator notions:

* `IsLinearEstimator fhat` — `fhat` is a *linear* nonparametric regression estimator: there are
  weights `W x i` (depending on the design but not on the responses) with
  `fhat Y x = ∑ i, Y i · W x i`.
* `nadarayaWatson xdat Y K h x` — the locally-weighted-average kernel regression estimator
  $f_n(x) = \dfrac{\sum_i Y_i K((X_i - x)/h)}{\sum_j K((X_j - x)/h)}$, set to `0` when the
  denominator vanishes.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.5: nonparametric regression, the
Nadaraya–Watson estimator, Eqs. (1.62)–(1.63), and Definition 1.7 (linear estimators).

**Proof formalization notes.**

* `IsLinearEstimator` fixes the design implicitly: `fhat` maps a response vector and an
  evaluation point to a value, and linearity is the existence of response-free weights. The
  classical side remark that the weights "typically sum to one" is *not* part of the
  definition; it is a property proved where true.
* The `0`-on-vanishing-denominator convention in `nadarayaWatson` follows the classical
  definition verbatim (and makes the estimator total). `Classical` choice is used only for the
  denominator case split; the definition is `noncomputable` anyway.

**Bibliographic comments.** The kernel regression estimator was proposed independently by
E. A. Nadaraya, "On estimating regression," *Theory Probab. Appl.* **9** (1964), 141–142, and
G. S. Watson, "Smooth regression analysis," *Sankhyā Ser. A* **26** (1964), 359–372. The
weight-function (linear estimator) viewpoint is standard; see C. J. Stone, "Consistent
nonparametric regression," *Ann. Statist.* **5** (1977), 595–620.
-/

namespace StatLean.NonparametricStatistics

/-- **Linear nonparametric regression estimator**: `fhat` (response vector ↦ evaluation point ↦
value) is linear iff it is given by response-free weights: `fhat Y x = ∑ i, Y i · W x i`.
The weights may depend arbitrarily on the (fixed) design, the bandwidth, `n`, and `x`. -/
def IsLinearEstimator {n : ℕ} (fhat : (Fin n → ℝ) → ℝ → ℝ) : Prop :=
  ∃ W : ℝ → Fin n → ℝ, ∀ (Y : Fin n → ℝ) (x : ℝ), fhat Y x = ∑ i, Y i * W x i

open Classical in
/-- **Kernel regression (locally weighted average) estimator**:
`∑ i, Y i · K((xdat i − x)/h) / ∑ j, K((xdat j − x)/h)`, and `0` when the denominator is `0`
(including the degenerate `n = 0` and `h = 0` cases). -/
noncomputable def nadarayaWatson {n : ℕ} (xdat Y : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ)
    (x : ℝ) : ℝ :=
  if (∑ i, K ((xdat i - x) / h)) = 0 then 0
  else (∑ i, Y i * K ((xdat i - x) / h)) / ∑ i, K ((xdat i - x) / h)

end StatLean.NonparametricStatistics
