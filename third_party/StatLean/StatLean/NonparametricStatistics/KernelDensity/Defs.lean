module
public import StatLean.NonparametricStatistics.SmoothnessClasses.Defs
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Kernel density estimation — definitions

The kernel density estimator and its risk functionals:

* `IsKernelOfOrder K ℓ` — `K` integrates to one and its moments of orders `1, …, ℓ` vanish.
* `kdeData xdat K h x` — the kernel density estimate at `x` built from the data vector `xdat`:
  $\hat p_n(x) = \frac{1}{nh}\sum_{i=1}^n K\bigl(\frac{X_i - x}{h}\bigr)$.
* `kde2Data xdat ydat K h x y` — the bivariate product-kernel estimate
  $\frac{1}{nh^2}\sum_i K(\frac{X_i-x}{h})\,K(\frac{Y_i-y}{h})$.
* `kde X K h ω x` — the estimator as a random function on a sample space.
* `kdeMeanAt`, `kdeBiasAt`, `kdeVarianceAt`, `kdeMseAt`, `kdeMise` — mean, bias, variance,
  pointwise mean squared error, and mean integrated squared error.
* `IsIIDSample P X μ` — the sampling model: `X 0, …, X (n-1)` mutually independent, each with
  law `μ`, under `P`.
* `kdeVarianceConst K pmax = pmax·∫K²` and
  `kdeBiasConst β L K = (L/ℓ!)·∫|u|^β|K(u)|du` — the explicit constants of the pointwise
  variance and bias bounds.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2: the kernel density estimator, Eqs.
(1.2)–(1.3); Definition 1.1 (bias and variance) and the MSE (1.4); Definition 1.3 (kernel of order
$\ell$); the MISE (1.13).

**Proof formalization notes.**

* *Sign convention.* The kernel argument is `(X i − x)/h`, matching the classical display; for
  symmetric kernels this agrees with the `(x − X i)/h` convention.
* *Risk functionals in `ℝ≥0∞`.* Variance, MSE and MISE are defined via the lower Lebesgue
  integral of the (nonnegative) squared deviation. With Bochner integrals a non-integrable
  square would return the junk value `0` and make every upper bound vacuous; `∫⁻` records the
  genuine (possibly infinite) risk, so the stated bounds carry real content. The bias, a signed
  quantity, uses the Bochner integral; its integrability is *derived* in the bias lemmas, never
  assumed.
* *Degenerate inputs.* `n = 0` gives `kdeData = 0` (the factor `(n·h)⁻¹` multiplies an empty
  sum; `(0)⁻¹ = 0` in `ℝ`); `h = 0` similarly gives `0`. Bias statements therefore carry
  `0 < n`, `0 < h` side conditions.

**Bibliographic comments.** The estimator goes back to ideas of E. Fix and J. L. Hodges
(*Discriminatory analysis — nonparametric discrimination*, USAF School of Aviation Medicine,
Report 4, 1951) and H. Akaike ("An approximation to the density function," *Ann. Inst. Statist.
Math.* **6** (1954), 127–132); its mathematical theory was initiated by M. Rosenblatt, "Remarks
on some nonparametric estimates of a density function," *Ann. Math. Statist.* **27** (1956),
832–837, and E. Parzen, "On estimation of a probability density function and mode," *Ann. Math.
Statist.* **33** (1962), 1065–1076 — whence *Parzen–Rosenblatt estimator*. Higher-order kernels
(vanishing moments) are classical bias-reduction devices, systematically constructible from
orthogonal polynomial systems (cf. G. Szegő, *Orthogonal Polynomials*, 4th ed., AMS, 1975);
the parabolic kernel optimal for asymptotic integrated risk is due to M. S. Bartlett
("Statistical estimation of density functions," *Sankhyā Ser. A* **25** (1963), 245–254) and
V. A. Epanechnikov ("Non-parametric estimation of a multivariate probability density," *Theory
Probab. Appl.* **14** (1969), 153–158).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Kernel of order `ℓ`**: the functions `u ↦ uʲ·K(u)` are integrable for `j ≤ ℓ`, `K`
integrates to one, and the moments of orders `1, …, ℓ` vanish. (Order `0` just says `K` is an
integrable function with `∫K = 1`.) Following the classical convention, nothing is assumed
about the `(ℓ+1)`-st moment. -/
structure IsKernelOfOrder (K : ℝ → ℝ) (ℓ : ℕ) : Prop where
  /-- Constitutive: integrability of `u ↦ uʲ·K(u)` for `0 ≤ j ≤ ℓ`. -/
  integrable_pow : ∀ j : ℕ, j ≤ ℓ → Integrable fun u => u ^ j * K u
  /-- Constitutive: `∫ K = 1`. -/
  integral_eq_one : ∫ u, K u = 1
  /-- Constitutive: vanishing moments `∫ uʲ K(u) du = 0` for `1 ≤ j ≤ ℓ`. -/
  moment_eq_zero : ∀ j : ℕ, 1 ≤ j → j ≤ ℓ → ∫ u, u ^ j * K u = 0

/-- Kernel density estimate at `x` from the data vector `xdat` with kernel `K`, bandwidth `h`:
`(n·h)⁻¹ · ∑ i, K ((xdat i − x)/h)`. Degenerate `n = 0` or `h = 0` yields `0`. -/
noncomputable def kdeData {n : ℕ} (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (x : ℝ) : ℝ :=
  ((n : ℝ) * h)⁻¹ * ∑ i, K ((xdat i - x) / h)

/-- Bivariate product-kernel density estimate at `(x, y)` from paired data `(xdat, ydat)`:
`(n·h²)⁻¹ · ∑ i, K((xdat i − x)/h) · K((ydat i − y)/h)`. -/
noncomputable def kde2Data {n : ℕ} (xdat ydat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ)
    (x y : ℝ) : ℝ :=
  ((n : ℝ) * h ^ 2)⁻¹ * ∑ i, K ((xdat i - x) / h) * K ((ydat i - y) / h)

/-- The kernel density estimator as a random function: `kde X K h ω = kdeData (X · ω) K h`. -/
noncomputable def kde {n : ℕ} (X : Fin n → Ω → ℝ) (K : ℝ → ℝ) (h : ℝ) (ω : Ω) (x : ℝ) : ℝ :=
  kdeData (fun i => X i ω) K h x

/-- Mean of the estimator at `x`: `E_P[p̂ₙ(x)]`. -/
noncomputable def kdeMeanAt {n : ℕ} (P : Measure Ω) (X : Fin n → Ω → ℝ) (K : ℝ → ℝ)
    (h : ℝ) (x : ℝ) : ℝ :=
  ∫ ω, kde X K h ω x ∂P

/-- Bias of the estimator at `x`: `b(x) = E_P[p̂ₙ(x)] − p(x)`. -/
noncomputable def kdeBiasAt {n : ℕ} (P : Measure Ω) (X : Fin n → Ω → ℝ) (K : ℝ → ℝ)
    (h : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  kdeMeanAt P X K h x - p x

/-- Variance of the estimator at `x`, as a lower Lebesgue integral (`∞` when the estimator is
not square-integrable, rather than a Bochner junk `0`). -/
noncomputable def kdeVarianceAt {n : ℕ} (P : Measure Ω) (X : Fin n → Ω → ℝ) (K : ℝ → ℝ)
    (h : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((kde X K h ω x - kdeMeanAt P X K h x) ^ 2) ∂P

/-- Pointwise mean squared error at `x`: `E_P[(p̂ₙ(x) − p(x))²]`, as a lower Lebesgue
integral. -/
noncomputable def kdeMseAt {n : ℕ} (P : Measure Ω) (X : Fin n → Ω → ℝ) (K : ℝ → ℝ)
    (h : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((kde X K h ω x - p x) ^ 2) ∂P

/-- Mean integrated squared error: `E_P ∫ (p̂ₙ(x) − p(x))² dx`, as an iterated lower Lebesgue
integral (sample-space integral outermost, matching the classical display). -/
noncomputable def kdeMise {n : ℕ} (P : Measure Ω) (X : Fin n → Ω → ℝ) (K : ℝ → ℝ)
    (h : ℝ) (p : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ x, ENNReal.ofReal ((kde X K h ω x - p x) ^ 2)) ∂P

/-- **The i.i.d. sampling model**: the coordinates `X 0, …, X (n−1)` are mutually independent
under `P` and each has law `μ`. This is the standard formalization of "an i.i.d. sample of size
`n` from `μ`". -/
structure IsIIDSample {n : ℕ} (P : Measure Ω) (X : Fin n → Ω → ℝ)
    (μ : Measure ℝ) : Prop where
  /-- Constitutive: mutual independence of the observations. -/
  indep : iIndepFun X P
  /-- Constitutive: each observation has law `μ`. -/
  law : ∀ i, HasLaw (X i) μ P

/-- The explicit constant of the pointwise variance bound: `C₁ = pmax · ∫ K²`. -/
noncomputable def kdeVarianceConst (K : ℝ → ℝ) (pmax : ℝ) : ℝ :=
  pmax * ∫ u, (K u) ^ 2

/-- The explicit constant of the pointwise bias bound:
`C₂ = (L / ℓ!) · ∫ |u|^β · |K u| du` with `ℓ = holderIndex β`. -/
noncomputable def kdeBiasConst (β L : ℝ) (K : ℝ → ℝ) : ℝ :=
  L / (Nat.factorial (holderIndex β) : ℝ) * ∫ u, |u| ^ β * |K u|

end StatLean.NonparametricStatistics
