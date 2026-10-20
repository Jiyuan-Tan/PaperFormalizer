module
public import StatLean.NonparametricStatistics.SmoothnessClasses.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

/-!
# Projection (orthogonal series) estimators — definitions

The projection estimator of a regression function on `[0, 1]` in the trigonometric basis, the
regular design, and the Sobolev-type classes of its risk analysis:

* `trigBasis j` — the trigonometric orthonormal basis of `L²[0,1]`, indexed from `1`:
  `φ₁ ≡ 1`, `φ_{2k}(x) = √2·cos(2πkx)`, `φ_{2k+1}(x) = √2·sin(2πkx)` (`j = 0` is unused, set
  to `0`).
* `regularDesign n i = (i+1)/n` — the regular design `1/n, 2/n, …, 1`.
* `coeffEstimator Y j = n⁻¹ ∑ i, Y i · φⱼ(i/n)` and
  `projEstimator Y N = ∑_{j=1}^N coeffEstimator Y j · φⱼ` — coefficient estimates and the
  projection estimator of order `N`.
* `seriesFun θ = ∑' j, θ j · φⱼ` — the function with prescribed coefficient sequence `θ`
  (the primitive object of the analysis).
* `sobolevWeight β` — the weight sequence `a_j = j^β` (`j` even), `(j−1)^β` (`j` odd);
  `MemEllipsoid β Q θ` — the **Sobolev ellipsoid** `Θ(β, Q) = {θ : ∑ a_j²θ_j² ≤ Q}`;
  `ellipsoidRadius β L = L²/π^{2β}` — the radius matching the Sobolev ball of radius `L`.
* `MemSobolevW β L f` / `MemSobolevWper β L f` — the (periodic) Sobolev class `W(β, L)` on
  `[0,1]`: `f^{(β−1)}` absolutely continuous with `∫₀¹ (f^{(β)})² ≤ L²` (plus matching boundary
  derivatives in the periodic case).
* `riemannResidual θ n j` — the Riemann-sum residual `αⱼ = n⁻¹∑ᵢ f(i/n)φⱼ(i/n) − θⱼ` for
  `f = seriesFun θ`; `tailEnergy θ N = ∑_{j>N} θⱼ²` — the squared-bias tail.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.7: Definition 1.9 (projection estimator);
§1.7.1: Definitions 1.11–1.12 (Sobolev classes $W(\beta, L)$, $W^{\mathrm{per}}$) and the
ellipsoid $\Theta(\beta, Q)$, Eqs. (1.90)–(1.91).

**Proof formalization notes.**

* *Coefficients as the primitive object.* The target class is parametrized by the coefficient
  sequence `θ` and the function is *defined* as `seriesFun θ`; membership of a given `f` in the
  class is then a statement about its coefficient sequence. This makes the risk theorems
  self-contained without invoking completeness of the trigonometric system.
* *Indexing.* The basis is `1`-indexed as in the classical display; sums run over
  `Finset.Icc 1 N`. Index `0` is inert: `trigBasis 0 = 0`, `sobolevWeight β 0 = 0` (as
  `0^β = 0` for `β > 0`), so `θ 0` never contributes and is unconstrained. Note
  `sobolevWeight β 1 = 0` — the first weight vanishes, as in the classical weight sequence.
* *Junk-value discipline.* `MemEllipsoid` carries a `Summable` field: without it, a
  non-summable weighted series would have `tsum = 0` and satisfy the radius bound vacuously.
* *Absolute continuity in `W(β, L)`.* Encoded by an explicit a.e.-derivative witness `g` with
  `f^{(β−1)}(x) = f^{(β−1)}(0) + ∫₀ˣ g` and lower-Lebesgue bound `∫₀¹ g² ≤ L²` — the honest
  rendering of "absolutely continuous derivative with `L²`-bounded density".

**Bibliographic comments.** Orthogonal series estimation is due to N. N. Čencov, "Evaluation of
an unknown distribution density from observations," *Soviet Math. Dokl.* **3** (1962),
1559–1562 (density case; detailed treatment in his *Statistical Decision Rules and Optimal
Inference*, Nauka, 1972). For regression on a regular design in the trigonometric system, the
setup here follows early analyses of R. Shibata ("An optimal selection of regression
variables," *Biometrika* **68** (1981), 45–54) and J. Rice ("Bandwidth choice for
nonparametric regression," *Ann. Statist.* **12** (1984), 1215–1230). Sobolev ellipsoids as
coefficient bodies for smoothness classes are standard in the Gaussian-model minimax theory
initiated by I. A. Ibragimov and R. Z. Has'minskii (*Statistical Estimation: Asymptotic
Theory*, Springer, 1981) and M. S. Pinsker ("Optimal filtering of square-integrable signals in
Gaussian noise," *Probl. Inf. Transm.* **16** (1980), 120–133).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- The trigonometric system on `[0,1]`, `1`-indexed: `φ₁ ≡ 1`, `φ_{2k}(x) = √2·cos(2πkx)`,
`φ_{2k+1}(x) = √2·sin(2πkx)` (for `j ≥ 2` the frequency is `j / 2`, ℕ-division). Index `0` is
unused and set to `0`. -/
noncomputable def trigBasis (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then 0
  else if j = 1 then 1
  else if j % 2 = 0 then Real.sqrt 2 * Real.cos (2 * Real.pi * (j / 2 : ℕ) * x)
  else Real.sqrt 2 * Real.sin (2 * Real.pi * (j / 2 : ℕ) * x)

/-- The regular design on `(0, 1]`: `x_i = (i+1)/n` for `i : Fin n`, i.e. `1/n, 2/n, …, 1`. -/
noncomputable def regularDesign (n : ℕ) : Fin n → ℝ :=
  fun i => ((i : ℕ) + 1 : ℝ) / n

/-- Coefficient estimate `θ̂ⱼ = n⁻¹ ∑ i, Y i · φⱼ(x_i)` at the regular design. -/
noncomputable def coeffEstimator {n : ℕ} (Y : Fin n → ℝ) (j : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, Y i * trigBasis j (regularDesign n i)

/-- **Projection (orthogonal series) estimator** of order `N`:
`f̂_{nN}(x) = ∑_{j=1}^N θ̂ⱼ · φⱼ(x)`. -/
noncomputable def projEstimator {n : ℕ} (Y : Fin n → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, coeffEstimator Y j * trigBasis j x

/-- The function with prescribed trigonometric coefficients: `f = ∑' j, θ j · φⱼ` (pointwise
`tsum`; genuinely the uniform-limit sum whenever `∑ |θ j| < ∞`). -/
noncomputable def seriesFun (θ : ℕ → ℝ) : ℝ → ℝ :=
  fun x => ∑' j, θ j * trigBasis j x

/-- The Sobolev weight sequence `a_j`: `j^β` for even `j`, `(j−1)^β` for odd `j`.
Note `a₀ = a₁ = 0` (for `β > 0`), so `θ 0, θ 1` are unweighted, as in the classical sequence. -/
noncomputable def sobolevWeight (β : ℝ) (j : ℕ) : ℝ :=
  if j % 2 = 0 then (j : ℝ) ^ β else ((j : ℝ) - 1) ^ β

/-- **Sobolev ellipsoid** `Θ(β, Q)`: coefficient sequences with `∑ j, a_j²·θ_j² ≤ Q`.
The `Summable` field is constitutive of "the series converges with sum ≤ Q": without it the
`tsum` junk value `0` would satisfy the bound vacuously. -/
structure MemEllipsoid (β Q : ℝ) (θ : ℕ → ℝ) : Prop where
  /-- Constitutive: the weighted square series converges. -/
  summable : Summable fun j => (sobolevWeight β j * θ j) ^ 2
  /-- Constitutive: the defining radius bound `∑ a_j²θ_j² ≤ Q`. -/
  tsum_le : ∑' j, (sobolevWeight β j * θ j) ^ 2 ≤ Q

/-- The ellipsoid radius `Q = L²/π^{2β}` corresponding to the Sobolev ball of radius `L`. -/
noncomputable def ellipsoidRadius (β L : ℝ) : ℝ :=
  L ^ 2 / Real.pi ^ (2 * β)

/-- **Sobolev class** `W(β, L)` on `[0,1]` (integer `β ≥ 1`): `f` is `β−1` times continuously
differentiable on `[0,1]`, `f^{(β−1)}` is absolutely continuous with a.e. derivative `g`
satisfying `∫₀¹ g² ≤ L²`. The a.e. derivative is an explicit witness. -/
structure MemSobolevW (β : ℕ) (L : ℝ) (f : ℝ → ℝ) : Prop where
  /-- Constitutive: `β − 1` times differentiable on `[0,1]`. -/
  contDiffOn : ContDiffOn ℝ (β - 1) f (Set.Icc 0 1)
  /-- Constitutive: absolute continuity of `f^{(β−1)}` with `L²`-bounded a.e. derivative,
  witnessed by `g` (the classical `f^{(β)}`). The energy bound uses the lower Lebesgue
  integral to avoid the Bochner junk value. -/
  ac_deriv : ∃ g : ℝ → ℝ, Measurable g ∧
    (∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((g x) ^ 2)) ≤ ENNReal.ofReal (L ^ 2) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      iteratedDerivWithin (β - 1) f (Set.Icc 0 1) x
        = iteratedDerivWithin (β - 1) f (Set.Icc 0 1) 0 + ∫ s in (0 : ℝ)..x, g s

/-- **Periodic Sobolev class** `W^{per}(β, L)`: members of `W(β, L)` whose derivatives of
orders `0, …, β−1` match at the endpoints of `[0,1]`. -/
def MemSobolevWper (β : ℕ) (L : ℝ) (f : ℝ → ℝ) : Prop :=
  MemSobolevW β L f ∧ ∀ j : ℕ, j ≤ β - 1 →
    iteratedDerivWithin j f (Set.Icc 0 1) 0 = iteratedDerivWithin j f (Set.Icc 0 1) 1

/-- The Riemann-sum residual `αⱼ = n⁻¹ ∑ᵢ f(xᵢ)·φⱼ(xᵢ) − θⱼ` of the coefficient estimate at
the regular design, for `f = seriesFun θ`. -/
noncomputable def riemannResidual (θ : ℕ → ℝ) (n : ℕ) (j : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * (∑ i : Fin n, seriesFun θ (regularDesign n i) * trigBasis j (regularDesign n i))
    - θ j

/-- The squared-bias tail `ρ_N = ∑_{j > N} θⱼ²` (re-indexed as a `tsum` over `m ↦ N+1+m`). -/
noncomputable def tailEnergy (θ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' m : ℕ, θ (N + 1 + m) ^ 2

end StatLean.NonparametricStatistics
