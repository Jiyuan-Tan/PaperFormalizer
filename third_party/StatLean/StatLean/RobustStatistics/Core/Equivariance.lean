module
public import StatLean.RobustStatistics.Core.Contamination

@[expose] public section

/-!
# Equivariance of statistical functionals — location, scale, dispersion

Robust estimation is organized around transformation behaviour: a *location* functional
follows shifts of the data, a *dispersion* functional ignores shifts and scales by `|c|`
(`MMY §2.3` for M-estimators, eq. (2.58) for dispersion, §4.9.1 and §6.17.1 for why
equivariance is the right invariance frame). This file states the population-level
(functional-on-measures) predicates; the finite-sample predicates
`StatLean.PointEstimation.IsLocEquivariant` / `IsLocInvariant` already exist and are reused
by the breakdown files.

* `IsLocationEquivariantOn T 𝒟` — `T((·+a)_#P) = T(P) + a` on a domain class `𝒟`.
* `IsLocationInvariantOn S 𝒟` — `S((·+a)_#P) = S(P)`.
* `IsScaleEquivariantOn S 𝒟` — `S((c·)_#P) = |c| S(P)` for `c ≠ 0`.
* `IsDispersionFunctionalOn S 𝒟` — the conjunction, the population form of `MMY` (2.58).
* `IsDispersionEstimator S` — the finite-sample form of (2.58).
* `map_add_grossErrorNbhd` — shifts map contamination neighbourhoods to contamination
  neighbourhoods of the shifted center (the equivariance step of `MMY §3.8.2`).

**Design note (domain classes).** Functionals such as the mean are only shift-equivariant
on integrable inputs — on a non-integrable `P` both sides degenerate to Lean's junk value
`0` and the identity fails. The predicates therefore quantify over an explicit domain
`𝒟 : Set (Measure Ω)`; each concrete functional registers the class on which its
equivariance actually holds.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.3 (shift
equivariance of M-estimators), eq. (2.58) (dispersion estimators), §3.8.2, §4.9.1.

**Bibliographic comments.** Equivariant estimation goes back to E. J. G. Pitman, "The
estimation of the location and scale parameters of a continuous population of any given
form," *Biometrika* **30** (1939), 391–421; its decision-theoretic role is ch. 3 of Lehmann
and Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998. In robustness it is the
side condition of Huber's 1964 minimax problem and of the maximal-breakdown bound
(Donoho–Huber 1983).
-/

open MeasureTheory

namespace StatLean.RobustStatistics

/-! ### Population-level predicates -/

/-- **Location equivariance** of a functional on a domain class `𝒟`
(`MMY §2.3`): shifting the distribution shifts the value, `T((·+a)_#P) = T(P) + a`. -/
def IsLocationEquivariantOn (T : Measure ℝ → ℝ) (𝒟 : Set (Measure ℝ)) : Prop :=
  ∀ P ∈ 𝒟, ∀ a : ℝ, T (P.map (· + a)) = T P + a

/-- **Location invariance** of a functional on a domain class `𝒟` (`MMY` eq. (2.58),
first condition): shifting the distribution does not change the value. -/
def IsLocationInvariantOn (S : Measure ℝ → ℝ) (𝒟 : Set (Measure ℝ)) : Prop :=
  ∀ P ∈ 𝒟, ∀ a : ℝ, S (P.map (· + a)) = S P

/-- **Absolute scale equivariance** of a functional on a domain class `𝒟` (`MMY` eq.
(2.58), second condition): rescaling the distribution by `c ≠ 0` multiplies the value
by `|c|`. -/
def IsScaleEquivariantOn (S : Measure ℝ → ℝ) (𝒟 : Set (Measure ℝ)) : Prop :=
  ∀ P ∈ 𝒟, ∀ c : ℝ, c ≠ 0 → S (P.map (c * ·)) = |c| * S P

/-- **Dispersion functional** on a domain class (`MMY` eq. (2.58), population form):
location invariant and absolutely scale equivariant. -/
def IsDispersionFunctionalOn (S : Measure ℝ → ℝ) (𝒟 : Set (Measure ℝ)) : Prop :=
  IsLocationInvariantOn S 𝒟 ∧ IsScaleEquivariantOn S 𝒟

/-! ### Finite-sample dispersion (`MMY` eq. (2.58))

The finite-sample location predicates `IsLocEquivariant`/`IsLocInvariant` live in
`StatLean.PointEstimation.Equivariance.Defs`; only the `|c|`-scale form is new here. -/

/-- **Dispersion (scatter) estimator** (`MMY` eq. (2.58)): a statistic that ignores shifts
and is absolutely scale equivariant, `S(x + c·𝟙) = S(x)` and `S(cx) = |c| S(x)`. -/
def IsDispersionEstimator {n : ℕ} (S : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ (a : ℝ) (x : Fin n → ℝ), S (x + a • (1 : Fin n → ℝ)) = S x) ∧
    ∀ (c : ℝ) (x : Fin n → ℝ), S (c • x) = |c| * S x

/-! ### Transformations of contamination neighbourhoods -/

/-- Shifting the data maps the gross-error neighbourhood of `P` onto the gross-error
neighbourhood of the shifted `P` (the equivariance step in the maximal-breakdown argument,
`MMY §3.8.2`, eq. (3.60)). -/
theorem map_add_grossErrorNbhd (P : Measure ℝ) (a ε : ℝ) :
    (fun R : Measure ℝ => R.map (· + a)) '' grossErrorNbhd P ε ⊆
      grossErrorNbhd (P.map (· + a)) ε := by
  rintro R ⟨S, ⟨Q, hQ, rfl⟩, rfl⟩
  haveI := hQ
  have hmeas : Measurable (fun x : ℝ => x + a) := measurable_add_const a
  exact ⟨Q.map (· + a), Measure.isProbabilityMeasure_map hmeas.aemeasurable,
    map_contaminate hmeas ε⟩

end StatLean.RobustStatistics
