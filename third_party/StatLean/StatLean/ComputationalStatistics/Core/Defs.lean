module
public import Mathlib.MeasureTheory.Measure.Dirac

@[expose] public section

/-!
# Computational statistics — core data model

The shared substrate for every sampling and resampling algorithm in the area:

* **`empiricalMeasure x`** — the discrete uniform distribution `(1/n)·Σᵢ δ_{xᵢ}`
  carried by a sample `x : Fin n → 𝓧` (ECS ch. 4, p. 83: "the observed sample can
  be considered to be the population");
* **`weightedMeasure w x`** — the weighted particle approximation `Σᵢ wᵢ·δ_{xᵢ}`
  of importance sampling and sequential Monte Carlo;
* **`categorical q`** — the law of a single draw from `Fin m` with probabilities
  `q` (the index distribution of multinomial resampling);
* **`mcEstimate g x`** — the Monte Carlo estimate `(1/n)·Σᵢ g(xᵢ)` of `∫ g dP`
  (ECS §2.2, eq. (2.8)).

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.2 (Monte Carlo estimation, eqs. (2.5)–(2.9)), §2.5
(random sampling from data), ch. 4 (the empirical population).  (`ECS §X.Y`.)

**Proof formalization notes.**

* This is a laptop-only Defs surface: definitions and `rfl`-level lemmas only,
  0-sorry; all lemma content lives in the sibling files.
* Weights are **real** (`w : Fin n → ℝ`), converted by `ENNReal.ofReal`; negative
  weights are silently clipped to `0`, and the probability-measure instance in
  `Core/EmpiricalMeasure.lean` carries the simplex hypotheses explicitly.  This
  matches the simplex conventions of `StatLean.Bayesian.multinomialWeight`.
* Edge behaviour: for `n = 0`, `empiricalMeasure` is the zero measure
  (`(0 : ℝ≥0∞)⁻¹ = ∞` collapses against the empty sum) and `mcEstimate` is junk
  `0` (`(0 : ℝ)⁻¹ = 0`); probability statements carry `[NeZero n]`.
* `empiricalMeasure` and `mcEstimate` deliberately **coexist** with
  `AsymptoticStatistics.EmpiricalProcess.empiricalMeasure` /
  `AsymptoticStatistics.empiricalAvg` (vdV lane),
  `StatLean.HypothesisTesting.empiricalMeasure` (bootstrap-asymptotics lane) and
  `StatLean.StatisticalLearning.empRisk` (SSBD lane): each area states its book's
  objects in its own vocabulary, per the per-area-reference convention.  A future
  promotion to a shared home is deliberately deferred.

**Bibliographic comments.** The empirical distribution as a surrogate population
is Efron's bootstrap principle (B. Efron, "Bootstrap methods: another look at the
jackknife," *Ann. Statist.* **7** (1979), 1–26); Monte Carlo estimation of
integrals goes back to Metropolis–Ulam (*J. Amer. Statist. Assoc.* **44** (1949),
335–341).
-/

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **empirical measure** of a sample `x : Fin n → 𝓧`:

`empiricalMeasure x = (1/n) · Σᵢ Measure.dirac (x i)`

(ECS ch. 4, p. 83: the sample viewed as a finite population).  Edge behaviour:
for `n = 0` this is the zero measure; the `IsProbabilityMeasure` instance is
stated under `[NeZero n]` in `Core/EmpiricalMeasure.lean`. -/
noncomputable def empiricalMeasure {n : ℕ} (x : Fin n → 𝓧) : Measure 𝓧 :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (x i)

/-- The **weighted empirical measure** `Σᵢ wᵢ · δ_{xᵢ}` of a weighted sample
(ECS §2.6; the particle approximation of sequential Monte Carlo).  Edge
behaviour: negative weights are clipped to `0` by `ENNReal.ofReal`; the
probability-measure statement carries `0 ≤ wᵢ` and `Σᵢ wᵢ = 1` explicitly. -/
noncomputable def weightedMeasure {n : ℕ} (w : Fin n → ℝ) (x : Fin n → 𝓧) :
    Measure 𝓧 :=
  ∑ i : Fin n, ENNReal.ofReal (w i) • Measure.dirac (x i)

/-- The **categorical distribution** on `Fin m` with probability vector `q`: the
law of a single draw of a particle index in multinomial resampling.  Edge
behaviour: negative entries are clipped to `0`; off-simplex `q` gives a
non-probability measure. -/
noncomputable def categorical {m : ℕ} (q : Fin m → ℝ) : Measure (Fin m) :=
  ∑ i : Fin m, ENNReal.ofReal (q i) • Measure.dirac i

/-- The **Monte Carlo estimate** `(1/n) · Σᵢ g(xᵢ)` of `∫ g dP` from a sample
`x` (ECS §2.2, eq. (2.8)).  Edge behaviour: `n = 0` gives junk `0`
(`(0 : ℝ)⁻¹ = 0`). -/
noncomputable def mcEstimate {n : ℕ} (g : 𝓧 → ℝ) (x : Fin n → 𝓧) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, g (x i)

/-- The categorical distribution is the weighted empirical measure of the
identity sample on the index set. -/
theorem categorical_eq_weightedMeasure {m : ℕ} (q : Fin m → ℝ) :
    categorical q = weightedMeasure q id := rfl

end StatLean.ComputationalStatistics
