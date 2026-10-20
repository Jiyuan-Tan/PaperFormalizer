module
public import StatLean.ComputationalStatistics.Resampling.CategoricalCounts
public import StatLean.ComputationalStatistics.Core.EmpiricalMeasure
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.Covariance

@[expose] public section

/-!
# Moments of multinomial category counts

First and second moments of the count vector `V_j = #{i | Aᵢ = j}` of `n`
i.i.d. `categorical q` draws:

* `integral_categoricalCount` — `E[V_j] = n·q_j`;
* `variance_categoricalCount` — `Var(V_j) = n·q_j·(1 − q_j)`;
* `covariance_categoricalCount` — `Cov(V_j, V_k) = −n·q_j·q_k` for `j ≠ k`.

Noted absent from the repo by the 2026-08-10 survey; they are the moment
inputs for resampling-scheme comparisons (e.g. multinomial vs. residual
resampling variances) in later rounds.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), ch. 4 p. 84 (the multinomial resampling vector);
moments are the classical multinomial moments.  (`ECS ch. 4`.)

**Proof formalization notes.**

* Each count is a sum of indicator functions of the independent coordinates,
  so the proofs are `iIndepFun_pi` + Bernoulli-moment algebra; no multinomial
  pmf manipulation is needed.
* Counts are `ℕ`-valued; the statements coerce to `ℝ`.

**Bibliographic comments.** Classical; see also Johnson–Kotz–Balakrishnan,
*Discrete Multivariate Distributions*, Wiley, 1997, ch. 35.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {m n : ℕ} {q : Fin m → ℝ}

/-! ### Coordinate indicators

Each count is the sum over the coordinates of the indicator that the coordinate
takes the value `j`; those indicators are independent (`iIndepFun_pi`) and
Bernoulli`(q j)`, which is all the moment computations need.
-/

/-- Indicator form of the count statistic, cast to `ℝ`. -/
private theorem cast_categoricalCounts (a : Fin n → Fin m) (j : Fin m) :
    ((categoricalCounts a j : ℕ) : ℝ) = ∑ i, if a i = j then (1 : ℝ) else 0 := by
  simp only [categoricalCounts, Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by split <;> simp

/-- On the finite index sample space every function is square-integrable. -/
private theorem memLp_two_pi (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (F : (Fin n → Fin m) → ℝ) :
    MemLp F 2 (Measure.pi fun _ : Fin n => categorical q) := by
  haveI : IsProbabilityMeasure (categorical q) := isProbabilityMeasure_categorical hq0 hq1
  exact (memLp_two_iff_integrable_sq
    (Integrable.of_finite (f := F)).aestronglyMeasurable).mpr Integrable.of_finite

/-- Mean of a scaled coordinate indicator: the coordinate marginal is
`categorical q`. -/
private theorem integral_coord_ite (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (i : Fin n) (j : Fin m) (c : ℝ) :
    ∫ a, (if a i = j then c else 0) ∂(Measure.pi fun _ : Fin n => categorical q)
      = q j * c := by
  haveI : IsProbabilityMeasure (categorical q) := isProbabilityMeasure_categorical hq0 hq1
  have hmp := measurePreserving_eval (fun _ : Fin n => categorical q) i
  have hmap := integral_map (μ := Measure.pi fun _ : Fin n => categorical q)
    (φ := fun a : Fin n → Fin m => a i) (f := fun s : Fin m => if s = j then c else 0)
    (measurable_pi_apply i).aemeasurable
    (Measurable.of_discrete.stronglyMeasurable.aestronglyMeasurable)
  rw [hmp.map_eq] at hmap
  rw [← hmap, integral_categorical (fun s => if s = j then c else 0) hq0]
  simp

/-- Indicators of *different* coordinates are uncorrelated (they are
independent under the product law). -/
private theorem cov_coord_ne (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    {i i' : Fin n} (hii : i ≠ i') (j k : Fin m) :
    covariance (fun a : Fin n → Fin m => if a i = j then (1 : ℝ) else 0)
      (fun a : Fin n → Fin m => if a i' = k then (1 : ℝ) else 0)
      (Measure.pi fun _ : Fin n => categorical q) = 0 := by
  haveI : IsProbabilityMeasure (categorical q) := isProbabilityMeasure_categorical hq0 hq1
  have hind : iIndepFun (fun (i : Fin n) (a : Fin n → Fin m) => a i)
      (Measure.pi fun _ : Fin n => categorical q) :=
    iIndepFun_pi (X := fun _ : Fin n => (id : Fin m → Fin m)) fun _ => aemeasurable_id
  have h2 := (hind.indepFun hii).comp
    (Measurable.of_discrete (f := fun s : Fin m => if s = j then (1 : ℝ) else 0))
    (Measurable.of_discrete (f := fun s : Fin m => if s = k then (1 : ℝ) else 0))
  exact h2.covariance_eq_zero (memLp_two_pi hq0 hq1 _) (memLp_two_pi hq0 hq1 _)

/-- Covariance of two indicators of the *same* coordinate. -/
private theorem cov_coord_same (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (i : Fin n) (j k : Fin m) :
    covariance (fun a : Fin n → Fin m => if a i = j then (1 : ℝ) else 0)
      (fun a : Fin n → Fin m => if a i = k then (1 : ℝ) else 0)
      (Measure.pi fun _ : Fin n => categorical q)
      = (if j = k then q j else 0) - q j * q k := by
  haveI : IsProbabilityMeasure (categorical q) := isProbabilityMeasure_categorical hq0 hq1
  rw [covariance_eq_sub (memLp_two_pi hq0 hq1 _) (memLp_two_pi hq0 hq1 _)]
  have hprod : ∀ a : Fin n → Fin m,
      ((fun a : Fin n → Fin m => if a i = j then (1 : ℝ) else 0) *
        fun a : Fin n → Fin m => if a i = k then (1 : ℝ) else 0) a
        = if a i = j then (if j = k then (1 : ℝ) else 0) else 0 := by
    intro a
    simp only [Pi.mul_apply]
    by_cases h1 : a i = j
    · by_cases h2 : j = k
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]
  simp only [hprod]
  rw [integral_coord_ite hq0 hq1 i j (if j = k then (1 : ℝ) else 0),
    integral_coord_ite hq0 hq1 i j 1, integral_coord_ite hq0 hq1 i k 1]
  by_cases hjk : j = k <;> simp [hjk]

/-- **Multinomial count mean**: `E[V_j] = n·q_j`. -/
theorem integral_categoricalCount
    -- USER-INPUT: nonnegative probability vector; ECS §2.5
    (hq0 : ∀ i, 0 ≤ q i)
    -- USER-INPUT: probabilities sum to one; ECS §2.5
    (hq1 : ∑ i, q i = 1) (j : Fin m) :
    ∫ a, (categoricalCounts a j : ℝ) ∂(Measure.pi fun _ : Fin n => categorical q)
      = n * q j := by
  haveI : IsProbabilityMeasure (categorical q) := isProbabilityMeasure_categorical hq0 hq1
  simp only [cast_categoricalCounts]
  rw [integral_finset_sum _ fun i _ => Integrable.of_finite,
    Finset.sum_congr rfl fun i _ => integral_coord_ite hq0 hq1 i j 1]
  simp

/-- **Multinomial count variance**: `Var(V_j) = n·q_j·(1 − q_j)`. -/
theorem variance_categoricalCount
    -- USER-INPUT: nonnegative probability vector; ECS §2.5
    (hq0 : ∀ i, 0 ≤ q i)
    -- USER-INPUT: probabilities sum to one; ECS §2.5
    (hq1 : ∑ i, q i = 1) (j : Fin m) :
    variance (fun a => (categoricalCounts a j : ℝ))
        (Measure.pi fun _ : Fin n => categorical q)
      = n * q j * (1 - q j) := by
  haveI : IsProbabilityMeasure (categorical q) := isProbabilityMeasure_categorical hq0 hq1
  simp only [cast_categoricalCounts]
  rw [variance_fun_sum fun i => memLp_two_pi hq0 hq1 _]
  have hrow : ∀ i : Fin n,
      ∑ i' : Fin n, covariance (fun a : Fin n → Fin m => if a i = j then (1 : ℝ) else 0)
          (fun a : Fin n → Fin m => if a i' = j then (1 : ℝ) else 0)
          (Measure.pi fun _ : Fin n => categorical q)
        = q j - q j * q j := by
    intro i
    rw [Finset.sum_eq_single i (fun b _ hb => cov_coord_ne hq0 hq1 (Ne.symm hb) j j)
      fun h => absurd (Finset.mem_univ i) h, cov_coord_same hq0 hq1 i j j, if_pos rfl]
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Multinomial count covariance**: `Cov(V_j, V_k) = −n·q_j·q_k` for
distinct categories. -/
theorem covariance_categoricalCount
    -- USER-INPUT: nonnegative probability vector; ECS §2.5
    (hq0 : ∀ i, 0 ≤ q i)
    -- USER-INPUT: probabilities sum to one; ECS §2.5
    (hq1 : ∑ i, q i = 1) {j k : Fin m}
    -- USER-INPUT: distinct categories; ECS ch. 4
    (hjk : j ≠ k) :
    covariance (fun a => (categoricalCounts a j : ℝ))
        (fun a => (categoricalCounts a k : ℝ))
        (Measure.pi fun _ : Fin n => categorical q)
      = -(n * q j * q k) := by
  haveI : IsProbabilityMeasure (categorical q) := isProbabilityMeasure_categorical hq0 hq1
  simp only [cast_categoricalCounts]
  rw [covariance_fun_sum_fun_sum (fun i => memLp_two_pi hq0 hq1 _)
    fun i => memLp_two_pi hq0 hq1 _]
  have hrow : ∀ i : Fin n,
      ∑ i' : Fin n, covariance (fun a : Fin n → Fin m => if a i = j then (1 : ℝ) else 0)
          (fun a : Fin n → Fin m => if a i' = k then (1 : ℝ) else 0)
          (Measure.pi fun _ : Fin n => categorical q)
        = -(q j * q k) := by
    intro i
    rw [Finset.sum_eq_single i (fun b _ hb => cov_coord_ne hq0 hq1 (Ne.symm hb) j k)
      fun h => absurd (Finset.mem_univ i) h, cov_coord_same hq0 hq1 i j k, if_neg hjk,
      zero_sub]
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

end StatLean.ComputationalStatistics
