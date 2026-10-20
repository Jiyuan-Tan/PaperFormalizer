module
public import StatLean.HypothesisTesting.Tests.Defs
public import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
public import StatLean.MultipleTesting.ForMathlib.ChiSquared
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateCLT
public import StatLean.AsymptoticStatistics.ParametricFamily.ScoreCLT
public import StatLean.HypothesisTesting.Bootstrap.Multivariate
public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.StrongLaw

@[expose] public section

/-!
# Pearson's chi-squared statistic for a simple multinomial null

`n` independent trials, each resulting in one of `k + 1` outcomes, outcome `j` occurring
with probability `pⱼ`. Writing `Yⱼ` for the number of trials resulting in outcome `j`, the
vector `(Y₁, …, Y_{k+1})` is multinomial. For the simple null `pⱼ = πⱼ`, the classical
statistic rejects for large values of
$$ Q_n \;=\; \sum_{j=1}^{k+1} \frac{(Y_j - n\pi_j)^2}{n\pi_j}. $$
This file fixes the cell counts and the statistic, and states the three asymptotic facts
about it:

* `multinomialCount`, `pearsonQ` — the cell counts `Yⱼ` and the statistic `Qₙ`;
* `pearsonQ_weakConverges_chiSquared` — under the null, `Qₙ ⇒ χ²_k`;
* `pearsonQ_weakConverges_noncentral` — under the local alternatives
  `p⁽ⁿ⁾ⱼ = πⱼ + hⱼ n^{-1/2}` with `∑ⱼ hⱼ = 0`, `Qₙ ⇒ χ²_k(λ)` with `λ = ∑ⱼ hⱼ²/πⱼ`;
* `pearsonQ_consistent` — against a fixed alternative `p ≠ π` the power tends to one;
* `pearsonQ_local_power_nondegenerate` — against the local alternatives with some `hⱼ ≠ 0`
  the power tends to a limit strictly between `α` and `1`.

The degrees of freedom are `k`, one less than the number of cells `k + 1`: the counts are
constrained by `∑ⱼ Yⱼ = n`, so only `k` of the centred and scaled cell frequencies are
free. Correspondingly, the noncentrality parameter is a sum over all `k + 1` cells, of the
squared local shifts standardized by the null cell probabilities.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 16 (Testing Goodness of
Fit), §16.3 (Pearson's Chi-Squared Statistic), Theorem 16.3.1 (§16.3.1, Simple Null
Hypothesis): Pearson's chi-squared statistic converges to `χ²_k`. (`TSH4 §16.3 Thm 16.3.1`.)

**Proof formalization notes.**
* `multinomialCount` and `pearsonQ` are defined directly on categorical observations
  `X : Fin n → Ω → Fin (k+1)` rather than on a multinomial random vector: the counts are
  then genuine functions of the sample, the multinomial law is a consequence of
  independence rather than an assumption, and independence enters as `iIndepFun` exactly
  as in the other sampling models of the area.
* Cell probabilities are recorded as `((μ) {j}).toReal = πⱼ`, i.e. through the law of a
  single observation; this keeps the null and the local alternatives in one and the same
  format and avoids carrying a multinomial p.m.f. as data.
* The null hypothesis `π` is required to have all cells strictly positive (`0 < πⱼ`) —
  the "interior point" condition. It is genuinely needed: `Qₙ` divides by `nπⱼ`, and the
  limiting covariance matrix is singular without it.
* Convergence in law is `AsymptoticStatistics.WeakConverges` applied to the pushforwards
  of the stage-`n` sampling laws under the statistic, matching the convention of that
  area's `ForMathlib/Contiguity.lean`.
* The intended proof of the first two items is the multivariate central limit theorem
  (`ProbabilityTheory.tendstoInDistribution_multivariate_clt`) applied to the vector of
  the first `k` centred cell frequencies, followed by the continuous mapping theorem for
  the quadratic form with matrix `Σ⁻¹`; the algebraic identity that this quadratic form
  equals `Qₙ` (which reintroduces the `(k+1)`-st cell) is the only combinatorial step.
* The third item is the law of large numbers: if `pⱼ ≠ πⱼ` for some `j` then
  `Qₙ ≥ n (Yⱼ/n − πⱼ)²/πⱼ → ∞` in probability.
* `noncentralChiSquared` of `ForMathlib/NoncentralChiSquared.lean` takes its noncentrality
  parameter in `ℝ≥0`, while `multinomialNoncentrality` is a real sum; the two are joined
  by `Real.toNNReal`, which is the identity here because all `πⱼ > 0` makes the sum
  nonnegative.

**Bibliographic comments.** The statistic and the chi-squared approximation to its null
distribution are due to K. Pearson ("On the criterion that a given system of deviations
from the probable in the case of a correlated system of variables is such that it can be
reasonably supposed to have arisen from random sampling," *Philosophical Magazine*,
Series 5, **50** (1900), 157–175). The noncentral chi-squared limit under local
alternatives, and the resulting local power calculation, go back to R. A. Fisher
("The conditions under which χ² measures the discrepancy between observation and
hypothesis," *J. Roy. Statist. Soc.* **87** (1924), 442–450) and to
E. S. Pearson ("The probability integral transformation for testing goodness of fit and
combining independent tests of significance," *Biometrika* **30** (1938), 134–148); the
modern treatment via the multivariate central limit theorem is standard.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators Matrix RealInnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The cell counts and Pearson's statistic -/

/-- The **multinomial cell count** `Yⱼ = #{ i : Xᵢ = j }`: the number of the `n` trials
resulting in outcome `j`, for categorical observations taking values in the `k + 1`
outcomes `Fin (k+1)`. -/
noncomputable def multinomialCount {n k : ℕ} (X : Fin n → Ω → Fin (k + 1))
    (j : Fin (k + 1)) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun i => X i ω = j).card

/-- **Pearson's chi-squared statistic**
`Qₙ = ∑_{j=1}^{k+1} (Yⱼ − nπⱼ)² / (nπⱼ)` for the simple null `p = π`, where `Yⱼ` are the
cell counts of the sample `X`. Degenerate cells (`πⱼ = 0`) or an empty sample (`n = 0`)
produce division by zero, i.e. the junk value `0` in that summand; every statement below
assumes `0 < n` and `0 < πⱼ` for all `j`. -/
noncomputable def pearsonQ {n k : ℕ} (π : Fin (k + 1) → ℝ) (X : Fin n → Ω → Fin (k + 1))
    (ω : Ω) : ℝ :=
  ∑ j : Fin (k + 1), ((multinomialCount X j ω : ℝ) - (n : ℝ) * π j) ^ 2 / ((n : ℝ) * π j)

/-- The **noncentrality parameter** attached to a local shift `h` of the cell
probabilities: `λ = ∑_{j=1}^{k+1} hⱼ² / πⱼ`. This is `|I^{1/2}(π) h|²` for the multinomial
information matrix, which is why it is the noncentrality of the limiting law. -/
noncomputable def multinomialNoncentrality {k : ℕ} (π h : Fin (k + 1) → ℝ) : ℝ :=
  ∑ j : Fin (k + 1), (h j) ^ 2 / π j

/-! ### Algebraic core: reduction to the first `k` cells

The proof drops the last cell and works with the first `k` centred, scaled cell
frequencies `reducedVec`.  The `(k+1)`-st cell is reconstructed from the linear constraint
`∑ⱼ (Yⱼ − nπⱼ) = 0`, which is the algebraic content of `pearsonQ_eq_reducedQ` below:
Pearson's `Qₙ` equals the reduced quadratic form `reducedQ`, a sum over the first `k` cells
plus a single term standing in for the dropped cell.  The matrix realisation of `reducedQ`
as `⟪z, Σ⁻¹ z⟫` (Sherman–Morrison) is `reducedQ_eq_quadForm`. -/

/-- The number of trials is the sum of the cell counts (partition of `Fin n` by outcome). -/
private lemma sum_multinomialCount {n k : ℕ} (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) :
    ∑ j : Fin (k + 1), multinomialCount X j ω = n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin (k + 1))))
    (f := fun i => X i ω) (fun i _ => Finset.mem_univ _)
  simpa [multinomialCount, Finset.card_univ, Fintype.card_fin] using h.symm

/-- The centred cell frequencies sum to zero: this is the linear constraint that makes the
limiting covariance singular and lets the last cell be reconstructed from the first `k`. -/
private lemma sum_centered_eq_zero {n k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπsum : ∑ j, π j = 1) (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) :
    ∑ j : Fin (k + 1), ((multinomialCount X j ω : ℝ) - (n : ℝ) * π j) = 0 := by
  have hcount : (∑ j : Fin (k + 1), (multinomialCount X j ω : ℝ)) = (n : ℝ) := by
    rw [← Nat.cast_sum, sum_multinomialCount]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hπsum, mul_one, hcount, sub_self]

/-- The reduced quadratic form: a sum over the first `k` cells plus one term for the dropped
cell (reconstructed via the linear constraint). -/
private noncomputable def reducedQ {k : ℕ} (π : Fin (k + 1) → ℝ) (z : Fin k → ℝ) : ℝ :=
  (∑ i : Fin k, z i ^ 2 / π i.castSucc) + (∑ i : Fin k, z i) ^ 2 / π (Fin.last k)

/-- The first `k` centred, scaled cell frequencies `(Yⱼ − nπⱼ)/√n`, `j < k`. -/
private noncomputable def reducedVec {n k : ℕ} (π : Fin (k + 1) → ℝ)
    (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) (i : Fin k) : ℝ :=
  ((multinomialCount X i.castSucc ω : ℝ) - (n : ℝ) * π i.castSucc) / Real.sqrt n

/-- **The combinatorial step.** Pearson's statistic equals the reduced quadratic form of the
first `k` centred frequencies; the dropped `(k+1)`-st cell reappears through the constraint
`∑ⱼ (Yⱼ − nπⱼ) = 0`.  Holds for every `n` (both sides are the junk value `0` when `n = 0`). -/
private lemma pearsonQ_eq_reducedQ {n k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπsum : ∑ j, π j = 1) (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) :
    pearsonQ π X ω = reducedQ π (reducedVec π X ω) := by
  -- the square-and-divide identity `(c/√n)² / p = c² / (n p)`
  have hsq : ∀ (c p : ℝ), (c / Real.sqrt n) ^ 2 / p = c ^ 2 / ((n : ℝ) * p) := by
    intro c p
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n), div_div]
  -- the reconstruction: `∑_{i<k} (Y_{i} − nπ_{i}) = − (Y_last − nπ_last)`
  have hlast : (∑ i : Fin k, ((multinomialCount X i.castSucc ω : ℝ) - (n : ℝ) * π i.castSucc))
      = - ((multinomialCount X (Fin.last k) ω : ℝ) - (n : ℝ) * π (Fin.last k)) := by
    have h0 := sum_centered_eq_zero hπsum X ω
    rw [Fin.sum_univ_castSucc] at h0
    linarith [h0]
  rw [pearsonQ, reducedQ]
  simp only [reducedVec]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hsq]
  · rw [← Finset.sum_div, hsq, hlast, neg_sq]

/-- **The noncentrality identity.** The multinomial noncentrality `∑ⱼ hⱼ²/πⱼ` equals the
reduced quadratic form of the first `k` drift components; the dropped cell reappears via the
constraint `∑ⱼ hⱼ = 0`. This is `pearsonQ_eq_reducedQ` for the drift `h` in place of the
centred counts. -/
private lemma multinomialNoncentrality_eq_reducedQ {k : ℕ} {π h : Fin (k + 1) → ℝ}
    (hhsum : ∑ j, h j = 0) :
    multinomialNoncentrality π h = reducedQ π (fun i => h i.castSucc) := by
  rw [multinomialNoncentrality, reducedQ, Fin.sum_univ_castSucc]
  have hlast : (∑ i : Fin k, h i.castSucc) = - h (Fin.last k) := by
    have := hhsum; rw [Fin.sum_univ_castSucc] at this; linarith
  congr 1
  rw [hlast, neg_sq]

/-- The reduced `k × k` covariance `Σ = diag(π') − π' π'ᵀ` of the first `k` cell
frequencies (`π' j = π j.castSucc`). It is `PosDef` (`reducedCov_posDef`), unlike the full
`(k+1)`-dimensional covariance which is singular. -/
private noncomputable def reducedCov {k : ℕ} (π : Fin (k + 1) → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    (if i = j then π i.castSucc else 0) - π i.castSucc * π j.castSucc

/-- The Sherman–Morrison inverse of `reducedCov`: `Σ⁻¹ = diag(1/π') + (1/π_{k}) 𝟙 𝟙ᵀ`. -/
private noncomputable def reducedCovInv {k : ℕ} (π : Fin (k + 1) → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    (if i = j then (π i.castSucc)⁻¹ else 0) + (π (Fin.last k))⁻¹

/-- The action of `Σ⁻¹` on a vector: `(Σ⁻¹ z)_i = z_i/π_i + (∑_j z_j)/π_{k}`. -/
private lemma reducedCovInv_mulVec {k : ℕ} {π : Fin (k + 1) → ℝ} (z : Fin k → ℝ) (i : Fin k) :
    (reducedCovInv π *ᵥ z) i
      = (π i.castSucc)⁻¹ * z i + (π (Fin.last k))⁻¹ * ∑ j, z j := by
  simp only [reducedCovInv, Matrix.mulVec, dotProduct, Matrix.of_apply]
  have h : ∀ j : Fin k,
      ((if i = j then (π i.castSucc)⁻¹ else 0) + (π (Fin.last k))⁻¹) * z j
        = (if i = j then (π i.castSucc)⁻¹ * z j else 0) + (π (Fin.last k))⁻¹ * z j := by
    intro j
    by_cases hij : i = j
    · simp only [if_pos hij, add_mul]
    · simp only [if_neg hij, zero_add, add_mul]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib,
    Finset.sum_ite_eq Finset.univ i (fun j => (π i.castSucc)⁻¹ * z j), ← Finset.mul_sum]
  simp

/-- **The quadratic form.** `z ⬝ᵥ Σ⁻¹ z = reducedQ π z`. -/
private lemma dotProduct_reducedCovInv {k : ℕ} {π : Fin (k + 1) → ℝ} (z : Fin k → ℝ) :
    z ⬝ᵥ (reducedCovInv π) *ᵥ z = reducedQ π z := by
  rw [reducedQ]
  simp only [dotProduct]
  simp_rw [reducedCovInv_mulVec, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [div_eq_mul_inv]; ring)
  · rw [← Finset.sum_mul, div_eq_mul_inv]; ring

/-- **Sherman–Morrison.** `Σ · Σ⁻¹ = 1`.  The cancellation uses `π_{k} = 1 − ∑_{j<k} π_j`
(the last cell probability), i.e. the null-probability normalisation. -/
private lemma reducedCov_mul_inv {k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1) :
    reducedCov π * reducedCovInv π = 1 := by
  have hlne : π (Fin.last k) ≠ 0 := (hπpos _).ne'
  ext i l
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [reducedCov, reducedCovInv, Matrix.of_apply]
  have step : ∀ j : Fin k,
      (((if i = j then π i.castSucc else 0) - π i.castSucc * π j.castSucc) *
        ((if j = l then (π j.castSucc)⁻¹ else 0) + (π (Fin.last k))⁻¹))
      = (if i = j then (if j = l then (1 : ℝ) else 0) else 0)
        + (if i = j then π i.castSucc * (π (Fin.last k))⁻¹ else 0)
        - (if j = l then π i.castSucc else 0)
        - π i.castSucc * π j.castSucc * (π (Fin.last k))⁻¹ := by
    intro j
    have hj : π j.castSucc ≠ 0 := (hπpos _).ne'
    split_ifs <;> subst_vars <;> field_simp <;> ring
  rw [Finset.sum_congr rfl (fun j _ => step j), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib,
    Finset.sum_ite_eq Finset.univ i (fun j => if j = l then (1 : ℝ) else 0),
    Finset.sum_ite_eq Finset.univ i (fun _ => π i.castSucc * (π (Fin.last k))⁻¹),
    Finset.sum_ite_eq' Finset.univ l (fun _ => π i.castSucc)]
  simp only [Finset.mem_univ, if_true]
  have hD : (∑ j : Fin k, π i.castSucc * π j.castSucc * (π (Fin.last k))⁻¹)
      = π i.castSucc * (π (Fin.last k))⁻¹ * ∑ j : Fin k, π j.castSucc := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  have hs : (∑ j : Fin k, π j.castSucc) = 1 - π (Fin.last k) := by
    have := hπsum; rw [Fin.sum_univ_castSucc] at this; linarith
  rw [hD, hs]
  have hz : π i.castSucc * (π (Fin.last k))⁻¹ - π i.castSucc
      - π i.castSucc * (π (Fin.last k))⁻¹ * (1 - π (Fin.last k)) = 0 := by
    field_simp; ring
  linear_combination hz

/-- `Σ⁻¹` is positive definite (`∑ z_i²/π_i + (∑ z_i)²/π_{k} > 0` for `z ≠ 0`). -/
private lemma reducedCovInv_posDef {k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπpos : ∀ j, 0 < π j) : (reducedCovInv π).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, reducedCovInv, Matrix.of_apply, star_trivial]
    by_cases h : i = j <;> simp [h, eq_comm]
  · intro x hx
    rw [star_trivial, dotProduct_reducedCovInv, reducedQ]
    have hA : 0 < ∑ i : Fin k, x i ^ 2 / π i.castSucc := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · exact div_nonneg (sq_nonneg _) (hπpos _).le
      · exact div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))) (hπpos _)
    have hB : 0 ≤ (∑ i : Fin k, x i) ^ 2 / π (Fin.last k) :=
      div_nonneg (sq_nonneg _) (hπpos _).le
    linarith

/-- `Σ = reducedCov` is positive definite (inverse of the `PosDef` matrix `Σ⁻¹`). -/
private lemma reducedCov_posDef {k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1) : (reducedCov π).PosDef := by
  have hinv : (reducedCovInv π)⁻¹ = reducedCov π :=
    Matrix.inv_eq_left_inv (reducedCov_mul_inv hπpos hπsum)
  rw [← hinv]
  exact (reducedCovInv_posDef hπpos).inv

/-- `Σ⁻¹ = reducedCovInv` as matrices. -/
private lemma reducedCov_inv_eq {k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1) :
    (reducedCov π)⁻¹ = reducedCovInv π :=
  Matrix.inv_eq_right_inv (reducedCov_mul_inv hπpos hπsum)

/-- The cell count as a real-valued measurable function of the sample. -/
private lemma measurable_multinomialCount {n k : ℕ} {X : Fin n → Ω → Fin (k + 1)}
    (hX : ∀ i, Measurable (X i)) (j : Fin (k + 1)) :
    Measurable (fun ω => (multinomialCount X j ω : ℝ)) := by
  classical
  have hrw : (fun ω => (multinomialCount X j ω : ℝ))
      = fun ω => ∑ i : Fin n, if X i ω = j then (1 : ℝ) else 0 := by
    funext ω
    rw [multinomialCount, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => by by_cases h : X i ω = j <;> simp [h])
  rw [hrw]
  refine Finset.univ.measurable_sum (fun i _ => ?_)
  exact Measurable.ite ((hX i) (measurableSet_singleton j)) measurable_const measurable_const

/-- The standardised reduced cell-count vector `((Yⱼ − nπⱼ)/√n)_{j<k}` as an element of
`EuclideanSpace ℝ (Fin k)`; the object the multivariate CLT is applied to. -/
private noncomputable def reducedCount {n k : ℕ} (π : Fin (k + 1) → ℝ)
    (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (reducedVec π X ω)

private lemma measurable_reducedCount {n k : ℕ} {π : Fin (k + 1) → ℝ}
    {X : Fin n → Ω → Fin (k + 1)} (hX : ∀ i, Measurable (X i)) :
    Measurable (reducedCount π X) := by
  have hg : Measurable (fun ω => reducedVec π X ω) := by
    refine measurable_pi_iff.mpr (fun i => ?_)
    simp only [reducedVec]
    exact ((measurable_multinomialCount hX i.castSucc).sub measurable_const).div measurable_const
  exact (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp hg

/-! #### The canonical i.i.d. transfer

We realise `reducedCount` as the standardised sum of the centred per-observation indicator
vectors `g x = indicatorVec x − piVec π`, transfer the per-stage law to the canonical
infinite-product i.i.d. model (via `iIndepFun_iff_map_fun_eq_pi_map`), and apply the
reusable fixed-i.i.d. CLT `clt_finDim`. -/

/-- The cell count as a real-valued sum of indicators. -/
private lemma multinomialCount_cast_eq_sum {n k : ℕ} (X : Fin n → Ω → Fin (k + 1))
    (j : Fin (k + 1)) (ω : Ω) :
    (multinomialCount X j ω : ℝ) = ∑ i : Fin n, if X i ω = j then (1 : ℝ) else 0 := by
  classical
  rw [multinomialCount, Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => by by_cases h : X i ω = j <;> simp [h])

/-- The per-observation indicator vector in the reduced space:
`(indicatorVec x)_i = 1[x = i.castSucc]`. -/
private noncomputable def indicatorVec {k : ℕ} (x : Fin (k + 1)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => if x = i.castSucc then (1 : ℝ) else 0)

/-- The reduced null-probability vector `(piVec π)_i = π i.castSucc`. -/
private noncomputable def piVec {k : ℕ} (π : Fin (k + 1) → ℝ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => π i.castSucc)

/-- The real inner product on `EuclideanSpace ℝ (Fin k)` as a coordinate sum. -/
private lemma inner_euclidean_eq_sum {k : ℕ} (u w : EuclideanSpace ℝ (Fin k)) :
    ⟪u, w⟫ = ∑ i, u i * w i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The centred indicator vector `g x = indicatorVec x − piVec π` paired with a direction
`u`, in coordinate form. -/
private lemma inner_u_g {k : ℕ} (π : Fin (k + 1) → ℝ) (u : EuclideanSpace ℝ (Fin k))
    (x : Fin (k + 1)) :
    ⟪u, indicatorVec x - piVec π⟫
      = ∑ i, u i * ((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc) := by
  rw [inner_euclidean_eq_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rfl

/-- The `∑_x π_x 1[x = i.castSucc] = π i.castSucc` pick identity. -/
private lemma sum_pi_ite_castSucc {k : ℕ} (π : Fin (k + 1) → ℝ) (i : Fin k) :
    ∑ x : Fin (k + 1), π x * (if x = i.castSucc then (1 : ℝ) else 0) = π i.castSucc := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ i.castSucc (fun x => π x)]
  simp

/-- The `∑_x π_x 1[x = i.cs] 1[x = j.cs] = δ_{ij} π i.castSucc` product-pick identity. -/
private lemma sum_pi_ite_ite {k : ℕ} (π : Fin (k + 1) → ℝ) (i j : Fin k) :
    ∑ x : Fin (k + 1),
        π x * ((if x = i.castSucc then (1 : ℝ) else 0) * (if x = j.castSucc then 1 else 0))
      = if i = j then π i.castSucc else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hx : ∀ x : Fin (k + 1),
        π x * ((if x = i.castSucc then (1 : ℝ) else 0) * (if x = i.castSucc then 1 else 0))
          = π x * (if x = i.castSucc then 1 else 0) := by
      intro x; by_cases hx : x = i.castSucc <;> simp [hx]
    simp_rw [hx]; exact sum_pi_ite_castSucc π i
  · rw [if_neg hij]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hxi : x = i.castSucc
    · by_cases hxj : x = j.castSucc
      · exact absurd (Fin.castSucc_injective k (hxi.symm.trans hxj)) hij
      · simp [hxj]
    · simp [hxi]

/-- The covariance-entry integral: `∑_x π_x (b_i − π'_i)(b_j − π'_j) = reducedCov π i j`. -/
private lemma sum_pi_center_prod {k : ℕ} (π : Fin (k + 1) → ℝ) (hπsum : ∑ j, π j = 1)
    (i j : Fin k) :
    ∑ x : Fin (k + 1),
        π x * (((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc)
          * ((if x = j.castSucc then 1 else 0) - π j.castSucc))
      = reducedCov π i j := by
  have hexp : ∀ x : Fin (k + 1),
      π x * (((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc)
          * ((if x = j.castSucc then 1 else 0) - π j.castSucc))
        = π x * ((if x = i.castSucc then 1 else 0) * (if x = j.castSucc then 1 else 0))
          - π j.castSucc * (π x * (if x = i.castSucc then 1 else 0))
          - π i.castSucc * (π x * (if x = j.castSucc then 1 else 0))
          + π i.castSucc * π j.castSucc * π x := by
    intro x; ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_pi_ite_ite, ← Finset.mul_sum, sum_pi_ite_castSucc, ← Finset.mul_sum, sum_pi_ite_castSucc,
    ← Finset.mul_sum, hπsum]
  simp only [reducedCov, Matrix.of_apply]
  ring

/-- `reducedCount` is the standardised sum of the centred per-observation indicator vectors. -/
private lemma reducedCount_eq_smul_sum {n k : ℕ} (π : Fin (k + 1) → ℝ)
    (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) :
    reducedCount π X ω
      = (Real.sqrt n)⁻¹ • ∑ i : Fin n, (indicatorVec (X i ω) - piVec π) := by
  classical
  rw [reducedCount]
  simp only [indicatorVec, piVec]
  simp_rw [← WithLp.toLp_sub]
  rw [← WithLp.toLp_sum, ← WithLp.toLp_smul]
  refine congrArg (WithLp.toLp 2) ?_
  funext j
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [reducedVec, multinomialCount_cast_eq_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [div_eq_inv_mul]

/-- **Multivariate CLT for the reduced cell frequencies** (the single deep analytic brick of
the null-limit proof). The standardised reduced count vector converges in law to the centred
Gaussian with the reduced covariance `Σ = diag π' − π' π'ᵀ`.

The proof realises `reducedCount` as the standardised sum of the centred per-observation
indicator vectors `g x = indicatorVec x − piVec π` (`reducedCount_eq_smul_sum`), transfers the
per-stage law to the canonical infinite-product i.i.d. model produced by
`ProbabilityTheory.exists_iid` (matching both sequences to `(Measure.pi …).map` via
`iIndepFun_iff_map_fun_eq_pi_map`), and applies the reusable fixed-i.i.d. CLT
`AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim`. The covariance side-condition
`∫ ⟪u, g⟫⟪v, g⟫ = u ⬝ᵥ Σ v` is the finite computation `sum_pi_center_prod`, and the zero-mean
side-condition is `sum_pi_ite_castSucc`. -/
private lemma reducedCount_weakConverges_gaussian {k : ℕ} {π : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : Measure (Fin (k + 1))}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1)
    (hX : ∀ n i, Measurable (X n i))
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hlaw : ∀ n i, Measure.map (X n i) (P n) = μ)
    (hcell : ∀ j, (μ {j}).toReal = π j) :
    WeakConverges (fun n => (P n).map (reducedCount π (X n)))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (reducedCov π)) := by
  classical
  -- `μ` is the common observation law, a probability measure.
  haveI hP1prob : IsProbabilityMeasure (P 1) := ‹∀ n, IsProbabilityMeasure (P n)› 1
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [← hlaw 1 0]
    exact Measure.isProbabilityMeasure_map (μ := P 1) (hX 1 0).aemeasurable
  -- the canonical i.i.d. model `(Ω₀, P₀, Z)` with marginal law `μ`
  obtain ⟨Ω₀, mΩ₀, P₀, Z, hZmeas, hZlaw, hZindep, hP₀prob⟩ :=
    ProbabilityTheory.exists_iid ℕ μ
  letI : MeasurableSpace Ω₀ := mΩ₀
  haveI : IsProbabilityMeasure P₀ := hP₀prob
  -- centred per-observation indicator map `g` and per-observation vectors `Y`
  set g : Fin (k + 1) → EuclideanSpace ℝ (Fin k) := fun x => indicatorVec x - piVec π with hg
  have hgmeas : Measurable g := (measurable_of_finite indicatorVec).sub measurable_const
  set Y : ℕ → Ω₀ → EuclideanSpace ℝ (Fin k) := fun i ω => g (Z i ω) with hY
  -- an integral of `F ∘ Z 0` reduces to a finite `π`-weighted sum
  have hkey : ∀ (F : Fin (k + 1) → ℝ), ∫ ω, F (Z 0 ω) ∂P₀ = ∑ x, π x * F x := by
    intro F
    have hFmeas : Measurable F := measurable_of_finite F
    rw [show (∫ ω, F (Z 0 ω) ∂P₀) = ∫ x, F x ∂(P₀.map (Z 0)) from
          (integral_map (hZmeas 0).aemeasurable hFmeas.aestronglyMeasurable).symm,
        (hZlaw 0).map_eq, integral_fintype (f := F) Integrable.of_finite]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [MeasureTheory.Measure.real, hcell x, smul_eq_mul]
  -- inputs to `clt_finDim`
  have hYmeas : ∀ i, Measurable (Y i) := fun i => hgmeas.comp (hZmeas i)
  have hYindep : iIndepFun Y P₀ := hZindep.comp (fun _ => g) (fun _ => hgmeas)
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) P₀ P₀ := fun i =>
    (show IdentDistrib (Z i) (Z 0) P₀ P₀ from
      ⟨(hZmeas i).aemeasurable, (hZmeas 0).aemeasurable,
        (hZlaw i).map_eq.trans (hZlaw 0).map_eq.symm⟩).comp hgmeas
  -- the centred indicators have zero mean
  have h_zero_mean : ∀ u : EuclideanSpace ℝ (Fin k), ∫ ω, ⟪u, Y 0 ω⟫ ∂P₀ = 0 := by
    intro u
    have hint : (∫ ω, ⟪u, Y 0 ω⟫ ∂P₀) = ∑ x, π x * ⟪u, g x⟫ := hkey (fun x => ⟪u, g x⟫)
    rw [hint]
    simp_rw [hg, inner_u_g, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hterm : ∀ x : Fin (k + 1),
        π x * (u i * ((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc))
          = u i * (π x * (if x = i.castSucc then 1 else 0)) - u i * π i.castSucc * π x := by
      intro x; ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_pi_ite_castSucc, ← Finset.mul_sum, hπsum]
    ring
  -- the covariance identity `∫ ⟪u,·⟫⟪v,·⟫ = u ⬝ Σ v`
  have h_cov : ∀ u v : EuclideanSpace ℝ (Fin k),
      ∫ ω, ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P₀ = u.ofLp ⬝ᵥ (reducedCov π).mulVec v.ofLp := by
    intro u v
    have hRHS : u.ofLp ⬝ᵥ (reducedCov π).mulVec v.ofLp
        = ∑ i, ∑ j, (u i * v j) * reducedCov π i j := by
      simp only [dotProduct, Matrix.mulVec]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show u i * (reducedCov π i j * v j) = (u i * v j) * reducedCov π i j
      ring
    have hint : (∫ ω, ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P₀) = ∑ x, π x * (⟪u, g x⟫ * ⟪v, g x⟫) :=
      hkey (fun x => ⟪u, g x⟫ * ⟪v, g x⟫)
    rw [hint, hRHS]
    simp_rw [hg, inner_u_g, Finset.sum_mul_sum]
    have hswap : ∀ x : Fin (k + 1),
        π x * ∑ i, ∑ j, (u i * ((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc))
              * (v j * ((if x = j.castSucc then 1 else 0) - π j.castSucc))
          = ∑ i, ∑ j, (u i * v j)
              * (π x * (((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc)
                  * ((if x = j.castSucc then 1 else 0) - π j.castSucc))) := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    simp_rw [hswap]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.mul_sum, sum_pi_center_prod π hπsum i j]
  -- the centred indicators are square-integrable (bounded, factoring through a finite type)
  have h_L2 : MemLp (Y 0) 2 P₀ := by
    obtain ⟨C, hC⟩ := (Set.finite_range (fun x => ‖g x‖)).bddAbove
    have hbd : ∀ ω, ‖Y 0 ω‖ ≤ C := fun ω => hC ⟨Z 0 ω, rfl⟩
    exact (memLp_top_of_bound (hYmeas 0).aestronglyMeasurable C
      (Filter.Eventually.of_forall hbd)).mono_exponent le_top
  -- the fixed-i.i.d. CLT for the canonical model
  have hclt := AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim
    P₀ Y hYmeas hYindep hYident h_zero_mean (reducedCov π)
    (reducedCov_posDef hπpos hπsum).posSemidef h_cov h_L2
  -- the canonical standardised sum has, at each `n`, the same law as `reducedCount`
  have hmatch : ∀ n : ℕ,
      P₀.map (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω)
        = (P n).map (reducedCount π (X n)) := by
    intro n
    set F : (Fin n → Fin (k + 1)) → EuclideanSpace ℝ (Fin k) :=
      fun d => (Real.sqrt n)⁻¹ • ∑ i : Fin n, g (d i) with hF
    have hFmeas : Measurable F := measurable_of_finite F
    have hgZ : Measurable (fun ω (i : Fin n) => Z (i : ℕ) ω) :=
      measurable_pi_lambda _ (fun i => hZmeas i)
    have hgX : Measurable (fun ω (i : Fin n) => X n i ω) :=
      measurable_pi_lambda _ (fun i => hX n i)
    have hLHSfun : (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω)
        = F ∘ (fun ω (i : Fin n) => Z (i : ℕ) ω) := by
      funext ω
      simp only [hF, hY, Function.comp]
      rw [← Fin.sum_univ_eq_sum_range (fun i => g (Z i ω)) n]
    have hRHSfun : reducedCount π (X n) = F ∘ (fun ω (i : Fin n) => X n i ω) := by
      funext ω
      rw [reducedCount_eq_smul_sum π (X n) ω]
      simp only [hF, hg, Function.comp]
    have hpiZ : P₀.map (fun ω (i : Fin n) => Z (i : ℕ) ω) = Measure.pi (fun _ : Fin n => μ) := by
      have hsub : iIndepFun (fun (i : Fin n) => Z (i : ℕ)) P₀ :=
        hZindep.precomp Fin.val_injective
      rw [(iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin n) => Z (i : ℕ))
        (fun i => (hZmeas (i : ℕ)).aemeasurable)).1 hsub]
      congr 1; funext i; exact (hZlaw (i : ℕ)).map_eq
    have hpiX : (P n).map (fun ω (i : Fin n) => X n i ω) = Measure.pi (fun _ : Fin n => μ) := by
      rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX n i).aemeasurable)).1 (hindep n)]
      congr 1; funext i; exact hlaw n i
    rw [hLHSfun, hRHSfun, ← Measure.map_map hFmeas hgZ, ← Measure.map_map hFmeas hgX,
      hpiZ, hpiX]
  simp only [hmatch] at hclt
  exact hclt

/-- **Null limiting distribution.** Under the simple null hypothesis `pⱼ = πⱼ` for
`j = 1, …, k+1`, Pearson's statistic converges in law to the chi-squared distribution with
`k` degrees of freedom. -/
theorem pearsonQ_weakConverges_chiSquared {k : ℕ} {π : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : Measure (Fin (k + 1))}
    -- USER-INPUT: at least one degree of freedom; `χ²₀` is degenerate
    (hk : 0 < k)
    -- USER-INPUT: the null cell probabilities are an interior point of the simplex
    (hπpos : ∀ j, 0 < π j)
    -- USER-INPUT: the null cell probabilities sum to one
    (hπsum : ∑ j, π j = 1)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the trials are i.i.d.; Pearson 1900
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at every stage every trial has the common law `μ`
    (hlaw : ∀ n, ∀ i, Measure.map (X n i) (P n) = μ)
    -- USER-INPUT: the null hypothesis: the cell probabilities of `μ` are `π`
    (hcell : ∀ j, (μ {j}).toReal = π j) :
    WeakConverges (fun n => Measure.map (pearsonQ π (X n)) (P n)) (chiSquared k) := by
  -- the continuous quadratic form `q z = ⟪z, Σ⁻¹ z⟫`
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (reducedCov π)⁻¹ with hTdef
  set q : EuclideanSpace ℝ (Fin k) → ℝ := fun z => ⟪z, T z⟫ with hqdef
  have hq_cont : Continuous q := continuous_id.inner T.continuous
  -- pointwise: `q (reducedCount ω) = pearsonQ ω` (bridge algebra)
  have hq : ∀ n ω, q (reducedCount π (X n) ω) = pearsonQ π (X n) ω := by
    intro n ω
    simp only [hqdef, hTdef]
    rw [Matrix.inner_toEuclideanCLM, reducedCov_inv_eq hπpos hπsum, pearsonQ_eq_reducedQ hπsum,
      ← dotProduct_reducedCovInv]
    rfl
  -- the lifted CLT brick, then continuous mapping
  have hbrick := reducedCount_weakConverges_gaussian (π := π) (P := P) (X := X) (μ := μ)
    hπpos hπsum hX hindep hlaw hcell
  have hmapped := hbrick.map hq_cont hq_cont.measurable
  -- the target is `χ²_k` (Gaussian → chi-squared bridge)
  have htarget : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (reducedCov π)).map q
      = chiSquared k := by
    simp only [hqdef, hTdef]
    exact multivariateGaussian_map_inner_inv_eq_chiSquared hk (reducedCov_posDef hπpos hπsum)
  -- each pushforward term equals the law of `pearsonQ`
  have hseq : (fun n => ((P n).map (reducedCount π (X n))).map q)
      = fun n => Measure.map (pearsonQ π (X n)) (P n) := by
    funext n
    rw [Measure.map_map hq_cont.measurable (measurable_reducedCount (hX n))]
    exact Measure.map_congr (Filter.Eventually.of_forall (fun ω => hq n ω))
  rw [hseq, htarget] at hmapped
  exact hmapped

/-! ### (ii) Local alternatives and the noncentral limit -/

/-! #### The drifting-row transfer

Unlike the null case this is a *triangular array*: the per-observation law `μ n` drifts with
`n`, so the fixed-i.i.d. brick `clt_finDim` no longer applies. The multivariate bootstrap
limit law `meanVec_root_tendsto` is exactly a drifting-row statement — it is proved by the
Cramér–Wold reduction to the univariate triangular-array central limit theorem — and the
local-alternative array satisfies its class condition `meanVecSeqClass`: the cell weights
`p⁽ⁿ⁾ = π + h/√n` converge to `π`, hence so do the laws, the mean vectors and the covariance
matrices of the centred indicator vectors. The only bookkeeping is the centring:
`reducedCount` centres at `π`, while `meanVecRootLaw` centres at the stage-`n` mean, and the
difference is the fixed vector `(hⱼ)_{j<k}` — which is precisely why the limit is the
Gaussian shifted by the drift. -/

/-- The centred per-observation indicator vector `g x = indicatorVec x − piVec π`. -/
private noncomputable def centredIndicator {k : ℕ} (π : Fin (k + 1) → ℝ)
    (x : Fin (k + 1)) : EuclideanSpace ℝ (Fin k) :=
  indicatorVec x - piVec π

private lemma ofLp_centredIndicator {k : ℕ} (π : Fin (k + 1) → ℝ) (x : Fin (k + 1))
    (i : Fin k) :
    WithLp.ofLp (centredIndicator π x) i
      = (if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc := rfl

private lemma measurable_centredIndicator {k : ℕ} (π : Fin (k + 1) → ℝ) :
    Measurable (centredIndicator π) := measurable_of_finite _

/-- The multinomial cell law attached to a probability vector `π` on `Fin (k+1)`. -/
private noncomputable def cellMeasure {k : ℕ} (π : Fin (k + 1) → ℝ) :
    Measure (Fin (k + 1)) :=
  Measure.sum fun x => ENNReal.ofReal (π x) • Measure.dirac x

private lemma cellMeasure_apply {k : ℕ} (π : Fin (k + 1) → ℝ) (s : Set (Fin (k + 1))) :
    cellMeasure π s = ∑ x, ENNReal.ofReal (π x) * s.indicator 1 x := by
  rw [cellMeasure, Measure.sum_apply _ s.toFinite.measurableSet, tsum_fintype]
  exact Finset.sum_congr rfl fun x _ => by
    rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

private lemma isProbabilityMeasure_cellMeasure {k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1) :
    IsProbabilityMeasure (cellMeasure π) := by
  constructor
  rw [cellMeasure_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => (hπpos x).le), hπsum, ENNReal.ofReal_one]

private lemma cellMeasure_real {k : ℕ} {π : Fin (k + 1) → ℝ} (hπpos : ∀ j, 0 < π j)
    (j : Fin (k + 1)) : (cellMeasure π).real {j} = π j := by
  rw [MeasureTheory.Measure.real, cellMeasure_apply]
  rw [Finset.sum_eq_single j
    (fun b _ hb => by simp [Set.mem_singleton_iff, hb])
    (fun hb => absurd (Finset.mem_univ j) hb)]
  simp [ENNReal.toReal_ofReal (hπpos j).le]

/-- Integrals against the law of the centred indicator are finite `π`-weighted sums. -/
private lemma integral_map_centredIndicator {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (π : Fin (k + 1) → ℝ) (ρ : Measure (Fin (k + 1)))
    [IsFiniteMeasure ρ] {f : EuclideanSpace ℝ (Fin k) → E} (hf : Continuous f) :
    ∫ y, f y ∂(ρ.map (centredIndicator π)) = ∑ x, ρ.real {x} • f (centredIndicator π x) := by
  rw [integral_map (measurable_centredIndicator π).aemeasurable hf.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]

/-- Every continuous function is `p`-integrable for the law of the centred indicator: that
law is carried by finitely many points. -/
private lemma memLp_map_centredIndicator {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    (π : Fin (k + 1) → ℝ) (ρ : Measure (Fin (k + 1))) [IsFiniteMeasure ρ]
    {f : EuclideanSpace ℝ (Fin k) → E} (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp f p (ρ.map (centredIndicator π)) := by
  have hfm : AEStronglyMeasurable f (ρ.map (centredIndicator π)) := hf.aestronglyMeasurable
  rw [memLp_map_measure_iff hfm (measurable_centredIndicator π).aemeasurable]
  obtain ⟨C, hC⟩ := (Set.finite_range fun x => ‖f (centredIndicator π x)‖).bddAbove
  exact (memLp_top_of_bound (hfm.comp_aemeasurable (measurable_centredIndicator π).aemeasurable)
    C (Filter.Eventually.of_forall fun x => hC ⟨x, rfl⟩)).mono_exponent le_top

/-- The mean vector of a weighted family of centred indicators, in coordinates. -/
private lemma sum_smul_centredIndicator {k : ℕ} (π w : Fin (k + 1) → ℝ)
    (hw : ∑ x, w x = 1) :
    ∑ x, w x • centredIndicator π x
      = WithLp.toLp 2 (fun i : Fin k => w i.castSucc - π i.castSucc) := by
  simp only [centredIndicator, indicatorVec, piVec]
  simp_rw [← WithLp.toLp_sub, ← WithLp.toLp_smul]
  rw [← WithLp.toLp_sum]
  refine congrArg (WithLp.toLp 2) ?_
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hterm : ∀ x : Fin (k + 1),
      w x * ((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc)
        = w x * (if x = i.castSucc then 1 else 0) - π i.castSucc * w x := by
    intro x; ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hw, mul_one, sum_pi_ite_castSucc w i]

/-- The covariance matrix of the law of the centred indicator, in weights. -/
private lemma covMatrix_map_centredIndicator {k : ℕ} (π : Fin (k + 1) → ℝ)
    (ρ : Measure (Fin (k + 1))) [IsProbabilityMeasure ρ] (i j : Fin k) :
    covMatrix (ρ.map (centredIndicator π)) i j
      = (∑ x, ρ.real {x} * (WithLp.ofLp (centredIndicator π x) i
            * WithLp.ofLp (centredIndicator π x) j))
        - (∑ x, ρ.real {x} * WithLp.ofLp (centredIndicator π x) i)
          * ∑ x, ρ.real {x} * WithLp.ofLp (centredIndicator π x) j := by
  haveI : IsProbabilityMeasure (ρ.map (centredIndicator π)) :=
    Measure.isProbabilityMeasure_map (measurable_centredIndicator π).aemeasurable
  rw [covMatrix, Matrix.of_apply,
    covariance_eq_sub (memLp_map_centredIndicator π ρ
        (f := fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i) (by fun_prop) 2)
      (memLp_map_centredIndicator π ρ
        (f := fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y j) (by fun_prop) 2)]
  have h1 : ∫ y : EuclideanSpace ℝ (Fin k),
        (fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i) y
        * (fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y j) y ∂(ρ.map (centredIndicator π))
      = ∑ x, ρ.real {x} * (WithLp.ofLp (centredIndicator π x) i
          * WithLp.ofLp (centredIndicator π x) j) := by
    rw [integral_map_centredIndicator π ρ
      (f := fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i * WithLp.ofLp y j) (by fun_prop)]
    exact Finset.sum_congr rfl fun x _ => by rw [smul_eq_mul]
  have h2 : ∀ l : Fin k, ∫ y : EuclideanSpace ℝ (Fin k),
        (fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y l) y ∂(ρ.map (centredIndicator π))
      = ∑ x, ρ.real {x} * WithLp.ofLp (centredIndicator π x) l := by
    intro l
    rw [integral_map_centredIndicator π ρ
      (f := fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y l) (by fun_prop)]
    exact Finset.sum_congr rfl fun x _ => by rw [smul_eq_mul]
  simp only [Pi.mul_apply]
  rw [h1, h2 i, h2 j]

/-- Translating the centred multivariate Gaussian by `m` gives mean `m`. -/
private lemma multivariateGaussian_map_add {k : ℕ} (m : EuclideanSpace ℝ (Fin k))
    (S : Matrix (Fin k) (Fin k) ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S).map (fun z => m + z)
      = multivariateGaussian m S := by
  rw [multivariateGaussian, multivariateGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp [Function.comp]

/-- **Multivariate CLT for the reduced cell frequencies under local alternatives.** Under
`p⁽ⁿ⁾ = π + h/√n` the standardised reduced count vector converges in law to `N(ν, Σ)` with
drift `ν = (hⱼ)_{j<k}` and covariance `Σ = reducedCov π`.

This is a *triangular array*: the per-observation law drifts with `n`. The proof runs the
drifting-row multivariate limit law `meanVec_root_tendsto` on the sequence of laws
`F n = (μ n).map (centredIndicator π)` of the centred per-observation indicator vector, whose
membership in `meanVecSeqClass Q` (with `Q` the law under the null cell weights `π`) is the
finite computation `p⁽ⁿ⁾ → π`; the identification of the pushforwards is
`hlawid`, the translation of the mean-vector root by the drift. -/
private lemma reducedCount_weakConverges_noncentral {k : ℕ} {π h : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : ℕ → Measure (Fin (k + 1))}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1) (hhsum : ∑ j, h j = 0)
    (hX : ∀ n i, Measurable (X n i))
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hlaw : ∀ n i, Measure.map (X n i) (P n) = μ n)
    (hcell : ∀ n j, ((μ n) {j}).toReal = π j + h j / Real.sqrt (n : ℝ)) :
    WeakConverges (fun n => (P n).map (reducedCount π (X n)))
      (multivariateGaussian (WithLp.toLp 2 (fun i => h i.castSucc)) (reducedCov π)) := by
  classical
  haveI hcellprob : IsProbabilityMeasure (cellMeasure π) :=
    isProbabilityMeasure_cellMeasure hπpos hπsum
  set Q : Measure (EuclideanSpace ℝ (Fin k)) := (cellMeasure π).map (centredIndicator π) with hQ
  haveI hQprob : IsProbabilityMeasure Q :=
    Measure.isProbabilityMeasure_map (measurable_centredIndicator π).aemeasurable
  set hred : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun i : Fin k => h i.castSucc) with hhred
  -- the stage-`n` cell weights and their limit
  set w : ℕ → Fin (k + 1) → ℝ := fun n x => π x + h x / Real.sqrt (n : ℝ) with hw
  have hwsum : ∀ n, ∑ x, w n x = 1 := by
    intro n
    simp only [hw]
    rw [Finset.sum_add_distrib, hπsum, ← Finset.sum_div, hhsum, zero_div, add_zero]
  have hwlim : ∀ x, Tendsto (fun n : ℕ => w n x) atTop (𝓝 (π x)) := by
    intro x
    have hz : Tendsto (fun n : ℕ => h x / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [hw, add_zero] using tendsto_const_nhds.add hz
  have hμprob : ∀ n : ℕ, 0 < n → IsProbabilityMeasure (μ n) := by
    intro n hn
    rw [← hlaw n ⟨0, hn⟩]
    exact Measure.isProbabilityMeasure_map (hX n ⟨0, hn⟩).aemeasurable
  have hμreal : ∀ n x, (μ n).real {x} = w n x := by
    intro n x
    rw [MeasureTheory.Measure.real, hcell n x]
  -- the sequence of laws of the centred indicator
  set F : ℕ → Measure (EuclideanSpace ℝ (Fin k)) :=
    fun n => if n = 0 then Q else (μ n).map (centredIndicator π) with hF
  have hFeq : ∀ n : ℕ, 0 < n → F n = (μ n).map (centredIndicator π) := by
    intro n hn; simp only [hF, if_neg hn.ne']
  have hF0 : F 0 = Q := by simp only [hF, if_pos rfl]
  have hFprob : ∀ n : ℕ, 0 < n → IsProbabilityMeasure (F n) := by
    intro n hn
    haveI := hμprob n hn
    rw [hFeq n hn]
    exact Measure.isProbabilityMeasure_map (measurable_centredIndicator π).aemeasurable
  -- the class conditions
  have hFclass : F ∈ meanVecSeqClass Q := by
    refine ⟨hFprob, ?_, ?_, ?_, ?_⟩
    · intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [hF0, hQ]
        exact memLp_map_centredIndicator π (cellMeasure π) continuous_id' 2
      · haveI := hμprob n hn
        rw [hFeq n hn]
        exact memLp_map_centredIndicator π (μ n) continuous_id' 2
    · intro f
      have hQint : ∫ y, f y ∂Q = ∑ x, π x * f (centredIndicator π x) := by
        rw [hQ, integral_map_centredIndicator π (cellMeasure π) f.continuous]
        exact Finset.sum_congr rfl fun x _ => by rw [cellMeasure_real hπpos x, smul_eq_mul]
      rw [hQint]
      refine Tendsto.congr' ?_ (tendsto_finset_sum _ fun x _ => (hwlim x).mul tendsto_const_nhds)
      filter_upwards [eventually_gt_atTop 0] with n hn
      haveI := hμprob n hn
      rw [hFeq n hn, integral_map_centredIndicator π (μ n) f.continuous]
      exact Finset.sum_congr rfl fun x _ => by rw [hμreal n x, smul_eq_mul]
    · intro i
      have hQint : ∫ y, WithLp.ofLp y i ∂Q
          = ∑ x, π x * WithLp.ofLp (centredIndicator π x) i := by
        rw [hQ, integral_map_centredIndicator π (cellMeasure π)
          (f := fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i) (by fun_prop)]
        exact Finset.sum_congr rfl fun x _ => by rw [cellMeasure_real hπpos x, smul_eq_mul]
      rw [hQint]
      refine Tendsto.congr' ?_ (tendsto_finset_sum _ fun x _ => (hwlim x).mul tendsto_const_nhds)
      filter_upwards [eventually_gt_atTop 0] with n hn
      haveI := hμprob n hn
      rw [hFeq n hn, integral_map_centredIndicator π (μ n)
        (f := fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i) (by fun_prop)]
      exact Finset.sum_congr rfl fun x _ => by rw [hμreal n x, smul_eq_mul]
    · intro i j
      have hQcov : covMatrix Q i j
          = (∑ x, π x * (WithLp.ofLp (centredIndicator π x) i
                * WithLp.ofLp (centredIndicator π x) j))
            - (∑ x, π x * WithLp.ofLp (centredIndicator π x) i)
              * ∑ x, π x * WithLp.ofLp (centredIndicator π x) j := by
        rw [hQ, covMatrix_map_centredIndicator π (cellMeasure π) i j]
        congr 1
        · exact Finset.sum_congr rfl fun x _ => by rw [cellMeasure_real hπpos x]
        · congr 1 <;> exact Finset.sum_congr rfl fun x _ => by rw [cellMeasure_real hπpos x]
      rw [hQcov]
      refine Tendsto.congr' ?_
        (((tendsto_finset_sum _ fun x _ => (hwlim x).mul tendsto_const_nhds).sub
          ((tendsto_finset_sum _ fun x _ => (hwlim x).mul tendsto_const_nhds).mul
            (tendsto_finset_sum _ fun x _ => (hwlim x).mul tendsto_const_nhds))))
      filter_upwards [eventually_gt_atTop 0] with n hn
      haveI := hμprob n hn
      haveI := hFprob n hn
      rw [hFeq n hn, covMatrix_map_centredIndicator π (μ n) i j]
      congr 1
      · exact Finset.sum_congr rfl fun x _ => by rw [hμreal n x]
      · congr 1 <;> exact Finset.sum_congr rfl fun x _ => by rw [hμreal n x]
  -- the limiting covariance is the reduced multinomial covariance
  have hcovQ : covMatrix Q = reducedCov π := by
    ext i j
    rw [hQ, covMatrix_map_centredIndicator π (cellMeasure π) i j]
    have hz : ∀ l : Fin k,
        ∑ x, (cellMeasure π).real {x} * WithLp.ofLp (centredIndicator π x) l = 0 := by
      intro l
      have hterm : ∀ x : Fin (k + 1),
          (cellMeasure π).real {x} * WithLp.ofLp (centredIndicator π x) l
            = π x * (if x = l.castSucc then (1 : ℝ) else 0) - π l.castSucc * π x := by
        intro x
        rw [cellMeasure_real hπpos x, ofLp_centredIndicator]; ring
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib, sum_pi_ite_castSucc, ← Finset.mul_sum, hπsum, mul_one, sub_self]
    rw [hz i, hz j, mul_zero, sub_zero]
    have hterm : ∀ x : Fin (k + 1),
        (cellMeasure π).real {x} * (WithLp.ofLp (centredIndicator π x) i
            * WithLp.ofLp (centredIndicator π x) j)
          = π x * (((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc)
              * ((if x = j.castSucc then 1 else 0) - π j.castSucc)) := by
      intro x
      rw [cellMeasure_real hπpos x, ofLp_centredIndicator, ofLp_centredIndicator]
    simp_rw [hterm]
    exact sum_pi_center_prod π hπsum i j
  have hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q := by
    rw [hQ]; exact memLp_map_centredIndicator π (cellMeasure π) continuous_id' 2
  -- the drifting-row multivariate central limit theorem
  have hweak : WeakConverges (fun n => meanVecRootLaw (F n) n)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (covMatrix Q)) :=
    meanVec_root_tendsto hQ2 hFclass
  have hshift := hweak.map (f := fun z : EuclideanSpace ℝ (Fin k) => hred + z)
    (by fun_prop) (by fun_prop)
  rw [multivariateGaussian_map_add, hcovQ] at hshift
  -- the law identity: `reducedCount` is the mean-vector root translated by the drift
  have hlawid : ∀ n : ℕ, 0 < n →
      (meanVecRootLaw (F n) n).map (fun z : EuclideanSpace ℝ (Fin k) => hred + z)
        = (P n).map (reducedCount π (X n)) := by
    intro n hn
    haveI := hμprob n hn
    haveI hFnprob : IsProbabilityMeasure ((μ n).map (centredIndicator π)) :=
      Measure.isProbabilityMeasure_map (measurable_centredIndicator π).aemeasurable
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg n)
    have h1 : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ = (Real.sqrt (n : ℝ))⁻¹ := by
      have hne : (n : ℝ) ≠ 0 := hnR.ne'
      field_simp
      linarith [hsq]
    have h2 : Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hspos.ne'
    have hmeanF : ∫ z, z ∂(F n) = (Real.sqrt (n : ℝ))⁻¹ • hred := by
      rw [hFeq n hn, integral_map_centredIndicator π (μ n) continuous_id']
      have hre : ∀ x : Fin (k + 1), (μ n).real {x} • centredIndicator π x
          = w n x • centredIndicator π x := fun x => by rw [hμreal n x]
      simp_rw [hre]
      rw [sum_smul_centredIndicator π (w n) (hwsum n), hhred, ← WithLp.toLp_smul]
      refine congrArg (WithLp.toLp 2) ?_
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, hw]
      rw [div_eq_inv_mul]
      ring
    set Ψ : (Fin n → EuclideanSpace ℝ (Fin k)) → EuclideanSpace ℝ (Fin k) :=
      fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i with hΨ
    have hΨcont : Continuous Ψ :=
      (continuous_finset_sum _ fun i _ => continuous_apply i).fun_const_smul _
    have hstep1 : (meanVecRootLaw (F n) n).map (fun z : EuclideanSpace ℝ (Fin k) => hred + z)
        = (Measure.pi fun _ : Fin n => F n).map Ψ := by
      rw [meanVecRootLaw, Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext y
      simp only [Function.comp_apply, hmeanF, hΨ]
      rw [smul_sub, smul_smul, smul_smul, h1, h2, one_smul]
      abel
    have hpiX : (P n).map (fun ω (i : Fin n) => X n i ω) = Measure.pi (fun _ : Fin n => μ n) := by
      rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX n i).aemeasurable)).1 (hindep n)]
      congr 1; funext i; exact hlaw n i
    have hXmeas : Measurable (fun ω (i : Fin n) => X n i ω) :=
      measurable_pi_lambda _ (fun i => hX n i)
    have hgmeas : Measurable
        (fun (d : Fin n → Fin (k + 1)) (i : Fin n) => centredIndicator π (d i)) :=
      measurable_pi_lambda _ (fun i =>
        (measurable_centredIndicator π).comp (measurable_pi_apply i))
    have hstep2 : (P n).map (reducedCount π (X n)) = (Measure.pi fun _ : Fin n => F n).map Ψ := by
      have hcomp : reducedCount π (X n)
          = Ψ ∘ ((fun (d : Fin n → Fin (k + 1)) (i : Fin n) => centredIndicator π (d i))
              ∘ (fun ω (i : Fin n) => X n i ω)) := by
        funext ω
        rw [reducedCount_eq_smul_sum π (X n) ω]
        rfl
      rw [hcomp, ← Measure.map_map hΨcont.measurable (hgmeas.comp hXmeas),
        ← Measure.map_map hgmeas hXmeas, hpiX,
        Measure.pi_map_pi (fun _ => (measurable_centredIndicator π).aemeasurable)]
      have hfun : (fun _ : Fin n => (μ n).map (centredIndicator π)) = fun _ : Fin n => F n := by
        funext i; rw [hFeq n hn]
      exact congrArg (Measure.map Ψ) (congrArg Measure.pi hfun)
    rw [hstep1, hstep2]
  intro f
  refine (hshift f).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hlawid n hn]


/-- **Limiting distribution under local alternatives.** Under the alternative sequence
`p⁽ⁿ⁾ⱼ = πⱼ + hⱼ n^{-1/2}` with `∑_{j=1}^{k+1} hⱼ = 0`, Pearson's statistic converges in
law to the noncentral chi-squared distribution with `k` degrees of freedom and
noncentrality parameter
$$ \lambda \;=\; \sum_{j=1}^{k+1} \frac{h_j^2}{\pi_j}. $$
The constraint `∑ⱼ hⱼ = 0` is what makes `p⁽ⁿ⁾` a probability vector; positivity of the
perturbed cells is assumed separately, since it fails for small `n` when some `hⱼ < 0`. -/
theorem pearsonQ_weakConverges_noncentral {k : ℕ} {π h : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : ℕ → Measure (Fin (k + 1))}
    -- USER-INPUT: at least one degree of freedom
    (hk : 0 < k)
    -- USER-INPUT: the null cell probabilities are an interior point of the simplex
    (hπpos : ∀ j, 0 < π j)
    -- USER-INPUT: the null cell probabilities sum to one
    (hπsum : ∑ j, π j = 1)
    -- USER-INPUT: the local shifts sum to zero, so the perturbed vector is a probability
    -- vector
    (hhsum : ∑ j, h j = 0)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the trials are i.i.d.; Pearson 1900
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at stage `n` every trial has the stage-`n` law `μ n`
    (hlaw : ∀ n, ∀ i, Measure.map (X n i) (P n) = μ n)
    -- USER-INPUT: the local alternative: the stage-`n` cell probabilities are
    -- `πⱼ + hⱼ n^{-1/2}`
    (hcell : ∀ n, ∀ j, ((μ n) {j}).toReal = π j + h j / Real.sqrt (n : ℝ)) :
    WeakConverges (fun n => Measure.map (pearsonQ π (X n)) (P n))
      (noncentralChiSquared k (multinomialNoncentrality π h).toNNReal) := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (reducedCov π)⁻¹ with hTdef
  set q : EuclideanSpace ℝ (Fin k) → ℝ := fun z => ⟪z, T z⟫ with hqdef
  have hq_cont : Continuous q := continuous_id.inner T.continuous
  have hq : ∀ n ω, q (reducedCount π (X n) ω) = pearsonQ π (X n) ω := by
    intro n ω
    simp only [hqdef, hTdef]
    rw [Matrix.inner_toEuclideanCLM, reducedCov_inv_eq hπpos hπsum, pearsonQ_eq_reducedQ hπsum,
      ← dotProduct_reducedCovInv]
    rfl
  have hbrick := reducedCount_weakConverges_noncentral (π := π) (h := h) (P := P) (X := X) (μ := μ)
    hπpos hπsum hhsum hX hindep hlaw hcell
  set ν : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun i => h i.castSucc) with hνdef
  have hmapped := hbrick.map hq_cont hq_cont.measurable
  have hnc_id : (⟪ν, Matrix.toEuclideanCLM (𝕜 := ℝ) (reducedCov π)⁻¹ ν⟫ : ℝ)
      = multinomialNoncentrality π h := by
    rw [Matrix.inner_toEuclideanCLM, reducedCov_inv_eq hπpos hπsum, dotProduct_reducedCovInv,
      hνdef]
    exact (multinomialNoncentrality_eq_reducedQ hhsum).symm
  have htarget : (multivariateGaussian ν (reducedCov π)).map q
      = noncentralChiSquared k (multinomialNoncentrality π h).toNNReal := by
    simp only [hqdef, hTdef]
    rw [multivariateGaussian_map_inner_inv_eq_noncentralChiSquared
      (reducedCov_posDef hπpos hπsum) ν, hnc_id]
  have hseq : (fun n => ((P n).map (reducedCount π (X n))).map q)
      = fun n => Measure.map (pearsonQ π (X n)) (P n) := by
    funext n
    rw [Measure.map_map hq_cont.measurable (measurable_reducedCount (hX n))]
    exact Measure.map_congr (Filter.Eventually.of_forall (fun ω => hq n ω))
  rw [hseq, htarget] at hmapped
  exact hmapped

/-! ### (iii) Power -/

/-- Pearson's statistic as a function of the raw data tuple `d : Fin n → Fin (k+1)`. -/
private noncomputable def pearsonQTuple {n k : ℕ} (π : Fin (k + 1) → ℝ)
    (d : Fin n → Fin (k + 1)) : ℝ :=
  ∑ j : Fin (k + 1),
    (((Finset.univ.filter fun i => d i = j).card : ℝ) - (n : ℝ) * π j) ^ 2 / ((n : ℝ) * π j)

private lemma pearsonQ_eq_tuple {n k : ℕ} (π : Fin (k + 1) → ℝ)
    (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) :
    pearsonQ π X ω = pearsonQTuple π (fun i => X i ω) := rfl

private lemma measurable_pearsonQ {n k : ℕ} {π : Fin (k + 1) → ℝ}
    {X : Fin n → Ω → Fin (k + 1)} (hX : ∀ i, Measurable (X i)) :
    Measurable (pearsonQ π X) := by
  have : pearsonQ π X = pearsonQTuple π ∘ (fun ω (i : Fin n) => X i ω) := by
    funext ω; exact pearsonQ_eq_tuple π X ω
  rw [this]
  exact (measurable_of_finite _).comp (measurable_pi_lambda _ hX)

/-- **Law transfer for Pearson's statistic.** The law of `pearsonQ` under any i.i.d. sample
with marginal `μ` is the pushforward of the product measure `μ^{⊗ n}` under `pearsonQTuple`;
in particular it does not depend on the underlying probability space. -/
private lemma map_pearsonQ_eq_tuple {n k : ℕ} {π : Fin (k + 1) → ℝ} {μ : Measure (Fin (k + 1))}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Fin n → Ω' → Fin (k + 1)} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P') (hlaw : ∀ i, Measure.map (X i) P' = μ) :
    P'.map (pearsonQ π X) = (Measure.pi (fun _ : Fin n => μ)).map (pearsonQTuple π) := by
  have hpi : P'.map (fun ω (i : Fin n) => X i ω) = Measure.pi (fun _ : Fin n => μ) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).1 hindep]
    congr 1; funext i; exact hlaw i
  have hcomp : pearsonQ π X = pearsonQTuple π ∘ (fun ω (i : Fin n) => X i ω) := by
    funext ω; exact pearsonQ_eq_tuple π X ω
  rw [hcomp, ← Measure.map_map (measurable_of_finite _) (measurable_pi_lambda _ hX), hpi]

/-- **Consistency against a fixed alternative.** If the true cell probabilities differ
from `π` in at least one cell, the power of the chi-squared test tends to one. The reason
is that `Qₙ ≥ n (Yⱼ/n − πⱼ)²/πⱼ` for the offending cell `j`, and `Yⱼ/n → pⱼ ≠ πⱼ` in
probability by the law of large numbers, so `Qₙ → ∞` in probability. -/
theorem pearsonQ_consistent {k : ℕ} {α c : ℝ} {π p : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : Measure (Fin (k + 1))}
    -- USER-INPUT: at least one degree of freedom
    (hk : 0 < k)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the null cell probabilities are an interior point of the simplex
    (hπpos : ∀ j, 0 < π j)
    -- USER-INPUT: the null cell probabilities sum to one
    (hπsum : ∑ j, π j = 1)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the trials are i.i.d.; Pearson 1900
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at every stage every trial has the common alternative law `μ`
    (hlaw : ∀ n, ∀ i, Measure.map (X n i) (P n) = μ)
    -- USER-INPUT: the alternative cell probabilities of `μ` are `p`
    (hcell : ∀ j, (μ {j}).toReal = p j)
    -- USER-INPUT: the alternative genuinely differs from the null in some cell
    (hne : ∃ j, p j ≠ π j) :
    Tendsto (fun n => ((P n) {ω | c < pearsonQ π (X n) ω}).toReal) atTop (nhds 1) := by
  classical
  -- `μ` is the common (alternative) observation law, a probability measure.
  haveI hP1prob : IsProbabilityMeasure (P 1) := ‹∀ n, IsProbabilityMeasure (P n)› 1
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [← hlaw 1 0]
    exact Measure.isProbabilityMeasure_map (μ := P 1) (hX 1 0).aemeasurable
  -- an offending cell `j₀` and the positive discrepancy `d = |p j₀ − π j₀|`
  obtain ⟨j₀, hj₀⟩ := hne
  set d : ℝ := |p j₀ - π j₀| with hd_def
  have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hj₀)
  have hπj₀ : 0 < π j₀ := hπpos j₀
  -- the canonical i.i.d. model `(Ω₀, P₀, Z)` with marginal law `μ`
  obtain ⟨Ω₀, mΩ₀, P₀, Z, hZmeas, hZlaw, hZindep, hP₀prob⟩ :=
    ProbabilityTheory.exists_iid ℕ μ
  letI : MeasurableSpace Ω₀ := mΩ₀
  haveI : IsProbabilityMeasure P₀ := hP₀prob
  -- `Qz n` is Pearson's statistic on the canonical sample of size `n`
  set Qz : ℕ → Ω₀ → ℝ := fun n ω => pearsonQ π (fun (i : Fin n) => Z (i : ℕ)) ω with hQz
  -- law transfer: the event probability is the same on `P n` and on the canonical model
  have hmeaseq : ∀ n, (P n) {ω | c < pearsonQ π (X n) ω} = P₀ {ω | c < Qz n ω} := by
    intro n
    have hmap : (P n).map (pearsonQ π (X n)) = P₀.map (Qz n) := by
      rw [map_pearsonQ_eq_tuple (hX n) (hindep n) (hlaw n),
        map_pearsonQ_eq_tuple (μ := μ) (P' := P₀) (fun i => hZmeas (i : ℕ))
          (hZindep.precomp Fin.val_injective) (fun i => (hZlaw (i : ℕ)).map_eq)]
    have e1 : (P n) {ω | c < pearsonQ π (X n) ω}
        = ((P n).map (pearsonQ π (X n))) (Set.Ioi c) := by
      rw [Measure.map_apply (measurable_pearsonQ (hX n)) measurableSet_Ioi]; rfl
    have e2 : P₀ {ω | c < Qz n ω} = (P₀.map (Qz n)) (Set.Ioi c) := by
      rw [Measure.map_apply (measurable_pearsonQ (fun i => hZmeas (i : ℕ)))
        measurableSet_Ioi]; rfl
    rw [e1, e2, hmap]
  simp_rw [hmeaseq]
  -- the indicator Bernoulli variables `W i = 1[Z i = j₀]` and the LLN for the cell frequency
  set φ : Fin (k + 1) → ℝ := fun x => if x = j₀ then (1 : ℝ) else 0 with hφ
  have hφmeas : Measurable φ := measurable_of_finite φ
  set W : ℕ → Ω₀ → ℝ := fun i ω => φ (Z i ω) with hW
  have hWmeas : ∀ i, Measurable (W i) := fun i => hφmeas.comp (hZmeas i)
  have hWbd : ∀ i ω, ‖W i ω‖ ≤ 1 := by
    intro i ω; simp only [hW, hφ, Real.norm_eq_abs]
    by_cases h : Z i ω = j₀ <;> simp [h]
  have hWint : Integrable (W 0) P₀ :=
    (integrable_const (1 : ℝ)).mono' (hWmeas 0).aestronglyMeasurable
      (Filter.Eventually.of_forall (hWbd 0))
  have hWindep : Pairwise (fun i j => IndepFun (W i) (W j) P₀) := fun i j hij =>
    (hZindep.indepFun hij).comp hφmeas hφmeas
  have hWident : ∀ i, IdentDistrib (W i) (W 0) P₀ P₀ := fun i =>
    (show IdentDistrib (Z i) (Z 0) P₀ P₀ from
      ⟨(hZmeas i).aemeasurable, (hZmeas 0).aemeasurable,
        (hZlaw i).map_eq.trans (hZlaw 0).map_eq.symm⟩).comp hφmeas
  have hEW : P₀[W 0] = p j₀ := by
    rw [show (fun ω => W 0 ω) = fun ω => φ (Z 0 ω) from rfl,
      ← integral_map (hZmeas 0).aemeasurable hφmeas.aestronglyMeasurable, (hZlaw 0).map_eq,
      integral_fintype (f := φ) Integrable.of_finite]
    simp only [MeasureTheory.Measure.real, hcell, hφ, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ j₀ (fun x => p x)]
    simp
  have hLLN := ProbabilityTheory.strong_law_ae W hWint hWindep hWident
  rw [hEW] at hLLN
  -- convert the canonical average into the cell frequency `Ȳ_n = Yⱼ₀ / n`
  have hcardeq : ∀ (n : ℕ) (ω : Ω₀),
      ((Finset.univ.filter fun (i : Fin n) => Z (i : ℕ) ω = j₀).card : ℝ)
        = ∑ i ∈ Finset.range n, W i ω := by
    intro n ω
    rw [Finset.card_filter, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => W i ω) n]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hW, hφ]
    by_cases h : Z (i : ℕ) ω = j₀ <;> simp [h]
  have hYbar : ∀ᵐ ω ∂P₀, Tendsto
      (fun n => ((Finset.univ.filter fun (i : Fin n) => Z (i : ℕ) ω = j₀).card : ℝ) / n)
      atTop (nhds (p j₀)) := by
    filter_upwards [hLLN] with ω hω
    refine hω.congr (fun n => ?_)
    rw [hcardeq n ω, smul_eq_mul, div_eq_inv_mul]
  -- for a.e. `ω`, `c < Qz n ω` for all large `n`
  have hev : ∀ᵐ ω ∂P₀, ∀ᶠ n in atTop, c < Qz n ω := by
    filter_upwards [hYbar] with ω hω
    set K : ℝ := (d / 2) ^ 2 / π j₀ with hK_def
    have hK : 0 < K := by rw [hK_def]; positivity
    have h1 : ∀ᶠ n in atTop,
        |((Finset.univ.filter fun (i : Fin n) => Z (i : ℕ) ω = j₀).card : ℝ) / n - p j₀|
          < d / 2 := by
      have := (Metric.tendsto_atTop.mp hω) (d / 2) (by positivity)
      obtain ⟨N, hN⟩ := this
      exact Filter.eventually_atTop.mpr ⟨N, fun n hn => by
        have := hN n hn; rwa [Real.dist_eq] at this⟩
    have h2 : ∀ᶠ n : ℕ in atTop, c < (n : ℝ) * K := by
      have htend : Tendsto (fun n : ℕ => (n : ℝ) * K) atTop atTop :=
        Filter.Tendsto.atTop_mul_const hK (tendsto_natCast_atTop_atTop (R := ℝ))
      exact htend.eventually_gt_atTop c
    filter_upwards [h1, h2, Filter.eventually_gt_atTop 0] with n hn1 hn2 hn0
    set Y : ℝ := ((Finset.univ.filter fun (i : Fin n) => Z (i : ℕ) ω = j₀).card : ℝ) with hY
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    -- the frequency is `> d/2` away from `π j₀`
    have hfar : d / 2 < |Y / n - π j₀| := by
      have htri : d ≤ |Y / n - p j₀| + |Y / n - π j₀| := by
        calc d = |p j₀ - π j₀| := hd_def
        _ = |(p j₀ - Y / n) + (Y / n - π j₀)| := by ring_nf
        _ ≤ |p j₀ - Y / n| + |Y / n - π j₀| := abs_add_le _ _
        _ = |Y / n - p j₀| + |Y / n - π j₀| := by rw [abs_sub_comm (p j₀)]
      linarith [hn1]
    have hsq : (d / 2) ^ 2 ≤ (Y / n - π j₀) ^ 2 := by
      rw [← sq_abs (Y / n - π j₀)]
      exact pow_le_pow_left₀ (by positivity) hfar.le 2
    -- the single-cell lower bound and the arithmetic
    have hterm : c < (Y - (n : ℝ) * π j₀) ^ 2 / ((n : ℝ) * π j₀) := by
      have hEq : (Y - (n : ℝ) * π j₀) ^ 2 / ((n : ℝ) * π j₀)
          = (n : ℝ) * ((Y / n - π j₀) ^ 2 / π j₀) := by
        rw [hY]; field_simp
      rw [hEq]
      have hb : K ≤ (Y / n - π j₀) ^ 2 / π j₀ := by
        rw [hK_def]; exact div_le_div_of_nonneg_right hsq hπj₀.le
      have hmono : (n : ℝ) * K ≤ (n : ℝ) * ((Y / n - π j₀) ^ 2 / π j₀) :=
        mul_le_mul_of_nonneg_left hb hn0'.le
      linarith [hn2]
    have hle : (Y - (n : ℝ) * π j₀) ^ 2 / ((n : ℝ) * π j₀) ≤ Qz n ω := by
      rw [hQz]
      exact Finset.single_le_sum
        (f := fun j => (((multinomialCount (fun (i : Fin n) => Z (i : ℕ)) j ω : ℝ))
            - (n : ℝ) * π j) ^ 2 / ((n : ℝ) * π j))
        (fun j _ => div_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg n) (hπpos j).le))
        (Finset.mem_univ j₀)
    linarith [hterm, hle]
  -- bounded (dominated) convergence of the indicators of `{c < Qz n}`
  have hfmeas : ∀ n, MeasurableSet {ω | c < Qz n ω} := fun n =>
    measurableSet_lt measurable_const (measurable_pearsonQ (fun i => hZmeas (i : ℕ)))
  have hlim : ∀ᵐ ω ∂P₀,
      Tendsto (fun n => Set.indicator {ω | c < Qz n ω} (1 : Ω₀ → ℝ) ω) atTop (nhds 1) := by
    filter_upwards [hev] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hω] with n hn
    rw [Set.indicator_of_mem (show ω ∈ {ω | c < Qz n ω} from hn)]; rfl
  have hdom := tendsto_integral_of_dominated_convergence
    (F := fun n => Set.indicator {ω | c < Qz n ω} (1 : Ω₀ → ℝ)) (f := fun _ => (1 : ℝ))
    (bound := fun _ : Ω₀ => (1 : ℝ))
    (fun n => (measurable_one.indicator (hfmeas n)).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]
      by_cases h : ω ∈ {ω | c < Qz n ω} <;> simp [Set.indicator, h]))
    hlim
  simp_rw [integral_indicator_one (hfmeas _)] at hdom
  simpa [MeasureTheory.Measure.real] using hdom

/-! ### Strict comparisons for the noncentral chi-squared tail

The nondegenerate-power theorem below needs three facts about `noncentralChiSquared` that are
finer than the (non-strict) shrink monotonicity `noncentralChiSquared_tail_mono` of the sibling
brick `ForMathlib/NoncentralChiSquared.lean`: at a positive threshold a positive noncentrality
**strictly** increases the upper tail, that tail is **strictly** below one, and the law carries
no atom at the threshold.

All three are proved in the product ("Pi") picture: the standard Gaussian on `Fin k → ℝ` is
`volume.withDensity ρ` with `ρ x = ∏ᵢ φ(xᵢ)`
(`AsymptoticStatistics.pi_gaussianReal_eq_withDensity`), and `map_pi_eq_stdGaussian` transports
that to `EuclideanSpace ℝ (Fin k)`, where `noncentralChiSquared k l` lives as the law of
`‖μ + ·‖²`.

The strict inequality is **not** an Anderson/Prékopa–Leindler statement — those give only the
non-strict comparison. It comes from the reflection `σ` of the first coordinate across the
perpendicular bisector of the two ball centres, `σ u = (−a − u₀, u₁, …, u_{k−1})`. That map is
Lebesgue-measure preserving, is an involution, and exchanges the two balls
`A = {∑ᵢ (mᵢ + uᵢ)² ≤ t}` and `B = {∑ᵢ uᵢ² ≤ t}`; hence it exchanges the two crescents `A \ B`
and `B \ A`. On `A \ B` one has `∑ᵢ (σu)ᵢ² = ∑ᵢ (mᵢ + uᵢ)² ≤ t < ∑ᵢ uᵢ²`, so the Gaussian
density is *pointwise strictly larger* at `σ u` than at `u`; integrating over the crescent —
which contains a nonempty open set, hence has positive Lebesgue measure — gives `ν A < ν B`,
i.e. a strictly larger upper tail. -/

section StrictNoncentralTail

open scoped NNReal

/-- The product standard-Gaussian density on `Fin k → ℝ`. -/
private noncomputable def piGaussDensity (k : ℕ) : (Fin k → ℝ) → ℝ≥0∞ :=
  fun x => ∏ i, gaussianPDF 0 1 (x i)

private lemma measurable_piGaussDensity (k : ℕ) : Measurable (piGaussDensity k) :=
  Finset.measurable_prod _ fun i _ => (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)

/-- Closed form of the product density: a positive constant times `exp(−‖x‖²/2)`. -/
private lemma piGaussDensity_eq {k : ℕ} (x : Fin k → ℝ) :
    piGaussDensity k x
      = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ k
          * Real.exp (-(∑ i, x i ^ 2) / 2)) := by
  simp only [piGaussDensity, gaussianPDF_def]
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _]
  congr 1
  have hexp : ∏ i : Fin k, Real.exp (-x i ^ 2 / 2) = Real.exp (-(∑ i, x i ^ 2) / 2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_div]
    congr 1
    simp
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hexp]

private lemma piGaussDensity_pos {k : ℕ} (x : Fin k → ℝ) : 0 < piGaussDensity k x := by
  rw [piGaussDensity_eq]
  exact ENNReal.ofReal_pos.mpr (by positivity)

/-- The density is strictly larger at the point of smaller squared norm. -/
private lemma piGaussDensity_lt {k : ℕ} {x y : Fin k → ℝ}
    (h : ∑ i, y i ^ 2 < ∑ i, x i ^ 2) : piGaussDensity k x < piGaussDensity k y := by
  rw [piGaussDensity_eq, piGaussDensity_eq]
  refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr ?_
  have hc : (0 : ℝ) < (Real.sqrt (2 * Real.pi))⁻¹ ^ k := by positivity
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith)) hc

/-- The closed shifted "ball" `{u : ∑ᵢ (mᵢ + uᵢ)² ≤ t}` in the product picture. -/
private def piBall (k : ℕ) (m : Fin k → ℝ) (t : ℝ) : Set (Fin k → ℝ) :=
  {u | ∑ i, (m i + u i) ^ 2 ≤ t}

private lemma measurableSet_piBall {k : ℕ} (m : Fin k → ℝ) (t : ℝ) :
    MeasurableSet (piBall k m t) :=
  measurableSet_le (Finset.measurable_sum _ fun i _ => by fun_prop) measurable_const

private lemma piGauss_apply {k : ℕ} {S : Set (Fin k → ℝ)} (hS : MeasurableSet S) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1) S
      = ∫⁻ x in S, piGaussDensity k x ∂(volume : Measure (Fin k → ℝ)) := by
  rw [AsymptoticStatistics.pi_gaussianReal_eq_withDensity, withDensity_apply _ hS]
  rfl

/-- A set of positive Lebesgue measure has positive product-Gaussian mass. -/
private lemma piGauss_pos {k : ℕ} {S : Set (Fin k → ℝ)} (hS : MeasurableSet S)
    (hvol : (volume : Measure (Fin k → ℝ)) S ≠ 0) :
    0 < (Measure.pi fun _ : Fin k => gaussianReal 0 1) S := by
  rw [piGauss_apply hS, pos_iff_ne_zero]
  intro hzero
  rw [lintegral_eq_zero_iff (measurable_piGaussDensity k)] at hzero
  have hfalse : ∀ᵐ x ∂((volume : Measure (Fin k → ℝ)).restrict S), False := by
    filter_upwards [hzero] with x hx
    exact (piGaussDensity_pos x).ne' hx
  have hbot := ae_eq_bot.mp (eventually_false_iff_eq_bot.mp hfalse)
  rw [Measure.restrict_eq_zero] at hbot
  exact hvol hbot

/-- **The strict crescent comparison.** For a positive threshold and a positive shift along
the first axis, the shifted product-Gaussian ball has *strictly* smaller mass. -/
private lemma piGauss_piBall_lt {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 < a) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1)
        (piBall k (fun i => if (i : ℕ) = 0 then a else 0) t)
      < (Measure.pi fun _ : Fin k => gaussianReal 0 1) (piBall k (fun _ => 0) t) := by
  classical
  set ν := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hν
  set i₀ : Fin k := ⟨0, hk⟩ with hi₀
  set m : Fin k → ℝ := fun i => if (i : ℕ) = 0 then a else 0 with hm
  have hmi₀ : m i₀ = a := by simp [hm, hi₀]
  have hmne : ∀ i : Fin k, i ≠ i₀ → m i = 0 := by
    intro i hi
    have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    simp [hm, hi']
  set A : Set (Fin k → ℝ) := piBall k m t with hA
  set B : Set (Fin k → ℝ) := piBall k (fun _ : Fin k => (0 : ℝ)) t with hB
  have hAmem : ∀ u : Fin k → ℝ, u ∈ A ↔ ∑ i, (m i + u i) ^ 2 ≤ t := fun u => Iff.rfl
  have hBmem : ∀ u : Fin k → ℝ, u ∈ B ↔ ∑ i, u i ^ 2 ≤ t := by
    intro u
    simp only [hB, piBall, Set.mem_setOf_eq, zero_add]
  -- the reflection of the first coordinate across the perpendicular bisector
  set σ : (Fin k → ℝ) → (Fin k → ℝ) :=
    fun u i => if i = i₀ then -a - u i else u i with hσ
  have hσapp : ∀ (u : Fin k → ℝ) (i : Fin k), σ u i = if i = i₀ then -a - u i else u i :=
    fun _ _ => rfl
  have hq₁ : ∀ u : Fin k → ℝ, ∑ i, σ u i ^ 2 = ∑ i, (m i + u i) ^ 2 := by
    intro u
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = i₀
    · subst hi; rw [hσapp, if_pos rfl, hmi₀]; ring
    · rw [hσapp, if_neg hi, hmne i hi, zero_add]
  have hq₂ : ∀ u : Fin k → ℝ, ∑ i, (m i + σ u i) ^ 2 = ∑ i, u i ^ 2 := by
    intro u
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = i₀
    · subst hi; rw [hσapp, if_pos rfl, hmi₀]; ring
    · rw [hσapp, if_neg hi, hmne i hi, zero_add]
  have hpreB : σ ⁻¹' B = A := by
    ext u; simp only [Set.mem_preimage, hBmem, hAmem, hq₁]
  have hpreA : σ ⁻¹' A = B := by
    ext u; simp only [Set.mem_preimage, hAmem, hBmem, hq₂]
  -- `σ` preserves Lebesgue measure
  have hσmp : MeasurePreserving σ (volume : Measure (Fin k → ℝ)) volume := by
    have h1 : MeasurePreserving (fun x : ℝ => -a - x) (volume : Measure ℝ) volume :=
      Measure.measurePreserving_sub_left volume (-a)
    have hf : ∀ i : Fin k, MeasurePreserving
        (fun x : ℝ => if i = i₀ then -a - x else x) (volume : Measure ℝ) volume := by
      intro i
      by_cases hi : i = i₀
      · simpa [hi] using h1
      · simpa [hi] using! (MeasurePreserving.id (volume : Measure ℝ))
    have hpi := MeasureTheory.measurePreserving_pi (fun _ : Fin k => (volume : Measure ℝ))
      (fun _ : Fin k => (volume : Measure ℝ)) hf
    rw [← volume_pi] at hpi
    exact hpi
  have hAmeas : MeasurableSet A := measurableSet_piBall m t
  have hBmeas : MeasurableSet B := measurableSet_piBall _ t
  have hSmeas : MeasurableSet (A \ B) := hAmeas.diff hBmeas
  -- the crescent `A \ B` has positive Lebesgue measure
  have hvolS : (volume : Measure (Fin k → ℝ)) (A \ B) ≠ 0 := by
    set r : ℝ := Real.sqrt t with hr
    have hrpos : 0 < r := Real.sqrt_pos.mpr ht
    have hr2 : r ^ 2 = t := Real.sq_sqrt ht.le
    set s : ℝ := r - min a r / 2 with hs
    have hminpos : 0 < min a r := lt_min ha hrpos
    have hslt : s < r := by rw [hs]; linarith
    have hs0 : 0 ≤ s := by
      have hmr : min a r ≤ r := min_le_right _ _
      rw [hs]; linarith
    have hsr : r < a + s := by
      have hma : min a r ≤ a := min_le_left _ _
      rw [hs]; linarith
    set u₀ : Fin k → ℝ := fun i => if i = i₀ then -(a + s) else 0 with hu₀
    have hsum₁ : ∑ i, (m i + u₀ i) ^ 2 = s ^ 2 := by
      rw [Finset.sum_eq_single i₀]
      · simp only [hu₀, if_pos rfl, hmi₀]; ring
      · intro i _ hi; simp only [hu₀, if_neg hi, hmne i hi, add_zero]; ring
      · intro h; exact absurd (Finset.mem_univ i₀) h
    have hsum₂ : ∑ i, u₀ i ^ 2 = (a + s) ^ 2 := by
      rw [Finset.sum_eq_single i₀]
      · simp only [hu₀, if_pos rfl]; ring
      · intro i _ hi; simp only [hu₀, if_neg hi]; ring
      · intro h; exact absurd (Finset.mem_univ i₀) h
    have hcont₁ : Continuous fun u : Fin k → ℝ => ∑ i, (m i + u i) ^ 2 := by fun_prop
    have hcont₂ : Continuous fun u : Fin k → ℝ => ∑ i, u i ^ 2 := by fun_prop
    set U : Set (Fin k → ℝ) :=
      {u | ∑ i, (m i + u i) ^ 2 < t} ∩ {u | t < ∑ i, u i ^ 2} with hU
    have hUopen : IsOpen U :=
      (isOpen_lt hcont₁ continuous_const).inter (isOpen_lt continuous_const hcont₂)
    have hu₀U : u₀ ∈ U := by
      refine ⟨?_, ?_⟩
      · change ∑ i, (m i + u₀ i) ^ 2 < t
        rw [hsum₁, ← hr2]
        nlinarith
      · change t < ∑ i, u₀ i ^ 2
        rw [hsum₂, ← hr2]
        nlinarith
    have hUsub : U ⊆ A \ B := by
      rintro u ⟨h1, h2⟩
      have h1' : ∑ i, (m i + u i) ^ 2 < t := h1
      have h2' : t < ∑ i, u i ^ 2 := h2
      exact ⟨(hAmem u).mpr h1'.le, fun hu => absurd ((hBmem u).mp hu) (not_le.mpr h2')⟩
    have hpos := hUopen.measure_pos (volume : Measure (Fin k → ℝ)) ⟨u₀, hu₀U⟩
    exact (lt_of_lt_of_le hpos (measure_mono hUsub)).ne'
  -- the two crescents, transported to one another by `σ`
  have hcrescA : ν (A \ B) = ∫⁻ x in A \ B, piGaussDensity k x ∂(volume : Measure (Fin k → ℝ)) :=
    piGauss_apply hSmeas
  have hcrescB : ν (B \ A)
      = ∫⁻ x in A \ B, piGaussDensity k (σ x) ∂(volume : Measure (Fin k → ℝ)) := by
    have hBA : MeasurableSet (B \ A) := hBmeas.diff hAmeas
    have hind : Measurable ((B \ A).indicator (piGaussDensity k)) :=
      (measurable_piGaussDensity k).indicator hBA
    have hcomp := hσmp.lintegral_comp hind
    have hpre : σ ⁻¹' (B \ A) = A \ B := by
      rw [Set.preimage_diff, hpreB, hpreA]
    rw [piGauss_apply hBA, ← lintegral_indicator hBA, ← hcomp, ← lintegral_indicator hSmeas]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A \ B
    · have hx' : σ x ∈ B \ A := by rwa [← hpre, Set.mem_preimage] at hx
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
    · have hx' : σ x ∉ B \ A := by
        intro hcon; exact hx (by rwa [← hpre, Set.mem_preimage])
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]
  have hstrict : (∫⁻ x in A \ B, piGaussDensity k x ∂(volume : Measure (Fin k → ℝ)))
      < ∫⁻ x in A \ B, piGaussDensity k (σ x) ∂(volume : Measure (Fin k → ℝ)) := by
    refine setLIntegral_strict_mono hSmeas hvolS
      ((measurable_piGaussDensity k).comp hσmp.measurable) ?_ ?_
    · rw [← hcrescA]; exact measure_ne_top _ _
    · filter_upwards with x hx
      refine piGaussDensity_lt ?_
      have h1 : ∑ i, σ x i ^ 2 ≤ t := by rw [hq₁]; exact (hAmem x).mp hx.1
      have h2 : t < ∑ i, x i ^ 2 := not_le.mp fun hcon => hx.2 ((hBmem x).mpr hcon)
      linarith
  -- assemble
  have hsplitA : ν (A ∩ B) + ν (A \ B) = ν A := measure_inter_add_diff A hBmeas
  have hsplitB : ν (B ∩ A) + ν (B \ A) = ν B := measure_inter_add_diff B hAmeas
  rw [Set.inter_comm B A] at hsplitB
  rw [← hsplitA, ← hsplitB]
  refine ENNReal.add_lt_add_left (measure_ne_top ν (A ∩ B)) ?_
  rw [hcrescA, hcrescB]
  exact hstrict

/-- Every shifted ball of positive radius has positive product-Gaussian mass. -/
private lemma piGauss_piBall_pos {k : ℕ} (m : Fin k → ℝ) {t : ℝ} (ht : 0 < t) :
    0 < (Measure.pi fun _ : Fin k => gaussianReal 0 1) (piBall k m t) := by
  refine piGauss_pos (measurableSet_piBall m t) ?_
  have hcont : Continuous fun u : Fin k → ℝ => ∑ i, (m i + u i) ^ 2 := by fun_prop
  have hUopen : IsOpen {u : Fin k → ℝ | ∑ i, (m i + u i) ^ 2 < t} :=
    isOpen_lt hcont continuous_const
  have hmem : (-m) ∈ {u : Fin k → ℝ | ∑ i, (m i + u i) ^ 2 < t} := by
    change ∑ i, (m i + (-m) i) ^ 2 < t
    have hz : ∑ i, (m i + (-m) i) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      simp
    rw [hz]; exact ht
  have hsub : {u : Fin k → ℝ | ∑ i, (m i + u i) ^ 2 < t} ⊆ piBall k m t := by
    intro u hu
    have hu' : ∑ i, (m i + u i) ^ 2 < t := hu
    exact hu'.le
  have hpos := hUopen.measure_pos (volume : Measure (Fin k → ℝ)) ⟨-m, hmem⟩
  exact (lt_of_lt_of_le hpos (measure_mono hsub)).ne'

private lemma piGauss_singleton_zero {k : ℕ} (hk : 0 < k) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1) {(0 : Fin k → ℝ)} = 0 := by
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hset : ({0} : Set (Fin k → ℝ)) = Set.pi Set.univ fun _ : Fin k => ({0} : Set ℝ) := by
    ext u; simp [funext_iff]
  rw [hset, Measure.pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ (⟨0, hk⟩ : Fin k)) ?_
  simp

/-! #### Transport from the product picture to `noncentralChiSquared` -/

private lemma measurable_toLp_pi (k : ℕ) :
    Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) := by
  have h : (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k))
      = ⇑(WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm := rfl
  rw [h]
  have hcont : Continuous ⇑(WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm :=
    (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.toLinearMap.continuous_of_finiteDimensional
  exact hcont.measurable

private lemma stdGaussian_ball_eq {k : ℕ} (m : Fin k → ℝ) (t : ℝ) :
    stdGaussian (EuclideanSpace ℝ (Fin k))
        {x | ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin k)) + x‖ ^ 2 ≤ t}
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1) (piBall k m t) := by
  have hset : MeasurableSet {x : EuclideanSpace ℝ (Fin k) |
      ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin k)) + x‖ ^ 2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (measurable_toLp_pi k) hset]
  congr 1
  ext u
  simp only [Set.mem_preimage, Set.mem_setOf_eq, piBall,
    EuclideanSpace.real_norm_sq_eq]
  rfl

private lemma stdGaussian_sphere_eq {k : ℕ} (m : Fin k → ℝ) (t : ℝ) :
    stdGaussian (EuclideanSpace ℝ (Fin k))
        {x | ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin k)) + x‖ ^ 2 = t}
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1)
          {u : Fin k → ℝ | ∑ i, (m i + u i) ^ 2 = t} := by
  have hset : MeasurableSet {x : EuclideanSpace ℝ (Fin k) |
      ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin k)) + x‖ ^ 2 = t} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (measurable_toLp_pi k) hset]
  congr 1
  ext u
  simp only [Set.mem_preimage, Set.mem_setOf_eq, EuclideanSpace.real_norm_sq_eq]
  rfl

private lemma multivariateGaussian_one_eq_map_add' {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) :
    multivariateGaussian v (1 : Matrix (Fin k) (Fin k) ℝ)
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => v + x) := by
  rw [multivariateGaussian]
  simp only [CFC.sqrt_one, map_one, ContinuousLinearMap.one_apply]

/-- The `Iic`-mass of `noncentralChiSquared` in the product picture. -/
private lemma noncentralChiSquared_Iic_eq {k : ℕ} (l : ℝ≥0) (t : ℝ) :
    noncentralChiSquared k l (Set.Iic t)
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1)
          (piBall k (fun i => if (i : ℕ) = 0 then Real.sqrt (l : ℝ) else 0) t) := by
  rw [noncentralChiSquared, multivariateGaussian_one_eq_map_add',
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) measurableSet_Iic]
  exact stdGaussian_ball_eq _ t

/-- **No atom at a positive threshold.** The `{t}`-mass of `noncentralChiSquared` is the
standard-Gaussian mass of a Euclidean sphere of positive radius, hence zero. -/
private lemma noncentralChiSquared_singleton {k : ℕ} {t : ℝ} (ht : 0 < t) (l : ℝ≥0) :
    noncentralChiSquared k l {t} = 0 := by
  set m : Fin k → ℝ := fun i => if (i : ℕ) = 0 then Real.sqrt (l : ℝ) else 0 with hm
  have hstep : noncentralChiSquared k l {t}
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1)
          {u : Fin k → ℝ | ∑ i, (m i + u i) ^ 2 = t} := by
    rw [noncentralChiSquared, multivariateGaussian_one_eq_map_add',
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
    exact stdGaussian_sphere_eq _ t
  rw [hstep]
  -- the set is Lebesgue-null: it is the preimage of a Euclidean sphere of radius `√t > 0`
  have hmeas : MeasurableSet {u : Fin k → ℝ | ∑ i, (m i + u i) ^ 2 = t} :=
    measurableSet_eq_fun (Finset.measurable_sum _ fun i _ => by fun_prop) measurable_const
  have hvol : (volume : Measure (Fin k → ℝ)) {u : Fin k → ℝ | ∑ i, (m i + u i) ^ 2 = t} = 0 := by
    have hpre : {u : Fin k → ℝ | ∑ i, (m i + u i) ^ 2 = t}
        = (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) ⁻¹'
            (Metric.sphere (-(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin k))) (Real.sqrt t)) := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_sphere, dist_eq_norm,
        sub_neg_eq_add]
      constructor
      · intro h
        have hnorm : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin k))
            + WithLp.toLp 2 m‖ ^ 2 = t := by
          rw [EuclideanSpace.real_norm_sq_eq]
          rw [← h]
          exact Finset.sum_congr rfl fun i _ => by simp [add_comm]
        rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
      · intro h
        have hnorm : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin k))
            + WithLp.toLp 2 m‖ ^ 2 = t := by
          rw [h, Real.sq_sqrt ht.le]
        rw [EuclideanSpace.real_norm_sq_eq] at hnorm
        rw [← hnorm]
        exact Finset.sum_congr rfl fun i _ => by simp [add_comm]
    rw [hpre, (PiLp.volume_preserving_toLp (Fin k)).measure_preimage
      (Metric.isClosed_sphere.measurableSet.nullMeasurableSet)]
    exact Measure.addHaar_sphere_of_ne_zero _ _ (Real.sqrt_ne_zero'.mpr ht)
  calc (Measure.pi fun _ : Fin k => gaussianReal 0 1)
        {u : Fin k → ℝ | ∑ i, (m i + u i) ^ 2 = t}
      = ∫⁻ x in {u : Fin k → ℝ | ∑ i, (m i + u i) ^ 2 = t},
          piGaussDensity k x ∂(volume : Measure (Fin k → ℝ)) := piGauss_apply hmeas
    _ = 0 := by
        rw [Measure.restrict_eq_zero.mpr hvol, lintegral_zero_measure]

/-- The upper tail as one minus the lower mass. -/
private lemma noncentralChiSquared_Ioi_toReal {k : ℕ} (l : ℝ≥0) (t : ℝ) :
    (noncentralChiSquared k l (Set.Ioi t)).toReal
      = 1 - (noncentralChiSquared k l (Set.Iic t)).toReal := by
  have hc : Set.Ioi t = (Set.Iic t)ᶜ := by ext x; simp
  rw [hc, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

/-- **Strictly increasing tail.** At a positive threshold, a positive noncentrality strictly
increases the upper tail of the noncentral chi-squared law. -/
private lemma noncentralChiSquared_tail_lt {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    {l : ℝ≥0} (hl : 0 < l) :
    (noncentralChiSquared k 0 (Set.Ioi t)).toReal
      < (noncentralChiSquared k l (Set.Ioi t)).toReal := by
  rw [noncentralChiSquared_Ioi_toReal, noncentralChiSquared_Ioi_toReal]
  have hlt : noncentralChiSquared k l (Set.Iic t) < noncentralChiSquared k 0 (Set.Iic t) := by
    rw [noncentralChiSquared_Iic_eq, noncentralChiSquared_Iic_eq]
    have hzero : (fun i : Fin k => if (i : ℕ) = 0 then Real.sqrt ((0 : ℝ≥0) : ℝ) else 0)
        = fun _ : Fin k => (0 : ℝ) := by
      funext i; simp
    rw [hzero]
    exact piGauss_piBall_lt hk ht (Real.sqrt_pos.mpr (by exact_mod_cast hl))
  have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr hlt
  linarith

/-- **The tail is strictly below one.** A positive threshold leaves positive mass below it. -/
private lemma noncentralChiSquared_tail_lt_one {k : ℕ} {t : ℝ} (ht : 0 < t) (l : ℝ≥0) :
    (noncentralChiSquared k l (Set.Ioi t)).toReal < 1 := by
  rw [noncentralChiSquared_Ioi_toReal]
  have hpos : 0 < (noncentralChiSquared k l (Set.Iic t)).toReal := by
    rw [noncentralChiSquared_Iic_eq]
    exact ENNReal.toReal_pos (piGauss_piBall_pos _ ht).ne' (measure_ne_top _ _)
  linarith

/-- **A nondegenerate level forces a positive critical value.** If `χ²_k(c, ∞) = α < 1` with
`k ≥ 1` then `c > 0`: below zero the chi-squared law puts no mass, so the tail would be one. -/
private lemma pos_of_chiSquared_tail_lt_one {k : ℕ} (hk : 0 < k) {α c : ℝ} (hα1 : α < 1)
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α) : 0 < c := by
  by_contra hcon
  rw [not_lt] at hcon
  rw [← noncentralChiSquared_zero hk] at hc
  have hIic : noncentralChiSquared k 0 (Set.Iic c) = 0 := by
    rw [noncentralChiSquared_Iic_eq]
    have hzero : (fun i : Fin k => if (i : ℕ) = 0 then Real.sqrt ((0 : ℝ≥0) : ℝ) else 0)
        = fun _ : Fin k => (0 : ℝ) := by
      funext i; simp
    rw [hzero]
    refine le_antisymm ?_ (zero_le)
    refine le_trans (measure_mono ?_) (le_of_eq (piGauss_singleton_zero hk))
    intro u hu
    have hu' : ∑ i, u i ^ 2 ≤ c := by
      simpa [piBall, zero_add] using hu
    have hzero' : ∀ i : Fin k, u i = 0 := by
      intro i
      have hle : u i ^ 2 ≤ 0 :=
        le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i))
          (le_trans hu' hcon)
      have := le_antisymm hle (sq_nonneg (u i))
      exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this
    exact funext hzero'
  have htail : (noncentralChiSquared k 0 (Set.Ioi c)).toReal = 1 := by
    rw [noncentralChiSquared_Ioi_toReal, hIic, ENNReal.toReal_zero, sub_zero]
  rw [hc] at htail
  rcases le_or_gt α 0 with h | h
  · rw [ENNReal.ofReal_of_nonpos h, ENNReal.toReal_zero] at htail
    norm_num at htail
  · rw [ENNReal.toReal_ofReal h.le] at htail
    linarith

end StrictNoncentralTail

/-- **Nondegenerate local power.** Against the local alternatives of
`pearsonQ_weakConverges_noncentral` with not all `hⱼ` equal to zero, the power of the
chi-squared test tends to a limit strictly greater than `α` and strictly less than one,
namely `P{χ²_k(λ) > c}` with `λ = ∑ⱼ hⱼ²/πⱼ > 0`. -/
theorem pearsonQ_local_power_nondegenerate {k : ℕ} {α c : ℝ} {π h : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : ℕ → Measure (Fin (k + 1))}
    -- USER-INPUT: at least one degree of freedom
    (hk : 0 < k)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the null cell probabilities are an interior point of the simplex
    (hπpos : ∀ j, 0 < π j)
    -- USER-INPUT: the null cell probabilities sum to one
    (hπsum : ∑ j, π j = 1)
    -- USER-INPUT: the local shifts sum to zero
    (hhsum : ∑ j, h j = 0)
    -- USER-INPUT: the local alternative is nondegenerate: not all shifts vanish
    (hhne : ∃ j, h j ≠ 0)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the trials are i.i.d.; Pearson 1900
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at stage `n` every trial has the stage-`n` law `μ n`
    (hlaw : ∀ n, ∀ i, Measure.map (X n i) (P n) = μ n)
    -- USER-INPUT: the local alternative cell probabilities are `πⱼ + hⱼ n^{-1/2}`
    (hcell : ∀ n, ∀ j, ((μ n) {j}).toReal = π j + h j / Real.sqrt (n : ℝ)) :
    Tendsto (fun n => ((P n) {ω | c < pearsonQ π (X n) ω}).toReal) atTop
        (nhds ((noncentralChiSquared k (multinomialNoncentrality π h).toNNReal)
          (Set.Ioi c)).toReal)
      ∧ α < ((noncentralChiSquared k (multinomialNoncentrality π h).toNNReal)
          (Set.Ioi c)).toReal
      ∧ ((noncentralChiSquared k (multinomialNoncentrality π h).toNNReal)
          (Set.Ioi c)).toReal < 1 := by
  classical
  -- a nondegenerate level forces a positive critical value
  have hcpos : 0 < c := pos_of_chiSquared_tail_lt_one hk hα1 hc
  -- the noncentrality is positive
  have hlampos : 0 < multinomialNoncentrality π h := by
    obtain ⟨j, hj⟩ := hhne
    rw [multinomialNoncentrality]
    refine Finset.sum_pos' (fun i _ => div_nonneg (sq_nonneg _) (hπpos i).le)
      ⟨j, Finset.mem_univ j, div_pos ?_ (hπpos j)⟩
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj))
  have hlamnn : 0 < (multinomialNoncentrality π h).toNNReal := Real.toNNReal_pos.mpr hlampos
  refine ⟨?_, ?_, ?_⟩
  · -- (1) the limiting power, by the constant-threshold portmanteau step
    have hweak := pearsonQ_weakConverges_noncentral hk hπpos hπsum hhsum hX hindep hlaw hcell
    haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (Measure.map (pearsonQ π (X n)) (P n)) :=
      fun n => Measure.isProbabilityMeasure_map (measurable_pearsonQ (hX n)).aemeasurable
    set μs : ℕ → ProbabilityMeasure ℝ :=
      fun n => ⟨Measure.map (pearsonQ π (X n)) (P n), hprob n⟩ with hμs
    set νl : ProbabilityMeasure ℝ :=
      ⟨noncentralChiSquared k (multinomialNoncentrality π h).toNNReal, inferInstance⟩ with hνl
    have hconv : Tendsto μs atTop (𝓝 νl) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f
      simpa only [hμs, hνl, ProbabilityMeasure.coe_mk] using hweak f
    have hfront : (νl : Measure ℝ) (frontier (Set.Ioi c)) = 0 := by
      rw [frontier_Ioi]
      exact noncentralChiSquared_singleton hcpos _
    have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hfront
    have htoreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
    refine htoreal.congr fun n => ?_
    simp only [Function.comp_apply, hμs, ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_pearsonQ (hX n)) measurableSet_Ioi]
    rfl
  · -- (2) the limit exceeds the level, by the strict tail comparison
    have hαeq : α = (noncentralChiSquared k 0 (Set.Ioi c)).toReal := by
      rw [noncentralChiSquared_zero hk, hc, ENNReal.toReal_ofReal hα.le]
    rw [hαeq]
    exact noncentralChiSquared_tail_lt hk hcpos hlamnn
  · -- (3) the limit is below one, since the ball below the threshold has positive mass
    exact noncentralChiSquared_tail_lt_one hcpos _

end StatLean.HypothesisTesting
