module
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Finite-population summaries: total, mean, variance

Design-based inference regards the experimental (or survey) units as a *fixed finite
population* `U` carrying a *deterministic* quantity `y : U → ℝ`; all randomness enters
later, through the randomization or sampling design.  This file records the
deterministic population summaries
$$Y = \sum_{i} y_i, \qquad \bar y = \frac1N \sum_i y_i, \qquad
  S^2_y = \frac{1}{N-1}\sum_i (y_i - \bar y)^2, \qquad N = |U|,$$
and their elementary algebra: centering, the computational form of the sum of squared
deviations, nonnegativity and degeneracy of `S²`, and behaviour under translation and
scaling.

Keeping these summaries deterministic — never entangled with a design — is the load-
bearing convention of the whole `ExperimentalDesign` area: unbiasedness statements
read `pmfExpect D (statistic) = populationMean y` with the right-hand side a pure
function of the data.

## Main results

* `populationTotal`, `populationMean`, `populationVariance` — the summaries.
* `sum_sub_populationMean` — centered values sum to zero.
* `sum_sq_sub_populationMean` — `∑ (yᵢ − ȳ)² = ∑ yᵢ² − N ȳ²`.
* `populationVariance_nonneg`, `populationVariance_eq_zero_iff` — degeneracy.
* `populationMean_add`, `populationMean_smul`, `populationVariance_smul`,
  `populationVariance_add_const` — affine equivariance.

**Reference.** The finite model of experimental data — a fixed set of units, all used,
with fixed unit values — is Mead's "finite model": R. Mead, *The Design of
Experiments*, Cambridge University Press, 1988, §9.4–§9.5 (the finite model and its
contrast with the infinite model).  The `N − 1` normalisation of `S²` is the standard
finite-population variance of survey sampling.  (`Mead §9.4`.)

**Proof formalization notes.**
* Edge behaviour is by Lean's `(0:ℝ)⁻¹ = 0` convention: for `U` empty the mean is `0`;
  for `N ≤ 1` the variance is `0`.  Statements that would be false degenerately carry
  explicit cardinality hypotheses (`Nonempty U`, `2 ≤ Fintype.card U`).
* `populationVariance_eq_zero_iff` requires `2 ≤ N`: for `N ≤ 1` the variance is `0`
  by convention while the right-hand side is vacuously true, so the statement happens
  to hold, but we keep the hypothesis to match the honest mathematical content.
-/

namespace StatLean.ExperimentalDesign

variable {U : Type*} [Fintype U]

/-- The **population total** `Y = ∑ᵢ yᵢ` of a deterministic finite-population quantity
(`Mead §9.4`, the finite model). -/
noncomputable def populationTotal (y : U → ℝ) : ℝ := ∑ i, y i

/-- The **population mean** `ȳ = N⁻¹ ∑ᵢ yᵢ`.  Edge behaviour: `0` for the empty
population (`(0:ℝ)⁻¹ = 0`). -/
noncomputable def populationMean (y : U → ℝ) : ℝ :=
  (Fintype.card U : ℝ)⁻¹ * ∑ i, y i

/-- The **finite-population variance** `S² = (N−1)⁻¹ ∑ᵢ (yᵢ − ȳ)²`, with the survey-
sampling `N − 1` normalisation.  Edge behaviour: `0` when `N ≤ 1`. -/
noncomputable def populationVariance (y : U → ℝ) : ℝ :=
  ((Fintype.card U : ℝ) - 1)⁻¹ * ∑ i, (y i - populationMean y) ^ 2

/-- The population size is a nonzero real when the population is nonempty. -/
private theorem card_ne_zero_real (U : Type*) [Fintype U] [Nonempty U] :
    (Fintype.card U : ℝ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero (α := U)

/-- The total is `N` times the mean (degenerately `0 = 0` for the empty population). -/
theorem populationTotal_eq_card_mul_mean (y : U → ℝ) :
    populationTotal y = (Fintype.card U : ℝ) * populationMean y := by
  rcases isEmpty_or_nonempty U with hU | hU
  · simp [populationTotal, populationMean, Fintype.card_eq_zero]
  · rw [populationMean, populationTotal, ← mul_assoc,
      mul_inv_cancel₀ (card_ne_zero_real U), one_mul]

/-- Centered population values sum to zero. -/
theorem sum_sub_populationMean [Nonempty U] (y : U → ℝ) :
    ∑ i, (y i - populationMean y) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    populationMean, ← mul_assoc, mul_inv_cancel₀ (card_ne_zero_real U), one_mul, sub_self]

/-- The population mean of a constant is that constant. -/
theorem populationMean_const [Nonempty U] (c : ℝ) :
    populationMean (fun _ : U => c) = c := by
  rw [populationMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (card_ne_zero_real U), one_mul]

/-- Additivity of the population mean. -/
theorem populationMean_add (y z : U → ℝ) :
    populationMean (fun i => y i + z i) = populationMean y + populationMean z := by
  rw [populationMean, populationMean, populationMean, Finset.sum_add_distrib, mul_add]

/-- Homogeneity of the population mean. -/
theorem populationMean_smul (c : ℝ) (y : U → ℝ) :
    populationMean (fun i => c * y i) = c * populationMean y := by
  rw [populationMean, populationMean, ← Finset.mul_sum]
  ring

/-- Computational form of the centered sum of squares:
`∑ (yᵢ − ȳ)² = ∑ yᵢ² − N ȳ²`. -/
theorem sum_sq_sub_populationMean [Nonempty U] (y : U → ℝ) :
    ∑ i, (y i - populationMean y) ^ 2
      = ∑ i, y i ^ 2 - (Fintype.card U : ℝ) * populationMean y ^ 2 := by
  have hexp : ∀ i : U, (y i - populationMean y) ^ 2
      = y i ^ 2 + ((-2 * populationMean y) * y i + populationMean y ^ 2) := by
    intro i; ring
  have hsum : ∑ i, y i = (Fintype.card U : ℝ) * populationMean y :=
    populationTotal_eq_card_mul_mean y
  rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The finite-population variance is nonnegative (including the degenerate `N ≤ 1`
cases, where it is `0` by convention). -/
theorem populationVariance_nonneg (y : U → ℝ) : 0 ≤ populationVariance y := by
  rcases isEmpty_or_nonempty U with hU | hU
  · simp [populationVariance]
  · refine mul_nonneg (inv_nonneg.mpr ?_) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have h1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := U)
    linarith

/-- The finite-population variance of a constant vanishes. -/
theorem populationVariance_const (c : ℝ) :
    populationVariance (fun _ : U => c) = 0 := by
  rcases isEmpty_or_nonempty U with hU | hU
  · simp [populationVariance]
  · have hterm : ∀ i ∈ (Finset.univ : Finset U),
        (c - populationMean (fun _ : U => c)) ^ 2 = (0 : ℝ) := by
      intro i _; rw [populationMean_const]; ring
    rw [populationVariance, Finset.sum_congr rfl hterm, Finset.sum_const_zero, mul_zero]

/-- For a population with at least two units, zero variance characterises constancy. -/
theorem populationVariance_eq_zero_iff
    -- LEAN-ONLY: rules out the `N ≤ 1` convention cases; no scope change
    (h2 : 2 ≤ Fintype.card U) (y : U → ℝ) :
    populationVariance y = 0 ↔ ∀ i j, y i = y j := by
  have hne : Nonempty U := Fintype.card_pos_iff.mp (by omega)
  have hNpos : (0 : ℝ) < (Fintype.card U : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast h2
    linarith
  constructor
  · intro h i j
    rw [populationVariance] at h
    have hS : ∑ k, (y k - populationMean y) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left (inv_ne_zero (ne_of_gt hNpos))
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg
      (y k - populationMean y)).mp hS
    have hi : y i = populationMean y :=
      sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (hzero i (Finset.mem_univ i)))
    have hj : y j = populationMean y :=
      sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (hzero j (Finset.mem_univ j)))
    rw [hi, hj]
  · intro h
    have hmean : ∀ i : U, populationMean y = y i := by
      intro i
      rw [populationMean, Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h j i,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (card_ne_zero_real U), one_mul]
    have hterm : ∀ i ∈ (Finset.univ : Finset U), (y i - populationMean y) ^ 2 = (0 : ℝ) := by
      intro i _; rw [hmean i]; ring
    rw [populationVariance, Finset.sum_congr rfl hterm, Finset.sum_const_zero, mul_zero]

/-- Quadratic scaling of the finite-population variance. -/
theorem populationVariance_smul (c : ℝ) (y : U → ℝ) :
    populationVariance (fun i => c * y i) = c ^ 2 * populationVariance y := by
  simp only [populationVariance, populationMean_smul]
  have hterm : ∀ i ∈ (Finset.univ : Finset U), (c * y i - c * populationMean y) ^ 2
      = c ^ 2 * (y i - populationMean y) ^ 2 := fun i _ => by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/-- Translation invariance of the finite-population variance. -/
theorem populationVariance_add_const (y : U → ℝ) (c : ℝ) :
    populationVariance (fun i => y i + c) = populationVariance y := by
  rcases isEmpty_or_nonempty U with hU | hU
  · simp [populationVariance]
  · have hm : populationMean (fun i => y i + c) = populationMean y + c := by
      rw [populationMean_add, populationMean_const]
    have hs : ∑ i, (y i + c - (populationMean y + c)) ^ 2
        = ∑ i, (y i - populationMean y) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by ring
    simp only [populationVariance, hm, hs]

end StatLean.ExperimentalDesign
