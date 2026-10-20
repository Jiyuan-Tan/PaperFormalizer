module
public import StatLean.ExperimentalDesign.SurveySampling.InclusionProbability
public import StatLean.ExperimentalDesign.Core.FinitePopulation

@[expose] public section

/-!
# The Horvitz–Thompson estimator

For a sampling design with inclusion probabilities `πᵢ > 0`, the **Horvitz–Thompson
estimator** of the population total from an observed sample `S` is
$$\widehat Y_{HT}(S) = \sum_{i \in S} \frac{y_i}{\pi_i}.$$
This file proves the two fundamental exact results of design-based estimation:

* **Unbiasedness**: `E_D[Ŷ_HT] = ∑ᵢ yᵢ` whenever every `πᵢ > 0`;
* **Exact design variance**:
  $$\operatorname{Var}_D(\widehat Y_{HT})
    = \sum_{i}\sum_{j} \frac{\pi_{ij} - \pi_i \pi_j}{\pi_i \pi_j}\, y_i y_j,$$
  with the diagonal convention `π_{ii} = πᵢ`.

## Main results

* `horvitzThompson` — the estimator.
* `horvitzThompson_eq_sum_indicator` — its indicator representation.
* `horvitzThompson_unbiased` — design unbiasedness.
* `horvitzThompson_variance` — the exact design variance.

**Reference.** D.G. Horvitz and D.J. Thompson, "A generalization of sampling without
replacement from a finite universe," *J. Amer. Statist. Assoc.* **47** (1952),
663–685: the estimator and its unbiasedness (their Theorem 1), the variance in
inclusion-probability form (their §5).  Not covered by Mead, whose finite-population
frame (`Mead §9.1`) it complements.  (`HT52`.)

**Proof formalization notes.**
* Both theorems reduce to the indicator representation
  `Ŷ_HT(S) = ∑ᵢ 𝟙{i ∈ S} · yᵢ/πᵢ` plus the `pmfExpect`/`pmfVar` calculus:
  unbiasedness via `pmfExpect_sum` and `E[𝟙ᵢ] = πᵢ`; the variance via `pmfVar_sum`,
  `pmfCov_smul_smul`, and `cov_inclusionIndicator`.
* Positivity `0 < πᵢ` is a genuine external condition of the theorem (a *measurable
  design* in the survey-sampling sense): without it, units with `πᵢ = 0` are never
  observed and their `yᵢ` cannot be estimated.
* The estimator itself is defined without any positivity hypothesis; for `πᵢ = 0`
  the term contributes `yᵢ/0 = 0` (Lean convention), and the moment theorems carry
  the positivity hypothesis explicitly.
-/

namespace StatLean.ExperimentalDesign

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The **Horvitz–Thompson estimator** of the population total: `∑_{i ∈ S} yᵢ/πᵢ`
(`HT52`).  Edge behaviour: units with `πᵢ = 0` contribute `0` by the division
convention; the moment theorems assume `πᵢ > 0`. -/
noncomputable def horvitzThompson (D : SamplingDesign U) (y : U → ℝ)
    (s : Finset U) : ℝ :=
  ∑ i ∈ s, y i / inclusionProb D i

/-- Indicator representation of the Horvitz–Thompson estimator. -/
theorem horvitzThompson_eq_sum_indicator (D : SamplingDesign U) (y : U → ℝ)
    (s : Finset U) :
    horvitzThompson D y s
      = ∑ i, inclusionIndicator i s * (y i / inclusionProb D i) := by
  exact sum_sample_eq_sum_indicator (fun i => y i / inclusionProb D i) s

/-- **Design unbiasedness of Horvitz–Thompson** (`HT52`, Theorem 1): if every unit
has positive inclusion probability, the estimator's design expectation is the
population total. -/
theorem horvitzThompson_unbiased (D : SamplingDesign U) (y : U → ℝ)
    -- USER-INPUT: strictly positive inclusion probabilities (measurable design); HT52
    (hpos : ∀ i, 0 < inclusionProb D i) :
    pmfExpect D (horvitzThompson D y) = populationTotal y := by
  have h : horvitzThompson D y
      = fun s => ∑ i, (y i / inclusionProb D i) * inclusionIndicator i s := by
    funext s
    rw [horvitzThompson_eq_sum_indicator]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h, pmfExpect_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pmfExpect_smul]
  exact div_mul_cancel₀ _ (hpos i).ne'

/-- **Exact design variance of Horvitz–Thompson** (`HT52`, §5):
`Var(Ŷ_HT) = ∑ᵢ ∑ⱼ ((π_{ij} − πᵢ πⱼ)/(πᵢ πⱼ)) yᵢ yⱼ`, diagonal `π_{ii} = πᵢ`. -/
theorem horvitzThompson_variance (D : SamplingDesign U) (y : U → ℝ)
    -- USER-INPUT: strictly positive inclusion probabilities (measurable design); HT52
    (hpos : ∀ i, 0 < inclusionProb D i) :
    pmfVar D (horvitzThompson D y)
      = ∑ i, ∑ j,
          (pairInclusionProb D i j - inclusionProb D i * inclusionProb D j)
            / (inclusionProb D i * inclusionProb D j) * (y i * y j) := by
  have h : horvitzThompson D y
      = fun s => ∑ i, (y i / inclusionProb D i) * inclusionIndicator i s := by
    funext s
    rw [horvitzThompson_eq_sum_indicator]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h, pmfVar_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pmfCov_smul_smul, cov_inclusionIndicator]
  have hi := (hpos i).ne'
  have hj := (hpos j).ne'
  field_simp

end StatLean.ExperimentalDesign
