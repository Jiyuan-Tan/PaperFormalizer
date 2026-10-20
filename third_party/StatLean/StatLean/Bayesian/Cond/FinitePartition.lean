module
public import StatLean.Bayesian.Cond.Defs

@[expose] public section

/-!
# Law of total probability and finite-partition Bayes' theorem

For a finite measurable partition `{H i}ᵢ∈ₛ` of the sample space and observed data `d`, this file
proves the **law of total probability**
$$\mu(d) = \sum_{i \in s} \mu[d \mid H_i]\,\mu(H_i),$$
the **finite-partition Bayes' theorem**
$$\mu[H_j \mid d] = \frac{\mu[d \mid H_j]\,\mu(H_j)}{\sum_{i \in s} \mu[d \mid H_i]\,\mu(H_i)},$$
and the **two-hypothesis Bayes' theorem** (the `{t, tᶜ}` special case).

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §1.3
(Bayes' rule / conditional probability), p. 6.

**Proof formalization notes.** Built directly on Mathlib's `ProbabilityTheory.cond`
(`μ[d | H i] = cond μ (H i) d`). We work in `ℝ≥0∞` with `[IsFiniteMeasure μ]`, which removes all
`∞` cases; degenerate parts (`μ (H i) = 0`) contribute `0` to both sides under the
extended-nonnegative conventions (`0/0 = 0`), so **no positivity hypotheses are needed**. Key
Mathlib bricks: `cond_mul_eq_inter`, `cond_add_cond_compl_eq`, `cond_apply'`,
`measure_biUnion_finset`.

**Bibliographic comments.** Bayes' theorem first appeared, for the binomial case, in the essay of
T. Bayes read to the Royal Society in 1761 and published posthumously by R. Price ("An essay
towards solving a problem in the doctrine of chances," *Philosophical Transactions of the Royal
Society* 53 (1763), 370–418). P. S. Laplace rediscovered it in full generality in his "Mémoire sur
la probabilité des causes par les événements" (1773/1774), apparently unaware of Bayes's work; the
finite-partition computation formalized here is exactly Laplace's usage.
For the history see S. M. Stigler, *The History of Statistics* (Harvard, 1986) and A. I. Dale,
*A History of Inverse Probability* (Springer, 1991).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω]

/-- **Law of total probability** over a finite measurable partition:
`μ d = ∑ i ∈ s, μ[d | H i] * μ (H i)`. Parts with `μ (H i) = 0` contribute `0` to both sides,
so no positivity hypotheses are needed (Gelman §1.3, the total-probability denominator). -/
theorem measure_eq_sum_cond_mul_of_partition {s : Finset ι} {H : ι → Set Ω}
    -- LEAN-ONLY: the hypotheses `H i` are events (measurability is measure-theoretic regularity)
    (hHm : ∀ i ∈ s, MeasurableSet (H i))
    -- USER-INPUT: the hypotheses are mutually exclusive; Gelman §1.3
    (hHd : (s : Set ι).PairwiseDisjoint H)
    -- USER-INPUT: the hypotheses are exhaustive; Gelman §1.3
    (hHc : ⋃ i ∈ s, H i = Set.univ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    -- LEAN-ONLY: the observed data `d` is an event (measurability is regularity)
    {d : Set Ω} (hd : MeasurableSet d) :
    μ d = ∑ i ∈ s, μ[d | H i] * μ (H i) := by
  have hdisj : (s : Set ι).PairwiseDisjoint (fun i => H i ∩ d) :=
    fun i hi j hj hij => (hHd hi hj hij).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas : ∀ i ∈ s, MeasurableSet (H i ∩ d) := fun i hi => (hHm i hi).inter hd
  have hunion : (⋃ i ∈ s, H i ∩ d) = d := by
    rw [← Set.iUnion₂_inter, hHc, Set.univ_inter]
  calc μ d = μ (⋃ i ∈ s, H i ∩ d) := by rw [hunion]
    _ = ∑ i ∈ s, μ (H i ∩ d) := measure_biUnion_finset hdisj hmeas
    _ = ∑ i ∈ s, μ[d | H i] * μ (H i) :=
        Finset.sum_congr rfl fun i hi => (cond_mul_eq_inter (hHm i hi) d μ).symm

/-- **Bayes' theorem for a finite partition** (Gelman §1.3, discrete posterior form). If
`μ d = 0` both sides are `0` (`0/0 = 0` in `ℝ≥0∞`), so the observed-data event needs no
positivity hypothesis. -/
theorem cond_eq_cond_mul_div_sum_of_partition {s : Finset ι} {H : ι → Set Ω}
    -- LEAN-ONLY: the hypotheses `H i` are events
    (hHm : ∀ i ∈ s, MeasurableSet (H i))
    -- USER-INPUT: the hypotheses are mutually exclusive; Gelman §1.3
    (hHd : (s : Set ι).PairwiseDisjoint H)
    -- USER-INPUT: the hypotheses are exhaustive; Gelman §1.3
    (hHc : ⋃ i ∈ s, H i = Set.univ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    -- LEAN-ONLY: the observed data `d` is an event
    {d : Set Ω} (hd : MeasurableSet d) {j : ι} (hj : j ∈ s) :
    μ[H j | d] = μ[d | H j] * μ (H j) / ∑ i ∈ s, μ[d | H i] * μ (H i) := by
  rw [← measure_eq_sum_cond_mul_of_partition hHm hHd hHc μ hd,
    cond_apply' (hHm j hj) μ, cond_mul_eq_inter (hHm j hj) d μ, Set.inter_comm d (H j),
    ENNReal.div_eq_inv_mul]

/-- **Two-hypothesis Bayes' theorem** (Gelman §1.3). Only the hypothesis `t` needs
measurability; the data `d` may be any set (`cond_apply'` / `cond_add_cond_compl_eq` take the
target set arbitrary). Degenerate cases vanish under the `ℝ≥0∞` conventions. -/
theorem cond_eq_cond_mul_div_add_compl (μ : Measure Ω) [IsFiniteMeasure μ]
    -- LEAN-ONLY: the hypothesis `t` is an event
    {t : Set Ω} (ht : MeasurableSet t) (d : Set Ω) :
    μ[t | d] = μ[d | t] * μ t / (μ[d | t] * μ t + μ[d | tᶜ] * μ tᶜ) := by
  rw [cond_add_cond_compl_eq ht μ, cond_apply' ht μ, cond_mul_eq_inter ht d μ,
    Set.inter_comm d t, ENNReal.div_eq_inv_mul]

end StatLean.Bayesian
