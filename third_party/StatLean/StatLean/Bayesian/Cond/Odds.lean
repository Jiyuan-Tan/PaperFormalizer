module
public import StatLean.Bayesian.Cond.FinitePartition

@[expose] public section

/-!
# Posterior odds and the Bayes factor

The odds reformulation of Bayes' theorem for a single hypothesis event `s` against `sᶜ`:

* **posterior odds = prior odds × Bayes factor**
  $$\frac{\mu[s \mid d]}{\mu[s^c \mid d]} = \frac{\mu(s)}{\mu(s^c)} \cdot \frac{\mu[d \mid s]}{\mu[d \mid s^c]};$$
* the **Bayes factor as the odds ratio** `bayesFactor = posteriorOdds / priorOdds`.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.2 (odds form of
Bayes' theorem, eq. (1.2.2), p. 9); §5.2.2, Definition 5.2.5 (Bayes factor) and eq. (5.2.2),
p. 227.

**Proof formalization notes.** Everything unfolds to Mathlib's `ProbabilityTheory.cond` and
`ℝ≥0∞` division. The factorization identity is stated *unconditionally*: under `[IsFiniteMeasure μ]`
the generic case reduces to `ENNReal.mul_div_mul_left` with the nonzero, non-infinite factor
`(μ d)⁻¹`, and every degenerate case (`μ d`, `μ s`, or `μ sᶜ` equal to `0`) makes both sides `0`
or both `∞`. The *inversion* (`bayesFactor = posteriorOdds / priorOdds`) does need nondegenerate
priors `μ s ≠ 0`, `μ sᶜ ≠ 0` (else the odds ratio is `0/0` junk), which is exactly Robert's
standing assumption in Definition 5.2.5.

**Bibliographic comments.** The odds formulation of Bayesian hypothesis comparison and the Bayes
factor are due to H. Jeffreys (*Theory of Probability*, Oxford University Press, 1939; 3rd ed.
1961), whose calibration scale for Bayes factors — refined by I. J. Good ("Significance tests in
parallel and in series," *J. Amer. Statist. Assoc.* 53 (1958), 799–813) — remains in use. The
modern survey is R. E. Kass and A. E. Raftery, "Bayes factors," *J. Amer. Statist. Assoc.* 90
(1995), 773–795.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **Posterior odds = prior odds × Bayes factor** (Robert §1.2, eq. (1.2.2); Definition 5.2.5).
Holds unconditionally for a finite measure: all degenerate cases collapse both sides under the
`ℝ≥0∞` conventions. -/
theorem posteriorOdds_eq_priorOdds_mul_bayesFactor (μ : Measure Ω) [IsFiniteMeasure μ]
    -- LEAN-ONLY: the hypothesis `s` is an event
    {s : Set Ω} (hs : MeasurableSet s) (d : Set Ω) :
    posteriorOdds μ s d = priorOdds μ s * bayesFactor μ s d := by
  -- Both sides equal `μ (s ∩ d) / μ (sᶜ ∩ d)`.
  have hRHS : priorOdds μ s * bayesFactor μ s d = μ (s ∩ d) / μ (sᶜ ∩ d) := by
    rw [priorOdds, bayesFactor,
      (ENNReal.mul_div_mul_comm (Or.inr (measure_ne_top (μ[|sᶜ]) d))
        (Or.inl (measure_ne_top μ sᶜ))).symm,
      mul_comm (μ s), mul_comm (μ sᶜ),
      cond_mul_eq_inter hs d μ, cond_mul_eq_inter hs.compl d μ]
  rw [posteriorOdds, cond_apply' hs μ, cond_apply' hs.compl μ,
    Set.inter_comm d s, Set.inter_comm d sᶜ, hRHS]
  rcases eq_or_ne (μ d) 0 with hd0 | hd0
  · have hP0 : μ (s ∩ d) = 0 := measure_mono_null Set.inter_subset_right hd0
    have hQ0 : μ (sᶜ ∩ d) = 0 := measure_mono_null Set.inter_subset_right hd0
    simp [hP0, hQ0]
  · exact ENNReal.mul_div_mul_left _ _ (ENNReal.inv_ne_zero.mpr (measure_ne_top μ d))
      (ENNReal.inv_ne_top.mpr hd0)

/-- **Bayes factor as the odds ratio** (Robert Definition 5.2.5). Nondegeneracy of the prior is a
genuine input: without positive prior mass on both `s` and `sᶜ` the ratio is `0/0` junk. -/
theorem bayesFactor_eq_posteriorOdds_div_priorOdds (μ : Measure Ω) [IsFiniteMeasure μ]
    -- LEAN-ONLY: the hypothesis `s` is an event
    {s : Set Ω} (hs : MeasurableSet s) (d : Set Ω)
    -- USER-INPUT: the hypothesis has positive prior probability; Robert Definition 5.2.5
    (hs0 : μ s ≠ 0)
    -- USER-INPUT: the alternative has positive prior probability; Robert Definition 5.2.5
    (hsc0 : μ sᶜ ≠ 0) :
    bayesFactor μ s d = posteriorOdds μ s d / priorOdds μ s := by
  have hpne0 : priorOdds μ s ≠ 0 := fun h =>
    (ENNReal.div_eq_zero_iff.mp h).elim hs0 (measure_ne_top μ sᶜ)
  have hpnetop : priorOdds μ s ≠ ∞ := ENNReal.div_ne_top (measure_ne_top μ s) hsc0
  rw [posteriorOdds_eq_priorOdds_mul_bayesFactor μ hs d,
    mul_comm (priorOdds μ s) (bayesFactor μ s d),
    ENNReal.mul_div_cancel_right hpne0 hpnetop]

end StatLean.Bayesian
