module
public import StatLean.ExperimentalDesign.Core.FinitePopulation

@[expose] public section

/-!
# Stratification of a finite population

A **stratification** (block structure) of the population `U` is a labelling
`st : U → B` into finitely many strata (blocks); the stratum of label `b` is the
subtype `{i // st i = b}`.  This file provides the deterministic decomposition
algebra shared by *blocked experiments* and *stratified sampling*:
$$N = \sum_b N_b, \qquad Y = \sum_b Y_b, \qquad
  \bar y = \sum_b \frac{N_b}{N}\, \bar y_b,$$
where `N_b`, `Y_b`, `ȳ_b` are the stratum size, total and mean.

Blocked randomization (`Randomization/Blocked`) and stratified sampling
(`Stratified/`) both instantiate one generic product-design construction over these
strata; the identities here are the deterministic half of every blockwise
unbiasedness statement.

## Main results

* `Stratum` — the stratum subtype.
* `sum_card_stratum` — stratum sizes partition the population size.
* `populationTotal_stratified` — the total decomposes over strata.
* `populationMean_stratified` — the mean is the size-weighted average of stratum
  means.

**Reference.** R. Mead, *The Design of Experiments*, Cambridge University Press,
1988, §7.1–§7.2 (design principles in blocked experiments: units grouped into blocks,
comparisons arranged within blocks) and §2.2 (block totals and means in the analysis
of variance identity).  (`Mead §7.2`, `Mead §2.2`.)

**Proof formalization notes.**
* Strata are subtypes, so stratum summaries are the `FinitePopulation` summaries of
  the restricted quantity `fun i : Stratum st b => y i` — no new definitions needed.
* Empty strata are allowed: their size weight is `0` and their (convention-valued)
  mean is multiplied by `0`, so the decompositions hold without nonemptiness
  hypotheses on individual strata.
* `populationMean_stratified` needs `Nonempty U` (for `N ≠ 0`); the empty-population
  version would read `0 = 0` but the proof divides by `N`.
-/

namespace StatLean.ExperimentalDesign

variable {U B : Type*} [Fintype U] [DecidableEq U] [Fintype B] [DecidableEq B]

/-- The **stratum** (block) of label `b` under the stratification `st`: the units
labelled `b`, as a subtype (`Mead §7.2`). -/
abbrev Stratum (st : U → B) (b : B) := {i : U // st i = b}

/-- Stratum sizes partition the population size. -/
theorem sum_card_stratum (st : U → B) :
    ∑ b, Fintype.card (Stratum st b) = Fintype.card U := by
  simp only [Stratum, Fintype.card_subtype]
  rw [← Finset.card_univ (α := U)]
  exact (Finset.card_eq_sum_card_fiberwise fun i _ => Finset.mem_univ (st i)).symm

/-- The population total decomposes as the sum of stratum totals. -/
theorem populationTotal_stratified (st : U → B) (y : U → ℝ) :
    populationTotal y = ∑ b, populationTotal (fun i : Stratum st b => y i) := by
  rw [populationTotal]
  exact (Fintype.sum_fiberwise st y).symm

/-- The population mean is the size-weighted average of the stratum means:
`ȳ = ∑_b (N_b / N) ȳ_b`.  Empty strata contribute `0` through their vanishing
weight. -/
theorem populationMean_stratified
    -- LEAN-ONLY: nonempty population, so the global size `N` is invertible
    [Nonempty U] (st : U → B) (y : U → ℝ) :
    populationMean y
      = ∑ b, (Fintype.card (Stratum st b) : ℝ) / (Fintype.card U : ℝ)
          * populationMean (fun i : Stratum st b => y i) := by
  have h : ∀ b ∈ (Finset.univ : Finset B),
      (Fintype.card (Stratum st b) : ℝ) / (Fintype.card U : ℝ)
          * populationMean (fun i : Stratum st b => y i)
        = (Fintype.card U : ℝ)⁻¹ * populationTotal (fun i : Stratum st b => y i) := by
    intro b _
    rw [populationTotal_eq_card_mul_mean]
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ← populationTotal_stratified,
    populationTotal, populationMean]

end StatLean.ExperimentalDesign
