module
public import StatLean.ComputationalStatistics.Resampling.Jackknife
public import StatLean.ComputationalStatistics.ForMathlib.PiMarginal
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Jackknife bias reduction

The probabilistic content of the jackknife (ECS §3.3, "Jackknife Bias
Correction"): if the statistic pair `(T, T')` has the two-term bias expansion

`E_{P^m}[T_m] = θ + a₁/m + a₂/m²` at the sample sizes `m = n+1` and `m = n`,

then the jackknifed statistic kills the first-order term exactly:

* `integral_jackknifeMean` — the delete-one average has the reduced-sample
  mean, `E_{P^{n+1}}[T₍•₎] = E_{P^n}[T']` (each deleted sample is again an
  i.i.d. sample);
* `integral_jackknifed` — `E[J(T)] = (n+1)·E[T] − n·E[T']`;
* `jackknife_bias_reduction` — `E[J(T)] = θ − a₂/((n+1)·n)`: the bias drops
  from order `1/n` to order `1/n²`, with the *exact* constant.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §3.3, "Jackknife Bias Correction" (pp. 76–77: the
power-series computation showing `Bias(J(T))` is at most of order `n⁻²`).
(`ECS §3.3`.)

**Proof formalization notes.**

* The book assumes a full power series `Σ_q a_q/n^q` *with constant
  coefficients*; we assume only the two-term expansion **at the two sample
  sizes actually used**, which is both weaker and precisely what the algebra
  consumes, and in exchange the conclusion is exact rather than `O(n⁻²)`.
  (A statistic family with genuinely higher-order terms satisfies our
  hypotheses only approximately; a later round can add the `O`-form.)
* The marginalization step is `ForMathlib/PiMarginal.lean`; the deleted-sample
  integrals need `T'` a.e.-strongly measurable to transport along the
  pushforward.
* Integrability of `T` and `T'` are the book's implicit "the expectations
  exist" (USER-INPUT).

**Bibliographic comments.** Quenouille (1956) for the bias-order computation;
Schucany–Gray–Owen, "On bias reduction in estimation," *J. Amer. Statist.
Assoc.* **66** (1971), 524–533, for higher-order versions (deferred).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {P : Measure 𝓧} [IsProbabilityMeasure P]
  {n : ℕ} {T : (Fin (n + 1) → 𝓧) → ℝ} {T' : (Fin n → 𝓧) → ℝ}

/-- The deletion map `x ↦ x ∘ Fin.succAbove i` is measurable. -/
private theorem measurable_comp_succAbove (i : Fin (n + 1)) :
    Measurable (fun x : Fin (n + 1) → 𝓧 => x ∘ i.succAbove) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Integrability transports along coordinate deletion: the deleted sample has law
`P^n`, so an integrable reduced-sample statistic stays integrable after deletion. -/
private theorem integrable_comp_delete (i : Fin (n + 1))
    (hT' : Integrable T' (Measure.pi fun _ : Fin n => P))
    (hT'm : AEStronglyMeasurable T' (Measure.pi fun _ : Fin n => P)) :
    Integrable (fun x => T' (jackknifeDelete i x))
      (Measure.pi fun _ : Fin (n + 1) => P) :=
  (integrable_map_measure (by rw [pi_map_precomp_succAbove i]; exact hT'm)
    (measurable_comp_succAbove i).aemeasurable).mp
    (by rw [pi_map_precomp_succAbove i]; exact hT')

/-- The delete-one average is integrable: it is a finite average of the deleted
statistics, each integrable by `integrable_comp_delete`. -/
private theorem integrable_jackknifeMean
    (hT' : Integrable T' (Measure.pi fun _ : Fin n => P))
    (hT'm : AEStronglyMeasurable T' (Measure.pi fun _ : Fin n => P)) :
    Integrable (jackknifeMean T') (Measure.pi fun _ : Fin (n + 1) => P) := by
  unfold jackknifeMean
  exact (integrable_finset_sum _ fun i _ => integrable_comp_delete i hT' hT'm).const_mul _

/-- **The delete-one average has the reduced-sample expectation** (ECS §3.3):
`E_{P^{n+1}}[T₍•₎] = E_{P^n}[T']`, because each deleted sample is again an
i.i.d. `P`-sample. -/
theorem integral_jackknifeMean
    -- USER-INPUT: the reduced-sample statistic has a finite mean; ECS §3.3
    (hT' : Integrable T' (Measure.pi fun _ : Fin n => P))
    -- LEAN-ONLY: a.e.-strong measurability, to transport along the deletion pushforward
    (hT'm : AEStronglyMeasurable T' (Measure.pi fun _ : Fin n => P)) :
    ∫ x, jackknifeMean T' x ∂(Measure.pi fun _ : Fin (n + 1) => P)
      = ∫ z, T' z ∂(Measure.pi fun _ : Fin n => P) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hEach : ∀ i : Fin (n + 1),
      ∫ x, T' (jackknifeDelete i x) ∂(Measure.pi fun _ : Fin (n + 1) => P)
        = ∫ z, T' z ∂(Measure.pi fun _ : Fin n => P) := by
    intro i
    have h₁ : ∫ z, T' z ∂((Measure.pi fun _ : Fin (n + 1) => P).map
          (fun x => x ∘ i.succAbove))
        = ∫ x, T' (x ∘ i.succAbove) ∂(Measure.pi fun _ : Fin (n + 1) => P) :=
      integral_map (measurable_comp_succAbove i).aemeasurable
        (by rw [pi_map_precomp_succAbove i]; exact hT'm)
    rw [pi_map_precomp_succAbove i] at h₁
    exact h₁.symm
  unfold jackknifeMean
  rw [integral_const_mul,
    integral_finset_sum _ fun i _ => integrable_comp_delete i hT' hT'm]
  simp only [hEach, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- **Expectation of the jackknifed statistic** (ECS §3.3):
`E[J(T)] = (n+1)·E[T] − n·E[T']`. -/
theorem integral_jackknifed
    -- USER-INPUT: the full-sample statistic has a finite mean; ECS §3.3
    (hT : Integrable T (Measure.pi fun _ : Fin (n + 1) => P))
    -- USER-INPUT: the reduced-sample statistic has a finite mean; ECS §3.3
    (hT' : Integrable T' (Measure.pi fun _ : Fin n => P))
    -- LEAN-ONLY: a.e.-strong measurability, to transport along the deletion pushforward
    (hT'm : AEStronglyMeasurable T' (Measure.pi fun _ : Fin n => P)) :
    ∫ x, jackknifed T T' x ∂(Measure.pi fun _ : Fin (n + 1) => P)
      = ((n : ℝ) + 1) * ∫ x, T x ∂(Measure.pi fun _ : Fin (n + 1) => P)
          - n * ∫ z, T' z ∂(Measure.pi fun _ : Fin n => P) := by
  simp only [jackknifed_eq]
  rw [integral_sub (hT.const_mul _) ((integrable_jackknifeMean hT' hT'm).const_mul _),
    integral_const_mul, integral_const_mul, integral_jackknifeMean hT' hT'm]

/-- **Jackknife bias reduction, exact form** (ECS §3.3, pp. 76–77): under the
two-term bias expansion `E[T_m] = θ + a₁/m + a₂/m²` at sizes `n+1` and `n`,
the jackknifed statistic has `E[J(T)] = θ − a₂/((n+1)·n)` — the `1/n` bias
term is annihilated and the remaining bias is of order `1/n²` with explicit
constant. -/
theorem jackknife_bias_reduction [NeZero n] {θ a₁ a₂ : ℝ}
    -- USER-INPUT: the full-sample statistic has a finite mean; ECS §3.3
    (hT : Integrable T (Measure.pi fun _ : Fin (n + 1) => P))
    -- USER-INPUT: the reduced-sample statistic has a finite mean; ECS §3.3
    (hT' : Integrable T' (Measure.pi fun _ : Fin n => P))
    -- LEAN-ONLY: a.e.-strong measurability, to transport along the deletion pushforward
    (hT'm : AEStronglyMeasurable T' (Measure.pi fun _ : Fin n => P))
    -- USER-INPUT: two-term bias expansion at sample size n+1; ECS §3.3
    (hTn : ∫ x, T x ∂(Measure.pi fun _ : Fin (n + 1) => P)
        = θ + a₁ / ((n : ℝ) + 1) + a₂ / ((n : ℝ) + 1) ^ 2)
    -- USER-INPUT: two-term bias expansion at sample size n; ECS §3.3
    (hTn' : ∫ z, T' z ∂(Measure.pi fun _ : Fin n => P)
        = θ + a₁ / (n : ℝ) + a₂ / (n : ℝ) ^ 2) :
    ∫ x, jackknifed T T' x ∂(Measure.pi fun _ : Fin (n + 1) => P)
      = θ - a₂ / (((n : ℝ) + 1) * n) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [integral_jackknifed hT hT' hT'm, hTn, hTn']
  field_simp
  ring

end StatLean.ComputationalStatistics

