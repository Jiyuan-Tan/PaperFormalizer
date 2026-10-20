module
public import StatLean.ComputationalStatistics.Core.Defs
public import StatLean.ComputationalStatistics.ForMathlib.PiMoments

@[expose] public section

/-!
# Monte Carlo estimation

The correctness core of ordinary Monte Carlo (ECS §2.2): for
`X₁, …, Xₙ ~ P` i.i.d. and `Î = (1/n)·Σᵢ g(Xᵢ)` (eq. (2.8)),

* `mcEstimate_unbiased` — `E[Î] = ∫ g dP`;
* `mcEstimate_variance` — `Var(Î) = Var_P(g)/n`;
* `mcEstimate_mse` — `E[(Î − ∫ g dP)²] = Var_P(g)/n`;
* `mcEstimate_consistent_ae` — `Îₙ → ∫ g dP` almost surely (ECS §2.2, p. 53).

The i.i.d. sample is the canonical product space
`Measure.pi (fun _ : Fin n => P)`; the statements are textbook-named wrappers of
the `ForMathlib/PiMoments.lean` coordinate-average lemmas at `g ∘ eval`.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.2 (Monte Carlo estimation, eqs. (2.5)–(2.9); the
strong-law display on p. 53).  (`ECS §2.2`.)

**Proof formalization notes.**

* The estimator is `mcEstimate g : (Fin n → 𝓧) → ℝ` from `Core/Defs.lean`;
  unfolding it reduces every statement to the corresponding
  `*_avg_eval_pi` lemma.
* `[NeZero n]` excludes the `n = 0` junk average.
* Consistency is along the canonical sequence space
  `Measure.infinitePi (fun _ : ℕ => P)`, restricting each finite prefix through
  `Fin.cast`-free coordinate reads `fun i : Fin n => ω i`.

**Bibliographic comments.** Monte Carlo estimation of functionals originates
with Metropolis–Ulam, "The Monte Carlo method," *J. Amer. Statist. Assoc.* **44**
(1949), 335–341; the variance analysis is standard since Hammersley–Handscomb,
*Monte Carlo Methods*, Methuen, 1964.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {P : Measure 𝓧} [IsProbabilityMeasure P]
  {n : ℕ} {g : 𝓧 → ℝ}

/-- **Unbiasedness of the Monte Carlo estimator** (ECS §2.2, eq. (2.8)):
`E[(1/n)·Σᵢ g(Xᵢ)] = ∫ g dP` for an i.i.d. sample from `P`. -/
theorem mcEstimate_unbiased [NeZero n]
    -- USER-INPUT: the integrand has a finite first moment; ECS §2.2
    (hg : Integrable g P) :
    ∫ x, mcEstimate g x ∂(Measure.pi fun _ : Fin n => P) = ∫ z, g z ∂P :=
  integral_avg_eval_pi hg

/-- **Variance of the Monte Carlo estimator** (ECS §2.2, eq. (2.9) discussion):
`Var(Î) = Var_P(g)/n`. -/
theorem mcEstimate_variance [NeZero n]
    -- USER-INPUT: the integrand has a finite second moment; ECS §2.2
    (hg : MemLp g 2 P) :
    variance (mcEstimate g) (Measure.pi fun _ : Fin n => P)
      = variance g P / n :=
  variance_avg_eval_pi hg

/-- **Mean-squared error of the Monte Carlo estimator** (ECS §2.2): since the
estimator is unbiased, `E[(Î − ∫ g dP)²] = Var_P(g)/n`. -/
theorem mcEstimate_mse [NeZero n]
    -- USER-INPUT: the integrand has a finite second moment; ECS §2.2
    (hg : MemLp g 2 P) :
    ∫ x, (mcEstimate g x - ∫ z, g z ∂P) ^ 2 ∂(Measure.pi fun _ : Fin n => P)
      = variance g P / n :=
  integral_sq_dev_avg_eval_pi hg

/-- **Strong consistency of the Monte Carlo estimator** (ECS §2.2, p. 53):
along the canonical i.i.d. sequence, `Îₙ → ∫ g dP` almost surely. -/
theorem mcEstimate_consistent_ae {g : 𝓧 → ℝ}
    -- USER-INPUT: the integrand has a finite first moment; ECS §2.2
    (hg : Integrable g P)
    -- LEAN-ONLY: measurability of the integrand (regularity)
    (hgm : Measurable g) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => P),
      Tendsto (fun n : ℕ => mcEstimate g fun i : Fin n => ω i)
        atTop (𝓝 (∫ z, g z ∂P)) := by
  filter_upwards [tendsto_avg_eval_infinitePi hg hgm] with ω hω
  refine hω.congr fun m => ?_
  simp only [mcEstimate]
  rw [Fin.sum_univ_eq_sum_range (fun i => g (ω i)) m]

end StatLean.ComputationalStatistics
