module
public import StatLean.Bayesian.Decision.Defs
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

@[expose] public section

/-!
# Rao–Blackwellization (variance reduction by conditioning)

Conditioning an estimator on a sub-σ-algebra cannot increase its quadratic risk:
$$\mathbb E\big[(\mathbb E[T \mid \mathcal G] - c)^2\big] \le \mathbb E\big[(T - c)^2\big].$$
In MCMC practice (`Robert §6.3.4`) this is the **Rao–Blackwellization** of an ergodic average:
replacing sampled values by their conditional expectations given the retained coordinates reduces
variance at no bias cost.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §6.3.4 (Rao–Blackwellization, displayed inequality, pp. 309–310 —
unnumbered; cites Gelfand and Smith 1990); the classical Rao–Blackwell theorem is the §2 exercise
tradition.

**Proof formalization notes.** Stretch item (2F.8). The route is L² contractivity of conditional
expectation: `eLpNorm_condExp_le : eLpNorm (μ[f|m]) 2 μ ≤ eLpNorm f 2 μ` applied to `f := T − c`
(`condExp_sub` and `condExp_const` move the constant through), then the `eLpNorm`-squared ↔
`∫⁻ sqLoss` bridge (`sqLoss c t = ‖t − c‖ₑ^2` up to symmetry of the square). If the exponent
bridging resists, this file's results are droppable without downstream impact (nothing consumes
them; recorded in the roadmap).

**Bibliographic comments.** The Rao–Blackwell theorem is C. R. Rao ("Information and the accuracy
attainable in the estimation of statistical parameters," *Bull. Calcutta Math. Soc.* 37 (1945),
81–91) and D. Blackwell ("Conditional expectation and unbiased sequential estimation," *Ann. Math.
Statist.* 18 (1947), 105–110). Its use as an MCMC variance-reduction device is A. E. Gelfand and
A. F. M. Smith (1990), extended by J. S. Liu, W. H. Wong and A. Kong ("Covariance structure of the
Gibbs sampler…," *Biometrika* 81 (1994), 27–40).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- **Rao–Blackwell for quadratic loss** (Robert §6.3.4, stretch): conditioning an integrable
real statistic on a sub-σ-algebra does not increase its quadratic risk about any center `c`. -/
theorem raoBlackwell_sqLoss {μ : Measure 𝓧} [IsFiniteMeasure μ] {m : MeasurableSpace 𝓧}
    -- LEAN-ONLY: `m` is a sub-σ-algebra of the ambient space (regularity)
    (hm : m ≤ m𝓧) {T : 𝓧 → ℝ}
    -- USER-INPUT: the statistic is square-integrable; Robert §6.3.4
    (hT : MemLp T 2 μ) (c : ℝ) :
    ∫⁻ x, sqLoss c ((μ[T | m]) x) ∂μ ≤ ∫⁻ x, sqLoss c (T x) ∂μ := by
  -- The quadratic risk about `c` is the square of the `L²` norm of `c - ·`.
  have bridge : ∀ h : 𝓧 → ℝ,
      ∫⁻ x, sqLoss c (h x) ∂μ = eLpNorm (fun x => c - h x) 2 μ ^ (2 : ℝ) := by
    intro h
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ← ENNReal.rpow_mul,
      ENNReal.toReal_ofNat, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one]
    simp only [sqLoss]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_natCast (‖c - h x‖ₑ) 2]
    norm_num
  -- The centered statistic and its conditional expectation.
  have hci : Integrable (fun _ : 𝓧 => c) μ := integrable_const c
  have hTi : Integrable T μ := hT.integrable one_le_two
  have hsub : μ[(fun _ => c) - T | m] =ᵐ[μ] fun x => c - (μ[T | m]) x := by
    have h1 := condExp_sub hci hTi m
    have h2 : μ[fun _ : 𝓧 => c | m] = fun _ => c := condExp_const hm c
    filter_upwards [h1] with x hx
    rw [hx, h2]
    rfl
  have hle : eLpNorm (fun x => c - (μ[T | m]) x) 2 μ ≤ eLpNorm (fun x => c - T x) 2 μ :=
    calc eLpNorm (fun x => c - (μ[T | m]) x) 2 μ
        = eLpNorm (μ[(fun _ => c) - T | m]) 2 μ := (eLpNorm_congr_ae hsub).symm
      _ ≤ eLpNorm ((fun _ => c) - T) 2 μ := eLpNorm_condExp_le_eLpNorm _ one_le_two
      _ = eLpNorm (fun x => c - T x) 2 μ := rfl
  rw [bridge (μ[T | m]), bridge T]
  exact ENNReal.rpow_le_rpow hle (by norm_num)

end StatLean.Bayesian
