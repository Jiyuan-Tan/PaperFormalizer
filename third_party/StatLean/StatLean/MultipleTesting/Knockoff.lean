module
public import StatLean.MultipleTesting.FDP.Defs
public import StatLean.MultipleTesting.Knockoff.Procedure
public import StatLean.MultipleTesting.Knockoff.FdpBound
public import StatLean.MultipleTesting.Knockoff.Supermartingale

@[expose] public section

/-!
# Knock-off filter FDR control

The **knock-off filter** at level $\alpha$ is a variable-selection procedure that, for a vector
of *knock-off statistics* $W = (W_1, \dots, W_d)$ (large positive $W_j$ flags variable $j$ as a
true signal, $W_j$ near zero or negative flags it as null), chooses a data-dependent threshold
$t^\star$ and rejects exactly the variables with $W_j \ge t^\star$. The threshold is the smallest
$t$ for which the estimated false discovery proportion stays at or below $\alpha$, using the
sign-symmetry of null statistics to estimate the number of false rejections by the number of
*negative* statistics that clear the threshold.

**Main result.** Under the knock-off-score sign-symmetry assumption on $W$, the procedure controls
the **false discovery rate** at level $\alpha$:
$$
  \mathrm{FDR} \;=\; \mathbb{E}\!\left[\mathrm{FDP}(t^\star)\right] \;\le\; \alpha .
$$
Here $\mathrm{FDP}(t) = \#\{j \in H_0 : W_j \ge t\} / \max(\#\{j : W_j \ge t\},\,1)$ is the
proportion of rejections that are true nulls.

The Lean statement adds two regularity hypotheses beyond the bare book statement, both of which
hold automatically for continuous knock-off statistics:
* `hties` — for every null coordinate $j \in H_0$, $W_j \ne 0$ almost surely, so the sign of a
  null statistic is well defined;
* `hmag` — almost surely the magnitudes $|W_i|$ are pairwise distinct, so the threshold ordering
  is unambiguous (no ties to break).

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 21 (Knock-Off), §21.3, Theorem 21.2 (Knock-Off).
Companion treatment: E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes, Stanford
University, 2023, Lecture 11, §11.5.

**Proof formalization notes.** This file assembles the two halves of the argument:

* `knockoff_fdp_le` (`Knockoff/FdpBound.lean`, deterministic): the pointwise bound
  $\mathrm{FDP}(t^\star) \le \alpha \cdot V_+(t^\star)/(1+V_-(t^\star))$, where $V_+$ counts null
  statistics above the threshold and $V_-$ counts null statistics whose negation is above it;
* `knockoff_ratio_stopped_le_one` (`Knockoff/Supermartingale.lean`, the supermartingale +
  optional-stopping core): $\mathbb{E}\!\left[V_+(t^\star)/(1+V_-(t^\star))\right] \le 1$, obtained
  by showing the reverse-time ratio process is a supermartingale and applying optional stopping at
  the data-dependent threshold $t^\star$.

Combining them, $\mathrm{FDR} = \int \mathrm{FDP} \le \int \alpha\,V_+/(1+V_-)
= \alpha \int V_+/(1+V_-) \le \alpha$ by integral monotonicity, factoring out $\alpha$, and the
ratio bound. The $1 + V_-$ in the denominator is the "$+1$" of the *knock-off$^+$* procedure,
which is what yields exact $\mathrm{FDR} \le \alpha$ control (rather than only a modified FDR).

**Bibliographic comments.** The knock-off filter originates with R. F. Barber and E. J. Candès,
"Controlling the false discovery rate via knockoffs", *Annals of Statistics* 43(5):2055–2085, 2015
(arXiv:1404.5609). That paper's Theorem 1 controls a *modified* FDR for the plain knock-off
procedure, while its Theorem 2 establishes exact $\mathrm{FDR} \le q$ control for the knock-off$^+$
procedure — the variant with the "$+1$" offset in the FDP estimate that is formalized here. The
sign-symmetry / supermartingale-with-optional-stopping argument used in this file follows the
structure of that paper's proof of Theorem 2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- `α * V₊(t*)/(1+V₋(t*))` is μ-integrable: via `ratio_eq_stoppedValue` it equals
`α * stoppedValue (Yproc W H₀) (tauStar W H₀ α)`, and the stopped value is integrable from
`Submartingale.integrable_stoppedValue` applied to the negated supermartingale. -/
private lemma ratio_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    Integrable (fun ω =>
      α * (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ))) μ := by
  haveI : SigmaFiniteFiltration μ (𝒢rev W H₀ hW.meas) := inferInstance
  -- Rewrite ratio as α * stoppedValue Yproc tauStar
  simp_rw [mul_div_assoc, ratio_eq_stoppedValue]
  -- Integrability from the negated supermartingale (= submartingale)
  have hstop_neg : Integrable (stoppedValue (-(Yproc W H₀)) (tauStar W H₀ α)) μ :=
    (knockoff_supermartingale W H₀ μ hW hmag).neg.integrable_stoppedValue
      (tauStar_isStoppingTime W H₀ α hW.meas) (tauStar_le W H₀ α)
  have hstop : Integrable (stoppedValue (Yproc W H₀) (tauStar W H₀ α)) μ := by
    have heq : stoppedValue (-(Yproc W H₀)) (tauStar W H₀ α) =
               -(stoppedValue (Yproc W H₀) (tauStar W H₀ α)) := by
      ext ω; simp [stoppedValue, Pi.neg_apply]
    rw [heq] at hstop_neg
    -- hstop_neg : Integrable (-(stoppedValue Yproc ...)) μ; negate twice
    simpa only [neg_neg] using hstop_neg.neg
  exact Integrable.const_mul hstop α

/-- **Knock-off FDR control** (Lu-BDA Ch. 21 (Knock-Off), §21.3, Theorem 21.2 (Knock-Off)). For a knock-off score `W`, the
knock-off procedure at level `α` controls the false discovery rate: `FDR ≤ α`. -/
theorem knockoff_fdr_le (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ) (hα : 0 < α)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ)
    -- LEAN-ONLY: no ties on null scores (`Wⱼ ≠ 0` a.s.), so the sign is well-defined; Lu-BDA §21.3
    (hties : ∀ j ∈ H₀, ∀ᵐ ω ∂μ, W j ω ≠ 0)
    -- USER-INPUT: a.s. distinct magnitudes (continuous knock-off statistics, no |Wᵢ| ties); Lu-BDA §21.3
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    FDR H₀ (knockoffRejects W α) μ ≤ α := by
  simp only [FDR]
  calc ∫ ω, FDP H₀ (knockoffRejects W α) ω ∂μ
      -- Step 1: FDP ≤ α · ratio pointwise → integrate monotonically
      ≤ ∫ ω, α * (Vplus W H₀ (tStar W α ω) ω : ℝ) /
             (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ :=
        integral_mono_of_nonneg
          -- FDP ≥ 0: numerator (Nat cast) ≥ 0, denominator max(R,1) ≥ 1 ≥ 0
          (Filter.Eventually.of_forall fun ω =>
            div_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (le_max_right _ _)))
          -- α · ratio integrable
          (ratio_integrable μ α W H₀ hW hmag)
          -- FDP ≤ α · ratio a.e. (deterministic, pointwise)
          (Filter.Eventually.of_forall fun ω => knockoff_fdp_le α hα W H₀ ω)
      -- Step 2: factor α out of the integral
    _ = α * ∫ ω, (Vplus W H₀ (tStar W α ω) ω : ℝ) /
                 (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ := by
        simp_rw [mul_div_assoc]; exact integral_const_mul α _
      -- Step 3: ∫ ratio ≤ 1, so α · ∫ ratio ≤ α · 1 = α
    _ ≤ α * 1 :=
        mul_le_mul_of_nonneg_left (knockoff_ratio_stopped_le_one μ α W H₀ hW hmag) hα.le
    _ = α := mul_one α

end StatLean.MultipleTesting
