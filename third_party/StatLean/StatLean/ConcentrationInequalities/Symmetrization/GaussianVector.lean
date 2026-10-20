module
public import StatLean.ConcentrationInequalities.ForMathlib.GaussianAbsMoment
public import StatLean.ConcentrationInequalities.SubGaussian.Defs
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
# The canonical standard Gaussian vector

The joint law of $N$ i.i.d. standard Gaussians $g_1, \dots, g_N \sim N(0,1)$,
realized as the product measure
$$ \mathrm{gaussVec}\,N \;=\; \bigl(N(0,1)\bigr)^{\otimes N}
   \quad\text{on } \mathrm{Fin}\,N \to \mathbb{R}, $$
with its coordinate API: coordinate marginals are measure-preserving
evaluations; coordinates are integrable, mean zero, with
$\mathbb{E}|g_i| = \sqrt{2/\pi}$; and each coordinate (and its negation) is
sub-Gaussian with variance proxy $1$. The Gaussian analogue of
`Rademacher.lean`, consumed by `GaussianMax.lean` and `Gaussian.lean`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.6 ($g_1,\dots,g_N$ i.i.d. $N(0,1)$, Lemma
6.6.2); the Gaussian-is-sub-Gaussian bridge is §2.5 (Example 2.5.8 with
$\sigma^2 = 1$).

**Proof formalization notes.** The MGF bridge
`hasSubgaussianMGF_eval_gaussVec` is *sharp* (the Gaussian MGF equals the
sub-Gaussian bound): route `mgf_gaussianReal` + `mgf_map`/`mgf_id_map` +
`integrable_exp_mul_gaussianReal` + `MeasurePreserving.integrable_comp` along
`measurePreserving_eval` (all pin-verified), then our centered `IsSubGaussian`
via mean zero; negation by `HasSubgaussianMGF.neg`. The abs-moment lemma
transports `ForMathlib/GaussianAbsMoment` along the coordinate evaluation.
Edge behavior: all statements are per-coordinate, so `N = 0` is vacuous.
Named-sorry fallback of this work item: `hasSubgaussianMGF_eval_gaussVec`
(the MGF-bridge fiddle isolated; eval/mean/abs lemmas proven).

**Bibliographic comments.** Gaussian multipliers as the comparison class for
Rademacher sums are classical Banach-space probability (Ledoux–Talagrand,
*Probability in Banach Spaces*, 1991, Ch. 4); the sub-Gaussian bridging facts
are standard.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The canonical Gaussian vector** (HDP §6.6): the joint law of `N` i.i.d.
standard Gaussians, as the `N`-fold product of `gaussianReal 0 1` on
`Fin N → ℝ`. Edge behavior: `N = 0` gives the Dirac mass at the empty
function. -/
noncomputable def gaussVec (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1

instance (N : ℕ) : IsProbabilityMeasure (gaussVec N) := by
  unfold gaussVec; infer_instance

/-- Each coordinate of the Gaussian vector is a standard Gaussian. -/
-- LEAN-ONLY: coordinate marginal of the product measure; no book content.
theorem measurePreserving_eval_gaussVec (N : ℕ) (i : Fin N) :
    MeasurePreserving (fun g => g i) (gaussVec N) (gaussianReal 0 1) := by
  rw [gaussVec]
  exact MeasureTheory.measurePreserving_eval (μ := fun _ => gaussianReal 0 1) i

/-- Coordinates of the Gaussian vector are integrable. -/
-- LEAN-ONLY: `memLp_id_gaussianReal` transported along the coordinate eval.
theorem integrable_eval_gaussVec (N : ℕ) (i : Fin N) :
    Integrable (fun g => g i) (gaussVec N) := by
  have hid : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by simp))
  simpa using (measurePreserving_eval_gaussVec N i).integrable_comp_of_integrable hid

/-- Coordinates of the Gaussian vector are mean zero (HDP §6.6). -/
theorem integral_eval_gaussVec (N : ℕ) (i : Fin N) :
    ∫ g, g i ∂(gaussVec N) = 0 := by
  have hmap := integral_map (μ := gaussVec N) (φ := fun g : Fin N → ℝ => g i)
    (f := fun x : ℝ => x) (measurable_pi_apply i).aemeasurable (by fun_prop)
  rw [(measurePreserving_eval_gaussVec N i).map_eq] at hmap
  rw [← hmap]
  exact integral_id_gaussianReal

/-- `E|gᵢ| = √(2/π)` for each coordinate (HDP §6.6, p. 185); transport of
`integral_abs_id_gaussianReal` along the coordinate evaluation. -/
theorem integral_abs_eval_gaussVec (N : ℕ) (i : Fin N) :
    ∫ g, |g i| ∂(gaussVec N) = Real.sqrt (2 / Real.pi) := by
  have hmap := integral_map (μ := gaussVec N) (φ := fun g : Fin N → ℝ => g i)
    (f := fun x : ℝ => |x|) (measurable_pi_apply i).aemeasurable (by fun_prop)
  rw [(measurePreserving_eval_gaussVec N i).map_eq] at hmap
  rw [← hmap]
  exact integral_abs_id_gaussianReal

/-- Each coordinate has the sub-Gaussian MGF bound with proxy `1` — sharp,
since the Gaussian MGF *equals* `exp(t²/2)`. Named-sorry debt candidate of
this work item. -/
-- LEAN-ONLY: MGF bridge via `mgf_gaussianReal`; no scope change.
theorem hasSubgaussianMGF_eval_gaussVec (N : ℕ) (i : Fin N) :
    HasSubgaussianMGF (fun g => g i) 1 (gaussVec N) := by
  have haem : AEMeasurable (fun g : Fin N → ℝ => g i) (gaussVec N) :=
    (measurable_pi_apply i).aemeasurable
  rw [← HasSubgaussianMGF.id_map_iff haem, (measurePreserving_eval_gaussVec N i).map_eq]
  refine ⟨fun t => ?_, fun t => ?_⟩
  · exact integrable_exp_mul_gaussianReal t
  · rw [mgf_id_gaussianReal]; simp

/-- Each coordinate of the Gaussian vector is sub-Gaussian with variance
proxy `1` (HDP §2.5, Gaussian is sub-Gaussian). -/
theorem isSubGaussian_eval_gaussVec (N : ℕ) (i : Fin N) :
    IsSubGaussian (fun g => g i) 1 (gaussVec N) := by
  unfold IsSubGaussian
  rw [integral_eval_gaussVec]
  simpa using hasSubgaussianMGF_eval_gaussVec N i

/-- Negated coordinates are sub-Gaussian with the same proxy. -/
-- LEAN-ONLY: `HasSubgaussianMGF.neg`; feeds the two-sided max in GaussianMax.
theorem isSubGaussian_neg_eval_gaussVec (N : ℕ) (i : Fin N) :
    IsSubGaussian (fun g => -g i) 1 (gaussVec N) := by
  unfold IsSubGaussian
  have hneg : ∫ g, -g i ∂(gaussVec N) = 0 := by
    rw [integral_neg, integral_eval_gaussVec, neg_zero]
  rw [hneg]
  simpa using! (hasSubgaussianMGF_eval_gaussVec N i).neg

/-- The coordinates of the canonical Gaussian vector are independent
(HDP §6.6: `g₁, …, g_N` independent). -/
-- LEAN-ONLY: coordinates of `Measure.pi` are independent; via `iIndepFun_pi`.
theorem iIndepFun_eval_gaussVec (N : ℕ) :
    ProbabilityTheory.iIndepFun (fun (i : Fin N) (g : Fin N → ℝ) => g i)
      (gaussVec N) := by
  rw [gaussVec]
  exact iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) (fun i => measurable_id.aemeasurable)

end StatLean.ConcentrationInequalities
