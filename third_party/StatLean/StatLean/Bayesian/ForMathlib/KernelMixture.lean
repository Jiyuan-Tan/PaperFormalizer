module
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

/-!
# Mixtures of kernels (`mixKernel`)

The two-component mixture `w • κ₁ + (1 − w) • κ₂` of kernels, defined pointwise on measures
(the pinned Mathlib's `Kernel` carries `Add` but no `ℝ≥0∞`-scalar action, so the mixture must be
built by hand). Mixtures model **randomized estimators** (choose estimator `κ₁` with probability
`w`, else `κ₂`; Robert §2.4.1) and **random-scan MCMC sweeps** (Robert §6.3.5).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §2.4.1, p. 66 (randomized estimators, Theorem 2.4.2);
§6.3.5 (random-scan Gibbs).

**Proof formalization notes.** `mixKernel w κ₁ κ₂ x := w • κ₁ x + (1 − w) • κ₂ x` — measures do
carry `SMul ℝ≥0∞` and `Add`, and measurability of the coe is `(Kernel.measurable_coe … ).const_smul`
composition; a `Kernel`-level module structure is deliberately not introduced. Markov for `w ≤ 1`
(`tsub_add_cancel_of_le`); `lintegral_mixKernel` and `bind_mixKernel` are `lintegral_add_measure` +
`lintegral_smul_measure` and `Measure.bind`-additivity respectively. Candidate for upstreaming.

**Bibliographic comments.** Randomization of decision rules is a founding device of statistical
decision theory — A. Wald, *Statistical Decision Functions* (Wiley, 1950) — and the convexity of
the risk set it produces underlies minimax and complete-class theory (D. Blackwell and
M. A. Girshick, *Theory of Games and Statistical Decisions*, Wiley, 1954). Mixtures of Markov
transition kernels as MCMC sweeps appear with the random-scan Gibbs sampler (Geman and Geman 1984).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {𝓧 𝓨 : Type*} [m𝓧 : MeasurableSpace 𝓧] [m𝓨 : MeasurableSpace 𝓨]

/-- The map `x ↦ w • κ₁ x + (1 − w) • κ₂ x` is measurable. -/
theorem measurable_mixKernel_coe (w : ℝ≥0∞) (κ₁ κ₂ : Kernel 𝓧 𝓨) :
    Measurable fun x => w • κ₁ x + (1 - w) • κ₂ x := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact ((Kernel.measurable_coe κ₁ hs).const_mul w).add
    ((Kernel.measurable_coe κ₂ hs).const_mul (1 - w))

/-- **Two-component kernel mixture** `w • κ₁ + (1 − w) • κ₂` (Robert §2.4.1: randomized
estimators; §6.3.5: random-scan sweeps). The pinned `Kernel` has no `ℝ≥0∞`-smul, so the mixture is
defined pointwise on measures. -/
noncomputable def mixKernel (w : ℝ≥0∞) (κ₁ κ₂ : Kernel 𝓧 𝓨) : Kernel 𝓧 𝓨 :=
  ⟨fun x => w • κ₁ x + (1 - w) • κ₂ x, measurable_mixKernel_coe w κ₁ κ₂⟩

@[simp]
theorem mixKernel_apply (w : ℝ≥0∞) (κ₁ κ₂ : Kernel 𝓧 𝓨) (x : 𝓧) :
    mixKernel w κ₁ κ₂ x = w • κ₁ x + (1 - w) • κ₂ x := rfl

/-- A mixture of Markov kernels with weight `w ≤ 1` is Markov. -/
theorem isMarkovKernel_mixKernel {w : ℝ≥0∞}
    -- USER-INPUT: the mixing weight is a probability; Robert §2.4.1
    (hw : w ≤ 1)
    (κ₁ κ₂ : Kernel 𝓧 𝓨) [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] :
    IsMarkovKernel (mixKernel w κ₁ κ₂) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [mixKernel_apply]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact add_tsub_cancel_of_le hw

/-- Lintegral against a mixture kernel value. -/
theorem lintegral_mixKernel (w : ℝ≥0∞) (κ₁ κ₂ : Kernel 𝓧 𝓨) (x : 𝓧) (f : 𝓨 → ℝ≥0∞) :
    ∫⁻ y, f y ∂(mixKernel w κ₁ κ₂ x)
      = w * ∫⁻ y, f y ∂(κ₁ x) + (1 - w) * ∫⁻ y, f y ∂(κ₂ x) := by
  rw [mixKernel_apply, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp only [smul_eq_mul]

/-- Binding a measure through a mixture kernel mixes the binds. -/
theorem bind_mixKernel (w : ℝ≥0∞) (κ₁ κ₂ : Kernel 𝓧 𝓨) (μ : Measure 𝓧) :
    mixKernel w κ₁ κ₂ ∘ₘ μ = w • (κ₁ ∘ₘ μ) + (1 - w) • (κ₂ ∘ₘ μ) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [mixKernel_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_left ((Kernel.measurable_coe κ₁ hs).const_mul w) _,
    lintegral_const_mul _ (Kernel.measurable_coe κ₁ hs),
    lintegral_const_mul _ (Kernel.measurable_coe κ₂ hs),
    Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _)]

/-- Composing a mixture on the left distributes over the mixture. -/
theorem mixKernel_comp_left (w : ℝ≥0∞) (κ₁ κ₂ : Kernel 𝓧 𝓨) {𝓩 : Type*}
    [m𝓩 : MeasurableSpace 𝓩] (η : Kernel 𝓩 𝓧) (z : 𝓩) :
    (mixKernel w κ₁ κ₂ ∘ₖ η) z = w • ((κ₁ ∘ₖ η) z) + (1 - w) • ((κ₂ ∘ₖ η) z) := by
  rw [Kernel.comp_apply, Kernel.comp_apply, Kernel.comp_apply]
  exact bind_mixKernel w κ₁ κ₂ (η z)

end StatLean.Bayesian
