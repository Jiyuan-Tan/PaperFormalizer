module
public import StatLean.StatisticalModels.Model.Defs
public import StatLean.PointEstimation.Model.Defs
public import Mathlib.Probability.Decision.Risk.Defs

@[expose] public section

/-!
# Adapter: decision-theoretic risks across the kernel bridge

Transports between the two risk vocabularies already in the library — PointEstimation's
bare-family risks (`risk`, `riskRand` over `P : Θ → Measure 𝓧`) and Mathlib's kernel-model
decision theory (`avgRisk`, `bayesRisk`, `minimaxRisk` over `P : Kernel Θ 𝓧`, the carrier of
the Minimaxity area) — so that lower bounds proved on one side apply verbatim on the other:

* `riskRand_coe` — on kernel models, `riskRand` is the inner integral of Mathlib's `avgRisk`
  (canonizing the identity `PointEstimation.Model.Defs` documents as "proved where used");
* `avgRisk_eq_lintegral_riskRand` — `avgRisk` is the prior-average of `riskRand`;
* `minimaxRisk_eq` — `minimaxRisk` is the inf-sup of `riskRand` over Markov estimators;
* `riskRand_deterministic` — randomized risk at a deterministic kernel is the nonrandomized
  risk.

**Reference.** A. Wald, *Statistical Decision Functions*, Wiley, 1950 (risk, minimax);
TPE2 §1.1 (the risk function); C. P. Robert, *The Bayesian Choice*, 2nd ed., §2.3 (Bayes and
minimax risks) (verify §).

**Proof formalization notes.** All statements are `lintegral` bookkeeping:
`riskRand_coe` unfolds `∘ₖ` composition via `Measure.lintegral_bind`/`Kernel.lintegral_comp`;
`riskRand_deterministic` is `lintegral_dirac'` (whence the LEAN-ONLY measurability of the
loss section). No new risk notions are defined — this file only equates existing ones.

**Bibliographic comments.** The randomized-estimator (kernel) formulation of decision rules is
Wald's; the observation that deterministic rules embed via Dirac kernels is standard (Wald
1950, §1.4; Le Cam 1986, Ch. 2) (verify §).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.StatisticalModels

open StatLean.PointEstimation

variable {Θ : Type*} [MeasurableSpace Θ] {𝓧 D : Type*}
  [MeasurableSpace 𝓧] [MeasurableSpace D]

/-- On kernel models, the bare-family randomized risk is the composed-kernel loss integral —
the inner layer of Mathlib's `avgRisk`. -/
theorem riskRand_coe (K : Kernel Θ 𝓧) [IsMarkovKernel K] (L : Θ → D → ℝ≥0∞)
    (κ : Kernel 𝓧 D) [IsMarkovKernel κ] (θ : Θ)
    -- LEAN-ONLY: measurability of the loss section (composed-measure lintegral unfolding)
    (hL : Measurable (L θ)) :
    riskRand ⇑K L κ θ = ∫⁻ d, L θ d ∂((κ ∘ₖ K) θ) :=
  (Kernel.lintegral_comp κ K θ hL).symm

/-- Mathlib's average risk is the prior-average of the bare-family randomized risk. -/
theorem avgRisk_eq_lintegral_riskRand (K : Kernel Θ 𝓧) [IsMarkovKernel K]
    (L : Θ → D → ℝ≥0∞) (κ : Kernel 𝓧 D) [IsMarkovKernel κ] (π : Measure Θ)
    -- LEAN-ONLY: measurability of the loss sections (riskRand_coe unfolding)
    (hL : ∀ θ, Measurable (L θ)) :
    avgRisk L K κ π = ∫⁻ θ, riskRand ⇑K L κ θ ∂π := by
  simp only [avgRisk]
  exact lintegral_congr fun θ => (riskRand_coe K L κ θ (hL θ)).symm

/-- Mathlib's minimax risk is the inf–sup of the bare-family randomized risk over Markov
estimators. Every Minimaxity-area lower bound thereby applies to bare families presented
through `toKernel`. -/
theorem minimaxRisk_eq (K : Kernel Θ 𝓧) [IsMarkovKernel K] (L : Θ → D → ℝ≥0∞)
    -- LEAN-ONLY: measurability of the loss sections (riskRand_coe unfolding)
    (hL : ∀ θ, Measurable (L θ)) :
    minimaxRisk (𝓨 := D) L K
      = ⨅ (κ : Kernel 𝓧 D) (_ : IsMarkovKernel κ), ⨆ θ, riskRand ⇑K L κ θ := by
  simp only [minimaxRisk]
  refine iInf_congr fun κ => iInf_congr fun hκ => iSup_congr fun θ => ?_
  have : IsMarkovKernel κ := hκ
  exact (riskRand_coe K L κ θ (hL θ)).symm

omit [MeasurableSpace Θ] in
/-- Randomized risk at a deterministic estimator is the nonrandomized risk (Wald §1.4:
deterministic rules embed via Dirac kernels). -/
theorem riskRand_deterministic (P : Θ → Measure 𝓧) (L : Θ → D → ℝ≥0∞) {δ : 𝓧 → D}
    -- LEAN-ONLY: measurability of the estimator and of the loss section (lintegral_dirac')
    (hδ : Measurable δ) (hL : ∀ θ, Measurable (L θ)) (θ : Θ) :
    riskRand P L (Kernel.deterministic δ hδ) θ = risk P L δ θ := by
  simp only [riskRand, risk, crossRisk, Kernel.lintegral_deterministic' hδ (hL θ)]

end StatLean.StatisticalModels
