module
public import StatLean.PointEstimation.Sufficiency.Basic
public import StatLean.PointEstimation.Model.Defs
public import Mathlib.Probability.Kernel.Composition.Comp

@[expose] public section

/-!
# Sufficiency has no operational cost: risk equality through a sufficient statistic

If `T` is sufficient for the model `P`, then every estimator — randomized or not — can be
replaced by an estimator that looks only at `T`, with *exactly* the same risk function. The
replacement is the composition of the original decision rule with the θ-free reconstruction
kernel `Q`: report `t`, regenerate an observation `x ~ Q t`, and then act as before.

Writing `Q : S ⇝ 𝓧` for the reconstruction kernel and `κ : 𝓧 ⇝ D` for the (possibly
randomized) estimator, the diagram commutes:

```
              Q                 κ
    S  ───────────────▶  𝓧  ───────────▶  D
    ▲                    ▲                ▲
    │ statLaw P T θ      │ P θ            │ risk of κ under P θ
    └────────────────────┴────── κ ∘ₖ Q ──┘
```

the top row being the composed kernel `κ ∘ₖ Q : S ⇝ D` and the bottom row the identity
`Q ∘ₘ (statLaw P T θ) = P θ` of `Sufficiency.Basic`. Contents:

* `riskRand_comp_eq_riskRand` — the risk identity for a fixed reconstruction kernel;
* `exists_riskRand_eq_of_sufficient` — the existence form (for any estimator there is a
  `T`-based randomized estimator with the same risk function);
* `riskRand_deterministic` — a nonrandomized estimator, viewed as a Dirac kernel, has its
  original risk;
* `exists_riskRand_eq_risk_of_sufficient` — the corollary for nonrandomized estimators.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.6
(Sufficient Statistics), Theorem 6.1 (any estimator is matched in risk by a randomized
estimator depending on the data only through a sufficient statistic). (`TPE2 §1.6 Thm 6.1`.)

**Proof formalization notes.**
* **Composition order.** `Q : Kernel S 𝓧` and `κ : Kernel 𝓧 D` compose as `κ ∘ₖ Q :
  Kernel S D` (Mathlib's `Kernel.comp` reads right-to-left, like function composition:
  `(η ∘ₖ κ) a = (κ a).bind η`). The reverse order does not typecheck, which is a useful
  guard rail here.
* The proof is `Kernel.lintegral_comp` (unfold `κ ∘ₖ Q` into an iterated integral) followed
  by `Measure.lintegral_bind` and the reconstruction identity `statLaw_snd`; no
  conditional-expectation machinery is involved. Measurability of the loss in the decision
  argument is the only side condition, and it is needed only to move the integrals.
* Risks are `ℝ≥0∞`-valued (`Model.Defs`), so the identity is an honest equality even when
  both sides are `∞`: no integrability hypothesis is required anywhere.
* Nothing here uses the fiber property `Q t {x | T x = t} = 1`; the risk identity holds for
  any reconstruction kernel that disintegrates the graph law.

**Bibliographic comments.** The interpretation of sufficiency as "no information is lost",
made precise by regenerating the data from the statistic with an auxiliary random mechanism,
goes back to R. A. Fisher ("On the mathematical foundations of theoretical statistics,"
*Phil. Trans. R. Soc. A* **222** (1922), 309–368). Its decision-theoretic form — that the
class of risk functions attainable by all procedures coincides with the class attainable by
procedures depending on a sufficient statistic alone — is due to R. R. Bahadur ("Sufficiency
and statistical decision functions," *Ann. Math. Statist.* **25** (1954), 423–462), building
on D. Blackwell ("Conditional expectation and unbiased sequential estimation," *Ann. Math.
Statist.* **18** (1947), 105–110).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S D : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S] [MeasurableSpace D]

/-- **Risk equality through a sufficient statistic (fixed reconstruction kernel).** If `Q`
disintegrates the graph law of `(T, id)` under every member, then for every randomized
estimator `κ : 𝓧 ⇝ D` the `T`-based estimator `κ ∘ₖ Q : S ⇝ D` has the same risk function. -/
theorem riskRand_comp_eq_riskRand (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (L : Θ → D → ℝ≥0∞) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T)
    -- LEAN-ONLY: measurability of the loss in the decision argument; needed to integrate
    -- against the kernels (no integrability is required, risks live in `ℝ≥0∞`)
    (hL : ∀ θ, Measurable (L θ)) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; classical sufficiency input
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    -- USER-INPUT: the (possibly randomized) estimator whose risk is to be matched
    (κ : Kernel 𝓧 D) [IsMarkovKernel κ] (θ : Θ) :
    riskRand (statLaw P T) L (κ ∘ₖ Q) θ = riskRand P L κ θ := by
  haveI := isProbabilityMeasure_statLaw P hT θ
  have hF : Measurable fun x => ∫⁻ d, L θ d ∂(κ x) := (hL θ).lintegral_kernel
  calc riskRand (statLaw P T) L (κ ∘ₖ Q) θ
      = ∫⁻ t, ∫⁻ x, (∫⁻ d, L θ d ∂κ x) ∂Q t ∂(statLaw P T θ) := by
        simp_rw [riskRand, Kernel.lintegral_comp _ _ _ (hL θ)]
    _ = ∫⁻ x, (∫⁻ d, L θ d ∂κ x) ∂(Q ∘ₘ (statLaw P T θ)) :=
        (Measure.lintegral_bind Q.aemeasurable hF.aemeasurable).symm
    _ = ∫⁻ x, (∫⁻ d, L θ d ∂κ x) ∂(P θ) := by rw [statLaw_snd P hT hgraph θ]
    _ = riskRand P L κ θ := rfl

/-- **Sufficiency ⇒ risk-equal randomized estimator based on `T`.** For any randomized
estimator there is a randomized estimator depending on the data only through the sufficient
statistic with the identical risk function. -/
theorem exists_riskRand_eq_of_sufficient (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (L : Θ → D → ℝ≥0∞) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T)
    -- LEAN-ONLY: measurability of the loss in the decision argument
    (hL : ∀ θ, Measurable (L θ))
    -- USER-INPUT: `T` is sufficient in the regular-conditional sense; classical hypothesis
    (hsuf : HasSufficientKernel P T)
    -- USER-INPUT: the estimator whose risk is to be matched
    (κ : Kernel 𝓧 D) [IsMarkovKernel κ] :
    ∃ κ' : Kernel S D, IsMarkovKernel κ' ∧
      ∀ θ, riskRand (statLaw P T) L κ' θ = riskRand P L κ θ := by
  obtain ⟨Q, hQ, hgraph⟩ := hsuf
  haveI := hQ
  exact ⟨κ ∘ₖ Q, inferInstance, fun θ => riskRand_comp_eq_riskRand P L hT hL hgraph κ θ⟩

/-- A nonrandomized estimator, regarded as the Dirac kernel `x ↦ δ_{δ(x)}`, has its own risk
as a randomized estimator. The bridge between `risk` and `riskRand`. -/
theorem riskRand_deterministic (P : Θ → Measure 𝓧) (L : Θ → D → ℝ≥0∞) {δ : 𝓧 → D}
    -- LEAN-ONLY: measurability of the estimator; required to form the Dirac kernel
    (hδ : Measurable δ)
    -- LEAN-ONLY: measurability of the loss in the decision argument
    (hL : ∀ θ, Measurable (L θ)) (θ : Θ) :
    riskRand P L (Kernel.deterministic δ hδ) θ = risk P L δ θ := by
  simp only [riskRand, risk, crossRisk, Kernel.lintegral_deterministic' hδ (hL θ)]

/-- **Sufficiency ⇒ risk-equal estimator based on `T`, nonrandomized case.** Every
nonrandomized estimator is matched, risk function for risk function, by the randomized
estimator `Kernel.deterministic δ ∘ₖ Q` which reads only the sufficient statistic. -/
theorem exists_riskRand_eq_risk_of_sufficient (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (L : Θ → D → ℝ≥0∞) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T)
    -- LEAN-ONLY: measurability of the loss in the decision argument
    (hL : ∀ θ, Measurable (L θ))
    -- USER-INPUT: `T` is sufficient in the regular-conditional sense; classical hypothesis
    (hsuf : HasSufficientKernel P T) {δ : 𝓧 → D}
    -- LEAN-ONLY: measurability of the estimator
    (hδ : Measurable δ) :
    ∃ κ' : Kernel S D, IsMarkovKernel κ' ∧
      ∀ θ, riskRand (statLaw P T) L κ' θ = risk P L δ θ := by
  obtain ⟨κ', hκ', hrisk⟩ :=
    exists_riskRand_eq_of_sufficient P L hT hL hsuf (Kernel.deterministic δ hδ)
  exact ⟨κ', hκ', fun θ => (hrisk θ).trans (riskRand_deterministic P L hδ hL θ)⟩

end StatLean.PointEstimation
