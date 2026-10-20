module
public import StatLean.StatisticalModels.FactorModels.Defs
public import StatLean.StatisticalModels.MixedEffects.Marginal

@[expose] public section

/-!
# The factor model **is** a linear mixed model

The one theorem this whole area is organized around:

* **`factorLaw_eq_lmmLaw`** — `factorLaw P F E = lmmLaw (factorDesign P) P.μ F E`, i.e. the
  linear factor model `x = μ + Λ y + e` is literally the linear mixed model with
  fixed-effects design `X = 1`, fixed effect `β = μ`, and random-effects design `Z = Λ`;
* `meanVec_factorLaw` and `covMatrix_factorLaw` — the first two moments: the observed mean is
  `μ` and the observed covariance is `Λ · Cov(latent) · Λᵀ + Cov(noise)` for an arbitrary
  latent law, which at laws carrying `(Φ, Ψ)` *is* `Σ = Λ Φ Λᵀ + Ψ`.

Specializing these to the declared parameters `(Φ, Ψ)` — i.e. `Σ = factorCovariance P` — is
`FactorModels.Moments`.

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, §3.2, Eq. (3.3) (`BKM`); N. M. Laird and
J. H. Ware, "Random-effects models for longitudinal data," *Biometrics* **38** (1982),
963–974, Eq. (1.1)–(1.2) (`LW82`).

**Proof formalization notes.** The bridge is a `Measure.bind`-versus-`Measure.prod`-image
identity: `(measurementKernel P E ∘ₘ F) s = ∫⁻ y, E {z ∣ Λ y + μ + z ∈ s} ∂F`, which is
`Measure.prod_apply` applied to `lmmLaw`'s definition after `add_comm`/`add_assoc` on
`μ + Λ y + z`. Both moment corollaries then need only `toEuclideanLin (1 : Matrix) x = x`.
*Book vs Lean:* `BKM` Eq. (3.12) is the orthogonal case `Φ = I` of `covMatrix_factorLaw`;
the general `Φ` is our generalization.

**Bibliographic comments.** That factor analysis, random-effects models and variance
components are the same linear latent-variable calculus is folklore going back to
C. R. Henderson (1950); `BKM` ch. 1 makes the "unified approach" its organizing theme.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

variable {p q : ℕ}

/-- LEAN-ONLY: the identity matrix acts as the identity on Euclidean space. -/
theorem toEuclideanLin_one_apply {a : ℕ} (x : EuclideanSpace ℝ (Fin a)) :
    Matrix.toEuclideanLin (𝕜 := ℝ) (1 : Matrix (Fin a) (Fin a) ℝ) x = x := by
  simp

/-- **The bridge**: the linear factor model is the linear mixed model with `X = 1`, `β = μ`,
`Z = Λ` (`BKM` Eq. (3.3) = `LW82` Eq. (1.1)). -/
theorem factorLaw_eq_lmmLaw (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p)))
    -- LEAN-ONLY: s-finiteness of both free laws; without it `Measure.bind` and
    -- `Measure.prod` are junk on both sides and the identity carries no content
    [SFinite F] [SFinite E] :
    factorLaw P F E = MixedEffects.lmmLaw (factorDesign P) P.μ F E := by
  have hA : Measurable fun y : EuclideanSpace ℝ (Fin q) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) P.loading y :=
    ((Matrix.toEuclideanLin (𝕜 := ℝ) P.loading).continuous_of_finiteDimensional).measurable
  have hg : Measurable fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin p) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) (factorDesign P).X P.μ
        + Matrix.toEuclideanLin (𝕜 := ℝ) (factorDesign P).Z be.1 + be.2 :=
    ((hA.comp measurable_fst).const_add _).add measurable_snd
  -- both sides are `∫⁻ y, E {z ∣ Λ y + μ + z ∈ s} ∂F`: `Measure.bind_apply` on the left,
  -- `Measure.prod_apply` on the right; the integrands differ only by `add_comm`
  ext s hs
  rw [factorLaw, MixedEffects.lmmLaw,
    Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
    Measure.map_apply hg hs, Measure.prod_apply (hg hs)]
  refine lintegral_congr fun y => ?_
  rw [measurementKernel_apply, Measure.map_apply (by fun_prop) hs]
  congr 1
  ext z
  simp only [Set.mem_preimage, factorDesign_X, factorDesign_Z, toEuclideanLin_one_apply]
  rw [add_comm (Matrix.toEuclideanLin (𝕜 := ℝ) P.loading y) P.μ]

/-- **First moment** (`BKM` Eq. (3.3); `LW82` Eq. (1.2)): with centered latent and specific
factors the observed mean is `μ`. -/
theorem meanVec_factorLaw (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure F]
    [IsProbabilityMeasure E]
    -- USER-INPUT: centered latent factors and specific factors; BKM Eq. (3.2)–(3.3)
    (hF : meanVec F = 0) (hE : meanVec E = 0)
    -- USER-INPUT: first moments exist; BKM Eq. (3.3)
    (hF1 : Integrable id F) (hE1 : Integrable id E) :
    meanVec (factorLaw P F E) = P.μ := by
  rw [factorLaw_eq_lmmLaw, MixedEffects.meanVec_lmmLaw (factorDesign P) P.μ F E hF hE hF1 hE1,
    factorDesign_X, toEuclideanLin_one_apply]

/-- **Second moment, latent form** (`LW82` Eq. (1.2) at `Z = Λ`): the observed covariance is
`Λ · Cov(y) · Λᵀ + Cov(e)`, for **arbitrary** latent and error laws. The covariance
decomposition of `BKM` Eq. (3.12) is its special case at laws carrying `(Φ, Ψ)`. -/
theorem covMatrix_factorLaw (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure F]
    [IsProbabilityMeasure E]
    -- USER-INPUT: second moments of the latent and specific factors; BKM Eq. (3.2)–(3.3)
    (hF2 : MemLp id 2 F) (hE2 : MemLp id 2 E) :
    covMatrix (factorLaw P F E)
      = P.loading * covMatrix F * P.loadingᵀ + covMatrix E := by
  rw [factorLaw_eq_lmmLaw, MixedEffects.covMatrix_lmmLaw (factorDesign P) P.μ F E hF2 hE2,
    factorDesign_Z]

end StatLean.StatisticalModels.FactorModels
