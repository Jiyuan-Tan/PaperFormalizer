module
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# Score and Fisher information — core data model for the information inequality

For a dominated model with densities `p_θ` (`θ` real, or `θ` in `ℝˢ`), the **score** is
the logarithmic derivative of the density in the parameter and the **Fisher
information** its second moment:
$$ \dot\ell_\theta(x) = \frac{\partial_\theta p_\theta(x)}{p_\theta(x)}, \qquad
   I(\theta) = \int \dot\ell_\theta(x)^2\, p_\theta(x)\, d\mu(x). $$

* `score M θ x` — 1-D score, junk-safe (`0/0 = 0`);
* `fisherInfo M μ θ` — 1-D Fisher information;
* `scoreVec M θ x` — the partial-derivative score vector for an `ℝˢ`-parametrized
  family (`EuclideanSpace ℝ (Fin s)`);
* `infoMatrix M μ θ` — the Fisher information matrix.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.5 (The
Information Inequality), the score function and the Fisher information. (`TPE2 §2.5`.)

**Proof formalization notes.**
* The score is *derived from the densities* (a `deriv` in `θ`), unlike the free
  candidate-score functionals of the asymptotic-statistics area; a bridge lemma
  (`InformationInequality.Basic`) identifies `fisherInfo` with that area's bilinear
  `fisherInformation` evaluated on the derived score.
* Division by a vanishing density yields `0` (Lean's total real division), so the
  definitions are junk-safe; regularity (differentiability in `θ` for a.e. `x`,
  differentiation under the integral sign) enters only as explicit hypotheses of the
  information-inequality theorems, never through the definitions.
* `infoMatrix` is an explicit `Matrix (Fin s) (Fin s) ℝ` of second moments of partial
  scores; positive definiteness is a hypothesis where needed (`Matrix.PosDef`).

**Bibliographic comments.** The score and its information were introduced by
R. A. Fisher ("Theory of statistical estimation," *Proc. Camb. Phil. Soc.* **22**
(1925), 700–725). The information lower bound for variances is due independently to
C. R. Rao ("Information and the accuracy attainable in the estimation of statistical
parameters," *Bull. Calcutta Math. Soc.* **37** (1945), 81–91) and H. Cramér
(*Mathematical Methods of Statistics*, Princeton, 1946, §32.3), with early forms in
M. Fréchet ("Sur l'extension de certaines évaluations statistiques au cas de petits
échantillons," *Rev. Inst. Int. Statist.* **11** (1943), 182–205) and G. Darmois;
the multiparameter matrix form is due to C. R. Rao (1945, ibid.).
-/

open MeasureTheory

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **score** of a real-parametrized dominated family: the logarithmic
`θ`-derivative `∂_θ p_θ(x) / p_θ(x)` of the density. Junk-safe: where the density
vanishes (or is not differentiable, so `deriv` returns junk), real division/`deriv`
conventions apply and the value carries no content — theorems restrict to the support
via their hypotheses. -/
noncomputable def score (M : ParametricFamily 𝓧 ℝ) (θ : ℝ) (x : 𝓧) : ℝ :=
  deriv (fun t => M.density t x) θ / M.density θ x

/-- The **Fisher information** of a real-parametrized dominated family at `θ`:
`I(θ) = ∫ (score)² p_θ dμ`. -/
noncomputable def fisherInfo (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧) (θ : ℝ) : ℝ :=
  ∫ x, score M θ x ^ 2 * M.density θ x ∂μ

/-- The **score vector** of an `ℝˢ`-parametrized dominated family: partial logarithmic
derivatives along the coordinate directions. -/
noncomputable def scoreVec {s : ℕ} (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    (θ : EuclideanSpace ℝ (Fin s)) (x : 𝓧) : EuclideanSpace ℝ (Fin s) :=
  WithLp.toLp 2 fun i =>
    deriv (fun t : ℝ => M.density (θ + t • EuclideanSpace.single i 1) x) 0 /
      M.density θ x

/-- The **Fisher information matrix** `I(θ)ᵢⱼ = E_θ [scoreᵢ · scoreⱼ]`. -/
noncomputable def infoMatrix {s : ℕ} (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    (μ : Measure 𝓧) (θ : EuclideanSpace ℝ (Fin s)) : Matrix (Fin s) (Fin s) ℝ :=
  fun i j => ∫ x, scoreVec M θ x i * scoreVec M θ x j * M.density θ x ∂μ

end StatLean.PointEstimation
