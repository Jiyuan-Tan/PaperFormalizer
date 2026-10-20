module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-!
# Linear mixed-effects models — the latent-variable structure

The linear mixed model in its **latent-variable form**, with the latent-effects law
**arbitrary** — Gaussianity is never baked in (the Gaussian case is one instantiation in
`MixedEffects.Marginal`), honoring the area rule that models capture structure, not
parametric families:

* `LMMDesign n p q` — the constitutive design pair: fixed-effects design `X` and
  random-effects design `Z`;
* `lmmLaw D β G R` — the observation law of `Y = Xβ + Z b + ε` with `b ∼ G` and `ε ∼ R`
  independent (`(G.prod R).map (affine)` — independence of latent effects and noise is
  structural);
* `lmmClusterLaw` — `M` independent clusters, each drawing its own latent effect
  (`Measure.pi` of per-cluster laws).

In the Core calculus reading: `lmmLaw` is the latent marginalization (`mix`) of the latent
model through the affine conditional kernel, definitionally through `Measure.bind`/`map`.

**Reference.** N. M. Laird and J. H. Ware, "Random-effects models for longitudinal data,"
*Biometrics* **38** (1982), 963–974, Eq. (1.1)–(1.2) (`LW82`); G. M. Fitzmaurice, N. M.
Laird, and J. H. Ware, *Applied Longitudinal Analysis*, 2nd ed., Wiley, 2011, Ch. 8 (linear
mixed effects) (verify §) (`FLW Ch. 8`); C. E. McCulloch, S. R. Searle, and J. M. Neuhaus,
*Generalized, Linear, and Mixed Models*, 2nd ed., Wiley, 2008, Ch. 6 (verify §)
(`MSN Ch. 6`).

**Proof formalization notes.** Laptop-only data model — definitions only. *Book vs Lean:*
the books state the model with Gaussian `b` and `ε`; here the laws are free parameters with
mean/covariance entering as USER-INPUT moment hypotheses in `Marginal` — the first-moment and
second-moment conclusions (`E Y = Xβ`, `Cov Y = Z G Zᵀ + R`) hold with no Gaussianity, a
strict strengthening; the Gaussian marginal law is the special case. Balanced clusters
(shared dimensions) — ragged designs are a documented deviation (D-M5).

**Bibliographic comments.** Mixed models go back to C. R. Henderson ("Estimation of genetic
parameters," *Ann. Math. Statist.* **21** (1950), abstract) (`Hen50`); the modern
longitudinal formulation is Laird–Ware (1982).
-/

open MeasureTheory Matrix

namespace StatLean.StatisticalModels.MixedEffects

/-- The **linear mixed-effects design** (`LW82` Eq. (1.1)): fixed-effects design `X` and
random-effects design `Z` for one cluster of `n` observations. -/
structure LMMDesign (n p q : ℕ) where
  /-- Constitutive (LW82 Eq. (1.1)): the fixed-effects design matrix. -/
  X : Matrix (Fin n) (Fin p) ℝ
  /-- Constitutive (LW82 Eq. (1.1)): the random-effects design matrix. -/
  Z : Matrix (Fin n) (Fin q) ℝ

/-- The **linear mixed-model observation law**: `Y = Xβ + Z b + ε`, `b ∼ G`, `ε ∼ R`
independent — the latent law `G` arbitrary (`LW82` Eq. (1.1); `FLW Ch. 8`). -/
noncomputable def lmmLaw {n p q : ℕ} (D : LMMDesign n p q) (β : EuclideanSpace ℝ (Fin p))
    (G : Measure (EuclideanSpace ℝ (Fin q))) (R : Measure (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (G.prod R).map fun be =>
    Matrix.toEuclideanLin (𝕜 := ℝ) D.X β + Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 + be.2

/-- `M` independent clusters, each with its own design and its own latent draw
(`FLW Ch. 8`). -/
noncomputable def lmmClusterLaw {M n p q : ℕ} (Ds : Fin M → LMMDesign n p q)
    (β : EuclideanSpace ℝ (Fin p)) (G : Measure (EuclideanSpace ℝ (Fin q)))
    (R : Measure (EuclideanSpace ℝ (Fin n))) :
    Measure (Fin M → EuclideanSpace ℝ (Fin n)) :=
  Measure.pi fun i => lmmLaw (Ds i) β G R

end StatLean.StatisticalModels.MixedEffects
