module
public import StatLean.StatisticalModels.FactorModels.Gaussian
public import StatLean.StatisticalModels.GraphicalModels.Core.CondIndep
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.Covariance

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

@[expose] public section

/-!
# Local independence — the bridge between factor models and graphical models

`BKM`'s **axiom of conditional (local) independence**, Eq. (1.9): once the latent factors are
held fixed, the observed coordinates carry no dependence left over. In the linear model
`x = μ + Λ y + e` with Gaussian specific factors and a **diagonal** specific-factor covariance
`Ψ`, this is a theorem rather than an axiom, and it is the point at which the two new areas
meet: the conclusion is stated with `GraphicalModels.CondIndep`, the conditional-independence
predicate of the graphical slice, applied to the factor model of `FactorModels.Defs`.

* `latentObsJointLaw P F E` — the joint law of the pair `(y, x)`, i.e. the latent law composed
  with the measurement kernel; `latentObsJointLaw_fst` / `latentObsJointLaw_snd` identify its two
  marginals as `F` and `factorLaw P F E`;

  *Coordinate order.* This is the **latent-first** joint law, because everything here
  conditions *on* the factor. `FactorScores.factorJointLaw` is the **observation-first** joint
  law of the same model, because there one conditions on the observation to obtain `y ∣ x`.
  The two are each other's `Prod.swap` pushforward; the names are kept distinct so a reader is
  never in doubt about which coordinate is being conditioned on.
* `indepFun_eval_measurementKernel` — at a **fixed** factor value, two distinct observed
  coordinates are independent (`BKM` Eq. (1.9), pairwise form);
* `iIndepFun_eval_measurementKernel` — the **family** version: at a fixed factor value the
  whole family `(x₁, …, x_p)` is jointly independent;
* `map_measurementKernel_eq_pi` — `BKM` Eq. (1.9) verbatim, as the product formula
  `g(x ∣ y) = ∏ᵢ gᵢ(xᵢ ∣ y)` with `gᵢ(· ∣ y) = N((μ + Λy)ᵢ, ψᵢ)`;
* **`condIndep_eval_latentObsJointLaw` (HEADLINE)** — local independence in the graphical
  vocabulary: `xᵢ ⫫ xⱼ ∣ y` under the joint law, for `i ≠ j`;
* `factorCovariance_apply_of_oneFactor`, `factorCovariance_apply_ne_zero_of_oneFactor`,
  `not_indepFun_eval_gaussianFactorModel` — **the contrast**. After the factor is marginalised
  out, the off-diagonal entry of `Σ = Λ Φ Λᵀ + Ψ` is `λᵢ Φ λⱼ`, which is non-zero as soon as
  two loadings on a common factor are; so the observed coordinates are *dependent* even though
  they were conditionally independent given the factor.

**The moral.** Conditional independence *given the latent variables* and dependence *in the
observed marginal* are two different statements, and a factor model is precisely a device that
produces the second from the first: the common factor manufactures the observed correlations,
and `Ψ` diagonal says that nothing else does. A graphical model describes dependence by which
conditional independences hold **among the observed variables themselves**; a factor model
describes it by positing latent variables that **explain the dependence away**. The two are
therefore complementary descriptions of the same phenomenon, and this file is the
one place where both vocabularies are used in a single statement.

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, §1.4, **Eq. (1.9)** (p. 7):
`g(x ∣ y) = ∏_{i=1}^{p} gᵢ(xᵢ ∣ y)` — note this is a **chapter 1** equation, not a chapter 2
one — together with the surrounding passage (pp. 7–8): "if the dependencies among the *x*s are
induced by a set of latent variables **y** then when all **y**s are accounted for, the *x*s
will be independent if all the **y**s are held fixed. If this were not so the set of **y**s
would not be *complete*"; and, on p. 8, "It is better regarded as a definition of what we mean
when we say that the set of latent variables **y** is complete. In other words, that **y** is
sufficient to explain the dependencies among the *x*s." Eq. (1.10) (p. 8),
`f(x) = ∫ h(y) ∏ᵢ gᵢ(xᵢ ∣ y) dy`, is the marginalisation that the contrast section is about.
The linear-Gaussian instance is §3.2, Eq. (3.1)–(3.3) and Eq. (3.12) (`BKM`).

**Proof formalization notes.**

*Book vs Lean, three points.*

1. **Diagonality of `Ψ` is only uncorrelatedness in general; Gaussianity is what upgrades it to
   independence.** `BKM` Eq. (1.9) is an assumption about the conditional *density*, and
   Eq. (3.1) supplies it by taking `x ∣ y ∼ N_p(μ + Λ y, Ψ)` with `Ψ` diagonal. Our statements
   therefore fix the specific-factor law to be `multivariateGaussian 0 Ψ`: for a non-Gaussian
   `E` with diagonal covariance the conclusion is **false**, and no theorem below is stated at
   that generality. Diagonality alone is `HasDiagonalUniqueness`; it is not enough.
2. **The conditioning variable is the factor itself, not another block of coordinates.** So the
   statement uses the general `GraphicalModels.CondIndep μ f g h` and *not* the contracted
   `CondIndepCoords`, whose three arguments are all blocks of one vector.
3. **The family version lives at the kernel level.** `GraphicalModels.CondIndep` is a binary
   predicate, and no *family* conditional-independence predicate (an `iIndepFun` conditioned
   on a third variable) is available. `iIndepFun_eval_measurementKernel`
   and `map_measurementKernel_eq_pi` therefore state the joint independence of all `p`
   coordinates **under the conditional law at each factor value** — which is exactly what
   `BKM` Eq. (1.9) asserts, since (1.9) is a statement about `g(· ∣ y)` for each `y`.

*Junk values.* `multivariateGaussian m S` collapses to `Measure.dirac m` off the
positive-semidefinite cone, so every statement carries `P.uniqueCov.PosSemidef` (or
`IsProperFactorParams`) explicitly; without it the "conditional law" is a point mass and the
covariance statements are false.

**Bibliographic comments.** The conditional-independence formulation of a latent-variable model
is P. F. Lazarsfeld's, in S. A. Stouffer et al., *Measurement and Prediction*, Princeton Univ.
Press, 1950, ch. 10–11, where it appears as the *axiom of local independence* for latent
structure analysis; `BKM` §1.4 is the modern statement, and `BKM` p. 8 makes the point recorded
above, that local independence is better read as a *definition of completeness* of the latent
vector than as a testable assumption. The observation that a common factor manufactures
observed correlation is Spearman's original argument for a general factor (C. Spearman,
"'General intelligence', objectively determined and measured," *Amer. J. Psychol.* **15**
(1904), 201–292): the *tetrad differences* vanish exactly because the observed covariances
factor through a single latent variable. The complementary reading — describing dependence by
conditional independences among the observed variables — is the graphical-models programme of
S. L. Lauritzen, *Graphical Models*, Clarendon Press, 1996.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

variable {p q : ℕ}

/-! ### The joint law of factor and observation -/

/-- The **joint law of the pair `(y, x)`** in the linear factor model (`BKM` Eq. (3.3)): the
latent law `F` composed with the measurement kernel `y ↦ law of (μ + Λ y + e)`. This is the
sample space on which "conditionally independent **given the factor**" can be said at all —
`factorLaw` has already marginalised the factor away.

*Edge behaviour:* a probability measure exactly when `F` and `E` are (instance below); for
non-s-finite `F` or a non-s-finite kernel, `⊗ₘ` degenerates to `0`, matching the usual junk
convention of `Measure.compProd`. -/
noncomputable def latentObsJointLaw (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p))) :
    Measure (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin p)) :=
  F ⊗ₘ measurementKernel P E

instance (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure F]
    [IsProbabilityMeasure E] : IsProbabilityMeasure (latentObsJointLaw P F E) := by
  rw [latentObsJointLaw]; infer_instance

/-- The **latent marginal** of the joint law is the latent law `F` (`BKM` Eq. (3.2)). -/
theorem latentObsJointLaw_fst (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p)))
    -- LEAN-ONLY: `Measure.fst_compProd` is stated for an s-finite first factor; without it
    -- `⊗ₘ` is junk and the identity carries no content
    [SFinite F]
    -- LEAN-ONLY: makes `measurementKernel P E` a Markov kernel, which is what
    -- `Measure.fst_compProd` needs to leave the first marginal untouched
    [IsProbabilityMeasure E] :
    (latentObsJointLaw P F E).fst = F := by
  rw [latentObsJointLaw, Measure.fst_compProd]

/-- The **observed marginal** of the joint law is `factorLaw P F E` (`BKM` Eq. (3.3)/(1.10)):
integrating the factor out of the joint law returns the observed law. This is the identity that
makes the contrast at the end of the file a statement about the *same* model. -/
theorem latentObsJointLaw_snd (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p)))
    -- LEAN-ONLY: s-finiteness of the latent law, demanded by `Measure.snd_compProd`
    [SFinite F]
    -- LEAN-ONLY: makes `measurementKernel P E` Markov, hence s-finite — the side condition of
    -- `Measure.snd_compProd`
    [IsProbabilityMeasure E] :
    (latentObsJointLaw P F E).snd = factorLaw P F E := by
  rw [latentObsJointLaw, Measure.snd_compProd, factorLaw]

/-! ### `BKM` Eq. (1.9) — local independence at a fixed factor value -/

/-- LEAN-ONLY: the whole coordinate family of a multivariate Gaussian is *jointly* Gaussian as a
map into the bare product `Fin n → ℝ`. This is the hypothesis shape that Mathlib's
`HasGaussianLaw.indepFun_of_covariance_eq_zero` / `.iIndepFun_of_covariance_eq_zero` demand, and
it is nothing but `IsGaussian.hasGaussianLaw_id` transported along the continuous linear
equivalence `PiLp.continuousLinearEquiv` that forgets the `L²` norm. -/
private theorem hasGaussianLaw_coords {n : ℕ} (m : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) :
    HasGaussianLaw (fun (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) => x i)
      (multivariateGaussian m S) :=
  (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian m S)).map_equiv
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ)

/-- **`BKM` Eq. (1.9), pairwise form.** With Gaussian specific factors and a **diagonal**
specific-factor covariance `Ψ`, two distinct observed coordinates are independent under the
conditional law given the factor — for *every* value `y` of the factor. -/
theorem indepFun_eval_measurementKernel (P : FactorParams p q)
    -- USER-INPUT: the specific factors are uncorrelated across coordinates, i.e. `Ψ` diagonal;
    -- BKM §3.2 Eq. (3.1), the hypothesis that makes Eq. (1.9) hold in the linear model
    (hΨdiag : HasDiagonalUniqueness P)
    -- USER-INPUT: `Ψ` is a genuine covariance matrix; BKM Eq. (3.1). Without it
    -- `multivariateGaussian 0 Ψ` is a Dirac mass and the conditional law is degenerate
    (hΨ : P.uniqueCov.PosSemidef) {i j : Fin p}
    -- USER-INPUT: two distinct observed coordinates; BKM Eq. (1.9)
    (hij : i ≠ j) (y : EuclideanSpace ℝ (Fin q)) :
    IndepFun (fun x : EuclideanSpace ℝ (Fin p) => x i) (fun x : EuclideanSpace ℝ (Fin p) => x j)
      (measurementKernel P (multivariateGaussian 0 P.uniqueCov) y) := by
  rw [measurementKernel_multivariateGaussian P hΨ y]
  refine ((hasGaussianLaw_coords _ P.uniqueCov).prodMk i j).indepFun_of_covariance_eq_zero ?_
  rw [covariance_eval_multivariateGaussian hΨ]
  exact hΨdiag hij

/-- **`BKM` Eq. (1.9), family form.** All `p` observed coordinates are *jointly* independent
under the conditional law at a fixed factor value — the statement `BKM` actually makes, since
Eq. (1.9) is a product over all `i = 1, …, p`. -/
theorem iIndepFun_eval_measurementKernel (P : FactorParams p q)
    -- USER-INPUT: `Ψ` diagonal; BKM §3.2 Eq. (3.1)
    (hΨdiag : HasDiagonalUniqueness P)
    -- USER-INPUT: `Ψ` a genuine covariance matrix; BKM Eq. (3.1)
    (hΨ : P.uniqueCov.PosSemidef) (y : EuclideanSpace ℝ (Fin q)) :
    iIndepFun (fun (i : Fin p) (x : EuclideanSpace ℝ (Fin p)) => x i)
      (measurementKernel P (multivariateGaussian 0 P.uniqueCov) y) := by
  rw [measurementKernel_multivariateGaussian P hΨ y]
  refine (hasGaussianLaw_coords _ P.uniqueCov).iIndepFun_of_covariance_eq_zero fun i j hij => ?_
  rw [covariance_eval_multivariateGaussian hΨ]
  exact hΨdiag hij

/-- **`BKM` Eq. (1.9) verbatim**: `g(x ∣ y) = ∏_{i=1}^{p} gᵢ(xᵢ ∣ y)`, with the univariate
conditional laws `gᵢ(· ∣ y) = N((μ + Λ y)ᵢ, ψᵢ)` read off the diagonal of `Ψ`. The pushforward
along `WithLp.ofLp` is only the passage from `EuclideanSpace ℝ (Fin p)` to the bare product
`Fin p → ℝ` on which `Measure.pi` lives; it changes nothing measure-theoretically. -/
theorem map_measurementKernel_eq_pi (P : FactorParams p q)
    -- USER-INPUT: `Ψ` diagonal; BKM §3.2 Eq. (3.1)
    (hΨdiag : HasDiagonalUniqueness P)
    -- USER-INPUT: `Ψ` a genuine covariance matrix; BKM Eq. (3.1)
    (hΨ : P.uniqueCov.PosSemidef) (y : EuclideanSpace ℝ (Fin q)) :
    (measurementKernel P (multivariateGaussian 0 P.uniqueCov) y).map (fun x => WithLp.ofLp x)
      = Measure.pi fun i : Fin p =>
          gaussianReal ((P.μ + Matrix.toEuclideanLin (𝕜 := ℝ) P.loading y) i)
            (P.uniqueCov i i).toNNReal := by
  have hiid := iIndepFun_eval_measurementKernel P hΨdiag hΨ y
  rw [measurementKernel_multivariateGaussian P hΨ y] at hiid ⊢
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin p => (by fun_prop :
      AEMeasurable (fun x : EuclideanSpace ℝ (Fin p) => x i)
        (multivariateGaussian
          (P.μ + Matrix.toEuclideanLin (𝕜 := ℝ) P.loading y) P.uniqueCov)))).1 hiid
  exact hmap.trans (congrArg Measure.pi (funext fun i =>
    (measurePreserving_eval_multivariateGaussian hΨ (i := i)).map_eq))

/-! ### The headline — local independence in the graphical vocabulary -/

/-- **HEADLINE — local independence** (`BKM` §1.4, Eq. (1.9); linear-Gaussian instance §3.2,
Eq. (3.1)). In the Gaussian linear factor model with a **diagonal** specific-factor covariance
`Ψ`, two distinct observed coordinates are conditionally independent given the latent factor:
`xᵢ ⫫ xⱼ ∣ y` under the joint law of `(y, x)`.

This is the bridge between the two areas: the conclusion is `GraphicalModels.CondIndep`, the
disintegration predicate of the graphical slice, and the model is `FactorModels.latentObsJointLaw`.
The witnesses `CondIndep` asks for are the two coordinate marginals of the measurement kernel.

*Book vs Lean:* `BKM` Eq. (1.9) states local independence for the whole family and for an
arbitrary conditional density; here it is a **theorem** in the Gaussian linear model, in the
pairwise form that `CondIndep` can express. The family form is
`iIndepFun_eval_measurementKernel` / `map_measurementKernel_eq_pi`, stated at the kernel level
for want of a family conditional-independence predicate. -/
theorem condIndep_eval_latentObsJointLaw (P : FactorParams p q)
    (F : Measure (EuclideanSpace ℝ (Fin q)))
    -- LEAN-ONLY: the latent law is a probability measure — needed for `⊗ₘ` to be the joint law
    -- of a pair of random variables and for `Measure.fst_compProd` to return `F`
    [IsProbabilityMeasure F]
    -- USER-INPUT: the specific factors are uncorrelated across coordinates, i.e. `Ψ` diagonal;
    -- BKM §3.2 Eq. (3.1) — this is what makes Eq. (1.9) true here, and it is *not* enough
    -- without the Gaussianity built into the error law below
    (hΨdiag : HasDiagonalUniqueness P)
    -- USER-INPUT: `Ψ` is a genuine covariance matrix; BKM Eq. (3.1)
    (hΨ : P.uniqueCov.PosSemidef) {i j : Fin p}
    -- USER-INPUT: two distinct observed coordinates; BKM Eq. (1.9)
    (hij : i ≠ j) :
    GraphicalModels.CondIndep
        (latentObsJointLaw P F (multivariateGaussian 0 P.uniqueCov))
        (fun z => z.2 i) (fun z => z.2 j) Prod.fst := by
  set K := measurementKernel P (multivariateGaussian 0 P.uniqueCov) with hKdef
  have hmi : Measurable (fun x : EuclideanSpace ℝ (Fin p) => x i) := by fun_prop
  have hmj : Measurable (fun x : EuclideanSpace ℝ (Fin p) => x j) := by fun_prop
  have hmij : Measurable (fun x : EuclideanSpace ℝ (Fin p) => (x i, x j)) := hmi.prodMk hmj
  refine ⟨K.map (fun x => x i), K.map (fun x => x j),
    Kernel.IsMarkovKernel.map _ hmi, Kernel.IsMarkovKernel.map _ hmj, ?_⟩
  -- the measurement kernel, read pairwise, *is* the product of its two coordinate marginals
  have hK : K.map (fun x : EuclideanSpace ℝ (Fin p) => (x i, x j))
      = (K.map fun x => x i) ×ₖ (K.map fun x => x j) := by
    refine Kernel.ext fun y => ?_
    rw [Kernel.map_apply _ hmij, Kernel.prod_apply, Kernel.map_apply _ hmi,
      Kernel.map_apply _ hmj]
    exact (indepFun_iff_map_prod_eq_prod_map_map hmi.aemeasurable hmj.aemeasurable).1
      (indepFun_eval_measurementKernel P hΨdiag hΨ hij y)
  have hfst : (latentObsJointLaw P F (multivariateGaussian 0 P.uniqueCov)).map Prod.fst = F := by
    rw [latentObsJointLaw, ← Measure.fst, Measure.fst_compProd]
  calc (latentObsJointLaw P F (multivariateGaussian 0 P.uniqueCov)).map
        (fun z => (z.1, (z.2 i, z.2 j)))
      = (F ⊗ₘ K).map (Prod.map id fun x : EuclideanSpace ℝ (Fin p) => (x i, x j)) := rfl
    _ = F ⊗ₘ (K.map fun x : EuclideanSpace ℝ (Fin p) => (x i, x j)) :=
        (Measure.compProd_map hmij).symm
    _ = F ⊗ₘ ((K.map fun x => x i) ×ₖ (K.map fun x => x j)) := by rw [hK]
    _ = _ := by rw [hfst]

/-! ### The contrast — dependence in the observed marginal

Local independence says nothing about the *observed* law. Marginalising the factor out
(`BKM` Eq. (1.10), `latentObsJointLaw_snd`) leaves `Σ = Λ Φ Λᵀ + Ψ`, whose off-diagonal entries
are the common part alone — the specific factors contribute only to the diagonal. In the
one-factor model `Σᵢⱼ = λᵢ φ λⱼ`, so any two coordinates loading on the same factor are
correlated, hence (being jointly Gaussian) dependent. This is the precise sense in which a
common factor *manufactures* the observed dependence that local independence has removed from
the conditional law. -/

section Contrast

/-- The **off-diagonal entries of the one-factor covariance**: for `q = 1` and `Ψ` diagonal,
`Σᵢⱼ = λᵢ φ λⱼ` whenever `i ≠ j` — the specific factors drop out entirely off the diagonal
(contrast `Communality.variance_eq_common_add_specificVariance`, which is the diagonal
case). -/
theorem factorCovariance_apply_of_oneFactor (P : FactorParams p 1)
    -- USER-INPUT: `Ψ` diagonal — the factor-analytic restriction; BKM Eq. (3.1), (3.12)
    (hΨdiag : HasDiagonalUniqueness P) {i j : Fin p}
    -- USER-INPUT: two distinct observed coordinates; BKM Eq. (3.12)
    (hij : i ≠ j) :
    factorCovariance P i j = P.loading i 0 * P.factorCov 0 0 * P.loading j 0 := by
  simp [factorCovariance, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    hΨdiag hij]

/-- **The common factor induces observed correlation** (`BKM` §1.4, p. 7: "if `x₁` and `x₂` both
depend on `y₁` we may expect the common influence of `y₁` to induce a correlation between `x₁`
and `x₂`"). For a standardized one-factor model, the observed covariance between two
coordinates with non-zero loadings is non-zero — despite their conditional independence given
the factor. -/
theorem factorCovariance_apply_ne_zero_of_oneFactor (P : FactorParams p 1)
    -- USER-INPUT: standardized latent factor, `Φ = I`; BKM Eq. (3.2)
    (hΦ : IsStandardized P)
    -- USER-INPUT: `Ψ` diagonal; BKM Eq. (3.1)
    (hΨdiag : HasDiagonalUniqueness P) {i j : Fin p}
    -- USER-INPUT: two distinct observed coordinates; BKM Eq. (3.12)
    (hij : i ≠ j)
    -- USER-INPUT: coordinate `i` genuinely loads on the factor; BKM §1.4, p. 7
    (hi : P.loading i 0 ≠ 0)
    -- USER-INPUT: coordinate `j` genuinely loads on the same factor; BKM §1.4, p. 7
    (hj : P.loading j 0 ≠ 0) :
    factorCovariance P i j ≠ 0 := by
  rw [factorCovariance_apply_of_oneFactor P hΨdiag hij, show P.factorCov = 1 from hΦ]
  simp only [Matrix.one_apply_eq, mul_one]
  exact mul_ne_zero hi hj

/-- **The contrast, as a negative statement about the observed law.** In the Gaussian
one-factor model with two non-zero loadings, the two observed coordinates are **not**
independent — even though `condIndep_eval_latentObsJointLaw` makes them conditionally independent
given the factor. Together the two theorems are the conceptual payload of this file.

The observed law is `N(μ, Σ)`, so independence of the two coordinates would force
`cov(xᵢ, xⱼ) = Σᵢⱼ = 0`, contradicting `factorCovariance_apply_ne_zero_of_oneFactor`. -/
theorem not_indepFun_eval_gaussianFactorModel (P : FactorParams p 1)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2) — without them
    -- `gaussianFactorModel` degenerates to a Dirac mass, under which every pair of coordinates
    -- *is* independent, so the hypothesis is essential
    (hP : IsProperFactorParams P)
    -- USER-INPUT: standardized latent factor, `Φ = I`; BKM Eq. (3.2)
    (hΦ : IsStandardized P)
    -- USER-INPUT: `Ψ` diagonal; BKM Eq. (3.1)
    (hΨdiag : HasDiagonalUniqueness P) {i j : Fin p}
    -- USER-INPUT: two distinct observed coordinates; BKM Eq. (3.12)
    (hij : i ≠ j)
    -- USER-INPUT: coordinate `i` genuinely loads on the factor; BKM §1.4, p. 7
    (hi : P.loading i 0 ≠ 0)
    -- USER-INPUT: coordinate `j` genuinely loads on the same factor; BKM §1.4, p. 7
    (hj : P.loading j 0 ≠ 0) :
    ¬ IndepFun (fun x : EuclideanSpace ℝ (Fin p) => x i)
        (fun x : EuclideanSpace ℝ (Fin p) => x j) (gaussianFactorModel p 1 P) := by
  intro hind
  rw [gaussianFactorModel_eq_multivariateGaussian P hP] at hind
  have hcoords := hasGaussianLaw_coords P.μ (factorCovariance P)
  have hcov := hind.covariance_eq_zero (hcoords.eval i).memLp_two (hcoords.eval j).memLp_two
  rw [covariance_eval_multivariateGaussian (posSemidef_factorCovariance P hP)] at hcov
  exact factorCovariance_apply_ne_zero_of_oneFactor P hΦ hΨdiag hij hi hj hcov

end Contrast

end StatLean.StatisticalModels.FactorModels
