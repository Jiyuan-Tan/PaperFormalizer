module
public import StatLean.StatisticalModels.FactorModels.Rotation
public import StatLean.AsymptoticStatistics.ForMathlib.PiGaussian
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# The observed-data likelihood of the normal factor model

The likelihood a factor analysis is actually fitted by. Because the latent factors are
integrated out, the observed-data likelihood is **not** a latent-data likelihood at all: it
is the ordinary multivariate normal likelihood evaluated at the structured covariance
`Σ = Λ Φ Λᵀ + Ψ`.

* `gaussianLogDensity m S x` — the multivariate normal log density
  `−(p/2)log 2π − ½ log det S − ½ (x−m)ᵀ S⁻¹ (x−m)`;
* `factorLogLik P x` — the factor model's observed-data log-likelihood contribution at `x`,
  *defined* as `gaussianLogDensity μ (factorCovariance P) x`, and tied to the actual law by
  `factorLaw_eq_withDensity_exp_factorLogLik` (the density theorem);
* `factorLogLikSample P x` — the log-likelihood of an i.i.d. sample `x : Fin n → ℝᵖ`;
* **`factorLogLik_rotateParams`** — the likelihood is invariant under every nonsingular
  reparameterization of the latent space, the precise sense in which maximum likelihood
  cannot select a rotation (`BKM` §3.3, p. 50; §3.13.1).

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, Eq. (3.5) (the marginal law whose
density this is), Eq. (3.12) (`Σ = Λ Λ′ + Ψ`), §3.3, p. 50 (requiring `Λ′Ψ⁻¹Λ` diagonal
"removes the freedom to arbitrarily rotate `Λ`"), §3.12.1 (identifiability) (`BKM`);
D. N. Lawley, "The estimation of factor loadings by the method of maximum likelihood,"
*Proc. Roy. Soc. Edinburgh* **60** (1940), 64–82 (`Law40`).

**Proof formalization notes.** The rotation invariance is one rewrite of the covariance —
the whole point of stating the likelihood as a function of `(μ, Σ)`. The density theorem is
the real analytic content: the Gaussian law is the affine image of `stdGaussian` under
`S^{1/2}`, so the change-of-variables formula for a linear isomorphism produces the classical
Lebesgue density, with `volume` on `EuclideanSpace ℝ (Fin p)` the standard
orthonormal-basis Haar measure. *Junk values:* `Matrix.det` of a singular `Σ` is `0` and
`Real.log 0 = 0`, and `Matrix.inv` is `0`, so `gaussianLogDensity` is finite nonsense at a
degenerate `Σ`; every statement about it as a likelihood carries `(factorCovariance P).PosDef`.
*Book vs Lean:* `BKM` writes the likelihood at `Φ = I`; the general-`Φ` form here specializes
to it.

**Bibliographic comments.** Maximum-likelihood factor analysis is Lawley (1940); the modern
EM treatment is D. B. Rubin and D. T. Thayer, "EM algorithms for ML factor analysis,"
*Psychometrika* **47** (1982), 69–76. Only the likelihood *function* and its exact invariance
are formalized here — no estimator, no EM, no asymptotics.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal RealInnerProductSpace MatrixOrder

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

variable {p q : ℕ}

/-- The **multivariate normal log density** at mean `m` and covariance `S`:
`−(p/2) log 2π − ½ log det S − ½ (x−m)ᵀ S⁻¹ (x−m)`.

*Edge behavior:* at a singular `S` this is finite nonsense (`Matrix.det S = 0` with
`Real.log 0 = 0`, and `S⁻¹ = 0`); it represents a density only under `S.PosDef`. -/
noncomputable def gaussianLogDensity (m : EuclideanSpace ℝ (Fin p))
    (S : Matrix (Fin p) (Fin p) ℝ) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  -(p / 2 : ℝ) * Real.log (2 * Real.pi) - (1 / 2 : ℝ) * Real.log S.det
    - (1 / 2 : ℝ) * (WithLp.ofLp (x - m) ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp (x - m))

/-- The **observed-data log-likelihood contribution** of the normal factor model at a single
observation `x` (`BKM` Eq. (3.5) with Eq. (3.12)): the multivariate normal log density at the
structured covariance `Σ = Λ Φ Λᵀ + Ψ`. The latent factors are already integrated out — this
is not a complete-data likelihood. -/
noncomputable def factorLogLik (P : FactorParams p q) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  gaussianLogDensity P.μ (factorCovariance P) x

theorem factorLogLik_eq_gaussianLogDensity (P : FactorParams p q)
    (x : EuclideanSpace ℝ (Fin p)) :
    factorLogLik P x = gaussianLogDensity P.μ (factorCovariance P) x := rfl

/-- The **log-likelihood of an i.i.d. sample** `x₁, …, x_n` (`BKM` §3.4). -/
noncomputable def factorLogLikSample {n : ℕ} (P : FactorParams p q)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i, factorLogLik P (x i)

/-! ### The Lebesgue density of the multivariate Gaussian

`multivariateGaussian m S` is a pushforward of `stdGaussian`, and its classical Lebesgue
density is obtained in four steps:

1. `stdGaussian_eq_withDensity` — `stdGaussian (EuclideanSpace ℝ (Fin p))` is
   `volume.withDensity ((2π)^{-p/2} exp(−‖x‖²/2))`, obtained from the product form
   `map_pi_eq_stdGaussian` + `AsymptoticStatistics.pi_gaussianReal_eq_withDensity` (the
   one-dimensional `gaussianPDF` product) transported by `PiLp.volume_preserving_toLp`;
2. `multivariateGaussian_zero_eq_withDensity` — push through the invertible
   `toEuclideanLin (√S)`; the Jacobian is `Measure.map_linearMap_addHaar_eq_smul_addHaar`
   with `LinearMap.det (toEuclideanLin √S) = det √S = √(det S)`, and the exponent becomes
   the Mahalanobis form because `(√S)ᵀ S⁻¹ √S = 1`;
3. `multivariateGaussian_eq_withDensity` — translate to an arbitrary mean using
   translation invariance of `volume`;
4. `multivariateGaussian_eq_withDensity_exp_gaussianLogDensity` — rewrite the constant as
   `exp(−(p/2)log 2π − ½ log det S)`.

A likelihood needs the normalizing constant, so it is tracked explicitly throughout. -/

/-- The **standard Gaussian on `EuclideanSpace ℝ (Fin p)` has the classical Lebesgue
density** `(2π)^{-p/2} exp(−‖x‖²/2)`. -/
theorem stdGaussian_eq_withDensity (p : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin p))
      = volume.withDensity (fun x : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal
          ((Real.sqrt (2 * Real.pi))⁻¹ ^ p * Real.exp (-‖x‖ ^ 2 / 2))) := by
  classical
  set C : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ p with hC
  set hd : EuclideanSpace ℝ (Fin p) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (C * Real.exp (-‖y‖ ^ 2 / 2)) with hhd
  have hhdmeas : Measurable hd := by rw [hhd]; fun_prop
  have hpres : MeasurePreserving (WithLp.toLp 2 : (Fin p → ℝ) → EuclideanSpace ℝ (Fin p))
      (volume : Measure (Fin p → ℝ)) (volume : Measure (EuclideanSpace ℝ (Fin p))) :=
    PiLp.volume_preserving_toLp (Fin p)
  have hcomp : (hd ∘ (WithLp.toLp 2 : (Fin p → ℝ) → EuclideanSpace ℝ (Fin p)))
      = fun x : Fin p → ℝ => ∏ i, gaussianPDF 0 1 (x i) := by
    funext x
    have hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin p))‖ ^ 2 = ∑ i, x i ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    have hprod : ∏ i, gaussianPDFReal 0 1 (x i) = C * Real.exp (-(∑ i, x i ^ 2) / 2) := by
      have hterm : ∀ i : Fin p, gaussianPDFReal 0 1 (x i)
          = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x i ^ 2) / 2) := by
        intro i; simp [gaussianPDFReal]
      rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib,
        Finset.prod_const, ← Real.exp_sum, Finset.card_univ, hC]
      · congr 1
        · simp
        · rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
    simp only [Function.comp_apply, hhd, hnorm, gaussianPDF]
    rw [← hprod, ← ENNReal.ofReal_prod_of_nonneg]
    exact fun i _ => gaussianPDFReal_nonneg 0 1 (x i)
  rw [← map_pi_eq_stdGaussian, AsymptoticStatistics.pi_gaussianReal_eq_withDensity, ← hcomp,
    ← AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity _ _ hpres.measurable _
      hhdmeas, hpres.map_eq]

/-- The **centered multivariate Gaussian has the classical Lebesgue density** — the affine
change of variables `x ↦ √S x` applied to `stdGaussian_eq_withDensity`. -/
theorem multivariateGaussian_zero_eq_withDensity (p : ℕ) {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a singular covariance has no Lebesgue density at all
    (hS : S.PosDef) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S
      = volume.withDensity (fun x : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal
          ((Real.sqrt (2 * Real.pi))⁻¹ ^ p * (Real.sqrt S.det)⁻¹
            * Real.exp (-(WithLp.ofLp x ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp x) / 2))) := by
  classical
  have hQQ : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
  have hQpd : (CFC.sqrt S).PosDef := hS.isStrictlyPositive.sqrt.posDef
  have hQdetpos : 0 < (CFC.sqrt S).det := hQpd.det_pos
  have hQT : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hQpd.isHermitian
  have hQdet : (CFC.sqrt S).det = Real.sqrt S.det := by
    have hd : (CFC.sqrt S).det * (CFC.sqrt S).det = S.det := by rw [← Matrix.det_mul, hQQ]
    rw [← hd, Real.sqrt_mul_self hQdetpos.le]
  have hQunit : IsUnit (CFC.sqrt S).det := (Matrix.isUnit_iff_isUnit_det _).mp hQpd.isUnit
  have hSinv : S⁻¹ = (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹ := by rw [← Matrix.mul_inv_rev, hQQ]
  have hconj : (CFC.sqrt S)ᵀ * S⁻¹ * CFC.sqrt S = 1 := by
    rw [hQT, hSinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQunit, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hQunit]
  have hlindet : LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (CFC.sqrt S))
      = (CFC.sqrt S).det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hne : LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (CFC.sqrt S)) ≠ 0 := by
    rw [hlindet]; exact hQdetpos.ne'
  have hvolmap : (volume : Measure (EuclideanSpace ℝ (Fin p))).map
        (Matrix.toEuclideanLin (𝕜 := ℝ) (CFC.sqrt S))
      = ENNReal.ofReal |(LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (CFC.sqrt S)))⁻¹|
          • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne
  have hmeasT : Measurable (Matrix.toEuclideanLin (𝕜 := ℝ) (CFC.sqrt S)) :=
    ((Matrix.toEuclideanLin (𝕜 := ℝ)
      (CFC.sqrt S)).continuous_of_finiteDimensional).measurable
  have hgmeas : Measurable (fun y : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ p
        * Real.exp (-(WithLp.ofLp y ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp y) / 2))) := by fun_prop
  have hgT : (fun y : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ p
          * Real.exp (-(WithLp.ofLp y ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp y) / 2)))
      ∘ (Matrix.toEuclideanLin (𝕜 := ℝ) (CFC.sqrt S))
      = fun x : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal
          ((Real.sqrt (2 * Real.pi))⁻¹ ^ p * Real.exp (-‖x‖ ^ 2 / 2)) := by
    funext x
    have hof : WithLp.ofLp (Matrix.toEuclideanLin (𝕜 := ℝ) (CFC.sqrt S) x)
        = CFC.sqrt S *ᵥ WithLp.ofLp x := by simp [Matrix.toLpLin_apply]
    have hquad : (CFC.sqrt S *ᵥ WithLp.ofLp x) ⬝ᵥ S⁻¹ *ᵥ (CFC.sqrt S *ᵥ WithLp.ofLp x)
        = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
      rw [show (CFC.sqrt S *ᵥ WithLp.ofLp x) ⬝ᵥ S⁻¹ *ᵥ (CFC.sqrt S *ᵥ WithLp.ofLp x)
          = WithLp.ofLp x ⬝ᵥ ((CFC.sqrt S)ᵀ * S⁻¹ * CFC.sqrt S) *ᵥ WithLp.ofLp x from by
        rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.dotProduct_mulVec (WithLp.ofLp x) (CFC.sqrt S)ᵀ, Matrix.vecMul_transpose],
        hconj, Matrix.one_mulVec]
    have hnorm : ‖x‖ ^ 2 = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
      rw [EuclideanSpace.real_norm_sq_eq]; simp [dotProduct, sq]
    simp only [Function.comp_apply, hof, hquad, hnorm]
  have hmvg : multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S
      = (stdGaussian (EuclideanSpace ℝ (Fin p))).map
          (Matrix.toEuclideanLin (𝕜 := ℝ) (CFC.sqrt S)) := by
    rw [multivariateGaussian]
    congr 1
    funext x
    rw [zero_add]
    rfl
  rw [hmvg, stdGaussian_eq_withDensity p, ← hgT,
    ← AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity volume _ hmeasT _ hgmeas,
    hvolmap, hlindet, withDensity_smul_measure, ← withDensity_smul _ hgmeas]
  congr 1
  funext y
  have habs : |((CFC.sqrt S).det)⁻¹| = (Real.sqrt S.det)⁻¹ := by
    rw [abs_of_pos (by positivity), hQdet]
  simp only [Pi.smul_apply, smul_eq_mul, habs]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The **multivariate Gaussian has the classical Lebesgue density** at any mean. -/
theorem multivariateGaussian_eq_withDensity (p : ℕ) (m : EuclideanSpace ℝ (Fin p))
    {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a singular covariance has no Lebesgue density at all
    (hS : S.PosDef) :
    multivariateGaussian m S
      = volume.withDensity (fun x : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal
          ((Real.sqrt (2 * Real.pi))⁻¹ ^ p * (Real.sqrt S.det)⁻¹
            * Real.exp (-(WithLp.ofLp (x - m) ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp (x - m)) / 2))) := by
  classical
  have hshift : Measurable fun x : EuclideanSpace ℝ (Fin p) => m + x := by fun_prop
  have hhmeas : Measurable (fun x : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ p * (Real.sqrt S.det)⁻¹
        * Real.exp (-(WithLp.ofLp (x - m) ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp (x - m)) / 2))) := by
    fun_prop
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin p))).map (fun x => m + x) = volume :=
    (measurePreserving_add_left volume m).map_eq
  have hcomp : (fun x : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ p * (Real.sqrt S.det)⁻¹
          * Real.exp (-(WithLp.ofLp (x - m) ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp (x - m)) / 2)))
      ∘ (fun x : EuclideanSpace ℝ (Fin p) => m + x)
      = fun x : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal
          ((Real.sqrt (2 * Real.pi))⁻¹ ^ p * (Real.sqrt S.det)⁻¹
            * Real.exp (-(WithLp.ofLp x ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp x) / 2)) := by
    funext x
    simp only [Function.comp_apply, add_sub_cancel_left]
  have key := AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
    (volume : Measure (EuclideanSpace ℝ (Fin p))) (fun x => m + x) hshift _ hhmeas
  rw [hvol, hcomp] at key
  have hshiftlaw : multivariateGaussian m S
      = (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).map (fun x => m + x) := by
    rw [multivariateGaussian_map_const_add 0 S hS.posSemidef m, add_zero]
  rw [hshiftlaw, multivariateGaussian_zero_eq_withDensity p hS, ← key]

/-- **`N(m, S)` is `volume.withDensity (exp ∘ gaussianLogDensity m S)`** — the normal
Lebesgue density in log form, i.e. `gaussianLogDensity` really is a log density. -/
theorem multivariateGaussian_eq_withDensity_exp_gaussianLogDensity (p : ℕ)
    (m : EuclideanSpace ℝ (Fin p)) {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a singular covariance has no Lebesgue density at all
    (hS : S.PosDef) :
    multivariateGaussian m S
      = volume.withDensity (fun x : EuclideanSpace ℝ (Fin p) =>
          ENNReal.ofReal (Real.exp (gaussianLogDensity m S x))) := by
  rw [multivariateGaussian_eq_withDensity p m hS]
  congr 1
  funext x
  congr 1
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hdet : (0:ℝ) < S.det := hS.det_pos
  have hsqpi : Real.sqrt (2 * Real.pi) = Real.exp (Real.log (2 * Real.pi) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpi]; ring_nf
  have hsqdet : Real.sqrt S.det = Real.exp (Real.log S.det / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hdet]; ring_nf
  have h1 : (Real.sqrt (2 * Real.pi))⁻¹ ^ p
      = Real.exp (-(p / 2 : ℝ) * Real.log (2 * Real.pi)) := by
    rw [hsqpi, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  have h2 : (Real.sqrt S.det)⁻¹ = Real.exp (-((1 / 2 : ℝ) * Real.log S.det)) := by
    rw [hsqdet, ← Real.exp_neg]
    congr 1
    ring
  rw [h1, h2, gaussianLogDensity,
    show -(p / 2 : ℝ) * Real.log (2 * Real.pi) - (1 / 2 : ℝ) * Real.log S.det
        - (1 / 2 : ℝ) * (WithLp.ofLp (x - m) ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp (x - m))
      = (-(p / 2 : ℝ) * Real.log (2 * Real.pi)) + (-((1 / 2 : ℝ) * Real.log S.det))
        + (-(WithLp.ofLp (x - m) ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp (x - m)) / 2) from by ring,
    Real.exp_add, Real.exp_add]

/-- **The density theorem** — the observed law of the normal factor model has
`exp (factorLogLik P ·)` as its Lebesgue density, i.e. `factorLogLik` really is the
observed-data log-likelihood and not merely a formula named after one (`BKM` Eq. (3.5)). -/
theorem factorLaw_eq_withDensity_exp_factorLogLik (P : FactorParams p q)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hP : IsProperFactorParams P)
    -- USER-INPUT: nondegenerate observed covariance — a singular Σ has no Lebesgue
    -- density at all; BKM Eq. (3.5)
    (hSig : (factorCovariance P).PosDef) :
    factorLaw P (multivariateGaussian 0 P.factorCov) (multivariateGaussian 0 P.uniqueCov)
      = volume.withDensity fun x => ENNReal.ofReal (Real.exp (factorLogLik P x)) := by
  rw [factorLaw_multivariateGaussian P hP.1 hP.2]
  exact multivariateGaussian_eq_withDensity_exp_gaussianLogDensity p P.μ hSig

/-- The likelihood sees the parameters only through `(μ, Σ)` — definitional, and the reason
every invariance below is a one-line corollary. -/
theorem factorLogLik_congr (P P' : FactorParams p q)
    -- LEAN-ONLY: the two parameter tuples agree on the pair the density depends on;
    -- antecedent, no scope change
    (hμ : P.μ = P'.μ) (hSig : factorCovariance P = factorCovariance P')
    (x : EuclideanSpace ℝ (Fin p)) :
    factorLogLik P x = factorLogLik P' x := by
  rw [factorLogLik_eq_gaussianLogDensity, factorLogLik_eq_gaussianLogDensity, hμ, hSig]

/-- **HEADLINE — the likelihood is rotation invariant** (`BKM` §3.3, p. 50; §3.13.1): every
nonsingular reparameterization `Λ ↦ Λ A`, `Φ ↦ A⁻¹ Φ A⁻ᵀ` of the latent space leaves the
observed-data log-likelihood unchanged, because it leaves `Σ` unchanged. This is why maximum
likelihood determines `Λ` only up to rotation and why an identifying restriction
(`BKM`: `Λ′Ψ⁻¹Λ` diagonal) must be imposed. -/
theorem factorLogLik_rotateParams (P : FactorParams p q) {A : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: the reparameterization is a change of basis of the latent space;
    -- BKM §2.11
    (hA : IsUnit A.det) (x : EuclideanSpace ℝ (Fin p)) :
    factorLogLik (rotateParams P A) x = factorLogLik P x :=
  factorLogLik_congr (rotateParams P A) P rfl (factorCovariance_rotateParams P hA) x

/-- The sample log-likelihood inherits rotation invariance. -/
theorem factorLogLikSample_rotateParams {n : ℕ} (P : FactorParams p q)
    {A : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: the reparameterization is a change of basis of the latent space;
    -- BKM §2.11
    (hA : IsUnit A.det) (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    factorLogLikSample (rotateParams P A) x = factorLogLikSample P x :=
  Finset.sum_congr rfl fun i _ => factorLogLik_rotateParams P hA (x i)

/-- **Orthogonal rotations leave the likelihood unchanged** — the statement `BKM` §3.13.1
makes for standardized factors. -/
theorem factorLogLik_rotateParams_orthogonal (P : FactorParams p q)
    {Q : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: `Q` is orthogonal; BKM §2.11, Eq. (2.24)
    (hQ : Q * Qᵀ = 1) (x : EuclideanSpace ℝ (Fin p)) :
    factorLogLik (rotateParams P Q) x = factorLogLik P x :=
  factorLogLik_congr (rotateParams P Q) P rfl
    (factorCovariance_rotateParams_orthogonal P hQ) x

end StatLean.StatisticalModels.FactorModels
