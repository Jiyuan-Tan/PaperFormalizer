module
public import StatLean.HypothesisTesting.LikelihoodMethods.EstimatorUnderAlternatives

@[expose] public section

/-!
# The normalized score vector under local alternatives

Under quadratic-mean differentiability at `θ₀` the normalized score
`Zₙ = n^{-1/2} ∑_{i≤n} \tildeη_{θ₀}(Xᵢ)` is asymptotically `N(0, I(θ₀))` under `P^n_{θ₀}`.
Along a local alternative sequence `θₙ = θ₀ + hₙ/√n` with `hₙ → h` the limit is the *same
Gaussian shifted by* `I(θ₀)h`:
$$ Z_n \;\rightsquigarrow\; N\bigl(I(\theta_0)h,\; I(\theta_0)\bigr) \quad
   \text{under } P^n_{\theta_n}. $$
This is the exact statement that turns the score into a usable test statistic against local
alternatives: the alternative moves the mean of the limiting law by `I(θ₀)h` while leaving
the covariance unchanged, which is what makes the score test's local power computable.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 14 (Quadratic Mean
Differentiable Families), §14.4 (Likelihood Methods in Parametric Models), Corollary 14.4.1
(under local alternatives the normalized score vector converges to `N(I(θ₀)h, I(θ₀))`). (`TSH4
§14.4 Cor 14.4.1`.)

**Proof formalization notes.**
* The proof is the model application of Le Cam's third lemma. The area supplies every
  ingredient: `AsymptoticStatistics.AsymptoticRepresentation.contiguous_local_alternatives`
  for mutual contiguity of `P^n_{θ₀}` and `P^n_{θₙ}`;
  `AsymptoticStatistics.AsymptoticRepresentation.scoreSum_weakly_converges` and
  `joint_weak_conv_with_scoreSum` for the joint limit of `(Zₙ, log Lₙ,ₕ)` under `P^n_{θ₀}`;
  and then the third lemma itself, available in three shapes —
  `AsymptoticStatistics.Contiguity.weak_limit_under_Q_of_lecam_third` (exact log-ratio
  identity), `…_ennreal` (density form), and
  `…_of_integral_comparison` (asymptotic singular-mass control) — the last being the shape
  that avoids assuming a common support.
* The tilted limit produced by the third lemma is the Gaussian law with density
  proportional to `exp(⟪h, ·⟫)` against `N(0, I(θ₀))`, i.e. `N(I(θ₀)h, I(θ₀))`; the mean
  shift is the matrix action `mulVecE J h`.
* The theorem is proved by *specialising the estimator theorem*
  (`weak_limit_estimator_centered_under_local_alternatives`) to the canonical asymptotically
  linear estimator `θ̂ₙ = θ₀ + J⁻¹Zₙ/√n`, whose linearization remainder vanishes identically,
  and then pushing the limit `N(h, I⁻¹(θ₀))` forward by `J`: this gives
  `N(J h, J J⁻¹ Jᵀ) = N(J h, J)`.  The source's bare nonsingularity hypothesis is enough —
  positive definiteness of `J` is *derived* (`posSemidef_of_fisherInformation`), since the
  Fisher information bilinear form is automatically symmetric and nonnegative.
* Statements use the same score `ℓ` that certifies quadratic-mean differentiability, which
  is the area's convention for `\tildeη_{θ₀} = 2η(·,θ₀)/√p_{θ₀}`; no separate definition of
  the score vector is introduced here.

**Bibliographic comments.** The score statistic is due to C. R. Rao ("Large sample tests of
statistical hypotheses concerning several parameters with applications to problems of
estimation," *Proc. Camb. Phil. Soc.* **44** (1948), 50–57). The contiguity machinery that
delivers its limit law under local alternatives is due to L. Le Cam ("Locally asymptotically
normal families of distributions," *Univ. California Publ. Statist.* **3** (1960), 37–98),
with the quadratic-mean differentiability hypothesis from L. Le Cam ("On the assumptions
used to prove asymptotic normality of maximum likelihood estimates," *Ann. Math. Statist.*
**41** (1970), 802–828).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics AsymptoticStatistics.AsymptoticRepresentation
open scoped RealInnerProductSpace ENNReal

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}

/-- **The normalized score under local alternatives.**

If the model is differentiable in quadratic mean at `θ₀` with score `ℓ` and nonsingular
Fisher information matrix `J`, then along `θₙ = θ₀ + hₙ/√n` with `hₙ → h` the normalized
score sum satisfies `Zₙ ⇝ N(J·h, J)` under `P^n_{θₙ}`. -/
theorem weak_limit_scoreSum_under_local_alternatives
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF` through
    -- `productMeasure_isProbabilityMeasure`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable; the model is a density family
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the parameter at which quadratic-mean differentiability is assumed
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`
    (J : Matrix (Fin k) (Fin k) ℝ)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: the Fisher information matrix is nonsingular
    (hJ_inv : IsUnit J.det)
    -- USER-INPUT: the local direction and the converging sequence of directions
    (h : EuclideanSpace ℝ (Fin k)) (h_n : ℕ → EuclideanSpace ℝ (Fin k))
    (hconv : Tendsto h_n atTop (𝓝 h)) :
    WeakConverges
      (fun n => (productMeasure M μ (localAlt θ₀ h_n n) n).map (scoreSum ℓ n))
      (multivariateGaussian (mulVecE J h) J) := by
  classical
  -- The Fisher information is positive semidefinite, hence (being nonsingular) positive
  -- definite; this is needed to make the Gaussian pushforward lemmas non-vacuous.
  have hJ_psd : J.PosSemidef := posSemidef_of_fisherInformation M μ θ₀ ℓ J hJ
  have hJ_pd : J.PosDef :=
    hJ_psd.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det J).mpr hJ_inv)
  have hJinv_psd : J⁻¹.PosSemidef := hJ_pd.inv.posSemidef
  -- The canonical asymptotically linear estimator `θ̂ₙ = θ₀ + Vₙ/√n` with `Vₙ = J⁻¹Zₙ`: its
  -- linearization remainder is identically zero, so the estimator theorem applies to it and
  -- returns the law of `Vₙ` itself.
  set est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k) :=
    fun n ω => θ₀ + (Real.sqrt n)⁻¹ • mulVecE J⁻¹ (scoreSum ℓ n ω) with hestdef
  have hVmeas : ∀ n : ℕ, Measurable
      (fun ω : Fin n → 𝓧 => mulVecE J⁻¹ (scoreSum ℓ n ω)) := by
    intro n
    have hsum : Measurable (fun ω : Fin n → 𝓧 => ∑ i, ℓ (ω i)) :=
      Finset.univ.measurable_sum fun i _ => hℓ.comp (measurable_pi_apply i)
    exact (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹).continuous.measurable.comp
      (hsum.const_smul ((Real.sqrt (n : ℝ))⁻¹ : ℝ))
  have hest : ∀ n, Measurable (est n) := fun n =>
    ((hVmeas n).const_smul ((Real.sqrt (n : ℝ))⁻¹ : ℝ)).const_add θ₀
  -- The exact linearization identity, including the degenerate `n = 0` case.
  have hid : ∀ (n : ℕ) (ω : Fin n → 𝓧),
      Real.sqrt n • (est n ω - θ₀) = mulVecE J⁻¹ (scoreSum ℓ n ω) := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hz : scoreSum ℓ 0 ω = 0 := by
        simp [scoreSum]
      have hz' : mulVecE J⁻¹ (scoreSum ℓ 0 ω) = 0 := by
        rw [hz, mulVecE]
        exact map_zero (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹)
      simp [hestdef, hz']
    · have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
      simp only [hestdef, add_sub_cancel_left, smul_smul,
        mul_inv_cancel₀ (ne_of_gt hsq), one_smul]
  have hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est := by
    intro ε hε
    have hempty : ∀ n : ℕ, {ω : Fin n → 𝓧 |
        ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖} = ∅ := by
      intro n
      ext ω
      simp only [hid n ω, sub_self, norm_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_le]
      exact hε
    simp only [hempty, measureReal_empty]
    exact tendsto_const_nhds
  -- The estimator theorem, centred at `θ₀`, is exactly the limit law of `Vₙ`.
  have hVweak := weak_limit_estimator_centered_under_local_alternatives M μ hPDF θ₀ ℓ hℓ
    hDQM J hJ hJ_inv est hest hlin h h_n hconv
  have hVrw : (fun n : ℕ => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n • (est n ω - θ₀)))
      = fun n : ℕ => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => mulVecE J⁻¹ (scoreSum ℓ n ω)) := by
    funext n
    congr 1
    funext ω
    exact hid n ω
  rw [hVrw] at hVweak
  -- Apply `J` to recover the score sum itself.
  have hmap := hVweak.map (f := fun z : EuclideanSpace ℝ (Fin k) =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) J z)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) J).continuous
    (Matrix.toEuclideanCLM (𝕜 := ℝ) J).continuous.measurable
  rw [ProbabilityTheory.multivariateGaussian_map_toEuclideanCLM J h hJinv_psd] at hmap
  -- `J · J⁻¹ · Jᴴ = J`.
  have hcov : J * J⁻¹ * J.conjTranspose = J := by
    rw [Matrix.mul_nonsing_inv J hJ_inv, Matrix.one_mul]
    exact hJ_pd.isHermitian
  rw [hcov] at hmap
  -- `J (J⁻¹ Zₙ) = Zₙ`.
  have hcomp : (fun n : ℕ => ((productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => mulVecE J⁻¹ (scoreSum ℓ n ω))).map
        (fun z : EuclideanSpace ℝ (Fin k) => Matrix.toEuclideanCLM (𝕜 := ℝ) J z))
      = fun n : ℕ => (productMeasure M μ (localAlt θ₀ h_n n) n).map (scoreSum ℓ n) := by
    funext n
    rw [Measure.map_map (Matrix.toEuclideanCLM (𝕜 := ℝ) J).continuous.measurable (hVmeas n)]
    congr 1
    funext ω
    have hinv : Matrix.toEuclideanCLM (𝕜 := ℝ) J
        (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ (scoreSum ℓ n ω)) = scoreSum ℓ n ω := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, Matrix.mul_nonsing_inv J hJ_inv, map_one]
      rfl
    exact hinv
  rw [hcomp] at hmap
  exact hmap

end StatLean.HypothesisTesting
