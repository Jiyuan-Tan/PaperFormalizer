module
public import StatLean.HypothesisTesting.LikelihoodMethods.UniformLAN
public import StatLean.MultipleTesting.ForMathlib.ChiSquared
public import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# The likelihood trinity: Wald, score and likelihood ratio statistics

Three statistics test the same simple null `θ = θ₀` in an i.i.d. quadratic-mean
differentiable model with positive definite Fisher information `I(θ₀)`:

* the **Wald statistic** `Wₙ = n·(θ̂ₙ − θ₀)ᵀ I(θ₀) (θ̂ₙ − θ₀)`, built from an efficient
  estimator sequence;
* the **Rao score statistic** `Rₙ = Zₙᵀ I⁻¹(θ₀) Zₙ`, built from the normalized score and
  requiring no estimator at all;
* the **likelihood ratio statistic** `2 log Rₙ = 2[ℓₙ(θ̂ₙ) − ℓₙ(θ₀)]`.

They are asymptotically equivalent — pairwise differences vanish in probability — and each
converges in law to `χ²` with `k` degrees of freedom. For the composite null obtained by
restricting `θ` to an affine subspace of codimension `p`, the likelihood ratio statistic
formed from efficient estimators in the full and in the restricted model converges to `χ²`
with `p` degrees of freedom.

Beyond quadratic-mean differentiability, the likelihood ratio analysis needs the source's
additional second-order remainder condition
$$ \bigl|\log p_\theta(x) - \log p_{\theta_0}(x)
   - \langle\theta-\theta_0, \tilde\eta_{\theta_0}(x)\rangle\bigr| \le M(x)\|\theta-\theta_0\|^2,
   \qquad E_{\theta_0}[M(X)]<\infty, $$
for `θ` in a neighbourhood of `θ₀` — the source uses it to make the local expansion uniform
over bounded directions, and hence usable at the random direction `√n(θ̂ₙ − θ₀)`. (It is not
by itself sufficient for that uniformity: see the counterexample recorded at
`sup_LAN_remainder_tendsto` in `UniformLAN.lean`. Both likelihood-ratio statements below
therefore carry the *two-point* form of the condition, which is what the uniform expansion
actually consumes and which returns the printed one at `θ' = θ₀`.)

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 14 (Quadratic Mean
Differentiable Families), §14.4 (Likelihood Methods in Parametric Models), Theorem 14.4.2
(§14.4.2–14.4.4, Wald Tests, Rao Score Tests and Likelihood Ratio Tests): the three statistics
are asymptotically equivalent and chi-squared. (`TSH4 §14.4 Thm 14.4.2`.)

**Proof formalization notes.**
* *Hypotheses are assigned per statistic, not globally.* The source states the whole theorem
  under one set of standing assumptions; here the envelope condition is imposed only on the
  likelihood-ratio statements, which are the ones that consume it (through
  `sup_LAN_remainder_tendsto`). The score and Wald limits follow from quadratic-mean
  differentiability, the score central limit theorem and the assumed expansion alone.
* The efficient estimator sequence is never constructed: it is data, constrained by
  `IsAsymptoticallyLinear`, exactly as in the source, where maximum likelihood estimators
  and one-step estimators are cited as examples but the expansion is what is assumed.
* The Wald statistic is normalized by `I(θ₀)` rather than by `I(θ̂ₙ)`. The source notes the
  two versions are interchangeable ("`I(θ̂ₙ)` may be replaced by `I(θ₀)` or any consistent
  estimator"); the fixed-matrix form avoids carrying a consistency hypothesis on a plug-in
  estimator of the information matrix.
* The composite null is presented as the affine subspace `a + range B` with `B` an injective
  linear map from a space of dimension `m`. This is exactly the solution set of
  `A(θ − a) = 0` for a `p × k` matrix `A` of rank `p = k − m`, and it lets the restricted
  model be an honest `ParametricFamily` in the chart `β`, so that "efficient estimator
  assuming the null" is the *same* predicate `IsAsymptoticallyLinear` applied to the
  restricted model rather than a new, unverified formula for its influence function.
* The smooth-constraint version of the composite case (null `{θ | g(θ) = 0}` with a
  continuously differentiable `g : ℝᵏ → ℝᵖ` whose Jacobian has rank `p`) is not stated
  separately: at `θ₀` it is the affine statement in the chart supplied by the implicit
  function theorem, with the same `p` degrees of freedom, and stating it independently would
  duplicate that reduction rather than add content.

**Bibliographic comments.** The three statistics are due to A. Wald ("Tests of statistical
hypotheses concerning several parameters when the number of observations is large," *Trans.
Amer. Math. Soc.* **54** (1943), 426–482), C. R. Rao ("Large sample tests of statistical
hypotheses concerning several parameters with applications to problems of estimation,"
*Proc. Camb. Phil. Soc.* **44** (1948), 50–57) and S. S. Wilks ("The large-sample
distribution of the likelihood ratio for testing composite hypotheses," *Ann. Math.
Statist.* **9** (1938), 60–62). The modern proof, which replaces classical
third-derivative conditions by quadratic-mean differentiability and contiguity, is due to
L. Le Cam ("Locally asymptotically normal families of distributions," *Univ. California
Publ. Statist.* **3** (1960), 37–98; "On the assumptions used to prove asymptotic normality
of maximum likelihood estimates," *Ann. Math. Statist.* **41** (1970), 802–828).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics AsymptoticStatistics.AsymptoticRepresentation
open scoped RealInnerProductSpace ENNReal Matrix BoundedContinuousFunction MatrixOrder

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}

/-! ## The three statistics -/

/-- The **Wald statistic** `Wₙ = n·⟪θ̂ₙ − θ₀, I(θ₀)(θ̂ₙ − θ₀)⟫` for the simple null
`θ = θ₀`, with the information matrix evaluated at the null value.

Edge behaviour: at `n = 0` the statistic is `0`. -/
noncomputable def waldStatistic (J : Matrix (Fin k) (Fin k) ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) : ℝ :=
  (n : ℝ) * ⟪est n ω - θ₀, mulVecE J (est n ω - θ₀)⟫

/-- The **Rao score statistic** `Rₙ = ⟪Zₙ, I⁻¹(θ₀)Zₙ⟫`, a quadratic form in the normalized
score sum. It uses no estimator of the parameter.

Edge behaviour: at `n = 0` the empty score sum vanishes, so the statistic is `0`. -/
noncomputable def scoreStatistic (J : Matrix (Fin k) (Fin k) ℝ)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) : ℝ :=
  ⟪scoreSum ℓ n ω, mulVecE J⁻¹ (scoreSum ℓ n ω)⟫

/-- The **likelihood ratio statistic** `2 log(Lₙ(θ̂ₙ)/Lₙ(θ̂ₙ,₀))` for a pair of estimator
sequences: twice the difference of the log-likelihoods at the unrestricted and restricted
estimates. The simple null `θ = θ₀` is the case of the constant restricted sequence.

Edge behaviour: densities enter through their ratio, so points where both densities vanish
contribute `Real.log (0/0) = 0`; at `n = 0` the statistic is `0`. -/
noncomputable def logLRStatistic (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (est est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (ω : Fin n → 𝓧) : ℝ :=
  2 * ∑ i, Real.log (M.density (est n ω) (ω i) / M.density (est₀ n ω) (ω i))

/-- The **affinely restricted model** `β ↦ P_{a + Bβ}`: the model reparametrized by a chart
of the affine null subspace `a + range B`. Densities, their measurability and their
nonnegativity are inherited pointwise from the full model. -/
noncomputable def restrictFamily {m : ℕ} (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin m)) where
  density := fun β x => M.density (a + B β) x
  density_meas := fun β => M.density_meas (a + B β)
  density_nonneg := fun β x => M.density_nonneg (a + B β) x

/-- **Differentiability in quadratic mean is inherited by an affine reparametrization.**
If `M` is DQM at `θ₀ = a + Bβ₀` with score `ℓ`, then the affinely restricted model is DQM at
`β₀` with score `B*ℓ`.

The residual of the restricted model in the direction `u` is *literally* the residual of `M`
in the direction `B u` — the parameters agree, `a + B(β₀ + u) = θ₀ + B u`, and
`⟪u, B*(ℓ x)⟫ = ⟪B u, ℓ x⟫` — so both clauses of `DifferentiableQuadraticMean` transport along
`B`: the `L²`-membership because `B` is continuous at `0`, and the rate because
`‖B u‖² ≤ ‖B‖²‖u‖²`. -/
lemma differentiableQuadraticMean_restrictFamily {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (β₀ : EuclideanSpace ℝ (Fin m)) (hθ₀ : θ₀ = a + B β₀)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (hℓB : ℓB = fun x => ContinuousLinearMap.adjoint B (ℓ x))
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) :
    DifferentiableQuadraticMean (restrictFamily M a B) μ β₀ ℓB := by
  -- The residual of the restricted model at `u` is the residual of `M` at `B u`.
  have hres : ∀ (u : EuclideanSpace ℝ (Fin m)) (x : 𝓧),
      (restrictFamily M a B).sqrtDensity (β₀ + u) x - (restrictFamily M a B).sqrtDensity β₀ x
          - (1 / 2 : ℝ) * ⟪u, ℓB x⟫ * (restrictFamily M a B).sqrtDensity β₀ x
        = M.sqrtDensity (θ₀ + B u) x - M.sqrtDensity θ₀ x
          - (1 / 2 : ℝ) * ⟪B u, ℓ x⟫ * M.sqrtDensity θ₀ x := by
    intro u x
    have h1 : a + B (β₀ + u) = θ₀ + B u := by rw [hθ₀, map_add]; abel
    have h2 : a + B β₀ = θ₀ := hθ₀.symm
    have h3 : ⟪u, ℓB x⟫ = ⟪B u, ℓ x⟫ := by
      rw [hℓB, real_inner_comm, ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
    simp only [restrictFamily, ParametricFamily.sqrtDensity, h1, h2, h3]
  -- `B` is continuous at the origin, so a neighbourhood condition transports.
  have htend : Filter.Tendsto (fun u : EuclideanSpace ℝ (Fin m) => B u)
      (𝓝 0) (𝓝 (0 : EuclideanSpace ℝ (Fin k))) := by
    have := B.continuous.tendsto (0 : EuclideanSpace ℝ (Fin m))
    simpa using this
  refine ⟨?_, ?_⟩
  · filter_upwards [htend.eventually hDQM.mem] with u hu
    simpa only [hres u] using hu
  · have hcomp := hDQM.isLittleO.comp_tendsto htend
    have hbig : (fun u : EuclideanSpace ℝ (Fin m) => ‖B u‖ ^ 2)
        =O[𝓝 (0 : EuclideanSpace ℝ (Fin m))] fun u => ‖u‖ ^ 2 := by
      refine Asymptotics.IsBigO.of_bound (‖B‖ ^ 2) (Filter.Eventually.of_forall fun u => ?_)
      have hle : ‖B u‖ ≤ ‖B‖ * ‖u‖ := B.le_opNorm u
      have hsq : ‖B u‖ ^ 2 ≤ (‖B‖ * ‖u‖) ^ 2 := by
        nlinarith [norm_nonneg (B u), hle]
      calc ‖‖B u‖ ^ 2‖ = ‖B u‖ ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ (‖B‖ * ‖u‖) ^ 2 := hsq
        _ = ‖B‖ ^ 2 * ‖‖u‖ ^ 2‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    have hfun : (fun u : EuclideanSpace ℝ (Fin m) =>
        ∫ x, ((restrictFamily M a B).sqrtDensity (β₀ + u) x
              - (restrictFamily M a B).sqrtDensity β₀ x
              - (1 / 2 : ℝ) * ⟪u, ℓB x⟫ * (restrictFamily M a B).sqrtDensity β₀ x) ^ 2 ∂μ)
        = fun u => ∫ x, (M.sqrtDensity (θ₀ + B u) x - M.sqrtDensity θ₀ x
              - (1 / 2 : ℝ) * ⟪B u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
      funext u
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hres u x])
    rw [hfun]
    simpa [Function.comp] using! hcomp.trans_isBigO hbig

/-! ## Algebraic, measurability and tightness helpers -/

/-- The matrix action `mulVecE J` is the application of the continuous linear map
`Matrix.toEuclideanCLM J`; the two spellings are definitionally equal. -/
private lemma mulVecE_eq_toEuclideanCLM (J : Matrix (Fin k) (Fin k) ℝ)
    (v : EuclideanSpace ℝ (Fin k)) :
    mulVecE J v = Matrix.toEuclideanCLM (𝕜 := ℝ) J v := rfl

/-- Continuity of the quadratic form `z ↦ ⟪z, A·z⟫` on `EuclideanSpace ℝ (Fin k)`; the matrix
action `mulVecE A` is definitionally `AsymptoticStatistics.GaussianShift.matrixAction A`, so
its continuity is inherited. -/
private lemma continuous_gaussQuadratic (A : Matrix (Fin k) (Fin k) ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin k) => ⟪z, mulVecE A z⟫) :=
  continuous_id.inner (GaussianShift.matrixAction_continuous A)

/-- Measurability of the normalized score sum. -/
private lemma measurable_scoreSum (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (n : ℕ) : Measurable (scoreSum ℓ n) := by
  unfold scoreSum
  exact (Finset.measurable_sum Finset.univ
    (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul (Real.sqrt n)⁻¹

/-- **Gaussian quadratic form is chi-squared.** For a positive-definite `k×k` matrix `J`
(`k > 0`), the pushforward of `N(0, J)` under the quadratic form `z ↦ ⟪z, J⁻¹ z⟫` is the
`χ²ₖ` distribution — the exact distributional identity `Zᵀ J⁻¹ Z ∼ χ²ₖ` for `Z ∼ N(0, J)`,
supplied by the whitening bridge of `ForMathlib/NoncentralChiSquared.lean`. -/
private lemma multivariateGaussian_map_quadratic_eq_chiSquared
    (hk : 0 < k) (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef) :
    (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
        (fun z => ⟪z, mulVecE J⁻¹ z⟫) = MultipleTesting.chiSquared k :=
  multivariateGaussian_map_inner_inv_eq_chiSquared hk hJ_pd

/-- The matrix action `mulVecE J` is `ℝ`-linear in its vector argument (scalar homogeneity). -/
private lemma mulVecE_smul (J : Matrix (Fin k) (Fin k) ℝ) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin k)) : mulVecE J (c • v) = c • mulVecE J v := by
  change Matrix.toEuclideanCLM (𝕜 := ℝ) J (c • v) = c • Matrix.toEuclideanCLM (𝕜 := ℝ) J v
  rw [map_smul]

/-- `J·(J⁻¹ z) = z` for a nonsingular `J`: `Matrix.toEuclideanCLM` is a `⋆`-algebra map, so
it carries `J * J⁻¹ = 1` to the identity operator. -/
private lemma mulVecE_mulVecE_inv (J : Matrix (Fin k) (Fin k) ℝ) (hdet : IsUnit J.det)
    (z : EuclideanSpace ℝ (Fin k)) : mulVecE J (mulVecE J⁻¹ z) = z := by
  rw [mulVecE_eq_toEuclideanCLM, mulVecE_eq_toEuclideanCLM,
    ← ContinuousLinearMap.mul_apply, ← map_mul, Matrix.mul_nonsing_inv J hdet, map_one]
  rfl

omit [MeasurableSpace 𝓧] in
/-- The Wald statistic is the quadratic form `⟪·, J ·⟫` evaluated at the normalized deviation
`√n·(θ̂ₙ − θ₀)`: `Wₙ = ⟪√n(θ̂ₙ−θ₀), J √n(θ̂ₙ−θ₀)⟫`. The two `√n` factors collapse the `n` in
front of the definition. -/
private lemma waldStatistic_eq_quadratic (J : Matrix (Fin k) (Fin k) ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) :
    waldStatistic J θ₀ est n ω
      = ⟪Real.sqrt n • (est n ω - θ₀), mulVecE J (Real.sqrt n • (est n ω - θ₀))⟫ := by
  unfold waldStatistic
  rw [mulVecE_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    Real.mul_self_sqrt (Nat.cast_nonneg n)]

omit [MeasurableSpace 𝓧] in
/-- The Rao score statistic is the *same* quadratic form `⟪·, J ·⟫` evaluated at
`Vₙ = J⁻¹Zₙ`: `Rₙ = ⟪Zₙ, J⁻¹Zₙ⟫ = ⟪J⁻¹Zₙ, J J⁻¹Zₙ⟫`. This is what puts the Wald and the
score statistic on a common footing. -/
private lemma scoreStatistic_eq_quadratic (J : Matrix (Fin k) (Fin k) ℝ) (hdet : IsUnit J.det)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) :
    scoreStatistic J ℓ n ω
      = ⟪mulVecE J⁻¹ (scoreSum ℓ n ω), mulVecE J (mulVecE J⁻¹ (scoreSum ℓ n ω))⟫ := by
  rw [mulVecE_mulVecE_inv J hdet, real_inner_comm]
  rfl

omit [MeasurableSpace 𝓧] in
/-- A Hermitian matrix acts as a self-adjoint operator. -/
private lemma inner_mulVecE_comm {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.IsHermitian)
    (x y : EuclideanSpace ℝ (Fin k)) : ⟪mulVecE A x, y⟫ = ⟪x, mulVecE A y⟫ := by
  rw [real_inner_comm, mulVecE_eq_toEuclideanCLM, mulVecE_eq_toEuclideanCLM,
    Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  have hAt : Aᵀ = A := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hAt, dotProduct_comm]

/-- Polarization of the difference of two values of the quadratic form `q(z) = ⟪z, J z⟫`:
`q(u) − q(v) = ⟪u−v, J u⟫ + ⟪v, J(u−v)⟫`, bilinear in the increment `u − v`. -/
private lemma inner_mulVecE_quadratic_sub (J : Matrix (Fin k) (Fin k) ℝ)
    (u v : EuclideanSpace ℝ (Fin k)) :
    ⟪u, mulVecE J u⟫ - ⟪v, mulVecE J v⟫
      = ⟪u - v, mulVecE J u⟫ + ⟪v, mulVecE J (u - v)⟫ := by
  have h : mulVecE J (u - v) = mulVecE J u - mulVecE J v := by
    rw [mulVecE_eq_toEuclideanCLM, mulVecE_eq_toEuclideanCLM, mulVecE_eq_toEuclideanCLM,
      map_sub]
  rw [h, inner_sub_left, inner_sub_right]
  ring

/-- The quantitative form of the previous lemma: the quadratic form is Lipschitz on bounded
sets, with the operator norm of `J` as constant. -/
private lemma abs_inner_mulVecE_quadratic_sub_le (J : Matrix (Fin k) (Fin k) ℝ)
    (u v : EuclideanSpace ℝ (Fin k)) :
    |⟪u, mulVecE J u⟫ - ⟪v, mulVecE J v⟫|
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * ‖u - v‖ * (‖u‖ + ‖v‖) := by
  set C := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ with hC
  have hop : ∀ w : EuclideanSpace ℝ (Fin k), ‖mulVecE J w‖ ≤ C * ‖w‖ := by
    intro w
    rw [mulVecE_eq_toEuclideanCLM]
    exact ContinuousLinearMap.le_opNorm _ w
  have h1 : |⟪u - v, mulVecE J u⟫| ≤ ‖u - v‖ * (C * ‖u‖) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hop u) (norm_nonneg _))
  have h2 : |⟪v, mulVecE J (u - v)⟫| ≤ ‖v‖ * (C * ‖u - v‖) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hop (u - v)) (norm_nonneg _))
  calc |⟪u, mulVecE J u⟫ - ⟪v, mulVecE J v⟫|
      = |⟪u - v, mulVecE J u⟫ + ⟪v, mulVecE J (u - v)⟫| := by
        rw [inner_mulVecE_quadratic_sub]
    _ ≤ |⟪u - v, mulVecE J u⟫| + |⟪v, mulVecE J (u - v)⟫| := abs_add_le _ _
    _ ≤ ‖u - v‖ * (C * ‖u‖) + ‖v‖ * (C * ‖u - v‖) := add_le_add h1 h2
    _ = C * ‖u - v‖ * (‖u‖ + ‖v‖) := by ring

/-- **The efficient-influence vector `Vₙ = J⁻¹Zₙ` is asymptotically `N(0, J⁻¹)`.** The score
central limit theorem gives `Zₙ ⇝ N(0, J)`; applying the linear map `J⁻¹` and using
`J⁻¹ J (J⁻¹)ᴴ = J⁻¹` turns this into the stated limit. -/
private lemma scoreSum_mulVecE_inv_weakConverges
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (fun ω => mulVecE J⁻¹ (scoreSum ℓ n ω)))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
  have hScore : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    scoreSum_weakly_converges M μ θ₀ ℓ hℓ (hPDF.density_integral_eq_one θ₀)
      (hPDF.density_integrable θ₀)
      (fun t u => hPDF.density_integral_eq_one _) (fun t u => hPDF.density_integrable _)
      hDQM J hJ_pd.posSemidef hJ
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ_pd.isUnit
  have hpush : (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
      (GaussianShift.matrixAction J⁻¹)
      = ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹ := by
    have hfun : GaussianShift.matrixAction J⁻¹
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ :
            EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) :=
      funext (GaussianShift.matrixAction_eq_toEuclideanCLM J⁻¹)
    rw [hfun, ProbabilityTheory.multivariateGaussian_map_toEuclideanCLM J⁻¹ 0
      hJ_pd.posSemidef]
    have hHerm : J⁻¹ᴴ = J⁻¹ := hJ_pd.inv.isHermitian
    congr 1
    · simp
    · rw [hHerm, Matrix.nonsing_inv_mul J hdet, Matrix.one_mul]
  have hmap := hScore.map (GaussianShift.matrixAction_continuous J⁻¹)
    (GaussianShift.matrixAction_measurable J⁻¹)
  rw [hpush] at hmap
  have hseqV : (fun n => (productMeasure M μ θ₀ n).map
      (fun ω => mulVecE J⁻¹ (scoreSum ℓ n ω)))
      = (fun n => ((productMeasure M μ θ₀ n).map (scoreSum ℓ n)).map
          (GaussianShift.matrixAction J⁻¹)) := by
    funext n
    rw [Measure.map_map (GaussianShift.matrixAction_measurable J⁻¹)
      (measurable_scoreSum ℓ hℓ n)]
    rfl
  rw [hseqV]; exact hmap

/-! ## Asymptotic equivalence and the chi-squared limits -/

/-- **Measurability of the likelihood-ratio statistic.** For measurable estimator sequences and
a jointly measurable density, the map `ω ↦ 2 ∑ᵢ log(p_{θ̂}(ωᵢ)/p_{θ̂₀}(ωᵢ))` is measurable.

The hypothesis `hjoint` is *not* redundant: the `ParametricFamily` structure records only
per-`θ` measurability (`density_meas : ∀ θ, Measurable (density θ)`), and that is genuinely
too weak here.  Take `𝓧 = ℝ` with `μ` Lebesgue measure, `S ⊆ [0,1]` nonmeasurable, and
`p_θ = 1_{[0,1]} + 1_{\{f θ\}}` where `f θ = θ` for `θ ∈ S` and `f θ = θ + 1` otherwise.  Each
`p_θ` is Borel measurable (it differs from `1_{[0,1]}` on one point) and every `p_θ`
integrates to `1`, so all the frozen hypotheses hold; but for `n = 1` and the measurable
estimator `est 1 ω = ω 0` the statistic equals `2 log 2 · 1_S(ω 0)` on `[0,1]`, which is not
measurable.  Joint measurability of `(θ, x) ↦ p_θ(x)` is therefore forced, and it is the
standard regularity assumption (Carathéodory measurability) under which the source works. -/
private lemma measurable_logLRStatistic
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (hjoint : Measurable (Function.uncurry M.density))
    (est est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n)) (hest₀ : ∀ n, Measurable (est₀ n)) (n : ℕ) :
    Measurable (logLRStatistic M est est₀ n) := by
  unfold logLRStatistic
  refine Measurable.const_mul (Finset.univ.measurable_sum fun i _ => ?_) 2
  refine Measurable.log (Measurable.div ?_ ?_)
  · exact hjoint.comp ((hest n).prodMk (measurable_pi_apply i))
  · exact hjoint.comp ((hest₀ n).prodMk (measurable_pi_apply i))

/-- **Wald − score is `o_P(1)`.** Under `P^n_{θ₀}` the Wald and Rao score statistics differ by a
quantity tending to zero in probability.

Writing `Uₙ = √n(θ̂ₙ−θ₀)` and `Vₙ = J⁻¹Zₙ`, one has `Wₙ = ⟪Uₙ, J Uₙ⟫` and `Rₙ = ⟪Vₙ, J Vₙ⟫`
(`waldStatistic_eq_quadratic`, `scoreStatistic_eq_quadratic`), so `Wₙ − Rₙ` is the bilinear
remainder `⟪Uₙ−Vₙ, J Uₙ⟫ + ⟪Vₙ, J(Uₙ−Vₙ)⟫`, bounded by `‖J‖·‖Uₙ−Vₙ‖·(‖Uₙ‖+‖Vₙ‖)`.
`IsAsymptoticallyLinear` makes `‖Uₙ−Vₙ‖` small in probability, and the score CLT makes `Vₙ`
tight (`exists_radius_eventually_measureReal_norm_le`); the event `{ε ≤ |Wₙ − Rₙ|}` is
therefore contained in `{η ≤ ‖Uₙ−Vₙ‖} ∪ {K ≤ ‖Vₙ‖}` for a suitable `η`, and subadditivity
of the measure finishes.  No LAN expansion is used. -/
private lemma wald_sub_score_tendstoInMeasure
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω|})
        atTop (𝓝 0) := by
  intro ε hε
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ_pd.isUnit
  set C : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ with hCdef
  have hC0 : 0 ≤ C := norm_nonneg _
  have hVmeas : ∀ n, Measurable (fun ω : Fin n → 𝓧 => mulVecE J⁻¹ (scoreSum ℓ n ω)) :=
    fun n => (GaussianShift.matrixAction_measurable J⁻¹).comp (measurable_scoreSum ℓ hℓ n)
  have hV := scoreSum_mulVecE_inv_weakConverges M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro α hα
  obtain ⟨K, hK0, hKev⟩ :=
    exists_radius_eventually_measureReal_norm_le hVmeas hV (α := α / 4) (by positivity)
  -- The tolerance on `‖Uₙ − Vₙ‖` that makes the bilinear remainder smaller than `ε`.
  have hD : (0 : ℝ) < C * (1 + 2 * K) + 1 := by positivity
  set η : ℝ := min 1 (ε / (C * (1 + 2 * K) + 1)) with hηdef
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηlt : C * η * (η + 2 * K) < ε := by
    have h1 : η * (C * (1 + 2 * K) + 1) ≤ ε := by
      rw [← le_div_iff₀ hD]; exact min_le_right _ _
    have h2 : C * η * (η + 2 * K) ≤ C * η * (1 + 2 * K) := by
      have hCη : (0 : ℝ) ≤ C * η := mul_nonneg hC0 hη0.le
      nlinarith
    nlinarith
  -- The bad event splits into a "linearization failed" part and a "score is large" part.
  have hincl : ∀ n : ℕ,
      {ω : Fin n → 𝓧 | ε ≤ |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω|}
        ⊆ {ω : Fin n → 𝓧 |
              η ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖}
            ∪ {ω : Fin n → 𝓧 | K ≤ ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖} := by
    intro n ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hkey : |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω| < ε := by
      rw [waldStatistic_eq_quadratic J θ₀ est n ω, scoreStatistic_eq_quadratic J hdet ℓ n ω]
      refine lt_of_le_of_lt
        (abs_inner_mulVecE_quadratic_sub_le J (Real.sqrt n • (est n ω - θ₀))
          (mulVecE J⁻¹ (scoreSum ℓ n ω))) ?_
      have hu : ‖Real.sqrt n • (est n ω - θ₀)‖ ≤ η + K := by
        have hsplit := norm_le_norm_add_norm_sub' (Real.sqrt n • (est n ω - θ₀))
          (mulVecE J⁻¹ (scoreSum ℓ n ω))
        linarith [h1.le, h2.le]
      refine lt_of_le_of_lt ?_ hηlt
      have hnn : (0 : ℝ) ≤ ‖Real.sqrt n • (est n ω - θ₀)
          - mulVecE J⁻¹ (scoreSum ℓ n ω)‖ := norm_nonneg _
      have hVn : (0 : ℝ) ≤ ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖ := norm_nonneg _
      have hsum : ‖Real.sqrt n • (est n ω - θ₀)‖ + ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖
          ≤ η + 2 * K := by linarith [h2.le]
      have hprod : C * ‖Real.sqrt n • (est n ω - θ₀)
          - mulVecE J⁻¹ (scoreSum ℓ n ω)‖ ≤ C * η :=
        mul_le_mul_of_nonneg_left h1.le hC0
      have hnonneg : (0 : ℝ) ≤ ‖Real.sqrt n • (est n ω - θ₀)‖
          + ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖ := by positivity
      calc C * ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖
              * (‖Real.sqrt n • (est n ω - θ₀)‖ + ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖)
          ≤ (C * η) * (‖Real.sqrt n • (est n ω - θ₀)‖
              + ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖) := by
            exact mul_le_mul_of_nonneg_right hprod hnonneg
        _ ≤ (C * η) * (η + 2 * K) :=
            mul_le_mul_of_nonneg_left hsum (mul_nonneg hC0 hη0.le)
    exact absurd hω (not_le.2 hkey)
  -- Subadditivity, then the two eventual bounds.
  have hmono : ∀ n : ℕ,
      (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 | ε ≤ |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω|}
        ≤ (productMeasure M μ θ₀ n).real
              {ω : Fin n → 𝓧 |
                η ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖}
            + (productMeasure M μ θ₀ n).real
              {ω : Fin n → 𝓧 | K ≤ ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖} := fun n =>
    (measureReal_mono (hincl n) (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  filter_upwards [(hlin η hη0).eventually_lt_const (u := α / 4) (by positivity), hKev]
    with n h1 h2
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  have := hmono n
  linarith

omit [MeasurableSpace 𝓧] in
/-- **Twice the quadratic form, polarized.**

`2(⟪u, J v⟫ − ½⟪u, J u⟫) − ⟪v, J v⟫ = −⟪u − v, J(u − v)⟫` for a Hermitian `J`. This is the
algebraic core of the likelihood-ratio/score comparison: substituting `ĥₙ = J⁻¹Zₙ + o_P(1)`
into the LAN quadratic collapses it to the score statistic, with a *negative-definite*
error that is quadratic in the linearization gap. -/
private lemma two_inner_mulVecE_polarize {J : Matrix (Fin k) (Fin k) ℝ} (hHerm : J.IsHermitian)
    (u v : EuclideanSpace ℝ (Fin k)) :
    2 * (⟪u, mulVecE J v⟫ - (1 / 2 : ℝ) * ⟪u, mulVecE J u⟫) - ⟪v, mulVecE J v⟫
      = -⟪u - v, mulVecE J (u - v)⟫ := by
  have hmap : mulVecE J (u - v) = mulVecE J u - mulVecE J v := by
    rw [mulVecE_eq_toEuclideanCLM, mulVecE_eq_toEuclideanCLM, mulVecE_eq_toEuclideanCLM,
      map_sub]
  have hsymm : ⟪v, mulVecE J u⟫ = ⟪u, mulVecE J v⟫ := by
    rw [← inner_mulVecE_comm hHerm v u, real_inner_comm]
  rw [hmap, inner_sub_left, inner_sub_right, inner_sub_right, hsymm]
  ring

/-- **The likelihood-ratio statistic in terms of the LAN remainder.**

For `n ≥ 1`, writing `ĥₙ = √n(θ̂ₙ − θ₀)` (so that `θ₀ + ĥₙ/√n = θ̂ₙ` exactly) and
`Vₙ = J⁻¹Zₙ`,
`2 log(Lₙ(θ̂ₙ)/Lₙ(θ₀)) − Rₙ = 2·lanRemainder(ĥₙ) − ⟪ĥₙ − Vₙ, J(ĥₙ − Vₙ)⟫`.
Both terms on the right are small in probability: the first by the uniform LAN expansion
(`sup_LAN_remainder_tendsto`), the second because `ĥₙ − Vₙ →_P 0`. -/
private lemma logLRStatistic_sub_scoreStatistic_eq
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (J : Matrix (Fin k) (Fin k) ℝ)
    (hdet : IsUnit J.det) (hHerm : J.IsHermitian)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (n : ℕ) (hn : 1 ≤ n)
    (ω : Fin n → 𝓧) :
    logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω
      = 2 * lanRemainder M θ₀ ℓ J (Real.sqrt n • (est n ω - θ₀)) n ω
        - ⟪Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω),
            mulVecE J (Real.sqrt n • (est n ω - θ₀)
              - mulVecE J⁻¹ (scoreSum ℓ n ω))⟫ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnpos
  -- `θ₀ + ĥₙ/√n` is exactly the estimator.
  have hθ : θ₀ + (Real.sqrt n)⁻¹ • (Real.sqrt n • (est n ω - θ₀)) = est n ω := by
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hsq), one_smul]
    abel
  -- The log-likelihood ratio statistic is twice the LAN log-likelihood at `ĥₙ`.
  have hlog : logLRStatistic M est (fun _ _ => θ₀) n ω
      = 2 * logLikelihood M θ₀ (Real.sqrt n • (est n ω - θ₀)) n ω := by
    simp only [logLRStatistic, logLikelihood, hθ]
  -- The score sum is `J Vₙ`.
  have hZ : scoreSum ℓ n ω = mulVecE J (mulVecE J⁻¹ (scoreSum ℓ n ω)) :=
    (mulVecE_mulVecE_inv J hdet _).symm
  have hscore : scoreStatistic J ℓ n ω
      = ⟪mulVecE J⁻¹ (scoreSum ℓ n ω), mulVecE J (mulVecE J⁻¹ (scoreSum ℓ n ω))⟫ :=
    scoreStatistic_eq_quadratic J hdet ℓ n ω
  have hpol := two_inner_mulVecE_polarize hHerm (Real.sqrt n • (est n ω - θ₀))
    (mulVecE J⁻¹ (scoreSum ℓ n ω))
  have hlan : logLikelihood M θ₀ (Real.sqrt n • (est n ω - θ₀)) n ω
      = lanRemainder M θ₀ ℓ J (Real.sqrt n • (est n ω - θ₀)) n ω
        + (⟪Real.sqrt n • (est n ω - θ₀), scoreSum ℓ n ω⟫
            - (1 / 2 : ℝ) * ⟪Real.sqrt n • (est n ω - θ₀),
                mulVecE J (Real.sqrt n • (est n ω - θ₀))⟫) := by
    simp only [lanRemainder]
    ring
  rw [hlog, hlan, hscore]
  rw [show ⟪Real.sqrt n • (est n ω - θ₀), scoreSum ℓ n ω⟫
      = ⟪Real.sqrt n • (est n ω - θ₀),
          mulVecE J (mulVecE J⁻¹ (scoreSum ℓ n ω))⟫ from by rw [← hZ]]
  linarith [hpol]

/-- **logLR − score is `o_P(1)`** (simple null). Under `P^n_{θ₀}` and the two-point
second-order envelope condition, the likelihood-ratio and Rao score statistics differ by a
quantity tending to zero in probability.

**AMENDED HYPOTHESIS.** `henv` is the *two-point* form of the source's second-order envelope
condition (pairs `(θ, θ')` in the neighbourhood, not only `(θ, θ₀)`), which is what the
uniform LAN expansion needs: at the source's one-point form the uniform expansion
`sup_LAN_remainder_tendsto` is provably **false** (counterexample recorded in
`UniformLAN.lean`), and the one-point form gives only
`2[ℓₙ(θ̂)−ℓₙ(θ₀)] = 2⟪ĥₙ, Zₙ⟫ + O_P(1)` — the `O_P(1)` being exactly the `−⟪ĥₙ, J ĥₙ⟫` that
has to be identified. Setting `θ' = θ₀` returns the printed condition. See
`sup_LAN_remainder_tendsto` for the full discussion.

Proof: apply the uniform expansion at the *random* direction `ĥₙ = √n(θ̂ₙ−θ₀)`, which is
legitimate because `ĥₙ` is bounded in probability (`hlin` plus tightness of `Vₙ = J⁻¹Zₙ` from
the score CLT), and then `logLRStatistic_sub_scoreStatistic_eq` reduces the difference to
`2·lanRemainder(ĥₙ) − ⟪ĥₙ−Vₙ, J(ĥₙ−Vₙ)⟫`. -/
private lemma logLR_sub_score_tendstoInMeasure
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int : Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    (δ : ℝ) (hδ : 0 < δ)
    (henv : ∀ θ θ' : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ‖θ' - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x / M.density θ₀ x)
          - Real.log (M.density θ' x / M.density θ₀ x) - ⟪θ - θ', ℓ x⟫|
        ≤ Menv x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 |
          ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|})
        atTop (𝓝 0) := by
  intro ε hε
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ_pd.isUnit
  have hHerm : J.IsHermitian := hJ_pd.isHermitian
  set C : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ with hCdef
  have hC0 : 0 ≤ C := norm_nonneg _
  have hVmeas : ∀ n, Measurable (fun ω : Fin n → 𝓧 => mulVecE J⁻¹ (scoreSum ℓ n ω)) :=
    fun n => (GaussianShift.matrixAction_measurable J⁻¹).comp (measurable_scoreSum ℓ hℓ n)
  have hV := scoreSum_mulVecE_inv_weakConverges M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro α hα
  obtain ⟨K, hK0, hKev⟩ :=
    exists_radius_eventually_measureReal_norm_le hVmeas hV (α := α / 4) (by positivity)
  -- Radius of directions: `‖ĥₙ‖ ≤ ‖Vₙ‖ + ‖ĥₙ − Vₙ‖ < K + 1` on the good event.
  have hc0 : (0 : ℝ) < K + 1 := by positivity
  -- Tolerance on the linearization gap making the quadratic error smaller than `ε/2`.
  set η : ℝ := min 1 (Real.sqrt (ε / (2 * (C + 1)))) with hηdef
  have hη0 : 0 < η :=
    lt_min one_pos (Real.sqrt_pos.2 (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηsq : C * η ^ 2 < ε / 2 := by
    have hle : η ≤ Real.sqrt (ε / (2 * (C + 1))) := min_le_right _ _
    have hpos : (0 : ℝ) < 2 * (C + 1) := by positivity
    have hsq : η ^ 2 ≤ ε / (2 * (C + 1)) := by
      have h := mul_self_le_mul_self hη0.le hle
      rw [← pow_two, ← pow_two, Real.sq_sqrt (by positivity : (0:ℝ) ≤ ε / (2 * (C + 1)))] at h
      exact h
    have hmul : C * η ^ 2 ≤ C * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hsq hC0
    have hlt : C * (ε / (2 * (C + 1))) < ε / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ hpos (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  -- The uniform LAN expansion over the ball of radius `K + 1`.
  have hULAN := sup_LAN_remainder_tendsto M μ hPDF θ₀ ℓ hℓ hDQM J hJ Menv hMenv_meas
    hMenv_int δ hδ henv (K + 1) hc0 (ε / 4) (by positivity)
  filter_upwards [hKev, (hlin η hη0).eventually_lt_const (u := α / 4) (by positivity),
    (NormedAddGroup.tendsto_nhds_zero.1 hULAN) (α / 4) (by positivity),
    eventually_ge_atTop 1] with n hnK hnlin hnLAN hn1
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] at hnLAN
  -- The bad event splits into three pieces.
  have hincl : {ω : Fin n → 𝓧 |
        ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|}
      ⊆ {ω : Fin n → 𝓧 | K ≤ ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖}
        ∪ ({ω : Fin n → 𝓧 |
              η ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖}
          ∪ {ω : Fin n → 𝓧 | ∃ h : EuclideanSpace ℝ (Fin k),
              ‖h‖ ≤ K + 1 ∧ ε / 4 ≤ |lanRemainder M θ₀ ℓ J h n ω|}) := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, not_le] at hcon
    obtain ⟨hVsmall, hgapsmall, hlanSmall⟩ := hcon
    -- `ĥₙ` lies in the ball of radius `K + 1`.
    have hball : ‖Real.sqrt n • (est n ω - θ₀)‖ ≤ K + 1 := by
      have hsplit := norm_le_norm_add_norm_sub' (Real.sqrt n • (est n ω - θ₀))
        (mulVecE J⁻¹ (scoreSum ℓ n ω))
      linarith [hVsmall, hgapsmall, hη1]
    have hlanval : |lanRemainder M θ₀ ℓ J (Real.sqrt n • (est n ω - θ₀)) n ω| < ε / 4 := by
      by_contra hbad
      exact absurd (hlanSmall _ hball) (not_lt.2 (not_lt.1 hbad))
    -- The quadratic error is controlled by the linearization gap.
    have hquad : |⟪Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω),
        mulVecE J (Real.sqrt n • (est n ω - θ₀)
          - mulVecE J⁻¹ (scoreSum ℓ n ω))⟫| < ε / 2 := by
      set w : EuclideanSpace ℝ (Fin k) :=
        Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω) with hwdef
      have hop : ‖mulVecE J w‖ ≤ C * ‖w‖ := by
        rw [mulVecE_eq_toEuclideanCLM, hCdef]
        exact ContinuousLinearMap.le_opNorm _ w
      have hb : |⟪w, mulVecE J w⟫| ≤ C * ‖w‖ ^ 2 := by
        refine le_trans (abs_real_inner_le_norm _ _) ?_
        calc ‖w‖ * ‖mulVecE J w‖ ≤ ‖w‖ * (C * ‖w‖) :=
              mul_le_mul_of_nonneg_left hop (norm_nonneg _)
          _ = C * ‖w‖ ^ 2 := by ring
      have hwlt : ‖w‖ < η := by rw [hwdef]; exact hgapsmall
      have hsq2 : ‖w‖ ^ 2 ≤ η ^ 2 := by
        have h := mul_self_le_mul_self (norm_nonneg w) hwlt.le
        rw [← pow_two, ← pow_two] at h
        exact h
      have : C * ‖w‖ ^ 2 ≤ C * η ^ 2 := mul_le_mul_of_nonneg_left hsq2 hC0
      linarith
    have hkey : |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω| < ε := by
      rw [logLRStatistic_sub_scoreStatistic_eq M θ₀ ℓ J hdet hHerm est n hn1 ω]
      refine lt_of_le_of_lt (abs_sub _ _) ?_
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      linarith
    exact absurd hω (not_le.2 hkey)
  -- Subadditivity and the three eventual bounds.
  have hmono := measureReal_mono (μ := productMeasure M μ θ₀ n) hincl (measure_ne_top _ _)
  have hu1 := measureReal_union_le (μ := productMeasure M μ θ₀ n)
    {ω : Fin n → 𝓧 | K ≤ ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖}
    ({ω : Fin n → 𝓧 |
        η ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖}
      ∪ {ω : Fin n → 𝓧 | ∃ h : EuclideanSpace ℝ (Fin k),
          ‖h‖ ≤ K + 1 ∧ ε / 4 ≤ |lanRemainder M θ₀ ℓ J h n ω|})
  have hu2 := measureReal_union_le (μ := productMeasure M μ θ₀ n)
    {ω : Fin n → 𝓧 |
      η ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖}
    {ω : Fin n → 𝓧 | ∃ h : EuclideanSpace ℝ (Fin k),
      ‖h‖ ≤ K + 1 ∧ ε / 4 ≤ |lanRemainder M θ₀ ℓ J h n ω|}
  linarith [hnlin.le]

/-- **Asymptotic equivalence of the trinity.**

Under `P^n_{θ₀}`, the Wald and likelihood ratio statistics each differ from the Rao score
statistic by a quantity tending to zero in probability. Consequently the three tests reject
the same data sets with probability tending to one. -/
theorem trinity_asymptotically_equivalent
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: an efficient (asymptotically linear) estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the envelope function of the second-order expansion, with finite mean
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int :
      Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- USER-INPUT: radius of the neighbourhood on which the envelope condition holds
    (δ : ℝ) (hδ : 0 < δ)
    -- USER-INPUT: two-point second-order envelope condition on the log-density increment.
    -- AMENDED: the source's one-point condition (the case `θ' = θ₀`) makes the uniform LAN
    -- expansion this proof needs provably false; see `sup_LAN_remainder_tendsto`.
    (henv : ∀ θ θ' : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ‖θ' - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x / M.density θ₀ x)
          - Real.log (M.density θ' x / M.density θ₀ x) - ⟪θ - θ', ℓ x⟫|
        ≤ Menv x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖) :
    (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 |
            ε ≤ |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω|})
          atTop (𝓝 0)) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 |
            ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|})
          atTop (𝓝 0)) :=
  ⟨wald_sub_score_tendstoInMeasure M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ est hest hlin,
    logLR_sub_score_tendstoInMeasure M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ est hest hlin
      Menv hMenv_meas hMenv_int δ hδ henv⟩

/-- **The Rao score statistic is asymptotically chi-squared.**

Under `P^n_{θ₀}`, `Zₙᵀ I⁻¹(θ₀) Zₙ ⇝ χ²ₖ`. This part needs no estimator and no envelope
condition: the score central limit theorem plus the continuous mapping theorem suffice, the
quadratic form of a `N(0, I)` vector in the metric `I⁻¹` being `χ²ₖ`. -/
theorem score_tendsto_chiSquared
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: nondegenerate parameter dimension; `χ²₀` is not a probability measure
    (hk : 0 < k)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreStatistic J ℓ n))
      (MultipleTesting.chiSquared k) := by
  -- Score CLT under the null: `Zₙ ⇝ N(0, J)`.
  have hScore : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    scoreSum_weakly_converges M μ θ₀ ℓ hℓ (hPDF.density_integral_eq_one θ₀)
      (hPDF.density_integrable θ₀)
      (fun t u => hPDF.density_integral_eq_one _) (fun t u => hPDF.density_integrable _)
      hDQM J hJ_pd.posSemidef hJ
  -- The quadratic form `q z = ⟪z, J⁻¹ z⟫` is continuous, and `scoreStatistic = q ∘ scoreSum`.
  have hcont := continuous_gaussQuadratic (k := k) J⁻¹
  have hmeas := hcont.measurable
  -- Rewrite the pushforward of the statistic as a composed pushforward of the score sum.
  have hseq : (fun n => (productMeasure M μ θ₀ n).map (scoreStatistic J ℓ n))
      = (fun n => ((productMeasure M μ θ₀ n).map (scoreSum ℓ n)).map
          (fun z => ⟪z, mulVecE J⁻¹ z⟫)) := by
    funext n
    rw [Measure.map_map hmeas (measurable_scoreSum ℓ hℓ n)]
    rfl
  rw [hseq, ← multivariateGaussian_map_quadratic_eq_chiSquared hk J hJ_pd]
  exact hScore.map hcont hmeas

/-- **The Wald statistic is asymptotically chi-squared.**

Under `P^n_{θ₀}`, `n(θ̂ₙ − θ₀)ᵀ I(θ₀)(θ̂ₙ − θ₀) ⇝ χ²ₖ` for any efficient estimator
sequence. Follows from the assumed expansion and the score limit; no envelope condition is
needed. -/
theorem wald_tendsto_chiSquared
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: nondegenerate parameter dimension; `χ²₀` is not a probability measure
    (hk : 0 < k)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: an efficient (asymptotically linear) estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (waldStatistic J θ₀ est n))
      (MultipleTesting.chiSquared k) := by
  -- `Vₙ = mulVecE J⁻¹ Zₙ ⇝ N(0, J⁻¹)`, by the score CLT and the linear pushforward.
  have hJinv_pd : J⁻¹.PosDef := hJ_pd.inv
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ_pd.isUnit
  have hV := scoreSum_mulVecE_inv_weakConverges M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ
  -- `Uₙ = √n·(θ̂ₙ − θ₀) ⇝ N(0, J⁻¹)` by Slutsky, since `‖Uₙ − Vₙ‖ →_P 0`.
  have hUmeas : ∀ n, Measurable (fun ω : Fin n → 𝓧 => Real.sqrt n • (est n ω - θ₀)) :=
    fun n => ((hest n).sub measurable_const).const_smul (Real.sqrt n)
  have hVmeas : ∀ n, Measurable (fun ω : Fin n → 𝓧 => mulVecE J⁻¹ (scoreSum ℓ n ω)) :=
    fun n => (GaussianShift.matrixAction_measurable J⁻¹).comp (measurable_scoreSum ℓ hℓ n)
  have hU : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (fun ω => Real.sqrt n • (est n ω - θ₀)))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
    refine WeakConverges.slutsky_of_tendstoInMeasure_dist
      (X := fun n ω => mulVecE J⁻¹ (scoreSum ℓ n ω))
      (Y := fun n ω => Real.sqrt n • (est n ω - θ₀))
      (fun n => (hVmeas n).aemeasurable) (fun n => (hUmeas n).aemeasurable) hV ?_
    intro ε hε
    have hset : (fun n => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ dist (mulVecE J⁻¹ (scoreSum ℓ n ω))
          (Real.sqrt n • (est n ω - θ₀))})
        = (fun n => (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 |
            ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖}) := by
      funext n; congr 1; ext ω
      simp only [Set.mem_setOf_eq]
      rw [dist_eq_norm, norm_sub_rev]
    rw [hset]; exact hlin ε hε
  -- Continuous mapping: `Wₙ = ⟪Uₙ, J Uₙ⟫`, and `N(0, J⁻¹)` pushes to `χ²ₖ`.
  have hcont := continuous_gaussQuadratic (k := k) J
  have hmeas := hcont.measurable
  have hmapU := hU.map hcont hmeas
  have hlim : (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹).map
      (fun z => ⟪z, mulVecE J z⟫) = MultipleTesting.chiSquared k := by
    have h := multivariateGaussian_map_quadratic_eq_chiSquared hk J⁻¹ hJinv_pd
    rwa [Matrix.nonsing_inv_nonsing_inv J hdet] at h
  rw [hlim] at hmapU
  have hseq : (fun n => (productMeasure M μ θ₀ n).map (waldStatistic J θ₀ est n))
      = (fun n => ((productMeasure M μ θ₀ n).map
          (fun ω => Real.sqrt n • (est n ω - θ₀))).map (fun z => ⟪z, mulVecE J z⟫)) := by
    funext n
    rw [Measure.map_map hmeas (hUmeas n)]
    congr 1
    funext ω
    exact waldStatistic_eq_quadratic J θ₀ est n ω
  rw [hseq]; exact hmapU

/-- **The likelihood ratio statistic is asymptotically chi-squared (simple null).**

Under `P^n_{θ₀}` and the second-order envelope condition,
`2 log(Lₙ(θ̂ₙ)/Lₙ(θ₀)) ⇝ χ²ₖ` for any efficient estimator sequence. -/
theorem logLR_tendsto_chiSquared
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: joint measurability of `(θ, x) ↦ p_θ(x)`; needed for the likelihood-ratio
    -- statistic to be a measurable function of the sample (see `measurable_logLRStatistic`,
    -- where the counterexample showing that per-`θ` measurability does not suffice is given)
    (hjoint : Measurable (Function.uncurry M.density))
    -- LEAN-ONLY: nondegenerate parameter dimension; `χ²₀` is not a probability measure
    (hk : 0 < k)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: an efficient (asymptotically linear) estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the envelope function of the second-order expansion, with finite mean
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int :
      Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- USER-INPUT: radius of the neighbourhood on which the envelope condition holds
    (δ : ℝ) (hδ : 0 < δ)
    -- USER-INPUT: two-point second-order envelope condition on the log-density increment.
    -- AMENDED: the source's one-point condition (the case `θ' = θ₀`) makes the uniform LAN
    -- expansion this proof needs provably false; see `sup_LAN_remainder_tendsto`.
    (henv : ∀ θ θ' : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ‖θ' - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x / M.density θ₀ x)
          - Real.log (M.density θ' x / M.density θ₀ x) - ⟪θ - θ', ℓ x⟫|
        ≤ Menv x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (logLRStatistic M est (fun _ _ => θ₀) n))
      (MultipleTesting.chiSquared k) := by
  -- Rao score statistic converges to `χ²ₖ`; the LR statistic differs from it by `o_P(1)`.
  haveI : NeZero k := ⟨hk.ne'⟩
  have hscore := score_tendsto_chiSquared M μ hPDF hk θ₀ ℓ hℓ hDQM J hJ_pd hJ
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n => scoreStatistic J ℓ n)
    (Y := fun n => logLRStatistic M est (fun _ _ => θ₀) n)
    (fun n => ((continuous_gaussQuadratic J⁻¹).measurable.comp
        (measurable_scoreSum ℓ hℓ n)).aemeasurable)
    (fun n => (measurable_logLRStatistic M hjoint est (fun _ _ => θ₀) hest
        (fun _ => measurable_const) n).aemeasurable)
    hscore ?_
  intro ε hε
  have h := logLR_sub_score_tendstoInMeasure M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ est hest hlin
    Menv hMenv_meas hMenv_int δ hδ henv ε hε
  have hset : (fun n => (productMeasure M μ θ₀ n).real
      {ω : Fin n → 𝓧 | ε ≤ dist (scoreStatistic J ℓ n ω)
        (logLRStatistic M est (fun _ _ => θ₀) n ω)})
      = (fun n => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 |
          ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|}) := by
    funext n; congr 1; ext ω
    simp only [Set.mem_setOf_eq, Real.dist_eq, abs_sub_comm]
  rw [hset]; exact h

/-! ### The affine composite null: the rank-`p` Gaussian geometry -/

omit [MeasurableSpace 𝓧] in
/-- Matrix actions compose: `A·(A'·z) = (A A')·z`. -/
private lemma mulVecE_comp (A A' : Matrix (Fin k) (Fin k) ℝ)
    (z : EuclideanSpace ℝ (Fin k)) : mulVecE A (mulVecE A' z) = mulVecE (A * A') z := by
  rw [mulVecE_eq_toEuclideanCLM, mulVecE_eq_toEuclideanCLM, mulVecE_eq_toEuclideanCLM,
    ← ContinuousLinearMap.mul_apply, ← map_mul]

omit [MeasurableSpace 𝓧] in
/-- The identity matrix acts as the identity. -/
private lemma mulVecE_one (z : EuclideanSpace ℝ (Fin k)) :
    mulVecE (1 : Matrix (Fin k) (Fin k) ℝ) z = z := by
  rw [mulVecE_eq_toEuclideanCLM, map_one]; rfl

/-- **Pushforward of a standard Gaussian under a coisometry.** If `φ` has norm at most one and
admits an isometric right inverse `ψ`, then `φ` maps the standard Gaussian of `E` to the
standard Gaussian of `F`.  Proved on characteristic functionals: the two hypotheses force
`‖L ∘ φ‖ = ‖L‖` for every continuous linear functional `L` on `F`. -/
private lemma stdGaussian_map_of_coisometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [FiniteDimensional ℝ F]
    (φ : E →L[ℝ] F) (ψ : F →L[ℝ] E) (hψ : ∀ y, ‖ψ y‖ = ‖y‖)
    (hφψ : ∀ y, φ (ψ y) = y) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) :
    (ProbabilityTheory.stdGaussian E).map φ = ProbabilityTheory.stdGaussian F := by
  haveI : IsProbabilityMeasure ((ProbabilityTheory.stdGaussian E).map φ) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFunDual
  ext L
  have hnorm : ‖L.comp φ‖ = ‖L‖ := by
    refine le_antisymm ?_ ?_
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      exact (L.le_opNorm (φ x)).trans (mul_le_mul_of_nonneg_left (hφ x) (norm_nonneg _))
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
      have h := (L.comp φ).le_opNorm (ψ y)
      rwa [ContinuousLinearMap.comp_apply, hφψ y, hψ y] at h
  rw [charFunDual_map, ProbabilityTheory.charFunDual_stdGaussian,
    ProbabilityTheory.charFunDual_stdGaussian, hnorm]

/-- **The squared length of the projection of a standard Gaussian onto a `p`-dimensional
subspace is `χ²ₚ`.** This is the degenerate (rank-`p`) Gaussian-quadratic ↔ chi-squared
bridge: an orthonormal basis of `V` turns the projection into a coisometry onto
`EuclideanSpace ℝ (Fin p)`, which carries the standard Gaussian to the standard Gaussian of
`ℝᵖ`, whose squared norm is `χ²ₚ`. -/
private lemma stdGaussian_map_normSq_starProjection {p : ℕ} (hp : 0 < p)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin k))) (hV : Module.finrank ℝ V = p) :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin k))).map
        (fun w => ‖V.starProjection w‖ ^ 2) = MultipleTesting.chiSquared p := by
  classical
  haveI : NeZero p := ⟨hp.ne'⟩
  let b : OrthonormalBasis (Fin p) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hV)
  let e : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin p) := b.repr
  let φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    (e.toLinearIsometry.toContinuousLinearMap).comp V.orthogonalProjection
  let ψ : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    V.subtypeL.comp (e.symm.toLinearIsometry.toContinuousLinearMap)
  have hφapp : ∀ w, φ w = e (V.orthogonalProjection w) := fun _ => rfl
  have hψapp : ∀ y, ψ y = ((e.symm y : V) : EuclideanSpace ℝ (Fin k)) := fun _ => rfl
  have hnormφ : ∀ w, ‖φ w‖ = ‖V.starProjection w‖ := by
    intro w
    rw [hφapp, e.norm_map]
    rfl
  have hψnorm : ∀ y, ‖ψ y‖ = ‖y‖ := by
    intro y
    rw [hψapp]
    exact (Submodule.norm_coe (e.symm y)).trans (e.symm.norm_map y)
  have hφψ : ∀ y, φ (ψ y) = y := by
    intro y
    rw [hφapp, hψapp, Submodule.orthogonalProjection_mem_subspace_eq_self,
      LinearIsometryEquiv.apply_symm_apply]
  have hφle : ∀ w, ‖φ w‖ ≤ ‖w‖ := by
    intro w
    have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection w V
    have h1 : ‖V.starProjection w‖ ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖Vᗮ.starProjection w‖]
    rw [hnormφ]
    nlinarith [norm_nonneg (V.starProjection w), norm_nonneg w]
  have hmapφ : (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin k))).map φ
      = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin p)) :=
    stdGaussian_map_of_coisometry φ ψ hψnorm hφψ hφle
  have hfun : (fun w : EuclideanSpace ℝ (Fin k) => ‖V.starProjection w‖ ^ 2)
      = (fun y : EuclideanSpace ℝ (Fin p) => ‖y‖ ^ 2) ∘ φ := by
    funext w
    simp only [Function.comp_apply, hnormφ w]
  rw [hfun, ← Measure.map_map (by fun_prop) φ.continuous.measurable, hmapφ,
    ← ProbabilityTheory.multivariateGaussian_zero_one (ι := Fin p),
    map_normSq_multivariateGaussian_of_norm_eq p 0 (by simp)]
  exact noncentralChiSquared_zero hp

/-- **The score-difference statistic of a `N(0, J)` vector is `χ²ₚ`.** With `√J` whitening the
Gaussian, the full-model quadratic form becomes `‖w‖²` and the restricted one becomes the
squared length of the projection of `w` onto the `m`-dimensional range of `T = √J ∘ B`; their
difference is the squared length of the projection onto the orthogonal complement, of
dimension `p = k − m`. -/
private lemma multivariateGaussian_map_scoreDiff_eq_chiSquared {m p : ℕ}
    (hdim : m + p = k) (hp : 0 < p)
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hB : Function.Injective B)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (hJBrel : ∀ u v : EuclideanSpace ℝ (Fin m),
      ⟪u, mulVecE JB v⟫ = ⟪B u, mulVecE J (B v)⟫) :
    (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
        (fun z => ⟪z, mulVecE J⁻¹ z⟫
          - ⟪ContinuousLinearMap.adjoint B z,
              mulVecE JB⁻¹ (ContinuousLinearMap.adjoint B z)⟫)
      = MultipleTesting.chiSquared p := by
  classical
  have hR_pd : (CFC.sqrt J).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp hJ_pd.isStrictlyPositive.sqrt
  have hRdet : IsUnit (CFC.sqrt J).det := (Matrix.isUnit_iff_isUnit_det _).mp hR_pd.isUnit
  have hRR : CFC.sqrt J * CFC.sqrt J = J := CFC.sqrt_mul_sqrt_self J hJ_pd.posSemidef.nonneg
  set T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt J)).comp B with hT
  have hTapp : ∀ u, T u = mulVecE (CFC.sqrt J) (B u) := fun _ => rfl
  have hRsa : ∀ x y : EuclideanSpace ℝ (Fin k),
      ⟪mulVecE (CFC.sqrt J) x, y⟫ = ⟪x, mulVecE (CFC.sqrt J) y⟫ :=
    inner_mulVecE_comm hR_pd.isHermitian
  -- Whitening turns the full-model quadratic form into the squared norm.
  have hterm1 : ∀ w, ⟪mulVecE (CFC.sqrt J) w, mulVecE J⁻¹ (mulVecE (CFC.sqrt J) w)⟫
      = ‖w‖ ^ 2 := by
    intro w
    have h0 : J⁻¹ = (CFC.sqrt J)⁻¹ * (CFC.sqrt J)⁻¹ := by
      rw [← Matrix.mul_inv_rev, hRR]
    have h1 : J⁻¹ * CFC.sqrt J = (CFC.sqrt J)⁻¹ := by
      rw [h0, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRdet, Matrix.mul_one]
    rw [mulVecE_comp, h1, hRsa, mulVecE_comp, Matrix.mul_nonsing_inv _ hRdet, mulVecE_one,
      real_inner_self_eq_norm_sq]
  -- `JB` is the Gram matrix of `T = √J ∘ B`.
  have hJB_gram : ∀ u v : EuclideanSpace ℝ (Fin m), ⟪u, mulVecE JB v⟫ = ⟪T u, T v⟫ := by
    intro u v
    rw [hJBrel u v, hTapp, hTapp, hRsa, mulVecE_comp, hRR]
  have hRinj : Function.Injective
      (fun z : EuclideanSpace ℝ (Fin k) => mulVecE (CFC.sqrt J) z) := by
    intro x y hxy
    have h := congrArg (fun z => mulVecE (CFC.sqrt J)⁻¹ z) hxy
    simpa [mulVecE_comp, Matrix.nonsing_inv_mul _ hRdet, mulVecE_one] using h
  have hTinj : Function.Injective T := fun x y hxy => hB (hRinj hxy)
  -- `JB` is nonsingular.
  have hJBdet : IsUnit JB.det := by
    rw [isUnit_iff_ne_zero]
    intro hdet0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
    set u : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm v with hu
    have h1 : mulVecE JB u = 0 := by
      simp [mulVecE, hu, hv]
    have h2 : ⟪T u, T u⟫ = 0 := by rw [← hJB_gram, h1, inner_zero_right]
    have h3 : T u = 0 := by
      rwa [inner_self_eq_zero] at h2
    have h4 : u = 0 := hTinj (by rw [h3, map_zero])
    exact hv0 (by simpa [hu] using congrArg (WithLp.equiv 2 (Fin m → ℝ)) h4)
  -- `T`'s adjoint composed with `T` is the action of `JB`.
  have hTT : ∀ v, ContinuousLinearMap.adjoint T (T v) = mulVecE JB v := by
    intro v
    have h : ⟪ContinuousLinearMap.adjoint T (T v) - mulVecE JB v,
        ContinuousLinearMap.adjoint T (T v) - mulVecE JB v⟫ = 0 := by
      rw [inner_sub_right, ContinuousLinearMap.adjoint_inner_right, ← hJB_gram, sub_self]
    rwa [inner_self_eq_zero, sub_eq_zero] at h
  -- The adjoint of `T` in terms of `B`.
  have hRadj : ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt J)) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt J) :=
    ((ContinuousLinearMap.eq_adjoint_iff _ _).2 (fun x y => hRsa x y)).symm
  have hTadj : ∀ w, ContinuousLinearMap.adjoint T w
      = ContinuousLinearMap.adjoint B (mulVecE (CFC.sqrt J) w) := by
    intro w
    rw [hT, ContinuousLinearMap.adjoint_comp, hRadj]
    rfl
  -- The restricted quadratic form is the squared length of the projection onto `range T`.
  set W : Submodule ℝ (EuclideanSpace ℝ (Fin k)) :=
    LinearMap.range (T : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) with hW
  have hterm2 : ∀ w : EuclideanSpace ℝ (Fin k),
      ⟪ContinuousLinearMap.adjoint B (mulVecE (CFC.sqrt J) w),
        mulVecE JB⁻¹ (ContinuousLinearMap.adjoint B (mulVecE (CFC.sqrt J) w))⟫
        = ‖W.starProjection w‖ ^ 2 := by
    intro w
    rw [← hTadj w]
    set y : EuclideanSpace ℝ (Fin m) := mulVecE JB⁻¹ (ContinuousLinearMap.adjoint T w) with hy
    have hyJB : mulVecE JB y = ContinuousLinearMap.adjoint T w :=
      mulVecE_mulVecE_inv JB hJBdet _
    have hproj : W.starProjection w = T y := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ⟨y, rfl⟩ ?_
      rintro _ ⟨u, rfl⟩
      have hzero : ContinuousLinearMap.adjoint T (w - T y) = 0 := by
        rw [map_sub, hTT y, hyJB, sub_self]
      have := ContinuousLinearMap.adjoint_inner_left T u (w - T y)
      rw [hzero, inner_zero_left] at this
      exact this.symm
    calc ⟪ContinuousLinearMap.adjoint T w, y⟫
        = ⟪w, T y⟫ := ContinuousLinearMap.adjoint_inner_left T y w
      _ = ⟪w, W.starProjection (W.starProjection w)⟫ := by
          rw [Submodule.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem w), hproj]
      _ = ⟪W.starProjection w, W.starProjection w⟫ :=
          (Submodule.inner_starProjection_left_eq_right W w (W.starProjection w)).symm
      _ = ‖W.starProjection w‖ ^ 2 := real_inner_self_eq_norm_sq _
  -- Pythagoras: the difference is the squared length of the complementary projection.
  have hFR : ∀ w : EuclideanSpace ℝ (Fin k),
      ⟪mulVecE (CFC.sqrt J) w, mulVecE J⁻¹ (mulVecE (CFC.sqrt J) w)⟫
        - ⟪ContinuousLinearMap.adjoint B (mulVecE (CFC.sqrt J) w),
            mulVecE JB⁻¹ (ContinuousLinearMap.adjoint B (mulVecE (CFC.sqrt J) w))⟫
        = ‖Wᗮ.starProjection w‖ ^ 2 := by
    intro w
    have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection w W
    rw [hterm1 w, hterm2 w]
    linarith
  -- The complementary subspace has dimension `p`.
  have hfinW : Module.finrank ℝ W = m := by
    rw [hW, LinearMap.finrank_range_of_inj hTinj, finrank_euclideanSpace_fin]
  have hfinWc : Module.finrank ℝ (Wᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin k))) = p := by
    have h := W.finrank_add_finrank_orthogonal (𝕜 := ℝ)
    rw [hfinW, finrank_euclideanSpace_fin] at h
    omega
  -- Change of variables and the projection law.
  have hmvg : ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J
      = (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin k))).map
          (fun x => mulVecE (CFC.sqrt J) x) := by
    rw [ProbabilityTheory.multivariateGaussian]
    simp only [zero_add]
    rfl
  have hmeas : Measurable fun z : EuclideanSpace ℝ (Fin k) => ⟪z, mulVecE J⁻¹ z⟫
      - ⟪ContinuousLinearMap.adjoint B z,
          mulVecE JB⁻¹ (ContinuousLinearMap.adjoint B z)⟫ :=
    ((continuous_gaussQuadratic J⁻¹).sub
      ((continuous_gaussQuadratic JB⁻¹).comp
        (ContinuousLinearMap.adjoint B).continuous)).measurable
  have hRmeas : Measurable fun x : EuclideanSpace ℝ (Fin k) => mulVecE (CFC.sqrt J) x :=
    GaussianShift.matrixAction_measurable (CFC.sqrt J)
  rw [hmvg, Measure.map_map hmeas hRmeas]
  have hcomp : ((fun z : EuclideanSpace ℝ (Fin k) => ⟪z, mulVecE J⁻¹ z⟫
        - ⟪ContinuousLinearMap.adjoint B z,
            mulVecE JB⁻¹ (ContinuousLinearMap.adjoint B z)⟫)
      ∘ fun x => mulVecE (CFC.sqrt J) x)
      = fun w => ‖Wᗮ.starProjection w‖ ^ 2 := by
    funext w
    exact hFR w
  rw [hcomp]
  exact stdGaussian_map_normSq_starProjection hp Wᗮ hfinWc

/-- **The restricted information matrix is the pullback of the full one along `B`.**
The two Fisher information integrands agree pointwise: the restricted density at `β₀` is the
full density at `θ₀ = a + Bβ₀`, and `⟪u, B*(ℓ x)⟫ = ⟪B u, ℓ x⟫`. -/
private lemma inner_mulVecE_pullback {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ = a + B β₀)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (hℓB : ℓB = fun x => ContinuousLinearMap.adjoint B (ℓ x))
    (J : Matrix (Fin k) (Fin k) ℝ)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (hJB : ∀ u v : EuclideanSpace ℝ (Fin m),
      fisherInformation (restrictFamily M a B) μ β₀ ℓB u v = ⟪u, mulVecE JB v⟫) :
    ∀ u v : EuclideanSpace ℝ (Fin m), ⟪u, mulVecE JB v⟫ = ⟪B u, mulVecE J (B v)⟫ := by
  intro u v
  rw [← hJB u v, ← hJ (B u) (B v)]
  unfold fisherInformation
  have hdens : ∀ x : 𝓧, (restrictFamily M a B).density β₀ x = M.density θ₀ x := by
    intro x
    rw [hθ₀]; rfl
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [hdens x, hℓB]
  have h1 : ⟪u, ContinuousLinearMap.adjoint B (ℓ x)⟫ = ⟪B u, ℓ x⟫ := by
    rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  have h2 : ⟪v, ContinuousLinearMap.adjoint B (ℓ x)⟫ = ⟪B v, ℓ x⟫ := by
    rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  rw [h1, h2]

/-- **Score-difference surrogate converges to `χ²ₚ`** (affine composite null). The difference of
the full-model and restricted-model Rao score statistics converges in law to `χ²ₚ`, `p = k − m`
the codimension.

The restricted-model score is `ℓB = B* ℓ`, so `scoreSum ℓB = B* (scoreSum ℓ)` and the whole
statistic is one fixed continuous function of the *full*-model score sum; no separate
restricted-model central limit theorem is needed.  The score CLT and the continuous mapping
theorem then reduce the claim to the Gaussian identity
`multivariateGaussian_map_scoreDiff_eq_chiSquared`. -/
private lemma affineScoreDiff_tendsto_chiSquared {m p : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (hdim : m + p = k) (hp : 0 < p)
    (a : EuclideanSpace ℝ (Fin k)) (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hB : Function.Injective B)
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ = a + B β₀)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (hℓB : ℓB = fun x => ContinuousLinearMap.adjoint B (ℓ x))
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (hJB : ∀ u v : EuclideanSpace ℝ (Fin m),
      fisherInformation (restrictFamily M a B) μ β₀ ℓB u v = ⟪u, mulVecE JB v⟫)
    [∀ β : EuclideanSpace ℝ (Fin m), ∀ n,
      IsProbabilityMeasure (productMeasure (restrictFamily M a B) μ β n)] :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω))
      (MultipleTesting.chiSquared p) := by
  classical
  -- Score CLT in the full model.
  have hScore : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    scoreSum_weakly_converges M μ θ₀ ℓ hℓ (hPDF.density_integral_eq_one θ₀)
      (hPDF.density_integrable θ₀)
      (fun t u => hPDF.density_integral_eq_one _) (fun t u => hPDF.density_integrable _)
      hDQM J hJ_pd.posSemidef hJ
  -- The restricted Fisher information is the pullback of the full one along `B`.
  have hJBrel := inner_mulVecE_pullback M μ a B β₀ θ₀ hθ₀ ℓ ℓB hℓB J hJ JB hJB
  -- The statistic is one fixed continuous function of the full-model score sum.
  have hscoreB : ∀ (n : ℕ) (ω : Fin n → 𝓧),
      scoreSum ℓB n ω = ContinuousLinearMap.adjoint B (scoreSum ℓ n ω) := by
    intro n ω
    rw [hℓB]
    unfold scoreSum
    rw [map_smul, map_sum]
  have hFcont : Continuous fun z : EuclideanSpace ℝ (Fin k) => ⟪z, mulVecE J⁻¹ z⟫
      - ⟪ContinuousLinearMap.adjoint B z,
          mulVecE JB⁻¹ (ContinuousLinearMap.adjoint B z)⟫ :=
    (continuous_gaussQuadratic J⁻¹).sub
      ((continuous_gaussQuadratic JB⁻¹).comp
        (ContinuousLinearMap.adjoint B).continuous)
  have hseq : (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω))
      = fun n => ((productMeasure M μ θ₀ n).map (scoreSum ℓ n)).map
          (fun z => ⟪z, mulVecE J⁻¹ z⟫
            - ⟪ContinuousLinearMap.adjoint B z,
                mulVecE JB⁻¹ (ContinuousLinearMap.adjoint B z)⟫) := by
    funext n
    rw [Measure.map_map hFcont.measurable (measurable_scoreSum ℓ hℓ n)]
    congr 1
    funext ω
    simp only [Function.comp_apply, scoreStatistic, hscoreB n ω]
  rw [hseq, ← multivariateGaussian_map_scoreDiff_eq_chiSquared hdim hp B hB J hJ_pd JB hJBrel]
  exact hScore.map hFcont hFcont.measurable

/-! ### Bricks for the affine reduction

The affine statistic is the *difference* of two simple-null statistics, one in the full model
at `θ₀` and one in the restricted model at `β₀`; the bricks below are the bookkeeping that
makes that reduction literal. -/

/-- The `n`-fold product law of the restricted model at the chart point is the product law of
the full model at `θ₀`: the two densities are the same function. -/
private lemma productMeasure_restrictFamily {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k))
    (hθ₀ : θ₀ = a + B β₀) (n : ℕ) :
    productMeasure (restrictFamily M a B) μ β₀ n = productMeasure M μ θ₀ n := by
  rw [hθ₀]; rfl

/-- The restricted model inherits the two `IsPDFOf` clauses: both are the full model's clauses
at the parameter `a + Bβ`. -/
private lemma isPDFOf_restrictFamily {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hPDF : IsPDFOf M μ) :
    IsPDFOf (restrictFamily M a B) μ :=
  ⟨fun _ => hPDF.density_integral_eq_one _, fun _ => hPDF.density_integrable _⟩

/-- **The pulled-back information matrix is positive definite.** `JB` is the Gram matrix of
`B` in the `J`-inner product (`inner_mulVecE_pullback`); injectivity of `B` turns the
positive definiteness of `J` into that of `JB`. This is the ingredient (iv) that the
simple-null lemma needs in the restricted chart. -/
private lemma posDef_pullback {m : ℕ}
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hB : Function.Injective B)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (hJBrel : ∀ u v : EuclideanSpace ℝ (Fin m),
      ⟪u, mulVecE JB v⟫ = ⟪B u, mulVecE J (B v)⟫) :
    JB.PosDef := by
  classical
  have hsymm : ∀ u v : EuclideanSpace ℝ (Fin m),
      ⟪u, mulVecE JB v⟫ = ⟪v, mulVecE JB u⟫ := by
    intro u v
    rw [hJBrel u v, hJBrel v u, ← inner_mulVecE_comm hJ_pd.isHermitian (B u) (B v),
      real_inner_comm]
  have hpos : ∀ u : EuclideanSpace ℝ (Fin m), u ≠ 0 → 0 < ⟪u, mulVecE JB u⟫ := by
    intro u hu
    rw [hJBrel u u, mulVecE_eq_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
    have hBu : B u ≠ 0 := fun h => hu (hB (by rw [h, map_zero]))
    have hne : (B u).ofLp ≠ 0 := by
      intro h
      exact hBu (by ext i; simpa using congrFun h i)
    simpa using hJ_pd.dotProduct_mulVec_pos hne
  have hsymm' : ∀ x y : Fin m → ℝ,
      dotProduct x (JB.mulVec y) = dotProduct y (JB.mulVec x) := by
    intro x y
    have h := hsymm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simp only [mulVecE_eq_toEuclideanCLM, Matrix.inner_toEuclideanCLM] at h
    simpa using h
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    have h := hsymm' (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ))
    simpa [Matrix.conjTranspose_apply, Matrix.mulVec_single, single_dotProduct] using h
  · have hx' : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m)) ≠ 0 := by
      intro h
      exact hx (by ext i; simpa using congrFun (congrArg WithLp.ofLp h) i)
    have h := hpos (WithLp.toLp 2 x) hx'
    simp only [mulVecE_eq_toEuclideanCLM, Matrix.inner_toEuclideanCLM] at h
    simpa using h

/-- **The base density does not vanish anywhere along the sample.** The sample is drawn from
`μ.withDensity p_{θ₀}`, for which `{p_{θ₀} = 0}` is a null set; the product of `n` copies then
gives all `n` coordinates at once. This is what makes the log-splitting below legitimate. -/
private lemma ae_forall_density_ne_zero
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    ∀ᵐ ω ∂(productMeasure M μ θ₀ n), ∀ i, M.density θ₀ (ω i) ≠ 0 := by
  classical
  set ν : Measure 𝓧 := μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x) with hν
  set S : Set 𝓧 := {x | M.density θ₀ x = 0} with hS
  have hSmeas : MeasurableSet S := (M.density_meas θ₀) (measurableSet_singleton 0)
  have hS0 : ν S = 0 := by
    rw [hν, MeasureTheory.withDensity_apply _ hSmeas]
    refine le_antisymm ?_ (zero_le)
    refine le_of_eq ?_
    rw [MeasureTheory.setLIntegral_congr_fun hSmeas (g := fun _ => (0 : ℝ≥0∞))
      (fun x hx => by simp [Set.mem_setOf_eq.mp hx])]
    simp
  rw [MeasureTheory.ae_all_iff]
  intro i
  rw [MeasureTheory.ae_iff]
  have hset : {ω : Fin n → 𝓧 | ¬ M.density θ₀ (ω i) ≠ 0}
      = Set.univ.pi (fun j => if j = i then S else Set.univ) := by
    ext ω
    simp only [Set.mem_setOf_eq, not_not, Set.mem_univ_pi]
    constructor
    · intro h j
      by_cases hj : j = i
      · subst hj; simpa [hS] using h
      · simp [hj]
    · intro h
      simpa [hS] using h i
  rw [hset, productMeasure, MeasureTheory.Measure.pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simpa using hS0

/-- **Splitting the affine log-likelihood ratio at `θ₀`.** Wherever the three densities are
nonzero, `log(p_{θ̂}/p_{a+Bβ̂}) = log(p_{θ̂}/p_{θ₀}) − log(p_{a+Bβ̂}/p_{θ₀})`, so the affine
statistic is the difference of the two simple-null statistics.

The hypothesis `hsupp` is what makes the identity true: at the Lean junk values it is FALSE
(with `p_{θ̂}(x) = 0 < p_{a+Bβ̂}(x), p_{θ₀}(x)` the left side is `Real.log 0 = 0` while the
right side is `−log(p_{a+Bβ̂}(x)/p_{θ₀}(x)) ≠ 0`). -/
private lemma logLRStatistic_affine_split {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k))
    (hθ₀ : θ₀ = a + B β₀)
    (hsupp : ∀ (θ : EuclideanSpace ℝ (Fin k)) (x : 𝓧),
      M.density θ₀ x ≠ 0 → M.density θ x ≠ 0)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin m))
    (n : ℕ) (ω : Fin n → 𝓧) (hω : ∀ i, M.density θ₀ (ω i) ≠ 0) :
    logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
      = logLRStatistic M est (fun _ _ => θ₀) n ω
        - logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω := by
  have hden : ∀ (β : EuclideanSpace ℝ (Fin m)) (x : 𝓧),
      (restrictFamily M a B).density β x = M.density (a + B β) x := fun _ _ => rfl
  have key : ∀ i : Fin n,
      Real.log (M.density (est n ω) (ω i) / M.density (a + B (est₀ n ω)) (ω i))
        = Real.log (M.density (est n ω) (ω i) / M.density θ₀ (ω i))
          - Real.log (M.density (a + B (est₀ n ω)) (ω i) / M.density θ₀ (ω i)) := by
    intro i
    have hD := hω i
    have hA := hsupp (est n ω) (ω i) hD
    have hC := hsupp (a + B (est₀ n ω)) (ω i) hD
    rw [Real.log_div hA hC, Real.log_div hA hD, Real.log_div hC hD]
    ring
  simp only [logLRStatistic, hden, ← hθ₀]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => key i)

/-- **The two-point envelope condition transports to the restricted chart**, with envelope
`|M|·‖B‖²` and radius `δ/(‖B‖+1)`: the chart is affine with linear part `B`, so
`‖(a+Bβ) − θ₀‖ ≤ ‖B‖‖β − β₀‖` and `⟪β − β', ℓB x⟫ = ⟪(a+Bβ) − (a+Bβ'), ℓ x⟫`. The absolute
value is taken because the envelope is only constrained through an upper bound. -/
private lemma envelope_restrictFamily {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k))
    (hθ₀ : θ₀ = a + B β₀)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (hℓB : ℓB = fun x => ContinuousLinearMap.adjoint B (ℓ x))
    (Menv : 𝓧 → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (henv : ∀ θ θ' : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ‖θ' - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x / M.density θ₀ x)
          - Real.log (M.density θ' x / M.density θ₀ x) - ⟪θ - θ', ℓ x⟫|
        ≤ Menv x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖) :
    ∀ β β' : EuclideanSpace ℝ (Fin m), ‖β - β₀‖ ≤ δ / (‖B‖ + 1) →
      ‖β' - β₀‖ ≤ δ / (‖B‖ + 1) → ∀ x : 𝓧,
      |Real.log ((restrictFamily M a B).density β x / (restrictFamily M a B).density β₀ x)
          - Real.log ((restrictFamily M a B).density β' x
              / (restrictFamily M a B).density β₀ x)
          - ⟪β - β', ℓB x⟫|
        ≤ |Menv x| * ‖B‖ ^ 2 * (‖β - β₀‖ + ‖β' - β₀‖) * ‖β - β'‖ := by
  intro β β' hβ hβ' x
  have hden : ∀ (γ : EuclideanSpace ℝ (Fin m)) (y : 𝓧),
      (restrictFamily M a B).density γ y = M.density (a + B γ) y := fun _ _ => rfl
  have hb0 : (0 : ℝ) ≤ ‖B‖ := norm_nonneg _
  have hsub : ∀ γ γ' : EuclideanSpace ℝ (Fin m),
      (a + B γ) - (a + B γ') = B (γ - γ') := by
    intro γ γ'
    rw [map_sub]
    abel
  have hbound : ∀ γ : EuclideanSpace ℝ (Fin m), ‖γ - β₀‖ ≤ δ / (‖B‖ + 1) →
      ‖(a + B γ) - θ₀‖ ≤ δ := by
    intro γ hγ
    have h1 : (a + B γ) - θ₀ = B (γ - β₀) := by rw [hθ₀]; exact hsub γ β₀
    have h2 : ‖B (γ - β₀)‖ ≤ ‖B‖ * ‖γ - β₀‖ := B.le_opNorm _
    have h3 : ‖B‖ * ‖γ - β₀‖ ≤ ‖B‖ * (δ / (‖B‖ + 1)) :=
      mul_le_mul_of_nonneg_left hγ hb0
    have h4 : ‖B‖ * (δ / (‖B‖ + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    rw [h1]; linarith
  have h1 := hbound β hβ
  have h2 := hbound β' hβ'
  have hinner : ⟪β - β', ℓB x⟫ = ⟪(a + B β) - (a + B β'), ℓ x⟫ := by
    rw [hsub β β', hℓB, real_inner_comm, ContinuousLinearMap.adjoint_inner_left,
      real_inner_comm]
  have hkey := henv (a + B β) (a + B β') h1 h2 x
  simp only [hden, ← hθ₀, hinner]
  refine hkey.trans ?_
  have hnb : ‖(a + B β) - θ₀‖ ≤ ‖B‖ * ‖β - β₀‖ := by
    have h : (a + B β) - θ₀ = B (β - β₀) := by rw [hθ₀]; exact hsub β β₀
    rw [h]; exact B.le_opNorm _
  have hnb' : ‖(a + B β') - θ₀‖ ≤ ‖B‖ * ‖β' - β₀‖ := by
    have h : (a + B β') - θ₀ = B (β' - β₀) := by rw [hθ₀]; exact hsub β' β₀
    rw [h]; exact B.le_opNorm _
  have hnd : ‖(a + B β) - (a + B β')‖ ≤ ‖B‖ * ‖β - β'‖ := by
    rw [hsub β β']; exact B.le_opNorm _
  have hMle : Menv x ≤ |Menv x| := le_abs_self _
  have hM0 : (0 : ℝ) ≤ |Menv x| := abs_nonneg _
  have hp : (0 : ℝ) ≤ ‖β - β₀‖ := norm_nonneg _
  have hq : (0 : ℝ) ≤ ‖β' - β₀‖ := norm_nonneg _
  have hr : (0 : ℝ) ≤ ‖β - β'‖ := norm_nonneg _
  have hX : (0 : ℝ) ≤ ‖(a + B β) - θ₀‖ + ‖(a + B β') - θ₀‖ := by positivity
  have hY : (0 : ℝ) ≤ ‖(a + B β) - (a + B β')‖ := norm_nonneg _
  calc Menv x * (‖(a + B β) - θ₀‖ + ‖(a + B β') - θ₀‖) * ‖(a + B β) - (a + B β')‖
      ≤ |Menv x| * (‖B‖ * ‖β - β₀‖ + ‖B‖ * ‖β' - β₀‖) * (‖B‖ * ‖β - β'‖) := by
        have hstep1 : Menv x * (‖(a + B β) - θ₀‖ + ‖(a + B β') - θ₀‖)
            ≤ |Menv x| * (‖B‖ * ‖β - β₀‖ + ‖B‖ * ‖β' - β₀‖) := by
          nlinarith
        have hstep2 : (0 : ℝ) ≤ |Menv x| * (‖B‖ * ‖β - β₀‖ + ‖B‖ * ‖β' - β₀‖) := by
          positivity
        nlinarith
    _ = |Menv x| * ‖B‖ ^ 2 * (‖β - β₀‖ + ‖β' - β₀‖) * ‖β - β'‖ := by ring

/-- **Assembly.** Once the affine statistic is the difference of the two simple-null
statistics, the event that it differs from the score difference by `ε` is covered by the two
events that each simple-null statistic differs from its own score statistic by `ε/2`, together
with the null set on which the splitting fails. -/
private lemma tendstoInMeasure_of_split {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (θ₀ : EuclideanSpace ℝ (Fin k)) (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (β₀ : EuclideanSpace ℝ (Fin m)) (hθ₀ : θ₀ = a + B β₀)
    (hsupp : ∀ (θ : EuclideanSpace ℝ (Fin k)) (x : 𝓧),
      M.density θ₀ x ≠ 0 → M.density θ x ≠ 0)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (J : Matrix (Fin k) (Fin k) ℝ)
    (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m)) (JB : Matrix (Fin m) (Fin m) ℝ)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin m))
    (h1 : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 |
          ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|})
        atTop (𝓝 0))
    (h2 : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure (restrictFamily M a B) μ β₀ n).real
        {ω : Fin n → 𝓧 |
          ε ≤ |logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
            - scoreStatistic JB ℓB n ω|})
        atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
          - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|})
        atTop (𝓝 0) := by
  intro ε hε
  have hprod := fun n : ℕ => productMeasure_restrictFamily M μ a B β₀ θ₀ hθ₀ n
  have h2' : Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
      {ω : Fin n → 𝓧 |
        ε / 2 ≤ |logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
          - scoreStatistic JB ℓB n ω|}) atTop (𝓝 0) := by
    have := h2 (ε / 2) (by positivity)
    simpa only [hprod] using this
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_)
    (by simpa using (h1 (ε / 2) (by positivity)).add h2')
  set A1 : Set (Fin n → 𝓧) := {ω : Fin n → 𝓧 |
    ε / 2 ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|} with hA1
  set A2 : Set (Fin n → 𝓧) := {ω : Fin n → 𝓧 |
    ε / 2 ≤ |logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
      - scoreStatistic JB ℓB n ω|} with hA2
  set G : Set (Fin n → 𝓧) := {ω : Fin n → 𝓧 | ∀ i, M.density θ₀ (ω i) ≠ 0} with hG
  have hGnull : (productMeasure M μ θ₀ n).real Gᶜ = 0 := by
    have hae := ae_forall_density_ne_zero M μ θ₀ n
    rw [MeasureTheory.ae_iff] at hae
    simp only [measureReal_def]
    rw [show Gᶜ = {ω : Fin n → 𝓧 | ¬ ∀ i, M.density θ₀ (ω i) ≠ 0} from rfl, hae]
    simp
  have hincl : {ω : Fin n → 𝓧 | ε ≤ |logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
      - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|} ⊆ A1 ∪ A2 ∪ Gᶜ := by
    intro ω hω
    by_cases hg : ω ∈ G
    · have hsplit := logLRStatistic_affine_split M a B β₀ θ₀ hθ₀ hsupp est est₀ n ω hg
      simp only [Set.mem_setOf_eq, hsplit] at hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_compl_iff, hA1, hA2, Set.mem_setOf_eq, not_or,
        not_le] at hcon
      obtain ⟨⟨hc1, hc2⟩, -⟩ := hcon
      have : |logLRStatistic M est (fun _ _ => θ₀) n ω
            - logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
            - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|
          ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|
            + |logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
              - scoreStatistic JB ℓB n ω| := by
        have heq : logLRStatistic M est (fun _ _ => θ₀) n ω
              - logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
              - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)
            = (logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω)
              - (logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
                - scoreStatistic JB ℓB n ω) := by ring
        rw [heq]
        exact abs_sub _ _
      linarith
    · exact Or.inr hg
  have hmono := measureReal_mono (μ := productMeasure M μ θ₀ n) hincl (measure_ne_top _ _)
  have hu1 := measureReal_union_le (μ := productMeasure M μ θ₀ n) (A1 ∪ A2) Gᶜ
  have hu2 := measureReal_union_le (μ := productMeasure M μ θ₀ n) A1 A2
  linarith

/-- **logLR − score-difference is `o_P(1)`** (affine composite null). The affine
likelihood-ratio statistic differs from the score-difference surrogate by a quantity tending
to zero in probability.

The proof is two applications of the simple-null lemma `logLR_sub_score_tendstoInMeasure`.
Writing `θ₀ = a + Bβ₀`, the restricted density at `β₀` is *literally* the full density at
`θ₀`, so
`2 ∑ᵢ log(p_{a+Bβ̂}(ωᵢ)/p_{θ₀}(ωᵢ)) = logLRStatistic (restrictFamily M a B) est₀ (·↦β₀)`
and the two conclusions subtract (`tendstoInMeasure_of_split`); the bookkeeping is
`isPDFOf_restrictFamily`, `productMeasure_restrictFamily`,
`differentiableQuadraticMean_restrictFamily`, `posDef_pullback` and
`envelope_restrictFamily`.

**SIGNATURE (re-parenthesization).** The lemma as frozen mentioned neither
`hθ₀ : θ₀ = a + Bβ₀`, nor `hℓB`, `hJB`, `hDQM`, `hJ_pd`, `hB`, so nothing tied `(a, B, β₀,
ℓB, JB)` to `(θ₀, ℓ, J)` and the score difference was unrelated to the likelihood ratio: it
was unprovable as stated. All of these are available at the unique call site,
`logLR_tendsto_chiSquared_affine`, and none of them changes a public statement.

**AMENDED HYPOTHESIS `hsupp` (common support relative to `θ₀`).** The reduction rests on
`log(p_{θ̂}/p_{a+Bβ̂}) = log(p_{θ̂}/p_{θ₀}) − log(p_{a+Bβ̂}/p_{θ₀})`, which is FALSE at the Lean
junk values: with `p_{θ̂}(x) = 0` and `p_{a+Bβ̂}(x), p_{θ₀}(x) > 0` the left side is
`Real.log 0 = 0` while the right side is `−log(p_{a+Bβ̂}(x)/p_{θ₀}(x)) ≠ 0`. The minimal
repair is that the densities do not vanish where `p_{θ₀}` does not — the pattern named
`HasCommonSupport` in `PointEstimation/InformationInequality/Basic.lean`, here in its
relative form. It is not a positivity assumption on the model (`∀ θ x, 0 < p_θ x` would be
false for many standard models); it only says that no parameter kills a point that `θ₀`
keeps, which is exactly what the source assumes implicitly whenever it manipulates
likelihood ratios. Under it, the sample being drawn from `μ.withDensity p_{θ₀}` makes all
three densities nonzero a.e. along the sample (`ae_forall_density_ne_zero`) and the splitting
is the ordinary `Real.log_div`. -/
private lemma logLR_affine_sub_scoreDiff_tendstoInMeasure {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (a : EuclideanSpace ℝ (Fin k)) (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hB : Function.Injective B)
    (β₀ : EuclideanSpace ℝ (Fin m)) (hθ₀ : θ₀ = a + B β₀)
    -- AMENDMENT: common support relative to `θ₀`; see the docstring
    (hsupp : ∀ (θ : EuclideanSpace ℝ (Fin k)) (x : 𝓧),
      M.density θ₀ x ≠ 0 → M.density θ x ≠ 0)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (hℓB : ℓB = fun x => ContinuousLinearMap.adjoint B (ℓ x))
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (hJB : ∀ u v : EuclideanSpace ℝ (Fin m),
      fisherInformation (restrictFamily M a B) μ β₀ ℓB u v = ⟪u, mulVecE JB v⟫)
    [∀ β : EuclideanSpace ℝ (Fin m), ∀ n,
      IsProbabilityMeasure (productMeasure (restrictFamily M a B) μ β n)]
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    (est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin m)) (hest₀ : ∀ n, Measurable (est₀ n))
    (hlin₀ : IsAsymptoticallyLinear (restrictFamily M a B) μ β₀ ℓB JB est₀)
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int : Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    (δ : ℝ) (hδ : 0 < δ)
    (henv : ∀ θ θ' : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ‖θ' - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x / M.density θ₀ x)
          - Real.log (M.density θ' x / M.density θ₀ x) - ⟪θ - θ', ℓ x⟫|
        ≤ Menv x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
          - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|})
        atTop (𝓝 0) := by
  classical
  have hℓB' : Measurable ℓB := by
    rw [hℓB]; exact (ContinuousLinearMap.adjoint B).continuous.measurable.comp hℓ
  have hJBrel := inner_mulVecE_pullback M μ a B β₀ θ₀ hθ₀ ℓ ℓB hℓB J hJ JB hJB
  have hJB_pd : JB.PosDef := posDef_pullback B hB J hJ_pd JB hJBrel
  have hDQM_B := differentiableQuadraticMean_restrictFamily M μ a B θ₀ β₀ hθ₀ ℓ ℓB hℓB hDQM
  have hPDF_B := isPDFOf_restrictFamily M μ a B hPDF
  have hMB_meas : Measurable (fun x => |Menv x| * ‖B‖ ^ 2) := hMenv_meas.abs.mul_const _
  have hdenB : (fun x => ENNReal.ofReal ((restrictFamily M a B).density β₀ x))
      = fun x => ENNReal.ofReal (M.density θ₀ x) := by
    funext x; rw [hθ₀]; rfl
  have hMB_int : Integrable (fun x => |Menv x| * ‖B‖ ^ 2)
      (μ.withDensity fun x => ENNReal.ofReal ((restrictFamily M a B).density β₀ x)) := by
    rw [hdenB]
    exact hMenv_int.abs.mul_const _
  have hδB : (0 : ℝ) < δ / (‖B‖ + 1) := by positivity
  -- the full model at `θ₀`
  have h1 := logLR_sub_score_tendstoInMeasure M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ est hest hlin
    Menv hMenv_meas hMenv_int δ hδ henv
  -- the restricted model at `β₀`
  have h2 := logLR_sub_score_tendstoInMeasure (restrictFamily M a B) μ hPDF_B β₀ ℓB hℓB'
    hDQM_B JB hJB_pd hJB est₀ hest₀ hlin₀ (fun x => |Menv x| * ‖B‖ ^ 2) hMB_meas hMB_int
    (δ / (‖B‖ + 1)) hδB
    (envelope_restrictFamily M a B β₀ θ₀ hθ₀ ℓ ℓB hℓB Menv δ hδ henv)
  exact tendstoInMeasure_of_split M μ θ₀ a B β₀ hθ₀ hsupp ℓ J ℓB JB est est₀ h1 h2

/-- **The likelihood ratio statistic is asymptotically chi-squared (affine composite null).**

Let the null hypothesis restrict `θ` to the affine subspace `a + range B` of codimension
`p = k − m` (equivalently, `A(θ − a) = 0` for a `p × k` matrix `A` of rank `p`), let `θ̂ₙ` be
efficient in the full model and let `β̂ₙ` be efficient in the restricted model
`β ↦ P_{a + Bβ}`. Then, under `P^n_{θ₀}` for any `θ₀ = a + Bβ₀` in the null,
`2 log(Lₙ(θ̂ₙ)/Lₙ(a + Bβ̂ₙ)) ⇝ χ²ₚ`: the degrees of freedom count the restrictions, i.e. the
dimension of the full parameter space minus that of the null. -/
theorem logLR_tendsto_chiSquared_affine {m p : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws of the full model; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: joint measurability of `(θ, x) ↦ p_θ(x)`; needed for the likelihood-ratio
    -- statistic to be a measurable function of the sample (see `measurable_logLRStatistic`)
    (hjoint : Measurable (Function.uncurry M.density))
    -- LEAN-ONLY: the codimension is the difference of dimensions and is nondegenerate
    (hdim : m + p = k) (hp : 0 < p)
    -- USER-INPUT: a chart of the affine null subspace: base point and injective direction map
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hB : Function.Injective B)
    -- USER-INPUT: the null parameter, given in the chart
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ = a + B β₀)
    -- USER-INPUT (AMENDMENT): common support relative to `θ₀` — no parameter kills a point
    -- that `θ₀` keeps. Without it the likelihood-ratio splitting
    -- `log(p_{θ̂}/p_{a+Bβ̂}) = log(p_{θ̂}/p_{θ₀}) − log(p_{a+Bβ̂}/p_{θ₀})` that identifies the
    -- affine statistic as the difference of two simple-null statistics is FALSE at the Lean
    -- junk values; see `logLR_affine_sub_scoreDiff_tendstoInMeasure`. This is the source's
    -- implicit standing assumption whenever it manipulates likelihood ratios, and is strictly
    -- weaker than strict positivity of the densities
    (hsupp : ∀ (θ : EuclideanSpace ℝ (Fin k)) (x : 𝓧),
      M.density θ₀ x ≠ 0 → M.density θ x ≠ 0)
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- LEAN-ONLY: name for the score of the restricted model — the adjoint image of `ℓ`
    (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (hℓB : ℓB = fun x => ContinuousLinearMap.adjoint B (ℓ x))
    -- LEAN-ONLY: matrix form of the restricted model's Fisher information at `β₀`
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (hJB : ∀ u v : EuclideanSpace ℝ (Fin m),
      fisherInformation (restrictFamily M a B) μ β₀ ℓB u v = ⟪u, mulVecE JB v⟫)
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws of the restricted model
    [∀ β : EuclideanSpace ℝ (Fin m), ∀ n,
      IsProbabilityMeasure (productMeasure (restrictFamily M a B) μ β n)]
    -- USER-INPUT: an efficient estimator sequence in the full model
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: an efficient estimator sequence in the restricted model, in the chart
    (est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin m))
    (hest₀ : ∀ n, Measurable (est₀ n))
    (hlin₀ : IsAsymptoticallyLinear (restrictFamily M a B) μ β₀ ℓB JB est₀)
    -- USER-INPUT: the envelope function of the second-order expansion, with finite mean
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int :
      Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- USER-INPUT: radius of the neighbourhood on which the envelope condition holds
    (δ : ℝ) (hδ : 0 < δ)
    -- USER-INPUT: two-point second-order envelope condition on the log-density increment.
    -- AMENDED: the source's one-point condition (the case `θ' = θ₀`) makes the uniform LAN
    -- expansion this proof needs provably false; see `sup_LAN_remainder_tendsto`.
    (henv : ∀ θ θ' : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ‖θ' - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x / M.density θ₀ x)
          - Real.log (M.density θ' x / M.density θ₀ x) - ⟪θ - θ', ℓ x⟫|
        ≤ Menv x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map
        (logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n))
      (MultipleTesting.chiSquared p) := by
  -- Score-difference surrogate converges to `χ²ₚ`; the affine LR differs from it by `o_P(1)`.
  haveI : NeZero p := ⟨hp.ne'⟩
  have hℓB' : Measurable ℓB := by
    rw [hℓB]; exact (ContinuousLinearMap.adjoint B).continuous.measurable.comp hℓ
  have hscorediff := affineScoreDiff_tendsto_chiSquared M μ hPDF hdim hp a B hB β₀ θ₀ hθ₀
    ℓ hℓ hDQM J hJ_pd hJ ℓB hℓB JB hJB
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n ω => scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)
    (Y := fun n => logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n)
    (fun n => (((continuous_gaussQuadratic J⁻¹).measurable.comp
        (measurable_scoreSum ℓ hℓ n)).sub
        ((continuous_gaussQuadratic JB⁻¹).measurable.comp
          (measurable_scoreSum ℓB hℓB' n))).aemeasurable)
    (fun n => (measurable_logLRStatistic M hjoint est (fun n ω => a + B (est₀ n ω)) hest
        (fun n => (B.continuous.measurable.comp (hest₀ n)).const_add a) n).aemeasurable)
    hscorediff ?_
  intro ε hε
  have h := logLR_affine_sub_scoreDiff_tendstoInMeasure M μ hPDF θ₀ a B hB β₀ hθ₀ hsupp
    ℓ hℓ hDQM J hJ_pd hJ ℓB hℓB JB hJB
    est hest hlin est₀ hest₀ hlin₀ Menv hMenv_meas hMenv_int δ hδ henv ε hε
  have hset : (fun n => (productMeasure M μ θ₀ n).real
      {ω : Fin n → 𝓧 | ε ≤ dist (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)
        (logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω)})
      = (fun n => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
          - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|}) := by
    funext n; congr 1; ext ω
    simp only [Set.mem_setOf_eq, Real.dist_eq, abs_sub_comm]
  rw [hset]; exact h

end StatLean.HypothesisTesting


