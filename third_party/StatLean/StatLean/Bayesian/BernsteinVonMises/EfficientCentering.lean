module
public import StatLean.Bayesian.BernsteinVonMises.PosteriorNormality
public import StatLean.Bayesian.ForMathlib.GaussianTV

@[expose] public section

/-!
# Efficient centering: the posterior is approximately `N(θ̂ₙ, (n I_{θ₀})⁻¹)`

The corollary after the Bernstein–von Mises theorem (vdV p. 144): the centering `Δ_{n,θ₀}` may be
replaced by
any **asymptotically efficient** estimator sequence. If `√n(θ̂ₙ − θ₀) − Δ_{n,θ₀} → 0` in
`P^n_{θ₀}`-probability, then on the *original* parameter scale
`‖ P_{Θ̄ | X₁..Xₙ} − N(θ̂ₙ, (n I_{θ₀})⁻¹) ‖ → 0` in `P^n_{θ₀}`-probability.

* `bernstein_von_mises_efficient_centering` — the headline;
* the version on the local scale is an immediate intermediate: replace the mean of the
  Gaussian in `bernstein_von_mises` by `√n(θ̂ₙ − θ₀)` via the mean-shift TV bound.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, p. 144
(the two displays following the proof of Lemma 10.3, including
`‖P_{Θ̄|X₁..Xₙ} − N(θ̂ₙ, n⁻¹ I⁻¹_θ)‖ → 0`).

**Proof formalization notes.** vdV derives the hypothesis `√n(θ̂ₙ − θ) − Δ_{n,θ} →ᵖ 0` from
best-regularity via his Theorem 8.14; here the expansion itself is taken as the definition
of asymptotic efficiency (USER-INPUT), which is exactly what the argument consumes —
best-regularity theory is out of scope for this batch. Chain: triangle with
`bernstein_von_mises`; `tvDist_multivariateGaussian_le` (Pinsker) turns the vanishing
center difference into vanishing TV between the two Gaussians; the unrescaling to the
original parameter scale is `tvDist_map_measurableEmbedding` along `bvmLocalUnscale`
(an affine measurable equivalence for `n ≥ 1`), which sends the local posterior to the
posterior of `Θ̄` and `N(√n(θ̂ₙ−θ₀), J⁻¹)` to `N(θ̂ₙ, (nJ)⁻¹)`
(`multivariateGaussian_map_const_add` + `multivariateGaussian_map_toEuclideanCLM`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace Matrix
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure)
open StatLean.Minimaxity (tvDist)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- Translation of a multivariate Gaussian (general mean version of
`multivariateGaussian_map_const_add`). -/
private lemma multivariateGaussian_map_add_const (S : Matrix (Fin k) (Fin k) ℝ)
    (a v : EuclideanSpace ℝ (Fin k)) :
    (multivariateGaussian a S).map (fun x => v + x) = multivariateGaussian (v + a) S := by
  rw [← AsymptoticStatistics.multivariateGaussian_map_const_add S a,
    Measure.map_map (by fun_prop) (by fun_prop),
    ← AsymptoticStatistics.multivariateGaussian_map_const_add S (v + a)]
  congr 1
  funext x
  simp [Function.comp, add_assoc]

/-- **The local rescaling transports the Gaussians of the two statements**: for `n ≥ 1`,
`θ ↦ √n(θ − θ₀)` sends `N(m, n⁻¹ S)` to `N(√n(m − θ₀), S)`. -/
private lemma multivariateGaussian_map_bvmLocalScale {n : ℕ} (hn : 1 ≤ n)
    (θ₀ m : EuclideanSpace ℝ (Fin k)) {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef) :
    (multivariateGaussian m ((n : ℝ)⁻¹ • S)).map (bvmLocalScale θ₀ n)
      = multivariateGaussian (Real.sqrt n • (m - θ₀)) S := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
  set c : ℝ := Real.sqrt n with hcdef
  set A : Matrix (Fin k) (Fin k) ℝ := c • (1 : Matrix (Fin k) (Fin k) ℝ) with hAdef
  have hSn : ((n : ℝ)⁻¹ • S).PosSemidef := hS.smul (by positivity)
  have hcov : A * ((n : ℝ)⁻¹ • S) * Aᴴ = S := by
    rw [hAdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      smul_smul, smul_smul]
    rw [hc, mul_inv_cancel₀ hnR.ne', one_smul]
  have hAx : ∀ x : EuclideanSpace ℝ (Fin k),
      Matrix.toEuclideanCLM (𝕜 := ℝ) A x = c • x := by
    intro x
    rw [hAdef, map_smul, map_one]
    rfl
  have hcomp : bvmLocalScale θ₀ n
      = (fun y : EuclideanSpace ℝ (Fin k) => (-(c • θ₀)) + y) ∘
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A) := by
    funext θ
    simp only [Function.comp_apply, hAx, bvmLocalScale, ← hcdef]
    rw [smul_sub]
    abel
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ProbabilityTheory.multivariateGaussian_map_toEuclideanCLM A m hSn, hcov, hAx,
    multivariateGaussian_map_add_const]
  congr 1
  rw [smul_sub]
  abel

/-- **Quantitative mean-shift continuity**: for a fixed positive-definite covariance and a
tolerance `t`, Gaussians whose means are within `ε` are within `t` in total variation. This
converts `hest_eff` (an `ε`-`δ` statement about the centerings) into a statement about the
Gaussians. -/
private lemma exists_eps_tvDist_multivariateGaussian_lt
    {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) {t : ℝ≥0∞} (ht : 0 < t) (htop : t ≠ ∞) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a b : EuclideanSpace ℝ (Fin k), ‖a - b‖ < ε →
      tvDist (multivariateGaussian a S) (multivariateGaussian b S) < t := by
  set s : ℝ := t.toReal with hsdef
  have hs : 0 < s := ENNReal.toReal_pos ht.ne' htop
  have hst : ENNReal.ofReal s = t := ENNReal.ofReal_toReal htop
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ with hTdef
  set L : ℝ := ‖T‖ + 1 with hLdef
  have hL : 0 < L := by positivity
  have hsqrtL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  refine ⟨s / Real.sqrt L, by positivity, fun a b hd => ?_⟩
  have hq : ⟪a - b, T (a - b)⟫ ≤ L * ‖a - b‖ ^ 2 := by
    calc ⟪a - b, T (a - b)⟫ ≤ ‖a - b‖ * ‖T (a - b)‖ := real_inner_le_norm _ _
      _ ≤ ‖a - b‖ * (‖T‖ * ‖a - b‖) := by
          exact mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ ≤ L * ‖a - b‖ ^ 2 := by
          rw [hLdef]; nlinarith [norm_nonneg (a - b), sq_nonneg ‖a - b‖]
  have hd2 : ‖a - b‖ ^ 2 ≤ (s / Real.sqrt L) ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg (a - b)) hd.le
    nlinarith
  have hLe : L * (s / Real.sqrt L) ^ 2 = s ^ 2 := by
    rw [div_pow, Real.sq_sqrt hL.le]
    field_simp
  have hqs : ⟪a - b, T (a - b)⟫ ≤ s ^ 2 := by
    refine le_trans hq ?_
    rw [← hLe]
    exact mul_le_mul_of_nonneg_left hd2 hL.le
  refine lt_of_le_of_lt (tvDist_multivariateGaussian_le hS a b) ?_
  have hstep : (ENNReal.ofReal (⟪a - b, T (a - b)⟫ / 4)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (s ^ 2 / 4)) ^ (1 / 2 : ℝ) := by
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    exact ENNReal.ofReal_le_ofReal (by linarith)
  refine lt_of_le_of_lt hstep ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← hst]
  refine (ENNReal.ofReal_lt_ofReal_iff hs).2 ?_
  have hhalf : (s ^ 2 / 4 : ℝ) ^ (1 / 2 : ℝ) = s / 2 := by
    rw [← Real.sqrt_eq_rpow, show (s ^ 2 / 4 : ℝ) = (s / 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hhalf]
  linarith

/-- **Efficient centering** (vdV p. 144). Under the hypotheses of the Bernstein–von Mises theorem,
if the
estimator sequence `θ̂ₙ` is asymptotically efficient — i.e.
`√n(θ̂ₙ − θ₀) − Δ_{n,θ₀} → 0` in `P^n_{θ₀}`-probability — then the posterior law of `Θ̄`
itself is approximated by `N(θ̂ₙ, (n)⁻¹ J⁻¹)` in total variation, in
`P^n_{θ₀}`-probability: for every `δ > 0`,
`P^n_{θ₀} { tvDist( (iidKernel κ n)†π ·, N(θ̂ₙ, n⁻¹ • J⁻¹) ) ≥ δ } → 0`. -/
theorem bernstein_von_mises_efficient_centering
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information matrix; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the uniform-tests condition; vdV §10.2
    (hTests : UniformlyConsistentTests M μ θ₀)
    -- USER-INPUT: the prior condition; vdV §10.2
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {est : ∀ n : ℕ, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)}
    -- LEAN-ONLY: measurable estimators (regularity)
    (hest_meas : ∀ n, Measurable (est n))
    -- USER-INPUT: asymptotic efficiency of `θ̂ₙ` in expansion form,
    -- `√n(θ̂ₙ − θ₀) − Δ_{n,θ₀} →ᵖ 0`; vdV p. 144 (via Thm 8.14, best-regular ⟺ expansion)
    (hest_eff : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω | ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - bvmEffScore J sc n ω‖})
        atTop (𝓝 0)) :
    ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => productMeasure M μ θ₀ n
          {ω | δ ≤ tvDist (((iidKernel κ n)†π) ω)
            (multivariateGaussian (est n ω) ((n : ℝ)⁻¹ • J⁻¹))})
        atTop (𝓝 0) := by
  classical
  haveI hProb : ∀ (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      IsProbabilityMeasure (productMeasure M μ θ n) :=
    fun θ n =>
      AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
        M μ hPDF θ n
  have hJinv : (J⁻¹).PosDef := hJ_pd.inv
  have hBvM := bernstein_von_mises hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ
  -- Real-valued convergence in probability upgrades to the `ℝ≥0∞`-valued form.
  have hreal : ∀ (S : ∀ n : ℕ, Set (Fin n → 𝓧)),
      Tendsto (fun n => (productMeasure M μ θ₀ n).real (S n)) atTop (𝓝 0) →
      Tendsto (fun n => productMeasure M μ θ₀ n (S n)) atTop (𝓝 0) := by
    intro S hS
    rw [ENNReal.tendsto_nhds_zero]
    intro t htpos
    have ht1 : (0 : ℝ≥0∞) < min t 1 := lt_min htpos zero_lt_one
    have ht1top : min t 1 ≠ ∞ := ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
    have hu : 0 < (min t 1).toReal := ENNReal.toReal_pos ht1.ne' ht1top
    filter_upwards [hS.eventually_lt_const hu] with n hn
    refine le_trans (le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hn.le)) ?_
    · exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    · rw [ENNReal.ofReal_toReal ht1top]
      exact min_le_left _ _
  intro δ hδ
  set δ₁ : ℝ≥0∞ := min δ 1 with hδ₁def
  have hδ₁pos : 0 < δ₁ := lt_min hδ zero_lt_one
  have hδ₁top : δ₁ ≠ ∞ := ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
  have hhalf : (0 : ℝ≥0∞) < δ₁ / 2 := ENNReal.half_pos hδ₁pos.ne'
  obtain ⟨ε, hεpos, hεlt⟩ := exists_eps_tvDist_multivariateGaussian_lt hJinv hhalf
    (by simpa using ENNReal.div_ne_top hδ₁top (by norm_num))
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.half_pos hη.ne'
  have hA : ∀ᶠ n : ℕ in atTop, productMeasure M μ θ₀ n
      {ω | δ₁ / 2 ≤ bvmTV κ π θ₀ J sc n ω} ≤ η / 2 := by
    have h := hBvM (δ₁ / 2) hhalf
    rw [ENNReal.tendsto_nhds_zero] at h
    exact h _ hη2
  have hB : ∀ᶠ n : ℕ in atTop, productMeasure M μ θ₀ n
      {ω | ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - bvmEffScore J sc n ω‖} ≤ η / 2 := by
    have h := hreal _ (hest_eff ε hεpos)
    rw [ENNReal.tendsto_nhds_zero] at h
    exact h _ hη2
  filter_upwards [hA, hB, eventually_ge_atTop 1] with n hAn hBn hn
  -- On the local scale the two total-variation distances coincide.
  have hemb : MeasurableEmbedding (bvmLocalScale θ₀ n) :=
    MeasurableEquiv.measurableEmbedding
      { toFun := bvmLocalScale θ₀ n
        invFun := bvmLocalUnscale θ₀ n
        left_inv := bvmLocalUnscale_bvmLocalScale θ₀ hn
        right_inv := bvmLocalScale_bvmLocalUnscale θ₀ hn
        measurable_toFun := measurable_bvmLocalScale θ₀ n
        measurable_invFun := measurable_bvmLocalUnscale θ₀ n }
  have hrescale : ∀ ω : Fin n → 𝓧,
      tvDist (((iidKernel κ n)†π) ω) (multivariateGaussian (est n ω) ((n : ℝ)⁻¹ • J⁻¹))
        = tvDist (bvmLocalPosterior κ π θ₀ n ω)
            (multivariateGaussian (Real.sqrt n • (est n ω - θ₀)) J⁻¹) := by
    intro ω
    rw [← tvDist_map_measurableEmbedding _ _ hemb,
      multivariateGaussian_map_bvmLocalScale hn θ₀ (est n ω) hJinv.posSemidef,
      bvmLocalPosterior, Kernel.map_apply _ (measurable_bvmLocalScale θ₀ n)]
  -- The deviation event is contained in the union of the two controlled events.
  have hincl : {ω : Fin n → 𝓧 | δ ≤ tvDist (((iidKernel κ n)†π) ω)
        (multivariateGaussian (est n ω) ((n : ℝ)⁻¹ • J⁻¹))}
      ⊆ {ω | δ₁ / 2 ≤ bvmTV κ π θ₀ J sc n ω}
        ∪ {ω | ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - bvmEffScore J sc n ω‖} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hdiff : ‖bvmEffScore J sc n ω - Real.sqrt n • (est n ω - θ₀)‖ < ε := by
      rw [← norm_neg, neg_sub]
      exact h2
    have hG : tvDist (bvmGaussian J sc n ω)
        (multivariateGaussian (Real.sqrt n • (est n ω - θ₀)) J⁻¹) < δ₁ / 2 :=
      hεlt _ _ hdiff
    haveI : IsProbabilityMeasure (bvmGaussian J sc n ω) := by
      unfold bvmGaussian; infer_instance
    have htri : tvDist (bvmLocalPosterior κ π θ₀ n ω)
        (multivariateGaussian (Real.sqrt n • (est n ω - θ₀)) J⁻¹)
        ≤ bvmTV κ π θ₀ J sc n ω + tvDist (bvmGaussian J sc n ω)
            (multivariateGaussian (Real.sqrt n • (est n ω - θ₀)) J⁻¹) :=
      tvDist_triangle _ _ _
    have hlt : tvDist (((iidKernel κ n)†π) ω)
        (multivariateGaussian (est n ω) ((n : ℝ)⁻¹ • J⁻¹)) < δ₁ := by
      rw [hrescale ω]
      refine lt_of_le_of_lt htri ?_
      calc _ < δ₁ / 2 + δ₁ / 2 := ENNReal.add_lt_add h1 hG
        _ = δ₁ := ENNReal.add_halves δ₁
    exact absurd hω (not_le.2 (lt_of_lt_of_le hlt (min_le_left _ _)))
  calc productMeasure M μ θ₀ n {ω | δ ≤ tvDist (((iidKernel κ n)†π) ω)
        (multivariateGaussian (est n ω) ((n : ℝ)⁻¹ • J⁻¹))}
      ≤ productMeasure M μ θ₀ n
          ({ω | δ₁ / 2 ≤ bvmTV κ π θ₀ J sc n ω}
            ∪ {ω | ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - bvmEffScore J sc n ω‖}) :=
        measure_mono hincl
    _ ≤ productMeasure M μ θ₀ n {ω | δ₁ / 2 ≤ bvmTV κ π θ₀ J sc n ω}
          + productMeasure M μ θ₀ n
            {ω | ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - bvmEffScore J sc n ω‖} :=
        measure_union_le _ _
    _ ≤ η / 2 + η / 2 := by gcongr
    _ = η := ENNReal.add_halves η

end StatLean.Bayesian
