module
public import StatLean.Bayesian.BernsteinVonMises.Defs
public import StatLean.Bayesian.BernsteinVonMises.PriorSmallBall
public import StatLean.AsymptoticStatistics.ForMathlib.ContiguityIntegralComparison

@[expose] public section

/-!
# The contiguity swap: base law vs localized prior mixtures

vdV's proof of the Bernstein–von Mises theorem constantly exchanges the base law `P^n_{θ₀}` with the
Bayesian
mixture `P_{n,U} = ∫ P^n_{θ} dΠ̄ₙ(θ)` over the shrinking prior ball `U/√n` ("we may always
exchange `P_{n,0}` and `P_{n,U}`", p. 141). This file supplies that swap:

* `bvmMixture` — the localized prior mixture `P_{n,U} := iidKernel κ n ∘ₘ π[|B(θ₀, u/√n)]`;
* `bvmMixture_absolutelyContinuous` — `P_{n,U} ≪ κₙ ∘ₘ π` (the predictive), so
  predictive-null exceptional sets of the a.e. posterior identities are `P_{n,U}`-null
  **exactly**;
* `logLikelihood_weakConverges` — asymptotic log-normality of the local log-likelihood ratio
  under `P^n_{θ₀}` (score CLT + LAN residual + Slutsky);
* `mutuallyContiguous_local_alternative` — the support-free per-`h` mutual contiguity
  `P^n_{θ₀} ◁▷ P^n_{θ₀+h/√n}` (via the integral-comparison Le Cam lemma — no common-support
  hypothesis, unlike `contiguous_local_alternatives`);
* `mutuallyContiguous_mixture_base` — the mixture swap `P^n_{θ₀} ◁▷ P_{n,U}`;
* `measure_tendsto_zero_of_predictive_null` — predictive-null (measurable) event sequences
  are asymptotically `P^n_{θ₀}`-null.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Theorem 10.1, pp. 141–142 (the preliminary contiguity observations), and Chapter 6, §6.4
(Le Cam's first lemma).

**Proof formalization notes.** Per-`h` contiguity routes through
`Contiguity.mutuallyContiguous_of_log_normal_of_integral_comparison` with the comparison
supplied by `AsymptoticRepresentation.productMeasure_integral_comparison_boundedMeasurable`
(support-free; vdV §10.2 makes no common-support assumption). The mixture direction uses
the two-sided prior-vs-Lebesgue comparison on small balls (`PriorSmallBall`), an
`L¹`-subsequence extraction (`TendstoInMeasure.exists_seq_tendsto_ae`), a single-`h`
application of the per-`h` lemma along the subsequence (`Contiguous.comp_subseq`), and
`Filter.tendsto_of_subseq_tendsto`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation WeakConverges)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure scoreSum logLikelihood)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure_isProbabilityMeasure
  logLikelihood_measurable scoreSum_weakly_converges lanResidual_tendsto_productMeasure
  productMeasure_integral_comparison_boundedMeasurable)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- **Localized prior mixture** `P_{n,U}`: the marginal law of the `n`-sample when the
parameter is drawn from the prior conditioned to the shrinking ball `B(θ₀, u/√n)`
(vdV p. 141, "`P_{n,U}` for `U` a ball of fixed radius around zero" — here expressed on the
original parameter scale). -/
noncomputable def bvmMixture (κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧) [IsMarkovKernel κ]
    (π : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure π]
    (θ₀ : EuclideanSpace ℝ (Fin k)) (u : ℝ) (n : ℕ) : Measure (Fin n → 𝓧) :=
  iidKernel κ n ∘ₘ (π[|Metric.ball θ₀ (u / Real.sqrt n)])

/-- The localized mixture is dominated by the predictive `κₙ ∘ₘ π` (with density bounded by
the inverse prior small-ball mass). In particular, predictive-null sets are
`bvmMixture`-null. -/
theorem bvmMixture_absolutelyContinuous (u : ℝ) (n : ℕ) :
    bvmMixture κ π θ₀ u n ≪ iidKernel κ n ∘ₘ π := by
  have hc : (π[|Metric.ball θ₀ (u / Real.sqrt n)]) ≪ π := by
    rw [ProbabilityTheory.cond]
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _
  exact Measure.AbsolutelyContinuous.comp_right hc (iidKernel κ n)

/-- **Asymptotic log-normality of the local log-likelihood ratio** under `P^n_{θ₀}`:
`log(dP^n_{θ₀+h/√n}/dP^n_{θ₀}) ⇝ N(−v/2, v)` with `v = ⟪h, J h⟫` (vdV Theorem 7.2 +
the score CLT + Slutsky). -/
theorem logLikelihood_weakConverges
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (h : EuclideanSpace ℝ (Fin k)) (v : NNReal)
    -- LEAN-ONLY: `v` is the quadratic form `⟪h, J h⟫` packaged as `NNReal`
    (hv : (v : ℝ) = ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫) :
    WeakConverges (fun n => (productMeasure M μ θ₀ n).map (logLikelihood M θ₀ h n))
      (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
  classical
  haveI hProb : ∀ θ : EuclideanSpace ℝ (Fin k), ∀ n : ℕ,
      IsProbabilityMeasure (productMeasure M μ θ n) := fun θ n =>
    productMeasure_isProbabilityMeasure M μ hPDF θ n
  have h_one : ∫ x, M.density θ₀ x ∂μ = 1 := hPDF.density_integral_eq_one θ₀
  have hint : Integrable (M.density θ₀) μ := hPDF.density_integrable θ₀
  have h_one_perturb : ∀ t : ℝ, ∀ w : EuclideanSpace ℝ (Fin k),
      ∫ x, M.density (θ₀ + t • w) x ∂μ = 1 := fun _ _ => hPDF.density_integral_eq_one _
  have hint_perturb : ∀ t : ℝ, ∀ w : EuclideanSpace ℝ (Fin k),
      Integrable (M.density (θ₀ + t • w)) μ := fun _ _ => hPDF.density_integrable _
  have hScoreCLT := scoreSum_weakly_converges
    M μ θ₀ sc hsc h_one hint h_one_perturb hint_perturb hDQM J hJ_pd.posSemidef hJ
  have hΔ_meas : ∀ n, Measurable (scoreSum sc n) := by
    intro n
    unfold AsymptoticStatistics.AsymptoticRepresentation.scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hsc.comp (measurable_pi_apply i))).const_smul ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  -- The quadratic form as a dot product; `v` is its `toNNReal`.
  have hv_dot : (v : ℝ) = h.ofLp ⬝ᵥ J.mulVec h.ofLp := by
    rw [hv]
    change inner ℝ h ((Matrix.toEuclideanCLM (𝕜 := ℝ) J) h) = _
    rw [Matrix.inner_toEuclideanCLM]
  have hv_eq : v = (h.ofLp ⬝ᵥ J.mulVec h.ofLp).toNNReal := by
    rw [← hv_dot]; exact Real.toNNReal_coe.symm
  -- Step A: `⟪h, Δₙ⟫ ⇝ N(0, v)`.
  have h_inner_cont : Continuous (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫) :=
    continuous_const.inner continuous_id
  have h_inner_meas : Measurable (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫) :=
    h_inner_cont.measurable
  have h_scalarCLT :
      WeakConverges (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => ⟪h, scoreSum sc n ω⟫)) (ProbabilityTheory.gaussianReal 0 v) := by
    have h_comp : (fun n => (productMeasure M μ θ₀ n).map
          (fun ω => ⟪h, scoreSum sc n ω⟫))
        = fun n => ((productMeasure M μ θ₀ n).map (scoreSum sc n)).map
            (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫) :=
      funext fun n => (Measure.map_map h_inner_meas (hΔ_meas n)).symm
    rw [h_comp]
    have h_map := hScoreCLT.map h_inner_cont h_inner_meas
    rw [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal h
      hJ_pd.posSemidef] at h_map
    rwa [hv_eq]
  -- Step B: shift by `−v/2`.
  have h_sub_cont : Continuous (fun y : ℝ => y - (v : ℝ) / 2) := by fun_prop
  have h_sub_meas : Measurable (fun y : ℝ => y - (v : ℝ) / 2) := h_sub_cont.measurable
  have h_shiftedCLT :
      WeakConverges (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => ⟪h, scoreSum sc n ω⟫ - (v : ℝ) / 2))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
    have h_comp : (fun n => (productMeasure M μ θ₀ n).map
          (fun ω => ⟪h, scoreSum sc n ω⟫ - (v : ℝ) / 2))
        = fun n => ((productMeasure M μ θ₀ n).map
            (fun ω => ⟪h, scoreSum sc n ω⟫)).map (fun y : ℝ => y - (v : ℝ) / 2) :=
      funext fun n => (Measure.map_map h_sub_meas (h_inner_meas.comp (hΔ_meas n))).symm
    rw [h_comp]
    have h_map := h_scalarCLT.map h_sub_cont h_sub_meas
    rwa [ProbabilityTheory.gaussianReal_map_sub_const ((v : ℝ) / 2), zero_sub,
      ← neg_div] at h_map
  -- Step C: Slutsky absorbs the LAN residual.
  have h_lanRes := lanResidual_tendsto_productMeasure
    M μ θ₀ sc hsc h_one hint h_one_perturb hint_perturb hDQM J hJ h
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (fun n => ((h_inner_meas.comp (hΔ_meas n)).sub_const _).aemeasurable)
    (fun n => (logLikelihood_measurable M θ₀ h n).aemeasurable) h_shiftedCLT ?_
  intro ε hε
  have h_set_eq : ∀ n : ℕ,
      {ω : Fin n → 𝓧 | ε ≤ dist (⟪h, scoreSum sc n ω⟫ - (v : ℝ) / 2)
          (logLikelihood M θ₀ h n ω)}
        = {ω : Fin n → 𝓧 | ε ≤ |logLikelihood M θ₀ h n ω
            - (⟪h, scoreSum sc n ω⟫ - (1 / 2 : ℝ) *
              ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)|} := by
    intro n
    ext ω
    have hhalf : (v : ℝ) / 2
        = (1 / 2 : ℝ) * ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ := by
      rw [← hv]; ring
    simp only [Set.mem_setOf_eq, Real.dist_eq, hhalf]
    rw [abs_sub_comm]
  exact (h_lanRes ε hε).congr fun n =>
    congrArg (productMeasure M μ θ₀ n).real (h_set_eq n).symm

/-- **Support-free per-`h` mutual contiguity of the local alternatives**
`P^n_{θ₀} ◁▷ P^n_{θ₀+h/√n}` (vdV Example 6.5 for a DQM family; no common-support
hypothesis). -/
theorem mutuallyContiguous_local_alternative
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (h : EuclideanSpace ℝ (Fin k)) :
    AsymptoticStatistics.Contiguity.MutuallyContiguous (ι := ℕ)
      (Ω := fun n => Fin n → 𝓧) atTop
      (fun n => productMeasure M μ θ₀ n)
      (fun n => productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) := by
  classical
  haveI hProb : ∀ θ : EuclideanSpace ℝ (Fin k), ∀ n : ℕ,
      IsProbabilityMeasure (productMeasure M μ θ n) := fun θ n =>
    productMeasure_isProbabilityMeasure M μ hPDF θ n
  have hv_nn : 0 ≤ h.ofLp ⬝ᵥ J.mulVec h.ofLp := by
    have := hJ_pd.posSemidef.re_dotProduct_nonneg (x := (h.ofLp : Fin k → ℝ))
    simpa using this
  have hv : ((h.ofLp ⬝ᵥ J.mulVec h.ofLp).toNNReal : ℝ)
      = ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ := by
    rw [Real.coe_toNNReal _ hv_nn]
    change _ = inner ℝ h ((Matrix.toEuclideanCLM (𝕜 := ℝ) J) h)
    rw [Matrix.inner_toEuclideanCLM]
  have hcmp := productMeasure_integral_comparison_boundedMeasurable M μ θ₀ sc hsc hDQM hPDF h
  exact AsymptoticStatistics.Contiguity.mutuallyContiguous_of_log_normal_of_integral_comparison
    _ _ (fun n => logLikelihood M θ₀ h n)
    (fun n => logLikelihood_measurable M θ₀ h n)
    hcmp _ (logLikelihood_weakConverges hPDF hsc hDQM hJ_pd hJ h _ hv)

/-- LEAN-ONLY affine change of variables `θ = θ₀ + a • h` in a ball integral: the Jacobian is
the constant `a^k` (`k = dim`). -/
private lemma lintegral_ball_affine (θ₀ : EuclideanSpace ℝ (Fin k)) {a : ℝ} (ha : 0 < a)
    (u : ℝ) {F : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ θ in Metric.ball θ₀ (a * u), F θ
      = ENNReal.ofReal (a ^ k)
        * ∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u, F (θ₀ + a • hh) := by
  classical
  set T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := fun hh => θ₀ + a • hh with hT
  have hTmeas : Measurable T := by fun_prop
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have hmap : Measure.map T (volume : Measure (EuclideanSpace ℝ (Fin k)))
      = ENNReal.ofReal ((a ^ k)⁻¹) • (volume : Measure (EuclideanSpace ℝ (Fin k))) := by
    have h1 : Measure.map (fun hh : EuclideanSpace ℝ (Fin k) => a • hh) volume
        = ENNReal.ofReal |(a ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin k))))⁻¹|
            • (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
      Measure.map_addHaar_smul volume ha.ne'
    have h2 : T = (fun y : EuclideanSpace ℝ (Fin k) => θ₀ + y)
        ∘ (fun hh : EuclideanSpace ℝ (Fin k) => a • hh) := rfl
    rw [h2, ← Measure.map_map (measurable_const_add θ₀) (measurable_const_smul a), h1,
      Measure.map_smul, Measure.IsAddLeftInvariant.map_add_left_eq_self
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin k)))) θ₀]
    rw [hfr, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a ^ k)⁻¹)]
  have hball : MeasurableSet (Metric.ball θ₀ (a * u)) := measurableSet_ball
  have hball0 : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u) := measurableSet_ball
  have hmem : ∀ hh, (T hh ∈ Metric.ball θ₀ (a * u))
      ↔ hh ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u := by
    intro hh
    have e1 : dist (T hh) θ₀ = a * ‖hh‖ := by
      rw [hT]
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    have e2 : dist hh (0 : EuclideanSpace ℝ (Fin k)) = ‖hh‖ := dist_zero_right hh
    rw [Metric.mem_ball, Metric.mem_ball, e1, e2]
    exact mul_lt_mul_iff_right₀ ha
  have hind : ∀ hh, (Metric.ball θ₀ (a * u)).indicator F (T hh)
      = (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u).indicator (fun y => F (T y)) hh := by
    intro hh
    by_cases hmem' : hh ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u
    · rw [Set.indicator_of_mem ((hmem hh).mpr hmem'), Set.indicator_of_mem hmem']
    · rw [Set.indicator_of_notMem (fun hc => hmem' ((hmem hh).mp hc)),
        Set.indicator_of_notMem hmem']
  have hkey := (lintegral_map (μ := (volume : Measure (EuclideanSpace ℝ (Fin k))))
      (f := (Metric.ball θ₀ (a * u)).indicator F) (g := T)
      (hF.indicator hball) hTmeas).symm
  rw [hmap, lintegral_smul_measure, lintegral_indicator hball] at hkey
  simp_rw [hind] at hkey
  rw [lintegral_indicator hball0] at hkey
  rw [hkey, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (pow_pos ha k)),
    mul_inv_cancel₀ (pow_pos ha k).ne', ENNReal.ofReal_one, one_mul]

/-- LEAN-ONLY: measurability of `θ ↦ P^n_θ(A)` (the model is a Markov kernel). -/
private lemma measurable_productMeasure_apply
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x)) (n : ℕ)
    {A : Set (Fin n → 𝓧)} (hA : MeasurableSet A) :
    Measurable fun θ : EuclideanSpace ℝ (Fin k) => productMeasure M μ θ n A := by
  have hfun : (fun θ : EuclideanSpace ℝ (Fin k) => productMeasure M μ θ n A)
      = fun θ => iidKernel κ n θ A :=
    funext fun θ => by rw [productMeasure_eq_iidKernel_apply hκ θ n]
  rw [hfun]
  exact Kernel.measurable_coe _ hA

/-- LEAN-ONLY: the mixture evaluated on a measurable set, as a normalized prior average of the
per-parameter sample laws. -/
private lemma bvmMixture_apply
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    (u : ℝ) (n : ℕ) {A : Set (Fin n → 𝓧)} (hA : MeasurableSet A) :
    bvmMixture κ π θ₀ u n A
      = (π (Metric.ball θ₀ (u / Real.sqrt n)))⁻¹
          * ∫⁻ θ in Metric.ball θ₀ (u / Real.sqrt n), productMeasure M μ θ n A ∂π := by
  rw [bvmMixture, Measure.bind_apply hA (Kernel.aemeasurable _), ProbabilityTheory.cond,
    lintegral_smul_measure]
  congr 1
  exact lintegral_congr fun θ => by rw [productMeasure_eq_iidKernel_apply hκ θ n]

/-- **The contiguity swap** (vdV p. 141: "`P_{n,U} ◁▷ P_{n,0}`"): the base law and the
localized prior mixture are mutually contiguous, given the model and prior conditions of
the Bernstein–von Mises theorem. -/
theorem mutuallyContiguous_mixture_base
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {u : ℝ}
    -- LEAN-ONLY: nontrivial localization radius
    (hu : 0 < u) :
    AsymptoticStatistics.Contiguity.MutuallyContiguous (ι := ℕ)
      (Ω := fun n => Fin n → 𝓧) atTop
      (fun n => productMeasure M μ θ₀ n)
      (fun n => bvmMixture κ π θ₀ u n) := by
  classical
  haveI hProb : ∀ θ : EuclideanSpace ℝ (Fin k), ∀ n : ℕ,
      IsProbabilityMeasure (productMeasure M μ θ n) := fun θ n =>
    productMeasure_isProbabilityMeasure M μ hPDF θ n
  obtain ⟨D₁, hD₁pos, -, Cb, hCbT, hUp⟩ := prior_smallBall_upper hπ
  obtain ⟨D₂, hD₂pos, -, cb, hcb0, hLo⟩ := prior_smallBall_lower hπ
  obtain ⟨D, hDpos, hDD₁, hDD₂⟩ : ∃ D : ℝ, 0 < D ∧ D ≤ D₁ ∧ D ≤ D₂ :=
    ⟨min D₁ D₂, lt_min hD₁pos hD₂pos, min_le_left _ _, min_le_right _ _⟩
  -- Abbreviation for the fixed local ball `U = B(0, u)`.
  have hvU0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 hu).ne'
  have hvUT : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u) ≠ ∞ :=
    measure_ball_lt_top.ne
  have hcbT : cb ≠ ∞ := by
    intro hc
    have hsub : Metric.ball θ₀ D ⊆ Metric.ball θ₀ D₂ := Metric.ball_subset_ball hDD₂
    have hlow := hLo (Metric.ball θ₀ D) hsub measurableSet_ball
    rw [hc, ENNReal.top_mul (Metric.measure_ball_pos volume θ₀ hDpos).ne'] at hlow
    exact absurd (top_le_iff.mp hlow) (measure_ne_top π _)
  have hcv0 : cb * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u) ≠ 0 :=
    mul_ne_zero hcb0.ne' hvU0
  have hcvT : cb * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u) ≠ ∞ :=
    ENNReal.mul_ne_top hcbT hvUT
  have hCvT : Cb * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u) ≠ ∞ :=
    ENNReal.mul_ne_top hCbT hvUT
  -- Measurability of the localized integrand.
  have hKmeas : ∀ (n : ℕ) (A : Set (Fin n → 𝓧)), MeasurableSet A →
      Measurable fun hh : EuclideanSpace ℝ (Fin k) =>
        productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n A := by
    intro n A hA
    exact (measurable_productMeasure_apply hκ n hA).comp (by fun_prop)
  -- `u/√n → 0`, so eventually the shrinking ball is inside the comparison zone.
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hdivD : ∀ᶠ n : ℕ in atTop, u / Real.sqrt n ≤ D := by
    have hdiv : Tendsto (fun n : ℕ => u / Real.sqrt n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsqrt
    filter_upwards [hdiv (Iio_mem_nhds hDpos)] with n hn using le_of_lt hn
  -- **Core two-sided estimate**: the mixture mass and the localized Lebesgue average agree
  -- up to the fixed constants `cb`, `Cb`.
  have hcore : ∀ᶠ n : ℕ in atTop, ∀ A : Set (Fin n → 𝓧), MeasurableSet A →
      bvmMixture κ π θ₀ u n A
            * (cb * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))
          ≤ Cb * ∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
              productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n A ∂volume
        ∧ cb * ∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
              productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n A ∂volume
          ≤ bvmMixture κ π θ₀ u n A
              * (Cb * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u)) := by
    filter_upwards [eventually_ge_atTop 1, hdivD] with n hn1 hnD A hA
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have ha : 0 < (Real.sqrt n)⁻¹ := inv_pos.mpr hsq
    have hau : u / Real.sqrt n = (Real.sqrt n)⁻¹ * u := div_eq_inv_mul u (Real.sqrt n)
    have hBD : Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u) ⊆ Metric.ball θ₀ D :=
      Metric.ball_subset_ball (by rw [← hau]; exact hnD)
    have hB1 : Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u) ⊆ Metric.ball θ₀ D₁ :=
      hBD.trans (Metric.ball_subset_ball hDD₁)
    have hB2 : Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u) ⊆ Metric.ball θ₀ D₂ :=
      hBD.trans (Metric.ball_subset_ball hDD₂)
    -- Two-sided measure comparison, restricted to the shrinking ball.
    have hπup : π.restrict (Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u))
        ≤ Cb • volume.restrict (Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u)) := by
      refine Measure.le_iff.mpr fun s hs => ?_
      rw [Measure.restrict_apply hs, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs]
      exact hUp _ (Set.inter_subset_right.trans hB1) (hs.inter measurableSet_ball)
    have hπlo : cb • volume.restrict (Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u))
        ≤ π.restrict (Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u)) := by
      refine Measure.le_iff.mpr fun s hs => ?_
      rw [Measure.restrict_apply hs, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs]
      exact hLo _ (Set.inter_subset_right.trans hB2) (hs.inter measurableSet_ball)
    -- Change of variables: the Jacobian `z` cancels in the ratio.
    have hcv := lintegral_ball_affine θ₀ ha u (measurable_productMeasure_apply hκ n hA)
    have hcv1 := lintegral_ball_affine θ₀ ha u (F := fun _ => (1 : ℝ≥0∞)) measurable_const
    rw [setLIntegral_one, setLIntegral_one] at hcv1
    have hz0 : ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (pow_pos ha k)).ne'
    have hzT : ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k) ≠ ∞ := ENNReal.ofReal_ne_top
    -- Numerator and denominator bounds.
    have hNup : ∫⁻ θ in Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u), productMeasure M μ θ n A ∂π
        ≤ Cb * (ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
            * ∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
                productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n A ∂volume) := by
      have h1 := lintegral_mono' (f := fun θ => productMeasure M μ θ n A)
        (g := fun θ => productMeasure M μ θ n A) hπup le_rfl
      rwa [lintegral_smul_measure, smul_eq_mul, hcv] at h1
    have hNlo : cb * (ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
            * ∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
                productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n A ∂volume)
        ≤ ∫⁻ θ in Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u), productMeasure M μ θ n A ∂π := by
      have h1 := lintegral_mono' (f := fun θ => productMeasure M μ θ n A)
        (g := fun θ => productMeasure M μ θ n A) hπlo le_rfl
      rwa [lintegral_smul_measure, smul_eq_mul, hcv] at h1
    have hπBup : π (Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u))
        ≤ Cb * (ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
            * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u)) := by
      rw [← hcv1]
      exact hUp _ hB1 measurableSet_ball
    have hπBlo : cb * (ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
            * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))
        ≤ π (Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u)) := by
      rw [← hcv1]
      exact hLo _ hB2 measurableSet_ball
    have hπB0 : π (Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u)) ≠ 0 := by
      intro hzero
      rw [hzero, nonpos_iff_eq_zero, mul_eq_zero] at hπBlo
      rcases hπBlo with hz | hz
      · exact hcb0.ne' hz
      · rcases mul_eq_zero.mp hz with hz' | hz'
        · exact hz0 hz'
        · exact hvU0 hz'
    have hπBT : π (Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u)) ≠ ∞ := measure_ne_top π _
    -- The mixture mass times the prior ball mass is the numerator.
    have hQ := bvmMixture_apply (θ₀ := θ₀) (π := π) hκ u n hA
    rw [hau] at hQ
    have hQmul : bvmMixture κ π θ₀ u n A * π (Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u))
        = ∫⁻ θ in Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u), productMeasure M μ θ n A ∂π := by
      rw [hQ, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hπB0 hπBT, one_mul]
    constructor
    · refine (ENNReal.mul_le_mul_iff_left hz0 hzT).mp ?_
      calc bvmMixture κ π θ₀ u n A
              * (cb * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))
              * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
          = bvmMixture κ π θ₀ u n A * (cb * (ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
              * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))) := by ring
        _ ≤ bvmMixture κ π θ₀ u n A * π (Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u)) :=
            mul_le_mul_right hπBlo _
        _ = ∫⁻ θ in Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u), productMeasure M μ θ n A ∂π := hQmul
        _ ≤ Cb * (ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
              * ∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
                  productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n A ∂volume) := hNup
        _ = Cb * (∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
                  productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n A ∂volume)
              * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k) := by ring
    · refine (ENNReal.mul_le_mul_iff_left hz0 hzT).mp ?_
      calc cb * (∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
                  productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n A ∂volume)
              * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
          = cb * (ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
              * ∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
                  productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n A ∂volume) := by ring
        _ ≤ ∫⁻ θ in Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u), productMeasure M μ θ n A ∂π := hNlo
        _ = bvmMixture κ π θ₀ u n A * π (Metric.ball θ₀ ((Real.sqrt n)⁻¹ * u)) := hQmul.symm
        _ ≤ bvmMixture κ π θ₀ u n A * (Cb * (ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
              * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))) :=
            mul_le_mul_right hπBup _
        _ = bvmMixture κ π θ₀ u n A
              * (Cb * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))
              * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k) := by ring
  constructor
  · -- `P^n_{θ₀} ⊲ P_{n,U}`: the localized average vanishes by dominated convergence.
    intro A hA_meas hA_tendsto
    have hK : Tendsto (fun n : ℕ => ∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
        productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n (A n) ∂volume) atTop (𝓝 0) := by
      have hlim : ∀ᵐ hh ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u)),
          Tendsto (fun n : ℕ => productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n (A n))
            atTop (𝓝 0) :=
        Filter.Eventually.of_forall fun hh =>
          (mutuallyContiguous_local_alternative hPDF hsc hDQM hJ_pd hJ hh).1 A hA_meas hA_tendsto
      have hdct := MeasureTheory.tendsto_lintegral_of_dominated_convergence
        (μ := volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))
        (F := fun (n : ℕ) hh => productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n (A n))
        (f := fun _ => (0 : ℝ≥0∞)) (bound := fun _ => (1 : ℝ≥0∞))
        (fun n => hKmeas n (A n) (hA_meas n))
        (fun n => Filter.Eventually.of_forall fun hh => prob_le_one)
        (by simpa using hvUT) hlim
      simpa using hdct
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hCK : Tendsto (fun n : ℕ => Cb * ∫⁻ hh in Metric.ball
        (0 : EuclideanSpace ℝ (Fin k)) u,
        productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n (A n) ∂volume) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hK (Or.inr hCbT)
      simpa using this
    have hεpos : 0 < ε * (cb * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u)) :=
      pos_iff_ne_zero.mpr (mul_ne_zero hε.ne' hcv0)
    filter_upwards [hcore, (ENNReal.tendsto_nhds_zero.mp hCK) _ hεpos] with n hn hCKn
    exact (ENNReal.mul_le_mul_iff_left hcv0 hcvT).mp
      (((hn (A n) (hA_meas n)).1).trans hCKn)
  · -- `P_{n,U} ⊲ P^n_{θ₀}`: an `L¹` subsequence extraction plus per-`h` contiguity.
    intro A hA_meas hA_tendsto
    have hK : Tendsto (fun n : ℕ => ∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
        productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • hh) n (A n) ∂volume) atTop (𝓝 0) := by
      have hQ0 : Tendsto (fun n : ℕ => bvmMixture κ π θ₀ u n (A n)
          * (Cb * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const hA_tendsto (Or.inr hCvT)
        simpa using this
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      have hεpos : 0 < cb * ε := pos_iff_ne_zero.mpr (mul_ne_zero hcb0.ne' hε.ne')
      filter_upwards [hcore, (ENNReal.tendsto_nhds_zero.mp hQ0) _ hεpos] with n hn hQn
      exact (ENNReal.mul_le_mul_iff_right hcb0.ne' hcbT).mp
        (((hn (A n) (hA_meas n)).2).trans hQn)
    -- Suppose the base masses do not vanish; extract a bad subsequence.
    by_contra hcon
    rw [ENNReal.tendsto_nhds_zero] at hcon
    push_neg at hcon
    obtain ⟨ε, hε, hfreq⟩ := hcon
    obtain ⟨φ, hφ, hφlt⟩ := Filter.extraction_of_frequently_atTop hfreq
    -- Along `φ`, the localized average still vanishes; pass to a.e. convergence.
    have hKφ : Tendsto (fun i : ℕ => ∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
        productMeasure M μ (θ₀ + (Real.sqrt (φ i))⁻¹ • hh) (φ i) (A (φ i)) ∂volume)
        atTop (𝓝 0) := hK.comp hφ.tendsto_atTop
    have hTIM : MeasureTheory.TendstoInMeasure
        (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))
        (fun (i : ℕ) hh => (productMeasure M μ (θ₀ + (Real.sqrt (φ i))⁻¹ • hh)
          (φ i) (A (φ i))).toReal) atTop (fun _ => (0 : ℝ)) := by
      refine MeasureTheory.tendstoInMeasure_of_ne_top ?_
      intro δ hδ hδT
      have hbound : ∀ i : ℕ,
          (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))
            {hh | δ ≤ edist ((productMeasure M μ (θ₀ + (Real.sqrt (φ i))⁻¹ • hh)
              (φ i) (A (φ i))).toReal) (0 : ℝ)}
          ≤ (∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
              productMeasure M μ (θ₀ + (Real.sqrt (φ i))⁻¹ • hh) (φ i) (A (φ i)) ∂volume)
              / δ := by
        intro i
        have hset : {hh : EuclideanSpace ℝ (Fin k) |
              δ ≤ edist ((productMeasure M μ (θ₀ + (Real.sqrt (φ i))⁻¹ • hh)
                (φ i) (A (φ i))).toReal) (0 : ℝ)}
            = {hh | δ ≤ productMeasure M μ (θ₀ + (Real.sqrt (φ i))⁻¹ • hh)
                (φ i) (A (φ i))} := by
          ext hh
          have hedist : edist ((productMeasure M μ (θ₀ + (Real.sqrt (φ i))⁻¹ • hh)
              (φ i) (A (φ i))).toReal) (0 : ℝ)
              = productMeasure M μ (θ₀ + (Real.sqrt (φ i))⁻¹ • hh) (φ i) (A (φ i)) := by
            rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal (measure_ne_top _ _)]
          simp only [Set.mem_setOf_eq, hedist]
        rw [hset]
        exact meas_ge_le_lintegral_div
          (hKmeas (φ i) (A (φ i)) (hA_meas _)).aemeasurable hδ.ne' hδT
      have hdivz : Tendsto (fun i : ℕ =>
          (∫⁻ hh in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u,
            productMeasure M μ (θ₀ + (Real.sqrt (φ i))⁻¹ • hh) (φ i) (A (φ i)) ∂volume)
              / δ) atTop (𝓝 0) := by
        simp only [ENNReal.div_eq_inv_mul]
        have := ENNReal.Tendsto.const_mul hKφ (Or.inr (ENNReal.inv_ne_top.mpr hδ.ne'))
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdivz
        (fun _ => zero_le) hbound
    obtain ⟨ms, hms, hae⟩ := hTIM.exists_seq_tendsto_ae
    -- A good local direction `hh₀` inside `U`.
    obtain ⟨hh₀, -, hgood⟩ : ∃ hh₀, hh₀ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u ∧
        Tendsto (fun i : ℕ => (productMeasure M μ (θ₀ + (Real.sqrt (φ (ms i)))⁻¹ • hh₀)
          (φ (ms i)) (A (φ (ms i)))).toReal) atTop (𝓝 0) := by
      by_contra hno
      push_neg at hno
      rw [MeasureTheory.ae_iff] at hae
      refine hvU0 (le_antisymm ?_ (zero_le))
      calc volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u)
          = (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))
              (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u) :=
            (Measure.restrict_apply_self _ _).symm
        _ ≤ (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u))
              {hh | ¬ Tendsto (fun i : ℕ => (productMeasure M μ
                (θ₀ + (Real.sqrt (φ (ms i)))⁻¹ • hh) (φ (ms i)) (A (φ (ms i)))).toReal)
                atTop (𝓝 0)} := measure_mono fun hh hhU => hno hh hhU
        _ = 0 := hae
    -- Lift to `ℝ≥0∞` and apply the per-`h` contiguity along the subsequence.
    have hgood' : Tendsto (fun i : ℕ => productMeasure M μ
        (θ₀ + (Real.sqrt (φ (ms i)))⁻¹ • hh₀) (φ (ms i)) (A (φ (ms i)))) atTop (𝓝 0) := by
      have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp hgood
      simpa [Function.comp_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h1
    have hcontig :=
      ((mutuallyContiguous_local_alternative hPDF hsc hDQM hJ_pd hJ hh₀).2).comp_subseq
        (hφ.comp hms)
    have hfin := hcontig (fun i => A (φ (ms i))) (fun i => hA_meas _) hgood'
    have hev : ∀ᶠ i : ℕ in atTop,
        productMeasure M μ θ₀ (φ (ms i)) (A (φ (ms i))) < ε := hfin (Iio_mem_nhds hε)
    obtain ⟨i, hi⟩ := hev.exists
    exact absurd hi (not_lt.mpr (le_of_lt (hφlt (ms i))))

/-- **Predictive-null events are asymptotically base-null**: if measurable events `Nₙ` are
null for the predictive `κₙ ∘ₘ π`, then `P^n_{θ₀}(Nₙ) → 0`. This discharges the exceptional
sets of the a.e. posterior identities (`posterior_iid_eq_withDensity_prod_likelihood` etc.)
under the base law. -/
theorem measure_tendsto_zero_of_predictive_null
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {N : ∀ n : ℕ, Set (Fin n → 𝓧)}
    -- LEAN-ONLY: measurable exceptional events (regularity)
    (hN_meas : ∀ n, MeasurableSet (N n))
    -- LEAN-ONLY: the events are predictive-null (they carry the a.e. identities)
    (hN : ∀ n, (iidKernel κ n ∘ₘ π) (N n) = 0) :
    Tendsto (fun n => productMeasure M μ θ₀ n (N n)) atTop (𝓝 0) := by
  have hmix : ∀ n : ℕ, bvmMixture κ π θ₀ 1 n (N n) = 0 := fun n =>
    bvmMixture_absolutelyContinuous (θ₀ := θ₀) (π := π) (κ := κ) 1 n (hN n)
  refine (mutuallyContiguous_mixture_base hPDF hsc hDQM hJ_pd hJ hκ hπ
    (u := 1) one_pos).2 N hN_meas ?_
  simpa [hmix] using tendsto_const_nhds (x := (0 : ℝ≥0∞)) (f := atTop (α := ℕ))

end StatLean.Bayesian
