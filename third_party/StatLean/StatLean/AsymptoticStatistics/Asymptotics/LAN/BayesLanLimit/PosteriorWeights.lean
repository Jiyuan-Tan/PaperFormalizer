module
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.LANExpansion
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF

@[expose] public section

/-!
# Posterior-weight weak convergence under the LAN sequence (vdV §8.5)

Under the LAN local alternative `Q_n := P^n_{θ₀ + h₀/√n}`, the normalised score
sum `Δ_n` weakly converges to a shifted multivariate Gaussian `N(J·h₀, J)`.
This is an input for the Bayes-estimator weak convergence and the Portmanteau
lsc-bridge to `bayesRisk`.

The proof is wired via Theorem 7.2 (iii) (LAN expansion), Le Cam's third lemma,
and the score CLT. The Le Cam 3 transfer routes through the DQM-derived
asymptotic integral comparison rather than the exact change-of-measure identity.

Headline declaration: `posteriorWeights_weakly_converges_under_lan`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal MatrixOrder

open AsymptoticStatistics

namespace AsymptoticStatistics.Asymptotics.LAN
namespace LocalAsymptoticMinimax
namespace BayesLanLimit

/-- Parameter space (matches `LocalAsymptoticMinimax.Θ`). -/
abbrev Θ (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)

/-- Target space of the statistic (matches `LocalAsymptoticMinimax.𝓨`). -/
abbrev 𝓨 (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

variable {k : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- ## Score sum `Δ_n` weakly converges under the perturbed LAN law.

Under the LAN local alternative `Q_n := P^n_{θ₀ + h₀/√n}`, the normalised
score sum `Δ_n(ω) := (1/√n) ∑_{i<n} ℓ(ω_i)` weakly converges (in the sense of
`WeakConverges`) to a shifted multivariate Gaussian `N(J·h₀, J)` on the
parameter space `Θ k = EuclideanSpace ℝ (Fin k)`.

This lemma is indexed by the local alternative `h₀ : Θ k` alone: no prior
structure appears, so it is the input that any `bayes_risk_lan_limit`-style
outer averaging (discrete prior, Gaussian-τ prior, …) consumes, by integrating
or summing it against its prior of choice.

This is a Le Cam third lemma application:
* **Under `P^n_{θ₀}`** (base law), the score CLT (`scoreSum_weakly_converges`)
  gives `Δ_n ⇝ N(0, J)`.
* **LAN expansion (Theorem 7.2 (iii))** rewrites the log-likelihood ratio
  `log (P^n_{θ₀+h₀/√n} / P^n_{θ₀})` as `h₀⊤ Δ_n - ½ h₀⊤ J h₀ + o_{P^n_{θ₀}}(1)`.
* **Le Cam 3 (`weak_limit_under_Q_of_lecam_third`)** combines the two: the
  perturbed law `P^n_{θ₀+h₀/√n}` is contiguous to `P^n_{θ₀}` with log-likelihood
  `h₀⊤ Δ_n - ½ h₀⊤ J h₀ + o_P(1)`, so pushforwards by `Δ_n` weakly converge to
  the **tilted** marginal of the joint Gaussian
  `N(0, J) ⊗ N(h₀⊤ · - ½ h₀⊤ J h₀, h₀⊤ J h₀)` — equivalently `N(J·h₀, J)` on
  `Θ k` (Cameron-Martin shift of a centered Gaussian by its log-density linear
  functional).

Hypotheses:
* `M, μ, θ₀, ℓ, hℓ, hDQM, hPDF, hM_joint, h_one_perturb, hint_perturb` are the
  regularity conditions on the parametric family that vdV §7.5 / §7.2 require
  for LAN to even be statable. Mirrors the hypothesis bundle in
  `LAN_expansion_iii` and `scoreSum_weakly_converges`.
* `J, hJ, hJ_fisher`: Fisher information matrix at `θ₀`, which vdV §8.11 requires
  non-singular (`PosDef`). The matching identity `hJ_fisher` says the abstract
  Fisher quadratic form coincides with the explicit matrix.
* No common-support assumption is needed: the Le Cam 3 transfer routes through
  the DQM-derived asymptotic integral comparison rather than the exact
  change-of-measure identity.
* `h₀ : Θ k` is the local alternative, the direction along which the perturbed
  law is taken.

**Proof outline**:
1. Build the **probability space** `Ω_n := Fin n → 𝓧` with `P_n := P^n_{θ₀}`,
   `Q_n := P^n_{θ₀+h₀/√n}`. Both are probability measures by
   `productMeasure_isProbabilityMeasure`.
2. **Score CLT under `P_n`** (`scoreSum_weakly_converges`):
   `(P_n).map (scoreSum ℓ n) ⇝ multivariateGaussian 0 J`.
3. **LAN log-likelihood expansion** (`LAN_expansion_iii`): the residual
   `log (Q_n / P_n) - h₀⊤ Δ_n + ½ h₀⊤ J h₀ → 0` in `P_n`-measure.
4. **Joint weak convergence** of `(Δ_n, log(Q_n/P_n))` under `P_n` to
   `(Δ, h₀⊤ Δ - ½ h₀⊤ J h₀)` for `Δ ∼ N(0, J)` — by `WeakConverges.map` +
   Slutsky-type combination of (2) and (3).
5. **Le Cam 3** (`weak_limit_under_Q_of_lecam_third_of_integral_comparison`):
   tilts the joint law from `P_n` to `Q_n`, projects onto the `Δ_n` coordinate;
   the tilted marginal of `(Δ, h₀⊤Δ - ½h₀⊤Jh₀)` on `Δ` is `N(J·h₀, J)`. The
   exact change-of-measure identity is replaced by the DQM-derived asymptotic
   integral comparison; uniform integrability is discharged via
   `uniform_integrability_exp_L_of_integral_tendsto_one`.
-/
theorem posteriorWeights_weakly_converges_under_lan
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (hPDF : IsPDFOf M μ)
    -- regularity; `ParametricFamily.density_meas` only gives per-θ).
    (_hM_joint : Measurable (Function.uncurry M.density))
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    -- (vdV §7.2; same bundle as `LAN_expansion_iii` / `scoreSum_weakly_converges`).
    (h_one_perturb : ∀ t : ℝ, ∀ u : Θ k, ∫ x, M.density (θ₀ + t • u) x ∂μ = 1)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ k, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (h₀ : Θ k) :
    -- Conclusion: under `P^n_{θ₀+h₀/√n}`, the pushforward of `Δ_n := scoreSum ℓ n`
    -- weakly converges to the shifted multivariate Gaussian `N(J·h₀, J)`.
    WeakConverges
      (fun n : ℕ =>
        (AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h₀) n).map
          (AsymptoticRepresentation.scoreSum ℓ n))
      (multivariateGaussian
        ((WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h₀))) J) := by
  classical
  -- Per-θ probability-measure typeclass for `productMeasure`.
  haveI hProb : ∀ θ : Θ k, ∀ n : ℕ,
      IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ n) :=
    fun θ n => AsymptoticRepresentation.productMeasure_isProbabilityMeasure M μ hPDF θ n
  -- Unpack `hPDF` into the per-parameter integrability/normalisation pair.
  have h_one : ∫ x, M.density θ₀ x ∂μ = 1 := hPDF.density_integral_eq_one θ₀
  have hint : Integrable (M.density θ₀) μ := hPDF.density_integrable θ₀
  -- Score CLT under `P_n := P^n_{θ₀}`: `Δ_n ⇝ N(0, J)`.
  have hScoreCLT :
      WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (AsymptoticRepresentation.scoreSum ℓ n))
        (multivariateGaussian (0 : Θ k) J) :=
    AsymptoticRepresentation.scoreSum_weakly_converges M μ θ₀ ℓ hℓ h_one hint
      h_one_perturb hint_perturb hDQM J hJ.posSemidef hJ_fisher
  -- Affine tilt `g(δ) := ⟪h₀, δ⟫ - ½ ⟪h₀, J h₀⟫_Mat`. Continuous and measurable.
  set Jh₀ : Θ k :=
    (WithLp.equiv 2 (Fin k → ℝ)).symm (J.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h₀))
    with hJh₀_def
  set c : ℝ := (1 / 2 : ℝ) * ⟪h₀, Jh₀⟫ with hc_def
  set g : Θ k → ℝ := fun δ => ⟪h₀, δ⟫ - c with hg_def
  have hg_cont : Continuous g :=
    (continuous_const.inner continuous_id).sub continuous_const
  have hg_meas : Measurable g := hg_cont.measurable
  -- Score sum measurability.
  have hΔ_meas : ∀ n, Measurable (AsymptoticRepresentation.scoreSum ℓ n) := by
    intro n
    unfold AsymptoticRepresentation.scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  -- Diagonal map `δ ↦ (δ, g δ)`, continuous and measurable.
  set diag : Θ k → Θ k × ℝ := fun δ => (δ, g δ) with hdiag_def
  have hdiag_cont : Continuous diag := continuous_id.prodMk hg_cont
  have hdiag_meas : Measurable diag := hdiag_cont.measurable
  -- The joint limit `π = (multivariateGaussian 0 J).map diag`.
  set π : Measure (Θ k × ℝ) := (multivariateGaussian (0 : Θ k) J).map diag with hπ_def
  haveI hπ_prob : IsProbabilityMeasure π := by
    refine Measure.isProbabilityMeasure_map hdiag_meas.aemeasurable
  -- Joint weak convergence of `(Δ_n, g(Δ_n))` under `P_n` to `π`.
  have h_joint_lin :
      WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => (AsymptoticRepresentation.scoreSum ℓ n ω, g (AsymptoticRepresentation.scoreSum ℓ
              n ω))))
        π := by
    have h_map := hScoreCLT.map hdiag_cont hdiag_meas
    -- Rewrite `((P_n).map Δ_n).map diag = (P_n).map (diag ∘ Δ_n)`.
    have h_rewrite : ∀ n,
        ((AsymptoticRepresentation.productMeasure M μ θ₀ n).map (AsymptoticRepresentation.scoreSum ℓ
            n)).map diag
          = (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
              (fun ω => (AsymptoticRepresentation.scoreSum ℓ n ω, g
                  (AsymptoticRepresentation.scoreSum ℓ n ω))) := by
      intro n
      rw [Measure.map_map hdiag_meas (hΔ_meas n)]
      rfl
    intro f
    have := h_map f
    simp_rw [h_rewrite] at this
    exact this
  -- LAN residual under `P_n`: `logLikelihood = g(Δ_n) + o_P(1)` (vdV §7.2 (iii)).
  have h_lanRes := AsymptoticRepresentation.lanResidual_tendsto_productMeasure
    M μ θ₀ ℓ hℓ h_one hint h_one_perturb hint_perturb hDQM J hJ_fisher h₀
  -- Slutsky: replace `g(Δ_n)` by `logLikelihood` in the second coordinate.
  have h_joint_logLik :
      WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => (AsymptoticRepresentation.scoreSum ℓ n ω,
            AsymptoticRepresentation.logLikelihood M θ₀ h₀ n ω)))
        π := by
    -- `dist((Δ_n, g(Δ_n)), (Δ_n, logLik n)) = |g(Δ_n) - logLik n|` →_P 0.
    have hX_meas : ∀ n, AEMeasurable
        (fun ω : Fin n → 𝓧 => (AsymptoticRepresentation.scoreSum ℓ n ω, g
            (AsymptoticRepresentation.scoreSum ℓ n ω)))
        (AsymptoticRepresentation.productMeasure M μ θ₀ n) := fun n =>
      ((hΔ_meas n).prodMk (hg_meas.comp (hΔ_meas n))).aemeasurable
    have hY_meas : ∀ n, AEMeasurable
        (fun ω : Fin n → 𝓧 => (AsymptoticRepresentation.scoreSum ℓ n ω,
          AsymptoticRepresentation.logLikelihood M θ₀ h₀ n ω))
        (AsymptoticRepresentation.productMeasure M μ θ₀ n) := fun n =>
      ((hΔ_meas n).prodMk (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h₀
          n)).aemeasurable
    refine WeakConverges.slutsky_of_tendstoInMeasure_dist hX_meas hY_meas h_joint_lin ?_
    intro ε hε
    -- The product-metric distance reduces to `|g(Δ_n) - logLik n|`.
    have h_set_eq : ∀ n,
        {ω : Fin n → 𝓧 |
            ε ≤ dist (AsymptoticRepresentation.scoreSum ℓ n ω, g (AsymptoticRepresentation.scoreSum
                ℓ n ω))
              (AsymptoticRepresentation.scoreSum ℓ n ω, AsymptoticRepresentation.logLikelihood M θ₀
                  h₀ n ω)}
          = {ω | ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h₀ n ω
                   - (⟪h₀, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (1/2 : ℝ) * ⟪h₀, Jh₀⟫)|} := by
      intro n
      ext ω
      simp only [Set.mem_setOf_eq, Prod.dist_eq, dist_self, Real.dist_eq, hg_def, hc_def]
      rw [max_eq_right (abs_nonneg _), abs_sub_comm]
    simp_rw [h_set_eq]
    exact h_lanRes ε hε
  -- The contiguity footing replaces the exact change-of-measure identity
  -- `Q n = (P n).withDensity (exp ∘ logLikelihood)`. The integral-comparison
  -- companions below are derived internally from `hDQM` + `hPDF` and feed the
  -- contiguity-footing Le Cam variants.
  have h_exp_int_full :=
    AsymptoticRepresentation.productMeasure_exp_logLikelihood_integrable M μ θ₀ ℓ hℓ hDQM hPDF h₀
  have h_mass_full :=
    AsymptoticRepresentation.productMeasure_integral_exp_logLikelihood_tendsto_one M μ θ₀ ℓ hℓ hDQM
        hPDF h₀
  -- The marginal `π.map snd` is the affine pushforward of `N(0, J)` by `g`,
  -- but we won't need this directly — UI and integrability come from the
  -- Gaussian-MGF of `multivariateGaussian 0 J` against `exp(g · )`.
  -- Marginal log-likelihood CLT under `P_n`: `logLikelihood ⇝ N(-v/2, v)` with
  -- `v := h₀.ofLp ⬝ᵥ J·h₀.ofLp = ⟪h₀, J h₀⟫_Mat`.
  set v : NNReal := (h₀.ofLp ⬝ᵥ J.mulVec h₀.ofLp).toNNReal with hv_def
  have hv_nn : 0 ≤ h₀.ofLp ⬝ᵥ J.mulVec h₀.ofLp := by
    have := hJ.posSemidef.re_dotProduct_nonneg (x := (h₀.ofLp : Fin k → ℝ))
    simpa using this
  have hv_coe : (v : ℝ) = h₀.ofLp ⬝ᵥ J.mulVec h₀.ofLp :=
    Real.coe_toNNReal _ hv_nn
  have hv_eq_inner : (v : ℝ) = ⟪h₀, Jh₀⟫ := by
    rw [hv_coe, hJh₀_def]
    -- `⟪h₀, (WithLp.equiv 2 _).symm (J.mulVec h₀.ofLp)⟫ = h₀.ofLp ⬝ᵥ J.mulVec h₀.ofLp`.
    change _ = inner ℝ h₀ ((Matrix.toEuclideanCLM (𝕜 := ℝ) J) h₀)
    rw [Matrix.inner_toEuclideanCLM]
  have hLogLik_weak :
      WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (AsymptoticRepresentation.logLikelihood M θ₀ h₀ n))
        (gaussianReal (-(v : ℝ) / 2) v) := by
    -- Step A: `⟨h₀, Δ_n⟩ ⇝ N(0, v)` via continuous-mapping + Gaussian projection.
    have h_inner_cont : Continuous (fun y : Θ k => ⟪h₀, y⟫) :=
      continuous_const.inner continuous_id
    have h_inner_meas : Measurable (fun y : Θ k => ⟪h₀, y⟫) := h_inner_cont.measurable
    have h_compA : (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h₀, AsymptoticRepresentation.scoreSum ℓ n ω⟫))
        = (fun n => ((AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (AsymptoticRepresentation.scoreSum ℓ n)).map (fun y : Θ k => ⟪h₀, y⟫)) := by
      funext n
      exact (Measure.map_map h_inner_meas (hΔ_meas n)).symm
    have h_scalarCLT :
        WeakConverges
          (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => ⟪h₀, AsymptoticRepresentation.scoreSum ℓ n ω⟫))
          (gaussianReal 0 v) := by
      rw [h_compA]
      have h_map := hScoreCLT.map h_inner_cont h_inner_meas
      rwa [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal h₀
        hJ.posSemidef] at h_map
    -- Step B: Shift by `-v/2` to get `⟨h₀, Δ_n⟩ - v/2 ⇝ N(-v/2, v)`.
    have h_sub_cont : Continuous (fun y : ℝ => y - (v : ℝ) / 2) := by fun_prop
    have h_sub_meas : Measurable (fun y : ℝ => y - (v : ℝ) / 2) := h_sub_cont.measurable
    have h_compB : (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h₀, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (v : ℝ) / 2))
        = (fun n => ((AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => ⟪h₀, AsymptoticRepresentation.scoreSum ℓ n ω⟫)).map
              (fun y : ℝ => y - (v : ℝ) / 2)) := by
      funext n
      exact (Measure.map_map h_sub_meas (h_inner_meas.comp (hΔ_meas n))).symm
    have h_shiftedCLT :
        WeakConverges
          (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => ⟪h₀, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (v : ℝ) / 2))
          (gaussianReal (-(v : ℝ) / 2) v) := by
      rw [h_compB]
      have h_map := h_scalarCLT.map h_sub_cont h_sub_meas
      rw [ProbabilityTheory.gaussianReal_map_sub_const ((v : ℝ) / 2),
        zero_sub, ← neg_div] at h_map
      exact h_map
    -- Step C: Slutsky absorbs the LAN residual to land at `logLikelihood`.
    have hc_as_v : (v : ℝ) / 2 = c := by
      rw [hc_def, hv_eq_inner]; ring
    have hX_ae : ∀ n, AEMeasurable
        (fun ω : Fin n → 𝓧 => ⟪h₀, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (v : ℝ) / 2)
        (AsymptoticRepresentation.productMeasure M μ θ₀ n) := fun n =>
      ((h_inner_meas.comp (hΔ_meas n)).sub_const _).aemeasurable
    have hY_ae : ∀ n, AEMeasurable (AsymptoticRepresentation.logLikelihood M θ₀ h₀ n)
        (AsymptoticRepresentation.productMeasure M μ θ₀ n) := fun n =>
      (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h₀ n).aemeasurable
    have h_dist_tendsto : ∀ ε > 0, Tendsto
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 | ε ≤ dist
            (⟪h₀, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (v : ℝ) / 2)
            (AsymptoticRepresentation.logLikelihood M θ₀ h₀ n ω)})
        atTop (𝓝 0) := by
      intro ε hε
      have h_set_eq : ∀ n,
          {ω : Fin n → 𝓧 | ε ≤ dist
            (⟪h₀, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (v : ℝ) / 2)
            (AsymptoticRepresentation.logLikelihood M θ₀ h₀ n ω)}
            = {ω | ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h₀ n ω
                - (⟪h₀, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (1/2 : ℝ) * ⟪h₀, Jh₀⟫)|} := by
        intro n
        ext ω
        simp only [Set.mem_setOf_eq, Real.dist_eq, hc_as_v, hc_def]
        rw [abs_sub_comm]
      simp_rw [h_set_eq]
      exact h_lanRes ε hε
    exact WeakConverges.slutsky_of_tendstoInMeasure_dist hX_ae hY_ae h_shiftedCLT
      h_dist_tendsto
  -- Uniform integrability of `exp(logLikelihood)` under `P_n` via the
  -- contiguity-footing variant `uniform_integrability_exp_L_of_integral_tendsto_one`,
  -- fed by the integral-comparison companions.
  have h_UI := Contiguity.uniform_integrability_exp_L_of_integral_tendsto_one
    (Ω := fun n => Fin n → 𝓧)
    (fun n => AsymptoticRepresentation.productMeasure M μ θ₀ n)
    (fun n => AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h₀) n)
    (fun n => AsymptoticRepresentation.logLikelihood M θ₀ h₀ n)
    (fun n => AsymptoticRepresentation.logLikelihood_measurable M θ₀ h₀ n)
    h_exp_int_full h_mass_full v hLogLik_weak
  -- Recast `π` through the diagonal trick: build `π_E : Measure (Θ k × Θ k)` whose
  -- second marginal is `mvG 0 J`, then push along the affine tilt to recover `π`.
  -- This unlocks `integrable_exp_tilt` / `integral_exp_tilt_eq_one` from `GaussianMGF`.
  haveI hMvG_prob : IsProbabilityMeasure (multivariateGaussian (0 : Θ k) J) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  set diagE : Θ k → Θ k × Θ k := fun δ => (δ, δ) with hdiagE_def
  have hdiagE_meas : Measurable diagE := measurable_id.prodMk measurable_id
  set π_E : Measure (Θ k × Θ k) :=
    (multivariateGaussian (0 : Θ k) J).map diagE with hπE_def
  haveI hπE_prob : IsProbabilityMeasure π_E :=
    Measure.isProbabilityMeasure_map hdiagE_meas.aemeasurable
  have hπE_snd : π_E.map Prod.snd = multivariateGaussian (0 : Θ k) J := by
    rw [hπE_def, Measure.map_map measurable_snd hdiagE_meas]
    -- `Prod.snd ∘ diagE = id`.
    have h_id : (Prod.snd ∘ diagE) = (id : Θ k → Θ k) := rfl
    rw [h_id, Measure.map_id]
  -- The affine tilt map.
  set tilt_map : Θ k × Θ k → Θ k × ℝ := fun p => (p.1, ⟪h₀, p.2⟫ - c) with htilt_def
  have htilt_meas : Measurable tilt_map := by
    refine measurable_fst.prodMk ?_
    exact ((continuous_const.inner continuous_id).measurable.comp measurable_snd).sub_const _
  -- Identify `π = π_E.map tilt_map`.
  have hπ_eq : π = π_E.map tilt_map := by
    rw [hπE_def, hπ_def]
    rw [Measure.map_map htilt_meas hdiagE_meas]
    rfl
  -- Get integrability + integral=1 from the Gaussian MGF brick.
  have h_exp_int_πtilt : Integrable (fun q : Θ k × ℝ => Real.exp q.2)
      (π_E.map (fun p : Θ k × Θ k =>
        (p.1, ⟪h₀, p.2⟫ - (1 / 2 : ℝ) *
          ⟪h₀, (WithLp.equiv 2 _).symm
            (J.mulVec ((WithLp.equiv 2 _) h₀))⟫))) :=
    ProbabilityTheory.integrable_exp_tilt π_E J hJ.posSemidef hπE_snd h₀
  have h_exp_int_πtilt_eq_one : ∫ q, Real.exp q.2
        ∂(π_E.map (fun p : Θ k × Θ k =>
          (p.1, ⟪h₀, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h₀, (WithLp.equiv 2 _).symm
              (J.mulVec ((WithLp.equiv 2 _) h₀))⟫))) = 1 :=
    ProbabilityTheory.integral_exp_tilt_eq_one π_E J hJ.posSemidef hπE_snd h₀
  -- Match: that pushforward equals `π_E.map tilt_map = π`.
  have h_tilt_eq : (fun p : Θ k × Θ k =>
        (p.1, ⟪h₀, p.2⟫ - (1 / 2 : ℝ) *
          ⟪h₀, (WithLp.equiv 2 _).symm
            (J.mulVec ((WithLp.equiv 2 _) h₀))⟫))
      = tilt_map := by
    funext p; simp only [htilt_def, hc_def, hJh₀_def]
  rw [h_tilt_eq, ← hπ_eq] at h_exp_int_πtilt h_exp_int_πtilt_eq_one
  -- Main integral-comparison bound (DQM-derived asymptotic singular-mass control),
  -- replacing the exact change-of-measure identity. The statistic is `scoreSum ℓ`.
  have h_int_cmp :=
    AsymptoticRepresentation.productMeasure_integral_comparison M μ θ₀ ℓ hℓ hDQM hPDF
      (fun n => AsymptoticRepresentation.scoreSum ℓ n) hΔ_meas h₀
  -- Apply Le Cam's third lemma via the contiguity-footing variant.
  have h_lecam := Contiguity.weak_limit_under_Q_of_lecam_third_of_integral_comparison
    (Ω := fun n => Fin n → 𝓧) (E := Θ k)
    (fun n => AsymptoticRepresentation.productMeasure M μ θ₀ n)
    (fun n => AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h₀) n)
    (fun n => AsymptoticRepresentation.scoreSum ℓ n)
    (fun n => AsymptoticRepresentation.logLikelihood M θ₀ h₀ n)
    hΔ_meas (fun n => AsymptoticRepresentation.logLikelihood_measurable M θ₀ h₀ n)
    h_int_cmp π h_joint_logLik h_UI h_exp_int_πtilt h_exp_int_πtilt_eq_one
  -- Identify the target `((π.withDensity (exp ∘ snd)).map fst)` with
  -- `multivariateGaussian (J h₀) J` using the Esscher-tilt identity.
  -- Step 1: `(π.withDensity (exp ∘ snd)).map fst = (mvG 0 J).withDensity (exp ∘ g) .map id`,
  -- via `withDensity_map_eq_map_withDensity` + `Measure.map_map` (Prod.fst ∘ diag = id).
  have h_density_simplify :
      ((π.withDensity (fun q : Θ k × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst)
        = (multivariateGaussian (0 : Θ k) J).withDensity
            (fun y => ENNReal.ofReal (Real.exp (g y))) := by
    rw [hπ_def]
    have h_snd_meas : Measurable (fun q : Θ k × ℝ => ENNReal.ofReal (Real.exp q.2)) :=
      (Real.continuous_exp.measurable.comp measurable_snd).ennreal_ofReal
    rw [Measure.withDensity_map_eq_map_withDensity (multivariateGaussian (0 : Θ k) J)
      diag hdiag_meas (fun q : Θ k × ℝ => ENNReal.ofReal (Real.exp q.2)) h_snd_meas]
    rw [Measure.map_map measurable_fst hdiag_meas]
    -- `Prod.fst ∘ diag = id` and the density `(exp ∘ snd) ∘ diag = exp ∘ g`.
    have h_id : (Prod.fst ∘ diag) = (id : Θ k → Θ k) := rfl
    rw [h_id, Measure.map_id]
    rfl
  -- Step 2: rewrite `g` to match the form expected by `multivariateGaussian_withDensity_exp_shift`.
  -- `g y = ⟪h₀, y⟫ - c = ⟪h₀, y⟫ - (h₀.ofLp ⬝ᵥ J.mulVec h₀.ofLp) / 2`.
  have hc_dotProduct : c = (h₀.ofLp ⬝ᵥ J.mulVec h₀.ofLp) / 2 := by
    rw [hc_def, hJh₀_def]
    -- `⟪h₀, (toEuclideanCLM J) h₀⟫ = h₀.ofLp ⬝ᵥ J.mulVec h₀.ofLp`.
    have : ⟪h₀, (WithLp.equiv 2 (Fin k → ℝ)).symm
          (J.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h₀))⟫
        = h₀.ofLp ⬝ᵥ J.mulVec h₀.ofLp := by
      change inner ℝ h₀ ((Matrix.toEuclideanCLM (𝕜 := ℝ) J) h₀) = _
      rw [Matrix.inner_toEuclideanCLM]
    rw [this]; ring
  -- Apply Esscher tilt.
  have h_esscher :
      (multivariateGaussian (0 : Θ k) J).withDensity
          (fun y => ENNReal.ofReal (Real.exp (g y)))
        = multivariateGaussian (Matrix.toEuclideanCLM (𝕜 := ℝ) J h₀) J := by
    have h_g_eq : (fun y : Θ k => ENNReal.ofReal (Real.exp (g y)))
        = fun y => ENNReal.ofReal (Real.exp (⟪h₀, y⟫
          - (h₀.ofLp ⬝ᵥ J.mulVec h₀.ofLp) / 2)) := by
      funext y; rw [hg_def, hc_dotProduct]
    rw [h_g_eq]
    exact ProbabilityTheory.multivariateGaussian_withDensity_exp_shift hJ.posSemidef h₀
  -- Identify `Matrix.toEuclideanCLM J h₀` with the target form
  -- `(WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h₀))`.
  have h_clm_eq : Matrix.toEuclideanCLM (𝕜 := ℝ) J h₀
      = (WithLp.equiv 2 (Fin k → ℝ)).symm
          (J.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h₀)) := rfl
  rw [h_clm_eq] at h_esscher
  -- Combine: weak convergence target is the desired Gaussian.
  have h_target_eq :
      ((π.withDensity (fun q : Θ k × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst)
        = multivariateGaussian
            ((WithLp.equiv 2 (Fin k → ℝ)).symm
              (J.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h₀))) J := by
    rw [h_density_simplify, h_esscher]
  rw [← h_target_eq]
  exact h_lecam

end BayesLanLimit
end LocalAsymptoticMinimax
end AsymptoticStatistics.Asymptotics.LAN
