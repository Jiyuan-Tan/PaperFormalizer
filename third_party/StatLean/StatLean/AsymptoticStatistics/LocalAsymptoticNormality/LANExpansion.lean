module
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs
public import StatLean.AsymptoticStatistics.ParametricFamily.Score
public import StatLean.AsymptoticStatistics.ParametricFamily.FisherInformation
public import StatLean.AsymptoticStatistics.ParametricFamily.SqrtDensityRatio
public import StatLean.AsymptoticStatistics.DQM.Defs
public import StatLean.AsymptoticStatistics.DQM.Properties
public import StatLean.AsymptoticStatistics.ForMathlib.MeanVarConvergence
public import StatLean.AsymptoticStatistics.ForMathlib.IntegrableTail
public import StatLean.AsymptoticStatistics.ForMathlib.Markov
public import StatLean.AsymptoticStatistics.ForMathlib.LogTaylor
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

/-!
# Theorem 7.2 — Local Asymptotic Normality (LAN) expansion

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §7.2.

Let `(P_θ : θ ∈ Θ)` be a parametric family on `(𝓧, μ)` differentiable in
quadratic mean (DQM) at `θ` with score `ℓ_θ`. Then for any `h_n → h` and
i.i.d. `X_i ∼ P_θ`:

  log ∏_i (p_{θ + h_n/√n}(X_i) / p_θ(X_i))
    = (1/√n) ∑_i ⟨h, ℓ_θ(X_i)⟩  -  ½ ⟨h, I_θ h⟩  +  o_P(1),

where `I_θ = P_θ ℓ_θ ℓ_θᵀ` is the Fisher information.

The proof goes through the L²(μ)-convergence
`√n (√p_{θ + h_n/√n} - √p_θ) → ½ ⟨h, ℓ_θ⟩ √p_θ` (the defining condition of DQM),
a Taylor expansion of `2 log(1 + W/2) = W - W²/4 + o_P(W²)` applied to
`W_i := 2 (√(p_{θ + h_n/√n}/p_θ)(X_i) - 1)`, and a mean-variance LLN/CLT
pair for the i.i.d. sample `(W_i)`.
-/

open MeasureTheory ProbabilityTheory Asymptotics Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal

namespace AsymptoticStatistics
namespace LANExpansion

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [MeasurableSpace Θ] [OpensMeasurableSpace Θ] [SecondCountableTopology Θ]

/-! ## Setup

Fix a model `M`, a base parameter `θ₀`, a dominating measure `μ`, a score `ℓ`,
and a convergent sequence `h_n → h ∈ Θ`. -/

/-! ## Auxiliary Hellinger-type statistic

Central to Steps 2–6 of the LAN expansion. Writing `p_n := M.density (θ₀ + h_n/√n)` and
`p := M.density θ₀`,
`auxStatistic M θ₀ h_n n x = 2·(√(p_n(x)/p(x)) − 1)`.

At `n = 0` the scaling factor `(√0)⁻¹ = 0` collapses the perturbation, so `W_0` is
identically zero on `{p > 0}` — irrelevant for `atTop` limits. -/
noncomputable def auxStatistic
    (M : ParametricFamily 𝓧 Θ) (θ₀ : Θ) (h_n : ℕ → Θ) (n : ℕ) (x : 𝓧) : ℝ :=
  2 * (Real.sqrt (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x / M.density θ₀ x) - 1)

omit [MeasurableSpace Θ] [OpensMeasurableSpace Θ] [SecondCountableTopology Θ] in
lemma auxStatistic_measurable
    (M : ParametricFamily 𝓧 Θ) (θ₀ : Θ) (h_n : ℕ → Θ) (n : ℕ) :
    Measurable (auxStatistic M θ₀ h_n n) := by
  unfold auxStatistic
  exact (((M.density_meas _).div (M.density_meas _)).sqrt.sub_const _).const_mul _

/-! ## Step 1 — Score has zero mean

Assuming DQM at `θ₀`, the score satisfies `P_{θ₀} ℓ = 0`, i.e. for every direction `u ∈ Θ`,
`∫ ⟨u, ℓ x⟩ p_{θ₀}(x) dμ(x) = 0`.

Proof idea (informal): DQM gives `√n(√p_{θ₀+h/√n} − √p_{θ₀}) → ½ ⟨h, ℓ⟩ √p_{θ₀}` in L²(μ),
so by inner-product continuity `√n ∫ (√p_n − √p) √p dμ → ½ ⟨h, P_{θ₀} ℓ⟩`. The LHS is
identically `0` (both densities integrate to 1), hence `P_{θ₀} ℓ = 0`. -/
lemma score_mean_zero
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ) (hℓ : Measurable ℓ)
    (h_one : ∫ x, M.density θ₀ x ∂μ = 1)
    (hint : Integrable (M.density θ₀) μ)
    (h_one_perturb : ∀ t : ℝ, ∀ u : Θ, ∫ x, M.density (θ₀ + t • u) x ∂μ = 1)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (u : Θ) :
    ∫ x, ⟪u, ℓ x⟫ * M.density θ₀ x ∂μ = 0 :=
  -- DQM supplies Fisher integrability and the residual `L²` bound.
  Score.score_mean_zero M μ θ₀ ℓ hℓ h_one hint h_one_perturb hint_perturb hDQM
    (dqm_fisher_integrable M μ θ₀ ℓ hint hDQM u (fun t => hint_perturb t u))
    (dqm_residual_eventually_memLp M μ θ₀ ℓ hDQM u)

/-! ## Step 2 — `Σᵢ E[W_{ni}]` limit

Define `W_{n,i}(x) = 2(√(p_{θ₀+h_n/√n}(x) / p_{θ₀}(x)) − 1)`.
Then `n · ∫ W_n · p dμ → −¼ ⟨h, I_θ₀ h⟩`.

Proof: the algebraic identity `∫W_n · p dμ = −∫(√p_n − √p)² dμ` (from
`(√p_n − √p)² = p_n + p − 2√(p_n p)` plus `∫p_n = ∫p = 1`), then
`n · ∫(√p_n − √p)² dμ = ‖√n(√p_n − √p)‖²_{L²} → ‖½⟨h, ℓ⟩√p‖²_{L²} = ¼ I(h, h)`
via `dqm_sqrt_density_l2_convergence` + `tendsto_integral_sq_of_tendsto_integral_diff_sq`. -/
omit [OpensMeasurableSpace Θ] [SecondCountableTopology Θ] in
lemma sum_expect_W_tendsto
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ) (_hℓ : Measurable ℓ)
    (h_one : ∫ x, M.density θ₀ x ∂μ = 1)
    (hint : Integrable (M.density θ₀) μ)
    (h_one_perturb : ∀ t : ℝ, ∀ u : Θ, ∫ x, M.density (θ₀ + t • u) x ∂μ = 1)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h_fisher_cont :
      Filter.Tendsto (fun v : Θ => ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
        (𝓝 0) (𝓝 0))
    (h : Θ) (h_n : ℕ → Θ) (hconv : Filter.Tendsto h_n Filter.atTop (𝓝 h)) :
    Filter.Tendsto
      (fun n : ℕ =>
        n * ∫ x, 2 *
            (Real.sqrt ((M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) / M.density θ₀ x) - 1)
            * M.density θ₀ x ∂μ)
      Filter.atTop
      (𝓝 (- (1/4 : ℝ) * fisherInformation M μ θ₀ ℓ h h)) := by
  -- Algebraic identity `∫W_n · p dμ = -∫(√p_n - √p)² dμ`.
  have h_alg : ∀ n : ℕ,
      ∫ x, 2 * (Real.sqrt ((M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) /
                            M.density θ₀ x) - 1) * M.density θ₀ x ∂μ
      = -∫ x, (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                - M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
    intro n
    -- Pointwise: `2(√(p_n/p) - 1)·p = -(√p_n - √p)² + p_n - p`.
    have h_pt : ∀ x,
        2 * (Real.sqrt ((M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) /
                          M.density θ₀ x) - 1) * M.density θ₀ x
        = -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2
          + M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.density θ₀ x := by
      intro x
      set pn := M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x with hpn_def
      set p := M.density θ₀ x with hp_def
      have hpn_nn : 0 ≤ pn := M.density_nonneg _ _
      have hp_nn : 0 ≤ p := M.density_nonneg _ _
      -- `(√pn - √p)² = pn + p - 2 √pn · √p = pn + p - 2 √(pn·p)`.
      have h_sqDensity_pn :
          (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) ^ 2 = pn :=
        M.sqrtDensity_sq _ x
      have h_sqDensity_p :
          (M.sqrtDensity θ₀ x) ^ 2 = p := M.sqrtDensity_sq _ x
      have h_sqrt_pn_nn :
          0 ≤ M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x :=
        M.sqrtDensity_nonneg _ x
      have h_sqrt_p_nn : 0 ≤ M.sqrtDensity θ₀ x := M.sqrtDensity_nonneg _ x
      have h_sqrt_mul : M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x *
                          M.sqrtDensity θ₀ x
                        = Real.sqrt (pn * p) := by
        rw [show (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) = Real.sqrt pn
              from rfl,
            show M.sqrtDensity θ₀ x = Real.sqrt p from rfl,
            ← Real.sqrt_mul hpn_nn]
      have h_sqrt_div_mul :
          Real.sqrt (pn / p) * p = Real.sqrt (pn * p) := by
        by_cases hp_zero : p = 0
        · rw [hp_zero]; simp
        · have hp_pos : 0 < p := lt_of_le_of_ne hp_nn (Ne.symm hp_zero)
          have hp_ne : p ≠ 0 := hp_zero
          -- √(pn/p) * p = √(pn/p) * √p * √p = √((pn/p)*p) * √p = √pn * √p = √(pn*p)
          have step1 : Real.sqrt (pn / p) * p
              = Real.sqrt (pn / p) * (Real.sqrt p * Real.sqrt p) := by
            rw [Real.mul_self_sqrt hp_nn]
          have step2 : Real.sqrt (pn / p) * (Real.sqrt p * Real.sqrt p)
              = (Real.sqrt (pn / p) * Real.sqrt p) * Real.sqrt p := by ring
          have step3 : Real.sqrt (pn / p) * Real.sqrt p =
              Real.sqrt ((pn / p) * p) := by
            rw [← Real.sqrt_mul (div_nonneg hpn_nn hp_nn)]
          have step4 : (pn / p) * p = pn := by
            field_simp
          rw [step1, step2, step3, step4, ← Real.sqrt_mul hpn_nn]
      -- Combine.
      have h_sq_expand :
          (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2
          = pn + p - 2 * Real.sqrt (pn * p) := by
        have : (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                  - M.sqrtDensity θ₀ x) ^ 2
             = (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) ^ 2
                + (M.sqrtDensity θ₀ x) ^ 2
                - 2 * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        * M.sqrtDensity θ₀ x) := by ring
        rw [this, h_sqDensity_pn, h_sqDensity_p, h_sqrt_mul]
      -- The left side simplifies to `2√(pn·p) - 2p`.
      have h_LHS : 2 * (Real.sqrt (pn / p) - 1) * p
                 = 2 * Real.sqrt (pn * p) - 2 * p := by
        have : 2 * (Real.sqrt (pn / p) - 1) * p
             = 2 * (Real.sqrt (pn / p) * p) - 2 * p := by ring
        rw [this, h_sqrt_div_mul]
      rw [h_LHS, h_sq_expand]; ring
    -- Integrate the pointwise identity.
    have h_pn_int : Integrable (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n)) μ :=
      hint_perturb ((Real.sqrt n)⁻¹) (h_n n)
    have h_sq_int : Integrable (fun x =>
        (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2) μ := by
      -- The square of the difference is ≤ 2·p_n + 2·p (integrable).
      -- More directly: the pointwise identity gives it equal to p_n + p - 2√(pn·p),
      -- and √(pn·p) ≤ (pn + p)/2, so the whole thing is between 0 and 2(pn + p).
      -- Quickest: use `MemLp.integrable_sq` after showing the difference ∈ L².
      have h_sqrt_pn_memLp : MemLp (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n)) 2 μ :=
        M.sqrtDensity_memLp_two μ _ h_pn_int
      have h_sqrt_p_memLp : MemLp (M.sqrtDensity θ₀) 2 μ :=
        M.sqrtDensity_memLp_two μ _ hint
      exact (h_sqrt_pn_memLp.sub h_sqrt_p_memLp).integrable_sq
    have h_sum_int : Integrable (fun x =>
        M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.density θ₀ x) μ :=
      h_pn_int.sub hint
    have h_rhs_int : Integrable (fun x =>
        -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2
          + M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.density θ₀ x) μ := by
      have h_part1 : Integrable (fun x =>
          -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2) μ :=
        h_sq_int.neg
      have : (fun x =>
          -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2
            + M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.density θ₀ x)
           = (fun x =>
          -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2
            + (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.density θ₀ x)) := by
        funext x; ring
      rw [this]
      exact h_part1.add h_sum_int
    calc ∫ x, 2 * (Real.sqrt ((M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) /
                          M.density θ₀ x) - 1) * M.density θ₀ x ∂μ
        = ∫ x, (-(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                    - M.sqrtDensity θ₀ x) ^ 2
                + M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.density θ₀ x) ∂μ := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
          exact h_pt
      _ = (∫ x, -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                    - M.sqrtDensity θ₀ x) ^ 2 ∂μ)
          + ∫ x, (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.density θ₀ x) ∂μ := by
          have h_part1 : Integrable (fun x =>
              -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2) μ :=
            h_sq_int.neg
          rw [show (fun x =>
              -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2
                + M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.density θ₀ x)
              = (fun x =>
              -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2
                + (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.density θ₀ x)) from
            by funext x; ring]
          exact MeasureTheory.integral_add h_part1 h_sum_int
      _ = -∫ x, (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                    - M.sqrtDensity θ₀ x) ^ 2 ∂μ + 0 := by
          congr 1
          · exact MeasureTheory.integral_neg _
          · rw [MeasureTheory.integral_sub h_pn_int hint,
                h_one_perturb ((Real.sqrt n)⁻¹) (h_n n), h_one]
            ring
      _ = -∫ x, (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                    - M.sqrtDensity θ₀ x) ^ 2 ∂μ := by ring
  -- Apply the L² norm-square limit.
  -- f_n := √n·(√p_n - √p), g := (1/2)⟨h, ℓ⟩√p. From dqm_sqrt_density_l2_convergence:
  -- ∫(f_n - g)² → 0. Hence ∫f_n² → ∫g² = (1/4)·I(h, h).
  have h_g_memLp : MemLp (fun x => (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
    have h_score_memLp :
        MemLp (fun x => ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ :=
      dqm_score_memLp_two M μ θ₀ ℓ hint hDQM h (fun t => hint_perturb t h)
    have h_eq : (fun x => (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x)
              = (fun x => (1 / 2 : ℝ) * (⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x)) := by
      funext x; ring
    rw [h_eq]
    exact h_score_memLp.const_mul _
  have h_fn_diff_memLp : ∀ n : ℕ,
      MemLp (fun x =>
        Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        - M.sqrtDensity θ₀ x)
        - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
    intro n
    -- √n·(√p_n - √p) ∈ L² and (1/2)⟨h, ℓ⟩√p ∈ L², so difference ∈ L².
    have h_sqrt_pn_memLp :
        MemLp (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n)) 2 μ :=
      M.sqrtDensity_memLp_two μ _ (hint_perturb _ _)
    have h_sqrt_p_memLp : MemLp (M.sqrtDensity θ₀) 2 μ :=
      M.sqrtDensity_memLp_two μ _ hint
    have h_diff : MemLp (fun x =>
        M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) 2 μ :=
      h_sqrt_pn_memLp.sub h_sqrt_p_memLp
    have h_scaled : MemLp (fun x =>
        Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        - M.sqrtDensity θ₀ x)) 2 μ :=
      h_diff.const_mul (Real.sqrt n)
    exact h_scaled.sub h_g_memLp
  have h_l2_conv :=
    dqm_sqrt_density_l2_convergence M μ θ₀ ℓ hint hint_perturb hDQM
      h_fisher_cont hconv
  have h_tendsto_sq :=
    L2Utils.tendsto_integral_sq_of_tendsto_integral_diff_sq μ
      (f := fun n x =>
        Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        - M.sqrtDensity θ₀ x))
      (g := fun x => (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x)
      h_g_memLp (Filter.Eventually.of_forall h_fn_diff_memLp) h_l2_conv
  -- Compute `∫g² = (1/4) · I(h, h)`.
  have h_g_sq_eq :
      ∫ x, ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
        = (1 / 4 : ℝ) * fisherInformation M μ θ₀ ℓ h h := by
    have hpt : ∀ x,
        ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
          = (1 / 4 : ℝ) * (⟪h, ℓ x⟫ * ⟪h, ℓ x⟫ * M.density θ₀ x) := by
      intro x
      have hsq : (M.sqrtDensity θ₀ x) ^ 2 = M.density θ₀ x :=
        M.sqrtDensity_sq θ₀ x
      have : ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
            = (1 / 4 : ℝ) * (⟪h, ℓ x⟫ * ⟪h, ℓ x⟫ * (M.sqrtDensity θ₀ x) ^ 2) := by ring
      rw [this, hsq]
    simp_rw [hpt]
    rw [MeasureTheory.integral_const_mul]
    rfl
  -- Link the quadratic form ∫(√n(√p_n - √p))² to n · ∫(√p_n - √p)².
  have h_sq_scale : ∀ n : ℕ,
      ∫ x, (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                            - M.sqrtDensity θ₀ x)) ^ 2 ∂μ
      = (n : ℝ) * ∫ x, (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                            - M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
    intro n
    have h_pt : ∀ x,
        (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                          - M.sqrtDensity θ₀ x)) ^ 2
        = (n : ℝ) * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        - M.sqrtDensity θ₀ x) ^ 2 := by
      intro x
      have hsqrt_sq : (Real.sqrt n) ^ 2 = (n : ℝ) :=
        Real.sq_sqrt (Nat.cast_nonneg n)
      have : (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                              - M.sqrtDensity θ₀ x)) ^ 2
            = (Real.sqrt n) ^ 2 * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                                      - M.sqrtDensity θ₀ x) ^ 2 := by ring
      rw [this, hsqrt_sq]
    simp_rw [h_pt]
    rw [MeasureTheory.integral_const_mul]
  -- Assemble.
  rw [h_g_sq_eq] at h_tendsto_sq
  have h_target : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * ∫ x, (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                                    - M.sqrtDensity θ₀ x) ^ 2 ∂μ) Filter.atTop
      (𝓝 ((1 / 4 : ℝ) * fisherInformation M μ θ₀ ℓ h h)) := by
    have := h_tendsto_sq
    refine this.congr fun n => ?_
    exact h_sq_scale n
  -- Combine: n · ∫W_n · p = -n · ∫(√p_n - √p)² → -(1/4)·I.
  have h_alg_n : ∀ n : ℕ,
      (n : ℝ) * ∫ x, 2 * (Real.sqrt ((M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) /
                                      M.density θ₀ x) - 1) * M.density θ₀ x ∂μ
      = -((n : ℝ) * ∫ x, (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                            - M.sqrtDensity θ₀ x) ^ 2 ∂μ) := by
    intro n
    rw [h_alg n]; ring
  -- Rewrite the target limit `-(1/4)·I` as `-((1/4)·I)` to match `h_target.neg`.
  have h_lim_eq : -(1 / 4 : ℝ) * fisherInformation M μ θ₀ ℓ h h
                  = -((1 / 4 : ℝ) * fisherInformation M μ θ₀ ℓ h h) := by ring
  rw [h_lim_eq]
  exact h_target.neg.congr fun n => (h_alg_n n).symm

/-! ## Step 3 — Variance control

For i.i.d. `X_i ∼ P_{θ₀}`, `Var[Σᵢ W_{n,i} − (1/√n) Σᵢ ⟨h, ℓ(X_i)⟩] → 0`. The
core analytic content is `E_{θ₀}[(√n W_n − ⟨h, ℓ⟩)²] → 0`, which is exactly

  `∫ (√n · W_n(x) − ⟨h, ℓ x⟩)² · p_{θ₀}(x) dμ → 0`.

**Proof**. The pointwise bound
  `(√n W_n − g)² · p ≤ 4 · (√n(√p_n − √p) − ½ g √p)²`
(equality on `{p > 0}` using `√(p_n/p)·√p = √p_n`; trivially `0 ≤ RHS` on
`{p = 0}`) plus `dqm_sqrt_density_l2_convergence` (the L² residual `φ_n`
integrates to 0) gives `∫(√n W_n − g)² · p dμ ≤ 4 ∫φ_n² dμ → 0`. Squeeze. -/
omit [OpensMeasurableSpace Θ] [SecondCountableTopology Θ] in
lemma variance_tendsto_zero
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ) (_hℓ : Measurable ℓ)
    (hint : Integrable (M.density θ₀) μ)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h_fisher_cont :
      Filter.Tendsto (fun v : Θ => ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
        (𝓝 0) (𝓝 0))
    (h : Θ) (h_n : ℕ → Θ) (hconv : Filter.Tendsto h_n Filter.atTop (𝓝 h)) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ x,
          (Real.sqrt n * 2 *
              (Real.sqrt ((M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) / M.density θ₀ x) - 1)
            - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x ∂μ)
      Filter.atTop
      (𝓝 0) := by
  -- Key pointwise bound: target ≤ 4 · φ_n² (with equality on {p > 0}).
  have h_pt : ∀ n : ℕ, ∀ x,
      (Real.sqrt n * 2 * (Real.sqrt ((M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) /
                                      M.density θ₀ x) - 1)
        - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x
      ≤ 4 *
        (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        - M.sqrtDensity θ₀ x)
          - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 := by
    intro n x
    set pn := M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x with hpn_def
    set p := M.density θ₀ x with hp_def
    have hpn_nn : 0 ≤ pn := M.density_nonneg _ _
    have hp_nn : 0 ≤ p := M.density_nonneg _ _
    by_cases hp_zero : p = 0
    · -- p = 0: LHS = 0, RHS ≥ 0.
      rw [hp_zero]
      simp
      positivity
    -- p > 0: show equality.
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nn (Ne.symm hp_zero)
    have hp_sqrt_nn : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
    have h_sqDensity_p : M.sqrtDensity θ₀ x = Real.sqrt p := rfl
    have h_sqDensity_pn :
        M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x = Real.sqrt pn := rfl
    have h_p_eq : p = Real.sqrt p * Real.sqrt p := (Real.mul_self_sqrt hp_nn).symm
    -- Key identity on {p > 0}: √(pn/p) · √p = √pn.
    have h_sqrt_div_mul : Real.sqrt (pn / p) * Real.sqrt p = Real.sqrt pn := by
      rw [← Real.sqrt_mul (div_nonneg hpn_nn hp_nn), div_mul_cancel₀ pn hp_zero]
    -- (√n · W_n − g) · √p = 2√n·(√pn − √p) − g · √p
    have h_inner_mul :
        (Real.sqrt n * 2 * (Real.sqrt (pn / p) - 1) - ⟪h, ℓ x⟫) * Real.sqrt p
        = 2 * Real.sqrt n * (Real.sqrt pn - Real.sqrt p)
          - ⟪h, ℓ x⟫ * Real.sqrt p := by
      have : (Real.sqrt n * 2 * (Real.sqrt (pn / p) - 1) - ⟪h, ℓ x⟫) * Real.sqrt p
           = 2 * Real.sqrt n * (Real.sqrt (pn / p) * Real.sqrt p - Real.sqrt p)
              - ⟪h, ℓ x⟫ * Real.sqrt p := by ring
      rw [this, h_sqrt_div_mul]
    -- Square both sides and use (a · b)² = a²·b² plus p = √p·√p.
    have h_LHS_eq :
        (Real.sqrt n * 2 * (Real.sqrt (pn / p) - 1) - ⟪h, ℓ x⟫) ^ 2 * p
        = (2 * Real.sqrt n * (Real.sqrt pn - Real.sqrt p)
            - ⟪h, ℓ x⟫ * Real.sqrt p) ^ 2 := by
      calc (Real.sqrt n * 2 * (Real.sqrt (pn / p) - 1) - ⟪h, ℓ x⟫) ^ 2 * p
          = (Real.sqrt n * 2 * (Real.sqrt (pn / p) - 1) - ⟪h, ℓ x⟫) ^ 2
              * (Real.sqrt p * Real.sqrt p) := by rw [← h_p_eq]
        _ = ((Real.sqrt n * 2 * (Real.sqrt (pn / p) - 1) - ⟪h, ℓ x⟫) * Real.sqrt p) ^ 2 := by
            ring
        _ = (2 * Real.sqrt n * (Real.sqrt pn - Real.sqrt p)
              - ⟪h, ℓ x⟫ * Real.sqrt p) ^ 2 := by rw [h_inner_mul]
    have h_RHS_eq :
        4 * (Real.sqrt n * (Real.sqrt pn - Real.sqrt p)
              - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * Real.sqrt p) ^ 2
        = (2 * Real.sqrt n * (Real.sqrt pn - Real.sqrt p)
            - ⟪h, ℓ x⟫ * Real.sqrt p) ^ 2 := by ring
    rw [h_sqDensity_pn, h_sqDensity_p, h_LHS_eq, ← h_RHS_eq]
  -- L² residual → 0 via dqm_sqrt_density_l2_convergence.
  have h_l2 :=
    dqm_sqrt_density_l2_convergence M μ θ₀ ℓ hint hint_perturb hDQM h_fisher_cont hconv
  -- Multiply by 4.
  have h_l2_4 :
      Filter.Tendsto (fun n : ℕ =>
        4 * ∫ x,
              (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                              - M.sqrtDensity θ₀ x)
                - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
        Filter.atTop (𝓝 0) := by
    have := h_l2.const_mul (4 : ℝ)
    simpa using this
  -- Integrability of the bounding integrand `4·φ_n²` for each n.
  have hφ_sq_memLp : ∀ n : ℕ,
      MemLp (fun x =>
        Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        - M.sqrtDensity θ₀ x)
        - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
    intro n
    have h_sqrt_pn_memLp :
        MemLp (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n)) 2 μ :=
      M.sqrtDensity_memLp_two μ _ (hint_perturb _ _)
    have h_sqrt_p_memLp : MemLp (M.sqrtDensity θ₀) 2 μ :=
      M.sqrtDensity_memLp_two μ _ hint
    have h_diff : MemLp (fun x =>
        M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) 2 μ :=
      h_sqrt_pn_memLp.sub h_sqrt_p_memLp
    have h_scaled : MemLp (fun x =>
        Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        - M.sqrtDensity θ₀ x)) 2 μ :=
      h_diff.const_mul (Real.sqrt n)
    have h_score_memLp :
        MemLp (fun x => ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ :=
      dqm_score_memLp_two M μ θ₀ ℓ hint hDQM h (fun t => hint_perturb t h)
    have h_half : MemLp (fun x =>
        (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
      have h_eq : (fun x => (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x)
                = (fun x => (1 / 2 : ℝ) * (⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x)) := by
        funext x; ring
      rw [h_eq]
      exact h_score_memLp.const_mul _
    exact h_scaled.sub h_half
  -- Squeeze.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (b := Filter.atTop)
    (g := fun (_ : ℕ) => (0 : ℝ)) (h := fun n : ℕ =>
      4 * ∫ x,
            (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                            - M.sqrtDensity θ₀ x)
              - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
    tendsto_const_nhds h_l2_4
    (Filter.Eventually.of_forall fun n =>
      MeasureTheory.integral_nonneg fun x =>
        mul_nonneg (sq_nonneg _) (M.density_nonneg θ₀ x))
    (Filter.Eventually.of_forall fun n => ?_)
  -- Pointwise + integration.
  have hφ_sq_int : Integrable (fun x =>
      (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                      - M.sqrtDensity θ₀ x)
        - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) μ :=
    (hφ_sq_memLp n).integrable_sq
  have h_4φ_sq_int : Integrable (fun x =>
      4 * (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                          - M.sqrtDensity θ₀ x)
            - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) μ :=
    hφ_sq_int.const_mul 4
  have h_int :
      ∫ x,
        (Real.sqrt n * 2 * (Real.sqrt ((M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) /
                                        M.density θ₀ x) - 1)
          - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x ∂μ ≤
      ∫ x, 4 *
        (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        - M.sqrtDensity θ₀ x)
          - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (sq_nonneg _) (M.density_nonneg θ₀ x))
      h_4φ_sq_int
      (Filter.Eventually.of_forall (h_pt n))
  have h_pull :
      ∫ x, 4 *
        (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        - M.sqrtDensity θ₀ x)
          - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ =
        4 * ∫ x,
          (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                          - M.sqrtDensity θ₀ x)
            - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ :=
    MeasureTheory.integral_const_mul _ _
  linarith

/-! ## Step 4 — Mean + variance → 0 ⇒ tendsto in probability (assembly)

On an auxiliary probability space `(Ω, P)` carrying an iid sample `X : ℕ → Ω → 𝓧`
with law `P_{θ₀} = μ.withDensity p_{θ₀}`, the *centred* sum

  `Y_n(ω) := ∑_{i<n} W_n(X_i ω) − (1/√n) ∑_{i<n} ⟨h, ℓ(X_i ω)⟩`,
  `W_n := auxStatistic M θ₀ h_n n`

converges in P-probability to `−¼ · fisherInformation M μ θ₀ ℓ h h`. Since Step 1
gives `P_{θ₀} ⟨h, ℓ⟩ = 0`, this is the `(⋆)` clause of the informal outline:

  `∑_i W_{n,i} = (1/√n) ∑_i g(X_i) − ¼ P g² + o_P(1)`.

The proof applies `tendstoInMeasure_of_tendsto_mean_of_tendsto_variance`
with the centred sum as `Y_n`, using
  * `E_{P}[Y_n] = n · ∫ W_n · p dμ − √n · ∫ ⟨h, ℓ⟩ · p dμ → −¼ · I(h, h)`
    (Step 2 `sum_expect_W_tendsto` + Step 1 `score_mean_zero`),
  * `Var_{P}[Y_n] = n · Var[W_n(X_0) − (1/√n) g(X_0)]
                    ≤ ∫ (√n · W_n − g)² · p dμ → 0` (Step 3 `variance_tendsto_zero`).
The identical-distribution hypothesis transfers expectations/variances from P to
integrals against `p · μ`; pairwise independence makes variance of the sum additive. -/
lemma sum_W_decomp
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ) (hℓ : Measurable ℓ)
    (h_one : ∫ x, M.density θ₀ x ∂μ = 1)
    (hint : Integrable (M.density θ₀) μ)
    (h_one_perturb : ∀ t : ℝ, ∀ u : Θ, ∫ x, M.density (θ₀ + t • u) x ∂μ = 1)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h_fisher_cont :
      Filter.Tendsto (fun v : Θ => ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
        (𝓝 0) (𝓝 0))
    (h : Θ) (h_n : ℕ → Θ) (hconv : Filter.Tendsto h_n Filter.atTop (𝓝 h))
    (X : ℕ → Ω → 𝓧) (hX_meas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) P)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P P)
    (hlaw : Measure.map (X 0) P
              = μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) :
    TendstoInMeasure P
      (fun n ω =>
        (∑ i ∈ Finset.range n, auxStatistic M θ₀ h_n n (X i ω))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, ⟪h, ℓ (X i ω)⟫)
      Filter.atTop
      (fun _ => -(1/4 : ℝ) * fisherInformation M μ θ₀ ℓ h h) := by
  -- Notation.
  set g : 𝓧 → ℝ := fun x => ⟪h, ℓ x⟫ with hg_def
  set p : 𝓧 → ℝ := M.density θ₀ with hp_def
  set ν : Measure 𝓧 := μ.withDensity fun x => ENNReal.ofReal (p x) with hν_def
  set W : ℕ → 𝓧 → ℝ := auxStatistic M θ₀ h_n with hW_def
  -- Basic measurability + nonnegativity of p.
  have hp_meas : Measurable p := M.density_meas θ₀
  have hp_nn : ∀ x, 0 ≤ p x := M.density_nonneg θ₀
  have hg_meas : Measurable g :=
    ((continuous_const (y := h)).inner continuous_id).measurable.comp hℓ
  have hW_meas : ∀ n, Measurable (W n) := fun n => auxStatistic_measurable M θ₀ h_n n
  -- `hident`-derived: each `X i` has law ν = μ.withDensity p.
  have h_map : ∀ i, Measure.map (X i) P = ν := by
    intro i
    rw [(hident i).map_eq, hlaw]
  -- Transfer lemma: `∫ ω, f (X i ω) ∂P = ∫ x, f x · p x ∂μ` (integrable/bochner side).
  have h_transfer : ∀ (f : 𝓧 → ℝ), AEStronglyMeasurable f ν →
      ∀ i, ∫ ω, f (X i ω) ∂P = ∫ x, f x * p x ∂μ := by
    intro f hf_aesm i
    have h_aesm_map : AEStronglyMeasurable f (Measure.map (X i) P) := by
      rw [h_map i]; exact hf_aesm
    have h_step1 : ∫ ω, f (X i ω) ∂P = ∫ y, f y ∂ν := by
      rw [← h_map i, MeasureTheory.integral_map (hX_meas i).aemeasurable h_aesm_map]
    have h_step2 : ∫ y, f y ∂ν = ∫ y, p y * f y ∂μ := by
      rw [hν_def,
          integral_withDensity_eq_integral_toReal_smul
            (μ := μ) hp_meas.ennreal_ofReal
            (MeasureTheory.ae_of_all μ fun _ => ENNReal.ofReal_lt_top) f]
      refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all μ fun y => ?_)
      simp [ENNReal.toReal_ofReal (hp_nn y)]
    rw [h_step1, h_step2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  -- The centred summand `Z n (X i ω) := W n (X i ω) - (1/√n)·g(X i ω)`, whose sum over
  -- `i ∈ range n` is `Y n ω`.
  set Z : ℕ → 𝓧 → ℝ := fun n x => W n x - (Real.sqrt n)⁻¹ * g x with hZ_def
  have hZ_meas : ∀ n, Measurable (Z n) :=
    fun n => (hW_meas n).sub ((measurable_const).mul hg_meas)
  -- Rewrite `Y n ω` as `∑ i, Z n (X i ω)`.
  have hY_eq : ∀ n : ℕ, ∀ ω,
      (∑ i ∈ Finset.range n, W n (X i ω))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)
      = ∑ i ∈ Finset.range n, Z n (X i ω) := by
    intro n ω
    simp only [Z, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- Integrability transfer: f · p ∈ L¹(μ) ⇒ f ∘ X i ∈ L¹(P).
  have h_transfer_int : ∀ (f : 𝓧 → ℝ), Measurable f →
      Integrable (fun x => f x * p x) μ →
      ∀ i, Integrable (fun ω => f (X i ω)) P := by
    intro f hf_meas hfp_int i
    have hf_ν : Integrable f ν := by
      rw [hν_def]
      refine (MeasureTheory.integrable_withDensity_iff hp_meas.ennreal_ofReal
                (MeasureTheory.ae_of_all μ fun _ => ENNReal.ofReal_lt_top)).mpr ?_
      refine hfp_int.congr (MeasureTheory.ae_of_all μ fun x => ?_)
      simp [ENNReal.toReal_ofReal (hp_nn x)]
    have hf_map : Integrable f (Measure.map (X i) P) := by
      rw [h_map i]; exact hf_ν
    exact (MeasureTheory.integrable_map_measure hf_meas.aestronglyMeasurable
            (hX_meas i).aemeasurable).mp hf_map
  -- L² memberships for √p and √p_n (standard), plus g · √p.
  have h_sqrt_p_memLp : MemLp (M.sqrtDensity θ₀) 2 μ :=
    M.sqrtDensity_memLp_two μ _ hint
  have h_sqrt_pn_memLp : ∀ n : ℕ,
      MemLp (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n)) 2 μ :=
    fun n => M.sqrtDensity_memLp_two μ _ (hint_perturb _ _)
  have h_score_memLp : MemLp (fun x => ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ :=
    dqm_score_memLp_two M μ θ₀ ℓ hint hDQM h (fun t => hint_perturb t h)
  -- `W n · p` integrable over μ: pointwise = `-(√p_n - √p)² + p_n - p`.
  have hWnp_int : ∀ n : ℕ, Integrable (fun x => W n x * p x) μ := by
    intro n
    have h_sqrt_diff_memLp : MemLp (fun x =>
        M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) 2 μ :=
      (h_sqrt_pn_memLp n).sub h_sqrt_p_memLp
    have h_sq_int : Integrable (fun x =>
        (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2) μ :=
      h_sqrt_diff_memLp.integrable_sq
    have hpn_int : Integrable (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n)) μ :=
      hint_perturb _ _
    -- RHS integrable: -(√p_n - √p)² + p_n - p.
    have h_rhs_int : Integrable (fun x =>
        -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2
          + M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - p x) μ := by
      have h1 := h_sq_int.neg
      have : (fun x =>
          -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2
            + M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - p x)
          = (fun x =>
          (-(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2)
            + (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - p x)) := by funext x; ring
      rw [this]
      exact h1.add (hpn_int.sub hint)
    -- Pointwise identity (copied from Step 2).
    have h_pt : ∀ x, W n x * p x
        = -(M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2
          + M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - p x := by
      intro x
      change 2 * (Real.sqrt (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x / M.density θ₀ x) - 1)
            * M.density θ₀ x = _
      set pn := M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
      set pp := M.density θ₀ x
      have hpn_nn : 0 ≤ pn := M.density_nonneg _ _
      have hpp_nn : 0 ≤ pp := M.density_nonneg _ _
      have h_sqDensity_pn :
          (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) ^ 2 = pn := M.sqrtDensity_sq _ x
      have h_sqDensity_p : (M.sqrtDensity θ₀ x) ^ 2 = pp := M.sqrtDensity_sq _ x
      have h_sqrt_mul : M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x *
                          M.sqrtDensity θ₀ x
                        = Real.sqrt (pn * pp) := by
        rw [show (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) = Real.sqrt pn from rfl,
            show M.sqrtDensity θ₀ x = Real.sqrt pp from rfl,
            ← Real.sqrt_mul hpn_nn]
      have h_sqrt_div_mul : Real.sqrt (pn / pp) * pp = Real.sqrt (pn * pp) := by
        by_cases hp_zero : pp = 0
        · rw [hp_zero]; simp
        · have hp_ne : pp ≠ 0 := hp_zero
          have step1 : Real.sqrt (pn / pp) * pp
              = Real.sqrt (pn / pp) * (Real.sqrt pp * Real.sqrt pp) := by
            rw [Real.mul_self_sqrt hpp_nn]
          have step2 : Real.sqrt (pn / pp) * (Real.sqrt pp * Real.sqrt pp)
              = (Real.sqrt (pn / pp) * Real.sqrt pp) * Real.sqrt pp := by ring
          have step3 : Real.sqrt (pn / pp) * Real.sqrt pp = Real.sqrt ((pn / pp) * pp) := by
            rw [← Real.sqrt_mul (div_nonneg hpn_nn hpp_nn)]
          have step4 : (pn / pp) * pp = pn := by field_simp
          rw [step1, step2, step3, step4, ← Real.sqrt_mul hpn_nn]
      have h_sq_expand :
          (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2
          = pn + pp - 2 * Real.sqrt (pn * pp) := by
        have : (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                  - M.sqrtDensity θ₀ x) ^ 2
             = (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) ^ 2
                + (M.sqrtDensity θ₀ x) ^ 2
                - 2 * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        * M.sqrtDensity θ₀ x) := by ring
        rw [this, h_sqDensity_pn, h_sqDensity_p, h_sqrt_mul]
      have h_LHS : 2 * (Real.sqrt (pn / pp) - 1) * pp = 2 * Real.sqrt (pn * pp) - 2 * pp := by
        have : 2 * (Real.sqrt (pn / pp) - 1) * pp
             = 2 * (Real.sqrt (pn / pp) * pp) - 2 * pp := by ring
        rw [this, h_sqrt_div_mul]
      change 2 * (Real.sqrt (pn / pp) - 1) * pp = _
      rw [h_LHS, h_sq_expand]; ring
    exact h_rhs_int.congr (MeasureTheory.ae_of_all μ fun x => (h_pt x).symm)
  -- `g · p` integrable over μ: factors as `(g · √p) · √p`, both L²(μ).
  have hgp_int : Integrable (fun x => g x * p x) μ := by
    have h_eq : (fun x => g x * p x)
              = fun x => (g x * M.sqrtDensity θ₀ x) * M.sqrtDensity θ₀ x := by
      funext x
      have hsq : (M.sqrtDensity θ₀ x) ^ 2 = p x := M.sqrtDensity_sq θ₀ x
      calc g x * p x = g x * (M.sqrtDensity θ₀ x) ^ 2 := by rw [hsq]
        _ = (g x * M.sqrtDensity θ₀ x) * M.sqrtDensity θ₀ x := by ring
    rw [h_eq]
    exact h_score_memLp.integrable_mul h_sqrt_p_memLp
  -- Integrability under P of each summand.
  have hWnX_int : ∀ n i, Integrable (fun ω => W n (X i ω)) P :=
    fun n i => h_transfer_int (W n) (hW_meas n) (hWnp_int n) i
  have hgX_int : ∀ i, Integrable (fun ω => g (X i ω)) P :=
    fun i => h_transfer_int g hg_meas hgp_int i
  -- Expected value of a single summand via transfer.
  have hWn_aesm_ν : ∀ n, AEStronglyMeasurable (W n) ν :=
    fun n => (hW_meas n).aestronglyMeasurable
  have hg_aesm_ν : AEStronglyMeasurable g ν := hg_meas.aestronglyMeasurable
  have hEW : ∀ n i, ∫ ω, W n (X i ω) ∂P = ∫ x, W n x * p x ∂μ :=
    fun n i => h_transfer (W n) (hWn_aesm_ν n) i
  have hEg : ∀ i, ∫ ω, g (X i ω) ∂P = ∫ x, g x * p x ∂μ :=
    fun i => h_transfer g hg_aesm_ν i
  -- The score has zero mean, hence `∫ g · p dμ = 0`.
  have h_Pg_zero : ∫ x, g x * p x ∂μ = 0 :=
    score_mean_zero M μ θ₀ ℓ hℓ h_one hint h_one_perturb hint_perturb hDQM h
  -- Integrability of `W n² · p` and `g² · p`.
  have hgsq_p_int : Integrable (fun x => g x ^ 2 * p x) μ :=
    dqm_fisher_integrable M μ θ₀ ℓ hint hDQM h (fun t => hint_perturb t h)
  -- Pointwise bound: `W n x² · p x ≤ 4 · (√p_n - √p)²`.
  have hWnsq_p_bound : ∀ n : ℕ, ∀ x, W n x ^ 2 * p x
      ≤ 4 *
        (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2 := by
    intro n x
    change (2 * (Real.sqrt (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x / M.density θ₀ x) - 1))
         ^ 2 * M.density θ₀ x ≤ _
    set pn := M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
    set pp := M.density θ₀ x
    have hpn_nn : 0 ≤ pn := M.density_nonneg _ _
    have hpp_nn : 0 ≤ pp := M.density_nonneg _ _
    by_cases hp_zero : pp = 0
    · rw [hp_zero, mul_zero]
      refine mul_nonneg (by norm_num) (sq_nonneg _)
    -- pp > 0
    have hpp_pos : 0 < pp := lt_of_le_of_ne hpp_nn (Ne.symm hp_zero)
    have h_sqDensity_pn :
        (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) ^ 2 = pn := M.sqrtDensity_sq _ x
    have h_sqDensity_p : (M.sqrtDensity θ₀ x) ^ 2 = pp := M.sqrtDensity_sq _ x
    have h_sqrt_mul : M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x *
                        M.sqrtDensity θ₀ x = Real.sqrt (pn * pp) := by
      rw [show (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x) = Real.sqrt pn from rfl,
          show M.sqrtDensity θ₀ x = Real.sqrt pp from rfl,
          ← Real.sqrt_mul hpn_nn]
    have h_sqrt_div_mul : Real.sqrt (pn / pp) * Real.sqrt pp = Real.sqrt pn := by
      rw [← Real.sqrt_mul (div_nonneg hpn_nn hpp_nn), div_mul_cancel₀ pn hp_zero]
    -- Square the inner product with √pp.
    have h_inner :
        (2 * (Real.sqrt (pn / pp) - 1)) * Real.sqrt pp
          = 2 * (Real.sqrt pn - Real.sqrt pp) := by
      have : (2 * (Real.sqrt (pn / pp) - 1)) * Real.sqrt pp
           = 2 * (Real.sqrt (pn / pp) * Real.sqrt pp - Real.sqrt pp) := by ring
      rw [this, h_sqrt_div_mul]
    -- Square gives the identity.
    have h_sq_eq : (2 * (Real.sqrt (pn / pp) - 1)) ^ 2 * pp
        = 4 * (Real.sqrt pn - Real.sqrt pp) ^ 2 := by
      have h_factor :
          ((2 * (Real.sqrt (pn / pp) - 1)) * Real.sqrt pp) ^ 2
            = (2 * (Real.sqrt (pn / pp) - 1)) ^ 2 * (Real.sqrt pp * Real.sqrt pp) := by ring
      have h_rearrange : (2 * (Real.sqrt (pn / pp) - 1)) ^ 2 * pp
          = ((2 * (Real.sqrt (pn / pp) - 1)) * Real.sqrt pp) ^ 2 := by
        rw [h_factor, Real.mul_self_sqrt hpp_nn]
      rw [h_rearrange, h_inner]; ring
    rw [h_sq_eq]
    -- sqrtDensity = Real.sqrt ∘ density by definition, so RHS matches LHS.
    exact le_refl _
  -- Integrability of `W n² · p`.
  have hWnsq_p_int : ∀ n : ℕ, Integrable (fun x => W n x ^ 2 * p x) μ := by
    intro n
    have h_sqrt_diff_memLp : MemLp (fun x =>
        M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) 2 μ :=
      (h_sqrt_pn_memLp n).sub h_sqrt_p_memLp
    have h_sq_int : Integrable (fun x =>
        (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2) μ :=
      h_sqrt_diff_memLp.integrable_sq
    have h_4sq_int : Integrable (fun x =>
        4 * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2) μ :=
      h_sq_int.const_mul 4
    refine Integrable.mono' h_4sq_int ?_ (MeasureTheory.ae_of_all μ fun x => ?_)
    · exact (((hW_meas n).pow_const 2).mul hp_meas).aestronglyMeasurable
    · have h_nn : 0 ≤ W n x ^ 2 * p x := mul_nonneg (sq_nonneg _) (hp_nn x)
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
      exact hWnsq_p_bound n x
  -- MemLp W_n and g over ν.
  have hWn_memLp_ν : ∀ n : ℕ, MemLp (W n) 2 ν := by
    intro n
    refine (MeasureTheory.memLp_two_iff_integrable_sq (hWn_aesm_ν n)).mpr ?_
    -- Integrable (W_n²) ν ↔ Integrable (W_n² · p) μ
    have h_eq : (fun x => W n x ^ 2) = (fun x => W n x ^ 2) := rfl
    rw [hν_def]
    refine (MeasureTheory.integrable_withDensity_iff hp_meas.ennreal_ofReal
              (MeasureTheory.ae_of_all μ fun _ => ENNReal.ofReal_lt_top)).mpr ?_
    refine (hWnsq_p_int n).congr (MeasureTheory.ae_of_all μ fun x => ?_)
    simp [ENNReal.toReal_ofReal (hp_nn x)]
  have hg_memLp_ν : MemLp g 2 ν := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq hg_aesm_ν).mpr ?_
    rw [hν_def]
    refine (MeasureTheory.integrable_withDensity_iff hp_meas.ennreal_ofReal
              (MeasureTheory.ae_of_all μ fun _ => ENNReal.ofReal_lt_top)).mpr ?_
    refine hgsq_p_int.congr (MeasureTheory.ae_of_all μ fun x => ?_)
    simp [ENNReal.toReal_ofReal (hp_nn x)]
  -- MemLp Z_n over ν: Z_n = W_n - (√n)⁻¹ · g.
  have hZn_memLp_ν : ∀ n : ℕ, MemLp (Z n) 2 ν := by
    intro n
    have h_scaled : MemLp (fun x => (Real.sqrt n)⁻¹ * g x) 2 ν := hg_memLp_ν.const_mul _
    have : (Z n) = (W n) - fun x => (Real.sqrt n)⁻¹ * g x := by
      funext x; simp [Z]
    rw [this]
    exact (hWn_memLp_ν n).sub h_scaled
  -- MemLp Z_n ∘ X_i over P: transfer via MemLp.comp_of_map.
  have hZnX_memLp : ∀ n i, MemLp (fun ω => Z n (X i ω)) 2 P := by
    intro n i
    have h_map_memLp : MemLp (Z n) 2 (Measure.map (X i) P) := by
      rw [h_map i]; exact hZn_memLp_ν n
    exact MemLp.comp_of_map h_map_memLp (hX_meas i).aemeasurable
  -- h_mem: sum of Z_n(X_i) is L² under P, and Y_n equals that sum.
  have h_mem : ∀ n, MemLp (fun ω =>
      (∑ i ∈ Finset.range n, W n (X i ω))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)) 2 P := by
    intro n
    have h_sum_memLp : MemLp (fun ω => ∑ i ∈ Finset.range n, Z n (X i ω)) 2 P :=
      MeasureTheory.memLp_finset_sum _ (fun i _ => hZnX_memLp n i)
    exact h_sum_memLp.ae_eq (MeasureTheory.ae_of_all P fun ω => (hY_eq n ω).symm)
  -- Mean limit.
  have h_mean : Filter.Tendsto
      (fun n => ∫ ω,
        ((∑ i ∈ Finset.range n, W n (X i ω))
          - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)) ∂P)
      Filter.atTop
      (𝓝 (-(1/4 : ℝ) * fisherInformation M μ θ₀ ℓ h h)) := by
    -- Expand the integral of the sum.
    have h_expand : ∀ n : ℕ, ∫ ω,
        ((∑ i ∈ Finset.range n, W n (X i ω))
          - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)) ∂P
        = (n : ℝ) * ∫ x, W n x * p x ∂μ
            - Real.sqrt n * ∫ x, g x * p x ∂μ := by
      intro n
      have h_sumW : ∫ ω, ∑ i ∈ Finset.range n, W n (X i ω) ∂P
                  = (n : ℝ) * ∫ x, W n x * p x ∂μ := by
        rw [MeasureTheory.integral_finset_sum _ (fun i _ => hWnX_int n i)]
        simp_rw [hEW n]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have h_sumg : ∫ ω, ∑ i ∈ Finset.range n, g (X i ω) ∂P
                  = (n : ℝ) * ∫ x, g x * p x ∂μ := by
        rw [MeasureTheory.integral_finset_sum _ (fun i _ => hgX_int i)]
        simp_rw [hEg]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [MeasureTheory.integral_sub
            (MeasureTheory.integrable_finset_sum _ (fun i _ => hWnX_int n i))
            ((MeasureTheory.integrable_finset_sum _ (fun i _ => hgX_int i)).const_mul _),
          h_sumW, MeasureTheory.integral_const_mul, h_sumg]
      -- Simplify `n·∫W·p - (√n)⁻¹·(n·∫g·p)` to `n·∫W·p - √n·∫g·p`.
      have h_inv_mul : (Real.sqrt n)⁻¹ * ((n : ℝ) * ∫ x, g x * p x ∂μ)
                     = Real.sqrt n * ∫ x, g x * p x ∂μ := by
        rcases Nat.eq_zero_or_pos n with rfl | hn_pos
        · simp
        · have h_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
          have hsqrt_pos : 0 < Real.sqrt n :=
            Real.sqrt_pos.mpr (by exact_mod_cast hn_pos)
          have hsqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrt_pos
          have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt h_nn
          have h_key : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
            field_simp; linarith [h_sqrt_sq]
          rw [← mul_assoc, h_key]
      linarith [h_inv_mul]
    -- Score zero mean eliminates the g term.
    have h_expand' : ∀ n, ∫ ω,
        ((∑ i ∈ Finset.range n, W n (X i ω))
          - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)) ∂P
        = n * ∫ x, W n x * p x ∂μ := by
      intro n; rw [h_expand n, h_Pg_zero]; ring
    -- Rewrite the target via `sum_expect_W_tendsto`.
    have h_step2 := sum_expect_W_tendsto M μ θ₀ ℓ hℓ h_one hint h_one_perturb hint_perturb
      hDQM h_fisher_cont h h_n hconv
    refine h_step2.congr fun n => ?_
    rw [h_expand' n]
    rfl
  have h_var : Filter.Tendsto
      (fun n => ProbabilityTheory.variance
        (fun ω =>
          (∑ i ∈ Finset.range n, W n (X i ω))
            - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)) P)
      Filter.atTop (𝓝 0) := by
    have h_step3 := variance_tendsto_zero M μ θ₀ ℓ hℓ hint hint_perturb hDQM
      h_fisher_cont h h_n hconv
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds h_step3
      (Filter.Eventually.of_forall fun n => ProbabilityTheory.variance_nonneg _ _)
      ?_
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    -- The variance of Y_n equals the variance of (Σᵢ Z_n ∘ X_i) via hY_eq.
    rw [ProbabilityTheory.variance_congr
          (MeasureTheory.ae_of_all P fun ω => hY_eq n ω)]
    -- Apply variance_sum to the pairwise independent summands.
    have h_Zn_indep : (↑(Finset.range n) : Set ℕ).Pairwise
        fun i j => ProbabilityTheory.IndepFun (fun ω => Z n (X i ω))
                                              (fun ω => Z n (X j ω)) P := by
      intros i _ j _ hij
      exact (hindep hij).comp (hZ_meas n) (hZ_meas n)
    -- Rewrite `fun ω => ∑ i, Z n (X i ω)` as `∑ i, fun ω => Z n (X i ω)` (η-equal).
    have h_sum_fn : (fun ω => ∑ i ∈ Finset.range n, Z n (X i ω))
                  = ∑ i ∈ Finset.range n, fun ω => Z n (X i ω) := by
      funext ω; simp [Finset.sum_apply]
    rw [h_sum_fn,
        ProbabilityTheory.IndepFun.variance_sum
          (fun i _ => hZnX_memLp n i) h_Zn_indep]
    -- All summands have the same variance by identical distribution.
    have h_var_same : ∀ i ∈ Finset.range n,
        ProbabilityTheory.variance (fun ω => Z n (X i ω)) P
          = ProbabilityTheory.variance (fun ω => Z n (X 0 ω)) P := by
      intros i _
      exact ((hident i).comp (hZ_meas n)).variance_eq
    rw [Finset.sum_congr rfl h_var_same, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- Bound the variance by E[X²] using IsProbabilityMeasure P.
    have h_aesm_Z0 : AEStronglyMeasurable (fun ω => Z n (X 0 ω)) P :=
      ((hZ_meas n).comp (hX_meas 0)).aestronglyMeasurable
    have h_var_le :
        ProbabilityTheory.variance (fun ω => Z n (X 0 ω)) P
          ≤ ∫ ω, Z n (X 0 ω) ^ 2 ∂P := by
      have := ProbabilityTheory.variance_le_expectation_sq h_aesm_Z0
      simpa using this
    have h_mul_le : (n : ℝ) * ProbabilityTheory.variance (fun ω => Z n (X 0 ω)) P
                  ≤ (n : ℝ) * ∫ ω, Z n (X 0 ω) ^ 2 ∂P :=
      mul_le_mul_of_nonneg_left h_var_le (Nat.cast_nonneg n)
    -- Transfer E_P[(Z_n ∘ X_0)²] = ∫ Z_n² · p dμ.
    have h_int_eq : ∫ ω, Z n (X 0 ω) ^ 2 ∂P
                 = ∫ x, Z n x ^ 2 * p x ∂μ :=
      h_transfer (fun x => Z n x ^ 2)
        ((hZ_meas n).pow_const 2).aestronglyMeasurable 0
    rw [h_int_eq] at h_mul_le
    -- Pull n inside the integral.
    have h_pull : (n : ℝ) * ∫ x, Z n x ^ 2 * p x ∂μ
                = ∫ x, (n : ℝ) * (Z n x ^ 2 * p x) ∂μ :=
      (MeasureTheory.integral_const_mul _ _).symm
    rw [h_pull] at h_mul_le
    -- Pointwise identity for n ≥ 1:
    --   n · (Z_n x)² · p x = (√n · W_n x - g x)² · p x.
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg n)
    have h_sqrt_ne : Real.sqrt n ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hn_pos_real)
    have h_inv_mul : Real.sqrt n * (Real.sqrt n)⁻¹ = 1 :=
      mul_inv_cancel₀ h_sqrt_ne
    have h_pt_eq : ∀ x, (n : ℝ) * (Z n x ^ 2 * p x)
                  = (Real.sqrt n * W n x - g x) ^ 2 * p x := by
      intro x
      have h_factor : Real.sqrt n * W n x - g x
                    = Real.sqrt n * (W n x - (Real.sqrt n)⁻¹ * g x) := by
        calc Real.sqrt n * W n x - g x
            = Real.sqrt n * W n x - 1 * g x := by ring
          _ = Real.sqrt n * W n x - (Real.sqrt n * (Real.sqrt n)⁻¹) * g x := by
              rw [h_inv_mul]
          _ = Real.sqrt n * (W n x - (Real.sqrt n)⁻¹ * g x) := by ring
      change (n : ℝ) * ((W n x - (Real.sqrt n)⁻¹ * g x) ^ 2 * p x) = _
      calc (n : ℝ) * ((W n x - (Real.sqrt n)⁻¹ * g x) ^ 2 * p x)
          = (Real.sqrt n * Real.sqrt n) * ((W n x - (Real.sqrt n)⁻¹ * g x) ^ 2 * p x) := by
            rw [h_sqrt_sq]
        _ = (Real.sqrt n * (W n x - (Real.sqrt n)⁻¹ * g x)) ^ 2 * p x := by ring
        _ = (Real.sqrt n * W n x - g x) ^ 2 * p x := by rw [← h_factor]
    simp_rw [h_pt_eq] at h_mul_le
    -- The RHS of h_mul_le matches the Step 3 integrand up to re-association
    -- (unfolding W = auxStatistic, g = ⟨h, ℓ·⟩, p = M.density θ₀).
    have h_integrand_eq : ∀ x,
        (Real.sqrt n * W n x - g x) ^ 2 * p x
          = (Real.sqrt n * 2 *
              (Real.sqrt (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x / M.density θ₀ x) - 1)
              - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x := by
      intro x
      change (Real.sqrt n * (2 *
              (Real.sqrt (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x / M.density θ₀ x) - 1))
            - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x
          = _
      ring
    refine le_of_le_of_eq h_mul_le ?_
    exact MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all μ h_integrand_eq)
  exact tendstoInMeasure_of_tendsto_mean_of_tendsto_variance h_mem h_mean h_var

/-! ## Step 5 — Taylor expansion of `log`

For all `x > -1`, `log(1+x) = x − ½ x² + x² R(2x)` with one **global** `R` that
satisfies `R(u) → 0` as `u → 0`. Here
`R = ForMathlib.logTaylorRemainder`. The same global remainder function applies
to every `x`, which is needed to pass from `max |W_{n,i}| → 0` to
`max |R(W_{n,i})| → 0`. -/
lemma log_one_add_taylor :
    ∃ R : ℝ → ℝ, Filter.Tendsto R (𝓝 0) (𝓝 0) ∧
      ∀ x : ℝ, -1 < x →
        Real.log (1 + x) = x - (1 / 2) * x ^ 2 + x ^ 2 * R (2 * x) :=
  ⟨ForMathlib.logTaylorRemainder,
    ForMathlib.logTaylorRemainder_tendsto_zero,
    fun _ hx => ForMathlib.log_one_add_eq_taylor hx⟩

/-! ## Step-3 L¹ corollary — `∫ |n·W_n² − g²| · p dμ → 0`

This corollary of `variance_tendsto_zero` supplies the two Δ-hypotheses
of `max_abs_W_tendsto_zero` and the primary estimate for the Markov bound. The
core argument is Cauchy–Schwarz on the factorisation

  `|n · W_n² − g²| = |√n · W_n − g| · |√n · W_n + g|`

followed by bounding the second factor using
`(√n W_n + g)² ≤ 2(√n W_n − g)² + 8 g²` and integrating. -/

omit [MeasurableSpace Θ] [OpensMeasurableSpace Θ] [SecondCountableTopology Θ] in
/-- Pointwise bound `W_n(x)² · p(x) ≤ 4 · (√p_n − √p)²`. -/
lemma auxStatistic_sq_mul_density_le
    (M : ParametricFamily 𝓧 Θ) (θ₀ : Θ) (h_n : ℕ → Θ) (n : ℕ) (x : 𝓧) :
    auxStatistic M θ₀ h_n n x ^ 2 * M.density θ₀ x
      ≤ 4 *
        (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) ^ 2 := by
  change (2 * (Real.sqrt (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x / M.density θ₀ x) - 1))
        ^ 2 * M.density θ₀ x ≤ _
  set pn := M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
  set pp := M.density θ₀ x
  have hpn_nn : 0 ≤ pn := M.density_nonneg _ _
  have hpp_nn : 0 ≤ pp := M.density_nonneg _ _
  by_cases hp_zero : pp = 0
  · rw [hp_zero, mul_zero]
    refine mul_nonneg (by norm_num) (sq_nonneg _)
  have h_sqrt_div_mul : Real.sqrt (pn / pp) * Real.sqrt pp = Real.sqrt pn := by
    rw [← Real.sqrt_mul (div_nonneg hpn_nn hpp_nn), div_mul_cancel₀ pn hp_zero]
  have h_inner :
      (2 * (Real.sqrt (pn / pp) - 1)) * Real.sqrt pp
        = 2 * (Real.sqrt pn - Real.sqrt pp) := by
    have : (2 * (Real.sqrt (pn / pp) - 1)) * Real.sqrt pp
         = 2 * (Real.sqrt (pn / pp) * Real.sqrt pp - Real.sqrt pp) := by ring
    rw [this, h_sqrt_div_mul]
  have h_factor :
      ((2 * (Real.sqrt (pn / pp) - 1)) * Real.sqrt pp) ^ 2
        = (2 * (Real.sqrt (pn / pp) - 1)) ^ 2 * (Real.sqrt pp * Real.sqrt pp) := by ring
  have h_rearrange : (2 * (Real.sqrt (pn / pp) - 1)) ^ 2 * pp
      = ((2 * (Real.sqrt (pn / pp) - 1)) * Real.sqrt pp) ^ 2 := by
    rw [h_factor, Real.mul_self_sqrt hpp_nn]
  have h_sq_eq : (2 * (Real.sqrt (pn / pp) - 1)) ^ 2 * pp
      = 4 * (Real.sqrt pn - Real.sqrt pp) ^ 2 := by
    rw [h_rearrange, h_inner]; ring
  rw [h_sq_eq]
  exact le_refl _

omit [SecondCountableTopology Θ] in
/-- Integrability of `|n · W_n² − g²| · p` for each `n`. -/
lemma delta_l1_integrable
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ) (hℓ : Measurable ℓ)
    (hint : Integrable (M.density θ₀) μ)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h : Θ) (h_n : ℕ → Θ) (n : ℕ) :
    Integrable (fun x =>
      |(n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 - ⟪h, ℓ x⟫ ^ 2|
        * M.density θ₀ x) μ := by
  -- Bound `|n · W_n² − g²| · p ≤ n · (W_n² · p) + g² · p`, both RHS integrable.
  -- W_n² · p ≤ 4 · (√p_n − √p)² pointwise ⇒ integrable.
  have h_sqrt_diff_memLp : MemLp (fun x =>
      M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) 2 μ := by
    exact (M.sqrtDensity_memLp_two μ _ (hint_perturb _ _)).sub
      (M.sqrtDensity_memLp_two μ _ hint)
  have h_Wnsq_p_int : Integrable
      (fun x => auxStatistic M θ₀ h_n n x ^ 2 * M.density θ₀ x) μ := by
    have h_sq_int := h_sqrt_diff_memLp.integrable_sq
    have h_m : Measurable fun x =>
        auxStatistic M θ₀ h_n n x ^ 2 * M.density θ₀ x :=
      ((auxStatistic_measurable M θ₀ h_n n).pow_const 2).mul (M.density_meas θ₀)
    refine Integrable.mono' (h_sq_int.const_mul 4) h_m.aestronglyMeasurable
      (MeasureTheory.ae_of_all μ fun x => ?_)
    rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (M.density_nonneg θ₀ x))]
    exact auxStatistic_sq_mul_density_le M θ₀ h_n n x
  have h_gsq_p_int : Integrable (fun x => ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x) μ :=
    dqm_fisher_integrable M μ θ₀ ℓ hint hDQM h (fun t => hint_perturb t h)
  -- Bound: |n · W_n² − g²| · p ≤ (n · W_n² + g²) · p
  have h_bound_int : Integrable
      (fun x => ((n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 + ⟪h, ℓ x⟫ ^ 2)
                  * M.density θ₀ x) μ := by
    have h1 : Integrable
        (fun x => (n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 * M.density θ₀ x) μ := by
      have : (fun x => (n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 * M.density θ₀ x)
            = fun x => (n : ℝ) * (auxStatistic M θ₀ h_n n x ^ 2 * M.density θ₀ x) := by
        funext x; ring
      rw [this]; exact h_Wnsq_p_int.const_mul _
    have h2 : (fun x => ((n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 + ⟪h, ℓ x⟫ ^ 2)
                        * M.density θ₀ x)
            = fun x => (n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 * M.density θ₀ x
                       + ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x := by
      funext x; ring
    rw [h2]; exact h1.add h_gsq_p_int
  have hg_meas : Measurable fun x => ⟪h, ℓ x⟫ :=
    ((continuous_const (y := h)).inner continuous_id).measurable.comp hℓ
  have h_outer_meas : Measurable fun x =>
      |(n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 - ⟪h, ℓ x⟫ ^ 2| * M.density θ₀ x := by
    have h_diff : Measurable fun x =>
        (n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 - ⟪h, ℓ x⟫ ^ 2 :=
      (((auxStatistic_measurable M θ₀ h_n n).pow_const 2).const_mul (n : ℝ)).sub
        (hg_meas.pow_const 2)
    exact (continuous_abs.measurable.comp h_diff).mul (M.density_meas θ₀)
  refine Integrable.mono' h_bound_int h_outer_meas.aestronglyMeasurable
    (MeasureTheory.ae_of_all μ fun x => ?_)
  have h_lhs_nn : 0 ≤ |(n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 - ⟪h, ℓ x⟫ ^ 2|
              * M.density θ₀ x :=
    mul_nonneg (abs_nonneg _) (M.density_nonneg θ₀ x)
  have h_A_nn : 0 ≤ (n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have h_B_nn : 0 ≤ (⟪h, ℓ x⟫ : ℝ) ^ 2 := sq_nonneg _
  have h_abs_le :
      |(n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 - ⟪h, ℓ x⟫ ^ 2|
        ≤ (n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 + ⟪h, ℓ x⟫ ^ 2 :=
    calc |(n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 - ⟪h, ℓ x⟫ ^ 2|
        ≤ |(n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2| + |⟪h, ℓ x⟫ ^ 2| := abs_sub _ _
      _ = (n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 + ⟪h, ℓ x⟫ ^ 2 := by
          rw [abs_of_nonneg h_A_nn, abs_of_nonneg h_B_nn]
  rw [Real.norm_eq_abs, abs_of_nonneg h_lhs_nn]
  exact mul_le_mul_of_nonneg_right h_abs_le (M.density_nonneg θ₀ x)

omit [SecondCountableTopology Θ] in
/-- Step-3 L¹ corollary: `∫ |n · W_n² − g²| · p dμ → 0`. Proof via Cauchy–Schwarz on
the factorisation `n · W_n² − g² = (√n · W_n − g)(√n · W_n + g)`, with the first
factor's L² norm going to 0 by Step 3 (`variance_tendsto_zero`) and the second
factor's L² norm eventually bounded via `(a+b)² ≤ 2(a−b)² + 8b²`. -/
lemma delta_l1_tendsto
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ) (hℓ : Measurable ℓ)
    (hint : Integrable (M.density θ₀) μ)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h_fisher_cont :
      Filter.Tendsto (fun v : Θ => ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
        (𝓝 0) (𝓝 0))
    (h : Θ) (h_n : ℕ → Θ) (hconv : Filter.Tendsto h_n Filter.atTop (𝓝 h)) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ x, |(n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 - ⟪h, ℓ x⟫ ^ 2|
              * M.density θ₀ x ∂μ)
      Filter.atTop (𝓝 0) := by
  -- Notation and basic facts.
  have hp_nn : ∀ x, 0 ≤ M.density θ₀ x := M.density_nonneg θ₀
  have hp_meas : Measurable (M.density θ₀) := M.density_meas θ₀
  have hW_meas : ∀ n, Measurable (auxStatistic M θ₀ h_n n) :=
    fun n => auxStatistic_measurable M θ₀ h_n n
  have hg_meas : Measurable (fun x => ⟪h, ℓ x⟫) :=
    ((continuous_const (y := h)).inner continuous_id).measurable.comp hℓ
  have hsp_nn : ∀ x, 0 ≤ M.sqrtDensity θ₀ x := M.sqrtDensity_nonneg θ₀
  have hsp_sq : ∀ x, M.sqrtDensity θ₀ x ^ 2 = M.density θ₀ x := M.sqrtDensity_sq θ₀
  have hsp_mul : ∀ x, M.sqrtDensity θ₀ x * M.sqrtDensity θ₀ x = M.density θ₀ x := by
    intro x; rw [← sq]; exact hsp_sq x
  -- Step-3 gives `α_n := ∫ (√n · W_n − g)² · p dμ → 0`.
  have h_step3 := variance_tendsto_zero M μ θ₀ ℓ hℓ hint hint_perturb hDQM
    h_fisher_cont h h_n hconv
  have h_α : Filter.Tendsto
      (fun n : ℕ => ∫ x,
        (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x ∂μ)
      Filter.atTop (𝓝 0) := by
    refine h_step3.congr (fun n => ?_)
    refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all μ fun x => ?_)
    change (Real.sqrt n * 2 *
            (Real.sqrt (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x / M.density θ₀ x) - 1)
            - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x
          = (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x
    change (Real.sqrt n * 2 *
            (Real.sqrt (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x / M.density θ₀ x) - 1)
            - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x
          = (Real.sqrt n *
              (2 * (Real.sqrt (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x /
                              M.density θ₀ x) - 1)) - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x
    ring
  -- `g² · p ∈ L¹(μ)` (Fisher finite).
  have hgsq_p_int : Integrable (fun x => ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x) μ :=
    dqm_fisher_integrable M μ θ₀ ℓ hint hDQM h (fun t => hint_perturb t h)
  set Pg_sq : ℝ := ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ with hPg_sq_def
  have hPg_sq_nn : 0 ≤ Pg_sq := by
    refine MeasureTheory.integral_nonneg fun x => ?_
    exact mul_nonneg (sq_nonneg _) (hp_nn x)
  -- Pointwise: `(√n W_n + g)² ≤ 2 (√n W_n − g)² + 8 g²`.
  have h_β_pt : ∀ n : ℕ, ∀ x,
      (Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x
        ≤ 2 * ((Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x)
          + 8 * (⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x) := by
    intro n x
    have h_px : 0 ≤ M.density θ₀ x := hp_nn x
    -- Pointwise: (a + b)² ≤ 2·(a-b)² + 8·b², where a = √n W_n, b = g.
    -- Via a + b = (a - b) + 2b, so (a+b)² = ((a-b) + 2b)² ≤ 2(a-b)² + 2(2b)² = 2(a-b)² + 8b².
    have h_sq :
        (Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫) ^ 2
          ≤ 2 * (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
            + 8 * ⟪h, ℓ x⟫ ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt n * auxStatistic M θ₀ h_n n x -
                              ⟪h, ℓ x⟫ - 2 * ⟪h, ℓ x⟫),
                 sq_nonneg (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫),
                 sq_nonneg (⟪h, ℓ x⟫)]
    have := mul_le_mul_of_nonneg_right h_sq h_px
    linarith [this]
  -- Integrability of `(√n W_n ± g)² · p`.
  have h_sumsq_int : ∀ n : ℕ, Integrable
      (fun x => (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                  * M.density θ₀ x) μ := by
    intro n
    -- Bound by 4 · (scaled sqrtDensity diff)² + 4 · g² · p, both integrable.
    have h_sqrt_diff_memLp : MemLp (fun x =>
        Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x -
                        M.sqrtDensity θ₀ x)
        - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
      have h_sqrt_p : MemLp (M.sqrtDensity θ₀) 2 μ :=
        M.sqrtDensity_memLp_two μ _ hint
      have h_sqrt_pn : MemLp (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n)) 2 μ :=
        M.sqrtDensity_memLp_two μ _ (hint_perturb _ _)
      have h_scaled : MemLp (fun x =>
          Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                          - M.sqrtDensity θ₀ x)) 2 μ :=
        (h_sqrt_pn.sub h_sqrt_p).const_mul _
      have h_score := dqm_score_memLp_two M μ θ₀ ℓ hint hDQM h (fun t => hint_perturb t h)
      have h_half : MemLp (fun x => (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
        have h_eq : (fun x => (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x)
                  = fun x => (1 / 2 : ℝ) * (⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) := by
          funext x; ring
        rw [h_eq]; exact h_score.const_mul _
      exact h_scaled.sub h_half
    have h_φ_sq_int : Integrable (fun x =>
        (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x -
                          M.sqrtDensity θ₀ x)
          - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) μ :=
      h_sqrt_diff_memLp.integrable_sq
    have h_4φ_sq_int : Integrable (fun x =>
        4 * (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x -
                              M.sqrtDensity θ₀ x)
              - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) μ :=
      h_φ_sq_int.const_mul 4
    -- Pointwise bound from Step 3's proof (equality on {p > 0}, trivial on {p = 0}).
    have h_bound_pt : ∀ x,
        (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2 * M.density θ₀ x
          ≤ 4 * (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x -
                                 M.sqrtDensity θ₀ x)
                  - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 := by
      -- This is the same pointwise bound as in `variance_tendsto_zero`'s proof.
      intro x
      set pn := M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
      set pp := M.density θ₀ x
      have hpn_nn : 0 ≤ pn := M.density_nonneg _ _
      have hpp_nn : 0 ≤ pp := M.density_nonneg _ _
      by_cases hp_zero : pp = 0
      · rw [hp_zero, mul_zero]
        refine mul_nonneg (by norm_num) (sq_nonneg _)
      have hp_pos : 0 < pp := lt_of_le_of_ne hpp_nn (Ne.symm hp_zero)
      have h_sqDensity_pn :
          M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x = Real.sqrt pn := rfl
      have h_sqDensity_p : M.sqrtDensity θ₀ x = Real.sqrt pp := rfl
      have h_p_eq : pp = Real.sqrt pp * Real.sqrt pp := (Real.mul_self_sqrt hpp_nn).symm
      have h_sqrt_div_mul : Real.sqrt (pn / pp) * Real.sqrt pp = Real.sqrt pn := by
        rw [← Real.sqrt_mul (div_nonneg hpn_nn hpp_nn), div_mul_cancel₀ pn hp_zero]
      change (Real.sqrt n * (2 * (Real.sqrt (pn / pp) - 1)) - ⟪h, ℓ x⟫) ^ 2 * pp ≤ _
      have h_inner_mul :
          (Real.sqrt n * (2 * (Real.sqrt (pn / pp) - 1)) - ⟪h, ℓ x⟫) * Real.sqrt pp
            = 2 * Real.sqrt n * (Real.sqrt pn - Real.sqrt pp)
              - ⟪h, ℓ x⟫ * Real.sqrt pp := by
        have : (Real.sqrt n * (2 * (Real.sqrt (pn / pp) - 1)) - ⟪h, ℓ x⟫) * Real.sqrt pp
             = 2 * Real.sqrt n * (Real.sqrt (pn / pp) * Real.sqrt pp - Real.sqrt pp)
                - ⟪h, ℓ x⟫ * Real.sqrt pp := by ring
        rw [this, h_sqrt_div_mul]
      have h_LHS_eq :
          (Real.sqrt n * (2 * (Real.sqrt (pn / pp) - 1)) - ⟪h, ℓ x⟫) ^ 2 * pp
            = (2 * Real.sqrt n * (Real.sqrt pn - Real.sqrt pp)
                - ⟪h, ℓ x⟫ * Real.sqrt pp) ^ 2 := by
        calc (Real.sqrt n * (2 * (Real.sqrt (pn / pp) - 1)) - ⟪h, ℓ x⟫) ^ 2 * pp
            = (Real.sqrt n * (2 * (Real.sqrt (pn / pp) - 1)) - ⟪h, ℓ x⟫) ^ 2
                * (Real.sqrt pp * Real.sqrt pp) := by rw [← h_p_eq]
          _ = ((Real.sqrt n * (2 * (Real.sqrt (pn / pp) - 1)) - ⟪h, ℓ x⟫) *
                Real.sqrt pp) ^ 2 := by ring
          _ = (2 * Real.sqrt n * (Real.sqrt pn - Real.sqrt pp)
                - ⟪h, ℓ x⟫ * Real.sqrt pp) ^ 2 := by rw [h_inner_mul]
      have h_RHS_eq :
          4 * (Real.sqrt n * (Real.sqrt pn - Real.sqrt pp)
                - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * Real.sqrt pp) ^ 2
            = (2 * Real.sqrt n * (Real.sqrt pn - Real.sqrt pp)
                - ⟪h, ℓ x⟫ * Real.sqrt pp) ^ 2 := by ring
      rw [h_LHS_eq, ← h_RHS_eq, h_sqDensity_pn, h_sqDensity_p]
    refine Integrable.mono' h_4φ_sq_int ?_ (MeasureTheory.ae_of_all μ fun x => ?_)
    · exact ((((hW_meas n).const_mul (Real.sqrt n)).sub hg_meas).pow_const 2).mul
              hp_meas |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (hp_nn x))]
      exact h_bound_pt x
  have h_sumsq_int_plus : ∀ n : ℕ, Integrable
      (fun x => (Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫) ^ 2
                  * M.density θ₀ x) μ := by
    intro n
    -- Use h_β_pt + integrability of 2 α_n integrand + 8 · g² · p.
    have h_minus := h_sumsq_int n
    have h_bound : Integrable
        (fun x => 2 * ((Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                          * M.density θ₀ x)
                    + 8 * (⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x)) μ :=
      (h_minus.const_mul 2).add (hgsq_p_int.const_mul 8)
    refine Integrable.mono' h_bound ?_ (MeasureTheory.ae_of_all μ fun x => ?_)
    · exact ((((hW_meas n).const_mul (Real.sqrt n)).add hg_meas).pow_const 2).mul
              hp_meas |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (hp_nn x))]
      exact h_β_pt n x
  -- β_n bound: `β_n ≤ 2 α_n + 8 Pg²`.
  have h_β_bound : ∀ n : ℕ,
      (∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫) ^ 2
              * M.density θ₀ x ∂μ)
        ≤ 2 * (∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                      * M.density θ₀ x ∂μ)
          + 8 * Pg_sq := by
    intro n
    have h_int_le :=
      MeasureTheory.integral_mono_of_nonneg
        (MeasureTheory.ae_of_all μ fun x =>
          mul_nonneg (sq_nonneg _) (hp_nn x))
        (((h_sumsq_int n).const_mul 2).add (hgsq_p_int.const_mul 8))
        (MeasureTheory.ae_of_all μ (h_β_pt n))
    have h_rhs_eq :
        ∫ x, 2 * ((Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                    * M.density θ₀ x)
              + 8 * (⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x) ∂μ
          = 2 * (∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                          * M.density θ₀ x ∂μ)
            + 8 * Pg_sq := by
      rw [MeasureTheory.integral_add ((h_sumsq_int n).const_mul 2)
            (hgsq_p_int.const_mul 8),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    simp only [Pi.add_apply] at h_int_le
    rw [h_rhs_eq] at h_int_le
    exact h_int_le
  -- Cauchy–Schwarz step: `∫ |n · W_n² − g²| · p ≤ √α_n · √β_n`.
  have h_cs : ∀ n : ℕ,
      ∫ x, |(n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 - ⟪h, ℓ x⟫ ^ 2|
            * M.density θ₀ x ∂μ
        ≤ Real.sqrt (∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                            * M.density θ₀ x ∂μ)
          * Real.sqrt (∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫) ^ 2
                              * M.density θ₀ x ∂μ) := by
    intro n
    -- F = |√n · W_n − g| · √p, G = |√n · W_n + g| · √p.
    set F : 𝓧 → ℝ := fun x =>
      |Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫| * M.sqrtDensity θ₀ x
    set G : 𝓧 → ℝ := fun x =>
      |Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫| * M.sqrtDensity θ₀ x
    -- MemLp of F, G (via pointwise equality with the signed version).
    have h_F_sq_eq : ∀ x,
        F x ^ 2 = (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                  * M.density θ₀ x := by
      intro x
      change (|Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫| * M.sqrtDensity θ₀ x) ^ 2
          = _
      rw [mul_pow, sq_abs]
      congr 1
      rw [show M.sqrtDensity θ₀ x ^ 2 = M.density θ₀ x from hsp_sq x]
    have h_G_sq_eq : ∀ x,
        G x ^ 2 = (Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫) ^ 2
                  * M.density θ₀ x := by
      intro x
      change (|Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫| * M.sqrtDensity θ₀ x) ^ 2
          = _
      rw [mul_pow, sq_abs]
      congr 1
      rw [show M.sqrtDensity θ₀ x ^ 2 = M.density θ₀ x from hsp_sq x]
    have hF_meas : Measurable F :=
      (continuous_abs.measurable.comp
        (((hW_meas n).const_mul (Real.sqrt n)).sub hg_meas)).mul (M.sqrtDensity_meas θ₀)
    have hG_meas : Measurable G :=
      (continuous_abs.measurable.comp
        (((hW_meas n).const_mul (Real.sqrt n)).add hg_meas)).mul (M.sqrtDensity_meas θ₀)
    have hF_memLp : MemLp F 2 μ := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq hF_meas.aestronglyMeasurable).mpr ?_
      refine (h_sumsq_int n).congr (MeasureTheory.ae_of_all μ fun x => ?_)
      exact (h_F_sq_eq x).symm
    have hG_memLp : MemLp G 2 μ := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq hG_meas.aestronglyMeasurable).mpr ?_
      refine (h_sumsq_int_plus n).congr (MeasureTheory.ae_of_all μ fun x => ?_)
      exact (h_G_sq_eq x).symm
    -- F · G = |n W_n² − g²| · p pointwise.
    have h_FG_eq : ∀ x, F x * G x
        = |(n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 - ⟪h, ℓ x⟫ ^ 2| * M.density θ₀ x := by
      intro x
      change |Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫| * M.sqrtDensity θ₀ x
            * (|Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫| * M.sqrtDensity θ₀ x)
          = _
      have h_sqrt_mul :
          M.sqrtDensity θ₀ x * M.sqrtDensity θ₀ x = M.density θ₀ x := hsp_mul x
      have h_n_real : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt (Nat.cast_nonneg
          n)).symm
      calc |Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫| * M.sqrtDensity θ₀ x
            * (|Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫| * M.sqrtDensity θ₀ x)
          = (|Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫|
              * |Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫|)
              * (M.sqrtDensity θ₀ x * M.sqrtDensity θ₀ x) := by ring
        _ = |(Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫)
              * (Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫)|
              * M.density θ₀ x := by rw [← abs_mul, h_sqrt_mul]
        _ = |(Real.sqrt n * auxStatistic M θ₀ h_n n x) ^ 2 - ⟪h, ℓ x⟫ ^ 2|
              * M.density θ₀ x := by
            congr 1; congr 1; ring
        _ = |(n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 - ⟪h, ℓ x⟫ ^ 2|
              * M.density θ₀ x := by
            congr 2
            rw [show (Real.sqrt n * auxStatistic M θ₀ h_n n x) ^ 2
                    = Real.sqrt n * Real.sqrt n * auxStatistic M θ₀ h_n n x ^ 2 from by ring,
                ← h_n_real]
    -- Apply CS.
    have h_FG_nn : ∀ x, 0 ≤ F x * G x := by
      intro x
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (hsp_nn x))
                        (mul_nonneg (abs_nonneg _) (hsp_nn x))
    have h_cs_abs :=
      AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq μ hF_memLp hG_memLp
    have h_FG_int :
        ∫ x, F x * G x ∂μ
          = ∫ x, |(n : ℝ) * auxStatistic M θ₀ h_n n x ^ 2 - ⟪h, ℓ x⟫ ^ 2|
                  * M.density θ₀ x ∂μ :=
      MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all μ h_FG_eq)
    have h_abs_int_eq :
        |∫ x, F x * G x ∂μ|
          = ∫ x, F x * G x ∂μ := by
      rw [abs_of_nonneg]
      exact MeasureTheory.integral_nonneg (fun x => h_FG_nn x)
    have h_F_sq_int :
        ∫ x, F x ^ 2 ∂μ
          = ∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                  * M.density θ₀ x ∂μ :=
      MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all μ h_F_sq_eq)
    have h_G_sq_int :
        ∫ x, G x ^ 2 ∂μ
          = ∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x + ⟪h, ℓ x⟫) ^ 2
                  * M.density θ₀ x ∂μ :=
      MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all μ h_G_sq_eq)
    rw [h_abs_int_eq, h_FG_int, h_F_sq_int, h_G_sq_int] at h_cs_abs
    exact h_cs_abs
  -- Squeeze: `0 ≤ target ≤ √α_n · √(2 α_n + 8 Pg²) → 0`.
  have h_upper_tendsto : Filter.Tendsto
      (fun n : ℕ =>
        Real.sqrt (∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                          * M.density θ₀ x ∂μ)
        * Real.sqrt (2 * (∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                          * M.density θ₀ x ∂μ) + 8 * Pg_sq))
      Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ =>
        Real.sqrt (∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                          * M.density θ₀ x ∂μ)) Filter.atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h_α
      simpa using! this
    have h2 : Filter.Tendsto (fun n : ℕ =>
        Real.sqrt (2 * (∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                          * M.density θ₀ x ∂μ) + 8 * Pg_sq))
        Filter.atTop (𝓝 (Real.sqrt (8 * Pg_sq))) := by
      have h_lin : Filter.Tendsto (fun n : ℕ =>
          2 * (∫ x, (Real.sqrt n * auxStatistic M θ₀ h_n n x - ⟪h, ℓ x⟫) ^ 2
                          * M.density θ₀ x ∂μ) + 8 * Pg_sq)
          Filter.atTop (𝓝 (2 * 0 + 8 * Pg_sq)) :=
        (h_α.const_mul 2).add_const _
      have := (Real.continuous_sqrt.tendsto (2 * 0 + 8 * Pg_sq)).comp h_lin
      simpa using! this
    have := h1.mul h2
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_upper_tendsto
    (Filter.Eventually.of_forall fun n =>
      MeasureTheory.integral_nonneg
        fun x => mul_nonneg (abs_nonneg _) (hp_nn x))
    (Filter.Eventually.of_forall fun n => ?_)
  refine (h_cs n).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt (h_β_bound n)

/-! ## Step 6a — `Σᵢ W_{n,i}² →ₚ P g²`

On the same iid setup as `sum_W_decomp` (probability space `(Ω, ℙ)`, iid
sample `X : ℕ → Ω → 𝓧` with law `P_{θ₀} = μ.withDensity p_{θ₀}`),

  `∑_{i < n} W_n(X_i ω)² →ₚ P_{θ₀} g² = fisherInformation M μ θ₀ ℓ h h`.

The proof writes `Σ W_n² = (1/n) (Σ g²(X_i) + Σ Δ_{n,i})`
where `Δ_{n,i} := n · W_n(X_i)² − g(X_i)²`. Then:
  * `(1/n) Σ g²(X_i) →ₚ P g²` by the strong law of large numbers applied
    to the iid sequence `g² ∘ X_i` (in-probability follows from a.s.),
    using `dqm_fisher_integrable` for `g² · p ∈ L¹(μ) ⇒ g² ∘ X_i ∈ L¹(ℙ)`.
  * `(1/n) Σ Δ_{n,i} →ₚ 0` by Markov, via
    `E|Δ_{n,1}| = ∫ |n · W_n² − g²| · p dμ → 0` (a Step-3 corollary, proved
    by Cauchy–Schwarz on `|n W_n² − g²| ≤ |√n W_n − g| · |√n W_n + g|`). -/
lemma sum_W_sq_tendsto_to_Pg_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ) (hℓ : Measurable ℓ)
    (hint : Integrable (M.density θ₀) μ)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h_fisher_cont :
      Filter.Tendsto (fun v : Θ => ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
        (𝓝 0) (𝓝 0))
    (h : Θ) (h_n : ℕ → Θ) (hconv : Filter.Tendsto h_n Filter.atTop (𝓝 h))
    (X : ℕ → Ω → 𝓧) (hX_meas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) P)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P P)
    (hlaw : Measure.map (X 0) P
              = μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) :
    TendstoInMeasure P
      (fun n ω => ∑ i ∈ Finset.range n, auxStatistic M θ₀ h_n n (X i ω) ^ 2)
      Filter.atTop
      (fun _ => fisherInformation M μ θ₀ ℓ h h) := by
  -- Notation.
  set g : 𝓧 → ℝ := fun x => ⟪h, ℓ x⟫ with hg_def
  set p : 𝓧 → ℝ := M.density θ₀ with hp_def
  set ν : Measure 𝓧 := μ.withDensity fun x => ENNReal.ofReal (p x) with hν_def
  set W : ℕ → 𝓧 → ℝ := auxStatistic M θ₀ h_n with hW_def
  have hp_meas : Measurable p := M.density_meas θ₀
  have hp_nn : ∀ x, 0 ≤ p x := M.density_nonneg θ₀
  have hg_meas : Measurable g :=
    ((continuous_const (y := h)).inner continuous_id).measurable.comp hℓ
  have hgsq_meas : Measurable (fun x => g x ^ 2) := hg_meas.pow_const 2
  have hW_meas : ∀ n, Measurable (W n) := fun n => auxStatistic_measurable M θ₀ h_n n
  -- Each `X i` has law `ν`.
  have h_map : ∀ i, Measure.map (X i) P = ν := by
    intro i
    rw [(hident i).map_eq, hlaw]
  -- Transfer integrals: `∫ ω, f (X i ω) ∂P = ∫ x, f x · p x ∂μ`.
  have h_transfer : ∀ (f : 𝓧 → ℝ), AEStronglyMeasurable f ν →
      ∀ i, ∫ ω, f (X i ω) ∂P = ∫ x, f x * p x ∂μ := by
    intro f hf_aesm i
    have h_aesm_map : AEStronglyMeasurable f (Measure.map (X i) P) := by
      rw [h_map i]; exact hf_aesm
    have h_step1 : ∫ ω, f (X i ω) ∂P = ∫ y, f y ∂ν := by
      rw [← h_map i, MeasureTheory.integral_map (hX_meas i).aemeasurable h_aesm_map]
    have h_step2 : ∫ y, f y ∂ν = ∫ y, p y * f y ∂μ := by
      rw [hν_def,
          integral_withDensity_eq_integral_toReal_smul
            (μ := μ) hp_meas.ennreal_ofReal
            (MeasureTheory.ae_of_all μ fun _ => ENNReal.ofReal_lt_top) f]
      refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all μ fun y => ?_)
      simp [ENNReal.toReal_ofReal (hp_nn y)]
    rw [h_step1, h_step2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  -- Transfer integrability: `f · p ∈ L¹(μ) ⇒ f ∘ X i ∈ L¹(P)`.
  have h_transfer_int : ∀ (f : 𝓧 → ℝ), Measurable f →
      Integrable (fun x => f x * p x) μ →
      ∀ i, Integrable (fun ω => f (X i ω)) P := by
    intro f hf_meas hfp_int i
    have hf_ν : Integrable f ν := by
      rw [hν_def]
      refine (MeasureTheory.integrable_withDensity_iff hp_meas.ennreal_ofReal
                (MeasureTheory.ae_of_all μ fun _ => ENNReal.ofReal_lt_top)).mpr ?_
      refine hfp_int.congr (MeasureTheory.ae_of_all μ fun x => ?_)
      simp [ENNReal.toReal_ofReal (hp_nn x)]
    have hf_map : Integrable f (Measure.map (X i) P) := by
      rw [h_map i]; exact hf_ν
    exact (MeasureTheory.integrable_map_measure hf_meas.aestronglyMeasurable
            (hX_meas i).aemeasurable).mp hf_map
  -- Integrability of `g² · p`.
  have hgsq_p_int : Integrable (fun x => g x ^ 2 * p x) μ :=
    dqm_fisher_integrable M μ θ₀ ℓ hint hDQM h (fun t => hint_perturb t h)
  -- Rewrite `fisherInformation` as `Pg_sq`.
  set Pg_sq : ℝ := ∫ x, g x ^ 2 * p x ∂μ with hPg_sq_def
  have h_fisher_eq : fisherInformation M μ θ₀ ℓ h h = Pg_sq := by
    change ∫ x, (⟪h, ℓ x⟫ * ⟪h, ℓ x⟫) * M.density θ₀ x ∂μ = ∫ x, g x ^ 2 * p x ∂μ
    refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all μ fun x => ?_)
    change (⟪h, ℓ x⟫ * ⟪h, ℓ x⟫) * M.density θ₀ x = ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x
    ring
  suffices h : TendstoInMeasure P
      (fun n ω => ∑ i ∈ Finset.range n, W n (X i ω) ^ 2)
      Filter.atTop (fun _ : Ω => Pg_sq) by
    refine h.congr_right ?_
    exact Filter.Eventually.of_forall (fun _ => h_fisher_eq.symm)
  -- Δ_n(x) := n · W_n(x)² − g(x)².
  set Δ : ℕ → 𝓧 → ℝ := fun n x => (n : ℝ) * W n x ^ 2 - g x ^ 2 with hΔ_def
  have hΔ_meas : ∀ n, Measurable (Δ n) :=
    fun n => (((hW_meas n).pow_const 2).const_mul _).sub hgsq_meas
  -- `W_n² · p ∈ L¹(μ)` via the 4·(√p_n − √p)² bound.
  have hWnsq_p_int : ∀ n : ℕ, Integrable (fun x => W n x ^ 2 * p x) μ := by
    intro n
    have h_sqrt_diff_memLp : MemLp (fun x =>
        M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x) 2 μ :=
      (M.sqrtDensity_memLp_two μ _ (hint_perturb _ _)).sub
        (M.sqrtDensity_memLp_two μ _ hint)
    have h_sq_int := h_sqrt_diff_memLp.integrable_sq
    have h_m : Measurable fun x => W n x ^ 2 * p x :=
      ((hW_meas n).pow_const 2).mul hp_meas
    refine Integrable.mono' (h_sq_int.const_mul 4) h_m.aestronglyMeasurable
      (MeasureTheory.ae_of_all μ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hp_nn x))]
    exact auxStatistic_sq_mul_density_le M θ₀ h_n n x
  -- `Δ_n · p ∈ L¹(μ)`.
  have hΔp_int : ∀ n, Integrable (fun x => Δ n x * p x) μ := by
    intro n
    have h_eq : (fun x => Δ n x * p x)
              = fun x => (n : ℝ) * (W n x ^ 2 * p x) - g x ^ 2 * p x := by
      funext x; change ((n : ℝ) * W n x ^ 2 - g x ^ 2) * p x = _; ring
    rw [h_eq]
    exact ((hWnsq_p_int n).const_mul _).sub hgsq_p_int
  -- `Δ_n ∘ X_i ∈ L¹(P)` and `g² ∘ X_i ∈ L¹(P)`.
  have hΔX_int : ∀ n i, Integrable (fun ω => Δ n (X i ω)) P :=
    fun n i => h_transfer_int (Δ n) (hΔ_meas n) (hΔp_int n) i
  have hgsqX_int : ∀ i, Integrable (fun ω => g (X i ω) ^ 2) P :=
    fun i => h_transfer_int (fun x => g x ^ 2) hgsq_meas hgsq_p_int i
  -- `g² ∘ X_i` is IdentDistrib with `g² ∘ X_0`, and pairwise independent.
  have hgsqX_ident : ∀ i, ProbabilityTheory.IdentDistrib
      (fun ω => g (X i ω) ^ 2) (fun ω => g (X 0 ω) ^ 2) P P := fun i =>
    (hident i).comp hgsq_meas
  have hgsqX_indep : Pairwise fun i j =>
      ProbabilityTheory.IndepFun (fun ω => g (X i ω) ^ 2) (fun ω => g (X j ω) ^ 2) P := by
    intro i j hij
    exact (hindep hij).comp hgsq_meas hgsq_meas
  have hE_gsqX : ∫ ω, g (X 0 ω) ^ 2 ∂P = Pg_sq :=
    h_transfer (fun x => g x ^ 2) hgsq_meas.aestronglyMeasurable 0
  -- Part A: `(1/n) ∑ g²(X_i) →_{a.s.} Pg_sq` by SLLN.
  have h_slln : ∀ᵐ ω ∂P, Filter.Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, g (X i ω) ^ 2) / (n : ℝ))
      Filter.atTop (𝓝 Pg_sq) := by
    have h := ProbabilityTheory.strong_law_ae_real
      (μ := P) (fun i ω => g (X i ω) ^ 2) (hgsqX_int 0) hgsqX_indep hgsqX_ident
    filter_upwards [h] with ω hω
    rw [← hE_gsqX]; exact hω
  -- Part A in-measure.
  have hA_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => (∑ i ∈ Finset.range n, g (X i ω) ^ 2) / (n : ℝ)) P := by
    intro n
    have h_sum : Measurable fun ω => ∑ i ∈ Finset.range n, g (X i ω) ^ 2 :=
      Finset.measurable_sum _ (fun i _ => (hg_meas.comp (hX_meas i)).pow_const 2)
    exact (h_sum.div_const _).aestronglyMeasurable
  have hA_tendsto : TendstoInMeasure P
      (fun n ω => (∑ i ∈ Finset.range n, g (X i ω) ^ 2) / (n : ℝ))
      Filter.atTop (fun _ => Pg_sq) :=
    tendstoInMeasure_of_tendsto_ae hA_meas h_slln
  -- Part B: `(1/n) ∑ Δ_n(X_i) →_P 0` via L¹.
  have hΔ_l1 := delta_l1_tendsto M μ θ₀ ℓ hℓ hint hint_perturb hDQM h_fisher_cont h h_n hconv
  have hB_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ)) P := by
    intro n
    have h_sum : Measurable fun ω => ∑ i ∈ Finset.range n, Δ n (X i ω) :=
      Finset.measurable_sum _ (fun i _ => (hΔ_meas n).comp (hX_meas i))
    exact (h_sum.div_const _).aestronglyMeasurable
  have hB_int : ∀ n, Integrable
      (fun ω => (∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ)) P := by
    intro n
    refine (MeasureTheory.integrable_finset_sum _ ?_).div_const _
    intro i _
    exact hΔX_int n i
  -- L¹ bound: `∫ |B_n| dP ≤ ∫ |Δ_n| · p dμ` for `n ≥ 1`.
  have hB_L1_bound : ∀ n : ℕ, 1 ≤ n →
      ∫ ω, |(∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ)| ∂P
        ≤ ∫ x, |Δ n x| * p x ∂μ := by
    intro n hn
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos_real
    have h_pt : ∀ ω, |(∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ)|
                    ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, |Δ n (X i ω)| := by
      intro ω
      rw [abs_div, abs_of_pos hn_pos_real, div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Finset.abs_sum_le_sum_abs _ _
    have h_int_abs : Integrable
        (fun ω => ∑ i ∈ Finset.range n, |Δ n (X i ω)|) P :=
      MeasureTheory.integrable_finset_sum _ (fun i _ => (hΔX_int n i).abs)
    calc ∫ ω, |(∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ)| ∂P
        ≤ ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, |Δ n (X i ω)| ∂P := by
          refine MeasureTheory.integral_mono_ae (hB_int n).abs ?_
            (Filter.Eventually.of_forall h_pt)
          exact h_int_abs.const_mul _
      _ = (n : ℝ)⁻¹ * ∫ ω, ∑ i ∈ Finset.range n, |Δ n (X i ω)| ∂P := by
          rw [MeasureTheory.integral_const_mul]
      _ = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ ω, |Δ n (X i ω)| ∂P := by
          rw [MeasureTheory.integral_finset_sum _ (fun i _ => (hΔX_int n i).abs)]
      _ = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ x, |Δ n x| * p x ∂μ := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          exact h_transfer (fun x => |Δ n x|)
            (continuous_abs.measurable.comp (hΔ_meas n)).aestronglyMeasurable i
      _ = (n : ℝ)⁻¹ * ((n : ℝ) * ∫ x, |Δ n x| * p x ∂μ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∫ x, |Δ n x| * p x ∂μ := by
          rw [← mul_assoc, inv_mul_cancel₀ hn_ne, one_mul]
  -- `∫ |B_n| dP → 0`.
  have h_integral_B_abs : Filter.Tendsto
      (fun n : ℕ => ∫ ω, |(∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ)| ∂P)
      Filter.atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hΔ_l1
      (Filter.Eventually.of_forall fun n =>
        MeasureTheory.integral_nonneg (fun ω => abs_nonneg _))
      (Filter.eventually_atTop.mpr ⟨1, hB_L1_bound⟩)
  -- Convert `∫ |B_n| → 0` to `eLpNorm B_n 1 → 0`, then to in-measure.
  have hB_eLpNorm : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun ω => (∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ)) 1 P)
      Filter.atTop (𝓝 0) := by
    have h_eLpNorm_eq : ∀ n : ℕ,
        eLpNorm (fun ω => (∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ)) 1 P
          = ENNReal.ofReal
              (∫ ω, |(∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ)| ∂P) := by
      intro n
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
          ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hB_int n)]
      simp only [Real.norm_eq_abs]
    simp_rw [h_eLpNorm_eq]
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h_integral_B_abs
    simpa using! this
  have hB_tendsto : TendstoInMeasure P
      (fun n ω => (∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ))
      Filter.atTop (fun _ => (0 : ℝ)) := by
    refine MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (p := 1) (by norm_num) hB_meas aestronglyMeasurable_const ?_
    refine hB_eLpNorm.congr fun n => ?_
    congr 1
    funext ω; simp
  -- Pointwise decomposition: `∑ W_n(X_i)² = A n ω + B n ω`.
  have h_SAB : ∀ n : ℕ, ∀ ω : Ω,
      ∑ i ∈ Finset.range n, W n (X i ω) ^ 2
        = (∑ i ∈ Finset.range n, g (X i ω) ^ 2) / (n : ℝ)
          + (∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ) := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · simp
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
    rw [← add_div, ← Finset.sum_add_distrib]
    have h_pt : ∀ i, g (X i ω) ^ 2 + Δ n (X i ω) = (n : ℝ) * W n (X i ω) ^ 2 := by
      intro i
      change g (X i ω) ^ 2 + ((n : ℝ) * W n (X i ω) ^ 2 - g (X i ω) ^ 2)
            = (n : ℝ) * W n (X i ω) ^ 2
      ring
    simp_rw [h_pt]
    rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hn_ne]
  -- Combine via ε-split.
  rw [MeasureTheory.tendstoInMeasure_iff_norm]
  intro ε hε
  set δ : ℝ := ε / 2 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hε_le : ε ≤ δ + δ := by rw [hδ_def]; linarith
  have hA_bd := MeasureTheory.tendstoInMeasure_iff_norm.mp hA_tendsto δ hδ_pos
  have hB_bd := MeasureTheory.tendstoInMeasure_iff_norm.mp hB_tendsto δ hδ_pos
  have h_meas_sub : ∀ n : ℕ,
      P {ω | ε ≤ ‖(∑ i ∈ Finset.range n, W n (X i ω) ^ 2) - Pg_sq‖}
        ≤ P {ω | δ ≤ ‖(∑ i ∈ Finset.range n, g (X i ω) ^ 2) / (n : ℝ) - Pg_sq‖}
          + P {ω | δ ≤ ‖(∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ) - (0 : ℝ)‖} := by
    intro n
    have h_inclusion :
        {ω | ε ≤ ‖(∑ i ∈ Finset.range n, W n (X i ω) ^ 2) - Pg_sq‖}
          ⊆ {ω | δ ≤ ‖(∑ i ∈ Finset.range n, g (X i ω) ^ 2) / (n : ℝ) - Pg_sq‖}
            ∪ {ω | δ ≤ ‖(∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ) - (0 : ℝ)‖} := by
      intro ω hω
      rw [Set.mem_setOf_eq, Real.norm_eq_abs, h_SAB n ω] at hω
      by_contra h
      rw [Set.mem_union, not_or] at h
      obtain ⟨hA', hB'⟩ := h
      rw [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at hA'
      rw [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at hB'
      have hdecomp :
          ((∑ i ∈ Finset.range n, g (X i ω) ^ 2) / (n : ℝ)
            + (∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ)) - Pg_sq
          = ((∑ i ∈ Finset.range n, g (X i ω) ^ 2) / (n : ℝ) - Pg_sq)
            + ((∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ) - 0) := by ring
      have htri :
          |((∑ i ∈ Finset.range n, g (X i ω) ^ 2) / (n : ℝ)
              + (∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ)) - Pg_sq|
            ≤ |(∑ i ∈ Finset.range n, g (X i ω) ^ 2) / (n : ℝ) - Pg_sq|
              + |(∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ) - 0| := by
        rw [hdecomp]; exact abs_add_le _ _
      linarith
    exact (measure_mono h_inclusion).trans (measure_union_le _ _)
  have h_sum_tendsto : Filter.Tendsto
      (fun n : ℕ =>
        P {ω | δ ≤ ‖(∑ i ∈ Finset.range n, g (X i ω) ^ 2) / (n : ℝ) - Pg_sq‖}
          + P {ω | δ ≤ ‖(∑ i ∈ Finset.range n, Δ n (X i ω)) / (n : ℝ) - (0 : ℝ)‖})
      Filter.atTop (𝓝 0) := by
    have := hA_bd.add hB_bd
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_sum_tendsto
    (Filter.Eventually.of_forall fun n => zero_le)
    (Filter.Eventually.of_forall h_meas_sub)

/-! ## Step 6b — single-index tail of `|W_{n}|` (analytic core)

The statement `max_{1≤i≤n} |W_{n,i}| →ₚ 0` from van der Vaart is obtained from the
**single-index** analytic core proved here, namely

  `∀ ε > 0, n · P_{θ₀}({|W_n| > ε}) → 0`,

by a trivial union bound. The `max` form itself is `max_abs_W_tendsto_zero_iid`
below (Step 6b-iid), which wraps this core with
`P(max_i |W_{n,i}| > ε) ≤ n · P(|W_{n,1}| > ε)` on the iid sample.

**Proof.** Set `g := ⟨h, ℓ⟩` and threshold `t_n := n ε²/2`. From the pointwise
set inclusion
  `{|W_n|>ε} ⊆ {g² > t_n} ∪ {|n W_n² − g²| > t_n}`
(because `g² ≤ t_n` and `|n W_n² − g²| ≤ t_n` force `n W_n² ≤ 2 t_n = n ε²`),
Markov on each piece gives
  `n · P_{θ₀}({|W_n|>ε}) ≤ (2/ε²) · (∫ g² · 𝟙_{g²>t_n} · p dμ + ∫ |n W_n² − g²| · p dμ)`.
The first integrand is dominated by the `L¹`-function `g² · p`
(via `dqm_fisher_integrable`) and `𝟙_{g²>t_n}(x) → 0` pointwise, so DCT drives it
to `0`. The second integrand → 0 by the hypothesis `h_delta_l1`
(a Step-3 corollary: `E[(√n W_n − g)²] → 0` implies
`E[|n W_n² − g²|] → 0` via Cauchy–Schwarz). -/
omit [SecondCountableTopology Θ] in
lemma max_abs_W_tendsto_zero
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ) (hℓ : Measurable ℓ)
    (hint : Integrable (M.density θ₀) μ)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h : Θ) (h_n : ℕ → Θ) (_hconv : Filter.Tendsto h_n Filter.atTop (𝓝 h))
    (h_delta_integrable : ∀ n : ℕ,
      Integrable (fun x =>
        |(n : ℝ) * (auxStatistic M θ₀ h_n n x) ^ 2 - ⟪h, ℓ x⟫ ^ 2|
          * M.density θ₀ x) μ)
    (h_delta_l1 :
      Filter.Tendsto
        (fun n : ℕ =>
          ∫ x, |(n : ℝ) * (auxStatistic M θ₀ h_n n x) ^ 2 - ⟪h, ℓ x⟫ ^ 2|
                * M.density θ₀ x ∂μ)
        Filter.atTop (𝓝 0)) :
    ∀ ε > 0,
      Filter.Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            ∫ x in {y | ε < |auxStatistic M θ₀ h_n n y|}, M.density θ₀ x ∂μ)
        Filter.atTop (𝓝 0) := by
  intro ε hε
  -- Abbreviations.
  set W : ℕ → 𝓧 → ℝ := auxStatistic M θ₀ h_n with hW_def
  set g : 𝓧 → ℝ := fun x => ⟪h, ℓ x⟫ with hg_def
  set p : 𝓧 → ℝ := M.density θ₀ with hp_def
  have hW_meas : ∀ n : ℕ, Measurable (W n) :=
    fun n => auxStatistic_measurable M θ₀ h_n n
  have hg_meas : Measurable g :=
    ((continuous_const (y := h)).inner continuous_id).measurable.comp hℓ
  have hp_meas : Measurable p := M.density_meas θ₀
  have hp_nn : ∀ x, 0 ≤ p x := M.density_nonneg θ₀
  have hε_sq_pos : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  -- Fisher-type integrability: g² · p ∈ L¹.
  have hg2p_int : Integrable (fun x => g x ^ 2 * p x) μ :=
    dqm_fisher_integrable M μ θ₀ ℓ hint hDQM h (fun t => hint_perturb t h)
  have hg2p_nn : ∀ x, 0 ≤ g x ^ 2 * p x :=
    fun x => mul_nonneg (sq_nonneg _) (hp_nn x)
  -- Measurability of the three level sets.
  have hA_meas : ∀ n : ℕ, MeasurableSet {y | ε < |W n y|} :=
    fun n => measurableSet_lt measurable_const (continuous_abs.measurable.comp (hW_meas n))
  have hBg_meas : ∀ n : ℕ, MeasurableSet {y | (n : ℝ) * ε ^ 2 / 2 < g y ^ 2} :=
    fun n => measurableSet_lt measurable_const (hg_meas.pow_const 2)
  have hBΔ_meas : ∀ n : ℕ, MeasurableSet
      {y | (n : ℝ) * ε ^ 2 / 2 < |(n : ℝ) * (W n y) ^ 2 - g y ^ 2|} := by
    intro n
    refine measurableSet_lt measurable_const ?_
    exact continuous_abs.measurable.comp
      ((((hW_meas n).pow_const 2).const_mul ((n : ℝ))).sub (hg_meas.pow_const 2))
  -- The two convergent tails.
  set A₁ : ℕ → ℝ := fun n =>
    ∫ x in {y | (n : ℝ) * ε ^ 2 / 2 < g y ^ 2}, g x ^ 2 * p x ∂μ with hA₁_def
  set A₂ : ℕ → ℝ := fun n =>
    ∫ x, |(n : ℝ) * (W n x) ^ 2 - g x ^ 2| * p x ∂μ with hA₂_def
  -- A₁ → 0 by DCT on the `g²`-tail (via `tendsto_setIntegral_tail_of_integrable`).
  have hA₁_tendsto : Filter.Tendsto A₁ Filter.atTop (𝓝 0) := by
    have h_threshold_tendsto :
        Filter.Tendsto (fun n : ℕ => (n : ℝ) * ε ^ 2 / 2) Filter.atTop Filter.atTop := by
      have h_nat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop
      have h_scaled :
          Filter.Tendsto (fun n : ℕ => (n : ℝ) * (ε ^ 2 / 2)) Filter.atTop Filter.atTop :=
        h_nat.atTop_mul_const (by positivity)
      simpa [mul_div_assoc] using h_scaled
    exact ForMathlib.tendsto_setIntegral_tail_of_integrable
      hg2p_int (hg_meas.pow_const 2) h_threshold_tendsto
  -- A₂ → 0 by hypothesis.
  have hA₂_tendsto : Filter.Tendsto A₂ Filter.atTop (𝓝 0) := h_delta_l1
  -- The combined upper bound tends to zero.
  have h_upper_tendsto :
      Filter.Tendsto (fun n : ℕ => (2 / ε ^ 2) * (A₁ n + A₂ n))
        Filter.atTop (𝓝 0) := by
    have h_sum : Filter.Tendsto (fun n : ℕ => A₁ n + A₂ n) Filter.atTop (𝓝 0) := by
      simpa using hA₁_tendsto.add hA₂_tendsto
    have := h_sum.const_mul (2 / ε ^ 2)
    simpa using this
  -- Step B+C: set-integral chain (eventually, for `n ≥ 1`) assembling
  -- set inclusion + union-subadditivity + Markov on each piece.
  have h_le : ∀ᶠ (n : ℕ) in Filter.atTop,
      (n : ℝ) * ∫ x in {y | ε < |W n y|}, p x ∂μ ≤ (2 / ε ^ 2) * (A₁ n + A₂ n) := by
    refine Filter.eventually_atTop.mpr ⟨1, fun (n : ℕ) (hn : 1 ≤ n) => ?_⟩
    have hn_nat_pos : 0 < n := hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_nat_pos
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hε2_ne : ε ^ 2 ≠ 0 := ne_of_gt hε_sq_pos
    have h_t_pos : (0 : ℝ) < (n : ℝ) * ε ^ 2 / 2 := by positivity
    -- Set inclusion: `{|W n|>ε} ⊆ Bg ∪ BΔ`.
    have h_incl : {y | ε < |W n y|} ⊆
        {y | (n : ℝ) * ε ^ 2 / 2 < g y ^ 2} ∪
        {y | (n : ℝ) * ε ^ 2 / 2 < |(n : ℝ) * (W n y) ^ 2 - g y ^ 2|} := by
      intro y hy
      rw [Set.mem_union]
      by_contra h_not
      push Not at h_not
      obtain ⟨h_notg, h_notΔ⟩ := h_not
      simp only [Set.mem_setOf_eq, not_lt] at h_notg h_notΔ
      have h3 : (n : ℝ) * (W n y) ^ 2 - g y ^ 2 ≤ (n : ℝ) * ε ^ 2 / 2 :=
        (le_abs_self _).trans h_notΔ
      have h4 : (n : ℝ) * (W n y) ^ 2 ≤ (n : ℝ) * ε ^ 2 := by linarith
      have h5 : (W n y) ^ 2 ≤ ε ^ 2 := le_of_mul_le_mul_left h4 hn_pos
      have h6 : |W n y| ≤ ε := abs_le_of_sq_le_sq h5 hε.le
      exact (not_lt.mpr h6) hy
    -- Step 1 (monotonicity): `∫_A p ≤ ∫_{Bg ∪ BΔ} p`.
    have h_step1 :
        ∫ x in {y | ε < |W n y|}, p x ∂μ ≤
          ∫ x in {y | (n : ℝ) * ε ^ 2 / 2 < g y ^ 2} ∪
                {y | (n : ℝ) * ε ^ 2 / 2 < |(n : ℝ) * (W n y) ^ 2 - g y ^ 2|},
            p x ∂μ := by
      refine MeasureTheory.setIntegral_mono_set hint.integrableOn
        (Filter.Eventually.of_forall (fun x => hp_nn x))
        (Filter.Eventually.of_forall h_incl)
    -- Step 2 (union-subadditivity): `∫_{Bg ∪ BΔ} p ≤ ∫_{Bg} p + ∫_{BΔ} p`.
    have h_step2 :=
      ForMathlib.setIntegral_union_le_add_of_nonneg
        (hBg_meas n) (hBΔ_meas n) hp_nn hint.integrableOn hint.integrableOn
    -- Step 3a (Markov on Bg): `∫_{Bg} p ≤ t⁻¹ · A₁`.
    have h_mk_Bg :=
      ForMathlib.setIntegral_le_const_mul_of_threshold
        h_t_pos (hBg_meas n) (fun _ hx => hx)
        (fun x _ => hp_nn x) hint.integrableOn hg2p_int.integrableOn
    -- Step 3b (Markov on BΔ, then extend domain): `∫_{BΔ} p ≤ t⁻¹ · A₂`.
    have h_mk_BΔ :
        ∫ x in {y | (n : ℝ) * ε ^ 2 / 2 < |(n : ℝ) * (W n y) ^ 2 - g y ^ 2|}, p x ∂μ ≤
          ((n : ℝ) * ε ^ 2 / 2)⁻¹ * A₂ n := by
      have h_loc :=
        ForMathlib.setIntegral_le_const_mul_of_threshold
          h_t_pos (hBΔ_meas n) (fun _ hx => hx)
          (fun x _ => hp_nn x) hint.integrableOn
          (h_delta_integrable n).integrableOn
      have h_ext :
          ∫ x in {y | (n : ℝ) * ε ^ 2 / 2 < |(n : ℝ) * (W n y) ^ 2 - g y ^ 2|},
            |(n : ℝ) * (W n x) ^ 2 - g x ^ 2| * p x ∂μ ≤ A₂ n :=
        MeasureTheory.setIntegral_le_integral (h_delta_integrable n)
          (Filter.Eventually.of_forall
            (fun x => mul_nonneg (abs_nonneg _) (hp_nn x)))
      exact h_loc.trans
        (mul_le_mul_of_nonneg_left h_ext (inv_pos.mpr h_t_pos).le)
    -- Combine + multiply by `n` + simplify coefficient `n / (nε²/2) = 2/ε²`.
    have h_combined :
        ∫ x in {y | ε < |W n y|}, p x ∂μ ≤
          ((n : ℝ) * ε ^ 2 / 2)⁻¹ * A₁ n + ((n : ℝ) * ε ^ 2 / 2)⁻¹ * A₂ n :=
      h_step1.trans (h_step2.trans (add_le_add h_mk_Bg h_mk_BΔ))
    have h_coef_eq :
        (n : ℝ) * (((n : ℝ) * ε ^ 2 / 2)⁻¹ * A₁ n
                      + ((n : ℝ) * ε ^ 2 / 2)⁻¹ * A₂ n)
          = (2 / ε ^ 2) * (A₁ n + A₂ n) := by
      field_simp
    calc (n : ℝ) * ∫ x in {y | ε < |W n y|}, p x ∂μ
        ≤ (n : ℝ) * (((n : ℝ) * ε ^ 2 / 2)⁻¹ * A₁ n
                        + ((n : ℝ) * ε ^ 2 / 2)⁻¹ * A₂ n) :=
          mul_le_mul_of_nonneg_left h_combined (Nat.cast_nonneg n)
      _ = (2 / ε ^ 2) * (A₁ n + A₂ n) := h_coef_eq
  -- Squeeze to conclude.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_upper_tendsto
    (Filter.Eventually.of_forall fun n => by
      refine mul_nonneg (Nat.cast_nonneg n) ?_
      exact MeasureTheory.setIntegral_nonneg (hA_meas n) (fun x _ => hp_nn x))
    h_le

/-! ## Step 6b — `max_{i<n} |W_{n,i}| →ₚ 0` (iid union-bound upgrade)

Promotes the single-index analytic core `max_abs_W_tendsto_zero` to the actual
statement `max_{1≤i≤n} |W_{n,i}(ω)| →ₚ 0` used by van der Vaart. On the same
iid setup as `sum_W_decomp`/`sum_W_sq_tendsto_to_Pg_sq`, we bound
`P(⋃_{i<n} {|W_n(X_i)| > ε}) ≤ n · ν({|W_n|>ε})` (union bound + `IdentDistrib`),
then identify `n · ν(…) = ENNReal.ofReal(n · ∫_{|W_n|>ε} p dμ) → 0` via the
single-index lemma. -/
lemma max_abs_W_tendsto_zero_iid
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ) (hℓ : Measurable ℓ)
    (hint : Integrable (M.density θ₀) μ)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h_fisher_cont :
      Filter.Tendsto (fun v : Θ => ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
        (𝓝 0) (𝓝 0))
    (h : Θ) (h_n : ℕ → Θ) (hconv : Filter.Tendsto h_n Filter.atTop (𝓝 h))
    (X : ℕ → Ω → 𝓧) (hX_meas : ∀ i, Measurable (X i))
    (_hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) P)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P P)
    (hlaw : Measure.map (X 0) P
              = μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) :
    ∀ ε > 0, Filter.Tendsto
      (fun n : ℕ => P (⋃ i ∈ Finset.range n,
                        {ω | ε < |auxStatistic M θ₀ h_n n (X i ω)|}))
      Filter.atTop (𝓝 0) := by
  intro ε hε
  set W : ℕ → 𝓧 → ℝ := auxStatistic M θ₀ h_n with hW_def
  set p : 𝓧 → ℝ := M.density θ₀ with hp_def
  set ν : Measure 𝓧 := μ.withDensity fun x => ENNReal.ofReal (p x) with hν_def
  have hp_meas : Measurable p := M.density_meas θ₀
  have hp_nn : ∀ x, 0 ≤ p x := M.density_nonneg θ₀
  have hW_meas : ∀ n, Measurable (W n) := fun n => auxStatistic_measurable M θ₀ h_n n
  have hA_meas : ∀ n : ℕ, MeasurableSet {y | ε < |W n y|} := fun n =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hW_meas n))
  -- Each `X i` has law `ν`.
  have h_map : ∀ i, Measure.map (X i) P = ν := fun i => by
    rw [(hident i).map_eq, hlaw]
  -- Feed `max_abs_W_tendsto_zero` with its two Δ-hypotheses (Step-3 L¹ corollary).
  have h_delta_int := fun n =>
    delta_l1_integrable M μ θ₀ ℓ hℓ hint hint_perturb hDQM h h_n n
  have h_delta_l1 :=
    delta_l1_tendsto M μ θ₀ ℓ hℓ hint hint_perturb hDQM h_fisher_cont h h_n hconv
  have h_single :=
    max_abs_W_tendsto_zero M μ θ₀ ℓ hℓ hint hint_perturb hDQM h h_n hconv
      h_delta_int h_delta_l1 ε hε
  -- Lift the single-index tail to `ℝ≥0∞`.
  have h_single_ennreal :
      Filter.Tendsto (fun n : ℕ =>
          ENNReal.ofReal ((n : ℝ) * ∫ x in {y | ε < |W n y|}, p x ∂μ))
        Filter.atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp h_single
    rw [ENNReal.ofReal_zero] at h
    exact h
  -- Upper bound: `P(⋃_i …) ≤ ENNReal.ofReal (n · ∫_{…} p dμ)`.
  have h_bound : ∀ n : ℕ,
      P (⋃ i ∈ Finset.range n, {ω | ε < |W n (X i ω)|})
        ≤ ENNReal.ofReal ((n : ℝ) * ∫ x in {y | ε < |W n y|}, p x ∂μ) := by
    intro n
    -- Union bound.
    have h_union :
        P (⋃ i ∈ Finset.range n, {ω | ε < |W n (X i ω)|})
          ≤ ∑ i ∈ Finset.range n, P {ω | ε < |W n (X i ω)|} :=
      measure_biUnion_finset_le _ _
    -- Each `P{|W_n(X_i)| > ε}` equals `ν{|W_n| > ε}`.
    have h_each : ∀ i, P {ω | ε < |W n (X i ω)|} = ν {y | ε < |W n y|} := by
      intro i
      have hpre : {ω | ε < |W n (X i ω)|} = (X i)⁻¹' {y | ε < |W n y|} := rfl
      rw [hpre, ← Measure.map_apply (hX_meas i) (hA_meas n), h_map i]
    -- Sum over `range n` collapses to `n • ν(A_n)`.
    have h_sum_eq :
        ∑ i ∈ Finset.range n, P {ω | ε < |W n (X i ω)|}
          = (n : ℕ) • ν {y | ε < |W n y|} := by
      rw [Finset.sum_congr rfl (fun i _ => h_each i),
          Finset.sum_const, Finset.card_range]
    -- `ν(A_n) = ∫⁻_{A_n} ENNReal.ofReal p dμ`.
    have hν_expr :
        ν {y | ε < |W n y|} = ∫⁻ x in {y | ε < |W n y|}, ENNReal.ofReal (p x) ∂μ := by
      rw [hν_def, MeasureTheory.withDensity_apply _ (hA_meas n)]
    -- `∫⁻_{A_n} ENNReal.ofReal p dμ = ENNReal.ofReal (∫_{A_n} p dμ)`.
    have h_of_real :
        ∫⁻ x in {y | ε < |W n y|}, ENNReal.ofReal (p x) ∂μ
          = ENNReal.ofReal (∫ x in {y | ε < |W n y|}, p x ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hint.integrableOn
          (MeasureTheory.ae_of_all _ fun x => hp_nn x)).symm
    -- `n • ENNReal.ofReal x = ENNReal.ofReal (n · x)` for `x ≥ 0`.
    have h_nsmul :
        (n : ℕ) • ENNReal.ofReal (∫ x in {y | ε < |W n y|}, p x ∂μ)
          = ENNReal.ofReal ((n : ℝ) * ∫ x in {y | ε < |W n y|}, p x ∂μ) := by
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    calc P (⋃ i ∈ Finset.range n, {ω | ε < |W n (X i ω)|})
        ≤ ∑ i ∈ Finset.range n, P {ω | ε < |W n (X i ω)|} := h_union
      _ = (n : ℕ) • ν {y | ε < |W n y|} := h_sum_eq
      _ = (n : ℕ) • ENNReal.ofReal (∫ x in {y | ε < |W n y|}, p x ∂μ) := by
          rw [hν_expr, h_of_real]
      _ = ENNReal.ofReal ((n : ℝ) * ∫ x in {y | ε < |W n y|}, p x ∂μ) := h_nsmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_single_ennreal
    (Filter.Eventually.of_forall fun _ => zero_le)
    (Filter.Eventually.of_forall h_bound)

/-! ## Step 5 corollary — pointwise Taylor identity for the log density ratio

Uses `ForMathlib.log_one_add_eq_taylor` with `x = √(p_n/p) − 1 = W_{n,i}/2`:
`log (p_n/p) = W − W²/4 + (W²/2) · R(W)` where `R = ForMathlib.logTaylorRemainder`.

**No positivity hypothesis is required.** When `p_n = 0` (or `p = 0`), Lean's
convention `log 0 = 0` combined with the specific shape of `logTaylorRemainder`
makes the identity hold at the boundary: `W = -2`, and `R(-2) = 3/2`, so
`W − W²/4 + (W²/2) · R(-2) = -2 − 1 + 3 = 0 = log 0`. This eliminates the
`hpn_pos_ν` regularity hypothesis from `LAN_expansion_iii` and restores vdV's
literal statement (only DQM + structural regularity needed). -/
omit [MeasurableSpace Θ] [OpensMeasurableSpace Θ] [SecondCountableTopology Θ] in
lemma log_density_ratio_taylor
    (M : ParametricFamily 𝓧 Θ) (θ₀ : Θ) (h_n : ℕ → Θ) (n : ℕ) (x : 𝓧) :
    Real.log (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x / M.density θ₀ x)
      = auxStatistic M θ₀ h_n n x
        - auxStatistic M θ₀ h_n n x ^ 2 / 4
        + auxStatistic M θ₀ h_n n x ^ 2 / 2
          * ForMathlib.logTaylorRemainder (auxStatistic M θ₀ h_n n x) := by
  exact M.log_density_ratio_taylor θ₀ (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x

/-! ## LAN expansion clause (iii) — the full assembly

On the iid setup as in `sum_W_decomp`, with ae-positive densities `p` and `p_n`,
the log-likelihood ratio admits the expansion

  `∑_{i<n} log (p_n(X_i) / p(X_i))
    = (1/√n) ∑_{i<n} ⟨h, ℓ(X_i)⟩ − (1/2) ⟨h, I_{θ₀} h⟩ + o_P(1)`.

Proof: apply the Taylor identity to each summand (ae under `P`, via positivity
of `p` and `p_n`) to get `∑ log = ∑ W − (1/4) ∑ W² + (1/2) ∑ W² R(W)`. Combining
with Steps 4, 6a, 6b-iid:

* Step 4 gives `∑W − (1/√n)∑g →_P −(1/4)·I`.
* Step 6a gives `∑W² →_P I`.
* Step 6b-iid + continuity of `R` at 0 + Step 6a's boundedness gives
  `∑ W² R(W) →_P 0` (ε-δ argument).

Target = (∑W − (1/√n)∑g + (1/4)I) + (−(1/4)∑W² + (1/4)I) + (1/2)∑W²R(W), each
bracket →_P 0. -/
theorem LAN_expansion_iii
    {k : ℕ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (h_one : ∫ x, M.density θ₀ x ∂μ = 1)
    (hint : Integrable (M.density θ₀) μ)
    (h_one_perturb : ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin k),
      ∫ x, M.density (θ₀ + t • u) x ∂μ = 1)
    (hint_perturb : ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin k),
      Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h : EuclideanSpace ℝ (Fin k)) (h_n : ℕ → EuclideanSpace ℝ (Fin k))
    (hconv : Filter.Tendsto h_n Filter.atTop (𝓝 h))
    (X : ℕ → Ω → 𝓧) (hX_meas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) P)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P P)
    (hlaw : Measure.map (X 0) P
              = μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) :
    TendstoInMeasure P
      (fun n ω =>
        (∑ i ∈ Finset.range n,
          Real.log (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) (X i ω)
                    / M.density θ₀ (X i ω)))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, ⟪h, ℓ (X i ω)⟫
        + (1/2 : ℝ) * fisherInformation M μ θ₀ ℓ h h)
      Filter.atTop (fun _ => (0 : ℝ)) := by
  set g : 𝓧 → ℝ := fun x => ⟪h, ℓ x⟫ with hg_def
  set W : ℕ → 𝓧 → ℝ := auxStatistic M θ₀ h_n with hW_def
  set I : ℝ := fisherInformation M μ θ₀ ℓ h h with hI_def
  set R : ℝ → ℝ := ForMathlib.logTaylorRemainder with hR_def
  have hp_nn : ∀ x, 0 ≤ M.density θ₀ x := M.density_nonneg θ₀
  -- Fisher quadratic-form continuity at zero follows from DQM via `dqm_fisher_cont`.
  have h_fisher_cont :
      Filter.Tendsto
        (fun v : EuclideanSpace ℝ (Fin k) =>
          ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
        (𝓝 0) (𝓝 0) :=
    dqm_fisher_cont M μ θ₀ ℓ hint hDQM hint_perturb
  -- Fisher information is non-negative.
  have hI_nn : 0 ≤ I := by
    refine MeasureTheory.integral_nonneg fun x => ?_
    change 0 ≤ (⟪h, ℓ x⟫ * ⟪h, ℓ x⟫) * M.density θ₀ x
    exact mul_nonneg (mul_self_nonneg _) (hp_nn x)
  -- Step 4, 6a, 6b-iid outputs.
  have hA_tendsto :=
    sum_W_decomp P M μ θ₀ ℓ hℓ h_one hint h_one_perturb hint_perturb
      hDQM h_fisher_cont h h_n hconv X hX_meas hindep hident hlaw
  have hB_tendsto :=
    sum_W_sq_tendsto_to_Pg_sq P M μ θ₀ ℓ hℓ hint hint_perturb hDQM
      h_fisher_cont h h_n hconv X hX_meas hindep hident hlaw
  have hMax_tendsto :=
    max_abs_W_tendsto_zero_iid P M μ θ₀ ℓ hℓ hint hint_perturb hDQM
      h_fisher_cont h h_n hconv X hX_meas hindep hident hlaw
  -- Part 1: `(∑W - (1/√n)∑g) + (1/4)·I  →_P  0`.
  have h_part1 : TendstoInMeasure P
      (fun n ω =>
        ((∑ i ∈ Finset.range n, W n (X i ω))
         - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω))
        + (1/4 : ℝ) * I)
      Filter.atTop (fun _ => (0 : ℝ)) := by
    have h_sum := AsymptoticStatistics.tendstoInMeasure_add
      hA_tendsto (AsymptoticStatistics.tendstoInMeasure_const ((1/4 : ℝ) * I))
    have h_lim : -(1/4 : ℝ) * I + (1/4 : ℝ) * I = 0 := by ring
    rw [h_lim] at h_sum
    exact h_sum
  -- Part 2: `-(1/4)·∑W² + (1/4)·I  →_P  0`.
  have h_part2 : TendstoInMeasure P
      (fun n ω =>
        -(1/4 : ℝ) * (∑ i ∈ Finset.range n, W n (X i ω) ^ 2) + (1/4 : ℝ) * I)
      Filter.atTop (fun _ => (0 : ℝ)) := by
    have hB_scaled :=
      AsymptoticStatistics.tendstoInMeasure_const_mul (-(1/4 : ℝ)) hB_tendsto
    have h_sum := AsymptoticStatistics.tendstoInMeasure_add
      hB_scaled (AsymptoticStatistics.tendstoInMeasure_const ((1/4 : ℝ) * I))
    have h_lim : -(1/4 : ℝ) * I + (1/4 : ℝ) * I = 0 := by ring
    rw [h_lim] at h_sum
    exact h_sum
  -- Part 3: `(1/2) · ∑ W²(X_i) R(W(X_i)) →_P 0`.
  have h_part3 : TendstoInMeasure P
      (fun n ω => (1/2 : ℝ) *
        ∑ i ∈ Finset.range n, W n (X i ω) ^ 2 * R (W n (X i ω)))
      Filter.atTop (fun _ => (0 : ℝ)) := by
    -- It suffices to show `∑ W² R(W) →_P 0`, then scale by (1/2).
    suffices hC : TendstoInMeasure P
        (fun n ω => ∑ i ∈ Finset.range n, W n (X i ω) ^ 2 * R (W n (X i ω)))
        Filter.atTop (fun _ => (0 : ℝ)) by
      have := AsymptoticStatistics.tendstoInMeasure_const_mul (1/2 : ℝ) hC
      simpa using this
    -- ε-δ argument using B_n (bounded) and Max (→ 0) + continuity of R.
    rw [MeasureTheory.tendstoInMeasure_iff_norm]
    intro ε hε
    set Mbd : ℝ := I + 1 with hMbd_def
    have hMbd_pos : 0 < Mbd := by linarith
    set ε' : ℝ := ε / (2 * Mbd) with hε'_def
    have hε'_pos : 0 < ε' := div_pos hε (by positivity)
    -- Continuity of `R` at 0 → γ witness.
    obtain ⟨γ, hγ_pos, hγ⟩ :=
      Metric.tendsto_nhds_nhds.mp ForMathlib.logTaylorRemainder_tendsto_zero ε' hε'_pos
    have hγ2_pos : 0 < γ / 2 := by positivity
    -- Step 6a: eventually `P{|B_n - I| ≥ 1} < δ/2`.
    have hB_bd :=
      MeasureTheory.tendstoInMeasure_iff_norm.mp hB_tendsto 1 one_pos
    -- Step 6b-iid: `P(⋃_i {|W(X_i)| > γ/2}) → 0`.
    have hMax_bd := hMax_tendsto (γ / 2) hγ2_pos
    -- Pointwise bound: inclusion of level sets.
    have h_incl : ∀ n : ℕ,
        {ω | ε ≤ ‖(∑ i ∈ Finset.range n, W n (X i ω) ^ 2 * R (W n (X i ω))) - 0‖}
          ⊆ (⋃ i ∈ Finset.range n, {ω | γ / 2 < |W n (X i ω)|})
            ∪ {ω | 1 ≤ ‖(∑ i ∈ Finset.range n, W n (X i ω) ^ 2) - I‖} := by
      intro n ω hω
      rw [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω
      by_contra h
      rw [Set.mem_union, not_or] at h
      obtain ⟨h_not_max, h_not_B⟩ := h
      -- `h_not_max` : `¬ ω ∈ ⋃ i, {|W(X_i ω)| > γ/2}`, so `∀ i < n, |W(X_i ω)| ≤ γ/2`.
      have h_W_le : ∀ i ∈ Finset.range n, |W n (X i ω)| ≤ γ / 2 := by
        intro i hi
        by_contra h_gt
        push Not at h_gt
        exact h_not_max (Set.mem_biUnion hi h_gt)
      -- `h_not_B` gives `|B_n ω - I| < 1`, so `B_n ω < Mbd`.
      rw [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at h_not_B
      have hB_sum_nn : 0 ≤ ∑ i ∈ Finset.range n, W n (X i ω) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have hB_lt : (∑ i ∈ Finset.range n, W n (X i ω) ^ 2) < Mbd := by
        have : (∑ i ∈ Finset.range n, W n (X i ω) ^ 2) - I < 1 := by
          have := abs_lt.mp h_not_B
          linarith [this.2]
        linarith
      -- For each i, `|R(W(X_i ω))| < ε'`.
      have h_R_bd : ∀ i ∈ Finset.range n, |R (W n (X i ω))| < ε' := by
        intro i hi
        have h_W_lt : |W n (X i ω)| < γ := lt_of_le_of_lt (h_W_le i hi) (by linarith)
        have h_dist : dist (W n (X i ω)) (0 : ℝ) < γ := by
          rw [dist_zero_right, Real.norm_eq_abs]; exact h_W_lt
        have : dist (R (W n (X i ω))) (0 : ℝ) < ε' := hγ h_dist
        rw [dist_zero_right, Real.norm_eq_abs] at this
        exact this
      -- Pointwise summand bound: `|W²·R(W)| ≤ W² · ε'`.
      have h_summand : ∀ i ∈ Finset.range n,
          |W n (X i ω) ^ 2 * R (W n (X i ω))| ≤ W n (X i ω) ^ 2 * ε' := by
        intro i hi
        rw [abs_mul]
        have h1 : |W n (X i ω) ^ 2| = W n (X i ω) ^ 2 := abs_of_nonneg (sq_nonneg _)
        rw [h1]
        exact mul_le_mul_of_nonneg_left (h_R_bd i hi).le (sq_nonneg _)
      have h_abs_sum : |∑ i ∈ Finset.range n, W n (X i ω) ^ 2 * R (W n (X i ω))|
          ≤ ∑ i ∈ Finset.range n, |W n (X i ω) ^ 2 * R (W n (X i ω))| :=
        Finset.abs_sum_le_sum_abs _ _
      have h_bound_total :
          ∑ i ∈ Finset.range n, |W n (X i ω) ^ 2 * R (W n (X i ω))|
            ≤ ε' * ∑ i ∈ Finset.range n, W n (X i ω) ^ 2 := by
        calc ∑ i ∈ Finset.range n, |W n (X i ω) ^ 2 * R (W n (X i ω))|
            ≤ ∑ i ∈ Finset.range n, W n (X i ω) ^ 2 * ε' :=
              Finset.sum_le_sum h_summand
          _ = ε' * ∑ i ∈ Finset.range n, W n (X i ω) ^ 2 := by
              rw [← Finset.sum_mul, mul_comm]
      -- Combine: `|C_n| ≤ ε' · B_n < ε' · Mbd = ε/2 < ε`. Contradicts `hω`.
      have h_final :
          |∑ i ∈ Finset.range n, W n (X i ω) ^ 2 * R (W n (X i ω))| < ε := by
        have h1 : ε' * Mbd = ε / 2 := by
          rw [hε'_def]; field_simp
        calc |∑ i ∈ Finset.range n, W n (X i ω) ^ 2 * R (W n (X i ω))|
            ≤ ∑ i ∈ Finset.range n, |W n (X i ω) ^ 2 * R (W n (X i ω))| := h_abs_sum
          _ ≤ ε' * ∑ i ∈ Finset.range n, W n (X i ω) ^ 2 := h_bound_total
          _ < ε' * Mbd := mul_lt_mul_of_pos_left hB_lt hε'_pos
          _ = ε / 2 := h1
          _ < ε := by linarith
      exact absurd hω (not_le.mpr h_final)
    have h_sum_tendsto :
        Filter.Tendsto
          (fun n : ℕ =>
            P (⋃ i ∈ Finset.range n, {ω | γ / 2 < |W n (X i ω)|})
              + P {ω | 1 ≤ ‖(∑ i ∈ Finset.range n, W n (X i ω) ^ 2) - I‖})
          Filter.atTop (𝓝 0) := by
      have := hMax_bd.add hB_bd
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds h_sum_tendsto
      (Filter.Eventually.of_forall fun _ => zero_le)
      (Filter.Eventually.of_forall fun n => ?_)
    calc P {ω | ε ≤ ‖(∑ i ∈ Finset.range n, W n (X i ω) ^ 2 * R (W n (X i ω))) - 0‖}
        ≤ P ((⋃ i ∈ Finset.range n, {ω | γ / 2 < |W n (X i ω)|})
              ∪ {ω | 1 ≤ ‖(∑ i ∈ Finset.range n, W n (X i ω) ^ 2) - I‖}) :=
          measure_mono (h_incl n)
      _ ≤ P (⋃ i ∈ Finset.range n, {ω | γ / 2 < |W n (X i ω)|})
          + P {ω | 1 ≤ ‖(∑ i ∈ Finset.range n, W n (X i ω) ^ 2) - I‖} :=
          measure_union_le _ _
  -- Combine parts via `tendstoInMeasure_add`.
  have h_combined : TendstoInMeasure P
      (fun n ω =>
        (((∑ i ∈ Finset.range n, W n (X i ω))
          - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω))
          + (1/4 : ℝ) * I)
        + (-(1/4 : ℝ) * (∑ i ∈ Finset.range n, W n (X i ω) ^ 2) + (1/4 : ℝ) * I)
        + ((1/2 : ℝ) *
            ∑ i ∈ Finset.range n, W n (X i ω) ^ 2 * R (W n (X i ω))))
      Filter.atTop (fun _ => (0 : ℝ)) := by
    have h12 := AsymptoticStatistics.tendstoInMeasure_add h_part1 h_part2
    have h123 := AsymptoticStatistics.tendstoInMeasure_add h12 h_part3
    have h_zero : (0 : ℝ) + 0 + 0 = 0 := by ring
    rw [show (0 : ℝ) = (0 : ℝ) + 0 + 0 from by ring]
    exact h123
  -- Identify the target using the pointwise Taylor identity, which holds without
  -- a separate positivity assumption.
  refine h_combined.congr (fun n => ?_) (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards with ω
  -- Pointwise Taylor identity for each summand.
  have h_taylor_each : ∀ i ∈ Finset.range n,
      Real.log (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) (X i ω) / M.density θ₀ (X i ω))
        = W n (X i ω)
          - W n (X i ω) ^ 2 / 4
          + W n (X i ω) ^ 2 / 2 * R (W n (X i ω)) :=
    fun i _ => log_density_ratio_taylor M θ₀ h_n n (X i ω)
  rw [Finset.sum_congr rfl h_taylor_each]
  -- Algebraic manipulation: split sum and rearrange.
  have h_split : ∑ i ∈ Finset.range n,
        (W n (X i ω) - W n (X i ω) ^ 2 / 4
          + W n (X i ω) ^ 2 / 2 * R (W n (X i ω)))
      = (∑ i ∈ Finset.range n, W n (X i ω))
        - (1/4 : ℝ) * (∑ i ∈ Finset.range n, W n (X i ω) ^ 2)
        + (1/2 : ℝ) * (∑ i ∈ Finset.range n,
              W n (X i ω) ^ 2 * R (W n (X i ω))) := by
    rw [Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h_split]
  ring

/-! ## Main theorem — model-level conclusions

The model-level content of Theorem 7.2 — `P_θ ℓ = 0` and Fisher-information
finiteness — on the parametric family itself, free of any sample-space data.
The iid-sample conclusion (clause (iii), the LAN expansion proper) is
`LAN_expansion_iii` above, on a separately-carried probability space `(Ω, P)`
with `X : ℕ → Ω → 𝓧` iid under `P_{θ₀}`. -/
theorem LAN_expansion_score_fisher_part
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ) (hℓ : Measurable ℓ)
    (h_one : ∫ x, M.density θ₀ x ∂μ = 1)
    (hint : Integrable (M.density θ₀) μ)
    (h_one_perturb : ∀ t : ℝ, ∀ u : Θ, ∫ x, M.density (θ₀ + t • u) x ∂μ = 1)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) :
    -- (i) score has zero mean (Step 1)
    (∀ u : Θ, ∫ x, ⟪u, ℓ x⟫ * M.density θ₀ x ∂μ = 0) ∧
    -- (ii) Fisher information is well-defined for every direction `u`,
    --      i.e. `⟨u, ℓ⟩² · p_{θ₀}` is integrable. Derived from DQM.
    (∀ u : Θ, Integrable (fun x => ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) μ) := by
  refine ⟨?_, ?_⟩
  · -- (i) Step 1.
    intro u
    exact score_mean_zero M μ θ₀ ℓ hℓ h_one hint h_one_perturb hint_perturb hDQM u
  · -- (ii) Fisher information finite: derived from DQM via `dqm_fisher_integrable`.
    intro u
    exact dqm_fisher_integrable M μ θ₀ ℓ hint hDQM u (fun t => hint_perturb t u)

/-! ## vdV Theorem 7.2 (full form) — (i) ∧ (ii) ∧ (iii)

van der Vaart, *Asymptotic Statistics*, Theorem 7.2 in full. Conclusions:

(i)   Score has zero mean under `P_{θ₀}`: `∀ u, ∫ ⟨u, ℓ⟩ · p_{θ₀} dμ = 0`.
(ii)  Fisher information is well-defined: `⟨u, ℓ⟩² · p_{θ₀}` is integrable for every `u`.
(iii) LAN expansion: for every converging sequence `h_n → h`,

  `∑_{i<n} log (p_{θ₀ + h_n/√n}(X_i) / p_{θ₀}(X_i))
     = (1/√n) ∑_{i<n} ⟨h, ℓ(X_i)⟩  − (1/2) ⟨h, I_{θ₀} h⟩  + o_{P_{θ₀}}(1)`.

Specialised to `Θ = EuclideanSpace ℝ (Fin k)` to match vdV's finite-dimensional
setting; `dqm_fisher_cont` supplies continuity of Fisher information.

**Only vdV-structural hypotheses remain**:

* `IsPDFOf M μ` — packages "`p_θ` is a μ-density that normalises and is integrable
  for every `θ`". vdV tacitly assumes this by writing `p_θ` at all.
* `hDQM` — differentiability in quadratic mean at `θ₀`.
* `hconv : h_n → h` — the parameter perturbation sequence converges.
* iid sample setup (`X`, `hX_meas`, `hindep`, `hident`, `hlaw`).

Fisher continuity follows from DQM via `dqm_fisher_cont`. The Taylor identity
in `log_density_ratio_taylor` requires no positivity assumption because it
holds universally under Lean's `log 0 = 0` convention. -/
theorem LAN_expansion
    {k : ℕ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score representative.
    (hℓ : Measurable ℓ)
    -- USER-INPUT: normalized density family and differentiability in quadratic
    -- mean at `θ₀`; vdV Theorem 7.2.
    (hPDF : IsPDFOf M μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h : EuclideanSpace ℝ (Fin k)) (h_n : ℕ → EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: convergence of the local parameter directions; vdV Theorem 7.2.
    (hconv : Filter.Tendsto h_n Filter.atTop (𝓝 h))
    (X : ℕ → Ω → 𝓧)
    -- LEAN-ONLY: measurability of each sample coordinate.
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: iid observations from the base law `P_{θ₀}`; vdV Theorem 7.2.
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) P)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P P)
    (hlaw : Measure.map (X 0) P
              = μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) :
    -- (i) score has zero mean under `P_{θ₀}`
    (∀ u : EuclideanSpace ℝ (Fin k), ∫ x, ⟪u, ℓ x⟫ * M.density θ₀ x ∂μ = 0) ∧
    -- (ii) Fisher information is finite for every direction `u`
    (∀ u : EuclideanSpace ℝ (Fin k),
      Integrable (fun x => ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) μ) ∧
    -- (iii) LAN expansion
    TendstoInMeasure P
      (fun n ω =>
        (∑ i ∈ Finset.range n,
          Real.log (M.density (θ₀ + (Real.sqrt n)⁻¹ • h_n n) (X i ω)
                    / M.density θ₀ (X i ω)))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, ⟪h, ℓ (X i ω)⟫
        + (1/2 : ℝ) * fisherInformation M μ θ₀ ℓ h h)
      Filter.atTop (fun _ => (0 : ℝ)) := by
  have h_one : ∫ x, M.density θ₀ x ∂μ = 1 := hPDF.density_integral_eq_one θ₀
  have hint : Integrable (M.density θ₀) μ := hPDF.density_integrable θ₀
  have h_one_perturb : ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin k),
      ∫ x, M.density (θ₀ + t • u) x ∂μ = 1 :=
    fun t u => hPDF.density_integral_eq_one (θ₀ + t • u)
  have hint_perturb : ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin k),
      Integrable (M.density (θ₀ + t • u)) μ :=
    fun t u => hPDF.density_integrable (θ₀ + t • u)
  refine ⟨?_, ?_, ?_⟩
  · intro u
    exact score_mean_zero M μ θ₀ ℓ hℓ h_one hint h_one_perturb hint_perturb hDQM u
  · intro u
    exact dqm_fisher_integrable M μ θ₀ ℓ hint hDQM u (fun t => hint_perturb t u)
  · exact LAN_expansion_iii P M μ θ₀ ℓ hℓ h_one hint h_one_perturb hint_perturb
      hDQM h h_n hconv X hX_meas hindep hident hlaw

end LANExpansion
end AsymptoticStatistics
