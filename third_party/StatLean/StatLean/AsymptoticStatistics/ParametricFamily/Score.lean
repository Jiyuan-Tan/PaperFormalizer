module
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs
public import StatLean.AsymptoticStatistics.DQM.Defs
public import StatLean.AsymptoticStatistics.ForMathlib.L2
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Zero mean of the score function

Let $(P_\theta : \theta \in \Theta)$ be a statistical model with densities
$p_\theta$ with respect to a dominating measure $\mu$. Suppose the model is
*differentiable in quadratic mean* at $\theta_0$ with score function
$\ell_{\theta_0} : \mathcal X \to \Theta$; that is, the map
$\theta \mapsto \sqrt{p_\theta}$ admits an $L^2(\mu)$ derivative
$\tfrac12\,\langle \cdot, \ell_{\theta_0}\rangle\,\sqrt{p_{\theta_0}}$ at
$\theta_0$. Then the score has **zero mean** under $P_{\theta_0}$: for every
direction $u \in \Theta$,
$$\int \langle u, \ell_{\theta_0}(x)\rangle\, p_{\theta_0}(x)\, d\mu(x) = 0,$$
equivalently $P_{\theta_0}\,\ell_{\theta_0} = 0$.

The headline declaration is `score_mean_zero`, assembled from the supporting
lemmas `diff_sq_identity`, `inner_product_continuity`, `dqm_to_rescaled_l2`, and
`sqrt_sum_convergence_of_rescaled`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 7 (Local Asymptotic Normality), §7.2 (Expanding the Likelihood),
Theorem 7.2, differentiability-in-quadratic-mean condition Eq (7.1). Van der
Vaart's Theorem 7.2 states that DQM at $\theta$ implies both
$P_\theta\,\ell_\theta = 0$ and existence of the Fisher information
$I_\theta = P_\theta\,\ell_\theta\ell_\theta^\top$; this file formalizes the
zero-mean half.

**Proof formalization notes.** The argument follows van der Vaart's proof of
Theorem 7.2. It uses the inner-product identity in $L^2(\mu)$
$$\big\langle \sqrt{n}\,(\sqrt{p_n} - \sqrt{p}),\ \sqrt{p_n} + \sqrt{p}\big\rangle_{L^2(\mu)}
  = \sqrt{n}\int (p_n - p)\, d\mu = 0,$$
which vanishes because both densities integrate to $1$ (`diff_sq_identity`).
Taking the limit along a perturbation $\theta_0 + t\cdot u$ as $t \to 0$ and using
the DQM-induced $L^2$ convergence (`dqm_to_rescaled_l2`,
`sqrt_sum_convergence_of_rescaled`) together with continuity of the $L^2$ inner
product (`inner_product_continuity`) gives
$\langle \tfrac12\,\langle u, \ell\rangle\,\sqrt{p},\ 2\sqrt{p}\rangle
  = \int \langle u, \ell\rangle\, p\, d\mu$,
so the limit equals $0$ and the score has zero mean. The Lean statement carries a
few hypotheses that van der Vaart treats as automatic consequences of DQM but that
are supplied here as explicit regularity inputs: finiteness of the Fisher
information along the chosen direction (`h_Fisher`), local $L^2$-membership of the
DQM residual near $t = 0$ (`h_fminus_memLp`), and that each perturbed density
integrates to $1$ and is integrable (`h_one_perturb`, `hint_perturb`).

**Bibliographic comments.** The zero-mean identity for the score is classical
folklore in mathematical statistics, tracing to R. A. Fisher's foundational work
on maximum likelihood estimation and information (R. A. Fisher, "On the
mathematical foundations of theoretical statistics," *Philosophical Transactions
of the Royal Society A* **222** (1922), 309–368; "Theory of statistical
estimation," *Proceedings of the Cambridge Philosophical Society* **22** (1925),
700–725). It has no single seminal source as an isolated proposition. The
specific derivation formalized here — obtaining $P_\theta\,\ell_\theta = 0$ from
differentiability in quadratic mean *without* assuming pointwise differentiability
— is due to the Le Cam–Hájek school of asymptotic decision theory (L. Le Cam,
*Asymptotic Methods in Statistical Decision Theory*, Springer, 1986; J. Hájek,
"Local asymptotic minimax and admissibility in estimation," *Proc. Sixth Berkeley
Symp. on Math. Statist. and Prob.*, vol. 1, 1972, 175–194) and is presented in
textbook form as van der Vaart's Theorem 7.2.
-/

open MeasureTheory Asymptotics Filter Topology
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

section ScoreFunction

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [MeasurableSpace Θ]

/-- A *score function* at a parameter `θ` for a model `M`: a measurable map `𝓧 → Θ`. -/
structure ScoreFunction
    (M : ParametricFamily 𝓧 Θ) (θ : Θ) where
  /-- The score map `ℓ_θ : 𝓧 → Θ`. -/
  toFun : 𝓧 → Θ
  measurable : Measurable toFun

instance {M : ParametricFamily 𝓧 Θ} {θ : Θ} :
    CoeFun (ScoreFunction M θ) (fun _ => 𝓧 → Θ) := ⟨ScoreFunction.toFun⟩

end ScoreFunction

namespace Score

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [MeasurableSpace Θ] [OpensMeasurableSpace Θ] [SecondCountableTopology Θ]

/-! ## Analytical consequences of DQM

These are the analytical consequences of DQM that the score-mean argument uses,
stated as named predicates.
-/

/-- "Rescaled L² convergence": with `h_t := t • h` for `t → 0`, `t⁻¹ (√p_{θ+h_t} − √p_θ)`
converges in L²(μ) to `½ ⟨h, ℓ⟩ √p_θ`. This is the standard restatement of DQM. -/
def RescaledL2Convergence
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ₀ : Θ) (ℓ : 𝓧 → Θ) (h : Θ) : Prop :=
  Filter.Tendsto
    (fun t : ℝ =>
      ∫ x, (t⁻¹ * (M.sqrtDensity (θ₀ + t • h) x - M.sqrtDensity θ₀ x)
            - (1/2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
    (𝓝[≠] 0) (𝓝 0)

/-- "Sum convergence": `√p_{θ+t·h} + √p_θ → 2 √p_θ` in L²(μ) as `t → 0` (on the
punctured neighbourhood to match `RescaledL2Convergence`). -/
def SqrtSumConvergence
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ₀ : Θ) (h : Θ) : Prop :=
  Filter.Tendsto
    (fun t : ℝ => ∫ x, (M.sqrtDensity (θ₀ + t • h) x - M.sqrtDensity θ₀ x) ^ 2 ∂μ)
    (𝓝[≠] (0 : ℝ)) (𝓝 0)

/-! ## Lemma 1 — Difference-of-squares identity (the key cancellation)

For any `θ, θ' ∈ Θ`, if both densities integrate to 1, then
`∫ (√p_{θ'} − √p_θ)(√p_{θ'} + √p_θ) dμ = 0`.

This is `(a-b)(a+b) = a²-b² = p_{θ'} - p_θ`, integrated. -/
omit [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [MeasurableSpace Θ]
  [OpensMeasurableSpace Θ] [SecondCountableTopology Θ] in
lemma diff_sq_identity
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ θ' : Θ)
    (h_one : ∫ x, M.density θ x ∂μ = 1) (h_one' : ∫ x, M.density θ' x ∂μ = 1)
    (hint : Integrable (M.density θ) μ) (hint' : Integrable (M.density θ') μ) :
    ∫ x, (M.sqrtDensity θ' x - M.sqrtDensity θ x) *
         (M.sqrtDensity θ' x + M.sqrtDensity θ x) ∂μ = 0 := by
  -- Pointwise rewrite: (√p' - √p)(√p' + √p) = (√p')² - (√p)² = p' - p.
  have hpt : ∀ x,
      (M.sqrtDensity θ' x - M.sqrtDensity θ x) *
        (M.sqrtDensity θ' x + M.sqrtDensity θ x)
      = M.density θ' x - M.density θ x := by
    intro x
    have h1 := M.sqrtDensity_sq θ' x
    have h2 := M.sqrtDensity_sq θ x
    -- (a - b) * (a + b) = a^2 - b^2
    have hring : (M.sqrtDensity θ' x - M.sqrtDensity θ x) *
                  (M.sqrtDensity θ' x + M.sqrtDensity θ x)
                = M.sqrtDensity θ' x ^ 2 - M.sqrtDensity θ x ^ 2 := by ring
    rw [hring, h1, h2]
  -- Transport the pointwise identity into the integral.
  calc ∫ x, (M.sqrtDensity θ' x - M.sqrtDensity θ x) *
             (M.sqrtDensity θ' x + M.sqrtDensity θ x) ∂μ
      = ∫ x, (M.density θ' x - M.density θ x) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall hpt
    _ = (∫ x, M.density θ' x ∂μ) - (∫ x, M.density θ x ∂μ) :=
        MeasureTheory.integral_sub hint' hint
    _ = 1 - 1 := by rw [h_one', h_one]
    _ = 0 := by ring

/-! ## Lemma 2 — Inner-product continuity for L²(μ)

For sequences `f_t, g_t : 𝓧 → ℝ` with
* `∫ (f_t − f)² dμ → 0`
* `∫ (g_t − g)² dμ → 0`

and with `f, g, f_t, g_t ∈ L²(μ)`, the integral `∫ f_t·g_t dμ → ∫ f·g dμ`.

Proof structure:
1. Algebraic identity  `f_t·g_t − f·g = (f_t − f)·g_t + f·(g_t − g)`.
2. Cauchy–Schwarz on each summand:
   `|∫ (f_t − f)·g_t dμ| ≤ √(∫ (f_t−f)² dμ) · √(∫ g_t² dμ)`,
   `|∫ f·(g_t − g) dμ| ≤ √(∫ f² dμ) · √(∫ (g_t−g)² dμ)`.
3. `√(∫ g_t² dμ) ≤ √(∫ (g_t − g)² dμ) + √(∫ g² dμ)` — L² triangle inequality,
   showing the first factor stays bounded.
4. First factor of first term → 0, second factor bounded ⇒ term → 0.
   First factor of second term bounded (constant), second factor → 0 ⇒ term → 0.
5. Sum of two tendsto-zero sequences → 0, which means `|∫ f_t·g_t − ∫ f·g| → 0`.
-/
omit [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [MeasurableSpace Θ]
  [OpensMeasurableSpace Θ] [SecondCountableTopology Θ] in
lemma inner_product_continuity
    {l : Filter ℝ}
    (μ : Measure 𝓧) (f g : 𝓧 → ℝ) (f_seq g_seq : ℝ → 𝓧 → ℝ)
    (hf_mem : MemLp f 2 μ) (hg_mem : MemLp g 2 μ)
    (hf_seq_mem : ∀ᶠ t in l, MemLp (f_seq t) 2 μ)
    (hg_seq_mem : ∀ᶠ t in l, MemLp (g_seq t) 2 μ)
    (hfminus_mem : ∀ᶠ t in l, MemLp (fun x => f_seq t x - f x) 2 μ)
    (hgminus_mem : ∀ᶠ t in l, MemLp (fun x => g_seq t x - g x) 2 μ)
    (hf : Filter.Tendsto (fun t => ∫ x, (f_seq t x - f x) ^ 2 ∂μ) l (𝓝 0))
    (hg : Filter.Tendsto (fun t => ∫ x, (g_seq t x - g x) ^ 2 ∂μ) l (𝓝 0)) :
    Filter.Tendsto
      (fun t => ∫ x, f_seq t x * g_seq t x ∂μ)
      l
      (𝓝 (∫ x, f x * g x ∂μ)) := by
  -- We show `|∫ f_t·g_t dμ - ∫ f·g dμ| → 0` via the metric formulation.
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Constants from the fixed `f` and `g`:
  set Sf : ℝ := Real.sqrt (∫ x, (f x) ^ 2 ∂μ) with hSf_def
  set Sg : ℝ := Real.sqrt (∫ x, (g x) ^ 2 ∂μ) with hSg_def
  have hSf_nn : 0 ≤ Sf := Real.sqrt_nonneg _
  have hSg_nn : 0 ≤ Sg := Real.sqrt_nonneg _
  -- `√(∫(f_t-f)²) → 0` and `√(∫(g_t-g)²) → 0` as `t → 0`.
  have hf_sqrt : Filter.Tendsto
      (fun t => Real.sqrt (∫ x, (f_seq t x - f x) ^ 2 ∂μ)) l (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hf
    simpa using! this
  have hg_sqrt : Filter.Tendsto
      (fun t => Real.sqrt (∫ x, (g_seq t x - g x) ^ 2 ∂μ)) l (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hg
    simpa using! this
  -- Choose `δ > 0` small enough that `δ · (Sg + 1 + Sf) + δ < ε`.
  -- A safe choice: `δ = ε / (Sg + Sf + 3)` (then bound below). For simplicity
  -- we pick `δ = min 1 (ε / (Sg + Sf + 2))` so that `δ ≤ 1` *and* the linear
  -- combination is `< ε`.
  set K : ℝ := Sg + Sf + 2 with hK_def
  have hK_pos : 0 < K := by positivity
  -- Take `δ ≤ ε/(3K)` so the final combined bound is `δ·2K ≤ (2/3)·ε < ε`.
  set δ : ℝ := min 1 (ε / (3 * K)) with hδ_def
  have h3K_pos : 0 < 3 * K := by positivity
  have hδ_pos : 0 < δ := lt_min one_pos (div_pos hε h3K_pos)
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_le : δ ≤ ε / (3 * K) := min_le_right _ _
  -- Eventually `√(∫(f_t-f)²) < δ` and `√(∫(g_t-g)²) < δ`.
  have h_sqrtf_small : ∀ᶠ t in l,
      Real.sqrt (∫ x, (f_seq t x - f x) ^ 2 ∂μ) < δ := by
    have := (Metric.tendsto_nhds.mp hf_sqrt) δ hδ_pos
    filter_upwards [this] with t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)] at ht
    exact ht
  have h_sqrtg_small : ∀ᶠ t in l,
      Real.sqrt (∫ x, (g_seq t x - g x) ^ 2 ∂μ) < δ := by
    have := (Metric.tendsto_nhds.mp hg_sqrt) δ hδ_pos
    filter_upwards [this] with t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)] at ht
    exact ht
  filter_upwards [h_sqrtf_small, h_sqrtg_small, hf_seq_mem, hg_seq_mem, hfminus_mem, hgminus_mem]
    with t hSff hSgg hf_seq_mem_t hg_seq_mem_t hfminus_mem_t hgminus_mem_t
  -- Algebraic split (pointwise): `f_t·g_t − f·g = (f_t − f)·g + f_t·(g_t − g)`.
  have h_split : ∀ x, f_seq t x * g_seq t x - f x * g x
      = (f_seq t x - f x) * g x + f_seq t x * (g_seq t x - g x) := by
    intro x; ring
  -- Integrate the split.
  have h_fg_int : Integrable (fun x => f x * g x) μ :=
    L2Utils.integrable_mul_of_memLp_two μ hf_mem hg_mem
  have h_fseq_gseq_int : Integrable (fun x => f_seq t x * g_seq t x) μ :=
    L2Utils.integrable_mul_of_memLp_two μ hf_seq_mem_t hg_seq_mem_t
  have h_fminus_g_int : Integrable (fun x => (f_seq t x - f x) * g x) μ :=
    L2Utils.integrable_mul_of_memLp_two μ hfminus_mem_t hg_mem
  have h_fseq_gminus_int : Integrable (fun x => f_seq t x * (g_seq t x - g x)) μ :=
    L2Utils.integrable_mul_of_memLp_two μ hf_seq_mem_t hgminus_mem_t
  have h_int_split :
      ∫ x, f_seq t x * g_seq t x ∂μ - ∫ x, f x * g x ∂μ
      = (∫ x, (f_seq t x - f x) * g x ∂μ) + (∫ x, f_seq t x * (g_seq t x - g x) ∂μ) := by
    rw [← MeasureTheory.integral_sub h_fseq_gseq_int h_fg_int]
    rw [← MeasureTheory.integral_add h_fminus_g_int h_fseq_gminus_int]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall h_split
  -- Cauchy–Schwarz on each summand.
  have h_cs1 :
      |∫ x, (f_seq t x - f x) * g x ∂μ|
        ≤ Real.sqrt (∫ x, (f_seq t x - f x) ^ 2 ∂μ) * Sg := by
    rw [hSg_def]
    exact L2Utils.abs_integral_mul_le_sqrt_integral_sq μ hfminus_mem_t hg_mem
  have h_cs2 :
      |∫ x, f_seq t x * (g_seq t x - g x) ∂μ|
        ≤ Real.sqrt (∫ x, (f_seq t x) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (g_seq t x - g x) ^ 2 ∂μ) :=
    L2Utils.abs_integral_mul_le_sqrt_integral_sq μ hf_seq_mem_t hgminus_mem_t
  -- Bound `√(∫ f_t²) ≤ √(∫(f_t-f)²) + Sf` via the L² triangle inequality
  -- (proved here pointwise via `(a + b)² ≤ 2(a² + b²)`).
  -- Helper: `√(a + b) ≤ √a + √b` for `a, b ≥ 0`.
  have h_sqrt_add_le : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b →
      Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    have h_a := Real.sq_sqrt ha
    have h_b := Real.sq_sqrt hb
    have h_sum_nn : 0 ≤ Real.sqrt a + Real.sqrt b :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_prod_nn : 0 ≤ Real.sqrt a * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_sum_sq : (Real.sqrt a + Real.sqrt b) ^ 2 = a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
      have : (Real.sqrt a + Real.sqrt b) ^ 2
            = Real.sqrt a ^ 2 + 2 * (Real.sqrt a * Real.sqrt b) + Real.sqrt b ^ 2 := by ring
      rw [this, h_a, h_b]; ring
    have h_le : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
      rw [h_sum_sq]; linarith
    have h_step := Real.sqrt_le_sqrt h_le
    rwa [Real.sqrt_sq h_sum_nn] at h_step
  have h_sqrt_ftsq_bd :
      Real.sqrt (∫ x, (f_seq t x) ^ 2 ∂μ)
        ≤ Real.sqrt 2 *
          (Real.sqrt (∫ x, (f_seq t x - f x) ^ 2 ∂μ) + Sf) := by
    have h_pt : ∀ x, (f_seq t x) ^ 2 ≤
        2 * (f_seq t x - f x) ^ 2 + 2 * (f x) ^ 2 := by
      intro x
      have h_apply := L2Utils.sq_add_le_two_mul_sq (f_seq t x - f x) (f x)
      have h_decomp : (f_seq t x - f x) + f x = f_seq t x := by ring
      rw [h_decomp] at h_apply
      exact h_apply
    have hint_fseq_sq : Integrable (fun x => f_seq t x ^ 2) μ :=
      MemLp.integrable_sq hf_seq_mem_t
    have hint_fminus_sq : Integrable (fun x => (f_seq t x - f x) ^ 2) μ :=
      MemLp.integrable_sq hfminus_mem_t
    have hint_f_sq : Integrable (fun x => f x ^ 2) μ :=
      MemLp.integrable_sq hf_mem
    have h_int_le :
        ∫ x, (f_seq t x) ^ 2 ∂μ
          ≤ ∫ x, (2 * (f_seq t x - f x) ^ 2 + 2 * (f x) ^ 2) ∂μ := by
      refine MeasureTheory.integral_mono_ae
        hint_fseq_sq ?_ (Filter.Eventually.of_forall h_pt)
      exact (hint_fminus_sq.const_mul _).add (hint_f_sq.const_mul _)
    have h_int_eq :
        ∫ x, (2 * (f_seq t x - f x) ^ 2 + 2 * (f x) ^ 2) ∂μ
        = 2 * ((∫ x, (f_seq t x - f x) ^ 2 ∂μ) + (∫ x, (f x) ^ 2 ∂μ)) := by
      rw [MeasureTheory.integral_add (hint_fminus_sq.const_mul _) (hint_f_sq.const_mul _)]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      ring
    rw [h_int_eq] at h_int_le
    have h_sqrt_mono := Real.sqrt_le_sqrt h_int_le
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)] at h_sqrt_mono
    have h_sub_le := h_sqrt_add_le
        (∫ x, (f_seq t x - f x) ^ 2 ∂μ) (∫ x, (f x) ^ 2 ∂μ)
        (L2Utils.integral_sq_nonneg μ _) (L2Utils.integral_sq_nonneg μ f)
    have h_2pos : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    calc Real.sqrt (∫ x, (f_seq t x) ^ 2 ∂μ)
        ≤ Real.sqrt 2 * Real.sqrt
            ((∫ x, (f_seq t x - f x) ^ 2 ∂μ) + (∫ x, (f x) ^ 2 ∂μ)) := h_sqrt_mono
      _ ≤ Real.sqrt 2 *
            (Real.sqrt (∫ x, (f_seq t x - f x) ^ 2 ∂μ) + Sf) := by
          rw [hSf_def]
          exact mul_le_mul_of_nonneg_left h_sub_le h_2pos
  -- Combine all the pieces.
  -- abbreviations for the small quantities
  set Aε : ℝ := Real.sqrt (∫ x, (f_seq t x - f x) ^ 2 ∂μ) with hAε_def
  set Bε : ℝ := Real.sqrt (∫ x, (g_seq t x - g x) ^ 2 ∂μ) with hBε_def
  have hAε_nn : 0 ≤ Aε := Real.sqrt_nonneg _
  have hBε_nn : 0 ≤ Bε := Real.sqrt_nonneg _
  -- Triangle inequality on absolute values:
  have h_combined :
      |∫ x, f_seq t x * g_seq t x ∂μ - ∫ x, f x * g x ∂μ|
        ≤ Aε * Sg + Real.sqrt 2 * (Aε + Sf) * Bε := by
    rw [h_int_split]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add h_cs1 ?_
    calc |∫ x, f_seq t x * (g_seq t x - g x) ∂μ|
        ≤ Real.sqrt (∫ x, (f_seq t x) ^ 2 ∂μ) * Bε := h_cs2
      _ ≤ Real.sqrt 2 * (Aε + Sf) * Bε :=
          mul_le_mul_of_nonneg_right h_sqrt_ftsq_bd hBε_nn
  -- Numerical bound: with `Aε < δ`, `Bε < δ`, `δ ≤ 1`, `δ ≤ ε/K`,
  -- `Aε * Sg + √2·(Aε + Sf)·Bε ≤ δ·Sg + √2·(δ + Sf)·δ ≤ δ·(Sg + √2·(1 + Sf)) < ε`.
  -- We prove the bound numerically.
  have hAε_lt : Aε < δ := hSff
  have hBε_lt : Bε < δ := hSgg
  have h_sqrt2_le_2 : Real.sqrt 2 ≤ 2 := by
    have h_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ), h_sq]
  -- Final bound: |·| < ε
  rw [Real.dist_eq]
  refine lt_of_le_of_lt h_combined ?_
  -- `Aε * Sg ≤ δ · Sg`, `Aε ≤ δ ≤ 1` so `Aε + Sf ≤ 1 + Sf`,
  -- and `Bε ≤ δ ≤ ε/K` so `√2·(Aε + Sf)·Bε ≤ 2·(1 + Sf)·δ`.
  have h1 : Aε * Sg ≤ δ * Sg := mul_le_mul_of_nonneg_right hAε_lt.le hSg_nn
  have h2 : Real.sqrt 2 * (Aε + Sf) * Bε ≤ 2 * (1 + Sf) * δ := by
    refine mul_le_mul ?_ hBε_lt.le hBε_nn (by positivity)
    refine mul_le_mul h_sqrt2_le_2 ?_ (by linarith) (by norm_num)
    linarith [hAε_lt.le]
  have h_sum_le : Aε * Sg + Real.sqrt 2 * (Aε + Sf) * Bε ≤ δ * Sg + 2 * (1 + Sf) * δ := by
    linarith
  refine lt_of_le_of_lt h_sum_le ?_
  -- `δ * Sg + 2 * (1 + Sf) * δ = δ · (Sg + 2 + 2·Sf)`, and `Sg + 2 + 2·Sf ≤ 2K`
  -- with `K = Sg + Sf + 2`, so the sum is `≤ 2·δ·K ≤ (2/3)·ε < ε` since `δ ≤ ε/(3K)`.
  have : δ * Sg + 2 * (1 + Sf) * δ = δ * (Sg + 2 + 2 * Sf) := by ring
  rw [this]
  -- Sg + 2 + 2·Sf ≤ 2·K = 2·(Sg + Sf + 2)
  have h_le_2K : Sg + 2 + 2 * Sf ≤ 2 * K := by rw [hK_def]; linarith
  have h_step : δ * (Sg + 2 + 2 * Sf) ≤ δ * (2 * K) :=
    mul_le_mul_of_nonneg_left h_le_2K hδ_pos.le
  refine lt_of_le_of_lt h_step ?_
  -- `δ ≤ ε / (3K)`, so `δ · 2K ≤ (2/3) · ε < ε`.
  have h_2K_pos : 0 < 2 * K := by positivity
  calc δ * (2 * K) ≤ (ε / (3 * K)) * (2 * K) :=
        mul_le_mul_of_nonneg_right hδ_le (by positivity)
    _ = (2 / 3) * ε := by field_simp
    _ < ε := by linarith

/-! ## Lemma 3 — DQM-derived L² approximation, restated for our inner-product step

This is the application of DQM along the sequence `h_t = t • u`. -/
omit [MeasurableSpace Θ] [OpensMeasurableSpace Θ] [SecondCountableTopology Θ] in
lemma dqm_to_rescaled_l2
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ₀ : Θ) (ℓ : 𝓧 → Θ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) (u : Θ) :
    RescaledL2Convergence M μ θ₀ ℓ u := by
  -- Specialise DQM along `t ↦ t • u`.
  have h_smul_tendsto : Filter.Tendsto (fun t : ℝ => t • u) (𝓝 (0 : ℝ)) (𝓝 (0 : Θ)) := by
    have h_cont : Continuous (fun t : ℝ => t • u) := continuous_id.smul continuous_const
    simpa using h_cont.tendsto (0 : ℝ)
  have h_smul_ne : Filter.Tendsto (fun t : ℝ => t • u) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : Θ)) :=
    h_smul_tendsto.mono_left nhdsWithin_le_nhds
  have h_along := hDQM.isLittleO.comp_tendsto h_smul_ne
  -- Pointwise manipulation:
  --   DQM integrand at `t • u` = t² × (rescaled integrand at t).
  -- Apply `isLittleO_iff` to get the sup bound, then squeeze.
  rw [show RescaledL2Convergence M μ θ₀ ℓ u
      ↔ Filter.Tendsto (fun t : ℝ =>
          ∫ x, (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
                - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
          (𝓝[≠] (0 : ℝ)) (𝓝 0) from Iff.rfl]
  -- Metric convergence: reduce to `∀ ε > 0, ∀ᶠ t, |r_sq t| < ε`.
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Choose `c = ε / (‖u‖² + 1)` ; then `c · ‖u‖² < ε`.
  set c : ℝ := ε / (‖u‖ ^ 2 + 1) with hc_def
  have hc_pos : 0 < c := div_pos hε (by positivity)
  have hc_bd : c * ‖u‖ ^ 2 < ε := by
    have h_denom : 0 < ‖u‖ ^ 2 + 1 := by positivity
    rw [hc_def, div_mul_eq_mul_div, div_lt_iff₀ h_denom]
    nlinarith [sq_nonneg ‖u‖, hε]
  -- From `IsLittleO` with constant `c`:
  have h_bd := (isLittleO_iff.mp h_along) hc_pos
  -- Inside `h_bd : ∀ᶠ t, ‖∫ dqm t•u‖ ≤ c · ‖‖t • u‖²‖`
  -- Combine with `t ≠ 0` and rewrite.
  filter_upwards [h_bd, self_mem_nhdsWithin] with t h_bd_t ht_mem
  have ht_ne : t ≠ 0 := ht_mem
  have htsq_pos : 0 < t ^ 2 := by positivity
  have ht_inv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht_ne
  -- Pointwise identity for the DQM integrand at direction `t • u`.
  have h_pt : ∀ x,
      (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x
        - (1/2 : ℝ) * ⟪t • u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
      = t ^ 2 *
        (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
          - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 := by
    intro x
    have h_inner : (⟪t • u, ℓ x⟫ : ℝ) = t * (⟪u, ℓ x⟫ : ℝ) :=
      real_inner_smul_left u (ℓ x) t
    rw [h_inner]
    have h_factor :
        M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x
          - (1/2 : ℝ) * (t * ⟪u, ℓ x⟫) * M.sqrtDensity θ₀ x
        = t * (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
               - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) := by
      have h_t_inv_t : t * t⁻¹ = 1 := ht_inv
      have h_t_inv_t_a :
          t * (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x))
          = M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x := by
        rw [← mul_assoc, h_t_inv_t, one_mul]
      linarith [h_t_inv_t_a]
    rw [h_factor]; ring
  -- LHS of the `isLittleO` at `t`: split LHS integral using `h_pt`.
  have h_lhs_eq :
      ∫ x, (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x
        - (1/2 : ℝ) * ⟪t • u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
      = t ^ 2 *
        ∫ x, (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
              - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
    simp_rw [h_pt]
    rw [MeasureTheory.integral_const_mul]
  -- `‖t • u‖² = t² · ‖u‖²`.
  have h_norm_sq : ‖t • u‖ ^ 2 = t ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  -- Non-negativity of both sides of `h_bd_t`.
  have h_lhs_nn :
      0 ≤ ∫ x, (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x
              - (1/2 : ℝ) * ⟪t • u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  have h_rsq_nn :
      0 ≤ ∫ x, (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
              - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  -- Unfold the function composition in `h_bd_t`.
  simp only [Function.comp] at h_bd_t
  -- Rewrite `h_bd_t` using `h_lhs_eq`, `h_norm_sq`, and strip the absolute values.
  rw [Real.norm_eq_abs, abs_of_nonneg h_lhs_nn, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)] at h_bd_t
  rw [h_lhs_eq, h_norm_sq] at h_bd_t
  -- `h_bd_t : t² · r_sq ≤ c · (t² · ‖u‖²)` ⇒ divide by `t² > 0` : `r_sq ≤ c · ‖u‖²`.
  have h_rsq_bd :
      ∫ x, (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
              - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
        ≤ c * ‖u‖ ^ 2 := by
    nlinarith [htsq_pos, h_bd_t]
  -- Combine with `c · ‖u‖² < ε` to conclude.
  have : ∫ x, (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
              - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ < ε :=
    lt_of_le_of_lt h_rsq_bd hc_bd
  rw [Real.dist_eq, sub_zero]
  exact abs_lt.mpr ⟨by linarith [h_rsq_nn], this⟩

/-! ## Lemma 4 — Sum convergence is a corollary of rate-control

`SqrtSumConvergence` follows from `RescaledL2Convergence`.

**Strategy**.  Let `r_t := t⁻¹·(√p_{θ+tu} − √p_θ) − ½·⟨u,ℓ⟩·√p_θ` (the residual
controlled by `RescaledL2Convergence`).  Rearranging,
`√p_{θ+tu} − √p_θ = t·r_t + (t/2)·⟨u,ℓ⟩·√p_θ`.
Squaring and using `(a+b)² ≤ 2a² + 2b²` (`L2Utils.sq_add_le_two_mul_sq`),
`(√p_{θ+tu} − √p_θ)² ≤ 2·t²·r_t² + (t²/2)·⟨u,ℓ⟩²·p_θ`.
Integrating and taking `t → 0`, both terms tend to 0 — the first because
`t² → 0` and `∫ r_t² → 0`, the second because `t² → 0` and
`∫ ⟨u,ℓ⟩²·p_θ` is a fixed finite constant (Fisher information at `u`).  The
squeeze theorem then gives the result.

The Fisher-information-finite assumption (`h_Fisher`) and integrability of the
pointwise squares (`h_r_sq_int`) are taken as hypotheses here; both follow from
DQM via the same `MemLp` chain (see `dqm_to_rescaled_l2`). -/
omit [MeasurableSpace Θ] [OpensMeasurableSpace Θ] [SecondCountableTopology Θ] in
lemma sqrt_sum_convergence_of_rescaled
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ₀ : Θ) (ℓ : 𝓧 → Θ) (u : Θ)
    (h_rescaled : RescaledL2Convergence M μ θ₀ ℓ u)
    -- Fisher information finite along direction `u`:
    (h_Fisher : Integrable (fun x => ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) μ)
    -- `r_t²` integrable locally near `t = 0` (the only region used here):
    (h_r_sq_int : ∀ᶠ t in 𝓝[≠] (0 : ℝ), Integrable
      (fun x =>
        (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
          - (1 / 2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) μ) :
    SqrtSumConvergence M μ θ₀ u := by
  -- Convenient abbreviations. (`set` allows Lean to unfold them on request.)
  set C : ℝ := ∫ x, ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ with hC_def
  set r_sq : ℝ → ℝ := fun t =>
    ∫ x, (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
        - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ with hr_sq_def
  set diff_sq : ℝ → ℝ := fun t =>
    ∫ x, (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) ^ 2 ∂μ with hdiff_sq_def
  set B : ℝ → ℝ := fun t => 2 * t ^ 2 * r_sq t + t ^ 2 / 2 * C with hB_def
  -- `r_sq t → 0` is exactly the hypothesis `RescaledL2Convergence`.
  have h_rsq_tendsto : Filter.Tendsto r_sq (𝓝[≠] (0 : ℝ)) (𝓝 0) := h_rescaled
  -- Part 1: `B → 0` on `𝓝[≠] 0`.
  have hB_tendsto : Filter.Tendsto B (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h_tsq : Filter.Tendsto (fun t : ℝ => t ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have := (continuous_pow 2).tendsto (0 : ℝ)
      simpa using this
    have h_tsq_ne : Filter.Tendsto (fun t : ℝ => t ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      h_tsq.mono_left nhdsWithin_le_nhds
    have h1 : Filter.Tendsto (fun t : ℝ => 2 * t ^ 2 * r_sq t) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have h2t : Filter.Tendsto (fun t : ℝ => 2 * t ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        have := h_tsq_ne.const_mul (2 : ℝ); simpa using this
      have := h2t.mul h_rsq_tendsto
      simpa using this
    have h2 : Filter.Tendsto (fun t : ℝ => t ^ 2 / 2 * C) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have hh : Filter.Tendsto (fun t : ℝ => t ^ 2 / 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        have := h_tsq_ne.div_const (2 : ℝ); simpa using this
      have := hh.mul_const C
      simpa using this
    have := h1.add h2
    simpa [hB_def] using this
  -- Part 2: For every `t ≠ 0`, `diff_sq t ≤ B t`.
  have h_upper : ∀ᶠ t in 𝓝[≠] (0 : ℝ), diff_sq t ≤ B t := by
    filter_upwards [self_mem_nhdsWithin, h_r_sq_int] with t (ht : t ∈ ({0} : Set ℝ)ᶜ) h_r_sq_int_t
    have ht_ne : t ≠ 0 := by simpa [Set.mem_compl_iff] using ht
    -- Pointwise bound: `(√p_{θ+tu} − √p_θ)² ≤ 2·t²·r_t² + (t²/2)·⟪u,ℓ⟫²·p_θ`.
    have h_pt : ∀ x,
        (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) ^ 2
        ≤ 2 * t ^ 2 *
            (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
              - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
          + t ^ 2 / 2 * (⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) := by
      intro x
      -- Local names for readability
      set a : ℝ := M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x with ha_def
      set q : ℝ := ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x with hq_def
      have hsq : (M.sqrtDensity θ₀ x) ^ 2 = M.density θ₀ x := M.sqrtDensity_sq θ₀ x
      have ht_inv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht_ne
      -- Key linearisation: `a = t · (t⁻¹·a − ½·q) + (t/2)·q`.
      have h_linear : a = t * (t⁻¹ * a - (1/2 : ℝ) * q) + (t / 2) * q := by
        have h1 : t * (t⁻¹ * a) = a := by
          rw [← mul_assoc, ht_inv, one_mul]
        have : t * (t⁻¹ * a - (1/2 : ℝ) * q) + (t / 2) * q = a := by
          rw [mul_sub, h1]; ring
        linarith
      -- `q² = ⟪u,ℓ⟫² · p_θ`.
      have hq_sq : q ^ 2 = ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x := by
        change (⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 = ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x
        rw [mul_pow, hsq]
      -- Apply `sq_add_le_two_mul_sq` and rearrange.
      calc a ^ 2
          = (t * (t⁻¹ * a - (1/2 : ℝ) * q) + (t / 2) * q) ^ 2 := by rw [← h_linear]
        _ ≤ 2 * (t * (t⁻¹ * a - (1/2 : ℝ) * q)) ^ 2 + 2 * ((t / 2) * q) ^ 2 :=
            L2Utils.sq_add_le_two_mul_sq _ _
        _ = 2 * t ^ 2 * (t⁻¹ * a - (1/2 : ℝ) * q) ^ 2 + t ^ 2 / 2 * q ^ 2 := by ring
        _ = 2 * t ^ 2 * (t⁻¹ * a - (1/2 : ℝ) * q) ^ 2
            + t ^ 2 / 2 * (⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) := by rw [hq_sq]
        _ = 2 * t ^ 2 *
              (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
                - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
            + t ^ 2 / 2 * (⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) := by
              show 2 * t ^ 2 * (t⁻¹ * a - (1/2 : ℝ) * q) ^ 2
                   + t ^ 2 / 2 * (⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) = _
              simp only [ha_def, hq_def]
              ring
    -- Integrability of the upper-bound integrand:
    have h_rhs_int : Integrable
        (fun x => 2 * t ^ 2 *
            (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
              - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
          + t ^ 2 / 2 * (⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x)) μ :=
      (h_r_sq_int_t.const_mul _).add (h_Fisher.const_mul _)
    -- Integrability of the LHS:
    have h_lhs_meas : Measurable
        (fun x : 𝓧 => (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) ^ 2) := by
      exact ((M.sqrtDensity_meas _).sub (M.sqrtDensity_meas _)).pow_const 2
    have h_lhs_int : Integrable
        (fun x => (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) ^ 2) μ := by
      -- Follows from the pointwise bound together with `h_rhs_int`, via
      -- `Integrable.mono'` (non-negative, measurable, dominated by integrable).
      refine MeasureTheory.Integrable.mono' h_rhs_int h_lhs_meas.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h_norm : ‖(M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) ^ 2‖
                  = (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) ^ 2 := by
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (sq_nonneg _)
      rw [h_norm]
      exact h_pt x
    -- Integrate the pointwise bound.
    have h_int_le :
        (∫ x, (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) ^ 2 ∂μ)
        ≤ ∫ x, (2 * t ^ 2 *
            (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
              - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
          + t ^ 2 / 2 * (⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x)) ∂μ :=
      MeasureTheory.integral_mono_ae h_lhs_int h_rhs_int
        (Filter.Eventually.of_forall h_pt)
    -- Express the RHS integral as `B t`.
    have h_rhs_eq :
        ∫ x, (2 * t ^ 2 *
            (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
              - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
          + t ^ 2 / 2 * (⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x)) ∂μ
        = B t := by
      rw [MeasureTheory.integral_add (h_r_sq_int_t.const_mul _)
            (h_Fisher.const_mul _)]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    change diff_sq t ≤ B t
    calc diff_sq t
        = ∫ x, (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) ^ 2 ∂μ := rfl
      _ ≤ _ := h_int_le
      _ = B t := h_rhs_eq
  -- Part 3: Squeeze.
  have h_nonneg : ∀ᶠ t in (𝓝[≠] (0 : ℝ)), (0 : ℝ) ≤ diff_sq t :=
    Filter.Eventually.of_forall (fun _ =>
      MeasureTheory.integral_nonneg (fun _ => sq_nonneg _))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hB_tendsto h_nonneg h_upper

/-! ## Final assembly: score has zero mean

Assembled from the four lemmas above.

Strategy:
  1. Pick any direction `u : Θ`.
  2. The integrand `(√p_{θ₀+t·u} − √p_{θ₀}) (√p_{θ₀+t·u} + √p_{θ₀})` integrates to 0
     for every `t ≠ 0` (Lemma 1).
  3. Multiplying by `t⁻¹`, the integrand factors as `(t⁻¹·diff) · sum`. By Lemma 2 +
     Lemma 3 + Lemma 4, this integral converges to `∫ (½ ⟨u, ℓ⟩ √p_θ)(2 √p_θ) dμ
       = ⟨u, ∫ ℓ x · p_{θ₀}(x) dμ⟩`.
  4. The LHS is 0 for every `t ≠ 0`, hence the limit is 0.
  5. Therefore `⟨u, ∫ ℓ p_{θ₀} dμ⟩ = 0` for *every* `u`, which gives
     `∫ ℓ p_{θ₀} dμ = 0` and in particular `∫ ⟨u, ℓ x⟩ p_{θ₀} x dμ = 0`. -/
lemma score_mean_zero
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ) (hℓ : Measurable ℓ)
    (h_one : ∫ x, M.density θ₀ x ∂μ = 1)
    (hint : Integrable (M.density θ₀) μ)
    (h_one_perturb : ∀ t : ℝ, ∀ u : Θ, ∫ x, M.density (θ₀ + t • u) x ∂μ = 1)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- Local `L²` control of the DQM residual near `t = 0`.
    (h_Fisher : Integrable (fun x => ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) μ)
    (h_fminus_memLp : ∀ᶠ t in 𝓝[≠] (0 : ℝ), MemLp (fun x =>
        t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
          - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ)
    :
    ∫ x, ⟪u, ℓ x⟫ * M.density θ₀ x ∂μ = 0 := by
  -- ─────────────────────────────────────────────────────────────
  -- Set up the four functions `f_seq, g_seq, f, g` used throughout.
  -- ─────────────────────────────────────────────────────────────
  set f_seq : ℝ → 𝓧 → ℝ := fun t x =>
    t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) with hf_seq_def
  set g_seq : ℝ → 𝓧 → ℝ := fun t x =>
    M.sqrtDensity (θ₀ + t • u) x + M.sqrtDensity θ₀ x with hg_seq_def
  set f : 𝓧 → ℝ := fun x =>
    (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x with hf_def
  set g : 𝓧 → ℝ := fun x => 2 * M.sqrtDensity θ₀ x with hg_def
  have h_sqrt_memLp : MemLp (M.sqrtDensity θ₀) 2 μ :=
    M.sqrtDensity_memLp_two μ θ₀ hint
  have h_sqrt_perturb_memLp : ∀ t : ℝ, MemLp (M.sqrtDensity (θ₀ + t • u)) 2 μ := by
    intro t
    exact M.sqrtDensity_memLp_two μ (θ₀ + t • u) (hint_perturb t u)
  have h_g_memLp : MemLp g 2 μ := by
    simpa [hg_def] using h_sqrt_memLp.const_mul (2 : ℝ)
  have h_gseq_memLp : ∀ t : ℝ, MemLp (g_seq t) 2 μ := by
    intro t
    simpa [hg_seq_def] using! (h_sqrt_perturb_memLp t).add h_sqrt_memLp
  have h_gminus_memLp : ∀ t : ℝ,
      MemLp (fun x => M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) 2 μ := by
    intro t
    exact (h_sqrt_perturb_memLp t).sub h_sqrt_memLp
  have h_f_memLp : MemLp f 2 μ := by
    have h_inner : AEStronglyMeasurable (fun x => ⟪u, ℓ x⟫) μ := by
      simpa using (AEStronglyMeasurable.const_inner (c := u) hℓ.aestronglyMeasurable)
    have h_prod : AEStronglyMeasurable (fun x => ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) μ := by
      exact h_inner.mul (M.sqrtDensity_meas θ₀).aestronglyMeasurable
    refine (MeasureTheory.memLp_two_iff_integrable_sq
      ((show AEStronglyMeasurable f μ from by
        simpa [hf_def, mul_assoc] using h_prod.const_mul (1 / 2 : ℝ)))).2 ?_
    have h_funext :
        (fun x => (f x) ^ 2) =
        (fun x => (1 / 4 : ℝ) * (⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x)) := by
      funext x
      have hsq : M.sqrtDensity θ₀ x ^ 2 = M.density θ₀ x := M.sqrtDensity_sq θ₀ x
      rw [show M.density θ₀ x = M.sqrtDensity θ₀ x ^ 2 by simpa using hsq.symm]
      simp [hf_def]
      ring_nf
    rw [h_funext]
    exact h_Fisher.const_mul (1 / 4 : ℝ)
  have h_fseq_memLp : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      MemLp (fun x => t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)) 2 μ := by
    filter_upwards [h_fminus_memLp] with t h_fminus_memLp_t
    have h_funext :
        (fun x => t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)) =
        (fun x =>
          (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
            - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x)
          + ((1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x)) := by
      funext x
      ring
    rw [h_funext]
    exact h_fminus_memLp_t.add h_f_memLp
  have h_r_sq_int : ∀ᶠ t in 𝓝[≠] (0 : ℝ), Integrable
      (fun x =>
        (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
          - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) μ := by
    filter_upwards [h_fminus_memLp] with t h_fminus_memLp_t
    exact h_fminus_memLp_t.integrable_sq
  -- ─────────────────────────────────────────────────────────────
  -- L3 → `f_seq t - f → 0` in L² (on the punctured neighbourhood of 0).
  -- ─────────────────────────────────────────────────────────────
  have h_rescaled : RescaledL2Convergence M μ θ₀ ℓ u :=
    dqm_to_rescaled_l2 M μ θ₀ ℓ hDQM u
  have hf_l2 :
      Filter.Tendsto (fun t => ∫ x, (f_seq t x - f x) ^ 2 ∂μ) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    -- `f_seq t x - f x` is exactly the integrand of `RescaledL2Convergence`
    -- (up to associativity of the `(1/2)·⟪u,ℓ⟫·√p` factor). Rewrite pointwise.
    have h_pt : ∀ t x,
        (f_seq t x - f x) ^ 2 =
          (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
            - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 := by
      intro t x; simp [hf_seq_def, hf_def]
    simp_rw [h_pt]
    exact h_rescaled
  -- ─────────────────────────────────────────────────────────────
  -- L4 → `g_seq t - g → 0` in L²; convert to the punctured filter.
  -- ─────────────────────────────────────────────────────────────
  have h_sqrt_sum : SqrtSumConvergence M μ θ₀ u :=
    sqrt_sum_convergence_of_rescaled M μ θ₀ ℓ u h_rescaled h_Fisher h_r_sq_int
  have hg_l2 :
      Filter.Tendsto (fun t => ∫ x, (g_seq t x - g x) ^ 2 ∂μ) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    -- `(√p_{θ+tu} + √p_θ) - 2 √p_θ = √p_{θ+tu} - √p_θ`
    have h_pt : ∀ t x,
        (g_seq t x - g x) ^ 2
          = (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) ^ 2 := by
      intro t x; simp [hg_seq_def, hg_def]; ring
    simp_rw [h_pt]
    exact h_sqrt_sum
  -- ─────────────────────────────────────────────────────────────
  -- L2 → `∫ f_seq t · g_seq t dμ → ∫ f · g dμ` on the punctured filter.
  -- ─────────────────────────────────────────────────────────────
  have h_limit :
      Filter.Tendsto
        (fun t => ∫ x, f_seq t x * g_seq t x ∂μ)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (∫ x, f x * g x ∂μ)) := by
    refine inner_product_continuity (l := 𝓝[≠] (0 : ℝ)) μ f g f_seq g_seq
      h_f_memLp h_g_memLp h_fseq_memLp (Filter.Eventually.of_forall h_gseq_memLp)
      h_fminus_memLp ?_ hf_l2 hg_l2
    · filter_upwards [Filter.Eventually.of_forall h_gminus_memLp] with t h_gminus_memLp_t
      -- `g_seq t x - g x = √p_{θ+tu}(x) - √p_θ(x)` (pointwise functional equality)
      have h_funext :
          (fun x => g_seq t x - g x) =
          (fun x => M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) := by
        funext x; simp [hg_seq_def, hg_def]; ring
      rw [h_funext]
      exact h_gminus_memLp_t
  -- ─────────────────────────────────────────────────────────────
  -- L1 → `∫ f_seq t · g_seq t dμ = 0` for every `t ≠ 0`.
  -- ─────────────────────────────────────────────────────────────
  have h_const_zero :
      ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∫ x, f_seq t x * g_seq t x ∂μ = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ∈ ({0} : Set ℝ)ᶜ)
    have ht_ne : t ≠ 0 := by simpa [Set.mem_compl_iff] using ht
    -- Apply L1 at (θ₀, θ₀ + t • u):
    have hL1 :
        ∫ x, (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) *
             (M.sqrtDensity (θ₀ + t • u) x + M.sqrtDensity θ₀ x) ∂μ = 0 :=
      diff_sq_identity M μ θ₀ (θ₀ + t • u)
        h_one (h_one_perturb t u) hint (hint_perturb t u)
    -- Factor `t⁻¹` out of `f_seq t · g_seq t`.
    calc ∫ x, f_seq t x * g_seq t x ∂μ
        = ∫ x, t⁻¹ * ((M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) *
                       (M.sqrtDensity (θ₀ + t • u) x + M.sqrtDensity θ₀ x)) ∂μ := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun x => by
            simp [hf_seq_def, hg_seq_def]; ring)
      _ = t⁻¹ * ∫ x, (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) *
                     (M.sqrtDensity (θ₀ + t • u) x + M.sqrtDensity θ₀ x) ∂μ := by
          rw [integral_const_mul]
      _ = t⁻¹ * 0 := by rw [hL1]
      _ = 0 := by ring
  -- ─────────────────────────────────────────────────────────────
  -- Therefore the limit of the (constantly-0) sequence is 0.
  -- ─────────────────────────────────────────────────────────────
  have h_limit_zero :
      Filter.Tendsto
        (fun t => ∫ x, f_seq t x * g_seq t x ∂μ)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h_ee : (fun t => ∫ x, f_seq t x * g_seq t x ∂μ)
                =ᶠ[𝓝[≠] (0 : ℝ)] (fun _ => (0 : ℝ)) := h_const_zero
    exact (tendsto_congr' h_ee).mpr tendsto_const_nhds
  -- Uniqueness of the limit on the *non-trivial* filter `𝓝[≠] 0`
  -- (`NeBot` instance is automatic for ℝ via `nhdsNE_neBot` in normed fields).
  have h_fg_zero : ∫ x, f x * g x ∂μ = 0 :=
    tendsto_nhds_unique h_limit h_limit_zero
  -- ─────────────────────────────────────────────────────────────
  -- Compute ∫ f·g dμ = ∫ ⟪u, ℓ⟫ · p_θ dμ (using √p · √p = p).
  -- ─────────────────────────────────────────────────────────────
  have h_pointwise :
      ∀ x, f x * g x = ⟪u, ℓ x⟫ * M.density θ₀ x := by
    intro x
    have hsq : M.sqrtDensity θ₀ x ^ 2 = M.density θ₀ x := M.sqrtDensity_sq θ₀ x
    have hsq' :
        M.sqrtDensity θ₀ x * M.sqrtDensity θ₀ x = M.density θ₀ x := by
      have : M.sqrtDensity θ₀ x * M.sqrtDensity θ₀ x = M.sqrtDensity θ₀ x ^ 2 := by ring
      rw [this, hsq]
    simp [hf_def, hg_def]
    linear_combination ⟪u, ℓ x⟫ * hsq'
  have h_goal :
      ∫ x, f x * g x ∂μ = ∫ x, ⟪u, ℓ x⟫ * M.density θ₀ x ∂μ := by
    refine integral_congr_ae ?_
    exact Filter.Eventually.of_forall h_pointwise
  linarith [h_goal, h_fg_zero]

end Score
end AsymptoticStatistics
