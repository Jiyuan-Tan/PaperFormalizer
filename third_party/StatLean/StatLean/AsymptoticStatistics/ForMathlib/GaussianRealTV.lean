module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
Total-variation / L¹ continuity of `gaussianReal 0 v` in the variance parameter.

This is the analytic upgrade of the pointwise characteristic-function continuity
shipped in `ForMathlib/GaussianVarCharFn.lean`: as a sequence of variances
`σ² : ℕ → ℝ≥0` converges (in `ℝ`) to a *positive* limit `σ²_∞`, the densities
`gaussianPDFReal 0 (σ² n)` converge to `gaussianPDFReal 0 σ²_∞` in **L¹(volume)**
(Scheffé's theorem). This is strictly stronger than weak convergence and yields
integral convergence against any bounded measurable test function — in particular
against the bowl-shaped lower-semi-continuous losses used in the LAM proof of
thm 25.21.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.3,
`hLevy_continuity` step in the proof of thm 25.21.

Mathlib does not have Scheffé's theorem packaged by name. The proof here is the
classical "min trick": for nonnegative densities `f g` each integrating to `1`,

    ∫ |f - g| = ∫ f + ∫ g − 2·∫ min f g = 2 − 2·∫ min f g,

and `min f_n f → f` pointwise with `min f_n f ≤ f` (integrable), so dominated
convergence gives `∫ min f_n f → 1`, hence `∫ |f_n − f| → 0`.

Note on the variance hypothesis: since `σ² n → σ²_∞ > 0`, the sequence is
*eventually* positive, so `gaussianReal 0 (σ² n)` is eventually a non-trivial
Gaussian (not the Dirac case `σ² = 0`). The Lebesgue limit ignores finitely
many indices, so this eventual-positivity suffices and is folded silently into
the proof.
-/

open Filter Topology MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace AsymptoticStatistics.ForMathlib.GaussianRealTV

/-- *Pointwise continuity of the Gaussian density in the variance parameter,
on the positive cone.*

For every `x : ℝ`, the map `v ↦ gaussianPDFReal 0 v x` is continuous in `v` at
any *positive* `v_∞ : ℝ≥0` — i.e., if `(v n : ℝ) → (v_∞ : ℝ)` then
`gaussianPDFReal 0 (v n) x → gaussianPDFReal 0 v_∞ x` in `ℝ`. -/
private lemma gaussianPDFReal_tendsto_of_var_tendsto
    {σ_sq : ℕ → ℝ≥0} {σ_sq_inf : ℝ≥0}
    (h_pos : 0 < σ_sq_inf)
    (hσ : Tendsto (fun n => (σ_sq n : ℝ)) atTop (𝓝 (σ_sq_inf : ℝ))) (x : ℝ) :
    Tendsto (fun n => gaussianPDFReal 0 (σ_sq n) x) atTop
      (𝓝 (gaussianPDFReal 0 σ_sq_inf x)) := by
  simp only [gaussianPDFReal, sub_zero]
  have h_pos_real : (0 : ℝ) < (σ_sq_inf : ℝ) := by exact_mod_cast h_pos
  have h_cont : ContinuousAt
      (fun v : ℝ => (√(2 * π * v))⁻¹ * rexp (-x ^ 2 / (2 * v))) (σ_sq_inf : ℝ) := by
    have h2pv : (0 : ℝ) < 2 * π * (σ_sq_inf : ℝ) := by positivity
    have h2v : (0 : ℝ) < 2 * (σ_sq_inf : ℝ) := by positivity
    have h_sqrt_ne : √(2 * π * (σ_sq_inf : ℝ)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr h2pv)
    have h2v_ne : (2 * (σ_sq_inf : ℝ)) ≠ 0 := ne_of_gt h2v
    refine ContinuousAt.mul ?_ ?_
    · have h1 : ContinuousAt (fun v : ℝ => √(2 * π * v)) (σ_sq_inf : ℝ) := by
        have h_lin : ContinuousAt (fun v : ℝ => 2 * π * v) (σ_sq_inf : ℝ) := by fun_prop
        exact (Real.continuous_sqrt.continuousAt).comp h_lin
      exact h1.inv₀ h_sqrt_ne
    · have h2 : ContinuousAt (fun v : ℝ => -x ^ 2 / (2 * v)) (σ_sq_inf : ℝ) := by
        have hd : ContinuousAt (fun v : ℝ => (2 * v : ℝ)) (σ_sq_inf : ℝ) := by fun_prop
        exact (continuousAt_const).div hd h2v_ne
      exact (Real.continuous_exp.continuousAt).comp h2
  exact h_cont.tendsto.comp hσ

/-- *Scheffé's theorem for `gaussianPDFReal 0 ·` along a converging variance.*

If `σ² n → σ²_∞ > 0`, then the densities converge in L¹(Lebesgue):

    ∫ |gaussianPDFReal 0 (σ² n) x − gaussianPDFReal 0 σ²_∞ x| dx → 0.

(Equivalently, `(1/2)·` this integral is the total-variation distance between
the probability measures `gaussianReal 0 (σ² n)` and `gaussianReal 0 σ²_∞`.)

Proof: for nonneg densities `f, g` with `∫ f = ∫ g = 1`,
`|f − g| = f + g − 2·min f g`, and `min f_n f ≤ f` is an integrable dominating
function with `min f_n f → f` pointwise. DCT gives `∫ min → 1`, so the L¹
distance tends to `2 − 2 = 0`. -/
theorem gaussianReal_TV_tendsto
    {σ_sq : ℕ → ℝ≥0} {σ_sq_inf : ℝ≥0}
    (h_pos : 0 < σ_sq_inf)
    (hσ : Tendsto (fun n => (σ_sq n : ℝ)) atTop (𝓝 (σ_sq_inf : ℝ))) :
    Tendsto (fun n => ∫ x, |gaussianPDFReal 0 (σ_sq n) x
                              - gaussianPDFReal 0 σ_sq_inf x|) atTop (𝓝 0) := by
  -- Eventually σ² n > 0 since σ² n → σ²_∞ > 0.
  have h_eventually_pos : ∀ᶠ n in atTop, (0 : ℝ) < (σ_sq n : ℝ) :=
    hσ.eventually_const_lt (by exact_mod_cast h_pos)
  -- Abbreviations.
  set f_inf : ℝ → ℝ := gaussianPDFReal 0 σ_sq_inf with hf_inf_def
  set f : ℕ → ℝ → ℝ := fun n => gaussianPDFReal 0 (σ_sq n) with hf_def
  -- Pointwise continuity in v.
  have h_ptwise : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (f_inf x)) :=
    fun x => gaussianPDFReal_tendsto_of_var_tendsto h_pos hσ x
  have h_int_n : ∀ n, Integrable (f n) := fun n => integrable_gaussianPDFReal _ _
  have h_int_inf : Integrable f_inf := integrable_gaussianPDFReal _ _
  have h_nn_n : ∀ n x, 0 ≤ f n x := fun n x => gaussianPDFReal_nonneg _ _ _
  have h_nn_inf : ∀ x, 0 ≤ f_inf x := fun x => gaussianPDFReal_nonneg _ _ _
  have h_one_inf : ∫ x, f_inf x = 1 :=
    integral_gaussianPDFReal_eq_one _ (ne_of_gt h_pos)
  have h_one_n : ∀ᶠ n in atTop, ∫ x, f n x = 1 := by
    refine h_eventually_pos.mono ?_
    intro n hn
    have hne : σ_sq n ≠ 0 := by
      intro hzero
      simp [hzero] at hn
    exact integral_gaussianPDFReal_eq_one _ hne
  -- DCT on `min (f n) f_inf` with bound `f_inf`.
  have h_min_meas : ∀ n, AEStronglyMeasurable (fun x => min (f n x) (f_inf x)) volume :=
    fun n => (((measurable_gaussianPDFReal _ _).min
      (measurable_gaussianPDFReal _ _)).aestronglyMeasurable)
  have h_min_bound : ∀ n, ∀ᵐ x, ‖min (f n x) (f_inf x)‖ ≤ f_inf x := fun n =>
    Filter.Eventually.of_forall fun x => by
      have h1 : 0 ≤ min (f n x) (f_inf x) := le_min (h_nn_n n x) (h_nn_inf x)
      have h2 : min (f n x) (f_inf x) ≤ f_inf x := min_le_right _ _
      simpa [Real.norm_eq_abs, abs_of_nonneg h1] using h2
  have h_min_lim : ∀ᵐ x, Tendsto (fun n => min (f n x) (f_inf x)) atTop
      (𝓝 (f_inf x)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have : Tendsto (fun n => min (f n x) (f_inf x)) atTop
        (𝓝 (min (f_inf x) (f_inf x))) :=
      Tendsto.min (h_ptwise x) tendsto_const_nhds
    simpa [min_self] using this
  have h_min_to_one : Tendsto (fun n => ∫ x, min (f n x) (f_inf x)) atTop (𝓝 1) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (bound := f_inf)
      (F := fun n x => min (f n x) (f_inf x)) (f := f_inf) (l := atTop)
      (Filter.Eventually.of_forall h_min_meas)
      (Filter.Eventually.of_forall h_min_bound)
      h_int_inf h_min_lim
    rw [h_one_inf] at h
    exact h
  -- Algebraic identity: |a - b| = a + b - 2·min a b.
  have h_abs_eq : ∀ n x, |f n x - f_inf x| =
      f n x + f_inf x - 2 * min (f n x) (f_inf x) := by
    intro n x
    by_cases h : f n x ≤ f_inf x
    · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]; ring
    · push Not at h
      rw [abs_of_pos (sub_pos.mpr h), min_eq_right h.le]; ring
  -- Min is integrable (dominated by f_inf).
  have h_int_min : ∀ n, Integrable (fun x => min (f n x) (f_inf x)) := by
    intro n
    refine (h_int_inf).mono' (h_min_meas n) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    have h1 : 0 ≤ min (f n x) (f_inf x) := le_min (h_nn_n n x) (h_nn_inf x)
    have h2 : min (f n x) (f_inf x) ≤ f_inf x := min_le_right _ _
    simpa [Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg (h_nn_inf x)] using h2
  -- ∫|f n - f_inf| = (∫ f n) + (∫ f_inf) - 2·(∫ min) = (∫ f n) + 1 - 2·(∫ min).
  have h_int_eq : ∀ n, ∫ x, |f n x - f_inf x| =
      (∫ x, f n x) + 1 - 2 * ∫ x, min (f n x) (f_inf x) := by
    intro n
    have hA : Integrable (fun x => f n x + f_inf x) := (h_int_n n).add h_int_inf
    have hB : Integrable (fun x => (2 : ℝ) * min (f n x) (f_inf x)) :=
      (h_int_min n).const_mul 2
    have hSub : ∫ x, f n x + f_inf x - 2 * min (f n x) (f_inf x) =
        (∫ x, f n x + f_inf x) - ∫ x, (2 : ℝ) * min (f n x) (f_inf x) :=
      integral_sub hA hB
    have hAdd : ∫ x, f n x + f_inf x = (∫ x, f n x) + ∫ x, f_inf x :=
      integral_add (h_int_n n) h_int_inf
    have hMul : ∫ x, (2 : ℝ) * min (f n x) (f_inf x)
        = 2 * ∫ x, min (f n x) (f_inf x) :=
      integral_const_mul 2 _
    calc ∫ x, |f n x - f_inf x|
        = ∫ x, (f n x + f_inf x - 2 * min (f n x) (f_inf x)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro x; exact h_abs_eq n x
      _ = (∫ x, f n x) + 1 - 2 * ∫ x, min (f n x) (f_inf x) := by
          rw [hSub, hAdd, hMul, h_one_inf]
  -- Eventually `∫ f n = 1`, so RHS → 2 - 2·1 = 0.
  have h_target : Tendsto (fun n => ∫ x, |f n x - f_inf x|) atTop (𝓝 (1 + 1 - 2 * 1)) := by
    have h_rhs : Tendsto (fun n => (∫ x, f n x) + 1 - 2 * ∫ x, min (f n x) (f_inf x))
        atTop (𝓝 (1 + 1 - 2 * 1)) := by
      have h_one_tendsto : Tendsto (fun n => ∫ x, f n x) atTop (𝓝 1) := by
        refine tendsto_const_nhds.congr' ?_
        exact h_one_n.mono fun n hn => hn.symm
      exact (h_one_tendsto.add tendsto_const_nhds).sub (h_min_to_one.const_mul 2)
    refine h_rhs.congr' ?_
    exact Filter.Eventually.of_forall fun n => (h_int_eq n).symm
  have hz : (1 + 1 - 2 * 1 : ℝ) = 0 := by norm_num
  rw [hz] at h_target
  exact h_target

/-- *Bounded measurable integrals are continuous in the variance parameter.*

If `σ² n → σ²_∞ > 0` and `f : ℝ → ℝ` is bounded measurable (`|f x| ≤ M`), then

    ∫ x, f x ∂(gaussianReal 0 (σ² n)) → ∫ x, f x ∂(gaussianReal 0 σ²_∞).

Direct corollary of `gaussianReal_TV_tendsto` via the bound
`|∫ f dμ_n − ∫ f dμ_∞| ≤ M · ∫ |g_n − g_∞|` where `g_n, g_∞` are the Lebesgue
densities. -/
theorem gaussianReal_integral_continuous_of_var_tendsto
    {σ_sq : ℕ → ℝ≥0} {σ_sq_inf : ℝ≥0}
    (h_pos : 0 < σ_sq_inf)
    (hσ : Tendsto (fun n => (σ_sq n : ℝ)) atTop (𝓝 (σ_sq_inf : ℝ)))
    {f : ℝ → ℝ} (hf_meas : Measurable f) {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M) :
    Tendsto (fun n => ∫ x, f x ∂(gaussianReal 0 (σ_sq n))) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 σ_sq_inf))) := by
  -- Eventually σ² n ≠ 0.
  have h_eventually_ne : ∀ᶠ n in atTop, σ_sq n ≠ 0 := by
    have h := hσ.eventually_const_lt (by exact_mod_cast h_pos)
    refine h.mono fun n hn hzero => ?_
    simp [hzero] at hn
  have hv_inf_ne : (σ_sq_inf : ℝ≥0) ≠ 0 := ne_of_gt h_pos
  -- M ≥ 0.
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (hf_bdd 0)
  have hf_norm : ∀ x, ‖f x‖ ≤ M := fun x => by rw [Real.norm_eq_abs]; exact hf_bdd x
  -- Eventually, |∫f dμ_n − ∫f dμ_∞| ≤ M · ∫|g_n − g_∞|.
  have h_squeeze : ∀ᶠ n in atTop,
      |(∫ x, f x ∂(gaussianReal 0 (σ_sq n))) -
        (∫ x, f x ∂(gaussianReal 0 σ_sq_inf))| ≤
          M * ∫ x, |gaussianPDFReal 0 (σ_sq n) x - gaussianPDFReal 0 σ_sq_inf x| := by
    refine h_eventually_ne.mono ?_
    intro n hn
    -- Express both as Lebesgue integrals against densities.
    have h_int_n : ∫ x, f x ∂(gaussianReal 0 (σ_sq n))
        = ∫ x, gaussianPDFReal 0 (σ_sq n) x • f x :=
      integral_gaussianReal_eq_integral_smul (μ := 0) (v := σ_sq n) (f := f) hn
    have h_int_inf : ∫ x, f x ∂(gaussianReal 0 σ_sq_inf)
        = ∫ x, gaussianPDFReal 0 σ_sq_inf x • f x :=
      integral_gaussianReal_eq_integral_smul (μ := 0) (v := σ_sq_inf) (f := f) hv_inf_ne
    rw [h_int_n, h_int_inf]
    -- Integrability of `density · f`.
    have hgnf : Integrable (fun x => gaussianPDFReal 0 (σ_sq n) x * f x) :=
      ((integrable_gaussianPDFReal 0 (σ_sq n))).mul_bdd
        hf_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall hf_norm)
    have hginff : Integrable (fun x => gaussianPDFReal 0 σ_sq_inf x * f x) :=
      ((integrable_gaussianPDFReal 0 σ_sq_inf)).mul_bdd
        hf_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall hf_norm)
    -- Combine: ∫(g_n·f) − ∫(g_∞·f) = ∫(g_n − g_∞)·f, then |·| ≤ ∫|·| ≤ M·∫|g_n−g_∞|.
    have h_diff_eq : (∫ x, gaussianPDFReal 0 (σ_sq n) x • f x) -
        (∫ x, gaussianPDFReal 0 σ_sq_inf x • f x) =
        ∫ x, (gaussianPDFReal 0 (σ_sq n) x - gaussianPDFReal 0 σ_sq_inf x) * f x := by
      rw [show (fun x => gaussianPDFReal 0 (σ_sq n) x • f x)
          = (fun x => gaussianPDFReal 0 (σ_sq n) x * f x) from rfl,
        show (fun x => gaussianPDFReal 0 σ_sq_inf x • f x)
          = (fun x => gaussianPDFReal 0 σ_sq_inf x * f x) from rfl,
        ← integral_sub hgnf hginff]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [h_diff_eq]
    -- Pointwise bound.
    have h_pt : ∀ x,
        |(gaussianPDFReal 0 (σ_sq n) x - gaussianPDFReal 0 σ_sq_inf x) * f x|
          ≤ M * |gaussianPDFReal 0 (σ_sq n) x - gaussianPDFReal 0 σ_sq_inf x| := by
      intro x
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hf_bdd x) (abs_nonneg _)
    have h_diff_int : Integrable (fun x =>
        (gaussianPDFReal 0 (σ_sq n) x - gaussianPDFReal 0 σ_sq_inf x) * f x) := by
      have : (fun x => (gaussianPDFReal 0 (σ_sq n) x - gaussianPDFReal 0 σ_sq_inf x) * f x)
          = fun x => gaussianPDFReal 0 (σ_sq n) x * f x
                      - gaussianPDFReal 0 σ_sq_inf x * f x := by
        funext x; ring
      rw [this]; exact hgnf.sub hginff
    have h_abs_int : Integrable (fun x =>
        |gaussianPDFReal 0 (σ_sq n) x - gaussianPDFReal 0 σ_sq_inf x|) :=
      ((integrable_gaussianPDFReal 0 (σ_sq n)).sub
        (integrable_gaussianPDFReal 0 σ_sq_inf)).abs
    calc |∫ x, (gaussianPDFReal 0 (σ_sq n) x - gaussianPDFReal 0 σ_sq_inf x) * f x|
        ≤ ∫ x, |(gaussianPDFReal 0 (σ_sq n) x - gaussianPDFReal 0 σ_sq_inf x) * f x| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x, M * |gaussianPDFReal 0 (σ_sq n) x - gaussianPDFReal 0 σ_sq_inf x| := by
          refine integral_mono_ae h_diff_int.abs (h_abs_int.const_mul M)
            (Filter.Eventually.of_forall h_pt)
      _ = M * ∫ x, |gaussianPDFReal 0 (σ_sq n) x - gaussianPDFReal 0 σ_sq_inf x| :=
          integral_const_mul _ _
  -- The bound goes to M·0 = 0; difference is squeezed to 0.
  have h_bound_to_zero :
      Tendsto (fun n => M * ∫ x, |gaussianPDFReal 0 (σ_sq n) x
                                  - gaussianPDFReal 0 σ_sq_inf x|) atTop (𝓝 0) := by
    have := (gaussianReal_TV_tendsto h_pos hσ).const_mul M
    simpa using this
  -- Express the goal as `Δn → 0` after subtracting the limit.
  have h_diff_to_zero : Tendsto (fun n =>
      (∫ x, f x ∂(gaussianReal 0 (σ_sq n))) -
        (∫ x, f x ∂(gaussianReal 0 σ_sq_inf))) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = 0 from rfl]
    refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => abs_nonneg _) h_squeeze ?_
    simpa using h_bound_to_zero
  -- Add back the constant limit.
  have := h_diff_to_zero.add_const (∫ x, f x ∂(gaussianReal 0 σ_sq_inf))
  simpa using this

end AsymptoticStatistics.ForMathlib.GaussianRealTV
