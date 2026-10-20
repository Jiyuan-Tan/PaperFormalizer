module
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation
public import StatLean.AsymptoticStatistics.ForMathlib.SlutskyFrechetShift

@[expose] public section

/-!
# Theorem 8.3 — Lower Bound for Experiments

Consider a fixed point $\theta_0$ in an open parameter set $\Theta \subseteq
\mathbb{R}^k$ and a functional $\psi : \Theta \to \mathbb{R}^m$. Assume the
experiment $(P_\theta : \theta \in \Theta)$ is differentiable in quadratic mean
at $\theta_0$ with nonsingular Fisher information matrix $J$ (the book's
$I_{\theta_0}$), and that $\psi$ is differentiable at $\theta_0$ with derivative
$\dot\psi_{\theta_0}$ (here a continuous linear map, written `ψ̇`). Let $T_n$ be
estimators in the localized experiments $\bigl(P^n_{\theta_0 + h/\sqrt n} : h \in
\mathbb{R}^k\bigr)$ for which the standardized sequence converges to a limit law
$L_{\theta_0,h}$,
$$
  \sqrt{n}\,\Bigl(T_n - \psi\bigl(\theta_0 + h/\sqrt n\bigr)\Bigr)
    \;\rightsquigarrow\; L_{\theta_0,h}
  \quad\text{under } P^n_{\theta_0 + h/\sqrt n},
  \qquad\text{every } h.
  \tag{8.2}
$$
Then there exists a randomized statistic $T$ in the Gaussian limit experiment
$\bigl(N(h, J^{-1}) : h \in \mathbb{R}^k\bigr)$ — formalized as a Markov kernel
$\kappa$ — such that, for every $h$, the law of $T - \dot\psi_{\theta_0} h$ equals
$L_{\theta_0,h}$. Equivalently, in pushforward form,
$$
  L_{\theta_0,h} \;=\; \bigl(N(h, J^{-1}) \mathbin{\gg\!=} \kappa\bigr)
    \circ \bigl(y \mapsto y - \dot\psi_{\theta_0} h\bigr)^{-1}.
$$

*Alignment with the Lean statement.* The book states the conclusion as "the
randomized statistic $T$ has $T - \dot\psi_{\theta_0} h$ distributed as
$L_{\theta_0,h}$"; the Lean formalization makes the randomization explicit as a
Markov kernel $\kappa$ and expresses the conclusion as the pushforward identity
$L_{\theta_0,h} = ((N(h,J^{-1}) \gg\!= \kappa).\mathrm{map}(\,\cdot - \dot\psi_{\theta_0}h\,))$.
Fisher information is supplied through its bilinear form $J$ via the hypothesis
identifying `fisherInformation` with $\langle u, J v\rangle$; differentiability
of $\psi$ is the Fréchet derivative `HasFDerivAt ψ ψDot θ₀`. No constants are
altered relative to the book.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 8 (Efficiency of Estimators), §8.3 (Lower Bound for Experiments),
Theorem 8.3, Eq (8.2); via Theorem 7.10 (the asymptotic representation theorem,
Chapter 7, Local Asymptotic Normality).

**Proof formalization notes.** Apply Theorem 7.10 to `S_n := √n(T_n − ψ θ₀)`.
Since `S_n` equals `√n(T_n − ψ(θ₀ + h/√n))` plus the deterministic null sequence
`√n(ψ(θ₀ + h/√n) − ψ θ₀)`, which tends to `ψ̇h` by Fréchet differentiability,
Slutsky gives `S_n ⇝ L_{θ,h} * δ_{ψ̇h}` under each `P^n_{θ₀ + h/√n}` (book:
`L_{θ,h} * δ_{ψ̇h}`, the translate of `L_{θ,h}` by `ψ̇h`). Theorem 7.10
(`LAN_representation`) yields a Markov kernel `κ` with
`L_{θ,h} * δ_{ψ̇h} = N(h, J⁻¹) >>= κ`. Translating back by `· − ψ̇h` gives the
stated identity. The formalization splits this into three steps:
`S_n_weak_conv_under_shifted` (Step 1, the Slutsky pre-standardization),
`AsymptoticRepresentation.LAN_representation` (Step 2, Theorem 7.10), and
`map_add_map_sub_eq` (Step 3, inverting the Dirac translation).

**Bibliographic comments.** The theorem is a specialization to the estimation
problem of Le Cam's asymptotic representation theorem (vdV Theorem 7.10), and
its content — that the standardized limit law of any estimator sequence is the
law of a randomized statistic in the Gaussian shift limit experiment, shifted by
$\dot\psi_{\theta_0} h$ — originates with the theory of limits of experiments:
L. Le Cam, "Limits of experiments," *Proceedings of the Sixth Berkeley Symposium
on Mathematical Statistics and Probability* (Vol. 1: Theory of Statistics),
University of California Press, Berkeley, 1972, pp. 245–261. The local
asymptotic minimax and convolution consequences of this lower bound trace to
J. Hájek, "A characterization of limiting distributions of regular estimates,"
*Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete* 14 (1970),
323–330, and J. Hájek, "Local asymptotic minimax and admissibility in
estimation," *Proc. Sixth Berkeley Symp.* (Vol. 1), 1972, pp. 175–194. Theorem
8.3 itself is van der Vaart's packaging of these results; the precise
statement and the Theorem 7.10 reduction follow vdV §8.3.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace AsymptoticStatistics
namespace LowerBoundForExperiments

variable {k d : ℕ}
variable {𝓧 : Type*} [MeasurableSpace 𝓧]

open AsymptoticRepresentation (Θ 𝓨 productMeasure productMeasure_isProbabilityMeasure)

/-! ## Step 1 — Slutsky bridge: pre-standardise (8.2) for Theorem 7.10. -/

/-- **Step 1 sub-lemma.** Given vdV (8.2) — the shifted normalisation
`√n (T_n − ψ(θ₀+h/√n))` weakly converging to `L_h` under `P^n_{θ₀+h/√n}` —
together with Fréchet differentiability of `ψ` at `θ₀`, the **unshifted**
normalisation `S_n := √n (T_n − ψ θ₀)` weakly converges to
`L_h.map (· + ψ̇h)` under the same product measure.

Proof: Slutsky with deterministic null sequence
`√n (ψ(θ₀+h/√n) − ψ θ₀) − ψ̇h →_n 0` (Fréchet) on the difference
`(unshifted − ψ̇h) − shifted = √n (ψ(θ₀+h/√n) − ψ θ₀) − ψ̇h`, then push
through `(· + ψ̇h)` (continuous). -/
theorem S_n_weak_conv_under_shifted
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k)
    (ψ : Θ k → 𝓨 d) (ψDot : Θ k →L[ℝ] 𝓨 d)
    (hψ_diff : HasFDerivAt ψ ψDot θ₀)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (hPDF : IsPDFOf M μ)
    (h : Θ k) (L : Measure (𝓨 d)) [IsProbabilityMeasure L]
    (hT_weak : WeakConverges
      (fun n : ℕ => (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).map
        (fun x => (Real.sqrt n) • (T n x - ψ (θ₀ + (Real.sqrt n)⁻¹ • h))))
      L) :
    WeakConverges
      (fun n : ℕ => (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).map
        (fun x => (Real.sqrt n) • (T n x - ψ θ₀)))
      (L.map (fun y : 𝓨 d => y + ψDot h)) := by
  classical
  -- Notation: each `P n` is the per-`n` product measure at the LAN-perturbed point.
  let P : ∀ n : ℕ, Measure (Fin n → 𝓧) := fun n =>
    productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n
  haveI hP_prob : ∀ n, IsProbabilityMeasure (P n) := fun n =>
    productMeasure_isProbabilityMeasure M μ hPDF _ _
  -- Sqrt n along ℕ tends to ∞.
  have h_sqn_atTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop := by
    have h_cast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    exact Real.tendsto_sqrt_atTop.comp h_cast
  -- Eventually `√n > 0` (along `n : ℕ`).
  have h_sqn_pos_event : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt n :=
    h_sqn_atTop.eventually (eventually_gt_atTop (0 : ℝ))
  -- Reduce `(√n)⁻¹` to a null sequence in ℝ.
  have h_sqn_inv_to_zero : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    h_sqn_atTop.inv_tendsto_atTop
  have h_pt_to_θ₀ : Tendsto (fun n : ℕ => θ₀ + (Real.sqrt n)⁻¹ • h) atTop (𝓝 θ₀) := by
    have hh : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ • h) atTop (𝓝 0) := by
      simpa using h_sqn_inv_to_zero.smul_const h
    simpa using tendsto_const_nhds.add hh
  -- Fréchet `=o[𝓝 θ₀]` form composed along `n ↦ θ₀ + (√n)⁻¹ • h`.
  have h_little_o := hψ_diff.isLittleO
  have h_little_o_comp : (fun n : ℕ =>
        ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀ - ψDot ((Real.sqrt n)⁻¹ • h))
        =o[atTop] (fun n : ℕ => (Real.sqrt n)⁻¹ • h) := by
    have h_comp := h_little_o.comp_tendsto h_pt_to_θ₀
    have h_lhs_eq : (fun x' => ψ x' - ψ θ₀ - ψDot (x' - θ₀)) ∘
        (fun n : ℕ => θ₀ + (Real.sqrt n)⁻¹ • h)
        = (fun n : ℕ =>
          ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀ - ψDot ((Real.sqrt n)⁻¹ • h)) := by
      funext n
      simp [add_sub_cancel_left]
    have h_rhs_eq : (fun x' => x' - θ₀) ∘
        (fun n : ℕ => θ₀ + (Real.sqrt n)⁻¹ • h)
        = (fun n : ℕ => (Real.sqrt n)⁻¹ • h) := by
      funext n
      simp [add_sub_cancel_left]
    rw [h_lhs_eq, h_rhs_eq] at h_comp
    exact h_comp
  -- Fréchet shift: `√n (ψ(θ₀+h/√n) − ψ θ₀) − ψ̇h → 0`.
  have h_frechet_shift : Tendsto (fun n : ℕ =>
      Real.sqrt n • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀) - ψDot h)
    atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set c : ℝ := ε / (‖h‖ + 1) with hc_def
    have hc_pos : 0 < c := by
      have : 0 < ‖h‖ + 1 := by positivity
      positivity
    have hc_bound : c * ‖h‖ < ε := by
      have hh1 : 0 < ‖h‖ + 1 := by positivity
      have := mul_lt_mul_of_pos_left
        (show ‖h‖ < ‖h‖ + 1 by linarith [norm_nonneg h]) hc_pos
      calc c * ‖h‖
          < c * (‖h‖ + 1) := this
        _ = ε := by rw [hc_def, div_mul_cancel₀ _ hh1.ne']
    have h_eventually : ∀ᶠ n : ℕ in atTop,
        ‖ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀ - ψDot ((Real.sqrt n)⁻¹ • h)‖
          ≤ c * ‖(Real.sqrt n)⁻¹ • h‖ := by
      have := h_little_o_comp.def hc_pos
      filter_upwards [this] with n hn using hn
    filter_upwards [h_eventually, h_sqn_pos_event] with n h_bound h_sqn_pos
    have h_ψDot_smul : ψDot ((Real.sqrt n)⁻¹ • h) = (Real.sqrt n)⁻¹ • ψDot h := by
      simp
    have h_norm_smul : ‖(Real.sqrt n)⁻¹ • h‖ = (Real.sqrt n)⁻¹ * ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h_sqn_pos)]
    have h_smul_factor :
        Real.sqrt n • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀) - ψDot h
          = Real.sqrt n •
            (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀ - (Real.sqrt n)⁻¹ • ψDot h) := by
      rw [smul_sub (Real.sqrt n) (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀)
        ((Real.sqrt n)⁻¹ • ψDot h), smul_inv_smul₀ h_sqn_pos.ne']
    have h_dist_eq :
        dist (Real.sqrt n • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀) - ψDot h) 0
          = Real.sqrt n * ‖ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀
              - ψDot ((Real.sqrt n)⁻¹ • h)‖ := by
      rw [dist_zero_right, h_smul_factor, norm_smul, Real.norm_eq_abs,
        abs_of_pos h_sqn_pos, h_ψDot_smul]
    rw [h_dist_eq]
    calc Real.sqrt n * ‖ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀
              - ψDot ((Real.sqrt n)⁻¹ • h)‖
        ≤ Real.sqrt n * (c * ‖(Real.sqrt n)⁻¹ • h‖) :=
          mul_le_mul_of_nonneg_left h_bound h_sqn_pos.le
      _ = Real.sqrt n * (c * ((Real.sqrt n)⁻¹ * ‖h‖)) := by rw [h_norm_smul]
      _ = (Real.sqrt n * (Real.sqrt n)⁻¹) * (c * ‖h‖) := by ring
      _ = 1 * (c * ‖h‖) := by rw [mul_inv_cancel₀ h_sqn_pos.ne']
      _ = c * ‖h‖ := one_mul _
      _ < ε := hc_bound
  -- Apply `slutsky_of_tendstoInMeasure_dist` with
  --   X k ω := √k • (T k ω - ψ (θ₀ + h/√k))   (shifted; weakly converges to L)
  --   Y k ω := √k • (T k ω - ψ θ₀) - ψ̇h     (unshifted minus the limit shift)
  -- The dist between X and Y is exactly the deterministic Fréchet shift,
  -- which tends to 0, so Y also converges weakly to L.
  have hX_meas : ∀ n, AEMeasurable
      (fun ω : (Fin n → 𝓧) =>
        Real.sqrt n • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h))) (P n) := by
    intro n
    have h1 : Measurable (T n) := hT_meas n
    fun_prop
  have hY_meas : ∀ n, AEMeasurable
      (fun ω : (Fin n → 𝓧) =>
        Real.sqrt n • (T n ω - ψ θ₀) - ψDot h) (P n) := by
    intro n
    have h1 : Measurable (T n) := hT_meas n
    fun_prop
  -- dist(X k ω, Y k ω) = ‖(X - Y) k ω‖ = ‖√k(ψ(θ₀+h/√k) - ψ θ₀) - ψ̇h‖.
  -- (Independent of ω; the negation `‖-x‖ = ‖x‖` absorbs the sign flip.)
  have h_dist_eq : ∀ (n : ℕ) (ω : Fin n → 𝓧),
      dist (Real.sqrt n • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
        (Real.sqrt n • (T n ω - ψ θ₀) - ψDot h)
        = ‖Real.sqrt n • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀) - ψDot h‖ := by
    intro n ω
    rw [dist_eq_norm]
    have h_sub_eq :
        Real.sqrt n • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h))
            - (Real.sqrt n • (T n ω - ψ θ₀) - ψDot h)
          = -(Real.sqrt n • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀)
              - ψDot h) := by
      simp only [smul_sub]
      abel
    rw [h_sub_eq, norm_neg]
  have hDist : ∀ ε > 0,
      Tendsto (fun n => (P n).real
        {ω | ε ≤ dist
          (Real.sqrt n • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
          (Real.sqrt n • (T n ω - ψ θ₀) - ψDot h)})
        atTop (𝓝 0) := by
    intro ε hε
    have h_norm_small : ∀ᶠ n : ℕ in atTop,
        ‖Real.sqrt n • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀) - ψDot h‖ < ε := by
      have := h_frechet_shift.eventually (Metric.ball_mem_nhds (0 : 𝓨 d) hε)
      filter_upwards [this] with n hn
      simpa [Metric.mem_ball, dist_zero_right] using hn
    have h_set_empty : ∀ᶠ n : ℕ in atTop,
        {ω : (Fin n → 𝓧) | ε ≤ dist
          (Real.sqrt n • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
          (Real.sqrt n • (T n ω - ψ θ₀) - ψDot h)}
          = (∅ : Set (Fin n → 𝓧)) := by
      filter_upwards [h_norm_small] with n hn
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      calc dist (Real.sqrt n • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
              (Real.sqrt n • (T n ω - ψ θ₀) - ψDot h)
          = ‖Real.sqrt n • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀) - ψDot h‖ :=
            h_dist_eq n ω
        _ < ε := hn
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [h_set_empty] with n hn
    rw [hn]
    simp
  -- Y's law converges to L by Slutsky.
  have h_wc_Y : WeakConverges
      (fun n : ℕ => (P n).map
        (fun ω => Real.sqrt n • (T n ω - ψ θ₀) - ψDot h)) L :=
    WeakConverges.slutsky_of_tendstoInMeasure_dist
      (P := P)
      (X := fun n ω => Real.sqrt n • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
      (Y := fun n ω => Real.sqrt n • (T n ω - ψ θ₀) - ψDot h)
      (ν := L)
      hX_meas hY_meas hT_weak hDist
  -- Push through the continuous map `· + ψ̇h` to recover the unshifted form.
  have hAdd_cont : Continuous (fun y : 𝓨 d => y + ψDot h) := by fun_prop
  have hAdd_meas : Measurable (fun y : 𝓨 d => y + ψDot h) := hAdd_cont.measurable
  have h_Y_meas_strict : ∀ n,
      Measurable (fun ω : (Fin n → 𝓧) =>
        Real.sqrt n • (T n ω - ψ θ₀) - ψDot h) := fun n => by
    have := hT_meas n; fun_prop
  -- Map both sides through `y ↦ y + ψ̇h`, then collapse the double map on the left.
  have h_map_Y := h_wc_Y.map hAdd_cont hAdd_meas
  -- Rewrite `((P n).map Y).map (·+ψ̇h) = (P n).map(Y + ψ̇h) = (P n).map(√n • (T - ψ θ₀))`.
  have h_rewrite : ∀ n,
      ((P n).map (fun ω => Real.sqrt n • (T n ω - ψ θ₀) - ψDot h)).map
          (fun y : 𝓨 d => y + ψDot h)
        = (P n).map (fun ω => Real.sqrt n • (T n ω - ψ θ₀)) := by
    intro n
    rw [Measure.map_map hAdd_meas (h_Y_meas_strict n)]
    congr 1
    funext ω
    simp [sub_add_cancel]
  intro f
  have hf := h_map_Y f
  have h_funext : (fun n : ℕ => ∫ x, f x
        ∂(((P n).map (fun ω => Real.sqrt n • (T n ω - ψ θ₀) - ψDot h)).map
          (fun y : 𝓨 d => y + ψDot h)))
      = (fun n : ℕ => ∫ x, f x
        ∂((P n).map (fun ω => Real.sqrt n • (T n ω - ψ θ₀)))) :=
    funext fun n => by rw [h_rewrite n]
  rw [h_funext] at hf
  exact hf

/-! ## Step 3 — Invert the Dirac translation. -/

/-- **Step 3 helper.** Translation by `c` on `𝓨 d` is invertible: pushing
through `(· + c)` then through `(· − c)` returns the original measure. -/
theorem map_add_map_sub_eq (ν : Measure (𝓨 d)) (c : 𝓨 d) :
    (ν.map (fun y : 𝓨 d => y + c)).map (fun y : 𝓨 d => y - c) = ν := by
  have h_add : Measurable (fun y : 𝓨 d => y + c) := measurable_id.add_const c
  have h_sub : Measurable (fun y : 𝓨 d => y - c) := measurable_id.sub_const c
  rw [Measure.map_map h_sub h_add]
  have h_comp : (fun y : 𝓨 d => y - c) ∘ (fun y : 𝓨 d => y + c) = id := by
    funext y; simp
  rw [h_comp, Measure.map_id]

/-! ## Main theorem — vdV §8.3. -/

/-- **Theorem 8.3 (vdV §8.3) — Lower Bound for Experiments.**

Assume the experiment is DQM at `θ₀` with non-singular Fisher information `J`.
Let `ψ` be Fréchet-differentiable at `θ₀` with derivative `ψ̇`. Let `T_n` be
estimators of `ψ(θ)` in `(P^n_{θ₀+h/√n} : h)` with
`√n(T_n − ψ(θ₀+h/√n)) ⇝ L_h` under `P^n_{θ₀+h/√n}` for every `h` (vdV (8.2)).

Then there is a Markov kernel `κ : Θ ⇝ 𝓨` such that for every `h`,

    L_h = ((N(h, J⁻¹)) >>= κ).map (· − ψ̇h).

Proof. `S_n := √n(T_n − ψ θ₀)` weakly converges to `L_h.map(·+ψ̇h)` by
`S_n_weak_conv_under_shifted`. `LAN_representation` produces `κ` with
`L_h.map(·+ψ̇h) = (N(h, J⁻¹)) >>= κ`. Invert the translation. -/
theorem lower_bound_for_experiments
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : Matrix.PosDef J)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d) (ψDot : Θ k →L[ℝ] 𝓨 d)
    (hψ_diff : HasFDerivAt ψ ψDot θ₀)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L_θh : Θ k → Measure (𝓨 d)) [∀ h, IsProbabilityMeasure (L_θh h)]
    (hT_weak : ∀ h : Θ k,
      WeakConverges
        (fun n : ℕ =>
          (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).map
            (fun x => (Real.sqrt n) •
              (T n x - ψ (θ₀ + (Real.sqrt n)⁻¹ • h))))
        (L_θh h))
    (hPDF : IsPDFOf M μ) :
    ∃ κ : Kernel (Θ k) (𝓨 d), IsMarkovKernel κ ∧
      ∀ h : Θ k,
        L_θh h =
          (((ProbabilityTheory.multivariateGaussian h J⁻¹).bind κ)).map
            (fun y : 𝓨 d => y - ψDot h) := by
  classical
  -- The translated limit `L' h := L_θh h .map (· + ψ̇h)` is the input for 7.10.
  set Lprime : Θ k → Measure (𝓨 d) := fun h =>
    (L_θh h).map (fun y : 𝓨 d => y + ψDot h) with hLprime_def
  -- Each `Lprime h` is a probability measure (pushforward of one).
  haveI hLprime_prob : ∀ h, IsProbabilityMeasure (Lprime h) := fun h => by
    have h_add_meas : Measurable (fun y : 𝓨 d => y + ψDot h) :=
      (continuous_id.add continuous_const).measurable
    exact Measure.isProbabilityMeasure_map h_add_meas.aemeasurable
  -- Step 1: pre-standardise via the Slutsky bridge.
  have hT'_weak : ∀ h : Θ k, WeakConverges
      (fun n : ℕ =>
        (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).map
          (fun x => (Real.sqrt n) • (T n x - ψ θ₀)))
      (Lprime h) := fun h =>
    S_n_weak_conv_under_shifted M μ θ₀ ψ ψDot hψ_diff T hT_meas hPDF h (L_θh h)
      (hT_weak h)
  -- Step 2: apply Theorem 7.10 (vdV-literal LAN representation).
  obtain ⟨κ, hκ_markov, hκ⟩ :=
    AsymptoticRepresentation.LAN_representation M μ θ₀ ℓ hℓ hDQM J hJ_pd hJ_fisher
      (fun n x => Real.sqrt n • (T n x - ψ θ₀))
      (fun n => by have := hT_meas n; fun_prop)
      Lprime hT'_weak hPDF
  refine ⟨κ, hκ_markov, ?_⟩
  intro h
  -- Step 3: invert the translation.
  have h_inv :=
    map_add_map_sub_eq (d := d) (L_θh h) (ψDot h)
  calc L_θh h
      = ((L_θh h).map (fun y : 𝓨 d => y + ψDot h)).map
          (fun y : 𝓨 d => y - ψDot h) := h_inv.symm
    _ = (Lprime h).map (fun y : 𝓨 d => y - ψDot h) := by rw [hLprime_def]
    _ = ((ProbabilityTheory.multivariateGaussian h J⁻¹).bind κ).map
          (fun y : 𝓨 d => y - ψDot h) := by rw [hκ h]

end LowerBoundForExperiments
end AsymptoticStatistics
