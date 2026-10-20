module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Taylor domination for the classical Z-estimator (vdV §*5.6, book p.67-68)

The classical conditions of vdV Theorems 5.41 and 5.42 require that the
"essential condition" of vdV §*5.6 is that the estimating functions `θ ↦ ψ_θ(x)` are
twice continuously differentiable in `θ` for every `x`, with second-order partials
dominated by a fixed integrable `ψ̈(x)` on a neighborhood of `θ₀` (book p.67, "the
second-order partial derivatives ... satisfy [domination] for some integrable measurable
function `ψ̈`").

This file defines the derivative objects (`psiDot`, the entrywise Jacobian; `Vmat`, its
`P`-average `V = Pψ̇_{θ₀}`) and states the deterministic Taylor / domination lemmas that
feed both theorems:

* `pointwise_taylor_bound` — first-order Taylor remainder of `ψ_θ` controlled by
  `ψ̈·‖θ − θ₀‖²`;
* `psiDot_lipschitz` — the Jacobian `ψ̇_θ` is `ψ̈`-Lipschitz in `θ`;
* `empirical_taylor_random` — the empirical-average version of the Taylor bound;
* `Psi_differentiable` — the population map `Ψ(θ) = Pψ_θ` is `C¹` with derivative
  `Vmat P ψ θ`;
* `PsiDot_lipschitz` — `θ ↦ Vmat P ψ θ` is `(Pψ̈)`-Lipschitz;
* `PsiDot_nonsingular_nbhd` — nonsingularity of `V` at `θ₀` propagates to a
  neighborhood.

The shared calculus lemma `fderiv_lipschitz_opNorm` is the operator-norm mean-value bound
on `Dψ` obtained from `hdom`.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace Matrix

namespace AsymptoticStatistics.ClassicalZEstimator

open AsymptoticStatistics.EmpiricalProcess

/-- **`ψ̇_θ(x)` — the entrywise Jacobian of the estimating functions.** Entry `(j, i)` is
the `i`-th partial derivative `∂_{θᵢ} ψ_{θ,j}(x)`, obtained by applying the Fréchet
derivative `fderiv ℝ (θ' ↦ ψ_{θ',j}(x)) θ` to the `i`-th standard basis vector
`EuclideanSpace.single i 1`. Row `j` is the gradient of `θ' ↦ ψ_{θ',j}(x)`.

Constitutive (vdV §*5.6 p.68): the first-order derivative of `ψ_θ` whose `P`-average is
the matrix `V` in the asymptotic covariance; the book's "`ψ̇_θ`". Edge: where `ψ_{·,j}(x)`
is not differentiable at `θ`, `fderiv` is `0`, so the entry is `0`. -/
noncomputable def psiDot {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ : EuclideanSpace ℝ (Fin k)) (x : Ω) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun j i => fderiv ℝ (fun θ' => ψ θ' j x) θ (EuclideanSpace.single i (1 : ℝ))

/-- **`V = Pψ̇_{θ₀}` — the population Jacobian.** Entry `(j, i)` is `∫ ∂_{θᵢ}ψ_{θ₀,j} ∂P`.
This is vdV's matrix `V = Pψ̇_{θ₀}` (book p.68), assumed nonsingular; it is the derivative
of the population estimating map `Ψ(θ) = Pψ_θ` at `θ₀` and appears (inverted) in the
asymptotic covariance `V⁻¹ P[ψψᵀ] V⁻ᵀ`.

Constitutive (vdV §*5.6 p.68): the book's `V = Pψ̇_{θ₀}`. -/
noncomputable def Vmat {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun j i => ∫ x, psiDot ψ θ₀ x j i ∂P

/-! ### Measurability of the Jacobian entries -/

/-- **`x ↦ ψ̇_θ(x)ⱼᵢ` is measurable.** The `(j,i)` entry is a limit of measurable
difference quotients `(ψ_{θ + t·eᵢ,j}(x) − ψ_{θ,j}(x))/t` (each measurable in `x` by
`hψ_meas`), hence measurable where `ψ_{·,j}(x)` is differentiable (guaranteed by `hC2`).
-/
theorem psiDot_measurable {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ : EuclideanSpace ℝ (Fin k)) (Θ : Set (EuclideanSpace ℝ (Fin k)))
    (hΘ_open : IsOpen Θ) (hθ : θ ∈ Θ)
    (hψ_meas : ∀ θ' j, Measurable (ψ θ' j))
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ' => ψ θ' j x) Θ) :
    ∀ j i, Measurable (fun x => psiDot ψ θ x j i) := by
  intro j i
  have hdiff : ∀ x : Ω, DifferentiableAt ℝ (fun θ' => ψ θ' j x) θ := fun x =>
    ((hC2 j x).differentiableOn (by norm_num)).differentiableAt (hΘ_open.mem_nhds hθ)
  -- The difference quotients along `t = (m+1)⁻¹` are measurable in `x` …
  have hgmeas : ∀ m : ℕ, Measurable (fun x : Ω =>
      (((m : ℝ) + 1)⁻¹)⁻¹ * (ψ (θ + ((m : ℝ) + 1)⁻¹ • EuclideanSpace.single i (1 : ℝ)) j x
        - ψ θ j x)) := fun m =>
    ((hψ_meas _ j).sub (hψ_meas θ j)).const_mul _
  -- … and converge pointwise to the directional derivative, i.e. to the `(j,i)` entry.
  have htend : ∀ x : Ω, Filter.Tendsto (fun m : ℕ =>
      (((m : ℝ) + 1)⁻¹)⁻¹ * (ψ (θ + ((m : ℝ) + 1)⁻¹ • EuclideanSpace.single i (1 : ℝ)) j x
        - ψ θ j x)) Filter.atTop (𝓝 (psiDot ψ θ x j i)) := by
    intro x
    have hγ : HasDerivAt (fun s : ℝ => θ + s • EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ)) 0 := by
      simpa using
        ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add θ
    have hline : HasDerivAt (fun s : ℝ => ψ (θ + s • EuclideanSpace.single i (1 : ℝ)) j x)
        (psiDot ψ θ x j i) 0 := by
      have hpt : θ + (0 : ℝ) • EuclideanSpace.single i (1 : ℝ) = θ := by simp
      have hF : HasFDerivAt (fun θ' => ψ θ' j x) (fderiv ℝ (fun θ' => ψ θ' j x) θ)
          (θ + (0 : ℝ) • EuclideanSpace.single i (1 : ℝ)) := by
        rw [hpt]; exact (hdiff x).hasFDerivAt
      simpa [Function.comp_def, psiDot] using hF.comp_hasDerivAt (0 : ℝ) hγ
    have hseq : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) Filter.atTop (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨by simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ),
        Filter.Eventually.of_forall fun m => ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      positivity
    simpa [Function.comp_def, smul_eq_mul] using hline.tendsto_slope_zero.comp hseq
  exact measurable_of_tendsto_metrizable' Filter.atTop hgmeas (tendsto_pi_nhds.2 htend)

/-- **Operator-norm Lipschitz bound for the derivative.** The Fréchet derivative map
`θ ↦ D(ψ_{·,j}(x))(θ)` is `ψ̈(x)`-Lipschitz in operator norm on the ball, by the mean-value
inequality applied to `fderiv` with the second derivative dominated by `ψ̈` (`hdom`).

It implies both the entrywise statement `psiDot_lipschitz` and the Taylor bound
`pointwise_taylor_bound`. -/
theorem fderiv_lipschitz_opNorm {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (Θ : Set (EuclideanSpace ℝ (Fin k)))
    (ψddot : Ω → ℝ) {ρ : ℝ}
    (hΘ_open : IsOpen Θ)
    (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ' => ψ θ' j x) Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x) :
    ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ θ' ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖fderiv ℝ (fun θ'' => ψ θ'' j x) θ - fderiv ℝ (fun θ'' => ψ θ'' j x) θ'‖
        ≤ ψddot x * ‖θ - θ'‖ := by
  intro θ hθ θ' hθ' j x
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ (fun θ'' => ψ θ'' j x)) Θ :=
    (hC2 j x).fderiv_of_isOpen hΘ_open (by norm_num)
  have hdiff : ∀ z ∈ Metric.closedBall θ₀ ρ,
      DifferentiableAt ℝ (fderiv ℝ (fun θ'' => ψ θ'' j x)) z := fun z hz =>
    (hfd.differentiableOn one_ne_zero).differentiableAt (hΘ_open.mem_nhds (hball hz))
  have hbnd : ∀ z ∈ Metric.closedBall θ₀ ρ,
      ‖fderiv ℝ (fderiv ℝ (fun θ'' => ψ θ'' j x)) z‖ ≤ ψddot x := by
    intro z hz
    have h1 : ‖fderiv ℝ (fderiv ℝ (fun θ'' => ψ θ'' j x)) z‖
        = ‖iteratedFDeriv ℝ 2 (fun θ'' => ψ θ'' j x) z‖ := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    rw [h1]
    exact hdom z hz j x
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbnd (convex_closedBall θ₀ ρ) hθ' hθ

/-! ### Pointwise Taylor remainder bound -/

/-- **First-order Taylor remainder of `ψ_θ`.** On the ball `‖θ − θ₀‖ ≤ ρ`, the
first-order Taylor remainder of `θ' ↦ ψ_{θ',j}(x)` at `θ₀` is controlled by the
dominating second derivative:

    `|ψ_{θ,j}(x) − ψ_{θ₀,j}(x) − ∑ᵢ ψ̇_{θ₀}(x)ⱼᵢ (θ − θ₀)ᵢ| ≤ ½ ψ̈(x) ‖θ − θ₀‖²`.

Mean-value form of vdV's Taylor expansion "By Taylor's theorem there exists a (random)
vector `θ̃ₙ` on the line segment ..." (book p.68), with the second-order term dominated by
`hdom`. -/
theorem pointwise_taylor_bound {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (Θ : Set (EuclideanSpace ℝ (Fin k)))
    (ψddot : Ω → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hΘ_open : IsOpen Θ)
    (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ' => ψ θ' j x) Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x) :
    ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      |ψ θ j x - ψ θ₀ j x - ∑ i, psiDot ψ θ₀ x j i * (θ - θ₀) i|
        ≤ (1 / 2) * ψddot x * ‖θ - θ₀‖ ^ 2 := by
  classical
  intro θ hθ j x
  -- The coordinate sum is exactly the derivative applied to `θ - θ₀`.
  have hdec : ∑ i, (θ - θ₀) i • EuclideanSpace.single i (1 : ℝ) = (θ - θ₀) := by
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr (θ - θ₀)
  have hsum : ∑ i, psiDot ψ θ₀ x j i * (θ - θ₀) i
      = fderiv ℝ (fun θ'' => ψ θ'' j x) θ₀ (θ - θ₀) := by
    conv_rhs => rw [← hdec]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    simp [psiDot, mul_comm]
  rw [hsum]
  -- Abbreviations for the segment argument.
  set v : EuclideanSpace ℝ (Fin k) := θ - θ₀ with hv
  set φ : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := fderiv ℝ (fun θ'' => ψ θ'' j x) θ₀ with hφ
  set c : ℝ := ψddot x * ‖v‖ ^ 2 with hc
  -- The segment `θ₀ + t·v`, `t ∈ [0,1]`, stays in the ball.
  have hvnorm : ‖v‖ ≤ ρ := by
    simpa [hv, dist_eq_norm] using Metric.mem_closedBall.mp hθ
  have hshift : ∀ t : ℝ, θ₀ + t • v - θ₀ = t • v := fun t => by abel
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, θ₀ + t • v ∈ Metric.closedBall θ₀ ρ := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm, hshift t, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    calc t * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ = ‖v‖ := one_mul _
      _ ≤ ρ := hvnorm
  have hdiffAt : ∀ z ∈ Metric.closedBall θ₀ ρ,
      DifferentiableAt ℝ (fun θ'' => ψ θ'' j x) z := fun z hz =>
    ((hC2 j x).differentiableOn (by norm_num)).differentiableAt (hΘ_open.mem_nhds (hball hz))
  -- The scalar curve `u t = ψ(θ₀ + t·v) - ψ(θ₀) - t·φ(v)`.
  set u : ℝ → ℝ := fun t => ψ (θ₀ + t • v) j x - ψ θ₀ j x - t * φ v with hu
  have hu_deriv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt u ((fderiv ℝ (fun θ'' => ψ θ'' j x) (θ₀ + t • v)) v - φ v) t := by
    intro t ht
    have hγ : HasDerivAt (fun s : ℝ => θ₀ + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add θ₀
    have h1 : HasDerivAt (fun s : ℝ => ψ (θ₀ + s • v) j x)
        ((fderiv ℝ (fun θ'' => ψ θ'' j x) (θ₀ + t • v)) v) t := by
      simpa [Function.comp_def] using
        (hdiffAt _ (hmem t ht)).hasFDerivAt.comp_hasDerivAt t hγ
    have h2 : HasDerivAt (fun s : ℝ => s * φ v) (φ v) t := by
      simpa using (hasDerivAt_id t).mul_const (φ v)
    exact (h1.sub_const (ψ θ₀ j x)).sub h2
  -- Derivative bound along the segment, from the operator-norm Lipschitz estimate.
  have hderiv_bd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(fderiv ℝ (fun θ'' => ψ θ'' j x) (θ₀ + t • v)) v - φ v| ≤ c * t := by
    intro t ht
    have hop := fderiv_lipschitz_opNorm ψ θ₀ Θ ψddot hΘ_open hball hC2 hdom
      (θ₀ + t • v) (hmem t ht) θ₀ (Metric.mem_closedBall_self hρ.le) j x
    rw [hshift t, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hop
    calc |(fderiv ℝ (fun θ'' => ψ θ'' j x) (θ₀ + t • v)) v - φ v|
        = ‖(fderiv ℝ (fun θ'' => ψ θ'' j x) (θ₀ + t • v) - φ) v‖ := by
          simp [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ (fun θ'' => ψ θ'' j x) (θ₀ + t • v) - φ‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ψddot x * (t * ‖v‖)) * ‖v‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
      _ = c * t := by rw [hc]; ring
  -- `u 0 = 0`; comparison with `±(c/2)t²` gives the two-sided bound at `t = 1`.
  have hu0 : u 0 = 0 := by simp [hu]
  have hu1 : u 1 = ψ θ j x - ψ θ₀ j x - φ v := by
    simp [hu, hv]
  have hup : u 1 ≤ c / 2 := by
    have hHd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => u s - c / 2 * (s * s))
          ((fderiv ℝ (fun θ'' => ψ θ'' j x) (θ₀ + t • v)) v - φ v - c * t) t := by
      intro t ht
      have h2 : HasDerivAt (fun s : ℝ => c / 2 * (s * s)) (c * t) t := by
        have h0 : HasDerivAt (fun s : ℝ => s * s) (1 * t + t * 1) t :=
          (hasDerivAt_id t).mul (hasDerivAt_id t)
        simpa using (HasDerivAt.const_mul (c / 2) h0).congr_deriv (by ring)
      exact (hu_deriv t ht).sub h2
    have hmono := antitoneOn_of_deriv_nonpos (D := Set.Icc (0 : ℝ) 1)
      (convex_Icc 0 1)
      (fun t ht => ((hHd t ht).continuousAt).continuousWithinAt)
      (by
        rw [interior_Icc]
        exact fun t ht =>
          ((hHd t (Set.Ioo_subset_Icc_self ht)).differentiableAt).differentiableWithinAt)
      (by
        rw [interior_Icc]
        intro t ht
        rw [(hHd t (Set.Ioo_subset_Icc_self ht)).deriv]
        have h1 := (abs_le.mp (hderiv_bd t (Set.Ioo_subset_Icc_self ht))).2
        linarith)
      (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
    simp only [hu0] at hmono
    norm_num at hmono
    linarith
  have hlow : -(c / 2) ≤ u 1 := by
    have hHd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => u s + c / 2 * (s * s))
          ((fderiv ℝ (fun θ'' => ψ θ'' j x) (θ₀ + t • v)) v - φ v + c * t) t := by
      intro t ht
      have h2 : HasDerivAt (fun s : ℝ => c / 2 * (s * s)) (c * t) t := by
        have h0 : HasDerivAt (fun s : ℝ => s * s) (1 * t + t * 1) t :=
          (hasDerivAt_id t).mul (hasDerivAt_id t)
        simpa using (HasDerivAt.const_mul (c / 2) h0).congr_deriv (by ring)
      exact (hu_deriv t ht).add h2
    have hmono := monotoneOn_of_deriv_nonneg (D := Set.Icc (0 : ℝ) 1)
      (convex_Icc 0 1)
      (fun t ht => ((hHd t ht).continuousAt).continuousWithinAt)
      (by
        rw [interior_Icc]
        exact fun t ht =>
          ((hHd t (Set.Ioo_subset_Icc_self ht)).differentiableAt).differentiableWithinAt)
      (by
        rw [interior_Icc]
        intro t ht
        rw [(hHd t (Set.Ioo_subset_Icc_self ht)).deriv]
        have h1 := (abs_le.mp (hderiv_bd t (Set.Ioo_subset_Icc_self ht))).1
        linarith)
      (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
    simp only [hu0] at hmono
    norm_num at hmono
    linarith
  rw [← hu1]
  rw [abs_le]
  constructor
  · have : (1 : ℝ) / 2 * ψddot x * ‖v‖ ^ 2 = c / 2 := by rw [hc]; ring
    rw [this]; exact hlow
  · have : (1 : ℝ) / 2 * ψddot x * ‖v‖ ^ 2 = c / 2 := by rw [hc]; ring
    rw [this]; exact hup

/-! ### Lipschitz continuity of the Jacobian in `θ` -/

/-- **The Jacobian `ψ̇_θ` is `ψ̈`-Lipschitz in `θ`.** On the ball, each entry varies by
at most `ψ̈(x) ‖θ − θ'‖`:

    `|ψ̇_θ(x)ⱼᵢ − ψ̇_{θ'}(x)ⱼᵢ| ≤ ψ̈(x) ‖θ − θ'‖`,

the mean-value bound for the first derivative with Lipschitz constant `sup‖D²ψ‖ ≤ ψ̈`. -/
theorem psiDot_lipschitz {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (Θ : Set (EuclideanSpace ℝ (Fin k)))
    (ψddot : Ω → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hΘ_open : IsOpen Θ)
    (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ' => ψ θ' j x) Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x) :
    ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ θ' ∈ Metric.closedBall θ₀ ρ, ∀ (j i : Fin k) (x : Ω),
      |psiDot ψ θ x j i - psiDot ψ θ' x j i| ≤ ψddot x * ‖θ - θ'‖ := by
  intro θ hθ θ' hθ' j i x
  have hop := fderiv_lipschitz_opNorm ψ θ₀ Θ ψddot hΘ_open hball hC2 hdom θ hθ θ' hθ' j x
  have hrw : |psiDot ψ θ x j i - psiDot ψ θ' x j i|
      = ‖(fderiv ℝ (fun θ'' => ψ θ'' j x) θ - fderiv ℝ (fun θ'' => ψ θ'' j x) θ')
          (EuclideanSpace.single i (1 : ℝ))‖ := by
    simp [psiDot, Real.norm_eq_abs]
  rw [hrw]
  refine (ContinuousLinearMap.le_opNorm _ _).trans (le_trans (le_of_eq ?_) hop)
  rw [PiLp.norm_single, norm_one, mul_one]

/-! ### Empirical Taylor expansion -/

/-- **Empirical Taylor expansion.** Averaging `pointwise_taylor_bound` over a sample
`Xs : Fin n → Ω` gives, on the ball,

    `|ℙₙψ_{θ,j} − ℙₙψ_{θ₀,j} − ∑ᵢ (ℙₙψ̇_{θ₀})ⱼᵢ (θ − θ₀)ᵢ| ≤ ½ (ℙₙψ̈) ‖θ − θ₀‖²`.

This is vdV's "average of the i.i.d. ... The second derivative `ψ̈(θ̃ₙ)` ... On this event
[the remainder is bounded]" (book p.68), phrased for the empirical measure. -/
theorem empirical_taylor_random {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (ψddot : Ω → ℝ) {ρ : ℝ}
    (hbound : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      |ψ θ j x - ψ θ₀ j x - ∑ i, psiDot ψ θ₀ x j i * (θ - θ₀) i|
        ≤ (1 / 2) * ψddot x * ‖θ - θ₀‖ ^ 2)
    (n : ℕ) (Xs : Fin n → Ω) :
    ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ j : Fin k,
      |empiricalAvg (ψ θ j) n Xs - empiricalAvg (ψ θ₀ j) n Xs
          - ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (θ - θ₀) i|
        ≤ (1 / 2) * empiricalAvg ψddot n Xs * ‖θ - θ₀‖ ^ 2 := by
  intro θ hθ j
  -- Step 1: the empirical remainder is the sample average of the pointwise remainders.
  have hrw : empiricalAvg (ψ θ j) n Xs - empiricalAvg (ψ θ₀ j) n Xs
      - ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (θ - θ₀) i
      = (n : ℝ)⁻¹ * ∑ l, (ψ θ j (Xs l) - ψ θ₀ j (Xs l)
          - ∑ i, psiDot ψ θ₀ (Xs l) j i * (θ - θ₀) i) := by
    have hA : empiricalAvg (ψ θ j) n Xs - empiricalAvg (ψ θ₀ j) n Xs
        = (n : ℝ)⁻¹ * ∑ l, (ψ θ j (Xs l) - ψ θ₀ j (Xs l)) := by
      simp only [empiricalAvg, Finset.sum_sub_distrib, mul_sub]
    have hC : ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (θ - θ₀) i
        = (n : ℝ)⁻¹ * ∑ l, ∑ i, psiDot ψ θ₀ (Xs l) j i * (θ - θ₀) i := by
      calc ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (θ - θ₀) i
          = ∑ i, (n : ℝ)⁻¹ * ∑ l, psiDot ψ θ₀ (Xs l) j i * (θ - θ₀) i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [empiricalAvg]
            rw [mul_assoc, Finset.sum_mul]
        _ = (n : ℝ)⁻¹ * ∑ i, ∑ l, psiDot ψ θ₀ (Xs l) j i * (θ - θ₀) i := by
            rw [← Finset.mul_sum]
        _ = (n : ℝ)⁻¹ * ∑ l, ∑ i, psiDot ψ θ₀ (Xs l) j i * (θ - θ₀) i := by
            rw [Finset.sum_comm]
    rw [hA, hC, ← mul_sub, ← Finset.sum_sub_distrib]
  -- Step 2: average the pointwise Taylor bound.
  have hstep : |∑ l, (ψ θ j (Xs l) - ψ θ₀ j (Xs l)
      - ∑ i, psiDot ψ θ₀ (Xs l) j i * (θ - θ₀) i)|
      ≤ ∑ l, ((1 : ℝ) / 2 * ψddot (Xs l) * ‖θ - θ₀‖ ^ 2) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun l _ => hbound θ hθ j (Xs l))
  have hfinal : ∑ l, ((1 : ℝ) / 2 * ψddot (Xs l) * ‖θ - θ₀‖ ^ 2)
      = (∑ l, ψddot (Xs l)) * ((1 : ℝ) / 2 * ‖θ - θ₀‖ ^ 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  calc (n : ℝ)⁻¹ * |∑ l, (ψ θ j (Xs l) - ψ θ₀ j (Xs l)
        - ∑ i, psiDot ψ θ₀ (Xs l) j i * (θ - θ₀) i)|
      ≤ (n : ℝ)⁻¹ * ∑ l, ((1 : ℝ) / 2 * ψddot (Xs l) * ‖θ - θ₀‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (1 / 2) * empiricalAvg ψddot n Xs * ‖θ - θ₀‖ ^ 2 := by
        rw [hfinal]
        simp only [empiricalAvg]
        ring

/-! ### Differentiability of the population estimating map -/

/-- Crude coordinate bound for the Euclidean norm: `‖w‖ ≤ ∑ⱼ |wⱼ|`. Used to lift the
coordinatewise Taylor estimate of `Ψ` to a vector estimate. -/
theorem euclidean_norm_le_sum_abs {k : ℕ} (w : EuclideanSpace ℝ (Fin k)) :
    ‖w‖ ≤ ∑ j, |w j| := by
  classical
  have hdec : ∑ j, w j • EuclideanSpace.single j (1 : ℝ) = w := by
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr w
  calc ‖w‖ = ‖∑ j, w j • EuclideanSpace.single j (1 : ℝ)‖ := by rw [hdec]
    _ ≤ ∑ j, ‖w j • EuclideanSpace.single j (1 : ℝ)‖ := norm_sum_le _ _
    _ = ∑ j, |w j| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]

/-- **The population map `Ψ(θ) = Pψ_θ` is `C¹` with derivative `Vmat P ψ θ`.** On the
ball, the vector-valued map `θ' ↦ (Pψ_{θ',j})ⱼ` (bundled into `EuclideanSpace ℝ (Fin k)`)
has Fréchet derivative the linear map of the matrix `Vmat P ψ θ = Pψ̇_θ`:

vdV p.68 "Thus, the map `Ψ(θ) = Pψ_θ` is differentiable at `θ₀`. By the same argument `Ψ`
is differentiable throughout a small neighborhood of `θ₀` ...". Differentiation under the
integral sign is justified by the domination `hdom` + integrability. -/
theorem Psi_differentiable {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (Θ : Set (EuclideanSpace ℝ (Fin k)))
    (ψddot : Ω → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hΘ_open : IsOpen Θ)
    (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ' => ψ θ' j x) Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x)
    (hψddot_int : Integrable ψddot P)
    (hψ_int : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ j : Fin k, Integrable (ψ θ j) P)
    (hVint : ∀ (θ : EuclideanSpace ℝ (Fin k)) (j i : Fin k),
      Integrable (fun x => psiDot ψ θ x j i) P) :
    ∀ θ ∈ Metric.ball θ₀ ρ,
      HasFDerivAt (fun θ' => ((WithLp.equiv 2 (Fin k → ℝ)).symm
          (fun j => ∫ x, ψ θ' j x ∂P) : EuclideanSpace ℝ (Fin k)))
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ)) θ := by
  classical
  intro θ hθ
  rw [Metric.mem_ball] at hθ
  -- A closed ball around `θ` inside the domination ball.
  have hr : 0 < (ρ - dist θ θ₀) / 2 := by linarith
  set r : ℝ := (ρ - dist θ θ₀) / 2 with hr_def
  have hsub : Metric.closedBall θ r ⊆ Metric.closedBall θ₀ ρ := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    calc dist z θ₀ ≤ dist z θ + dist θ θ₀ := dist_triangle _ _ _
      _ ≤ r + dist θ θ₀ := by linarith
      _ ≤ ρ := by rw [hr_def]; linarith
  have hθball : θ ∈ Metric.closedBall θ₀ ρ := hsub (Metric.mem_closedBall_self hr.le)
  -- Coordinatewise second-order Taylor estimate for `Ψ`, obtained by integrating `B`.
  have hscalar : ∀ θ' ∈ Metric.closedBall θ r, ∀ j : Fin k,
      |(∫ x, ψ θ' j x ∂P) - (∫ x, ψ θ j x ∂P) - ∑ i, Vmat P ψ θ j i * (θ' - θ) i|
        ≤ (1 / 2) * (∫ x, ψddot x ∂P) * ‖θ' - θ‖ ^ 2 := by
    intro θ' hθ' j
    have hB := pointwise_taylor_bound ψ θ Θ ψddot hr hΘ_open
      (hsub.trans hball) hC2 (fun z hz => hdom z (hsub hz)) θ' hθ' j
    have hint1 : Integrable (ψ θ' j) P := hψ_int θ' (hsub hθ') j
    have hint2 : Integrable (ψ θ j) P := hψ_int θ hθball j
    have hint3 : Integrable (fun x => ∑ i, psiDot ψ θ x j i * (θ' - θ) i) P :=
      integrable_finset_sum _ fun i _ => (hVint θ j i).mul_const _
    have hint12 : Integrable (fun x => ψ θ' j x - ψ θ j x) P := hint1.sub hint2
    have hIall : Integrable (fun x => ψ θ' j x - ψ θ j x
        - ∑ i, psiDot ψ θ x j i * (θ' - θ) i) P := hint12.sub hint3
    have hsplit : ∫ x, (ψ θ' j x - ψ θ j x - ∑ i, psiDot ψ θ x j i * (θ' - θ) i) ∂P
        = (∫ x, ψ θ' j x ∂P) - (∫ x, ψ θ j x ∂P)
          - ∑ i, Vmat P ψ θ j i * (θ' - θ) i := by
      rw [integral_sub hint12 hint3, integral_sub hint1 hint2,
        integral_finset_sum _ fun i _ => (hVint θ j i).mul_const _]
      exact congrArg _ (Finset.sum_congr rfl fun i _ => integral_mul_const _ _)
    rw [← hsplit]
    calc |∫ x, (ψ θ' j x - ψ θ j x - ∑ i, psiDot ψ θ x j i * (θ' - θ) i) ∂P|
        ≤ ∫ x, |ψ θ' j x - ψ θ j x - ∑ i, psiDot ψ θ x j i * (θ' - θ) i| ∂P := by
          simpa only [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := P)
              (f := fun x => ψ θ' j x - ψ θ j x - ∑ i, psiDot ψ θ x j i * (θ' - θ) i)
      _ ≤ ∫ x, (1 / 2) * ψddot x * ‖θ' - θ‖ ^ 2 ∂P :=
          integral_mono hIall.abs ((hψddot_int.const_mul _).mul_const _) hB
      _ = (1 / 2) * (∫ x, ψddot x ∂P) * ‖θ' - θ‖ ^ 2 := by
          rw [integral_mul_const, integral_const_mul]
  -- Package the coordinate estimates into the Fréchet-derivative statement.
  set C : ℝ := max ((k : ℝ) * ((1 / 2) * (∫ x, ψddot x ∂P))) 0 with hC_def
  have hC0 : 0 ≤ C := le_max_right _ _
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min r (c / (C + 1)), lt_min hr (by positivity), fun {θ'} hθ' => ?_⟩
  have hlt_r : dist θ' θ < r := lt_of_lt_of_le hθ' (min_le_left _ _)
  have hmem : θ' ∈ Metric.closedBall θ r := Metric.mem_closedBall.mpr hlt_r.le
  have hnorm_eq : ‖θ' - θ‖ = dist θ' θ := (dist_eq_norm _ _).symm
  -- Each coordinate of the residual is the scalar remainder bounded above.
  have hcoord : ∀ j : Fin k,
      (((WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => ∫ x, ψ θ' j x ∂P) :
            EuclideanSpace ℝ (Fin k))
          - ((WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => ∫ x, ψ θ j x ∂P) :
            EuclideanSpace ℝ (Fin k))
          - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ) (θ' - θ)) j
        = (∫ x, ψ θ' j x ∂P) - (∫ x, ψ θ j x ∂P) - ∑ i, Vmat P ψ θ j i * (θ' - θ) i := by
    intro j
    simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
  calc ‖((WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => ∫ x, ψ θ' j x ∂P) :
          EuclideanSpace ℝ (Fin k))
        - ((WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => ∫ x, ψ θ j x ∂P) :
          EuclideanSpace ℝ (Fin k))
        - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ) (θ' - θ)‖
      ≤ ∑ j, |(((WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => ∫ x, ψ θ' j x ∂P) :
            EuclideanSpace ℝ (Fin k))
          - ((WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => ∫ x, ψ θ j x ∂P) :
            EuclideanSpace ℝ (Fin k))
          - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ) (θ' - θ)) j| :=
        euclidean_norm_le_sum_abs _
    _ ≤ ∑ _j : Fin k, (1 / 2) * (∫ x, ψddot x ∂P) * ‖θ' - θ‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [hcoord j]
        exact hscalar θ' hmem j
    _ = (k : ℝ) * ((1 / 2) * (∫ x, ψddot x ∂P)) * ‖θ' - θ‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ C * ‖θ' - θ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = (C * ‖θ' - θ‖) * ‖θ' - θ‖ := by ring
    _ ≤ c * ‖θ' - θ‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have h1 : ‖θ' - θ‖ ≤ c / (C + 1) := by
          rw [hnorm_eq]; exact (lt_of_lt_of_le hθ' (min_le_right _ _)).le
        calc C * ‖θ' - θ‖ ≤ C * (c / (C + 1)) := mul_le_mul_of_nonneg_left h1 hC0
          _ ≤ c := by
              rw [mul_div_assoc'] at *
              rw [div_le_iff₀ (by positivity)]
              nlinarith
    _ = c * ‖θ' - θ‖ := rfl

/-! ### Lipschitz continuity of `θ ↦ Vmat P ψ θ` -/

/-- **The map `θ ↦ Vmat P ψ θ` is `(Pψ̈)`-Lipschitz.** Averaging the entrywise Jacobian
Lipschitz bound over `P`:

    `|Vmat P ψ θ ⱼᵢ − Vmat P ψ θ' ⱼᵢ| ≤ (∫ ψ̈ ∂P) ‖θ − θ'‖`.

vdV p.68 "the derivative `Pψ̇` can be seen to be continuous throughout this neighborhood".
-/
theorem PsiDot_lipschitz {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (Θ : Set (EuclideanSpace ℝ (Fin k)))
    (ψddot : Ω → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hlip : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ θ' ∈ Metric.closedBall θ₀ ρ,
      ∀ (j i : Fin k) (x : Ω), |psiDot ψ θ x j i - psiDot ψ θ' x j i| ≤ ψddot x * ‖θ - θ'‖)
    (hψddot_int : Integrable ψddot P)
    (hVint : ∀ (θ : EuclideanSpace ℝ (Fin k)) (j i : Fin k),
      Integrable (fun x => psiDot ψ θ x j i) P) :
    ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ θ' ∈ Metric.closedBall θ₀ ρ, ∀ (j i : Fin k),
      |Vmat P ψ θ j i - Vmat P ψ θ' j i| ≤ (∫ x, ψddot x ∂P) * ‖θ - θ'‖ := by
  intro θ hθ θ' hθ' j i
  have hsub : Vmat P ψ θ j i - Vmat P ψ θ' j i
      = ∫ x, (psiDot ψ θ x j i - psiDot ψ θ' x j i) ∂P := by
    rw [integral_sub (hVint θ j i) (hVint θ' j i)]
    rfl
  rw [hsub]
  calc |∫ x, (psiDot ψ θ x j i - psiDot ψ θ' x j i) ∂P|
      ≤ ∫ x, |psiDot ψ θ x j i - psiDot ψ θ' x j i| ∂P := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (μ := P) (f := fun x => psiDot ψ θ x j i - psiDot ψ θ' x j i)
    _ ≤ ∫ x, ψddot x * ‖θ - θ'‖ ∂P :=
        integral_mono ((hVint θ j i).sub (hVint θ' j i)).abs
          (hψddot_int.mul_const _) (fun x => hlip θ hθ θ' hθ' j i x)
    _ = (∫ x, ψddot x ∂P) * ‖θ - θ'‖ := integral_mul_const _ _

/-! ### Nonsingularity on a neighborhood -/

/-- **Nonsingularity of `V` propagates to a ball.** Since `θ ↦ Vmat P ψ θ` is
continuous and `det (Vmat P ψ θ₀)` is a unit (`hV`), the determinant is a unit
throughout some smaller ball `‖θ − θ₀‖ ≤ ρ'`.

vdV p.68 "Because `Pψ̇_{θ₀}` is nonsingular by assumption, we can make the neighborhood
still smaller ... to ensure that the derivative of `Ψ` is nonsingular throughout the
neighborhood." -/
theorem PsiDot_nonsingular_nbhd {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (Θ : Set (EuclideanSpace ℝ (Fin k)))
    (ψddot : Ω → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hKlip : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ θ' ∈ Metric.closedBall θ₀ ρ, ∀ (j i : Fin k),
      |Vmat P ψ θ j i - Vmat P ψ θ' j i| ≤ (∫ x, ψddot x ∂P) * ‖θ - θ'‖)
    (hV : IsUnit (Vmat P ψ θ₀).det) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧
      ∀ θ ∈ Metric.closedBall θ₀ ρ', IsUnit (Vmat P ψ θ).det := by
  classical
  set K : NNReal := ⟨max (∫ x, ψddot x ∂P) 0, le_max_right _ _⟩ with hK
  -- Each entry of `V` is Lipschitz on the ball, hence continuous there.
  have hentry : ∀ j i : Fin k,
      ContinuousOn (fun θ => Vmat P ψ θ j i) (Metric.closedBall θ₀ ρ) := by
    intro j i
    refine (LipschitzOnWith.of_dist_le_mul (K := K) ?_).continuousOn
    intro a ha b hb
    rw [Real.dist_eq, dist_eq_norm]
    exact (hKlip a ha b hb j i).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- Hence so is `det V`, a polynomial in the entries.
  have hdet_cont : ContinuousOn (fun θ => (Vmat P ψ θ).det) (Metric.closedBall θ₀ ρ) := by
    simp only [Matrix.det_apply']
    refine continuousOn_finset_sum _ fun σ _ => ?_
    exact continuousOn_const.mul
      (continuousOn_finset_prod _ fun i _ => hentry (σ i) i)
  have hdet0 : (Vmat P ψ θ₀).det ≠ 0 := isUnit_iff_ne_zero.mp hV
  have hcontAt : ContinuousAt (fun θ => (Vmat P ψ θ).det) θ₀ :=
    hdet_cont.continuousAt (Metric.closedBall_mem_nhds θ₀ hρ)
  have hne : ∀ᶠ θ in 𝓝 θ₀, (Vmat P ψ θ).det ≠ 0 := hcontAt.eventually_ne hdet0
  rw [Metric.eventually_nhds_iff] at hne
  obtain ⟨δ, hδ, hδne⟩ := hne
  refine ⟨min (δ / 2) ρ, lt_min (by linarith) hρ, min_le_right _ _, fun θ hθ => ?_⟩
  rw [Metric.mem_closedBall] at hθ
  refine isUnit_iff_ne_zero.mpr (hδne ?_)
  have h1 : dist θ θ₀ ≤ δ / 2 := hθ.trans (min_le_left _ _)
  linarith

end AsymptoticStatistics.ClassicalZEstimator
