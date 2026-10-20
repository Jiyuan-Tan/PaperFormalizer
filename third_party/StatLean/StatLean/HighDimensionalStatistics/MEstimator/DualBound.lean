module
public import StatLean.HighDimensionalStatistics.MEstimator.Deviation
public import StatLean.HighDimensionalStatistics.MEstimator.SubspaceLip
public import StatLean.Optimization.Convex.Subgradient

@[expose] public section

/-!
# Dual-norm error bound for general M-estimators

The second, sharper error guarantee of the decomposable-regularizer framework. Write
$\Phi$ for the (decomposable) regularizer, $\Phi^*$ for its dual norm, and $\Psi(\bar M)$
for the subspace compatibility (Lipschitz) constant of $\Phi$ relative to the model subspace
$\bar M$. Let $\hat\theta$ be any minimizer of the penalized objective $L(\theta) + \lambda\,\Phi(\theta)$.

Under the *dual-norm curvature condition* with parameters $(\kappa,\tau;R)$ — the dual-norm
analogue of restricted strong convexity, controlling the loss curvature in $\Phi^*$ rather
than in the Euclidean norm — together with decomposability of $\Phi$, the target lying in the
model subspace ($\theta^* \in M$), the slack condition $\tau\,\Psi^2(\bar M) < \kappa/32$, and the
localization $\Phi^*(\hat\theta - \theta^*) \le R$, then conditioned on the good event
$\mathcal G(\lambda) = \{\Phi^*(\nabla L(\theta^*)) \le \lambda/2\}$ every optimum satisfies
$$ \Phi^*(\hat\theta - \theta^*) \;\le\; \frac{3\lambda}{\kappa}. $$
For $\ell_1$-regularization this is an $\ell_\infty$ bound on the error, strictly stronger than the
$\ell_2$/$\ell_1$ bounds of the basic decomposable-regularizer theorem (the analogue of
Wainwright Theorem 9.19).

The key auxiliary fact is the cone comparison
$$ \Phi(\Delta) \;\le\; 16\,\Psi^2(\bar M)\,\Phi^*(\Delta) \qquad (\theta^* \in M,\ \Delta \in \mathbb C) $$
relating the regularizer to its dual on the error cone (Lemma 9.25, eq 9.60).

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 9 (Decomposability and restricted strong convexity),
§9.4, Theorem 9.24 (dual-norm error bound, eq 9.58), with the dual-norm curvature condition
Definition 9.22 (eq 9.55), the good event eq 9.46, and Lemma 9.25 (eq 9.60).

**Proof formalization notes.**
Two ingredients beyond the deterministic machinery of `Bound.lean`:
* the **stationarity** of the composite minimizer `θ̂` — there is a subgradient `z ∈ ∂Φ(θ̂)` with
  `∇L(θ̂) + λ·z = 0`. Mathlib has no subdifferential calculus, so this is hand-built from optimality
  via a directional-derivative argument (`exists_stationary_subgradient`);
* **Lemma 9.25**, `Φ(Δ) ≤ 16·Ψ²(M̄)·Φ*(Δ)` on the cone when `θ* ∈ M` (eq 9.60).

Theorem `mestimator_dual_bound` then proceeds: stationarity gives `∇L(θ̂) = −λz` with `Φ*(z) ≤ 1`;
the good event yields `Φ*(∇L(θ̂)−∇L(θ*)) ≤ 3λ/2`; the dual-norm curvature condition together with
Lemma 9.25 turns this into `(κ − 16τΨ²(M̄))·Φ*(θ̂−θ*) ≤ 3λ/2`, and the slack `τΨ²(M̄) < κ/32`
finishes. The constants here (`3λ/κ`, the `16Ψ²` cone factor, the `κ/32` slack) are exactly those of
Wainwright Thm 9.24 / Lemma 9.25; no book-vs-Lean deviation.

**Bibliographic comments.**
The decomposable-regularizer framework and its master M-estimator bound originate with
S. N. Negahban, P. Ravikumar, M. J. Wainwright and B. Yu, "A unified framework for high-dimensional
analysis of M-estimators with decomposable regularizers", *Statistical Science* 27(4), 538–557 (2012)
(see also the earlier NeurIPS 2009 version). That paper introduces decomposability and the subspace
compatibility constant `Ψ(M̄)` and proves the Euclidean-norm oracle bound (its Theorem 1). The
dual-norm refinement formalized here — controlling `Φ*(θ̂−θ*)` under a dual-norm curvature condition
— is the book's synthesis (Wainwright 2019, Thm 9.24); the present statement and constants follow the
book's treatment rather than a single equation in the Negahban et al. paper.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace
open StatLean.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Stationarity of the composite minimizer.** If `θ̂` minimizes `L + λ·Φ` with `L` convex
differentiable, `Φ` a (convex) seminorm and `λ > 0`, then there is a subgradient `z ∈ ∂Φ(θ̂)` with
`∇L(θ̂) + λ·z = 0` — i.e. `−∇L(θ̂)/λ ∈ ∂Φ(θ̂)`. Mathlib has no convex subdifferential sum rule, so
this is proved by hand: for each direction `w`, the one-sided derivative of `t ↦ L(θ̂+tw)+λΦ(θ̂+tw)`
at `0` is `≥ 0`, giving `⟨−∇L(θ̂), w⟩ ≤ λ(Φ(θ̂+w) − Φ(θ̂))`. -/
theorem exists_stationary_subgradient (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` convex; Wainwright §9.4.
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` differentiable; Wainwright §9.3.
    (hdiff : Differentiable ℝ L)
    (θhat : E) (lam : ℝ)
    -- USER-INPUT: `λ > 0`; Wainwright eq 9.3.
    (hlam : 0 < lam)
    -- USER-INPUT: `θ̂` minimizes `L + λ·Φ`; Wainwright eq 9.3.
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ) :
    ∃ z : E, IsSubgradient (fun x => dr.Φ x) θhat z ∧ gradient L θhat + lam • z = 0 := by
  set g := gradient L θhat with hg_def
  refine ⟨(-(1 / lam)) • g, ?_, ?_⟩
  · -- `z = −(1/λ)·g` is a subgradient of `Φ` at `θ̂`.
    intro y
    set w := y - θhat with hw_def
    -- Build the one-sided directional derivative of `s ↦ L(θ̂ + s·w)` at `0`, equal to `⟪g, w⟫`.
    have hφ : HasDerivAt (fun s : ℝ => θhat + s • w) w 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s • w) w 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
      simpa using h1.const_add θhat
    have hcomp : HasDerivAt (fun s : ℝ => L (θhat + s • w)) ((fderiv ℝ L θhat) w) 0 := by
      have hfd : HasFDerivAt L (fderiv ℝ L θhat) (θhat + (0 : ℝ) • w) := by
        simpa using (hdiff θhat).hasFDerivAt
      simpa using! hfd.comp_hasDerivAt 0 hφ
    have hval : (fderiv ℝ L θhat) w = ⟪g, w⟫_ℝ := by
      rw [hg_def]; exact inner_gradient_left.symm
    rw [hval] at hcomp
    -- Optimality + convexity of `Φ`: the slope is `≥ −λ(Φy − Φθ̂)` for `s ∈ (0,1]`.
    have hslope_lb : ∀ s : ℝ, 0 < s → s ≤ 1 →
        -(lam * (dr.Φ y - dr.Φ θhat)) ≤ slope (fun t : ℝ => L (θhat + t • w)) 0 s := by
      intro s hs hs1
      have hΦconv : dr.Φ (θhat + s • w) ≤ (1 - s) * dr.Φ θhat + s * dr.Φ y := by
        have heq : θhat + s • w = (1 - s) • θhat + s • y := by rw [hw_def]; module
        rw [heq]
        calc dr.Φ ((1 - s) • θhat + s • y)
            ≤ dr.Φ ((1 - s) • θhat) + dr.Φ (s • y) := map_add_le_add _ _ _
          _ = ‖1 - s‖ * dr.Φ θhat + ‖s‖ * dr.Φ y := by rw [map_smul_eq_mul, map_smul_eq_mul]
          _ = (1 - s) * dr.Φ θhat + s * dr.Φ y := by
              rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs.le]
      have hopts := hopt (θhat + s • w)
      rw [slope_def_field, sub_zero, le_div_iff₀ hs]
      simp only [zero_smul, add_zero]
      have hmul := mul_le_mul_of_nonneg_left hΦconv hlam.le
      nlinarith [hopts, hmul]
    -- The eventual bound holds on `𝓝[>] 0`.
    have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        -(lam * (dr.Φ y - dr.Φ θhat)) ≤ slope (fun t : ℝ => L (θhat + t • w)) 0 s := by
      have h1 : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) := Iio_mem_nhds (by norm_num)
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h1] with s hs_pos hs_lt
      exact hslope_lb s hs_pos (le_of_lt hs_lt)
    -- The slope tends to `⟪g, w⟫`, so the limit inherits the lower bound.
    have htend : Filter.Tendsto (slope (fun t : ℝ => L (θhat + t • w)) 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⟪g, w⟫_ℝ)) := by
      refine (hasDerivAt_iff_tendsto_slope.mp hcomp).mono_left (nhdsWithin_mono 0 ?_)
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx
    have hkey : -(lam * (dr.Φ y - dr.Φ θhat)) ≤ ⟪g, w⟫_ℝ := ge_of_tendsto htend hev
    -- Convert `key` to the subgradient inequality.
    rw [real_inner_smul_left, show -(1 / lam) * ⟪g, w⟫_ℝ = -⟪g, w⟫_ℝ / lam from by ring,
        div_le_iff₀ hlam]
    nlinarith [hkey]
  · -- `∇L(θ̂) + λ·z = g + λ·(−(1/λ)·g) = 0`.
    have hcancel : lam * -(1 / lam) = -1 := by field_simp
    rw [smul_smul, hcancel, neg_one_smul, add_neg_cancel]

/-- **Lemma 9.25** (eq 9.60). When `θ* ∈ M`, for any `Δ ∈ ℂ(M, M̄ᗮ)` we have
`Φ(Δ) ≤ 16·Ψ²(M̄)·Φ*(Δ)`. Proof: eq 9.45 gives `Φ(Δ) ≤ 4Ψ(M̄)‖Δ‖`; Hölder gives
`‖Δ‖² ≤ Φ(Δ)·Φ*(Δ) ≤ 4Ψ(M̄)‖Δ‖·Φ*(Δ)`, hence `‖Δ‖ ≤ 4Ψ(M̄)Φ*(Δ)`; combine. -/
theorem reg_le_dual_of_mem (dr : DecomposableReg E) (θstar : E)
    -- USER-INPUT: target lies in the model subspace `θ* ∈ M`; Wainwright Lemma 9.25.
    (hmem : θstar ∈ dr.M) (Δ : E) (hΔ : Δ ∈ errorCone dr θstar) :
    dr.Φ Δ ≤ 16 * (subspaceLip dr.Φ dr.Mbar) ^ 2 * dr.Φstar Δ := by
  set Ψ := subspaceLip dr.Φ dr.Mbar with hΨ
  -- `θ* ∈ M` kills the approximation term `Φ(θ*_{Mᗮ}) = Φ 0 = 0` in the cone inequality.
  have hθ0 : (dr.M)ᗮ.starProjection θstar = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero hmem
  have hcone : dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) ≤ 3 * dr.Φ (dr.Mbar.starProjection Δ) := by
    have h := hΔ
    simp only [errorCone, Set.mem_setOf_eq, hθ0, map_zero] at h
    linarith
  -- eq 9.45: `Φ(Δ) ≤ 4Φ(Δ_{M̄}) ≤ 4Ψ‖Δ‖`.
  have hsplit : dr.Mbar.starProjection Δ + (dr.Mbar)ᗮ.starProjection Δ = Δ :=
    dr.Mbar.starProjection_add_starProjection_orthogonal Δ
  have hΦsplit : dr.Φ Δ ≤
      dr.Φ (dr.Mbar.starProjection Δ) + dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) := by
    have h := map_add_le_add dr.Φ (dr.Mbar.starProjection Δ) ((dr.Mbar)ᗮ.starProjection Δ)
    rwa [hsplit] at h
  have hlip : dr.Φ (dr.Mbar.starProjection Δ) ≤ Ψ * ‖dr.Mbar.starProjection Δ‖ :=
    subspaceLip_le dr.Φ dr.Mbar (dr.Mbar.starProjection_apply_mem Δ)
  have hnorm : ‖dr.Mbar.starProjection Δ‖ ≤ ‖Δ‖ := dr.Mbar.norm_starProjection_apply_le Δ
  have hΨ0 : 0 ≤ Ψ := subspaceLip_nonneg dr.Φ dr.Mbar
  have hΦle : dr.Φ Δ ≤ 4 * Ψ * ‖Δ‖ := by
    have h1 : dr.Φ (dr.Mbar.starProjection Δ) ≤ Ψ * ‖Δ‖ := by
      calc dr.Φ (dr.Mbar.starProjection Δ) ≤ Ψ * ‖dr.Mbar.starProjection Δ‖ := hlip
        _ ≤ Ψ * ‖Δ‖ := mul_le_mul_of_nonneg_left hnorm hΨ0
    nlinarith [hcone, hΦsplit, h1]
  -- Hölder: `‖Δ‖² = ⟪Δ,Δ⟫ ≤ Φ(Δ)·Φ*(Δ) ≤ 4Ψ‖Δ‖·Φ*(Δ)`.
  have hhold : ⟪Δ, Δ⟫_ℝ ≤ dr.Φ Δ * dr.Φstar Δ := dr.holder Δ Δ
  have hnormsq : ‖Δ‖ ^ 2 = ⟪Δ, Δ⟫_ℝ := (real_inner_self_eq_norm_sq Δ).symm
  have hΦstar0 : 0 ≤ dr.Φstar Δ := apply_nonneg dr.Φstar Δ
  by_cases hΔ0 : ‖Δ‖ = 0
  · have hz : Δ = 0 := by rwa [norm_eq_zero] at hΔ0
    simp [hz, map_zero]
  · have hpos : 0 < ‖Δ‖ := lt_of_le_of_ne (norm_nonneg Δ) (Ne.symm hΔ0)
    have h1 : ‖Δ‖ ^ 2 ≤ 4 * Ψ * ‖Δ‖ * dr.Φstar Δ := by
      calc ‖Δ‖ ^ 2 = ⟪Δ, Δ⟫_ℝ := hnormsq
        _ ≤ dr.Φ Δ * dr.Φstar Δ := hhold
        _ ≤ 4 * Ψ * ‖Δ‖ * dr.Φstar Δ := mul_le_mul_of_nonneg_right hΦle hΦstar0
    have h2 : ‖Δ‖ ≤ 4 * Ψ * dr.Φstar Δ := by nlinarith [h1, hpos]
    nlinarith [hΦle, h2, hΨ0, hpos, hΦstar0]

/-- **Theorem 9.24** — dual-norm error bound (eq 9.58). Given `θ* ∈ M`, the `Φ*`-curvature condition
(A1′, Def 9.22) with `(κ, τ; R)`, decomposability (A2), and `τ·Ψ²(M̄) < κ/32`, then conditioned on the
good event `𝔾(λ)` and `Φ*(θ̂−θ*) ≤ R`, any optimum satisfies `Φ*(θ̂ − θ*) ≤ 3λ/κ`.

Proof: stationarity gives `∇L(θ̂) = −λz`, `Φ*(z) ≤ 1`; with the good event,
`Φ*(∇L(θ̂)−∇L(θ*)) ≤ 3λ/2`. The curvature condition + Lemma 9.25 turn this into
`(κ − 16τΨ²(M̄))·Φ*(θ̂−θ*) ≤ 3λ/2`, and `τΨ²(M̄) < κ/32` finishes. -/
theorem mestimator_dual_bound (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` convex (A1′ context); Wainwright §9.4.2.
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` differentiable; Wainwright §9.3.
    (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam κ τ R : ℝ)
    (hlam : 0 < lam) (hκ : 0 < κ)
    -- USER-INPUT: target lies in the model subspace `θ* ∈ M`; Wainwright Thm 9.24.
    (hmem : θstar ∈ dr.M)
    -- USER-INPUT: `Φ*`-curvature condition `(κ, τ; R)` (A1′, Def 9.22); Wainwright eq 9.55.
    (hcurv : dualCurvature L θstar dr.Φ dr.Φstar κ τ R)
    -- USER-INPUT: `θ̂` minimizes `L + λ·Φ`; Wainwright eq 9.3.
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    -- USER-INPUT: good event `𝔾(λ)`; Wainwright eq 9.46.
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam)
    -- USER-INPUT: slack condition `τ·Ψ²(M̄) < κ/32`; Wainwright Thm 9.24.
    (hτ : τ * (subspaceLip dr.Φ dr.Mbar) ^ 2 < κ / 32)
    -- USER-INPUT: localization `Φ*(θ̂−θ*) ≤ R` (the conditioning event); Wainwright Thm 9.24.
    (hRloc : dr.Φstar (θhat - θstar) ≤ R) :
    dr.Φstar (θhat - θstar) ≤ 3 * lam / κ := by
  set Δ := θhat - θstar with hΔdef
  set Ψ := subspaceLip dr.Φ dr.Mbar with hΨ
  obtain ⟨z, hz, hstat⟩ :=
    exists_stationary_subgradient dr L hL hdiff θhat lam hlam hopt
  -- Stationarity: `∇L(θ̂) = −λ·z`.
  have hg : gradient L θhat = -(lam • z) := eq_neg_of_add_eq_zero_left hstat
  -- `Φ*(z) ≤ 1` from the subgradient inequality + subadditivity of `Φ`.
  have hzstar : dr.Φstar z ≤ 1 := by
    apply dr.tight z 1
    intro u hu
    have h := hz (θhat + u)
    simp only [add_sub_cancel_left] at h
    have htri := map_add_le_add dr.Φ θhat u
    have hcomm : ⟪z, u⟫_ℝ = ⟪u, z⟫_ℝ := real_inner_comm u z
    linarith
  -- Good event: `Φ*(∇L(θ̂) − ∇L(θ*)) ≤ 3λ/2`.
  have hG' : dr.Φstar (gradient L θstar) ≤ lam / 2 := hG
  have hgg : gradient L θhat - gradient L θstar = -(lam • z + gradient L θstar) := by
    rw [hg]; abel
  have hdualbound : dr.Φstar (gradient L θhat - gradient L θstar) ≤ 3 * lam / 2 := by
    rw [hgg, map_neg_eq_map]
    calc dr.Φstar (lam • z + gradient L θstar)
        ≤ dr.Φstar (lam • z) + dr.Φstar (gradient L θstar) := map_add_le_add _ _ _
      _ = ‖lam‖ * dr.Φstar z + dr.Φstar (gradient L θstar) := by rw [map_smul_eq_mul]
      _ ≤ 3 * lam / 2 := by
          rw [Real.norm_of_nonneg hlam.le]
          have := mul_le_mul_of_nonneg_left hzstar hlam.le
          linarith
  -- Curvature condition at `Δ = θ̂ − θ*` (`θ* + Δ = θ̂`).
  have hcurvΔ := hcurv Δ hRloc
  have hθhat : θstar + Δ = θhat := by rw [hΔdef]; abel
  rw [hθhat] at hcurvΔ
  -- Lemma 9.25: `Φ(Δ) ≤ 16Ψ²·Φ*(Δ)`.
  have hcone : Δ ∈ errorCone dr θstar := by
    have h := error_mem_cone dr L hL hdiff θstar θhat lam hlam hopt hG
    rwa [← hΔdef] at h
  have hreg : dr.Φ Δ ≤ 16 * Ψ ^ 2 * dr.Φstar Δ := reg_le_dual_of_mem dr θstar hmem Δ hcone
  -- Combine: `(κ − 16τΨ²)Φ*(Δ) ≤ 3λ/2` and `τΨ² < κ/32`.
  rw [le_div_iff₀ hκ]
  rcases le_total 0 τ with hτnn | hτnp
  · have H1 := mul_le_mul_of_nonneg_left hreg hτnn
    nlinarith [hcurvΔ, hdualbound, H1, hτ, hκ, hlam,
      apply_nonneg dr.Φstar Δ, apply_nonneg dr.Φ Δ, subspaceLip_nonneg dr.Φ dr.Mbar]
  · have H0 : τ * dr.Φ Δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hτnp (apply_nonneg dr.Φ Δ)
    nlinarith [hcurvΔ, hdualbound, H0, hlam, apply_nonneg dr.Φstar Δ]

end StatLean.HighDimensionalStatistics.MEstimator
