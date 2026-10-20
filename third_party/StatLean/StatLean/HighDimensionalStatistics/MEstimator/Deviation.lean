module
public import StatLean.HighDimensionalStatistics.MEstimator.Defs
public import StatLean.Optimization.ForMathlib.FirstOrderConvex

@[expose] public section

/-!
# Deviation inequalities and error-cone membership

The first structural consequence of decomposability. Let $\widehat\theta$ be any minimizer of the
regularized $M$-estimator $L(\theta) + \lambda\,\Phi(\theta)$, write the error as
$\widehat\Delta = \widehat\theta - \theta^*$, and condition on the *good event*
$\mathbb{G}(\lambda) = \{\Phi^*(\nabla L(\theta^*)) \le \lambda/2\}$ (the regularizer dominates the
dual norm of the score). Then $\widehat\Delta$ lies in the cone
$$
\mathbb{C}(M, \overline{M}^{\perp}; \theta^*)
  = \bigl\{ \Delta : \Phi(\Delta_{\overline{M}^{\perp}})
      \le 3\,\Phi(\Delta_{\overline{M}}) + 4\,\Phi(\theta^*_{M^{\perp}}) \bigr\},
$$
where $\Phi$ is the decomposable regularizer and $\Phi^*$ its dual.

The engine is a pair of deviation lower bounds. The **regularizer deviation bound** is purely
geometric, following from decomposability and the triangle inequality with no convexity or good
event:
$$
\Phi(\theta^* + \Delta) - \Phi(\theta^*)
  \ge \Phi(\Delta_{\overline{M}^{\perp}}) - \Phi(\Delta_{\overline{M}})
      - 2\,\Phi(\theta^*_{M^{\perp}}).
$$
The **cost deviation bound** uses convexity and Hölder's inequality, conditioned on
$\mathbb{G}(\lambda)$:
$$
L(\theta^* + \Delta) - L(\theta^*)
  \ge -\tfrac{\lambda}{2}\bigl(\Phi(\Delta_{\overline{M}^{\perp}}) + \Phi(\Delta_{\overline{M}})\bigr).
$$
Combining these two bounds with the optimality inequality $\mathcal{F}(\widehat\Delta) \le 0$ yields
the cone membership.

All $\theta^*$ projection terms are onto $M^{\perp}$ (orthogonal complement of the model subspace
$M$), since the decomposability step
$\Phi(\theta^*_M + \Delta_{\overline{M}^{\perp}}) = \Phi(\theta^*_M) + \Phi(\Delta_{\overline{M}^{\perp}})$
requires $\theta^*_M \in M$; the $\Delta$ projections are onto $\overline{M}$ and
$\overline{M}^{\perp}$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019, Chapter 9 (Decomposability and restricted strong convexity),
§9.4, Lemma 9.14, Eq (9.32) and (9.33) (the regularizer and cost deviation lower bounds), and
Proposition 9.13 (the error $\widehat\Delta \in \mathbb{C}(M, \overline{M}^{\perp})$, cone defined
in Eq (9.29); good event Eq (9.28)/(9.46); estimator Eq (9.3)).

**Proof formalization notes.**
* `reg_deviation_lower` (Eq 9.32): project $\theta^*$ onto $(M, M^{\perp})$ and $\Delta$ onto
  $(\overline{M}, \overline{M}^{\perp})$. Writing $\theta^* + \Delta = (a + b') + (a' + b)$ with
  $a = \theta^*_M$, $b' = \Delta_{\overline{M}^{\perp}}$, the reverse triangle inequality lower-bounds
  $\Phi(\theta^* + \Delta)$, and decomposability gives the matching equality
  $\Phi(a + b') = \Phi(a) + \Phi(b')$ on the cross term. No convexity or good event used.
* `cost_deviation_lower` (Eq 9.33): first-order convexity gives
  $L(\theta^* + \Delta) - L(\theta^*) \ge \langle \nabla L(\theta^*), \Delta\rangle$; two-sided Hölder
  gives $\langle \nabla L(\theta^*), \Delta\rangle \ge -\Phi(\Delta)\,\Phi^*(\nabla L(\theta^*))$; the
  good event $\Phi^*(\nabla L(\theta^*)) \le \lambda/2$ plus nonnegativity yields the $\lambda/2$
  bound, and $\Phi(\Delta) \le \Phi(\Delta_{\overline{M}^{\perp}}) + \Phi(\Delta_{\overline{M}})$
  finishes it.
* `error_mem_cone` (Proposition 9.13): combine (9.32) scaled by $\lambda > 0$ with (9.33) and the
  optimality inequality $\mathcal{F}(\widehat\Delta) \le 0$ to obtain
  $\Phi(\widehat\Delta_{\overline{M}^{\perp}}) \le 3\,\Phi(\widehat\Delta_{\overline{M}})
  + 4\,\Phi(\theta^*_{M^{\perp}})$.

**Bibliographic comments.** These deviation bounds and the cone-membership result originate in
S. N. Negahban, P. Ravikumar, M. J. Wainwright and B. Yu, "A unified framework for high-dimensional
analysis of $M$-estimators with decomposable regularizers," *Statistical Science* 27(4) (2012),
538–557 (arXiv:1010.2731). There the cone-membership statement appears as Lemma 1: on the event
$\{\lambda_n \ge 2\,\mathcal{R}^*(\nabla \mathcal{L}(\theta^*))\}$ the error lies in the set
$\mathbb{C}(M, \overline{M}^{\perp}; \theta^*)$ — the same content as Proposition 9.13 here, modulo
the $\lambda/2$ versus $2\lambda$ normalization of the good event. Lemma 9.14 and
Proposition 9.13 present that paper's analysis in the form this file formalizes.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace
open StatLean.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lemma 9.14, eq (9.32)** — regularizer deviation lower bound. For any decomposable regularizer
and any `θ*, Δ`,
`Φ(θ* + Δ) − Φ(θ*) ≥ Φ(Δ_{M̄ᗮ}) − Φ(Δ_{M̄}) − 2·Φ(θ*_{Mᗮ})`.
Geometric: decomposability (`dr.decomp`) applied to `θ*_M` and `Δ_{M̄ᗮ}`, plus the triangle
inequality. No convexity or good event needed. -/
theorem reg_deviation_lower (dr : DecomposableReg E) (θstar Δ : E) :
    dr.Φ (θstar + Δ) - dr.Φ θstar ≥
      dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) - dr.Φ (dr.Mbar.starProjection Δ)
        - 2 * dr.Φ ((dr.M)ᗮ.starProjection θstar) := by
  -- Geometric decomposition: project `θ*` onto `(M, Mᗮ)` and `Δ` onto `(M̄, M̄ᗮ)`.
  set a := dr.M.starProjection θstar with ha_def
  set a' := (dr.M)ᗮ.starProjection θstar with ha'_def
  set b := dr.Mbar.starProjection Δ with hb_def
  set b' := (dr.Mbar)ᗮ.starProjection Δ with hb'_def
  have hθ : a + a' = θstar := dr.M.starProjection_add_starProjection_orthogonal θstar
  have hΔ : b + b' = Δ := dr.Mbar.starProjection_add_starProjection_orthogonal Δ
  have ha : a ∈ dr.M := dr.M.starProjection_apply_mem θstar
  have hb' : b' ∈ (dr.Mbar)ᗮ := (dr.Mbar)ᗮ.starProjection_apply_mem Δ
  -- `θ* + Δ = (a + b') + (a' + b)`; the reverse triangle inequality lower-bounds `Φ(θ*+Δ)`.
  have hsplit : θstar + Δ = (a + b') + (a' + b) := by rw [← hθ, ← hΔ]; abel
  have heq : (θstar + Δ) - (a' + b) = a + b' := by rw [hsplit]; abel
  have htri1 : dr.Φ (a + b') ≤ dr.Φ (θstar + Δ) + dr.Φ (a' + b) := by
    have h := map_sub_le_add dr.Φ (θstar + Δ) (a' + b)
    rwa [heq] at h
  have htri2 : dr.Φ (a' + b) ≤ dr.Φ a' + dr.Φ b := map_add_le_add dr.Φ a' b
  have hθle : dr.Φ θstar ≤ dr.Φ a + dr.Φ a' := by
    rw [← hθ]; exact map_add_le_add dr.Φ a a'
  -- Decomposability gives the matching equality on the `(M, M̄ᗮ)` cross term.
  have hdecomp : dr.Φ (a + b') = dr.Φ a + dr.Φ b' := dr.decomp a ha b' hb'
  linarith [htri1, htri2, hθle, hdecomp]

/-- **Lemma 9.14, eq (9.33)** — cost deviation lower bound. For a convex differentiable cost `L`,
conditioned on the good event `Φ*(∇L(θ*)) ≤ λ/2`,
`L(θ* + Δ) − L(θ*) ≥ −(λ/2)·(Φ(Δ_{M̄ᗮ}) + Φ(Δ_{M̄}))`.
Proof: convexity gives `L(θ*+Δ) − L(θ*) ≥ ⟨∇L(θ*), Δ⟩ ≥ −Φ*(∇L(θ*))·Φ(Δ) ≥ −(λ/2)Φ(Δ)`, then
`Φ(Δ) ≤ Φ(Δ_{M̄ᗮ}) + Φ(Δ_{M̄})`. -/
theorem cost_deviation_lower (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` is convex (A1); Wainwright §9.4.1 (A1).
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` is differentiable; Wainwright §9.3 (gradient/score well-defined).
    (hdiff : Differentiable ℝ L)
    (θstar Δ : E) (lam : ℝ)
    -- USER-INPUT: good event `𝔾(λ) = {Φ*(∇L(θ*)) ≤ λ/2}`; Wainwright eq 9.28/9.46.
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam) :
    L (θstar + Δ) - L θstar ≥
      -(lam / 2) * (dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) + dr.Φ (dr.Mbar.starProjection Δ)) := by
  set g := gradient L θstar with hg_def
  simp only [GoodEvent] at hG
  -- Convexity (first-order): `L(θ*+Δ) − L(θ*) ≥ ⟨∇L(θ*), Δ⟩`.
  have hgrad := inner_gradient_le_sub_of_convexOn hL hdiff θstar (θstar + Δ)
  rw [add_sub_cancel_left] at hgrad
  -- Hölder, both signs: `⟨g, Δ⟩ ≥ −Φ(Δ)·Φ*(g)`.
  have hh1 : ⟪Δ, g⟫_ℝ ≤ dr.Φ Δ * dr.Φstar g := dr.holder Δ g
  have hh2 : ⟪(-Δ), g⟫_ℝ ≤ dr.Φ (-Δ) * dr.Φstar g := dr.holder (-Δ) g
  rw [inner_neg_left, map_neg_eq_map] at hh2
  have hcomm : ⟪g, Δ⟫_ℝ = ⟪Δ, g⟫_ℝ := real_inner_comm Δ g
  have hlow : ⟪g, Δ⟫_ℝ ≥ -(dr.Φ Δ * dr.Φstar g) := by rw [hcomm]; linarith
  -- Good event + nonnegativity turn the Hölder bound into the `λ/2` bound.
  have hsnn : 0 ≤ dr.Φstar g := apply_nonneg dr.Φstar g
  have hpnn : 0 ≤ dr.Φ Δ := apply_nonneg dr.Φ Δ
  have hlamhalf_nn : 0 ≤ lam / 2 := le_trans hsnn hG
  have hmul1 : dr.Φ Δ * dr.Φstar g ≤ dr.Φ Δ * (lam / 2) :=
    mul_le_mul_of_nonneg_left hG hpnn
  -- `Φ(Δ) ≤ Φ(Δ_{M̄ᗮ}) + Φ(Δ_{M̄})`.
  have hΔsplit : dr.Mbar.starProjection Δ + (dr.Mbar)ᗮ.starProjection Δ = Δ :=
    dr.Mbar.starProjection_add_starProjection_orthogonal Δ
  have hΔsum : dr.Φ Δ ≤
      dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) + dr.Φ (dr.Mbar.starProjection Δ) := by
    have h := map_add_le_add dr.Φ (dr.Mbar.starProjection Δ) ((dr.Mbar)ᗮ.starProjection Δ)
    rw [hΔsplit] at h
    linarith
  have hmul2 : dr.Φ Δ * (lam / 2) ≤
      (dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) + dr.Φ (dr.Mbar.starProjection Δ)) * (lam / 2) :=
    mul_le_mul_of_nonneg_right hΔsum hlamhalf_nn
  nlinarith [hgrad, hlow, hmul1, hmul2]

/-- **Proposition 9.13** — error-cone membership. For a convex differentiable cost `L`, a decomposable
regularizer, and any optimum `θ̂` of `L + λ·Φ` (`λ > 0`), conditioned on the good event the error
`θ̂ − θ*` lies in the cone `ℂ(M, M̄ᗮ)` (eq 9.29). Immediate from Lemma 9.14: combining (9.32)+(9.33)
with `ℱ(θ̂−θ*) ≤ 0` (optimality) gives `Φ(Δ̂_{M̄ᗮ}) ≤ 3Φ(Δ̂_{M̄}) + 4Φ(θ*_{Mᗮ})`. -/
theorem error_mem_cone (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` is convex (A1); Wainwright §9.4.1 (A1).
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` is differentiable; Wainwright §9.3.
    (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam : ℝ)
    -- USER-INPUT: regularization weight `λ > 0`; Wainwright eq 9.3.
    (hlam : 0 < lam)
    -- USER-INPUT: `θ̂` minimizes the regularized objective `L + λ·Φ` (the M-estimator); Wainwright eq 9.3.
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    -- USER-INPUT: good event `𝔾(λ)`; Wainwright eq 9.28/9.46.
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam) :
    (θhat - θstar) ∈ errorCone dr θstar := by
  set Δ := θhat - θstar with hΔdef
  have hθΔ : θstar + Δ = θhat := by rw [hΔdef]; abel
  -- Optimality `ℱ(Δ) ≤ 0`, rewritten at `θ̂ = θ* + Δ`.
  have hoptΔ : L (θstar + Δ) + lam * dr.Φ (θstar + Δ) ≤ L θstar + lam * dr.Φ θstar := by
    rw [hθΔ]; exact hopt θstar
  -- The two deviation bounds of Lemma 9.14.
  have hreg := reg_deviation_lower dr θstar Δ
  have hcost := cost_deviation_lower dr L hL hdiff θstar Δ lam hG
  -- Multiply the regularizer bound by `λ > 0` so it can combine linearly with optimality.
  have hlamreg := mul_le_mul_of_nonneg_left hreg (le_of_lt hlam)
  simp only [errorCone, Set.mem_setOf_eq]
  nlinarith [hoptΔ, hcost, hlamreg, hlam]

end StatLean.HighDimensionalStatistics.MEstimator
