module
public import StatLean.HighDimensionalStatistics.MEstimator.Deviation
public import StatLean.HighDimensionalStatistics.MEstimator.SubspaceLip

@[expose] public section

/-!
# Estimation-error bounds for general M-estimators (Theorem 9.19, Corollary 9.20)

This is the central deterministic result of the decomposable-regularizer framework. Consider a
regularized M-estimator
$$ \hat\theta \in \arg\min_{\theta}\; \big\{ \mathcal{L}(\theta) + \lambda\,\Phi(\theta) \big\}, $$
where the loss $\mathcal{L}$ is convex and differentiable, $\Phi$ is a decomposable norm-like
regularizer relative to a subspace pair $(M, \overline{M})$, and $\lambda > 0$. Write
$\theta^*$ for the target, $\Delta = \hat\theta - \theta^*$ for the estimation error,
$\Psi(\overline{M})$ for the subspace-Lipschitz (compatibility) constant of $\Phi$ over
$\overline{M}$, and $\Phi(\theta^*_{M^\perp})$ for the approximation error (the regularizer of the
projection of $\theta^*$ onto $M^\perp$).

Assume that the regularization weight dominates the dual norm of the loss gradient at $\theta^*$,
i.e. the **good event** $\Phi^*(\nabla\mathcal{L}(\theta^*)) \le \lambda/2$ holds, and that
$\mathcal{L}$ satisfies **restricted strong convexity** with curvature $\kappa$, radius $R$, and
tolerance $\tau^2 \ge 0$. Then:

* **Regularizer bound (Theorem 9.19(a), Eq 9.48a).**
  $\Phi(\hat\theta - \theta^*) \le 4\big( \Psi(\overline{M})\,\|\hat\theta - \theta^*\| +
  \Phi(\theta^*_{M^\perp}) \big).$ This requires only the good event and decomposability — no
  restricted strong convexity.

* **Squared-error bound (Theorem 9.19(b), Eq 9.48b).** Provided
  $\tau^2\,\Psi^2(\overline{M}) \le \kappa/128$ and $\varepsilon_n^2 \le R^2$,
  $$ \|\hat\theta - \theta^*\|^2 \le \varepsilon_n^2 :=
  144\,\frac{\lambda^2}{\kappa^2}\,\Psi^2(\overline{M})
  + \frac{32}{\kappa}\Big( \lambda\,\Phi(\theta^*_{M^\perp})
  + 16\,\tau^2\,\Phi(\theta^*_{M^\perp})^2 \Big). $$

Specializing to $\theta^* \in M$ makes the approximation error vanish
($\Phi(\theta^*_{M^\perp}) = 0$), giving **Corollary 9.20**: the squared-error bound
$\|\hat\theta - \theta^*\|^2 \le 144\,(\lambda^2/\kappa^2)\,\Psi^2(\overline{M})$ (Eq 9.49b) and
the regularizer bound $\Phi(\hat\theta - \theta^*) \le 48\,(\lambda/\kappa)\,\Psi^2(\overline{M})$
(Eq 9.49a).

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019, Chapter 9 (Decomposability and restricted strong convexity),
§9.4, Theorem 9.19 (Eqs 9.48a–9.48b), Corollary 9.20 (Eqs 9.49a–9.49b), via Lemma 9.21
(Eqs 9.50–9.53). The restricted-strong-convexity definition is §9.4.1, Definition 9.15
(Eq 9.38); the good event is Eq 9.46.

**Proof formalization notes.**
The proof goes through Lemma 9.21 (sign control): if the objective increment $\mathcal{F}$ is
strictly positive on the sphere $\{\|\Delta\| = \delta\} \cap \mathbb{C}$, then
$\|\hat\theta - \theta^*\| \le \delta$, because the error cone $\mathbb{C}$ is star-shaped about
$0$, $\mathcal{F}$ is convex with $\mathcal{F}(0) = 0$, $\mathcal{F}(\hat\theta - \theta^*) \le 0$
(optimality), and $\hat\theta - \theta^* \in \mathbb{C}$ (Proposition 9.13). Theorem 9.19(a) is
immediate from $\hat\theta - \theta^* \in \mathbb{C}$ plus the subspace-Lipschitz bound and a
non-expansive projection. For Theorem 9.19(b), the quadratic-form argument (Eqs 9.50–9.53) shows
$\mathcal{F} > 0$ on the sphere of radius $\varepsilon_n$, and then Lemma 9.21 closes it.

*Book-vs-Lean constant deviations.* The book states slack $\tau^2\Psi^2 \le \kappa/64$ and a
leading constant $9$ in $\varepsilon_n^2$ (Eq 9.48b), and $6$ in the regularizer corollary
(Eq 9.49a). Tracking the effective curvature rigorously gives $c = \kappa/2 - 32\tau^2\Psi^2$, so
the provable conditions are $\tau^2\Psi^2 \le \kappa/128$ (ensuring $c \ge \kappa/4$) and the
inflated $\varepsilon_n^2$ constants ($144$ in place of $9$, $32/\kappa$), with $4\cdot 12 = 48$ in
place of $6$ in Corollary 9.20. These differ from the book only by fixed factors; the statistical
rate is identical. One hypothesis is also added beyond the book's wording: $0 \le \tau^2$. The
book's $\tau^2 = \tau_n^2$ is a *squared* tolerance, hence nonnegative, but the underlying
`RSC` definition leaves it an unconstrained real; the conclusion is false without
$\tau^2 \ge 0$ (a strongly-convex quadratic with $\tau^2 \to -\infty$ makes $\varepsilon_n^2 < 0$
while $\|\hat\theta - \theta^*\|^2 > 0$), so it is the missing constitutive hypothesis.

**Bibliographic comments.**
The decomposable-regularizer framework and these bounds originate with S. N. Negahban,
P. Ravikumar, M. J. Wainwright and B. Yu, "A unified framework for high-dimensional analysis of
M-estimators with decomposable regularizers," *Statistical Science*, 27(4):538–557, 2012. The
key result there is Theorem 1, which states exactly the squared-error bound $\|\hat\theta -
\theta^*\|^2 \le 9\,(\lambda^2/\kappa^2)\,\Psi^2(\overline{M}) + \ldots$ under restricted strong
convexity (their Definition 2) and the dual-norm condition $\lambda \ge 2\,\Phi^*(\nabla
\mathcal{L}(\theta^*))$. Wainwright's Theorem 9.19 / Corollary 9.20 restate that paper's
Theorem 1 and its $\theta^* \in M$ corollary; the formalization here follows Wainwright's
notation and proof.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace
open StatLean.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Star-shapedness of the error cone about `0`: if `Δ ∈ ℂ` and `0 ≤ t ≤ 1`, then `t·Δ ∈ ℂ`.
The projections are linear (`map_smul` on the `starProjection` CLM) and `Φ(t·x) = t·Φ(x)` for
`t ≥ 0`, so the defining inequality of `ℂ` is preserved (using `t·Φ(θ*_{Mᗮ}) ≤ Φ(θ*_{Mᗮ})`). -/
private lemma errorCone_smul_mem (dr : DecomposableReg E) (θstar Δ : E) {t : ℝ}
    (hΔ : Δ ∈ errorCone dr θstar) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t • Δ) ∈ errorCone dr θstar := by
  simp only [errorCone, Set.mem_setOf_eq] at hΔ ⊢
  simp only [map_smul, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hΦ0 : 0 ≤ dr.Φ ((dr.M)ᗮ.starProjection θstar) := apply_nonneg _ _
  nlinarith [mul_le_mul_of_nonneg_left hΔ ht0,
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) hΦ0]

/-- **Lemma 9.21** — sign control. If the objective increment `ℱ` (eq 9.31) is strictly positive on
the slice `𝕂(δ) = ℂ ∩ {‖Δ‖ = δ}`, then `‖θ̂ − θ*‖ ≤ δ`. Proof: contrapositive via star-shapedness of
`ℂ` about `0`, convexity of `ℱ`, `ℱ(0) = 0`, and `ℱ(θ̂−θ*) ≤ 0` (optimality), so a scaled copy
`t·(θ̂−θ*) ∈ 𝕂(δ)` would have `ℱ ≤ 0`, contradicting positivity. -/
theorem norm_error_le_of_pos_on_sphere (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` convex (A1); Wainwright §9.4.1.
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` differentiable; Wainwright §9.3.
    (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam : ℝ)
    -- USER-INPUT: regularization weight `λ > 0`; Wainwright eq 9.3.
    (hlam : 0 < lam)
    -- USER-INPUT: `θ̂` minimizes `L + λ·Φ`; Wainwright eq 9.3.
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    -- USER-INPUT: good event `𝔾(λ)`; Wainwright eq 9.46.
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam)
    {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ Δ ∈ errorCone dr θstar, ‖Δ‖ = δ → 0 < Fcal L dr.Φ θstar lam Δ) :
    ‖θhat - θstar‖ ≤ δ := by
  by_contra h
  rw [not_le] at h
  set e := θhat - θstar with hedef
  have hmem : e ∈ errorCone dr θstar :=
    error_mem_cone dr L hL hdiff θstar θhat lam hlam hopt hG
  have hθ : θstar + e = θhat := by rw [hedef]; abel
  have hF0 : Fcal L dr.Φ θstar lam e ≤ 0 := by
    have hh := hopt θstar
    simp only [Fcal, hθ]
    nlinarith [hh]
  have hnpos : 0 < ‖e‖ := lt_trans hδ h
  have hne : ‖e‖ ≠ 0 := ne_of_gt hnpos
  set t := δ / ‖e‖ with htdef
  have ht0 : 0 < t := div_pos hδ hnpos
  have ht1 : t < 1 := by rw [htdef, div_lt_one hnpos]; exact h
  have hnorm : ‖t • e‖ = δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, htdef]
    field_simp
  have hmemt : (t • e) ∈ errorCone dr θstar := errorCone_smul_mem dr θstar e hmem ht0.le ht1.le
  have hpos' := hpos (t • e) hmemt hnorm
  have hconv_id : θstar + t • e = (1 - t) • θstar + t • θhat := by
    rw [hedef]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hLconv : L ((1 - t) • θstar + t • θhat) ≤ (1 - t) * L θstar + t * L θhat := by
    have hh := hL.2 (Set.mem_univ θstar) (Set.mem_univ θhat)
      (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    simpa using hh
  have hΦconv : dr.Φ ((1 - t) • θstar + t • θhat) ≤ (1 - t) * dr.Φ θstar + t * dr.Φ θhat := by
    have hh := dr.Φ.convexOn.2 (Set.mem_univ θstar) (Set.mem_univ θhat)
      (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    simpa using hh
  have hopt0 : (L θhat - L θstar) + lam * (dr.Φ θhat - dr.Φ θstar) ≤ 0 := by
    have hh := hopt θstar; nlinarith [hh]
  have key : Fcal L dr.Φ θstar lam (t • e) ≤ 0 := by
    simp only [Fcal, hconv_id]
    nlinarith [hLconv, mul_le_mul_of_nonneg_left hΦconv hlam.le,
      mul_le_mul_of_nonneg_left hopt0 ht0.le]
  linarith [hpos', key]

/-- **Theorem 9.19(a)** — regularizer bound (eq 9.48a). Conditioned on the good event, any optimum
satisfies `Φ(θ̂ − θ*) ≤ 4·(Ψ(M̄)·‖θ̂ − θ*‖ + Φ(θ*_{Mᗮ}))`. Immediate from Proposition 9.13
(`θ̂−θ* ∈ ℂ`) + the subspace Lipschitz bound + non-expansive projection. No RSC needed. -/
theorem mestimator_reg_bound (dr : DecomposableReg E) (L : E → ℝ)
    (hL : ConvexOn ℝ Set.univ L) (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam : ℝ) (hlam : 0 < lam)
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam) :
    dr.Φ (θhat - θstar) ≤
      4 * (subspaceLip dr.Φ dr.Mbar * ‖θhat - θstar‖ + dr.Φ ((dr.M)ᗮ.starProjection θstar)) := by
  set e := θhat - θstar with hedef
  have hmem : e ∈ errorCone dr θstar :=
    error_mem_cone dr L hL hdiff θstar θhat lam hlam hopt hG
  have hcone : dr.Φ ((dr.Mbar)ᗮ.starProjection e) ≤
      3 * dr.Φ (dr.Mbar.starProjection e) + 4 * dr.Φ ((dr.M)ᗮ.starProjection θstar) := by
    have h := hmem; simp only [errorCone, Set.mem_setOf_eq] at h; exact h
  have htri : dr.Φ e ≤ dr.Φ (dr.Mbar.starProjection e) + dr.Φ ((dr.Mbar)ᗮ.starProjection e) := by
    have h := map_add_le_add dr.Φ (dr.Mbar.starProjection e) ((dr.Mbar)ᗮ.starProjection e)
    rwa [dr.Mbar.starProjection_add_starProjection_orthogonal e] at h
  have hΨb : dr.Φ (dr.Mbar.starProjection e) ≤ subspaceLip dr.Φ dr.Mbar * ‖e‖ := by
    calc dr.Φ (dr.Mbar.starProjection e)
          ≤ subspaceLip dr.Φ dr.Mbar * ‖dr.Mbar.starProjection e‖ :=
            subspaceLip_le dr.Φ dr.Mbar (dr.Mbar.starProjection_apply_mem e)
      _ ≤ subspaceLip dr.Φ dr.Mbar * ‖e‖ :=
            mul_le_mul_of_nonneg_left (dr.Mbar.norm_starProjection_apply_le e)
              (subspaceLip_nonneg dr.Φ dr.Mbar)
  nlinarith [hcone, htri, hΨb, apply_nonneg dr.Φ (dr.Mbar.starProjection e)]

set_option maxHeartbeats 800000 in -- the `nlinarith` quadratic-form certificate (`hLB` + `key*`)
-- is a fixed linear combination, but its search overruns the default heartbeat budget.
/-- **Positivity of `ℱ` on the sphere** (Wainwright eqs 9.50–9.53). Under RSC, the good event, and
the cleared threshold inequalities (`hc : c ≥ κ/4`, `hδlb : 12λΨ ≤ κδ`, `hδeps : κ²δ² ≥ …`), the
objective increment `ℱ(Δ)` is strictly positive for every `Δ ∈ ℂ` with `‖Δ‖ = δ`. The certificate
splits `c·δ²` into thirds (`κ/4 = κ/8 + κ/16 + κ/16`), absorbing the linear `Ψδ` term and the
approximation-error term `2λΦ₀ + 32τ²Φ₀²`, leaving a strict `(κ/16)δ² > 0` margin. Requires
`0 ≤ τ²` so the `−τ²(ΦΔ)²` term can be bounded by `−τ²(32Ψ²δ² + 32Φ₀²)`. -/
private lemma fcal_pos_on_sphere (dr : DecomposableReg E) (L : E → ℝ)
    (θstar : E) (lam κ R τSq : ℝ) (hlam : 0 < lam) (hκ : 0 < κ) (hτSq : 0 ≤ τSq)
    (hRSC : RSC L θstar dr.Φ κ R τSq)
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam)
    (hc : κ / 4 ≤ κ / 2 - 32 * τSq * (subspaceLip dr.Φ dr.Mbar) ^ 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδR : δ ≤ R)
    (hδlb : 12 * lam * subspaceLip dr.Φ dr.Mbar ≤ κ * δ)
    (hδeps : 144 * lam ^ 2 * (subspaceLip dr.Φ dr.Mbar) ^ 2
        + 32 * κ * (lam * dr.Φ ((dr.M)ᗮ.starProjection θstar)
          + 16 * τSq * (dr.Φ ((dr.M)ᗮ.starProjection θstar)) ^ 2) ≤ κ ^ 2 * δ ^ 2)
    {Δ : E} (hΔcone : Δ ∈ errorCone dr θstar) (hΔnorm : ‖Δ‖ = δ) :
    0 < Fcal L dr.Φ θstar lam Δ := by
  set Ψ := subspaceLip dr.Φ dr.Mbar with hΨdef
  set Φ0 := dr.Φ ((dr.M)ᗮ.starProjection θstar) with hΦ0def
  set Δb := dr.Mbar.starProjection Δ with hΔbdef
  set Δb' := (dr.Mbar)ᗮ.starProjection Δ with hΔb'def
  have hΨ0 : 0 ≤ Ψ := subspaceLip_nonneg dr.Φ dr.Mbar
  have hΦ0nn : 0 ≤ Φ0 := apply_nonneg _ _
  have hΦΔnn : 0 ≤ dr.Φ Δ := apply_nonneg _ _
  have hΦb'nn : 0 ≤ dr.Φ Δb' := apply_nonneg _ _
  -- RSC at Δ (‖Δ‖ = δ ≤ R)
  have hRSCΔ : taylorErr L θstar Δ ≥ κ / 2 * δ ^ 2 - τSq * (dr.Φ Δ) ^ 2 := by
    have h := hRSC Δ (by rw [hΔnorm]; exact hδR)
    rwa [hΔnorm] at h
  -- gradient bound: ⟪g, Δ⟫ ≥ -(λ/2)·Φ(Δ)
  have hg : ⟪gradient L θstar, Δ⟫_ℝ ≥ -(lam / 2) * dr.Φ Δ := by
    have hh2 : ⟪(-Δ), gradient L θstar⟫_ℝ ≤ dr.Φ (-Δ) * dr.Φstar (gradient L θstar) :=
      dr.holder (-Δ) _
    rw [inner_neg_left, map_neg_eq_map] at hh2
    have hGle : dr.Φstar (gradient L θstar) ≤ lam / 2 := hG
    have hm := mul_le_mul_of_nonneg_left hGle hΦΔnn
    have hcomm : ⟪gradient L θstar, Δ⟫_ℝ = ⟪Δ, gradient L θstar⟫_ℝ := real_inner_comm _ _
    nlinarith [hh2, hm, hcomm]
  -- regularizer deviation (eq 9.32), scaled by λ
  have hreg := reg_deviation_lower dr θstar Δ
  have hlamreg : lam * (dr.Φ Δb' - dr.Φ Δb - 2 * Φ0)
      ≤ lam * (dr.Φ (θstar + Δ) - dr.Φ θstar) :=
    mul_le_mul_of_nonneg_left hreg hlam.le
  -- triangle, cone, subspace-Lipschitz
  have htri : dr.Φ Δ ≤ dr.Φ Δb + dr.Φ Δb' := by
    have h := map_add_le_add dr.Φ Δb Δb'
    rwa [dr.Mbar.starProjection_add_starProjection_orthogonal Δ] at h
  have hΨb : dr.Φ Δb ≤ Ψ * δ := by
    calc dr.Φ Δb ≤ Ψ * ‖Δb‖ :=
          subspaceLip_le dr.Φ dr.Mbar (dr.Mbar.starProjection_apply_mem Δ)
      _ ≤ Ψ * δ := by
          rw [← hΔnorm]
          exact mul_le_mul_of_nonneg_left (dr.Mbar.norm_starProjection_apply_le Δ) hΨ0
  have hcone : dr.Φ Δb' ≤ 3 * dr.Φ Δb + 4 * Φ0 := by
    have h := hΔcone; simp only [errorCone, Set.mem_setOf_eq] at h; exact h
  -- Φ(Δ) ≤ 4Ψδ + 4Φ₀, hence (Φ Δ)² ≤ 32(Ψδ)² + 32Φ₀²
  have hΦΔub : dr.Φ Δ ≤ 4 * (Ψ * δ) + 4 * Φ0 := by nlinarith [htri, hcone, hΨb]
  have hΦΔsq : (dr.Φ Δ) ^ 2 ≤ 32 * (Ψ * δ) ^ 2 + 32 * Φ0 ^ 2 := by
    have hsum : 0 ≤ 4 * (Ψ * δ) + 4 * Φ0 + dr.Φ Δ := by
      have : 0 ≤ Ψ * δ := mul_nonneg hΨ0 hδ0.le
      linarith [hΦΔnn, hΦ0nn]
    nlinarith [mul_nonneg (sub_nonneg.mpr hΦΔub) hsum, sq_nonneg (Ψ * δ - Φ0)]
  -- ℱ(Δ) = taylorErr + ⟪g,Δ⟫ + λ·(Φ(θ*+Δ) − Φ(θ*))
  have hFcal_eq : Fcal L dr.Φ θstar lam Δ
      = taylorErr L θstar Δ + ⟪gradient L θstar, Δ⟫_ℝ
        + lam * (dr.Φ (θstar + Δ) - dr.Φ θstar) := by
    simp only [Fcal, taylorErr]; ring
  -- Assemble: ℱ(Δ) ≥ c·δ² − (3λ/2)Ψδ − (2λΦ₀ + 32τ²Φ₀²)
  have hLB : Fcal L dr.Φ θstar lam Δ
      ≥ (κ / 2 - 32 * τSq * Ψ ^ 2) * δ ^ 2 - 3 * lam / 2 * (Ψ * δ)
        - (2 * lam * Φ0 + 32 * τSq * Φ0 ^ 2) := by
    have htriT : lam / 2 * (dr.Φ Δb + dr.Φ Δb' - dr.Φ Δ) ≥ 0 :=
      mul_nonneg (by linarith) (by linarith [htri])
    have hPsibT : 3 * lam / 2 * (Ψ * δ - dr.Φ Δb) ≥ 0 :=
      mul_nonneg (by linarith) (by linarith [hΨb])
    have htsqT : τSq * (32 * (Ψ * δ) ^ 2 + 32 * Φ0 ^ 2 - (dr.Φ Δ) ^ 2) ≥ 0 :=
      mul_nonneg hτSq (by linarith [hΦΔsq])
    have hbpT : lam * dr.Φ Δb' ≥ 0 := mul_nonneg hlam.le hΦb'nn
    -- First a linear combination of the three deviation bounds (atoms match syntactically).
    have step1 : Fcal L dr.Φ θstar lam Δ
        ≥ (κ / 2 * δ ^ 2 - τSq * (dr.Φ Δ) ^ 2) + -(lam / 2) * dr.Φ Δ
          + lam * (dr.Φ Δb' - dr.Φ Δb - 2 * Φ0) := by
      rw [hFcal_eq]; linarith [hRSCΔ, hg, hlamreg]
    -- Then bound the remaining terms; the four slack facts give the certificate (ring-normalized).
    nlinarith [step1, htriT, hPsibT, htsqT, hbpT]
  -- Cleared threshold bounds, then a strict (κ/16)δ² margin.
  have key1 : 3 * lam / 2 * (Ψ * δ) ≤ κ / 8 * δ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hδlb hδ0.le]
  have key2 : 2 * lam * Φ0 + 32 * τSq * Φ0 ^ 2 ≤ κ / 16 * δ ^ 2 := by
    have h144 : (0:ℝ) ≤ 144 * lam ^ 2 * Ψ ^ 2 := by positivity
    have hmul : κ * (2 * lam * Φ0 + 32 * τSq * Φ0 ^ 2) ≤ κ * (κ / 16 * δ ^ 2) := by
      nlinarith [hδeps, h144]
    exact le_of_mul_le_mul_left hmul hκ
  have key3 : κ / 4 * δ ^ 2 ≤ (κ / 2 - 32 * τSq * Ψ ^ 2) * δ ^ 2 := by
    nlinarith [hc, mul_pos hδ0 hδ0]
  nlinarith [hLB, key1, key2, key3, mul_pos hκ (mul_pos hδ0 hδ0)]

/-- **Theorem 9.19(b)** — squared-error bound (eq 9.48b). Under RSC `(κ, R, τ²)`, conditioned on the
good event, and provided `τ²·Ψ²(M̄) ≤ κ/128` and `εₙ² ≤ R²`, any optimum satisfies
`‖θ̂ − θ*‖² ≤ εₙ²(M̄, Mᗮ)`. Proof: the quadratic-form argument (eqs 9.50–9.53) shows `ℱ > 0` on the
sphere of radius `εₙ`, then Lemma 9.21 applies.

Book-constant deviation: the book uses slack `τ²Ψ² ≤ κ/64` and `εₙ²` with leading `9`; rigorously
the effective curvature is `c = κ/2 − 32τ²Ψ²`, so `κ/128` (giving `c ≥ κ/4`) and the inflated `εₙ²`
constants (`144`, `32/κ`, see `epsilonSq`) are what is provable. Same rate.

Hypothesis note (`hτSq`): the book's `τ² = τ_n²` is a *squared* tolerance, hence `≥ 0`; the original
`Defs.RSC` stub left `τSq` an unconstrained real. The conclusion is **false** without `0 ≤ τSq` (a
strongly-convex quadratic with `τ² → −∞` makes `εₙ² < 0` while `‖θ̂−θ*‖² > 0`, satisfying RSC, the
good event, `hτ`, and `hεR`), so `hτSq` is the missing constitutive hypothesis, added here. -/
theorem mestimator_l2_bound (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` convex (A1); Wainwright §9.4.1.
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` differentiable; Wainwright §9.3.
    (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam κ R τSq : ℝ)
    (hlam : 0 < lam) (hκ : 0 < κ) (hR : 0 < R)
    -- USER-INPUT: restricted strong convexity `(κ, R, τ²)` (A1, Def 9.15); Wainwright eq 9.38.
    (hRSC : RSC L θstar dr.Φ κ R τSq)
    -- USER-INPUT: `θ̂` minimizes `L + λ·Φ`; Wainwright eq 9.3.
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    -- USER-INPUT: good event `𝔾(λ)`; Wainwright eq 9.46.
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam)
    -- USER-INPUT: squared tolerance `τ² = τ_n² ≥ 0` (constitutive, Def 9.15); Wainwright eq 9.38.
    (hτSq : 0 ≤ τSq)
    -- USER-INPUT: curvature dominates tolerance, `τ²Ψ²(M̄) ≤ κ/128`; Wainwright Thm 9.19(b).
    (hτ : τSq * (subspaceLip dr.Φ dr.Mbar) ^ 2 ≤ κ / 128)
    -- USER-INPUT: `εₙ ≤ R` so the RSC ball contains the error; Wainwright Thm 9.19(b).
    (hεR : epsilonSq dr θstar lam κ τSq ≤ R ^ 2) :
    ‖θhat - θstar‖ ^ 2 ≤ epsilonSq dr θstar lam κ τSq := by
  set Ψ := subspaceLip dr.Φ dr.Mbar with hΨdef
  set Φ0 := dr.Φ ((dr.M)ᗮ.starProjection θstar) with hΦ0def
  have hΨ0 : 0 ≤ Ψ := subspaceLip_nonneg dr.Φ dr.Mbar
  have hΦ0nn : 0 ≤ Φ0 := apply_nonneg _ _
  have hbr : 0 ≤ lam * Φ0 + 16 * τSq * Φ0 ^ 2 :=
    add_nonneg (mul_nonneg hlam.le hΦ0nn)
      (mul_nonneg (mul_nonneg (by norm_num) hτSq) (sq_nonneg _))
  have hc : κ / 4 ≤ κ / 2 - 32 * τSq * Ψ ^ 2 := by nlinarith [hτ]
  have h1 : 0 ≤ 144 * (lam ^ 2 / κ ^ 2) * Ψ ^ 2 := by positivity
  have h2 : 0 ≤ 32 / κ * (lam * Φ0 + 16 * τSq * Φ0 ^ 2) :=
    mul_nonneg (div_nonneg (by norm_num) hκ.le) hbr
  have heps_nn : 0 ≤ epsilonSq dr θstar lam κ τSq := by
    simp only [epsilonSq, ← hΨdef, ← hΦ0def]; linarith
  rcases eq_or_lt_of_le heps_nn with hdeg | hpos_eps
  · -- Degenerate case `εₙ² = 0`: forces `Ψ = 0` and `Φ₀ = 0`, so `θ̂ = θ*`.
    have heps0 : epsilonSq dr θstar lam κ τSq = 0 := hdeg.symm
    have hsum0 : 144 * (lam ^ 2 / κ ^ 2) * Ψ ^ 2
        + 32 / κ * (lam * Φ0 + 16 * τSq * Φ0 ^ 2) = 0 := by
      have h := heps0; simp only [epsilonSq, ← hΨdef, ← hΦ0def] at h; linarith [h]
    have hΨ0' : Ψ = 0 := by
      have hpos144 : 0 < 144 * (lam ^ 2 / κ ^ 2) := by positivity
      have hzero : 144 * (lam ^ 2 / κ ^ 2) * Ψ ^ 2 = 0 := by linarith
      have hsq : Ψ ^ 2 = 0 := by
        rcases mul_eq_zero.mp hzero with h | h
        · exact absurd h (ne_of_gt hpos144)
        · exact h
      exact (pow_eq_zero_iff (by norm_num)).mp hsq
    have hΦ0' : Φ0 = 0 := by
      have hpos32 : 0 < 32 / κ := by positivity
      have hzero : 32 / κ * (lam * Φ0 + 16 * τSq * Φ0 ^ 2) = 0 := by linarith
      have hbrk : lam * Φ0 + 16 * τSq * Φ0 ^ 2 = 0 := by
        rcases mul_eq_zero.mp hzero with h | h
        · exact absurd h (ne_of_gt hpos32)
        · exact h
      have h16 : 0 ≤ 16 * τSq * Φ0 ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) hτSq) (sq_nonneg _)
      have hlamPhi : lam * Φ0 = 0 := by
        have hlamPhinn : 0 ≤ lam * Φ0 := mul_nonneg hlam.le hΦ0nn
        linarith
      rcases mul_eq_zero.mp hlamPhi with h | h
      · exact absurd h (ne_of_gt hlam)
      · exact h
    have hsphere0 : ∀ {δ' : ℝ}, 0 < δ' → δ' ≤ R → ∀ Δ ∈ errorCone dr θstar, ‖Δ‖ = δ'
        → 0 < Fcal L dr.Φ θstar lam Δ := by
      intro δ' hδ'0 hδ'R Δ hΔc hΔn
      refine fcal_pos_on_sphere dr L θstar lam κ R τSq hlam hκ hτSq hRSC hG hc
        hδ'0 hδ'R ?_ ?_ hΔc hΔn
      · rw [← hΨdef, hΨ0']; simp only [mul_zero]; positivity
      · rw [← hΨdef, ← hΦ0def, hΨ0', hΦ0']; ring_nf; positivity
    have hle0 : ‖θhat - θstar‖ ≤ 0 := by
      by_contra hgt
      rw [not_le] at hgt
      have hd : (0:ℝ) < min (‖θhat - θstar‖ / 2) R := lt_min (by linarith) hR
      have hk : ‖θhat - θstar‖ ≤ min (‖θhat - θstar‖ / 2) R :=
        norm_error_le_of_pos_on_sphere dr L hL hdiff θstar θhat lam hlam hopt hG hd
          (fun Δ hΔc hΔn => hsphere0 hd (min_le_right _ _) Δ hΔc hΔn)
      have : ‖θhat - θstar‖ ≤ ‖θhat - θstar‖ / 2 := le_trans hk (min_le_left _ _)
      linarith
    rw [heps0]
    nlinarith [hle0, norm_nonneg (θhat - θstar)]
  · -- Main case `εₙ² > 0`: take `δ = √εₙ²` and apply Lemma 9.21.
    set δ := Real.sqrt (epsilonSq dr θstar lam κ τSq) with hδdef
    have hδsq : δ ^ 2 = epsilonSq dr θstar lam κ τSq := Real.sq_sqrt heps_nn
    have hδpos : 0 < δ := Real.sqrt_pos.mpr hpos_eps
    have hδR : δ ≤ R := by
      rw [hδdef]
      calc Real.sqrt (epsilonSq dr θstar lam κ τSq) ≤ Real.sqrt (R ^ 2) :=
            Real.sqrt_le_sqrt hεR
        _ = R := Real.sqrt_sq hR.le
    -- Cleared thresholds: `12λΨ ≤ κδ` and `κ²δ² ≥ 144λ²Ψ² + 32κ(λΦ₀ + 16τ²Φ₀²)`.
    have hδeps : 144 * lam ^ 2 * Ψ ^ 2
        + 32 * κ * (lam * Φ0 + 16 * τSq * Φ0 ^ 2) ≤ κ ^ 2 * δ ^ 2 := by
      rw [hδsq]
      have heq : κ ^ 2 * epsilonSq dr θstar lam κ τSq
          = 144 * lam ^ 2 * Ψ ^ 2 + 32 * κ * (lam * Φ0 + 16 * τSq * Φ0 ^ 2) := by
        simp only [epsilonSq, ← hΨdef, ← hΦ0def]; field_simp
      linarith [heq]
    have hδlb : 12 * lam * Ψ ≤ κ * δ := by
      have hnn2 : 0 ≤ 32 * κ * (lam * Φ0 + 16 * τSq * Φ0 ^ 2) :=
        mul_nonneg (mul_nonneg (by norm_num) hκ.le) hbr
      have hsq : (12 * lam * Ψ) ^ 2 ≤ (κ * δ) ^ 2 := by nlinarith [hδeps, hnn2]
      have h12 : 0 ≤ 12 * lam * Ψ := mul_nonneg (mul_nonneg (by norm_num) hlam.le) hΨ0
      have hκδ : 0 ≤ κ * δ := mul_nonneg hκ.le hδpos.le
      calc 12 * lam * Ψ = Real.sqrt ((12 * lam * Ψ) ^ 2) := (Real.sqrt_sq h12).symm
        _ ≤ Real.sqrt ((κ * δ) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = κ * δ := Real.sqrt_sq hκδ
    have hbound : ‖θhat - θstar‖ ≤ δ :=
      norm_error_le_of_pos_on_sphere dr L hL hdiff θstar θhat lam hlam hopt hG hδpos
        (fun Δ hΔc hΔn => fcal_pos_on_sphere dr L θstar lam κ R τSq hlam hκ hτSq
          hRSC hG hc hδpos hδR hδlb hδeps hΔc hΔn)
    rw [← hδsq]
    nlinarith [hbound, norm_nonneg (θhat - θstar)]

/-- **Corollary 9.20**, eq (9.49b) — squared-error bound when `θ* ∈ M`. The approximation error
vanishes (`θ*_{Mᗮ} = 0`), so `‖θ̂ − θ*‖² ≤ 144(λ²/κ²)·Ψ²(M̄)` (= `epsilonSq` with `Φ(θ*_{Mᗮ}) = 0`,
i.e. Theorem 9.19(b) specialized). Book: leading `9`; provable inflated constant, same rate. -/
theorem cor_l2_bound_of_mem (dr : DecomposableReg E) (L : E → ℝ)
    (hL : ConvexOn ℝ Set.univ L) (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam κ R τSq : ℝ)
    (hlam : 0 < lam) (hκ : 0 < κ) (hR : 0 < R)
    (hRSC : RSC L θstar dr.Φ κ R τSq)
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam)
    -- USER-INPUT: squared tolerance `τ² = τ_n² ≥ 0` (constitutive, Def 9.15); Wainwright eq 9.38.
    (hτSq : 0 ≤ τSq)
    (hτ : τSq * (subspaceLip dr.Φ dr.Mbar) ^ 2 ≤ κ / 128)
    (hεR : epsilonSq dr θstar lam κ τSq ≤ R ^ 2)
    -- USER-INPUT: target lies in the model subspace `θ* ∈ M`; Wainwright Cor 9.20.
    (hmem : θstar ∈ dr.M) :
    ‖θhat - θstar‖ ^ 2 ≤ 144 * (lam ^ 2 / κ ^ 2) * (subspaceLip dr.Φ dr.Mbar) ^ 2 := by
  have hΦ0 : (dr.M)ᗮ.starProjection θstar = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (dr.M.le_orthogonal_orthogonal hmem)
  have hb := mestimator_l2_bound dr L hL hdiff θstar θhat lam κ R τSq hlam hκ hR hRSC hopt hG
    hτSq hτ hεR
  have heq : epsilonSq dr θstar lam κ τSq
      = 144 * (lam ^ 2 / κ ^ 2) * (subspaceLip dr.Φ dr.Mbar) ^ 2 := by
    simp only [epsilonSq, hΦ0, map_zero]; ring
  rw [heq] at hb; exact hb

/-- **Corollary 9.20**, eq (9.49a) — regularizer bound when `θ* ∈ M`:
`Φ(θ̂ − θ*) ≤ 48(λ/κ)·Ψ²(M̄)`. From (9.48a) `Φ(θ̂−θ*) ≤ 4Ψ‖θ̂−θ*‖` (θ*∈M) and
`‖θ̂−θ*‖ ≤ 12(λ/κ)Ψ` (from 9.49b, `√144 = 12`). (Book: `6`; rigorous `4·12 = 48`. Same rate.) -/
theorem cor_reg_bound_of_mem (dr : DecomposableReg E) (L : E → ℝ)
    (hL : ConvexOn ℝ Set.univ L) (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam κ R τSq : ℝ)
    (hlam : 0 < lam) (hκ : 0 < κ) (hR : 0 < R)
    (hRSC : RSC L θstar dr.Φ κ R τSq)
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam)
    -- USER-INPUT: squared tolerance `τ² = τ_n² ≥ 0` (constitutive, Def 9.15); Wainwright eq 9.38.
    (hτSq : 0 ≤ τSq)
    (hτ : τSq * (subspaceLip dr.Φ dr.Mbar) ^ 2 ≤ κ / 128)
    (hεR : epsilonSq dr θstar lam κ τSq ≤ R ^ 2)
    (hmem : θstar ∈ dr.M) :
    dr.Φ (θhat - θstar) ≤ 48 * (lam / κ) * (subspaceLip dr.Φ dr.Mbar) ^ 2 := by
  have hΦ0 : (dr.M)ᗮ.starProjection θstar = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (dr.M.le_orthogonal_orthogonal hmem)
  have hreg := mestimator_reg_bound dr L hL hdiff θstar θhat lam hlam hopt hG
  rw [hΦ0, map_zero] at hreg
  have hl2 := cor_l2_bound_of_mem dr L hL hdiff θstar θhat lam κ R τSq hlam hκ hR hRSC hopt hG
    hτSq hτ hεR hmem
  set Ψ := subspaceLip dr.Φ dr.Mbar with hΨdef
  have hΨ0 : 0 ≤ Ψ := subspaceLip_nonneg dr.Φ dr.Mbar
  have hnn : 0 ≤ ‖θhat - θstar‖ := norm_nonneg _
  have hnormle : ‖θhat - θstar‖ ≤ 12 * (lam / κ) * Ψ := by
    have h12 : 0 ≤ 12 * (lam / κ) * Ψ :=
      mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hlam.le hκ.le)) hΨ0
    have hsq : ‖θhat - θstar‖ ^ 2 ≤ (12 * (lam / κ) * Ψ) ^ 2 := by
      calc ‖θhat - θstar‖ ^ 2 ≤ 144 * (lam ^ 2 / κ ^ 2) * Ψ ^ 2 := hl2
        _ = (12 * (lam / κ) * Ψ) ^ 2 := by ring
    calc ‖θhat - θstar‖ = Real.sqrt (‖θhat - θstar‖ ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((12 * (lam / κ) * Ψ) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 12 * (lam / κ) * Ψ := Real.sqrt_sq h12
  calc dr.Φ (θhat - θstar) ≤ 4 * (Ψ * ‖θhat - θstar‖ + 0) := hreg
    _ = 4 * Ψ * ‖θhat - θstar‖ := by ring
    _ ≤ 4 * Ψ * (12 * (lam / κ) * Ψ) :=
        mul_le_mul_of_nonneg_left hnormle (mul_nonneg (by norm_num) hΨ0)
    _ = 48 * (lam / κ) * Ψ ^ 2 := by ring

end StatLean.HighDimensionalStatistics.MEstimator
