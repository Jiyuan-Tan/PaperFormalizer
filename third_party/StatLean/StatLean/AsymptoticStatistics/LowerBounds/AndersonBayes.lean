module
public import StatLean.AsymptoticStatistics.ForMathlib.Anderson
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import StatLean.AsymptoticStatistics.Experiment.GaussianShiftMinimax

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Anderson–Bayes inequality for the Gaussian shift experiment

Consider the Gaussian shift experiment: a parameter $h \in \mathbb{R}^m$ is
endowed with the prior $N(0, \tau^2 I_m)$, and conditionally on $h$ the data are
$\Delta \sim N(h, I_m)$. Let $A$ be a $1 \times m$ matrix defining the scalar
estimation target $Ah$, and let $L$ be any *bowl-shaped* loss on $\mathbb{R}$
(nonnegative, symmetric about the origin, with convex sublevel sets). Then for
every measurable estimator $T = T(\Delta)$, the Bayes risk of the optimal
posterior-mean estimator is a lower bound for the Bayes risk of $T$:
$$
  \int L(y)\, dN\!\big(0,\, A\,\Sigma_\tau\, A^{\top}\big)(y)
    \;\le\;
  \int\!\!\int
    \exp\!\Big(\langle h, \Delta\rangle - \tfrac12\|h\|^2\Big)\,
    L\big(T(\Delta) - Ah\big)\,
    dN(0, \tau^2 I_m)(h)\, dN(0, I_m)(\Delta),
$$
where $\Sigma_\tau = (I_m + \tau^{-2} I_m)^{-1}$ is the posterior covariance of
$h$ given $\Delta$ (here the posterior covariance of the family `posteriorCov`),
and the weight $\exp(\langle h, \Delta\rangle - \tfrac12\|h\|^2)$ is the
likelihood ratio $dN(h, I_m)/dN(0, I_m)$, which lets the data integral be taken
against the fixed reference measure $N(0, I_m)$ rather than against the
parameter-dependent law $N(h, I_m)$. The left-hand side is exactly the Bayes
risk attained by the posterior-mean estimator $T_*$, whose error
$T_*(\Delta) - Ah$ is centered Gaussian with covariance $A\,\Sigma_\tau A^{\top}$
and is independent of $\Delta$ (the projection/innovations property). This is
the foundational fact that the posterior mean is Bayes-optimal for bowl-shaped
losses on Gaussian shift experiments.

The headline declaration is `anderson_bayes_inequality_gaussian_shift`; the
specialization to the constant zero estimator $T \equiv 0$ is
`anderson_bayes_inequality_gaussian_shift_at_zero`.

*Alignment with the Lean statement.* The formalization fixes the base
noise/prior covariance to the identity $I_m$ (the book's matrix $J$ is taken to
be $J = I_m$) and the target dimension to one ($A$ is $1 \times m$, so $Ah$ is a
scalar). No book constants are changed; the LaTeX above matches the Lean
`multivariateGaussian`/`posteriorCov` data verbatim.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 8 (Efficiency of Estimators), §8.4 (Estimating Normal Means) — the
normal-means Bayes/minimax argument — invoking Anderson's Lemma 8.5 (stated in
§8.4, Estimating Normal Means).

**Proof formalization notes.** The proof of the general (arbitrary-$T$) version
`anderson_bayes_inequality_gaussian_shift` has two main ingredients:

1. **Tower + change-of-measure**: Tonelli (swap the inner/outer integrals) plus
   the change-of-measure identity
   $\int \exp(\langle h, \Delta\rangle - \tfrac12\|h\|^2)\, F(\Delta)\,
   dN(0, I_m)(\Delta) = \int F(\Delta)\, dN(h, I_m)(\Delta)$
   (the Radon–Nikodym derivative property of the Gaussian shift, supplied by
   `multivariateGaussian_withDensity_exp_shift`).

2. **Anderson optimality**: for the Gaussian conditional $h \mid \Delta$, the
   posterior-mean error $T_*(\Delta) - Ah$ is Gaussian
   $N(0,\, A\,\Sigma_\tau A^{\top})$ and independent of $\Delta$ (projection
   property). The innovations representation
   `GaussianShiftMinimax.gaussianShift_innovations_repr` exposes this split, and
   the pushforward through $A$ (`multivariateGaussian_map_rectangular`) followed
   by `anderson_lemma_loss` (the loss form of Anderson's lemma, shifting by the
   data-dependent center) yields the stated lower bound for every measurable
   $T$.

The companion `anderson_bayes_inequality_gaussian_shift_at_zero` ($T \equiv 0$)
bypasses the Gaussian-conditional machinery and uses only bowl symmetry, the
Gaussian MGF-tilt identity (`gaussian_mgf_tilt_eq_one`), the rectangular
pushforward, and Anderson PSD-monotonicity
(`gaussian_lintegral_mono_of_psd_le`) from $\Sigma_\tau \preceq \tau^2 I_m$; its
five-step outline and named sub-lemmas (`bowl_at_zero_simplify`,
`mvgaussian_pushforward_at_zero`, `posteriorCov_le_tausq_after_conjugate`, …)
are documented in the section comment preceding that theorem.

**Bibliographic comments.** Anderson's lemma is T. W. Anderson, "The integral of
a symmetric unimodal function over a symmetric convex set and some probability
inequalities," *Proceedings of the American Mathematical Society* **6** (1955),
170–176 (DOI 10.1090/S0002-9939-1955-0069229-1). Its main theorem and corollaries
give, for a centered Gaussian $\nu$ and a symmetric convex set $C$, the
translate inequality $\nu(C - y) \le \nu(C)$ for all $y$ — equivalently
$\int L\, d\nu \le \int L(\cdot + y)\, d\nu$ for every bowl-shaped $L$. The
Bayes-risk / posterior-mean optimality packaging for the Gaussian shift (limit)
experiment, and the resulting convolution and local asymptotic minimax theorems,
are due to J. Hájek ("A characterization of limiting distributions of regular
estimates," *Z. Wahrscheinlichkeitstheorie verw. Gebiete* **14** (1970),
323–330; "Local asymptotic minimax and admissibility in estimation," *Proc.
Sixth Berkeley Symp. Math. Statist. Probab.* **1** (1972), 175–194) and L. Le
Cam; see vdV §8.5–8.7. The specific name "Anderson–Bayes inequality" used here
is van der Vaart's textbook synthesis of Anderson's lemma with the Bayes-risk
optimality argument rather than a single separately titled theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics

namespace AndersonBayes

variable {m : ℕ}

/-- **Anderson-Bayes inequality (lintegral form, abstract).**

For the Gaussian shift experiment with prior `N(0, τ²·I_m)` on parameter
`h` and data `Δ ~ N(h, I_m)`, target `Aθ ∈ ℝ` (1-dimensional), and any
measurable estimator `T : ℝ^m → ℝ`, the Bayes risk under the prior is
bounded above by the per-`T` LR-form integral.

**Statement** (in matrix form):
```
∫⁻ y, L y ∂(multivariateGaussian 0 (A · posteriorCov 1 τ · Aᵀ))
  ≤ ∫⁻ Δ, ∫⁻ h, ENNReal.ofReal (exp (⟪h, Δ⟫ - ½‖h‖²)) ·
        L (fun _ : Fin 1 => T Δ - (A * Matrix.col Unit h) 0 0)
      ∂(multivariateGaussian 0 ((τ^2) • (1 : Matrix _ _ ℝ)))
      ∂(multivariateGaussian 0 (1 : Matrix _ _ ℝ))
```

where `posteriorCov 1 τ = (1 + τ⁻²·I)⁻¹` is the posterior covariance of the
parameter under the Gaussian shift experiment with prior `N(0, τ²·I)`.

**Proof outline**:
1. By definition `bayesRiskAtTau τ = ∫⁻ y, L y ∂N(0, A · posteriorCov · Aᵀ)`
   (LHS).
2. Identify the LHS as `E[L(T_*(Δ) - Ah)]` for the optimal posterior-mean
   estimator `T_*`. Uses linear-Gaussian conditional Bayesian theory.
3. By projection independence, `T_*(Δ) - Ah ⊥ Δ` under the joint distribution.
4. By `anderson_lemma_independent`, `E[L(X)] ≤ E[L(X + Z)]` for `X = T_*(Δ) - Ah`
   centered Gaussian and `Z = T(Δ) - T_*(Δ)` independent of `X` (since
   `Z` is `σ(Δ)`-measurable and `Δ ⊥ X`).
5. `E[L(X + Z)] = E[L(T(Δ) - Ah)] = `LR-form RHS by change-of-measure (Tonelli
   + Gaussian shift Radon-Nikodym derivative). -/
theorem anderson_bayes_inequality_gaussian_shift
    (A : Matrix (Fin 1) (Fin m) ℝ)
    (L : EuclideanSpace ℝ (Fin 1) → ℝ≥0∞) (hL : BowlShaped L)
    {τ : ℝ} (hτ : 0 < τ)
    (T : EuclideanSpace ℝ (Fin m) → ℝ) (hT : Measurable T) :
    ∫⁻ y : EuclideanSpace ℝ (Fin 1), L y
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
            (A * GaussianShiftMinimax.posteriorCov
                (1 : Matrix (Fin m) (Fin m) ℝ) τ * A.transpose))
      ≤ ∫⁻ Δ : EuclideanSpace ℝ (Fin m),
          ∫⁻ h : EuclideanSpace ℝ (Fin m),
              ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ - (1/2 : ℝ) * ‖h‖ ^ 2))
                * L ((EuclideanSpace.equiv (Fin 1) ℝ).symm
                    (fun _ : Fin 1 => T Δ - ∑ k : Fin m, A 0 k * h k))
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
                ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)))
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
              (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  classical
  -- Notation.
  set ρ : Matrix (Fin m) (Fin m) ℝ := GaussianShiftMinimax.posteriorCov 1 τ with hρ_def
  set Sy : Matrix (Fin 1) (Fin 1) ℝ := A * ρ * A.transpose with hSy_def
  set N_y : Measure (EuclideanSpace ℝ (Fin 1)) :=
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) Sy with hNy_def
  set π_τ : Measure (EuclideanSpace ℝ (Fin m)) :=
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)) with hπτ_def
  set N_Δ : Measure (EuclideanSpace ℝ (Fin m)) :=
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (1 : Matrix (Fin m) (Fin m) ℝ) with hNΔ_def
  -- Bowl-shape gives L measurable + symmetric.
  have hL_meas := hL.measurable
  -- PosSemidef facts.
  have hτsq_pos : (0 : ℝ) < τ ^ 2 := by positivity
  have h_τsq_one_psd : ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
    Matrix.PosDef.one.posSemidef.smul hτsq_pos.le
  have h_one_psd : (1 : Matrix (Fin m) (Fin m) ℝ).PosSemidef :=
    Matrix.PosDef.one.posSemidef
  have h_ρ_posDef : ρ.PosDef :=
    GaussianShiftMinimax.posteriorCov_posDef Matrix.PosDef.one hτ
  have h_ρ_psd : ρ.PosSemidef := h_ρ_posDef.posSemidef
  -- The integrand `F h Δ := L (equiv.symm (fun _ => T Δ - A·h))`.
  set F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ≥0∞ :=
      fun h Δ => L ((EuclideanSpace.equiv (Fin 1) ℝ).symm
        (fun _ : Fin 1 => T Δ - ∑ k : Fin m, A 0 k * h k)) with hF_def
  -- Joint measurability.
  have hF_meas : Measurable (Function.uncurry F) := by
    refine hL_meas.comp ?_
    refine (EuclideanSpace.equiv (Fin 1) ℝ).symm.continuous.measurable.comp ?_
    refine measurable_pi_lambda _ fun _ => ?_
    have hT_p : Measurable (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
        T p.2) := hT.comp measurable_snd
    have h_lin : Measurable (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
        ∑ k : Fin m, A 0 k * p.1 k) := by
      refine Finset.measurable_sum _ fun k _ => ?_
      refine measurable_const.mul ?_
      have : Continuous fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
          p.1 k := by fun_prop
      exact this.measurable
    exact hT_p.sub h_lin
  -- Joint measurability of the full RHS integrand (with the exp tilt).
  have h_full_meas : Measurable
      (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
        ENNReal.ofReal (Real.exp (⟪p.2, p.1⟫_ℝ - (1/2 : ℝ) * ‖p.2‖ ^ 2)) * F p.2 p.1) := by
    refine Measurable.mul ?_ ?_
    · refine ENNReal.continuous_ofReal.measurable.comp ?_
      refine Real.continuous_exp.measurable.comp ?_
      refine Measurable.sub ?_ ?_
      · exact (continuous_snd.inner continuous_fst).measurable
      · exact (measurable_const.mul (continuous_snd.norm.pow 2).measurable)
    · -- F p.2 p.1 is measurable in (p.1, p.2) via hF_meas (uncurried form).
      exact hF_meas.comp (measurable_snd.prodMk measurable_fst)
  -- Change the goal so the RHS integrand uses `F h Δ` notation.
  change ∫⁻ y, L y ∂N_y ≤
      ∫⁻ Δ, ∫⁻ h,
        ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ - (1/2 : ℝ) * ‖h‖ ^ 2)) * F h Δ ∂π_τ ∂N_Δ
  -- Step 1: Tonelli swap to put h outer.
  have h_swap : ∫⁻ Δ, ∫⁻ h,
        ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ - (1/2 : ℝ) * ‖h‖ ^ 2)) * F h Δ ∂π_τ ∂N_Δ
      = ∫⁻ h, ∫⁻ Δ,
        ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ - (1/2 : ℝ) * ‖h‖ ^ 2)) * F h Δ ∂N_Δ ∂π_τ := by
    rw [lintegral_lintegral_swap]
    exact h_full_meas.aemeasurable
  -- Step 2: Per-h, inner Δ-integral converts to ∫⁻ Δ F h Δ dN(h, I)(Δ) via Gaussian shift RN.
  have h_rn : ∀ h : EuclideanSpace ℝ (Fin m),
      ∫⁻ Δ, ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ - (1/2 : ℝ) * ‖h‖ ^ 2)) * F h Δ ∂N_Δ
        = ∫⁻ Δ, F h Δ ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)) := by
    intro h
    -- Step 2a: rewrite the exponent in dot-product form to match
    -- `multivariateGaussian_withDensity_exp_shift`.
    have h_norm_sq_eq :
        h.ofLp ⬝ᵥ (1 : Matrix (Fin m) (Fin m) ℝ).mulVec h.ofLp = ‖h‖ ^ 2 := by
      rw [Matrix.one_mulVec, EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => by positivity))]
      simp [dotProduct, sq]
    have h_arg_eq : ∀ Δ : EuclideanSpace ℝ (Fin m),
        Real.exp (⟪h, Δ⟫_ℝ - (1/2 : ℝ) * ‖h‖ ^ 2)
          = Real.exp (⟪h, Δ⟫_ℝ -
              h.ofLp ⬝ᵥ (1 : Matrix (Fin m) (Fin m) ℝ).mulVec h.ofLp / 2) := by
      intro Δ; congr 1; rw [h_norm_sq_eq]; ring
    simp_rw [h_arg_eq]
    -- Step 2b: Use multivariateGaussian_withDensity_exp_shift S=1 + lintegral_withDensity.
    have h_meas_density : Measurable
        (fun Δ : EuclideanSpace ℝ (Fin m) => ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ -
            h.ofLp ⬝ᵥ (1 : Matrix (Fin m) (Fin m) ℝ).mulVec h.ofLp / 2))) := by
      refine ENNReal.continuous_ofReal.measurable.comp
        (Real.continuous_exp.measurable.comp ?_)
      exact ((continuous_const.inner continuous_id).measurable).sub measurable_const
    have h_F_meas : Measurable (fun Δ : EuclideanSpace ℝ (Fin m) => F h Δ) := by
      have h := hF_meas.comp (Measurable.prodMk (measurable_const (a := h)) measurable_id)
      simpa [Function.uncurry] using! h
    rw [show ∫⁻ Δ, ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ -
            h.ofLp ⬝ᵥ (1 : Matrix (Fin m) (Fin m) ℝ).mulVec h.ofLp / 2)) * F h Δ ∂N_Δ
          = ∫⁻ Δ, F h Δ ∂(N_Δ.withDensity (fun Δ : EuclideanSpace ℝ (Fin m) =>
              ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ -
                  h.ofLp ⬝ᵥ (1 : Matrix (Fin m) (Fin m) ℝ).mulVec h.ofLp / 2))))
          from (lintegral_withDensity_eq_lintegral_mul N_Δ h_meas_density h_F_meas).symm]
    rw [hNΔ_def]
    rw [multivariateGaussian_withDensity_exp_shift Matrix.PosDef.one.posSemidef h]
    -- After the shift, the mean is `toEuclideanCLM 1 h`, which equals `h`.
    have h_toCLM_one : (Matrix.toEuclideanCLM (𝕜 := ℝ)
        (1 : Matrix (Fin m) (Fin m) ℝ)) h = h := by
      apply (WithLp.equiv 2 (Fin m → ℝ)).injective
      simp
    rw [h_toCLM_one]
  simp_rw [h_swap, h_rn]
  -- Step 3: Apply innovations rep with J = 1.
  -- The LHS-form of innovations rep is `∫⁻ h ∫⁻ x f h x dN(h, I) dN(0, τ²I)`;
  -- after our reduction the goal matches with f = F.
  have h_innov := GaussianShiftMinimax.gaussianShift_innovations_repr
      (J := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one (τ := τ) hτ
      F hF_meas
  -- After applying innovations rep, the goal becomes:
  --   ∫⁻ y L y ∂N(0, Sy) ≤ ∫⁻ x ∫⁻ g F (g + posteriorMean 1 τ x) x dN(0, ρ) dmarginal(x).
  have h_J_inv : (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ = 1 := inv_one
  -- Normalize h_innov to use plain `1` instead of `1⁻¹`.
  simp only [h_J_inv] at h_innov
  rw [h_innov]
  -- Step 4: For each x, the inner integral over g is ≥ bayesRiskAtTau τ.
  -- F (g + posteriorMean 1 τ x) x = L (equiv.symm (fun _ => T x - A·(g + posteriorMean 1 τ x)))
  --                                = L (equiv.symm (fun _ => c(x) - A·g))
  -- where c(x) := T x - A·posteriorMean 1 τ x (scalar).
  -- The g-integral pushes forward to N(0, A · ρ · Aᵀ) = N_y via matrixToEuclideanCLMRect A.
  -- By Anderson lemma (shift by `lift c(x)`), the integral is ≥ ∫⁻ y L y dN(0, A·ρ·Aᵀ) = LHS.
  have h_inner_lb : ∀ x : EuclideanSpace ℝ (Fin m),
      ∫⁻ y : EuclideanSpace ℝ (Fin 1), L y ∂N_y
        ≤ ∫⁻ g : EuclideanSpace ℝ (Fin m), F (g + GaussianShiftMinimax.posteriorMean 1 τ x) x
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) ρ) := by
    intro x
    -- Algebraic: F (g + posteriorMean 1 τ x) x rewrites.
    have hF_eq : ∀ g : EuclideanSpace ℝ (Fin m),
        F (g + GaussianShiftMinimax.posteriorMean 1 τ x) x
          = L ((EuclideanSpace.equiv (Fin 1) ℝ).symm
            (fun _ : Fin 1 =>
              (T x - ∑ k : Fin m, A 0 k * (GaussianShiftMinimax.posteriorMean 1 τ x) k)
                - ∑ k : Fin m, A 0 k * g k)) := by
      intro g
      simp only [hF_def]
      congr 2
      funext _
      have : ∀ k : Fin m, (g + GaussianShiftMinimax.posteriorMean 1 τ x) k
          = g k + (GaussianShiftMinimax.posteriorMean 1 τ x) k := fun k => rfl
      simp_rw [this, mul_add, Finset.sum_add_distrib]
      ring
    simp_rw [hF_eq]
    -- Pushforward: ∫⁻ g (...) dN(0, ρ) = ∫⁻ y (...lifted...) dN(0, A·ρ·Aᵀ).
    -- We identify equiv.symm (fun _ => c - A·g) = lift_c - matrixToEuclideanCLMRect A g
    -- where lift_c := equiv.symm (fun _ => c).
    set c : ℝ := T x - ∑ k : Fin m, A 0 k * (GaussianShiftMinimax.posteriorMean 1 τ x) k
      with hc_def
    set lift_c : EuclideanSpace ℝ (Fin 1) :=
      (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ : Fin 1 => c) with hlift_c_def
    have h_subtract_eq : ∀ g : EuclideanSpace ℝ (Fin m),
        (EuclideanSpace.equiv (Fin 1) ℝ).symm
            (fun _ : Fin 1 => c - ∑ k : Fin m, A 0 k * g k)
          = lift_c - matrixToEuclideanCLMRect A g := by
      intro g
      ext i
      fin_cases i
      simp [lift_c, matrixToEuclideanCLMRect, Matrix.mulVec, dotProduct,
            EuclideanSpace.equiv]
    simp_rw [h_subtract_eq]
    -- Pushforward via matrixToEuclideanCLMRect A: N(0, ρ).map(...) = N(0, A·ρ·Aᵀ) = N_y.
    have h_pushforward :
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) ρ).map
            (matrixToEuclideanCLMRect A)
          = N_y := by
      rw [multivariateGaussian_map_rectangular A 0 h_ρ_psd, hNy_def]
      simp [hSy_def]
    have h_map_int :
        ∫⁻ g, L (lift_c - matrixToEuclideanCLMRect A g)
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) ρ)
          = ∫⁻ y, L (lift_c - y) ∂N_y := by
      rw [← h_pushforward]
      symm
      have h_int_meas : Measurable (fun y : EuclideanSpace ℝ (Fin 1) => L (lift_c - y)) :=
        hL_meas.comp (measurable_const.sub measurable_id)
      have h_map_meas : Measurable (matrixToEuclideanCLMRect A) :=
        (matrixToEuclideanCLMRect A).continuous.measurable
      exact lintegral_map h_int_meas h_map_meas
    rw [h_map_int]
    -- Anderson lemma: ∫⁻ y L y dN(0, Sy) ≤ ∫⁻ y L (lift_c - y) dN(0, Sy).
    -- We use bowl symmetry to rewrite L (lift_c - y) = L (y + (-lift_c)),
    -- then apply anderson_lemma_loss with shift `-lift_c`.
    have h_symm_rewrite : ∀ y : EuclideanSpace ℝ (Fin 1),
        L (lift_c - y) = L (y + (-lift_c)) := by
      intro y
      have h1 : lift_c - y = -(y + (-lift_c)) := by abel
      rw [h1, hL.symm]
    simp_rw [h_symm_rewrite]
    -- Sy is PosSemidef (conjugation of PosSemidef ρ by A).
    have h_Sy_psd : Sy.PosSemidef := by
      have := h_ρ_psd.mul_mul_conjTranspose_same A
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    calc ∫⁻ y, L y ∂N_y
        ≤ ∫⁻ y, L (y + (-lift_c)) ∂N_y := by
          rw [hNy_def]
          exact anderson_lemma_loss h_Sy_psd hL (-lift_c)
      _ = ∫⁻ y, L (y + (-lift_c)) ∂N_y := rfl
  -- Step 5: Outer integral over x (marginalGaussianShift is a probability measure).
  haveI hπX_prob : IsProbabilityMeasure (GaussianShiftMinimax.marginalGaussianShift
      (1 : Matrix (Fin m) (Fin m) ℝ) τ) := by
    unfold GaussianShiftMinimax.marginalGaussianShift; infer_instance
  calc ∫⁻ y, L y ∂N_y
      = ∫⁻ _x, ∫⁻ y, L y ∂N_y
          ∂(GaussianShiftMinimax.marginalGaussianShift
              (1 : Matrix (Fin m) (Fin m) ℝ) τ) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ x, ∫⁻ g, F (g + GaussianShiftMinimax.posteriorMean 1 τ x) x
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) ρ)
          ∂(GaussianShiftMinimax.marginalGaussianShift
              (1 : Matrix (Fin m) (Fin m) ℝ) τ) :=
        lintegral_mono fun x => h_inner_lb x

/-! ## Anderson-Bayes inequality specialized to T = 0 (constant zero estimator)

For the constant zero estimator `T(Δ) = 0`, the Anderson-Bayes inequality
follows from Anderson PSD-monotone applied to a specific pushforward: no
Gaussian conditional theory is required.

**Proof outline**:

1. **Bowl symmetry**: `L((equiv).symm(fun _ => -∑_k A 0 k h k)) = L((equiv).symm(fun _ => ∑_k A 0 k
h k))`
   since `L` is bowl-shape and `equiv.symm` is linear (preserves negation).

2. **Tonelli + factor-out**: the inner integral `∫⁻ Δ ofReal(exp(⟨h,Δ⟩-½‖h‖²)) · L(...) dN(0, I)`
   factors as `L(...) · ∫⁻ Δ ofReal(exp(⟨h,Δ⟩-½‖h‖²)) dN(0, I)` since the
   `L`-factor doesn't depend on `Δ` (after Tonelli swap puts h-integral inner).

3. **Gaussian MGF tilt = 1**: `∫⁻ Δ ofReal(exp(⟨h,Δ⟩-½‖h‖²)) dN(0, I_m) = 1`
   via `multivariateGaussian_withDensity_exp_shift` evaluated at the constant
   function 1.

4. **Pushforward identification**:
   `∫⁻ h L((equiv).symm(fun _ => ∑_k A 0 k h k)) dN(0, τ²I)
      = ∫⁻ y L y ∂((multivariateGaussian 0 (τ²I)).map (matrixToEuclideanCLMRect A))
      = ∫⁻ y L y ∂(multivariateGaussian 0 (A·(τ²I)·Aᵀ))
      = ∫⁻ y L y ∂(multivariateGaussian 0 (τ²·A·Aᵀ))`
   via `multivariateGaussian_map_rectangular` and matrix arithmetic.

5. **Anderson PSD-monotone** (`gaussian_lintegral_mono_of_psd_le`): since
   `posteriorCov 1 τ = (τ²/(τ²+1))·I ≼ τ²·I`, we get
   `A · posteriorCov · Aᵀ ≼ τ² · A · Aᵀ`, hence
   `∫⁻ L ∂N(0, smaller) ≤ ∫⁻ L ∂N(0, larger)`.

This proof bypasses the general Gaussian conditional theory needed for the
arbitrary-T abstract version and uses only existing infrastructure
(`multivariateGaussian_withDensity_exp_shift`, `multivariateGaussian_map_rectangular`,
`gaussian_lintegral_mono_of_psd_le`). -/

/-! ## Sub-lemmas for the `_at_zero` proof

The `_at_zero` proof composes named sub-lemmas, each capturing one substantive
step from the 5-step recipe above. -/

/-- **Step 1 sub-lemma**: bowl symmetry collapses the negation of a 1D
EuclideanSpace value. Specifically, for bowl-shape `L`, applying `L` to
`(equiv).symm(fun _ => 0 - x)` equals `L(matrixToEuclideanCLMRect A h)` —
i.e., the negation in `0 - ∑_k A 0 k h k` is removed by bowl-symmetry +
linearity of `equiv.symm`. -/
private lemma bowl_at_zero_simplify
    (A : Matrix (Fin 1) (Fin m) ℝ)
    {L : EuclideanSpace ℝ (Fin 1) → ℝ≥0∞} (hL : BowlShaped L)
    (h : EuclideanSpace ℝ (Fin m)) :
    L ((EuclideanSpace.equiv (Fin 1) ℝ).symm
        (fun _ : Fin 1 => (0 : ℝ) - ∑ k : Fin m, A 0 k * h k))
      = L (matrixToEuclideanCLMRect A h) := by
  -- Step 1: equiv.symm(fun _ => 0 - x) = -equiv.symm(fun _ => x) (pointwise negation).
  have h_neg : (EuclideanSpace.equiv (Fin 1) ℝ).symm
        (fun _ : Fin 1 => (0 : ℝ) - ∑ k : Fin m, A 0 k * h k)
      = -(EuclideanSpace.equiv (Fin 1) ℝ).symm
            (fun _ : Fin 1 => ∑ k : Fin m, A 0 k * h k) := by
    ext i
    simp [zero_sub]
  -- Step 2: bowl symmetry: L(-z) = L(z).
  rw [h_neg, hL.symm]
  -- Step 3: identify `equiv.symm(fun _ => ∑_k A 0 k * h k) = matrixToEuclideanCLMRect A h`
  -- via `.ofLp`-equality (both have the same underlying function on `Fin 1`).
  congr 1
  ext i
  -- Goal at i : Fin 1: equiv.symm(fun _ => ∑_k A 0 k * h k) i = matrixToEuclideanCLMRect A h i.
  -- The RHS equals (A.mulVec h.ofLp) i = ∑_k A i k * h.ofLp k by ofLp_matrixToEuclideanCLMRect.
  -- For i : Fin 1 (only value 0), this equals ∑_k A 0 k * h k.
  fin_cases i
  rfl

/-- **Step 3 sub-lemma**: Gaussian MGF tilt evaluates to 1.
`∫⁻ Δ ofReal(exp(⟨h, Δ⟩ - ‖h‖²/2)) dN(0, 1_m) = 1`.

Proof: by `multivariateGaussian_withDensity_exp_shift` with `S = 1`,
the LHS measure equals `multivariateGaussian h 1`, a probability measure. -/
private lemma gaussian_mgf_tilt_eq_one (h : EuclideanSpace ℝ (Fin m)) :
    ∫⁻ Δ : EuclideanSpace ℝ (Fin m),
        ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ - (1/2 : ℝ) * ‖h‖ ^ 2))
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (1 : Matrix (Fin m) (Fin m) ℝ)) = 1 := by
  -- Step 1: rewrite (1/2)·‖h‖² as (h.ofLp ⬝ᵥ 1·h.ofLp)/2 to match
  -- `multivariateGaussian_withDensity_exp_shift`.
  have h_dot_eq_norm_sq :
      h.ofLp ⬝ᵥ (1 : Matrix (Fin m) (Fin m) ℝ).mulVec h.ofLp = ‖h‖ ^ 2 := by
    rw [Matrix.one_mulVec, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => by positivity))]
    simp [dotProduct, sq]
  -- Step 2: convert the integrand by rewriting ‖h‖² to the dot-product form.
  have h_arg_eq : ∀ Δ : EuclideanSpace ℝ (Fin m),
      Real.exp (⟪h, Δ⟫_ℝ - (1/2 : ℝ) * ‖h‖ ^ 2) =
      Real.exp (⟪h, Δ⟫_ℝ -
          (h.ofLp ⬝ᵥ (1 : Matrix (Fin m) (Fin m) ℝ).mulVec h.ofLp) / 2) := by
    intro Δ
    congr 1
    rw [h_dot_eq_norm_sq]; ring
  simp_rw [h_arg_eq]
  -- Step 3: convert ∫⁻ y, g y ∂μ to (μ.withDensity g) Set.univ.
  rw [show ∫⁻ Δ : EuclideanSpace ℝ (Fin m),
        ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ -
            (h.ofLp ⬝ᵥ (1 : Matrix (Fin m) (Fin m) ℝ).mulVec h.ofLp) / 2))
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
            (1 : Matrix (Fin m) (Fin m) ℝ))
      = ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
            (1 : Matrix (Fin m) (Fin m) ℝ)).withDensity
          (fun y : EuclideanSpace ℝ (Fin m) => ENNReal.ofReal
            (Real.exp (⟪h, y⟫_ℝ -
              (h.ofLp ⬝ᵥ (1 : Matrix (Fin m) (Fin m) ℝ).mulVec h.ofLp) / 2))))
          Set.univ from by
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]]
  -- Step 4: apply `multivariateGaussian_withDensity_exp_shift` (S = 1) to identify
  -- the withDensity as a translated Gaussian (a probability measure).
  rw [multivariateGaussian_withDensity_exp_shift Matrix.PosDef.one.posSemidef h]
  -- Step 5: probability measure on Set.univ equals 1.
  exact measure_univ

/-- **Step 4 sub-lemma**: pushforward of `multivariateGaussian 0 (τ²·1)` under the
linear map `h ↦ equiv.symm(fun _ => ∑_k A 0 k h k) = matrixToEuclideanCLMRect A h`
equals `multivariateGaussian 0 (A·(τ²·1)·Aᵀ) = multivariateGaussian 0 (τ²·A·Aᵀ)`. -/
private lemma mvgaussian_pushforward_at_zero
    (A : Matrix (Fin 1) (Fin m) ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ))).map
        (matrixToEuclideanCLMRect A)
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
          (A * ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)) * A.transpose) := by
  have h_smul_psd : ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
    Matrix.PosDef.one.posSemidef.smul (by positivity)
  rw [multivariateGaussian_map_rectangular A 0 h_smul_psd]
  -- matrixToEuclideanCLMRect A 0 = 0 (CLM applied to 0 is 0).
  simp

/-- **Step 5 sub-lemma**: PSD comparison `A·posteriorCov·Aᵀ ≼ A·(τ²·1)·Aᵀ`.

Since `posteriorCov 1 τ = (τ²/(τ²+1))·1 ≼ τ²·1` (in PSD order), the conjugation
by `A` preserves the PSD comparison. -/
private lemma posteriorCov_le_tausq_after_conjugate
    (A : Matrix (Fin 1) (Fin m) ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (A * ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)) * A.transpose
        - A * GaussianShiftMinimax.posteriorCov
            (1 : Matrix (Fin m) (Fin m) ℝ) τ * A.transpose).PosSemidef := by
  -- Step 1: identify posteriorCov(1, τ) = c • 1 with c = (1 + τ⁻²)⁻¹ = τ²/(τ²+1).
  have hτ2 : 0 < τ ^ 2 := by positivity
  have h_one_plus_pos : (0 : ℝ) < 1 + (τ ^ 2)⁻¹ := by positivity
  have h_one_plus_ne : (1 + (τ ^ 2)⁻¹ : ℝ) ≠ 0 := ne_of_gt h_one_plus_pos
  set c : ℝ := (1 + (τ ^ 2)⁻¹)⁻¹ with hc_def
  have hc_pos : 0 < c := inv_pos.mpr h_one_plus_pos
  -- c ≤ τ², equivalently (1 + τ⁻²)⁻¹ ≤ τ², equivalently 1 ≤ τ²·(1 + τ⁻²) = τ² + 1.
  have hc_le_tausq : c ≤ τ ^ 2 := by
    rw [hc_def, inv_le_iff_one_le_mul₀ h_one_plus_pos]
    have h_expand : τ ^ 2 * (1 + (τ ^ 2)⁻¹) = τ ^ 2 + 1 := by field_simp
    rw [h_expand]; linarith
  -- Step 2: posteriorCov 1 τ = c • 1, by checking (1 + τ⁻²·1) * (c·1) = 1.
  have h_post_eq :
      GaussianShiftMinimax.posteriorCov (1 : Matrix (Fin m) (Fin m) ℝ) τ
        = c • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    unfold GaussianShiftMinimax.posteriorCov
    refine Matrix.inv_eq_right_inv ?_
    rw [show (1 : Matrix (Fin m) (Fin m) ℝ) + (τ ^ 2)⁻¹ • 1
          = (1 + (τ ^ 2)⁻¹) • (1 : Matrix (Fin m) (Fin m) ℝ) from by
            rw [add_smul, one_smul]]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, hc_def,
        mul_inv_cancel₀ h_one_plus_ne, one_smul]
  rw [h_post_eq]
  -- Step 3: A · ((τ²) • 1) · Aᵀ - A · (c • 1) · Aᵀ = (τ² - c) • (A · Aᵀ).
  have h_AAT : A * (1 : Matrix (Fin m) (Fin m) ℝ) * A.transpose = A * A.transpose := by
    rw [Matrix.mul_one]
  have h_diff_eq :
      A * ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)) * A.transpose
        - A * (c • (1 : Matrix (Fin m) (Fin m) ℝ)) * A.transpose
        = (τ ^ 2 - c) • (A * A.transpose) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        h_AAT, ← sub_smul]
  rw [h_diff_eq]
  -- Step 4: PSD of (τ² - c) • (A · Aᵀ).
  have h_AAT_psd : (A * A.transpose).PosSemidef := by
    have := Matrix.PosDef.one.posSemidef.mul_mul_conjTranspose_same A
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_one] at this
    exact this
  exact h_AAT_psd.smul (sub_nonneg.mpr hc_le_tausq)

/-- **Step 5 sub-lemma**: PSD-ness of A·posteriorCov·Aᵀ. -/
private lemma A_posteriorCov_AT_posSemidef
    (A : Matrix (Fin 1) (Fin m) ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (A * GaussianShiftMinimax.posteriorCov
        (1 : Matrix (Fin m) (Fin m) ℝ) τ * A.transpose).PosSemidef := by
  have hP : (GaussianShiftMinimax.posteriorCov
      (1 : Matrix (Fin m) (Fin m) ℝ) τ).PosDef :=
    GaussianShiftMinimax.posteriorCov_posDef Matrix.PosDef.one hτ
  have := hP.posSemidef.mul_mul_conjTranspose_same A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- **Step 5 sub-lemma**: PSD-ness of A·(τ²·1)·Aᵀ. -/
private lemma A_tausq_AT_posSemidef
    (A : Matrix (Fin 1) (Fin m) ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (A * ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)) * A.transpose).PosSemidef := by
  have hτsq : (0 : ℝ) ≤ τ ^ 2 := by positivity
  have h_one_psd : (1 : Matrix (Fin m) (Fin m) ℝ).PosSemidef :=
    Matrix.PosDef.one.posSemidef
  have h_smul_psd : ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
    h_one_psd.smul hτsq
  have := h_smul_psd.mul_mul_conjTranspose_same A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem anderson_bayes_inequality_gaussian_shift_at_zero
    (A : Matrix (Fin 1) (Fin m) ℝ)
    (L : EuclideanSpace ℝ (Fin 1) → ℝ≥0∞) (hL : BowlShaped L)
    {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ y : EuclideanSpace ℝ (Fin 1), L y
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
            (A * GaussianShiftMinimax.posteriorCov
                (1 : Matrix (Fin m) (Fin m) ℝ) τ * A.transpose))
      ≤ ∫⁻ Δ : EuclideanSpace ℝ (Fin m),
          ∫⁻ h : EuclideanSpace ℝ (Fin m),
              ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ - (1/2 : ℝ) * ‖h‖ ^ 2))
                * L ((EuclideanSpace.equiv (Fin 1) ℝ).symm
                    (fun _ : Fin 1 =>
                      (0 : ℝ) - ∑ k : Fin m, A 0 k * h k))
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
                ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)))
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
              (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  -- Use the 4 sub-lemmas above to chain Anderson PSD → pushforward → bowl
  -- symmetry → Tonelli + factor-out + MGF=1.
  -- Step 1 (Anderson PSD): LHS ≤ ∫⁻ y L y ∂N(0, A·(τ²·1)·Aᵀ).
  refine (gaussian_lintegral_mono_of_psd_le
      (A_posteriorCov_AT_posSemidef A hτ)
      (A_tausq_AT_posSemidef A hτ)
      (posteriorCov_le_tausq_after_conjugate A hτ) hL).trans ?_
  -- Step 2 (pushforward): rewrite covariance via the rectangular pushforward.
  rw [show A * ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)) * A.transpose
        = A * ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)) * A.transpose from rfl]
  rw [← mvgaussian_pushforward_at_zero A hτ]
  rw [lintegral_map hL.measurable (matrixToEuclideanCLMRect A).continuous.measurable]
  -- Step 3 (bowl symmetry): identify L (matrixToEuclideanCLMRect A h) with
  -- L (equiv.symm (fun _ => 0 - ∑ k, A 0 k * h k)) for each h.
  have h_bowl_eq : ∀ h : EuclideanSpace ℝ (Fin m),
      L (matrixToEuclideanCLMRect A h)
        = L ((EuclideanSpace.equiv (Fin 1) ℝ).symm
            (fun _ : Fin 1 => (0 : ℝ) - ∑ k : Fin m, A 0 k * h k)) :=
    fun h => (bowl_at_zero_simplify A hL h).symm
  simp_rw [h_bowl_eq]
  -- Steps 4-5 (Tonelli + factor-out + MGF=1):
  -- ∫⁻ h L(...) dN(0, τ²·1) = ∫⁻ Δ ∫⁻ h ofReal(...) · L(...) dN(0, τ²·1) dN(0, 1).
  refine le_of_eq ?_
  symm
  -- Goal: ∫⁻ Δ ∫⁻ h ofReal(...) · L(...) dN(0, τ²·1)(h) dN(0, 1)(Δ)
  --     = ∫⁻ h L(...) dN(0, τ²·1)(h).
  -- Joint measurability premise for Tonelli swap.
  have h_meas_exp_factor :
      Measurable fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
        ENNReal.ofReal (Real.exp (⟪p.2, p.1⟫_ℝ - (1/2 : ℝ) * ‖p.2‖ ^ 2)) := by
    refine ENNReal.continuous_ofReal.measurable.comp
      (Real.continuous_exp.measurable.comp ?_)
    refine Continuous.measurable ?_
    refine Continuous.sub ?_ ?_
    · exact (continuous_snd.inner continuous_fst)
    · exact continuous_const.mul (continuous_snd.norm.pow 2)
  have h_meas_L_factor :
      Measurable fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
        L ((EuclideanSpace.equiv (Fin 1) ℝ).symm
              (fun _ : Fin 1 => (0 : ℝ) - ∑ k : Fin m, A 0 k * p.2 k)) := by
    refine hL.measurable.comp ?_
    refine (EuclideanSpace.equiv (Fin 1) ℝ).symm.continuous.measurable.comp ?_
    refine measurable_pi_lambda _ fun _ => ?_
    refine Measurable.sub measurable_const ?_
    refine Finset.measurable_sum _ fun k _ => ?_
    refine measurable_const.mul ?_
    have hk : Continuous fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
        p.2 k := by fun_prop
    exact hk.measurable
  have h_meas_uncurry :
      AEMeasurable (Function.uncurry fun (Δ h : EuclideanSpace ℝ (Fin m)) =>
        ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ - (1/2 : ℝ) * ‖h‖ ^ 2))
          * L ((EuclideanSpace.equiv (Fin 1) ℝ).symm
                (fun _ : Fin 1 => (0 : ℝ) - ∑ k : Fin m, A 0 k * h k)))
        ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
              (1 : Matrix (Fin m) (Fin m) ℝ)).prod
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
              ((τ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)))) :=
    (h_meas_exp_factor.mul h_meas_L_factor).aemeasurable
  rw [lintegral_lintegral_swap h_meas_uncurry]
  -- Goal: ∫⁻ h ∫⁻ Δ ofReal(...) · L(...) dN(0, 1) dN(0, τ²·1) = ∫⁻ h L(...) dN(0, τ²·1).
  refine lintegral_congr (fun h => ?_)
  -- For each h: ∫⁻ Δ ofReal(exp(⟨h,Δ⟩-‖h‖²/2)) · L(...) dN(0, 1) = L(...).
  -- Factor L(...) out (it's constant in Δ).
  have h_meas_inner :
      Measurable fun Δ : EuclideanSpace ℝ (Fin m) =>
        ENNReal.ofReal (Real.exp (⟪h, Δ⟫_ℝ - (1/2 : ℝ) * ‖h‖ ^ 2)) := by
    refine ENNReal.continuous_ofReal.measurable.comp
      (Real.continuous_exp.measurable.comp ?_)
    exact ((continuous_const.inner continuous_id).measurable).sub measurable_const
  rw [lintegral_mul_const _ h_meas_inner]
  rw [gaussian_mgf_tilt_eq_one h, one_mul]

end AndersonBayes

end AsymptoticStatistics
