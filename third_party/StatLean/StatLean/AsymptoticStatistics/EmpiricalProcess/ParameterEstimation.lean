module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
public import StatLean.AsymptoticStatistics.EmpiricalProcess.IIDFiniteRestriction
public import StatLean.AsymptoticStatistics.EmpiricalProcess.RandomFunctions
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperational
public import StatLean.AsymptoticStatistics.ForMathlib.TendstoInMeasureAlgebra
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.HasLaw

@[expose] public section

/-!
# Theorem 19.23: empirical process under parameter estimation

vdV §19.4. Let `X_1, …, X_n` be a random sample from `P_θ` indexed by
`θ ∈ ℝ^k`. If `F` is `P_θ`-Donsker, `θ̂_n` is asymptotically linear with
influence function `ψ_θ`, and `θ ↦ P_θ` from `ℝ^k` to `ℓ^∞(F)` is Fréchet
differentiable at `θ`, then `√n(P_n − P_{θ̂})` converges in distribution to
the process `f ↦ G_{P_θ} f − G_{P_θ}(ψ_θᵀ Ṗ_θ f)`.

This file ships the single-direction (`k = 1`) special case, expressed against
the ℝ-target `AsymptoticallyLinearAt`. The conclusion is the pointwise
weak-convergence statement: for every `f ∈ F`, `√n · (P_n f − P_{θ̂_n} f)`
converges in distribution under `μ` to `N(0, σ_f²)` with
`σ_f² := ∫ (f − Pf − dPθ f · ψ_{θ₀})² ∂P_{θ₀}`.

Principal declarations: `Theorem19_23Hyp` (bundled hypotheses) and
`empiricalProcess_param_estimation`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ENNReal
open scoped ENNReal Topology InnerProductSpace
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperational

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Bundled hypotheses for Theorem 19.23 (single-direction k=1 case).**

vdV's thm 19.23 takes `θ ∈ ℝ^k`; this Lean version restricts to `k = 1`
(ℝ-target) so as to use the ℝ-target `AsymptoticallyLinearAt`.

Three layers:

1. **Donsker hypothesis** (`donsker`): `F` is `P_{θ₀}`-Donsker.
2. **Asymptotic linearity** (`asymp_linear`): `θ̂_n` admits the
   expansion `√n(θ̂_n − θ₀) = (1/√n)·Σ ψ_{θ₀}(X_i) + o_P(1)` under
   `P_{θ₀}^n`. Stated using `AsymptoticallyLinearAt`.
3. **Fréchet differentiability of `θ ↦ P_θ`** (`frechet`): the F-indexed
   map `θ ↦ P_θ` from `ℝ` to `ℓ^∞(F)` (in supNormOver-norm) is Fréchet
   differentiable at `θ₀` with derivative `dPθ : (Ω → ℝ) → ℝ` (the
   F-indexed family of derivatives, evaluated at each `f ∈ F`). -/
structure Theorem19_23Hyp
    (F : Set (Ω → ℝ)) (P_θ : ℝ → Measure Ω) (θ₀ : ℝ)
    [IsProbabilityMeasure (P_θ θ₀)]
    (ψ_θ₀ : ↥(L2ZeroMean (P_θ θ₀)))
    (θ_hat : ∀ n, (Fin n → Ω) → ℝ)
    (dPθ : (Ω → ℝ) → ℝ) : Prop where
  /-- vdV §19.4 thm 19.23: `F` is `P_{θ₀}`-Donsker. -/
  donsker : IsPDonsker F (P_θ θ₀)
  /-- vdV thm 19.23: `θ̂_n` is asymptotically linear at `P_{θ₀}`
  with influence function `ψ_{θ₀}` and centering `θ₀`. -/
  asymp_linear : AsymptoticallyLinearAt θ_hat (P_θ θ₀) ψ_θ₀ θ₀
  /-- vdV thm 19.23: `θ ↦ P_θ` from ℝ to ℓ^∞(F) is
  Fréchet differentiable at `θ₀` with derivative `dPθ`. The `ε-δ`
  form: for every `ε > 0`, there exists `δ > 0` such that for all `h`
  with `0 < |h| < δ`, the supremum-over-F deviation between
  `P_{θ₀+h} − P_{θ₀}` and `h · dPθ` (as a functional on F) is at most
  `ε · |h|`. -/
  frechet : ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < |h| → |h| < δ →
    (⨆ f ∈ F, ENNReal.ofReal
        |∫ x, f x ∂(P_θ (θ₀ + h)) - ∫ x, f x ∂(P_θ θ₀) - h * dPθ f|)
      ≤ ENNReal.ofReal (ε * |h|)

/-- **k=1 pointwise form of Theorem 19.23 (single-direction case).**

For every `f ∈ F`, the rescaled "empirical minus estimated" functional
`√n · ((1/n) Σ_i f(X_i) − ∫ f ∂P_{θ̂_n})` converges in distribution
under the sample-space measure `μ` to `N(0, σ_f²)`, where
`σ_f² := ∫ (f − Pf − dPθ f · ψ_{θ₀})² ∂P_{θ₀}`.

**Proof (4-step textbook proof, vdV §19.4 specialised to k=1).**

1. **Master decomposition (eq:19.22).** From `h.frechet` (ε-δ Fréchet at
   `θ₀`) together with `h.asymp_linear`, derive
   `∫ f ∂P_{θ̂_n} − ∫ f ∂P_{θ₀} = (θ̂_n − θ₀) · dPθ f + o_P(n^{−1/2})`
   then substitute `θ̂_n − θ₀ = n^{−1/2}·(1/√n) Σ_i ψ_{θ₀}(X_i) + o_P(n^{−1/2})`
   to get
   `√n · (P_n f − P_{θ̂_n} f) = (1/√n) Σ_i [f(X_i) − Pf − dPθ f · ψ_{θ₀}(X_i)] + o_P(1)`.

2. **Real CLT.** Apply Mathlib's iid 1D CLT
   (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`) to
   `g(X_i) := f(X_i) − Pf − dPθ f · ψ_{θ₀}(X_i)`. Mean zero: `ψ_{θ₀} ∈
   L2ZeroMean (P_θ θ₀)` (centered) and `f − Pf` is the standard
   centering. Variance: `σ_f²` by definition. Conclude
   `n^{−1/2} · Σ_i g(X_i) ⇝ N(0, σ_f²)`.

3. **Slutsky.** Absorb the `o_P(1)` residual via
   `MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`: the full
   `√n · (P_n f − P_{θ̂_n} f)` converges to the same Gaussian.

4. **Variance finiteness.** From `h.donsker.marginalCLT f hf` we get
   `MemLp f 2 (P_θ θ₀)`; combined with `ψ_{θ₀} ∈ L²(P_θ θ₀)` (carried
   by the L2ZeroMean coercion) we get `σ_f² < ∞`, so
   `gaussianReal 0 σ_f²` is well-defined. -/
private theorem empiricalProcess_param_estimation_pointwise_aux
    (F : Set (Ω → ℝ)) (P_θ : ℝ → Measure Ω) (θ₀ : ℝ)
    [IsProbabilityMeasure (P_θ θ₀)]
    (ψ_θ₀ : ↥(L2ZeroMean (P_θ θ₀)))
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (_hX_meas : ∀ i, Measurable (X i))
    (_hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (_hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (_hX_law : μ.map (X 0) = P_θ θ₀)
    (θ_hat : ∀ n, (Fin n → Ω) → ℝ)
    (dPθ : (Ω → ℝ) → ℝ)
    (_h : Theorem19_23Hyp F P_θ θ₀ ψ_θ₀ θ_hat dPθ)
    (f : Ω → ℝ) (_hf : f ∈ F)
    -- the target sequence is AEMeasurable under μ. This decomposes as: (i)
    -- measurability of `Σ f(X_i ξ)` (follows from `_hX_meas` + `f` AEStronglyMeasurable),
    -- and (ii) measurability of `ξ ↦ ∫ f dP_θ (θ_hat n (...))`, which needs
    -- `Measurable (θ_hat n)` AND `θ ↦ ∫ f dP_θ` measurable. Both are caller-side
    -- regularity conditions not captured by `Theorem19_23Hyp`.
    (target_aem : ∀ (n : ℕ),
      AEMeasurable
        (fun ξ : Ξ => Real.sqrt n *
          ((1 / (n : ℝ)) * ∑ i : Fin n, f (X i.val ξ)
            - ∫ y, f y ∂(P_θ (θ_hat n (fun i : Fin n => X i.val ξ))))) μ) :
    let σ_sq : ℝ :=
      ∫ x, (f x - ∫ y, f y ∂(P_θ θ₀)
              - dPθ f
                * (((ψ_θ₀ : ↥(L2ZeroMean (P_θ θ₀))) : Lp ℝ 2 (P_θ θ₀)) : Ω → ℝ) x) ^ 2
        ∂(P_θ θ₀)
    MeasureTheory.TendstoInDistribution
      (fun (n : ℕ) (ξ : Ξ) => Real.sqrt n *
        ((1 / (n : ℝ)) * ∑ i : Fin n, f (X i.val ξ)
          - ∫ y, f y ∂(P_θ (θ_hat n (fun i : Fin n => X i.val ξ)))))
      atTop
      (id : ℝ → ℝ)
      (fun _ => μ)
      (ProbabilityTheory.gaussianReal 0
        (∫ x, (f x - ∫ y, f y ∂(P_θ θ₀)
                - dPθ f
                  * (((ψ_θ₀ : ↥(L2ZeroMean (P_θ θ₀))) : Lp ℝ 2 (P_θ θ₀)) : Ω → ℝ) x) ^ 2
            ∂(P_θ θ₀)).toNNReal) := by
  classical
  simp only
  -- Step 0: Setup notation.
  set ψ : Ω → ℝ :=
    (((ψ_θ₀ : ↥(L2ZeroMean (P_θ θ₀))) : Lp ℝ 2 (P_θ θ₀)) : Ω → ℝ) with hψ_def
  set Pf : ℝ := ∫ y, f y ∂(P_θ θ₀) with hPf_def
  set g : Ω → ℝ := fun x => f x - Pf - dPθ f * ψ x with hg_def
  set σ_sq : ℝ := ∫ x, (g x) ^ 2 ∂(P_θ θ₀) with hσ_def
  -- Step 1: L²-membership.
  have hf_L2 : MemLp f 2 (P_θ θ₀) := _h.donsker.marginalCLT.memLp f _hf
  have hψ_L2 : MemLp ψ 2 (P_θ θ₀) := Lp.memLp _
  have hf_aem : AEStronglyMeasurable f (P_θ θ₀) := hf_L2.aestronglyMeasurable
  have hψ_aem : AEStronglyMeasurable ψ (P_θ θ₀) := hψ_L2.aestronglyMeasurable
  have hg_L2 : MemLp g 2 (P_θ θ₀) := by
    refine (hf_L2.sub (memLp_const Pf)).sub ?_
    simpa using hψ_L2.const_mul (dPθ f)
  have hg_aem : AEStronglyMeasurable g (P_θ θ₀) := hg_L2.aestronglyMeasurable
  -- Step 2: ψ is mean-zero (it lies in L2ZeroMean).
  have hψ_mean : ∫ x, ψ x ∂(P_θ θ₀) = 0 := by
    have h_mem : ((ψ_θ₀ : ↥(L2ZeroMean (P_θ θ₀))) : Lp ℝ 2 (P_θ θ₀))
        ∈ L2ZeroMean (P_θ θ₀) := ψ_θ₀.2
    change ((ψ_θ₀ : ↥(L2ZeroMean (P_θ θ₀))) : Lp ℝ 2 (P_θ θ₀))
        ∈ LinearMap.ker (integralL2 (P_θ θ₀)).toLinearMap at h_mem
    rw [LinearMap.mem_ker] at h_mem
    have h_inner :
        ⟪oneL2 (P_θ θ₀),
          ((ψ_θ₀ : ↥(L2ZeroMean (P_θ θ₀))) : Lp ℝ 2 (P_θ θ₀))⟫_ℝ = 0 := h_mem
    rw [MeasureTheory.L2.inner_def] at h_inner
    have h_one_ae : (oneL2 (P_θ θ₀) : Ω → ℝ) =ᵐ[P_θ θ₀] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    have h_int_eq :
        ∫ a, ⟪((oneL2 (P_θ θ₀) : Lp ℝ 2 (P_θ θ₀)) : Ω → ℝ) a, ψ a⟫_ℝ ∂(P_θ θ₀)
          = ∫ a, ψ a ∂(P_θ θ₀) := by
      apply integral_congr_ae
      filter_upwards [h_one_ae] with a ha
      have hcomm :
          ⟪((oneL2 (P_θ θ₀) : Lp ℝ 2 (P_θ θ₀)) : Ω → ℝ) a, ψ a⟫_ℝ
            = ψ a * ((oneL2 (P_θ θ₀) : Lp ℝ 2 (P_θ θ₀)) : Ω → ℝ) a := rfl
      rw [hcomm, ha, mul_one]
    rw [h_int_eq] at h_inner
    exact h_inner
  -- Step 3: g is mean-zero.
  have hg_mean : ∫ x, g x ∂(P_θ θ₀) = 0 := by
    have hf_int : Integrable f (P_θ θ₀) := hf_L2.integrable (by norm_num)
    have hψ_int : Integrable ψ (P_θ θ₀) := hψ_L2.integrable (by norm_num)
    have h_cmψ_int : Integrable (fun x => dPθ f * ψ x) (P_θ θ₀) :=
      hψ_int.const_mul (dPθ f)
    have hfPf_int : Integrable (fun x => f x - Pf) (P_θ θ₀) :=
      hf_int.sub (integrable_const Pf)
    have h1 : ∫ x, (f x - Pf) - dPθ f * ψ x ∂(P_θ θ₀)
        = (∫ x, f x - Pf ∂(P_θ θ₀)) - ∫ x, dPθ f * ψ x ∂(P_θ θ₀) :=
      integral_sub hfPf_int h_cmψ_int
    have h2 : ∫ x, f x - Pf ∂(P_θ θ₀)
        = (∫ x, f x ∂(P_θ θ₀)) - Pf := by
      rw [integral_sub hf_int (integrable_const _)]; simp
    have h3 : ∫ x, dPθ f * ψ x ∂(P_θ θ₀) = dPθ f * ∫ x, ψ x ∂(P_θ θ₀) :=
      MeasureTheory.integral_const_mul _ _
    change ∫ x, (f x - Pf) - dPθ f * ψ x ∂(P_θ θ₀) = 0
    rw [h1, h2, h3, hψ_mean, mul_zero, sub_zero, hPf_def, sub_self]
  -- Step 4: Push everything through `X 0` to the sample-space measure μ.
  have hX_aem : ∀ i, AEMeasurable (X i) μ := fun i => (_hX_meas i).aemeasurable
  have hX0_aem : AEMeasurable (X 0) μ := hX_aem 0
  have hX_law : ∀ i, μ.map (X i) = P_θ θ₀ := by
    intro i; rw [(_hX_idem i).map_eq]; exact _hX_law
  have hg_L2_map : MemLp g 2 (μ.map (X 0)) := by rw [hX_law 0]; exact hg_L2
  have hgX0_L2 : MemLp (g ∘ X 0) 2 μ := hg_L2_map.comp_of_map hX0_aem
  have hgX0_mean : ∫ ξ, g (X 0 ξ) ∂μ = 0 := by
    have hg_aem_map : AEStronglyMeasurable g (μ.map (X 0)) := by
      rw [hX_law 0]; exact hg_aem
    have h_int : ∫ ξ, g (X 0 ξ) ∂μ = ∫ x, g x ∂(μ.map (X 0)) :=
      (integral_map hX0_aem hg_aem_map).symm
    rw [h_int, hX_law 0, hg_mean]
  -- Step 5: iIndepFun and IdentDistrib of g ∘ X.
  have hg_aem' : ∀ i, AEMeasurable g (μ.map (X i)) := by
    intro i; rw [hX_law i]; exact hg_aem.aemeasurable
  have hgX_indep : ProbabilityTheory.iIndepFun (fun i => g ∘ X i) μ := by
    exact _hX_iindep.comp₀ (fun _ => g) hX_aem hg_aem'
  have hgX_idem : ∀ i, ProbabilityTheory.IdentDistrib
      (g ∘ X i) (g ∘ X 0) μ μ := by
    intro i; exact (_hX_idem i).comp_of_aemeasurable (hg_aem' i)
  -- Step 6: Variance of g ∘ X 0 under μ equals σ_sq.
  have hgX0_var : ProbabilityTheory.variance (g ∘ X 0) μ = σ_sq := by
    -- variance_eq_integral: Var[Y; μ] = ∫ (Y - μ[Y])² ∂μ
    -- with Y := g ∘ X 0; μ[Y] = 0 by hgX0_mean; transport via map.
    have h_aem : AEMeasurable (g ∘ X 0) μ :=
      hgX0_L2.aestronglyMeasurable.aemeasurable
    rw [ProbabilityTheory.variance_eq_integral h_aem]
    -- Expand μ[g ∘ X 0] inline via integral notation.
    have h_mean0 : ∫ ξ, (g ∘ X 0) ξ ∂μ = 0 := hgX0_mean
    rw [show (∫ ω, (g ∘ X 0) ω ∂μ) = 0 from h_mean0]
    simp only [sub_zero, Function.comp_apply]
    -- ∫ ξ, (g (X 0 ξ))^2 ∂μ = σ_sq via map.
    have hg_aem_map : AEStronglyMeasurable (fun x : Ω => (g x)^2) (μ.map (X 0)) := by
      rw [hX_law 0]; exact (hg_aem.aemeasurable.pow_const _).aestronglyMeasurable
    have h_int : ∫ ξ, (g (X 0 ξ))^2 ∂μ = ∫ x, (g x)^2 ∂(μ.map (X 0)) :=
      (integral_map hX0_aem hg_aem_map).symm
    rw [h_int, hX_law 0]
  -- Step 7: Apply Mathlib's iid 1D CLT.
  have h_CLT_raw : MeasureTheory.TendstoInDistribution
      (fun (n : ℕ) (ξ : Ξ) => (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, g (X k ξ) - n * (∫ ξ, g (X 0 ξ) ∂μ)))
      atTop (id : ℝ → ℝ) (fun _ => μ)
      (ProbabilityTheory.gaussianReal 0 σ_sq.toNNReal) := by
    -- Use Mathlib's iid 1D CLT; the variance matches σ_sq via hgX0_var.
    have h_id_law : ProbabilityTheory.HasLaw (id : ℝ → ℝ)
        (ProbabilityTheory.gaussianReal 0
          (ProbabilityTheory.variance ((fun i => g ∘ X i) 0) μ).toNNReal)
        (ProbabilityTheory.gaussianReal 0 σ_sq.toNNReal) := by
      rw [hgX0_var]; exact ProbabilityTheory.HasLaw.id
    exact ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
      h_id_law hgX0_L2 hgX_indep hgX_idem
  -- Step 8: Convert Σ range to Σ Fin and drop the (zero) mean.
  have h_CLT_clean : MeasureTheory.TendstoInDistribution
      (fun (n : ℕ) (ξ : Ξ) =>
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i.val ξ))
      atTop (id : ℝ → ℝ) (fun _ => μ)
      (ProbabilityTheory.gaussianReal 0 σ_sq.toNNReal) := by
    have h_eq : (fun (n : ℕ) (ξ : Ξ) =>
          (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i.val ξ))
        = (fun (n : ℕ) (ξ : Ξ) =>
          (Real.sqrt n)⁻¹ *
            (∑ k ∈ Finset.range n, g (X k ξ) - n * ∫ ξ, g (X 0 ξ) ∂μ)) := by
      funext n ξ
      rw [hgX0_mean, mul_zero, sub_zero, Fin.sum_univ_eq_sum_range
            (fun k => g (X k ξ))]
    rw [h_eq]
    exact h_CLT_raw
  -- Step 9: Master decomposition residual r_n →_P 0 under μ.
  --
  -- Algebraic identity (verified by `ring` after expanding g):
  --   r_n ξ = -(A_n ξ) - dPθ f · (B_n ξ)
  -- where
  --   A_n ξ := √n · (∫ f dP_{θ̂_n(...)} − Pf − dPθ f · (θ̂_n(...) − θ₀))
  --           — the Fréchet residual times √n.
  --   B_n ξ := √n · (θ̂_n(...) − θ₀) − (1/√n) · Σ ψ(X_i ξ)
  --           — the asymp_linear residual.
  --
  -- Each →_P 0 under μ:
  --   (a) B_n →_P 0 under μ: from `_h.asymp_linear` (which gives →_P 0 under Pⁿ)
  --       pushed through `μ.map (fun ξ ↦ fun i ↦ X i.val ξ) = Measure.pi _`, the
  --       latter equality coming from `iIndepFun_iff_map_fun_eq_pi_map` applied
  --       to the restriction of X to Fin n.
  --   (b) A_n →_P 0 under μ: Fréchet ε-δ ⟹ |A_n| ≤ ε · |√n(θ̂_n − θ₀)|; the latter
  --       is tight (= main term `(1/√n) Σ ψ(X_i)` + B_n; main term is bounded in
  --       distribution by CLT and B_n →_P 0). For arbitrary ε' > 0 pick ε small.
  --   (c) r_n = -A_n - dPθ f · B_n →_P 0 by sum + scalar-mul preserving →_P 0.
  have h_residual : MeasureTheory.TendstoInMeasure μ
      (fun (n : ℕ) (ξ : Ξ) =>
        (Real.sqrt n *
          ((1 / (n : ℝ)) * ∑ i : Fin n, f (X i.val ξ)
            - ∫ y, f y ∂(P_θ (θ_hat n (fun i : Fin n => X i.val ξ)))))
        - (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i.val ξ))
      atTop (fun _ => (0 : ℝ)) := by
    -- Fréchet-residual sequence: A n ξ := √n · (∫ f dP_{θ̂_n} − Pf − dPθ f · (θ̂_n − θ₀)).
    set A : ℕ → Ξ → ℝ := fun (n : ℕ) (ξ : Ξ) => Real.sqrt n *
      (∫ y, f y ∂(P_θ (θ_hat n (fun i : Fin n => X i.val ξ))) - Pf
        - dPθ f * (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) with hA_def
    -- Asymptotic-linearity residual: B n ξ := √n·(θ̂_n − θ₀) − (1/√n)·Σ ψ(X_i ξ).
    set B : ℕ → Ξ → ℝ := fun (n : ℕ) (ξ : Ξ) =>
      Real.sqrt n * (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
        - (Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (X i.val ξ) with hB_def
    -- (c) Algebraic identity: r_n ξ = -(A n ξ) - dPθ f * (B n ξ).
    have h_identity : ∀ (n : ℕ) (ξ : Ξ),
        (Real.sqrt n *
          ((1 / (n : ℝ)) * ∑ i : Fin n, f (X i.val ξ)
            - ∫ y, f y ∂(P_θ (θ_hat n (fun i : Fin n => X i.val ξ)))))
          - (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i.val ξ)
        = -(A n ξ) - dPθ f * (B n ξ) := by
      intro n ξ
      have h_sum_g : ∑ i : Fin n, g (X i.val ξ)
          = (∑ i : Fin n, f (X i.val ξ)) - (n : ℝ) * Pf
            - dPθ f * (∑ i : Fin n, ψ (X i.val ξ)) := by
        simp only [hg_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
                   Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      simp only [hA_def, hB_def]
      rw [h_sum_g]
      by_cases hn : n = 0
      · subst hn; simp
      · have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have h_n_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
        have h_sqrt_ne : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn_pos).ne'
        have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
          Real.mul_self_sqrt hn_pos.le
        -- Bridge identities for √n · (1/n) = 1/√n and (1/√n) · n = √n.
        have eq1 : Real.sqrt n * (1 / (n : ℝ)) = (Real.sqrt n)⁻¹ := by
          field_simp; linarith [h_sqrt_sq]
        have eq2 : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
          field_simp; linarith [h_sqrt_sq]
        -- Distribute √n into the parenthetical and rewrite each bridge.
        have lhs_expand : Real.sqrt n *
            ((1 / (n : ℝ)) * ∑ i : Fin n, f (X i.val ξ)
              - ∫ y, f y ∂(P_θ (θ_hat n (fun i : Fin n => X i.val ξ))))
            = Real.sqrt n * (1 / (n : ℝ)) * ∑ i : Fin n, f (X i.val ξ)
              - Real.sqrt n
                * ∫ y, f y ∂(P_θ (θ_hat n (fun i : Fin n => X i.val ξ))) := by
          ring
        have rhs_expand : (Real.sqrt n)⁻¹
            * (∑ i : Fin n, f (X i.val ξ) - (n : ℝ) * Pf
                - dPθ f * ∑ i : Fin n, ψ (X i.val ξ))
            = (Real.sqrt n)⁻¹ * ∑ i : Fin n, f (X i.val ξ)
              - (Real.sqrt n)⁻¹ * ((n : ℝ) * Pf)
              - (Real.sqrt n)⁻¹ * (dPθ f * ∑ i : Fin n, ψ (X i.val ξ)) := by
          ring
        rw [lhs_expand, rhs_expand, eq1,
            show (Real.sqrt n)⁻¹ * ((n : ℝ) * Pf) = Real.sqrt n * Pf from by
              rw [← mul_assoc, eq2]]
        ring
    -- (a) and (b): A and B both →_P 0 under μ.
    -- The asymptotic linearity hypothesis and `iidFiniteRestriction_map_eq_pi`
    -- imply `B →_P 0` under `μ`.
    have h_B_mu : MeasureTheory.TendstoInMeasure μ B atTop (fun _ => (0 : ℝ)) := by
      apply MeasureTheory.tendstoInMeasure_of_ne_top
      intro ε hε hε_top
      have hε_real : (0 : ℝ) < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
      have h_asymp := _h.asymp_linear ε.toReal hε_real
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_asymp
        (Eventually.of_forall (fun _ => zero_le))
        (Eventually.of_forall (fun n => ?_))
      have hΦ_meas : Measurable (fun ξ : Ξ => fun i : Fin n => X i.val ξ) :=
        measurable_pi_lambda _ (fun i => _hX_meas i.val)
      have hset_eq :
          {ξ : Ξ | ε ≤ edist (B n ξ) 0}
            = (fun ξ : Ξ => fun i : Fin n => X i.val ξ) ⁻¹'
                {x : Fin n → Ω | ε.toReal ≤
                  |Real.sqrt n * (θ_hat n x - θ₀)
                    - (Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (x i)|} := by
        ext ξ
        simp only [Set.mem_preimage, Set.mem_setOf_eq, hB_def, edist_zero_right,
          Real.enorm_eq_ofReal_abs]
        exact ENNReal.le_ofReal_iff_toReal_le hε_top (abs_nonneg _)
      calc μ {ξ : Ξ | ε ≤ edist (B n ξ) 0}
          = μ ((fun ξ : Ξ => fun i : Fin n => X i.val ξ) ⁻¹'
                {x : Fin n → Ω | ε.toReal ≤
                  |Real.sqrt n * (θ_hat n x - θ₀)
                    - (Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (x i)|}) := by rw [hset_eq]
        _ ≤ (μ.map (fun ξ : Ξ => fun i : Fin n => X i.val ξ))
                {x : Fin n → Ω | ε.toReal ≤
                  |Real.sqrt n * (θ_hat n x - θ₀)
                    - (Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (x i)|} :=
              MeasureTheory.Measure.le_map_apply hΦ_meas.aemeasurable _
        _ = (MeasureTheory.Measure.pi (fun _ : Fin n => P_θ θ₀))
                {x : Fin n → Ω | ε.toReal ≤
                  |Real.sqrt n * (θ_hat n x - θ₀)
                    - (Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (x i)|} := by
              rw [iidFiniteRestriction_map_eq_pi (P_θ θ₀) μ X _hX_meas
                _hX_iindep _hX_idem _hX_law n]
    -- Closure of A via Fréchet ε-δ + consistency + tightness.
    have h_A_to_zero : MeasureTheory.TendstoInMeasure μ A atTop (fun _ => (0 : ℝ)) := by
      -- ψ-side tightness via Chebyshev on the mean-zero iid sum `(1/√n)·Σ ψ(X_i ξ)`.
      -- The L² variance of this sum under μ equals `∫ ψ² ∂P_{θ₀}` (mean-zero + iid),
      -- giving the Chebyshev tail bound `Var[ψ]/M²`.
      have h_psi_tight : ∀ ε'' > (0 : ℝ≥0∞), ∃ M'' > (0 : ℝ),
          ∀ (n : ℕ),
            μ {ξ | M'' ≤ |(Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (X i.val ξ)|} ≤ ε'' := by
        -- Build the ψ-side iid block (mirroring Steps 5–6 for g).
        have hψ_aem' : ∀ i, AEMeasurable ψ (μ.map (X i)) := by
          intro i; rw [hX_law i]; exact hψ_aem.aemeasurable
        have hψX_indep : ProbabilityTheory.iIndepFun (fun i => ψ ∘ X i) μ :=
          _hX_iindep.comp₀ (fun _ => ψ) hX_aem hψ_aem'
        have hψX_idem : ∀ i, ProbabilityTheory.IdentDistrib
            (ψ ∘ X i) (ψ ∘ X 0) μ μ := fun i =>
          (_hX_idem i).comp_of_aemeasurable (hψ_aem' i)
        have hψ_L2_map : MemLp ψ 2 (μ.map (X 0)) := by rw [hX_law 0]; exact hψ_L2
        have hψX0_L2 : MemLp (ψ ∘ X 0) 2 μ := hψ_L2_map.comp_of_map hX0_aem
        have hψX_L2 : ∀ i, MemLp (ψ ∘ X i) 2 μ := by
          intro i
          have h_map : MemLp ψ 2 (μ.map (X i)) := by rw [hX_law i]; exact hψ_L2
          exact h_map.comp_of_map (hX_aem i)
        have hψX0_mean : ∫ ξ, ψ (X 0 ξ) ∂μ = 0 := by
          have hψ_aem_map : AEStronglyMeasurable ψ (μ.map (X 0)) := by
            rw [hX_law 0]; exact hψ_aem
          have h_int : ∫ ξ, ψ (X 0 ξ) ∂μ = ∫ x, ψ x ∂(μ.map (X 0)) :=
            (integral_map hX0_aem hψ_aem_map).symm
          rw [h_int, hX_law 0, hψ_mean]
        have hψX_mean : ∀ i, ∫ ξ, ψ (X i ξ) ∂μ = 0 := by
          intro i
          have h_eq : ∫ ξ, (ψ ∘ X i) ξ ∂μ = ∫ ξ, (ψ ∘ X 0) ξ ∂μ :=
            (hψX_idem i).integral_eq
          simpa [Function.comp_apply] using h_eq.trans hψX0_mean
        -- V := ∫ ψ² ∂P_θ θ₀ ; equals Var[ψ ∘ X 0; μ] using hψX0_mean and map.
        set V : ℝ := ∫ x, (ψ x)^2 ∂(P_θ θ₀) with hV_def
        have hV_nonneg : 0 ≤ V := by
          rw [hV_def]; exact integral_nonneg (fun _ => sq_nonneg _)
        have hψX0_var : ProbabilityTheory.variance (ψ ∘ X 0) μ = V := by
          have h_aem : AEMeasurable (ψ ∘ X 0) μ :=
            hψX0_L2.aestronglyMeasurable.aemeasurable
          rw [ProbabilityTheory.variance_eq_integral h_aem]
          have h_mean0 : ∫ ξ, (ψ ∘ X 0) ξ ∂μ = 0 := hψX0_mean
          rw [show (∫ ω, (ψ ∘ X 0) ω ∂μ) = 0 from h_mean0]
          simp only [sub_zero, Function.comp_apply]
          have hψ_sq_aem_map : AEStronglyMeasurable (fun x : Ω => (ψ x)^2) (μ.map (X 0)) := by
            rw [hX_law 0]; exact (hψ_aem.aemeasurable.pow_const _).aestronglyMeasurable
          have h_int : ∫ ξ, (ψ (X 0 ξ))^2 ∂μ = ∫ x, (ψ x)^2 ∂(μ.map (X 0)) :=
            (integral_map hX0_aem hψ_sq_aem_map).symm
          rw [h_int, hX_law 0]
        -- IdentDistrib propagates variance.
        have hψXi_var : ∀ i, ProbabilityTheory.variance (ψ ∘ X i) μ = V := by
          intro i
          rw [(hψX_idem i).variance_eq, hψX0_var]
        -- The case `ε'' = ⊤` is immediate.
        intro ε'' hε''_pos
        by_cases hε''_top : ε'' = ⊤
        · refine ⟨1, one_pos, fun n => ?_⟩
          rw [hε''_top]; exact le_top
        -- ε'' < ⊤ case.
        have hε''_real_pos : (0 : ℝ) < ε''.toReal :=
          ENNReal.toReal_pos hε''_pos.ne' hε''_top
        -- Pick M'' large enough so V / M''² ≤ ε''.toReal.
        set M'' : ℝ := max 1 (Real.sqrt (V / ε''.toReal) + 1) with hM''_def
        have hM''_pos : (0 : ℝ) < M'' := by
          rw [hM''_def]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
        have hM''_ge_one : (1 : ℝ) ≤ M'' := le_max_left _ _
        have hM''_ge_sqrt : Real.sqrt (V / ε''.toReal) + 1 ≤ M'' := le_max_right _ _
        have hM''_sq_lb : V / ε''.toReal < M'' ^ 2 := by
          have h_sqrt_lt : Real.sqrt (V / ε''.toReal) < M'' :=
            lt_of_lt_of_le (by linarith) hM''_ge_sqrt
          have h_sqrt_nn : 0 ≤ Real.sqrt (V / ε''.toReal) := Real.sqrt_nonneg _
          have h_sq : Real.sqrt (V / ε''.toReal) ^ 2 = V / ε''.toReal := by
            rw [sq, Real.mul_self_sqrt (div_nonneg hV_nonneg hε''_real_pos.le)]
          have h_pow_lt : Real.sqrt (V / ε''.toReal) ^ 2 < M'' ^ 2 :=
            pow_lt_pow_left₀ h_sqrt_lt h_sqrt_nn (by norm_num)
          linarith [h_pow_lt, h_sq.symm.le, h_sq.le]
        have hM''_sq_pos : 0 < M'' ^ 2 := by positivity
        -- The Chebyshev bound for general n.
        refine ⟨M'', hM''_pos, fun n => ?_⟩
        -- n = 0 case: sum is empty so |0| < M''.
        by_cases hn : n = 0
        · subst hn
          have hset_empty :
              {ξ : Ξ | M'' ≤ |(Real.sqrt (0 : ℕ))⁻¹ * ∑ i : Fin 0, ψ (X i.val ξ)|} = ∅ := by
            ext ξ; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            intro h
            have : (Real.sqrt (0 : ℕ))⁻¹ * ∑ i : Fin 0, ψ (X i.val ξ) = 0 := by
              simp
            rw [this, abs_zero] at h
            linarith
          rw [hset_empty, measure_empty]
          exact zero_le
        -- n > 0 case.
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
        have hn_pos_real : (0 : ℝ) < n := by exact_mod_cast hn_pos
        have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos_real
        have h_sqrt_ne : Real.sqrt n ≠ 0 := h_sqrt_pos.ne'
        have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
          Real.mul_self_sqrt hn_pos_real.le
        -- S ξ := (√n)⁻¹ * Σ_i ψ(X i.val ξ).
        set S : Ξ → ℝ := fun ξ => (Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (X i.val ξ) with hS_def
        -- S = (√n)⁻¹ * (∑ i, ψ ∘ X i.val), so as function: λ ξ, (√n)⁻¹ * Y ξ where Y is sum.
        set Y : Ξ → ℝ := fun ξ => ∑ i : Fin n, ψ (X i.val ξ) with hY_def
        have hY_eq : Y = ∑ i : Fin n, (ψ ∘ X i.val) := by
          funext ξ; simp [hY_def, Function.comp_apply, Finset.sum_apply]
        -- Variance of Y under μ = sum of variances = n * V.
        have hY_L2 : ∀ i : Fin n, MemLp (ψ ∘ X i.val) 2 μ := fun i => hψX_L2 i.val
        have hY_pairwise :
            Set.Pairwise ((Finset.univ : Finset (Fin n)) : Set (Fin n))
              (fun i j => ProbabilityTheory.IndepFun (ψ ∘ X i.val) (ψ ∘ X j.val) μ) := by
          intro i _ j _ hij
          have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
          exact hψX_indep.indepFun hij'
        have hY_var : ProbabilityTheory.variance Y μ = (n : ℝ) * V := by
          rw [hY_eq]
          rw [ProbabilityTheory.IndepFun.variance_sum (fun i _ => hY_L2 i) hY_pairwise]
          have h_each : ∀ i ∈ (Finset.univ : Finset (Fin n)),
              ProbabilityTheory.variance (ψ ∘ X i.val) μ = V := fun i _ => hψXi_var i.val
          rw [Finset.sum_congr rfl h_each]
          simp [Finset.sum_const, Finset.card_univ]
        -- Y is MemLp 2 μ as a finite sum of MemLp.
        have hY_memLp : MemLp Y 2 μ := by
          rw [hY_eq]
          exact memLp_finset_sum' _ (fun i _ => hY_L2 i)
        -- S = (√n)⁻¹ * Y; so it's also MemLp 2.
        have hS_memLp : MemLp S 2 μ := by
          have : (fun ξ => (Real.sqrt n)⁻¹ * Y ξ) = S := by
            funext ξ; simp [hS_def, hY_def]
          rw [← this]
          exact hY_memLp.const_mul _
        -- Variance of S = (1/n) * Var Y = V.
        have hS_var : ProbabilityTheory.variance S μ = V := by
          have h_S_eq : S = fun ξ => (Real.sqrt n)⁻¹ * Y ξ := by
            funext ξ; simp [hS_def, hY_def]
          rw [h_S_eq, ProbabilityTheory.variance_const_mul, hY_var]
          rw [inv_pow, sq, h_sqrt_sq]
          field_simp
        -- Mean of S = 0.
        have hS_mean : ∫ ξ, S ξ ∂μ = 0 := by
          have h_S_eq : S = fun ξ => (Real.sqrt n)⁻¹ * Y ξ := by
            funext ξ; simp [hS_def, hY_def]
          rw [h_S_eq]
          rw [MeasureTheory.integral_const_mul]
          have hY_int : ∫ ξ, Y ξ ∂μ = 0 := by
            rw [hY_def]
            -- ∫ Σ_i ψ(X i.val ξ) = Σ_i ∫ ψ(X i.val ξ) = Σ_i 0 = 0
            rw [MeasureTheory.integral_finset_sum]
            · simp [hψX_mean]
            · intro i _
              exact (hψX_L2 i.val).integrable (by norm_num)
          rw [hY_int, mul_zero]
        -- Apply Chebyshev.
        have h_cheb := ProbabilityTheory.meas_ge_le_variance_div_sq hS_memLp hM''_pos
        rw [hS_mean] at h_cheb
        simp only [sub_zero] at h_cheb
        rw [hS_var] at h_cheb
        -- h_cheb : μ {ξ | M'' ≤ |S ξ|} ≤ ENNReal.ofReal (V / M''²)
        -- Need: ENNReal.ofReal (V/M''²) ≤ ε''
        have h_ofReal_le : ENNReal.ofReal (V / M'' ^ 2) ≤ ε'' := by
          rw [← ENNReal.ofReal_toReal hε''_top]
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_iff₀ hM''_sq_pos]
          -- V ≤ ε''.toReal * M''².  We have V/ε''.toReal < M''², so V < ε''.toReal * M''².
          have h_div_lt : V / ε''.toReal < M'' ^ 2 := hM''_sq_lb
          have h_lt : V < ε''.toReal * M'' ^ 2 := by
            rw [div_lt_iff₀ hε''_real_pos] at h_div_lt
            linarith
          linarith
        exact le_trans h_cheb h_ofReal_le
      -- Sub-step 2: tightness of √n·(θ̂_n − θ₀) under μ via h_B_mu + h_psi_tight.
      have h_tight : ∀ ε' > (0 : ℝ≥0∞), ∃ M > (0 : ℝ),
          ∀ᶠ (n : ℕ) in atTop,
            μ {ξ | M < |Real.sqrt n *
                  (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)|} ≤ ε' := by
        intro ε' hε'_pos
        -- Split ε'/2 between ψ and B sides; works for both ε' = ⊤ and ε' < ⊤.
        have h_half_pos : (0 : ℝ≥0∞) < ε' / 2 := by
          rw [ENNReal.div_pos_iff]; exact ⟨hε'_pos.ne', by simp⟩
        -- ψ side: pick M_ψ from h_psi_tight.
        obtain ⟨M_ψ, hM_ψ_pos, hM_ψ_bound⟩ := h_psi_tight (ε' / 2) h_half_pos
        -- B side: use h_B_mu specialised to ε = 1.
        have hB1 : Tendsto (fun n : ℕ => μ {ξ | (1 : ℝ≥0∞) ≤ edist (B n ξ) 0}) atTop
            (𝓝 0) := h_B_mu 1 one_pos
        rw [ENNReal.tendsto_atTop_zero] at hB1
        obtain ⟨N_B, hN_B⟩ := hB1 (ε' / 2) h_half_pos
        refine ⟨1 + M_ψ, by linarith, ?_⟩
        rw [Filter.eventually_atTop]
        refine ⟨N_B, fun n hn => ?_⟩
        -- Subset: {1+M_ψ < |√n(θ̂-θ₀)|} ⊆ {1 ≤ edist(B,0)} ∪ {M_ψ ≤ |(1/√n)Σψ|}.
        have h_subset :
            {ξ | 1 + M_ψ < |Real.sqrt n *
                  (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)|}
              ⊆ {ξ | (1 : ℝ≥0∞) ≤ edist (B n ξ) 0}
                ∪ {ξ | M_ψ ≤ |(Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (X i.val ξ)|} := by
          intro ξ hξ
          by_contra hnot
          rw [Set.mem_union, not_or] at hnot
          obtain ⟨hnB, hnψ⟩ := hnot
          simp only [Set.mem_setOf_eq] at hξ
          simp only [Set.mem_setOf_eq, edist_zero_right,
            Real.enorm_eq_ofReal_abs, not_le] at hnB
          simp only [Set.mem_setOf_eq, not_le] at hnψ
          -- From hnB (ENNReal.ofReal |B| < 1) extract |B n ξ| < 1.
          have hnB_real : |B n ξ| < 1 := by
            have h_lt : ENNReal.ofReal |B n ξ| < (1 : ℝ≥0∞) := hnB
            have h1_ofreal : (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by
              rw [ENNReal.ofReal_one]
            rw [h1_ofreal] at h_lt
            exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp h_lt
          -- |√n(θ̂-θ₀)| = |B n ξ + (1/√n)·Σψ| ≤ |B n ξ| + |(1/√n)·Σψ| < 1 + M_ψ.
          have h_decomp : Real.sqrt n * (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
              = B n ξ + (Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (X i.val ξ) := by
            simp only [hB_def]; ring
          rw [h_decomp] at hξ
          have h_tri := abs_add_le (B n ξ)
            ((Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (X i.val ξ))
          linarith
        calc μ {ξ | 1 + M_ψ < |Real.sqrt n *
                  (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)|}
            ≤ μ ({ξ | (1 : ℝ≥0∞) ≤ edist (B n ξ) 0}
                ∪ {ξ | M_ψ ≤
                    |(Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (X i.val ξ)|}) :=
              measure_mono h_subset
          _ ≤ μ {ξ | (1 : ℝ≥0∞) ≤ edist (B n ξ) 0}
              + μ {ξ | M_ψ ≤
                  |(Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (X i.val ξ)|} :=
              measure_union_le _ _
          _ ≤ ε' / 2 + ε' / 2 :=
              add_le_add (hN_B n hn) (hM_ψ_bound n)
          _ = ε' := ENNReal.add_halves _
      -- Sub-step 1: consistency from h_tight.
      have h_consistency : ∀ δ' > (0 : ℝ), Tendsto
          (fun n : ℕ => μ {ξ | δ' ≤ |θ_hat n (fun i : Fin n => X i.val ξ) - θ₀|})
          atTop (𝓝 (0 : ℝ≥0∞)) := by
        intro δ' hδ'_pos
        rw [ENNReal.tendsto_atTop_zero]
        intro ε hε_pos
        by_cases hε_top : ε = ⊤
        · refine ⟨0, fun n _ => ?_⟩; rw [hε_top]; exact le_top
        obtain ⟨M, hM_pos, hM_event⟩ := h_tight ε hε_pos
        rw [Filter.eventually_atTop] at hM_event
        obtain ⟨N₀, hN₀⟩ := hM_event
        -- Pick N₁ such that for n ≥ N₁, M/δ' < √n.
        have h_sqrt_inf : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
          Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
        have h_ev_sqrt : ∀ᶠ n : ℕ in atTop, M / δ' < Real.sqrt n :=
          h_sqrt_inf.eventually_gt_atTop (M / δ')
        rw [Filter.eventually_atTop] at h_ev_sqrt
        obtain ⟨N₁, hN₁⟩ := h_ev_sqrt
        refine ⟨max N₀ N₁, fun n hn => ?_⟩
        have hn₀ : N₀ ≤ n := le_of_max_le_left hn
        have hn₁ : N₁ ≤ n := le_of_max_le_right hn
        -- Subset: {δ' ≤ |θ̂_n - θ₀|} ⊆ {M < |√n·(θ̂_n - θ₀)|}.
        have h_subset :
            {ξ | δ' ≤ |θ_hat n (fun i : Fin n => X i.val ξ) - θ₀|}
              ⊆ {ξ | M < |Real.sqrt n *
                    (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)|} := by
          intro ξ hξ
          simp only [Set.mem_setOf_eq] at hξ ⊢
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          have h_md_pos : 0 < M / δ' := div_pos hM_pos hδ'_pos
          have h1 : M / δ' * δ' < Real.sqrt n * δ' :=
            mul_lt_mul_of_pos_right (hN₁ n hn₁) hδ'_pos
          have h_div_eq : M / δ' * δ' = M := by field_simp
          have h2 : Real.sqrt n * δ'
              ≤ Real.sqrt n
                * |θ_hat n (fun i : Fin n => X i.val ξ) - θ₀| :=
            mul_le_mul_of_nonneg_left hξ (Real.sqrt_nonneg _)
          linarith
        calc μ {ξ | δ' ≤ |θ_hat n (fun i : Fin n => X i.val ξ) - θ₀|}
            ≤ μ {ξ | M < |Real.sqrt n *
                  (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)|} := measure_mono h_subset
          _ ≤ ε := hN₀ n hn₀
      -- Sub-step 3: Fréchet ε-δ argument using h_consistency + h_tight + _h.frechet + _hf.
      rw [MeasureTheory.tendstoInMeasure_iff_dist]
      intro ε hε
      rw [ENNReal.tendsto_atTop_zero]
      intro ε₂ hε₂
      -- Handle ε₂ = ∞ trivially.
      by_cases hε₂_top : ε₂ = ∞
      · exact ⟨0, fun n _ => by rw [hε₂_top]; exact le_top⟩
      -- ε₂ < ∞ case: use ε₂/2 for the two-event split.
      have h_half_pos : (0 : ℝ≥0∞) < ε₂ / 2 := by
        rw [ENNReal.div_pos_iff]
        exact ⟨hε₂.ne', by simp⟩
      -- Step A: tightness gives M and N_tight.
      obtain ⟨M, hM_pos, hM_event⟩ := h_tight (ε₂/2) h_half_pos
      rw [Filter.eventually_atTop] at hM_event
      obtain ⟨N_tight, hN_tight⟩ := hM_event
      -- Step B: Fréchet at ε_f := ε / (M + 1). Note: ε_f * M < ε.
      have hMp1 : (0 : ℝ) < M + 1 := by linarith
      set ε_f : ℝ := ε / (M + 1) with hε_f_def
      have hε_f_pos : (0 : ℝ) < ε_f := div_pos hε hMp1
      obtain ⟨δ, hδ_pos, hδ_frechet⟩ := _h.frechet ε_f hε_f_pos
      -- Step C: consistency at δ.
      have h_cons_lim := h_consistency δ hδ_pos
      rw [ENNReal.tendsto_atTop_zero] at h_cons_lim
      obtain ⟨N_cons, hN_cons⟩ := h_cons_lim (ε₂/2) h_half_pos
      -- Combine for n ≥ max N_tight N_cons.
      refine ⟨max N_tight N_cons, fun n hn => ?_⟩
      have hn_tight : N_tight ≤ n := le_of_max_le_left hn
      have hn_cons : N_cons ≤ n := le_of_max_le_right hn
      -- Notation for the three events.
      set bad : Set Ξ := {ξ | ε ≤ dist (A n ξ) (0 : ℝ)} with hbad_def
      set tight_bad : Set Ξ :=
        {ξ | M < |Real.sqrt n *
          (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)|} with htbad_def
      set cons_bad : Set Ξ :=
        {ξ | δ ≤ |θ_hat n (fun i : Fin n => X i.val ξ) - θ₀|} with hcbad_def
      -- Claim: bad ⊆ tight_bad ∪ cons_bad.
      have h_subset : bad ⊆ tight_bad ∪ cons_bad := by
        intro ξ hξ
        by_contra hnot
        rw [Set.mem_union, not_or] at hnot
        obtain ⟨h_not_t, h_not_c⟩ := hnot
        simp only [htbad_def, Set.mem_setOf_eq, not_lt] at h_not_t
        simp only [hcbad_def, Set.mem_setOf_eq, not_le] at h_not_c
        simp only [hbad_def, Set.mem_setOf_eq] at hξ
        have h_dist_eq : dist (A n ξ) (0 : ℝ) = |A n ξ| := by
          rw [Real.dist_eq, sub_zero]
        rw [h_dist_eq] at hξ
        set h_diff : ℝ := θ_hat n (fun i : Fin n => X i.val ξ) - θ₀ with hh_def
        have h_A_eq : A n ξ = Real.sqrt n *
            (∫ y, f y ∂(P_θ (θ₀ + h_diff)) - Pf - h_diff * dPθ f) := by
          change Real.sqrt n * (∫ y, f y ∂(P_θ (θ_hat n
                (fun i : Fin n => X i.val ξ))) - Pf
              - dPθ f * (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
            = Real.sqrt n *
              (∫ y, f y ∂(P_θ (θ₀ + h_diff)) - Pf - h_diff * dPθ f)
          have hθ : θ₀ + h_diff = θ_hat n (fun i : Fin n => X i.val ξ) := by
            simp [hh_def]
          rw [hθ]; ring
        by_cases hh_zero : h_diff = 0
        · -- A n ξ = 0 in this case.
          have h_A_zero : A n ξ = 0 := by
            rw [h_A_eq, hh_zero, add_zero]
            show Real.sqrt n *
              (∫ y, f y ∂(P_θ θ₀) - Pf - 0 * dPθ f) = 0
            rw [show (∫ y, f y ∂(P_θ θ₀) : ℝ) = Pf from rfl, sub_self,
                zero_mul, sub_zero, mul_zero]
          rw [h_A_zero, abs_zero] at hξ
          linarith
        · -- |h_diff| > 0, apply Fréchet.
          have hh_abs_pos : 0 < |h_diff| := abs_pos.mpr hh_zero
          have hh_abs_lt : |h_diff| < δ := h_not_c
          have h_fre := hδ_frechet h_diff hh_abs_pos hh_abs_lt
          have h_le_iSup :
              ENNReal.ofReal |∫ x, f x ∂(P_θ (θ₀ + h_diff)) -
                  ∫ x, f x ∂(P_θ θ₀) - h_diff * dPθ f|
                ≤ ⨆ f' ∈ F, ENNReal.ofReal
                    |∫ x, f' x ∂(P_θ (θ₀ + h_diff)) -
                      ∫ x, f' x ∂(P_θ θ₀) - h_diff * dPθ f'| :=
            le_iSup₂ (f := fun f' (_ : f' ∈ F) => ENNReal.ofReal
              |∫ x, f' x ∂(P_θ (θ₀ + h_diff)) -
                ∫ x, f' x ∂(P_θ θ₀) - h_diff * dPθ f'|) f _hf
          have h_real_bound : |∫ x, f x ∂(P_θ (θ₀ + h_diff)) - Pf -
              h_diff * dPθ f| ≤ ε_f * |h_diff| := by
            have hrhs_nn : (0 : ℝ) ≤ ε_f * |h_diff| :=
              mul_nonneg hε_f_pos.le (abs_nonneg _)
            have h_chain : ENNReal.ofReal |∫ x, f x ∂(P_θ (θ₀ + h_diff)) -
                ∫ x, f x ∂(P_θ θ₀) - h_diff * dPθ f|
                  ≤ ENNReal.ofReal (ε_f * |h_diff|) := h_le_iSup.trans h_fre
            have hreal := (ENNReal.ofReal_le_ofReal_iff hrhs_nn).mp h_chain
            convert hreal using 2
          have h_sqrt_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
          have h_abs_A : |A n ξ| ≤ Real.sqrt n * (ε_f * |h_diff|) := by
            rw [h_A_eq, abs_mul, abs_of_nonneg h_sqrt_nn]
            have h_inner :
                |∫ y, f y ∂(P_θ (θ₀ + h_diff)) - Pf - h_diff * dPθ f|
                  ≤ ε_f * |h_diff| := h_real_bound
            exact mul_le_mul_of_nonneg_left h_inner h_sqrt_nn
          have h_sqrt_h : Real.sqrt n * |h_diff|
              = |Real.sqrt n * h_diff| := by
            rw [abs_mul, abs_of_nonneg h_sqrt_nn]
          have h_sqrt_h_le_M : Real.sqrt n * |h_diff| ≤ M := by
            rw [h_sqrt_h]; exact h_not_t
          have h_A_bound : |A n ξ| ≤ ε_f * M := by
            calc |A n ξ| ≤ Real.sqrt n * (ε_f * |h_diff|) := h_abs_A
              _ = ε_f * (Real.sqrt n * |h_diff|) := by ring
              _ ≤ ε_f * M := mul_le_mul_of_nonneg_left h_sqrt_h_le_M hε_f_pos.le
          have h_ef_M : ε_f * M < ε := by
            have hM_lt : M < M + 1 := by linarith
            have hlt : ε_f * M < ε_f * (M + 1) :=
              mul_lt_mul_of_pos_left hM_lt hε_f_pos
            have hclose : ε_f * (M + 1) = ε := by
              rw [hε_f_def]; field_simp
            linarith [hlt, hclose.symm]
          linarith
      -- Final measure bound.
      calc μ bad
          ≤ μ (tight_bad ∪ cons_bad) := measure_mono h_subset
        _ ≤ μ tight_bad + μ cons_bad := measure_union_le _ _
        _ ≤ ε₂ / 2 + ε₂ / 2 := by
            gcongr
            · exact hN_tight n hn_tight
            · exact hN_cons n hn_cons
        _ = ε₂ := ENNReal.add_halves _
    have h_B_to_zero : MeasureTheory.TendstoInMeasure μ B atTop (fun _ => (0 : ℝ)) := by
      apply MeasureTheory.tendstoInMeasure_of_ne_top
      intro ε hε hε_top
      have hε_real : (0 : ℝ) < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
      have h_asymp := _h.asymp_linear ε.toReal hε_real
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_asymp
        (Eventually.of_forall (fun _ => zero_le))
        (Eventually.of_forall (fun n => ?_))
      have hΦ_meas : Measurable (fun ξ : Ξ => fun i : Fin n => X i.val ξ) :=
        measurable_pi_lambda _ (fun i => _hX_meas i.val)
      have hset_eq :
          {ξ : Ξ | ε ≤ edist (B n ξ) 0}
            = (fun ξ : Ξ => fun i : Fin n => X i.val ξ) ⁻¹'
                {x : Fin n → Ω | ε.toReal ≤
                  |Real.sqrt n * (θ_hat n x - θ₀)
                    - (Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (x i)|} := by
        ext ξ
        simp only [Set.mem_preimage, Set.mem_setOf_eq, hB_def, edist_zero_right,
          Real.enorm_eq_ofReal_abs]
        exact ENNReal.le_ofReal_iff_toReal_le hε_top (abs_nonneg _)
      calc μ {ξ : Ξ | ε ≤ edist (B n ξ) 0}
          = μ ((fun ξ : Ξ => fun i : Fin n => X i.val ξ) ⁻¹'
                {x : Fin n → Ω | ε.toReal ≤
                  |Real.sqrt n * (θ_hat n x - θ₀)
                    - (Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (x i)|}) := by rw [hset_eq]
        _ ≤ (μ.map (fun ξ : Ξ => fun i : Fin n => X i.val ξ))
                {x : Fin n → Ω | ε.toReal ≤
                  |Real.sqrt n * (θ_hat n x - θ₀)
                    - (Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (x i)|} :=
              MeasureTheory.Measure.le_map_apply hΦ_meas.aemeasurable _
        _ = (MeasureTheory.Measure.pi (fun _ : Fin n => P_θ θ₀))
                {x : Fin n → Ω | ε.toReal ≤
                  |Real.sqrt n * (θ_hat n x - θ₀)
                    - (Real.sqrt n)⁻¹ * ∑ i : Fin n, ψ (x i)|} := by
              rw [iidFiniteRestriction_map_eq_pi (P_θ θ₀) μ X _hX_meas
                _hX_iindep _hX_idem _hX_law n]
    -- Combine via the h_identity bridge + TendstoInMeasure algebra helpers.
    have h_combine : MeasureTheory.TendstoInMeasure μ
        (fun (n : ℕ) (ξ : Ξ) => -(A n ξ) - dPθ f * (B n ξ))
        atTop (fun _ => (0 : ℝ)) := by
      have h_negA : MeasureTheory.TendstoInMeasure μ
          (fun (n : ℕ) (ξ : Ξ) => -(A n ξ)) atTop (fun _ => (0 : ℝ)) :=
        h_A_to_zero.neg_zero
      have h_cmB : MeasureTheory.TendstoInMeasure μ
          (fun (n : ℕ) (ξ : Ξ) => dPθ f * (B n ξ)) atTop (fun _ => (0 : ℝ)) :=
        h_B_to_zero.const_mul_zero (dPθ f)
      exact h_negA.sub_zero h_cmB
    -- Bridge via the algebraic identity h_identity.
    have h_eq_fn : (fun (n : ℕ) (ξ : Ξ) =>
          (Real.sqrt n *
            ((1 / (n : ℝ)) * ∑ i : Fin n, f (X i.val ξ)
              - ∫ y, f y ∂(P_θ (θ_hat n (fun i : Fin n => X i.val ξ)))))
          - (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i.val ξ))
        = (fun (n : ℕ) (ξ : Ξ) => -(A n ξ) - dPθ f * (B n ξ)) := by
      funext n ξ; exact h_identity n ξ
    rw [h_eq_fn]; exact h_combine
  -- Step 10: AE-measurability of the target sequence, supplied as `target_aem`.
  have h_target_aem := target_aem
  -- Step 11: Slutsky absorption.
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (n : ℕ) (ξ : Ξ) => (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i.val ξ))
    (Y := fun (n : ℕ) (ξ : Ξ) => Real.sqrt n *
      ((1 / (n : ℝ)) * ∑ i : Fin n, f (X i.val ξ)
        - ∫ y, f y ∂(P_θ (θ_hat n (fun i : Fin n => X i.val ξ)))))
    (Z := (id : ℝ → ℝ))
    h_CLT_clean
    (by simpa using! h_residual)
    h_target_aem

/-- **Theorem 19.23 (Empirical process under parameter estimation, k=1)**.

Under `Theorem19_23Hyp` and an iid sample `X : ℕ → Ξ → Ω` on `(Ξ, μ)`
with law `P_{θ₀}`, the rescaled "empirical minus estimated" functional
`√n · (P_n f − P_{θ̂_n} f)` converges in distribution under `μ` to
`N(0, σ_f²)` for every `f ∈ F`, where
`σ_f² := ∫ (f − Pf − dPθ f · ψ_{θ₀})² ∂P_{θ₀}`.

vdV §19.4. The body delegates to
`empiricalProcess_param_estimation_pointwise_aux`, which carries the
4-step textbook proof (Fréchet expansion + iid 1D CLT + Slutsky-on-o_P
+ variance finiteness).

**Proof outline** (vdV §19.4, specialised to k=1):
1. Eq:19.22 (master decomposition) — Lem 2.12 + Fréchet via `h.frechet`
   substituted with `h.asymp_linear`.
2. Real iid CLT
   (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`)
   applied to `g(X_i) := f(X_i) − Pf − dPθ f · ψ_{θ₀}(X_i)`.
3. Slutsky-on-o_P
   (`MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`).
4. Variance finiteness via `h.donsker.marginalCLT f hf` + L²-membership
   of `ψ_{θ₀}`.

See `empiricalProcess_param_estimation_pointwise_aux` for the full proof. -/
theorem empiricalProcess_param_estimation
    (F : Set (Ω → ℝ)) (P_θ : ℝ → Measure Ω) (θ₀ : ℝ)
    [IsProbabilityMeasure (P_θ θ₀)]
    (ψ_θ₀ : ↥(L2ZeroMean (P_θ θ₀)))
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P_θ θ₀)
    (θ_hat : ∀ n, (Fin n → Ω) → ℝ)
    (dPθ : (Ω → ℝ) → ℝ)
    (h : Theorem19_23Hyp F P_θ θ₀ ψ_θ₀ θ_hat dPθ)
    -- the F-indexed target sequence is AEMeasurable under μ for every n.
    (target_aem : ∀ f ∈ F, ∀ (n : ℕ),
      AEMeasurable
        (fun ξ : Ξ => Real.sqrt n *
          ((1 / (n : ℝ)) * ∑ i : Fin n, f (X i.val ξ)
            - ∫ y, f y ∂(P_θ (θ_hat n (fun i : Fin n => X i.val ξ))))) μ) :
    ∀ f ∈ F,
      let σ_sq : ℝ :=
        ∫ x, (f x - ∫ y, f y ∂(P_θ θ₀)
                - dPθ f
                  * (((ψ_θ₀ : ↥(L2ZeroMean (P_θ θ₀))) : Lp ℝ 2 (P_θ θ₀)) : Ω → ℝ) x) ^ 2
          ∂(P_θ θ₀)
      MeasureTheory.TendstoInDistribution
        (fun (n : ℕ) (ξ : Ξ) => Real.sqrt n *
          ((1 / (n : ℝ)) * ∑ i : Fin n, f (X i.val ξ)
            - ∫ y, f y ∂(P_θ (θ_hat n (fun i : Fin n => X i.val ξ)))))
        atTop
        (id : ℝ → ℝ)
        (fun _ => μ)
        (ProbabilityTheory.gaussianReal 0 σ_sq.toNNReal) := by
  intro f hf
  exact empiricalProcess_param_estimation_pointwise_aux
    F P_θ θ₀ ψ_θ₀ μ X hX_meas hX_iindep hX_idem hX_law θ_hat dPθ h f hf
    (target_aem f hf)

end AsymptoticStatistics.EmpiricalProcess
