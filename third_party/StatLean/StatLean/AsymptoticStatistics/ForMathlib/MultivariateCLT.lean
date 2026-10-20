module
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.LevyConvergence

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Multivariate Central Limit Theorem

We deduce the multivariate iid central limit theorem from Mathlib's 1-D iid CLT
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`) using the
**Cramér–Wold device** at the level of characteristic functions:

For each direction `t : EuclideanSpace ℝ (Fin m)` the inner product
`⟪t, X i⟫` is a 1-D iid sequence whose mean is `⟪t, P[X 0]⟫` and whose variance
agrees, by hypothesis, with the quadratic form `t ⬝ᵥ S *ᵥ t`.  The 1-D CLT
therefore yields convergence of the 1-D characteristic functions, which by
linearity of inner product is precisely the pointwise convergence of the
multivariate characteristic functions of the standardised sample mean.
Lévy's continuity theorem
(`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) closes the argument.

The multivariate CLT upgrades per-coordinate score CLTs into a joint
weak-convergence statement on `EuclideanSpace ℝ (Fin m)`.

## Main result

* `ProbabilityTheory.tendstoInDistribution_multivariate_clt`: the standardised
  sample mean of an iid sequence in `EuclideanSpace ℝ (Fin m)` with finite
  second moment converges weakly to the multivariate Gaussian whose covariance
  matches the input.

The covariance hypothesis is shipped as
`Var[⟪t, X 0⟫; P] = t ⬝ᵥ S *ᵥ t` for each `t`; the caller picks `S` and
proves this identity, which decouples the headline statement from any one
matrix-construction convention.

(We use `S` for the covariance matrix instead of `Σ`, since `Σ` is reserved in
Lean for sigma types.)
-/

open MeasureTheory ProbabilityTheory Filter Complex Matrix
open scoped Real Topology RealInnerProductSpace ENNReal Matrix

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P']

namespace MultivariateCLT

/-! ### Internal helpers.

These factor the algebra of the inner product / CLT identification into small
named pieces. They are kept `private` because they are byproducts of the
proof and do not deserve a stable user-facing name. -/

variable {m : ℕ}

/-- The inner-product evaluation of the standardised sample mean equals the
1-D standardised sum that Mathlib's CLT speaks about. -/
private lemma inner_inv_sqrt_smul_sum_sub
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (μ : EuclideanSpace ℝ (Fin m)) (t : EuclideanSpace ℝ (Fin m))
    (n : ℕ) (ω : Ω) :
    ⟪t, (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, X k ω - n • μ)⟫ =
      (Real.sqrt n)⁻¹ * (∑ k ∈ Finset.range n, ⟪t, X k ω⟫ - n * ⟪t, μ⟫) := by
  rw [real_inner_smul_right, inner_sub_right, inner_sum,
    show ((n : ℕ) • μ : EuclideanSpace ℝ (Fin m)) = ((n : ℝ) • μ) from
      (Nat.cast_smul_eq_nsmul ℝ n μ).symm,
    real_inner_smul_right]

/-- `1-D` Mathlib CLT applied to the iid family `(⟪t, X i ·⟫)`. -/
private lemma tendstoInDistribution_inner
    {X : ℕ → Ω → EuclideanSpace ℝ (Fin m)} {Y : Ω' → ℝ}
    (t : EuclideanSpace ℝ (Fin m))
    (hX : MemLp (X 0) 2 P)
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hY : HasLaw Y
      (gaussianReal 0 (Var[fun ω => ⟪t, X 0 ω⟫; P]).toNNReal) P') :
    MeasureTheory.TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, ⟪t, X k ω⟫ - n * P[fun ω => ⟪t, X 0 ω⟫]))
      atTop Y (fun _ => P) P' := by
  -- Apply the 1-D CLT to `Yᵢ ω := ⟪t, X i ω⟫`.
  refine tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun i ω => ⟪t, X i ω⟫) (Y := Y) (P := P) (P' := P') hY ?_ ?_ ?_
  · -- `MemLp (⟪t, X 0 ·⟫) 2` via the bound `‖⟪t, X 0 ω⟫‖ ≤ ‖t‖ * ‖X 0 ω‖`.
    have hCLM : AEStronglyMeasurable (fun ω => ⟪t, X 0 ω⟫) P :=
      (continuous_const.inner continuous_id).comp_aestronglyMeasurable hX.aestronglyMeasurable
    have hbound :
        ∀ᵐ ω ∂P, ‖⟪t, X 0 ω⟫‖ ≤ ‖(fun ω => ‖t‖ * ‖X 0 ω‖) ω‖ :=
      ae_of_all _ fun ω => by
        have hineq : |⟪t, X 0 ω⟫| ≤ ‖t‖ * ‖X 0 ω‖ :=
          abs_real_inner_le_norm t (X 0 ω)
        have hnn : 0 ≤ ‖t‖ * ‖X 0 ω‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
        exact hineq
    have hX_norm : MemLp (fun ω => ‖t‖ * ‖X 0 ω‖) 2 P := by
      have := hX.norm.const_mul (‖t‖)
      simpa using this
    exact hX_norm.mono hCLM hbound
  · -- Independence of `(⟪t, X i ·⟫)`.
    exact hindep.comp (fun _ y => ⟪t, y⟫)
      (fun _ => continuous_const.inner continuous_id |>.measurable)
  · -- Identical distribution of `(⟪t, X i ·⟫)`.
    intro i
    exact (hident i).comp
      (continuous_const.inner continuous_id : Continuous fun v => ⟪t, v⟫).measurable

end MultivariateCLT

open MultivariateCLT

/-- *Multivariate iid Central Limit Theorem* (Cramér–Wold form).

For an iid sequence `X i : Ω → EuclideanSpace ℝ (Fin m)` with finite second
moment and a witness `Y : Ω' → EuclideanSpace ℝ (Fin m)` of the multivariate
Gaussian limit law `multivariateGaussian 0 S`, the standardised sample mean
`(√n)⁻¹ • (∑ᵢ X i − n • E[X 0])` converges in distribution to `Y`,
**provided** the matrix `S` represents the inner-product variance of `X 0`,
i.e. `Var[⟪t, X 0⟫; P] = t ⬝ᵥ S *ᵥ t` for every direction `t`.

The covariance side-condition `hS_eq` is intentionally an external input: it
records the user's choice of how to *name* the limit covariance (e.g. via a
matrix of element-wise covariances, via `covarianceBilin`, etc.).  The
positive-semidefiniteness side-condition `hS_pos` is the standard
non-degeneracy requirement for `multivariateGaussian`.

The proof reduces to Mathlib's 1-D CLT through the Cramér–Wold device on
characteristic functions, closed by Lévy continuity. -/
theorem tendstoInDistribution_multivariate_clt
    {m : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin m)}
    {Y : Ω' → EuclideanSpace ℝ (Fin m)}
    {S : Matrix (Fin m) (Fin m) ℝ}
    (hS_pos : S.PosSemidef)
    (hS_eq : ∀ t : EuclideanSpace ℝ (Fin m),
      Var[fun ω => ⟪t, X 0 ω⟫; P] = t ⬝ᵥ S *ᵥ t)
    (hY : HasLaw Y (multivariateGaussian 0 S) P')
    (hX : MemLp (X 0) 2 P)
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    MeasureTheory.TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, X k ω - n • P[X 0]))
      atTop Y (fun _ => P) P' := by
  classical
  -- Common measurability shorthand.
  have hX0_meas : AEMeasurable (X 0) P := hX.aemeasurable
  have hXi_meas : ∀ i, AEMeasurable (X i) P := fun i => (hident i).aemeasurable_fst
  have hXi_memLp : ∀ i, MemLp (X i) 2 P := fun i => (hident i).symm.memLp_iff.1 hX
  -- Each standardised sample is AEMeasurable.
  have h_sum_aem : ∀ n : ℕ,
      AEMeasurable
        (fun ω => (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, X k ω - n • P[X 0])) P := by
    intro n
    have h_sum :
        AEMeasurable (fun ω => ∑ k ∈ Finset.range n, X k ω) P :=
      Finset.aemeasurable_fun_sum _ fun i _ => hXi_meas i
    have h_sub :
        AEMeasurable (fun ω => ∑ k ∈ Finset.range n, X k ω - n • P[X 0]) P :=
      h_sum.sub aemeasurable_const
    exact h_sub.const_smul ((Real.sqrt n)⁻¹)
  -- Limit `Y` is AEMeasurable from its `HasLaw`.
  have hY_aem : AEMeasurable Y P' := hY.aemeasurable
  refine ⟨h_sum_aem, hY_aem, ?_⟩
  -- Reduce to pointwise convergence of charFun via Lévy continuity.
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr ?_
  intro t
  -- Step 1.  Build the 1-D CLT statement with witness `id : ℝ → ℝ`.
  set v : NNReal := (Var[fun ω => ⟪t, X 0 ω⟫; P]).toNNReal with hv
  have hidZ : @HasLaw ℝ ℝ _ _ id (gaussianReal 0 v) (gaussianReal 0 v) :=
    HasLaw.id
  have h1D :
      MeasureTheory.TendstoInDistribution
        (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
          (∑ k ∈ Finset.range n, ⟪t, X k ω⟫ - n * P[fun ω => ⟪t, X 0 ω⟫]))
        atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 v) :=
    tendstoInDistribution_inner (X := X) (Y := id) t hX hindep hident hidZ
  have h1D_charFun :
      Tendsto (fun (n : ℕ) =>
        charFun (P.map (fun ω => (Real.sqrt n)⁻¹ *
          (∑ k ∈ Finset.range n, ⟪t, X k ω⟫ - n * P[fun ω => ⟪t, X 0 ω⟫]))) 1)
        atTop (𝓝 (charFun ((gaussianReal 0 v).map (id : ℝ → ℝ)) 1)) := by
    have h := h1D.tendsto
    have := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp h) (1 : ℝ)
    simpa using this
  have hmap_id : (gaussianReal 0 v).map (id : ℝ → ℝ) = gaussianReal 0 v := by
    simp [Measure.map_id (μ := gaussianReal 0 v)]
  rw [hmap_id] at h1D_charFun
  -- Step 2.  Identify the 1-D charFun at 1 with the multivariate charFun at t.
  -- For any AEMeasurable `g : Ω → ℝ^m`,
  --   charFun (P.map (⟪t, g ·⟫)) 1 = charFun (P.map g) t.
  have charFun_inner :
      ∀ {g : Ω → EuclideanSpace ℝ (Fin m)} (_ : AEMeasurable g P),
        charFun (P.map (fun ω => ⟪t, g ω⟫)) 1 = charFun (P.map g) t := by
    intro g hg
    have hcont_inner : Continuous (fun v : EuclideanSpace ℝ (Fin m) => ⟪t, v⟫) :=
      continuous_const.inner continuous_id
    have hg_inner : AEMeasurable (fun ω => ⟪t, g ω⟫) P :=
      hcont_inner.measurable.comp_aemeasurable hg
    have hf1_aestr :
        AEStronglyMeasurable (fun (x : ℝ) => Complex.exp ((1 : ℝ) * x * Complex.I))
          (P.map (fun ω => ⟪t, g ω⟫)) :=
      Measurable.aestronglyMeasurable (by fun_prop)
    have hf2_aestr :
        AEStronglyMeasurable
          (fun (x : EuclideanSpace ℝ (Fin m)) => Complex.exp (↑(⟪x, t⟫ : ℝ) * Complex.I))
          (P.map g) :=
      Measurable.aestronglyMeasurable (by fun_prop)
    -- Use `charFun_apply_real` for the LHS to bypass `⟪x, 1⟫_ℝ` simplification.
    rw [charFun_apply_real, charFun_apply, integral_map hg_inner hf1_aestr,
      integral_map hg hf2_aestr]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    -- LHS: `cexp((1 : ℝ) * ⟪t, g ω⟫ * I)`, RHS: `cexp(↑⟪g ω, t⟫ * I)`.
    change Complex.exp ((1 : ℝ) * ⟪t, g ω⟫ * Complex.I) =
         Complex.exp (↑(⟪g ω, t⟫ : ℝ) * Complex.I)
    have h_rhs : (⟪g ω, t⟫ : ℝ) = ⟪t, g ω⟫ := real_inner_comm _ _
    rw [h_rhs]
    push_cast
    ring_nf
  -- Apply `charFun_inner` at the standardised sample `V_n`.
  have h_charFun_eq :
      ∀ n : ℕ,
        charFun
          (P.map (fun ω => (Real.sqrt n)⁻¹ *
            (∑ k ∈ Finset.range n, ⟪t, X k ω⟫ -
              n * P[fun ω => ⟪t, X 0 ω⟫]))) 1 =
        charFun
          (P.map (fun ω =>
            (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, X k ω - n • P[X 0]))) t := by
    intro n
    have h_eq :
        (fun ω => (Real.sqrt n)⁻¹ *
          (∑ k ∈ Finset.range n, ⟪t, X k ω⟫ - n * P[fun ω => ⟪t, X 0 ω⟫])) =
        (fun ω => ⟪t,
          (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, X k ω - n • P[X 0])⟫) := by
      funext ω
      rw [inner_inv_sqrt_smul_sum_sub X (P[X 0]) t n ω]
      have h_pull : P[fun ω => ⟪t, X 0 ω⟫] = ⟪t, P[X 0]⟫ := by
        -- ∫ ω, ⟪t, X 0 ω⟫ ∂P = ⟪t, ∫ ω, X 0 ω ∂P⟫ by linearity (`integral_inner`).
        have hX0_int : Integrable (X 0) P :=
          hX.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
        exact integral_inner hX0_int t
      rw [h_pull]
    rw [h_eq, charFun_inner (h_sum_aem n)]
  -- Substitute pointwise into the 1-D charFun convergence.
  have h1D_charFun' :
      Tendsto (fun (n : ℕ) =>
        charFun (P.map (fun ω =>
          (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, X k ω - n • P[X 0]))) t)
        atTop (𝓝 (charFun (gaussianReal 0 v) 1)) := by
    have := h1D_charFun
    simp_rw [h_charFun_eq] at this
    exact this
  -- Step 3.  Identify the limit charFuns.
  have h_lim_1d : charFun (gaussianReal 0 v) (1 : ℝ) =
      Complex.exp (- ((v : ℝ) : ℂ) / 2) := by
    rw [charFun_gaussianReal]
    push_cast
    ring_nf
  have h_lim_mv :
      charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) t =
        Complex.exp (- ((t ⬝ᵥ S *ᵥ t : ℝ) : ℂ) / 2) := by
    rw [charFun_multivariateGaussian hS_pos]
    simp [neg_div]
  have h_v_real : (v : ℝ) = t ⬝ᵥ S *ᵥ t := by
    have hvar_nn : 0 ≤ Var[fun ω => ⟪t, X 0 ω⟫; P] := variance_nonneg _ _
    rw [hv, Real.coe_toNNReal _ hvar_nn]
    exact hS_eq t
  have h_match :
      charFun (gaussianReal 0 v) (1 : ℝ) =
        charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) t := by
    rw [h_lim_1d, h_lim_mv, h_v_real]
  -- Convert `h1D_charFun'` to land in `𝓝 (charFun (multivariateGaussian 0 S) t)`,
  -- and finally identify with `charFun (P'.map Y) t` via `hY.map_eq`.
  have h_target_underlying :
      Tendsto (fun (n : ℕ) =>
        charFun (P.map (fun ω =>
          (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, X k ω - n • P[X 0]))) t)
        atTop (𝓝 (charFun (P'.map Y) t)) := by
    rw [hY.map_eq, ← h_match]
    exact h1D_charFun'
  -- The goal is the same statement with `charFun` applied to `ProbabilityMeasure`-coerced
  -- objects.  Since the coercion is definitionally the underlying measure,
  -- the two forms agree, and `convert` (or `exact_mod_cast`) closes it.
  exact h_target_underlying

end ProbabilityTheory
