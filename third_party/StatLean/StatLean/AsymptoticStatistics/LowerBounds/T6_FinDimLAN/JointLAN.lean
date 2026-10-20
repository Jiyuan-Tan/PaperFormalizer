module
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.CLTinf
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import Mathlib.Probability.CentralLimitTheorem

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Per-direction score-sum CLT under `Pⁿ`

For any direction `g : ↥(L2ZeroMean P)`, the standardised scalar score sum
under the iid product `Pⁿ`,

    Δ_{n,g}(X) := (√n)⁻¹ · ∑_{j : Fin n} g(X j),

converges weakly to `gaussianReal 0 ‖g‖²`. This is the per-direction joint LAN
brick; finite-index joint statements are recovered from it via the Cramér–Wold
device.

## Strategy

`weakConverges_scoreSumScalar_under_pi` reduces to Mathlib's 1-D iid CLT
`tendstoInDistribution_inv_sqrt_mul_sum_sub` applied to the iid sequence
`Y k ω := g(ω k)` on `Measure.infinitePi (fun _ : ℕ => P)`, then bridges to
the `Pⁿ`-form (`Measure.pi (fun _ : Fin n => P)`) via
`pi_const_eq_infinitePi_map`. The mean-zero property of `g ∈ L2ZeroMean P`
collapses the sum-minus-mean form to the plain partial sum.

Reference: vdV §25.3.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped InnerProductSpace ENNReal NNReal RealInnerProductSpace BigOperators

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN
namespace JointLAN

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Per-direction scalar score sum -/

/-- The standardised scalar score sum at direction `g`,
`(√n)⁻¹ · ∑ⱼ g(Xⱼ)`, viewed as a function on the joint sample space
`(Fin n → Ω) → ℝ`. -/
noncomputable def scoreSumScalar
    (g : ↥(L2ZeroMean P)) (n : ℕ) (X : Fin n → Ω) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ j : Fin n, ((g : Lp ℝ 2 P) : Ω → ℝ) (X j)

lemma measurable_scoreSumScalar (g : ↥(L2ZeroMean P)) (n : ℕ) :
    Measurable (scoreSumScalar (P := P) g n) := by
  unfold scoreSumScalar
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ (fun j _ => ?_)
  exact (Lp.stronglyMeasurable _).measurable.comp (measurable_pi_apply _)

/-! ## Helper: `g` is `MemLp 2` and integrable -/

private lemma memLp_two_g (g : ↥(L2ZeroMean P)) :
    MemLp ((g : Lp ℝ 2 P) : Ω → ℝ) 2 P := Lp.memLp _

/-- The integral of `g` (viewed as a function `Ω → ℝ`) under `P` is `0`. -/
private lemma integral_g_eq_zero (g : ↥(L2ZeroMean P)) :
    ∫ x, ((g : Lp ℝ 2 P) : Ω → ℝ) x ∂P = 0 := by
  -- Mirrors the proof from CLTinf.lean: `g ∈ L2ZeroMean P` means
  -- `integralL2 P (g : Lp ℝ 2 P) = 0`, which unfolds to the integral.
  have h_mem : (g : Lp ℝ 2 P) ∈ L2ZeroMean P := g.2
  have h_ker : integralL2 P (g : Lp ℝ 2 P) = 0 := by
    change (g : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap at h_mem
    rw [LinearMap.mem_ker] at h_mem
    exact h_mem
  have h_inner : (⟪(oneL2 P : Lp ℝ 2 P), (g : Lp ℝ 2 P)⟫_ℝ : ℝ) = 0 := h_ker
  rw [MeasureTheory.L2.inner_def] at h_inner
  have h_one_ae : ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  have h_pointwise :
      (fun x => ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) x,
                  ((g : Lp ℝ 2 P) : Ω → ℝ) x⟫_ℝ)
          =ᵐ[P]
      fun x => ((g : Lp ℝ 2 P) : Ω → ℝ) x := by
    filter_upwards [h_one_ae] with x hx
    have hcomm :
        ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) x,
          ((g : Lp ℝ 2 P) : Ω → ℝ) x⟫_ℝ
          = ((g : Lp ℝ 2 P) : Ω → ℝ) x
              * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) x := rfl
    rw [hcomm, hx, mul_one]
  rw [integral_congr_ae h_pointwise] at h_inner
  exact h_inner

/-- The integral `∫ g² dP` equals `‖(g : Lp ℝ 2 P)‖²`. -/
private lemma integral_g_sq_eq_norm_sq (g : ↥(L2ZeroMean P)) :
    ∫ x, ((g : Lp ℝ 2 P) : Ω → ℝ) x ^ 2 ∂P =
      ‖(g : Lp ℝ 2 P)‖ ^ 2 := by
  -- Use the L²-inner-product self identity: `⟪g, g⟫ = ‖g‖²` and
  -- `⟪g, g⟫ = ∫ g·g dP` (`MeasureTheory.L2.inner_def`).
  have h_inner_self :
      (⟪(g : Lp ℝ 2 P), (g : Lp ℝ 2 P)⟫_ℝ : ℝ) = ‖(g : Lp ℝ 2 P)‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  rw [MeasureTheory.L2.inner_def] at h_inner_self
  -- `⟪g x, g x⟫_ℝ = g x * g x = g x ^ 2`.
  have h_pointwise :
      (fun x => ⟪((g : Lp ℝ 2 P) : Ω → ℝ) x,
                 ((g : Lp ℝ 2 P) : Ω → ℝ) x⟫_ℝ)
        =ᵐ[P] fun x => ((g : Lp ℝ 2 P) : Ω → ℝ) x ^ 2 := by
    filter_upwards with x
    change ((g : Lp ℝ 2 P) : Ω → ℝ) x * ((g : Lp ℝ 2 P) : Ω → ℝ) x =
           ((g : Lp ℝ 2 P) : Ω → ℝ) x ^ 2
    ring
  rw [integral_congr_ae h_pointwise] at h_inner_self
  exact h_inner_self

/-! ## Per-direction iid setup on `infinitePi` -/

/-- Per-coordinate evaluation of `g` on the iid Kolmogorov extension. -/
private noncomputable def Yseq
    (g : ↥(L2ZeroMean P)) (k : ℕ) (ω : ℕ → Ω) : ℝ :=
  ((g : Lp ℝ 2 P) : Ω → ℝ) (ω k)

private lemma measurable_Yseq (g : ↥(L2ZeroMean P)) (k : ℕ) :
    Measurable (Yseq (P := P) g k) :=
  ((Lp.stronglyMeasurable _).measurable).comp (measurable_pi_apply _)

private lemma Yseq_eq_comp (g : ↥(L2ZeroMean P)) (k : ℕ) :
    Yseq (P := P) g k =
      (fun x : Ω => ((g : Lp ℝ 2 P) : Ω → ℝ) x) ∘ (fun ω : ℕ → Ω => ω k) := rfl

/-! ## Main theorem -/

/-- **Per-direction scalar score-sum CLT under `Pⁿ`.**

For any `g ∈ ↥(L2ZeroMean P)`, the law of the standardised scalar score sum
`Δ_{n,g}(X) := (√n)⁻¹ · ∑ⱼ g(Xⱼ)` under `Pⁿ = Measure.pi (fun _ : Fin n => P)`
converges weakly to `gaussianReal 0 ‖g‖²`.

This is the per-direction joint LAN brick. For finite-index joint statements,
paste across directions via the Cramér–Wold device.

Strategy: Apply Mathlib's 1-D iid CLT
`tendstoInDistribution_inv_sqrt_mul_sum_sub` to the iid sequence
`Y k ω := g(ω k)` on `Measure.infinitePi (fun _ : ℕ => P)`, exploiting
`g ∈ L2ZeroMean P` ⇒ mean-zero ⇒ `∑ⱼ Y j − n·E[Y 0] = ∑ⱼ Y j`.
Bridge `Pⁿ`-form to the `infinitePi` form via
`AsymptoticStatistics.pi_const_eq_infinitePi_map`.

Reference: vdV §25.3. -/
theorem weakConverges_scoreSumScalar_under_pi
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (g : ↥(L2ZeroMean P)) :
    WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P)).map (scoreSumScalar (P := P) g n))
      (gaussianReal 0 (‖(g : Lp ℝ 2 P)‖ ^ 2).toNNReal) := by
  classical
  -- Set up the iid Kolmogorov extension and the per-coordinate sequence.
  set Pinf : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P) with hPinf_def
  haveI hPinf_prob : IsProbabilityMeasure Pinf := by
    rw [hPinf_def]; infer_instance
  -- iid + ident under `Pinf` for `Yseq g`.
  have h_eval_iid : ProbabilityTheory.iIndepFun
      (fun k (ωi : ℕ → Ω) => ωi k) Pinf := by
    rw [hPinf_def]
    exact ProbabilityTheory.iIndepFun_infinitePi
      (X := fun (_ : ℕ) (x : Ω) => x) (fun _ => measurable_id)
  have hY_iid : ProbabilityTheory.iIndepFun (Yseq (P := P) g) Pinf := by
    refine h_eval_iid.comp (g := fun _ => fun x : Ω => ((g : Lp ℝ 2 P) : Ω → ℝ) x)
      (fun _ => ?_)
    exact (Lp.stronglyMeasurable _).measurable
  have h_eval_law : ∀ k : ℕ, Pinf.map (fun ωi : ℕ → Ω => ωi k) = P := by
    intro k
    rw [hPinf_def]
    exact MeasureTheory.Measure.infinitePi_map_eval (fun _ : ℕ => P) k
  have hY_law : ∀ k : ℕ,
      Pinf.map (Yseq (P := P) g k) =
        P.map (fun x => ((g : Lp ℝ 2 P) : Ω → ℝ) x) := by
    intro k
    have h_eval_meas : Measurable (fun ω : ℕ → Ω => ω k) :=
      measurable_pi_apply k
    have h_g_meas : Measurable (fun x : Ω => ((g : Lp ℝ 2 P) : Ω → ℝ) x) :=
      (Lp.stronglyMeasurable _).measurable
    rw [Yseq_eq_comp, ← Measure.map_map h_g_meas h_eval_meas, h_eval_law k]
  have hident : ∀ k, ProbabilityTheory.IdentDistrib
      (Yseq (P := P) g k) (Yseq (P := P) g 0) Pinf Pinf := fun k =>
    ⟨(measurable_Yseq g k).aemeasurable, (measurable_Yseq g 0).aemeasurable, by
      rw [hY_law k, hY_law 0]⟩
  -- `Y 0` is `MemLp 2` under `Pinf` via `infinitePi_map_eval`.
  have h_memLp : MemLp (Yseq (P := P) g 0) 2 Pinf := by
    rw [Yseq_eq_comp]
    refine (MeasureTheory.memLp_map_measure_iff
      (?_ : AEStronglyMeasurable
        (fun x : Ω => ((g : Lp ℝ 2 P) : Ω → ℝ) x) _)
      (measurable_pi_apply _).aemeasurable).mp ?_
    · rw [h_eval_law 0]; exact (Lp.stronglyMeasurable _).aestronglyMeasurable
    · rw [h_eval_law 0]; exact memLp_two_g g
  -- Mean-zero of `Y 0` under `Pinf`.
  have h_int_Y0 : ∫ ω, Yseq (P := P) g 0 ω ∂Pinf = 0 := by
    -- `Yseq g 0 ω = g (ω 0)`. Push through `eval 0`: `Pinf.map (eval 0) = P`.
    have h_eval0_meas : Measurable (fun ω : ℕ → Ω => ω 0) :=
      measurable_pi_apply 0
    have h_g_meas_strong : AEStronglyMeasurable
        (fun x : Ω => ((g : Lp ℝ 2 P) : Ω → ℝ) x)
        (Pinf.map (fun ω : ℕ → Ω => ω 0)) := by
      rw [h_eval_law 0]; exact (Lp.stronglyMeasurable _).aestronglyMeasurable
    have h_step :
        ∫ ω, Yseq (P := P) g 0 ω ∂Pinf
          = ∫ y, ((g : Lp ℝ 2 P) : Ω → ℝ) y ∂Pinf.map (fun ω : ℕ → Ω => ω 0) :=
      (MeasureTheory.integral_map h_eval0_meas.aemeasurable h_g_meas_strong).symm
    rw [h_step, h_eval_law 0]
    exact integral_g_eq_zero g
  -- Variance of `Y 0` under `Pinf` equals `‖g‖²`.
  have h_var : Var[Yseq (P := P) g 0; Pinf] = ‖(g : Lp ℝ 2 P)‖ ^ 2 := by
    -- Pull through the pushforward identity `Pinf.map (eval 0) = P`.
    have h_AEM : AEMeasurable (Yseq (P := P) g 0) Pinf :=
      (measurable_Yseq g 0).aemeasurable
    rw [variance_of_integral_eq_zero h_AEM h_int_Y0]
    -- Push through the pushforward and identify the integrand.
    rw [Yseq_eq_comp]
    rw [show ((fun x : Ω => ((g : Lp ℝ 2 P) : Ω → ℝ) x)
              ∘ (fun ω : ℕ → Ω => ω 0))
            = fun ω : ℕ → Ω => ((g : Lp ℝ 2 P) : Ω → ℝ) (ω 0) from rfl]
    have h_int_pushforward :
        ∫ ω : ℕ → Ω, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω 0) ^ 2 ∂Pinf
          = ∫ x : Ω, ((g : Lp ℝ 2 P) : Ω → ℝ) x ^ 2 ∂P := by
      have hf_meas : Measurable (fun x : Ω => ((g : Lp ℝ 2 P) : Ω → ℝ) x ^ 2) :=
        ((Lp.stronglyMeasurable _).measurable).pow_const 2
      have h_eval0_meas : Measurable (fun ω : ℕ → Ω => ω 0) :=
        measurable_pi_apply 0
      have hf_meas_strong : AEStronglyMeasurable
          (fun x : Ω => ((g : Lp ℝ 2 P) : Ω → ℝ) x ^ 2)
          (Pinf.map (fun ω : ℕ → Ω => ω 0)) := by
        rw [h_eval_law 0]; exact hf_meas.aestronglyMeasurable
      have h_step :
          ∫ ω : ℕ → Ω, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω 0) ^ 2 ∂Pinf
            = ∫ y, ((g : Lp ℝ 2 P) : Ω → ℝ) y ^ 2 ∂
                Pinf.map (fun ω : ℕ → Ω => ω 0) :=
        (MeasureTheory.integral_map h_eval0_meas.aemeasurable hf_meas_strong).symm
      rw [h_step, h_eval_law 0]
    rw [h_int_pushforward]
    exact integral_g_sq_eq_norm_sq g
  -- Witness for the Gaussian limit law.
  haveI hG_prob : IsProbabilityMeasure
      (gaussianReal 0 (‖(g : Lp ℝ 2 P)‖ ^ 2).toNNReal) := inferInstance
  have hY_id : @HasLaw ℝ ℝ _ _ id
      (gaussianReal 0 (‖(g : Lp ℝ 2 P)‖ ^ 2).toNNReal)
      (gaussianReal 0 (‖(g : Lp ℝ 2 P)‖ ^ 2).toNNReal) := HasLaw.id
  -- Apply Mathlib's 1-D iid CLT (sum-minus-mean form).
  have h_mean_subst : (Var[Yseq (P := P) g 0; Pinf]).toNNReal
      = (‖(g : Lp ℝ 2 P)‖ ^ 2).toNNReal := by
    rw [h_var]
  have h_TID :
      MeasureTheory.TendstoInDistribution
        (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
          (∑ k ∈ Finset.range n, Yseq (P := P) g k ω -
            n * Pinf[Yseq (P := P) g 0]))
        atTop (id : ℝ → ℝ)
        (fun _ => Pinf)
        (gaussianReal 0 (‖(g : Lp ℝ 2 P)‖ ^ 2).toNNReal) := by
    have h := tendstoInDistribution_inv_sqrt_mul_sum_sub
      (X := Yseq (P := P) g) (Y := id)
      (P := Pinf)
      (P' := gaussianReal 0 (‖(g : Lp ℝ 2 P)‖ ^ 2).toNNReal)
      (by rw [h_mean_subst]; exact hY_id) h_memLp hY_iid hident
    exact h
  -- Replace `n * Pinf[Y 0]` by `0` and `Finset.range n` by `Fin n`.
  have h_simplify : ∀ n : ℕ, ∀ ω : ℕ → Ω,
      (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, Yseq (P := P) g k ω -
          n * Pinf[Yseq (P := P) g 0])
      = (Real.sqrt n)⁻¹ *
          ∑ j : Fin n, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω j.val) := by
    intro n ω
    rw [h_int_Y0, mul_zero, sub_zero]
    congr 1
    -- `Yseq g k ω = (g : Lp) (ω k)` definitionally; unfold first.
    change ∑ k ∈ Finset.range n, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω k)
        = ∑ j : Fin n, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω j.val)
    -- `∑ k ∈ range n, f k = ∑ j : Fin n, f j.val`.
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => ((g : Lp ℝ 2 P) : Ω → ℝ) (ω k))]
  -- Convert `TendstoInDistribution` (under `Pinf`) to `WeakConverges`.
  have h_weak_inf :
      WeakConverges
        (fun n : ℕ => Pinf.map
          (fun ω : ℕ → Ω => (Real.sqrt n)⁻¹ *
            ∑ j : Fin n, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω j.val)))
        (gaussianReal 0 (‖(g : Lp ℝ 2 P)‖ ^ 2).toNNReal) := by
    intro f
    have h_t := h_TID.tendsto
    -- Convert via `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`.
    replace h_t := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h_t
    have h_t_f := h_t f
    -- `id ∘ Z = Z`. The pushforward by `id` on the limit measure is itself.
    have h_id : (gaussianReal 0 (‖(g : Lp ℝ 2 P)‖ ^ 2).toNNReal).map
        (id : ℝ → ℝ) = gaussianReal 0 (‖(g : Lp ℝ 2 P)‖ ^ 2).toNNReal :=
      Measure.map_id
    -- The integrand on each side equals the simplified form pointwise.
    have h_integrand_eq : ∀ n : ℕ, ∀ ω : ℕ → Ω,
        (Real.sqrt n)⁻¹ *
          (∑ k ∈ Finset.range n, Yseq (P := P) g k ω -
            n * Pinf[Yseq (P := P) g 0])
        = (Real.sqrt n)⁻¹ *
            ∑ j : Fin n, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω j.val) := h_simplify
    have h_map_eq : ∀ n : ℕ,
        Pinf.map (fun ω => (Real.sqrt n)⁻¹ *
          (∑ k ∈ Finset.range n, Yseq (P := P) g k ω -
            n * Pinf[Yseq (P := P) g 0]))
        = Pinf.map (fun ω => (Real.sqrt n)⁻¹ *
            ∑ j : Fin n, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω j.val)) := by
      intro n
      congr 1
      funext ω
      exact h_integrand_eq n ω
    simp_rw [← h_map_eq]
    -- `h_t_f` is the integral-form `Tendsto` from
    -- `tendsto_iff_forall_integral_tendsto` applied to `f`.
    -- Its limit is `∫ f ∂(gaussianReal _).map id = ∫ f ∂gaussianReal _`.
    rw [← h_id]
    exact h_t_f
  -- Bridge from `Pinf`-form to `Pⁿ`-form via `pi_const_eq_infinitePi_map`.
  intro f
  have h_inf := h_weak_inf f
  -- For each `n`, the `Pⁿ`-pushforward equals the `Pinf`-pushforward of the
  -- composed map `(fun ω => fun j : Fin n => ω j.val)` followed by the
  -- score-sum.
  have h_pushforward_eq : ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P)).map (scoreSumScalar (P := P) g n)
      = Pinf.map (fun ω : ℕ → Ω =>
          (Real.sqrt n)⁻¹ *
          ∑ j : Fin n, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω j.val)) := by
    intro n
    have h_pi := AsymptoticStatistics.pi_const_eq_infinitePi_map P n
    rw [h_pi]
    have h_truncate_meas :
        Measurable (fun ω : ℕ → Ω => fun i : Fin n => ω i.val) := by
      refine measurable_pi_lambda _ (fun i => ?_)
      exact measurable_pi_apply _
    have h_score_meas : Measurable (scoreSumScalar (P := P) g n) :=
      measurable_scoreSumScalar g n
    rw [Measure.map_map h_score_meas h_truncate_meas]
    rfl
  simp_rw [h_pushforward_eq]
  exact h_inf

end JointLAN
end AsymptoticStatistics.LowerBounds.T6_FinDimLAN
