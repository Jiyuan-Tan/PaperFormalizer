module
public import StatLean.AsymptoticStatistics.ParametricFamily.ScoreCLT
public import StatLean.AsymptoticStatistics.Core.Hilbert
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Score-sum CLT under the infinite product measure

This file provides `cltInf_at_orthonormal_basis`, a self-contained
discharge of the `hCLT_inf` hypothesis consumed by `finDimSubmodel_lan`.

## Statement

For an `L²(P)`-orthonormal basis `g_P : Fin m → ↥(L2ZeroMean P)`, viewed
on the iid Kolmogorov extension `Measure.infinitePi (fun _ : ℕ => P)`,
the standardised score-sum statistic
`(√n)⁻¹ · ∑ⱼ ((g_P i) (ωi j.val))_{i ∈ Fin m}` converges weakly (against
bounded continuous test functions) to
`stdGaussian (EuclideanSpace ℝ (Fin m))`.

## Strategy

The proof reduces to
`AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim` with `J = 1`
(identity covariance):

* iid coordinate evaluation under `infinitePi` is `iIndepFun_infinitePi`.
* `IdentDistrib (X i) (X 0)` is `infinitePi_map_eval` plus the same map.
* Zero mean of `X 0` follows from `g_P i ∈ L2ZeroMean P`.
* `J = 1` covariance is the orthonormality `h_orth` translated through
  `MeasureTheory.L2.inner_def`.
* `MemLp (X 0) 2` follows from each `g_P i ∈ Lp ℝ 2 P`.

`multivariateGaussian 0 1 = stdGaussian` closes via
`ProbabilityTheory.multivariateGaussian_zero_one`.

The output of `clt_finDim` uses `Finset.range n` indexing; the target
form uses `Fin n` indexing on `ω j.val`. These match via
`Fin.sum_univ_eq_sum_range`.

Reference: vdV §25.3.
-/

open MeasureTheory Filter Topology ProbabilityTheory Matrix
open scoped InnerProductSpace ENNReal RealInnerProductSpace Matrix BigOperators

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics
open AsymptoticStatistics.ParametricFamily.ScoreCLT

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Internal helpers — `private` because they are byproducts of the
proof and do not deserve a stable user-facing name. -/

section Helpers

variable {m : ℕ}

/-- The vectorised coordinate evaluation
`X k ωi = (g_P i (ωi k))_{i ∈ Fin m}`, which we feed into the
multivariate iid CLT. -/
private noncomputable def Xseq (g_P : Fin m → ↥(L2ZeroMean P))
    (k : ℕ) (ω : ℕ → Ω) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i : Fin m => ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (ω k))

/-- The atomic (single-coordinate) version of `Xseq`: a function `Ω → ℝ^m`
that we then compose with each evaluation `ωi ↦ ωi k`. -/
private noncomputable def XseqAtom (g_P : Fin m → ↥(L2ZeroMean P)) (x : Ω) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i : Fin m => ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x)

private lemma Xseq_eq_atom_comp_eval (g_P : Fin m → ↥(L2ZeroMean P)) (k : ℕ) :
    Xseq g_P k = (XseqAtom g_P) ∘ (fun ω : ℕ → Ω => ω k) := rfl

private lemma measurable_XseqAtom (g_P : Fin m → ↥(L2ZeroMean P)) :
    Measurable (XseqAtom (P := P) g_P) := by
  unfold XseqAtom
  refine (WithLp.measurable_toLp 2 (Fin m → ℝ)).comp ?_
  refine measurable_pi_lambda _ (fun i => ?_)
  exact (Lp.stronglyMeasurable _).measurable

private lemma measurable_Xseq (g_P : Fin m → ↥(L2ZeroMean P)) (k : ℕ) :
    Measurable (Xseq g_P k) := by
  rw [Xseq_eq_atom_comp_eval]
  exact (measurable_XseqAtom g_P).comp (measurable_pi_apply _)

/-- Each `(g_P i : Lp ℝ 2 P)` is integrable under `P`: it lies in
`Lp 2 P`, hence in `Lp 1 P` (since `P` is finite), hence is integrable. -/
private lemma integrable_g_coe (g_P : Fin m → ↥(L2ZeroMean P)) (i : Fin m) :
    Integrable (fun x => ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x) P := by
  have h_memLp2 : MemLp ((g_P i : Lp ℝ 2 P) : Ω → ℝ) 2 P := Lp.memLp _
  have h_memLp1 : MemLp ((g_P i : Lp ℝ 2 P) : Ω → ℝ) 1 P :=
    h_memLp2.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact memLp_one_iff_integrable.mp h_memLp1

/-- `(XseqAtom g_P x) i = (g_P i : Lp) x` (definitional). -/
private lemma XseqAtom_apply (g_P : Fin m → ↥(L2ZeroMean P)) (x : Ω) (i : Fin m) :
    (XseqAtom g_P x) i = ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x := rfl

/-- The pointwise expansion of `⟪t, XseqAtom g_P x⟫_ℝ` as a real-coefficient
linear combination of the `(g_P i)` representatives. -/
private lemma inner_XseqAtom (g_P : Fin m → ↥(L2ZeroMean P))
    (t : EuclideanSpace ℝ (Fin m)) (x : Ω) :
    ⟪t, XseqAtom g_P x⟫_ℝ
      = ∑ i : Fin m, t i * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- `⟪t i, (XseqAtom g_P x) i⟫_ℝ = (XseqAtom g_P x) i * t i = (g_P i) x * t i`.
  -- We want `t i * (g_P i) x`. Use `mul_comm`.
  rw [XseqAtom_apply]
  -- The real RCLike inner is `b * a`.  Reduce by `change` (defeq).
  change ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x * t i = t i * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x
  ring

/-- For `u : EuclideanSpace ℝ (Fin m)`, `u.ofLp i = u i` (definitional). -/
private lemma ofLp_apply (u : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    u.ofLp i = u i := rfl

end Helpers

/-! ## Main theorem -/

/-- **Score-sum CLT under the infinite product measure.**

For an `L²(P)`-orthonormal basis `g_P : Fin m → ↥(L2ZeroMean P)`, the
standardised vectorised partial sum on `(Fin m)`-coordinates of an iid
sequence on `Measure.infinitePi P` converges weakly to the standard
multivariate Gaussian on `EuclideanSpace ℝ (Fin m)`.

This is the discharge of the `hCLT_inf` hypothesis in `finDimSubmodel_lan`.

Reference: vdV §25.3. -/
theorem cltInf_at_orthonormal_basis
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    WeakConverges
      (fun n : ℕ =>
        (Measure.infinitePi (fun _ : ℕ => P)).map
          (fun ω : ℕ → Ω =>
            WithLp.toLp 2 (fun i : Fin m =>
              (Real.sqrt n)⁻¹ *
              ∑ j : Fin n, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (ω j.val))))
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  classical
  -- Set up the iid Kolmogorov extension and the vectorised score family.
  set Pinf : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P) with hPinf_def
  haveI hPinf_prob : IsProbabilityMeasure Pinf := by
    rw [hPinf_def]; infer_instance
  set Y : ℕ → (ℕ → Ω) → EuclideanSpace ℝ (Fin m) := Xseq g_P with hY_def
  -- Measurability and atom identity.
  have hY_meas : ∀ k, Measurable (Y k) := fun k => measurable_Xseq g_P k
  have h_atom_meas : Measurable (XseqAtom (P := P) g_P) := measurable_XseqAtom g_P
  have h_eval_meas : ∀ k : ℕ, Measurable (fun ωi : ℕ → Ω => ωi k) := fun k =>
    measurable_pi_apply _
  -- ---------------------------------------------------------------
  -- (1) iid + ident under `infinitePi`.
  -- ---------------------------------------------------------------
  have h_eval_iid : ProbabilityTheory.iIndepFun
      (fun k (ωi : ℕ → Ω) => ωi k) Pinf := by
    rw [hPinf_def]
    exact ProbabilityTheory.iIndepFun_infinitePi
      (X := fun (_ : ℕ) (x : Ω) => x) (fun _ => measurable_id)
  have hY_iid : ProbabilityTheory.iIndepFun Y Pinf := by
    have hY_eq : Y = fun k ωi => XseqAtom g_P (ωi k) := rfl
    rw [hY_eq]
    exact h_eval_iid.comp (g := fun _ => XseqAtom g_P) (fun _ => h_atom_meas)
  have h_eval_law : ∀ k : ℕ, Pinf.map (fun ωi : ℕ → Ω => ωi k) = P := by
    intro k
    rw [hPinf_def]
    exact MeasureTheory.Measure.infinitePi_map_eval (fun _ : ℕ => P) k
  have hY_law : ∀ k, Pinf.map (Y k) = P.map (XseqAtom g_P) := by
    intro k
    have h_comp : Y k = (XseqAtom g_P) ∘ (fun ωi : ℕ → Ω => ωi k) :=
      Xseq_eq_atom_comp_eval g_P k
    rw [h_comp, ← Measure.map_map h_atom_meas (h_eval_meas k), h_eval_law k]
  have hident : ∀ k, ProbabilityTheory.IdentDistrib (Y k) (Y 0) Pinf Pinf := fun k =>
    ⟨(hY_meas k).aemeasurable, (hY_meas 0).aemeasurable, by rw [hY_law k, hY_law 0]⟩
  -- ---------------------------------------------------------------
  -- (2) Zero mean of Y 0 under Pinf, in inner-product sense.
  -- ---------------------------------------------------------------
  have h_g_int_zero : ∀ i : Fin m,
      ∫ x, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x ∂P = 0 := by
    intro i
    have h_mem : (g_P i : Lp ℝ 2 P) ∈ L2ZeroMean P := (g_P i).2
    have h_ker : integralL2 P (g_P i : Lp ℝ 2 P) = 0 := by
      change (g_P i : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap at h_mem
      rw [LinearMap.mem_ker] at h_mem
      exact h_mem
    have h_inner : (⟪(oneL2 P : Lp ℝ 2 P), (g_P i : Lp ℝ 2 P)⟫_ℝ : ℝ) = 0 := h_ker
    rw [MeasureTheory.L2.inner_def] at h_inner
    have h_one_ae : ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    have h_pointwise :
        (fun x => ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) x,
                   ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x⟫_ℝ)
            =ᵐ[P]
        fun x => ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x := by
      filter_upwards [h_one_ae] with x hx
      have hcomm :
          ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) x,
            ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x⟫_ℝ
            = ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x
                * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) x := rfl
      rw [hcomm, hx, mul_one]
    rw [integral_congr_ae h_pointwise] at h_inner
    exact h_inner
  have h_zero_mean : ∀ t : EuclideanSpace ℝ (Fin m),
      ∫ ωi, ⟪t, Y 0 ωi⟫_ℝ ∂Pinf = 0 := by
    intro t
    have h_inner_meas :
        Measurable (fun y : EuclideanSpace ℝ (Fin m) => ⟪t, y⟫_ℝ) :=
      Measurable.const_inner (c := t) measurable_id
    have h_inner_atom_meas :
        Measurable (fun x : Ω => ⟪t, XseqAtom g_P x⟫_ℝ) :=
      h_inner_meas.comp h_atom_meas
    have h_step1 :
        ∫ ωi, ⟪t, Y 0 ωi⟫_ℝ ∂Pinf
          = ∫ x, ⟪t, XseqAtom g_P x⟫_ℝ ∂P := by
      have h_int_via_map :
          ∫ x, ⟪t, XseqAtom g_P x⟫_ℝ ∂(Pinf.map (fun ωi : ℕ → Ω => ωi 0))
            = ∫ ωi, ⟪t, XseqAtom g_P (ωi 0)⟫_ℝ ∂Pinf := by
        refine MeasureTheory.integral_map (h_eval_meas 0).aemeasurable ?_
        rw [h_eval_law 0]
        exact h_inner_atom_meas.aestronglyMeasurable
      rw [h_eval_law 0] at h_int_via_map
      exact h_int_via_map.symm
    rw [h_step1]
    have h_expand : (fun x : Ω => ⟪t, XseqAtom g_P x⟫_ℝ)
        =ᵐ[P] fun x => ∑ i : Fin m, t i * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x := by
      filter_upwards with x; exact inner_XseqAtom g_P t x
    rw [integral_congr_ae h_expand]
    have h_each_int : ∀ i : Fin m,
        Integrable (fun x : Ω =>
          t i * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x) P := fun i =>
      (integrable_g_coe g_P i).const_mul (t i)
    rw [MeasureTheory.integral_finset_sum _ (fun i _ => h_each_int i)]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul, h_g_int_zero i, mul_zero]
  -- ---------------------------------------------------------------
  -- (3) Covariance: `J = 1` (identity) under orthonormality.
  -- ---------------------------------------------------------------
  -- `⟪g_P i, g_P j⟫_(Lp 2 P) = δᵢⱼ` by orthonormality.
  have h_g_inner : ∀ i j : Fin m,
      ⟪(g_P i : Lp ℝ 2 P), (g_P j : Lp ℝ 2 P)⟫_ℝ =
        (if i = j then 1 else 0 : ℝ) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h_norm := h_orth.norm_eq_one i
      rw [real_inner_self_eq_norm_sq, h_norm]
      simp
    · have := h_orth.inner_eq_zero hij
      simp [this, hij]
  -- Translate `⟪g_P i, g_P j⟫_(Lp 2 P) = δᵢⱼ` to integral form.
  have h_g_prod_int : ∀ i j : Fin m,
      ∫ x, ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x *
            ((g_P j : Lp ℝ 2 P) : Ω → ℝ) x ∂P =
        (if i = j then 1 else 0 : ℝ) := by
    intro i j
    have h := h_g_inner i j
    rw [MeasureTheory.L2.inner_def] at h
    have h_swap : ∫ x, ⟪((g_P i : Lp ℝ 2 P) : Ω → ℝ) x,
                       ((g_P j : Lp ℝ 2 P) : Ω → ℝ) x⟫_ℝ ∂P =
                  ∫ x, ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x *
                       ((g_P j : Lp ℝ 2 P) : Ω → ℝ) x ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change ((g_P j : Lp ℝ 2 P) : Ω → ℝ) x * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x =
             ((g_P i : Lp ℝ 2 P) : Ω → ℝ) x * ((g_P j : Lp ℝ 2 P) : Ω → ℝ) x
      ring
    rw [h_swap] at h
    exact h
  have h_cov : ∀ u v : EuclideanSpace ℝ (Fin m),
      ∫ ωi, ⟪u, Y 0 ωi⟫_ℝ * ⟪v, Y 0 ωi⟫_ℝ ∂Pinf =
      u.ofLp ⬝ᵥ (1 : Matrix (Fin m) (Fin m) ℝ).mulVec v.ofLp := by
    intro u v
    -- LHS: Push through `eval 0` to P, then expand inner products and use
    -- orthonormality.
    have h_inner_u_meas :
        Measurable (fun y : EuclideanSpace ℝ (Fin m) => ⟪u, y⟫_ℝ) :=
      Measurable.const_inner (c := u) measurable_id
    have h_inner_v_meas :
        Measurable (fun y : EuclideanSpace ℝ (Fin m) => ⟪v, y⟫_ℝ) :=
      Measurable.const_inner (c := v) measurable_id
    have h_prod_atom_meas :
        Measurable (fun x : Ω =>
          ⟪u, XseqAtom g_P x⟫_ℝ * ⟪v, XseqAtom g_P x⟫_ℝ) :=
      (h_inner_u_meas.comp h_atom_meas).mul (h_inner_v_meas.comp h_atom_meas)
    have h_step1 :
        ∫ ωi, ⟪u, Y 0 ωi⟫_ℝ * ⟪v, Y 0 ωi⟫_ℝ ∂Pinf
          = ∫ x, ⟪u, XseqAtom g_P x⟫_ℝ * ⟪v, XseqAtom g_P x⟫_ℝ ∂P := by
      have h_int_via_map :
          ∫ x, ⟪u, XseqAtom g_P x⟫_ℝ * ⟪v, XseqAtom g_P x⟫_ℝ
              ∂(Pinf.map (fun ωi : ℕ → Ω => ωi 0))
            = ∫ ωi,
                ⟪u, XseqAtom g_P (ωi 0)⟫_ℝ * ⟪v, XseqAtom g_P (ωi 0)⟫_ℝ ∂Pinf := by
        refine MeasureTheory.integral_map (h_eval_meas 0).aemeasurable ?_
        rw [h_eval_law 0]
        exact h_prod_atom_meas.aestronglyMeasurable
      rw [h_eval_law 0] at h_int_via_map
      exact h_int_via_map.symm
    rw [h_step1]
    -- Expand both inner products and distribute.
    have h_each_int : ∀ i j : Fin m,
        Integrable (fun x : Ω =>
          (u i * v j) * (((g_P i : Lp ℝ 2 P) : Ω → ℝ) x *
                         ((g_P j : Lp ℝ 2 P) : Ω → ℝ) x)) P := by
      intro i j
      have h_i : MemLp ((g_P i : Lp ℝ 2 P) : Ω → ℝ) 2 P := Lp.memLp _
      have h_j : MemLp ((g_P j : Lp ℝ 2 P) : Ω → ℝ) 2 P := Lp.memLp _
      exact (h_i.integrable_mul h_j).const_mul (u i * v j)
    have h_step2 :
        ∫ x, ⟪u, XseqAtom g_P x⟫_ℝ * ⟪v, XseqAtom g_P x⟫_ℝ ∂P
          = ∑ i : Fin m, ∑ j : Fin m,
              ∫ x, (u i * v j) * (((g_P i : Lp ℝ 2 P) : Ω → ℝ) x *
                                  ((g_P j : Lp ℝ 2 P) : Ω → ℝ) x) ∂P := by
      have h_pointwise : ∀ x : Ω,
          ⟪u, XseqAtom g_P x⟫_ℝ * ⟪v, XseqAtom g_P x⟫_ℝ =
          ∑ i : Fin m, ∑ j : Fin m,
            (u i * v j) * (((g_P i : Lp ℝ 2 P) : Ω → ℝ) x *
                           ((g_P j : Lp ℝ 2 P) : Ω → ℝ) x) := by
        intro x
        rw [inner_XseqAtom g_P u x, inner_XseqAtom g_P v x, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall h_pointwise)]
      rw [MeasureTheory.integral_finset_sum _ (fun i _ =>
        MeasureTheory.integrable_finset_sum _ (fun j _ => h_each_int i j))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [MeasureTheory.integral_finset_sum _ (fun j _ => h_each_int i j)]
    rw [h_step2]
    -- Each inner integral collapses to `(uᵢ vⱼ) * δᵢⱼ`.
    have h_ij : ∀ i j : Fin m,
        ∫ x, (u i * v j) * (((g_P i : Lp ℝ 2 P) : Ω → ℝ) x *
                            ((g_P j : Lp ℝ 2 P) : Ω → ℝ) x) ∂P =
        (u i * v j) * (if i = j then 1 else 0 : ℝ) := by
      intro i j
      rw [MeasureTheory.integral_const_mul, h_g_prod_int i j]
    have h_step3 :
        ∑ i : Fin m, ∑ j : Fin m,
          ∫ x, (u i * v j) * (((g_P i : Lp ℝ 2 P) : Ω → ℝ) x *
                              ((g_P j : Lp ℝ 2 P) : Ω → ℝ) x) ∂P
          = ∑ i : Fin m, u i * v i := by
      have h_inner_collapse : ∀ i : Fin m,
          ∑ j : Fin m,
            (u i * v j) * (if i = j then 1 else 0 : ℝ) = u i * v i := by
        intro i
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          have : ¬ (i = j) := fun h => hji h.symm
          simp [this]
        · intro h
          exact (h (Finset.mem_univ _)).elim
      calc ∑ i : Fin m, ∑ j : Fin m,
            ∫ x, (u i * v j) * (((g_P i : Lp ℝ 2 P) : Ω → ℝ) x *
                                ((g_P j : Lp ℝ 2 P) : Ω → ℝ) x) ∂P
          = ∑ i : Fin m, ∑ j : Fin m,
              (u i * v j) * (if i = j then 1 else 0 : ℝ) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            refine Finset.sum_congr rfl (fun j _ => ?_)
            exact h_ij i j
        _ = ∑ i : Fin m, u i * v i := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            exact h_inner_collapse i
    rw [h_step3]
    -- RHS: `u.ofLp ⬝ᵥ (1).mulVec v.ofLp = u.ofLp ⬝ᵥ v.ofLp = ∑ i, u i * v i`.
    rw [Matrix.one_mulVec]
    -- `dotProduct` is `∑ i, v i * w i` by definition; `u.ofLp i = u i`.
    change ∑ i : Fin m, u i * v i = ∑ i : Fin m, u.ofLp i * v.ofLp i
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rfl
  -- ---------------------------------------------------------------
  -- (4) MemLp 2: Y 0 has finite second moment under Pinf.
  -- ---------------------------------------------------------------
  have h_atom_L2 : MemLp (XseqAtom (P := P) g_P) 2 P := by
    rw [memLp_two_iff_integrable_sq_norm h_atom_meas.aestronglyMeasurable]
    have h_norm_sq : ∀ x : Ω, ‖XseqAtom g_P x‖ ^ 2 =
        ∑ i : Fin m, (((g_P i : Lp ℝ 2 P) : Ω → ℝ) x) ^ 2 := by
      intro x
      rw [EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [XseqAtom_apply]
    have h_eq : (fun x => ‖XseqAtom g_P x‖ ^ 2) =
        fun x => ∑ i : Fin m, (((g_P i : Lp ℝ 2 P) : Ω → ℝ) x) ^ 2 := by
      funext x; exact h_norm_sq x
    rw [h_eq]
    refine MeasureTheory.integrable_finset_sum _ (fun i _ => ?_)
    have h_i : MemLp ((g_P i : Lp ℝ 2 P) : Ω → ℝ) 2 P := Lp.memLp _
    exact h_i.integrable_sq
  have h_L2 : MemLp (Y 0) 2 Pinf := by
    have h_comp : Y 0 = (XseqAtom g_P) ∘ (fun ωi : ℕ → Ω => ωi 0) :=
      Xseq_eq_atom_comp_eval g_P 0
    rw [h_comp]
    have h_meas_eq : Pinf.map (fun ωi : ℕ → Ω => ωi 0) = P := h_eval_law 0
    refine
      (MeasureTheory.memLp_map_measure_iff (?_ : AEStronglyMeasurable (XseqAtom g_P) _)
        (h_eval_meas 0).aemeasurable).mp ?_
    · rw [h_meas_eq]; exact h_atom_meas.aestronglyMeasurable
    · rw [h_meas_eq]; exact h_atom_L2
  -- ---------------------------------------------------------------
  -- (5) Apply the engine `clt_finDim` with `J = 1`.
  -- ---------------------------------------------------------------
  have hJ_psd : (1 : Matrix (Fin m) (Fin m) ℝ).PosSemidef := Matrix.PosSemidef.one
  have h_engine :
      WeakConverges
        (fun n : ℕ => Pinf.map
          (fun ωi => (Real.sqrt n)⁻¹ • ∑ k ∈ Finset.range n, Y k ωi))
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (1 : Matrix (Fin m) (Fin m) ℝ)) :=
    AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim Pinf Y hY_meas hY_iid hident
      h_zero_mean (1 : Matrix (Fin m) (Fin m) ℝ) hJ_psd h_cov h_L2
  -- Replace `multivariateGaussian 0 1` with `stdGaussian` via
  -- `multivariateGaussian_zero_one`.
  rw [multivariateGaussian_zero_one] at h_engine
  -- ---------------------------------------------------------------
  -- (6) Identify the standardised partial-sum with the target integrand.
  -- ---------------------------------------------------------------
  have h_integrand_eq : ∀ n : ℕ, ∀ ω : ℕ → Ω,
      (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, Y k ω) =
      (WithLp.toLp 2 (fun i : Fin m =>
        (Real.sqrt n)⁻¹ *
        ∑ j : Fin n, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (ω j.val))
        : EuclideanSpace ℝ (Fin m)) := by
    intro n ω
    -- Coordinate-wise equality. The LHS at `i`:
    --   ((√n)⁻¹ • ∑ k ∈ range n, Y k ω) i
    --     = (√n)⁻¹ * ∑ k ∈ range n, (Y k ω) i
    --     = (√n)⁻¹ * ∑ k ∈ range n, (g_P i) (ω k).
    -- The RHS at `i`:
    --   (WithLp.toLp 2 (fun i => (√n)⁻¹ * ∑ j : Fin n, (g_P i) (ω j.val))) i
    --     = (√n)⁻¹ * ∑ j : Fin n, (g_P i) (ω j.val).
    -- Bridge: `Fin.sum_univ_eq_sum_range`.
    apply (WithLp.equiv 2 (Fin m → ℝ)).injective
    funext i
    -- Pass to coordinates via `ofLp`, which is a linear bijection from
    -- `EuclideanSpace ℝ (Fin m)` to `Fin m → ℝ`.
    change (((Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, Y k ω) :
            EuclideanSpace ℝ (Fin m)).ofLp) i =
         ((WithLp.toLp 2 (fun i : Fin m =>
            (Real.sqrt n)⁻¹ *
            ∑ j : Fin n, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (ω j.val))
            : EuclideanSpace ℝ (Fin m)).ofLp) i
    -- The smul on `EuclideanSpace = WithLp 2 (Fin m → ℝ)` is pointwise on
    -- coordinates; the sum likewise. We unfold via the underlying `ofLp`.
    have h_sum_apply :
        (((∑ k ∈ Finset.range n, Y k ω) : EuclideanSpace ℝ (Fin m)).ofLp) i =
        ∑ k ∈ Finset.range n, ((Y k ω : EuclideanSpace ℝ (Fin m)).ofLp) i := by
      -- `WithLp.linearEquiv 2 ℝ (Fin m → ℝ)` is a linear equivalence and hence
      -- distributes over finite sums via the generic `map_sum`.
      have h_lin : (((∑ k ∈ Finset.range n, Y k ω)
            : EuclideanSpace ℝ (Fin m)).ofLp) =
            ∑ k ∈ Finset.range n,
              ((Y k ω : EuclideanSpace ℝ (Fin m)).ofLp) :=
        map_sum (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap _ _
      rw [h_lin]
      exact Finset.sum_apply (M := fun _ : Fin m => ℝ) i _ _
    rw [show (((Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, Y k ω) :
            EuclideanSpace ℝ (Fin m)).ofLp) i =
        (Real.sqrt n)⁻¹ *
          (((∑ k ∈ Finset.range n, Y k ω) : EuclideanSpace ℝ (Fin m)).ofLp) i
        from rfl]
    rw [h_sum_apply]
    -- RHS: `((WithLp.toLp 2 _).ofLp) i = _ i`.
    change (Real.sqrt n)⁻¹ *
        ∑ k ∈ Finset.range n, ((Y k ω : EuclideanSpace ℝ (Fin m)).ofLp) i =
        (Real.sqrt n)⁻¹ *
        ∑ j : Fin n, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (ω j.val)
    congr 1
    -- `(Y k ω).ofLp i = (g_P i) (ω k)` (definitional).
    have h_Y : ∀ k, ((Y k ω : EuclideanSpace ℝ (Fin m)).ofLp) i =
        ((g_P i : Lp ℝ 2 P) : Ω → ℝ) (ω k) := fun k => rfl
    simp_rw [h_Y]
    -- `∑ k ∈ range n, f k = ∑ j : Fin n, f j.val` via `Fin.sum_univ_eq_sum_range`.
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => ((g_P i : Lp ℝ 2 P) : Ω → ℝ) (ω k))]
  -- Transport `h_engine` through the integrand identification.
  intro f
  have h := h_engine f
  have h_pf_eq : ∀ n : ℕ,
      Pinf.map (fun ωi => (Real.sqrt n)⁻¹ • ∑ k ∈ Finset.range n, Y k ωi) =
      Pinf.map (fun ω : ℕ → Ω =>
        WithLp.toLp 2 (fun i : Fin m =>
          (Real.sqrt n)⁻¹ *
          ∑ j : Fin n, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (ω j.val))) := by
    intro n
    congr 1
    funext ω
    exact h_integrand_eq n ω
  simp_rw [h_pf_eq] at h
  exact h
end AsymptoticStatistics.LowerBounds.T6_FinDimLAN
