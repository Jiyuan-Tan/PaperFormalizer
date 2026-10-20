module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.JointInfluenceCoordinates
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.GaussianL2Closure
public import StatLean.AsymptoticStatistics.ForMathlib.Prohorov
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperationalVec

@[expose] public section

/-!
# Gaussian extension of a Brownian bridge by finite influence coordinates

This module constructs the tight centered Gaussian coupling required by
van der Vaart Theorem 19.23 from an explicit L² assumption on the class.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal InnerProductSpace
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperationalVec

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem jointCov_comm
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) (a b : Sum ↥F (Fin k)) :
    jointCov P ψ a b = jointCov P ψ b a := by
  unfold jointCov
  congr 1
  · apply integral_congr_ae
    filter_upwards [] with x
    ring
  · ring

private noncomputable def centeredClassLp
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (f : ↥F) : Lp ℝ 2 P :=
  (hF_L2 f f.2).toLp (f : Ω → ℝ) -
    (memLp_const (∫ x, (f : Ω → ℝ) x ∂P)).toLp
      (fun _ : Ω => ∫ x, (f : Ω → ℝ) x ∂P)

private theorem inner_centeredClassLp
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (f g : ↥F) :
    ⟪ centeredClassLp P hF_L2 f, centeredClassLp P hF_L2 g ⟫_ℝ =
      jointCov P (fun i : Fin 0 => Fin.elim0 i) (Sum.inl f) (Sum.inl g) := by
  rw [L2.inner_def]
  set cf : ℝ := ∫ x, (f : Ω → ℝ) x ∂P with hcf
  set cg : ℝ := ∫ x, (g : Ω → ℝ) x ∂P with hcg
  have hf := hF_L2 f f.2
  have hg := hF_L2 g g.2
  have hf_int : Integrable (f : Ω → ℝ) P := hf.integrable (by norm_num)
  have hg_int : Integrable (g : Ω → ℝ) P := hg.integrable (by norm_num)
  have hcentf : (⇑(centeredClassLp P hF_L2 f) : Ω → ℝ) =ᵐ[P]
      fun x => (f : Ω → ℝ) x - cf := by
    apply (Lp.coeFn_sub _ _).trans
    filter_upwards [hf.coeFn_toLp,
      (memLp_const cf).coeFn_toLp] with x hfx hcx
    simp only [Pi.sub_apply]
    rw [hfx, hcx]
  have hcentg : (⇑(centeredClassLp P hF_L2 g) : Ω → ℝ) =ᵐ[P]
      fun x => (g : Ω → ℝ) x - cg := by
    apply (Lp.coeFn_sub _ _).trans
    filter_upwards [hg.coeFn_toLp,
      (memLp_const cg).coeFn_toLp] with x hgx hcx
    simp only [Pi.sub_apply]
    rw [hgx, hcx]
  rw [integral_congr_ae (by
    filter_upwards [hcentf, hcentg] with x hfx hgx
    change (centeredClassLp P hF_L2 g : Ω → ℝ) x *
      (centeredClassLp P hF_L2 f : Ω → ℝ) x = _
    rw [hfx, hgx])]
  have hfg_int : Integrable (fun x => (f : Ω → ℝ) x * (g : Ω → ℝ) x) P :=
    hf.integrable_mul hg
  have hexp : (fun x => ((g : Ω → ℝ) x - cg) * ((f : Ω → ℝ) x - cf)) =
      fun x => (f : Ω → ℝ) x * (g : Ω → ℝ) x
        - cg * (f : Ω → ℝ) x - cf * (g : Ω → ℝ) x + cf * cg := by
    funext x
    ring
  rw [hexp]
  have h1 : Integrable (fun x => (f : Ω → ℝ) x * (g : Ω → ℝ) x
      - cg * (f : Ω → ℝ) x) P := hfg_int.sub (hf_int.const_mul cg)
  have h2 : Integrable (fun x => (f : Ω → ℝ) x * (g : Ω → ℝ) x
      - cg * (f : Ω → ℝ) x - cf * (g : Ω → ℝ) x) P :=
    h1.sub (hg_int.const_mul cf)
  rw [integral_add h2 (integrable_const _),
    integral_sub h1 (hg_int.const_mul cf),
    integral_sub hfg_int (hf_int.const_mul cg), integral_const_mul, integral_const_mul,
    integral_const]
  simp only [jointCov, jointIndexFunction, probReal_univ, smul_eq_mul, one_mul]
  rw [← hcf, ← hcg]
  ring

/-- The covariance matrix of a finite family of `L²(P)` functions is positive
semidefinite; this also covers the empty family when `m = 0`. -/
theorem marginalCovMatrix_posSemidef_of_memLp
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}
    (f : Fin m → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 P) :
    (marginalCovMatrix P f).PosSemidef := by
  let F : Set (Ω → ℝ) := Set.range f
  let hF : ∀ g ∈ F, MemLp g 2 P := fun g hg => by
    rcases hg with ⟨i, rfl⟩
    exact hf i
  let fi : Fin m → ↥F := fun i => ⟨f i, ⟨i, rfl⟩⟩
  have heq : marginalCovMatrix P f =
      Matrix.gram ℝ (fun i => centeredClassLp P hF (fi i)) := by
    ext i j
    rw [Matrix.gram_apply, inner_centeredClassLp hF (fi i) (fi j)]
    simp [marginalCovMatrix, marginalCovEntry, jointCov, jointIndexFunction, fi]
  rw [heq]
  exact Matrix.posSemidef_gram ℝ _

private theorem bridgeEval_memLp
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {nu : Measure (LinfF F)} (hnu : IsPBrownianBridge F P nu) (f : ↥F) :
    MemLp (fun z : LinfF F => z f) 2 nu := by
  let pr : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have h := (hnu.isGaussian_fdd 1 (fun _ => f)).map pr
  simpa only [Function.comp_apply, pr] using! h.memLp_two

private noncomputable def bridgeEvalLp
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {nu : Measure (LinfF F)} (hnu : IsPBrownianBridge F P nu) (f : ↥F) :
    Lp ℝ 2 nu :=
  (bridgeEval_memLp hnu f).toLp (fun z => z f)

private theorem inner_bridgeEvalLp
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {nu : Measure (LinfF F)} (hnu : IsPBrownianBridge F P nu) (f g : ↥F) :
    ⟪ bridgeEvalLp hnu f, bridgeEvalLp hnu g ⟫_ℝ =
      jointCov P (fun i : Fin 0 => Fin.elim0 i) (Sum.inl f) (Sum.inl g) := by
  rw [L2.inner_def]
  rw [integral_congr_ae (by
    filter_upwards [(bridgeEval_memLp hnu f).coeFn_toLp,
      (bridgeEval_memLp hnu g).coeFn_toLp] with z hf hg
    change (bridgeEvalLp hnu g : LinfF F → ℝ) z *
      (bridgeEvalLp hnu f : LinfF F → ℝ) z = _
    simp only [bridgeEvalLp]
    rw [hf, hg])]
  calc
    (∫ z : LinfF F, z g * z f ∂nu) = ∫ z : LinfF F, z f * z g ∂nu := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    _ = jointCov P (fun i : Fin 0 => Fin.elim0 i) (Sum.inl f) (Sum.inl g) := by
      simpa only [jointCov, jointIndexFunction] using hnu.cov f g

/-! The covariance-preserving extension from the closed span of the centred
class in `L²(P)` to the closed span of the bridge evaluations in `L²(ν)`. -/

private noncomputable def centeredCombination
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) :
    (↥F →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 P :=
  Finsupp.linearCombination ℝ (centeredClassLp P hF_L2)

private noncomputable def bridgeCombination
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν) :
    (↥F →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 ν :=
  Finsupp.linearCombination ℝ (bridgeEvalLp hν)

private theorem inner_centeredCombination_eq_bridgeCombination
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (u v : ↥F →₀ ℝ) :
    ⟪centeredCombination P hF_L2 u, centeredCombination P hF_L2 v⟫_ℝ =
      ⟪bridgeCombination hν u, bridgeCombination hν v⟫_ℝ := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ hu₁ hu₂ => simp only [map_add, inner_add_left, hu₁, hu₂]
  | single f c =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v₁ v₂ hv₁ hv₂ => simp only [map_add, inner_add_right, hv₁, hv₂]
      | single g d =>
          simp only [centeredCombination, bridgeCombination,
            Finsupp.linearCombination_single, inner_smul_left, inner_smul_right]
          rw [inner_centeredClassLp hF_L2, inner_bridgeEvalLp hν]

private theorem norm_centeredCombination_eq_bridgeCombination
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (u : ↥F →₀ ℝ) :
    ‖centeredCombination P hF_L2 u‖ = ‖bridgeCombination hν u‖ := by
  have h := inner_centeredCombination_eq_bridgeCombination hν hF_L2 u u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (centeredCombination P hF_L2 u),
    norm_nonneg (bridgeCombination hν u)]

private noncomputable def centeredSpan
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) : Submodule ℝ (Lp ℝ 2 P) :=
  Submodule.span ℝ (Set.range (centeredClassLp P hF_L2))

private noncomputable def centeredClosure
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) : Submodule ℝ (Lp ℝ 2 P) :=
  (centeredSpan P hF_L2).topologicalClosure

private noncomputable def centeredCombinationSpan
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) :
    (↥F →₀ ℝ) →ₗ[ℝ] centeredSpan P hF_L2 :=
  (centeredCombination P hF_L2).codRestrict _ fun u => by
    change (Finsupp.linearCombination ℝ (centeredClassLp P hF_L2)) u ∈
      Submodule.span ℝ (Set.range (centeredClassLp P hF_L2))
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ u

private theorem centeredCombinationSpan_surjective
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) :
    Function.Surjective (centeredCombinationSpan P hF_L2) := by
  intro x
  have hx : (x : Lp ℝ 2 P) ∈ LinearMap.range (centeredCombination P hF_L2) := by
    simpa only [centeredSpan, centeredCombination, Finsupp.range_linearCombination] using x.2
  rcases hx with ⟨u, hu⟩
  exact ⟨u, Subtype.ext hu⟩

private noncomputable def centeredSpanInclusion
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) :
    centeredSpan P hF_L2 →ₗ[ℝ] centeredClosure P hF_L2 :=
  (centeredSpan P hF_L2).subtype.codRestrict _ fun x =>
    Submodule.le_topologicalClosure _ x.2

private theorem centeredSpanInclusion_denseRange
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) :
    DenseRange (centeredSpanInclusion P hF_L2) := by
  simpa only [centeredSpanInclusion] using!
    (denseRange_inclusion_iff (Submodule.le_topologicalClosure
      (centeredSpan P hF_L2))).2 (by intro x hx; exact hx)

private noncomputable def centeredCombinationClosure
    {F : Set (Ω → ℝ)} (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) :
    (↥F →₀ ℝ) →ₗ[ℝ] centeredClosure P hF_L2 :=
  (centeredSpanInclusion P hF_L2).comp (centeredCombinationSpan P hF_L2)

private theorem centeredCombinationClosure_denseRange
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) :
    DenseRange (centeredCombinationClosure P hF_L2) := by
  exact (centeredSpanInclusion_denseRange hF_L2).comp
    (centeredCombinationSpan_surjective hF_L2).denseRange
    (Continuous.subtype_mk continuous_subtype_val _)

private noncomputable def bridgeEmbedding
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) :
    centeredClosure P hF_L2 →L[ℝ] Lp ℝ 2 ν :=
  (bridgeCombination hν).extendOfNorm (centeredCombinationClosure P hF_L2)

private theorem bridgeEmbedding_centeredClassLp
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (f : ↥F) :
    bridgeEmbedding hν hF_L2
        ⟨centeredClassLp P hF_L2 f,
          Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self f))⟩ =
      bridgeEvalLp hν f := by
  let u : ↥F →₀ ℝ := Finsupp.single f 1
  have hext := LinearMap.extendOfNorm_eq
    (f := bridgeCombination hν) (e := centeredCombinationClosure P hF_L2)
    (centeredCombinationClosure_denseRange hF_L2)
    ⟨1, fun v => by
      calc
        ‖bridgeCombination hν v‖ = ‖centeredCombination P hF_L2 v‖ :=
          (norm_centeredCombination_eq_bridgeCombination hν hF_L2 v).symm
        _ = ‖centeredCombinationClosure P hF_L2 v‖ := by
          rfl
        _ ≤ 1 * ‖centeredCombinationClosure P hF_L2 v‖ := by simp⟩ u
  have hu : centeredCombinationClosure P hF_L2 u =
      ⟨centeredClassLp P hF_L2 f,
        Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self f))⟩ := by
    apply Subtype.ext
    change centeredCombination P hF_L2 u = centeredClassLp P hF_L2 f
    simp only [u, centeredCombination, Finsupp.linearCombination_single, one_smul]
  rw [← hu]
  simpa only [bridgeEmbedding, u, bridgeCombination,
    Finsupp.linearCombination_single, one_smul] using hext

private theorem coeFn_finset_sum_L2
    {S ι : Type*} [MeasurableSpace S] {μ : Measure S}
    (v : ι → Lp ℝ 2 μ) (s : Finset ι) :
    (⇑(∑ i ∈ s, v i) : S → ℝ) =ᵐ[μ] fun x => ∑ i ∈ s, (v i : S → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using! (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ))
  | @insert a s ha ih =>
      have hadd := Lp.coeFn_add (v a) (∑ i ∈ s, v i)
      filter_upwards [hadd, ih] with x hx hsum
      simp only [Finset.sum_insert ha, hx, hsum, Pi.add_apply]

private theorem bridgeCombination_ae_eq
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν) (u : ↥F →₀ ℝ) :
    (⇑(bridgeCombination hν u) : LinfF F → ℝ) =ᵐ[ν]
      fun z => u.sum fun f c => c * z f := by
  classical
  have hsum : bridgeCombination hν u = ∑ f ∈ u.support, u f • bridgeEvalLp hν f := by
    simp only [bridgeCombination, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hsum]
  have hcoe := coeFn_finset_sum_L2 (fun f => u f • bridgeEvalLp hν f) u.support
  have hterms : ∀ f ∈ u.support,
      (⇑(u f • bridgeEvalLp hν f) : LinfF F → ℝ) =ᵐ[ν] fun z => u f * z f := by
    intro f hf
    filter_upwards [Lp.coeFn_smul (u f) (bridgeEvalLp hν f),
      (bridgeEval_memLp hν f).coeFn_toLp] with z hsmul heval
    rw [hsmul]
    change u f * ((bridgeEval_memLp hν f).toLp (fun z => z f) : LinfF F → ℝ) z =
      u f * z f
    rw [heval]
  filter_upwards [hcoe,
    (Filter.eventually_all_finset u.support).2 hterms] with z hz hzt
  rw [hz]
  simp only [Finsupp.sum]
  exact Finset.sum_congr rfl fun f hf => hzt f hf

private theorem bridgeCombination_hasGaussianLaw
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν) (u : ↥F →₀ ℝ) :
    HasGaussianLaw (⇑(bridgeCombination hν u) : LinfF F → ℝ) ν := by
  classical
  letI := hν.isProbabilityMeasure
  let e := Fintype.equivFin ↥u.support
  let a : Fin (Fintype.card ↥u.support) → ↥F := fun i => (e.symm i).1
  let L : (Fin (Fintype.card ↥u.support) → ℝ) →L[ℝ] ℝ :=
    ∑ i, u (a i) • ContinuousLinearMap.proj i
  have hraw := (hν.isGaussian_fdd _ a).map L
  have hfun : ⇑L ∘ (fun z : LinfF F => fun i => z (a i)) =
      fun z => u.sum fun f c => c * z f := by
    funext z
    simp only [Function.comp_apply]
    have hL : L (fun i => z (a i)) = ∑ i, u (a i) * z (a i) := by
      simp [L]
    rw [hL]
    rw [Finsupp.sum]
    calc
      (∑ i, u (a i) * z (a i)) =
          ∑ f : ↥u.support, u f.1 * z f.1 := by
            simpa only [a] using e.symm.sum_comp (fun f : ↥u.support => u f.1 * z f.1)
      _ = ∑ f ∈ u.support, u f * z f := by
        simpa only [Finset.univ_eq_attach] using
          u.support.sum_attach (fun f => u f * z f)
  rw [hfun] at hraw
  exact hraw.congr (bridgeCombination_ae_eq hν u).symm

private theorem bridgeCombination_mean
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν) (u : ↥F →₀ ℝ) :
    ∫ z, (bridgeCombination hν u : LinfF F → ℝ) z ∂ν = 0 := by
  classical
  letI := hν.isProbabilityMeasure
  rw [integral_congr_ae (bridgeCombination_ae_eq hν u)]
  simp only [Finsupp.sum]
  rw [integral_finset_sum _ (fun f _ =>
    ((bridgeEval_memLp hν f).integrable (by norm_num)).const_mul (u f))]
  simp_rw [integral_const_mul, hν.mean, mul_zero]
  exact Finset.sum_const_zero

private theorem bridgeEmbedding_centeredCombination
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (u : ↥F →₀ ℝ) :
    bridgeEmbedding hν hF_L2 (centeredCombinationClosure P hF_L2 u) =
      bridgeCombination hν u := by
  exact LinearMap.extendOfNorm_eq
    (f := bridgeCombination hν) (e := centeredCombinationClosure P hF_L2)
    (centeredCombinationClosure_denseRange hF_L2)
    ⟨1, fun v => by
      calc
        ‖bridgeCombination hν v‖ = ‖centeredCombination P hF_L2 v‖ :=
          (norm_centeredCombination_eq_bridgeCombination hν hF_L2 v).symm
        _ = ‖centeredCombinationClosure P hF_L2 v‖ := by rfl
        _ ≤ 1 * ‖centeredCombinationClosure P hF_L2 v‖ := by simp⟩ u

private theorem bridgeEmbedding_norm
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (h : centeredClosure P hF_L2) :
    ‖bridgeEmbedding hν hF_L2 h‖ = ‖h‖ := by
  have hmem : h ∈ closure (Set.range (centeredCombinationClosure P hF_L2)) :=
    centeredCombinationClosure_denseRange hF_L2 h
  obtain ⟨y, hy_range, hy_tendsto⟩ := mem_closure_iff_seq_limit.mp hmem
  choose u hu using hy_range
  have hmap : Tendsto (fun n => bridgeEmbedding hν hF_L2 (y n)) atTop
      (nhds (bridgeEmbedding hν hF_L2 h)) :=
    (bridgeEmbedding hν hF_L2).continuous.continuousAt.tendsto.comp hy_tendsto
  have heq : ∀ n, ‖bridgeEmbedding hν hF_L2 (y n)‖ = ‖y n‖ := by
    intro n
    rw [← hu n, bridgeEmbedding_centeredCombination hν hF_L2]
    exact (norm_centeredCombination_eq_bridgeCombination hν hF_L2 (u n)).symm
  exact tendsto_nhds_unique hmap.norm
    (hy_tendsto.norm.congr' (Filter.Eventually.of_forall fun n => (heq n).symm))

private theorem bridgeEmbedding_inner
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (h g : centeredClosure P hF_L2) :
    ⟪bridgeEmbedding hν hF_L2 h, bridgeEmbedding hν hF_L2 g⟫_ℝ = ⟪h, g⟫_ℝ := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add, bridgeEmbedding_norm hν hF_L2,
    bridgeEmbedding_norm hν hF_L2, bridgeEmbedding_norm hν hF_L2]

private theorem bridgeEmbedding_hasGaussianLaw
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (h : centeredClosure P hF_L2) :
    HasGaussianLaw (⇑(bridgeEmbedding hν hF_L2 h) : LinfF F → ℝ) ν := by
  letI := hν.isProbabilityMeasure
  have hmem : h ∈ closure (Set.range (centeredCombinationClosure P hF_L2)) :=
    centeredCombinationClosure_denseRange hF_L2 h
  obtain ⟨y, hy_range, hy_tendsto⟩ := mem_closure_iff_seq_limit.mp hmem
  choose u hu using hy_range
  have hmap : Tendsto (fun n => bridgeEmbedding hν hF_L2 (y n)) atTop
      (nhds (bridgeEmbedding hν hF_L2 h)) :=
    (bridgeEmbedding hν hF_L2).continuous.continuousAt.tendsto.comp hy_tendsto
  have hlim : Tendsto (fun n => bridgeCombination hν (u n)) atTop
      (nhds (bridgeEmbedding hν hF_L2 h)) :=
    hmap.congr' (Filter.Eventually.of_forall fun n => by
      rw [← hu n, bridgeEmbedding_centeredCombination hν hF_L2])
  exact hasGaussianLaw_of_centered_tendsto_L2 ν
    (fun n => bridgeCombination hν (u n)) (bridgeEmbedding hν hF_L2 h)
    (fun n => bridgeCombination_hasGaussianLaw hν (u n))
    (fun n => bridgeCombination_mean hν (u n)) hlim

private theorem integralL2_eq_integral
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (x : Lp ℝ 2 μ) : integralL2 μ x = ∫ s, (x : S → ℝ) s ∂μ := by
  unfold integralL2 oneL2
  rw [innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_const (1 : ℝ)).coeFn_toLp] with s hs
  rw [hs]
  change (x : S → ℝ) s * 1 = (x : S → ℝ) s
  ring

private theorem influenceFunction_mean
    {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P)) (j : Fin k) :
    ∫ x, influenceFunction ψ j x ∂P = 0 := by
  rw [← integral_congr_ae (influenceFunction_ae_eq ψ j)]
  have hzero := (ψ j).2
  change integralL2 P (ψ j : Lp ℝ 2 P) = 0 at hzero
  rwa [integralL2_eq_integral] at hzero

private theorem bridgeEmbedding_mean
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (h : centeredClosure P hF_L2) :
    ∫ z, (bridgeEmbedding hν hF_L2 h : LinfF F → ℝ) z ∂ν = 0 := by
  letI := hν.isProbabilityMeasure
  have hmem : h ∈ closure (Set.range (centeredCombinationClosure P hF_L2)) :=
    centeredCombinationClosure_denseRange hF_L2 h
  obtain ⟨y, hy_range, hy_tendsto⟩ := mem_closure_iff_seq_limit.mp hmem
  choose u hu using hy_range
  have hmap : Tendsto (fun n => bridgeEmbedding hν hF_L2 (y n)) atTop
      (nhds (bridgeEmbedding hν hF_L2 h)) :=
    (bridgeEmbedding hν hF_L2).continuous.continuousAt.tendsto.comp hy_tendsto
  have hlim : Tendsto (fun n => bridgeCombination hν (u n)) atTop
      (nhds (bridgeEmbedding hν hF_L2 h)) :=
    hmap.congr' (Filter.Eventually.of_forall fun n => by
      rw [← hu n, bridgeEmbedding_centeredCombination hν hF_L2])
  have hintlim := (integralL2 ν).continuous.continuousAt.tendsto.comp hlim
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have hmean : integralL2 ν (bridgeEmbedding hν hF_L2 h) = 0 :=
    tendsto_nhds_unique
      (hintlim.congr' (Filter.Eventually.of_forall fun n => by
        change integralL2 ν (bridgeCombination hν (u n)) = 0
        rw [integralL2_eq_integral, bridgeCombination_mean hν])) hzero
  rwa [integralL2_eq_integral] at hmean

private noncomputable def influenceProjection
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) (j : Fin k) :
    centeredClosure P hF_L2 := by
  letI : CompleteSpace (centeredClosure P hF_L2) := by
    change CompleteSpace (centeredSpan P hF_L2).topologicalClosure
    infer_instance
  exact (centeredClosure P hF_L2).orthogonalProjection (ψ j : Lp ℝ 2 P)

private theorem inner_centered_projection
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (f : ↥F) (j : Fin k) :
    ⟪(⟨centeredClassLp P hF_L2 f,
        Submodule.le_topologicalClosure _
          (Submodule.subset_span (Set.mem_range_self f))⟩ : centeredClosure P hF_L2),
      influenceProjection hF_L2 ψ j⟫_ℝ =
      ⟪centeredClassLp P hF_L2 f, (ψ j : Lp ℝ 2 P)⟫_ℝ := by
  letI : CompleteSpace (centeredClosure P hF_L2) := by
    change CompleteSpace (centeredSpan P hF_L2).topologicalClosure
    infer_instance
  exact (centeredClosure P hF_L2).inner_orthogonalProjection_eq_of_mem_left _ _

private noncomputable def bridgeInfluenceLp
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) (j : Fin k) :
    Lp ℝ 2 ν :=
  bridgeEmbedding hν hF_L2 (influenceProjection hF_L2 ψ j)

private noncomputable def bridgeInfluenceFunction
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (j : Fin k) : LinfF F → ℝ :=
  (Lp.aestronglyMeasurable (bridgeInfluenceLp hν hF_L2 ψ j)).mk
    (bridgeInfluenceLp hν hF_L2 ψ j : LinfF F → ℝ)

private noncomputable def influenceResidual
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) (j : Fin k) :
    Lp ℝ 2 P := by
  letI : CompleteSpace (centeredClosure P hF_L2) := by
    change CompleteSpace (centeredSpan P hF_L2).topologicalClosure
    infer_instance
  exact (ψ j : Lp ℝ 2 P) -
    (centeredClosure P hF_L2).starProjection (ψ j : Lp ℝ 2 P)

private theorem inner_centeredClassLp_influence
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (f : ↥F) (j : Fin k) :
    ⟪centeredClassLp P hF_L2 f, (ψ j : Lp ℝ 2 P)⟫_ℝ =
      jointCov P ψ (Sum.inl f) (Sum.inr j) := by
  rw [L2.inner_def]
  let cf : ℝ := ∫ x, (f : Ω → ℝ) x ∂P
  have hcentf : (⇑(centeredClassLp P hF_L2 f) : Ω → ℝ) =ᵐ[P]
      fun x => (f : Ω → ℝ) x - cf := by
    apply (Lp.coeFn_sub _ _).trans
    filter_upwards [(hF_L2 f f.2).coeFn_toLp,
      (memLp_const cf).coeFn_toLp] with x hfx hcx
    simp only [Pi.sub_apply]
    rw [hfx, hcx]
  change (∫ x, ((ψ j : Lp ℝ 2 P) : Ω → ℝ) x *
      (centeredClassLp P hF_L2 f : Ω → ℝ) x ∂P) = _
  have hae :
      (fun x => ((ψ j : Lp ℝ 2 P) : Ω → ℝ) x *
        (centeredClassLp P hF_L2 f : Ω → ℝ) x) =ᵐ[P]
        fun x => influenceFunction ψ j x * ((f : Ω → ℝ) x - cf) := by
    filter_upwards [hcentf, influenceFunction_ae_eq ψ j] with x hf hψ
    rw [hf, hψ]
  rw [integral_congr_ae hae]
  simp only [jointCov, jointIndexFunction]
  rw [influenceFunction_mean ψ j, mul_zero, sub_zero]
  have hprod : Integrable
      (fun x => (f : Ω → ℝ) x * influenceFunction ψ j x) P := by
    have hψLp : MemLp (influenceFunction ψ j) 2 P :=
      (memLp_congr_ae (influenceFunction_ae_eq ψ j)).mp
        (Lp.memLp (ψ j : Lp ℝ 2 P))
    exact (hF_L2 f f.2).integrable_mul hψLp
  have hψint : Integrable (influenceFunction ψ j) P :=
    ((memLp_congr_ae (influenceFunction_ae_eq ψ j)).mp
      (Lp.memLp (ψ j : Lp ℝ 2 P))).integrable (by norm_num)
  have hleft : Integrable
      (fun x => influenceFunction ψ j x * (f : Ω → ℝ) x) P := by
    exact hprod.congr (Filter.Eventually.of_forall fun x => by ring)
  have hright : Integrable (fun x => cf * influenceFunction ψ j x) P :=
    hψint.const_mul cf
  rw [show (fun x => influenceFunction ψ j x * ((f : Ω → ℝ) x - cf)) =
      fun x => influenceFunction ψ j x * (f : Ω → ℝ) x -
        cf * influenceFunction ψ j x by funext x; ring,
    integral_sub hleft hright]
  have hleft_eq : (∫ x, influenceFunction ψ j x * (f : Ω → ℝ) x ∂P) =
      ∫ x, (f : Ω → ℝ) x * influenceFunction ψ j x ∂P := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hleft_eq, integral_const_mul, influenceFunction_mean ψ j, mul_zero, sub_zero]

private theorem inner_influence
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (ψ : Fin k → ↥(L2ZeroMean P))
    (i j : Fin k) :
    ⟪(ψ i : Lp ℝ 2 P), (ψ j : Lp ℝ 2 P)⟫_ℝ =
      jointCov (F := F) P ψ (Sum.inr i) (Sum.inr j) := by
  rw [L2.inner_def]
  change (∫ x, ((ψ j : Lp ℝ 2 P) : Ω → ℝ) x *
      ((ψ i : Lp ℝ 2 P) : Ω → ℝ) x ∂P) = _
  have hae :
      (fun x => ((ψ j : Lp ℝ 2 P) : Ω → ℝ) x *
        ((ψ i : Lp ℝ 2 P) : Ω → ℝ) x) =ᵐ[P]
        fun x => influenceFunction ψ i x * influenceFunction ψ j x := by
    filter_upwards [influenceFunction_ae_eq ψ i,
      influenceFunction_ae_eq ψ j] with x hi hj
    rw [hi, hj]
    ring
  rw [integral_congr_ae hae]
  simp [jointCov, jointIndexFunction, influenceFunction_mean]

private theorem projection_residual_inner_decomp
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (i j : Fin k) :
    ⟪(influenceProjection hF_L2 ψ i : Lp ℝ 2 P),
        (influenceProjection hF_L2 ψ j : Lp ℝ 2 P)⟫_ℝ +
      ⟪influenceResidual hF_L2 ψ i, influenceResidual hF_L2 ψ j⟫_ℝ =
      ⟪(ψ i : Lp ℝ 2 P), (ψ j : Lp ℝ 2 P)⟫_ℝ := by
  letI : CompleteSpace (centeredClosure P hF_L2) := by
    change CompleteSpace (centeredSpan P hF_L2).topologicalClosure
    infer_instance
  let K := centeredClosure P hF_L2
  have hpi : (influenceProjection hF_L2 ψ i : Lp ℝ 2 P) =
      K.starProjection (ψ i : Lp ℝ 2 P) := rfl
  have hpj : (influenceProjection hF_L2 ψ j : Lp ℝ 2 P) =
      K.starProjection (ψ j : Lp ℝ 2 P) := rfl
  have hij : ⟪K.starProjection (ψ i : Lp ℝ 2 P),
      (ψ j : Lp ℝ 2 P) - K.starProjection (ψ j : Lp ℝ 2 P)⟫_ℝ = 0 :=
    (K.sub_starProjection_mem_orthogonal (ψ j : Lp ℝ 2 P))
      (K.starProjection (ψ i : Lp ℝ 2 P)) (K.starProjection_apply_mem _)
  have hji : ⟪(ψ i : Lp ℝ 2 P) - K.starProjection (ψ i : Lp ℝ 2 P),
      K.starProjection (ψ j : Lp ℝ 2 P)⟫_ℝ = 0 :=
    K.starProjection_inner_eq_zero (ψ i : Lp ℝ 2 P)
      (K.starProjection (ψ j : Lp ℝ 2 P)) (K.starProjection_apply_mem _)
  rw [hpi, hpj]
  change ⟪K.starProjection (ψ i : Lp ℝ 2 P), K.starProjection (ψ j : Lp ℝ 2 P)⟫_ℝ +
      ⟪(ψ i : Lp ℝ 2 P) - K.starProjection (ψ i : Lp ℝ 2 P),
        (ψ j : Lp ℝ 2 P) - K.starProjection (ψ j : Lp ℝ 2 P)⟫_ℝ = _
  symm
  calc
    _ = ⟪K.starProjection (ψ i : Lp ℝ 2 P) +
          ((ψ i : Lp ℝ 2 P) - K.starProjection (ψ i : Lp ℝ 2 P)),
        K.starProjection (ψ j : Lp ℝ 2 P) +
          ((ψ j : Lp ℝ 2 P) - K.starProjection (ψ j : Lp ℝ 2 P))⟫_ℝ := by
      congr <;> abel
    _ = _ := by
      simp only [inner_add_left, inner_add_right]
      rw [hij, hji]
      simp

private noncomputable def residualCovMatrix
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.gram ℝ (influenceResidual hF_L2 ψ)

private theorem residualCovMatrix_posSemidef
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) :
    (residualCovMatrix hF_L2 ψ).PosSemidef :=
  Matrix.posSemidef_gram ℝ _

private noncomputable def bridgeCoordinateSubspace
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Sum ↥F (Fin k)) : centeredClosure P hF_L2 :=
  match a with
  | Sum.inl f =>
      ⟨centeredClassLp P hF_L2 f,
        Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self f))⟩
  | Sum.inr j => influenceProjection hF_L2 ψ j

private noncomputable def bridgeCoordinateLp
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Sum ↥F (Fin k)) : Lp ℝ 2 ν :=
  bridgeEmbedding hν hF_L2 (bridgeCoordinateSubspace hF_L2 ψ a)

private noncomputable def bridgeCoordinateFunction
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Sum ↥F (Fin k)) : LinfF F → ℝ :=
  match a with
  | Sum.inl f => fun z => z f
  | Sum.inr j => bridgeInfluenceFunction hν hF_L2 ψ j

private theorem bridgeCoordinate_ae_eq
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Sum ↥F (Fin k)) :
    (⇑(bridgeCoordinateLp hν hF_L2 ψ a) : LinfF F → ℝ) =ᵐ[ν]
      bridgeCoordinateFunction hν hF_L2 ψ a := by
  cases a with
  | inl f =>
      rw [show bridgeCoordinateLp hν hF_L2 ψ (Sum.inl f) = bridgeEvalLp hν f by
        exact bridgeEmbedding_centeredClassLp hν hF_L2 f]
      exact (bridgeEval_memLp hν f).coeFn_toLp
  | inr j =>
      change (⇑(bridgeInfluenceLp hν hF_L2 ψ j) : LinfF F → ℝ) =ᵐ[ν]
        bridgeInfluenceFunction hν hF_L2 ψ j
      exact (Lp.aestronglyMeasurable (bridgeInfluenceLp hν hF_L2 ψ j)).ae_eq_mk

private theorem bridgeCoordinate_mean
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Sum ↥F (Fin k)) :
    ∫ z, bridgeCoordinateFunction hν hF_L2 ψ a z ∂ν = 0 := by
  rw [← integral_congr_ae (bridgeCoordinate_ae_eq hν hF_L2 ψ a)]
  exact bridgeEmbedding_mean hν hF_L2 (bridgeCoordinateSubspace hF_L2 ψ a)

private theorem bridgeCoordinate_secondMoment
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a b : Sum ↥F (Fin k)) :
    ∫ z, bridgeCoordinateFunction hν hF_L2 ψ a z *
        bridgeCoordinateFunction hν hF_L2 ψ b z ∂ν =
      ⟪bridgeCoordinateSubspace hF_L2 ψ a,
        bridgeCoordinateSubspace hF_L2 ψ b⟫_ℝ := by
  calc
    _ = ⟪bridgeCoordinateLp hν hF_L2 ψ a,
        bridgeCoordinateLp hν hF_L2 ψ b⟫_ℝ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [bridgeCoordinate_ae_eq hν hF_L2 ψ a,
        bridgeCoordinate_ae_eq hν hF_L2 ψ b] with z ha hb
      change bridgeCoordinateFunction hν hF_L2 ψ a z *
          bridgeCoordinateFunction hν hF_L2 ψ b z =
        (bridgeCoordinateLp hν hF_L2 ψ b : LinfF F → ℝ) z *
          (bridgeCoordinateLp hν hF_L2 ψ a : LinfF F → ℝ) z
      rw [ha, hb]
      ring
    _ = _ := bridgeEmbedding_inner hν hF_L2 _ _

private theorem bridgeCoordinate_hasGaussianLaw
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Sum ↥F (Fin k)) :
    HasGaussianLaw (bridgeCoordinateFunction hν hF_L2 ψ a) ν := by
  exact (bridgeEmbedding_hasGaussianLaw hν hF_L2
    (bridgeCoordinateSubspace hF_L2 ψ a)).congr
      (bridgeCoordinate_ae_eq hν hF_L2 ψ a)

private theorem bridgeCoordinate_memLp
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Sum ↥F (Fin k)) :
    MemLp (bridgeCoordinateFunction hν hF_L2 ψ a) 2 ν :=
  (bridgeCoordinate_hasGaussianLaw hν hF_L2 ψ a).memLp_two

private theorem bridgeCoordinates_hasGaussianLaw
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k m : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Fin m → Sum ↥F (Fin k)) :
    HasGaussianLaw
      (fun z : LinfF F => fun i => bridgeCoordinateFunction hν hF_L2 ψ (a i) z) ν := by
  letI := hν.isProbabilityMeasure
  apply hasGaussianLaw_of_forall_dual ν _
  · exact measurable_pi_iff.mpr fun i => by
      cases a i with
      | inl f => exact (linfEvalCLM F f).continuous.measurable
      | inr j => exact
          (Lp.aestronglyMeasurable (bridgeInfluenceLp hν hF_L2 ψ j)).measurable_mk
  · intro L
    let c : Fin m → ℝ := fun i => L (Pi.single i 1)
    let h : centeredClosure P hF_L2 :=
      ∑ i, c i • bridgeCoordinateSubspace hF_L2 ψ (a i)
    have hLp : bridgeEmbedding hν hF_L2 h =
        ∑ i, c i • bridgeCoordinateLp hν hF_L2 ψ (a i) := by
      simp only [h, bridgeCoordinateLp, map_sum, map_smul]
    have hcoe := coeFn_finset_sum_L2
      (fun i => c i • bridgeCoordinateLp hν hF_L2 ψ (a i)) Finset.univ
    have hterms : ∀ i : Fin m,
        (⇑(c i • bridgeCoordinateLp hν hF_L2 ψ (a i)) : LinfF F → ℝ) =ᵐ[ν]
          fun z => c i * bridgeCoordinateFunction hν hF_L2 ψ (a i) z := by
      intro i
      filter_upwards [Lp.coeFn_smul (c i) (bridgeCoordinateLp hν hF_L2 ψ (a i)),
        bridgeCoordinate_ae_eq hν hF_L2 ψ (a i)] with z hsmul hcoord
      rw [hsmul]
      change c i * (bridgeCoordinateLp hν hF_L2 ψ (a i) : LinfF F → ℝ) z = _
      rw [hcoord]
    have hall : ∀ᵐ z ∂ν, ∀ i : Fin m,
        (⇑(c i • bridgeCoordinateLp hν hF_L2 ψ (a i)) : LinfF F → ℝ) z =
          c i * bridgeCoordinateFunction hν hF_L2 ψ (a i) z :=
      Filter.eventually_all.mpr hterms
    have hae : (⇑(bridgeEmbedding hν hF_L2 h) : LinfF F → ℝ) =ᵐ[ν]
        L ∘ (fun z : LinfF F =>
          fun i => bridgeCoordinateFunction hν hF_L2 ψ (a i) z) := by
      filter_upwards [hcoe, hall] with z hz hallz
      rw [hLp]
      rw [hz]
      simp only [Function.comp_apply]
      rw [← LinearMap.sum_single_apply (fun _ : Fin m => ℝ)
        (fun i => bridgeCoordinateFunction hν hF_L2 ψ (a i) z), map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hallz i]
      let v := bridgeCoordinateFunction hν hF_L2 ψ (a i) z
      have hsingle : (Pi.single i v : Fin m → ℝ) =
          v • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
        ext j
        by_cases hij : i = j <;> simp [Pi.single_apply, hij]
      rw [hsingle, map_smul]
      simp only [c, smul_eq_mul]
      ring
    exact (bridgeEmbedding_hasGaussianLaw hν hF_L2 h).congr hae

private noncomputable def residualLaw
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) :
    Measure (EuclideanSpace ℝ (Fin k)) :=
  multivariateGaussian 0 (residualCovMatrix hF_L2 ψ)

private theorem residualCoordinate_mean
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) (j : Fin k) :
    ∫ r : EuclideanSpace ℝ (Fin k), r.ofLp j ∂(residualLaw hF_L2 ψ) = 0 := by
  change ∫ r : EuclideanSpace ℝ (Fin k),
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k => ℝ) j) (id r)
        ∂(residualLaw hF_L2 ψ) = 0
  letI : IsGaussian (residualLaw hF_L2 ψ) := by
    unfold residualLaw
    infer_instance
  rw [(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k => ℝ) j).integral_comp_comm
      (ProbabilityTheory.IsGaussian.integrable_id
        (μ := residualLaw hF_L2 ψ)),
    show (∫ x, id x ∂(residualLaw hF_L2 ψ)) = 0 by
      unfold residualLaw
      simpa only [id_eq] using
        (integral_id_multivariateGaussian
          (μ := (0 : EuclideanSpace ℝ (Fin k)))
          (S := residualCovMatrix hF_L2 ψ))]
  simp

private theorem residualCoordinate_memLp
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) (j : Fin k) :
    MemLp (fun r : EuclideanSpace ℝ (Fin k) => r.ofLp j) 2
      (residualLaw hF_L2 ψ) := by
  letI : IsGaussian (residualLaw hF_L2 ψ) := by
    unfold residualLaw
    infer_instance
  simpa only [Function.comp_id] using!
    ((IsGaussian.hasGaussianLaw_id (μ := residualLaw hF_L2 ψ)).map
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k => ℝ) j)).memLp_two

private theorem residualCoordinate_secondMoment
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) (i j : Fin k) :
    ∫ r : EuclideanSpace ℝ (Fin k), r.ofLp i * r.ofLp j ∂(residualLaw hF_L2 ψ) =
      residualCovMatrix hF_L2 ψ i j := by
  letI : IsGaussian (residualLaw hF_L2 ψ) := by
    unfold residualLaw
    infer_instance
  letI : IsProbabilityMeasure (residualLaw hF_L2 ψ) :=
    IsGaussian.toIsProbabilityMeasure _
  have hcov := covariance_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin k)))
    (residualCovMatrix_posSemidef hF_L2 ψ) i j
  change ∫ r : EuclideanSpace ℝ (Fin k), r.ofLp i * r.ofLp j
      ∂multivariateGaussian 0 (residualCovMatrix hF_L2 ψ) = _
  have hmi : MemLp (fun r : EuclideanSpace ℝ (Fin k) => r.ofLp i) 2
      (multivariateGaussian 0 (residualCovMatrix hF_L2 ψ)) := by
    simpa only [residualLaw] using residualCoordinate_memLp hF_L2 ψ i
  have hmj : MemLp (fun r : EuclideanSpace ℝ (Fin k) => r.ofLp j) 2
      (multivariateGaussian 0 (residualCovMatrix hF_L2 ψ)) := by
    simpa only [residualLaw] using residualCoordinate_memLp hF_L2 ψ j
  have hmeani : ∫ r : EuclideanSpace ℝ (Fin k), r.ofLp i
      ∂multivariateGaussian 0 (residualCovMatrix hF_L2 ψ) = 0 := by
    simpa only [residualLaw] using residualCoordinate_mean hF_L2 ψ i
  have hmeanj : ∫ r : EuclideanSpace ℝ (Fin k), r.ofLp j
      ∂multivariateGaussian 0 (residualCovMatrix hF_L2 ψ) = 0 := by
    simpa only [residualLaw] using residualCoordinate_mean hF_L2 ψ j
  rw [← hcov, covariance_eq_sub hmi hmj,
    hmeani, hmeanj,
    mul_zero, sub_zero]
  simp only [Pi.mul_apply]

private noncomputable def bridgeInfluenceVector
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (z : LinfF F) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 _).symm (fun j => bridgeInfluenceFunction hν hF_L2 ψ j z)

private theorem bridgeInfluenceVector_measurable
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) :
    Measurable (bridgeInfluenceVector hν hF_L2 ψ) := by
  apply (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp
  exact measurable_pi_iff.mpr fun j =>
    (Lp.aestronglyMeasurable (bridgeInfluenceLp hν hF_L2 ψ j)).measurable_mk

private noncomputable def jointExtensionMap
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) :
    LinfF F × EuclideanSpace ℝ (Fin k) →
      LinfF F × EuclideanSpace ℝ (Fin k) :=
  fun zr => (zr.1, bridgeInfluenceVector hν hF_L2 ψ zr.1 + zr.2)

private theorem jointExtensionMap_measurable
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) :
    Measurable (jointExtensionMap hν hF_L2 ψ) := by
  exact measurable_fst.prodMk
    (((bridgeInfluenceVector_measurable hν hF_L2 ψ).comp measurable_fst).add measurable_snd)

private noncomputable def residualCoordinateCLM
    {F : Set (Ω → ℝ)} {k m : ℕ}
    (a : Fin m → Sum ↥F (Fin k)) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    match a i with
    | Sum.inl _ => 0
    | Sum.inr j => PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k => ℝ) j

private theorem residualCoordinates_hasGaussianLaw
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k m : ℕ}
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Fin m → Sum ↥F (Fin k)) :
    HasGaussianLaw (residualCoordinateCLM a)
      (residualLaw hF_L2 ψ) := by
  letI : IsGaussian (residualLaw hF_L2 ψ) := by
    unfold residualLaw
    infer_instance
  simpa only [Function.comp_id] using
    (IsGaussian.hasGaussianLaw_id (μ := residualLaw hF_L2 ψ)).map
      (residualCoordinateCLM a)

private noncomputable def jointInfluenceLaw
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) :
    Measure (LinfF F × EuclideanSpace ℝ (Fin k)) :=
  (ν.prod (residualLaw hF_L2 ψ)).map (jointExtensionMap hν hF_L2 ψ)

private theorem bridgeResidualCoordinates_hasGaussianLaw
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k m : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Fin m → Sum ↥F (Fin k)) :
    HasGaussianLaw
      (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) =>
        (fun i => bridgeCoordinateFunction hν hF_L2 ψ (a i) zr.1) +
          residualCoordinateCLM a zr.2)
      (ν.prod (residualLaw hF_L2 ψ)) := by
  letI := hν.isProbabilityMeasure
  letI : IsProbabilityMeasure (residualLaw hF_L2 ψ) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  let B : LinfF F → (Fin m → ℝ) :=
    fun z i => bridgeCoordinateFunction hν hF_L2 ψ (a i) z
  let R : EuclideanSpace ℝ (Fin k) → (Fin m → ℝ) :=
    residualCoordinateCLM a
  have hB : HasGaussianLaw B ν := bridgeCoordinates_hasGaussianLaw hν hF_L2 ψ a
  have hR : HasGaussianLaw R (residualLaw hF_L2 ψ) :=
    residualCoordinates_hasGaussianLaw hF_L2 ψ a
  have hBprod : HasGaussianLaw (B ∘ Prod.fst)
      (ν.prod (residualLaw hF_L2 ψ)) :=
    hasGaussianLaw_comp_measurePreserving hB measurePreserving_fst
  have hRprod : HasGaussianLaw (R ∘ Prod.snd)
      (ν.prod (residualLaw hF_L2 ψ)) :=
    hasGaussianLaw_comp_measurePreserving hR measurePreserving_snd
  have hind : (B ∘ Prod.fst) ⟂ᵢ[ν.prod (residualLaw hF_L2 ψ)]
      (R ∘ Prod.snd) :=
    indepFun_prod
      (measurable_pi_iff.mpr fun i => by
        dsimp [B]
        cases a i with
        | inl f => exact (linfEvalCLM F f).continuous.measurable
        | inr j => exact
            (Lp.aestronglyMeasurable (bridgeInfluenceLp hν hF_L2 ψ j)).measurable_mk)
      (residualCoordinateCLM a).continuous.measurable
  simpa only [B, R, Function.comp_apply, Pi.add_apply] using
    (hind.hasGaussianLaw hBprod hRprod).fun_add

private theorem jointEval_jointExtensionMap
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Sum ↥F (Fin k)) (zr : LinfF F × EuclideanSpace ℝ (Fin k)) :
    jointEval (jointExtensionMap hν hF_L2 ψ zr) a =
      bridgeCoordinateFunction hν hF_L2 ψ a zr.1 +
        residualCoordinateCLM (fun _ : Fin 1 => a) zr.2 0 := by
  cases a with
  | inl f => simp [jointExtensionMap, jointEval, bridgeCoordinateFunction,
      residualCoordinateCLM]
  | inr j => simp [jointExtensionMap, jointEval, bridgeCoordinateFunction,
      bridgeInfluenceVector, residualCoordinateCLM]

private theorem jointInfluenceLaw_gaussianFDD
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (m : ℕ) (a : Fin m → Sum ↥F (Fin k)) :
    HasGaussianLaw
      (fun w : LinfF F × EuclideanSpace ℝ (Fin k) =>
        fun i => jointEval w (a i))
      (jointInfluenceLaw hν hF_L2 ψ) := by
  let Y : LinfF F × EuclideanSpace ℝ (Fin k) → (Fin m → ℝ) :=
    fun w i => jointEval w (a i)
  have hY : Measurable Y := measurable_pi_iff.mpr fun i => by
    dsimp [Y]
    cases a i with
    | inl f => exact (linfEvalCLM F f).continuous.measurable.comp measurable_fst
    | inr j => exact
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k => ℝ) j).continuous.measurable.comp measurable_snd
  have hsource := bridgeResidualCoordinates_hasGaussianLaw hν hF_L2 ψ a
  refine ⟨?_⟩
  rw [jointInfluenceLaw,
    Measure.map_map hY (jointExtensionMap_measurable hν hF_L2 ψ)]
  have hcomp : Y ∘ jointExtensionMap hν hF_L2 ψ =
      fun zr : LinfF F × EuclideanSpace ℝ (Fin k) =>
        (fun i => bridgeCoordinateFunction hν hF_L2 ψ (a i) zr.1) +
          residualCoordinateCLM a zr.2 := by
    funext zr i
    change jointEval (jointExtensionMap hν hF_L2 ψ zr) (a i) =
      bridgeCoordinateFunction hν hF_L2 ψ (a i) zr.1 +
        residualCoordinateCLM a zr.2 i
    rw [jointEval_jointExtensionMap]
    cases h : a i with
    | inl f => simp [residualCoordinateCLM, h]
    | inr j => simp [residualCoordinateCLM, h]
  rw [hcomp]
  exact hsource.isGaussian_map

private theorem jointInfluenceLaw_firstMarginal
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) :
    (jointInfluenceLaw hν hF_L2 ψ).map Prod.fst = ν := by
  letI := hν.isProbabilityMeasure
  letI : IsProbabilityMeasure (residualLaw hF_L2 ψ) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  rw [jointInfluenceLaw,
    Measure.map_map measurable_fst
      (jointExtensionMap_measurable hν hF_L2 ψ)]
  have hcomp : Prod.fst ∘ jointExtensionMap hν hF_L2 ψ = Prod.fst := rfl
  rw [hcomp, Measure.map_fst_prod, measure_univ, one_smul]

omit [MeasurableSpace Ω] in
private theorem jointEval_measurable
    {F : Set (Ω → ℝ)} {k : ℕ} (a : Sum ↥F (Fin k)) :
    Measurable (fun w : LinfF F × EuclideanSpace ℝ (Fin k) => jointEval w a) := by
  cases a with
  | inl f => exact (linfEvalCLM F f).continuous.measurable.comp measurable_fst
  | inr j => exact
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k => ℝ) j).continuous.measurable.comp measurable_snd

private theorem integral_fun_fst_probability
    {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : A → E) :
    ∫ z : A × B, f z.1 ∂μ.prod ν = ∫ x, f x ∂μ := by
  simpa using integral_fun_fst (μ := μ) (ν := ν) f

private theorem integral_fun_snd_probability
    {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : B → E) :
    ∫ z : A × B, f z.2 ∂μ.prod ν = ∫ y, f y ∂ν := by
  simpa using integral_fun_snd (μ := μ) (ν := ν) f

private theorem jointInfluenceLaw_mean
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a : Sum ↥F (Fin k)) :
    ∫ w, jointEval w a ∂(jointInfluenceLaw hν hF_L2 ψ) = 0 := by
  letI := hν.isProbabilityMeasure
  letI : IsFiniteMeasure ν := IsZeroOrProbabilityMeasure.toIsFiniteMeasure ν
  letI : SigmaFinite ν := IsFiniteMeasure.toSigmaFinite ν
  letI : SFinite ν := by infer_instance
  letI : IsProbabilityMeasure (residualLaw hF_L2 ψ) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  rw [jointInfluenceLaw, integral_map
    (jointExtensionMap_measurable hν hF_L2 ψ).aemeasurable
    (jointEval_measurable a).aestronglyMeasurable]
  cases a with
  | inl f =>
      change ∫ zr : LinfF F × EuclideanSpace ℝ (Fin k), zr.1 f
          ∂ν.prod (residualLaw hF_L2 ψ) = 0
      calc
        _ = ∫ z : LinfF F, z f ∂ν :=
          integral_fun_fst_probability (A := LinfF F)
            (B := EuclideanSpace ℝ (Fin k)) (μ := ν)
            (ν := residualLaw hF_L2 ψ) (fun z : LinfF F => z f)
        _ = 0 := by
          simpa [bridgeCoordinateFunction] using
            bridgeCoordinate_mean hν hF_L2 ψ (Sum.inl f)
  | inr j =>
      let q : LinfF F → ℝ := bridgeInfluenceFunction hν hF_L2 ψ j
      let r : EuclideanSpace ℝ (Fin k) → ℝ := fun x => x.ofLp j
      have hq : Integrable q ν :=
        (bridgeCoordinate_memLp hν hF_L2 ψ (Sum.inr j)).integrable (by norm_num)
      have hr : Integrable r (residualLaw hF_L2 ψ) :=
        (residualCoordinate_memLp hF_L2 ψ j).integrable (by norm_num)
      change ∫ zr : LinfF F × EuclideanSpace ℝ (Fin k),
          q zr.1 + r zr.2
          ∂ν.prod (residualLaw hF_L2 ψ) = 0
      rw [integral_add (hq.comp_fst (residualLaw hF_L2 ψ)) (hr.comp_snd ν),
        integral_fun_fst_probability, integral_fun_snd_probability]
      have hqmean : ∫ z, q z ∂ν = 0 := by
        simpa [q, bridgeCoordinateFunction] using
          bridgeCoordinate_mean hν hF_L2 ψ (Sum.inr j)
      have hrmean : ∫ x, r x ∂(residualLaw hF_L2 ψ) = 0 := by
        simpa [r] using residualCoordinate_mean hF_L2 ψ j
      rw [hqmean, hrmean, add_zero]

private theorem jointInfluenceLaw_covariance
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P))
    (a b : Sum ↥F (Fin k)) :
    ∫ w, jointEval w a * jointEval w b ∂(jointInfluenceLaw hν hF_L2 ψ) =
      jointCov P ψ a b := by
  letI := hν.isProbabilityMeasure
  letI : IsFiniteMeasure ν := IsZeroOrProbabilityMeasure.toIsFiniteMeasure ν
  letI : SigmaFinite ν := IsFiniteMeasure.toSigmaFinite ν
  letI : SFinite ν := by infer_instance
  letI : IsProbabilityMeasure (residualLaw hF_L2 ψ) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  rw [jointInfluenceLaw, integral_map
    (jointExtensionMap_measurable hν hF_L2 ψ).aemeasurable
    ((jointEval_measurable a).fun_mul (jointEval_measurable b)).aestronglyMeasurable]
  cases a with
  | inl f =>
      cases b with
      | inl g =>
          change ∫ zr : LinfF F × EuclideanSpace ℝ (Fin k), zr.1 f * zr.1 g
              ∂ν.prod (residualLaw hF_L2 ψ) = _
          calc
            _ = ∫ z, z f * z g ∂ν :=
              integral_fun_fst_probability (A := LinfF F)
                (B := EuclideanSpace ℝ (Fin k)) (μ := ν)
                (ν := residualLaw hF_L2 ψ) (fun z : LinfF F => z f * z g)
            _ = ⟪bridgeCoordinateSubspace hF_L2 ψ (Sum.inl f),
                bridgeCoordinateSubspace hF_L2 ψ (Sum.inl g)⟫_ℝ := by
              simpa [bridgeCoordinateFunction] using
                bridgeCoordinate_secondMoment hν hF_L2 ψ (Sum.inl f) (Sum.inl g)
            _ = _ := inner_centeredClassLp hF_L2 f g
      | inr j =>
          let qf : LinfF F → ℝ := fun z => z f
          let qj : LinfF F → ℝ := bridgeInfluenceFunction hν hF_L2 ψ j
          let rj : EuclideanSpace ℝ (Fin k) → ℝ := fun r => r.ofLp j
          have hqf : MemLp qf 2 ν := by
            change MemLp (bridgeCoordinateFunction hν hF_L2 ψ (Sum.inl f)) 2 ν
            exact bridgeCoordinate_memLp hν hF_L2 ψ (Sum.inl f)
          have hqj : MemLp qj 2 ν := by
            change MemLp (bridgeCoordinateFunction hν hF_L2 ψ (Sum.inr j)) 2 ν
            exact bridgeCoordinate_memLp hν hF_L2 ψ (Sum.inr j)
          have hrj : Integrable rj (residualLaw hF_L2 ψ) := by
            simpa [rj] using
              (residualCoordinate_memLp hF_L2 ψ j).integrable (by norm_num)
          have hqq : Integrable (fun z => qf z * qj z) ν :=
            hqf.integrable_mul hqj
          have hqr : Integrable
              (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) => qf zr.1 * rj zr.2)
              (ν.prod (residualLaw hF_L2 ψ)) :=
            (hqf.integrable (by norm_num)).mul_prod hrj
          have hqqfst : Integrable
              (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) => qf zr.1 * qj zr.1)
              (ν.prod (residualLaw hF_L2 ψ)) :=
            hqq.comp_fst (residualLaw hF_L2 ψ)
          change ∫ zr : LinfF F × EuclideanSpace ℝ (Fin k),
              qf zr.1 * (qj zr.1 + rj zr.2)
              ∂ν.prod (residualLaw hF_L2 ψ) = _
          rw [show (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) =>
              qf zr.1 * (qj zr.1 + rj zr.2)) =
              (fun zr => qf zr.1 * qj zr.1 + qf zr.1 * rj zr.2) by
                funext zr; ring,
            integral_add hqqfst hqr]
          rw [integral_fun_fst_probability (μ := ν)
              (ν := residualLaw hF_L2 ψ) (fun z => qf z * qj z),
            integral_prod_mul]
          have hrjmean : ∫ r, rj r ∂(residualLaw hF_L2 ψ) = 0 := by
            simpa [rj] using residualCoordinate_mean hF_L2 ψ j
          rw [hrjmean, mul_zero, add_zero]
          calc
            _ = ⟪bridgeCoordinateSubspace hF_L2 ψ (Sum.inl f),
                bridgeCoordinateSubspace hF_L2 ψ (Sum.inr j)⟫_ℝ := by
              simpa [bridgeCoordinateFunction] using
                bridgeCoordinate_secondMoment hν hF_L2 ψ (Sum.inl f) (Sum.inr j)
            _ = ⟪centeredClassLp P hF_L2 f, (ψ j : Lp ℝ 2 P)⟫_ℝ :=
              inner_centered_projection hF_L2 ψ f j
            _ = _ := inner_centeredClassLp_influence hF_L2 ψ f j
  | inr i =>
      cases b with
      | inl f =>
          rw [show jointCov P ψ (Sum.inr i) (Sum.inl f) =
              jointCov P ψ (Sum.inl f) (Sum.inr i) by
                exact jointCov_comm P ψ _ _]
          let qf : LinfF F → ℝ := fun z => z f
          let qi : LinfF F → ℝ := bridgeInfluenceFunction hν hF_L2 ψ i
          let ri : EuclideanSpace ℝ (Fin k) → ℝ := fun r => r.ofLp i
          have hqf : MemLp qf 2 ν := by
            change MemLp (bridgeCoordinateFunction hν hF_L2 ψ (Sum.inl f)) 2 ν
            exact bridgeCoordinate_memLp hν hF_L2 ψ (Sum.inl f)
          have hqi : MemLp qi 2 ν := by
            change MemLp (bridgeCoordinateFunction hν hF_L2 ψ (Sum.inr i)) 2 ν
            exact bridgeCoordinate_memLp hν hF_L2 ψ (Sum.inr i)
          have hri : Integrable ri (residualLaw hF_L2 ψ) := by
            simpa [ri] using
              (residualCoordinate_memLp hF_L2 ψ i).integrable (by norm_num)
          have hqq : Integrable (fun z => qf z * qi z) ν :=
            hqf.integrable_mul hqi
          have hqr : Integrable
              (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) => qf zr.1 * ri zr.2)
              (ν.prod (residualLaw hF_L2 ψ)) :=
            (hqf.integrable (by norm_num)).mul_prod hri
          have hqqfst : Integrable
              (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) => qf zr.1 * qi zr.1)
              (ν.prod (residualLaw hF_L2 ψ)) :=
            hqq.comp_fst (residualLaw hF_L2 ψ)
          change ∫ zr : LinfF F × EuclideanSpace ℝ (Fin k),
              (qi zr.1 + ri zr.2) * qf zr.1
              ∂ν.prod (residualLaw hF_L2 ψ) = _
          rw [show (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) =>
              (qi zr.1 + ri zr.2) * qf zr.1) =
              (fun zr => qf zr.1 * qi zr.1 + qf zr.1 * ri zr.2) by
                funext zr; ring,
            integral_add hqqfst hqr]
          rw [integral_fun_fst_probability (μ := ν)
              (ν := residualLaw hF_L2 ψ) (fun z => qf z * qi z),
            integral_prod_mul]
          have hrimean : ∫ r, ri r ∂(residualLaw hF_L2 ψ) = 0 := by
            simpa [ri] using residualCoordinate_mean hF_L2 ψ i
          rw [hrimean, mul_zero, add_zero]
          calc
            _ = ⟪bridgeCoordinateSubspace hF_L2 ψ (Sum.inl f),
                bridgeCoordinateSubspace hF_L2 ψ (Sum.inr i)⟫_ℝ := by
              simpa [bridgeCoordinateFunction] using
                bridgeCoordinate_secondMoment hν hF_L2 ψ (Sum.inl f) (Sum.inr i)
            _ = ⟪centeredClassLp P hF_L2 f, (ψ i : Lp ℝ 2 P)⟫_ℝ :=
              inner_centered_projection hF_L2 ψ f i
            _ = _ := inner_centeredClassLp_influence hF_L2 ψ f i
      | inr j =>
          let qi : LinfF F → ℝ := bridgeInfluenceFunction hν hF_L2 ψ i
          let qj : LinfF F → ℝ := bridgeInfluenceFunction hν hF_L2 ψ j
          let ri : EuclideanSpace ℝ (Fin k) → ℝ := fun r => r.ofLp i
          let rj : EuclideanSpace ℝ (Fin k) → ℝ := fun r => r.ofLp j
          have hqi2 : MemLp qi 2 ν := by
            change MemLp (bridgeCoordinateFunction hν hF_L2 ψ (Sum.inr i)) 2 ν
            exact bridgeCoordinate_memLp hν hF_L2 ψ (Sum.inr i)
          have hqj2 : MemLp qj 2 ν := by
            change MemLp (bridgeCoordinateFunction hν hF_L2 ψ (Sum.inr j)) 2 ν
            exact bridgeCoordinate_memLp hν hF_L2 ψ (Sum.inr j)
          have hri2 : MemLp ri 2 (residualLaw hF_L2 ψ) := by
            simpa [ri] using residualCoordinate_memLp hF_L2 ψ i
          have hrj2 : MemLp rj 2 (residualLaw hF_L2 ψ) := by
            simpa [rj] using residualCoordinate_memLp hF_L2 ψ j
          have hqi := hqi2.integrable (by norm_num)
          have hqj := hqj2.integrable (by norm_num)
          have hri := hri2.integrable (by norm_num)
          have hrj := hrj2.integrable (by norm_num)
          have hqq : Integrable (fun z => qi z * qj z) ν := hqi2.integrable_mul hqj2
          have hqrj : Integrable
              (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) => qi zr.1 * rj zr.2)
              (ν.prod (residualLaw hF_L2 ψ)) := hqi.mul_prod hrj
          have hqri : Integrable
              (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) => qj zr.1 * ri zr.2)
              (ν.prod (residualLaw hF_L2 ψ)) := hqj.mul_prod hri
          have hrr : Integrable (fun r => ri r * rj r) (residualLaw hF_L2 ψ) :=
            hri2.integrable_mul hrj2
          have hqqfst : Integrable
              (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) => qi zr.1 * qj zr.1)
              (ν.prod (residualLaw hF_L2 ψ)) :=
            hqq.comp_fst (residualLaw hF_L2 ψ)
          have hrrsnd : Integrable
              (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) => ri zr.2 * rj zr.2)
              (ν.prod (residualLaw hF_L2 ψ)) := hrr.comp_snd ν
          have hsumAB : Integrable
              (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) =>
                qi zr.1 * qj zr.1 + qi zr.1 * rj zr.2)
              (ν.prod (residualLaw hF_L2 ψ)) := hqqfst.add hqrj
          have hsumABC : Integrable
              (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) =>
                (qi zr.1 * qj zr.1 + qi zr.1 * rj zr.2) + qj zr.1 * ri zr.2)
              (ν.prod (residualLaw hF_L2 ψ)) := hsumAB.add hqri
          change ∫ zr : LinfF F × EuclideanSpace ℝ (Fin k),
              (qi zr.1 + ri zr.2) * (qj zr.1 + rj zr.2)
              ∂ν.prod (residualLaw hF_L2 ψ) = _
          rw [show (fun zr : LinfF F × EuclideanSpace ℝ (Fin k) =>
              (qi zr.1 + ri zr.2) * (qj zr.1 + rj zr.2)) =
              (fun zr => qi zr.1 * qj zr.1 + qi zr.1 * rj zr.2 +
                qj zr.1 * ri zr.2 + ri zr.2 * rj zr.2) by funext zr; ring]
          rw [integral_add
            hsumABC hrrsnd,
            integral_add hsumAB hqri,
            integral_add hqqfst hqrj]
          rw [integral_fun_fst_probability (μ := ν)
              (ν := residualLaw hF_L2 ψ) (fun z => qi z * qj z),
            integral_prod_mul, integral_prod_mul,
            integral_fun_snd_probability (μ := ν)
              (ν := residualLaw hF_L2 ψ) (fun r => ri r * rj r)]
          have hqimean : ∫ z, qi z ∂ν = 0 := by
            simpa [qi, bridgeCoordinateFunction] using
              bridgeCoordinate_mean hν hF_L2 ψ (Sum.inr i)
          have hqjmean : ∫ z, qj z ∂ν = 0 := by
            simpa [qj, bridgeCoordinateFunction] using
              bridgeCoordinate_mean hν hF_L2 ψ (Sum.inr j)
          have hrimean : ∫ r, ri r ∂(residualLaw hF_L2 ψ) = 0 := by
            simpa [ri] using residualCoordinate_mean hF_L2 ψ i
          have hrjmean : ∫ r, rj r ∂(residualLaw hF_L2 ψ) = 0 := by
            simpa [rj] using residualCoordinate_mean hF_L2 ψ j
          rw [hqimean, hqjmean, hrimean, hrjmean]
          simp only [mul_zero, add_zero]
          rw [show (∫ z, qi z * qj z ∂ν) =
              ⟪bridgeCoordinateSubspace hF_L2 ψ (Sum.inr i),
                bridgeCoordinateSubspace hF_L2 ψ (Sum.inr j)⟫_ℝ by
                simpa [qi, qj, bridgeCoordinateFunction] using
                  bridgeCoordinate_secondMoment hν hF_L2 ψ (Sum.inr i) (Sum.inr j),
            residualCoordinate_secondMoment hF_L2 ψ i j,
            residualCovMatrix, Matrix.gram_apply]
          change ⟪(influenceProjection hF_L2 ψ i : Lp ℝ 2 P),
              (influenceProjection hF_L2 ψ j : Lp ℝ 2 P)⟫_ℝ +
              ⟪influenceResidual hF_L2 ψ i, influenceResidual hF_L2 ψ j⟫_ℝ = _
          rw [projection_residual_inner_decomp hF_L2 ψ i j,
            inner_influence ψ i j]

private theorem jointInfluenceLaw_tight
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P) (ψ : Fin k → ↥(L2ZeroMean P)) :
    IsTightMeasureSet
      ({jointInfluenceLaw hν hF_L2 ψ} :
        Set (Measure (LinfF F × EuclideanSpace ℝ (Fin k)))) := by
  letI := hν.isProbabilityMeasure
  letI : IsProbabilityMeasure (residualLaw hF_L2 ψ) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  letI : IsProbabilityMeasure (jointInfluenceLaw hν hF_L2 ψ) :=
    Measure.isProbabilityMeasure_map
      (jointExtensionMap_measurable hν hF_L2 ψ).aemeasurable
  apply AsymptoticStatistics.Prohorov.tight_prod_of_tight_marginals
  · have himage :
        ((fun μ : Measure (LinfF F × EuclideanSpace ℝ (Fin k)) => μ.map Prod.fst) ''
            {jointInfluenceLaw hν hF_L2 ψ}) = {ν} := by
        ext ρ
        simp [jointInfluenceLaw_firstMarginal hν hF_L2 ψ]
    rw [himage]
    exact hν.tight
  · rw [Set.image_singleton]
    letI : IsProbabilityMeasure
        ((jointInfluenceLaw hν hF_L2 ψ).map Prod.snd) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    exact MeasureTheory.isTightMeasureSet_singleton

/-- Existence of the finite Gaussian influence extension of a supplied
`P`-Brownian bridge. The explicit `hF_L2` prevents the heavy-tail
`integral_undef` counterexample admitted by `IsPBrownianBridge` alone. -/
theorem exists_jointBridgeInfluence
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
    {ν : Measure (LinfF F)} (hν : IsPBrownianBridge F P ν)
    (hF_L2 : ∀ f ∈ F, MemLp f 2 P)
    (ψ : Fin k → ↥(L2ZeroMean P)) :
    ∃ κ : Measure (LinfF F × EuclideanSpace ℝ (Fin k)),
      IsJointBridgeInfluence F P ψ ν κ := by
  letI := hν.isProbabilityMeasure
  letI : IsProbabilityMeasure (residualLaw hF_L2 ψ) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  letI : IsProbabilityMeasure (jointInfluenceLaw hν hF_L2 ψ) :=
    Measure.isProbabilityMeasure_map
      (jointExtensionMap_measurable hν hF_L2 ψ).aemeasurable
  refine ⟨jointInfluenceLaw hν hF_L2 ψ, ?_⟩
  exact
    { isProbabilityMeasure := inferInstance
      firstMarginal := jointInfluenceLaw_firstMarginal hν hF_L2 ψ
      gaussianFDD := jointInfluenceLaw_gaussianFDD hν hF_L2 ψ
      mean := jointInfluenceLaw_mean hν hF_L2 ψ
      covariance := jointInfluenceLaw_covariance hν hF_L2 ψ
      tight := jointInfluenceLaw_tight hν hF_L2 ψ }


end AsymptoticStatistics.EmpiricalProcess
